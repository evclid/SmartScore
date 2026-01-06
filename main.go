package main

import (
	"context"
	"database/sql"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	"math"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode"

	"github.com/PuerkitoBio/goquery"
	"github.com/chromedp/cdproto/cdp"
	"github.com/chromedp/cdproto/network"
	"github.com/chromedp/chromedp"
	tgbotapi "github.com/go-telegram-bot-api/telegram-bot-api/v5"
	_ "github.com/mattn/go-sqlite3"
	"github.com/spf13/viper"
	"github.com/tinkoff/invest-api-go-sdk/investgo"
	pb "github.com/tinkoff/invest-api-go-sdk/proto"
	"gopkg.in/natefinch/lumberjack.v2"
)

// --- НАЧАЛО БЛОКА КОНСТАНТ И ГЛОБАЛЬНЫХ ПЕРЕМЕННЫХ ---
const (
	dbFileName              = "investors.db"
	telegramCommandTimeout  = 60
	maxConcurrentTrendTasks = 10
	cookieFilePath          = "cookies.json"
	smoothing               = 1.0
)

// Config определяет структуру конфигурации из YAML файла.
type Config struct {
	InvestorURLs            []string           `yaml:"investorURLs"`
	SuccessRates            map[string]float64 `yaml:"successRates"`
	CheckIntervalSeconds    int                `yaml:"checkIntervalSeconds"`
	AnalysisPeriodMinutes   int                `yaml:"analysisPeriodMinutes"`
	HistoryDays             int                `yaml:"historyDays"`
	UserDataDir             string             `yaml:"userDataDir"`
	ProfileDirectory        string             `yaml:"profileDirectory"`
	UserAgent               string             `yaml:"userAgent"`
	TelegramToken           string             `yaml:"telegramToken"`
	TinkoffToken            string             `yaml:"tinkoffToken"`
	TelegramChatID          int64              `yaml:"telegramChatID"`
	ProfileDelaySeconds     int                `yaml:"profileDelaySeconds"`
	MinTrendDurationMinutes int                `yaml:"minTrendDurationMinutes"`
	BuyThreshold            float64            `yaml:"buyThreshold"`
	TrendReversalThreshold  float64            `yaml:"trendReversalThreshold"`
	MinDataPoints           int                `yaml:"minDataPoints"`
	MinInvestors            int                `yaml:"minInvestors"`
	MinDataWeight           float64            `yaml:"minDataWeight"`
	MinRSquaredThreshold    float64            `yaml:"minRSquaredThreshold"`
	ExcludedStocks          []string           `yaml:"ExcludedStocks"`
	BaselineWeight          float64            `yaml:"baselineWeight"`
	CommissionRate          float64            `yaml:"commissionRate"`
	EWMAAlpha               float64            `yaml:"ewmaAlpha"`
	WhiteZoneSize           int                `yaml:"WhiteZoneSize"`
	GrayZoneSize            int                `yaml:"GrayZoneSize"`
	MinWeightThreshold      float64            `yaml:"MinWeightThreshold"`
	MinTransactionAmount    float64            `yaml:"MinTransactionAmount"`
}

var (
	config       Config
	dbStorage    *SQLiteStorage
	positionRepo PositionRepository
	telegramBot  *tgbotapi.BotAPI

	rankingMessage    string
	rankingMessageMtx sync.RWMutex
	rankingResults    []StockScore
	rankingResultsMtx sync.RWMutex

	openPositions    map[string]Position
	openPositionsMtx sync.RWMutex

	closedPositions    []Position
	closedPositionsMtx sync.RWMutex

	initialBudget  float64 = 147000.0
	availableFunds float64

	cycleMtx     sync.Mutex
	restartCycle = make(chan struct{})

	investorFailureCount   = make(map[string]int)
	investorSuspendedUntil = make(map[string]time.Time)
	investorLock           sync.Mutex

	lastSnapshotCount    = make(map[string]int)
	lastSnapshotCountMtx sync.Mutex

	marketAvgChange float64

	// <<< НОВЫЕ ГЛОБАЛЬНЫЕ ПЕРЕМЕННЫЕ ДЛЯ TINKOFF API >>>
	investClient *investgo.Client
	figiCache    map[string]string // Кэш для FIGI [ticker] -> "figi"
	figiCacheMtx sync.RWMutex

	investorCache    map[InvestorID]InvestorProfile
	investorCacheMtx sync.RWMutex
)

// --- КОНЕЦ БЛОКА КОНСТАНТ И ГЛОБАЛЬНЫХ ПЕРЕМЕННЫХ ---

// --- НАЧАЛО БЛОКА СТРУКТУР ДАННЫХ ---
type InvestorID string

type InvestorProfile struct {
	ID          InvestorID
	Capital     int
	Holdings    []Asset
	SuccessRate float64
	LastUpdated time.Time
}

type Asset struct {
	Name    string // Это русскоязычное название, например "Газпром"
	Percent float64
}

type InvestorInfo struct {
	ID          InvestorID
	Share       float64
	Capital     int
	LastUpdated time.Time
}

type Participant struct {
	ID          InvestorID
	ShareStart  float64
	ShareEnd    float64
	ShareChange float64
}

type StockScore struct {
	Ticker         string // Это тикер, например "GAZP"
	TotalWeight    float64
	Confidence     float64
	Trend          Trend
	Investors      []InvestorInfo
	AvgSuccessRate float64
	TotalCapital   int
	investorSet    map[InvestorID]bool
	InvestorsCount int
}

type Trend struct {
	Ticker              string
	ChangePercent       float64
	ChangeRate          float64
	RelativeChange      float64
	DistributionDetails string
	InvestorsCount      int
	Duration            time.Duration
	Regression          RegressionResult
	AvgChange           AverageChange
	Consistency         float64
	Participants        []Participant
	Timestamp           time.Time
	Score               float64
	PortfolioChange     float64
}

type Cookie struct {
	Name     string  `json:"name"`
	Value    string  `json:"value"`
	Domain   string  `json:"domain"`
	Path     string  `json:"path"`
	Expires  float64 `json:"expires,omitempty"`
	HTTPOnly bool    `json:"httpOnly,omitempty"`
	Secure   bool    `json:"secure,omitempty"`
	SameSite string  `json:"sameSite,omitempty"`
}

type RegressionResult struct {
	Intercept float64
	Slope     float64
	RSquared  float64
}

type AverageChange struct {
	FirstHalfAvg  float64
	SecondHalfAvg float64
}

type HistoricalHolding struct {
	Timestamp  time.Time
	Ticker     string
	TotalShare float64
	Investors  int
}

type Position struct {
	Ticker         string
	EntryTime      time.Time
	Shares         float64
	AllocatedMoney float64
	AveragePrice   float64
	CurrentPrice   float64
	ExitPrice      float64
	ProfitPercent  float64
	ExitTime       time.Time
	Strategy       string
}

type DynamicThresholds struct {
	BuyThreshold      float64
	DurationThreshold time.Duration
	ReversalThreshold float64
}

// --- КОНЕЦ БЛОКА СТРУКТУР ДАННЫХ ---

// --- НАЧАЛО БЛОКА РАБОТЫ С БД (SQLiteStorage, PositionRepository) - БЕЗ ИЗМЕНЕНИЙ ---
type SQLiteStorage struct {
	db *sql.DB
}

func NewSQLiteStorage(filepath string) (*SQLiteStorage, error) {
	db, err := sql.Open("sqlite3", filepath)
	if err != nil {
		return nil, fmt.Errorf("failed to open database: %w", err)
	}
	if err = db.Ping(); err != nil {
		return nil, fmt.Errorf("failed to ping database: %w", err)
	}

	tableStatements := []string{
		`CREATE TABLE IF NOT EXISTS investors (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            investor_id TEXT NOT NULL,
            capital INTEGER NOT NULL,
            success_rate REAL NOT NULL,
            timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
        );`,
		`CREATE TABLE IF NOT EXISTS holdings (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            investor_id TEXT NOT NULL,
            ticker TEXT NOT NULL,
            share REAL NOT NULL,
            timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
        );`,
		`CREATE INDEX IF NOT EXISTS idx_holdings_ticker ON holdings(ticker);`,
		`CREATE INDEX IF NOT EXISTS idx_holdings_timestamp ON holdings(timestamp);`,
		`CREATE INDEX IF NOT EXISTS idx_holdings_investor_ticker ON holdings(investor_id, ticker);`,
		`CREATE TABLE IF NOT EXISTS positions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ticker TEXT NOT NULL,
            entry_time DATETIME,
            exit_time DATETIME,
            average_price REAL,
            exit_price REAL,
            shares REAL,
            allocated_money REAL,
            profit_percent REAL,
            strategy TEXT,
            timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
        );`,
	}

	for _, stmt := range tableStatements {
		_, err := db.Exec(stmt)
		if err != nil {
			return nil, fmt.Errorf("failed to execute statement '%s': %w", stmt, err)
		}
	}
	db.Exec("ALTER TABLE positions ADD COLUMN average_price REAL")
	db.Exec("ALTER TABLE positions ADD COLUMN allocated_money REAL")
	db.Exec("ALTER TABLE positions ADD COLUMN strategy TEXT")
	return &SQLiteStorage{db: db}, nil
}

func (s *SQLiteStorage) SaveInvestors(ctx context.Context, investors []InvestorProfile) error {
	tx, err := s.db.BeginTx(ctx, nil)
	if err != nil {
		return fmt.Errorf("failed to begin transaction: %w", err)
	}
	defer func() {
		if rollbackErr := tx.Rollback(); rollbackErr != nil && !errors.Is(rollbackErr, sql.ErrTxDone) {
			log.Printf("failed to rollback transaction: %v", rollbackErr)
		}
	}()
	now := time.Now().UTC()
	for _, inv := range investors {
		_, err = tx.ExecContext(ctx,
			`INSERT INTO investors (investor_id, capital, success_rate, timestamp)
             VALUES (?, ?, ?, ?)`,
			inv.ID, inv.Capital, inv.SuccessRate, now)
		if err != nil {
			return fmt.Errorf("error saving investor %s: %w", inv.ID, err)
		}

		// ВАЖНО: В holdings мы сохраняем тикер, который получили из `stocks` map.
		// `asset.Name` в данном случае может быть "Газпром", а нам нужен "GAZP"
		for _, asset := range inv.Holdings {
			ticker, ok := stocks[asset.Name]
			if !ok {
				// Если тикер не найден, мы не можем его сохранить для анализа.
				// Эта проверка дублируется с той, что в processHolding, для надежности.
				continue
			}
			_, err = tx.ExecContext(ctx,
				`INSERT INTO holdings (investor_id, ticker, share, timestamp)
                 VALUES (?, ?, ?, ?)`,
				inv.ID, ticker, asset.Percent, now)
			if err != nil {
				return fmt.Errorf("error saving holding for investor %s, ticker %s: %w", inv.ID, ticker, err)
			}
		}
	}
	err = tx.Commit()
	if err != nil {
		return fmt.Errorf("failed to commit transaction: %w", err)
	}
	return nil
}

func (s *SQLiteStorage) GetHistoricalData(ctx context.Context, ticker string, analysisPeriod time.Duration) ([]HistoricalHolding, error) {
	query := `
        SELECT strftime('%Y-%m-%d %H:%M', timestamp) as time_window, SUM(share) as total_share, COUNT(DISTINCT investor_id) as investors
        FROM holdings
        WHERE ticker = ? AND timestamp >= ?
        GROUP BY time_window
        ORDER BY time_window
    `
	rows, err := s.db.QueryContext(ctx, query, ticker, time.Now().UTC().Add(-analysisPeriod))
	if err != nil {
		return nil, fmt.Errorf("database query error: %w", err)
	}
	defer rows.Close()

	var snapshots []HistoricalHolding
	for rows.Next() {
		var timeStr string
		var snapshot HistoricalHolding
		err = rows.Scan(&timeStr, &snapshot.TotalShare, &snapshot.Investors)
		if err != nil {
			return nil, fmt.Errorf("error scanning row: %w", err)
		}
		ts, err := time.Parse("2006-01-02 15:04", timeStr)
		if err != nil {
			log.Printf("Warning: failed to parse timestamp '%s': %v", timeStr, err)
			continue
		}
		snapshot.Timestamp = ts
		snapshot.Ticker = ticker
		snapshots = append(snapshots, snapshot)
	}
	err = rows.Err()
	if err != nil {
		return nil, fmt.Errorf("error iterating rows: %w", err)
	}
	return snapshots, nil
}

func (s *SQLiteStorage) GetAllTickers(ctx context.Context) ([]string, error) {
	rows, err := s.db.QueryContext(ctx, `SELECT DISTINCT ticker FROM holdings`)
	if err != nil {
		return nil, fmt.Errorf("database query error: %w", err)
	}
	defer rows.Close()

	var tickers []string
	for rows.Next() {
		var ticker string
		err = rows.Scan(&ticker)
		if err != nil {
			return nil, fmt.Errorf("error scanning row: %w", err)
		}
		tickers = append(tickers, ticker)
	}
	err = rows.Err()
	if err != nil {
		return nil, fmt.Errorf("error iterating rows: %w", err)
	}
	return tickers, nil
}

func (s *SQLiteStorage) GetHoldingsAtTime(ctx context.Context, ticker string, atTime time.Time) (map[InvestorID]float64, error) {
	query := `
        SELECT investor_id, share
        FROM holdings
        WHERE ticker = ? AND timestamp = (
            SELECT MAX(timestamp) FROM holdings WHERE ticker = ? AND timestamp <= ?
        )
    `
	rows, err := s.db.QueryContext(ctx, query, ticker, ticker, atTime)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	holdings := make(map[InvestorID]float64)
	for rows.Next() {
		var investorID InvestorID
		var share float64
		if err := rows.Scan(&investorID, &share); err != nil {
			return nil, err
		}
		holdings[investorID] = share
	}
	return holdings, nil
}

func (s *SQLiteStorage) GetParticipantsForTicker(ctx context.Context, ticker string, analysisPeriod time.Duration) ([]Participant, error) {
	startTime := time.Now().UTC().Add(-analysisPeriod)
	endTime := time.Now().UTC()

	startHoldings, err := s.GetHoldingsAtTime(ctx, ticker, startTime)
	if err != nil {
		return nil, fmt.Errorf("error getting start holdings: %w", err)
	}
	endHoldings, err := s.GetHoldingsAtTime(ctx, ticker, endTime)
	if err != nil {
		return nil, fmt.Errorf("error getting end holdings: %w", err)
	}

	allInvestors := make(map[InvestorID]bool)
	for id := range startHoldings {
		allInvestors[id] = true
	}
	for id := range endHoldings {
		allInvestors[id] = true
	}

	var participants []Participant
	for id := range allInvestors {
		shareStart := startHoldings[id]
		shareEnd := endHoldings[id]
		shareChange := shareEnd - shareStart
		participants = append(participants, Participant{
			ID:          id,
			ShareStart:  shareStart,
			ShareEnd:    shareEnd,
			ShareChange: shareChange,
		})
	}
	return participants, nil
}

func (s *SQLiteStorage) Close() error {
	return s.db.Close()
}

type PositionRepository interface {
	GetOpenPositions(ctx context.Context) (map[string]Position, error)
	SavePosition(ctx context.Context, pos Position) error
	UpdatePosition(ctx context.Context, pos Position) error
	ClosePosition(ctx context.Context, ticker string, pos Position) error
}

type SQLitePositionRepository struct {
	db *sql.DB
}

func NewSQLitePositionRepository(db *sql.DB) *SQLitePositionRepository {
	return &SQLitePositionRepository{db: db}
}

func (r *SQLitePositionRepository) GetOpenPositions(ctx context.Context) (map[string]Position, error) {
	rows, err := r.db.QueryContext(ctx, `
        SELECT ticker, entry_time, exit_time, average_price, exit_price, shares, allocated_money, profit_percent, strategy
        FROM positions WHERE exit_time = '0001-01-01 00:00:00+00:00'
    `)
	if err != nil {
		return nil, fmt.Errorf("failed to get open positions query: %w", err)
	}
	defer rows.Close()

	positions := make(map[string]Position)
	for rows.Next() {
		var pos Position
		err = rows.Scan(&pos.Ticker, &pos.EntryTime, &pos.ExitTime, &pos.AveragePrice, &pos.ExitPrice, &pos.Shares, &pos.AllocatedMoney, &pos.ProfitPercent, &pos.Strategy)
		if err != nil {
			return nil, fmt.Errorf("failed to scan open position row: %w", err)
		}
		positions[pos.Ticker] = pos
	}
	err = rows.Err()
	if err != nil {
		return nil, fmt.Errorf("error iterating open positions rows: %w", err)
	}
	return positions, nil
}

func (r *SQLitePositionRepository) SavePosition(ctx context.Context, pos Position) error {
	_, err := r.db.ExecContext(ctx, `
        INSERT INTO positions (ticker, entry_time, exit_time, average_price, exit_price, shares, allocated_money, profit_percent, strategy)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    `, pos.Ticker, pos.EntryTime, pos.ExitTime, pos.AveragePrice, pos.ExitPrice, pos.Shares, pos.AllocatedMoney, pos.ProfitPercent, pos.Strategy)
	if err != nil {
		return fmt.Errorf("failed to save position to database: %w", err)
	}
	return nil
}

func (r *SQLitePositionRepository) UpdatePosition(ctx context.Context, pos Position) error {
	_, err := r.db.ExecContext(ctx, `
        UPDATE positions SET shares = ?, allocated_money = ?, average_price = ?, exit_price = ?, profit_percent = ?, strategy = ?
        WHERE ticker = ? AND exit_time = '0001-01-01 00:00:00+00:00'
    `, pos.Shares, pos.AllocatedMoney, pos.AveragePrice, pos.ExitPrice, pos.ProfitPercent, pos.Strategy, pos.Ticker)
	if err != nil {
		return fmt.Errorf("failed to update position in database: %w", err)
	}
	return nil
}

func (r *SQLitePositionRepository) ClosePosition(ctx context.Context, ticker string, pos Position) error {
	now := time.Now().UTC()
	_, err := r.db.ExecContext(ctx, `
        UPDATE positions SET exit_time = ?, exit_price = ?, profit_percent = ?, strategy = ?
        WHERE ticker = ? AND exit_time = '0001-01-01 00:00:00+00:00'
    `, now, pos.ExitPrice, pos.ProfitPercent, pos.Strategy, ticker)
	if err != nil {
		return fmt.Errorf("failed to close position in database: %w", err)
	}
	return nil
}

// --- КОНЕЦ БЛОКА РАБОТЫ С БД ---

// --- НАЧАЛО БЛОКА ИНИЦИАЛИЗАЦИИ И КОНФИГУРАЦИИ ---
func loadConfig() error {
	viper.SetConfigName("config")
	viper.SetConfigType("yaml")
	viper.AddConfigPath(".")
	viper.AutomaticEnv()
	viper.SetEnvKeyReplacer(strings.NewReplacer(".", "_"))

	if err := viper.ReadInConfig(); err != nil {
		if _, ok := err.(viper.ConfigFileNotFoundError); ok {
			log.Println("config.yaml не найден, используются настройки по умолчанию/из окружения")
		} else {
			return fmt.Errorf("failed to read config file: %w", err)
		}
	}
	if err := viper.Unmarshal(&config); err != nil {
		return fmt.Errorf("failed to unmarshal config: %w", err)
	}
	// Проверка обязательных параметров
	if config.TelegramToken == "" {
		return errors.New("telegramToken is not set in configuration")
	}
	if config.TelegramChatID == 0 {
		return errors.New("telegramChatID is not set in configuration")
	}
	if config.TinkoffToken == "" {
		return errors.New("tinkoffToken is not set in configuration")
	}
	if config.CheckIntervalSeconds <= 0 {
		return errors.New("checkIntervalSeconds must be positive")
	}

	normalizedRates := make(map[string]float64, len(config.SuccessRates))
	for k, v := range config.SuccessRates {
		normalizedRates[strings.ToLower(k)] = v
	}
	config.SuccessRates = normalizedRates
	if config.MinDataWeight == 0 {
		config.MinDataWeight = 0.8
	}
	if config.MinRSquaredThreshold == 0 {
		config.MinRSquaredThreshold = 0.7
	}
	if config.BaselineWeight == 0 {
		config.BaselineWeight = 5000000.0
	}
	if config.CommissionRate == 0 {
		config.CommissionRate = 0.005
	}
	if config.EWMAAlpha == 0 {
		config.EWMAAlpha = 0.3
	}
	if config.GrayZoneSize == 0 {
		config.GrayZoneSize = 1
	}
	if config.BuyThreshold == 0 {
		config.BuyThreshold = 25.0
	}
	if config.TrendReversalThreshold == 0 {
		config.TrendReversalThreshold = 25.0
	}
	if config.MinDataPoints == 0 {
		config.MinDataPoints = 3
	}
	if config.HistoryDays == 0 {
		config.HistoryDays = 2
	}
	if config.WhiteZoneSize == 0 {
		config.WhiteZoneSize = 4
	}
	if config.MinWeightThreshold == 0 {
		config.MinWeightThreshold = 1000000.0
	}
	if config.MinTransactionAmount == 0 {
		config.MinTransactionAmount = 1000.0
	}

	availableFunds = initialBudget
	return nil
}

func initDatabase() error {
	var err error
	dbStorage, err = NewSQLiteStorage(dbFileName)
	if err != nil {
		return fmt.Errorf("database initialization failed: %w", err)
	}
	positionRepo = NewSQLitePositionRepository(dbStorage.db)
	log.Println("База данных и репозиторий позиций успешно инициализированы")
	return nil
}

func initTelegram() error {
	var err error
	telegramBot, err = tgbotapi.NewBotAPI(config.TelegramToken)
	if err != nil {
		return fmt.Errorf("failed to initialize Telegram bot: %w", err)
	}
	log.Println("Telegram bot успешно инициализирован")
	return nil
}

// initInvestorCache загружает последние данные о каждом инвесторе из БД в кеш.
func initInvestorCache() error {
	investorCache = make(map[InvestorID]InvestorProfile)
	ctx := context.Background()
	log.Println("Инициализация кеша инвесторов из базы данных...")

	// Для каждого инвестора из конфига находим его последние данные
	for _, url := range config.InvestorURLs {
		investorID := extractInvestorID(url)

		// 1. Найти последнее время обновления для этого инвестора
		var timestampStr sql.NullString // Используем sql.NullString на случай, если данных нет
		row := dbStorage.db.QueryRowContext(ctx,
			`SELECT MAX(timestamp) FROM investors WHERE investor_id = ?`, investorID)
		if err := row.Scan(&timestampStr); err != nil {
			return fmt.Errorf("ошибка сканирования timestamp для %s: %w", investorID, err)
		}

		if !timestampStr.Valid || timestampStr.String == "" {
			log.Printf("Нет данных в БД для инвестора %s, будет загружен при первом цикле", investorID)
			continue
		}

		// 2. Преобразуем строку в time.Time
		const layout = "2006-01-02 15:04:05.999999999-07:00"
		lastTimestamp, err := time.Parse(layout, timestampStr.String)
		if err != nil {
			// Попробуем другой формат, если первый не удался (на всякий случай)
			// const shortLayout = "2006-01-02 15:04"
			// lastTimestamp, err = time.Parse(shortLayout, timestampStr.String)
			// if err != nil {
			return fmt.Errorf("не удалось распарсить строку с датой '%s' для инвестора %s: %w", timestampStr.String, investorID, err)
			// }
		}

		// 3. Загрузить профиль и активы на это время
		var profile InvestorProfile
		profile.ID = investorID

		row = dbStorage.db.QueryRowContext(ctx,
			`SELECT capital, success_rate FROM investors WHERE investor_id = ? AND timestamp = ?`,
			investorID, lastTimestamp)
		if err := row.Scan(&profile.Capital, &profile.SuccessRate); err != nil {
			log.Printf("Не удалось загрузить профиль для %s на %v: %v", investorID, lastTimestamp, err)
			continue
		}

		profile.LastUpdated = lastTimestamp

		// 4. Загрузить его активы (холдинги)
		rows, err := dbStorage.db.QueryContext(ctx,
			`SELECT ticker, share FROM holdings WHERE investor_id = ? AND timestamp = ?`,
			investorID, lastTimestamp)
		if err != nil {
			log.Printf("Не удалось загрузить активы для %s на %v: %v", investorID, lastTimestamp, err)
			continue
		}
		defer rows.Close()

		// Обратное преобразование тикера в название для структуры Asset
		reverseStocks := make(map[string]string)
		for name, ticker := range stocks {
			reverseStocks[ticker] = name
		}

		var holdings []Asset
		for rows.Next() {
			var ticker string
			var share float64
			if err := rows.Scan(&ticker, &share); err != nil {
				log.Printf("Ошибка сканирования актива для %s: %v", investorID, err)
				continue
			}
			assetName, ok := reverseStocks[ticker]
			if !ok {
				log.Printf("Предупреждение: название для тикера %s не найдено, актив будет пропущен", ticker)
				continue
			}
			holdings = append(holdings, Asset{Name: assetName, Percent: share})
		}
		profile.Holdings = holdings

		investorCache[investorID] = profile
		log.Printf("  - Загружен кеш для %s (данные от %v)", investorID, lastTimestamp.In(time.Local).Format("2006-01-02 15:04"))
	}
	log.Printf("Кеш инвесторов инициализирован, загружено %d профилей.", len(investorCache))
	return nil
}

// getConsolidatedProfiles создает "виртуальный" срез профилей для анализа.
// Он включает в себя все свежезагруженные профили и те, что находятся в кеше
// в рамках льготного периода (grace period).
func getConsolidatedProfiles() []InvestorProfile {
	investorCacheMtx.RLock()
	defer investorCacheMtx.RUnlock()

	consolidated := make([]InvestorProfile, 0, len(investorCache))
	gracePeriod := time.Duration(30 * time.Minute)

	for id, profile := range investorCache {
		timeSinceUpdate := time.Since(profile.LastUpdated)

		if timeSinceUpdate <= gracePeriod {
			consolidated = append(consolidated, profile)
		} else {
			// Если инвестор пропал надолго, мы просто не включаем его в анализ.
			// Логика managePortfolio сама примет решение о продаже его активов,
			// так как их вес в общем рейтинге упадет.
			log.Printf("Инвестор %s не обновлялся %s (дольше %s), его данные не используются в текущем цикле.",
				id, formatDuration(timeSinceUpdate), formatDuration(gracePeriod))
		}
	}
	return consolidated
}

func initTinkoffAPI() error {
	var err error
	ctx := context.Background()

	cfg := investgo.Config{
		Token: config.TinkoffToken,
	}

	investClient, err = investgo.NewClient(ctx, cfg, &SimpleLogger{})
	if err != nil {
		return fmt.Errorf("tinkoff API client initialization failed: %w", err)
	}

	// Инициализация кэша для FIGI
	figiCache = make(map[string]string)

	log.Println("Tinkoff API клиент успешно инициализирован")
	return nil
}

func initComponents() error {
	if err := loadConfig(); err != nil {
		return fmt.Errorf("config initialization failed: %w", err)
	}
	if err := initDatabase(); err != nil {
		return fmt.Errorf("database initialization failed: %w", err)
	}
	if err := initTelegram(); err != nil {
		return fmt.Errorf("telegram initialization failed: %w", err)
	}
	if err := initTinkoffAPI(); err != nil {
		return fmt.Errorf("tinkoff API initialization failed: %w", err)
	}
	if err := initInvestorCache(); err != nil {
		return fmt.Errorf("investor cache initialization failed: %w", err)
	}
	return nil
}

// --- КОНЕЦ БЛОКА ИНИЦИАЛИЗАЦИИ И КОНФИГУРАЦИИ ---

// --- НАЧАЛО БЛОКА ЛОГИКИ TINKOFF API ---

// SimpleLogger реализует investgo.Logger для вывода логов в стандартный log.
type SimpleLogger struct{}

func (l *SimpleLogger) Infof(template string, args ...interface{}) {
	log.Printf("[INFO] "+template, args...)
}
func (l *SimpleLogger) Errorf(template string, args ...interface{}) {
	log.Printf("[ERROR] "+template, args...)
}
func (l *SimpleLogger) Fatalf(template string, args ...interface{}) {
	log.Fatalf("[FATAL] "+template, args...)
}

// findFigiByTicker находит FIGI для указанного тикера, используя кэширование
func findFigiByTicker(ticker string) (string, error) {
	// 1. Проверяем кэш (с блокировкой на чтение)
	figiCacheMtx.RLock()
	figi, found := figiCache[ticker]
	figiCacheMtx.RUnlock()
	if found {
		return figi, nil
	}

	// 2. Если в кэше нет - делаем запрос к API (с блокировкой на запись)
	figiCacheMtx.Lock()
	defer figiCacheMtx.Unlock()

	// 2.1 Повторно проверяем кэш, т.к. другой поток мог уже записать FIGI
	figi, found = figiCache[ticker]
	if found {
		return figi, nil
	}

	// 2.2 Делаем запрос
	instrumentsService := investClient.NewInstrumentsServiceClient()
	resp, err := instrumentsService.FindInstrument(ticker)
	if err != nil {
		return "", fmt.Errorf("failed to find instrument for %s: %w", ticker, err)
	}

	// 2.3 Ищем подходящий инструмент (акция TQBR или ETF)
	for _, instr := range resp.Instruments {
		if (instr.ClassCode == "TQBR" && instr.InstrumentKind == pb.InstrumentType_INSTRUMENT_TYPE_SHARE) ||
			instr.InstrumentKind == pb.InstrumentType_INSTRUMENT_TYPE_ETF {
			figi = instr.Figi
			figiCache[ticker] = figi // Сохраняем в кэш
			log.Printf("FIGI for %s found and cached: %s", ticker, figi)
			return figi, nil
		}
	}

	return "", fmt.Errorf("no suitable instrument found for ticker %s", ticker)
}

// fetchPrice получает последнюю цену для тикера через Tinkoff API.
// Это новая реализация, заменяющая старую на chromedp.
func fetchPrice(ticker string) (float64, error) {
	figi, err := findFigiByTicker(ticker)
	if err != nil {
		return 0, fmt.Errorf("could not get FIGI for %s: %w", ticker, err)
	}

	mds := investClient.NewMarketDataServiceClient()
	resp, err := mds.GetLastPrices([]string{figi})
	if err != nil {
		return 0, fmt.Errorf("API call GetLastPrices for %s (FIGI: %s) failed: %w", ticker, figi, err)
	}

	if len(resp.GetLastPrices()) == 0 {
		return 0, fmt.Errorf("no price data received for %s (FIGI: %s)", ticker, figi)
	}

	price := resp.GetLastPrices()[0].GetPrice().ToFloat()
	if price == 0 {
		return 0, fmt.Errorf("received zero price for %s (FIGI: %s)", ticker, figi)
	}
	// log.Printf("Price for %s fetched successfully: %.2f", ticker, price)
	return price, nil
}

// --- КОНЕЦ БЛОКА ЛОГИКИ TINKOFF API ---

// --- НАЧАЛО БЛОКА ВСПОМОГАТЕЛЬНЫХ ФУНКЦИЙ ---
func sendTelegram(msg tgbotapi.MessageConfig) {
	if _, err := telegramBot.Send(msg); err != nil {
		log.Printf("Ошибка отправки сообщения: %v", err)
	}
}

func formatDuration(d time.Duration) string {
	d = d.Round(time.Second)
	hours := int(d.Hours())
	minutes := int(d.Minutes()) % 60
	seconds := int(d.Seconds()) % 60
	switch {
	case hours > 0:
		return fmt.Sprintf("%d ч %d мин", hours, minutes)
	case minutes > 0:
		return fmt.Sprintf("%d мин %d с", minutes, seconds)
	default:
		return fmt.Sprintf("%d с", seconds)
	}
}

func isSignificantTrend(t Trend) bool {
	dynamicThreshold := config.BuyThreshold
	if marketAvgChange < 0.5 {
		dynamicThreshold *= 0.8
	}
	return math.Abs(t.ChangePercent) >= dynamicThreshold &&
		t.InvestorsCount >= config.MinInvestors &&
		t.Duration >= time.Duration(config.MinTrendDurationMinutes)*time.Minute
}

func calculateAverageChange(data []HistoricalHolding) AverageChange {
	if len(data) == 0 {
		return AverageChange{}
	}
	startTime := data[0].Timestamp
	endTime := data[len(data)-1].Timestamp
	midTime := startTime.Add(endTime.Sub(startTime) / 2)
	var sumFirst, sumSecond float64
	var countFirst, countSecond int
	for _, snapshot := range data {
		if !snapshot.Timestamp.After(midTime) {
			sumFirst += snapshot.TotalShare
			countFirst++
		} else {
			sumSecond += snapshot.TotalShare
			countSecond++
		}
	}
	firstAvg, secondAvg := 0.0, 0.0
	if countFirst > 0 {
		firstAvg = sumFirst / float64(countFirst)
	}
	if countSecond > 0 {
		secondAvg = sumSecond / float64(countSecond)
	}
	return AverageChange{FirstHalfAvg: firstAvg, SecondHalfAvg: secondAvg}
}

func calculateWeightedLinearRegression(data []HistoricalHolding) (RegressionResult, error) {
	if len(data) < 2 {
		return RegressionResult{}, fmt.Errorf("insufficient data for linear regression")
	}
	startTime := data[0].Timestamp
	endTime := data[len(data)-1].Timestamp
	duration := endTime.Sub(startTime).Minutes()
	if duration == 0 {
		duration = 1
	}
	var sumW, sumWX, sumWY, sumWXX, sumWXY float64
	for _, snapshot := range data {
		x := snapshot.Timestamp.Sub(startTime).Minutes()
		y := snapshot.TotalShare
		normalized := x / duration
		weight := config.MinDataWeight + (1-config.MinDataWeight)*normalized
		sumW += weight
		sumWX += weight * x
		sumWY += weight * y
		sumWXX += weight * x * x
		sumWXY += weight * x * y
	}
	denom := sumW*sumWXX - sumWX*sumWX
	if denom == 0 {
		return RegressionResult{}, fmt.Errorf("denominator is zero in weighted linear regression")
	}
	slope := (sumW*sumWXY - sumWX*sumWY) / denom
	intercept := (sumWY - slope*sumWX) / sumW
	weightedMeanY := sumWY / sumW
	var ssTot, ssRes float64
	for _, snapshot := range data {
		x := snapshot.Timestamp.Sub(startTime).Minutes()
		y := snapshot.TotalShare
		predicted := intercept + slope*x
		ssTot += math.Pow(y-weightedMeanY, 2)
		ssRes += math.Pow(y-predicted, 2)
	}
	rSquared := 1.0
	if ssTot != 0 {
		rSquared = 1 - ssRes/ssTot
	}
	return RegressionResult{Intercept: intercept, Slope: slope, RSquared: rSquared}, nil
}

func calculateEWMA(data []float64, alpha float64) []float64 {
	if len(data) == 0 {
		return nil
	}
	ewma := make([]float64, len(data))
	ewma[0] = data[0]
	for i := 1; i < len(data); i++ {
		ewma[i] = alpha*data[i] + (1-alpha)*ewma[i-1]
	}
	return ewma
}

func calculateConsistency(data []float64, ewma []float64) float64 {
	if len(data) != len(ewma) || len(data) == 0 {
		return 0.0
	}
	var sumAbsDiff, sumAbsData float64
	for i := 0; i < len(data); i++ {
		sumAbsDiff += math.Abs(data[i] - ewma[i])
		sumAbsData += math.Abs(data[i])
	}
	if sumAbsData == 0 {
		return 1.0
	}
	consistency := 1.0 - (sumAbsDiff / sumAbsData)
	if consistency < 0 {
		consistency = 0
	}
	return consistency
}

// --- КОНЕЦ БЛОКА ВСПОМОГАТЕЛЬНЫХ ФУНКЦИЙ ---

// --- ГЛАВНАЯ ФУНКЦИЯ И ОСНОВНОЙ ЦИКЛ ---
func main() {

	log.SetFlags(log.LstdFlags | log.Lshortfile) // Добавляем имя файла и номер строки в логи

	lumberjackLogger := &lumberjack.Logger{
		Filename:   "./log/bot.log", // Имя файла лога
		MaxSize:    10,              // Максимальный размер файла в мегабайтах
		MaxBackups: 5,               // Максимальное количество старых файлов для хранения
		MaxAge:     5,               // Максимальное количество дней для хранения логов
		Compress:   true,            // Сжимать старые файлы в .gz
	}

	multiWriter := io.MultiWriter(os.Stdout, lumberjackLogger)

	log.SetOutput(multiWriter)

	if err := initComponents(); err != nil {
		log.Fatalf("Ошибка инициализации компонентов: %v", err)
	}
	defer dbStorage.Close()
	defer investClient.Stop() // <<< ВАЖНО: Чисто останавливаем API клиент при выходе

	loadedPositions, err := positionRepo.GetOpenPositions(context.Background())
	if err != nil {
		log.Fatalf("Ошибка загрузки открытых позиций из БД: %v", err)
	}
	openPositions = loadedPositions

	var totalAllocated float64
	for _, pos := range openPositions {
		totalAllocated += pos.AllocatedMoney
	}
	availableFunds = initialBudget - totalAllocated

	log.Printf("Загружено %d открытых позиций. Вложено: %.2f. Свободно: %.2f",
		len(openPositions), totalAllocated, availableFunds)

	go listenTelegramCommands()

	ticker := time.NewTicker(time.Duration(config.CheckIntervalSeconds) * time.Second)
	defer ticker.Stop()

MainLoop:
	for {
		if !isMarketOpen() {
			log.Println("Маркет закрыт. Будет проведена проверка статуса через 1 час...")
			time.Sleep(1 * time.Hour)
			continue
		}

		select {
		case <-restartCycle:
			log.Println("Получен сигнал перезапуска цикла после pinCodeLogin")
			continue MainLoop
		case <-ticker.C:
			cycleMtx.Lock()
			log.Println("--- НАЧАЛО НОВОГО ЦИКЛА УПРАВЛЕНИЯ ПОРТФЕЛЕМ ---")

			// 1. Сбор и сохранение СВЕЖИХ данных. Функция также обновит кеш.
			freshProfiles := fetchProfiles()
			if len(freshProfiles) > 0 {
				err := dbStorage.SaveInvestors(context.Background(), freshProfiles)
				if err != nil {
					log.Printf("Ошибка сохранения свежих данных инвесторов: %v", err)
				} else {
					log.Printf("Сохранено %d свежих профилей инвесторов в БД", len(freshProfiles))
				}
			} else {
				log.Println("В этом цикле не было получено ни одного свежего профиля.")
			}

			// 2. Получаем консолидированный список для анализа (свежие + кеш в пределах grace period)
			consolidatedProfiles := getConsolidatedProfiles()
			log.Printf("Для анализа используется %d профилей (свежие + кешированные).", len(consolidatedProfiles))

			// 3. Анализ и управление портфелем на основе НАДЕЖНЫХ данных
			managePortfolio(consolidatedProfiles)

			// 4. Обновление цен для отчетности
			updateAllPositionsPrices()

			log.Println("--- КОНЕЦ ЦИКЛА УПРАВЛЕНИЯ ПОРТФЕЛЕМ ---")
			cycleMtx.Unlock()
		}
	}
}

// --- НОВАЯ ЛОГИКА УПРАВЛЕНИЯ ПОРТФЕЛЕМ ---

func managePortfolio(profiles []InvestorProfile) {
	log.Println("--- 1. СТРАТЕГИЧЕСКИЙ УРОВЕНЬ: ФОРМИРОВАНИЕ ПОРТФЕЛЯ ---")

	allStocks := CalculateBestStocks(profiles)
	printAnalysis(allStocks)

	whiteZoneMap, grayZoneMap := identifyZones(allStocks)

	logZone("Белая зона", whiteZoneMap)
	logZone("Серая зона", grayZoneMap)

	liquidateOutOfZonePositions(whiteZoneMap, grayZoneMap)

	whiteZoneStocks := mapToSlice(whiteZoneMap)
	targetAllocations := calculateTargetAllocations(whiteZoneStocks)

	log.Println("--- 2. ТАКТИЧЕСКИЙ УРОВЕНЬ: ИСПОЛНЕНИЕ СДЕЛОК ---")
	executeTrades(targetAllocations, whiteZoneMap)
}

func identifyZones(allStocks []StockScore) (map[string]StockScore, map[string]StockScore) {
	whiteZoneMap := make(map[string]StockScore)
	grayZoneMap := make(map[string]StockScore)
	var suitableStocks []StockScore
	for _, stock := range allStocks {
		if stock.TotalWeight > config.MinWeightThreshold && !isExcluded(stock.Ticker) {
			suitableStocks = append(suitableStocks, stock)
		}
	}

	// sort.Slice(suitableStocks, func(i, j int) bool {
	// 	return suitableStocks[i].TotalWeight > suitableStocks[j].TotalWeight
	// })

	endWhite := config.WhiteZoneSize
	if len(suitableStocks) < endWhite {
		endWhite = len(suitableStocks)
	}

	for i := 0; i < endWhite; i++ {
		stock := suitableStocks[i]
		whiteZoneMap[stock.Ticker] = stock
	}

	startGray := endWhite
	endGray := startGray + config.GrayZoneSize
	if len(suitableStocks) < endGray {
		endGray = len(suitableStocks)
	}

	for i := startGray; i < endGray; i++ {
		stock := suitableStocks[i]
		grayZoneMap[stock.Ticker] = stock
	}

	return whiteZoneMap, grayZoneMap
}

func liquidateOutOfZonePositions(whiteZoneMap, grayZoneMap map[string]StockScore) {
	openPositionsMtx.Lock()
	defer openPositionsMtx.Unlock()

	tickersToCheck := make([]string, 0, len(openPositions))
	for ticker := range openPositions {
		tickersToCheck = append(tickersToCheck, ticker)
	}

	for _, ticker := range tickersToCheck {
		position := openPositions[ticker]
		_, isInWhiteZone := whiteZoneMap[ticker]
		_, isInGrayZone := grayZoneMap[ticker]

		if !isInGrayZone && !isInWhiteZone {

			log.Printf("Ликвидация: Позиция %s. Продажа...", ticker)
			closePosition(ticker, position, "Ликвидация")
		}
	}
}

func mapToSlice(stockMap map[string]StockScore) []StockScore {
	slice := make([]StockScore, 0, len(stockMap))
	for _, stock := range stockMap {
		slice = append(slice, stock)
	}

	sort.Slice(slice, func(i, j int) bool {
		return slice[i].TotalWeight > slice[j].TotalWeight
	})
	return slice
}

func calculateTotalPortfolioValue() float64 {
	openPositionsMtx.RLock()
	defer openPositionsMtx.RUnlock()

	var positionsValue float64
	for ticker, pos := range openPositions {
		price, err := fetchPrice(ticker)
		if err != nil {
			log.Printf("Ошибка получения цены для %s при расчете стоимости портфеля, используется последняя известная цена: %.2f", ticker, pos.CurrentPrice)
			price = pos.CurrentPrice
		}
		positionsValue += pos.Shares * price
	}
	return availableFunds + positionsValue
}

func calculateTargetAllocations(whiteZoneStocks []StockScore) map[string]float64 {
	totalPortfolioValue := calculateTotalPortfolioValue()
	log.Printf("Общая стоимость портфеля для аллокации: %.2f", totalPortfolioValue)

	targetAllocations := make(map[string]float64)
	var totalWeight float64
	for _, stock := range whiteZoneStocks {
		totalWeight += stock.TotalWeight
	}

	if totalWeight == 0 {
		log.Println("Суммарный вес акций в белой зоне равен 0. Аллокация невозможна.")
		return targetAllocations
	}

	log.Println("--- Целевые аллокации ---")
	for _, stock := range whiteZoneStocks {
		proportion := stock.TotalWeight / totalWeight
		targetAmount := totalPortfolioValue * proportion
		targetAllocations[stock.Ticker] = targetAmount
		log.Printf("  - %s: %.2f (доля %.2f%%)", stock.Ticker, targetAmount, proportion*100)
	}
	return targetAllocations
}

func executeTrades(targetAllocations map[string]float64, whiteZoneMap map[string]StockScore) {
	for ticker, targetAmount := range targetAllocations {
		stockInfo := whiteZoneMap[ticker]

		openPositionsMtx.RLock()
		position, exists := openPositions[ticker]
		openPositionsMtx.RUnlock()

		currentAmount := 0.0
		if exists {
			price, err := fetchPrice(ticker)
			if err != nil {
				log.Printf("Ошибка получения цены для %s при исполнении сделки: %v. Пропуск.", ticker, err)
				continue
			}
			currentAmount = position.Shares * price
		}

		delta := targetAmount - currentAmount
		log.Printf("Анализ %s: Цель %.2f, Текущая %.2f, Дельта %.2f", ticker, targetAmount, currentAmount, delta)

		if math.Abs(delta) < config.MinTransactionAmount {
			log.Printf("Сделка по %s пропущена: дельта (%.2f) меньше минимального порога (%.2f)", ticker, delta, config.MinTransactionAmount)
			continue
		}

		if !isSignificantTrend(stockInfo.Trend) {
			log.Printf("Сделка по %s пропущена: тренд не является сильным (Изменение: %.2f%%, Длительность: %s)",
				ticker, stockInfo.Trend.ChangePercent, formatDuration(stockInfo.Trend.Duration))
			continue
		}

		if delta > 0 {
			if !exists {
				log.Printf("Новая покупка %s на сумму %.2f", ticker, targetAmount)
				openPosition(ticker, targetAmount)
			} else {
				log.Printf("Докупка %s на сумму %.2f", ticker, delta)
				adjustPosition(ticker, position, delta)
			}
		} else if delta < 0 {
			if exists {
				log.Printf("Частичная продажа %s на сумму %.2f", ticker, math.Abs(delta))
				adjustPosition(ticker, position, delta)
			}
		}
	}
}

func logZone(zoneName string, zoneMap map[string]StockScore) {
	if len(zoneMap) == 0 {
		log.Printf("%s пуста.", zoneName)
		return
	}

	tickers := make([]string, 0, len(zoneMap))
	for ticker := range zoneMap {
		tickers = append(tickers, ticker)
	}
	sort.Strings(tickers)

	log.Printf("%s: %d акций (%s)", zoneName, len(tickers), strings.Join(tickers, ", "))
}

// --- ФУНКЦИИ УПРАВЛЕНИЯ ПОЗИЦИЯМИ ---

func openPosition(ticker string, amountToInvest float64) {
	price, err := fetchPrice(ticker)
	if err != nil {
		log.Printf("Ошибка получения цены для открытия %s: %v", ticker, err)
		return
	}
	if price == 0 {
		log.Printf("Не удалось получить цену для %s, открытие позиции отменено.", ticker)
		return
	}

	moneyForShares := amountToInvest / (1 + config.CommissionRate)
	commission := moneyForShares * config.CommissionRate
	totalCost := moneyForShares + commission

	if totalCost > availableFunds {
		log.Printf("Недостаточно средств для открытия %s. Требуется %.2f, доступно %.2f", ticker, totalCost, availableFunds)
		moneyForShares = availableFunds / (1 + config.CommissionRate)
		totalCost = availableFunds
		if moneyForShares <= 0 {
			return
		}
	}

	sharesToBuy := moneyForShares / price
	availableFunds -= totalCost

	pos := Position{
		Ticker:         ticker,
		EntryTime:      time.Now().UTC(),
		Shares:         sharesToBuy,
		AllocatedMoney: moneyForShares,
		AveragePrice:   price,
		CurrentPrice:   price,
		Strategy:       "whitezone",
	}

	openPositionsMtx.Lock()
	openPositions[ticker] = pos
	openPositionsMtx.Unlock()

	log.Printf("ОТКРЫТА позиция %s: %.2f акций по %.2f на сумму %.2f (комиссия %.2f)",
		ticker, sharesToBuy, price, moneyForShares, commission)
	sendTelegram(tgbotapi.NewMessage(config.TelegramChatID,
		fmt.Sprintf("📈 ПОКУПКА %s\nКол-во: %.4f\nЦена: %.2f\nСумма: %.2f", ticker, sharesToBuy, price, moneyForShares)))

	if err := positionRepo.SavePosition(context.Background(), pos); err != nil {
		log.Printf("Ошибка сохранения новой позиции %s в БД: %v", ticker, err)
	}
}

func adjustPosition(ticker string, pos Position, deltaAmount float64) {
	price, err := fetchPrice(ticker)
	if err != nil {
		log.Printf("Ошибка получения цены для корректировки %s: %v", ticker, err)
		return
	}
	if price == 0 {
		log.Printf("Не удалось получить цену для %s, корректировка отменена.", ticker)
		return
	}

	if deltaAmount > 0 { // Покупаем
		moneyForShares := deltaAmount / (1 + config.CommissionRate)
		commission := moneyForShares * config.CommissionRate
		totalCost := moneyForShares + commission

		if totalCost > availableFunds {
			log.Printf("Недостаточно средств для докупки %s. Требуется %.2f, доступно %.2f", ticker, totalCost, availableFunds)
			moneyForShares = availableFunds / (1 + config.CommissionRate)
			totalCost = availableFunds
			if moneyForShares <= 0 {
				return
			}
		}

		sharesToBuy := moneyForShares / price
		availableFunds -= totalCost

		newTotalAllocated := pos.AllocatedMoney + moneyForShares
		newTotalShares := pos.Shares + sharesToBuy
		pos.AveragePrice = (pos.AllocatedMoney*pos.AveragePrice + moneyForShares*price) / newTotalAllocated
		pos.AllocatedMoney = newTotalAllocated
		pos.Shares = newTotalShares
		pos.CurrentPrice = price

		log.Printf("ДОКУПЛЕНО %s: %.2f акций по %.2f на сумму %.2f (комиссия %.2f)",
			ticker, sharesToBuy, price, moneyForShares, commission)
		sendTelegram(tgbotapi.NewMessage(config.TelegramChatID,
			fmt.Sprintf("📈 ДОКУПКА %s\nКол-во: %.4f\nЦена: %.2f\nСумма: %.2f", ticker, sharesToBuy, price, moneyForShares)))

	} else { // Продаем
		amountToGet := math.Abs(deltaAmount)
		sharesToSell := amountToGet / price

		if sharesToSell >= pos.Shares {
			log.Printf("Корректировка %s требует продажи %.2f акций, но в наличии только %.2f. Продаем все.", ticker, sharesToSell, pos.Shares)
			openPositionsMtx.Lock()
			closePosition(ticker, pos, "Ребалансировка (продажа излишка)")
			openPositionsMtx.Unlock()
			return
		}

		grossProceeds := sharesToSell * price
		commission := grossProceeds * config.CommissionRate
		netProceeds := grossProceeds - commission
		availableFunds += netProceeds

		freedAllocatedMoney := (sharesToSell / pos.Shares) * pos.AllocatedMoney
		pos.Shares -= sharesToSell
		pos.AllocatedMoney -= freedAllocatedMoney
		pos.CurrentPrice = price

		log.Printf("ЧАСТИЧНО ПРОДАНО %s: %.2f акций по %.2f. Получено %.2f (комиссия %.2f)",
			ticker, sharesToSell, price, netProceeds, commission)
		sendTelegram(tgbotapi.NewMessage(config.TelegramChatID,
			fmt.Sprintf("📉 ПРОДАЖА %s\nКол-во: %.4f\nЦена: %.2f\nСумма: %.2f", ticker, sharesToSell, price, grossProceeds)))
	}

	openPositionsMtx.Lock()
	openPositions[ticker] = pos
	openPositionsMtx.Unlock()

	if err := positionRepo.UpdatePosition(context.Background(), pos); err != nil {
		log.Printf("Ошибка обновления позиции %s в БД: %v", ticker, err)
	}
}

// closePosition закрывает позицию и обновляет баланс. Должна вызываться из Lock-секции.
func closePosition(ticker string, pos Position, reason string) {
	price, err := fetchPrice(ticker)
	if err != nil {
		log.Printf("Ошибка получения цены для закрытия %s, используется средняя цена входа: %v", ticker, err)
		price = pos.AveragePrice
	}

	grossProceeds := pos.Shares * price
	commission := grossProceeds * config.CommissionRate
	netProceeds := grossProceeds - commission
	realizedPL := netProceeds - pos.AllocatedMoney
	profitPercent := 0.0
	if pos.AllocatedMoney > 0 {
		profitPercent = realizedPL / pos.AllocatedMoney * 100
	}

	availableFunds += netProceeds

	pos.ExitPrice = price
	pos.ExitTime = time.Now().UTC()
	pos.ProfitPercent = profitPercent

	closedPositionsMtx.Lock()
	closedPositions = append(closedPositions, pos)
	closedPositionsMtx.Unlock()

	delete(openPositions, ticker)

	log.Printf("ЗАКРЫТА позиция %s: %.2f акций по %.2f. P/L: %.2f (%.2f%%). Причина: %s",
		ticker, pos.Shares, price, realizedPL, profitPercent, reason)
	sendTelegram(tgbotapi.NewMessage(config.TelegramChatID,
		fmt.Sprintf("🔴 ПРОДАЖА (полная) %s\nПричина: %s\nP/L: %.2f (%.2f%%)", ticker, reason, realizedPL, profitPercent)))

	if err := positionRepo.ClosePosition(context.Background(), ticker, pos); err != nil {
		log.Printf("Ошибка закрытия позиции %s в БД: %v", ticker, err)
	}
}

// --- КОНЕЦ НОВОЙ ЛОГИКИ ---

// --- АНАЛИЗ ТРЕНДОВ И АКЦИЙ ---
func AnalyzeTrend(ticker string) (Trend, error) {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	analysisPeriod := time.Duration(config.AnalysisPeriodMinutes) * time.Minute
	data, err := dbStorage.GetHistoricalData(ctx, ticker, analysisPeriod)
	if err != nil {
		return Trend{}, fmt.Errorf("historical data error: %w", err)
	}

	lastSnapshotCountMtx.Lock()
	currentCount := len(data)
	lastCount, exists := lastSnapshotCount[ticker]
	if !exists || lastCount != currentCount {
		lastSnapshotCount[ticker] = currentCount
	}
	lastSnapshotCountMtx.Unlock()

	if len(data) < config.MinDataPoints {
		var dur time.Duration
		if len(data) > 0 {
			dur = data[len(data)-1].Timestamp.Sub(data[0].Timestamp)
		}
		return Trend{Ticker: ticker, ChangePercent: 0, Duration: dur, Timestamp: time.Now().UTC()}, nil
	}

	startTime := data[0].Timestamp
	endTime := data[len(data)-1].Timestamp

	startHoldings, _ := dbStorage.GetHoldingsAtTime(ctx, ticker, startTime)
	endHoldings, _ := dbStorage.GetHoldingsAtTime(ctx, ticker, endTime)

	allInvestors := make(map[InvestorID]bool)
	for id := range startHoldings {
		allInvestors[id] = true
	}
	for id := range endHoldings {
		allInvestors[id] = true
	}

	var participants []Participant
	for id := range allInvestors {
		participants = append(participants, Participant{ID: id, ShareStart: startHoldings[id], ShareEnd: endHoldings[id], ShareChange: endHoldings[id] - startHoldings[id]})
	}

	var totalShareStart, totalShareEnd float64
	for _, share := range startHoldings {
		totalShareStart += share
	}
	for _, share := range endHoldings {
		totalShareEnd += share
	}

	var values []float64
	var timestamps []time.Time
	for _, snapshot := range data {
		values = append(values, snapshot.TotalShare)
		timestamps = append(timestamps, snapshot.Timestamp)
	}

	ewmaValues := calculateEWMA(values, config.EWMAAlpha)
	absChange := ewmaValues[len(ewmaValues)-1] - ewmaValues[0]

	regResult, _ := calculateWeightedLinearRegression(data)

	return Trend{
		Ticker:          ticker,
		ChangePercent:   absChange,
		RelativeChange:  0, // Calculation depends on market avg, can be done later
		InvestorsCount:  len(participants),
		Duration:        timestamps[len(timestamps)-1].Sub(timestamps[0]),
		Regression:      regResult,
		AvgChange:       calculateAverageChange(data),
		Consistency:     calculateConsistency(values, ewmaValues),
		Participants:    participants,
		Timestamp:       time.Now().UTC(),
		PortfolioChange: totalShareEnd - totalShareStart,
	}, nil
}

func updateAllPositionsPrices() {
	// Шаг 1: Создаем "снимок" позиций, которые нужно обновить.
	// Используем RLock (чтение), так как мы только читаем список.
	openPositionsMtx.RLock()
	positionsToUpdate := make(map[string]Position, len(openPositions))
	for ticker, pos := range openPositions {
		positionsToUpdate[ticker] = pos
	}
	openPositionsMtx.RUnlock() // Сразу освобождаем мьютекс!

	if len(positionsToUpdate) == 0 {
		log.Println("Нет открытых позиций для обновления цен.")
		return
	}

	var wg sync.WaitGroup
	for ticker, pos := range positionsToUpdate {
		wg.Add(1)
		go func(t string, p Position) {
			defer wg.Done()
			price, err := fetchPrice(t)
			if err != nil {
				log.Printf("Error updating price for %s: %v", t, err)
				return
			}

			// Шаг 2: Блокируем мьютекс только на момент записи.
			openPositionsMtx.Lock()
			defer openPositionsMtx.Unlock()

			// Важно: проверяем, что позиция все еще существует.
			// Ее могли закрыть, пока мы получали цену.
			if currentPos, ok := openPositions[t]; ok {
				currentPos.CurrentPrice = price
				openPositions[t] = currentPos
			}
		}(ticker, pos)
	}

	// Шаг 3: Ждем завершения всех горутин.
	wg.Wait()
	log.Println("Цены для всех открытых позиций обновлены.")
}

func CalculateBestStocks(profiles []InvestorProfile) []StockScore {
	stockData := make(map[string]*StockScore)
	totalInvestors := len(profiles)

	for _, profile := range profiles {
		timeWeight := calculateTimeWeight(profile.LastUpdated)
		for _, asset := range profile.Holdings {
			processHolding(profile, asset, stockData, timeWeight)
		}
	}
	normalizeConfidence(stockData, totalInvestors)
	addTrendAnalysis(stockData)
	return sortResults(stockData)
}

func processHolding(profile InvestorProfile, asset Asset, stockData map[string]*StockScore, timeWeight float64) {
	// <<< ИЗМЕНЕНИЕ: Преобразуем имя в тикер >>>
	ticker, ok := stocks[asset.Name]
	if !ok {
		log.Printf("Предупреждение: тикер для '%s' не найден в справочнике. Актив будет проигнорирован.", asset.Name)
		return
	}

	weight := float64(profile.Capital) * (asset.Percent / 100) * timeWeight * profile.SuccessRate
	if data, exists := stockData[ticker]; exists {
		data.TotalWeight += weight
		data.Confidence += profile.SuccessRate
		if !data.investorSet[profile.ID] {
			data.TotalCapital += profile.Capital
			data.investorSet[profile.ID] = true
			data.InvestorsCount = len(data.investorSet)
			data.Investors = append(data.Investors, InvestorInfo{
				ID: profile.ID, Share: asset.Percent, Capital: profile.Capital, LastUpdated: profile.LastUpdated,
			})
		}
	} else {
		stockData[ticker] = &StockScore{
			Ticker:         ticker, // Используем найденный тикер
			TotalWeight:    weight,
			Confidence:     profile.SuccessRate,
			TotalCapital:   profile.Capital,
			InvestorsCount: 1,
			Investors: []InvestorInfo{{
				ID: profile.ID, Share: asset.Percent, Capital: profile.Capital, LastUpdated: profile.LastUpdated,
			}},
			investorSet: map[InvestorID]bool{profile.ID: true},
		}
	}
}

func calculateTimeWeight(lastUpdated time.Time) float64 {
	timeFactor := time.Since(lastUpdated).Hours() / 24
	weight := 1.0 - (timeFactor / float64(config.HistoryDays))
	return math.Max(weight, 0)
}

func normalizeConfidence(stockData map[string]*StockScore, totalInvestors int) {
	if totalInvestors > 0 {
		for _, data := range stockData {
			data.Confidence = data.Confidence / float64(totalInvestors)
		}
	}
}

func addTrendAnalysis(stockData map[string]*StockScore) {
	var wg sync.WaitGroup
	sem := make(chan struct{}, maxConcurrentTrendTasks)

	for ticker := range stockData {
		wg.Add(1)
		sem <- struct{}{}
		go func(t string) {
			defer wg.Done()
			defer func() { <-sem }()
			trend, err := AnalyzeTrend(t)
			if err != nil {
				log.Printf("Ошибка анализа тренда для %s: %v", t, err)
			}
			stockData[t].Trend = trend
		}(ticker)
	}
	wg.Wait()
}

func sortResults(stockData map[string]*StockScore) []StockScore {
	result := make([]StockScore, 0, len(stockData))
	for _, data := range stockData {
		if len(data.Investors) > 0 {
			var sum float64
			for _, inv := range data.Investors {
				if rate, ok := config.SuccessRates[strings.ToLower(string(inv.ID))]; ok {
					sum += rate
				}
			}
			data.AvgSuccessRate = sum / float64(len(data.Investors))
		}
		result = append(result, *data)
	}
	sort.Slice(result, func(i, j int) bool {
		return result[i].TotalWeight > result[j].TotalWeight
	})
	return result
}

func isExcluded(ticker string) bool {
	for _, excluded := range config.ExcludedStocks {
		if strings.EqualFold(ticker, excluded) {
			return true
		}
	}
	return false
}

// --- ОТЧЕТНОСТЬ И ВЗАИМОДЕЙСТВИЕ С TELEGRAM ---
func formatBalance() string {
	openPositionsMtx.RLock()
	defer openPositionsMtx.RUnlock()

	var sb strings.Builder
	var totalInvested float64
	var currentPositionsValue float64

	for _, pos := range openPositions {
		totalInvested += pos.AllocatedMoney
		currentPositionsValue += pos.Shares * pos.CurrentPrice
	}

	unrealizedPL := currentPositionsValue - totalInvested

	totalPortfolioValue := availableFunds + currentPositionsValue

	totalIncome := totalPortfolioValue - initialBudget
	totalIncomePercent := 0.0
	if initialBudget > 0 {
		totalIncomePercent = totalIncome / initialBudget * 100
	}

	sb.WriteString("<b>💰 Баланс и доходность портфеля</b>\n\n")
	sb.WriteString(fmt.Sprintf("Начальный капитал: <code>%.2f</code>\n", initialBudget))
	sb.WriteString(fmt.Sprintf("Текущая стоимость: <code>%.2f</code>\n", totalPortfolioValue))
	sb.WriteString("--------------------------------\n")
	sb.WriteString(fmt.Sprintf("<b>Общий доход:</b> <code>%.2f (%.2f%%)</code>\n", totalIncome, totalIncomePercent))
	sb.WriteString(fmt.Sprintf("<b>Нереализованный P/L:</b> <code>%.2f</code>\n", unrealizedPL))
	sb.WriteString("--------------------------------\n")
	sb.WriteString(fmt.Sprintf("Инвестировано в акции: <code>%.2f</code>\n", totalInvested))
	sb.WriteString(fmt.Sprintf("Свободные средства: <code>%.2f</code>\n", availableFunds))
	sb.WriteString("\n")

	sb.WriteString("<b>📊 Открытые позиции:</b>\n")
	if len(openPositions) == 0 {
		sb.WriteString("Нет открытых позиций.\n")
	} else {
		sb.WriteString(fmt.Sprintf("<code>%-10s %-12s %-12s %-12s %-8s</code>\n", "Тикер", "Инвест.", "Стоимость", "P/L", "P/L %"))
		sb.WriteString("<code>" + strings.Repeat("-", 60) + "</code>\n")

		var sortedPositions []Position
		for _, pos := range openPositions {
			sortedPositions = append(sortedPositions, pos)
		}
		sort.Slice(sortedPositions, func(i, j int) bool {
			return sortedPositions[i].Ticker < sortedPositions[j].Ticker
		})

		for _, pos := range sortedPositions {
			currentValue := pos.Shares * pos.CurrentPrice
			pl := currentValue - pos.AllocatedMoney
			plPercent := 0.0
			if pos.AllocatedMoney > 0 {
				plPercent = pl / pos.AllocatedMoney * 100
			}
			sb.WriteString(fmt.Sprintf("<code>%-10s %-12.2f %-12.2f %-12.2f %-8.2f%%</code>\n",
				pos.Ticker, pos.AllocatedMoney, currentValue, pl, plPercent))
		}
	}

	return sb.String()
}

func formatOpenPositions() string {
	openPositionsMtx.RLock()
	defer openPositionsMtx.RUnlock()

	var sb strings.Builder
	sb.WriteString("<b>📊 Открытые позиции</b>\n\n")

	if len(openPositions) == 0 {
		sb.WriteString("🔹 Нет открытых позиций.\n")
	} else {
		sb.WriteString(fmt.Sprintf("%-12s %-16s %-12s %-12s %-10s\n",
			"Тикер", "Вход", "Инвест.", "Нереал. PL", "Доходн."))
		sb.WriteString(strings.Repeat("-", 70) + "\n")

		var sortedPositions []Position
		for _, pos := range openPositions {
			sortedPositions = append(sortedPositions, pos)
		}
		sort.Slice(sortedPositions, func(i, j int) bool {
			return sortedPositions[i].Ticker < sortedPositions[j].Ticker
		})

		for _, pos := range sortedPositions {
			entryTime := pos.EntryTime.Add(7 * time.Hour).Format("02.01 15:04")
			currentValue := pos.Shares * pos.CurrentPrice
			unrealizedPL := currentValue - pos.AllocatedMoney
			unrealizedPLPercent := 0.0
			if pos.AllocatedMoney > 0 {
				unrealizedPLPercent = unrealizedPL / pos.AllocatedMoney * 100
			}
			sb.WriteString(fmt.Sprintf("%-12s %-16s %-12.2f %-12.2f %-10.2f%%\n",
				pos.Ticker, entryTime, pos.AllocatedMoney, unrealizedPL, unrealizedPLPercent))
		}
	}

	return sb.String()
}

func formatClosedPositions() string {
	closedPositionsMtx.RLock()
	defer closedPositionsMtx.RUnlock()
	if len(closedPositions) == 0 {
		return "🔹 Закрытых позиций нет."
	}
	var sb strings.Builder
	sb.WriteString("<b>📊 Закрытые позиции</b>\n\n")
	sb.WriteString(fmt.Sprintf("%-10s %-16s %-16s %-10s %-12s\n", "Тикер", "Вход", "Выход", "Длит.", "Доходн."))
	sb.WriteString(strings.Repeat("-", 70) + "\n")
	for _, pos := range closedPositions {
		entryTime := pos.EntryTime.Add(7 * time.Hour).Format("02.01 15:04")
		exitTime := pos.ExitTime.Add(7 * time.Hour).Format("02.01 15:04")
		duration := formatDuration(pos.ExitTime.Sub(pos.EntryTime))
		sb.WriteString(fmt.Sprintf("%-10s %-16s %-16s %-10s %-12.2f%%\n",
			pos.Ticker, entryTime, exitTime, duration, pos.ProfitPercent))
	}
	return sb.String()
}

func sendLongMessage(chatID int64, text string, parseMode string) {
	const maxMessageLength = 4000
	lines := strings.Split(text, "\n")
	var chunk strings.Builder
	for _, line := range lines {
		if chunk.Len()+len(line)+1 > maxMessageLength {
			msg := tgbotapi.NewMessage(chatID, fmt.Sprintf("<pre>%s</pre>", chunk.String()))
			msg.ParseMode = parseMode
			sendTelegram(msg)
			chunk.Reset()
		}
		chunk.WriteString(line + "\n")
	}
	if chunk.Len() > 0 {
		msg := tgbotapi.NewMessage(chatID, fmt.Sprintf("<pre>%s</pre>", chunk.String()))
		msg.ParseMode = parseMode
		sendTelegram(msg)
	}
}

func listenTelegramCommands() {
	defer func() {
		if r := recover(); r != nil {
			log.Printf("Recovered in listenTelegramCommands: %v", r)
			go listenTelegramCommands()
		}
	}()
	u := tgbotapi.NewUpdate(0)
	u.Timeout = telegramCommandTimeout
	updates := telegramBot.GetUpdatesChan(u)
	for update := range updates {
		if update.Message == nil {
			continue
		}
		if update.Message.IsCommand() {
			handleCommand(update)
		} else {
			handleNonCommand(update)
		}
	}
}

func handleCommand(update tgbotapi.Update) {
	switch update.Message.Command() {
	case "range":
		rankingMessageMtx.RLock()
		msgText := rankingMessage
		rankingMessageMtx.RUnlock()
		if msgText == "" {
			msgText = "Ранжированный отчёт пока недоступен."
		}
		sendLongMessage(update.Message.Chat.ID, msgText, "HTML")
	case "status":
		sendLongMessage(update.Message.Chat.ID, formatOpenPositions(), "HTML")
	case "closed":
		closedPositionsMtx.RLock()
		msgText := formatClosedPositions()
		closedPositionsMtx.RUnlock()
		if msgText == "" {
			msgText = "Нет закрытых позиций."
		}
		sendLongMessage(update.Message.Chat.ID, msgText, "HTML")
	case "balance":
		sendLongMessage(update.Message.Chat.ID, formatBalance(), "HTML")
	case "screenshot":
		args := strings.Fields(update.Message.CommandArguments())
		if len(args) < 1 {
			msg := tgbotapi.NewMessage(update.Message.Chat.ID, "Пожалуйста, укажите URL для скриншота. Например: /screenshot https://example.com")
			sendTelegram(msg)
			return
		}
		url := args[0]
		err := captureScreenshot(url, update.Message.Chat.ID)
		if err != nil {
			msg := tgbotapi.NewMessage(update.Message.Chat.ID, "Ошибка при создании скриншота: "+err.Error())
			sendTelegram(msg)
		}
	case "help":
		helpText := `Доступные команды:
/range - Ранжированный список акций
/status - Список открытых позиций
/balance - Баланс портфеля
/closed - Список закрытых позиций
/help - Справка
<номер> - Детали акции из списка /range`
		msg := tgbotapi.NewMessage(update.Message.Chat.ID, helpText)
		sendTelegram(msg)
	default:
		msg := tgbotapi.NewMessage(update.Message.Chat.ID, "Используйте /range, /status, /balance, /closed или /help")
		sendTelegram(msg)
	}
}

func handleNonCommand(update tgbotapi.Update) {
	text := strings.TrimSpace(update.Message.Text)
	if num, err := strconv.Atoi(text); err == nil {
		rankingResultsMtx.RLock()
		total := len(rankingResults)
		if num < 1 || num > total {
			rankingResultsMtx.RUnlock()
			reply := fmt.Sprintf("Неверный номер ранга. Введите число от 1 до %d", total)
			msg := tgbotapi.NewMessage(update.Message.Chat.ID, reply)
			sendTelegram(msg)
			return
		}
		stock := rankingResults[num-1]
		rankingResultsMtx.RUnlock()

		var sb strings.Builder
		sb.WriteString(fmt.Sprintf("📊 <b>%s</b>\n", stock.Ticker))
		sb.WriteString(fmt.Sprintf("Суммарный вес: %.2f\n", stock.TotalWeight))
		sb.WriteString(fmt.Sprintf("Уверенность: %.1f%% (%d)\n", stock.Confidence*100, stock.InvestorsCount))
		sb.WriteString(fmt.Sprintf("Изменение тренда: %+0.2f%%\n", stock.Trend.ChangePercent))
		sb.WriteString(fmt.Sprintf("Согласованность тренда: %.2f\n", stock.Trend.Consistency))
		sb.WriteString(fmt.Sprintf("Продолжительность тренда: %s\n", formatDuration(stock.Trend.Duration)))
		sb.WriteString(fmt.Sprintf("Средняя успешность: %.1f%%\n", stock.AvgSuccessRate*100))
		sb.WriteString(fmt.Sprintf("Общий капитал: %d\n", stock.TotalCapital))
		sb.WriteString("\nДетали тренда:\n")
		sb.WriteString(formatTrendDetails(stock.Trend))
		msg := tgbotapi.NewMessage(update.Message.Chat.ID, sb.String())
		msg.ParseMode = "HTML"
		sendTelegram(msg)
	} else {
		msg := tgbotapi.NewMessage(update.Message.Chat.ID, "Пожалуйста, введите номер акции из списка /range или команду (например, /help).")
		sendTelegram(msg)
	}
}

func formatTrendDetails(trend Trend) string {
	var sb strings.Builder
	if trend.Duration == 0 {
		sb.WriteString("Нет подробного анализа для этого тикера (недостаточно данных или незначительный тренд).\n")
		return sb.String()
	}
	sb.WriteString(fmt.Sprintf("Регрессия:\n  Перехват: %.2f\n  Наклон: %.4f\n  R²: %.2f\n\n", trend.Regression.Intercept, trend.Regression.Slope, trend.Regression.RSquared))
	sb.WriteString(fmt.Sprintf("Сравнение средних:\n  Первая половина: %.2f\n  Вторая половина: %.2f\n\n", trend.AvgChange.FirstHalfAvg, trend.AvgChange.SecondHalfAvg))
	sb.WriteString(fmt.Sprintf("Изменение портфеля: %+0.2f%%\n", trend.PortfolioChange))
	sb.WriteString("Участники и их изменения:\n")
	for _, p := range trend.Participants {
		sb.WriteString(fmt.Sprintf("• %s: %.2f%% → %.2f%% (изменение: %+0.2f%%)\n",
			p.ID, p.ShareStart, p.ShareEnd, p.ShareChange))
	}
	return sb.String()
}

func normalizeWeight(totalWeight float64) float64 {
	return totalWeight / config.BaselineWeight * 100
}

func printAnalysis(stocks []StockScore) {
	var sb strings.Builder
	sb.WriteString("Ранг   Тикер                   Суммарный вес (норм.)    Уверенность (инвесторы)    Тренд\n")
	for i, stock := range stocks {
		if i >= 20 {
			break
		}
		normWeight := normalizeWeight(stock.TotalWeight)
		trendStr := fmt.Sprintf("%+0.2f%% за %s", stock.Trend.ChangePercent, formatDuration(stock.Trend.Duration))
		confStr := fmt.Sprintf("%.1f%% (%d)", stock.Confidence*100, stock.InvestorsCount)
		line := fmt.Sprintf("#%-3d  %-20s  %-12.2f (%-5.1f%%)  %-20s  %-20s",
			i+1, stock.Ticker, stock.TotalWeight, normWeight, confStr, trendStr)
		sb.WriteString(line + "\n")
	}
	result := sb.String()
	rankingMessageMtx.Lock()
	rankingMessage = result
	rankingMessageMtx.Unlock()
	rankingResultsMtx.Lock()
	rankingResults = stocks
	rankingResultsMtx.Unlock()
	log.Println("\n🔎 Результаты анализа:")
	log.Println(result)
}

// --- ПАРСИНГ И РАБОТА С CHROMEDP ---
func fetchProfiles() []InvestorProfile {
	var profiles []InvestorProfile
	var globalFailureCycleInARow int
	for i, url := range config.InvestorURLs {
		investorLock.Lock()
		suspendedUntil, exists := investorSuspendedUntil[url]
		if exists && time.Now().Before(suspendedUntil) {
			investorLock.Unlock()
			log.Printf("Портфель инвестора %s отключён до %v", url, suspendedUntil)
			continue
		}
		investorLock.Unlock()

		if i > 0 {
			log.Printf("Ожидание %d секунд перед следующим профилем...", config.ProfileDelaySeconds)
			time.Sleep(time.Duration(config.ProfileDelaySeconds) * time.Second)
		}

		profile, err := parseInvestorProfile(url)
		if err != nil {
			investorLock.Lock()
			investorFailureCount[url]++
			globalFailureCycleInARow++
			if investorFailureCount[url] >= 2 {
				investorSuspendedUntil[url] = time.Now().Add(3 * time.Hour)
				investorFailureCount[url] = 0
				log.Printf("Портфель инвестора %s не загружался 2 цикла, отключаем на 3 часа", url)
			}
			if globalFailureCycleInARow >= 3 {
				investorLock.Unlock()
				pinCodeLogin(telegramBot, config.TelegramChatID)
				investorLock.Lock()
				for u := range investorFailureCount {
					investorFailureCount[u] = 0
					delete(investorSuspendedUntil, u)
				}
				globalFailureCycleInARow = 0
				investorLock.Unlock()
				select {
				case restartCycle <- struct{}{}:
				default:
				}
				continue
			}
			investorLock.Unlock()
			log.Printf("Ошибка парсинга профиля инвестора с %s: %v", url, err)
			continue
		}

		investorCacheMtx.Lock()
		profile.LastUpdated = time.Now()
		investorCache[profile.ID] = profile
		// log.Printf("Кеш для инвестора %s успешно обновлен.", profile.ID)
		investorCacheMtx.Unlock()

		investorLock.Lock()
		globalFailureCycleInARow = 0
		investorFailureCount[url] = 0
		delete(investorSuspendedUntil, url)
		investorLock.Unlock()
		profiles = append(profiles, profile)
	}
	return profiles
}

func extractInvestorID(url string) InvestorID {
	parts := strings.Split(url, "/")
	var id string
	if len(parts) > 2 {
		if parts[len(parts)-1] == "" && len(parts) >= 3 {
			id = parts[len(parts)-3]
		} else {
			id = parts[len(parts)-2]
		}
	}
	return InvestorID(strings.TrimSpace(id))
}

func parseInvestorProfile(url string) (InvestorProfile, error) {
	html, err := fetchRenderedHTML(url)
	if err != nil {
		return InvestorProfile{}, fmt.Errorf("error fetching rendered HTML for %s: %w", url, err)
	}
	doc, err := goquery.NewDocumentFromReader(strings.NewReader(html))
	if err != nil {
		return InvestorProfile{}, fmt.Errorf("error parsing HTML content from %s: %w", url, err)
	}
	investorID := extractInvestorID(url)
	successRate := getSuccessRate(investorID)
	assets, err := parseAssets(doc)
	if err != nil {
		return InvestorProfile{}, fmt.Errorf("error parsing assets from %s: %w", url, err)
	}
	return InvestorProfile{
		ID:          investorID,
		Capital:     parseCapital(doc),
		Holdings:    assets,
		SuccessRate: successRate,
		LastUpdated: time.Now().UTC(),
	}, nil
}

func fetchRenderedHTML(url string) (string, error) {
	delayAttempts := 7
	var html string
	var err error
	for attempt := 1; attempt <= delayAttempts; attempt++ {
		html, err = attemptFetchRenderedHTML(url)
		if err == nil {
			return html, nil
		}
		waitTime := time.Duration(config.CheckIntervalSeconds / 2)
		log.Printf("Попытка %d/%d --- Повтор через %v...", attempt, delayAttempts, waitTime)
		time.Sleep(waitTime)
	}
	sendLongMessage(config.TelegramChatID, fmt.Sprintf("Не удалось загрузить %s после %d попыток", url, delayAttempts), "HTML")
	return "", fmt.Errorf("не удалось загрузить %s после %d попыток: %s", url, delayAttempts, err)
}

func attemptFetchRenderedHTML(url string) (string, error) {
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()
	opts := append(chromedp.DefaultExecAllocatorOptions[:],
		// chromedp.Flag("headless", false),
		chromedp.Flag("user-data-dir", config.UserDataDir),
		chromedp.Flag("profile-directory", config.ProfileDirectory),
		chromedp.Flag("user-agent", config.UserAgent),
		chromedp.Flag("disable-gpu", false),
		chromedp.Flag("enable-automation", false),
		chromedp.Flag("disable-extensions", false),
	)
	allocCtx, cancelAlloc := chromedp.NewExecAllocator(ctx, opts...)
	defer cancelAlloc()

	cdpCtx, cancelCtx := chromedp.NewContext(
		allocCtx,
		chromedp.WithLogf(func(format string, args ...interface{}) {}),
	)
	defer cancelCtx()

	err := ensureCorrectPage(cdpCtx, url)
	if err != nil {
		return "", fmt.Errorf("ошибка при проверке страницы: %w", err)
	}

	var html string
	err = chromedp.Run(cdpCtx,
		chromedp.WaitVisible(`[data-qa-file="PortfolioAnalyticsContent"]`),
		chromedp.Sleep(2*time.Second),
		chromedp.Click(`button[mentionlabel="Компании"]`),
		chromedp.Click(`button[mentionlabel="Компании"]`),
		chromedp.Click(`button[mentionlabel="Компании"]`),
		chromedp.Sleep(2*time.Second),
		chromedp.OuterHTML("html", &html),
	)
	if err != nil {
		return "", fmt.Errorf("chromedp run error for %s: %w", url, err)
	}
	return html, nil
}

func ensureCorrectPage(cdpCtx context.Context, expectedURL string) error {
	var currentURL string
	err := chromedp.Run(cdpCtx,
		chromedp.Location(&currentURL),
	)
	if err != nil {
		return fmt.Errorf("не удалось получить текущий URL: %w", err)
	}

	if currentURL == expectedURL {
		return nil
	}

	time.Sleep(2 * time.Second)
	err = chromedp.Run(cdpCtx,
		chromedp.Location(&currentURL),
	)
	if err != nil {
		return fmt.Errorf("не удалось получить текущий URL после ожидания: %w", err)
	}

	if currentURL != expectedURL {
		err = chromedp.Run(cdpCtx,
			chromedp.Navigate(expectedURL),
		)
		if err != nil {
			return fmt.Errorf("не удалось перейти на %s: %w", expectedURL, err)
		}
	}

	return nil
}

func pinCodeLogin(bot *tgbotapi.BotAPI, chatID int64) {
	opts := append(chromedp.DefaultExecAllocatorOptions[:],
		// chromedp.Flag("headless", false),
		chromedp.Flag("disable-gpu", true),
		chromedp.Flag("no-sandbox", true),
		chromedp.Flag("user-data-dir", config.UserDataDir),
		chromedp.Flag("profile-directory", config.ProfileDirectory),
		chromedp.Flag("disable-blink-features", "AutomationControlled"),
		chromedp.Flag("user-agent", config.UserAgent),
	)

	allocCtx, cancel := chromedp.NewExecAllocator(context.Background(), opts...)
	defer cancel()
	ctx, cancel := chromedp.NewContext(allocCtx)
	defer cancel()
	ctx, cancel = context.WithTimeout(ctx, 60*time.Second)
	defer cancel()

	err := chromedp.Run(ctx,
		reliableNavigate("https://www.tbank.ru/invest/portfolio/"),
	)
	if err != nil {
		handleError(bot, chatID, "Initial navigation to portfolio failed", err)
		return
	}

	if err := runWithLoadedCookies(ctx); err != nil {
		handleError(bot, chatID, "Cookies error", err)
	}

	err = chromedp.Run(ctx, enterPinCode()...)
	if err != nil {
		handleError(bot, chatID, "PIN code login failed", err)
		return
	}

	if _, err := bot.Send(tgbotapi.NewMessage(chatID, "PIN code login successful.")); err != nil {
		log.Printf("Error sending success message: %v", err)
	}
}

func reliableNavigate(url string) chromedp.Action {
	return chromedp.ActionFunc(func(ctx context.Context) error {
		var attempts int
		for attempts < 3 {
			attempts++
			err := chromedp.Navigate(url).Do(ctx)
			if err == nil {
				return nil
			}
			time.Sleep(1 * time.Second)
		}
		return fmt.Errorf("failed to navigate to %s after %d attempts", url, 3)
	})
}

func handleError(bot *tgbotapi.BotAPI, chatID int64, message string, err error) {
	bot.Send(tgbotapi.NewMessage(chatID, fmt.Sprintf("%s: %v", message, err)))
}

func enterPinCode() []chromedp.Action {
	return []chromedp.Action{
		chromedp.WaitVisible(`#pinCode0`, chromedp.ByQuery),
		chromedp.SendKeys(`#pinCode0`, "2000", chromedp.ByQuery),
		chromedp.Click(`#pinCode0`, chromedp.ByQuery),
		chromedp.Sleep(10 * time.Second),
	}
}

func parseCapital(doc *goquery.Document) int {
	selector := `[data-qa-file="TextValue"]`
	elements := doc.Find(selector)
	if elements.Length() == 0 {
		log.Printf("Ошибка: элементы с селектором %s не найдены", selector)
		return 0
	}
	text := cleanNumberString(elements.First().Text())
	amount, err := strconv.Atoi(text)
	if err != nil {
		log.Printf("Ошибка парсинга капитала из '%s': %v", text, err)
		return 0
	}
	if amount > 10000000 {
		amount /= 10
	}
	if remainder := amount % 10; remainder != 0 {
		amount -= remainder
	}
	return amount
}

func parseAssets(doc *goquery.Document) ([]Asset, error) {
	var assets []Asset
	doc.Find(`[data-qa-file="PieListItem"]`).Each(func(_ int, s *goquery.Selection) {
		name := strings.TrimSpace(s.Find(`[data-qa-tag="PieListItemName"]`).Text())
		percentStr := strings.TrimSpace(s.Find(`[data-qa-tag="PieListItemValue"]`).Text())
		if name == "" || percentStr == "" {
			return
		}
		percentStr = strings.ReplaceAll(percentStr, "%", "")
		percentStr = strings.Replace(percentStr, ",", ".", -1)
		percent, err := strconv.ParseFloat(percentStr, 64)
		if err != nil {
			log.Printf("Warning: parseAssets error for asset %s: %v", name, err)
			return
		}
		assets = append(assets, Asset{Name: name, Percent: percent})
	})
	return assets, nil
}

func cleanNumberString(s string) string {
	var result strings.Builder
	for _, r := range s {
		if unicode.IsDigit(r) {
			result.WriteRune(r)
		}
	}
	return result.String()
}

func getSuccessRate(investorID InvestorID) float64 {
	normalizedID := strings.ToLower(string(investorID))
	if rate, exists := config.SuccessRates[normalizedID]; exists {
		return rate
	}
	return 0.3
}

func captureScreenshot(url string, chatID int64) error {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	opts := append(chromedp.DefaultExecAllocatorOptions[:],
		chromedp.Flag("headless", true),
		chromedp.Flag("user-data-dir", config.UserDataDir),
		chromedp.Flag("profile-directory", config.ProfileDirectory),
	)
	allocCtx, cancelAlloc := chromedp.NewExecAllocator(ctx, opts...)
	defer cancelAlloc()

	cdpCtx, cancelCtx := chromedp.NewContext(allocCtx)
	defer cancelCtx()

	var buf []byte
	err := chromedp.Run(cdpCtx,
		chromedp.Navigate(url),
		chromedp.WaitVisible(`body`, chromedp.ByQuery),
		chromedp.Sleep(2*time.Second),
		chromedp.CaptureScreenshot(&buf),
	)
	if err != nil {
		return fmt.Errorf("ошибка выполнения chromedp: %w", err)
	}

	tmpFile, err := os.CreateTemp("", "screenshot-*.png")
	if err != nil {
		return fmt.Errorf("ошибка создания временного файла: %w", err)
	}
	defer os.Remove(tmpFile.Name())

	_, err = tmpFile.Write(buf)
	if err != nil {
		return fmt.Errorf("ошибка записи во временный файл: %w", err)
	}
	tmpFile.Close()

	photo := tgbotapi.NewPhoto(chatID, tgbotapi.FilePath(tmpFile.Name()))
	photo.Caption = "Скриншот страницы: " + url
	_, err = telegramBot.Send(photo)
	if err != nil {
		return fmt.Errorf("ошибка отправки скриншота: %w", err)
	}

	return nil
}

var stocks = map[string]string{
	"Газпром":               "GAZP",
	"Валюта и Металлы":      "Cash",
	"Т-Капитал":             "TPAY",
	"ВИМ Инвестиции":        "LQDT",
	"Сбер Банк":             "SBER",
	"Novabev group":         "BELU",
	"Т-Технологии":          "T",
	"ВТБ":                   "VTBR",
	"Новатэк":               "NVTK",
	"Норильский никель":     "GMKN",
	"Лукойл":                "LKOH",
	"ГК Самолет":            "SMLT",
	"Аэрофлот":              "AFLT",
	"Яндекс":                "YDEX",
	"Мечел":                 "MTLR",
	"Полюс":                 "PLZL",
	"X5 Retail Group":       "X5",
	"Роснефть":              "ROSN",
	"АФК Система":           "AFKS",
	"Positive Technologies": "POSI",
	"СПБ Биржа":             "SPBE",
	"Магнит":                "MGNT",
	"Селигдар":              "SELG",
	"ВК":                    "VKCO",
	"Московская Биржа":      "MOEX",
	"Сегежа":                "SGZH",
	"НЛМК":                  "NLMK",
	"ПИК-Корпорация":        "PIKK",
	"Северсталь":            "CHMF",
	"АЛРОСА":                "ALRS",
	"Татнефть":              "TATN",
	"ММК":                   "MAGN",
	"РУСАЛ":                 "RUAL",
	"Транснефть":            "TRNFP",
	"HeadHunter Group":      "HEAD",
	"Сургутнефтегаз":        "SNGS",
	"Русснефть":             "RNFT",
	"Юнипро":                "UPRO",
	"Южуралзолото":          "UGLD",
	"Газпром нефть":         "SIBN",
	"ОВК":                   "UWGN",
	"МТС":                   "MTSS",
	"Phosagro":              "PHOR",
	"Русагро":               "RAGR",
	`ПАО "Яковлев"`:         "IRKT",
	"Совкомфлот":            "FLOT",
	"Интер РАО ЕЭС":         "IRAO",
	"РусАгро":               "AGRO",
	"Whoosh":                "WUSH",
	"Совкомбанк":            "SVCB",
	"Ростелеком":            "RTKM",
	"ГТМ":                   "GTRK",
	"ТМК":                   "TRMK",
	"Распадская":            "RASP",
	"ЭсЭфАй":                "SFIN",
	"ЕвроТранс":             "EUTR",
	"Астра":                 "ASTR",
	"Банк Санкт-Петербург":  "BSPB",
	"Фармацевтическая компания ОЗОН": "OZPH",
	"РусГидро":      "HYDR",
	"ОАК":           "UNAC",
	"ДВМП":          "FESH",
	"Россети":       "FEES",
	"ВСМПО-АВИСМА":  "VSMO",
	"Софтлайн":      "SOFL",
	"Novabev Group": "BELU",
	"Европлан":      "LEAS",
	"Аренадата":     "DATA",
	"Киви":          "QIWI",
	"ИНАРКТИКА":     "AQUA",
	"СОЛЛЕРС":       "SVAV",
	"КАМАЗ":         "KMAZ",
	"Промомед":      "PRMD",
	"М.Видео":       "MVID",
	"Мать и дитя":   "MDMG",
	"Ренессанс Страхование": "RENI",
	"НМТП":          "NMTP",
	"ЛСР":           "LSRG",
	"МКБ":           "CBOM",
	"РБК":           "RBCM",
	"Артген":        "ABIO",
	"Башнефть":      "BANE",
	"Мосэнерго":     "MSNG",
	"МТС-Банк":      "MBNK",
	"Русолово":      "ROLO",
	"Лента":         "LENT",
	"Россети Центр": "MRKC",
	"HENDERSON":     "HNFG",
	"Ленэнерго":     "LSNG",
	"Делимобиль":    "DELI",
	"Диасофт":       "DIAS",
	"Россети Центр и Приволжье": "MRKP",
}

func runWithLoadedCookies(ctx context.Context) error {
	data, err := os.ReadFile(cookieFilePath)
	if err != nil {
		return fmt.Errorf("failed to read cookie file: %w", err)
	}

	var loadedCookies []Cookie
	if err := json.Unmarshal(data, &loadedCookies); err != nil {
		return fmt.Errorf("failed to parse cookies: %w", err)
	}
	log.Printf("Loaded %d cookies from %s", len(loadedCookies), cookieFilePath)

	expr := cdp.TimeSinceEpoch(time.Now().Add(180 * 24 * time.Hour))

	err = chromedp.Run(ctx,
		chromedp.ActionFunc(func(ctx context.Context) error {
			for _, c := range loadedCookies {
				err := network.SetCookie(c.Name, c.Value).
					WithDomain(c.Domain).
					WithPath(c.Path).
					WithExpires(&expr).
					WithHTTPOnly(c.HTTPOnly).
					WithSecure(c.Secure).
					Do(ctx)
				if err != nil {
					return fmt.Errorf("failed to set cookie: %w", err)
				}
			}
			log.Println("Cookies successfully set.")
			return nil
		}),
		chromedp.Navigate("https://www.tbank.ru/invest/portfolio/"),
		chromedp.ActionFunc(func(ctx context.Context) error {
			_, err := network.GetCookies().Do(ctx)
			if err != nil {
				return err
			}
			return nil
		}),
	)

	return err
}

func isMarketOpen() bool {
	now := time.Now()
	// Московское время UTC+3. Биржа работает с 05:50 до 18:45 (основная сессия) или до 23:50 (вечерняя)
	// Для простоты берем с запасом 06:00 UTC - 24:00 UTC
	loc, _ := time.LoadLocation("Europe/Moscow")
	nowMsk := now.In(loc)
	hour := nowMsk.Hour()
	return hour >= 6 && hour < 24
}
