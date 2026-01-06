package main

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/chromedp/chromedp"
	tgbotapi "github.com/go-telegram-bot-api/telegram-bot-api/v5"
	"github.com/sirupsen/logrus"
)

const (
	phoneInputSelector    = `input[name="phone"]`
	submitButtonSelector  = `button[type="submit"]`
	otpInputSelector      = `input[name="otp"]`
	passwordInputSelector = `input[name="password"]`
	pinCodeInputSelector  = `#pinCode0`
	pinCodeSubmitSelector = `button[automation-id="button-submit"]`
	resendButtonSelector  = `div._Content_1c73l_108`
	loginURL              = "https://www.tbank.ru/auth/login/?redirectTo=/invest/portfolio/"
	maxNavigationAttempts = 5
	maxElementAttempts    = 5
	elementTimeout        = 10 * time.Second
	otpTimeout            = 90 * time.Second
)

var (
	browserMutex      sync.Mutex
	logger            *logrus.Logger
	bot               *tgbotapi.BotAPI
	chatID            int64 = 1443661636 // Замените на ваш Telegram Chat ID
	currentLoginState *LoginState
	stateMutex        sync.Mutex
)

// LoginState хранит текущее состояние процесса логина
type LoginState struct {
	State           string
	OTPChan         chan string
	PINChan         chan string
	ResendAvailable bool
	Ctx             context.Context
}

func main() {
	initLogger()
	var err error
	bot, err = tgbotapi.NewBotAPI("") // Замените на ваш токен
	if err != nil {
		logger.Fatalf("Не удалось создать Telegram-бот: %v", err)
	}
	u := tgbotapi.NewUpdate(0)
	u.Timeout = 60
	updates := bot.GetUpdatesChan(u)

	go fullLogin(bot, chatID)

	// Обработка обновлений Telegram
	for update := range updates {
		if update.Message == nil || update.Message.Text == "" || update.Message.Chat.ID != chatID {
			continue
		}
		text := update.Message.Text
		stateMutex.Lock()
		state := currentLoginState
		stateMutex.Unlock()

		if state != nil {
			if state.State == "Waiting for OTP" && len(text) == 4 && isNumeric(text) {
				state.OTPChan <- text
			} else if state.State == "Waiting for PIN" && len(text) == 4 && isNumeric(text) {
				state.PINChan <- text
			} else if text == "/info" {
				if state.Ctx != nil {
					var screenshot []byte
					err := chromedp.Run(state.Ctx, chromedp.CaptureScreenshot(&screenshot))
					if err == nil {
						bot.Send(tgbotapi.NewPhoto(chatID, tgbotapi.FileBytes{Name: "screenshot.png", Bytes: screenshot}))
					} else {
						logger.Errorf("Ошибка при захвате скриншота: %v", err)
					}
					msg := fmt.Sprintf("Текущее состояние: %s\nКнопка 'Отправить еще раз' доступна: %t", state.State, state.ResendAvailable)
					bot.Send(tgbotapi.NewMessage(chatID, msg))
				} else {
					bot.Send(tgbotapi.NewMessage(chatID, "Нет активной сессии логина."))
				}
			} else {
				bot.Send(tgbotapi.NewMessage(chatID, "Неожиданное сообщение."))
			}
		}
	}
}

func initLogger() {
	logger = logrus.New()
	logger.SetFormatter(&logrus.TextFormatter{FullTimestamp: true})
	logger.SetOutput(os.Stdout)
	logger.SetLevel(logrus.InfoLevel)
}

func fullLogin(bot *tgbotapi.BotAPI, chatID int64) {
	browserMutex.Lock()
	defer browserMutex.Unlock()

	logger.Info("Запуск полного процесса логина")
	opts := append(chromedp.DefaultExecAllocatorOptions[:],
		chromedp.Flag("user-data-dir", getChromeDataDir()),
		chromedp.Flag("headless", false),
		chromedp.Flag("disable-gpu", false),
		chromedp.Flag("enable-automation", false),
		chromedp.Flag("disable-extensions", false),
	)
	allocCtx, cancel := chromedp.NewExecAllocator(context.Background(), opts...)
	defer cancel()
	ctx, cancel := chromedp.NewContext(allocCtx)
	defer cancel()
	ctx, cancel = context.WithTimeout(ctx, 300*time.Second) // Увеличен таймаут для полного процесса
	defer cancel()

	// Инициализация состояния
	state := &LoginState{
		State: "Navigating to login page",
		Ctx:   ctx,
	}
	stateMutex.Lock()
	currentLoginState = state
	stateMutex.Unlock()

	defer func() {
		stateMutex.Lock()
		currentLoginState = nil
		stateMutex.Unlock()
	}()

	// Навигация на страницу логина
	err := chromedp.Run(ctx,
		reliableNavigate(loginURL, chatID, bot),
		chromedp.Sleep(3*time.Second), // Дополнительная задержка для полной загрузки
	)
	if err != nil {
		handleError(bot, chatID, "Ошибка навигации", err)
		return
	}

	// Проверяем наличие поля ввода телефона
	var phoneInputExists bool
	err = chromedp.Run(ctx,
		chromedp.Evaluate(fmt.Sprintf(`document.querySelector('%s') !== null`, phoneInputSelector), &phoneInputExists),
	)
	if err != nil {
		handleError(bot, chatID, "Ошибка проверки наличия поля телефона", err)
		return
	}

	// Если поле ввода телефона существует, вводим номер, иначе нажимаем кнопку "Войти по SMS-коду"
	if phoneInputExists {
		state.State = "Entering phone number"
		err = chromedp.Run(ctx,
			chromedp.WaitVisible(phoneInputSelector, chromedp.ByQuery), // Ожидаем видимость поля телефона
			chromedp.Sleep(2*time.Second),
			chromedp.SendKeys(phoneInputSelector, "номер тут ввести нужно свой, без +7", chromedp.ByQuery), // Добавлен "+" для формата номера
			chromedp.Sleep(2*time.Second),
			chromedp.WaitVisible(submitButtonSelector, chromedp.ByQuery), // Ожидаем видимость кнопки
			chromedp.Click(submitButtonSelector, chromedp.ByQuery),
		)
		if err != nil {
			handleError(bot, chatID, "Ошибка ввода телефона", err)
			return
		}
	} else {
		// Если нет поля ввода телефона, ждем и нажимаем кнопку "Войти по SMS-коду"
		state.State = "Clicking SMS login button"
		err = chromedp.Run(ctx,
			chromedp.WaitVisible(`button[automation-id="button-submit"]`, chromedp.ByQuery),
			chromedp.Click(`button[automation-id="button-submit"]`, chromedp.ByQuery),
		)
		if err != nil {
			handleError(bot, chatID, "Ошибка нажатия кнопки 'Войти по SMS-коду'", err)
			return
		}
	}

	// Ожидание OTP с проверкой кнопки "Отправить еще раз"
	state.OTPChan = make(chan string, 1)
	state.State = "Waiting for OTP"
	bot.Send(tgbotapi.NewMessage(chatID, "Пожалуйста, отправьте OTP:"))

	go func() {
		time.Sleep(60 * time.Second) // Ждем минуту перед проверкой кнопки
		for {
			select {
			case <-ctx.Done():
				return
			default:
				var exists bool
				err := chromedp.Run(ctx, chromedp.Evaluate(fmt.Sprintf(`document.querySelector('%s') !== null`, resendButtonSelector), &exists))
				if err == nil && exists {
					state.ResendAvailable = true
				} else {
					state.ResendAvailable = false
				}
				time.Sleep(5 * time.Second)
			}
		}
	}()

	// Ожидание OTP с автоматическим нажатием "Отправить еще раз"
	const maxResendAttempts = 3
	for attempt := 0; attempt < maxResendAttempts; attempt++ {
		select {
		case otp := <-state.OTPChan:
			state.State = "Entering OTP"
			err = chromedp.Run(ctx,
				chromedp.WaitVisible(otpInputSelector, chromedp.ByQuery),
				chromedp.SendKeys(otpInputSelector, otp, chromedp.ByQuery),
				chromedp.WaitVisible(passwordInputSelector, chromedp.ByQuery),
				chromedp.SendKeys(passwordInputSelector, "пароль от своего аккаунта т-банк", chromedp.ByQuery),
				chromedp.WaitVisible(submitButtonSelector, chromedp.ByQuery),
				chromedp.Click(submitButtonSelector, chromedp.ByQuery),
			)
			if err != nil {
				handleError(bot, chatID, "Ошибка ввода OTP и пароля", err)
				return
			}

			// Ожидание PIN
			state.PINChan = make(chan string, 1)
			state.State = "Waiting for PIN"
			bot.Send(tgbotapi.NewMessage(chatID, "Пожалуйста, отправьте PIN-код:"))

			select {
			case pin := <-state.PINChan:
				state.State = "Entering PIN"
				err = chromedp.Run(ctx,
					chromedp.WaitVisible(pinCodeInputSelector, chromedp.ByQuery),
					chromedp.SendKeys(pinCodeInputSelector, pin, chromedp.ByQuery),
					chromedp.WaitVisible(pinCodeSubmitSelector, chromedp.ByQuery),
					chromedp.Click(pinCodeSubmitSelector, chromedp.ByQuery),
					chromedp.Sleep(10*time.Second),
				)
				if err != nil {
					handleError(bot, chatID, "Ошибка ввода PIN", err)
					return
				}
				state.State = "Logged in"
				logger.Info("Полный логин успешно завершен")
				bot.Send(tgbotapi.NewMessage(chatID, "Полный логин успешно выполнен."))
				return
			case <-time.After(otpTimeout):
				handleError(bot, chatID, "Превышено время ожидания PIN", nil)
				return
			}
		case <-time.After(otpTimeout):
			if state.ResendAvailable {
				err := chromedp.Run(ctx, chromedp.Click(resendButtonSelector, chromedp.ByQuery))
				if err != nil {
					handleError(bot, chatID, "Ошибка при нажатии 'Отправить еще раз'", err)
					return
				}
				logger.Info("Нажата кнопка 'Отправить еще раз'")
				bot.Send(tgbotapi.NewMessage(chatID, "Нажата кнопка 'Отправить еще раз'. Ожидайте новый OTP."))
			} else {
				handleError(bot, chatID, "Кнопка 'Отправить еще раз' не доступна", nil)
				return
			}
		}
	}
	handleError(bot, chatID, "Превышено максимальное количество попыток отправки OTP", nil)
}

func logPageContent(ctx context.Context) {
	var pageText string
	err := chromedp.Run(ctx,
		chromedp.Text(`body`, &pageText, chromedp.ByQuery),
	)
	if err != nil {
		logger.Errorf("Не удалось извлечь текст страницы: %v", err)
		return
	}
	cleanedText := strings.TrimSpace(pageText)
	logger.Infof("Содержимое страницы в момент застревания:\n---\n%s\n---", cleanedText)
}

func reliableNavigate(url string, chatID int64, bot *tgbotapi.BotAPI) chromedp.Action {
	return chromedp.ActionFunc(func(ctx context.Context) error {
		for attempts := 1; attempts <= maxNavigationAttempts; attempts++ {
			err := chromedp.Navigate(url).Do(ctx)
			if err == nil {
				logger.Infof("Успешная навигация на %s с попытки %d", url, attempts)
				return nil
			}
			logger.Warnf("Попытка навигации %d на %s провалилась: %v", attempts, url, err)
			time.Sleep(2 * time.Second)
		}
		return fmt.Errorf("не удалось перейти на %s после %d попыток", url, maxNavigationAttempts)
	})
}

func handleError(bot *tgbotapi.BotAPI, chatID int64, message string, err error) {
	logger.Errorf("%s: %v", message, err)
	bot.Send(tgbotapi.NewMessage(chatID, fmt.Sprintf("%s: %v", message, err)))
}

func enterPinCode(chatID int64, bot *tgbotapi.BotAPI, updates tgbotapi.UpdatesChannel) []chromedp.Action {
	return []chromedp.Action{
		chromedp.WaitVisible(pinCodeInputSelector, chromedp.ByQuery),
		chromedp.ActionFunc(func(ctx context.Context) error {
			bot.Send(tgbotapi.NewMessage(chatID, "Пожалуйста, отправьте PIN-код:"))
			pin, err := waitForPin(bot, chatID, updates)
			if err != nil {
				return fmt.Errorf("ошибка получения PIN: %v", err)
			}
			logger.Infof("Ввод PIN: %s", pin)
			return chromedp.SendKeys(pinCodeInputSelector, pin, chromedp.ByQuery).Do(ctx)
		}),
		chromedp.WaitVisible(pinCodeSubmitSelector, chromedp.ByQuery),
		chromedp.Click(pinCodeSubmitSelector, chromedp.ByQuery),
		chromedp.Sleep(10 * time.Second),
	}
}

func waitForOTP(bot *tgbotapi.BotAPI, chatID int64, updates tgbotapi.UpdatesChannel) (string, error) {
	timeout := time.After(otpTimeout)
	for {
		select {
		case update := <-updates:
			if update.Message == nil || update.Message.Text == "" || update.Message.Chat.ID != chatID {
				continue
			}
			otp := strings.TrimSpace(update.Message.Text)
			if len(otp) == 4 && isNumeric(otp) {
				logger.Infof("Получен корректный OTP: %s", otp)
				return otp, nil
			}
			bot.Send(tgbotapi.NewMessage(chatID, "Неверный OTP. Отправьте 4-значный код."))
		case <-timeout:
			return "", fmt.Errorf("превышено время ожидания OTP (%s)", otpTimeout)
		}
	}
}

func waitForPin(bot *tgbotapi.BotAPI, chatID int64, updates tgbotapi.UpdatesChannel) (string, error) {
	timeout := time.After(otpTimeout)
	for {
		select {
		case update := <-updates:
			if update.Message == nil || update.Message.Text == "" || update.Message.Chat.ID != chatID {
				continue
			}
			pin := strings.TrimSpace(update.Message.Text)
			if len(pin) == 4 && isNumeric(pin) {
				logger.Infof("Получен корректный PIN: %s", pin)
				return pin, nil
			}
			bot.Send(tgbotapi.NewMessage(chatID, "Неверный PIN. Отправьте 4-значный код."))
		case <-timeout:
			return "", fmt.Errorf("превышено время ожидания PIN (%s)", otpTimeout)
		}
	}
}

func isNumeric(s string) bool {
	for _, r := range s {
		if r < '0' || r > '9' {
			return false
		}
	}
	return true
}

func getChromeDataDir() string {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		logger.Fatalf("Ошибка получения домашней директории: %v", err)
	}
	chromiumDir := filepath.Join(homeDir, ".config", "chromium")
	if _, err := os.Stat(chromiumDir); err != nil {
		logger.Warnf("Директория Chromium не найдена: %s, создается по умолчанию", chromiumDir)
	}
	logger.Infof("Используется директория данных Chromium: %s", chromiumDir)
	return chromiumDir
}
