/*
 * SPDX-FileCopyrightText: 2022-2022 CSSlayer <wengxt@gmail.com>
 * SPDX-FileCopyrightText: 2025 Võ Ngô Hoàng Thành <thanhpy2009@gmail.com>
 * SPDX-FileCopyrightText: 2026 Nguyễn Hoàng Kỳ  <nhktmdzhg@gmail.com>
 *
 * SPDX-License-Identifier: GPL-3.0-or-later
 *
 */
#include "vmk.h"

#include <fcitx-config/iniparser.h>
#include <fcitx-utils/charutils.h>
#include <fcitx-utils/event.h>
#include <fcitx-utils/key.h>
#include <fcitx-utils/keysymgen.h>
#include <fcitx-utils/standardpath.h>
#include <fcitx-utils/textformatflags.h>
#include <fcitx-utils/utf8.h>
#include <fcitx/candidatelist.h>
#include <fcitx/inputcontext.h>
#include <fcitx/inputpanel.h>
#include <fcitx/menu.h>
#include <fcitx/statusarea.h>
#include <fcitx/userinterface.h>
#include <fcitx/userinterfacemanager.h>

#include <algorithm>
#include <atomic>
#include <cassert>
#include <cerrno>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <stdexcept>
#include <string>
#include <thread>
#include <sstream>

#include <dirent.h>
#include <errno.h>
#include <execinfo.h>
#include <fcntl.h>
#include <poll.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/un.h>
#include <unistd.h>

#ifdef __linux__
#include <X11/Xatom.h>
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdio>
#include <fstream>
#include <limits.h>
#include <mutex>
#include <iomanip>
#endif

fcitx::VMKMode    realMode = fcitx::VMKMode::VMK1;
std::atomic<bool> needEngineReset{false};
std::string       BASE_SOCKET_PATH;
// Global flag to signal mouse click for closing app mode menu
static std::atomic<bool> g_mouse_clicked{false};

std::atomic<bool>        is_deleting_{false};
static const int         MAX_BACKSPACE_COUNT = 15;
std::string              SubstrChar(const std::string& s, size_t start, size_t len);
int                      compareAndSplitStrings(const std::string& A, const std::string& B, std::string& commonPrefix, std::string& deletedPart, std::string& addedPart);
std::once_flag           monitor_init_flag;
std::atomic<bool>        stop_flag_monitor{false};
std::atomic<bool>        monitor_running{false};
int                      uinput_fd_        = -1;
int                      uinput_client_fd_ = -1;
int                      extraBackspace    = 0;
int                      realtextLen       = 0; // this shit to check suggestion text

//
void logToFile(const std::string& function, int line, const std::string& message) {
    static std::ofstream logFile("/tmp/vmk_debug.log", std::ios::app);
    if (!logFile.is_open()) {
        return;
    }

    auto now  = std::chrono::system_clock::now();
    auto time = std::chrono::system_clock::to_time_t(now);
    auto ms   = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch()) % 1000;

    logFile << std::put_time(std::localtime(&time), "%H:%M:%S") << "." << std::setfill('0') << std::setw(3) << ms.count() << " [" << function << ":" << line << "] " << message
            << std::endl;
    logFile.flush();
}

#define LOG(msg) logToFile(__func__, __LINE__, msg)

std::string escapeString(const std::string& str) {
    std::string result;
    result.reserve(str.size());
    for (unsigned char c : str) {
        if (c >= 32 && c < 127) {
            result += c;
        } else {
            char buf[10];
            std::snprintf(buf, sizeof(buf), "\\x%02x", c);
            result += buf;
        }
    }
    return result;
}

static void logCursorState(const char* context, int line, fcitx::InputContext* ic, const std::string& debugInfo = "") {
    if (!ic)
        return;

    auto s = ic->surroundingText();
    if (s.isValid()) {
        int                cursor  = s.cursor();
        const auto&        text    = s.text();
        size_t             textLen = fcitx_utf8_strlen(text.c_str());

        std::ostringstream oss;
        oss << "[CURSOR:" << line << "] " << context << " | cursor=" << cursor << " text_len=" << textLen << " text=\"" << escapeString(text) << "\""
            << " app=" << ic->program();
        if (!debugInfo.empty()) {
            oss << " " << debugInfo;
        }
        LOG(oss.str());

    } else {
        std::ostringstream oss;
        oss << "[CURSOR:" << line << "] " << context << " | surrounding=INVALID"
            << " app=" << ic->program();
        if (!debugInfo.empty()) {
            oss << " " << debugInfo;
        }
        LOG(oss.str());
    }
}

#define LOG_CURSOR(context, ic, debugInfo) logCursorState(context, __LINE__, ic, debugInfo)

std::string buildSocketPath(const char* base_path_suffix) {
    const char* username_c = std::getenv("USER");
    std::string username   = username_c ? std::string(username_c) : "default";
    std::string path       = "vmksocket-" + username + "-" + std::string(base_path_suffix);
    return path;
}

void deletingTimeMonitor() {
    LOG("Monitor thread started");
    auto t_start  = std::chrono::high_resolution_clock::now();
    bool last_val = 0;

    while (!stop_flag_monitor.load()) {
        bool current_val = is_deleting_.load();

        if (!last_val && current_val) {
            t_start = std::chrono::high_resolution_clock::now();
            LOG("Delete operation started");
        }

        if (current_val) {
            auto t_now    = std::chrono::high_resolution_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(t_now - t_start).count();

            if (duration >= 1500) {
                is_deleting_.store(false);
                needEngineReset.store(true);
                current_val = false;
                LOG("Deleting timeout reached, resetting engine");
            }
        }
        last_val = current_val;
        std::this_thread::sleep_for(std::chrono::milliseconds(2));
    }
    LOG("Monitor thread stopped");
}

void startMonitoringOnce() {
    if (monitor_running.load())
        return;
    std::call_once(monitor_init_flag, []() {
        stop_flag_monitor.store(false);
        std::thread(deletingTimeMonitor).detach();
        LOG("Monitor initialization completed");
    });
}

struct KeyEntry {
    uint32_t sym;
    uint32_t state;
};

bool isBackspace(uint32_t sym) {
    return sym == 65288 || sym == 8 || sym == FcitxKey_BackSpace;
}

namespace fcitx {
    namespace {
        constexpr std::string_view MacroPrefix             = "macro/";
        constexpr std::string_view InputMethodActionPrefix = "vmk-input-method-";
        constexpr std::string_view CharsetActionPrefix     = "vmk-charset-";
        const std::string          CustomKeymapFile        = "conf/vmk-custom-keymap.conf";

        std::string                macroFile(std::string_view imName) {
            return stringutils::concat("conf/vmk-macro-", imName, ".conf");
        }

        uintptr_t newMacroTable(const vmkMacroTable& macroTable) {
            std::vector<char*> charArray;
            RawConfig          r;
            macroTable.save(r);
            for (const auto& keymap : *macroTable.macros) {
                charArray.push_back(const_cast<char*>(keymap.key->data()));
                charArray.push_back(const_cast<char*>(keymap.value->data()));
            }
            charArray.push_back(nullptr);
            return NewMacroTable(charArray.data());
        }

        std::vector<std::string> convertToStringList(char** array) {
            std::vector<std::string> result;
            for (int i = 0; array[i]; ++i) {
                result.push_back(array[i]);
                free(array[i]);
            }
            free(array);
            return result;
        }

        static void DeletePreviousNChars(fcitx::InputContext* ic, size_t n, fcitx::Instance* instance) {
            if (!ic || !instance || n == 0)
                return;

            LOG_CURSOR("BEFORE_DELETE", ic, "chars_to_delete=" + std::to_string(n));

            if (ic->capabilityFlags().test(fcitx::CapabilityFlag::SurroundingText)) {
                int offset = -static_cast<int>(n);
                ic->deleteSurroundingText(offset, static_cast<int>(n));
                LOG_CURSOR("AFTER_DELETE_SURROUNDING", ic, "");
                return;
            }
            for (size_t i = 0; i < n; ++i) {
                fcitx::Key key(FcitxKey_BackSpace);
                ic->forwardKey(key, false);
                ic->forwardKey(key, true);
            }
            LOG_CURSOR("AFTER_DELETE_FORWARDKEY", ic, "");
        }

    } // namespace

    FCITX_DEFINE_LOG_CATEGORY(vmk, "vmk");

    class VMKState final : public InputContextProperty {
      public:
        VMKState(vmkEngine* engine, InputContext* ic) : engine_(engine), ic_(ic) {
            LOG("VMKState constructor called");
            logState("CONSTRUCTOR");
            setEngine();
        }

        ~VMKState() {
            LOG("VMKState destructor called");
            logState("DESTRUCTOR");
        }

        void logState(const std::string& context) {
            std::ostringstream oss;
            oss << "[STATE:" << context << "] "
                << "oldPreBuffer=\"" << escapeString(oldPreBuffer_) << "\" "
                << "history=\"" << escapeString(history_) << "\" "
                << "expected_backspaces=" << expected_backspaces_ << " "
                << "current_backspace_count=" << current_backspace_count_ << " "
                << "pending_commit=\"" << escapeString(pending_commit_string_) << "\" "
                << "thread_id=" << current_thread_id_.load() << " "
                << "is_deleting=" << is_deleting_.load() << " "
                << "realtextLen=" << realtextLen;
            LOG(oss.str());
        }

        void setEngine() {
            LOG("setEngine() called");
            logState("BEFORE_SET_ENGINE");
            vmkEngine_.reset();
            realMode = fcitx::modeStringToEnum(engine_->config().mode.value());

            std::ostringstream oss;
            oss << "Setting engine mode: " << engine_->config().mode.value();
            LOG(oss.str());

            if (engine_->config().inputMethod.value() == "Custom") {
                std::vector<char*> charArray;
                for (const auto& keymap : *engine_->customKeymap().customKeymap) {
                    charArray.push_back(const_cast<char*>(keymap.key->data()));
                    charArray.push_back(const_cast<char*>(keymap.value->data()));
                }
                charArray.push_back(nullptr);
                vmkEngine_.reset(NewCustomEngine(charArray.data(), engine_->dictionary(), engine_->macroTable()));
                LOG("Custom engine created");
            } else {
                vmkEngine_.reset(NewEngine(engine_->config().inputMethod->data(), engine_->dictionary(), engine_->macroTable()));
                LOG("Standard engine created with input method: " + engine_->config().inputMethod.value());
            }
            setOption();
            logState("AFTER_SET_ENGINE");
        }

        void setOption() {
            if (!vmkEngine_)
                return;

            LOG("setOption() called");
            logState("BEFORE_SET_OPTION");
            FcitxBambooEngineOption option = {
                .autoNonVnRestore    = *engine_->config().autoNonVnRestore,
                .ddFreeStyle         = true,
                .macroEnabled        = *engine_->config().macro,
                .autoCapitalizeMacro = *engine_->config().capitalizeMacro,
                .spellCheckWithDicts = *engine_->config().spellCheck,
                .outputCharset       = engine_->config().outputCharset->data(),
                .modernStyle         = *engine_->config().modernStyle,
                .freeMarking         = *engine_->config().freeMarking,
            };
            EngineSetOption(vmkEngine_.handle(), &option);

            std::ostringstream oss;
            oss << "Options set - macro=" << option.macroEnabled << " spellCheck=" << option.spellCheckWithDicts << " charset=" << option.outputCharset;
            LOG(oss.str());
            logState("AFTER_SET_OPTION");
        }

        bool connect_uinput_server() {
            if (uinput_client_fd_ >= 0) {
                LOG("Already connected to uinput server");
                return true;
            }

            BASE_SOCKET_PATH               = buildSocketPath("kb_socket");
            const std::string current_path = BASE_SOCKET_PATH;
            int               current_fd   = socket(AF_UNIX, SOCK_STREAM, 0);
            if (current_fd < 0) {
                LOG("Failed to create socket");
                return false;
            }

            struct sockaddr_un addr;
            memset(&addr, 0, sizeof(addr));
            addr.sun_family = AF_UNIX;

            addr.sun_path[0] = '\0';
            memcpy(addr.sun_path + 1, current_path.c_str(), current_path.length());
            socklen_t len = offsetof(struct sockaddr_un, sun_path) + current_path.length() + 1;

            if (connect(current_fd, (struct sockaddr*)&addr, len) == 0) {
                uinput_client_fd_ = current_fd;
                uinput_fd_        = current_fd;
                LOG("Connected to uinput server successfully");
                return true;
            }
            close(current_fd);
            uinput_client_fd_ = -1;
            uinput_fd_        = -1;
            LOG("Failed to connect to uinput server");
            return false;
        }

        bool send_command_to_server(int count) {
            std::ostringstream oss;
            oss << "Sending backspace command: count=" << count;
            LOG(oss.str());
            logState("BEFORE_SEND_COMMAND");

            if (uinput_client_fd_ >= 0) {
                if (send(uinput_client_fd_, &count, sizeof(count), 0) >= 0) {
                    LOG("Command sent successfully");
                    logState("AFTER_SEND_COMMAND_SUCCESS");
                    return true;
                }
            }
            if (uinput_client_fd_ >= 0) {
                close(uinput_client_fd_);
                uinput_client_fd_ = -1;
                uinput_fd_        = -1;
                LOG("Connection closed, attempting reconnect");
            }
            if (!connect_uinput_server())
                return false;
            if (send(uinput_client_fd_, &count, sizeof(count), 0) < 0) {
                close(uinput_client_fd_);
                uinput_client_fd_ = -1;
                uinput_fd_        = -1;
                LOG("Failed to send after reconnect");
                logState("AFTER_SEND_COMMAND_FAIL");
                return false;
            }
            LOG("Command sent successfully after reconnect");
            logState("AFTER_SEND_COMMAND_RECONNECT");
            return true;
        }

        int setup_uinput() {
            LOG("setup_uinput() called");
            return connect_uinput_server() ? uinput_fd_ : -1;
        }

        void send_backspace_uinput(int count) {
            logState("BEFORE_SEND_BACKSPACE_UINPUT");
            if (uinput_fd_ < 0 && !connect_uinput_server()) {
                LOG("Cannot send backspace - not connected");
                return;
            }
            if (count > MAX_BACKSPACE_COUNT)
                count = MAX_BACKSPACE_COUNT;

            LOG_CURSOR("BEFORE_SEND_BACKSPACE_UINPUT", ic_, "count=" + std::to_string(count));
            send_command_to_server(count);
            logState("AFTER_SEND_BACKSPACE_UINPUT");
        }

        bool handleUInputKeyPress(fcitx::KeyEvent& event, fcitx::KeySym currentSym) {
            if (!is_deleting_.load())
                return false;
            if (isBackspace(currentSym)) {
                current_backspace_count_ += 1;
                std::ostringstream oss;
                oss << "count=" << current_backspace_count_ << " expected=" << expected_backspaces_;
                LOG(oss.str());
                logState("DURING_BACKSPACE");

                LOG_CURSOR("DURING_BACKSPACE", ic_, "count=" + std::to_string(current_backspace_count_) + " expected=" + std::to_string(expected_backspaces_));

                if (current_backspace_count_ < expected_backspaces_) {
                    return false;
                } else {
                    is_deleting_.store(false);
                    current_thread_id_.fetch_add(1);
                    std::this_thread::sleep_for(std::chrono::milliseconds(20));

                    std::ostringstream oss;
                    oss << "Committing: " << pending_commit_string_;
                    LOG(oss.str());
                    logState("BEFORE_COMMIT");
                    LOG_CURSOR("BEFORE_COMMIT", ic_, "commit=" + pending_commit_string_);

                    ic_->commitString(pending_commit_string_);

                    LOG_CURSOR("AFTER_COMMIT", ic_, "");
                    logState("AFTER_COMMIT");

                    expected_backspaces_     = 0;
                    current_backspace_count_ = -1;
                    pending_commit_string_   = "";

                    event.filterAndAccept();
                    return true;
                }
            }
            return false;
        }

        void replayBufferToEngine(const std::string& buffer) {
            if (!vmkEngine_.handle())
                return;

            std::ostringstream oss;
            oss << "Replaying buffer: \"" << escapeString(buffer) << "\"";
            LOG(oss.str());
            logState("BEFORE_REPLAY");

            ResetEngine(vmkEngine_.handle());
            for (size_t i = 0; i < buffer.length();) {
                if (i + 2 < buffer.length() && buffer.substr(i, 3) == "\\b\\") {
                    EngineProcessKeyEvent(vmkEngine_.handle(), FcitxKey_BackSpace, 0);
                    i += 3;
                } else {
                    unsigned char c = static_cast<unsigned char>(buffer[i]);
                    EngineProcessKeyEvent(vmkEngine_.handle(), (uint32_t)c, 0);
                    i += 1;
                }
            }
            //realtextLen +=1; does this should be here
            logState("AFTER_REPLAY");
        }

        bool isAutofillCertain(const fcitx::SurroundingText& s) {
            if (!s.isValid() || oldPreBuffer_.empty()) {
                LOG("isAutofillCertain: FALSE (invalid surrounding or empty oldPreBuffer)");
                return false;
            }

            int                cursor  = s.cursor();
            // int                anchor  = s.anchor();
            const auto&        text    = s.text();
            size_t             textLen = fcitx_utf8_strlen(text.c_str());
            std::ostringstream oss0;
            oss0 << "isAutofillCertain: cursor=" << cursor << " textLen=" << textLen << " realtext=" << realtextLen;
            LOG(oss0.str());

            // This bushjt is done in other place
            // if (textLen <= realtextLen) {
            //     std::ostringstream oss;
            //     oss << "textLen <= realtextlen: cursor=" << cursor << " textLen="
            //     << textLen << " realtext=" << realtextLen;
            //     LOG(oss.str());

            //     realtextLen = textLen;
            // }

            // No text after cursor at all -> no suggestion possible.
            // Sync realtextLen to the actual end.
            if (textLen == static_cast<size_t>(cursor)) {
                LOG("isAutofillCertain: FALSE (cursor at end)");
                realtextLen = textLen;
                return false;
            }
            std::ostringstream oss2;
            oss2 << "isAutofillCertain: MAYBE. cursor=" << cursor << " textLen=" << textLen << " realtext=" << realtextLen;
            LOG(oss2.str());

            // Text exists after cursor AND cursor is exactly where we expected
            // (realtextLen tracks where cursor should be after our last commit).
            // This is the only reliable signal that the app appended a suggestion.
            if (textLen > static_cast<size_t>(cursor) && static_cast<size_t>(cursor) == realtextLen) {
                LOG("isAutofillCertain: TRUE (suggestion detected)");
                std::ostringstream oss;
                oss << "isAutofillCertain: YESYESYES cursor=" << cursor << " textLen=" << textLen << " realtext=" << realtextLen;
                LOG(oss.str());
                return true;
            }

            // Everything else: normal editing (mid-line, existing trailing text, etc.)
            // Sync realtextLen to cursor so next check has a clean baseline.
            realtextLen = static_cast<size_t>(cursor);
            LOG("isAutofillCertain: FALSE (normal, synced realtextLen to cursor)");
            return false;
        }

        // Helper function for preedit mode
        void handlePreeditMode(KeyEvent& keyEvent) {
            LOG("handlePreeditMode() called");
            logState("BEFORE_PREEDIT_MODE");
            if (EngineProcessKeyEvent(vmkEngine_.handle(), keyEvent.rawKey().sym(), keyEvent.rawKey().states()))
                keyEvent.filterAndAccept();
            if (char* commit = EnginePullCommit(vmkEngine_.handle())) {
                if (commit[0]) {
                    std::ostringstream oss;
                    oss << "Preedit commit: \"" << escapeString(commit) << "\"";
                    LOG(oss.str());
                    ic_->commitString(commit);
                }
                free(commit);
            }
            ic_->inputPanel().reset();
            UniqueCPtr<char> preedit(EnginePullPreedit(vmkEngine_.handle()));
            if (preedit && preedit.get()[0]) {
                std::string_view view = preedit.get();
                Text             text;
                TextFormatFlags  fmt = TextFormatFlag::NoFlag;
                if (utf8::validate(view))
                    text.append(std::string(view), fmt);
                text.setCursor(text.textLength());
                if (ic_->capabilityFlags().test(CapabilityFlag::Preedit))
                    ic_->inputPanel().setClientPreedit(text);
                else
                    ic_->inputPanel().setPreedit(text);
            }
            ic_->updatePreedit();
            ic_->updateUserInterface(UserInterfaceComponent::InputPanel);
            logState("AFTER_PREEDIT_MODE");
        }

        // Helper function for vmk1/vmk1hc mode
        void handleUinputMode(KeyEvent& keyEvent, fcitx::KeySym currentSym, bool checkEmptyPreedit) {
            logState("BEFORE_UINPUT_MODE MVK1/VMK1HC");
            // App (e.g. browser) may replace surrounding text entirely between key events
            // (address bar suggestion swap). If textLen dropped below realtextLen the text
            // changed under us; reset realtextLen to cursor immediately.
            {
                auto surr = ic_->surroundingText();
                if (surr.isValid()) {
                    size_t textLen = fcitx_utf8_strlen(surr.text().c_str());
                    if (textLen < static_cast<size_t>(realtextLen)) {
                        realtextLen = static_cast<size_t>(surr.cursor());
                        LOG("App replaced text, realtextLen reset to cursor=" + std::to_string(realtextLen));
                    }
                }
            }
            LOG("handleUinputMode.prev="+std::to_string(is_deleting_.load()));
            if (!is_deleting_.load()) {
                if (currentSym == FcitxKey_Tab
                    || currentSym == FcitxKey_Up
                    || currentSym == FcitxKey_Down
                    || currentSym == FcitxKey_Left
                    || currentSym == FcitxKey_Right) {
                    auto s = ic_->surroundingText();
                    if (s.isValid()) {
                        const int cursor = s.cursor();
                        realtextLen      = static_cast<size_t>(cursor);
                        LOG("Nav key pressed - realtextLen synced to cursor=" + std::to_string(cursor));
                    }
                }

                if (isBackspace(currentSym) || currentSym == FcitxKey_space || currentSym == FcitxKey_Return) {
                    if (isBackspace(currentSym)) {
                        history_ += "\\b\\";
                        replayBufferToEngine(history_);
                        UniqueCPtr<char> preeditC(EnginePullPreedit(vmkEngine_.handle()));
                        oldPreBuffer_ = (preeditC && preeditC.get()[0]) ? preeditC.get() : "";

                        auto s = ic_->surroundingText();
                        if (s.isValid()) {
                            realtextLen = static_cast<size_t>(s.cursor());
                        } else if (realtextLen > 0) {
                            realtextLen -= 1;
                        }
                        LOG("Backspace handled, updated history");
                        logState("AFTER_BACKSPACE_HANDLE");
                    } else {
                        history_.clear();
                        ResetEngine(vmkEngine_.handle());
                        oldPreBuffer_.clear();
                        std::ostringstream oss;
                        oss << "Non-typing key (0x" << std::hex << currentSym << ") - cleared history and buffer";
                        LOG(oss.str());
                        logState("AFTER_NON_TYPING_KEY");
                    }
                    keyEvent.forward();
                    return;
                }
            } else {
                if (isBackspace(currentSym) && is_deleting_) {
                    realtextLen -= 1;
                    bool done = handleUInputKeyPress(keyEvent, currentSym);
                    // sleep(0.1);
                    // keyEvent.filterAndAccept();
                    if (done) return;
                    //return; /// wtf is this. this fix that vmk1 eat char in chromium x11 but also make that not send to uniput to use backspace
                    return;
                }
                keyEvent.filterAndAccept();
                return;
            }
            LOG("handleUinputMode.next=" + std::to_string(is_deleting_.load()));
            // Does is_deleting_ value in prev if else statements is change??
            if (!is_deleting_.load()) {
                if (uinput_fd_ < 0)
                    setup_uinput();
                if (!EngineProcessKeyEvent(vmkEngine_.handle(), currentSym, keyEvent.rawKey().states())) {
                    if (checkEmptyPreedit) {
                        UniqueCPtr<char> preeditC(EnginePullPreedit(vmkEngine_.handle()));
                        std::string      preeditStr = (preeditC && preeditC.get()[0]) ? preeditC.get() : "";
                        if (preeditStr.empty()) {
                            history_.clear();
                            oldPreBuffer_.clear();
                            keyEvent.forward();
                            LOG("Empty preedit - forwarding key");
                            logState("EMPTY_PREEDIT");
                        }
                    }
                    return;
                }
                if (currentSym >= 32 && currentSym <= 126) {
                    history_ += static_cast<char>(currentSym);
                    realtextLen += 1;
                } else {
                    keyEvent.forward();
                    return;
                }
                replayBufferToEngine(history_);
                if (auto commitF = UniqueCPtr<char>(EnginePullCommit(vmkEngine_.handle())); commitF && commitF.get()[0]) {
                    history_.clear();
                    ResetEngine(vmkEngine_.handle());
                    oldPreBuffer_.clear();
                    LOG("Engine committed - cleared buffers");
                    logState("ENGINE_COMMITTED");
                    return;
                }
                keyEvent.filterAndAccept();
                UniqueCPtr<char> preeditC(EnginePullPreedit(vmkEngine_.handle()));
                std::string      preeditStr = (preeditC && preeditC.get()[0]) ? preeditC.get() : "";
                std::string      commonPrefix, deletedPart, addedPart;
                if (compareAndSplitStrings(oldPreBuffer_, preeditStr, commonPrefix, deletedPart, addedPart)) {
                    if (deletedPart.empty()) {
                        if (!addedPart.empty()) {
                            LOG_CURSOR("BEFORE_DIRECT_COMMIT", ic_, "added=" + addedPart);
                            logState("BEFORE_DIRECT_COMMIT");
                            ic_->commitString(addedPart);
                            LOG_CURSOR("AFTER_DIRECT_COMMIT", ic_, "");
                            logState("AFTER_DIRECT_COMMIT");
                            oldPreBuffer_ = preeditStr;
                        }
                    } else {
                        current_backspace_count_ = 0;
                        pending_commit_string_   = addedPart;
                        std::string oldBuffer    = oldPreBuffer_;
                        oldPreBuffer_            = preeditStr;

                        std::ostringstream oss;
                        oss << "old=\"" << escapeString(oldBuffer)
                            << "\" new=\"" << escapeString(preeditStr)
                            << "\" deleted=\"" << escapeString(deletedPart) << "\" added=\""
                            << escapeString(addedPart) << "\"";
                        LOG(oss.str());
                        logState("STRING_COMPARISON");
                        LOG_CURSOR("BEFORE_BACKSPACE_OPERATION", ic_, "deleted=" + deletedPart + " added=" + addedPart);

                        if (uinput_client_fd_ < 0) {
                            std::string rawKey = keyEvent.key().toString();
                            if (!rawKey.empty()) {
                                ic_->commitString(rawKey);
                            }
                            LOG("No uinput connection - committing raw key");
                            logState("NO_UINPUT");
                            return;
                        }

                        if (isAutofillCertain(ic_->surroundingText())) {
                            extraBackspace = 1;
                            LOG("Auto-suggest detected! Using double backspace strategy.");
                            logState("AUTO_SUGGEST_DETECTED");
                            LOG_CURSOR("AUTO_SUGGEST_ACTIVE", ic_, "");
                        }

                        if (is_deleting_.load()) {
                            is_deleting_.store(false);
                        }

                        expected_backspaces_ = fcitx::utf8::length(deletedPart) + 1 + extraBackspace;
                        if (expected_backspaces_ > 0)
                            is_deleting_.store(true);
                        logState("BEFORE_SEND_BACKSPACE");
                        send_backspace_uinput(expected_backspaces_);
                        int my_id = ++current_thread_id_;

                        std::thread([this, my_id]() {
                            auto               start = std::chrono::steady_clock::now();
                            std::ostringstream oss;
                            oss << "Thread " << my_id << " started";
                            LOG(oss.str());

                            while (is_deleting_.load()) {
                                if (current_thread_id_.load() != my_id) {
                                    std::ostringstream oss;
                                    oss << "Thread " << my_id << " cancelled";
                                    LOG(oss.str());
                                    return;
                                }

                                std::this_thread::sleep_for(std::chrono::milliseconds(5));

                                auto now = std::chrono::steady_clock::now();
                                if (std::chrono::duration_cast<std::chrono::milliseconds>(now - start).count() > 200) {
                                    std::ostringstream oss;
                                    oss << "Thread " << my_id << " timeout after 200ms";
                                    LOG(oss.str());
                                    break;
                                }
                            }

                            if (current_thread_id_.load() == my_id) {
                                if (!pending_commit_string_.empty()) {
                                    std::ostringstream oss;
                                    oss << "Thread " << my_id << " committing: " << pending_commit_string_;
                                    LOG(oss.str());
                                    ic_->commitString(pending_commit_string_);
                                    pending_commit_string_ = "";
                                }
                                // Sync realtextLen to actual cursor after commit
                                // so isAutofillCertain has a correct baseline.
                                auto surr = ic_->surroundingText();
                                if (surr.isValid())
                                    realtextLen = static_cast<size_t>(surr.cursor());
                                is_deleting_.store(false);
                            }
                        }).detach();

                        extraBackspace = 0;
                    }
                }
                logState("AFTER_UINPUT_MODE");
                LOG_CURSOR("AFTER_UINPUT_MODE", ic_, "realtextLen=" + std::to_string(realtextLen));
                return;
            }
        }

        void keyEvent(KeyEvent& keyEvent) {
            if (!vmkEngine_ || keyEvent.isRelease())
                return;

            char keySym[32];
            snprintf(keySym, sizeof(keySym), "0x%x", keyEvent.rawKey().sym());
            LOG_CURSOR("KEY_PRESS", ic_, "key=" + std::string(keySym));
            logState("KEY_EVENT_START");

            if (uinput_client_fd_ < 0) {
                connect_uinput_server();
            }
            if (current_backspace_count_ >= (int)expected_backspaces_ && is_deleting_.load()) {
                is_deleting_.store(false);
                current_backspace_count_ = -1;
                expected_backspaces_     = 0;
                LOG("Backspace completed");
                logState("BACKSPACE_COMPLETED");
            }
            if (needEngineReset.load() && (realMode == fcitx::VMKMode::VMK1
                                        || realMode == fcitx::VMKMode::VMK2
                                        || realMode == fcitx::VMKMode::VMK1HC)) {
                oldPreBuffer_.clear();
                history_.clear();
                ResetEngine(vmkEngine_.handle());
                is_deleting_.store(false);
                current_backspace_count_ = -1;
                needEngineReset.store(false);
                LOG("Engine reset triggered");
                logState("ENGINE_RESET");
            }
            if (keyEvent.rawKey().check(FcitxKey_Shift_L) || keyEvent.rawKey().check(FcitxKey_Shift_R))
                return;
            const fcitx::KeySym currentSym = keyEvent.rawKey().sym();

            switch (realMode) {
                case fcitx::VMKMode::VMK1: {
                    LOG("Processing in VMK1 mode");
                    handleUinputMode(keyEvent, currentSym, true);
                    break;
                }
                case fcitx::VMKMode::VMK1HC: {
                    LOG("Processing in VMK1HC mode");
                    handleUinputMode(keyEvent, currentSym, false);
                    break;
                }
                case fcitx::VMKMode::VMK2: {
                    LOG("Processing in VMK2 mode");
                    logState("VMK2_START");
                    auto ic = keyEvent.inputContext();
                    if (!ic)
                        return;
                    EngineProcessKeyEvent(vmkEngine_.handle(), keyEvent.rawKey().sym(), keyEvent.rawKey().states());
                    if (auto commitF = UniqueCPtr<char>(EnginePullCommit(vmkEngine_.handle())); commitF && commitF.get()[0]) {
                        ResetEngine(vmkEngine_.handle());
                        oldPreBuffer_.clear();
                        ic->inputPanel().reset();
                        ic->updateUserInterface(UserInterfaceComponent::InputPanel);
                        LOG("Engine committed, reset complete");
                        logState("VMK2_COMMITTED");
                        return;
                    }
                    UniqueCPtr<char> preeditC(EnginePullPreedit(vmkEngine_.handle()));
                    std::string      preeditStr = (preeditC && preeditC.get()[0]) ? preeditC.get() : "";
                    if (preeditStr != oldPreBuffer_) {
                        keyEvent.filterAndAccept();
                        if (!oldPreBuffer_.empty()) {
                            LOG_CURSOR("VMK2_BEFORE_DELETE", ic, "old=" + oldPreBuffer_);
                            logState("VMK2_BEFORE_DELETE");
                            DeletePreviousNChars(ic, fcitx::utf8::length(oldPreBuffer_), engine_->instance());
                            LOG_CURSOR("VMK2_AFTER_DELETE", ic, "");
                            logState("VMK2_AFTER_DELETE");
                        }
                        if (!preeditStr.empty()) {
                            LOG_CURSOR("VMK2_BEFORE_COMMIT", ic, "new=" + preeditStr);
                            logState("VMK2_BEFORE_COMMIT");
                            ic->commitString(preeditStr);
                            LOG_CURSOR("VMK2_AFTER_COMMIT", ic, "");
                            logState("VMK2_AFTER_COMMIT");
                            oldPreBuffer_ = preeditStr;
                        } else {
                            oldPreBuffer_.clear();
                            LOG("Cleared old preedit buffer");
                            logState("VMK2_CLEARED");
                        }
                    }
                    break;
                }
                case fcitx::VMKMode::Preedit: {
                    LOG("Processing in Preedit mode");
                    handlePreeditMode(keyEvent);
                    break;
                }
                default: {
                    LOG("Unknown mode - no processing");
                    break;
                }
            }
            LOG_CURSOR("KEY_PRESS_END", ic_, "key=" + std::string(keySym));
            logState("KEY_EVENT_END");
            if (current_backspace_count_ > 7)
                current_backspace_count_ = 0;
        }

        void reset() {
            LOG("==== reset() START ====");
            LOG_CURSOR("RESET_START", ic_, "");

            // TODO: This will report wrong when use mouse
            // click into the url bar that will select the cursor
            // pos now is 0 and realtextLen = textLen. Then the text
            // is select this not suggestion so can't sent 2 backspace
            // But in other case if click to the url bar in the first
            // place cursor pos is 0 and realtextLen = textLen too.
            // So we need get value of SurroundingText::selectedText()
            // but maybe can use that cus cursor alway = anchor in this
            // code base in vmk1 mode
            //
            // https://github.com/fcitx/fcitx5/blob/master/src/lib/fcitx/surroundingtext.cpp
            /*
              std::string SurroundingText::selectedText() const {
                FCITX_D();
                auto start = std::min(anchor(), cursor());
                auto end = std::max(anchor(), cursor());
                auto len = end - start;
                if (len == 0)
                    return {};
                auto startIter = utf8::nextNChar(d->text_.begin(), start);
                auto endIter = utf8::nextNChar(startIter, len);
                return std::string(startIter, endIter);
              }
              void SurroundingText::setText(const std::string &text, unsigned int cursor, unsigned int anchor) {
                FCITX_D();
                auto length = utf8::lengthValidated(text);
                if (length == utf8::INVALID_LENGTH || length < cursor || length < anchor) {
                    invalidate();
                    return;
                }
                d->valid_ = true;
                d->text_ = text;
                d->cursor_ = cursor;
                d->anchor_ = anchor;
                d->utf8Length_ = length;
            }
            void SurroundingText::setCursor(unsigned int cursor, unsigned int anchor) {
                FCITX_D();
                if (d->utf8Length_ < cursor || d->utf8Length_ < anchor) {
                    invalidate();
                    return;
                }
                d->cursor_ = cursor;
                d->anchor_ = anchor;
            }
            */

            const auto& text    = (ic_->surroundingText()).text();
            size_t      textLen = fcitx_utf8_strlen(text.c_str());
            realtextLen         = textLen;
            std::ostringstream oss;
            oss << "Reset called - mode=" << fcitx::modeEnumToString(realMode) << " is_deleting=" << is_deleting_.load();
            LOG(oss.str());
            logState("RESET_START");

            is_deleting_.store(false);
            clearAllBuffers();

            switch (realMode) {
                case fcitx::VMKMode::Preedit: {
                    LOG("Resetting Preedit mode");
                    ic_->inputPanel().reset();
                    ic_->updateUserInterface(UserInterfaceComponent::InputPanel);
                    ic_->updatePreedit();
                    LOG("Preedit mode reset complete");
                    break;
                }
                case fcitx::VMKMode::VMK2:
                case fcitx::VMKMode::VMK1:
                case fcitx::VMKMode::VMK1HC: {
                    std::ostringstream oss;
                    oss << "Resetting " << fcitx::modeEnumToString(realMode) << " mode";
                    LOG(oss.str());
                    ic_->inputPanel().reset();
                    LOG("Mode reset complete");
                    break;
                }
                default: {
                    LOG("Unknown mode - minimal reset");
                    break;
                }
            }

            LOG_CURSOR("RESET_END", ic_, "realtext=" + std::to_string(realtextLen));

            logState("RESET_END");
            LOG("==== reset() END ====");
        }

        void commitBuffer() {
            LOG("==== commitBuffer() START ====");
            LOG_CURSOR("COMMIT_BUFFER_START", ic_, "");
            logState("COMMIT_BUFFER_START");

            switch (realMode) {
                case fcitx::VMKMode::Preedit: {
                    LOG("Committing Preedit mode buffer");
                    ic_->inputPanel().reset();
                    if (vmkEngine_) {
                        EngineCommitPreedit(vmkEngine_.handle());
                        UniqueCPtr<char> commit(EnginePullCommit(vmkEngine_.handle()));
                        if (commit && commit.get()[0]) {
                            std::ostringstream oss;
                            oss << "Committing preedit: \"" << escapeString(commit.get()) << "\"";
                            LOG(oss.str());
                            ic_->commitString(commit.get());
                        } else {
                            LOG("No preedit to commit");
                        }
                    }
                    ic_->updateUserInterface(UserInterfaceComponent::InputPanel);
                    ic_->updatePreedit();
                    LOG("Preedit commit complete");
                    break;
                }
                case fcitx::VMKMode::VMK2: {
                    LOG("Resetting VMK2 engine");
                    if (vmkEngine_)
                        ResetEngine(vmkEngine_.handle());
                    LOG("VMK2 engine reset complete");
                    break;
                }
                default: {
                    LOG("No commit action for current mode");
                    break;
                }
            }

            LOG_CURSOR("COMMIT_BUFFER_END", ic_, "");
            logState("COMMIT_BUFFER_END");
            LOG("==== commitBuffer() END ====");
        }

        void clearAllBuffers() {
            LOG("==== clearAllBuffers() START ====");
            logState("BEFORE_CLEAR_BUFFERS");

            oldPreBuffer_.clear();
            expected_backspaces_     = 0;
            current_backspace_count_ = 0;
            pending_commit_string_.clear();
            current_thread_id_.store(0);
            history_.clear();
            if (vmkEngine_) {
                ResetEngine(vmkEngine_.handle());
                LOG("Engine reset");
            }

            logState("AFTER_CLEAR_BUFFERS");
            LOG("==== clearAllBuffers() END ====");
        }

      private:
        vmkEngine*       engine_;
        InputContext*    ic_;
        CGoObject        vmkEngine_;
        std::string      oldPreBuffer_;
        std::string      history_;
        size_t           expected_backspaces_     = 0;
        size_t           current_backspace_count_ = 0;
        std::string      pending_commit_string_;
        std::atomic<int> current_thread_id_{0};
    };

    void mousePressResetThread() {
        LOG("Mouse reset thread started");
        const std::string mouse_socket_path = buildSocketPath("mouse_socket");

        while (!stop_flag_monitor.load(std::memory_order_relaxed)) {
            int sock = socket(AF_UNIX, SOCK_STREAM, 0);
            if (sock < 0) {
                sleep(1);
                continue;
            }

            struct sockaddr_un addr{};
            addr.sun_family  = AF_UNIX;
            addr.sun_path[0] = '\0';
            memcpy(addr.sun_path + 1, mouse_socket_path.c_str(), mouse_socket_path.length());
            socklen_t len = offsetof(struct sockaddr_un, sun_path) + mouse_socket_path.length() + 1;

            if (connect(sock, (struct sockaddr*)&addr, len) < 0) {
                close(sock);
                sleep(1);
                continue;
            }

            LOG("Connected to mouse socket");

            struct pollfd pfd;
            pfd.fd     = sock;
            pfd.events = POLLIN;

            while (!stop_flag_monitor.load(std::memory_order_relaxed)) {
                int ret = poll(&pfd, 1, -1);

                if (ret > 0 && (pfd.revents & POLLIN)) {
                    char    buf[16];
                    ssize_t n = recv(sock, buf, sizeof(buf), 0);

                    if (n <= 0) {
                        LOG("Socket disconnected");
                        break;
                    }

                    struct ucred cred;
                    socklen_t    len                = sizeof(struct ucred);
                    char         exe_path[PATH_MAX] = {0};
                    if (getsockopt(sock, SOL_SOCKET, SO_PEERCRED, &cred, &len) == 0) {
                        char path[64];
                        snprintf(path, sizeof(path), "/proc/%d/exe", cred.pid);
                        ssize_t ret = readlink(path, exe_path, sizeof(exe_path) - 1);
                        if (ret != -1) {
                            exe_path[ret] = '\0';
                        }
                    }

                    if (n > 0 && std::string(exe_path) == "/usr/bin/fcitx5-vmk-server") {
                        needEngineReset.store(true, std::memory_order_relaxed);
                        g_mouse_clicked.store(true, std::memory_order_relaxed);
                        LOG("Mouse click detected, reset triggered");
                    }
                } else if (ret < 0 && errno != EINTR) {
                    LOG("Poll error");
                    break;
                }
            }
            close(sock);
            LOG("Socket closed, reconnecting...");
        }
        LOG("Mouse reset thread stopped");
    }

    void startMouseReset() {
        LOG("Starting mouse reset thread");
        std::thread(mousePressResetThread).detach();
    }

    vmkEngine::vmkEngine(Instance* instance) : instance_(instance), factory_([this](InputContext& ic) { return new VMKState(this, &ic); }) {
        LOG("==== vmkEngine constructor START ====");
        LOG("Starting vmkEngine");

        startMonitoringOnce();
        Init();
        {
            auto imNames = convertToStringList(GetInputMethodNames());
            imNames.push_back("Custom");
            imNames_ = std::move(imNames);

            std::ostringstream oss;
            oss << "Loaded " << imNames_.size() << " input methods";
            LOG(oss.str());
        }
        config_.inputMethod.annotation().setList(imNames_);
        auto fd = StandardPath::global().open(StandardPath::Type::PkgData, "vmk/vietnamese.cm.dict", O_RDONLY);
        if (!fd.isValid()) {
            LOG("FATAL: Failed to load dictionary");
            throw std::runtime_error("Failed to load dictionary");
        }
        dictionary_.reset(NewDictionary(fd.release()));
        LOG("Dictionary loaded successfully");

        auto& uiManager = instance_->userInterfaceManager();
        modeAction_     = std::make_unique<SimpleAction>();
        modeAction_->setIcon("preferences-system");
        modeAction_->setShortText(_("Chế độ gõ"));
        uiManager.registerAction("vmk-mode", modeAction_.get());
        modeMenu_ = std::make_unique<Menu>();
        modeAction_->setMenu(modeMenu_.get());

        std::vector<fcitx::VMKMode> modes = {fcitx::VMKMode::VMK1, fcitx::VMKMode::VMK2, fcitx::VMKMode::Preedit, fcitx::VMKMode::VMK1HC};
        for (const auto& mode : modes) {
            auto action = std::make_unique<SimpleAction>();
            action->setShortText(modeEnumToString(mode));
            action->setCheckable(true);
            uiManager.registerAction("vmk-mode-" + modeEnumToString(mode), action.get());
            connections_.emplace_back(action->connect<SimpleAction::Activated>([this, mode](InputContext* ic) {
                if (globalMode_ == mode) {
                    return;
                }

                std::ostringstream oss;
                oss << "Mode changed to: " << modeEnumToString(mode);
                LOG(oss.str());

                config_.mode.setValue(modeEnumToString(mode));
                saveConfig();
                realMode    = mode;
                globalMode_ = mode;
                reloadConfig();
                updateModeAction(ic);
                if (ic) {
                    ic->updateUserInterface(fcitx::UserInterfaceComponent::StatusArea);
                }
            }));
            modeMenu_->addAction(action.get());
            modeSubAction_.push_back(std::move(action));
        }

        inputMethodAction_ = std::make_unique<SimpleAction>();
        inputMethodAction_->setIcon("document-edit");
        inputMethodAction_->setShortText("Kiểu gõ");
        uiManager.registerAction("vmk-input-method", inputMethodAction_.get());
        inputMethodMenu_ = std::make_unique<Menu>();
        inputMethodAction_->setMenu(inputMethodMenu_.get());

        for (const auto& imName : imNames_) {
            inputMethodSubAction_.emplace_back(std::make_unique<SimpleAction>());
            auto action = inputMethodSubAction_.back().get();
            action->setShortText(imName);
            action->setCheckable(true);
            uiManager.registerAction(stringutils::concat(InputMethodActionPrefix, imName), action);
            connections_.emplace_back(action->connect<SimpleAction::Activated>([this, imName](InputContext* ic) {
                if (config_.inputMethod.value() == imName)
                    return;

                LOG("Input method changed to: " + imName);
                config_.inputMethod.setValue(imName);
                saveConfig();
                refreshEngine();
                updateInputMethodAction(ic);
                if (ic)
                    ic->updateUserInterface(fcitx::UserInterfaceComponent::StatusArea);
            }));
            inputMethodMenu_->addAction(action);
        }

        charsetAction_ = std::make_unique<SimpleAction>();
        charsetAction_->setShortText(_("Bảng mã"));
        charsetAction_->setIcon("character-set");
        uiManager.registerAction("vmk-charset", charsetAction_.get());
        charsetMenu_ = std::make_unique<Menu>();
        charsetAction_->setMenu(charsetMenu_.get());

        auto charsets = convertToStringList(GetCharsetNames());
        for (const auto& charset : charsets) {
            charsetSubAction_.emplace_back(std::make_unique<SimpleAction>());
            auto action = charsetSubAction_.back().get();
            action->setShortText(charset);
            action->setCheckable(true);
            uiManager.registerAction(stringutils::concat(CharsetActionPrefix, charset), action);
            connections_.emplace_back(action->connect<SimpleAction::Activated>([this, charset](InputContext* ic) {
                if (config_.outputCharset.value() == charset)
                    return;

                LOG("Charset changed to: " + charset);
                config_.outputCharset.setValue(charset);
                saveConfig();
                refreshEngine();
                updateCharsetAction(ic);
                if (ic)
                    ic->updateUserInterface(fcitx::UserInterfaceComponent::StatusArea);
            }));
            charsetMenu_->addAction(action);
        }
        config_.outputCharset.annotation().setList(charsets);

        spellCheckAction_ = std::make_unique<SimpleAction>();
        spellCheckAction_->setLongText(_("Enable spell check"));
        spellCheckAction_->setIcon("tools-check-spelling");
        spellCheckAction_->setCheckable(true);
        connections_.emplace_back(spellCheckAction_->connect<SimpleAction::Activated>([this](InputContext* ic) {
            config_.spellCheck.setValue(!*config_.spellCheck);
            saveConfig();
            refreshOption();
            updateSpellAction(ic);

            std::ostringstream oss;
            oss << "Spell check: " << (*config_.spellCheck ? "enabled" : "disabled");
            LOG(oss.str());
        }));
        uiManager.registerAction("vmk-spellcheck", spellCheckAction_.get());

        macroAction_ = std::make_unique<SimpleAction>();
        macroAction_->setLongText(_("Enable Macro"));
        macroAction_->setIcon("document-edit");
        macroAction_->setCheckable(true);
        connections_.emplace_back(macroAction_->connect<SimpleAction::Activated>([this](InputContext* ic) {
            config_.macro.setValue(!*config_.macro);
            saveConfig();
            refreshOption();
            updateMacroAction(ic);

            std::ostringstream oss;
            oss << "Macro: " << (*config_.macro ? "enabled" : "disabled");
            LOG(oss.str());
        }));
        uiManager.registerAction("vmk-macro", macroAction_.get());

        capitalizeMacroAction_ = std::make_unique<SimpleAction>();
        capitalizeMacroAction_->setLongText(_("Capitalize Macro"));
        capitalizeMacroAction_->setIcon("format-text-uppercase");
        capitalizeMacroAction_->setCheckable(true);
        connections_.emplace_back(capitalizeMacroAction_->connect<SimpleAction::Activated>([this](InputContext* ic) {
            config_.capitalizeMacro.setValue(!*config_.capitalizeMacro);
            saveConfig();
            refreshOption();
            updateCapitalizeMacroAction(ic);
        }));
        uiManager.registerAction("vmk-capitalizemacro", capitalizeMacroAction_.get());

        autoNonVnRestoreAction_ = std::make_unique<SimpleAction>();
        autoNonVnRestoreAction_->setLongText(_("Auto restore keys with invalid words"));
        autoNonVnRestoreAction_->setIcon("edit-undo");
        autoNonVnRestoreAction_->setCheckable(true);
        connections_.emplace_back(autoNonVnRestoreAction_->connect<SimpleAction::Activated>([this](InputContext* ic) {
            config_.autoNonVnRestore.setValue(!*config_.autoNonVnRestore);
            saveConfig();
            refreshOption();
            updateAutoNonVnRestoreAction(ic);
        }));
        uiManager.registerAction("vmk-autonvnrestore", autoNonVnRestoreAction_.get());

        modernStyleAction_ = std::make_unique<SimpleAction>();
        modernStyleAction_->setLongText(_("Use oà, _uý (instead of òa, úy)"));
        modernStyleAction_->setIcon("text-x-generic");
        modernStyleAction_->setCheckable(true);
        connections_.emplace_back(modernStyleAction_->connect<SimpleAction::Activated>([this](InputContext* ic) {
            config_.modernStyle.setValue(!*config_.modernStyle);
            saveConfig();
            refreshOption();
            updateModernStyleAction(ic);
        }));
        uiManager.registerAction("vmk-modernstyle", modernStyleAction_.get());

        freeMarkingAction_ = std::make_unique<SimpleAction>();
        freeMarkingAction_->setLongText(_("Allow type with more freedom"));
        freeMarkingAction_->setIcon("document-open-recent");
        freeMarkingAction_->setCheckable(true);
        connections_.emplace_back(freeMarkingAction_->connect<SimpleAction::Activated>([this](InputContext* ic) {
            config_.freeMarking.setValue(!*config_.freeMarking);
            saveConfig();
            refreshOption();
            updateFreeMarkingAction(ic);
        }));
        uiManager.registerAction("vmk-freemarking", freeMarkingAction_.get());

        reloadConfig();
        globalMode_ = modeStringToEnum(config_.mode.value());
        updateModeAction(nullptr);
        instance_->inputContextManager().registerProperty("VMKState", &factory_);

        std::string configDir = StandardPath::global().userDirectory(StandardPath::Type::Config) + "/fcitx5/conf";
        if (!std::filesystem::exists(configDir)) {
            std::filesystem::create_directories(configDir);
        }
        appRulesPath_ = configDir + "/vmk-app-rules.conf";
        loadAppRules();

        LOG("==== vmkEngine constructor END ====");
    }

    void vmkEngine::reloadConfig() {
        LOG("reloadConfig() called");
        readAsIni(config_, "conf/vmk.conf");
        readAsIni(customKeymap_, CustomKeymapFile);
        for (const auto& imName : imNames_) {
            auto& table = macroTables_[imName];
            readAsIni(table, macroFile(imName));
            macroTableObject_[imName].reset(newMacroTable(table));
        }
        populateConfig();
        LOG("reloadConfig() complete");
    }

    const Configuration* vmkEngine::getSubConfig(const std::string& path) const {
        if (path == "custom_keymap")
            return &customKeymap_;
        if (stringutils::startsWith(path, MacroPrefix)) {
            const auto imName = path.substr(MacroPrefix.size());
            if (auto iter = macroTables_.find(imName); iter != macroTables_.end())
                return &iter->second;
        }
        return nullptr;
    }

    void vmkEngine::setConfig(const RawConfig& config) {
        LOG("setConfig() called");
        config_.load(config, true);
        saveConfig();
        populateConfig();
    }

    void vmkEngine::populateConfig() {
        LOG("populateConfig() called");
        refreshEngine();
        refreshOption();
        updateModeAction(nullptr);
        updateInputMethodAction(nullptr);
        updateCharsetAction(nullptr);
        updateSpellAction(nullptr);
        updateMacroAction(nullptr);
        updateCapitalizeMacroAction(nullptr);
        updateAutoNonVnRestoreAction(nullptr);
        updateModernStyleAction(nullptr);
        updateFreeMarkingAction(nullptr);
    }

    void vmkEngine::setSubConfig(const std::string& path, const RawConfig& config) {
        if (path == "custom_keymap") {
            customKeymap_.load(config, true);
            safeSaveAsIni(customKeymap_, CustomKeymapFile);
            refreshEngine();
            LOG("Custom keymap updated");
        } else if (stringutils::startsWith(path, MacroPrefix)) {
            const auto imName = path.substr(MacroPrefix.size());
            if (auto iter = macroTables_.find(imName); iter != macroTables_.end()) {
                iter->second.load(config, true);
                safeSaveAsIni(iter->second, macroFile(imName));
                macroTableObject_[imName].reset(newMacroTable(iter->second));
                refreshEngine();
                LOG("Macro table updated for: " + imName);
            }
        }
    }

    std::string vmkEngine::subMode(const fcitx::InputMethodEntry&, fcitx::InputContext&) {
        return *config_.inputMethod;
    }

    void vmkEngine::activate(const InputMethodEntry& entry, InputContextEvent& event) {
        LOG("==== activate() START ====");

        auto                     ic = event.inputContext();
        static std::atomic<bool> mouseThreadStarted{false};
        if (!mouseThreadStarted.exchange(true))
            startMouseReset();

        auto& statusArea = event.inputContext()->statusArea();
        if (ic->capabilityFlags().test(fcitx::CapabilityFlag::Preedit))
            instance_->inputContextManager().setPreeditEnabledByDefault(true);

        std::string        appName = ic->program();
        fcitx::VMKMode     targetMode;

        std::ostringstream oss;
        oss << "app=" << appName;
        LOG(oss.str());

        if (!appRules_.empty() && appRules_.count(appName)) {
            targetMode = appRules_[appName];
            std::ostringstream oss2;
            oss2 << "Using app-specific mode: " << modeEnumToString(targetMode);
            LOG(oss2.str());
        } else {
            targetMode = globalMode_;
            std::ostringstream oss2;
            oss2 << "Using global mode: " << modeEnumToString(targetMode);
            LOG(oss2.str());
        }
        reloadConfig();
        updateModeAction(event.inputContext());
        updateInputMethodAction(event.inputContext());
        updateCharsetAction(event.inputContext());

        realMode = targetMode;

        auto state = ic->propertyFor(&factory_);

        state->clearAllBuffers();
        is_deleting_.store(false);
        needEngineReset.store(false);
        ic->inputPanel().reset();
        ic->updateUserInterface(UserInterfaceComponent::InputPanel);
        ic->updatePreedit();

        statusArea.addAction(StatusGroup::InputMethod, modeAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, inputMethodAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, charsetAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, spellCheckAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, macroAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, capitalizeMacroAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, autoNonVnRestoreAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, modernStyleAction_.get());
        statusArea.addAction(StatusGroup::InputMethod, freeMarkingAction_.get());

        LOG_CURSOR("ACTIVATE_END", ic, "");
        state->logState("ACTIVATE_END");
        LOG("==== activate() END ====");
    }

    void vmkEngine::keyEvent(const InputMethodEntry& entry, KeyEvent& keyEvent) {
        auto ic = keyEvent.inputContext();

        if (isSelectingAppMode_ && g_mouse_clicked.load(std::memory_order_relaxed)) {
            LOG("Mouse click detected - closing app mode menu");
            closeAppModeMenu();
            ic->inputPanel().reset();
            ic->updateUserInterface(UserInterfaceComponent::InputPanel);
            auto state = ic->propertyFor(&factory_);
            state->reset();
        }

        if (isSelectingAppMode_) {
            if (keyEvent.isRelease())
                return;

            keyEvent.filterAndAccept();
            fcitx::VMKMode selectedMode  = fcitx::VMKMode::NoMode;
            bool           selectionMade = false;

            if (keyEvent.key().check(FcitxKey_1)) {
                selectedMode = fcitx::VMKMode::VMK1;
                LOG("Selected mode: VMK1");
            } else if (keyEvent.key().check(FcitxKey_2)) {
                selectedMode = fcitx::VMKMode::VMK2;
                LOG("Selected mode: VMK2");
            } else if (keyEvent.key().check(FcitxKey_3)) {
                selectedMode = fcitx::VMKMode::Preedit;
                LOG("Selected mode: Preedit");
            } else if (keyEvent.key().check(FcitxKey_4)) {
                selectedMode = fcitx::VMKMode::VMK1HC;
                LOG("Selected mode: VMK1HC");
            } else if (keyEvent.key().check(FcitxKey_5)) {
                selectedMode = fcitx::VMKMode::Off;
                LOG("Selected mode: Off");
            } else if (keyEvent.key().check(FcitxKey_6)) {
                if (appRules_.count(currentConfigureApp_)) {
                    appRules_.erase(currentConfigureApp_);
                    saveAppRules();
                    LOG("Removed app rule for: " + currentConfigureApp_);
                }
                selectionMade = true;
            } else if (keyEvent.key().check(FcitxKey_Escape)) {
                LOG("Escape pressed - canceling");
                selectionMade = true;
            } else if (keyEvent.key().check(FcitxKey_grave)) {
                isSelectingAppMode_ = false;
                ic->inputPanel().reset();
                ic->updateUserInterface(UserInterfaceComponent::InputPanel);
                auto state = ic->propertyFor(&factory_);
                state->reset();
                ic->commitString("`");
                LOG("Backtick pressed - closing menu and committing `");
                return;
            }

            if (selectedMode != fcitx::VMKMode::NoMode) {
                appRules_[currentConfigureApp_] = selectedMode;
                saveAppRules();

                realMode      = selectedMode;
                selectionMade = true;

                std::ostringstream oss;
                oss << "Saved app rule: " << currentConfigureApp_ << " -> " << modeEnumToString(selectedMode);
                LOG(oss.str());
            }

            if (selectionMade) {
                isSelectingAppMode_ = false;
                ic->inputPanel().reset();
                ic->updateUserInterface(UserInterfaceComponent::InputPanel);
                auto state = ic->propertyFor(&factory_);
                state->reset();
                LOG("App mode menu closed");
            }
            return;
        }

        if (!keyEvent.isRelease() && keyEvent.rawKey().check(FcitxKey_grave)) {
            currentConfigureApp_ = ic->program();
            if (currentConfigureApp_.empty())
                currentConfigureApp_ = "unknown-app";
            g_mouse_clicked.store(false, std::memory_order_relaxed);

            LOG("Opening app mode menu for: " + currentConfigureApp_);
            showAppModeMenu(ic);
            keyEvent.filterAndAccept();
            return;
        }
        auto state = keyEvent.inputContext()->propertyFor(&factory_);
        state->keyEvent(keyEvent);
        state->logState("FUCKU");
        LOG_CURSOR("END_END_KEY_PRESS", ic, "");

        // UPDATE realtextLen when cursor pos is report
        // correct here
        auto        s       = ic->surroundingText();
        const auto& text    = s.text();
        size_t      textLen = fcitx_utf8_strlen(text.c_str());
        int         cursor  = s.cursor();
        if (textLen == static_cast<size_t>(cursor)) {
            realtextLen = textLen;
            LOG("UPDATE REAL TEXT LEN???");
        }
        // else if (textLen == static_cast<size_t>(realtextLen)){
        //     realtextLen = cursor;
        //     LOG("MAYBE FIX TODO?? cursor="+std::to_string(cursor));
        // }
    }

    void vmkEngine::reset(const InputMethodEntry& entry, InputContextEvent& event) {
        LOG("==== reset() (engine level) START ====");

        std::ostringstream oss;
        oss << "Reset event - app=" << event.inputContext()->program() << " type="
            << (event.type() == EventType::InputContextFocusOut              ? "FocusOut" :
                    event.type() == EventType::InputContextSwitchInputMethod ? "SwitchIM" :
                                                                               "Other");
        LOG(oss.str());

        auto state = event.inputContext()->propertyFor(&factory_);
        state->reset();

        LOG("==== reset() (engine level) END ====");
    }

    void vmkEngine::deactivate(const InputMethodEntry& entry, InputContextEvent& event) {
        LOG("==== deactivate() START ====");

        std::ostringstream oss;
        oss << "app=" << event.inputContext()->program() << " type="
            << (event.type() == EventType::InputContextFocusOut              ? "FocusOut" :
                    event.type() == EventType::InputContextSwitchInputMethod ? "SwitchIM" :
                                                                               "Other")
            << " mode=" << fcitx::modeEnumToString(realMode);
        LOG(oss.str());

        LOG_CURSOR("DEACTIVATE_START", event.inputContext(), "");

        auto state = event.inputContext()->propertyFor(&factory_);
        state->logState("DEACTIVATE_START");

        if (realMode == fcitx::VMKMode::Preedit) {
            if (event.type() != EventType::InputContextFocusOut) {
                LOG("Committing preedit buffer");
                state->commitBuffer();
            } else {
                LOG("Focus out - resetting instead of committing");
                state->reset();
            }
        } else {
            LOG("Clearing all buffers for non-preedit mode");
            state->clearAllBuffers();
            is_deleting_.store(false);
            needEngineReset.store(false);
            event.inputContext()->inputPanel().reset();
            event.inputContext()->updateUserInterface(UserInterfaceComponent::InputPanel);
            event.inputContext()->updatePreedit();
        }

        LOG_CURSOR("DEACTIVATE_END", event.inputContext(), "");
        state->logState("DEACTIVATE_END");
        LOG("==== deactivate() END ====");
    }

    void vmkEngine::refreshEngine() {
        LOG("refreshEngine() called");
        if (!factory_.registered())
            return;
        instance_->inputContextManager().foreach ([this](InputContext* ic) {
            auto state = ic->propertyFor(&factory_);
            state->setEngine();
            if (ic->hasFocus())
                state->reset();
            return true;
        });
        LOG("refreshEngine() complete");
    }

    void vmkEngine::refreshOption() {
        LOG("refreshOption() called");
        if (!factory_.registered())
            return;
        instance_->inputContextManager().foreach ([this](InputContext* ic) {
            auto state = ic->propertyFor(&factory_);
            state->setOption();
            if (ic->hasFocus())
                state->reset();
            return true;
        });
        LOG("refreshOption() complete");
    }

    void vmkEngine::updateModeAction(InputContext* ic) {
        std::string currentModeStr = config_.mode.value();
        realMode                   = fcitx::modeStringToEnum(currentModeStr);
        globalMode_                = realMode;

        for (const auto& action : modeSubAction_) {
            action->setChecked(action->name() == "vmk-mode-" + currentModeStr);
            if (ic)
                action->update(ic);
        }
        modeAction_->setLongText(_("Typing Mode: ") + currentModeStr);

        if (ic) {
            modeAction_->update(ic);
        }
    }

    void vmkEngine::updateInputMethodAction(InputContext* ic) {
        auto name = stringutils::concat(InputMethodActionPrefix, *config_.inputMethod);
        for (const auto& action : inputMethodSubAction_) {
            action->setChecked(action->name() == name);
            if (ic)
                action->update(ic);
        }
        if (ic) {
            inputMethodAction_->setLongText(stringutils::concat("Input Method: ", *config_.inputMethod));
            inputMethodAction_->update(ic);
        }
    }

    void vmkEngine::updateCharsetAction(InputContext* ic) {
        auto name = stringutils::concat(CharsetActionPrefix, *config_.outputCharset);
        for (const auto& action : charsetSubAction_) {
            action->setChecked(action->name() == name);
            if (ic)
                action->update(ic);
        }
    }

    void vmkEngine::updateSpellAction(InputContext* ic) {
        spellCheckAction_->setChecked(*config_.spellCheck);
        spellCheckAction_->setShortText(*config_.spellCheck ? _("Spell Check: Bật") : _("Spell Check: Tắt"));
        if (ic) {
            spellCheckAction_->update(ic);
        }
    }

    void vmkEngine::updateMacroAction(InputContext* ic) {
        macroAction_->setChecked(*config_.macro);
        macroAction_->setShortText(*config_.macro ? _("Macro: Bật") : _("Macro: Tắt"));
        if (ic) {
            macroAction_->update(ic);
        }
    }

    void vmkEngine::updateCapitalizeMacroAction(InputContext* ic) {
        capitalizeMacroAction_->setChecked(*config_.capitalizeMacro);
        capitalizeMacroAction_->setShortText(*config_.capitalizeMacro ? _("Capitalize Macro: Bật") : _("Capitalize Macro: Tắt"));
        if (ic) {
            capitalizeMacroAction_->update(ic);
        }
    }

    void vmkEngine::updateAutoNonVnRestoreAction(InputContext* ic) {
        autoNonVnRestoreAction_->setChecked(*config_.autoNonVnRestore);
        autoNonVnRestoreAction_->setShortText(*config_.autoNonVnRestore ? _("Auto Non-VN Restore: Bật") : _("Auto Non-VN Restore: Tắt"));
        if (ic) {
            autoNonVnRestoreAction_->update(ic);
        }
    }

    void vmkEngine::updateModernStyleAction(InputContext* ic) {
        modernStyleAction_->setChecked(*config_.modernStyle);
        modernStyleAction_->setShortText(*config_.modernStyle ? _("Modern Style: Bật") : _("Modern Style: Tắt"));
        if (ic) {
            modernStyleAction_->update(ic);
        }
    }

    void vmkEngine::updateFreeMarkingAction(InputContext* ic) {
        freeMarkingAction_->setChecked(*config_.freeMarking);
        freeMarkingAction_->setShortText(*config_.freeMarking ? _("Free Marking: Bật") : _("Free Marking: Tắt"));
        if (ic) {
            freeMarkingAction_->update(ic);
        }
    }
    void vmkEngine::loadAppRules() {
        LOG("Loading app rules from: " + appRulesPath_);
        appRules_.clear();
        std::ifstream file(appRulesPath_);
        if (!file.is_open()) {
            LOG("App rules file not found");
            return;
        }

        std::string line;
        int         lineCount = 0;
        while (std::getline(file, line)) {
            lineCount++;
            if (line.empty() || line[0] == '#')
                continue;
            auto delimiterPos = line.find('=');
            if (delimiterPos != std::string::npos) {
                std::string app     = line.substr(0, delimiterPos);
                std::string modeStr = line.substr(delimiterPos + 1);
                appRules_[app]      = fcitx::modeStringToEnum(modeStr);

                std::ostringstream oss;
                oss << "Loaded rule: " << app << " -> " << modeStr;
                LOG(oss.str());
            }
        }
        file.close();

        std::ostringstream oss;
        oss << "Loaded " << appRules_.size() << " app rules from " << lineCount << " lines";
        LOG(oss.str());
    }

    void vmkEngine::saveAppRules() {
        LOG("Saving app rules to: " + appRulesPath_);
        std::ofstream file(appRulesPath_, std::ios::trunc);
        if (!file.is_open()) {
            LOG("Failed to open app rules file for writing");
            return;
        }

        file << "# VMK Per-App Configuration\n";
        for (const auto& pair : appRules_) {
            std::string modeStr = fcitx::modeEnumToString(pair.second);
            file << pair.first << "=" << modeStr << "\n";
        }
        file.close();

        std::ostringstream oss;
        oss << "Saved " << appRules_.size() << " app rules";
        LOG(oss.str());
    }

    void vmkEngine::closeAppModeMenu() {
        LOG("closeAppModeMenu() called");
        isSelectingAppMode_ = false;
        g_mouse_clicked.store(false, std::memory_order_relaxed);
    }

    void vmkEngine::showAppModeMenu(InputContext* ic) {
        LOG("showAppModeMenu() called for app: " + currentConfigureApp_);
        isSelectingAppMode_ = true;

        auto candidateList = std::make_unique<CommonCandidateList>();

        candidateList->setLayoutHint(CandidateLayoutHint::Vertical);
        candidateList->setPageSize(7);

        fcitx::VMKMode currentAppRules = fcitx::VMKMode::Off;
        if (appRules_.count(currentConfigureApp_)) {
            currentAppRules = appRules_[currentConfigureApp_];
        } else {
            currentAppRules = globalMode_;
        }

        auto getLabel = [&](const fcitx::VMKMode& modeName, const std::string& modeLabel) {
            if (modeName == currentAppRules) {
                return Text(modeLabel + " (Default)");
            } else {
                return Text(modeLabel);
            }
        };

        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(Text(_("App name detected by fcitx5: ") + currentConfigureApp_)));
        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(getLabel(fcitx::VMKMode::VMK1, _("1. Fake backspace by Uinput"))));
        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(getLabel(fcitx::VMKMode::VMK2, _("2. Surrounding Text"))));
        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(getLabel(fcitx::VMKMode::Preedit, _("3. Preedit"))));
        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(getLabel(fcitx::VMKMode::VMK1HC, _("4. Fake backspace by Uinput for wine apps"))));
        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(getLabel(fcitx::VMKMode::Off, "5. OFF - Disable Input Method")));
        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(Text(_("6. Remove app settings"))));
        candidateList->append(std::make_unique<DisplayOnlyCandidateWord>(Text(_("`. Close menu and type `"))));

        ic->inputPanel().reset();
        ic->inputPanel().setCandidateList(std::move(candidateList));
        ic->updateUserInterface(UserInterfaceComponent::InputPanel);
        LOG("App mode menu displayed");
    }
} // namespace fcitx

FCITX_ADDON_FACTORY(fcitx::vmkFactory)

std::string SubstrChar(const std::string& s, size_t start, size_t len) {
    if (s.empty())
        return "";
    const char* start_ptr = fcitx_utf8_get_nth_char(s.c_str(), static_cast<uint32_t>(start));
    if (*start_ptr == '\0')
        return "";
    if (len == std::string::npos)
        return std::string(start_ptr);
    const char* end_ptr = fcitx_utf8_get_nth_char(start_ptr, static_cast<uint32_t>(len));
    return std::string(start_ptr, end_ptr - start_ptr);
}

int compareAndSplitStrings(const std::string& A, const std::string& B, std::string& commonPrefix, std::string& deletedPart, std::string& addedPart) {
    size_t lengthA     = fcitx_utf8_strlen(A.c_str());
    size_t lengthB     = fcitx_utf8_strlen(B.c_str());
    size_t minLength   = std::min(lengthA, lengthB);
    size_t matchLength = 0;
    for (size_t i = 0; i < minLength; ++i) {
        const char*  ptrA = fcitx_utf8_get_nth_char(A.c_str(), static_cast<uint32_t>(i));
        const char*  ptrB = fcitx_utf8_get_nth_char(B.c_str(), static_cast<uint32_t>(i));
        unsigned int lenA = fcitx_utf8_char_len(ptrA);
        unsigned int lenB = fcitx_utf8_char_len(ptrB);
        if (lenA == lenB && std::strncmp(ptrA, ptrB, lenA) == 0)
            ++matchLength;
        else
            break;
    }
    commonPrefix = SubstrChar(A, 0, matchLength);
    deletedPart  = SubstrChar(A, matchLength, std::string::npos);
    addedPart    = SubstrChar(B, matchLength, std::string::npos);
    return (deletedPart.empty() && addedPart.empty()) ? 1 : 2;
}