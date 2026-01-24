#include <atomic>
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <libinput.h>
#include <libudev.h>
#include <linux/input.h>
#include <linux/uinput.h>
#include <poll.h>
#include <pwd.h>
#include <sched.h>
#include <string>
#include <sys/ioctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <thread>
#include <unistd.h>
namespace fs = std::filesystem;

// event id for mouse event
#define EV_DEVICE_ADDED 1
#define EV_POINTER_BUTTON 402

static int uinput_fd_ = -1;
static std::string MOUSE_FLAG_PATH;
std::atomic<bool> stop_mouse_thread(false);

// get username
std::string get_current_username() {
    struct passwd *pw = getpwuid(getuid());
    return pw ? pw->pw_name : "unknown";
}

// setup environment in /dev/shm/vmksocket-<username>
void setup_environment(std::string target_user) {
    fs::path base_path = "/dev/shm/vmksocket-" + target_user;

    try {
        if (!fs::exists(base_path)) {
            fs::create_directories(base_path);
            fs::permissions(base_path, fs::perms::all,
                            fs::perm_options::replace);
        }

        MOUSE_FLAG_PATH = (base_path / ".mouse_flag").string();
        fs::remove(MOUSE_FLAG_PATH);

    } catch (const std::exception &e) {
        std::cerr << "Error when setup environment: " << e.what() << std::endl;
        exit(1);
    }
}

// system functions
static void boost_process_priority() { setpriority(PRIO_PROCESS, 0, -10); }

static void pin_to_pcore() {
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    for (int i = 0; i <= 3; ++i)
        CPU_SET(i, &cpuset);
    sched_setaffinity(0, sizeof(cpuset), &cpuset);
}

static inline void sleep_us(long us) {
    struct timespec ts;
    ts.tv_sec = us / 1000000;
    ts.tv_nsec = (us % 1000000) * 1000;
    clock_nanosleep(CLOCK_MONOTONIC, 0, &ts, nullptr);
}

// input injector functions
void send_uinput_event(int type, int code, int value) {
    if (uinput_fd_ < 0)
        return;
    struct input_event ev;
    memset(&ev, 0, sizeof(ev));
    ev.type = type;
    ev.code = code;
    ev.value = value;
    write(uinput_fd_, &ev, sizeof(ev));
}

// FIXED BACKSPACE: hold left key, send MSC_SCAN
void send_backspace_uinput(int count) {
    if (uinput_fd_ < 0)
        return;
    if (count <= 0)
        return;
    if (count > 10)
        count = 10;

    const int INTER_KEY_DELAY_US = 1200; // 1ms between backspace

    for (int i = 0; i < count; ++i) {
        send_uinput_event(EV_KEY, KEY_BACKSPACE, 1);
        send_uinput_event(EV_SYN, SYN_REPORT, 0);

        send_uinput_event(EV_KEY, KEY_BACKSPACE, 0);
        send_uinput_event(EV_SYN, SYN_REPORT, 0);

        sleep_us(INTER_KEY_DELAY_US);
    }
}
// mouse monitor
static const struct libinput_interface interface = {
    .open_restricted = [](const char *path, int flags, void *user_data) -> int {
        return open(path, flags);
    },
    .close_restricted = [](int fd, void *user_data) { close(fd); }};

void mousePressMonitorThread() {
    struct udev *udev = udev_new();
    struct libinput *li = libinput_udev_create_context(&interface, NULL, udev);
    libinput_udev_assign_seat(li, "seat0");

    // save last write time
    auto last_write_time = std::chrono::steady_clock::now();

    while (!stop_mouse_thread.load()) {
        // clear pending events
        libinput_dispatch(li);

        struct libinput_event *event;
        while ((event = libinput_get_event(li))) {
            int type = (int)libinput_event_get_type(event);

            if (type == EV_DEVICE_ADDED) {
                struct libinput_device *dev = libinput_event_get_device(event);
                if (libinput_device_config_tap_get_finger_count(dev) > 0) {
                    libinput_device_config_tap_set_enabled(
                        dev, LIBINPUT_CONFIG_TAP_ENABLED);
                    libinput_device_config_tap_set_button_map(
                        dev, LIBINPUT_CONFIG_TAP_MAP_LRM);
                }
            } else if (type == EV_POINTER_BUTTON) {
                struct libinput_event_pointer *p =
                    libinput_event_get_pointer_event(event);
                if (libinput_event_pointer_get_button_state(p) ==
                    1) { // Pressed

                    auto now = std::chrono::steady_clock::now();
                    // calculate elapsed time
                    auto elapsed =
                        std::chrono::duration_cast<std::chrono::milliseconds>(
                            now - last_write_time)
                            .count();

                    // delay 1000ms to avoid system too slow
                    if (elapsed >= 1000) {
                        std::ofstream flag(MOUSE_FLAG_PATH, std::ios::trunc);
                        if (flag.is_open()) {
                            flag << "Y=1\n";
                            flag.close();
                            last_write_time = now; // update last write time
                            chmod(MOUSE_FLAG_PATH.c_str(), 0666);
                        }
                    } else {
                    }
                }
            }
            libinput_event_destroy(event);
        }
        // sleep 5ms to reduce CPU usage
        usleep(5000);
    }
    libinput_unref(li);
    udev_unref(udev);
}
// main function
int main(int argc, char *argv[]) {
    std::string target_user;
    if (argc == 3 && std::string(argv[1]) == "-u") {
        target_user = argv[2];
    } else {
        target_user = get_current_username();
    }
    boost_process_priority();
    pin_to_pcore();

    setup_environment(target_user);
    std::string socket_path =
        ("/dev/shm/vmksocket-" + target_user + "/kb_socket");

    // Setup Uinput
    uinput_fd_ = open("/dev/uinput", O_WRONLY | O_NONBLOCK);
    if (uinput_fd_ >= 0) {
        ioctl(uinput_fd_, UI_SET_EVBIT, EV_KEY);
        ioctl(uinput_fd_, UI_SET_KEYBIT, KEY_BACKSPACE);
        struct uinput_user_dev uidev{};
        snprintf(uidev.name, UINPUT_MAX_NAME_SIZE, "Fcitx5_Uinput_Server");
        (void)write(uinput_fd_, &uidev, sizeof(uidev));
        ioctl(uinput_fd_, UI_DEV_CREATE);
    }

    // Setup Socket
    int server_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    struct sockaddr_un addr{.sun_family = AF_UNIX};
    strncpy(addr.sun_path, socket_path.c_str(), sizeof(addr.sun_path) - 1);
    unlink(socket_path.c_str());
    if (bind(server_fd, (struct sockaddr *)&addr, sizeof(addr)) == 0) {
        chmod(socket_path.c_str(), 0666); // allow read/write
        listen(server_fd, 5);
    }

    // Run mouse monitor thread
    std::thread(mousePressMonitorThread).detach();

    while (true) {
        int client_fd = accept(server_fd, nullptr, nullptr);
        if (client_fd < 0)
            continue;
        char buf[256];
        int n = recv(client_fd, buf, sizeof(buf) - 1, 0);
        if (n > 0) {
            buf[n] = 0;
            std::string cmd(buf);
            if (cmd.find("BACKSPACE_") == 0) {
                try {
                    send_backspace_uinput(std::stoi(cmd.substr(10)));
                } catch (...) {
                }
            }
        }
        close(client_fd);
    }
    return 0;
}