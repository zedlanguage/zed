# How the OS layer's failures map to Zed atoms (STUDY-os-error-map)

Study for plan rows STUDY-os-error-map and SPEC-c14-answer, 2026-11-17, agent os-errors. The spec text it led to is in DESIGN (sec:ports, "Why an operation failed"); this file keeps the evidence: every failure mode of the file, directory, process and socket operations of libzed's OS layer, on Linux, macOS and Windows, and the member of the canonical list each one maps to.

## 1. What the author asked

QUESTIONS C14, answered by the author (P346, 2026-11-17), verbatim:

> We need `#notFound` too (I think this is better than `#missing`, and probably `#notAFile` when trying to open a dir as a file (we also need a way to enumerate the files in a directory... schedule a task to brainstorm that). But yes, use the written family with those two additions. What is `#exists` for though? List out the failure modes for the 3 main OSes, and map them to a canonical list.

The written family (row PORT-why) was `#denied | #noSpace | #exists | #busy | #interrupted | #other(code)`. The rule for choosing between an atom and a fact is the author's rule for float failures (DESIGN "Float failures", P354 to P361): "if an operation can produce a value that is simply absolutely wrong or unusable, then it should become an atom in @fpstrict, otherwise it should be a taint."

## 2. Sources

- Linux: man-pages 6.13 as installed on this host (Fedora 44, kernel 7.3.3), the ERRORS section of each page named below, section 2 (system calls), 3 (library functions) and 7 (overviews: `ip(7)`, `tcp(7)`, `unix(7)`, `socket(7)`). Every Linux row cites its page.
- macOS: the errno names and numbers of XNU as Go 1.26 lists them (`/usr/lib/golang/src/syscall/zerrors_darwin_arm64.go`); macOS uses the same POSIX names as Linux for every code the two share, and the codes only macOS has are listed in section 5. Which call gives which code on macOS is inferred from the POSIX pages and the Linux pages; confirming it on Apple hardware belongs to row REL-macos.
- Windows: the values of `windows-sys` 0.61.2 (`~/.cargo/registry/src/*/windows-sys-0.61.2/`), Win32 error codes from `GetLastError`, Winsock codes from `WSAGetLastError`, and NTSTATUS values. Which call gives which code is inferred from Microsoft's documentation of each function and from the maps of Rust and Go; confirming it belongs to row REL-windows.
- Other implementations (the standing rule asks for at least three; their defects become tests, not code):
  - Rust std 1.93, `decode_error_kind` in `library/std/src/sys/pal/unix/mod.rs` and `library/std/src/sys/pal/windows/mod.rs`.
  - Go 1.26, `Errno.Is`, `Temporary` and `Timeout` in `/usr/lib/golang/src/syscall/syscall_unix.go` and `syscall_windows.go`.
  - Python 3, the `OSError` subclasses of PEP 3151 (`FileNotFoundError`, `FileExistsError`, `IsADirectoryError`, `NotADirectoryError`, `PermissionError`, `InterruptedError`, `BlockingIOError`, `ConnectionRefusedError`, `ConnectionResetError`, `ConnectionAbortedError`, `BrokenPipeError`, `TimeoutError`, `ChildProcessError`, `ProcessLookupError`), from the PEP; not run, since the project uses no Python.

## 3. The canonical list

The member is the field `why` of `#ioError(op:, path:, why:, text:)`, of the prelude type `IoReason`; `text` keeps the operating system's message. Members the author named are marked (author); the others are added by this study where a failure mode had no member and would otherwise fall into `#other(code)`.

| Member | Meaning, in the program's terms | `retry` retries it | Main codes (Linux and macOS / Windows) |
|---|---|---|---|
| `#notFound` (author) | The path, a directory on it, the program, the host or the device does not exist | no | ENOENT, ENXIO (no device), EAI_NONAME, EAI_NODATA, EADDRNOTAVAIL at `bind` / ERROR_FILE_NOT_FOUND, ERROR_PATH_NOT_FOUND, ERROR_INVALID_DRIVE, ERROR_BAD_NETPATH, ERROR_BAD_NET_NAME, WSAHOST_NOT_FOUND, WSANO_DATA |
| `#notAFile` (author) | The path names a directory, or another thing that is not a file the operation can use (a socket, a device) | no | EISDIR, ENXIO (socket file), ENODEV, EFTYPE (macOS) / ERROR_DIRECTORY_NOT_SUPPORTED, STATUS_FILE_IS_A_DIRECTORY; ERROR_ACCESS_DENIED on a directory, told apart by the layer (section 7) |
| `#notADirectory` | A name on the path that must be a directory is a file | no | ENOTDIR / ERROR_DIRECTORY, STATUS_NOT_A_DIRECTORY |
| `#denied` (author) | Permission is refused: by the file's mode, a read-only file system, a security policy, a firewall | no | EACCES, EPERM, EROFS, EAUTH and ENEEDAUTH (macOS) / ERROR_ACCESS_DENIED, ERROR_WRITE_PROTECT, ERROR_PRIVILEGE_NOT_HELD, ERROR_ELEVATION_REQUIRED, WSAEACCES |
| `#exists` (author) | The name the operation must create is taken, or the directory it must remove is not empty | no | EEXIST, ENOTEMPTY / ERROR_FILE_EXISTS, ERROR_ALREADY_EXISTS, ERROR_DIR_NOT_EMPTY |
| `#busy` (author) | Something else holds the file, the program or the address now | yes | EBUSY, ETXTBSY, EADDRINUSE, EWOULDBLOCK on a lock / ERROR_SHARING_VIOLATION, ERROR_LOCK_VIOLATION, ERROR_BUSY, STATUS_DELETE_PENDING, WSAEADDRINUSE |
| `#noSpace` (author) | The device or the user's quota is full | no | ENOSPC, EDQUOT / ERROR_DISK_FULL, ERROR_HANDLE_DISK_FULL, ERROR_DISK_QUOTA_EXCEEDED, WSAEDQUOT |
| `#limit` | A count the process or the system allows is used up: open files, processes, memory, buffers, links, local ports | yes | EMFILE, ENFILE, ENOMEM, ENOBUFS, EAGAIN at `fork`/`clone`/`execve`, EMLINK, EADDRNOTAVAIL at `connect`, EPROCLIM and EQFULL (macOS) / ERROR_TOO_MANY_OPEN_FILES, ERROR_NOT_ENOUGH_MEMORY, ERROR_OUTOFMEMORY, ERROR_NO_SYSTEM_RESOURCES, ERROR_TOO_MANY_LINKS, WSAEMFILE, WSAENOBUFS |
| `#tooLarge` | A value is larger than the operation takes: a file past the size limit, an argument list, a datagram | no | EFBIG, E2BIG, EMSGSIZE, EOVERFLOW / ERROR_FILE_TOO_LARGE, WSAEMSGSIZE |
| `#badName` | The path cannot name anything: too long, a loop of links, a byte the file system refuses | no | ENAMETOOLONG, ELOOP, EILSEQ, a NUL byte (found by the layer before the call) / ERROR_INVALID_NAME, ERROR_BAD_PATHNAME, ERROR_FILENAME_EXCED_RANGE, ERROR_CANT_RESOLVE_FILENAME, STATUS_OBJECT_NAME_INVALID |
| `#notExecutable` | The program exists but is not one this machine can run | no | ENOEXEC, ELIBBAD, EBADARCH, EBADEXEC, EBADMACHO, ESHLIBVERS (macOS) / ERROR_BAD_EXE_FORMAT, ERROR_BAD_FORMAT, ERROR_EXE_MACHINE_TYPE_MISMATCH, ERROR_INVALID_EXE_SIGNATURE |
| `#refused` | Nothing listens at the address | yes | ECONNREFUSED / WSAECONNREFUSED, ERROR_CONNECTION_REFUSED |
| `#unreachable` | The network or the host cannot be reached, or did not answer the connection, or the name server did not answer | yes | ENETUNREACH, EHOSTUNREACH, ENETDOWN, EHOSTDOWN, ETIMEDOUT at `connect`, EAI_AGAIN / WSAENETUNREACH, WSAEHOSTUNREACH, WSAENETDOWN, WSAEHOSTDOWN, WSAETIMEDOUT, WSATRY_AGAIN, ERROR_NETWORK_UNREACHABLE, ERROR_HOST_UNREACHABLE |
| `#lost` | The other end of a connection or pipe went away | yes, on an operation `retry` accepts | EPIPE, ECONNRESET, ECONNABORTED, ENOTCONN, ESHUTDOWN, ETIMEDOUT on an open connection / WSAECONNRESET, WSAECONNABORTED, WSAENETRESET, WSAENOTCONN, WSAESHUTDOWN, ERROR_BROKEN_PIPE, ERROR_NO_DATA, ERROR_PIPE_NOT_CONNECTED, ERROR_NETNAME_DELETED |
| `#deviceError` | The device failed to read or write, or went away | no | EIO, EREMOTEIO, ENOMEDIUM, ESTALE, EDEVERR and EPWROFF (macOS) / ERROR_CRC, ERROR_IO_DEVICE, ERROR_NOT_READY, ERROR_SECTOR_NOT_FOUND, STATUS_DEVICE_DATA_ERROR, STATUS_IO_DEVICE_ERROR |
| `#unsupported` | The host or the file system does not do this operation | no | EOPNOTSUPP, ENOTSUP, ENOSYS / ERROR_NOT_SUPPORTED, ERROR_CALL_NOT_IMPLEMENTED, STATUS_NOT_SUPPORTED; and a Landlock ABI below what `restrict` needs (DESIGN sec:ffi) |
| `#interrupted` (author) | A signal stopped the call before it finished | yes | EINTR; the layer restarts the call itself, so on Linux and macOS no operation gives it (section 6) |
| `#other(code: int)` | Any other code, the OS's own number, with `text` | no | EXDEV, EINVAL from a value the program gave, EPROTO, EAI_FAIL / ERROR_NOT_SAME_DEVICE, ERROR_INVALID_PARAMETER, WSANO_RECOVERY |

Codes that only a defect of the layer can give (EBADF, EFAULT, ENOTSOCK, EISCONN, EALREADY, EDESTADDRREQ, EAFNOSUPPORT, EPROTOTYPE, ESRCH on a pidfd the layer holds, ECHILD, EINVAL from flags the layer chose, ERROR_INVALID_HANDLE) are not failures of the program: they are an internal fault of the runtime, reported as a compiler bug with the build's content address (DESIGN sec:failure), as other internal faults are.

**Why each member that is not the author's was added.** Each one is a failure mode with a fix a program or its user can act on that no author member gives, and each has a match in at least two of Rust, Go and Python:

- `#notADirectory`: a file in the place of a directory (`a/b.txt` where `a` is a file) is fixed by moving the file, not by creating a directory. Rust `NotADirectory`, Python `NotADirectoryError`.
- `#limit`: a count used up (open files, processes) is a fault of the run, not of the path, and often passes when other work finishes, so `retry` takes it. Rust `OutOfMemory`; Go `Temporary()` is true for EMFILE and ENFILE.
- `#tooLarge`: the value is the problem; repeating cannot help. Rust `FileTooLarge`, `ArgumentListTooLong`.
- `#badName`: the path can name nothing; Rust `InvalidFilename`, `FilesystemLoop`.
- `#notExecutable`: the program is there but cannot run here; DESIGN sec:ports already names this case ("not executable") in the start-failure sentence.
- `#refused`, `#unreachable`, `#lost`: the three ways a peer is not there. Rust `ConnectionRefused`, `HostUnreachable`/`NetworkUnreachable`, `ConnectionReset`/`BrokenPipe`; Python the `ConnectionError` subclasses. `#lost` is the atom DESIGN already gives a call on a dropped connection (sec:robustness, "How lost work comes back").
- `#deviceError`: the data may be damaged; the user must look at the device. Rust has no kind (Uncategorized), Go none: a gap in both.
- `#unsupported`: the operation cannot work on this host or file system however often it is tried, and the fix is another host, file system or option. DESIGN already had the case without a member: `restrict` on a host whose Landlock is too old. Rust `Unsupported` (ENOSYS, EOPNOTSUPP, ERROR_CALL_NOT_IMPLEMENTED), Go `errors.ErrUnsupported` (ENOSYS, ENOTSUP, EOPNOTSUPP, ERROR_NOT_SUPPORTED, ERROR_CALL_NOT_IMPLEMENTED).

## 4. Linux, by operation

Each row: the code, the page, what causes it, the member. "Layer" means a code the layer's own choice of flags or descriptors causes, an internal fault.

### 4.1 Reading a whole file: `fs[path]`, `fs::bytes[path]`

The intrinsic opens with `open(path, O_RDONLY | O_CLOEXEC)`, checks the kind with `fstat`, reads to the end with `read` and closes.

| Code | Page | Cause | Gives |
|---|---|---|---|
| ENOENT | open(2) | no file at the path, or a directory on it missing | `#notFound` (the read's answer, not an `#ioError`) |
| ENOTDIR | open(2) | a name on the path is a file | `#notFound` (the answer: no file at the path) |
| EACCES | open(2) | no read permission, or no search permission on a directory of the path | `#denied` |
| EPERM | open(2) | `O_NOATIME` without ownership (not used), a sealed file | `#denied` |
| EISDIR | open(2), read(2) | the path names a directory; `open` with `O_RDONLY` succeeds on a directory, so `fstat` finds it, or `read` gives EISDIR | `#notAFile` |
| ENXIO | open(2) | a socket file, or a device file with no device | `#notAFile` (socket) or `#notFound` (no device) |
| ENODEV | open(2) | a device file whose driver is missing | `#notAFile` |
| ELOOP, ENAMETOOLONG | open(2) | a loop of symbolic links; a name too long | `#badName` |
| EMFILE, ENFILE, ENOMEM | open(2) | the open-file limits; no kernel memory | `#limit` |
| EFBIG, EOVERFLOW | open(2) | a file too large for the offset type (not reached with 64-bit offsets) | `#tooLarge` |
| ETXTBSY | open(2) | a swap file | `#busy` |
| EWOULDBLOCK | open(2) | a lease held by another process (`O_NONBLOCK` only) | `#busy` |
| EINTR | open(2), read(2) | a signal while blocked, on a FIFO or a slow device | restarted by the layer |
| EIO | read(2) | a read error of the device | `#deviceError` |
| EAGAIN | read(2) | a nonblocking descriptor with no data (only a FIFO) | waited for with `epoll` by the layer |
| EBADF, EFAULT, EINVAL | open(2), read(2) | layer | internal fault |

### 4.2 Writing a whole file: `fs[path] <- v`, `fs::bytes[path] <- b`

Today the interpreter writes no file through `Files`: `commit` in `zedc/src/run.rs` is called only with the writes to `m.stdout` and `m.stderr` (`finish`, run.rs:1650), and `Disk` only reads. The write this section maps is the one PORT-why adds: `open(path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC)`, `write` in a loop, and `close` with its result checked. Rust's `std::fs::write` is not fit for it, since the `File` it drops ignores the result of `close` (defect 6 of section 8). See section 6 for the durability question this raises.

| Code | Page | Cause | Gives |
|---|---|---|---|
| ENOENT | open(2) | a directory on the path does not exist | `#notFound` |
| ENOTDIR | open(2) | a name on the path is a file | `#notADirectory` |
| EACCES | open(2) | no write permission on the file, or on the directory to create in | `#denied` |
| EPERM | open(2), write(2) | an immutable or append-only file; a sealed file | `#denied` |
| EROFS | open(2) | a read-only file system | `#denied` |
| EISDIR | open(2) | the path names a directory | `#notAFile` |
| ETXTBSY | open(2) | the file is a program being run, or a swap file | `#busy` |
| EBUSY | open(2) | a device in exclusive use | `#busy` |
| ENOSPC, EDQUOT | open(2), write(2), close(2), fsync(2) | no space; the user's quota; on NFS reported late, at `close` or `fsync` | `#noSpace` |
| EFBIG | write(2) | past the file system's or the process's file size limit | `#tooLarge` |
| EIO | write(2), close(2), fsync(2) | the device failed; a write-back error, reported late | `#deviceError` |
| ELOOP, ENAMETOOLONG | open(2) | as for a read | `#badName` |
| EMFILE, ENFILE, ENOMEM | open(2) | as for a read | `#limit` |
| EINTR | open(2), write(2) | as for a read | restarted by the layer |
| EINTR | close(2) | the descriptor is closed anyway on Linux (close(2), NOTES) | not restarted; the outcome of the write is taken from `fsync` |
| EPIPE | write(2) | a FIFO with no reader | `#lost` |
| EBADF, EFAULT, EINVAL | open(2), write(2) | layer | internal fault |

### 4.3 Directory operations (row STUDY-dir-listing; listing, creating and removing)

DESIGN has no Zed operation for these today; the map is written now so the rows that add them use it.

| Code | Page | Cause | Gives |
|---|---|---|---|
| ENOENT | opendir(3), getdents(2), mkdir(2), rmdir(2), unlink(2), rename(2) | no such directory, or one on the path missing; a directory removed while it is listed (getdents(2)) | `#notFound` |
| ENOTDIR | opendir(3), mkdir(2), rmdir(2), rename(2) | a name on the path is a file; listing a file | `#notADirectory` |
| EEXIST | mkdir(2), link(2), symlink(2), rename(2) with `RENAME_NOREPLACE` | the name is taken | `#exists` |
| ENOTEMPTY, EEXIST | rmdir(2), rename(2) | removing or replacing a directory that has entries | `#exists` |
| EISDIR | unlink(2), rename(2) | removing a directory as a file; renaming a file over a directory | `#notAFile` |
| EBUSY | rmdir(2), rename(2) | a mount point, or the root of a mount | `#busy` |
| EACCES, EPERM, EROFS | all | permission; the sticky bit; a read-only file system | `#denied` |
| EMLINK | mkdir(2), link(2), rename(2) | the parent's link count is at its limit | `#limit` |
| ENOSPC, EDQUOT | mkdir(2), link(2), symlink(2), rename(2) | no space for the entry | `#noSpace` |
| EXDEV | link(2), rename(2) | the two paths are on different file systems | `#other(code)` (a move between file systems is a copy and a delete, which the operation that adds `rename` must decide) |
| ELOOP, ENAMETOOLONG | all | as for a read | `#badName` |
| EINVAL | rename(2), rmdir(2) | a directory renamed into itself; removing `.` | `#other(code)` |
| EIO | link(2), symlink(2), unlink(2) | device | `#deviceError` |
| EMFILE, ENFILE, ENOMEM | opendir(3) | limits | `#limit` |

### 4.4 Processes: `spawn`, `run`, and the OS-intrinsics layer

The layer starts a child with `clone3` (into the child's cgroup) and `execve`, or `posix_spawn`; the child reports a failed `execve` to the parent through a `pipe2(O_CLOEXEC)`, so the parent sees the child's errno.

| Code | Page | Cause | Gives |
|---|---|---|---|
| ENOENT | execve(2) | the program, or its ELF interpreter or script interpreter, does not exist; `osFindProgram` found nothing on `PATH` | `#notFound` |
| ENOTDIR | execve(2) | a name on the path is a file | `#notADirectory` |
| EACCES | execve(2) | no execute permission; a directory on the path not searchable; a `noexec` mount; the file is not a regular file | `#denied` |
| EPERM | execve(2), clone(2) | a set-user-ID file on a `nosuid` mount or under a tracer; a namespace flag without the capability | `#denied` |
| EISDIR | execve(2) | the ELF interpreter is a directory | `#notExecutable` |
| ENOEXEC | execve(2) | not a format this machine runs: wrong architecture, a script with no `#!` line | `#notExecutable` |
| ELIBBAD | execve(2) | the ELF interpreter is not in a known format | `#notExecutable` |
| ETXTBSY | execve(2) | the program is open for writing | `#busy` |
| E2BIG | execve(2) | the arguments and environment are too long | `#tooLarge` |
| EAGAIN | fork(2), clone(2), execve(2) | `RLIMIT_NPROC`, or the system's limit on threads or pids | `#limit` |
| ENOMEM | fork(2), clone(2), execve(2) | no memory for the task | `#limit` |
| ENOSPC | clone(2) | the namespace nesting limit (layer flags) | `#limit` |
| EMFILE, ENFILE | execve(2), pipe(2), pidfd_open(2) | descriptors used up | `#limit` |
| ELOOP, ENAMETOOLONG | execve(2) | as for a read | `#badName` |
| EIO | execve(2) | device | `#deviceError` |
| EACCES, EBUSY, EOPNOTSUPP | clone(2) | `CLONE_INTO_CGROUP` refused (a controller enabled in the cgroup, a domain-invalid cgroup) | the layer falls back to the process group, as DESIGN says for a runtime with no delegated cgroup; not a failure of the spawn |
| EINTR, ERESTARTNOINTR | fork(2), clone(2), waitid via wait(2) | signal | restarted by the layer |
| ESRCH | kill(2), pidfd_send_signal(2) | the process group is gone | not a failure: the stop has nothing left to stop (row OS-intrinsics tests this) |
| ECHILD, EBADF, EINVAL | wait(2), pidfd_open(2) | layer | internal fault |

A child that starts and then exits with a code or dies by a signal is not an `#ioError`: it is `p.status`, `#exit(code:)` or `#signal(Signal)` (DESIGN sec:ports, "Processes").

### 4.5 Sockets: `connect(address)`, `listen(address)`, the byte streams

Name lookup first (`getaddrinfo`), then `socket`, `connect` or `bind` + `listen`, then `accept4`, `send`/`recv` on nonblocking sockets with `epoll`.

| Code | Page | Cause | Gives |
|---|---|---|---|
| EAI_NONAME, EAI_NODATA | getaddrinfo(3) | the name has no address | `#notFound` |
| EAI_AGAIN | getaddrinfo(3) | the name server failed for now | `#unreachable` |
| EAI_FAIL | getaddrinfo(3) | the name server failed for good | `#other(code)` |
| EAI_MEMORY | getaddrinfo(3) | no memory | `#limit` |
| EAI_SERVICE, EAI_ADDRFAMILY, EAI_FAMILY, EAI_SOCKTYPE, EAI_BADFLAGS | getaddrinfo(3) | a service name the host does not know; the rest are layer | `#notFound` (service); internal fault (the rest) |
| EAI_SYSTEM | getaddrinfo(3) | an errno is in `errno` | that errno's member |
| ECONNREFUSED | connect(2), recv(2), unix(7) | nothing listens | `#refused` |
| ENETUNREACH, EHOSTUNREACH | connect(2), ip(7) | no route | `#unreachable` |
| ETIMEDOUT | connect(2), tcp(7) | no answer to the connection; on an open connection, the peer stopped answering keepalives or retransmissions | `#unreachable` at `connect`, `#lost` after |
| EADDRINUSE | bind(2), listen(2), connect(2) | the address is taken | `#busy` |
| EADDRNOTAVAIL | bind(2), connect(2) | at `bind`, an address that is not this host's; at `connect`, no ephemeral port left | `#notFound` at `bind`, `#limit` at `connect` |
| EACCES | bind(2), connect(2) | a port below 1024 without the capability; a firewall rule; a Unix socket file without write permission | `#denied` |
| EPERM | connect(2), ip(7) | a firewall rule | `#denied` |
| ENOENT | bind(2), connect(2), unix(7) | a Unix socket path that does not exist | `#notFound` |
| ECONNRESET, EPIPE | send(2), recv(2), unix(7), tcp(7) | the peer closed or reset the connection | `#lost` |
| ECONNABORTED | accept(2) | a connection aborted before it was accepted | not a failure of `listen`: the layer skips it and accepts the next |
| ENOTCONN | send(2), recv(2), shutdown(2) | the connection is gone | `#lost` |
| EMSGSIZE | send(2) | a datagram larger than the socket takes | `#tooLarge` |
| EMFILE, ENFILE, ENOBUFS, ENOMEM | socket(2), accept(2), send(2) | limits | `#limit` |
| EPROTO | accept(2) | a protocol error on the new connection | skipped by the layer, as ECONNABORTED |
| EAGAIN, EWOULDBLOCK, EINPROGRESS | accept(2), connect(2), send(2), recv(2) | nonblocking socket not ready | waited for with `epoll` by the layer; the `connect` result is then read from `SO_ERROR` (getsockopt(2)) and mapped by this table |
| EINTR | all | signal | restarted by the layer |
| EBADF, EFAULT, ENOTSOCK, EISCONN, EALREADY, EDESTADDRREQ, EAFNOSUPPORT, EPROTOTYPE, EOPNOTSUPP | all | layer | internal fault |

### 4.6 Clocks and entropy

`clock_gettime` through the vDSO has no failure with valid arguments (EINVAL, EFAULT are layer). `getrandom(2)` gives EAGAIN only with `GRND_NONBLOCK` before the pool is ready (the layer does not pass it, so it waits) and EINTR on a large request (restarted). `timerfd_create(2)` gives EMFILE, ENFILE, ENOMEM (`#limit`). No clock or entropy read gives an `#ioError` in practice.

## 5. macOS

macOS shares every POSIX code above, with different numbers for some (DESIGN never exposes the number except in `#other(code)`, which is documented as the host's own). The calls differ: no `pidfd`, `clone3` or cgroup (the layer uses `posix_spawn` and the process group), `kqueue` in place of `epoll`. Codes only macOS has, from `zerrors_darwin_arm64.go`, and where each goes:

| Code | Meaning | Gives |
|---|---|---|
| EAUTH, ENEEDAUTH | authentication failed or needed (NFS) | `#denied` |
| EBADARCH, EBADEXEC, EBADMACHO, ESHLIBVERS | the program is for another architecture, damaged, not Mach-O, or needs another library version | `#notExecutable` |
| EDEVERR, EPWROFF | device error; device powered off | `#deviceError` |
| EFTYPE | the file is the wrong kind for the operation | `#notAFile` |
| EPROCLIM | too many processes | `#limit` |
| EQFULL | an interface's output queue is full | `#limit` |
| ENOATTR, ENOPOLICY, EBADRPC, ERPCMISMATCH, EPROGUNAVAIL, EPROGMISMATCH, EPROCUNAVAIL | extended attributes, sandbox policy, Sun RPC; no operation of the layer gives them | `#other(code)` |

Inferred, to confirm under REL-macos: a case-insensitive file system gives EEXIST where Linux would create a second file differing only in case; `posix_spawn` reports a failed `exec` as its return value, not in `errno`.

## 6. Atom or fact, and the three questions the study had to answer

**Atom or fact.** Every failure mode above leaves the operation without its value: a read with no text, a write that did not land or may not have, a process that did not start, a connection that does not exist. None gives a value that is usable but less exact, the case the author's rule gives a fact to. So each is an atom: `#ioError` with its member, or the read's `#notFound`. No OS failure gives a fact. One case comes close, a write the OS took but the device has not yet stored; see durability below.

**What `#exists` is for.** The author asked. A name the operation must create is already taken: an exclusive create (`O_EXCL`, the edit algebra's `#insert` carried to a file), `mkdir`, `link`, `symlink`, a rename that must not replace, and removing a directory that is not empty (Go puts ENOTEMPTY in `ErrExist` for the same reason: entries exist that the operation needs gone). No operation DESIGN has today gives it: `fs[path] <- v` creates or replaces, so it never meets EEXIST. It is kept because the directory operations of row STUDY-dir-listing, and any exclusive create, need it, and because the edit algebra already uses `#exists` with this meaning for keys (DESIGN sec:generations, `#insert(v)` on a present key). Dropping it now would add it back with the first directory operation.

**`#interrupted`.** EINTR comes from a signal arriving while a call blocks. The layer restarts every call that EINTR interrupts (`SA_RESTART` and an explicit loop, as Go and Rust's `std` do), and its sockets and pipes are nonblocking under `epoll`, where a wait that a signal interrupts is simply waited again. `close` is the exception: on Linux the descriptor is closed even when `close` gives EINTR (close(2), NOTES), so `close` is never repeated, and the layer takes the outcome of a write from `fsync` before the close. Windows has no EINTR; the nearest code, ERROR_OPERATION_ABORTED (995), comes from `CancelIoEx`, which the runtime calls only when a `timeout` passes, so that operation gives `#timeout`. So no operation of the layer gives `#interrupted` on any of the three systems. The author named it in the family he accepted, so DESIGN keeps it and says no operation gives it on these systems, and QUESTIONS A138 asks whether to drop it (recommended).

**Durability of a write's `#ok`.** `fs[path] <- v` acknowledges `#ok` when `write` and `close` return. A write-back error found later (EIO from the device, ENOSPC or EDQUOT on NFS) is reported only to a later `fsync` or `close` (fsync(2): "Since Linux 4.13, errors from write-back will be reported to all file descriptors that might have written the data"; close(2): "Failing to check the return value when closing a file may lead to silent loss of data. This can especially be observed with NFS and with disk quota"). If no one calls `fsync`, the program was told `#ok` for data that was never stored: an absolutely wrong value by the author's rule. Two fixes, and their cost:

- Check `close`'s result (free): catches the NFS and quota cases close(2) names. `std::fs::write` cannot do this, since Rust ignores the result of `close` when it drops the `File`; the file write PORT-why adds must call `close` itself and check it.
- Write to a temporary file in the same directory, `fsync` it, `rename` it over the path, and `fsync` the directory, before `#ok`: the file is then either the old contents or the new, and `#ok` means stored. Measured on this host, ext4 on /home, 200 files of 4 KiB, 3 rounds, at load 48: create, write and close took 67 to 73 µs per file; a temporary file renamed over the name, 106 to 129 µs; the same with `fsync` of the file and of the directory, 2248 to 3701 µs. An earlier run (load 33.7, `dd conv=fsync`) found about 3.3 ms more per file with `fsync`. A program that writes many small files pays this per file.

Choosing between a stored `#ok` (slow) and a handed-to-the-OS `#ok` (fast) is the author's; QUESTIONS A139 puts it with a recommendation.

## 7. Windows

The calls: `CreateFileW` for reads and writes, `ReadFile`/`WriteFile`, `FlushFileBuffers`, `MoveFileExW`, `CreateDirectoryW`, `RemoveDirectoryW`, `DeleteFileW`, `FindFirstFileExW` for listing, `CreateProcessW` and a job object for processes, Winsock (`WSASocketW`, `connect`, `bind`, `listen`, `AcceptEx`, `WSASend`, `WSARecv`) and `GetAddrInfoW`. Win32 codes are read with `GetLastError`, Winsock codes with `WSAGetLastError`, and the NTSTATUS behind a Win32 code with `RtlGetLastNtStatus` where the Win32 code is ambiguous.

| Code (value) | Typical call | Gives |
|---|---|---|
| ERROR_FILE_NOT_FOUND (2), ERROR_PATH_NOT_FOUND (3), ERROR_INVALID_DRIVE (15), ERROR_BAD_NETPATH (53), ERROR_BAD_NET_NAME (67); STATUS_OBJECT_NAME_NOT_FOUND, STATUS_OBJECT_PATH_NOT_FOUND, STATUS_NO_SUCH_FILE | CreateFileW, CreateProcessW, MoveFileExW | `#notFound` (the answer for a read) |
| ERROR_DIRECTORY (267); STATUS_NOT_A_DIRECTORY | CreateDirectoryW, FindFirstFileExW, CreateProcessW (working directory) | `#notADirectory` |
| ERROR_DIRECTORY_NOT_SUPPORTED (336); STATUS_FILE_IS_A_DIRECTORY | CreateFileW with `FILE_NON_DIRECTORY_FILE` | `#notAFile` |
| ERROR_ACCESS_DENIED (5); STATUS_ACCESS_DENIED | CreateFileW | `#denied`, except on a directory (below) and on a file being deleted (below) |
| ERROR_WRITE_PROTECT (19), ERROR_PRIVILEGE_NOT_HELD (1314), ERROR_ELEVATION_REQUIRED (740), WSAEACCES (10013); STATUS_MEDIA_WRITE_PROTECTED, STATUS_PRIVILEGE_NOT_HELD | CreateFileW, CreateProcessW, bind | `#denied` |
| ERROR_FILE_EXISTS (80), ERROR_ALREADY_EXISTS (183), ERROR_DIR_NOT_EMPTY (145), ERROR_CANNOT_MAKE (82); STATUS_OBJECT_NAME_COLLISION, STATUS_DIRECTORY_NOT_EMPTY | CreateFileW `CREATE_NEW`, CreateDirectoryW, MoveFileExW without `MOVEFILE_REPLACE_EXISTING`, RemoveDirectoryW | `#exists` |
| ERROR_SHARING_VIOLATION (32), ERROR_LOCK_VIOLATION (33), ERROR_BUSY (170), WSAEADDRINUSE (10048); STATUS_SHARING_VIOLATION, STATUS_FILE_LOCK_CONFLICT, STATUS_LOCK_NOT_GRANTED, STATUS_DELETE_PENDING, STATUS_ADDRESS_ALREADY_EXISTS | CreateFileW of a file another process opened without sharing, bind | `#busy` |
| ERROR_DISK_FULL (112), ERROR_HANDLE_DISK_FULL (39), ERROR_DISK_QUOTA_EXCEEDED (1295), WSAEDQUOT (10069); STATUS_DISK_FULL, STATUS_QUOTA_EXCEEDED | WriteFile | `#noSpace` |
| ERROR_TOO_MANY_OPEN_FILES (4), ERROR_NOT_ENOUGH_MEMORY (8), ERROR_OUTOFMEMORY (14), ERROR_NO_SYSTEM_RESOURCES (1450), ERROR_TOO_MANY_LINKS (1142), WSAEMFILE (10024), WSAENOBUFS (10055); STATUS_TOO_MANY_OPENED_FILES, STATUS_NO_MEMORY, STATUS_INSUFFICIENT_RESOURCES | all | `#limit` |
| ERROR_FILE_TOO_LARGE (223), WSAEMSGSIZE (10040); STATUS_FILE_TOO_LARGE | WriteFile, send | `#tooLarge` |
| ERROR_INVALID_NAME (123), ERROR_BAD_PATHNAME (161), ERROR_FILENAME_EXCED_RANGE (206), ERROR_CANT_RESOLVE_FILENAME (1921), ERROR_STOPPED_ON_SYMLINK (681), ERROR_CANT_ACCESS_FILE (1920); STATUS_OBJECT_NAME_INVALID, STATUS_NAME_TOO_LONG, STATUS_REPARSE_POINT_NOT_RESOLVED, STATUS_STOPPED_ON_SYMLINK | CreateFileW | `#badName` |
| ERROR_BAD_EXE_FORMAT (193), ERROR_BAD_FORMAT (11), ERROR_EXE_MACHINE_TYPE_MISMATCH (216), ERROR_INVALID_EXE_SIGNATURE (191); STATUS_INVALID_IMAGE_FORMAT, STATUS_INVALID_IMAGE_NOT_MZ, STATUS_IMAGE_MACHINE_TYPE_MISMATCH | CreateProcessW | `#notExecutable` |
| WSAECONNREFUSED (10061), ERROR_CONNECTION_REFUSED (1225); STATUS_CONNECTION_REFUSED | connect | `#refused` |
| WSAENETUNREACH (10051), WSAEHOSTUNREACH (10065), WSAENETDOWN (10050), WSAEHOSTDOWN (10064), WSAETIMEDOUT (10060) at connect, WSATRY_AGAIN (11002), ERROR_NETWORK_UNREACHABLE (1231), ERROR_HOST_UNREACHABLE (1232), ERROR_SEM_TIMEOUT (121) on a network path; STATUS_NETWORK_UNREACHABLE, STATUS_HOST_UNREACHABLE, STATUS_IO_TIMEOUT | connect, GetAddrInfoW, CreateFileW on a share | `#unreachable` |
| WSAHOST_NOT_FOUND (11001), WSANO_DATA (11004) | GetAddrInfoW | `#notFound` |
| WSANO_RECOVERY (11003) | GetAddrInfoW | `#other(code)` |
| WSAECONNRESET (10054), WSAECONNABORTED (10053), WSAENETRESET (10052), WSAENOTCONN (10057), WSAESHUTDOWN (10058), WSAETIMEDOUT after connect, ERROR_BROKEN_PIPE (109), ERROR_NO_DATA (232), ERROR_PIPE_NOT_CONNECTED (233), ERROR_NETNAME_DELETED (64), ERROR_CONNECTION_ABORTED (1236); STATUS_CONNECTION_RESET, STATUS_CONNECTION_ABORTED, STATUS_PIPE_BROKEN, STATUS_PIPE_CLOSING | WSASend, WSARecv, ReadFile and WriteFile on a pipe | `#lost` |
| ERROR_CRC (23), ERROR_SECTOR_NOT_FOUND (27), ERROR_NOT_READY (21), ERROR_IO_DEVICE (1117); STATUS_DEVICE_DATA_ERROR, STATUS_DEVICE_NOT_READY, STATUS_IO_DEVICE_ERROR | ReadFile, WriteFile, FlushFileBuffers | `#deviceError` |
| ERROR_NOT_SUPPORTED (50), ERROR_CALL_NOT_IMPLEMENTED (120); STATUS_NOT_SUPPORTED | an operation the file system or the Windows version lacks | `#unsupported` |
| ERROR_NOT_SAME_DEVICE (17), ERROR_INVALID_PARAMETER (87) from a value the program gave; STATUS_NOT_SAME_DEVICE | MoveFileExW across volumes, others | `#other(code)` |
| ERROR_OPERATION_ABORTED (995); STATUS_CANCELLED | an I/O the runtime cancelled with CancelIoEx at a timeout | `#timeout` (the deadline's atom, not an `#ioError`) |
| ERROR_INVALID_HANDLE (6), WSAEWOULDBLOCK (10035) outside overlapped I/O, WSAEINTR (10004) | layer | internal fault (WSAEINTR comes only from the obsolete `WSACancelBlockingCall`) |

Two defects of Windows that the layer must correct (inferred from Microsoft's documentation; row REL-windows confirms each with a test):

- **A directory opened as a file gives ERROR_ACCESS_DENIED.** `CreateFileW` on a directory without `FILE_FLAG_BACKUP_SEMANTICS` fails with ERROR_ACCESS_DENIED, the same code as a permission refusal. The layer reads the path's attributes (`GetFileAttributesW`) after ERROR_ACCESS_DENIED and gives `#notAFile` when the path is a directory, as the author asked for this case.
- **A file being deleted gives ERROR_ACCESS_DENIED.** A file with a pending delete (another process deleted it while a handle is still open) fails with ERROR_ACCESS_DENIED; the NTSTATUS is STATUS_DELETE_PENDING (`RtlGetLastNtStatus`), and the layer gives `#busy`, since the name frees when the last handle closes.

## 8. Evidence from other implementations, and their defects

| Mode | Rust std 1.93 | Go 1.26 | Python (PEP 3151) | Zed |
|---|---|---|---|---|
| ENOENT | NotFound | ErrNotExist | FileNotFoundError | `#notFound` |
| EISDIR | IsADirectory | none | IsADirectoryError | `#notAFile` |
| ENOTDIR | NotADirectory | none | NotADirectoryError | `#notADirectory` (on a read, `#notFound`) |
| EACCES, EPERM | PermissionDenied | ErrPermission | PermissionError | `#denied` |
| EROFS | ReadOnlyFilesystem | none | none | `#denied` |
| EEXIST | AlreadyExists | ErrExist | FileExistsError | `#exists` |
| ENOTEMPTY | DirectoryNotEmpty | ErrExist | none | `#exists` |
| EBUSY, ETXTBSY | ResourceBusy, ExecutableFileBusy | none | none | `#busy` |
| ENOSPC, EDQUOT | StorageFull, QuotaExceeded | none | none | `#noSpace` |
| EMFILE, ENFILE | Uncategorized | Temporary() true | none | `#limit` |
| ENOMEM | OutOfMemory | none | MemoryError is not an OSError | `#limit` |
| EFBIG, E2BIG | FileTooLarge, ArgumentListTooLong | none | none | `#tooLarge` |
| ENAMETOOLONG, ELOOP | InvalidFilename, FilesystemLoop | none | none | `#badName` |
| ENOEXEC | Uncategorized | none | none | `#notExecutable` |
| ECONNREFUSED | ConnectionRefused | none | ConnectionRefusedError | `#refused` |
| ENETUNREACH, EHOSTUNREACH | NetworkUnreachable, HostUnreachable | none | none | `#unreachable` |
| ECONNRESET, EPIPE | ConnectionReset, BrokenPipe | none | ConnectionResetError, BrokenPipeError | `#lost` |
| EIO | Uncategorized | none | none | `#deviceError` |
| ENOSYS, EOPNOTSUPP | Unsupported | ErrUnsupported | none | `#unsupported` |
| EINTR | Interrupted | Temporary() true | InterruptedError | restarted |
| EAGAIN | WouldBlock | Timeout() true | BlockingIOError | waited for |

Defects found in these sources, each to become a test of the layer, never copied (standing rule P339):

1. Rust maps ERROR_SHARING_VIOLATION and ERROR_LOCK_VIOLATION to Uncategorized, not ResourceBusy: the commonest Windows "file in use" codes fall outside its busy kind. Test (REL-windows): a file opened by another process without sharing gives `#busy`.
2. Rust maps ERROR_OPERATION_ABORTED to TimedOut for every cause; an abort the program did not ask for would read as a timeout. Zed gives `#timeout` only from its own deadline. Test (REL-windows): a cancelled read with no deadline is an internal fault, not `#timeout`.
3. Rust has no kind for EMFILE and ENFILE (Uncategorized), and none for EIO. Test (OS-intrinsics): with `RLIMIT_NOFILE` set to the descriptors already open, a read gives `#limit`.
4. Go's `Timeout()` is true for EAGAIN, so a nonblocking read with no data reads as a timeout. Zed waits for readiness and never reports EAGAIN. Test (OS-intrinsics): a FIFO with no writer yet does not fail the read before its writer opens.
5. Go's ErrNotExist on Windows leaves out ERROR_INVALID_DRIVE and ERROR_BAD_NET_NAME, which Rust includes. Test (REL-windows): a path on drive `Q:` with no such drive gives `#notFound`.
6. Rust's `File` drop ignores the result of `close`, so `std::fs::write` reports `Ok` when close(2) reports a late ENOSPC, EDQUOT or EIO. The interpreter writes no file today, so it does not have this defect yet; the file write PORT-why adds must not use `std::fs::write`. Test (PORT-why): a write to a file system with a quota smaller than the file, on NFS or a FUSE file system that defers the error to `close`, gives `#noSpace`.
7. Rust maps ERROR_CALL_NOT_IMPLEMENTED to Unsupported but ERROR_NOT_SUPPORTED, the code a file system gives for an operation it lacks, to Uncategorized (`library/std/src/sys/pal/windows/mod.rs`, line 102); Go's `ErrUnsupported` takes both. Test (REL-windows): an operation that fails with ERROR_NOT_SUPPORTED on the test machine's file system (which one is for that row to find) gives `#unsupported`.

## 9. What changes where

- DESIGN sec:ports: the `#ioError` sentence, the new paragraph "Why an operation failed" with this list, the spawn sentence and its example; sec:keypaths, Failure forensics; sec:robustness, the retry bullet and the dropped-connection sentence; step S.1a; the other places that write the payload.
- Plan rows extended (author P368: extend, do not file): PORT-why (the type, the Linux map in the interpreter, the close check, the tests), OS-intrinsics (the Linux map in libzed, the restart of EINTR, the tests above), REL-macos and REL-windows (each system's map, its codes of sections 5 and 7, and the defect tests).
- QUESTIONS: C14 answered and removed; A138 (`#interrupted`) and A139 (what a write's `#ok` promises) added.
