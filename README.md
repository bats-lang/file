# file

File system operations for the [Bats](https://github.com/bats-lang) programming language.

## Features

- File open/close/read with POSIX flags
- Buffered writer (`buf_writer`)
- File metadata (`file_mtime`, `file_stat`)
- Directory operations (`dir_open`, `dir_next`, `dir_close`)
- Change directory (`file_chdir`)
- Short-read safe: `read()` loops until all bytes are read

## Usage

```bats
#use file as F
#use result as R

val fd_r = $F.file_open(path_bv, path_len, 0, 0)
case+ fd_r of
| ~$R.ok(fd) => let
    val buf = $A.alloc<byte>(4096)
    val rr = $F.file_read(fd, buf, 4096)
    ...
  end
| ~$R.err(_) => ...
```

## API

See [docs/lib.md](docs/lib.md) for the full API reference.

## Safety

`unsafe = true` — wraps POSIX file I/O syscalls. Exposes a safe typed API with linear ownership for file descriptors.
