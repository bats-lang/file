# file

File system operations for the [Bats](https://github.com/bats-lang) programming language.

## Features

- File open/close/read, opened for an `access` (`ReadOnly | WriteOnly |
  ReadWrite`) and an `opening` (`OpenExisting | CreateOrOpen |
  CreateOrTruncate | CreateOrAppend | TruncateExisting | AppendExisting`)
- Failures are an `io_error` (`NotFound`, `PermissionDenied`, ...,
  `Unrecognized`), decoded once from the errno; `io_error_text` words it
- Buffered writer (`buf_writer`)
- File metadata (`file_mtime`, `file_stat`)
- Directory operations (`dir_open`, `dir_next`, `dir_close`)
- Change directory (`file_chdir`)
- Short-read safe: `read()` loops until all bytes are read

## Usage

```bats
#use file as F
#use result as R

val fd_r = $F.file_open(path_bv, path_len, $F.ReadOnly(), $F.OpenExisting(), 0)
case+ fd_r of
| ~$R.ok(fd) => let
    val buf = $A.alloc<byte>(4096)
    val rr = $F.file_read(fd, buf, 4096)
    ...
  end
| ~$R.err(e) => println! ($F.io_error_text(e))
```

## API

See [docs/lib.md](docs/lib.md) for the full API reference.

## Safety

`unsafe = true` — wraps POSIX file I/O syscalls. Exposes a safe typed API with linear ownership for file descriptors.
