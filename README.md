# file

File system operations for the [Bats](https://github.com/bats-lang) programming language.

## API

See [docs/lib.md](docs/lib.md) for the full API reference.

## Safety

`unsafe = true` — wraps POSIX file I/O syscalls. Exposes a safe typed API with linear ownership for file descriptors.
