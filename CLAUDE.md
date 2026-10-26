# file

## CI is pinned

Every input to CI is pinned in the source (bats-lang/repository-prototype#269),
so a commit that passes keeps passing:

* `bats.lock` is committed: CI never runs `bats lock` for the package, so
  `bats check` and `bats build` fetch exactly the locked versions, and fail
  when the lock is missing or does not match `bats.toml`. A library's lock
  pins only its own CI and tests; its dependents still resolve their own.
* The compiler is the commit in `.github/bats-version`, read by every
  workflow that builds bats (and by the publish workflow).
* The package repository is fetched at the commit in
  `.github/repository-version`, so what the test packages under `tests/`
  lock (`bats lock --dev`) is pinned too.
* `publish.yml` and `relock-pins.yml` in bats-lang/repository-prototype are
  called by commit, never `@main`.

Pins move only through a reviewed pull request that runs the same CI. The
daily `relock.yml` (the shared `relock-pins.yml`) relocks against the
newest, moves the compiler and repository pins, pushes `relock/<date>`,
opens a pull request listing the old and new versions and dispatches
`check.yml` on it, so a breaking publish shows as a red relock pull
request and main stays green. GITHUB_TOKEN cannot change workflow files,
so without a `RELOCK_TOKEN` secret that pull request lists a workflow pin
that would move instead of moving it: move it in a pull request of its
own. A pull request that needs newer packages runs `bats lock
--repository <dir>` and commits `bats.lock` (and
`.github/repository-version`) with the change.

## Buffered-writer close (#61)

`buf_writer_close` flushes and closes but returns only the close's answer: a
failed final write is reported as success. It is kept as published, deprecated
(removal: #74), and `buf_writer_close_checked` is beside it: it returns a
`close_outcome` (`Closed`, `FlushFailed(e)`, `CloseFailed(e)`,
`FlushAndCloseFailed(flush_e, close_e)`), a linear type, so a caller must match
it with `case+`. The writer is closed in every case. `tests/dynamic/closeflush`
fails the final write with a read-only descriptor (`BadDescriptor`) and calls
both forms; `tests/static/reject/close-outcome-flush-left-out` rejects a match
without `FlushFailed`.

## Content writer and reader: the bytes of a file in the type (#76)

Keyword: content-io. `content_writer(written)` is a linear writer indexed by the
cells (array's `cells`) written to a file it made empty (`content_create`: created or
emptied, so it starts at `cnil`). A write (`content_write_byte`, `content_write` of a
frozen run, `content_write_prefix` of the first bytes of a run whose cells begin with
a chunk, by array's `HOLDS` and `CLEN`) returns the writer indexed by `APPEND(written,
chunk, both)`; `content_flush` returns it unchanged; `content_close` answers
`FILE_HOLDS(written)`, a proof that the file holds exactly those cells. A failed write,
flush or close consumes the writer (closed) and is a constructor of its own with only
the `io_error`, so no proof exists after it.

`content_reader(consumed, start, limit)` is indexed by the cells consumed from the
offset `start`, at most `limit` bytes. `content_read` into a `barr` returns the buffer
with new cells that begin with the chunk (`HOLDS`, `CLEN`) and the reader extended by
`APPEND`; the end is a constructor of its own, either the limit (`FILE_READ` and `CLEN`
of the consumed cells to the limit) or the end of the file before it (`FILE_READ`); a
failed read consumes the reader. `content_reader_open` reads from the first byte (limit
`CONTENT_READ_ALL`, the largest an int names), `content_reader_open_range` from an offset
with a limit. The names are those zip#64 declares (`content_writer`, `content_close`,
`FILE_HOLDS`, `content_reader`, `FILE_READ`, `io_error`); none is renamed.

**What is trusted** (the one place, the end of `src/lib.bats`, with the `$UNSAFE.cast`
that makes each proof; no `praxi`): that the file is made empty and nobody else writes
or changes it meanwhile; that a write acknowledged by the C call is not short (it
retries until all bytes are written, else it is a failure); that the close succeeded;
that the bytes read are the bytes the file holds at that offset; that the C call reads
at most the count asked and the limit. The index arithmetic (`APPEND`, `CELLS_EQ`,
`HOLDS`) is array's. A flush or a close that fails after bytes were written gives no
proof, though some of them are in the file.

**Tests.** `tests/dynamic/contentio` (valgrind) writes a pattern in every way, reads
it whole and in ranges (inside, past the end, after the end, limit zero), reads a
directory (a real read failure), opens a missing file, closes a reader early, copies
a file with a reader and a writer to a second file whose type proof says it holds what
the reader consumed (`append_functional` joins their `APPEND`s), and has the kernel
refuse a write (a byte written to a file of the process that takes only numbers).
`tests/static/accept/content-use` and the rejects in `tests/static/reject`:
`write-index-unchanged`, `close-proof-other-sequence`, `use-after-failed-write`,
`read-index-unchanged`, `read-proof-other-range`, `use-after-failed-read`, each with the
patsopt's error in `expect`, up to the first counter: patsopt numbers its variables
(`both$5131(12192)`) by what it has read first, and the numbers differ between this
machine and CI's run of the same fixture, so an `expect` that held them failed in CI;
the text before the first number names the error and the variable. The package has no lemma of its own, so quire's
`mutation_check.py` finds none to mutate (as in process); the mutants are the
declarations: weaken the type each reject guards and the reject is accepted, shown in
the pull request.

**Old forms.** `buf_writer` and its functions (removal: #80) and `buf_reader` and its
functions (removal: #81) are kept with their types, marked deprecated by a one-line
comment, and called by `tests/dynamic/buffered` and `tests/dynamic/closeflush`.
