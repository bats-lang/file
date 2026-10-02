#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* Each choice matched in full, and a file opened by them *)
fn writes (access: $F.access): bool =
  case+ access of
  | $F.ReadOnly() => false
  | $F.WriteOnly() => true
  | $F.ReadWrite() => true

fn creates (opening: $F.opening): bool =
  case+ opening of
  | $F.OpenExisting() => false
  | $F.CreateOrOpen() => true
  | $F.CreateOrTruncate() => true
  | $F.CreateOrAppend() => true
  | $F.TruncateExisting() => false
  | $F.AppendExisting() => false

fn missing (e: $F.io_error): bool =
  case+ e of
  | $F.NotFound() => true
  | $F.NotADirectory() => true
  | $F.PermissionDenied() => false
  | $F.AlreadyExists() => false
  | $F.IsADirectory() => false
  | $F.DirectoryNotEmpty() => false
  | $F.ReadOnlyFilesystem() => false
  | $F.FilesystemLoop() => false
  | $F.InvalidFilename() => false
  | $F.InvalidInput() => false
  | $F.FileTooLarge() => false
  | $F.StorageFull() => false
  | $F.TooManyOpenFiles() => false
  | $F.OutOfMemory() => false
  | $F.ResourceBusy() => false
  | $F.BrokenPipe() => false
  | $F.WouldBlock() => false
  | $F.BadDescriptor() => false
  | $F.DeviceError() => false
  | $F.Unsupported() => false
  | $F.CrossesDevices() => false
  | $F.Unrecognized() => false

fn open_for_writing {lb:agz}{n:pos | n < 1048576} (path: !$A.borrow(byte, lb, n), n: int n): bool =
  case+ $F.file_open(path, n, $F.WriteOnly(), $F.CreateOrTruncate(), 420) of
  | ~$R.ok(fd) => let val () = $R.discard<int><$F.io_error>($F.file_close(fd)) in true end
  | ~$R.err(e) => missing(e)
