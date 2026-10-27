#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A rename's outcome is linear: dropping it unread would lose the reason
   it failed, so it is a type error. *)
#pub fn rename_and_forget {ls,ld:agz}{ns,nd:pos | ns < 1048576; nd < 1048576}
  (source: !$A.borrow(byte, ls, ns), source_len: int ns,
   destination: !$A.borrow(byte, ld, nd), destination_len: int nd): void

implement rename_and_forget (source, source_len, destination, destination_len) = let
  val outcome = $F.file_rename(source, source_len, destination, destination_len)
in () end
