
From Coq Require Import BinNat.
From Wasm Require Export bytes.
From mathcomp Require Import ssrbool ssrnat.

Record handle : Type := {
    base : N;
    offset : N;
    bound : N;
    valid : bool;
    id : N;
  }.


Definition dummy_handle :=
  {| base := N.zero ;
    offset := N.zero ;
    bound := N.zero ;
    valid := false ;
    id := N.zero |}.

Definition upd_handle_validity h b :=
  {| base := h.(base) ;
    offset := h.(offset) ;
    bound := h.(bound) ;
    id := h.(id) ;
    valid := h.(valid) && b |}.

Definition slice_handle h n1 n2 :=
  if N.leb N.zero n1 && N.ltb n1 h.(bound) && N.leb N.zero n2 then
    Some {| base := h.(base) + n1 ;
           offset := h.(offset) ;
           bound := h.(bound) - n2 ;
           valid := h.(valid) ;
           id := h.(id) |}
  else None.



Class HandleBytes : Type := {
    handle_size : N;
    serialise_handle : handle -> bytes;
    handle_of_bytes : bytes -> handle;


    size_is_not_zero : 0 < nat_of_bin handle_size;
    length_serialise : forall h, length (serialise_handle h) = handle_size;
    handle_of_serialise : forall h, handle_of_bytes (serialise_handle h) = h;
    serialise_handle_of : forall bs, serialise_handle (handle_of_bytes bs) = bs
  } .
    
