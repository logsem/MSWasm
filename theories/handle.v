
From Coq Require Import ZArith.BinInt BinNat.
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



Definition is_dummy h :=
  N.eqb (base h) N.zero && N.eqb (offset h) N.zero && N.eqb (bound h) N.zero && negb (valid h) && N.eqb (id h) N.zero.

Lemma is_dummy_true h : is_dummy h -> h = dummy_handle.
Proof.
  destruct h; unfold is_dummy; simpl.
  intros H. repeat apply Bool.andb_true_iff in H as [H ?].
  apply N.eqb_eq in H as ->. apply N.eqb_eq in H3 as ->.
  apply N.eqb_eq in H2 as ->. apply N.eqb_eq in H0 as ->.
  destruct valid0. simpl in H1. inversion H1. reflexivity.
Qed.

Lemma is_dummy_false h : is_dummy h = false -> h <> dummy_handle.
Proof.
  intros H ->. unfold is_dummy, dummy_handle in H. simpl in H. inversion H.
Qed. 

Definition upd_handle_validity h b :=
  {| base := h.(base) ;
    offset := h.(offset) ;
    bound := h.(bound) ;
    id := h.(id) ;
    valid := h.(valid) && b |}.

Definition slice_handle h n1 n2 :=
  if N.ltb n1 h.(bound) then
    if N.leb n1 n2 then
    Some {| base := h.(base) + n1 ;
           offset := h.(offset) ;
           bound := h.(bound) - n2 ;
           valid := h.(valid) ;
           id := h.(id) |}
    else None
  else None.

Definition handle_add h (n: Z) :=
  if (Z.of_N (offset h) + n >=? 0)%Z then
    Some {| base := h.(base) ;
           offset := Z.to_N (Z.of_N (offset h) + n)%Z ;
           bound := h.(bound) ;
           valid := h.(valid) ;
           id := h.(id) |}
  else None.


Definition new_handle a n id :=
  {| base := a ; offset := 0 ; bound := n ; valid := true ; id := id |}.

Definition handle_addr h : N :=
  N.add (base h) (offset h).

Definition handle_eqb h1 h2 :=
  N.eqb (base h1) (base h2) && N.eqb (offset h1) (offset h2) &&
    N.eqb (bound h1) (bound h2) && Bool.eqb (valid h1) (valid h2) &&
    N.eqb (id h1) (id h2).

Lemma handle_eqb_eq h1 h2 : handle_eqb h1 h2 = true <-> h1 = h2.
Proof.
  split.
  - intro Heq.
    repeat apply Bool.andb_true_iff in Heq as [Heq ?].
    destruct h1, h2; simpl in *.
    apply N.eqb_eq in Heq as ->. apply N.eqb_eq in H2 as ->.
    apply N.eqb_eq in H1 as ->. apply N.eqb_eq in H as ->.
    destruct valid0, valid1; try inversion H0. trivial. trivial.
  - intros ->. unfold handle_eqb. repeat rewrite N.eqb_refl.
    destruct (valid h2); simpl; trivial.
Qed.


Class HandleBytes : Type := {
    handle_size : N;
    serialise_handle : handle -> bytes;
    handle_of_bytes : bytes -> handle;


    size_is_not_zero : 0 < nat_of_bin handle_size;
    length_serialise : forall h, length (serialise_handle h) = handle_size;
    handle_of_serialise : forall h, handle_of_bytes (serialise_handle h) = h;
    serialise_handle_of : forall bs, serialise_handle (handle_of_bytes bs) = bs
  } .
    
