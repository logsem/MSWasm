From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import BinNat Lia.
Require Export common.
From Wasm Require Import numerics bytes memory.
From stdpp Require Import gmap.


Inductive btag := Numeric | Handle.


Record segment_list : Type := {
    segl_data : list (byte * btag)
  }.


Record allocator : Type := {
    allocated : gmap N (option (N * N));
    next_free : N; 
  }.


Definition seg_make v len :=
  {| segl_data := List.repeat (v, Numeric) (N.to_nat len);
  |}.



Definition differ_at {A} (start len : N) (l1 l2 : list A) :=
  forall i, (i < start \/ i >= start + len)%N ->
       List.nth_error l1 (N.to_nat i) = List.nth_error l2 (N.to_nat i).

Definition find (nid : N) (l : gmap N (option (N * N))) : option (N * N) :=
  match l !! nid with
  | Some (Some x) => Some x
  | _ => None
  end.
Definition find_and_remove (nid : N) (l : gmap N (option (N * N))) : option (gmap N (option (N * N)) * N * N) :=
  match l !! nid with
  | Some (Some (b, c)) => Some (<[ nid := None ]> l, b, c)
  | _ => None
  end.  



Definition find_address nid l :=
  match find_and_remove nid l.(allocated) with
  | Some (_,a, n) => Some (a)
  | None => None end. 


Definition isAlloc nid s : Prop :=
  match find nid s.(allocated) with
  | None => False
  | Some _ => True
  end. 

Definition isAllocb nid s :=
  match find nid s.(allocated) with
  | None => false
  | _ => true
  end. 


Definition isNotAlloc nid s : Prop :=
  find nid s.(allocated) = None.
Definition canBeAlloc nid s : Prop :=
  s.(allocated) !! nid = None.


 Definition compatible addr size (s : gmap N (option (N * N))) : Prop :=
  forall nid addr' size', s !! nid = Some (Some (addr', size')) ->
                     (addr + size <= addr')%N \/ (addr >= addr' + size')%N. 

Definition seg_lookup i sl :=
  List.nth_error sl.(segl_data) (N.to_nat i).

Definition seg_update :=
  fun i v sl =>
    if N.ltb i (N.of_nat (List.length sl.(segl_data))) 
    then Some {| segl_data := take (N.to_nat i) sl.(segl_data) ++ [::v] ++ drop (N.to_nat i+1) sl.(segl_data) |}
    else None.

Definition seg_length :=
  fun sl => N.of_nat (List.length sl.(segl_data)).

Definition seg_grow :=
  fun len_delta sl =>
    {|
      segl_data := sl.(segl_data) ++ List.repeat (#00,Numeric) (N.to_nat len_delta)
    |}.


 Definition isSound_aux T (m : gmap N (option (N * N))) : Prop :=
  forall a b c, m !! a = Some (Some (b,c)) ->
           (b + c <= seg_length T)%N /\ compatible b c (<[ a := None ]> m). 

 Definition isSound T A : Prop :=
  isSound_aux T A.(allocated) /\
    forall k, (k >= A.(next_free))%N -> canBeAlloc k A.



Lemma data_length_is_compatible_aux :
  forall l T size, isSound_aux T l -> compatible (seg_length T) size l.
Proof.
  intros l T size Hsound.
  unfold compatible. unfold isSound_aux in Hsound.
  intros a b c Ha.
  apply Hsound in Ha.
  right. lia.
Qed. 


Lemma data_length_is_compatible :
  forall T A size, isSound T A -> compatible (seg_length T) size A.(allocated).
Proof.
  intros.
  apply data_length_is_compatible_aux.
  by destruct H.
Qed.

Lemma find_and_remove_compatible:
  forall l nid l' a n add size,
    compatible add size l ->
    find_and_remove nid l = Some (l', a, n) ->
    compatible add size l'.
Proof.
  intros l nid l' a n add size Hcomp Hrem nid' b c Hnid'.
  unfold find_and_remove in Hrem.
  destruct (l !! nid) eqn:Hnid => //.
  destruct o as [[??]|] => //.
  inversion Hrem; subst; clear Hrem.
  destruct (nid =? nid')%N eqn:Hn.
  - apply N.eqb_eq in Hn as ->.
    rewrite lookup_insert in Hnid' => //.
  - apply N.eqb_neq in Hn.
    rewrite lookup_insert_ne in Hnid' => //.
    by apply Hcomp in Hnid'.
Qed.

  
Lemma find_and_remove_isSound :
  forall T l nid l' a n,
    isSound_aux T l -> find_and_remove nid l = Some (l', a, n) -> isSound_aux T l'.
Proof.
  intros T l nid l' a n Hsound Hrem nid' b c Hnid'.
  unfold find_and_remove in Hrem.
  destruct (l !! nid) eqn:Hnid => //.
  destruct o as [[??]|] => //.
  inversion Hrem; subst; clear Hrem.
  destruct (nid =? nid')%N eqn:Hn.
  apply N.eqb_eq in Hn as ->.
  by rewrite lookup_insert in Hnid'.
  apply N.eqb_neq in Hn.
  rewrite lookup_insert_ne in Hnid' => //.
  apply Hsound in Hnid' as [??] => //.
  split => //. 
  eapply find_and_remove_compatible.
  exact H0. instantiate (3 := nid).
  unfold find_and_remove.
  rewrite lookup_insert_ne => //.
  rewrite Hnid.
  by rewrite insert_commute.
Qed.

Definition allocated_eq_dec : forall v1 v2 : gmap N (option (N * N)), {v1 = v2} + {v1 <> v2}.
Proof. intros. solve_decision. Qed.

