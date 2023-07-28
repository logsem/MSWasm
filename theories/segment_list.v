From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import BinNat Lia.
From Wasm Require Import numerics bytes memory.

Inductive btag := Numeric | Handle.


Record segment_list : Type := {
    segl_data : list (byte * btag)
  }.



Record allocator : Type := {
    allocated : list (N * N * N);
  }.


Definition seg_make v len :=
  {| segl_data := List.repeat (v, Numeric) (N.to_nat len);
  |}.



Definition differ_at {A} (start len : N) (l1 l2 : list A) :=
  forall i, (i < start \/ i >= start + len)%N ->
       List.nth_error l1 (N.to_nat i) = List.nth_error l2 (N.to_nat i).
(*
Definition data_alloc (data : byte * btag * option N) : option N :=
  let '(_,_,n) := data in n.
Definition data_proper (data: byte * btag * option N) :=
  let '(a,b,_) := data in (a,b).
Definition create_data (data : byte * btag) (alloc : option N) :=
  let '(a,b) := data in (a,b,alloc). 
Definition nth_alloc data i := option_map data_alloc (List.nth_error data i).
Definition count_some (x : N) l :=
  List.fold_left (fun acc obj =>
                    match data_alloc obj with
                    | Some y => if (y =? x)%N then acc + 1 else acc
                    | None => acc end) l 0. *) 

Fixpoint find (nid : N) (l: list (N * N * N)) : option (N * N) :=
  match l with
  | [::] => None
  | (a,b,c) :: q => if (a =? nid)%N then Some (b,c) else find nid q
  end.

                                                   

Fixpoint find_and_remove (nid : N) (l: list (N * N * N)) : option (list (N * N * N) * N * N) :=
  match l with
  | [::] => None
  | (a,b,c) :: q =>
      if (a =? nid)%N then Some (q, b, c) else
        match find_and_remove nid q with
        | Some (l, d, e) => Some ((a,b,c) :: l, d, e)
        | None => None
        end
  end.

Definition find_address nid l := match find_and_remove nid l.(allocated) with
                                 | Some (_,a, _) => Some a
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

Definition isFree nid s : Prop := find nid s.(allocated) = None.




Fixpoint compatible addr size (l : list (N * N * N)) : Prop :=
  match l with
  | [::] => True
  | (_,addr',size') :: q => ((addr + size <= addr')%N \/ (addr >= addr' + size')%N) /\ compatible addr size q
  end.


Lemma compatible_forall addr size l :
  (forall '(x,addr',size'), List.In (x,addr',size') l -> ((addr + size <= addr')%N \/ (addr >= addr' + size')%N)) -> compatible addr size l.
Proof.
  induction l => //=.
  intros.
  destruct a. destruct p. split.
  - apply (H (n0, n1, n)). by left.
  - apply IHl.
    intros. destruct pat as [[??]?].
    intro.
    apply (H (n2, n3, n4)).
    by right.
Qed. 



  
Fixpoint fresh_nid_aux (l : list (N * N * N)) :=
  match l with
  | [::] => 0%N
  | (id, _,_) :: q => let x := fresh_nid_aux q in
                    if (x <=? id)%N then (id + 1)%N else x
  end.

Definition fresh_nid A := fresh_nid_aux A.(allocated).

Lemma fresh_nid_is_free_aux: forall l n, (n >= fresh_nid_aux l)%N -> isFree n {| allocated := l |}.
Proof.
  induction l; intros => //=.
  simpl in H. destruct a. destruct p.
  unfold isFree. simpl.
  destruct (n1 =? n)%N eqn:Hn'.
  apply N.eqb_eq in Hn' as ->.
  destruct (fresh_nid_aux l <=? n)%N eqn:Hn; [ lia | apply N.leb_gt in Hn; lia].
  assert (n >= fresh_nid_aux l)%N as H0; last first.
  apply IHl in H0.
  unfold isFree in H0. simpl in H0. done.
  destruct (fresh_nid_aux l <=? n1)%N eqn:Hn; last done.
  apply N.leb_le in Hn. lia.
Qed. 
  


Lemma fresh_nid_is_free: forall A, isFree (fresh_nid A) A.
Proof.
  intro A. destruct A. unfold fresh_nid. apply fresh_nid_is_free_aux.
  simpl. lia.
Qed. 
  

(*
Lemma fresh_nid: forall A, exists nid, forall nid', (nid' >= nid)%N -> isFree nid' A.
Proof.
  intros. remember (length (allocated A)) as n.
  generalize dependent A.
  induction n; intros => //=.
  - apply sym_eq, List.length_zero_iff_nil in Heqn.
    exists 0%N. unfold isFree, find. rewrite Heqn. done.
  - destruct (allocated A) eqn:Ht => //. simpl in Heqn.
    inversion Heqn.
    replace l with (allocated {| allocated := l |}) in H0 => //.
    apply IHn in H0 as [nid Hnid].
    destruct p as [[p1 p2] pid].
    destruct (nid <=? p1)%N eqn:Hp; [ apply N.leb_le in Hp | apply N.leb_gt in Hp].
    + exists (p1 + 1)%N. intros.
      unfold isFree, find. rewrite Ht => /=.
      replace (p1 =? nid')%N with false => /=.
      assert (nid' >= nid)%N; first lia.
      by apply Hnid.
      apply sym_eq, N.eqb_neq. intro; lia.
    + exists nid. intros.
      unfold isFree, find. rewrite Ht => /=.
      replace (p1 =? nid')%N with false => /=.
      by apply Hnid.
      apply sym_eq, N.eqb_neq. intro; lia.
Qed.
Check (fresh_nid {| allocated := [::] |}). *)
  
(*
Lemma can_alloc: forall T A n, exists a nid T' A', salloc T A a n nid T' A'.
Proof.
  intros. destruct (fresh_nid A) as [nid Hnid].
  eexists (N.of_nat (length (segl_data T))), nid, _, _.
  apply Alloc => //. lia. apply Hnid. lia.
  
Qed.
Lemma can_free: forall T a nid, nth_alloc T.(segl_data) (N.to_nat a) = Some (Some nid) ->
                           exists T', sfree T a nid T'.
Proof.
  intros. admit.
Admitted. *)


(*Inductive isAlloc : N -> segment_list -> Prop :=
  Allocated : forall nid addr A, nth_alloc A.(segl_data) (N.to_nat addr) = Some (Some nid)
                            -> isAlloc nid A. *)

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

(* Definition isSound_aux T (l : list (N * N * N)) : Prop :=
  List.forallb (fun '(a,b,c) => N.leb (b + c) (seg_length T)) l. *)

Fixpoint isSound_aux T (l : list (N * N * N)) : Prop :=
  match l with
  | [::] => True
  | (a,b,c) :: q => N.leb (b + c) (seg_length T) /\ compatible b c q /\
                    ~(List.In a (List.map (fun '(x,_,_) => x) q)) /\ isSound_aux T q
  end. 

Definition isSound T A : Prop :=
  isSound_aux T A.(allocated).



Lemma data_length_is_compatible_aux :
  forall l T size, isSound_aux T l -> compatible (seg_length T) size l.
Proof.
  intro l. induction l => //=.
  intros. destruct a. destruct p.
  destruct H as (Hlim & Hcomp & Hdup & H).
  split.
  - right. 
    apply N.leb_le in Hlim. lia.
  - apply IHl.
    done. 
Qed. 

Lemma data_length_is_compatible :
  forall T A size, isSound T A -> compatible (seg_length T) size A.(allocated).
Proof.
  intros.
  apply data_length_is_compatible_aux.
  exact H.
Qed.


Lemma find_and_remove_compatible:
  forall l nid l' a n add size,
    compatible add size l -> find_and_remove nid l = Some (l', a, n) -> compatible add size l'.
Proof.
  induction l => //=.
  intros * Hcomp Hfr. destruct a as [[??]?].
  destruct (n0 =? nid)%N.
  - inversion Hfr; subst. by destruct Hcomp.
  - destruct Hcomp as [??]. destruct (find_and_remove nid l) eqn:Hfr' => //.
    destruct p as [[??]?]. eapply IHl in Hfr' => //; last exact H0.
    inversion Hfr; subst. simpl. split => //.
Qed.

Lemma find_and_remove_nodup:
  forall l nid l' a n nid',
    (~ List.In nid' (List.map (fun '(x,_,_) => x) l)) ->
    find_and_remove nid l = Some (l', a, n) ->
    (~ List.In nid' (List.map (fun '(x,_,_) => x) l')).
Proof.
  induction l => //=.
  intros * Hdup Hfr. destruct a as [[??]?].
  intro Habs.
  destruct (n0 =? nid)%N eqn:Hn.
  - apply N.eqb_eq in Hn as ->. inversion Hfr; subst.
    apply Hdup. by right.
  - destruct (find_and_remove nid l) eqn:Hfr' => //.
    destruct p as [[??]?]. eapply IHl in Hfr' => //.
    2:{ intro Habs'. apply Hdup. right. exact Habs'. }
    inversion Hfr; subst. apply Hfr'. simpl in Habs.
    destruct Habs => //. rewrite H in Hdup.
    exfalso. apply Hdup. left. done.
Qed.
  
Lemma find_and_remove_isSound :
  forall T l nid l' a n,
    isSound_aux T l -> find_and_remove nid l = Some (l', a, n) -> isSound_aux T l'.
Proof.
  intros T l.
  induction l => //=.
  intros nid l' a0 n HSound.
  destruct a.
  destruct p.
  destruct HSound as (Hlim & Hcomp & Hdup & HSound).
  destruct (n1 =? nid)%N eqn:Hn.
  - intro H; inversion H; subst.
    done. 
  - destruct (find_and_remove nid l) eqn:Hl => //.
    destruct p.
    destruct p.
    intro H; inversion H; subst.
    unfold isSound_aux.
    repeat split => //.
    eapply find_and_remove_compatible. exact Hcomp.
    exact Hl.
    eapply find_and_remove_nodup. exact Hdup. exact Hl.
    eapply IHl. exact HSound. exact Hl.
Qed. 

