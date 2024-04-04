(* Some extra operations on lists. *)

Set Implicit Arguments.

From Coq Require Import List.

(** Given list of option types, check that all options are [Some]
   and return the corresponding list of values. **)
Fixpoint those0 {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | None :: xs => None
  | (Some y) :: xs =>
    option_map (fun ys => y :: ys) (those0 xs)
  end.

Local Fixpoint those_aux {A} (acc : option (list A)) (l : list (option A)) : option (list A) :=
  match acc with
  | None => None
  | Some ys_rev =>
    match l with
    | nil => Some ys_rev
    | None :: xs => None
    | Some y :: xs =>
      those_aux (Some (y :: ys_rev)) xs
    end
  end.

(** A tail-recursive variant of [those0]. **)
Definition those {A} (l : list (option A)) : option (list A) :=
  match those_aux (Some nil) l with
  | None => None
  | Some l => Some (List.rev l)
  end.

Local Lemma those0_None : forall A (l : list (option A)),
  In None l <-> those0 l = None.
Proof.
  induction l as [|o l]; simpl.
  - split; inversion 1.
  - destruct o as [a|]; split; auto.
    + rewrite IHl. intros [?|E]; [discriminate|]. rewrite E. auto.
    + destruct those0; simpl; try discriminate. rewrite IHl. auto.
Qed.

Local Lemma those_aux_None : forall A (la : list A) l,
  In None l <-> those_aux (Some la) l = None.
Proof.
  intros A la l. generalize la. clear la. induction l as [|o l]; intros la; simpl.
  - split; inversion 1.
  - destruct o as [a|].
    + rewrite <- IHl. split; auto. intros [?|?]; [discriminate|auto].
    + split; auto.
Qed.

Local Lemma cons_app : forall A (a : A) l, a :: l = (a :: nil) ++ l.
Proof. reflexivity. Qed.

Local Lemma those_those0_gen : forall A l (la : list A),
  Forall (fun o : option A => o <> None) l ->
  exists rl rl',
    those0 l = Some rl /\ those_aux (Some la) l = Some rl' /\
    List.rev la ++ rl = List.rev rl'.
Proof.
  induction l; intros la F.
  - repeat eexists. rewrite app_nil_r. reflexivity.
  - inversion F. subst.
    destruct a as [a|]; try solve [ exfalso; auto ].
    edestruct IHl as (rl&rl'&E1&E2&E3); auto.
    repeat eexists.
    + simpl. rewrite E1. reflexivity.
    + simpl. rewrite E2. reflexivity.
    + rewrite <- E3. rewrite cons_app with (l := rl). rewrite cons_app with (l := la).
      rewrite rev_app_distr. rewrite <- app_assoc. reflexivity.
Qed.

(** [those0] and [those] are indeed equivalent. **)
Lemma those_those0 : forall A (l : list (option A)),
  those0 l = those l.
Proof.
  intros A l. unfold those.
  destruct (Forall_Exists_dec (fun o => o <> None)
              (fun x => ltac:(destruct x; auto; left; discriminate)) l) as [d|d].
  - eapply those_those0_gen in d. destruct d as (rl&rl'&E1&E2&E3).
    rewrite E1. rewrite E2. rewrite <- E3. reflexivity.
  - rewrite Exists_exists in d. destruct d as (x&I&E). destruct x.
    + exfalso. apply E. discriminate.
    + set (I' := I). clearbody I'.
      rewrite those0_None in I. rewrite I.
      rewrite those_aux_None in I'. rewrite I'.
      reflexivity.
Qed.

Lemma those_app {A} (l1 : list (option A)) l2 tl1 tl2 :
  those l1 = Some tl1 -> those l2 = Some tl2 -> those (l1 ++ l2) = Some (tl1 ++ tl2).
Proof.
  generalize dependent tl1. induction l1 ; intros.
  unfold those in H ; inversion H. rewrite app_nil_l. auto.
  rewrite <- those_those0 in H.
  unfold those0 in H. destruct a ; try (inversion H; auto).
  fold (those0 l1) in H. rewrite those_those0 in H.
  destruct tl1 ; destruct (those l1) ; inversion H.
  assert (those (l1 ++ l2) = Some (l ++ tl2)); try (eapply IHl1; eauto).
  rewrite <- those_those0. unfold those0; auto. simpl.
  fold (those0 (l1 ++ l2)). rewrite those_those0, H1. simpl. subst. reflexivity.
Qed.

Lemma those_app_inv {A} (l1 : list (option A)) l2 tl :
  those (l1 ++ l2) = Some tl ->
  exists tl1 tl2, those l1 = Some tl1 /\ those l2 = Some tl2 /\ tl1 ++ tl2 = tl.
Proof.
  generalize dependent tl ; induction l1 ; intros.
  eexists _, _ ; repeat split; simpl; auto.
  rewrite <- app_comm_cons in H.
  rewrite <- those_those0 in H.
  unfold those0 in H. destruct a eqn:Ha ; try (inversion H; auto).
  destruct (those0 (l1 ++ l2)) eqn:Hth ; unfold those0 in Hth ; rewrite Hth in H ;
    try (inversion H; auto).
  fold (those0 (l1 ++ l2)) in Hth.
  rewrite those_those0 in Hth.
  rewrite Hth in IHl1.
  destruct (IHl1 l) as (tl1 & tl2 & Hth1 & Hth2 & Htl); auto.
  rewrite <- those_those0.
  unfold those0. fold (those0 l1).
  unfold option_map. rewrite those_those0, Hth1.
  eexists _,_ ; repeat split; simpl; eauto. rewrite Htl.
  reflexivity.
Qed.

Fixpoint mapi_aux {A B} (acc : nat * list B) (f : nat -> A -> B) (xs : list A) : list B :=
  let '(i, ys_rev) := acc in
  match xs with
  | nil =>
    List.rev ys_rev
  | cons x xs' =>
    let y := f i x in
    mapi_aux (i + 1, cons y ys_rev) f xs'
  end.

Definition mapi {A B} (f : nat -> A -> B) (xs : list A) : list B :=
  mapi_aux (0, nil) f xs.

Definition fold_lefti {A B} (f : nat -> A -> B -> A) (xs : list B) (acc0 : A) : A :=
  let '(_, acc_end) :=
    List.fold_left
      (fun '(k, acc) x =>
        (k + 1, f k acc x))
      xs
      (0, acc0) in
  acc_end.

From ITree Require ITree ITreeFacts.

Section Monad.

Import ITree ITreeFacts.
Import Monads.
Import MonadNotation.

Open Scope monad_scope.

(** Let us assume a monad. **)
Variable m : Type -> Type.
Context {M : Monad m}.

(** Calls a function to each of the elements of a list, bindings the results into a new list. **)
Fixpoint bind_list0 {A B} (f : A -> m B) (l : list A) : m (list B) :=
  match l with
  | nil => ret nil
  | a :: l =>
    r <- f a ;;
    l' <- bind_list0 f l ;;
    ret (r :: l')
  end.

Fixpoint bind_list_aux {A B} (f : A -> m B) acc (l : list A) : m (list B) :=
  match l with
  | nil => ret (List.rev acc)
  | a :: l =>
    r <- f a ;;
    bind_list_aux f (r :: acc) l
  end.

(** A tail-recursive version of [bind_list0]. **)
Definition bind_list {A B} (f : A -> m B) :=
  bind_list_aux f nil.

End Monad.

