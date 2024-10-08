(** Miscellaneous properties about Wasm operations **)

From MSWasm Require Export datatypes_properties operations typing opsem common stdpp_aux handle.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require ssrnat.
From stdpp Require gmap.
(* From StrongInduction Require Import StrongInduction. *)
From Coq Require Import Bool BinNat Program.Equality.
Require Import Lia.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Basic Lemmas **)

Lemma const_const a: is_const (AI_const a).
Proof. destruct a => //. Qed.

Lemma app_app (es1 es2 es3 es4: list administrative_instruction) :
  es1 ++ es2 = es3 ++ es4 ->
  length es1 = length es3 ->
  (es1, es2) = (es3, es4).
Proof.
  move: es2 es3 es4.
  elim: es1; destruct es3 => //=; move => es4 H2 Hlen; try by subst.
  inversion H2; subst; clear H2.
  inversion Hlen; clear Hlen.
  apply H in H3 => //.
  by inversion H3 => //; subst.
Qed.

Lemma combine_app {T1 T2: Type} (l1 l3: list T1) (l2 l4: list T2):
  length l1 = length l2 ->
  List.combine (l1 ++ l3) (l2 ++ l4) = List.combine l1 l2 ++ List.combine l3 l4.
Proof.
  generalize dependent l2.
  generalize dependent l3.
  generalize dependent l4.
  induction l1; move => l4 l3 l2 Hlen => /=; first by destruct l2 => //.
  - destruct l2 => //=.
    simpl in Hlen.
    inversion Hlen; subst; clear Hlen.
    f_equal.
    by apply IHl1.
Qed.

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2. elim vs1 => {vs1} //=.
  - move => a vs1' IHvs1 H1 H2. simpl in H1. simpl.
    apply andb_true_iff in H1. destruct H1. rewrite IHvs1 //=. by rewrite andbT.
Qed.

Lemma const_list_split: forall vs1 vs2,
    const_list (vs1 ++ vs2) ->
    const_list vs1 /\
    const_list vs2.
Proof.
  induction vs1 => //=; move => vs2 HConst.
  move/andP in HConst. destruct HConst.
  apply IHvs1 in H0. destruct H0.
  split => //.
  by apply/andP.
Qed.    

(** This lemma justifies the computation “to the first non-[const_list]”. **)
Lemma const_list_concat_inv : forall vs1 vs2 e1 e2 es1 es2,
  const_list vs1 ->
  const_list vs2 ->
  ~ is_const e1 ->
  ~ is_const e2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  induction vs1 => vs2 e1 e2 es1 es2 C1 C2 N1 N2; destruct vs2 => /=; inversion 1; subst;
    try move: C1 => /= /andP [? ?] //;
    try move: C2 => /= /andP [? ?] //.
  - done.
  - apply IHvs1 in H2 => //. move: H2 => [? [? ?]]. by subst.
Qed.

Lemma const_list_take: forall vs l,
    const_list vs ->
    const_list (take l vs).
Proof.
  move => vs. induction vs => //=.
  - move => l HConst. destruct l => //=.
    + simpl. simpl in HConst. apply andb_true_iff in HConst. destruct HConst.
      apply andb_true_iff. split => //. by apply IHvs.
Qed.

Lemma v_to_e_is_const_list: forall vs,
    const_list (v_to_e_list vs).
Proof.
  move => vs. elim: vs => //.
  intros a; destruct a => //. 
Qed.

Lemma v_to_e_cat: forall vs1 vs2,
    v_to_e_list vs1 ++ v_to_e_list vs2 = v_to_e_list (vs1 ++ vs2).
Proof.
  move => vs1. elim: vs1 => //=.
  - move => a l IH vs2. by rewrite IH.
Qed.

Lemma v_to_e_inj: forall vs1 vs2,
    v_to_e_list vs1 = v_to_e_list vs2 ->
    vs1 = vs2.
Proof.
  move => vs1.
  induction vs1; move => vs2; destruct vs2 => //=.
  move => Heq. inversion Heq; subst.
  destruct a, v => //; f_equal; inversion H0; subst => //.
  all: by apply IHvs1.
Qed.

Lemma split_vals_e_v_to_e_duality: forall es vs es',
    split_vals_e es = (vs, es') ->
    es = (v_to_e_list vs) ++ es'.
Proof.
  move => es vs. move: es. elim: vs => //.
  - move=> es es'. destruct es => //=.
    + by inversion 1.
    + case a; try by inversion 1; [idtac].
      move => b. case b; try by inversion 1. 
      1-2:move => H.  1-2:by destruct (split_vals_e es).
      
  - move => a l H es es' HSplit. unfold split_vals_e in HSplit.
    destruct es => //. destruct a0 => //. destruct b => //.
    all: fold split_vals_e in HSplit.
    all: destruct (split_vals_e es) eqn:Heqn. all: inversion HSplit; subst.
    all: simpl. all: f_equal. all: by apply: H.
Qed.

Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof. by []. Qed.

Lemma v_to_e_list0 : v_to_e_list [::] = [::].
Proof. reflexivity. Qed.

Lemma v_to_e_list1 : forall v, v_to_e_list [:: v] = [:: AI_const v].
Proof. reflexivity. Qed.

Lemma e_is_trapP : forall e, reflect (e = AI_trap) (e_is_trap e).
Proof.
  case => //= >; by [ apply: ReflectF | apply: ReflectT ].
Qed.

Lemma es_is_trapP : forall l, reflect (l = [::AI_trap]) (es_is_trap l).
Proof.
  case; first by apply: ReflectF.
  move=> // a l. case l => //=.
  - apply: (iffP (e_is_trapP _)); first by elim.
    by inversion 1.
  - move=> >. by apply: ReflectF.
Qed.


Lemma split_n_is_take_drop: forall es n,
    split_n es n = (take n es, drop n es).
Proof.
  move => es n. move: es. elim:n => //=.
  - move => es. by destruct es.
  - move => n IH es'. destruct es' => //=.
    + by rewrite IH.
Qed.

Section using_ssrnat.
  Import ssrnat.

  
Lemma update_list_at_is_set_nth: forall {X:Type} (l:list X) n x,
    n < size l ->
    set_nth x l n x = update_list_at l n x.
Proof.
  move => X l n x. move: n. elim: l => //=.
  move => a l IH n HLen. destruct n => //=.
  unfold update_list_at. simpl. f_equal. by apply IH.
Qed.

Lemma length_is_size: forall {X:Type} (l: list X),
    length l = size l.
Proof.
  move => X l. by elim: l.
Qed.

Lemma v_to_e_take_exchange: forall vs n,
    v_to_e_list (take n vs) = take n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. destruct vs' => //=.
    + by rewrite IH.
Qed.

Lemma v_to_e_drop_exchange: forall vs n,
    v_to_e_list (drop n vs) = drop n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. by destruct vs' => //=.
Qed.

Lemma v_to_e_size: forall vs,
    size (v_to_e_list vs) = size vs.
Proof.
  move => vs. elim: vs => //=.
  - move => a l IH. by f_equal.
Qed.      
      
(** This lemma is useful when an instruction consumes some expressions on the stack:
  we usually have to split a list of expressions by the expressions effectively
  consumed by the instructions and the one left. **)
Lemma v_to_e_take_drop_split: forall l n,
  v_to_e_list l = v_to_e_list (take n l) ++ v_to_e_list (drop n l).
Proof.
  move => l n. rewrite v_to_e_cat. by rewrite cat_take_drop.
Qed.

Lemma v_to_e_take: forall l n,
  v_to_e_list (take n l) = take n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite take0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_drop: forall l n,
  v_to_e_list (drop n l) = drop n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite drop0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  elim => //=.
  move => a l IH. rewrite rev_cons. rewrite -cats1. rewrite -v_to_e_cat.
  rewrite rev_cons. rewrite -cats1. by rewrite -IH.
Qed.

Lemma to_b_list_concat: forall es1 es2 : seq administrative_instruction,
    to_b_list (es1 ++ es2) = to_b_list es1 ++ to_b_list es2.
Proof.
  induction es1 => //=.
  move => es2. by f_equal.
Qed.

Lemma to_e_list_basic: forall bes,
    es_is_basic (to_e_list bes).
Proof.
  induction bes => //=.
  split => //=.
  unfold e_is_basic. by eauto.
Qed.

Lemma basic_concat: forall es1 es2,
    es_is_basic (es1 ++ es2) ->
    es_is_basic es1 /\ es_is_basic es2.
Proof.
  induction es1 => //=.
  move => es2 H. destruct H.
  apply IHes1 in H0. destruct H0.
  by repeat split => //=.
Qed.

Lemma basic_split: forall es1 es2,
    es_is_basic es1 ->
    es_is_basic es2 ->
    es_is_basic (es1 ++ es2).
Proof.
  induction es1 => //=.
  move => es2 H1 H2.
  destruct H1.
  split => //=.
  by apply IHes1.
Qed.


Lemma to_b_list_rev: forall es : seq administrative_instruction,
    rev (to_b_list es) = to_b_list (rev es).
Proof.
  induction es => //=.
  repeat rewrite rev_cons.
  rewrite IHes.
  repeat rewrite -cats1.
  by rewrite to_b_list_concat.
Qed.

Lemma vs_to_vts_cat: forall vs1 vs2,
    vs_to_vts (vs1 ++ vs2) = vs_to_vts vs1 ++ vs_to_vts vs2.
Proof.
  induction vs1 => //=.
  move => vs2. by rewrite IHvs1.
Qed.
  
Lemma vs_to_vts_rev: forall vs,
    vs_to_vts (rev vs) = rev (vs_to_vts vs).
Proof.
  induction vs => //=.
  repeat rewrite rev_cons.
  repeat rewrite -cats1.
  rewrite vs_to_vts_cat.
  by rewrite IHvs.
Qed.
  
Lemma const_es_exists: forall es,
    const_list es ->
    exists vs, es = v_to_e_list vs.
Proof.
  induction es => //=.
  - by exists [::].
  - move => HConst.
    move/andP in HConst. destruct HConst.
    destruct a => //=. destruct b => //=. 
    all: edestruct IHes => //=.
    exists (VAL_numeric n :: x). 2: exists (VAL_handle h :: x). all: simpl. all: by rewrite H1.
Qed.

Lemma b_e_elim: forall bes es,
    to_e_list bes = es ->
    bes = to_b_list es /\ es_is_basic es.
Proof.
  induction bes; move => es H => //=.
  - by rewrite -H.
  - simpl in H. assert (es = to_e_list (a :: bes)) as H1.
    + by rewrite -H.
    + rewrite H1. split.
      -- simpl. f_equal. by apply IHbes.
      -- by apply to_e_list_basic.
Qed.

Lemma e_b_elim: forall bes es,
    bes = to_b_list es ->
    es_is_basic es ->
    es = to_e_list bes.
Proof.
  induction bes; move => es H1 H2 => //=.
  - by destruct es => //=.
  - destruct es => //=. simpl in H1. simpl in H2. destruct H2.
    inversion H1; subst.
    inversion H; subst => //=.
    f_equal. apply IHbes => //=.
Qed.
    
Lemma to_e_list_injective: forall bes bes',
    to_e_list bes = to_e_list bes' ->
    bes = bes'.
Proof.
  move => bes bes' H.
  apply b_e_elim in H; destruct H; subst => //=.
  induction bes' => //=.
  f_equal. apply IHbes'. by apply to_e_list_basic.
Qed.

Lemma to_e_list_cat: forall bes1 bes2,
    to_e_list (bes1 ++ bes2) = to_e_list bes1 ++ to_e_list bes2.
Proof.
  induction bes1 => //.
  move => bes2. simpl. by f_equal.
Qed.

Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [::e1] = l2 ++ [::e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [::e1]) = rev (l2 ++ [::e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

Lemma concat_cancel_last_n: forall (l1 l2 l3 l4: seq value_type),
    l1 ++ l2 = l3 ++ l4 ->
    size l2 = size l4 ->
    (l1 == l3) && (l2 == l4).
Proof.
  move => l1 l2 l3 l4 HCat HSize.
  rewrite -eqseq_cat; first by apply/eqP.
  assert (size (l1 ++ l2) = size (l3 ++ l4)); first by rewrite HCat.
  repeat rewrite size_cat in H.
  rewrite HSize in H. by lias.
Qed.

Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [::e1] = [::e2] ->
    es = [::] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list2 : forall {X:Type} (es: seq X) (e1 e2 e3:X),
    es ++ [::e1] = [::e2; e3] ->
    es = [::e2] /\ e1 = e3.
Proof.
  move => X es e1 e2 e3 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list3 : forall {X:Type} (es: seq X) (e1 e2 e3 e4:X),
    es ++ [::e1] = [::e2; e3; e4] ->
    es = [::e2; e3] /\ e1 = e4.
Proof.
  move => X es e1 e2 e3 e4 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list4 : forall {X:Type} (es: seq X) (e1 e2 e3 e4 e5:X),
    es ++ [::e1] = [::e2; e3; e4; e5] ->
    es = [::e2; e3; e4] /\ e1 = e5.
Proof.
  move => X es e1 e2 e3 e4 e5 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma list_nth_prefix: forall {X:Type} (l1 l2: seq X) x,
    List.nth_error (l1 ++ [::x] ++ l2) (length l1) = Some x.
Proof.
  move => X. induction l1 => //=.
Qed.

End using_ssrnat.
      


(** * Tactics **)

(** [gen_ind] perform an induction over predicates like [be_typing], generalising its parameters,
  but not generalising any section variables such as [host_function].
  The reason for this tactic is that [dependent induction] is far too aggressive
  in its generalisation, and prevents the use of some lemmas. **)

(** The first step is to name each parameter of the predicate. **)
Ltac gen_ind_pre H :=
  let rec aux v :=
    lazymatch v with
    | ?f ?x =>
        let only_do_if_ok_direct t cont :=
        lazymatch t with
        | HandleBytes => idtac
        | Type => idtac
        | _ => cont tt
        end in
      let t := type of x in
      only_do_if_ok_direct t ltac:(fun _ =>
        let t :=
          match t with
          | _ _ => t
          | ?t => eval unfold t in t
          | _ => t
          end in
        only_do_if_ok_direct t ltac:(fun _ =>
          let x' :=
            let rec get_name x :=
              match x with
              | ?f _ => get_name f
              | _ => fresh x
              | _ => fresh "x"
              end in
            get_name x in
          move: H;
          set_eq x' x;
          let E := fresh "E" x' in
          move=> E H));
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** Then, each of the associated parameters can be generalised. **)
Ltac gen_ind_gen H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize dependent x) ltac:(idtac)
    | _ => fail "unable to generalize" t
    end in
  let rec aux v :=
    lazymatch v with
    | ?f ?x => 
    lazymatch goal with
      | _ : x = ?y |- _ => try_generalize y
    | _ => lazymatch type of x with
          | HandleBytes => idtac
          | _ => fail "unexpected term" v
          end 
      end;
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** After the induction, one can inverse them again (and do some cleaning). **)
Ltac gen_ind_post :=
  repeat lazymatch goal with
  | |- _ = _ -> _ => inversion 1
  | |- _ -> _ => intro
  end;
  repeat lazymatch goal with
  | H: True |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  end.

(** Wrapping every part of the generalised induction together. **)
Ltac gen_ind H :=
  gen_ind_pre H;
  gen_ind_gen H;
  induction H;
  gen_ind_post.

(** Similar to [gen_ind H; subst], but cleaning just a little bit more. **)
Ltac gen_ind_subst H :=
  gen_ind H;
  subst;
  gen_ind_post.

(** Calls the continuation on [v] or, if it failed, on [v] whose root has been unfolded.
  This is useful for tactics with pattern mtaching recognising a predicate which is
  frequently folded in a section, like [be_typing]. **)
Ltac call_unfold v cont :=
  let rec unfold_root :=
    lazymatch v with
    | ?f ?x =>
      let f := unfold_root f in
      constr:(f x)
    | ?x => eval unfold x in x
    end in
  first [
      cont v
    | let v := unfold_root v in
      cont v ].

(** Perform basic simplifications of [es_is_basic]. **)
Ltac basic_inversion :=
   repeat lazymatch goal with
         | H: True |- _ =>
           clear H
         | H: es_is_basic (_ ++ _) |- _ =>
           let Ha := fresh H in
           let Hb := fresh H in
           apply basic_concat in H; destruct H as [Ha Hb]
         | H: es_is_basic [::] |- _ =>
           clear H
         | H: es_is_basic [::_] |- _ =>
           let H1 := fresh H in
           let H2 := fresh H in
           try by (unfold es_is_basic in H; destruct H as [H1 H2]; inversion H1)
         | H: e_is_basic _ |- _ =>
           inversion H; try by []
         end.

(** Rewrite hypotheses on the form [_ ++ [:: _] = _] as some easier to use equalities. **)
Ltac extract_listn :=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: _ :: _ = (_ ++ _)%list |- _ => symmetry in H
  | H: _ :: _ = _ ++ _ |- _ => symmetry in H
         end.

Ltac fold_upd_context :=
  lazymatch goal with
  | |- context [upd_local (upd_return ?C ?ret) ?loc] =>
    replace (upd_local (upd_return C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  | |- context [upd_return (upd_local ?C ?ret) ?loc] =>
    replace (upd_return (upd_local C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  end.



(** * More Advanced Lemmas **)



Lemma lfilled_swap : forall i lh es LI es', 
  lfilled i lh es LI ->
  exists LI', lfilled i lh es' LI'.
Proof.
  intros i.
  induction i;intros lh es LI es' Hfill%lfilled_Ind_Equivalent.
  { inversion Hfill; subst.
    exists (vs ++ es' ++ es'0).
    apply lfilled_Ind_Equivalent. by constructor. }
  { inversion Hfill;subst.
    apply lfilled_Ind_Equivalent in H1.
    apply IHi with (es':=es') in H1 as [LI' HLI'].
    exists (vs ++ [::AI_label n es'0 LI'] ++ es'').
    apply lfilled_Ind_Equivalent. constructor;auto.
    by apply lfilled_Ind_Equivalent. }
Qed.

Lemma lfilled_inj : forall i lh es LI LI',
  lfilled i lh es LI ->
  lfilled i lh es LI' ->
  LI = LI'.
Proof.
  intros i.
  induction i; intros lh es LI LI'
                      Hfill1%lfilled_Ind_Equivalent
                      Hfill2%lfilled_Ind_Equivalent.
  { inversion Hfill1; subst.
    inversion Hfill2; subst. done. }
  { inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHi lh' es LI0 LI);auto;by apply lfilled_Ind_Equivalent. }
Qed.

Lemma lfilled_collapse1: forall n lh vs es LI l,
    lfilledInd n lh (vs++es) LI ->
    const_list vs ->
    length vs >= l ->
    exists lh', lfilledInd n lh' ((drop (length vs-l) vs) ++ es) LI.
Proof.
  move => n lh vs es LI l HLF HConst HLen.
  remember (vs++es) as es'. induction HLF; subst.
  - exists (LH_base (vs0 ++ (take (length vs - l) vs)) es').
    replace (vs0++(vs++es)++es') with ((vs0++take (length vs - l) vs) ++ (drop (length vs - l) vs ++ es) ++ es').
    { apply LfilledBase. apply const_list_concat => //=.
      by apply const_list_take. }
    repeat rewrite -catA. f_equal.
    repeat rewrite catA. do 2 f_equal.
    by apply cat_take_drop. 
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse2: forall n lh es es' LI,
    lfilledInd n lh (es++es') LI ->
    exists lh', lfilledInd n lh' es LI.
Proof.
  move => n lh es es' LI HLF. remember (es ++ es') as Ees. induction HLF; subst.
  - eexists (LH_base _ _). rewrite <- catA. by apply LfilledBase.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse3: forall k lh n les es LI,
    lfilledInd k lh [:: AI_label n les es] LI ->
    exists lh', lfilledInd (k+1) lh' es LI.
Proof.
  move => k lh n les es LI HLF. remember [:: AI_label n les es] as E.  induction HLF; subst.
  - eexists (LH_rec _ _ _ _ _). apply LfilledRec. auto.
    assert (lfilledInd 0 (LH_base nil nil) es ([::] ++ es ++ [::])). { by apply LfilledBase. }
    simpl in H0. rewrite cats0 in H0. by apply H0.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_deterministic: forall k lh es les les',
    lfilledInd k lh es les ->
    lfilledInd k lh es les' ->
    les = les'.
Proof.
  move => k lh es les les' HLF HLF'.
  apply lfilled_Ind_Equivalent in HLF. unfold operations.lfilled in HLF.
  apply lfilled_Ind_Equivalent in HLF'. unfold operations.lfilled in HLF'.
  destruct (lfill k lh es) => //.
  replace les' with l.
  { move: HLF. by apply/eqseqP. }
  symmetry. move: HLF'. by apply/eqseqP. 
Qed.  

Lemma all_projection: forall {X:Type} f (l:seq X) n x,
    all f l ->
    List.nth_error l n = Some x ->
    f x.
Proof.
  move => X f l n x.
  generalize dependent l.
  induction n => //; destruct l => //=; move => HF HS; remove_bools_options => //.
  eapply IHn; by eauto.
Qed.

Lemma all2_projection: forall {X Y:Type} f (l1:seq X) (l2:seq Y) n x1 x2,
    all2 f l1 l2 ->
    List.nth_error l1 n = Some x1 ->
    List.nth_error l2 n = Some x2 ->
    f x1 x2.
Proof.
  move => X Y f l1 l2 n.
  generalize dependent l1.
  generalize dependent l2.
  induction n => //=; move => l2 l1 x1 x2 HALL HN1 HN2.
  - destruct l1 => //=. destruct l2 => //=.
    inversion HN1. inversion HN2. subst. clear HN1. clear HN2.
    simpl in HALL. move/andP in HALL. by destruct HALL.
  - destruct l1 => //=. destruct l2 => //=.
    simpl in HALL. move/andP in HALL. destruct HALL.
    eapply IHn; by eauto.
Qed.

Lemma all2_Forall2 {T1 T2: Type} r (l1: list T1) (l2: list T2):
  all2 r l1 l2 <-> List.Forall2 r l1 l2.
Proof.
  move: l2.
  elim: l1 => //=.
  - move => l2; destruct l2 => //=.
    split => //.
    move => Hcontra.
    by inversion Hcontra.
  - move => e l1 IH l2.
    destruct l2 => //=.
    + split => //.
      move => Hcontra.
      by inversion Hcontra.
    + split; move => H.
      * move/andP in H.
        destruct H.
        constructor => //.
        by apply IH.
      * apply/andP.
        inversion H; subst; clear H.
        split => //.
        by apply IH.
Qed.


Definition function {X Y:Type} (f: X -> Y -> Prop) : Prop :=
  forall x y1 y2, ((f x y1 /\ f x y2) -> y1 = y2).

Lemma all2_function_unique: forall {X Y:Type} f (l1:seq X) (l2 l3:seq Y),
    all2 f l1 l2 ->
    all2 f l1 l3 ->
    function f ->
    l2 = l3.
Proof.
  move => X Y f l1.
  induction l1 => //=; move => l2 l3 HA1 HA2 HF.
  - destruct l2 => //. by destruct l3 => //.
  - destruct l2 => //=; destruct l3 => //=.
    simpl in HA1. simpl in HA2.
    move/andP in HA1. move/andP in HA2.
    destruct HA1. destruct HA2.
    unfold function in HF.
    assert (y = y0); first by eapply HF; eauto.
    rewrite H3. f_equal.
    by apply IHl1.
Qed.


(** The decreasing measure used in the definition of [lfilled_pickable_rec_gen]. **)
(* Definition lfilled_pickable_rec_gen_measure (LI : seq administrative_instruction) :=
  TProp.max
    (seq_administrative_instruction_rect'
       (fun _ => 0)
       (fun _ => 0)
       0
       (fun _ => 0)
       (fun _ LI1 LI2 m1 m2 => 1 + TProp.max m2)
       (fun _ _ LI' m => 0)
       (fun _ _ _ => 0)
       LI). *)

Fixpoint lfilled_pickable_rec_gen_measure_single (e : administrative_instruction) :=
  match e with
  | AI_label _ _ es1 =>
(*      List.fold_left (fun a b => a + lfilled_pickable_rec_gen_measure_single b) es0 0 + *)
      1 + List.fold_left (fun a b => max a (lfilled_pickable_rec_gen_measure_single b)) es1 0
  | _ => 0
  end.
     
                

Definition lfilled_pickable_rec_gen_measure (LI : seq administrative_instruction) :=
  List.fold_left (fun a b => max a (lfilled_pickable_rec_gen_measure_single b)) LI 0.

(* Section using_ssrnat.
  Import ssrnat. *)

Lemma fold_left_max_rem {A} n (l : seq A) f:
  List.fold_left (fun a b => max a (f b)) l n = max n (List.fold_left (fun a b => max a (f b)) l 0).
Proof.
  generalize dependent n. induction l; intros n => //=. lia.
  rewrite (IHl (max n (f a))). rewrite (IHl (f a)).
  lia.
Qed. 

Lemma fold_left_max_app_cons {A} x (l : seq A) f n:
  List.fold_left (fun a b => max a (f b)) (x :: l) n =
    max (f x) (List.fold_left (fun a b => max a (f b)) l n).
Proof.
  simpl. rewrite (fold_left_max_rem (max n (f x))).
  rewrite (fold_left_max_rem n).
  lia.
Qed. 



(*
Lemma fold_left_max_app {A} (l : seq A) f n:
  List.fold_left (fun a b => max a (f b)) l n >= n.
Proof.
  generalize dependent n. induction l; intros n => //=.
  specialize (IHl (Nat.max n (f a))).
  lia.
Qed. 
*)

Lemma lfilled_pickable_rec_gen_measure_cons : forall I LI,
  lfilled_pickable_rec_gen_measure LI <= lfilled_pickable_rec_gen_measure (I :: LI).
Proof.
  move=> I LI. unfold lfilled_pickable_rec_gen_measure.
  rewrite fold_left_max_app_cons. lia.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_l : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI1 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /lfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /lfilled_pickable_rec_gen_measure /=.
    do 2 rewrite (fold_left_max_rem (_ a)).
    unfold lfilled_pickable_rec_gen_measure in IHLI1. lia.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_r : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI2 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /lfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /lfilled_pickable_rec_gen_measure /=.
    rewrite (fold_left_max_rem (_ a)).
    unfold lfilled_pickable_rec_gen_measure in IHLI1. lia.
Qed.

Lemma lfilled_pickable_rec_gen_measure_label_r : forall n es LI LI',
  lfilled_pickable_rec_gen_measure LI < lfilled_pickable_rec_gen_measure (AI_label n es LI :: LI').
Proof.
  move=> n es LI LI'. rewrite /lfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lia.
Qed.

(** A helper definition for [lfilled_decidable_rec]. **)
Definition lfilledInd_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilledInd n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')); first by [].
  move: 0 => k.
  have [m E]: { m | lfilled_pickable_rec_gen_measure es' = m }; first by eexists.
  move: fes D0 es' E k.
  assert (forall m' m, m <= m' ->
                forall fes : nat -> lholed -> seq administrative_instruction,
                  (forall (es' : seq administrative_instruction) (lh lh' : lholed) (n0 : nat),
                      decidable (lfilledInd 0 lh (fes n0 lh') es')) ->
                  forall es' : seq administrative_instruction,
                    lfilled_pickable_rec_gen_measure es' = m ->
                    forall k : nat,
                      pickable2 (fun (n : nat) (lh : lholed) => lfilledInd n lh (fes (k + n) lh) es')) as H.
  2:{ apply (H (S m) m). lia. }
  clear m. induction m'.
  { move=> m Hm fes D0 es' E k.
    destruct m; last lia.
    have Dcl: forall vs, decidable (const_list vs).
    { move=> vs. by apply: is_true_decidable. }
    (** First, we check whether we can set [n = 0]. **)
    have P0: pickable2 (fun vs es'' =>
                       let lh := LH_base vs es'' in
                       let es := fes k lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ lfilledInd 0 lh es es').
    {
      have: pickable3 (fun vs es es'' =>
                         es' = vs ++ es ++ es'' /\ let lh := LH_base vs es'' in
                                                  es = fes k lh /\ const_list vs /\ lfilledInd 0 lh es es').
      {
        apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
        case E': (es == fes k (LH_base vs es'')); move/eqP: E' => E'.
        - rewrite E'. repeat apply: decidable_and => //. by apply: eq_comparable.
        - right. by move=> [Ees2 [Cl I]].
      }
      case.
      - move=> [[[vs es] es''] [E1 [E2 [Cl I]]]]. left. exists (vs, es''). by subst.
      - move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]]. apply: Ex.
        by repeat eexists; eassumption.
    }
    case P0.
    {
      move=> [[vs es''] [E' [Cvs I]]]. left. exists (0, LH_base vs es'').
      subst. rewrite_by (k + 0 = k). by apply: LfilledBase.
    }
    move=> nE.
    (** Otherwise, we have to apply [LfilledRec]. **)
    have Dparse: forall es' : seq administrative_instruction,
        decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
    {
      clear. move=> es'.
      have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
      {
        let no := by intros; right; intros (?&?&?&?&?) in
        (case es'; first by no); case; try by no.
        move=> n l1 l2 l3. left. by exists (n, l1, l2, l3).
      }
    convert_pickable Pparse.
  }
  case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
  - move=> [[vs es''] [E1 [C Ex]]].
    destruct es'' as [| [| | | | n es1 LI | |] es2];
      try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
    clear Ex. rewrite E1.
    exfalso. subst es'.
    specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_label n es1 LI :: es2)) as H.
    specialize (lfilled_pickable_rec_gen_measure_label_r n es1 LI es2) as H'.
    lia. 
  - move=> nE'. right. move=> [n [lh I]]. inversion I; subst.
    + apply: nE. do 2 eexists. rewrite_by (k + 0 = k). repeat split; try eassumption.
      by apply: LfilledBase.
    + apply: nE'. by repeat eexists. } 


  move=> m Hm fes D0 es' E k.
  have Dcl: forall vs, decidable (const_list vs).
  { move=> vs. by apply: is_true_decidable. }
  (** First, we check whether we can set [n = 0]. **)
  have P0: pickable2 (fun vs es'' =>
                       let lh := LH_base vs es'' in
                       let es := fes k lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ lfilledInd 0 lh es es').
  {
    have: pickable3 (fun vs es es'' =>
      es' = vs ++ es ++ es'' /\ let lh := LH_base vs es'' in
      es = fes k lh /\ const_list vs /\ lfilledInd 0 lh es es').
    {
      apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
      case E': (es == fes k (LH_base vs es'')); move/eqP: E' => E'.
      - rewrite E'. repeat apply: decidable_and => //. by apply: eq_comparable.
      - right. by move=> [Ees2 [Cl I]].
    }
    case.
    - move=> [[[vs es] es''] [E1 [E2 [Cl I]]]]. left. exists (vs, es''). by subst.
    - move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]]. apply: Ex.
      by repeat eexists; eassumption.
  }
  case P0.
  {
    move=> [[vs es''] [E' [Cvs I]]]. left. exists (0, LH_base vs es'').
    subst. rewrite_by (k + 0 = k). by apply: LfilledBase.
  }
  move=> nE.
  (** Otherwise, we have to apply [LfilledRec]. **)
  have Dparse: forall es' : seq administrative_instruction,
    decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
  {
    clear. move=> es'.
    have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
    {
      let no := by intros; right; intros (?&?&?&?&?) in
      (case es'; first by no); case; try by no.
      move=> n l1 l2 l3. left. by exists (n, l1, l2, l3).
    }
    convert_pickable Pparse.
  }
  case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
  - move=> [[vs es''] [E1 [C Ex]]].
    destruct es'' as [| [| | | | n es1 LI | |] es2];
      try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
    clear Ex. rewrite E1.
    destruct m.
    { exfalso. subst es'.
      specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_label n es1 LI :: es2)) as H.
      specialize (lfilled_pickable_rec_gen_measure_label_r n es1 LI es2) as H'.
      lia. }
    have I_LI: (lfilled_pickable_rec_gen_measure LI <= m').
    {
      assert (lfilled_pickable_rec_gen_measure LI < S m); last lia.
      rewrite -E E1. 
      eapply PeanoNat.Nat.le_trans;
        last by apply lfilled_pickable_rec_gen_measure_concat_r.
      eapply lfilled_pickable_rec_gen_measure_label_r.
    }
    
    set fes' := fun k lh => fes (k + 1) (LH_rec vs n es1 lh es2).
    have D1: forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes' n0 lh') es').
    { move=> ? ? ? ?. by apply: D0. }
    specialize (IHm' (lfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[[n' lh] LF]|NP].
    - eapply LfilledRec with (vs := vs) in LF => //.
      left. exists (S n', LH_rec vs n es1 lh es2).
      move: LF. rewrite /fes'. rewrite_by (k + n' + 1 = k + S n') => /= LF. by apply: LF.
    - right. move=> [n' [lh FI]]. apply: NP. inversion FI; subst.
      + exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
        * rewrite -H. by rewrite_by (k + 0 = k).
        * by rewrite_by (k = k + 0).
      + apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
        exists k0. eexists. rewrite /fes'. rewrite_by (k + k0 + 1 = k + S k0). by apply: H4.
  - move=> nE'. right. move=> [n [lh I]]. inversion I; subst.
    + apply: nE. do 2 eexists. rewrite_by (k + 0 = k). repeat split; try eassumption.
      by apply: LfilledBase.
    + apply: nE'. by repeat eexists.
Defined.

Definition lfilled_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilled 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')).
  { move=> n lh. by split; apply lfilled_Ind_Equivalent. }
  apply: lfilledInd_pickable_rec_gen => es'' lh lh' n0.
  by apply: decidable_equiv; first by apply: lfilled_Ind_Equivalent.
Defined.

(** We can always decide [lfilled 0]. **)
Lemma lfilled_decidable_base : forall es es' lh,
  decidable (lfilled 0 lh es es').
Proof.
  move=> es es' lh. apply: (@decidable_equiv (lfilledInd 0 lh es es')).
  { by split; apply lfilled_Ind_Equivalent. }
  case lh.
  - move=> vsh esh.
    have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ vs = vsh /\ es'' = esh).
    {
      apply: list_search_split_pickable2.
      - by apply: administrative_instruction_eq_dec.
      - move=> ? ?. by repeat apply: decidable_and; apply: eq_comparable.
    }
    case.
    + move=> [[vs es''] [E [C [E1 E2]]]]. left. subst. by constructor.
    + move=> nE. right. move=> I. apply: nE. inversion I. subst. by repeat eexists.
  - move=> vs n es'' lh' es'''. right. move=> I. by inversion I.
Defined.

(** We can furthermore rebuild the stack [lh] for any [lfilled 0] predicate. **)
Lemma lfilled_pickable_base : forall es es',
  pickable (fun lh => lfilled 0 lh es es').
Proof.
  move=> es es'. apply: (@pickable_equiv _ (fun lh => lfilledInd 0 lh es es')).
  { move=> lh. by split; apply lfilled_Ind_Equivalent. }
  have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ True).
  {
    apply: list_search_split_pickable2.
    - by apply: administrative_instruction_eq_dec.
    - move=> ? ?. apply: decidable_and.
      + by apply: is_true_decidable.
      + by left.
  }
  case.
  - move=> [[vs es''] [E [C _]]]. left. eexists. subst. by constructor.
  - move=> nE. right. move=> [lh I]. apply: nE. inversion I. subst. by repeat eexists.
Defined.

Definition lfilled_pickable_rec : forall es,
  (forall es' lh, decidable (lfilled 0 lh es es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh es es').
Proof.
  move=> es D. by apply: lfilled_pickable_rec_gen.
Defined.


Section Elim.
  Context `{HHB: HandleBytes}.
  Import ssrnat.

(** The lemmas [r_eliml] and [r_elimr] are the fundamental framing lemmas.
  They enable to focus on parts of the stack, ignoring the context. **)

Lemma r_eliml: forall s f es me s' f' es' lconst,
    const_list lconst ->
    reduce s f es me s' f' es' ->
    reduce s f (lconst ++ es) me s' f' (lconst ++ es').
Proof.
  move => s f es me s' f' es' lconst HConst H0.
  apply: rm_label; try apply/lfilledP.
  - by apply: H0.
  - replace (lconst++es) with (lconst++es++[::]); first by apply: LfilledBase.
    f_equal. by apply: cats0.
  - replace (lconst++es') with (lconst++es'++[::]); first by apply: LfilledBase.
    f_equal. by apply: cats0.
Qed.

Lemma r_elimr: forall s f es me s' f' es' les,
    reduce s f es me s' f' es' ->
    reduce s f (es ++ les) me s' f' (es' ++ les).
Proof.
  move => s f es me s' f' es' les H0.
  apply: rm_label; try apply/lfilledP.
  - apply: H0.
  - replace (es++les) with ([::]++es++les) => //. by apply: LfilledBase.
  - replace (es'++les) with ([::]++es'++les) => //. by apply: LfilledBase.
Qed.

(** [r_eliml_empty] and [r_elimr_empty] are useful instantiations on empty stacks. **)

Lemma r_eliml_empty: forall s f es me s' f' lconst,
    const_list lconst ->
    reduce s f es me s' f' [::] ->
    reduce s f (lconst ++ es) me s' f' lconst.
Proof.
  move => s f es me s' f' lconst HConst H.
  assert (reduce s f (lconst++es) me s' f' (lconst++[::])); first by apply: r_eliml.
  by rewrite cats0 in H0.
Qed.

Lemma r_elimr_empty: forall s f es me s' f' les,
    reduce s f es me s' f' [::] ->
    reduce s f (es ++ les) me s' f' les.
Proof.
  move => s f es me s' f' les H.
  assert (reduce s f (es++les) me s' f' ([::] ++les)); first by apply: r_elimr.
  by rewrite cat0s in H0.
Qed.



(* A reformulation of [ety_a] that is easier to be used. *)
Lemma ety_a': forall s C es ts,
    es_is_basic es ->
    be_typing C (to_b_list es) ts ->
    e_typing s C es ts.
Proof.
  move => s C es ts HBasic HType.
  replace es with (to_e_list (to_b_list es)).
  - by apply ety_a.
  - symmetry. by apply e_b_elim.
Qed.

Lemma ety_const' v t s C :
  typeof v = t -> e_typing s C [::AI_const v] (Tf [::] [::t]).
Proof.
  intros <-. by apply ety_const.
Qed. 

(* Some quality of life lemmas *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Tf [::] t2s) ->
    e_typing s C es (Tf ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  assert (e_typing s C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  assert (be_typing C es (Tf (ts ++ t1s) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_2: forall s C es ts t1s,
    e_typing s C es (Tf t1s [::]) ->
    e_typing s C es (Tf (ts ++ t1s) ts).
Proof.
  move => s C es ts t1s HType.
  assert (e_typing s C es (Tf (ts ++ t1s) (ts ++ [::]))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_both: forall s C es ts,
    e_typing s C es (Tf [::] [::]) ->
    e_typing s C es (Tf ts ts).
Proof.
  move => s C es ts HType.
  assert (e_typing s C es (Tf (ts ++ [::]) (ts ++ [::]))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma empty_btyping: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by destruct es.
  - f_equal. by eapply IHHType.
Qed.

Lemma empty_typing: forall s C t1s t2s,
    e_typing s C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => s C t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //. by apply empty_btyping in H.
  - by destruct es.
  - f_equal. by eapply IHHType.
Qed.

(* A convenient lemma to invert e_typing back to be_typing. *)
Lemma et_to_bet: forall s C es ts,
    es_is_basic es ->
    e_typing s C es ts ->
    be_typing C (to_b_list es) ts.
Proof.
  move => s C es ts HBasic HType.
  dependent induction HType; basic_inversion.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite to_b_list_concat.
    eapply bet_composition.
    * by eapply IHHType1 => //.
    * by eapply IHHType2 => //.
  + apply bet_weakening. by eapply IHHType => //.
Qed.
End Elim.


Section composition_typing_proofs.
  Context `{HHB: HandleBytes}.
Hint Constructors be_typing : core.

(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists ts t1s t2s t3s, ?tn = ts ++ t1s /\ ?tm = ts ++ t2s /\
                                   be_typing _ [::] (Tf _ _) /\ _ =>
    try exists [::], tn, tm, tn; try eauto
  | H: _ |- _ /\ _ =>
    split => //=; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

Lemma composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C [::e] (Tf t3s t2s').
Proof.
  move => C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn; auto_prove_bet.
  + by apply bet_block.
  + by destruct es1 => //=.
  + apply concat_cancel_last in H1. destruct H1. subst.
    by exists [::], t1s0, t2s0, t2s.
  + edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H5 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //=; rewrite -catA.
Qed.


Lemma composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C es2 (Tf t3s t2s').
Proof.
  move => C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply bet_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply bet_composition; eauto.
      by apply bet_weakening.
Qed.

Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C [::e] (Tf t3s t2s').
Proof.
  move => s C es1 es2 t1s t2s HType.
  gen_ind_subst HType; extract_listn.
  - (* const *)
    repeat eexists. instantiate (1 := [::]). instantiate (1 := [::]). done.
    done. apply ety_a'. done. apply bet_empty.
    econstructor.
  - (* basic *)
    apply b_e_elim in H3. destruct H3. subst.
    rewrite to_b_list_concat in H.
    apply composition_typing in H.
    apply basic_concat in H1. destruct H1.
    destruct H as [ts' [t1s' [t2s' [t3s' [H2 [H3 [H4 H5]]]]]]]. subst.
    exists ts', t1s', t2s', t3s'.
    by repeat split => //=; apply ety_a' => //=.
  - (* composition *)
    apply concat_cancel_last in H2. destruct H2. subst.
    by exists [::], t1s0, t2s0, t2s.
  - (* weakening *)
    edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //; rewrite catA.
  - (* Trap *)
    exists [::], t1s, t2s, t1s.
    repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_trap.
  - (* Local *)
    exists [::], [::], t2s, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by apply ety_local.
  - (* Invoke *)
    exists [::], t1s, t2s, t1s. repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by eapply ety_invoke; eauto.
  - (* Label *)
    exists [::], [::], t2s0, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_label; eauto.
  - (* Call host *)
    exists [::], [::], t2s0, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_call_host ; eauto.
Qed.

Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C es2 (Tf t3s t2s').
Proof.
  move => s C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply ety_a' => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply e_composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply ety_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply ety_composition; eauto.
      by apply ety_weakening.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply empty_btyping in HType2. by subst.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply bet_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply bet_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply bet_weakening.
Qed.

Lemma bet_composition_front: forall C e es t1s t2s t3s,
    be_typing C [::e] (Tf t1s t2s) ->
    be_typing C es (Tf t2s t3s) ->
    be_typing C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply bet_composition'; eauto.
Qed.

Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Tf t1s t2s) ->
    e_typing s C es2 (Tf t2s t3s) ->
    e_typing s C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => s C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply et_to_bet in HType2. apply empty_btyping in HType2. by subst.
  - by [].
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply e_composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply ety_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply ety_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply ety_weakening.
Qed.

Lemma et_composition_front: forall s C e es t1s t2s t3s,
    e_typing s C [::e] (Tf t1s t2s) ->
    e_typing s C es (Tf t2s t3s) ->
    e_typing s C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply et_composition'; eauto.
Qed.

End composition_typing_proofs.

Lemma cat_cons_not_nil : forall T (xs : list T) y ys,
  xs ++ (y :: ys) <> [::].
Proof. move => T xs y ys E. by move: (List.app_eq_nil _ _ E) => [? ?]. Qed.

Section nil_proofs.
  Import ssrnat.
  Context `{HHB : HandleBytes}.

Lemma not_reduce_simple_nil : forall es', ~ reduce_simple [::] es'.
Proof.
  assert (forall es es', reduce_simple es es' -> es = [::] -> False) as H.
  { move => es es' H.
    elim: {es es'} H => //=.
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      apply: cat_cons_not_nil. exact H. }
    { move => vs es _ _ t1s t2s _ _ _ _ H.
      apply: cat_cons_not_nil. exact H. }
    { move => es lh _ H Hes.
      rewrite Hes {es Hes} /lfilled /operations.lfilled /= in H.
      case: lh H => //=.
      { move => es es2.
        case_eq (const_list es) => //=.
        move=> _ /eqP H.
        symmetry in H.
        by move: (List.app_eq_nil _ _ H) => [? ?]. } } }
  { move => es' H2.
    apply: H. exact H2. done. }
Qed.


Lemma lfill_cons_not_Some_nil : forall i lh es es' e es0,
  lfill i lh es = es' -> es = e :: es0 -> es' <> Some [::].
Proof.
  elim.
  { elim; last by intros; subst.
    move=> l l0 es es' /=.
    case: (const_list l).
    { move => Hfill H1 H2 H3 H4.
      rewrite H4 in H2.
      injection H2 => H5 {H2}.
      rewrite H3 in H5.
      apply: cat_cons_not_nil.
      exact H5.
       }
    { intros; subst; discriminate. } }
  { move=> n IH.
    elim; first by intros; subst.
    intros.
    rewrite /= in H0.
    move: H0.
    case: (const_list l).
    { rewrite H1 {H1}.
      case_eq (lfill n l1 (e :: es0)).
      { move=> l3 H1 H2 H3.
        rewrite H3 in H2.
        injection H2.
        move=> {} H2.
        apply: cat_cons_not_nil.
        exact H2. }
      { intros; subst; discriminate. } }
    { intros; subst; discriminate. } }
Qed.

Lemma lfilled_not_nil : forall i lh es es', lfilled i lh es es' -> es <> [::] -> es' <> [::].
Proof.
  move => i lh es es' H Hes Hes'.
  move: (List.exists_last Hes) => [e [e0 H']].
  rewrite H' in H.
  move: H.
  rewrite /lfilled /operations.lfilled.
  case_eq (operations.lfill i lh es).
  { intros; subst.
    rewrite H in H0.
    assert ([::] = l) as H0'.
    { apply/eqP.
      apply H0. }
    { rewrite H0' in H.
      rewrite /= in H.
      case E: (e ++ (e0 :: l)%SEQ)%list; first by move: (List.app_eq_nil _ _ E) => [? ?].
      apply: lfill_cons_not_Some_nil.
      apply: H.
      apply: E.
      by rewrite H0'. } }
  { intros; subst.
    rewrite H in H0.
    done. }
Qed.

Lemma reduce_not_nil : forall σ1 f es me σ2 f' es',
  reduce σ1 f es me σ2 f' es' -> es <> [::].
Proof.
  move => σ1 f es me σ2 f' es' Hred.
  elim: {σ1 f es me f' σ2} Hred => //.
  move => σ1 f es σ2 f' es2 Hred.
  elim: {σ1 f es f' σ2} Hred => //;
    try solve [ repeat intro;
                match goal with
                | H : (_ ++ _)%SEQ = [::] |- _ =>
                  by move: (app_eq_nil _ _ H) => [? ?]
                end ].
  { move => e e' _ _ Hreds He.
    rewrite He in Hreds.
    apply: not_reduce_simple_nil.
    apply: Hreds. }
  { intros. destruct ves => //. }
  { intros. destruct ves => //. }
  { intros. apply: lfilled_not_nil. exact H1. exact H0. }
Qed.

End nil_proofs.



Lemma same_length_is_Sound T T' A :
  seg_length T = seg_length T' ->
  isSound T A -> isSound T' A.
Proof.
  intros Hlen HS.
  unfold isSound.
  destruct HS as [Haux H].
  split => //.
  intros a b c Ha.
  rewrite - Hlen.
  by apply Haux.
Qed.



Lemma size_tagged_bytes_takefill a l b :
  size (tagged_bytes_takefill a l b) = l.
Proof.
  generalize dependent b. induction l => //=.
  intro b; destruct b => //=.
  by rewrite IHl.
  by rewrite IHl.
Qed.

Section using_ssrnat.
  Import ssrnat.

Lemma segstore_is_None_aux_aux addr c' k:
   List.fold_left
    (fun '(k0, acc) (x : byte * btag) =>
     ((k0 + 1)%coq_nat,
     match acc with
     | Some dat => seg_update (addr + N.of_nat k0) x dat
     | None => None
     end)) c' (k, None) = (k + length c', None).
Proof.
  generalize dependent k. induction c' => //=.
  intro k. induction k => //=. inversion IHk. rewrite <- H0 at 2. done.
  intro k. rewrite IHc'. clear. induction k => //=.
  inversion IHk. rewrite addSn H0. done.
Qed.


Lemma segstore_is_None_aux a a' addr c c' k k':
  length c = length c' ->
  length a.(segl_data) = length a'.(segl_data) ->
List.fold_left
        (fun '(k, acc) (x : byte * btag) =>
         ((k + 1)%coq_nat,
         match acc with
         | Some dat => seg_update (addr + N.of_nat k) x dat
         | None => None
         end)) c (k, Some a)
= (k', None) -> 
  List.fold_left
        (fun '(k, acc) (x : byte * btag) =>
         ((k + 1)%coq_nat,
         match acc with
         | Some dat => seg_update (addr + N.of_nat k) x dat
         | None => None
         end)) c' (k, Some a') = (k', None).
Proof.
  generalize dependent a. generalize dependent a'.
  generalize dependent k. generalize dependent k'.
  generalize dependent c'. induction c => //=.
  destruct c' => //=.
  intros k' k a' a0 Hlen Hlena. 
  unfold seg_update at 2 4.
  rewrite Hlena. destruct (N.ltb _ _) => //.
  - intro H. erewrite IHc. done. by inversion Hlen. 2: exact H.
    simpl. do 2 rewrite length_is_size size_cat => //=.
    repeat rewrite - length_is_size.
    rewrite List.firstn_length.
    rewrite List.firstn_length.
    do 2 rewrite List.skipn_length. 
    repeat rewrite Hlena. done. 
  - do 2 rewrite segstore_is_None_aux_aux. by inversion Hlen.
Qed. 


Lemma segstore_is_None a b c c' d :
  segstore a b c d = None -> segstore a b c' d = None.
Proof.
  unfold segstore. destruct (N.leb _ _) => //.
  unfold write_segbytes. unfold fold_lefti.
  destruct (List.fold_left _ _ _) eqn:Hfl => //.
  destruct o => //. erewrite segstore_is_None_aux. done. 3: exact Hfl.
  do 2 rewrite length_is_size size_tagged_bytes_takefill. done. done.
Qed. 


 Lemma segstore_same_length_aux:
  forall l addr s s' k k',
    BinNat.N.leb (BinNat.N.add addr (BinNat.N.of_nat (k + length l))) (seg_length s) = true ->        
      List.fold_left
        (fun '(off, dat_o) (b : byte * btag) =>
        (off + 1, match dat_o with
           | Some dat =>
               seg_update
                 (BinNatDef.N.add addr (BinNat.N.of_nat off))
                 b dat
           | None => None
       end)) l (k, Some s) = (k', Some s') ->
  seg_length s = seg_length s'.
Proof.
  intro l; induction l => //=.
  intros h s s' k k' Hlen H.
  by inversion H.
  intros h s s' k k' Hlen H.
  unfold seg_update in H at 2.
  replace (BinNat.N.ltb
             (BinNatDef.N.add h (BinNat.N.of_nat k))
             (BinNat.N.of_nat (length (segl_data s)))) with true in H.
  apply IHl in H.
  rewrite - H.
  unfold seg_length => /=.
  rewrite List.app_length => /=.
  rewrite List.firstn_length_le.
  rewrite List.skipn_length.
  remember (BinNat.N.to_nat (BinNatDef.N.add h (BinNat.N.of_nat k))) as x.
  replace (x + 1)%coq_nat with x.+1; last lias. 
  rewrite subnSK.
  replace (Nat.add x (subn (length (segl_data s)) x)) with
    (addn x (subn (length (segl_data s)) x)); last lias.
  rewrite subnKC. 
  done. subst.
  unfold seg_length in Hlen. 
  apply BinNat.N.leb_le in Hlen. lias.
  unfold seg_length in Hlen. 
  apply BinNat.N.leb_le in Hlen. lias.
  unfold seg_length in Hlen. 
  apply BinNat.N.leb_le in Hlen. lias.
  unfold seg_length => /=. 
  rewrite List.app_length => /=.
  rewrite List.firstn_length_le. rewrite List.skipn_length.
  remember (BinNat.N.to_nat (BinNatDef.N.add h (BinNat.N.of_nat k))) as x.
  replace (x + 1)%coq_nat with x.+1; last lias.
  rewrite subnSK.
    replace (Nat.add x (subn (length (segl_data s)) x)) with
    (addn x (subn (length (segl_data s)) x)); last lias.
  rewrite subnKC.
  unfold seg_length in Hlen. 
  apply BinNat.N.leb_le in Hlen. apply BinNat.N.leb_le. lias.
  unfold seg_length in Hlen. 
  apply BinNat.N.leb_le in Hlen. lias.
  unfold seg_length in Hlen. 
  apply BinNat.N.leb_le in Hlen. lias.
  unfold seg_length in Hlen. 
  apply BinNat.N.leb_le in Hlen. lias.
  apply Logic.eq_sym, BinNat.N.ltb_lt.
  apply BinNat.N.leb_le in Hlen.
  unfold seg_length in Hlen. lias.
Qed. 




Lemma segstore_same_length s h l i s' :
  segstore s h l i = Some s' -> operations.seg_length s = operations.seg_length s'.
Proof.
  unfold segstore.
  destruct (_ <=? _)%num eqn:Hlen' => //.
  unfold write_segbytes.
  unfold fold_lefti.
  destruct (List.fold_left _ _ _) eqn:Hfl.
  destruct o => //.
  apply segstore_same_length_aux in Hfl.
  intro H; inversion H; subst.
  unfold operations.seg_length.
  rewrite Hfl.
  done.
  rewrite length_is_size size_tagged_bytes_takefill.
  replace (0 + i) with i; last lias.
  assumption.
Qed.


Lemma nth_error_update_other {A} l i {x:A} j:
  i <> j ->
  j < length l -> 
  List.nth_error (update_list_at l i x) j = List.nth_error l j.
Proof.
  intros Hij Hj.
  generalize dependent l. generalize dependent i.
  induction j => //=; intros.
  destruct l => //=.
  destruct i => //=.
  destruct l => //=.
  destruct i => //=.
  unfold update_list_at in IHj. simpl in IHj.
  apply IHj. lias. simpl in Hj. lias.
Qed.
 
End using_ssrnat.
Section using_gmap.
  Import gmap.

    Set Bullet Behavior "Strict Subproofs".

    Lemma compatible_delete x y x' A :
      compatible x y A -> compatible x y (<[ x' := None ]> A).
    Proof.
      intros H x0 y0 s0 H0.
      destruct (x0 =? x')%N eqn:Hx.
      - apply N.eqb_eq in Hx as ->. rewrite lookup_insert in H0 => //.
      - apply N.eqb_neq in Hx. rewrite lookup_insert_ne in H0 => //.
        by apply H in H0.
    Qed. 
  
Lemma salloc_sound T A a n nid T' A' :
  isSound T.(seg_data) A -> salloc T A a n nid T' A' -> isSound T'.(seg_data) A'.
Proof.
  intros HSound Halloc.
  inversion Halloc; subst; clear Halloc.
  unfold isSound => /=.
  destruct HSound as [Haux Hfree].
  split.
  - intros nid' b c Hnid.
    destruct (nid =? nid')%N eqn:Hnid'.
    + apply N.eqb_eq in Hnid' as ->.
      rewrite lookup_insert in Hnid.
      inversion Hnid; subst; clear Hnid. 
      split.
      * unfold seg_length => /=.
        repeat rewrite List.app_length.
        rewrite List.firstn_length_le; last lias.
        rewrite List.repeat_length.
        rewrite List.skipn_length.
        repeat rewrite Nnat.Nat2N.inj_add.
        rewrite Nnat.Nat2N.inj_sub.
        repeat rewrite Nnat.N2Nat.id.
        lia.
      * rewrite insert_insert. by apply compatible_delete. 
    + apply N.eqb_neq in Hnid'.
      rewrite lookup_insert_ne in Hnid => //.
      specialize (Haux _ _ _ Hnid) as [??].
      split.
      * unfold seg_length => /=.
        repeat rewrite List.app_length.
        rewrite List.firstn_length_le; last lias.
        rewrite List.repeat_length.
        rewrite List.skipn_length.
        repeat rewrite Nnat.Nat2N.inj_add.
        rewrite Nnat.Nat2N.inj_sub.
        repeat rewrite Nnat.N2Nat.id.
        unfold seg_length in H4. lia.
      * rewrite insert_commute => //.
        intros x y z Hx.
        destruct (x =? nid)%N eqn:Hxnid.
        apply N.eqb_eq in Hxnid as ->.
        rewrite lookup_insert in Hx.
        inversion Hx; subst; clear Hx.
        apply H3 in Hnid as [?|?]; lia.
        apply N.eqb_neq in Hxnid.
        rewrite lookup_insert_ne in Hx => //.
        apply H5 in Hx. done.
  - intros k Hk.
    destruct (k =? nid)%N eqn:Hknid.
    + apply N.eqb_eq in Hknid as ->.
      lia.
    + apply N.eqb_neq in Hknid.
      unfold canBeAlloc.
      rewrite lookup_insert_ne => //.
      apply Hfree. lia.
Qed. 


Lemma sfree_sound T A a n nid T' A' :
  isSound T.(seg_data) A -> sfree T A a n nid T' A' -> isSound T'.(seg_data) A'.
Proof.
  intros HSound Hfree.
  inversion Hfree; subst; clear Hfree.
  split.
  { eapply find_and_remove_isSound => //.
    by destruct HSound. } 
  simpl. destruct HSound.
  intros k Hk.
  apply H1 in Hk.
  unfold find_and_remove in H.
  destruct (allocated A !! nid) eqn:Hid => //.
  destruct o as [[??]|] => //.
  inversion H; subst.
  destruct (k =? nid)%N eqn:Hknid.
  apply N.eqb_eq in Hknid as ->.
  unfold canBeAlloc in Hk. by rewrite Hid in Hk. 
  
  apply N.eqb_neq in Hknid.
  unfold canBeAlloc. rewrite lookup_insert_ne => //.
Qed.

End using_gmap.

Lemma salloc_sound_local T A a n nid T' A' A0 :
  isSound T.(seg_data) A0 -> salloc T A a n nid T' A' -> isSound T'.(seg_data) A0.
Proof.
  intros HSound Halloc.
  inversion Halloc; subst; clear Halloc.
  destruct HSound as [Haux Hfree].
  split => //=.
  intros nid' b c Hnid'.
  apply Haux in Hnid' as [??].
  split => //.
  unfold seg_length.
  repeat rewrite List.app_length.
  rewrite List.firstn_length_le.
  rewrite List.repeat_length.
  rewrite List.skipn_length.
  unfold seg_length in H4.
  repeat rewrite Nnat.Nat2N.inj_add.
  rewrite Nnat.Nat2N.inj_sub.
  repeat rewrite Nnat.N2Nat.id. 
  lia. lias.
Qed.

Lemma sfree_sound_local T A a n nid T' A' A0 :
  isSound T.(seg_data) A0 -> sfree T A a n nid T' A' -> isSound T'.(seg_data) A0.
Proof.
  intros HSound Hfree.
  inversion Hfree; subst.
  done.
Qed.



Lemma segstore_sound T A h bts len T':
  isSound T.(seg_data) A ->
  segstore T h bts len = Some T' ->
  isSound T'.(seg_data) A.
Proof.
  intros HSound HStore.
  eapply same_length_is_Sound; last exact HSound.
  eapply segstore_same_length.
  exact HStore.
Qed.
  






Definition current_local_instance es :=
  match es with
  | AI_local n f es' :: q => Some f.(f_inst)
  | _ => None
  end.


Definition wellFormedState s :=
  isSound s.(s_segs).(seg_data) s.(s_alls).



Section reduce_wellformed_proof.
  Context `{HHB : HandleBytes}.

Lemma reduce_preserves_wellformedness s f es me s' f' es':
  wellFormedState s ->
  reduce s f es me s' f' es' ->
  wellFormedState s'.
Proof.
  intros HWF Hred.
  induction Hred => //.
  { inversion H; try by subst.
    subst.
    assert (s_alls s' = s_alls s /\ s_segs s' = s_segs s) as [Halls Hsegs].
    destruct s; simpl.
    unfold supdate_glob in H0.
    unfold option_bind in H0.
    destruct (sglob_ind _ _ _) => //.
    unfold supdate_glob_s in H0.
    simpl in H0.
    unfold option_map in H0.
    destruct (List.nth_error _ n) => //.
    by inversion H0.
    unfold wellFormedState. rewrite Halls Hsegs.
    exact HWF. }
  { unfold wellFormedState.
    destruct s => //=.
    eapply same_length_is_Sound; last exact HWF.
    apply segstore_same_length in H6.
    by subst. }
  { eapply same_length_is_Sound; last exact HWF.
    apply segstore_same_length in H7.
    by subst. }
  { eapply salloc_sound.
    exact HWF. subst. exact H2. }
  { eapply sfree_sound.
    exact HWF. subst. exact H1. }
  by apply IHHred.
  by apply IHHred.
Qed.

End reduce_wellformed_proof.

Section handle_size_non_zero.

  Context `{ HHB: HandleBytes }.
  Lemma hsnz: gt (ssrnat.nat_of_bin (@handle_size HHB)) O.
  Proof.
    destruct HHB. simpl.
    destruct (PeanoNat.Nat.eq_0_gt_0_cases (ssrnat.nat_of_bin handle_size)) as [Htv|] => //.
    assert (ssrnat.leq 1 (ssrnat.nat_of_bin handle_size)) => //.
    rewrite Htv in H. lias.
  Qed.
End handle_size_non_zero.


Section arithmetics.

  Lemma mul_le a b c : a <= b -> c * a <= c * b.
  Proof.
    intros Hab.
    induction c; lia.
  Qed.

  Lemma mul_lt a b c : a < b -> c * a + c <= c * b.
    intros Hab.
    assert (S a <= b); first lia.
    replace (c * a + c) with (c * S a); last lia.
    apply mul_le. done.
  Qed.

Lemma div_leq a b c: a <= b -> PeanoNat.Nat.div a c <= PeanoNat.Nat.div b c.
Proof.
  intros.
  unfold Nat.div.
  destruct c => //.
  specialize (PeanoNat.Nat.divmod_spec a c 0 c (PeanoNat.Nat.le_refl c)) as Ha.
  specialize (PeanoNat.Nat.divmod_spec b c 0 c (PeanoNat.Nat.le_refl c)) as Hb.
  destruct (Nat.divmod a c 0 c).
  destruct (Nat.divmod b c 0 c).
  simpl.
  destruct Ha as [Ha Hra].
  destruct Hb as [Hb Hrb].
  rewrite PeanoNat.Nat.sub_diag in Ha, Hb.
  rewrite PeanoNat.Nat.mul_0_r in Ha, Hb.
  repeat rewrite PeanoNat.Nat.add_0_r in Ha, Hb.
  remember (c - n0) as ra.
  clear Hra.
  assert (ra < S c) as Hra; first lia.
  clear Heqra.
  remember (c - n2) as rb.
  clear Hrb.
  assert (rb < S c) as Hrb; first lia.
  clear Heqrb.
  remember (S c) as d. assert (d > 0) as Hd; first lia. clear Heqd.
  destruct (PeanoNat.Nat.leb n n1) eqn:Hn; first by apply PeanoNat.Nat.leb_le in Hn.
  apply PeanoNat.Nat.leb_gt in Hn.
  assert (d * n1 + d <= d * n); first by apply mul_lt.
  lia.
Qed. 

End arithmetics.

