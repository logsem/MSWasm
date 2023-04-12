From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations iris_properties.
Require Export datatypes operations properties opsem.

Section atomicity.
  Context `{HHB : HandleBytes}.

Local Definition reducible := @reducible wasm_lang.

Local Definition expr := iris.expr.
Local Definition val := iris.val.
Local Definition to_val := iris.to_val.


(* The following atomicity definition will be useful for opening invariants *)
Definition is_atomic (e : expr) : Prop :=
  match e with
  | [::AI_basic (BI_const (VAL_int32 _)); AI_basic (BI_load _ _ _ _)] => True
  | [::AI_basic (BI_const (VAL_handle _)); AI_basic (BI_segload _)] => True
  | [::AI_basic (BI_const (VAL_int32 _)); AI_basic (BI_const _); AI_basic (BI_store _ _ _ _)] => True
  | [::AI_basic (BI_const (VAL_handle _)); AI_basic (BI_const _); AI_basic (BI_segstore _)] => True
  | [::AI_basic (BI_const _); AI_basic (BI_set_global _)] => True
  | [::AI_basic (BI_get_global _)] => True
  | [::AI_trap] => True
  | _ => False
  end.

Ltac destruct_match_goal :=
  let x := fresh "x" in 
  match goal with
                | _ : _ |- (match ?x with | _ => _ end -> _) => case: x => x //=
  end.
Lemma is_atomic_eq (e : expr) :
  is_atomic e ->
  (∃ k x1 x2 x3 x4, e = [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load x1 x2 x3 x4)]) ∨
      (∃ k x1, e = [::AI_basic (BI_const (VAL_handle k)); AI_basic (BI_segload x1)]) ∨
    (∃ k v x1 x2 x3 x4, e = [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store x1 x2 x3 x4)]) ∨
      (∃ k v x1, e = [::AI_basic (BI_const (VAL_handle k)); AI_basic (BI_const v); AI_basic (BI_segstore x1)]) ∨
  (∃ v g, e = [::AI_basic (BI_const v); AI_basic (BI_set_global g)]) ∨
  (∃ g, e = [::AI_basic (BI_get_global g)]) ∨
  (e = [::AI_trap]).
Proof.
  intros He.
  do 2 (destruct e;try done).
  { destruct a;try done.
    destruct b;try done. right. right. right. right. right. eauto.
    destruct v;try done.
    right. right. right. right. right. by right. }
  do 1 (destruct e;try done).
  { revert He. cbn. repeat destruct_match_goal.
    all: try by (move => *; right; right; right; right; left; repeat eexists).
    move => *. left. repeat eexists. move => *. right; left. repeat eexists. } 
  { destruct e.
    2: { exfalso. cbn in He. revert He.
         repeat destruct_match_goal. }
    revert He. cbn. repeat destruct_match_goal.
    move => *. right; right; left. repeat eexists. right; right; right; left.
    repeat eexists. }
Qed.

Lemma atomic_no_hole_load s0 f es me s' f' es' k lh k0 x0 x1 x2 x3 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_load x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.  
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_load_false;eauto. }
Qed.

Lemma atomic_no_hole_segload s0 f es me s' f' es' k lh k0 x0:
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_handle k0)); AI_basic (BI_segload x0)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.  
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_segload_false;eauto. }
Qed.
    
Lemma atomic_no_hole_store s0 f es me s' f' es' k lh k0 v x0 x1 x2 x3 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_const v); AI_basic (BI_store x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_store_false_2;eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_store_false;eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
Qed.


Lemma atomic_no_hole_segstore s0 f es me s' f' es' k lh k0 v x0 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_handle k0)); AI_basic (BI_const v); AI_basic (BI_segstore x0 )] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_segstore_false_2;eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_segstore_false;eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
Qed.

Lemma atomic_no_hole_trap s0 f es me s' f' es' k lh :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_trap] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
Qed.

Lemma reduce_set_global_false s0 f me s' f' es es' g :
  es = [AI_basic (BI_set_global g)] ->
  reduce s0 f es me s' f' es' -> False.
Proof.
  intros Heq Hred.
  apply Logic.eq_sym in Heq.
  no_reduce Heq Hred.
Qed.

Lemma atomic_no_hole_set_global s0 f es me s' f' es' k lh v g :
  reduce s0 f es me s' f' es' ->
  lfilled k lh es [::AI_basic (BI_const v); AI_basic (BI_set_global g)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_set_global_false;eauto. }
Qed.

Lemma atomic_no_hole_get_global s0 f es me s' f' es' k lh g:
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_get_global g)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
Qed.
  

Global Instance is_atomic_correct s e : is_atomic e → @Atomic wasm_lang s e.
Proof.
  intros Ha; apply strongly_atomic_atomic.
  move => σ e' K σ' e'' /= Hstep.
  unfold iris.prim_step in Hstep.
  destruct σ as [[[hs ws] locs] inst].
  destruct σ' as [[[hs' ws'] locs'] inst'].
  destruct K => //. destruct K => //.
  destruct Hstep as [Hstep ->].
  induction Hstep. (* using reduce_ind. *)
  destruct H.
  all: apply is_atomic_eq in Ha as Heq.
  all: destruct Heq as [(?&?&?&?&?&?)|[(?&?&?)|[(?&?&?&?&?&?&?)|[(?&?&?&?)|[(?&?&?)|[(?&?)|?]]]]]];simplify_eq; eauto.
  all: try by (do 2 (destruct vcs;try done)).
  all: try by (do 3 (destruct vcs;try done)).
  { inversion H;subst;eauto.
    1,2: do 3 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 3 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). }
    { inversion H;subst;eauto.
      1,2: do 4 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). }
  { inversion H;simpl;eauto; subst; exfalso.
    - do 2 (destruct vs;inversion H0;try done).
    - do 2 (destruct vs;inversion H0;try done). }
  { eapply atomic_no_hole_load in Hstep as HH;eauto. destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { eapply atomic_no_hole_segload in Hstep as HH;eauto. destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_store as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_segstore as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_set_global as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_get_global as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }  
  { edestruct atomic_no_hole_trap as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
Qed.

End atomicity. 

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.



Global Hint Extern 0 (Atomic _ _) => solve_atomic : core.
Global Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.


