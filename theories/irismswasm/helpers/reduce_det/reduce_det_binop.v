From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From MSWasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.
From MSWasm Require Import operations opsem.


Section reduce_det_binop.
  Context `{ HHB : HandleBytes }.


Lemma binop_det v1 v2 v op t s f me s' f' es:
  app_binop op v1 v2 = Some v ->
  reduce s f [AI_const v1; AI_const v2; AI_basic (BI_binop t op)] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_const v] me s' f' es [AI_const v1; AI_const v2; AI_basic (BI_binop t op)].
Proof.
  move => H Hred.
    (* an example where we the user need to provide some extra work because [ only_one ]
         couldn't exfalso away every possibility : here, knowing that Hred2 is
         hypothesis [ [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; 
         AI_basic (BI_binop t op)] -> es2 ], the tactic leaves us with two (not one)
         possibilities : Hred2 holds either using rs_binop_success or rs_binop_failure.
         It is up to us to exfalso away the second case using the rest of the
         hypotheses *)

  by only_one [AI_const v1 ; AI_const v2 ; AI_basic (BI_binop t op)] Hred ; 
  destruct v1, v2, v3, v0; inversion Heqes ; subst => // ; rewrite H in H0 ; inversion H0 ; subst.
Qed.

Lemma binop_none_det v1 v2 op t s f me s' f' es:
  app_binop op v1 v2 = None ->
  reduce s f [AI_const v1; AI_const v2; AI_basic (BI_binop t op)] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_trap] me s' f' es [AI_const v1; AI_const v2; AI_basic (BI_binop t op)].
Proof.
  move => H Hred.
  by only_one [AI_const v1 ; AI_const v2 ; AI_basic (BI_binop t op)] Hred ;
  destruct v1, v2, v3, v0; inversion Heqes ; subst => //; rewrite H in H0 ; inversion H0 ; subst.
Qed.


End reduce_det_binop.

