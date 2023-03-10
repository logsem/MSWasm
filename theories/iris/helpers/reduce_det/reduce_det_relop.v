From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma relop_det v1 v2 op t s f me s' f' es:
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))] me s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)].
Proof.
  move => Hred.
  by only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_relop t op)] Hred.
Qed.
