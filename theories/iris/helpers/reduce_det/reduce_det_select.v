From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.

Lemma select_false_det v1 v2 n s f me s' f' es:
  n = Wasm_int.int_zero i32m ->
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_basic (BI_const v2)] me s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select].
Proof.
  move => H Hred.
  only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2);
            AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] Hred ;
    [done | by inversion Heqes ; subst ].
Qed.

Lemma select_true_det v1 v2 n s f me s' f' es:
  n <> Wasm_int.int_zero i32m ->
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_basic (BI_const v1)] me s' f' es [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select].
Proof.
  move => H Hred.
  only_one [AI_basic (BI_const v1) ; AI_basic (BI_const v2);
            AI_basic (BI_const (VAL_int32 n)) ; AI_basic BI_select] Hred ;
    [ by inversion Heqes ; subst | done ].
Qed.
