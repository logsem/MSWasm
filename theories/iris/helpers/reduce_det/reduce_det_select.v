From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_det_prelude.


Section reduce_det_select.
  Context `{ HHB: HandleBytes }.

Lemma select_false_det v1 v2 n s f me s' f' es:
  n = Wasm_int.int_zero i32m ->
  reduce s f [AI_const v1; AI_const v2; AI_const (VAL_int32 n); AI_basic BI_select] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_const v2] me s' f' es [AI_const v1; AI_const v2; AI_const (VAL_int32 n); AI_basic BI_select].
Proof.
  move => H Hred.
  only_one [AI_const v1 ; AI_const v2;
            AI_const (VAL_int32 n) ; AI_basic BI_select] Hred. 
Qed.

Lemma select_true_det v1 v2 n s f me s' f' es:
  n <> Wasm_int.int_zero i32m ->
  reduce s f [AI_const v1; AI_const v2; AI_const (VAL_int32 n); AI_basic BI_select] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_const v1] me s' f' es [AI_const v1; AI_const v2; AI_const (VAL_int32 n); AI_basic BI_select].
Proof.
  move => H Hred.
  only_one [AI_const v1 ; AI_const v2;
            AI_const (VAL_int32 n) ; AI_basic BI_select] Hred. 
Qed.

End reduce_det_select.
