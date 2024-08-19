From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From MSWasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.
From MSWasm Require Import operations opsem.


Section reduce_det_testop.
  Context `{ HHB: HandleBytes }.

Lemma testop_i32_det c s f me s' f' es testop:
  reduce s f [AI_const (VAL_int32 c); AI_basic (BI_testop T_i32 testop)] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i32t) testop c)))]
    me s' f' es [AI_const (VAL_int32 c); AI_basic (BI_testop T_i32 testop)].
Proof.
  move => Hred.
  by only_one [AI_const (VAL_int32 c) ; AI_basic (BI_testop T_i32 testop)] Hred.
Qed.

Lemma testop_i64_det c s f me s' f' es testop:
  reduce s f [AI_const (VAL_int64 c); AI_basic (BI_testop T_i64 testop)] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i64t) testop c)))]
    me s' f' es [AI_const (VAL_int64 c); AI_basic (BI_testop T_i64 testop)].
Proof.
  move => Hred.
  by only_one [AI_const (VAL_int64 c) ; AI_basic (BI_testop T_i64 testop)] Hred.
Qed.

End reduce_det_testop.
      
