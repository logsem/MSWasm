From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From MSWasm.iris.examples.segstack Require Export segstack_common.
From MSWasm.iris.logrel Require Import iris_fundamental.
From MSWasm.iris.rules Require Import proofmode iris_rules.
From MSWasm.iris.language Require Import iris_wp_def.
From MSWasm.iris.helpers.prelude Require Import iris_reduce_properties.
From MSWasm Require Import opsem stdpp_aux common.

Close Scope byte_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section stack.

 Context `{!wasmG Σ, HHB: HandleBytes}. 


Section code.

(*
  is_full: [i32] -> [i32]
  locals declared: []

  Given a stack pointer, determine if the stack is full.

  Implemented by reading the stack top pointer address and taking remainder against 65536. In the case of a full stack,
  the stack top pointer will be pointing to (starting address + 65532), resulting in the remainder being 65532.
  Performs an input validation check prior to execution. Can trap only if validation fails.

  Returns 1 if the stack is full, 0 otherwise.

  Parameters/Locals:
  0 (input)     stack pointer
*)
                 
Definition is_full := 
  [
    i32const 65531 ;
    BI_get_local 0 ;
    BI_segload T_i32;
    BI_relop T_i32 (Relop_i (ROI_lt SX_U)) 
  ].


End code.

Section specs.

Lemma spec_is_full f0 (v : handle) (s : seq.seq i32) E: 
  ⊢ {{{
        ⌜ (f_locs f0) !! 0 = Some (value_of_handle v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s }}}
    to_e_list is_full @ E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s ∗
                           ⌜ (k = 1) /\ (N.of_nat (length s) = (two14 - 1)%N)%N \/ (k = 0) /\ (N.of_nat (length s) < two14 - 1)%N ⌝ ∗
          ↪[frame] f0 }}}.
Proof.
  iIntros "!>" (Φ) "(%Hlocv & Hf & Hstack) HΦ" => /=.
  
  iDestruct (stack_pure with "Hstack") as "(%Hoff & %Hbound & %Hvalid & %Hstack)".
  
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int _ ; value_of_handle v
                                      ] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply wp_get_local => //.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate ( 1 := λ x, ((⌜ x = immV [value_of_int _ ; value_of_int (length s * 4)] ⌝
                                          ∗ ↪[frame] f0 ∗ isStack v s)%I)).
    iSplitR ; first by iIntros "(%Habs & _)".
    iSplitL "Hf Hstack".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> (%Habs & _)".
    iApply wp_wand_r.
    iSplitL.
    iApply (wp_segload with "[Hf Hstack]"); last first.
    iDestruct "Hstack" as "(_ & _ & _ & _ & Hid & Hbase & Hstack & Hrest)".
    iFrame. iSplitR "Hbase".
    instantiate (2 := λ v, (⌜ v = immV _ ⌝ ∗ _)%I).
    iIntros "!> H". 
    iSplit; first done. iCombine "Hstack Hrest H" as "H". iExact "H". 
    iApply i32_wss. unfold handle_addr; rewrite Hoff N.add_0_r. done.
    by rewrite Hoff Hbound. done. rewrite map_fst_map_pair.
    instantiate (1 := VAL_int32 _). done. done. done.
    
  - iIntros (w) "((-> & Hstack & Hrest & Hid & Hbase) & Hf)" => /=.
    iFrame. iSplit; last first. repeat iSplit => //.
    iApply i32_wss. unfold handle_addr; rewrite Hoff N.add_0_r. done.
    iPureIntro. unfold value_of_int => /=.
    assert (Z.of_N (N.of_nat (length s) * 4) = length s * 4)%Z.
    lia. rewrite H. done.
      
  - iIntros (w) "(-> & Hf & Hstack)" => /=.
    iApply wp_wand_r. iSplitL "Hf".
    fold_const; iApply (wp_relop with "Hf") => //.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  - iIntros (w) "[-> Hf]".
    iSimpl.
    iApply "HΦ".
    destruct (N.of_nat (length s) <? two14 - 1)%N eqn:Hfull.
    { iExists 0. 
      iSplit => //=.
      iPureIntro. unfold Wasm_int.Int32.ltu.
      rewrite wasm_int_unsigned; last lia.
      rewrite wasm_int_unsigned; last first.
      split; first lia. unfold two14 in Hstack.
      remember (length s) as x. rewrite - Heqx. lia.
      apply N.ltb_lt in Hfull.
      rewrite Coqlib.zlt_false => //. 
      unfold two14 in Hfull.
      remember (length s) as x. rewrite - Heqx. lia.
      iFrame "Hstack Hf".
      iPureIntro.
      right; split => //.
      apply N.ltb_lt in Hfull. 
      remember (length s) as x; rewrite - Heqx. lia. 
    }
    iExists 1.
    iSplit => //=.
    iPureIntro. unfold Wasm_int.Int32.ltu.
    rewrite wasm_int_unsigned; last lia.
    rewrite wasm_int_unsigned; last first.
    split; first lia. unfold two14 in Hstack.
    remember (length s) as x; rewrite - Heqx; lia.
    apply N.ltb_ge in Hfull.
    rewrite Coqlib.zlt_true => //.
    assert (N.of_nat (length s) = two14 - 1)%N. lia. remember ((length s)) as x.
    rewrite - Heqx. unfold two14 in H. lia.
    iFrame. iPureIntro. left; split => //.
    apply N.ltb_ge in Hfull. remember (length s) as x. rewrite - Heqx. lia. 
Qed.    

End specs.


End stack.    
      

