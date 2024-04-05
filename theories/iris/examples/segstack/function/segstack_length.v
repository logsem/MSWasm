From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export segstack_common iris_fundamental proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section stack.

 Context `{!wasmG Σ, HHB: HandleBytes}. 
 
Section code.

(*
  stack_length: [handle] -> [i32]
  locals declared: []

  Given a stack pointer, find the length of the stack.

  Implemented by simply subtracting the stack top pointer by the stack pointer.
  Performs an input validation check prior to execution. Can trap only if validation fails.

  Returns the length of the stack as a u32.

  Parameters/Locals:
  0 (input)     stack pointer
 *)
  
Definition stack_length :=
  [
    BI_get_local 0 ;
    BI_segload T_i32;
    (i32const 4) ;
    BI_binop T_i32 (Binop_i (BOI_div SX_U))
  ].



End code.



Section specs.
  
Lemma spec_stack_length f0 (v: handle) s E (len: N): 
  ⊢ {{{
        ⌜ (f_locs f0) !! 0 = Some (value_of_handle v) ⌝ ∗ 
        ⌜ (N.of_nat (length s) = len)%N ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s }}}
    to_e_list stack_length @ E
    {{{ w, ⌜ w = immV [value_of_uint len] ⌝ ∗ isStack v s ∗
           ↪[frame] f0}}}.
Proof.
  iIntros "!>" (Φ) "(%Hlocv & %Hlen & Hf & Hstack) HΦ" => /=.

  iDestruct (stack_pure with "Hstack") as "(%Hoff & %Hbound & %Hvalid & %Hlens)".
  
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: {
    iApply (wp_get_local with "[] [$Hf]") => //.
    by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "[-> Hf]" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hstack Hf".
  2: { by iApply (stack_load_0 with "[$Hstack] [$Hf]") => //. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hstack & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  { unfold i32const; fold_const; iApply (wp_binop with "Hf") => //=. 
    unfold Wasm_int.Int32.divu => /=.
    rewrite Wasm_int.Int32.Z_mod_modulus_id.
    2: { unfold two14 in Hlens; rewrite u32_modulus. remember (length s) as x. rewrite - Heqx. lia. }
    rewrite N2Z.inj_mul => /=.
    rewrite Z.div_mul => //.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  }
  
  iIntros (w) "(-> & Hf)".
  iApply "HΦ".
  iFrame. rewrite Hlen. done.
Qed.


End specs.

End stack.    
      

