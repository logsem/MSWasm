From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export segstack_common segstack_is_empty iris_fundamental proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section stack.

 Context `{!wasmG Σ, HHB:HandleBytes}. 

Section code.


(*
  pop: [handle] -> [i32]
  locals declared: [i32]

  Given a stack pointer, pop the top i32 value from the stack.

  Implementation contains the is_empty check which results in a trap if the stack is empty. Otherwise, load the 
  stack top pointer from the stack pointer address, retrieve the value to be popped, then decrement the stack
  top pointer address by 4 and update it.
  
  Returns the popped value of type i32. Can trap only if the stack pointer is invalid or the stack is empty.

  Parameters/Locals:
  0 (input)     stack pointer
  1             temporary variable storing the new address of the stack top pointer
*)
Definition pop :=
  is_empty ++
  [
    BI_if (Tf [] []) [BI_unreachable] [];
    BI_get_local 0 ;
    BI_segload T_i32 ;
    BI_tee_local 1 ;
    BI_get_local 0 ;
    BI_handleadd ;
    BI_segload T_i32 ;
    BI_get_local 0 ;
    BI_get_local 1 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_sub) ;
    BI_segstore T_i32 
  ].

End code.

Section specs.

Lemma spec_pop f0 (v: handle) (a : i32) s E:
  ⊢ {{{ 
          ⌜ f0.(f_locs) !! 0 = Some (value_of_handle v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ isStack v (a :: s)
         ∗ ↪[frame] f0 }}}
    to_e_list pop @ E
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hlocv & %Hlocs & Hstack & Hf) HΦ" => /=.
  
  iDestruct (stack_pure with "Hstack") as "(%Hoff & %Hbound & %Hvalid & %Hlen)".
  
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜x = immV [value_of_int 0]⌝ ∗ isStack v (a :: s) ∗ ↪[frame] f0)%I).
  iSplitR; last iSplitL "Hstack Hf".
  2: { iApply (spec_is_empty with "[$Hstack $Hf]") => //.
       iIntros (w) "H".
       iDestruct "H" as (k) "(-> & Hstack & %Hk & Hf)".
       iFrame "Hstack Hf".
       by destruct Hk as [[-> ?] | [-> _]] => //.
  }
  { by iIntros "(%Habs & ?)". }
  
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [ ]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hf".
  iApply (wp_if_false with "Hf") => //.
  { iIntros "!> Hf".
    take_drop_app_rewrite 0.
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf /=".
      by iApply (wp_label_value with "Hf").
  }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_handle v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    iSplitR ; last iSplitL "Hstack Hf".
    2: { by iApply (stack_load_0 with "[$] [$]") => //. }
    { by iIntros "(%Habs & _)". }
    
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    rewrite separate2.
    iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [_] ⌝
                                           ∗ ↪[frame] _)%I)).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - fold_const; iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "[]Hf") => //.
    
  - iIntros (w) "[-> Hf]".
    iSimpl. 
    rewrite separate2.
    iApply wp_seq.
    iSplitR; last iSplitL "Hf".
    2: {
      rewrite (separate1 (AI_basic _)).
      iApply wp_val_app => //.
      iSplitR; last first.
      iApply wp_wand_r. iSplitL. iApply (wp_get_local with "[] Hf").
      simpl. unfold set_nth. destruct (f_locs f0); first by inversion Hlocs.
      simpl. done.
      
      by instantiate (1 := λ x, (⌜ x = immV [value_of_handle v] ⌝)%I).
      iIntros (w) "[-> Hf]".
      instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
      iFrame. done.
      by iIntros "!> [% _]". }
    { by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite separate4.
    iApply wp_seq.
    iSplitR; last iSplitL "Hf Hstack".
    2:{
      iApply (stack_load_j_alt with "[] [] [] [$Hstack] [$Hf]") => //.
      { iPureIntro => /=.
        instantiate (1 := 0%N). lia. }
      { by instantiate (1 := a) => /=. }
      { done. } 
    }
    { by iIntros "(%Habs & _)". }
    
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    subst.
    iApply (wp_get_local with "[] [$Hf]") => //=.
    unfold set_nth.
    destruct (f_locs f0); first by inversion Hlocs.
    done.
    
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                    ↪[frame] _)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=.
    by rewrite set_nth_read.
      
  - iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                       ↪[frame] _)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite (separate2 (AI_basic _)).
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    unfold i32const; fold_const; iApply (wp_binop with "Hf") => //.
    simpl.
  - iIntros (w) "[-> Hf]".
    iSimpl.
    iApply wp_wand_r.
    iDestruct "Hstack" as "(_ & _ & _ & _ & Hid & Hbase & Hrest)".
    iSplitL "Hid Hbase Hf".
  - rewrite (separate1 (AI_basic _)).
    iApply wp_val_app => //.
    iSplit ; last first.
    iApply wp_wand_r. iSplitL.
    fold_const; iApply wp_segstore => //; last first.
    iFrame. instantiate (2 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I). 
    iSplitR "Hbase". iIntros "!> H". iSplit; first done. iExact "H".
    iApply i32_wss. unfold handle_addr; rewrite Hoff N.add_0_r. done.
    rewrite Hoff Hbound => //. done.
    iIntros (w) "[(-> & Hid & Hbase) Hf]".
    iSimpl.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _ ∗ _ ∗ ↪[frame] _)%I).
    iSplit; first done.  iSplitL "Hid"; first iExact "Hid".
    iSplitL "Hbase"; first iExact "Hbase". iFrame. 
    by iIntros "!> [% _]".
        
  - iIntros (w) "(-> & Hid & Hbase & Hf)".
    iApply "HΦ".
    iSplitR => //.
    unfold isStack.
    rewrite cons_length in Hlen.
    iSplitR "Hf".
    repeat iSplit => //.
    iPureIntro.
    lia. iFrame. 
    iSplitL "Hbase".
  - simpl. 
    unfold handle_addr; rewrite Hoff N.add_0_r.
    iApply i32_wss.
    unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub.
    rewrite wasm_int_unsigned. rewrite wasm_int_unsigned; last lia.
    assert (Z.pos (Pos.of_succ_nat (length s) * 4) - 4 = Z.of_N (N.of_nat (length s) * 4))%Z.
    lia.
    rewrite H. done. split; first lia. unfold two14 in Hlen.
    assert (N.of_nat (S (length s) * 4) <= 65536)%N. lia.
    assert (N.to_nat (N.of_nat (S (length s) * 4)) <= N.to_nat 65536). lia.
    rewrite Nat2N.id in H0.
    assert (Z.pos (Pos.of_succ_nat (length s) * 4) = Z.of_nat (S (length s) * 4)).
    lia. rewrite H1. lia.
  - remember (length s) as x. 
    iDestruct "Hrest" as "((Ha & Hs) & Hrest)".
    iSplitL "Hs".
    iApply (big_sepL_impl with "Hs").
    iIntros "!>" (k y) "% H".
    iApply (points_to_i32_eq with "H") => //.
    simpl. 
    fold (4 * (N.of_nat k))%N.
    rewrite - Heqx. lia.
  - iDestruct "Hrest" as (bs) "(%Hbs & Hrest)".
    iExists (map (fun x => (x, Numeric)) (serialise_i32 a) ++ bs).
    iSplit.
    iPureIntro.
    rewrite app_length.
    rewrite Nat2N.inj_add.
    rewrite Hbs.
    remember (serialise_i32 a) as l.
    repeat (destruct l ; first done).
    destruct l ; last done.
    repeat rewrite cons_length.
    rewrite nil_length.
    rewrite - Heqx. unfold two14 in Hlen; unfold two16. lia. 
  - unfold seg_block_at_pos.
    rewrite big_sepL_app.
    iSplitL "Ha".
    iDestruct (i32_wss with "Ha") as "Ha".
    iApply (big_sepL_impl with "Ha").
    iIntros "!>" (k ?) "%Hbits H".
    do 2 rewrite of_nat_to_nat_plus.
    unfold Wasm_int.N_of_uint => //=.
    assert (base v + N.pos (Pos.of_succ_nat (length s) * 4) - 0 + N.of_nat k =
              base v + N.of_nat x * 4 + 4 + N.of_nat k)%N.
    lia. rewrite H. done.
  - iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (k ?) "%Hbits H".
    repeat rewrite of_nat_to_nat_plus.
    remember (serialise_i32 a) as l.
    repeat (destruct l => //).
    assert (base v + N.of_nat (length (a :: s)) * 4 + 4 + N.of_nat k =
              base v + N.of_nat x * 4 + 4 +
          N.of_nat (length (map (λ x1 : byte, (x1, Numeric)) [b; b0; b1; b2]) + k))%N.
    repeat rewrite cons_length.
    simpl. rewrite - Heqx. by lias. rewrite H. done.
    iExists _ ; by subst ; iFrame.
Qed.    



End specs.

End stack.    
      
