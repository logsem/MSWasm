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
Definition pop_op :=
  is_empty_op ++
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

Definition pop :=
  (* validate_stack 0 ++ validate_stack_bound 0 ++ *) pop_op.

End code.

Section specs.

Lemma spec_pop_op f0 (v: handle) (a : i32) s E:
  ⊢ {{{ 
          ⌜ f0.(f_locs) !! 0 = Some (value_of_handle v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ isStack v (a :: s)
         ∗ ↪[frame] f0 }}}
    to_e_list pop_op @ E
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
  2: { iApply (spec_is_empty_op with "[$Hstack $Hf]") => //.
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
  - iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "[]Hf") => //.
    
  - iIntros (w) "[-> Hf]".
(*    remember {| f_locs := set_nth (value_of_uint (v + N.of_nat (S (length s)) * 4)) (f_locs f0) 1
                                  (value_of_uint (v + N.of_nat (S (length s)) * 4)) ;
                f_inst := f_inst f0 |} as f1.
    rewrite - Heqf1. *)
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
    iApply (wp_binop with "Hf") => //.
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
    iApply wp_segstore => //; last first.
    iFrame. instantiate (2 := λ x, (⌜ x = immV _ ⌝)%I). 
    iSplit; first done. 
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


(*
Lemma spec_pop f0 n v (a : i32) s E:
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝
         ∗ ⌜ f0.(f_locs) !! 0 = Some (value_of_uint v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ isStack v (a :: s) n
         ∗ ↪[frame] f0 }}}
    to_e_list pop @ E
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s n ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & %Hlocs & Hstack & Hf) HΦ" => /=.
  
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v _ n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_valid with "[$Hstack $Hf]").
  
  iIntros (w) "(-> & Hstack & Hf) /=".
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v _ n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_bound_valid with "[$Hstack $Hf]").
  
  iIntros (w) "(-> & Hstack & Hf) /=".
  iApply (spec_pop_op with "[$Hf $Hstack] [$]").
  auto.
Qed.
*)

End specs.

Section valid.
  Context `{!logrel_na_invs Σ}.
  Set Bullet Behavior "Strict Subproofs".
(*
  Lemma valid_pop m t funcs :
    let i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := funcs;
                     inst_tab := [t];
                     inst_memory := [m];
                     inst_globs := []
              |} in
    na_inv logrel_nais stkN (stackModuleInv (λ (a : N) (b : seq.seq i32), isStack a b m) (λ n : nat, N.of_nat m↦[wmlength]N.of_nat n)) -∗
    interp_closure_native i0 [T_i32] [T_i32] [T_i32] (to_e_list pop) [].
  Proof.
    iIntros "#Hstk".
    iIntros (vcs f) "#Hv Hown Hf".
    iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8;subst;simpl.
    iApply (wp_frame_bind with "[$]");auto.
    iIntros "Hf".
    match goal with | |- context [ [AI_label _ _ ?l] ] => set (e:=l) end.
    build_ctx e.
    iApply wp_label_bind.
    subst e.
    iDestruct "Hv" as "[%Hcontr|Hws]";[done|iDestruct "Hws" as (ws) "[%Heq Hws]"].
    iDestruct (big_sepL2_length with "Hws") as %Hlen. inversion Heq;subst.
    destruct ws as [|w0 ws];[done|destruct ws as [|w1 ws];[|done]].
    iSimpl in "Hws".
    iDestruct "Hws" as "[Hw0 _]".
    iDestruct "Hw0" as (z0) "->".
    pose proof (value_of_uint_repr z0) as [v ->]. iSimpl in "Hf".
    take_drop_app_rewrite (length (validate_stack 1)).

    match goal with | |- context [ (WP ?e @ _; _ {{ _ }} )%I ] => set (e0:=e) end.
    match goal with | |- context [ (↪[frame] ?f0)%I ] => set (f':=f0) end.
    build_ctx e0. subst e0.
    iApply wp_seq_can_trap_ctx.
    instantiate (1:=(λ f0, ⌜f0 = f'⌝ ∗ na_own logrel_nais ⊤)%I).
    iFrame "Hf".
    iSplitR;[|iSplitR;[|iSplitL]];cycle 1.
    - iIntros (f0) "(Hf & -> & Hown)".
      deconstruct_ctx.
      iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
      iApply (wp_label_trap with "Hf");auto.
      iIntros (v0) "[-> Hf]". iExists _. iFrame.
      iIntros "Hf".
      iApply (wp_frame_trap with "Hf").
      iNext. iLeft. iLeft. auto.
    - iIntros "Hf". iFrame.
      iApply (wp_wand with "[Hf]").
      iApply check_stack_valid;iFrame;subst;eauto.
      iIntros (v0) "[$ HH]". eauto.
    - subst f'. iIntros (w f0) "([-> %Hdiv] & Hf & -> & Hown) /=".
      deconstruct_ctx.
      take_drop_app_rewrite (length (validate_stack_bound 0)).
      iApply fupd_wp.
      iMod (na_inv_acc with "Hstk Hown") as "(>Hstkres & Hown & Hcls)";[solve_ndisj..|].
      iModIntro.
      iDestruct "Hstkres" as (l Hmul) "[Hlen Hstkres]".
      iDestruct "Hstkres" as (l' Hmultiple) "Hl'".
      match goal with | |- context [ (WP ?e @ _; _ {{ _ }} )%I ] => set (e0:=e) end.
      match goal with | |- context [ (↪[frame] ?f0)%I ] => set (f':=f0) end.
      match goal with | |- context [ (?P ={⊤}=∗ ?Q)%I ] => set (CLS:=(P ={⊤}=∗ Q)%I) end.
      set (k:=Wasm_int.N_of_uint i32m ((Wasm_int.int_of_Z i32m (Z.of_N v)))).
      destruct (decide (k < N.of_nat l)%N).
      + apply div_mod_i32 in Hdiv as Hdiv'.
        eapply multiples_upto_in in Hmultiple as Hin;[..|apply Hdiv'];[|lia].
        apply elem_of_list_lookup_1 in Hin as [i Hi].
        iDestruct (big_sepL_lookup_acc with "Hl'") as "[Hv Hl']";[eauto|].
        iDestruct "Hv" as (stk) "Hv".
        iApply (wp_seq _ _ _ (λ v, ⌜v = immV []⌝ ∗ _)%I).
        iSplitR;[by iIntros "[%Hcontr _]"|].
        iSplitL "Hf Hv".
        { iApply is_stack_bound_valid. iFrame "Hf Hv". iSplit;auto.
          iPureIntro. subst f'. simpl. unfold value_of_uint.
          f_equal. f_equal. apply int_of_Z_mod. }
        iIntros (w) "(-> & Hstack & Hf) /=".
        destruct (decide (stk = []));cycle 1.
        * destruct stk;[done|].
          iApply (spec_pop_op with "[$Hstack $Hf]").
          { subst f';simpl;repeat iSplit;auto. iPureIntro.
            unfold value_of_uint. f_equal. f_equal. apply int_of_Z_mod. }
          iIntros (w) "[-> [Hstack Hf]]".
          iDestruct "Hf" as (f1) "[Hf %Hfeq]".
          iDestruct ("Hl'" with "[Hstack]") as "Hl'".
          { iExists _. iFrame. }
          deconstruct_ctx.
          iApply fupd_wp.
          iMod ("Hcls" with "[Hlen Hl' $Hown]") as "Hown".
          { iExists _. iFrame. iNext. iSplit;auto. }
          iModIntro.
          iApply (wp_wand _ _ _ (λ v, ⌜v = immV [_]⌝ ∗ _)%I with "[Hf]").
          iApply (wp_label_value with "Hf");eauto.
          iIntros (v0) "[-> Hf]".
          iExists _. iFrame.
          iIntros "Hf".
          iApply (wp_frame_value with "Hf");eauto.
          iNext. iLeft. iRight. iExists [VAL_int32 s]. iSplit;auto. iSplit; simpl;auto. eauto.
        * iDestruct (stack_pure with "Hstack") as "(_ & _ & %Hstkbound & Hstack)".
          take_drop_app_rewrite (length (is_empty_op)).
          iApply wp_seq.
          iSplitR;[|iSplitL "Hf Hstack"];cycle 1.
          { iApply (spec_is_empty_op with "[$Hf $Hstack]").
            - repeat iSplit;auto.
              iPureIntro. subst f';simpl. unfold value_of_uint.
              f_equal. f_equal. apply int_of_Z_mod.
            - iIntros (w) "H". iExact "H". }
          2: iIntros "H";by iDestruct "H" as (? ?) "_".
          iIntros (w) "H".
          iDestruct "H" as (k0) "(-> & Hstack & [[-> %Hcond]|[-> %Hcond]] & Hf)";[|congruence].
          simpl.
          iDestruct ("Hl'" with "[Hstack]") as "Hl'".
          { iExists _. iFrame. }
          iApply fupd_wp.
          iMod ("Hcls" with "[Hlen Hl' $Hown]") as "Hown".
          { iExists _. iFrame. iNext. iSplit;auto. }
          iModIntro.
          take_drop_app_rewrite 2.
          iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
          iApply wp_seq_trap. iFrame.
          iIntros "Hf". iApply (wp_if_true with "[$]");auto.
          iNext. iIntros "Hf".
          take_drop_app_rewrite 0.
          iApply (wp_block with "[$]");auto.
          iNext. iIntros "Hf".
          build_ctx [AI_basic BI_unreachable].
          take_drop_app_rewrite 1.
          iApply wp_seq_trap_ctx. iFrame. iIntros "Hf".
          iApply (wp_unreachable with "[$]"). auto.
          iIntros (v') "[-> Hf]".
          deconstruct_ctx.
          iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
          iApply (wp_label_trap with "[$]");eauto.
          iIntros (v0) "[-> Hf]".
          iExists _. iFrame. iIntros "Hf".
          iApply (wp_frame_trap with "[$]").
          iNext. iLeft. iLeft. auto.          
      + iApply (wp_wand with "[Hlen Hf]").
        iApply (fail_stack_bound_valid with "[$Hlen $Hf]").
        eauto.
        iIntros (v0) "(-> & Hlen & Hf)".
        deconstruct_ctx.
        iApply fupd_wp.
        iMod ("Hcls" with "[$Hown Hl' Hlen]") as "Hown".
        { iNext. iExists _. iFrame. auto. }
        iModIntro.
        iApply (wp_wand _ _ _ (λ v, ⌜v = trapV⌝ ∗ _)%I with "[Hf]").
        iApply (wp_label_trap with "Hf");eauto.
        iIntros (v0) "[-> Hf]".
        iExists _. iFrame. iIntros "Hf".
        iApply (wp_frame_trap with "[$]").
        iNext. iLeft. iLeft. auto.
    - iIntros "[%Hcontr _]";done.
  Qed. *)
      
End valid.

End stack.    
      
