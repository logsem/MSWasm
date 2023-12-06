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



Section stack.

 Context `{!wasmG Σ, HHB: HandleBytes}. 
 
Section code.

(*
  is_empty: [handle] -> [i32]
  locals declared: []

  Given a stack pointer, determine if the stack is empty.

  Implemented by comparing the stack top pointer against 0: in the case of an empty stack,
    the stack top pointer will be 0.


  Returns 1 if the stack is empty, 0 otherwise.

  Parameters/Locals:
  0 (input)     stack pointer
*)
Definition is_empty_op :=
  [
    i32const 0;
    BI_get_local 0 ;
    BI_segload T_i32;
    BI_relop T_i32 (Relop_i ROI_eq)
  ].


 Definition is_empty :=
(*  validate_stack 0 ++
  validate_stack_bound 0 ++ *)
  is_empty_op. 

End code.



Section specs.
  Set Bullet Behavior "Strict Subproofs".
  
Lemma spec_is_empty_op f0 v s E: 
  ⊢ {{{ 
        ⌜ (f_locs f0) !! 0 = Some (value_of_handle v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s }}}
    to_e_list is_empty @  E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s ∗
                           ⌜ (k = 1 /\ s = []) \/
                  (k = 0 /\ s <> []) ⌝ ∗
           ↪[frame] f0}}}.
Proof.
  iIntros "!>" (Φ) "(%Hlocv & Hf & Hstack) HΦ" => /=.

  iDestruct (stack_pure with "Hstack") as "(%Hoff & %Hbound & %Hvalid & %Hstack)". 
  
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 0; value_of_handle v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR.
  by iIntros "[%Habs _]".
  iSplitL "Hf".
  { rewrite separate1.
    iApply wp_val_app => //=.
    iSplitR. by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=. }
  iIntros (w) "[-> Hf]".
  iSimpl. 
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 0; value_of_int (length s * 4)] ⌝ ∗ ↪[frame] f0 ∗ isStack v s )%I).
  iSplitR.
  by iIntros "[%Habs _]".
  iSplitL "Hf Hstack".
  { rewrite separate1.
    iApply wp_val_app => //=.
    iSplitR.
    by iIntros "!> [%Habs _]".
    iApply wp_wand_r. iSplitL. iApply (wp_segload with "[Hf Hstack]"); last first.
    iDestruct "Hstack" as "(_ & _ & _ & _ & Hid & Hbase & Hws & Hrest)".
    unfold handle_addr; rewrite Hoff N.add_0_r. iFrame. iSplitR "Hbase".
    instantiate (2 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iIntros "!> [Hid Hss]". iSplit; first done.
    iCombine "Hws Hrest Hid Hss" as "H".
    iExact "H".
    iApply i32_wss. iExact "Hbase". rewrite Hoff Hbound. done. done.
    rewrite map_fst_map_pair. 
    instantiate (1 := VAL_int32 _). done. done. done.
    iIntros (w) "[(-> & Hws & Hrest & Hid & Hbase) Hf]".
    iFrame. iSplit; last first. repeat iSplit => //.
    iApply i32_wss. done. 
    iPureIntro. unfold value_of_int => /=.
    assert (Z.of_N (N.of_nat (length s) * 4) = length s * 4)%Z.
    lia. rewrite H. done.
  }
  iIntros (w) "(-> & Hf & Hstack)".
  iSimpl. 
  iApply wp_wand_r.
  iSplitL "Hf". 
  iApply (wp_relop with "Hf") => //=.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  { iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR.
    iPureIntro.
    unfold value_of_int.
    unfold wasm_bool.
    repeat f_equal.
    instantiate (1 := if (Wasm_int.Int32.eq (Wasm_int.Int32.repr 0)
                            (Wasm_int.Int32.repr (length s * 4)))
                           then 1%Z else 0%Z). 
    remember (Wasm_int.Int32.eq (Wasm_int.Int32.repr 0)
                (Wasm_int.Int32.repr (length s * 4))) as cmpres.
    rewrite - Heqcmpres. by destruct cmpres => //=.
    iFrame "Hstack Hf".
    iPureIntro.
    destruct s.
    left.
    split => //=.
    right.
    split => //=.
    rewrite Wasm_int.Int32.eq_false => //=.
    intro.
    apply Wasm_int.Int32.repr_inv in H. lia.
    rewrite u32_modulus. lia. rewrite u32_modulus. unfold two14 in Hstack.
    simpl in Hstack. lia. }
Qed.


(*
Lemma spec_is_empty f0 v s E: 
  ⊢ {{{ ⌜ f0.(f_inst).(inst_memory) !! 0 = Some n ⌝ ∗
        ⌜ (f_locs f0) !! 0 = Some (value_of_uint v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s n }}}
    to_e_list is_empty @  E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s n ∗
                           ⌜ (k = 1 /\ s = []) \/
                  (k = 0 /\ s <> []) ⌝ ∗
           ↪[frame] f0}}}.
Proof.
  iIntros "!>" (Φ) "(%Hinst & %Hlocv & Hf & Hstack) HΦ" => /=.
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_valid with "[$Hstack $Hf]").
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.

  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜ x = immV [] ⌝ ∗ isStack v s n ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hstack Hf"; first by iApply (is_stack_bound_valid with "[$Hstack $Hf]").
  
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.
  by iApply (spec_is_empty_op with "[$Hf $Hstack] [HΦ]") => //.
Qed. *)

End specs.

Section valid.
  Context `{!logrel_na_invs Σ}.
  Set Bullet Behavior "Strict Subproofs".

  (*
  Lemma valid_is_empty t funcs :
    let i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := funcs;
                     inst_tab := [t];
                     inst_memory := [];
                     inst_globs := []
              |} in
    na_inv logrel_nais stkN (stackModuleInv (λ (a : handle) (b : seq.seq i32), isStack a b) (λ n : nat, ↦[wslength]N.of_nat n)) -∗
    interp_closure_native i0 [T_i32] [T_i32] [] (to_e_list is_empty) [].
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
        iApply (spec_is_empty_op with "[$Hstack $Hf]").
        { subst f';simpl;repeat iSplit;auto. iPureIntro.
          unfold value_of_uint. f_equal. f_equal. apply int_of_Z_mod. }
        iIntros (w) "Hk".
        iDestruct "Hk" as (k0) "(-> & Hstack & %Hk & Hf)".
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
        iNext. iLeft. iRight. iExists [_]. iSplit;eauto. iSplit; simpl;auto. eauto.
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
  Qed.
*)
      
End valid.

End stack.    
      
