From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

From MSWasm.iris.language.iris Require Import iris iris_locations.
From MSWasm.iris.helpers Require Import iris_properties.
From MSWasm.iris.language Require Import iris_atomicity iris_wp_def.
From MSWasm Require Import stdpp_aux datatypes operations properties opsem typing.
From MSWasm.iris.rules Require Import iris_rules. 
From MSWasm.iris.logrel Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ, HHB: HandleBytes, cancelg: cancelG Σ, !cinvG Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Lemma interp_ctx_continuations_push_label_block lh C hl i tm :
    base_is_empty lh ->
    lholed_lengths (rev (tc_label C)) lh ->
    interp_ctx_continuations (tc_label C) (tc_return C) hl (tc_local C) i lh -∗
    interp_ctx_continuation (tc_label (upd_label C ([tm] ++ tc_label C))) (tc_return C) hl (push_base lh (length tm) [] [] [])
                              0 tm (tc_local C) i.
  Proof.
    iIntros (Hlh_base Hlh_len) "#Hc". unfold interp_ctx_continuation.
    iSimpl. rewrite lh_depth_push_base.
    assert (S (lh_depth lh) - 1 = lh_depth lh) as ->;[lia|].
    rewrite get_layer_push_base_0;[|auto].
    apply lh_minus_push_base_Some with (n:=length tm) (es:=[]) (vs1:=[]) (es2:=[]) in Hlh_base as Hmin.
    iExists _,_,_,_,_,_. repeat (iSplit;[simpl;eauto|]).
    iModIntro. iIntros (v f all).
    iIntros "#Hw [Hf Hfv] Hall".
    unfold interp_expression.
    rewrite app_nil_l app_nil_r.

    iDestruct "Hw" as "[-> | Hv]".
    { iExists [].
      take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [Hf]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _, _. iFrame "∗ #". }

    iDestruct "Hv" as (ws' ->) "Hv". iExists tm.
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    repeat rewrite -!/(interp_frame _ _ _).
    rewrite app_nil_r.
    iApply wp_value;[done|].
    iSplitR;[|iExists _;iFrame;iExists _;eauto].
    iLeft. iRight. iExists _. eauto.
  Qed.

  Lemma interp_ctx_push_label_block C hl tm i lh :
    interp_ctx (tc_label C) (tc_return C) hl (tc_local C) i lh -∗
    interp_ctx (tc_label (upd_label C ([tm] ++ tc_label C)%list))
      (tc_return C) hl (tc_local (upd_label C ([tm] ++ tc_label C)%list)) i
      (push_base lh (length tm) [] [] []).
  Proof.
    iIntros "[%Hlh_base [%Hlh_len [%Hlh_valid #Hc]]]".
    iSplit;[|iSplit;[|iSplit]].
    { iPureIntro. apply base_is_empty_push_base. }
    { iPureIntro. apply lholed_lengths_push_base. auto. }
    { iPureIntro. apply lholed_valid_push_base. auto. }
    { iSplitR.
      { iSimpl. iSplitR;[|done].
        iApply (interp_ctx_continuations_push_label_block with "[]");auto. }
      iApply (big_sepL_mono with "Hc").
      iIntros (k y Hk). iSimpl.
      iIntros "#Hcont".
      iDestruct "Hcont" as (vs j es0 lh' es' lh'' Hlayer Hdep Hmin) "Hcont".
      iExists vs,j,es0,_,es',lh''.
      rewrite lh_depth_push_base PeanoNat.Nat.sub_succ.
      iSplit.
      { iPureIntro. apply get_layer_push_base;eauto. }
      iSplit;[auto|]. iSplit.
      { iPureIntro. apply push_base_lh_minus_is_Some. auto. }
      iModIntro. iIntros (v f all) "#Hv [Hf Hvf] Hall".
      iDestruct ("Hcont" with "Hv [$Hf $Hvf] Hall") as "Hcont'".
      iFrame.
    }
  Qed.

  (* ----------------------------------------- BLOCK --------------------------------------- *)

  Lemma typing_block C tn tm es : (⊢ semantic_typing (upd_label C ([tm] ++ tc_label C)%list) (to_e_list es) (Tf tn tm)) ->
                                  ⊢ semantic_typing C (to_e_list [BI_block (Tf tn tm) es]) (Tf tn tm).
  Proof.
    intros IHbe_typing.
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi".
    
    iDestruct (IHbe_typing $! i (push_base lh (length tm) [] [] []) with "[]") as "HH"; [by (destruct C,i;eauto)|].

    iIntros "#Hc". iIntros (f all vs) "[Hf Hfv] Hall #Hv".
    
    iDestruct "Hv" as "[-> | Hv]".
    {  take_drop_app_rewrite_twice 0 1.
       iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
       { iApply (wp_trap with "[] [Hf]");auto. }
       iIntros (v0) "[? ?]". iFrame. iExists _,_. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.

    iApply (wp_block with "Hf");eauto.
    { apply v_to_e_is_const_list. }
    { rewrite fmap_length //. }
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.

    iAssert (∀ f, interp_frame (tc_local C) i f -∗ ↪[frame] f -∗ interp_allocator all -∗ WP of_val (immV ws) ++ to_e_list es
              {{ v, (⌜v = trapV⌝ ∨
                       interp_values tm v ∨
                       interp_br (tc_local C) i (tc_return C) hl v _ _ ∨ _)
                      ∗ ∃ f all, ↪[frame] f ∗ interp_frame (tc_local C) i f ∗ interp_allocator all }})%I as "Hcont".
    { iIntros (f') "Hfv Hf Hall".
      iDestruct ("HH" with "[] [Hf Hfv] Hall []") as "Hcont".
      { iApply (interp_ctx_push_label_block with "[$]"). }
      { iFrame "∗ #". }
      { iRight. iExists _. eauto. } 
      iApply (wp_wand with "Hcont").
      iIntros (v) "[H ?]". rewrite -or_assoc. iFrame. }
    
    iDestruct ("Hcont" $! f with "[$]") as "Hcontf". simpl push_base.
    iApply iRewrite_nil_r_ctx.

    iApply (wp_seq_can_trap_ctx). iFrame.
    iSplitR; last (iSplitR; last iSplitL).
    3:{ iIntros "Hf". iSpecialize ("Hcontf" with "Hf Hall").
        iApply (wp_wand with "Hcontf").
        iIntros (v) "[H Hf]".
        iSplitL "H"; first iExact "H".
        instantiate (1 := λ f0, (∃ all0, interp_frame (tc_local C) i f0 ∗ interp_allocator all0)%I).
        iDestruct "Hf" as (f0 all0) "(Hf & Hfv & Hall)".
        iExists _; iFrame. iExists _; iFrame. } 
    { iIntros "[Hcontr | [Hcontr | [Hcontr | Hcontr] ] ]";[by iDestruct "Hcontr" as (? ?) "_"|..].
      { rewrite fixpoint_interp_br_eq. iDestruct "Hcontr" as (? ? ? ? ?) "_". done. }
      { iDestruct "Hcontr" as (? ? ?) "_";done. }
      { rewrite fixpoint_interp_call_host_eq. iDestruct "Hcontr" as (? ? ? ? ? ? ?) "_";done. } }
    { iIntros (f0) "[Hf (%all0 & Hfv & Hall)]".
      iSplitR; first by iLeft; iLeft.
      iExists _,_. iFrame. } 

    iIntros (w f') "(Hred & Hf & %all0 & Hfv & Hall)".
    rewrite app_nil_r.
    iDestruct "Hred" as "[#Hval | [Hbr|[Hret|Hch]]]".
    
    { iDestruct "Hval" as (vs ->) "Hval".
      iDestruct (big_sepL2_length with "Hval") as %Hlen'.
      iApply (wp_wand_ctx _ _ _ (λ vs0, ⌜vs0 = immV vs⌝ ∗ ↪[frame] _)%I with "[Hf]").
      { iApply (wp_val_return with "Hf");[apply const_list_of_val|].
        iIntros "Hf". rewrite app_nil_l app_nil_r.
        iApply wp_value;[done|].  eauto. }
      iIntros (v) "[-> Hf]".
      iSplitR;[|iExists _;iFrame;iExists _;eauto].
      iLeft. iRight. iExists _. iSplit;eauto. }

    { rewrite fixpoint_interp_br_eq.
      iDestruct "Hbr" as (j vh vs p -> Hbase Hsize) "Hbr".
      simpl of_val.
      
      assert (LH_rec [] (length tm) [] (LH_base [] []) [] =
                push_base (LH_base [] []) (length tm) [] [] []) as Heq;[auto|].
      rewrite Heq.
      iApply wp_label_push_nil_inv. iApply wp_wasm_empty_ctx.

      destruct (decide (j = p)).
      { iApply (interp_br_step with "Hbr Hf Hfv Hall"); eauto. } 

      { iAssert (⌜lholed_lengths (rev (tc_label C)) lh⌝ ∧ ⌜lholed_valid lh⌝ ∧ ⌜base_is_empty lh⌝)%I as %[Hlh_length [Hlh_valid Hlh_empty]].
        { iDestruct "Hc" as "[% [% [% _]]]". auto. }
        iApply (interp_br_stuck_push with "Hbr Hf Hfv Hall") ;eauto. } 
    }
    { iApply (interp_return_label with "Hret Hf Hfv Hall"). }
    { iApply (interp_call_host_label with "Hc Hch Hf Hfv Hall"). }
  Qed.

End fundamental.
