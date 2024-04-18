From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export segstack_common segstack_is_empty proofmode segstack_pop.
Require Import iris_fundamental iris_fundamental_get_local iris_fundamental_segstore.
Require Export type_checker_reflects_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section pop_robust.
Context `{ HHB: HandleBytes, !wasmG Σ, !cinvG Σ, cancelg: cancelG Σ, !hvisG Σ, !hasG Σ, !hmsG Σ, !logrel_na_invs Σ}. 
  
Lemma spec_pop_robust vcs f hfs (* C *) i all:
(*   tc_label C = [] ∧ tc_return C = None ->
   interp_instance C [] i -∗ *)
     interp_val [T_handle] (immV vcs) -∗
      ↪[frame] f -∗
      na_own logrel_nais ⊤ -∗
      interp_allocator all -∗
      WP to_e_list pop
      FRAME
      length [T_i32];
{|
  f_locs := vcs ++ n_zeros [T_i32];
  f_inst := i
|}
  CTX
  1; LH_rec [] (length [T_i32]) [] (LH_base [] []) []
       {{ v, (interp_val [T_i32] v ∨ interp_call_host_cls hfs [T_i32] v) ∗
               na_own logrel_nais ⊤ ∗  ↪[frame]f ∗
               (∃ all0 : leibnizO allocator, interp_allocator all0) }}.
Proof.
(*  intros HC. *)
  iIntros "#Hv Hf Hown Hall" (lh HLI%lfilled_Ind_Equivalent).
  inversion HLI; inversion H8 ; subst.

(*  assert (be_typing (upd_local_label_return C ([T_handle] ++ [T_i32]) [[T_i32]] (Some [T_i32])) pop (Tf [] [T_i32])).
  { unfold pop, is_empty. simpl.
     rewrite (separate9 (i32const _ )).
     eapply bet_composition'.
     { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
     { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
  } 

  iDestruct (be_fundamental_local _ pop [T_handle] _ _ HC H) as "H".
  
  iApply (wp_wand with "[-]").
  iApply ("H" with "Hi Hf Hown Hall [Hv]").
  { iRight. iDestruct "Hv" as "[%Habs | Hv]"; first done.
    iDestruct "Hv" as (ws) "(%Heq & Hv)". inversion Heq; subst.
    iDestruct (big_sepL2_length with "Hv") as "%Hlen". 
    destruct ws; first done.  destruct ws; last done.
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    iSimpl. iExists _. repeat iSplit => //. iExists _. done. }

  iIntros (v) "([Hv' Hown] & Hf & Hall)".
  iFrame. 
 *)


  (* iSimpl. rewrite separate2. iApply wp_seq.
  iSplitR; last first. iSplitL "Hf".
  rewrite (separate1 (AI_basic _)).
  iApply wp_val_app. done.
  iSplitR; last first.
  iApply (wp_wand with "[-]").

   iDestruct (typing_get_local with "[] [] [] [] []") as "H".
  6:{ instantiate (1 := immV []). iRight. iExists _. iSplit => //. }
  6:{ iSimpl in "H". iApply "H". }
  6:{ iIntros (w) "H".  *)


    iApply (wp_frame_bind with "Hf").
  done.
  iIntros "Hf".
  match goal with | |- context [ [ AI_label _ _ ?l ] ] => set (e := l) end.
  build_ctx e.
  iApply wp_label_bind.
  subst e. 

  

  
  iDestruct "Hv" as "[%Habs | Hv]"; first done.
  iDestruct "Hv" as (ws) "(%Heq & Hv)". inversion Heq; subst.
  iDestruct (big_sepL2_length with "Hv") as "%Hlen". 
  destruct ws; first done.  destruct ws; last done.
  iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
  rewrite fixpoint_interp_value_handle_eq. 
  iDestruct "Hv" as (h) "[-> H]".
  iSimpl. unfold i32const. 
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf".
  rewrite (separate1 (AI_basic _)).
  iApply wp_val_app. done.
  iSplitR; last first.
  iApply (wp_wand with "[Hf]"). 
  iApply (wp_get_local with "[] Hf"). done.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (v) "[-> Hf]".
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
  iSplit; [done | iExact "Hf"].
  by iIntros "!> [% _]".
  2: by iIntros "[% _]".
  iIntros (w) "[-> Hf]".
  iSimpl. 
  
  destruct (valid h) eqn:Hval. 

  (* Case A: the handle is corrupt *)
  2:{ rewrite separate3.
      iApply (wp_wand with "[Hf]"). 
      iApply (wp_seq_trap with "[$Hf]").
      iSplitR; last first. iIntros "Hf".
      rewrite (separate1 (AI_basic _)). 
      iApply (wp_val_app_trap with "[$Hf]"). done.
      iSplitR; last first. 
      iIntros "Hf".
      iApply wp_segload_failure1. by left.
      iFrame. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      1-2: by iIntros "!>" (w) "->". 
      iIntros (w) "[-> Hf]".
      iSimpl.
      rewrite - (app_nil_l [AI_trap]).
      rewrite - (app_nil_r [AI_trap]).
      iApply (wp_wand_ctx with "[Hf]").
      iApply (wp_trap_ctx with "Hf"). done.
      iIntros (v) "[-> Hf]".
      iExists _. iFrame.
      iIntros "Hf".
      iSimpl. iApply (wp_wand with "[Hf]").
      iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iSplitR. by iLeft; iLeft.
      iFrame. iExists _. iFrame. }

  iDestruct "H" as "[%Habs | (%γ & %base' & %bound' & %base_all & %bound_all & %q & %Hq & Hw & %Hbase_all & %Hbase' & %Hbound_all & %Hbound' & Hinv)]"; first done.

  destruct (offset h + N.of_nat (t_length T_i32) <=? bound h)%N eqn:Hbound.
  (* Case B: the offset is OOB *)
  2:{ rewrite separate3.
      iApply (wp_wand with "[Hf]").
      iApply (wp_seq_trap with "[$Hf]").
      iSplitR; last first. 
      iIntros "Hf".
      rewrite (separate1 (AI_basic _)). 
      iApply (wp_val_app_trap with "[$Hf]"). done.
      iSplitR; last first. iIntros "Hf". iApply wp_segload_failure1.
      right; left. apply N.leb_gt in Hbound. lia.
      iFrame. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      1-2: by iIntros "!>" (w) "->". 
      iIntros (w) "[-> Hf]".
      iSimpl.
      rewrite - (app_nil_l [AI_trap]).
      rewrite - (app_nil_r [AI_trap]).
      iApply (wp_wand_ctx with "[Hf]").
      iApply (wp_trap_ctx with "Hf"). done.
      iIntros (v) "[-> Hf]".
      iExists _. iFrame.
      iIntros "Hf".
      iSimpl. iApply (wp_wand with "[Hf]").
      iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iSplitR. by iLeft; iLeft.
      iFrame. iExists _. iFrame. }

  apply N.leb_le in Hbound.
  iDestruct "Hall" as (f1) "[Hbl Hall]".
  iDestruct (gamma_agree with "Hw Hbl") as "%Hf1".
  iDestruct (big_sepM_lookup_acc with "Hall") as "[Ha Hrestitute]"; first done.
  iDestruct "Ha" as (y Hy) "[Ha Hy]".
  destruct y as [[base'' all'']|].

  (* Case C: the handle has been freed *)
  2:{ rewrite separate3.
      iApply (wp_wand with "[Hf Ha]").
      iApply (wp_seq_trap with "[$Hf Ha]").
      iSplitR; last first. iIntros "Hf".
      rewrite (separate1 (AI_basic _)). 
      iApply (wp_val_app_trap with "[$Hf Ha]"). done.
      iSplitR; last first. iIntros "Hf". iApply (wp_segload_failure2 with "[$Hf $Ha]").
      iIntros "!> Ha". 
      instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
      iSplit; [done | iExact "Ha"].
      1-2: by iIntros "!>" (w) "[-> _]". 
      iIntros (w) "[[-> Ha] Hf]".
      iSimpl.
      rewrite - (app_nil_l [AI_trap]).
      rewrite - (app_nil_r [AI_trap]).
      iApply (wp_wand_ctx with "[Hf]").
      iApply (wp_trap_ctx with "Hf"). done.
      iIntros (v) "[-> Hf]".
      iExists _. iFrame.
      iIntros "Hf".
      iSimpl. iApply (wp_wand with "[Hf]").
      iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iSplitR. by iLeft; iLeft.
      iFrame. iExists _,_.
      iFrame. iApply "Hrestitute". iExists None. iFrame. done. 
      
  }

  iDestruct "Hy" as "(-> & -> & Htok)".
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf Ha Htok".
  rewrite (separate1 (AI_basic _)).
  iApply wp_val_app. done.
  iSplitR; last first.
  iApply (wp_wand with "[-]").

  iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
  iMod (cinv_acc with "Hinv Htok") as "((%tbs & >%Htbs & >Hss & Haddrs) & Htok & Hclose)"; first by set_solver. 
  iModIntro. rewrite - (N2Nat.id base'). 
  iDestruct (wss_select (N.to_nat base') (N.to_nat bound') (N.to_nat (handle_addr h)) 4 with "Hss") as "(%Hlentake & Hss & Hrestore)".
  unfold handle_addr. lia. unfold handle_addr. simpl in Hbound. lia.
  done.
  repeat rewrite N2Nat.id.
  iApply (wp_wand with "[Hss Ha Hf]"). 
  iApply (wp_segload_deserialize with "[$Hf $Ha $Hss]") => //.
  iIntros "!> H".
  instantiate (1 := λ x, (⌜ x = immV _ ⌝%I ∗ _)%I).
  iSplit; [done | iExact "H"].
  iIntros (w) "[(-> & Ha & Hss) Hf]".
  iMod ("Hclose" with "[Hrestore Hss Haddrs]").
  iNext. iExists tbs. 
  iDestruct ("Hrestore" with "[] Hss") as "Hss".
  done. iFrame. iSplit; first done.
  rewrite cat_app reconstitute. done.
  iModIntro. iFrame.
  instantiate (1 := λ x, (∃ v, ⌜ x = immV [VAL_int32 v] ⌝ ∗ _)%I).
  iCombine "Htok Ha" as "H".
  iExists _. iSplit; [done | iExact "H"].
  iIntros (w) "[(%v & -> & Htok & Ha) Hf]".
  iCombine "Htok Ha Hf" as "H".
  instantiate (1 := λ x, (∃ v, ⌜ x = immV [_;VAL_int32 v] ⌝ ∗ _)%I).
  iExists _. iSplit; first done. iExact "H".
  by iIntros "!> (%v & % & _)".
  2: by iIntros "(%v & % & _)". 

  iIntros (w) "(%v & -> & Htok & Ha & Hf)".
  iSimpl.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf". fold_const. iApply (wp_relop with "Hf"). done.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  2: by iIntros "[% _]".
  iIntros (w) "[-> Hf]". 
  
  iSimpl.

  rewrite separate2.
  destruct (Wasm_int.Int32.eq _ _).
  (* Case D: popping from an empty list *)
  { iApply (wp_wand with "[Hf]").
    iApply wp_seq_trap. iSplitR; last first.
    iFrame. iIntros "Hf". 
    iApply (wp_if_true with "Hf") => //.
    iIntros "!> Hf".
    rewrite - (app_nil_l [AI_basic _]).
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_wasm_empty_ctx. 
    iApply wp_label_push_nil.
    iSimpl.
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq_trap_ctx. iSplitR; last first.
    iFrame. iIntros "Hf". iApply (wp_unreachable with "Hf").
    by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
    1-2: by iIntros "!>" (w) "%".
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite - (app_nil_l [AI_trap]).
    rewrite - (app_nil_r [AI_trap]).
    iApply (wp_wand_ctx with "[Hf]"). iApply (wp_trap_ctx with "Hf"). done.
    iIntros (w) "[-> Hf]".
    iExists _. iFrame. iIntros "Hf".
    iApply (wp_wand with "[Hf]"). 
    iApply (wp_frame_trap with "Hf").
    by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
    iIntros (w) "[-> Hf]". iFrame. iSplitR. by iLeft; iLeft.
    iExists _,_. iFrame. iApply "Hrestitute".
    iExists _; iFrame. done. } 
  
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [ ]⌝ ∗ ↪[frame] _)%I).
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
  instantiate (1 := λ x, (⌜ x = immV [_] ⌝ ∗ ↪[frame] _)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  iApply (wp_get_local with "[] [$Hf]") => //=.
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite (separate2 (AI_handle _)).
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf Ha Htok".

  iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
  iMod (cinv_acc with "Hinv Htok") as "((%tbs & >%Htbs & >Hss & Haddrs) & Htok & Hclose)"; first by set_solver. 
  iModIntro. rewrite - (N2Nat.id base'). 
  iDestruct (wss_select (N.to_nat base') (N.to_nat bound') (N.to_nat (handle_addr h)) 4 with "Hss") as "(%Hlentake & Hss & Hrestore)".
  unfold handle_addr. lia. unfold handle_addr. simpl in Hbound. lia.
  done.
  repeat rewrite N2Nat.id.
  iApply (wp_wand with "[Hss Ha Hf]"). 
  iApply (wp_segload_deserialize with "[$Hf $Ha $Hss]") => //.
  iIntros "!> H".
  instantiate (1 := λ x, (⌜ x = immV _ ⌝%I ∗ _)%I).
  iSplit; [done | iExact "H"].
  iIntros (w) "[(-> & Ha & Hss) Hf]".
  iMod ("Hclose" with "[Hrestore Hss Haddrs]").
  iNext. iExists tbs. 
  iDestruct ("Hrestore" with "[] Hss") as "Hss".
  done. iFrame. iSplit; first done.
  rewrite cat_app reconstitute. done.
  iModIntro. iFrame.
  instantiate (1 := λ x, (∃ v, ⌜ x = immV [VAL_int32 v] ⌝ ∗ _)%I).
  iCombine "Htok Ha" as "H".
  iExists _. iSplit; [done | iExact "H"].
  iIntros (w) "[(%v' & -> & Htok & Ha) Hf]".
  2: by iIntros "[(%v' & % & _) _]". 


  iSimpl.
  rewrite (separate2 (AI_basic _)).
  iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [_] ⌝
                                      ∗ ↪[frame] _)%I)).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  fold_const; iApply (wp_tee_local with "Hf").
  iIntros "!> Hf".
  rewrite (separate1 (AI_const _)).
  iApply wp_val_app => //.
  iSplitR ; first by iIntros "!> [%Habs _]".
  iApply (wp_set_local with "[]Hf") => //.
  simpl. lia. 
  
  iIntros (w) "[-> Hf]".
  iSimpl. 
  rewrite (separate2 (AI_basic _)).
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf".
  rewrite (separate1 (AI_basic _)).
  iApply wp_val_app => //.
  iSplitR; last first.
  iApply wp_wand_r. iSplitL. iApply (wp_get_local with "[] Hf"). done.
  by instantiate (1 := λ x, (⌜ x = immV [_] ⌝)%I).
  iIntros (w) "[-> Hf]".
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
  iFrame. done.
  by iIntros "!> [% _]". 
  2: by iIntros "[% _]".
  
  iIntros (w) "[-> Hf]". iSimpl.
  rewrite separate3.
  destruct (handle_add h (Wasm_int.Z_of_sint i32m v')) eqn:Hhadd.

  (* Case E: handleadd fails *)
  2:{ iApply (wp_wand with "[Hf]").
      iApply (wp_seq_trap with "[$Hf]").
      iSplitR; last first.
      iIntros "Hf". iApply (wp_handleadd_failure with "Hf").
      done. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      by iIntros "!>" (w) "%".
      iIntros (w) "[-> Hf]".
       iSimpl.
       rewrite - (app_nil_l [AI_trap]).
       rewrite - (app_nil_r [AI_trap]).
       iApply (wp_wand_ctx with "[Hf]"). iApply (wp_trap_ctx with "Hf"). done.
       iIntros (w) "[-> Hf]".
       iExists _. iFrame. iIntros "Hf".
       iApply (wp_wand with "[Hf]"). 
       iApply (wp_frame_trap with "Hf").
       by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
       iIntros (w) "[-> Hf]". iFrame. iSplitR. by iLeft; iLeft.
       iExists _,_. iFrame. iApply "Hrestitute".
       iExists _; iFrame. done. } 
                                       

  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf".
  fold_const. iApply (wp_handleadd with "Hf").
  done. by instantiate ( 1 := λ x, ⌜ x = immV _ ⌝%I).
  2: by iIntros "[% _]".
  unfold handle_add in Hhadd. destruct (_ >=? _)%Z => //.
  
  iIntros (w) "[-> Hf]". iSimpl.
  destruct (offset h0 + N.of_nat (t_length T_i32) <=? bound h0)%N eqn:Hbound0.
  (* Case F: the new offset is OOB *)
  2:{ rewrite (separate2 (AI_handle _)).
      iApply (wp_wand with "[Hf]").
      iApply (wp_seq_trap with "[$Hf]").
      iSplitR; last first. 
      iIntros "Hf".
      iApply wp_segload_failure1.
      right; left. apply N.leb_gt in Hbound0. lia.
      iFrame. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      by iIntros "!>" (w) "->". 
      iIntros (w) "[-> Hf]".
      iSimpl.
      rewrite - (app_nil_l [AI_trap]).
      rewrite - (app_nil_r [AI_trap]).
      iApply (wp_wand_ctx with "[Hf]").
      iApply (wp_trap_ctx with "Hf"). done.
      iIntros (?) "[-> Hf]".
      iExists _. iFrame.
      iIntros "Hf".
      iSimpl. iApply (wp_wand with "[Hf]").
      iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iSplitR. by iLeft; iLeft.
      iFrame. iExists _,_. iFrame. iApply "Hrestitute".
      iExists _; iFrame. done.
  }
  apply N.leb_le in Hbound0.
  rewrite (separate2 (AI_handle _)).
  iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf Ha Htok".

  iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
  iMod (cinv_acc with "Hinv Htok") as "((%tbs & >%Htbs & >Hss & Haddrs) & Htok & Hclose)"; first by set_solver. 
  iModIntro. rewrite - (N2Nat.id base'). 
  iDestruct (wss_select (N.to_nat base') (N.to_nat bound') (N.to_nat (handle_addr h0)) 4 with "Hss") as "(%Hlentake & Hss & Hrestore)".
  unfold handle_addr. inversion Hhadd; subst. simpl. lia.
  unfold handle_addr. inversion Hhadd; subst. simpl. simpl in Hbound0. simpl in Hbound. lia.
  done.
  repeat rewrite N2Nat.id.
  iApply (wp_wand with "[Hss Ha Hf]"). 
  iApply (wp_segload_deserialize with "[$Hf Ha $Hss]") => //.
  inversion Hhadd; subst => //.
  replace (id h0) with (id h); last by inversion Hhadd; subst. iFrame.
  
  iIntros "!> H".
  instantiate (1 := λ x, (⌜ x = immV _ ⌝%I ∗ _)%I).
  iSplit; [done | iExact "H"].
  iIntros (w) "[(-> & Ha & Hss) Hf]".
  iMod ("Hclose" with "[Hrestore Hss Haddrs]").
  iNext. iExists tbs. 
  iDestruct ("Hrestore" with "[] Hss") as "Hss".
  done. iFrame. iSplit; first done.
  rewrite cat_app reconstitute. done.
  iModIntro. iFrame.
  instantiate (1 := λ x, (∃ v, ⌜ x = immV [VAL_int32 v] ⌝ ∗ _)%I).
  iCombine "Htok Ha" as "H".
  iExists _. iSplit; [done | iExact "H"].
  iIntros (w) "[(%v'' & -> & Htok & Ha) Hf]".
  2: by iIntros "[(%v'' & % & _) _]".
  iSimpl.

  rewrite (separate2 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  rewrite (separate1 (AI_basic _)).
  iApply wp_val_app => //.
  iSplitR ; first by iIntros "!> [%Habs _]".
  
  iApply (wp_get_local with "[] [$Hf]") => //=. 
    
  iIntros (w) "[-> Hf]".
  iSimpl.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                    ↪[frame] _)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  rewrite (separate2 (AI_basic _)).
  iApply wp_val_app => //.
  iSplitR ; first by iIntros "!> [%Habs _]".
  iApply (wp_get_local with "[] [$Hf]") => //=.

  iIntros (w) "[-> Hf]".
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
  iSimpl.


  iIntros (w) "[-> Hf]".
  iSimpl.
  iApply (wp_wand with "[Hf Ha Htok]").

  rewrite (separate1 (AI_basic _)).
  iApply wp_val_app => //.
  iSplit ; last first.
  iApply (wp_wand with "[-]").

  iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
  iMod (cinv_acc with "Hinv Htok") as "((%tbs & >%Htbs & >Hss & Haddrs) & Htok & Hclose)"; first by set_solver. 
  iModIntro. rewrite - (N2Nat.id base'). 
  iDestruct (wss_select (N.to_nat base') (N.to_nat bound') (N.to_nat (handle_addr h)) 4 with "Hss") as "(%Hlentake & Hss & Hrestore)".
  unfold handle_addr. lia.
  unfold handle_addr. simpl in Hbound0. simpl in Hbound. lia.
  done.
  repeat rewrite N2Nat.id.
  iApply (wp_wand with "[Hss Ha Hf]"). 
  fold_const. iApply (wp_segstore with "[$Hf $Ha $Hss]") => //.
  
  iIntros "!> H".
  instantiate (1 := λ x, (⌜ x = immV _ ⌝%I ∗ _)%I).
  iSplit; [done | iExact "H"].
  iIntros (w) "[(-> & Ha & Hss) Hf]".
  iMod ("Hclose" with "[Hrestore Hss Haddrs]").
  iNext. iExists _. 
  iDestruct ("Hrestore" with "[] Hss") as "Hss".
  done. iFrame. iSplit; first iPureIntro.
  do 2 rewrite cat_app. do 2 rewrite app_length. rewrite map_length.
  rewrite (length_bits _ T_i32); last done. rewrite drop_length.
  rewrite take_length_le. unfold handle_addr. simpl in Hbound. simpl in Hbound0.
  simpl. lia. unfold handle_addr. lia.

  { 
 iIntros (addr) "%Haddr".
 (* We must show that knowning addr is handle-aligned, it either doesn't store
    a handle, or stores a valid one *)
 destruct (handle_addr h - base' + N.of_nat (t_length T_i32) <=? addr)%N eqn:Hlo.
              
  -- (* Case 1: the place where we wrote to memory is before addr *)
    (* I.e. the previous invariant still holds *)
    apply N.leb_le in Hlo.
    iDestruct ("Haddrs" $! addr Haddr) as "[%Hnum | Hvalid]";
      destruct Haddr as [Hmod Haddr].
    ++ iLeft. 
       iPureIntro.
       destruct Hnum as (addr' & b & Haddr' & Hnum).
       exists addr', b. split; first done.
       rewrite lookup_app.
       rewrite lookup_take_ge; last lia.
       rewrite cat_app. rewrite lookup_app.
       rewrite lookup_ge_None_2.
       2:{ rewrite map_length take_length_le; try lia.
           rewrite (length_bits _ T_i32) => //. lia. }
       rewrite lookup_drop.
       rewrite map_length take_length_le; try lia.
       rewrite (length_bits _ T_i32) => //.
       replace  (N.to_nat (handle_addr h) - N.to_nat base' + t_length T_i32 +
                   (N.to_nat (addr + addr') - (N.to_nat (handle_addr h) - N.to_nat base') -
                      t_length T_i32)) with (N.to_nat (addr + addr')); first done.
       lia.
    ++ iRight.
       rewrite catA.
       rewrite drop_app_ge.
       2:{ rewrite app_length map_length take_length_le; try lia.
           rewrite (length_bits _ T_i32) => //. lia. } 
       rewrite drop_drop.
       rewrite app_length map_length take_length_le; last lia.
       rewrite (length_bits _ T_i32) => //.
       rewrite - le_plus_minus. done. simpl in Hlo. lia. 
  -- apply N.leb_gt in Hlo.
     destruct (addr + handle_size <=? handle_addr h - base')%N eqn:Hhi.
     ++ (* Case 2: the place where we wrote is far after addr *)
       (* i.e. the previous invariant still holds *)
       apply N.leb_le in Hhi.
       iDestruct ("Haddrs" $! addr Haddr) as "[%Hnum | Hvalid]";
                    destruct Haddr as [Hmod Haddr].
       ** iLeft. 
          iPureIntro.
          destruct Hnum as (addr' & b & Haddr' & Hnum).
          exists addr', b. split; first done.
          rewrite lookup_app.
          rewrite lookup_take; last lia.
          rewrite Hnum. done.
       ** iRight. 
          rewrite drop_app_le.
          2:{ rewrite take_length. lia. }
          
          rewrite take_app_le.
          2:{ rewrite drop_length take_length. lia. }
          rewrite take_drop_take => //.
          lia.
          
     ++ (* Case 3: the place where we wrote is right after addr *)
       (* I.e. we know that a handle isn't stored there -- we just wrote
                    a numerical value *)
       apply N.leb_gt in Hhi.
       iLeft.
       iPureIntro. specialize hsnz as Hsize. rewrite nat_bin in Hsize.
       destruct (overlap addr handle_size (handle_addr h - base') (N.of_nat (t_length T_i32))) as (y & ? & ? & ? & ?); try lia; try by destruct t. done. 
       assert (N.to_nat (addr + (y - addr)) - (N.to_nat (handle_addr h) - N.to_nat base') < length (bits (VAL_numeric (NVAL_int32 (Wasm_int.Int32.isub v' (Wasm_int.Int32.repr 4)))))) as Hbits.
       { rewrite (length_bits _ T_i32) => //. lia. }
       apply lookup_lt_Some_inv in Hbits as [b Hb].
       exists (y - addr)%N, b.
       split; first lia.
       rewrite lookup_app.
       rewrite lookup_take_ge; last lia.
       rewrite cat_app.
       rewrite lookup_app.
       rewrite take_length_le; last lia.
       rewrite lookup_map. rewrite Hb. done. } 

  iFrame. instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
  iModIntro. iCombine "Htok Ha" as "H". iSplit; [done | iExact "H"].

  iIntros (w) "[(-> & Htok & Ha) Hf]".
  instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
  iCombine "Htok Ha Hf" as "H". iSplit; [done | iExact "H"].
  by iIntros "!> [% _]".
  iIntros (w) "(-> & Htok & Ha & Hf)".
  iSimpl.
  
  iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
  iApply wp_wasm_empty_ctx.
  iApply (wp_wand with "[Hf]"). iApply (wp_label_value with "Hf").
  done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]". iExists _. iFrame. iIntros "Hf".
  iApply (wp_wand with "[Hf]"). iApply (wp_frame_value with "Hf").
  done. done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  iIntros (w) "[-> Hf]". iFrame. iSplitR.
  iLeft. iRight. iExists [_]. iSplit; first done.
  iSimpl. iSplit; last done. iExists _. done.
  iExists _, _. iFrame. iApply "Hrestitute".
  iExists _. iFrame. done.  
Qed.    

End pop_robust.
