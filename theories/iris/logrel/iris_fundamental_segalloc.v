From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules.
Require Export datatypes operations properties opsem typing.
Require Export iris_logrel iris_fundamental_helpers.
Import uPred.
  
Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ, HHB: HandleBytes, cancelg : cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
                                                           
    
    
    
  (* ----------------------------------------- SEGALLOC ---------------------------------------- *)


  Lemma typing_segalloc C : 
    ⊢ semantic_typing C (to_e_list [BI_segalloc]) (Tf [T_i32] [T_handle]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i all lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _,_. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|wh ws];[done|destruct ws; last done].  
    iSimpl in "Hv". iDestruct "Hv" as "(Hv & _)".
    iDestruct "Hv" as (z) "->".

    iSimpl.
    iApply wp_fupd.
    iApply (wp_wand with "[Hf]").
    { iApply (wp_segalloc with "[$Hf]") => //.
      iIntros "!>" (w) "H". iExact "H". }
    iIntros (v) "[(%h & -> & [-> | (Ha & %Hbound & %Hoff & %Hvalid & Hss)]) Hf]".
    - (* Segalloc failed *)
      iSplitR "Hf Hfv".
      + iLeft; iRight. iExists _. iModIntro. iSplit; first done. iSplit; last done.
        rewrite fixpoint_interp_value_handle_eq.
        iExists _. iSplit; first done. by iLeft.
      + iExists _, _. iModIntro. iFrame. 
    - (* Segalloc succeeded *)
      iAssert (▷ ∃ tbs, ⌜ length tbs = N.to_nat (bound h) ⌝ ∗ ↦[wss][base h] tbs ∗
                                       ∀ addr,  ⌜ (N.modulo (base h + addr) handle_size = 0 /\
                                                     addr + handle_size <= bound h )%N ⌝ -∗
                                                  ⌜ exists addr' (b: byte), (addr' < handle_size)%N  /\
                                                                         tbs !! (N.to_nat (addr + addr')%N) = Some (b, Numeric) ⌝ ∨
                                                                         interp_value_handle (VAL_handle (handle_of_bytes (map fst (take (N.to_nat handle_size) (drop (N.to_nat addr) tbs))))))%I with "[Hss]" as "Hinv".
      { iExists _. iFrame "Hss". iSplit.
        - iPureIntro. rewrite repeat_length Hbound. done.
        - iIntros (addr) "%Haddr". iLeft. iPureIntro. exists 0%N, #00%byte.
          specialize hsnz as H. rewrite nat_bin in H.
          split; first lia. apply repeat_lookup.
          lia. }
      iMod (cinv_alloc with "Hinv") as (γ) "[#Hinv Htok]".
      iDestruct "Hfv" as "[(%fall & Hbl & Htoks) Hfv]".
      destruct (fall !! id h) eqn:Hidh.
      { iDestruct (big_sepM_lookup_acc with "Htoks") as "[(%x & _ & Habs & _) ?]"; first done.
        iDestruct (ghost_map_elem_combine with "Ha Habs") as "[Habs _]".
        iDestruct (ghost_map_elem_valid with "Habs") as "%Habs".
        done. } 
      iMod (ghost_map_insert_persist _ γ with "Hbl") as "[Hbl #Hw]"; first done.
      iModIntro.
      iSplitR.
      + iLeft; iRight. iExists _. iSplit; first done. iSplit; last done.
        rewrite fixpoint_interp_value_handle_eq.
        iExists _. iSplit; first done. iRight.
        iExists γ, (base h), (bound h). iFrame "Hw Hinv".
        iSplit; iPureIntro; lia.
      + iExists _, _. iFrame "Hf Hfv".
        iExists _. iFrame "Hbl".
        iApply big_sepM_insert; first done.
        iSplitR "Htoks".
        * iExists _. iFrame. iPureIntro.
          instantiate (1 := {| allocated := <[ id h := _ ]> (allocated all); next_free := next_free all |}).
          simpl. rewrite lookup_insert. done.
        * iApply big_sepM_mono; last done.
          iIntros (k x Hx) "(%y & %Hy & Ha & Htok)".
          iExists _. iFrame. iPureIntro.
          simpl. rewrite lookup_insert_ne => //.
          intros Habs; rewrite Habs Hx in Hidh.  done.
  Qed. 


End fundamental.
