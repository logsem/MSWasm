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

 
(*  Lemma wss_select_nat a b a' b' tbs:
    (a' >= a) -> (a' + b' <= a + b) -> length tbs = b ->
    ↦[wss][ N.of_nat a ] tbs -∗
      ∃ tbs', ⌜ (length tbs') = b' ⌝ ∗
                                ↦[wss][ N.of_nat a' ] tbs' ∗
                                (↦[wss][ N.of_nat a' ] tbs' -∗ ↦[wss][ N.of_nat a ] tbs).
  Proof.
    iIntros (Ha Hb Htbs) "Hs".
    rewrite - (take_drop (a' - a) tbs).
    rewrite - (take_drop b' (drop (a' - a) tbs)).
    iDestruct (big_sepL_app with "Hs") as "[Hbegin Hs]".
    iDestruct (big_sepL_app with "Hs") as "[Hs Hend]".
    iExists (take b' (drop (a' - a) tbs)).
    iSplit.
    - iPureIntro. rewrite take_length_le; first done.
      rewrite drop_length Htbs. lia.
    - iSplitL "Hs".
      + iApply (big_sepL_impl with "[Hs]"); first done.
        iIntros "!>" (k x) "%Hx Hs".
        rewrite take_length_le; last lia. repeat rewrite Nat2N.id.
        replace (a + (a' - a + k)) with (a' + k); first done.
        lia.
      + iIntros "Hs".
        iApply (big_sepL_app with "[$Hbegin Hs Hend]").
        iApply (big_sepL_app with "[Hend Hs]").
        iSplitL "Hs"; last done.
        iApply (big_sepL_impl with "[Hs]"); first done.
        iIntros "!>" (k x) "%Hx Hs".
        rewrite take_length_le; last lia. repeat rewrite Nat2N.id.
        replace (a + (a' - a + k)) with (a' + k); first done.
        lia.
  Qed.

    Lemma wss_select a b a' b' tbs:
    (a' >= a)%N -> (a' + b' <= a + b)%N -> N.of_nat (length tbs) = b ->
    ↦[wss][ a ] tbs -∗
      ∃ tbs', ⌜ N.of_nat (length tbs') = b' ⌝ ∗
                                ↦[wss][ a' ] tbs' ∗
                                (↦[wss][ a' ] tbs' -∗ ↦[wss][ a ] tbs).
    Proof.
      iIntros (Ha Hb Htbs) "Hs".
      iDestruct (wss_select_nat (N.to_nat a) (N.to_nat b) (N.to_nat a') (N.to_nat b') tbs
                  with "[Hs]") as "(%tbs' & % & ?)"; try lia.
      - by rewrite N2Nat.id.
      - repeat rewrite N2Nat.id. iExists tbs'. iFrame.
        iPureIntro. lia.
    Qed.  *)

        
                                                           
    
    
    
  (* ----------------------------------------- SEGFREE ---------------------------------------- *)


  Lemma typing_segload C t : 
    ⊢ semantic_typing C (to_e_list [BI_segfree t]) (Tf [T_handle] []).
  Proof.
  Admitted. 
(*    unfold semantic_typing, interp_expression.
    iIntros (i all lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws];[done|destruct ws;[|done]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv" as (h γ base' bound') "(-> & #Hw & %Hbase & %Hbound & #Hinv)".

    iSimpl.



    destruct (valid h) eqn:Hvalid.
    2:{ iApply (wp_wand with "[Hf]").
        - iApply (wp_segload_failure with "[$Hf]").
          + by left.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _. iFrame. } 

    destruct (bound h <? offset h + N.of_nat (t_length t))%N eqn:Hbounds.
    { apply N.ltb_lt in Hbounds.
      iApply (wp_wand with "[Hf]").
      - iApply (wp_segload_failure with "[$Hf]").
        + by right; left; lia.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _. iFrame. } 
    apply N.ltb_ge in Hbounds.

    iDestruct "Hfv" as "[Halloc Hfv]".
    iDestruct "Halloc" as (γmap) "[Hbl Htok]".
    iApply fupd_wp. 
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iDestruct (gamma_agree with "Hw Hbl") as "%Hid".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hid with "Htok") as "[(%x & %Hx & Halloc & Htok) Htoks]".
    iMod (cinv_acc with "Hinv Htok") as "(Hss & Hwon & Hcls)"; first solve_ndisj.
    iDestruct "Hss" as (tbs) "(>%Htbs & >Hss & Hhandles)".
    iDestruct (wss_select base' bound' (handle_addr h) (N.of_nat (t_length t)) tbs with "Hss")
      as "(%tbs' & %Htbs' & Hss & Hreconstitute)"; try by subst; unfold handle_addr; lia.
    assert (length tbs' = t_length t) as Htbs''; first lia. 

    destruct t eqn:Ht.

    - (* Segload T_i32 *)
      iApply (wp_wand _ _ _ (λ vs, (⌜ vs = immV _ ⌝ ∗ _) ∗ _)%I with "[Hf Halloc Hss]"). 
      + iApply (wp_segload_deserialize with "[$Hf $Halloc $Hss]") => //.
      + iIntro (v) "(-> & Halloc & Hss)". iMod ("Hcls" with "[Hss Hhandles]"). iIntros (v).
    
    destruct (N_lt_dec (mem_length ms) ((Wasm_int.N_of_uint i32m z) + off + (N.of_nat (t_length t))))%N.
      { iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = trapV⌝ ∗ _) ∗ _)%I with "[Hsize Hf]").
        { by iApply (wp_load_failure with "[$Hf $Hsize]");[by rewrite Hlocs /=|by apply N.lt_gt|]. }
        iIntros (v) "[[-> Hsize] Hf]".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[by iLeft; iLeft|iExists _;iFrame].
        iExists _. eauto. 
      }
      { iDestruct (mem_extract _ (Wasm_int.N_of_uint i32m z + off) (t_length t) with "Hmem") as (bv) "[Ha [Hmem %Hlenbv]]";[destruct t;simpl;try lia; try apply hsnz|lia|].
        iApply wp_fupd.
        iApply (wp_wand _ _ _ (λ vs, (⌜vs = immV _⌝ ∗ _) ∗ _)%I with "[Ha Hf]").
        { iApply (wp_load_deserialize with "[$Hf $Ha]");eauto;by rewrite Hlocs /=. }
        iIntros (v) "[[-> Ha] Hf]".
        iDestruct ("Hmem" with "Ha") as "Hmem".
        iMod ("Hcls" with "[$Hown Hsize Hmem]") as "Hown".
        { iNext. iExists _. iFrame. }
        iModIntro.
        iSplitR;[iLeft; iRight|iExists _;iFrame;iExists _;eauto].
        iExists _. iSplit;[eauto|]. iSimpl.
        iSplit =>//. unfold interp_value.
        destruct t;iSimpl;eauto.
      }

    }
  Qed. *)

End fundamental.
