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


  Context `{!wasmG Σ, !logrel_na_invs Σ, HHB: HandleBytes, cancelg : cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

 
    
  (* ----------------------------------------- SEGFREE ---------------------------------------- *)


  Lemma typing_segfree C : 
    ⊢ semantic_typing C (to_e_list [BI_segfree]) (Tf [T_handle] []).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f all vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _,_. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|wh ws];[done|destruct ws; last done].  
    iSimpl in "Hv". iDestruct "Hv" as "(Hv & _)".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv" as (h) "(-> & [%Hval | (%γ & %base' & %bound' & %base_all & %bound_all & %q & %Hq & #Hw & %Hbase_all & %Hbase & %Hbound_all & %Hbound & #Hinv)])".
    { iApply (wp_wand with "[Hf]").
        - iApply (wp_segfree_failure1 with "[$Hf]"). 
          + by right.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame. } 



    destruct (handle.valid h) eqn:Hvalid.
    2: { iApply (wp_wand with "[Hf]").
        - iApply (wp_segfree_failure1 with "[$Hf]"). 
          + by right.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame. }

    destruct (offset h =? 0)%N eqn:Hoff.
    2:{ apply N.eqb_neq in Hoff. iApply (wp_wand with "[Hf]").
      - iApply (wp_segfree_failure1 with "[$Hf]"). 
        + by left.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _, _. iFrame. }
    apply N.eqb_eq in Hoff.

    
    
    iDestruct "Hall" as "(%fall & Hbl & Htoks)".
    iDestruct (gamma_agree with "Hw Hbl") as "%Hγ".
    rewrite - (insert_delete _ _ _ Hγ).

    iDestruct (big_sepM_insert with "Htoks") as "[(%y & %Hy & Halloc & Htok) Htoks]";
      first by rewrite lookup_delete. 
    destruct y as [[base0 bound0]|] ; first iDestruct "Htok" as "(-> & -> & Htok)". 
    2:{ 
        iApply (wp_wand with "[Hf Halloc]").
        - iApply (wp_segfree_failure3 with "[$Hf $Halloc]").
          iIntros "!> Ha".
          instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
          iSplit; last iExact "Ha". done.
        - iIntros (v) "[[-> Ha] Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_.
          iFrame. iExists _. iFrame "Hbl".
          iApply big_sepM_insert; first by rewrite lookup_delete.
          iFrame. iExists None. iFrame. done. } 
    
    destruct (base0 =? base h)%N eqn:Hnbase.
    2:{ apply N.eqb_neq in Hnbase. iApply (wp_wand with "[Hf Halloc]").
        - iApply (wp_segfree_failure2 with "[$Hf $Halloc]") => //; try by left.
          iNext. iIntros "Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
          iSplit; first done. iExact "Ha".
        - iIntros (v) "[[-> Ha] Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame.
          iExists _. iFrame "Hbl". iApply big_sepM_insert; first by rewrite lookup_delete.
          iFrame. 
          iExists (Some (_,_)). iFrame. done.
    }

    iSimpl.
    apply N.eqb_eq in Hnbase as ->.
    destruct (bound0 =? bound h)%N eqn:Hnbase.
    2:{ apply N.eqb_neq in Hnbase. iApply (wp_wand with "[Hf Halloc]").
        - iApply (wp_segfree_failure2 with "[$Hf $Halloc]") => //; try by right.
          iNext. iIntros "Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
          iSplit; first done. iExact "Ha".
        - iIntros (v) "[[-> Ha] Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame.
          iExists _. iFrame "Hbl". iApply big_sepM_insert; first by rewrite lookup_delete.
          iFrame. 
          iExists (Some (_,_)). iFrame. done.
    }

    iSimpl.
    apply N.eqb_eq in Hnbase as ->.
    iApply fupd_wp.
    iMod (cinv_cancel with "Hinv Htok") as "(%tbs & >%Htbs & >Hss & #Hhandles)"; first solve_ndisj.

    
    iDestruct (wss_select (N.to_nat base') (N.to_nat bound') (N.to_nat (handle_addr h)) (N.to_nat (bound h)) tbs with "[Hss]") 
        as "(%Htbs' & Hss & Hreconstitute)";
        try rewrite N2Nat.id;
        try done;
        try by subst; unfold handle_addr; lia.
    unfold handle_addr. rewrite Hoff N.add_0_r.
    unfold handle_addr in Htbs'. rewrite Hoff N.add_0_r in Htbs'. 
    iModIntro.
    simpl in Hq. subst q. 
    iApply (wp_wand with "[Hf Halloc Hss]").
    
    - iApply (wp_segfree with "[$Hf $Hss $Halloc]") => //.
      instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ _)%I).
      iIntros "!> Ha". iSplit; last iExact "Ha". done.
    - iIntros (v) "[[-> Ha] Hf]".
      iSplitR.
      + iLeft; iRight. iExists _. iSplit => //. 
      + iExists _,({| allocated := <[ id h := None ]> (allocated all); next_free := next_free all |}). iFrame.
        iExists _. iFrame.
        iApply big_sepM_insert; first by rewrite lookup_delete.
        iSplitL "Ha".
        * iExists None. iFrame. 
          by rewrite lookup_insert.
        * iApply (big_sepM_impl with "[Htoks]"); first done.
          iIntros "!>" (k [[[??]?]?]) "%Hx (%y & %Hy' & Hall & H)".
          iExists y. iFrame. iPureIntro.
          simpl. destruct (N.eqb k (id h)) eqn:Hkid.
          -- apply N.eqb_eq in Hkid as ->.
             by rewrite lookup_delete in Hx.
          -- apply N.eqb_neq in Hkid.
             rewrite lookup_insert_ne => //.
  Qed. 

End fundamental.
