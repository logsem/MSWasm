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

 
    
  (* ----------------------------------------- SEGFREE ---------------------------------------- *)


  Lemma typing_segfree C : 
    ⊢ semantic_typing C (to_e_list [BI_segfree]) (Tf [T_handle] []).
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
    rewrite fixpoint_interp_value_handle_eq.
     iDestruct "Hv" as (h) "(-> & [%Hval | (%γ & %base' & %bound' & #Hw & %Hbase & %Hbound & #Hinv)])".
    { iApply (wp_wand with "[Hf]").
        - iApply (wp_segfree_failure_1 with "[$Hf]"). 
          + by right.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame. } 



    destruct (valid h) eqn:Hvalid.
    2: { iApply (wp_wand with "[Hf]").
        - iApply (wp_segfree_failure_1 with "[$Hf]"). 
          + by right.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame. }

    destruct (offset h =? 0)%N eqn:Hoff.
    2:{ apply N.eqb_neq in Hoff. iApply (wp_wand with "[Hf]").
      - iApply (wp_segfree_failure_1 with "[$Hf]"). 
        + by left.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _, _. iFrame. }
    apply N.eqb_eq in Hoff.

    
    
    iDestruct "Hfv" as "[(%fall & Hbl & Htoks) Hfv]".
    iDestruct (gamma_agree with "Hw Hbl") as "%Hγ".
    rewrite - (insert_delete _ _ _ Hγ).
    iDestruct (big_sepM_insert with "Htoks") as "[(%Hx & Ha & Hown) Htoks]";
      first by rewrite lookup_delete.
    iApply fupd_wp. Check ghost_map_delete.  Search (ghost_map_auth _ _ (delete _ _)).
    unfold gamma_id_white.
    Search (_ ↪[_]□ _ -∗ _ ↪[_] _)%I.
    iMod (ghost_map_delete with "Hbl [Hw]").
    { unfold gamma_id_white. iExact "Hw".
    destruct (base' =? base h)%N eqn:Hnbase.
    2:{ apply N.eqb_neq in Hnbase. iApply (wp_wand with "[Hf Ha]").
        - iApply (wp_segfree_failure_2 with "[$Hf $Ha]") => //; try by left.
          iNext. iIntros "Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
          iSplit; first done. iExact "Ha".
        - iIntros (v) "[[-> Ha] Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame.
          iExists _. iFrame. admit.  (*rewrite insert_delete => //. 
          iDestruct (big_sepM_insert. iApply "Htoks". iFrame. done. *)
    }
(*    destruct (n0 =? bound h)%N eqn:Hnbound.
    2:{ apply N.eqb_neq in Hnbound. iApply (wp_wand with "[Hf Ha]").
        - iApply (wp_segfree_failure_2 with "[$Hf $Ha]") => //; try by right.
          iNext. iIntros "Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
          iSplit; first done. iExact "Ha".
        - iIntros (v) "[[-> Ha] Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame.
          iExists _. iFrame. iApply "Htoks". iExists _. iFrame. done.
    } *)
    iSimpl.
    apply N.eqb_eq in Hnbase as ->.
(*    apply N.eqb_eq in Hnbound as ->. *)
    iApply fupd_wp. 
    iMod (cinv_cancel with "Hinv Hown") as "(%tbs & >%Htbs & >Hss & #Hhandles)"; first solve_ndisj.
      iDestruct (wss_select (N.to_nat (base h)) (N.to_nat bound') (N.to_nat (handle_addr h)) (N.to_nat bound') tbs with "[Hss]") 
        as "(%Htbs' & Hss & Hreconstitute)";
        try rewrite N2Nat.id;
        try done;
        try by subst; unfold handle_addr; lia.
      unfold handle_addr. rewrite Hoff N.add_0_r.
      unfold handle_addr in Htbs'. rewrite Hoff N.add_0_r in Htbs'. 
    iModIntro.
    iApply (wp_wand with "[Hf Ha Hss]").
    { iApply (wp_wand with "[Hf Ha Hss]").
      - iApply (wp_segfree with "[$Hf $Hss $Ha]") => //.
        by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
      - iIntros (v) "[-> Hf]". instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ ↪[frame] f)%I).
        by iFrame. }
    iIntros (v) "[-> Hf]".
    iSplitR.
    - iLeft; iRight. iExists _. iSplit => //. 
    - iExists _,_. iFrame. iExists _. iFrame "Htoks".
      Search "ghost_map_del".
      admit.
      
    
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
