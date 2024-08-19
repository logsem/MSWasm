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


 
    Lemma forallb_false {A} f (l: list A) :
      (exists x, In x l /\ f x = false) -> forallb f l = false.
    Proof.
      induction l => //=.
      { intros (x & ? & _) => //. }
      intros (x & [-> | Hx] & Hfx).
      - rewrite Hfx. done.
      - rewrite IHl; first by destruct (f a).
        exists x; split => //.
    Qed. 


    Lemma lookup_Some_in {A B} l:
      forall i lo hi (x: A) (y: B),
      i >= lo -> i < lo + hi ->
      l !! i = Some (x, y) -> In y (map snd (take hi (drop lo l))).
    Proof.
      induction l; intros i lo hi x y Hlo Hhi Hlook => //=.
      destruct i.
      - simpl in Hlook. inversion Hlook; subst.
        destruct lo; last lia. simpl.
        destruct hi; first lia. simpl.
        by left.
      - simpl in Hlook.
        destruct hi; first lia.
        destruct lo.
        + simpl. right. 
          apply (IHl i 0 hi x y) in Hlook; try lia.
          done.
        + apply (IHl i lo (S hi) x y) in Hlook; try lia.
          simpl. done.
    Qed. 

  
    (* ----------------------------------------- SEGLOAD ---------------------------------------- *)

    
    Lemma typing_segload_numeric C t :
      t <> T_handle ->
    ⊢ semantic_typing C (to_e_list [BI_segload t]) (Tf [T_handle] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Ht i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f all vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _,_. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws];[done|destruct ws;[|done]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv" as (h) "(-> & [%Hval | (%γ & %base' & %bound' & %base_all & %bound_all & %q & %Hq & #Hw & %Hbase_all & %Hbase & %Hbound_all & %Hbound & #Hinv)])".
    { iApply (wp_wand with "[Hf]").
        - iApply (wp_segload_failure1 with "[$Hf]").
          + by left.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 
    iSimpl.

    destruct (handle.valid h) eqn:Hvalid.
    2:{ iApply (wp_wand with "[Hf]").
        - iApply (wp_segload_failure1 with "[$Hf]").
          + by left.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 

    destruct (bound h <? offset h + N.of_nat (t_length t))%N eqn:Hbounds.
    { apply N.ltb_lt in Hbounds.
      iApply (wp_wand with "[Hf]").
      - iApply (wp_segload_failure1 with "[$Hf]").
        + by right; left; lia.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 
    apply N.ltb_ge in Hbounds.
    
    iDestruct "Hall" as (γmap) "[Hbl Htok]".
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
    iDestruct (gamma_agree with "Hw Hbl") as "%Hid".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hid with "Htok") as "[(%y & %Hy & Halloc & Htok) Htoks]".
    destruct y as [[base0 bound0]|].
    2:{ iApply (wp_wand with "[Hf Halloc]").
        - iApply (wp_segload_failure2 with "[$Hf $Halloc]").
          iIntros "!> Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
          iSplit; first done. iExact "Ha".
        - iIntros (v) "[[-> Ha] Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame.
          iSplitR "Hbl Htoks Ha".
          + iExists _. iSplit; first done. done.
          + iExists _. iFrame.
            iApply "Htoks".
            iExists None. iFrame. done.
}
            
    iDestruct "Htok" as "(-> & -> & Htok)". 
    iApply (wp_wand _ _ _ (λ x, (( ∃ v, ⌜ x = immV [v] ⌝ ∗ interp_value t v) ∗ interp_frame (tc_local C) i f ∗ interp_allocator all) ∗ ↪[frame] f )%I with "[Hf Hbl Hown Halloc Htok Htoks]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
     
      iMod (cinv_acc with "Hinv Htok") as "(Hss & Hwon & Hcls)"; first solve_ndisj.
      iModIntro.
      iDestruct "Hss" as (tbs) "(>%Htbs & >Hss & #Hhandles)".
      iDestruct (wss_select (N.to_nat base') (N.to_nat bound') (N.to_nat (handle_addr h)) (t_length t) tbs with "[Hss]") 
        as "(%Htbs' & Hss & Hreconstitute)";
        try rewrite N2Nat.id;
        try done;
        try by subst; unfold handle_addr; lia.
      remember (take (t_length t) (drop (N.to_nat (handle_addr h) - N.to_nat base') tbs)) as tbs'.
      
      assert (length tbs' = t_length t) as Htbs''; first lia. 

      iApply (wp_wand _ _ _ (λ v,  (|={⊤ ∖ ↑wsN (id h),⊤}=>
       ((∃ v0 : value, ⌜v = immV [v0]⌝ ∗ interp_value t v0) ∗
          interp_frame (tc_local C) i f ∗ interp_allocator all)) ∗  ↪[frame]f)%I
               with "[ Hf Hbl Hown Halloc Htoks Hwon Hcls Hss Hreconstitute]").
      2:{ iIntros (v) "[??]"; iFrame. } 
      iApply wp_segload_deserialize => //.
      iSplitR "Halloc Hss Hf"; last by iFrame.
      iNext. iIntros "(Hid & Hss)".
      iDestruct ("Hreconstitute" $! tbs' Htbs' with "Hss") as "Hss".
      subst tbs'.
      rewrite cat_app reconstitute N2Nat.id.
      iMod ("Hcls" with "[Hss]").
      + iNext. iExists tbs. iFrame "Hhandles Hss". done.
      + iModIntro. 
        iSplitR.
        * iExists _. 
          iSplit; first done. destruct t; try done; by iExists _.
        * iSplitL "Hown".
          -- iExists _. iFrame. iSplit; done.
          -- iExists _. iFrame. iApply ("Htoks" with "[Hwon Hid]").
             iExists _.
             iFrame. done.

    }
     iIntros (v) "[((%v0 & -> & Hv) & Hfv) Hf]".
    iSplitL "Hv".
      + iLeft. iRight. iExists _. iSplit; first done. iFrame. done.
      + iExists _,_. iFrame.
  Qed. 
        

  Lemma typing_segload C t : 
    ⊢ semantic_typing C (to_e_list [BI_segload t]) (Tf [T_handle] [t]).
  Proof.
    destruct t; try by apply typing_segload_numeric.
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
    destruct ws as [|w ws];[done|destruct ws;[|done]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv" as (h) "(-> & [%Hval | (%γ & %base' & %bound' & %base_all & %bound_all & %q & %Hq & #Hw & %Hbase_all & %Hbase & %Hbound_all & %Hbound & #Hinv)])".
    { iApply (wp_wand with "[Hf]").
      - iApply (wp_segload_failure1 with "[$Hf]").
        + by left.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _,_. iFrame. } 
    iSimpl.

    destruct (handle.valid h) eqn:Hvalid.
    2:{ iApply (wp_wand with "[Hf]").
        - iApply (wp_segload_failure1 with "[$Hf]").
          + by left.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 

    destruct (bound h <? offset h + N.of_nat (t_length T_handle))%N eqn:Hbounds.
    { apply N.ltb_lt in Hbounds.
      iApply (wp_wand with "[Hf]").
      - iApply (wp_segload_failure1 with "[$Hf]").
        + by right; left; lia.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _,_. iFrame. } 
    apply N.ltb_ge in Hbounds.
    destruct ((handle_addr h `mod` handle_size)%N =? N.of_nat 0)%N eqn:Hmod.
    2:{  iApply (wp_wand with "[Hf]").
         - iApply (wp_segload_failure1 with "[$Hf]").
           + right; right; split => //. intros Habs.
             rewrite Habs in Hmod. simpl in Hmod. done.
           + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
         - iIntros (v) "[-> Hf]".
           iSplitR; first by do 2 iLeft.
           iExists _,_. iFrame. } 
      iDestruct "Hall" as (γmap) "[Hbl Htok]".
      iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
      iDestruct (gamma_agree with "Hw Hbl") as "%Hid".
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hid with "Htok") as "[(%y & %Hy & Halloc & Htok) Htoks]".
      destruct y as [[base0 bound0]|] ; first iDestruct "Htok" as "(-> & -> & Htok)". 
      2:{
        iApply (wp_wand with "[Hf Halloc]").
        - iApply (wp_segload_failure2 with "[$Hf $Halloc]").
          iIntros "!> Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
          iSplit; first done. iExact "Ha".
        - iIntros (v) "[[-> Ha] Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _, _. iFrame.
          iSplitR.
          + iExists _. iSplit => //.  
          + iExists _. iFrame. iApply "Htoks". iExists None.
            iFrame. done.
      }
          
    iApply (wp_wand _ _ _ (λ x, ((∃ v, ⌜ x = immV [v] ⌝ ∗ interp_value T_handle v) ∗ interp_frame (tc_local C) i f ∗ interp_allocator all) ∗ ↪[frame] f )%I with "[Hf Hbl Hown Halloc Htok Htoks]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
     
      iMod (cinv_acc with "Hinv Htok") as "(Hss & Hwon & Hcls)"; first solve_ndisj.
      iModIntro.
      iDestruct "Hss" as (tbs) "(>%Htbs & >Hss & #Hhandles)".
      iDestruct (wss_select (N.to_nat (base')) (N.to_nat (bound')) (N.to_nat (handle_addr h)) (t_length T_handle) tbs with "[Hss]") 
        as "(%Htbs' & Hss & Hreconstitute)";
        try rewrite N2Nat.id;
        try done;
        try by subst; unfold handle_addr; lia.
      remember (take (t_length T_handle) (drop (N.to_nat (handle_addr h) - N.to_nat (base')) tbs)) as tbs'.
      
      assert (length tbs' = t_length T_handle) as Htbs''; first lia. 

      
      apply N.eqb_eq in Hmod.
      iApply (wp_wand _ _ _ (λ v, (|={⊤ ∖ ↑wsN (id h), ⊤}=> (∃ v0 : value, ⌜v = immV [v0]⌝ ∗ interp_value T_handle v0) ∗
                                                             interp_frame (tc_local C) i f ∗ interp_allocator all) ∗ ↪[frame] f)%I with "[Hf Hbl Hown Halloc Htoks Hwon Hcls Hss Hreconstitute]").
      2:{ iIntros (v) "[H Hf]". iFrame. }
      
      iApply wp_segload_handle_deserialize => //; try by unfold t_length; rewrite nat_bin; lia.
      
      iSplitR "Halloc Hss Hf"; last by iFrame.
      iNext. iIntros "(Hid & Hss)".
      
      iDestruct ("Hreconstitute" $! tbs' Htbs' with "Hss") as "Hss".
      subst tbs'; rewrite cat_app reconstitute N2Nat.id.
      iMod ("Hcls" with "[Hss Hhandles]").
      * iNext. iExists tbs. iFrame "Hss Hhandles". done.
      * remember (handle_addr h - base')%N as addr.
        assert ((base' + addr) `mod` handle_size = 0 /\ (addr + handle_size <= bound'))%N as Haddr.
        { subst. unfold handle_addr.
          replace (base' + (base h + offset h - base'))%N with (base h + offset h)%N;
            last lia.
          split.
          - fold (handle_addr h). done.  
          - unfold t_length in Hbounds; rewrite nat_bin N2Nat.id in Hbounds. 
            clear - Hbound Hbounds Hbase. lia.
        }
        iSpecialize ("Hhandles" $! addr Haddr).
        iDestruct "Hhandles" as "[%Hnum | Hvalid]".
        -- iModIntro. iSplitR.
           ++ iExists _. iSplit; first done.
              rewrite fixpoint_interp_value_handle_eq.
              iExists _. iSplit; first done.
              iLeft. iPureIntro. simpl.
              apply andb_false_intro2.
              apply forallb_false.
              destruct Hnum as (addr' & b & Haddr' & Hb).
              exists Numeric. split => //.
              eapply lookup_Some_in; last exact Hb; try lia.
              subst addr. rewrite nat_bin. lia.
           ++ iSplitL "Hown".
              ** iExists _. iFrame. iSplit; first done.
                 done.
              ** iExists _. iFrame. iApply "Htoks".
                 iExists _.
                 iFrame. done.
        -- iModIntro. iSplitR.
           ++ iExists _. iSplit; first done.
              iApply interp_handle_update_validity.
              unfold t_length; rewrite nat_bin.
              subst addr. rewrite N2Nat.inj_sub. done.
           ++ iSplitL "Hown".
              ** iExists _. iFrame. iSplit => //.
              ** iExists _. iFrame. iApply "Htoks".
                 iExists _. iFrame. done.

    }
    iIntros (v) "[((%v0 & -> & Hv) & Hfv) Hf]".
    iSplitL "Hv".
      + iLeft. iRight. iExists _. iSplit; first done. iFrame. done.
      + iExists _,_. iFrame.
  Qed.

End fundamental.
