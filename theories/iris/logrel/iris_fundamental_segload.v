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

   Lemma wss_select a b a' b' tbs:
    (a' >= a) -> (a' + b' <= a + b) -> length tbs = b ->
    ↦[wss][ N.of_nat a ] tbs -∗
     ⌜ length (take b' (drop (a' - a) tbs)) = b' ⌝ ∗
                          ↦[wss][ N.of_nat a' ] (take b' (drop (a' - a) tbs)) ∗
                          ∀ tbs', (⌜ length tbs' = b' ⌝ -∗ ↦[wss][ N.of_nat a' ] tbs' -∗ ↦[wss][ N.of_nat a ] (take (a' - a) tbs ++ tbs' ++ drop (a' - a + b') tbs)).
  Proof.
    iIntros (Ha Hb Htbs) "Hs".
    rewrite <- (take_drop (a' - a) tbs) at 1.
    rewrite <- (take_drop b' (drop (a' - a) tbs)) at 1.
    iDestruct (big_sepL_app with "Hs") as "[Hbegin Hs]".
    iDestruct (big_sepL_app with "Hs") as "[Hs Hend]".
    iSplit.
    - iPureIntro. rewrite take_length_le; first done.
      rewrite drop_length Htbs. lia.
    - iSplitL "Hs".
      + iApply (big_sepL_impl with "[Hs]"); first done.
        iIntros "!>" (k x) "%Hx Hs".
        rewrite take_length_le; last lia. repeat rewrite Nat2N.id.
        replace (a + (a' - a + k)) with (a' + k); first done.
        lia.
      + iIntros (tbs') "%Hlen Hs".
        iApply (big_sepL_app with "[$Hbegin Hs Hend]").
        iApply (big_sepL_app with "[Hend Hs]").
        iSplitL "Hs". 
        * iApply (big_sepL_impl with "[Hs]"); first done.
          iIntros "!>" (k x) "%Hx Hs".
          rewrite take_length_le; last lia. repeat rewrite Nat2N.id.
          replace (a + (a' - a + k)) with (a' + k); first done.
          lia.
        * rewrite drop_drop.
          iApply (big_sepL_impl with "[Hend]"); first done.
          iIntros "!>" (k x) "%Hx Hs".
          rewrite take_length_le; last lia. repeat rewrite Nat2N.id.
          rewrite take_length_le.
          -- rewrite Hlen. done.
          -- rewrite drop_length. lia.
  Qed.

  Lemma reconstitute {A} a a' b' (tbs: list A):
    take (a' - a) tbs ++ take b' (drop (a' - a) tbs) ++ drop (a' - a + b') tbs = tbs.
  Proof.
    rewrite - drop_drop. rewrite take_drop.
    rewrite take_drop. done.
  Qed. 
  
(*
  Lemma wss_select_nat a b a' b' tbs:
    (a' >= a)%N -> (a' + b' <= a + b)%N -> N.of_nat (length tbs) = b ->
    ↦[wss][ a ] tbs -∗
     ⌜ N.of_nat (length (take (N.to_nat b') (drop (N.to_nat a' - a) tbs))) = b' ⌝ ∗
                          ↦[wss][ a' ] (take b' (drop (a' - a) tbs)) ∗
                          ∀ tbs', (⌜ length tbs' = b' ⌝ -∗ ↦[wss][ N.of_nat a' ] tbs' -∗ ↦[wss][ N.of_nat a ] (take (a' - a) tbs ++ tbs' ++ drop (a' - a + b') tbs)).
     Proof.
      iIntros (Ha Hb Htbs) "Hs".
      iDestruct (wss_select_nat (N.to_nat a) (N.to_nat b) (N.to_nat a') (N.to_nat b') tbs
                  with "[Hs]") as "(%tbs' & % & ?)"; try lia.
      - by rewrite N2Nat.id.
      - repeat rewrite N2Nat.id. iExists tbs'. iFrame.
        iPureIntro. lia.
    Qed. *)

  (*
  Lemma wss_select_nat a b a' b' tbs:
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

        
                                                           
    
    
    
  (* ----------------------------------------- SEGLOAD ---------------------------------------- *)

(*    Lemma minimal_example0 n f:
      inv n True ∗ ↪[frame] f ⊢ WP [AI_basic BI_nop] {{ w, ⌜ w = immV [] ⌝ ∗ ↪[frame] f}}.
    Proof.
      iIntros "[H Hf]".
      iApply fupd_wp.
      iInv "H" as "Htrue" "Hcls".
      iApply (wp_nop with "Hf").
      iMod ("Hcls" with "[]").
      - iNext. done.
      - iModIntro. done.
    Qed. 

    Check wp_load_deserialize.

    Lemma minimal_example bv k a off f n nspace:
      length bv = 4 -> inst_memory (f_inst f) !! 0 = Some n ->
      inv nspace (N.of_nat n↦[wms][Wasm_int.N_of_uint i32m k + off]bv) ∗ ↪[frame] f
        ⊢ WP [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load T_i32 None a off)]
        {{ w, ∃ v, ⌜ w = immV [v] ⌝ ∗ ↪[frame] f }}.
    Proof.

(*       (* Attempt 1: open inv, then wand *) 
      iIntros (??) "[H Hf]". 
      iApply fupd_wp.
      iInv "H" as ">Hm" "Hcls".
      
      iApply (wp_wand with "[Hm Hf]").
      - iApply wp_load_deserialize => //. iFrame.
        by instantiate (1 := λ x, ⌜ x = immV _⌝%I).
      - (* Blocked !!! *)  *)

      
      (* Attempt 2: wand, then open inv *)
      iIntros (??) "[H Hf]".
      iApply (wp_wand with "[H Hf]").
      - iApply (wp_atomic _ _ (⊤ ∖ ↑nspace)). (* iApply fupd_wp. *)
        iInv "H" as ">Hm" "Hcls".
        iApply (wp_wand with "[Hf Hm]").
        + iApply wp_load_deserialize => //. iFrame.
          instantiate (1 := λ x, ⌜ x = immV _ ⌝%I). done.
        + iIntros (v). 
        (* Whom to give the resource from "Hm"? To "Hcls" or to the goal? *)
    
    
    Lemma minimal_example' tbs h f:
      (offset h + 4 <= bound h)%N -> valid h -> length tbs = 4 ->
      inv (wsN (id h)) (↦[wss][handle_addr h] tbs ∗ (id h)↣[allocated](handle_addr h, bound h)) ∗ ↪[frame] f ⊢
        WP [AI_basic (BI_const (VAL_handle h)); AI_basic (BI_segload T_i32)] {{ w, ∃ v, ⌜ w = immV [v] ⌝ ∗ ↪[frame] f}}.
    Proof.
      iIntros (???) "[H Hf]".
      iApply fupd_wp.
      iInv "H" as ">[Hs Hall]" "Hcls".
      iApply (wp_wand with "[Hs Hall Hf]").
      - iApply wp_segload_deserialize => //. iFrame.
        by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      - 
      iApply (wp_wand with "[H Hf]").
      - iApply fupd_wp.
        iInv "H" as ">[Hs Hall]" "Hcls".
        iApply (wp_segload_deserialize) => //.x

        
        + iFrame.
      *)


    Lemma better_wp_segload (Φ:iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t:value_type) (bv:bytes) (tbv: list (byte * btag))
  (h: handle) (f0: frame) (x: N*N) :
  t <> T_handle ->
  length tbv = t_length t ->
  List.map fst tbv = bv ->
  valid h = true ->
  ((offset h) + N.of_nat (t_length t) <= bound h)%N ->

  (
     (h.(id) ↣[allocated] x ∗ ↦[wss][ handle_addr h ]tbv ∗ ↪[frame] f0 -∗ Φ (immV [wasm_deserialise bv t])) ∗
   ↪[frame] f0 ∗ h.(id) ↣[allocated] x ∗ 
      ↦[wss][ handle_addr h ] tbv ⊢
     (WP [AI_basic (BI_const (VAL_handle h)) ;
          AI_basic (BI_segload t)] @ s; E {{ Φ }})).
    Proof.
      iIntros (?????) "(HΦ & Hf & Ha & Hs)".
      iApply (wp_wand with "[Hf Ha Hs]").
      - iApply wp_segload_deserialize => //.
        iSplitR; last by iFrame.
        iNext. iIntros "H". instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
        iSplit; first done. iExact "H".
      - iIntros (v) "[(-> & ?) Hf]".
        iApply "HΦ". iFrame.
    Qed.

        Lemma better_wp_segload_handle (Φ:iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t:value_type) (bv:bytes) (tbv: list (byte * btag))
          (h: handle) (f0: frame) (x: N*N) hmem bc ts:
           t = T_handle ->
  length tbv = t_length t ->
  List.map fst tbv = bv ->
  List.map snd tbv = ts ->
  valid h = true ->
  ((offset h) + N.of_nat (t_length T_handle) <= bound h)%N ->
  (N.modulo (handle_addr h) (N.of_nat (t_length T_handle)) = N.of_nat 0)%N ->
  wasm_deserialise bv t = VAL_handle hmem ->
  bc = List.forallb (fun x => match x with Handle => true | _ => false end) ts ->
  (
     (h.(id) ↣[allocated] x ∗ ↦[wss][ handle_addr h ]tbv ∗ ↪[frame] f0 -∗ Φ (immV [VAL_handle (upd_handle_validity hmem bc)])) ∗
   ↪[frame] f0 ∗ h.(id) ↣[allocated] x ∗ 
      ↦[wss][ handle_addr h ] tbv ⊢
     (WP [AI_basic (BI_const (VAL_handle h)) ;
          AI_basic (BI_segload t)] @ s; E {{ Φ }})).
    Proof.
      iIntros (?????????) "(HΦ & Hf & Ha & Hs)".
      iApply (wp_wand with "[Hf Ha Hs]").
      - iApply wp_segload_handle_deserialize => //.
        iFrame "Hf Ha Hs". iNext. iIntros "H".
        instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
        iSplit; first done. iExact "H".
      - iIntros (v) "[(-> & ?) Hf]".
        iApply "HΦ". iFrame.
    Qed. 


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

    Lemma interp_handle_update_validity h (b: bool) :
      interp_value_handle (VAL_handle h) ⊢
        interp_value_handle (VAL_handle (upd_handle_validity h b)).
    Proof.
      iIntros "H".
      destruct h; unfold upd_handle_validity => /=.
      destruct b, valid => //.
      iClear "H". rewrite fixpoint_interp_value_handle_eq.
      iExists _. iSplit; first done.
      iLeft. iPureIntro. done. 
    Qed. 
        

        

  Lemma typing_segload C t : 
    ⊢ semantic_typing C (to_e_list [BI_segload t]) (Tf [T_handle] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
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
    iDestruct "Hv" as (h) "(-> & [%Hval | (%γ & %base' & %bound' & #Hw & %Hbase & %Hbound & #Hinv)])".
    { iApply (wp_wand with "[Hf]").
        - iApply (wp_segload_failure with "[$Hf]").
          + by left.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _. iFrame. } 
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


    iApply (wp_wand _ _ _ (λ x, ((⌜ x = trapV ⌝ ∨ ∃ v, ⌜ x = immV [v] ⌝ ∗ interp_value t v) ∗ interp_frame (tc_local C) i all f) ∗ ↪[frame] f )%I with "[Hf Hfv]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
      iDestruct "Hfv" as "[Halloc Hfv]".
      iDestruct "Halloc" as (γmap) "[Hbl Htok]".
      (*    iApply fupd_wp.  *)
      iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
      iDestruct (gamma_agree with "Hw Hbl") as "%Hid".
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hid with "Htok") as "[(%x & %Hx & Halloc & Htok) Htoks]".
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

      destruct t eqn:Ht. 
      
      - (* Segload T_i32 *)
        iApply better_wp_segload => //.
        iSplitR "Halloc Hss Hf"; last by iFrame.
        iIntros "(Hid & Hss & Hf)".
        iDestruct ("Hreconstitute" $! tbs' Htbs' with "Hss") as "Hss".
        subst tbs'.
        rewrite cat_app reconstitute N2Nat.id.
        iMod ("Hcls" with "[Hss]").
        + iNext. iExists tbs. iFrame "Hhandles Hss". done.
        + iModIntro. iFrame "Hf".
          iSplitR.
          * iRight. iExists _. 
            iSplit; first done. by iExists _.
          * iSplitR "Hown".
            -- iExists _. iFrame. iApply ("Htoks" with "[Hwon Hid]").
               iExists _. iFrame. done.
            -- iExists _. iFrame. iSplit; done.
      - (* Segload T_i64 *)
        iApply better_wp_segload => //.
        iSplitR "Halloc Hss Hf"; last by iFrame.
        iIntros "(Hid & Hss & Hf)".
        iDestruct ("Hreconstitute" $! tbs' Htbs' with "Hss") as "Hss".
        subst tbs'. rewrite cat_app reconstitute N2Nat.id.
        iMod ("Hcls" with "[Hss Hhandles]").
        + iNext. iExists tbs. iFrame "Hhandles Hss". done.
        + iModIntro. iFrame "Hf".
          iSplitR.
          * iRight. iExists _. 
            iSplit; first done. by iExists _.
          * iSplitR "Hown".
          -- iExists _. iFrame. iApply ("Htoks" with "[Hwon Hid]").
            iExists _. iFrame. done.
          -- iExists _. iFrame. iSplit; done.
      - (* Segload T_f32 *)
        iApply better_wp_segload => //.
        iSplitR "Halloc Hss Hf"; last by iFrame.
        iIntros "(Hid & Hss & Hf)".
        iDestruct ("Hreconstitute" $! tbs' Htbs' with "Hss") as "Hss".
        subst tbs'; rewrite cat_app reconstitute N2Nat.id.
        iMod ("Hcls" with "[Hss Hhandles]").
        + iNext. iExists tbs. iFrame "Hhandles Hss". done.
        + iModIntro. iFrame "Hf".
          iSplitR.
          * iRight. iExists _. 
          iSplit; first done. by iExists _.
          * iSplitR "Hown".
          -- iExists _. iFrame. iApply ("Htoks" with "[Hwon Hid]").
            iExists _. iFrame. done.
          -- iExists _. iFrame. iSplit; done.
      - (* Segload T_f64 *)
        iApply better_wp_segload => //.
        iSplitR "Halloc Hss Hf"; last by iFrame.
        iIntros "(Hid & Hss & Hf)".
        iDestruct ("Hreconstitute" $! tbs' Htbs' with "Hss") as "Hss".
        subst tbs'. rewrite cat_app reconstitute N2Nat.id.
        iMod ("Hcls" with "[Hss Hhandles]").
        + iNext. iExists tbs. iFrame "Hhandles Hss". done.
        + iModIntro. iFrame "Hf".
          iSplitR.
          * iRight. iExists _. 
          iSplit; first done. by iExists _.
          * iSplitR "Hown".
          -- iExists _. iFrame. iApply ("Htoks" with "[Hwon Hid]").
            iExists _. iFrame. done.
          -- iExists _. iFrame. iSplit; done.
      - (* Segload T_handle *)
        destruct ((handle_addr h `mod` N.of_nat (t_length T_handle))%N =? N.of_nat 0)%N eqn:Hmod.
        + apply N.eqb_eq in Hmod.
          iApply (wp_wand _ _ _ (λ v, (|={⊤ ∖ ↑wsN (id h), ⊤}=> (⌜v = trapV⌝ ∨ (∃ v0 : value, ⌜v = immV [v0]⌝ ∗ interp_value T_handle v0)) ∗
                                                                 interp_frame (tc_local C) i all f) ∗ ↪[frame] f)%I with "[Hf Hbl Hown Halloc Htoks Hwon Hcls Hss Hreconstitute]").
          2:{ iIntros (v) "[H Hf]". iFrame. }
            
          iApply wp_segload_handle_deserialize => //.
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
              - fold (handle_addr h). unfold t_length in Hmod. rewrite nat_bin in Hmod.
                rewrite N2Nat.id in Hmod. done.
              - unfold t_length in Hbounds; rewrite nat_bin N2Nat.id in Hbounds. 
                clear - Hbound Hbounds Hbase. lia.
            }
            iSpecialize ("Hhandles" $! addr Haddr).
            iDestruct "Hhandles" as "[%Hnum | Hvalid]".
            -- iModIntro. iSplitR.
               ++ iRight. iExists _. iSplit; first done.
                  rewrite fixpoint_interp_value_handle_eq.
                  iExists _. iSplit; first done.
                  iLeft. iPureIntro. simpl.
                  apply andb_false_intro2.
                  apply forallb_false.
                  destruct Hnum as (addr' & b & Haddr' & Hb).
                  exists Numeric. split => //.
                  eapply lookup_Some_in; last exact Hb; try lia.
                  subst addr. rewrite nat_bin. lia.
               ++ iSplitR "Hown".
                  ** iExists _. iFrame. iApply "Htoks".
                     iExists _. iFrame. done.
                  ** iExists _. iFrame. iSplit; first done.
                     done.
            -- iModIntro. iSplitR.
               ++ iRight. iExists _. iSplit; first done.
                  iApply interp_handle_update_validity.
                  unfold t_length; rewrite nat_bin.
                     subst addr. rewrite N2Nat.inj_sub. done.
               ++ iSplitR "Hown".
                  ** iExists _. iFrame. iApply "Htoks".
                     iExists _. iFrame. done.
                  ** iExists _. iFrame. iSplit => //.
        + apply N.eqb_neq in Hmod.
          iApply (wp_wand with "[Hf]").
          * iApply (wp_segload_failure with "[$Hf]").  
            -- do 2 right. split => //.
               unfold t_length in Hmod.
               rewrite nat_bin N2Nat.id in Hmod.
               done.
            -- by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
          * iIntros (v) "[-> Hf]".
            iMod ("Hcls" with "[Hreconstitute Hss]").
            -- iNext. iExists _.
               iDestruct ("Hreconstitute" $! tbs' Htbs' with "Hss") as "Hss".
               subst tbs'; rewrite cat_app reconstitute N2Nat.id.
               iFrame "Hss Hhandles". done.
            -- iModIntro. iFrame "Hf". iSplitR.
               ++ iLeft. done.
               ++ iSplitR "Hown".
                  ** iExists _. iFrame. iApply "Htoks".
                     iExists _. iFrame. done.
                  ** iExists _. iFrame. iSplit => //.
    }
    iIntros (v) "[([-> | (%v0 & -> & Hv)] & Hfv) Hf]".
    - iSplitR.
      + iLeft. iLeft. done.
      + iExists _. iFrame.
    - iSplitL "Hv".
      + iLeft. iRight. iExists _. iSplit; first done. iFrame. done.
      + iExists _. iFrame.
Qed.

End fundamental.
