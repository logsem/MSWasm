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

  
  Lemma lookup_map {A B} (f: A -> B) l k:
    map f l !! k = match l !! k with Some x => Some (f x) | None => None end.
  Proof.
    generalize dependent k.
    induction l => //=; intros.
    destruct k => //=.
  Qed. 
  

  Lemma take_drop_take {A} lo hi lo' (l: list A) :
    lo + hi <= lo' ->
    take hi (drop lo (take lo' l)) = take hi (drop lo l).
  Proof.
    intros H. generalize dependent lo'; generalize dependent hi; generalize dependent lo.
    induction l => //=; intros.
    { rewrite take_nil drop_nil take_nil. done. }
    destruct hi => //=.
    destruct lo' => //=; first lia.
    destruct lo => //=.
    { specialize (IHl 0). rewrite drop_0 in IHl. erewrite <- IHl.
      - rewrite drop_0. rewrite take_take.
        replace (hi `min` lo') with hi; last lia.
        rewrite take_take.
        instantiate (1 := lo').
        replace (hi `min` lo') with hi; last lia.
        done.
      - lia. }
    rewrite IHl; last lia. done.
  Qed.

  Lemma overlap_nat a b a' b':
    a + S b > a' -> a' + S b' > a -> exists x, a <= x /\ x < a + S b /\ a' <= x /\ x < a' + S b'.
  Proof.
    intros H H'.
    induction b.
    { exists a. repeat split; lia. }
    destruct (a + S b =? a') eqn:Ha.
    { apply Nat.eqb_eq in Ha.
      exists a'. repeat split; lia. }
    apply Nat.eqb_neq in Ha.
    assert (a + S b > a') as Ha'.
    { lia. }
    apply IHb in Ha' as (x & ? & ? & ? & ?).
    exists x. repeat split; lia. 
  Qed.

  Lemma overlap a b a' b':
    (b > 0 -> b' > 0 ->
     a + b > a' -> a' + b' > a -> exists x, a <= x /\ x < a + b /\ a' <= x /\ x < a' + b')%N.
  Proof.
    intros Hb Hb' H H'.
    destruct (overlap_nat (N.to_nat a) ((N.to_nat b - 1)) (N.to_nat a') ((N.to_nat b' - 1))) as (x & ? & ? & ? & ?); try lia.
    exists (N.of_nat x). repeat split; lia.
  Qed.

  Lemma lookup_lt_Some_inv {A} i (l: list A):
    i < length l -> exists x, l !! i = Some x.
  Proof.
    generalize dependent i.
    induction l; intros; first by simpl in *; lia.
    destruct i; first by eexists a.
    simpl in H. assert (i < length l) as Hi; first lia.
    apply IHl in Hi as [x Hx].
    exists x. simpl. done.
  Qed. 


  Lemma modulo_divisible a m:
    (a `mod` m = 0 -> (a / m) * m = a)%N.
  Proof.
    unfold N.modulo, N.div.
    specialize (N.div_eucl_spec a m) as H. 
    destruct (N.div_eucl a m) eqn:Hdivmod.
    simpl.
    intros ->.
    lia.
  Qed. 
    

  
  Lemma modulo_trapped a b m :
    (a `mod` m = 0 -> b `mod` m = 0 -> a > b - m -> a < b + m -> a = b)%N.
  Proof.
    intros Ha Hb Hlo Hhi.
    apply modulo_divisible in Ha, Hb => //.
    remember (a `div` m)%N as ka; clear Heqka.
    remember (b `div` m)%N as kb; clear Heqkb.
    remember (N.to_nat a) as a'.
    remember (N.to_nat b) as b'.
    remember (N.to_nat m) as m'.
    remember (N.to_nat ka) as ka'.
    remember (N.to_nat kb) as kb'.
    assert (ka' * m' = a') as Ha'; first lia.
    assert (kb' * m' = b') as Hb'; first lia.
    assert (a' > b' - m') as Hlo'; first lia.
    assert (a' < b' + m') as Hhi'; first lia.
    assert (a' = b'); last lia.
    assert (b' - a' = (kb' - ka') * m') as Hamb.
    { rewrite - Ha' - Hb'. 
      rewrite Nat.mul_sub_distr_r.
      done. }
    remember (kb' - ka') as k; clear Heqk.
    assert (b' - a' < m'); first lia.
    destruct k; last lia. 
    assert (b' <= a'); first lia.
    assert (a' - b' = (ka' - kb') * m') as Hbma.
    { rewrite - Ha' - Hb'. 
      rewrite Nat.mul_sub_distr_r.
      done. }
     remember (ka' - kb') as k; clear Heqk.
     assert (a' - b' < m'); first lia.
     destruct k; last lia.
     lia.
  Qed.

  Lemma modulo_leq a m:
    (a `mod` m = 0 -> a = 0 \/ a >= m)%N.
  Proof.
    intro H; apply modulo_divisible in H.
    remember (a `div` m)%N as k; clear Heqk.
    remember (N.to_nat a) as a'.
    remember (N.to_nat m) as m'.
    remember (N.to_nat k) as k'.
    assert (k' * m' = a') as H'; first lia.
    assert (a' = 0 \/ a' >= m') as [?|?]; [|lia|lia].
    destruct k'; first by left.
    right; lia.
  Qed. 


  Lemma lt_plus : forall a b c, c <= a -> a < b + c -> a - c < b.
  Proof. lia. Qed.
  Lemma lt_minus : forall a b c, a < b - c -> a + c < b.
  Proof. lia. Qed.
  
  Lemma arith: forall a b c d, (d <= a -> a < b - c + d -> b > c + a - d)%N.
  Proof. lia. Qed. 

    
    
    
    

    
    (* ----------------------------------------- SEGSTORE ---------------------------------------- *)


  Lemma typing_segstore_numeric C t :
    t <> T_handle ->
    ⊢ semantic_typing C (to_e_list [BI_segstore t]) (Tf [T_handle; t] []).
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
    destruct ws as [|wh ws];[done|destruct ws as [|w ws];[done|destruct ws;[|done]]].
    iSimpl in "Hv". iDestruct "Hv" as "(Hvh & Hv & _)".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct (interp_value_agree with "Hv") as "%Hagree".

    iDestruct "Hvh" as (h) "(-> & [%Hval | (%γ & %base' & %bound' & #Hw & %Hbase & %Hbound & #Hinv)])".
    { iApply (wp_wand with "[Hf]").
      - iApply (wp_segstore_failure1 with "[$Hf]"); first done.
        + by left.
         + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _,_. iFrame. } 
    iSimpl.

    destruct (valid h) eqn:Hvalid.
    2:{ iApply (wp_wand with "[Hf]").
        - iApply (wp_segstore_failure1 with "[$Hf]"); first done.
          + by left.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 

    destruct (bound h <? offset h + N.of_nat (t_length t))%N eqn:Hbounds.
    { apply N.ltb_lt in Hbounds.
      iApply (wp_wand with "[Hf]").
      - iApply (wp_segstore_failure1 with "[$Hf]"); first done.
        + by right; left; lia.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 
    apply N.ltb_ge in Hbounds.

      iDestruct "Hall" as (γmap) "[Hbl Htok]".
      iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
      iDestruct (gamma_agree with "Hw Hbl") as "%Hid".
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hid with "Htok") as "[(%x & %Hx & Halloc & Htok) Htoks]".
      destruct x as [[base bound] | ]; first iDestruct "Htok" as "(-> & -> & Htok)".
      2:{ iApply (wp_wand with "[Hf Halloc]").
          - iApply (wp_segstore_failure2 with "[$Hf $Halloc]").
            iIntros "!> Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
            iSplit; last iExact "Ha". done.
          - iIntros (v) "[[-> Ha] Hf]".
            iSplitR; first by do 2 iLeft.
            iExists _,_. iFrame. iSplitR.
            + iExists _. iSplit => //. 
            + iExists _. iFrame.  iApply "Htoks".
              iExists None. iFrame.  done.
      }
        

    iApply (wp_wand _ _ _ (λ x, (⌜ x = immV [] ⌝ ∗ interp_frame (tc_local C) i f ∗ interp_allocator all) ∗ ↪[frame] f )%I with "[Hf Hbl Hown Halloc Htok Htoks]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
     
      iMod (cinv_acc with "Hinv Htok") as "(Hss & Hwon & Hcls)"; first solve_ndisj.
      iModIntro.
      iDestruct "Hss" as (tbs) "(>%Htbs & >Hss & #Hhandles)".
      iDestruct (wss_select (N.to_nat base) (N.to_nat bound) (N.to_nat (handle_addr h)) (t_length t) tbs with "[Hss]") 
        as "(%Htbs' & Hss & Hreconstitute)";
        try rewrite N2Nat.id;
        try done;
        try by subst; unfold handle_addr; lia.
      remember (take (t_length t) (drop (N.to_nat (handle_addr h) - N.to_nat base) tbs)) as tbs'.
      
      assert (length tbs' = t_length t) as Htbs''; first lia. 

      iApply (wp_wand _ _ _ (λ v, ((|={⊤ ∖ ↑wsN (id h),⊤}=>
                                       (⌜v = immV []⌝ ∗ interp_frame (tc_local C) i f ∗ interp_allocator all)) ∗  ↪[frame]f))%I
                 with "[Hf Hbl Hown Halloc Htoks Hwon Hcls Hss Hreconstitute]").
        2:{ iIntros (v) "[H Hf]". iFrame. } 
        iApply wp_segstore => //.
        iSplitR "Halloc Hss Hf"; last by iFrame.
        iNext. iIntros "(Hid & Hss)".
        assert (length (map (λ b, (b, Numeric)) (bits w)) = t_length t) as Hlen'.
        { rewrite map_length. by apply length_bits. } 
        iDestruct ("Hreconstitute" $! _ Hlen' with "Hss") as "Hss".
        rewrite N2Nat.id.
        iMod ("Hcls" with "[Hss]").
        + iNext. iExists _. iFrame "Hss". iSplit.
          * iPureIntro. repeat rewrite app_length.
            rewrite drop_length Hlen' take_length_le.
            2:{ rewrite Htbs. unfold handle_addr. lia. }
            unfold handle_addr. lia.
          * (* We must now restore the invariant on all stored handles to be valid *)
            iIntros (addr) "%Haddr".
            (* We must show that knowning addr is handle-aligned, it either doesn't store
               a handle, or stores a valid one *)
            destruct (handle_addr h - base + N.of_nat (t_length t) <=? addr)%N eqn:Hlo.
              
            -- (* Case 1: the place where we wrote to memory is before addr *)
              (* I.e. the previous invariant still holds *)
              apply N.leb_le in Hlo.
               iDestruct ("Hhandles" $! addr Haddr) as "[%Hnum | Hvalid]";
                 destruct Haddr as [Hmod Haddr].
               ++ iLeft. 
                  iPureIntro.
                  destruct Hnum as (addr' & b & Haddr' & Hnum).
                  exists addr', b. split; first done.
                  rewrite lookup_app.
                  rewrite lookup_take_ge; last lia.
                  rewrite lookup_app.
                  rewrite lookup_ge_None_2.
                  2:{ rewrite map_length take_length_le; try lia.
                      erewrite length_bits => //. lia. }
                  rewrite lookup_drop.
                  rewrite map_length take_length_le; try lia.
                  erewrite length_bits => //.
                  replace  (N.to_nat (handle_addr h) - N.to_nat base + t_length t +
                              (N.to_nat (addr + addr') - (N.to_nat (handle_addr h) - N.to_nat base) -
                                 t_length t)) with (N.to_nat (addr + addr')); first done.
                  lia.
               ++ iRight.
                  rewrite catA.
                  rewrite drop_app_ge.
                  2:{ rewrite app_length map_length take_length_le; try lia.
                      erewrite length_bits => //. lia. } 
                  rewrite drop_drop.
                  rewrite app_length map_length take_length_le; last lia.
                  erewrite length_bits => //.
                  rewrite - le_plus_minus; last lia.
                  done.
            -- apply N.leb_gt in Hlo.
               destruct (addr + handle_size <=? handle_addr h - base)%N eqn:Hhi.
               ++ (* Case 2: the place where we wrote is far after addr *)
               (* i.e. the previous invariant still holds *)
                 apply N.leb_le in Hhi.
                  iDestruct ("Hhandles" $! addr Haddr) as "[%Hnum | Hvalid]";
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
                 destruct (overlap addr handle_size (handle_addr h - base) (N.of_nat (t_length t))) as (y & ? & ? & ? & ?); try lia; try by destruct t.
                 assert (N.to_nat (addr + (y - addr)) - (N.to_nat (handle_addr h) - N.to_nat base) < length (bits w)) as Hbits.
                 { erewrite length_bits => //. lia. }
                 apply lookup_lt_Some_inv in Hbits as [b Hb].
                 exists (y - addr)%N, b.
                 split; first lia.
                 rewrite lookup_app.
                 rewrite lookup_take_ge; last lia.
                 rewrite cat_app.
                 rewrite lookup_app.
                 rewrite take_length_le; last lia.
                 rewrite lookup_map. rewrite Hb. done.
        + iModIntro. 
          iSplitR => //.
          iSplitL "Hown".
          -- iExists _. iFrame. iSplit; done.
          -- iExists _. iFrame. iApply ("Htoks" with "[Hwon Hid]").
               iExists _. iFrame. done.
    }
    iIntros (v) "[(-> & Hfv) Hf]".
    iSplitR.
      + iLeft. iRight. iExists _. iSplit; first done. done. 
      + iExists _,_. iFrame.
  Qed.

  
  Lemma typing_segstore C t :
    ⊢ semantic_typing C (to_e_list [BI_segstore t]) (Tf [T_handle; t] []).
  Proof.
    destruct t; try by apply typing_segstore_numeric.
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
    destruct ws as [|wh ws];[done|destruct ws as [|w ws];[done|destruct ws;[|done]]].
    iSimpl in "Hv". iDestruct "Hv" as "(Hvh & Hv & _)".
    do 2 rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv" as (hv) "[-> Hv]".

    iDestruct "Hvh" as (h) "(-> & [%Hval | (%γ & %base' & %bound' & #Hw & %Hbase & %Hbound & #Hinv)])".
    { iApply (wp_wand with "[Hf]").
      - iApply (wp_segstore_failure1 with "[$Hf]"); first done.
        + by left.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _,_. iFrame. } 
    iSimpl.

    destruct (valid h) eqn:Hvalid.
    2:{ iApply (wp_wand with "[Hf]").
        - iApply (wp_segstore_failure1 with "[$Hf]"); first done.
          + by left.
          + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
        - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 

    destruct (bound h <? offset h + N.of_nat (t_length T_handle))%N eqn:Hbounds.
    { apply N.ltb_lt in Hbounds.
      iApply (wp_wand with "[Hf]").
      - iApply (wp_segstore_failure1 with "[$Hf]"); first done.
        + by right; left; lia.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
          iSplitR; first by do 2 iLeft.
          iExists _,_. iFrame. } 
    apply N.ltb_ge in Hbounds.

    destruct ((handle_addr h `mod` handle_size)%N =? N.of_nat 0)%N eqn:Hmod.
    2:{  iApply (wp_wand with "[Hf]").
         - iApply (wp_segstore_failure1 with "[$Hf]") => //.
           + right; right; split => //. intros Habs.
             rewrite Habs in Hmod. simpl in Hmod. done.
           + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
         - iIntros (v) "[-> Hf]".
           iSplitR; first by do 2 iLeft.
           iExists _,_. iFrame. } 
    apply N.eqb_eq in Hmod.

    assert (types_agree T_handle (VAL_handle hv)) as Hagree; first done.
    iDestruct "Hall" as (γmap) "[Hbl Htok]".
      iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".
      iDestruct (gamma_agree with "Hw Hbl") as "%Hid".
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hid with "Htok") as "[(%x & %Hx & Halloc & Htok) Htoks]".
      destruct x as [[base bound]|]; first iDestruct "Htok" as "(-> & -> & Htok)".
      2:{ iApply (wp_wand with "[Hf Halloc]").
          - iApply (wp_segstore_failure2 with "[$Hf $Halloc]") => //.
            iIntros "!> Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
            iSplit; last iExact "Ha". done.
          - iIntros (v) "[[-> Ha] Hf]".
            iSplitR; first by do 2 iLeft.
            iExists _,_. iFrame. iSplitR.
            + iExists _. iSplit => //.
            + iExists _. iFrame. iApply "Htoks".
              iExists None. iFrame. done.
      } 
    iApply (wp_wand _ _ _ (λ x, (⌜ x = immV [] ⌝ ∗ interp_frame (tc_local C) i f ∗ interp_allocator all) ∗ ↪[frame] f )%I with "[Hf Hbl Hown Halloc Htok Htoks]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(wsN (id h)))).
     
      iMod (cinv_acc with "Hinv Htok") as "(Hss & Hwon & Hcls)"; first solve_ndisj.
      iModIntro.
      iDestruct "Hss" as (tbs) "(>%Htbs & >Hss & #Hhandles)".
      iDestruct (wss_select (N.to_nat base) (N.to_nat bound) (N.to_nat (handle_addr h)) (t_length T_handle) tbs with "[Hss]") 
        as "(%Htbs' & Hss & Hreconstitute)";
        try rewrite N2Nat.id;
        try done;
        try by subst; unfold handle_addr; lia.
      remember (take (t_length T_handle) (drop (N.to_nat (handle_addr h) - N.to_nat base) tbs)) as tbs'.
      
      assert (length tbs' = t_length T_handle) as Htbs''; first lia. 

      iApply (wp_wand _ _ _ (λ v, ((|={⊤ ∖ ↑wsN (id h),⊤}=>
                                       (⌜v = immV []⌝ ∗ interp_frame (tc_local C) i f ∗ interp_allocator all)) ∗  ↪[frame]f))%I
                 with "[Hf Hbl Hown Halloc Htoks Hwon Hcls Hss Hreconstitute]").
        2:{ iIntros (v) "[H Hf]". iFrame. } 
        iApply wp_segstore_handle => //; try by unfold t_length; rewrite nat_bin; lia.
        iSplitR "Halloc Hss Hf"; last by iFrame.
        iNext. iIntros "(Hid & Hss)".
        assert (length (map (λ b, (b, Handle)) (bits (VAL_handle hv))) = t_length T_handle) as Hlen'.
        { rewrite map_length. by apply length_bits. } 
        iDestruct ("Hreconstitute" $! _ Hlen' with "Hss") as "Hss".
        rewrite N2Nat.id.
        iMod ("Hcls" with "[Hss]").
        + iNext. iExists _. iFrame "Hss". iSplit.
          * iPureIntro. repeat rewrite app_length.
            rewrite drop_length Hlen' take_length_le.
            2:{ rewrite Htbs. unfold handle_addr. lia. }
            unfold handle_addr. lia.
          * (* We must now restore the invariant on all stored handles to be valid *)
            iIntros (addr) "%Haddr".
            (* We must show that knowning addr is handle-aligned, it either doesn't store
               a handle, or stores a valid one *)
            (* destruct (handle_addr h + handle_size <=? base + addr)%N eqn:Hlo. *)
            (* destruct (handle_addr h <=? base + addr - handle_size)%N eqn:Hlo. *)
            destruct (handle_addr h - base + N.of_nat (t_length T_handle) <=? addr)%N eqn:Hlo.  
              
            -- (* Case 1: the place where we wrote to memory is before addr *)
              (* I.e. the previous invariant still holds *)
              apply N.leb_le in Hlo.
              iDestruct ("Hhandles" $! addr Haddr) as "[%Hnum | Hvalid]";
                 destruct Haddr as [Hmod' Haddr].
               ++ iLeft. 
                  iPureIntro.
                  destruct Hnum as (addr' & b & Haddr' & Hnum).
                  exists addr', b. split; first done.
                  rewrite lookup_app.
                  rewrite lookup_take_ge; last lia.
                  rewrite lookup_app.
                  rewrite lookup_ge_None_2.
                  2:{ rewrite map_length take_length_le; try lia.
                      erewrite length_bits => //. lia. 
                  }
                  rewrite lookup_drop.
                  rewrite map_length take_length_le; try lia.
                  erewrite length_bits => //.
                  replace  (N.to_nat (handle_addr h) - N.to_nat base + t_length T_handle +
                              (N.to_nat (addr + addr') - (N.to_nat (handle_addr h) - N.to_nat base) -
                                 t_length T_handle)) with (N.to_nat (addr + addr')); first done.
                  lia.
               ++ iRight.
                  rewrite catA.
                  rewrite drop_app_ge.
                  2:{ rewrite app_length map_length take_length_le; try lia.
                      erewrite length_bits => //. lia. } 
                  rewrite drop_drop.
                  rewrite app_length map_length take_length_le; last lia.
                  erewrite length_bits => //.
                  rewrite - le_plus_minus; last lia.
                  done.
            -- apply N.leb_gt in Hlo.
               destruct (addr + handle_size <=? handle_addr h - base)%N eqn:Hhi.
               ++ (* Case 2: the place where we wrote is far after addr *)
               (* i.e. the previous invariant still holds *)
                 apply N.leb_le in Hhi.
                  iDestruct ("Hhandles" $! addr Haddr) as "[%Hnum | Hvalid]";
                    destruct Haddr as [Hmod' Haddr].
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
                 (* I.e. we know that this handle is safe as it is our argument *)

                 apply N.leb_gt in Hhi.
                 iRight.
                 destruct Haddr as [Hmod' Haddr].
                 unfold t_length in Hlo. rewrite nat_bin N2Nat.id in Hlo.
                 assert (handle_addr h < base + addr + handle_size)%N as Hhi'; first lia.
                 assert (handle_addr h > base + addr - handle_size)%N as Hlo'.
                 { admit. }
                 
                 specialize (modulo_trapped _ _ _ Hmod Hmod' Hlo' Hhi') as Heqaddr.
                 assert (N.to_nat addr = length (take (N.to_nat (handle_addr h) - N.to_nat base) tbs)) as Hlentake.
                 { rewrite take_length_le; last lia. lia. } 
                 rewrite Hlentake drop_app.
                 assert (N.to_nat handle_size = length (map (λ b, (b, Handle)) (bits (VAL_handle hv)))) as Hlenmap.
                 { rewrite map_length. erewrite length_bits => //. unfold t_length.
                   by rewrite nat_bin. }
                 rewrite Hlenmap take_app.
                 unfold bits. rewrite map_map.
                 rewrite map_id.
                 assert (handle_of_bytes (serialise_handle hv) = hv) as ->.
                 { destruct HHB.
                   unfold handle.handle_of_bytes, handle.serialise_handle.
                   rewrite handle_of_serialise. done. } 
                 rewrite fixpoint_interp_value_handle_eq.
                 iExists hv. iSplit; first done.
                 rewrite map_length.
                 assert (length (serialise_handle hv) = N.to_nat handle_size) as ->.
                 { destruct HHB. unfold handle.serialise_handle, handle.handle_size.
                   rewrite length_serialise nat_bin. done. }
                 iExact "Hv". 
        + iModIntro. 
          iSplitR; first done.
          iSplitL "Hown".
          -- iExists _. iFrame. iSplit; done.
          -- iExists _. iFrame. iApply ("Htoks" with "[Hwon Hid]").
             iExists _. iFrame. done.

    }
    iIntros (v) "[( -> & Hfv) Hf]".
    iSplitR.
      + iLeft. iRight. iExists _. iSplit; first done. done. 
      + iExists _,_. iFrame.
Admitted.

End fundamental.
