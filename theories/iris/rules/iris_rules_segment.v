From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language. 
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Import Coq.Program.Equality.
Require Export iris_wp_def iris_rules_resources.
From Coq Require Import BinNat.

Import uPred.

Set Default Proof Using "Type".

Section iris_rules_segment.
Context `{HHB : HandleBytes}.
Let reducible := @reducible wasm_lang.

Context `{!wasmG Σ}.


Lemma segment_in_bounds m i b :
  (segl_data (seg_data m)) !! i = Some b -> i < N.to_nat (seg_length m.(seg_data)) .
Proof.
  intros. 
  apply lookup_lt_Some in H. unfold seg_length, segment_list.seg_length.
  lia.
Qed.

Lemma commutes nid addr size (a: gmap N (N * N)):
  ∀ (j1 j2 : N) (z1 z2 : N * N) (y : gmap N ()),
    j1 ≠ j2
    → <[nid:=(addr, size)]> a !! j1 = Some z1
      → <[nid:=(addr, size)]> a !! j2 = Some z2
        → (let
           '(addr0, lim) := z1 in
            λ res : gmap N (),
              fold_left (λ (res0 : gmap N ()) (j : nat), <[N.of_nat j:=()]> res0)
                (iota (N.to_nat addr0) (N.to_nat lim)) res)
            ((let
              '(addr0, lim) := z2 in
               λ res : gmap N (),
                 fold_left (λ (res0 : gmap N ()) (j : nat), <[N.of_nat j:=()]> res0)
                   (iota (N.to_nat addr0) (N.to_nat lim)) res) y) =
          (let
           '(addr0, lim) := z2 in
            λ res : gmap N (),
              fold_left (λ (res0 : gmap N ()) (j : nat), <[N.of_nat j:=()]> res0)
                (iota (N.to_nat addr0) (N.to_nat lim)) res)
            ((let
              '(addr0, lim) := z1 in
               λ res : gmap N (),
                 fold_left (λ (res0 : gmap N ()) (j : nat), <[N.of_nat j:=()]> res0)
                   (iota (N.to_nat addr0) (N.to_nat lim)) res) y).
Proof.
  intros x1 x2 [y1 z1] [y2 z2] z _ _ _.
    remember (N.to_nat y1) as y1'.
    remember (N.to_nat y2) as y2'.
    remember (N.to_nat z1) as z1'.
    remember (N.to_nat z2) as z2'. 
    clear Heqy1' y1 Heqy2' y2 Heqz1' z1 Heqz2' z2.
    generalize dependent y1'. generalize dependent z.
    induction z1' => //=.
    intros. rewrite - IHz1'.
    clear.
    generalize dependent y2'. generalize dependent z.
    induction z2' => //=.
    intros.
    replace (<[ N.of_nat y2':=() ]> (<[ N.of_nat y1' := () ]> z))
      with (<[ N.of_nat y1':=() ]> (<[ N.of_nat y2' := () ]> z)).
    rewrite - IHz2'. done.
    destruct (Nat.eqb y1' y2') eqn:Hy.
    apply Nat.eqb_eq in Hy as ->; by repeat rewrite insert_insert. 
    apply Nat.eqb_neq in Hy. rewrite insert_commute. done.
    intro Habs. apply Nat2N.inj in Habs => //.
Qed.


Lemma was_not_added addr lim r j :
  (j < addr)%N \/ (j >= addr + lim)%N ->
  fold_left (λ (res : gmap N ()) (i : nat), <[N.of_nat i:=()]> res)
    (iota (N.to_nat addr) (N.to_nat lim)) r !! j = r !! j.
Proof.
  intros Hj.
  rewrite - (N2Nat.id lim) in Hj.
  rewrite - (N2Nat.id addr) in Hj.
  remember (N.to_nat addr) as addr'.
  remember (N.to_nat lim) as lim'.
  clear Heqaddr' Heqlim' lim addr.
  generalize dependent addr'. generalize dependent r.
  induction lim' => //=.
  intros.
  rewrite IHlim'.
  rewrite lookup_insert_ne => //.
  intros <-; lia.
  lia.
Qed.


Lemma gmap_of_segment_some s a i v :
  gmap_of_segment s a !! i = Some v ->
  s.(seg_data).(segl_data) !! (N.to_nat i) = Some v /\
    live_locations a !! i = Some () /\
  exists id addr size, allocated a !! id = Some (addr, size) /\
                    (i >= addr)%N /\ (i < addr + size)%N.
Proof.
  intros Hseg.
  unfold gmap_of_segment in Hseg.
  apply map_filter_lookup_Some in Hseg as [Hv Hi].
  repeat split => //.
  - rewrite gmap_of_list_lookup in Hv => //.
  - unfold live_locations in Hi.
    pose (P (res: gmap N ()) (a : gmap N (N*N)) := forall i, res !! i = Some () -> exists id addr size,
               a !! id = Some (addr, size) /\ (i >= addr )%N /\ (i < addr + size)%N).
    remember (map_fold _ _ _) as res.
    assert (P res (allocated a)) as H; last by apply H.
    subst res.
    apply (map_fold_ind P).
    done.
    intros i0 [addr lim] m r Hi0 Hm j Hj.
    destruct (j <? addr)%N eqn:Hj1.
    apply N.ltb_lt in Hj1.
    rewrite was_not_added in Hj; last by left.
    apply Hm in Hj as (id & addr' & lim' & Hid & Hsize).
    exists id, addr', lim'.
    split => //. rewrite lookup_insert_ne => //.
    intros ->; by rewrite Hi0 in Hid.
    destruct (addr + lim <=? j)%N eqn:Hj2.
    apply N.leb_le in Hj2.
    rewrite was_not_added in Hj; last by right; lia.
    apply Hm in Hj as (id & addr' & lim' & Hid & Hsize).
    exists id, addr', lim'.
    split => //. rewrite lookup_insert_ne => //.
    intros ->; by rewrite Hi0 in Hid.
    apply N.ltb_ge in Hj1. apply N.leb_gt in Hj2.
    exists i0, addr, lim.
    repeat split; try lia.
    by rewrite lookup_insert.
Qed.    
    
Definition all_live lo hi a : Prop :=
  forall i, (i >= lo)%N -> (i < hi)%N -> live_locations a !! i = Some ().
Definition one_live i a : Prop :=
  live_locations a !! i = Some ().

Lemma wss_is_segload h bv ws :
  length bv > 0 ->
  ( ↦[wss][ handle_addr h ] bv -∗
            ghost_map_auth segGName 1 (gmap_of_segment (s_segs ws) (s_alls ws))
            -∗ ⌜ segload (ws.(s_segs)) h (length bv) = Some bv /\
      all_live (handle_addr h) (handle_addr h + N.of_nat (length bv))%N
        (s_alls ws)⌝).
Proof.
  iIntros (Ht) "Hwss Hs".
  iAssert ( (∀ i, ⌜ i < length bv ⌝ -∗
                          ⌜ (segl_data (seg_data (s_segs ws))) !! (N.to_nat (handle_addr h + N.of_nat i))
                  = bv !! i /\ one_live (handle_addr h + N.of_nat i)%N (s_alls ws) ⌝)%I ) as "%Hseq".
  { iIntros (i) "%Hi".
    iDestruct (big_sepL_lookup with "Hwss") as "H" => //.
    destruct (nth_lookup_or_length bv i (bytes.encode 1, Numeric)) => //=.
    lia.
    iDestruct (ghost_map_lookup with "Hs H") as "%H".
    apply gmap_of_segment_some in H as (Hdata & Hlive & id & addr & size & Hid & Hsize1 & Hsize2).
    iPureIntro. replace (N.to_nat (handle_addr h + N.of_nat i)) with
      (N.to_nat (handle_addr h) + i). rewrite Nat2N.id in Hdata. rewrite Hdata.
    split => //. apply Logic.eq_sym.
    destruct (nth_lookup_or_length bv i (bytes.encode 1, Numeric)) => //=.
    lia. replace (handle_addr h + N.of_nat i)%N with
      (N.of_nat (N.to_nat (handle_addr h) + i)) => //.
    lia. lia. }
  
  iPureIntro.
  unfold segload.

  replace (handle_addr h + N.of_nat (length bv) <=? operations.seg_length (s_segs ws))%N with true.
  split.
  - unfold read_segbytes, seg_lookup.
    apply those_map_Some => //=.
    intros.
    rewrite nth_error_lookup. by apply Hseq.
  - intros i Hi1 Hi2.
    replace i with (handle_addr h + N.of_nat (N.to_nat (i - handle_addr h)))%N.
    apply Hseq. lia. lia.
  - apply Logic.eq_sym, N.leb_le.
    assert (segl_data (seg_data (s_segs ws)) !! N.to_nat (handle_addr h + N.of_nat (length bv - 1)) =
              bv !! (length bv - 1)).
    + apply Hseq ; first lia.
    + destruct (nth_lookup_or_length bv (length bv - 1) (bytes.encode 1, Numeric)) => //=. 
      rewrite e in H.
      apply segment_in_bounds in H. unfold lt in H.
      replace (S (N.to_nat (handle_addr h + N.of_nat (length bv - 1)))) with
        (N.to_nat (handle_addr h + N.of_nat (length bv))) in H.
      unfold operations.seg_length. lia.
      rewrite <- N2Nat.inj_succ. 
      rewrite <- N.add_succ_r. 
      rewrite <- Nat2N.inj_succ. lia. lia.
Qed.



Lemma allocated_implies_is_in_allocator a i x:
  ghost_map_auth allGName 1 (gmap_of_allocator a) -∗
    i ↣[allocated] x -∗ ⌜ a.(allocated) !! i = Some x ⌝.
Proof.
  iIntros "Ha Hi".
  iDestruct (ghost_map_lookup with "Ha Hi") as "%H".
  iPureIntro.
  done.
Qed.

 Lemma in_allocated_implies_isAlloc i x a:
  a.(allocated) !! i = Some x -> isAlloc i a.
 Proof.
   unfold isAlloc, find. intro H; rewrite H; done.
Qed. 




Lemma wp_segload_deserialize (Φ:iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t:value_type) (bv:bytes) (tbv: list (byte * btag))
  (h: handle) (f0: frame) (x: N*N) :
  t <> T_handle ->
  length tbv = t_length t ->
  List.map fst tbv = bv ->
  valid h = true ->
  ((offset h) + N.of_nat (t_length t) <= bound h)%N ->

  (▷ Φ (immV [wasm_deserialise bv t]) ∗
   ↪[frame] f0 ∗ h.(id) ↣[allocated] x ∗ 
      ↦[wss][ handle_addr h ] tbv ⊢
     (WP [AI_basic (BI_const (VAL_handle h)) ;
          AI_basic (BI_segload t)] @ s; E {{ w, (Φ w ∗ h.(id) ↣[allocated] x ∗ ↦[wss][ handle_addr h ]tbv) ∗ ↪[frame] f0 }})).
Proof.
  iIntros (Ht Htv Hfst Hvalid Hhi) "(HΦ & Hf0 & Halloc & Hwss)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & Ha & ? & Hframe & Hγ)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  destruct tbv eqn:Hb. destruct t => //.
  rewrite <- Hb.
  iDestruct (wss_is_segload with "Hwss Hs") as "%Hsegload" => //=.
  { rewrite Hb. simpl;lia. }
  destruct Hsegload as [Hsegload Hlive].
  rewrite -Hb in Htv.
  rewrite Htv in Hsegload.
  iDestruct (allocated_implies_is_in_allocator with "Ha Halloc") as "%Halloc".
  apply in_allocated_implies_isAlloc in Halloc.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_basic (BI_const _)], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_segload_success => //.
    repeat rewrite nat_bin. lias.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) |  [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 &
                                                                  Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_segload_success => //=);
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    inversion H;subst. iFrame. done.
    repeat rewrite nat_bin. lias.
Qed.

Lemma wp_segload (Φ:iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t:value_type) (v:value)
      h tbv x (f: frame):
  t <> T_handle ->
  types_agree t v ->
  List.map fst tbv = (bits v) ->
  valid h = true ->
  ((offset h) + N.of_nat (t_length t) <= bound h)%N ->
  (▷ Φ (immV [v]) ∗
   ↪[frame] f ∗ h.(id) ↣[allocated] x ∗
     ↦[wss][ handle_addr h ]
     tbv ⊢
     (WP [AI_basic (BI_const (VAL_handle h)) ;
          AI_basic (BI_segload t)] @ s; E {{ w, (Φ w ∗ id h ↣[allocated] x ∗ ↦[wss][ handle_addr h ]tbv) ∗ ↪[frame] f }})).
Proof.
  iIntros (Ht Htv Htbv Hvalid Hhi) "(HΦ & Hf0 & Halloc & Hwss)".
  iApply wp_segload_deserialize;auto.
  { rewrite - (map_length fst). rewrite Htbv. erewrite length_bits;eauto. }
  rewrite Htbv deserialise_bits;auto. iFrame.
Qed.

Lemma wp_segload_handle_deserialize (Φ:iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t:value_type) (bv:bytes) (tbv: list (byte * btag))
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
  (▷ Φ (immV [VAL_handle (upd_handle_validity hmem bc)]) ∗
   ↪[frame] f0 ∗ h.(id) ↣[allocated] x ∗
      ↦[wss][ handle_addr h ] tbv ⊢
     (WP [AI_basic (BI_const (VAL_handle h)) ;
          AI_basic (BI_segload t)] @ s; E {{ w, (Φ w ∗ h.(id) ↣[allocated] x ∗ ↦[wss][ handle_addr h ]tbv) ∗ ↪[frame] f0 }})).
Proof.
  iIntros (Ht Htv Hfst Hsnd Hvalid Hhi Hmod Hser Hbc) "(HΦ & Hf0 & Halloc & Hwss)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & Ha & ? & Hframe & Hγ)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  destruct tbv eqn:Hb.
  simpl in Htv. destruct HHB. simpl in Htv.
  assert (ssrnat.leq 1 (ssrnat.nat_of_bin handle_size)) => //.
  rewrite <- Htv in H. lias.
  rewrite <- Hb.
  iDestruct (wss_is_segload with "Hwss Hs") as "%Hsegload" => //=.
  { rewrite Hb. simpl;lia. }
  destruct Hsegload as [Hsegload Hlive].
  rewrite -Hb in Htv.
  rewrite Htv in Hsegload. 
  iDestruct (allocated_implies_is_in_allocator with "Ha Halloc") as "%Halloc".
  apply in_allocated_implies_isAlloc in Halloc.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_basic (BI_const _)], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_segload_handle_success => //.
    repeat rewrite nat_bin. lias.
    
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) |  [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 &
                                                                  Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_segload_handle_success => //);
      try by unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    inversion H;subst. unfold wasm_deserialise in Hser.
    inversion Hser; subst. iFrame.
    done.
    repeat rewrite nat_bin. lias.
Qed.

Lemma wp_segload_handle (Φ:iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t:value_type) hmem
      h tbv x (f: frame) bc ts:
  t = T_handle ->
  List.map fst tbv = (bits (VAL_handle hmem)) ->
  List.map snd tbv = ts ->
  valid h = true ->
  ((offset h) + N.of_nat (t_length T_handle) <= bound h)%N ->
  (N.modulo (handle_addr h) (N.of_nat (t_length T_handle)) = N.of_nat 0)%N ->
  bc = List.forallb (fun x => match x with Handle => true | _ => false end) ts ->
  (▷ Φ (immV [VAL_handle (upd_handle_validity hmem bc)]) ∗
   ↪[frame] f ∗ h.(id) ↣[allocated] x ∗
     ↦[wss][ handle_addr h ]
     tbv ⊢
     (WP [AI_basic (BI_const (VAL_handle h)) ;
          AI_basic (BI_segload t)] @ s; E {{ w, (Φ w ∗ id h ↣[allocated] x ∗ ↦[wss][ handle_addr h ]tbv) ∗ ↪[frame] f }})).
Proof.
  iIntros (Ht Htv Hts Hvalid Hhi Hmod Hbc) "(HΦ & Hf0 & Halloc & Hwss)".
  iApply wp_segload_handle_deserialize;auto.
  { rewrite - (map_length fst). rewrite Htv. erewrite length_bits;eauto. by rewrite Ht. }
  rewrite Htv deserialise_bits;auto. by rewrite Ht.
  rewrite Hbc Hts. iFrame. 
Qed.

Lemma wp_segload_failure (Φ: iris.val -> iProp Σ) (s:stuckness) (E:coPset) (t: value_type) h (f: frame):
  valid h = false \/ (offset h + N.of_nat (t_length t) > bound h)%N \/ t = T_handle /\ (N.modulo (handle_addr h) handle_size <> N.of_nat 0)%N ->
  (▷ Φ trapV ∗ ↪[frame] f ⊢
     (WP [AI_basic (BI_const (VAL_handle h)); AI_basic (BI_segload t)] @ s; E {{ w, Φ w ∗ ↪[frame] f }}))%I.
Proof.
  iIntros (Hfail) "[HΦ Hf0]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & ? & ? & Hframe & ?)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  simplify_map_eq.
  iSplit.
  + iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_trap], (_, locs, winst), [].
    repeat split => //.
    eapply rm_segload_failure => //.
    destruct Hfail as [Hfail | [Hfail | [-> Hfail]]].
    * by left.
    * right; left.
      unfold ssrnat.leq. unfold ssrnat.subn, ssrnat.addn.
      unfold ssrnat.subn_rec, ssrnat.addn_rec.
      apply /eqP.
      assert (S (N.to_nat (bound h)) - (N.to_nat (offset h) + t_length t) = 0).
      lia.
      by do 2 rewrite nat_bin.
    * repeat right; split => //. unfold t_length.
      rewrite nat_bin. rewrite N2Nat.id. done.
  + iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws2 locs2] winst2].
(*    rewrite -nth_error_lookup in Hm. *)
    iModIntro.
    prim_split κ HStep HStep. 
    eapply reduce_det in HStep as [H | [ (? & Hfirst & ?) | [ [? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                                Hfirst3 & Hσ & Hme)]]] ;
        last (eapply rm_segload_failure => //=) ;
        try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    inversion H ; subst; clear H => /=.
    iFrame.
     destruct Hfail as [Hfail | [Hfail | [-> Hfail]]].
    * by left.
    * right; left.
      unfold ssrnat.leq. unfold ssrnat.subn, ssrnat.addn.
      unfold ssrnat.subn_rec, ssrnat.addn_rec.
      apply /eqP.
      assert (S (N.to_nat (bound h)) - (N.to_nat (offset h) + t_length t) = 0).
      lia.
      by do 2 rewrite nat_bin.
    * repeat right; split => //. unfold t_length.
      rewrite nat_bin. rewrite N2Nat.id. done.
Qed.   
                                                                                  
                                                                              


Lemma seg_update_length dat dat' k b:
  seg_update k b dat = Some dat' -> length (segl_data dat) = length (segl_data dat').
Proof.
  intros Hupd.
  unfold seg_update in Hupd.
  destruct ( _ <? _)%N eqn:Hl ; inversion Hupd; clear Hupd.
  subst => /=.
  repeat rewrite app_length => /=.
  apply N.ltb_lt in Hl.
  rewrite take_length_le; last lia. 
  rewrite drop_length => //=. lia.
Qed.

Lemma if_segload_then_segstore bs bs' m h:
  length bs = length bs' ->
  segload m h (length bs) = Some bs ->
  exists m', segstore m h bs' (length bs') = Some m'.
Proof.
  intros Hlen Hload.
  unfold segstore, write_segbytes, fold_lefti.
  unfold segload, read_segbytes in Hload.
  rewrite - Hlen.
  destruct (_ <=? _)%N eqn:Hklen ; try by inversion Hload.
  cut (forall i dat,
          length (segl_data dat) = length (segl_data (seg_data m)) ->
          i <= length bs ->
          let j := length bs - i in
          those (map (λ off0, seg_lookup (handle_addr h + N.of_nat off0)%N (seg_data m))
                     (iota j i)) = Some (drop j bs) ->
          exists dat', (let '(_, acc_end) :=
                     fold_left
                       (λ '(k0, acc) x,
                         (k0 + 1,
                           match acc with
                           | Some dat => seg_update (handle_addr h + N.of_nat k0)%N x dat
                           | None => None
                           end)) (tagged_bytes_takefill (#00%byte, Numeric) i (drop j bs'))
                       (j, Some dat) in acc_end) = Some dat').
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    eapply Hi in H as [dat' Hdat'].
    + rewrite PeanoNat.Nat.sub_diag in Hdat'.
      unfold drop in Hdat'.
      rewrite Hdat'.
      by eexists _.
    + done.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      exact Hload.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite Hlen.
      rewrite drop_all.
      simpl.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs') eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs') = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H3. lia.
      * destruct (drop (length bs - S i) bs) eqn:Hdrop0.
        **  assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop0.
            rewrite drop_length in H3. lia.
        ** assert (exists dat0, seg_update (handle_addr h + N.of_nat (length bs - S i))%N p dat =
                             Some dat0) as [dat0 Hdat0].
           { unfold seg_update.
             assert (handle_addr h + N.of_nat (length bs - S i) <
                       N.of_nat (length (segl_data dat)))%N.
             rewrite H.
             unfold operations.seg_length, segment_list.seg_length in Hklen.
             apply N.leb_le in Hklen.
             lia.
             apply N.ltb_lt in H3.
             rewrite H3.
             by eexists _. } 
           eapply (IHi dat0) in H2 as [dat' Hdat'].
        ++ simpl.
           replace (length bs - i) with (length bs - S i + 1) in Hdat' ; last lia.
           rewrite - drop_drop in Hdat'.
           rewrite Hdrop in Hdat'.
           unfold drop in Hdat'.
           rewrite Hdat0.
           rewrite Hdat'.
           by eexists _.
        ++ rewrite - H.
           erewrite <- seg_update_length ; last exact Hdat0.
           done.
        ++ simpl in H1.
           rewrite - those_those0 in H1.
           unfold those0 in H1.
           fold (those0 (A:=byte*btag)) in H1.
           rewrite those_those0 in H1.
           destruct (seg_lookup _ _) ; try by inversion H1.
           unfold option_map in H1.
           destruct (those (map (λ off0, seg_lookup (handle_addr h + N.of_nat off0)%N
                                (seg_data m))
                                (iota (S (length bs - S i)) i)) )
                    eqn:Hth ; try by inversion H1.
           replace (S (length bs - S i)) with (length bs - i) in Hth ; last lia.
           rewrite Hth.
           inversion H1.
           replace (length bs - i) with (length bs - S i + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop0 => //=.
Qed.

Lemma wss_append k b bs :
  ⊢ (↦[wss][k] (b :: bs) ∗-∗ ( ↦[ws][k] b ∗ ↦[wss][N.add k 1%N] bs))%I.
Proof.
  iSplit.
  - iIntros "Hwms". unfold seg_block_at_pos, big_opL. rewrite Nat.add_0_r.
    rewrite N2Nat.id.
    fold (big_opL (M := iPropI Σ)).
    iDestruct "Hwms" as "[Hwm Hwms]".
    iSplitL "Hwm" => //=.
    iApply (big_sepL_impl with "Hwms").
    iIntros (k0 x) "!> %Hx Hwm".
    replace (N.to_nat k + S k0) with (N.to_nat (k+1) + k0) => //=.
    lia.
  - iIntros "[Hwm Hwms]". unfold seg_block_at_pos, big_opL.
    rewrite Nat.add_0_r N2Nat.id.
    fold (big_opL (M := iPropI Σ)).
    iSplitL "Hwm" => //=.
    iApply (big_sepL_impl with "Hwms").
    iIntros (k0 x) "!> %Hx Hwm".
    replace (N.to_nat (k+1) + k0) with (N.to_nat k + S k0) => //=.
    lia.
Qed.

Definition plus_one h :=
  {| base := base h ; offset := offset h + 1 ; bound := bound h ; valid := valid h;
                                                                  id := id h |}.

Lemma handle_addr_plus_one h :
  handle_addr (plus_one h) = (handle_addr h + 1)%N.
Proof.
  unfold handle_addr, plus_one => /=. lia.
Qed. 
                                               

Lemma segstore_length (m m': segment) h bs :
  segstore m h bs (length bs) = Some m' -> 
  length m.(seg_data).(segl_data) = length m'.(seg_data).(segl_data).
Proof.
  intros.
  unfold segstore, write_segbytes, fold_lefti in H.
  destruct (_ <=? _)%N eqn:Hlen ; try by inversion H.
  cut (forall j dat dat',
          j <= length bs ->
          let i := length bs - j in
          (let '(_,acc_end) :=
            fold_left
              (λ '(k, acc) x,
                (k + 1,
                  match acc with
                  | Some dat => seg_update (handle_addr h + N.of_nat k)%N x dat
                  | None => None
                  end)) (tagged_bytes_takefill (#00%byte, Numeric) j (drop i bs))
              (i, Some dat) in acc_end) = Some dat' ->
                               length (segl_data dat) = length (segl_data (seg_data m)) ->
                               length (segl_data dat') = length (segl_data (seg_data m))).
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    destruct (let '(_, acc_end) := fold_left _ _ _ in acc_end) eqn:Hfl ; try by inversion H.
    eapply (Hi _ (seg_data m) s) in H0 => //=.
    + destruct m' ; inversion H ; by subst. 
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      exact Hfl.
  - induction j ; intros ; subst i.
    + rewrite Nat.sub_0_r in H1.
      rewrite drop_all in H1.
      simpl in H1. inversion H1. by rewrite - H4.
    + assert (j <= length bs) ; first lia.
      destruct (drop (length bs - S j) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S j) bs) = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H4. lia.
      * assert (exists dat0, seg_update (handle_addr h + N.of_nat (length bs - S j))%N
                                   p dat = Some dat0) as [dat0 Hdat0].
         { unfold seg_update. apply N.leb_le in Hlen.
           assert (handle_addr h + N.of_nat (length bs - S j) <
                     N.of_nat (length (segl_data dat)))%N.
           rewrite H2.
           unfold operations.seg_length, segment_list.seg_length in Hlen.
           lia.
           apply N.ltb_lt in H4.
           rewrite H4.
           by eexists _. } 
        apply (IHj dat0 dat') in H3.
        ++ done.
        ++ simpl in H1.
           rewrite Hdat0 in H1.
           replace (length bs - j) with (length bs - S j + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop.
           unfold drop => //=.
        ++ erewrite <- seg_update_length => //=.
Qed.

Lemma segstore_seg_max_opt (m m' : segment) h bs l :
  segstore m h bs l = Some m' ->
  seg_max_opt m = seg_max_opt m'.
Proof.
  intros.
  unfold segstore in H.
  destruct ( _ <=? _)%N ; try by inversion H.
  unfold write_segbytes in H.
  destruct (fold_lefti _ _ _) ; try by inversion H.
Qed.


Lemma segstore_append1 m h b bs m':
  segstore m h (b :: bs) (length (b :: bs)) = Some m' ->
  exists m'', segstore m'' (plus_one h) bs (length bs) = Some m' /\
           segstore m h [b] 1 = Some m''.
Proof.
  intros Hstore.
  unfold segstore.
  unfold segstore in Hstore.
  destruct (handle_addr h + N.of_nat (length (b :: bs)) <=? operations.seg_length m)%N eqn:Hlen ;
    try by inversion Hstore.
  apply N.leb_le in Hlen.
  simpl in Hlen.
  assert (handle_addr h + N.of_nat 1 <= operations.seg_length m)%N ; first lia.
  apply N.leb_le in H.
  rewrite H.
  unfold write_segbytes, fold_lefti => //=.
  rewrite N.add_0_r.
  unfold seg_update.
  unfold operations.seg_length, segment_list.seg_length in H.
  apply N.leb_le in H.
  assert (handle_addr h < N.of_nat (length (segl_data (seg_data m))))%N ; first lia.
  apply N.ltb_lt in H0.
  rewrite H0.
  eexists _ ; split => //=.
  remember {| seg_data := _ ; seg_max_opt := _ |} as m''.
  assert (segstore m h [b] 1 = Some m'').
  { subst. unfold segstore. apply N.leb_le in H. rewrite H.
    unfold write_segbytes, fold_lefti => //=.
    unfold seg_update. rewrite N.add_0_r.
    rewrite H0. done. }
  assert (operations.seg_length m'' = operations.seg_length m).
  { unfold operations.seg_length, segment_list.seg_length.
    erewrite <- segstore_length => //=.
    by instantiate (1 := [b]) => //=. }
  assert (seg_max_opt m'' = seg_max_opt m) as Hmax; first by 
    eapply Logic.eq_sym, segstore_seg_max_opt.  
  rewrite H2.
  assert (handle_addr (plus_one h) + N.of_nat (length bs) <= operations.seg_length m)%N.
  { rewrite handle_addr_plus_one => //. lia. } 
  apply N.leb_le in H3. rewrite H3.
  unfold write_segbytes, fold_lefti in Hstore.
  simpl in Hstore.
  rewrite N.add_0_r in Hstore.
  replace (seg_update (handle_addr h) b (seg_data m)) with (Some (seg_data m'')) in Hstore.
  rewrite <- (plus_O_n 1) in Hstore.
  destruct (fold_left _ _ (0 + 1, _)) eqn:Hfl ; try by inversion Hstore.
  rewrite (fold_left_lift _ (λ '(k0, acc) x,
                              (k0 + 1,
                                match acc with
                                | Some dat =>
                                    if (handle_addr (plus_one h) + N.of_nat k0 <?
                                          N.of_nat (length (segl_data dat)))%N
                                    then
                                      Some {| segl_data :=
                                             take (N.to_nat (handle_addr (plus_one h) +
                                                                   N.of_nat k0))
                                                      (segl_data dat) ++
                                                      x :: drop (N.to_nat (handle_addr (plus_one h) + N.of_nat k0) + 1)
                                                      (segl_data dat)
                                           |}
                                    else None
                                | None => None
                                end)))
    in Hfl.
  apply incr_fst_equals in Hfl.
  rewrite Hfl.
  rewrite Hmax.
  done.
  intros. unfold incr_fst => //=.
  unfold mem_update.
  replace (handle_addr h + N.of_nat (i+1))%N with (handle_addr (plus_one h) + N.of_nat i)%N.
  2:{ rewrite handle_addr_plus_one => //. lia. } 
  done.
  unfold segstore in H1.
  apply N.leb_le in H.
  rewrite H in H1.
  unfold write_segbytes, fold_lefti in H1.
  simpl in H1.
  rewrite N.add_0_r in H1.
  destruct (seg_update (handle_addr h) b (seg_data m)) eqn:Hupd ; try by inversion H1.
Qed.

Lemma enough_space_to_segstore m h bs :
  (handle_addr h + N.of_nat (length bs) <= operations.seg_length m)%N ->
  exists mf, segstore m h bs (length bs) = Some mf.
Proof.
  intros Hmlen.
  unfold segstore.
  apply N.leb_le in Hmlen.
  rewrite Hmlen.
  unfold write_segbytes, fold_lefti. 
  cut (forall i dat,
          i <= length bs ->
          length (segl_data dat) = N.to_nat (operations.seg_length m) ->
          let j := length bs - i in
          exists datf, (let '(_, acc_end) :=
                      fold_left (λ '(k0,acc) x,
                                  (k0 + 1,
                                    match acc with
                                    | Some dat => seg_update (handle_addr h + N.of_nat k0)%N x dat
                                    | None => None
                                    end)) (tagged_bytes_takefill (#00%byte, Numeric) (length (drop j bs))
                                                          (drop j bs))
                                (j, Some dat) in acc_end) = Some datf).
  - intros H.
    assert (length bs <= length bs) ; first lia.
    apply (H _ (seg_data m)) in H0 as [datf' Hdatf'].
    + rewrite PeanoNat.Nat.sub_diag in Hdatf'.
      unfold drop in Hdatf'.
      rewrite Hdatf'.
      by eexists _.
    + unfold operations.seg_length, segment_list.seg_length.
      by rewrite Nat2N.id.
  - induction i ; intros ; subst j.
    + rewrite <- minus_n_O.
      rewrite drop_all => //=.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H2. lia.
      * assert (exists datupd,
                   seg_update (handle_addr h + N.of_nat (length bs - S i))%N p dat =
                     Some datupd ) as [datupd Hdatupd].
        { unfold seg_update.
           apply N.leb_le in Hmlen.
           assert ( handle_addr h + N.of_nat (length bs - S i) <
                      N.of_nat (length (segl_data dat)))%N ;
             first lia.
           apply N.ltb_lt in H2 ; rewrite H2.
           by eexists _. }
        eapply (IHi datupd) in H1 as [datf Hdatf].
        ++ rewrite - Hdrop. rewrite drop_length.
           rewrite <- (list.take_drop 1 (drop (length bs - S i) bs)). 
           rewrite drop_drop. 
           rewrite Hdrop.
           unfold take.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           replace (length bs - (length bs - S i)) with (S i) ; last lia.
           simpl.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           rewrite drop_length in Hdatf.
           replace (length bs - (length bs - i)) with i in Hdatf ; last lia.
           rewrite Hdatupd.
           rewrite Hdatf.
           by eexists _.
        ++ rewrite <- H0.
           by erewrite <- seg_update_length.
Qed.



Lemma seg_update_insert k b dat dat':
  seg_update k b dat = Some dat' ->
  dat' = Build_segment_list (<[(N.to_nat k) := b]> (segl_data dat)) /\
  (N.to_nat k) < length (segl_data dat).
Proof.
  unfold seg_update.
  destruct (k <? N.of_nat (length (segl_data dat)))%N eqn:Hk => //.
  move => Hupd.
  inversion Hupd; subst; clear Hupd.
  apply N.ltb_lt in Hk.
  split; last by lia.
  f_equal.
  rewrite - (list_insert_destruct (N.to_nat k) (segl_data dat) b) => //.
  2:lia.
  by rewrite take_seq_take drop_seq_drop.
Qed.

Lemma seg_update_swap k b dat k' b' dat' dat'' :
  k <> k' ->
  seg_update k b dat = Some dat' ->
  seg_update k' b' dat' = Some dat'' ->
  exists dat0, seg_update k' b' dat = Some dat0 /\
            seg_update k b dat0 = Some dat''.
Proof.
  intros Hkk' Hupd Hupd'.
  apply seg_update_insert in Hupd as [Hupd Hk].
  apply seg_update_insert in Hupd' as [Hupd' Hk'].
  assert (length (segl_data dat) = length (segl_data dat')) as Hupdlen.
  { subst => /=.
    by rewrite insert_length.
  }
  exists (Build_segment_list (<[(N.to_nat k') := b']> (segl_data dat))).
  unfold seg_update.
  assert (k' <? N.of_nat (length (segl_data dat')))%N as Hk'0.
  { apply N.ltb_lt. lia. }
  assert (k <? N.of_nat (length (segl_data dat)))%N as Hk0.
  { apply N.ltb_lt. lia. }
  rewrite Hupdlen Hk'0 insert_length Hk0 => /=.
  subst.
  split; (do 2 f_equal); rewrite - list_insert_destruct; try lias;  try by (rewrite take_seq_take drop_seq_drop; lias).
  rewrite list_insert_destruct; last by lias.
  simpl.
  rewrite list_insert_commute; last by lias.
  rewrite - (list_insert_destruct (N.to_nat k)) => //.
  2:by rewrite insert_length.
  by rewrite take_seq_take drop_seq_drop.
Qed.
  
Lemma swap_segstores m m' m'' h b bs :
  segstore m h [b] 1 = Some m' ->
  segstore m' (plus_one h) bs (length bs) = Some m'' ->
  exists m0, segstore m (plus_one h) bs (length bs) = Some m0 /\
          segstore m0 h [b] 1 = Some m''.
Proof.
  intros.
  assert (operations.seg_length m = operations.seg_length m') as Hmlen ;
    first (unfold operations.seg_length, segment_list.seg_length ; erewrite segstore_length => //= ;
          by instantiate (1:=[b]) => //=).
  unfold segstore in H0.
  destruct (handle_addr (plus_one h) + N.of_nat (length (bs)) <=? operations.seg_length m')%N eqn:Hlen;
    last by inversion H0.
  apply N.leb_le in Hlen.
  rewrite <- Hmlen in Hlen.
  destruct (enough_space_to_segstore m (plus_one h) (bs)) as [m0 Hm0] => //=.
  exists m0 ; split => //=.
  unfold segstore, write_segbytes, fold_lefti => //=.
  assert (operations.seg_length m = operations.seg_length m0) as Hmlen0 ;
    first by unfold operations.seg_length, segment_list.seg_length ; erewrite segstore_length.
  rewrite Hmlen0 in Hlen.
  unfold plus_one in Hlen; simpl in Hlen.
  assert (handle_addr h + 1 <= operations.seg_length m0)%N. 
  { rewrite handle_addr_plus_one in Hlen => //. lia. }
  apply N.leb_le in H1 ; rewrite H1.
  rewrite N.add_0_r.
  unfold seg_update.
  apply N.leb_le in H1.
  assert (handle_addr h < N.of_nat (length (segl_data (seg_data m0))))%N ;
    first by unfold operations.seg_length, segment_list.seg_length in H1 ; lia.
  apply N.ltb_lt in H2.
  rewrite H2.
  rewrite - H0.
  unfold write_segbytes, fold_lefti.
  unfold segstore, write_segbytes, fold_lefti in H.
  rewrite - Hmlen0 in H1.
  apply N.leb_le in H1 ; rewrite H1 in H.
  simpl in H.
  rewrite N.add_0_r in H.
  unfold seg_update in H.
  replace (length (segl_data (seg_data m0))) with (length (segl_data (seg_data m)))
    in H2 ; last by eapply segstore_length.
  rewrite H2 in H.
  inversion H.
  unfold segstore in Hm0.
  rewrite - Hmlen0 in Hlen.
  apply N.leb_le in Hlen ; rewrite Hlen in Hm0.
  unfold write_segbytes, fold_lefti in Hm0.
  destruct (fold_left _ _ _) eqn:Hfl.
  destruct o ; inversion Hm0.
  simpl.
  assert (s = seg_data m0) ; first by rewrite - H5.
  cut (forall i dat datf n,
          i <= length bs ->
          length (segl_data dat) = N.to_nat (operations.seg_length m) ->
          let j := length bs - i in
          fold_left (λ '(k0, acc) x,
                      (k0 + 1,
                        match acc with
                        | Some dat => seg_update (handle_addr (plus_one h) + N.of_nat k0)%N x dat
                        | None => None
                        end)) (tagged_bytes_takefill (#00%byte, Numeric) (length (drop j bs))
                                              (drop j bs))
                    (j, Some dat) = (n, Some datf) ->
          exists m, fold_left (λ '(k0, acc) x,
                           (k0 + 1,
                             match acc with
                             | Some dat => seg_update (handle_addr (plus_one h) + N.of_nat k0)%N
                                                     x dat
                             | None => None
                             end)) (tagged_bytes_takefill (#00%byte, Numeric) (length (drop j bs))
                                                   (drop j bs))
                         (j, seg_update (handle_addr h) b dat) =
                 (m, seg_update (handle_addr h) b datf)).
  - intros Hi.
    assert (length bs <= length bs) as Hlbs; first lia.
    apply (Hi _ (seg_data m) s n) in Hlbs as [nn Hia].
    + rewrite PeanoNat.Nat.sub_diag in Hia.
      unfold drop in Hia.
      unfold seg_update in Hia.
      rewrite H2 in Hia.
      rewrite Hia.
      rewrite H3.
      unfold operations.seg_length, segment_list.seg_length in Hmlen0 ; rewrite Hmlen0 in H2 ;
        rewrite H2.
      done.
    + unfold seg_length, segment_list.seg_length.
      by rewrite Nat2N.id.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      done.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite drop_all.
      simpl.
      rewrite Nat.sub_0_r in H8.
      rewrite drop_all in H8.
      simpl in H8.
      inversion H8.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite drop_length in H10. lia.
      * assert (exists dat', seg_update (handle_addr h) b dat = Some dat') as [dat' Hdat'].
        { unfold seg_update. rewrite H7 Nat2N.id H2. by eexists _. }
        assert (exists dat'',
                   seg_update (handle_addr (plus_one h) + N.of_nat (length bs - S i))%N p dat'
                   = Some dat'') as [dat'' Hdat''].
        { unfold seg_update.
          erewrite <- seg_update_length => //=.
          rewrite H7 Nat2N.id.
          apply N.leb_le in Hlen.
          assert (handle_addr (plus_one h) + N.of_nat (length bs - S i) < N.of_nat (length (segl_data (seg_data m))))%N.
          { unfold operations.seg_length, segment_list.seg_length in Hlen.
            assert (N.of_nat (length bs - S i) < N.of_nat (length bs))%N ; try lia.
            rewrite handle_addr_plus_one => //. 
            unfold handle_addr in Hlen.
            simpl in Hlen. unfold handle_addr. lias.
          }
          apply N.ltb_lt in H10.
          rewrite H10.
          by eexists _. }
        rewrite - Hdrop.
        assert (handle_addr h <> handle_addr (plus_one h) + N.of_nat (length bs - S i))%N.
        { rewrite handle_addr_plus_one => //. lia. }
        destruct (seg_update_swap _ _ _ _ _ _ _ H10 Hdat' Hdat'')
          as (dat0 & Hdat0 & Hdat0'') => //=.
        eapply (IHi dat0) in H9 as [nn Hflf].
        ++ rewrite drop_length.
           rewrite <- (list.take_drop 1 (drop (length bs - S i) bs)).
           rewrite drop_drop.
           rewrite Hdrop.
           unfold take.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           replace (length bs - (length bs - S i)) with (S i) ; last lia.
           simpl.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           rewrite drop_length in Hflf.
           replace (length bs - (length bs - i)) with i in Hflf ; last lia.
           rewrite Hdat' Hdat''.
           rewrite - Hdat0''.
           rewrite Hflf.
           by eexists _.
        ++ erewrite <- seg_update_length => //=.
        ++ rewrite - Hdrop in H8.
           rewrite drop_length in H8.
           replace (length bs - (length bs - S i)) with (S i) in H8 ; last lia.
           rewrite drop_length.
           replace (length bs - (length bs - i)) with i ; last lia.
           rewrite Hdrop in H8.
           simpl in H8.
           rewrite Hdat0 in H8.
           replace (length bs - i) with (length bs - S i + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop.
           unfold drop => //=.
Qed.

Lemma segstore_append m h b bs m':
  segstore m h (b :: bs) (length (b :: bs)) = Some m' ->
  exists m'', segstore m (plus_one h) bs (length bs) = Some m'' /\
           segstore m'' h [b] 1 = Some m'.
Proof.
  intros Hm.
  apply segstore_append1 in Hm as (m0 & Hm0 & Hm0') => //.
  eapply swap_segstores => //=.
Qed.

Lemma segload_append m h b bs :
  segload m h (length (b :: bs)) = Some (b :: bs) ->
  segload m (plus_one h) (length bs) = Some bs.
Proof.
  unfold segload ; intros Hm.
  replace (handle_addr h + N.of_nat (length (b :: bs)))%N with
    (handle_addr (plus_one h) + N.of_nat (length bs))%N in Hm.
  2:{ rewrite handle_addr_plus_one => //. simpl. lia. }
  destruct (handle_addr (plus_one h) + N.of_nat (length bs) <=? operations.seg_length m)%N eqn:Hleq; try by inversion Hm.
  unfold read_segbytes. unfold read_segbytes in Hm. simpl in Hm.
  destruct (seg_lookup (handle_addr h + 0)%N (seg_data m)) ; inversion Hm.
  rewrite list_extra.cons_app in H0.
  destruct (those_app_inv [Some p] _ _ H0) as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  unfold those in Htl1. simpl in Htl1. inversion Htl1 ; subst ; clear Htl1.
  inversion Htl ; subst ; clear Htl.
  erewrite <- map_iota_lift => //=.
  intros. replace (handle_addr h + N.of_nat (x+1))%N with
    (handle_addr (plus_one h) + N.of_nat x)%N => //=.
  rewrite handle_addr_plus_one => //. lia.
Qed.

Lemma ghost_map_update_big_ws bs bs' h (m m' : segment) a:
  length bs = length bs' -> 
  segload m h (length bs) = Some bs ->
  segstore m h bs' (length bs') = Some m' ->
  (forall i, (i >= handle_addr h)%N -> (i < handle_addr h + N.of_nat (length bs))%N ->
        live_locations a !! i = Some ()) ->
  ghost_map_auth segGName 1 (gmap_of_segment m a) -∗
                  ↦[wss][handle_addr h] bs ==∗
                  ghost_map_auth segGName 1 (gmap_of_segment m' a) ∗
                  ↦[wss][handle_addr h] bs'.
Proof.
  move : m' h bs'.
  induction bs ; iIntros (m' h bs' Hlen Hm Hm' Ha) "Hσ Hwms".
  { simpl in Hlen. apply Logic.eq_sym, nil_length_inv in Hlen ; subst.
    iSplitR "Hwms" => //=. 
    simpl in Hm'. unfold segstore in Hm'.
    simpl in Hm. unfold segload in Hm.
    destruct (_ + N.of_nat 0 <=? operations.seg_length m)%N ; try by inversion Hm.
    unfold write_segbytes in Hm'. simpl in Hm'.
    destruct m ; simpl in Hm'.
    by inversion Hm'; subst.
  }
  destruct bs' ; inversion Hlen.
  iDestruct (wss_append with "Hwms") as "[Hwm Hwms]".
  destruct (segstore_append _ _ _ _ _ Hm') as (m'' & Hm'' & Hb).
  remember (plus_one h) as h'.
  replace (base h) with (base h'); last by subst; unfold plus_one.
  replace (handle_addr h + 1)%N with (handle_addr h').
  2:{ subst; rewrite handle_addr_plus_one => //. }
  iMod (IHbs with "Hσ Hwms") as "[Hσ Hwms]" => //.
(*  subst; unfold plus_one; simpl; lia. *)
  by subst; eapply segload_append.
  subst h'; simpl; intros. apply Ha.
  rewrite handle_addr_plus_one in H; lia.
  rewrite handle_addr_plus_one in H1; simpl; lia.
  iMod (ghost_map_update with "Hσ Hwm") as "[Hσ Hwm]". 
  iIntros "!>".
  iSplitR "Hwms Hwm".
  2:{ subst; rewrite handle_addr_plus_one => //; iApply wss_append ; iFrame. }
  unfold segstore in Hb.
  destruct (handle_addr h + N.of_nat 1 <=? operations.seg_length m'')%N eqn: Hlen0; try by inversion Hb.
  unfold write_segbytes, fold_lefti in Hb ; simpl in Hb.
  rewrite N.add_0_r in Hb.
  destruct (seg_update (handle_addr h) p (seg_data m'')) eqn:Hupd ; inversion Hb; clear Hb.
  erewrite gmap_of_segment_insert => //.
  - apply N.leb_le in Hlen0. unfold operations.seg_length, seg_length in Hlen0.
    subst; lias.
  - subst h'; simpl. apply Ha. lia. simpl. lia.
Qed.



Lemma wp_segstore (ϕ: iris.val -> iProp Σ) (s: stuckness) (E: coPset) (t: value_type) (v: value)
  tbs h (f: frame) x:
  t <> T_handle -> 
  types_agree t v ->
  length tbs = t_length t ->
  valid h = true ->
  ((offset h) + N.of_nat (t_length t) <= bound h)%N ->
  (▷ ϕ (immV []) ∗
   ↪[frame] f ∗ h.(id) ↣[allocated] x ∗
  ↦[wss][ handle_addr h ] tbs) ⊢
  (WP ([AI_basic (BI_const (VAL_handle h)); AI_basic (BI_const v); AI_basic (BI_segstore t)]) @ s; E {{ w, (ϕ w ∗ h.(id) ↣[allocated] x ∗ ↦[wss][ handle_addr h ] (List.map (fun b => (b, Numeric)) (bits v))) ∗ ↪[frame] f }}).
Proof.
  iIntros (Ht Hvt Htbs Hval Hhi) "(HΦ & Hf0 & Hid & Hwss)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & Hall & ? & Hframe & ? & ? & ? & ? & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  destruct tbs; first by destruct t => //.
  iDestruct (wss_is_segload with "Hwss Hs") as "%Hsegload" => //=.
  lia.
  destruct Hsegload as [Hsegload Hlive].
  iDestruct (allocated_implies_is_in_allocator with "Hall Hid") as "%Halloc".
  apply in_allocated_implies_isAlloc in Halloc.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    edestruct (if_segload_then_segstore (p :: tbs) (List.map (fun x => (x, Numeric)) (bits v))) as [seg Hsomeseg];eauto.
    { rewrite map_length Htbs. erewrite length_bits => //=. }
    rewrite map_length in Hsomeseg; erewrite length_bits in Hsomeseg => //=. 
    eexists [_], [], (_, locs, winst), [].
    repeat split => //.
    eapply rm_segstore_success => //=.
    repeat rewrite nat_bin. lias.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws2 locs2] winst2].
    edestruct (if_segload_then_segstore (p :: tbs) (List.map (fun x => (x, Numeric)) (bits v))) as [seg Hsomeseg] ; eauto;
      repeat rewrite map_length; repeat erewrite length_bits => //=.
    rewrite map_length in Hsomeseg. erewrite length_bits in Hsomeseg => //=.
    iMod (ghost_map_update_big_ws (p :: tbs) (List.map (fun x => (x, Numeric)) (bits v)) with "Hs Hwss") as "[Hs Hwss]" => //.
    rewrite map_length. erewrite length_bits => //=. eauto.
    rewrite map_length. erewrite length_bits => //=.
    iModIntro. prim_split κ HStep HStep.
    eapply reduce_det in HStep as [H | [( ? & Hfirst & ?) | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ & Hme) ]]] ;
      last (eapply rm_segstore_success => //=) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    inversion H ; subst; clear H => /=.
    iFrame.
(*    assert (operations.seg_length (s_segs ws)= operations.seg_length seg) as Hmsize.
    { rewrite <- (length_bits v) in Hsomeseg => //=. 
      rewrite - (map_length (fun x => (x, Numeric)) (bits v)) in Hsomeseg.
      apply segstore_length in Hsomeseg.
      by unfold operations.seg_length, seg_length; rewrite Hsomeseg. }  
    unfold operations.seg_length in Hmsize. rewrite Hmsize.
    apply segstore_seg_max_opt in Hsomeseg as Hseglimit. 
    rewrite - Hseglimit. 
    iFrame. *) iPureIntro.
    eapply (reduce_preserves_wellformedness (f := {| f_inst := winst2; f_locs := locs2 |})).
    exact HWF. eapply rm_segstore_success => //=.
    repeat rewrite nat_bin. lias.
    repeat rewrite nat_bin. lias.
Qed.

Lemma wp_segstore_handle (ϕ: iris.val -> iProp Σ) (s: stuckness) (E: coPset) (t: value_type) (v: value)
  tbs h (f: frame) x:
  t = T_handle -> 
  types_agree t v ->
  length tbs = t_length t ->
  valid h = true ->
  ((offset h) + N.of_nat (t_length T_handle) <= bound h)%N ->
  (N.modulo (handle_addr h) (N.of_nat (t_length T_handle)) = N.of_nat 0)%N ->
  (▷ ϕ (immV []) ∗
   ↪[frame] f ∗ h.(id) ↣[allocated] x ∗
  ↦[wss][ handle_addr h ] tbs) ⊢
  (WP ([AI_basic (BI_const (VAL_handle h)); AI_basic (BI_const v); AI_basic (BI_segstore t)]) @ s; E {{ w, (ϕ w ∗ h.(id) ↣[allocated] x ∗ ↦[wss][ handle_addr h ] (List.map (fun b => (b, Handle)) (bits v))) ∗ ↪[frame] f }}).
Proof.
  iIntros (Ht Hvt Htbs Hval Hhi Hallign) "(HΦ & Hf0 & Hid & Hwss)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & Hall & ? & Hframe & ? & ? & ? & ? & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  destruct tbs. specialize hsnz as H. simpl in Htbs. lia. 
  iDestruct (wss_is_segload with "Hwss Hs") as "%Hsegload" => //=.
  lia.
  destruct Hsegload as [Hsegload Hlive].
  iDestruct (allocated_implies_is_in_allocator with "Hall Hid") as "%Halloc".
  apply in_allocated_implies_isAlloc in Halloc.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    edestruct (if_segload_then_segstore (p :: tbs) (List.map (fun x => (x, Handle)) (bits v))) as [seg Hsomeseg];eauto.
    { rewrite map_length Htbs. erewrite length_bits => //=. done. }
    rewrite map_length in Hsomeseg; erewrite length_bits in Hsomeseg => //=. 
    eexists [_], [], (_, locs, winst), [].
    repeat split => //.
    eapply rm_segstore_handle_success => //.
    repeat rewrite nat_bin. lias.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws2 locs2] winst2].
    edestruct (if_segload_then_segstore (p :: tbs) (List.map (fun x => (x, Handle)) (bits v))) as [seg Hsomeseg] ; eauto;
      repeat rewrite map_length; repeat erewrite length_bits => //=.
    rewrite map_length in Hsomeseg. erewrite length_bits in Hsomeseg => //=.
    iMod (ghost_map_update_big_ws (p :: tbs) (List.map (fun x => (x, Handle)) (bits v)) with "Hs Hwss") as "[Hs Hwss]" => //.
    rewrite map_length. erewrite length_bits => //=. eauto.
    rewrite map_length. erewrite length_bits => //=.
    iModIntro. prim_split κ HStep HStep.
    eapply reduce_det in HStep as [H | [( ? & Hfirst & ?) | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ & Hme) ]]] ;
      last (eapply rm_segstore_handle_success => //) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    inversion H ; subst; clear H => /=.
    iFrame.
(*    assert (operations.seg_length (s_segs ws)= operations.seg_length seg) as Hmsize.
    { rewrite <- (length_bits v) in Hsomeseg => //=. 
      rewrite - (map_length (fun x => (x, Handle)) (bits v)) in Hsomeseg.
      apply segstore_length in Hsomeseg.
      by unfold operations.seg_length, seg_length; rewrite Hsomeseg. }  
    unfold operations.seg_length in Hmsize. rewrite Hmsize.
    apply segstore_seg_max_opt in Hsomeseg as Hseglimit.
    rewrite - Hseglimit.
    iFrame.*)  iPureIntro.
    eapply (reduce_preserves_wellformedness (f := {| f_inst := winst2; f_locs := locs2 |})).
    exact HWF. eapply rm_segstore_handle_success => //.
    repeat rewrite nat_bin. lias.
    repeat rewrite nat_bin. lias.
Qed.


Lemma wp_segstore_failure (Φ: iris.val -> iProp Σ) (s:stuckness) (E:coPset) v (t: value_type) h (f: frame):
  types_agree t v ->
  valid h = false \/ (offset h + N.of_nat (t_length t) > bound h)%N \/ t = T_handle /\ (N.modulo (handle_addr h) handle_size <> N.of_nat 0)%N ->
  (▷ Φ trapV ∗ ↪[frame] f ⊢
     (WP [AI_basic (BI_const (VAL_handle h)); AI_basic (BI_const v); AI_basic (BI_segstore t)] @ s; E {{ w, Φ w ∗ ↪[frame] f }}))%I.
Proof.
  iIntros (Htv Hfail) "[HΦ Hf0]".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & ? & ? & Hframe & ?)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  simplify_map_eq.
  iSplit.
  + iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_trap], (_, locs, winst), [].
    repeat split => //.
    eapply rm_segstore_failure => //.
    destruct Hfail as [Hfail | [Hfail | [-> Hfail]]].
    * by left.
    * right; left.
      unfold ssrnat.leq. unfold ssrnat.subn, ssrnat.addn.
      unfold ssrnat.subn_rec, ssrnat.addn_rec.
      apply /eqP.
      assert (S (N.to_nat (bound h)) - (N.to_nat (offset h) + t_length t) = 0).
      lia.
      by do 2 rewrite nat_bin.
    * repeat right; split => //. unfold t_length.
      rewrite nat_bin. rewrite N2Nat.id. done.
  + iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws2 locs2] winst2].
    iModIntro.
    prim_split κ HStep HStep. 
    eapply reduce_det in HStep as [H | [ (? & Hfirst & ?) | [ [? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                                Hfirst3 & Hσ & Hme)]]] ;
        last (eapply rm_segstore_failure => //=) ;
        try by unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    inversion H ; subst; clear H => /=.
    iFrame.
     destruct Hfail as [Hfail | [Hfail | [-> Hfail]]].
    * by left.
    * right; left.
      unfold ssrnat.leq. unfold ssrnat.subn, ssrnat.addn.
      unfold ssrnat.subn_rec, ssrnat.addn_rec.
      apply /eqP.
      assert (S (N.to_nat (bound h)) - (N.to_nat (offset h) + t_length t) = 0).
      lia.
      by do 2 rewrite nat_bin.
    * repeat right; split => //. unfold t_length.
      rewrite nat_bin. rewrite N2Nat.id. done.
Qed.   


Lemma drop_is_nil {A} k (l: list A) : drop k l = [] -> k >= length l.
Proof.
  move:l. induction k => //=; intros. unfold drop in H; subst. simpl. lia.
  destruct l => //=. lia. simpl in H. apply IHk in H. lia.
Qed. 

Lemma map_fold_grows (f : N -> (N * N) -> gmap N () -> gmap N ()) (res : gmap N ()) (m : gmap N (N * N)) (i : N):
  res !! i = None ->
  map_fold f res m !! i = Some () ->
  exists (j: N) (x: N * N) (res' : gmap N ()), res' !! i = None /\ m !! j = Some x /\ f j x res' !! i = Some ().
Proof.
  intros * Hres Hfold.
  pose (P := λ (result: gmap N ()) (em: gmap N (N * N)), result !! i = Some () -> exists (j: N) (x: N * N) (res': gmap N ()), res' !! i = None /\ em !! j = Some x /\ f j x res' !! i = Some ()). 
  assert (P (map_fold f res m) m) as HP.
  2:{ apply HP => //. }
  apply (map_fold_ind P f).
  intros Habs. rewrite Hres in Habs => //.
  intros j x mm r Hj Hmm Hr.
  destruct (r !! i) eqn:Hri.
  destruct u.
  apply Hmm in Hri as (j0 & x0 & res' & Hres' & Hmm' & Hf).
  repeat eexists => //.
  rewrite lookup_insert_ne => //.
  intros ->. rewrite Hj in Hmm' => //.
  repeat eexists => //. rewrite lookup_insert => //.
Qed. 


Lemma fold_left_grows: forall (X A B N: Type) (LA: Lookup A B N) (f: N -> X -> N) (res: N) (l: list X) (i : A) (v : B),
    res !! i = None ->
    fold_left f l res !! i = Some v -> exists (j: nat) x v' res', res' !! i = None /\ l !! j = Some x /\ f res' x !! i = Some v'.
Proof.
  intros * Hres Hfold.
  generalize dependent res.
  induction l => //=; intros.
  simpl in Hfold. by rewrite Hfold in Hres.
  simpl in Hfold. destruct (f res a !! i) eqn:Hres'.
  repeat eexists => //. instantiate (1 := 0) => //.
  apply IHl in Hfold as (j & x & v' & res' & Hres'' & Hj & Hr) => //.
  repeat eexists. 3: exact Hr. exact Hres''. instantiate (1 := S j) => //.
Qed.

Lemma lookup_iota a b c i: iota a b !! i = Some c <-> c = a + i /\ i < b.
Proof.
  move: a i. induction b => //=; intros.
  split; intro Habs => //. lia.
  destruct i => /=.
  { rewrite Nat.add_0_r. split. intro H; inversion H; subst; lia.
    intros [-> _]. done. }
  split. intro H; apply IHb in H. lia.
  intros [-> H]. apply IHb. lia.
Qed.
  

Lemma ghost_map_delete_big_ws bs (m : segment) a addr size id:
  length bs = N.to_nat size ->
  a.(allocated) !! id = Some (addr, size) ->
  (*  isSound s a -> *)
  compatible addr size (delete id a.(allocated)) ->
  ghost_map_auth segGName 1 (gmap_of_segment m a) -∗
                  ↦[wss][addr] bs ==∗
                  ghost_map_auth segGName 1 (gmap_of_segment m
                                                             {| allocated := delete id (allocated a);
                                                               next_free := next_free a |}).
Proof.
  iIntros (Hlen Ha HWF) "Hσ Hwms".  
  unfold gmap_of_segment.
  unfold live_locations. simpl.
  erewrite <- (insert_delete (allocated a)) => //=.
  rewrite map_fold_insert; last first.
  { apply lookup_delete. }
  { apply commutes. } 
  rewrite insert_delete => //.
  iAssert (∀ k,
              ⌜ k <= N.to_nat size ⌝ -∗
                      |==> ghost_map_auth segGName 1
                      (filter
                         (λ '(i, _),
                           fold_left (λ (res : gmap N ()) (j : nat), <[N.of_nat j:=()]> res)
                             (iota (N.to_nat addr + k) (N.to_nat size - k))
                             (map_fold
                                (λ (_ : N) '(addr0, lim) (res : gmap N ()),
                                  fold_left (λ (res0 : gmap N ()) (j : nat), <[N.of_nat j:=()]> res0)
                                    (iota (N.to_nat addr0) (N.to_nat lim)) res) ∅ (delete id (allocated a))) !! i =
                             Some ()) (gmap_of_list (segl_data (seg_data m)))) ∗
                      ↦[wss][addr + N.of_nat k](drop k bs))%I with "[Hσ Hwms]" as "H".  
  2:{ iDestruct ("H" $! (N.to_nat size) (Nat.le_refl _)) as "[H _]".
      rewrite Nat.sub_diag. done. }
  iIntros (k).
  iInduction k as [|k] "IHk"; iIntros "%Hk".
  { rewrite Nat.add_0_r. rewrite Nat.sub_0_r. rewrite N.add_0_r. unfold drop.
    iFrame. done. }
  iSpecialize ("IHk" with "Hσ Hwms").
  assert (k <= N.to_nat size) as H; first lia.
  iSpecialize ("IHk" $! H).
  iMod "IHk" as "[Hσ Hwms]".
  destruct (drop k bs) eqn:Hbs.
  { apply drop_is_nil in Hbs. lia. }
  iDestruct (wss_append with "Hwms") as "[Hwm Hwms]".
  simpl.
  iMod (ghost_map_delete with "Hσ Hwm") as "Hσ".
  rewrite - map_filter_delete.
  edestruct (map_filter_ext (K := N) (A := byte * btag) (λ '(i, _),
                 fold_left (λ (res : gmap N ()) (j : nat), <[N.of_nat j:=()]> res)
                   (iota (N.to_nat addr + k) (N.to_nat size - k))
                   (map_fold
                      (λ (_ : N) '(addr0, lim) (res : gmap N ()),
                         fold_left (λ (res0 : gmap N ()) (j : nat), <[N.of_nat j:=()]> res0)
                           (iota (N.to_nat addr0) (N.to_nat lim)) res) ∅
                      (delete id (allocated a))) !! i = Some ())
            (λ '(i, _),
            fold_left (λ (res : gmap N ()) (j : nat), <[N.of_nat j:=()]> res)
              (iota (N.to_nat addr + S k) (N.to_nat size - S k))
              (map_fold
                 (λ (_ : N) '(addr0, lim) (res : gmap N ()),
                    fold_left (λ (res0 : gmap N ()) (j : nat), <[N.of_nat j:=()]> res0)
                      (iota (N.to_nat addr0) (N.to_nat lim)) res) ∅ (delete id (allocated a)))
            !! i = Some ()) (delete (addr + N.of_nat k)%N (gmap_of_list (segl_data (seg_data m))))) as [H0 _].
  rewrite H0; clear H0. 
  rewrite map_filter_delete_not.
  replace (addr + N.pos (Pos.of_succ_nat k))%N with (addr + N.of_nat k + 1)%N; last lia.
  replace (S k) with (k + 1); last lia.
  rewrite - drop_drop.
  rewrite Hbs. 
  unfold drop.
  iFrame. done.
  { intros y Hy Habs.
    remember (map_fold _ _ _) as mf.
    replace ((fold_left (λ (res : gmap N ()) (j: nat), <[ N.of_nat j :=()]> res)
               (iota (N.to_nat addr + S k) (N.to_nat size - S k)) mf) !! (addr + N.of_nat k)%N)
      with (mf !! (addr + N.of_nat k)%N) in Habs.
    2:{ clear. remember (N.to_nat size - S k) as y.
        remember (N.to_nat addr + S k) as x.
        remember (addr + N.of_nat k)%N as z.
        assert (x > N.to_nat z) as Hx; first lia.
        clear Heqx Heqy Heqz.
        generalize dependent mf. generalize dependent x.
        induction y => //=.
        intros x Hx mf. rewrite - IHy.
        rewrite lookup_insert_ne => //. lia. lia.
    }
    subst mf.
    eapply map_fold_grows in Habs as (j & [addr0 lim0] & res & Hres & Hin & Habs).
    2: done.
    apply fold_left_grows in Habs as (j' & x & () & res' & Hres' & Hin' & Habs).
    2: done.
    destruct (N.of_nat x =? addr + N.of_nat k)%N eqn:Hx.
    2:{ apply N.eqb_neq in Hx. rewrite lookup_insert_ne in Habs => //.
        by rewrite Hres' in Habs. }
    apply N.eqb_eq in Hx. assert (x = N.to_nat addr + k) as ->; first lia.
    clear Hx.
    apply lookup_iota in Hin' as [Hx Hj'].
    apply HWF in Hin as [?|?]; lia.
  }

  intros i x Hi.
  split.
  { unfold base.uncurry, Datatypes.uncurry.
    intros Hj.
    remember (map_fold _ _ _) as mf.
    replace (N.to_nat size - k) with (S (N.to_nat size - S k)) in Hj; last lia.
    simpl in Hj.
    clear - Hj Hi.
    remember (S _) as strtp. remember (_ - _) as endp.
    replace (N.to_nat addr + S k) with strtp; last lia.
    assert (strtp > N.to_nat addr + k) as Hstrtp; first lia.
    clear Heqstrtp Heqendp.
    generalize dependent mf. generalize dependent strtp.
    induction endp; intros strtp Hstrtp mf Hj => //=.
    simpl in Hj. rewrite lookup_insert_ne in Hj => //.
    intro Habs. replace (addr + N.of_nat k)%N with i in Hi; last lia.
    rewrite lookup_delete in Hi.
    done.
    simpl in Hj.
    rewrite insert_commute in Hj.
    apply IHendp in Hj. done. lia. lia.
  }

  unfold base.uncurry, Datatypes.uncurry.
  intros Hj.
  remember (map_fold _ _ _) as mf.
  replace (N.to_nat size - k) with (S (N.to_nat size - S k)); last lia.
  simpl.
  clear - Hj Hi.
  remember (S (_ + _)) as strtp. remember (_ - _) as endp.
  replace (N.to_nat addr + S k) with strtp in Hj; last lia.
  assert (strtp > N.to_nat addr + k) as Hstrtp; first lia.
  clear Heqstrtp Heqendp.
  generalize dependent mf. generalize dependent strtp.
  induction endp; intros strtp Hstrtp mf Hj => //=.
  simpl in Hj. rewrite lookup_insert_ne => //. 
  intro Habs. replace (addr + N.of_nat k)%N with i in Hi; last lia.
  rewrite lookup_delete in Hi.
  done.
  rewrite insert_commute.
  apply IHendp in Hj. done. lia. lia.

Qed.


(*
Lemma point_to_implies_compatible id addr size bs s a:
    length bs = N.to_nat size ->
    ↦[wss][ addr ] bs -∗
      id ↣[allocated] (addr, size) -∗
      ghost_map_auth segGName 1 (gmap_of_segment s a) -∗
      ghost_map_auth allGName 1 (gmap_of_allocator a) -∗
      ⌜ compatible addr size (delete id a.(allocated)) ⌝.
Proof.
  iIntros (Hbs) "Hwss Hall Hs Ha".
  unfold compatible.
  iIntros (nid addr' size' H).

  iAssert (∀ nid addr' size', ⌜ delete id (allocated a) !! nid = Some (addr', size') ⌝ -∗
                                                                   ⌜ (addr + size <= addr')%N \/ (addr >= addr' + size')%N ⌝)%I
    with "[Hwss Hall Hs Ha]" as "H".
  2:{ iIntros (nid).
*)


Lemma wp_segfree h f0 bts Φ s E:
  valid h = true ->
  offset h = 0%N ->
  length bts = N.to_nat (bound h) ->
  (▷ Φ (immV []) ∗ ↪[frame] f0 ∗ ↦[wss][ base h ] bts ∗ id h ↣[allocated] (base h, bound h)
     ⊢ (WP [AI_basic (BI_const (VAL_handle h)) ;
            AI_basic BI_segfree ] @ s; E {{ w, Φ w ∗ ↪[frame] f0 }})).
Proof.
  iIntros (Hvalid Hoff Hbts) "(HΦ & Hf0 & Hwss & Halloc)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & Ha & ? & Hframe & Hγ & ? & ? & ? & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Ha Halloc") as "%Halloc".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    eexists [_], [], (_, locs, winst), [].
    repeat split => //.
    eapply rm_segfree_success => //.
    econstructor => //.
    unfold find_and_remove.
    rewrite Halloc.
    done.
  - iIntros "!>" (es σ2 efs HStep). 
    iMod (ghost_map_delete with "Ha Halloc") as "Ha".
    iMod (ghost_map_delete_big_ws with "Hs Hwss") as "Hs" => //.
    destruct HWF. apply H in Halloc as [_ ?] => //.
    iIntros "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & ?) |[[? Hfirst] | (?&?&?& Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme) ]]];
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    2:{ eapply rm_segfree_success => //. econstructor => //. unfold find_and_remove.
        by rewrite Halloc. }
    inversion H; subst; clear H => /=.
    iFrame. iPureIntro.
    eapply (reduce_preserves_wellformedness (f := {| f_locs := locs'; f_inst := inst' |})).
    exact HWF. eapply rm_segfree_success => //. econstructor => //.
    unfold find_and_remove. rewrite Halloc. done.
Qed. 



Lemma fold_left_last {A B} f l (x:A) (acc:B):
  fold_left f (l ++ [x]) acc = f (fold_left f l acc) x.
Proof.
  generalize dependent acc.
  induction l => //=.
Qed.


Lemma ghost_map_insert_wss addr size nid a s :
  compatible addr size a.(allocated) ->
  isFree nid a ->
  N.to_nat addr ≤ length (segl_data (seg_data s)) ->
  ghost_map_auth segGName 1 (gmap_of_segment s a) ==∗
    ghost_map_auth segGName 1 (gmap_of_segment
                                 {| seg_data :=
                                     {| segl_data :=
                                         take (N.to_nat addr) (segl_data (seg_data s)) ++
                                           repeat (#00%byte, Numeric) (N.to_nat size) ++
                                           drop (N.to_nat (addr + size)) (segl_data (seg_data s)) |};
                                   seg_max_opt := seg_max_opt s |}
                                 {| allocated := <[ nid := (addr, size) ]> (allocated a);
                                   next_free := next_free a `max` (nid + 1)
                                 |}) ∗
    ↦[wss][addr] repeat (#00%byte, Numeric)
    (N.to_nat size).
Proof.
  iIntros (Hcomp Hfree Haddr) "Hs".
  rewrite - (N2Nat.id size). rewrite - (N2Nat.id size) in Hcomp.
  remember (N.to_nat size) as size'.
  clear Heqsize' size.
  iInduction size' as [|size] "IH".
  { rewrite N.add_0_r.
    simpl. rewrite cat_app. rewrite list.take_drop.
    destruct s => /=.
    unfold gmap_of_segment, live_locations.
    rewrite map_fold_insert. iFrame.
    unfold seg_block_at_pos. simpl. done.
    apply commutes. done. }
  assert (compatible addr (N.of_nat size) (allocated a)).
  { intros x addr' size' Hx.
    apply Hcomp in Hx as [?|?].
    left; lia. right; lia. }
  iSpecialize ("IH" $! H).
  iMod ("IH" with "Hs") as "[Hs Hwss]".
  iMod (ghost_map_insert (addr + N.of_nat size)%N (#00%byte, Numeric) with "Hs")
    as "[Hs Hws]".
  { unfold gmap_of_segment.
    apply map_filter_lookup_None_2.
    right. intros x Hx Habs.
    unfold live_locations in Habs.
    apply map_fold_grows in Habs as (j & [addr' lim'] & res & Hres & Hall & Hj) => //.
    apply fold_left_grows in Hj as (j' & y & () & res' & Hres' & Hall' & Hj') => //.
    destruct (N.of_nat y =? addr + N.of_nat size)%N eqn:Hy.
    2:{ apply N.eqb_neq in Hy. rewrite lookup_insert_ne in Hj' => //.
        rewrite Hres' in Hj' => //. } 
    apply N.eqb_eq in Hy. assert (y = N.to_nat addr + size) as ->; first lia.
    apply lookup_iota in Hall' as [??].
    simpl in Hall.
    destruct (j =? nid)%N eqn:Hjnid.
    apply N.eqb_eq in Hjnid as ->.
    rewrite lookup_insert in Hall. inversion Hall; subst; lia.
    apply N.eqb_neq in Hjnid. rewrite lookup_insert_ne in Hall => //.
    apply Hcomp in Hall as [?|?]; lia. }
  iSplitL "Hs"; last first.
  { repeat rewrite Nat2N.id.
    replace (S size) with (size + 1); last lia.
    rewrite repeat_app.
    simpl. iApply big_sepL_app.
    iFrame. iSimpl. rewrite repeat_length. rewrite Nat.add_0_r.
    replace (N.of_nat (N.to_nat addr + size)) with (addr + N.of_nat size)%N; last lia.
    iFrame. done. }
  replace (<[(addr + N.of_nat size)%N:=(#00%byte, Numeric)]>
              (gmap_of_segment
                 {|
                   seg_data :=
                     {|
                       segl_data :=
                         take (N.to_nat addr) (segl_data (seg_data s)) ++
                         repeat (#00%byte, Numeric) (N.to_nat (N.of_nat size)) ++
                         drop (N.to_nat (addr + N.of_nat size)) (segl_data (seg_data s))
                     |};
                   seg_max_opt := seg_max_opt s
                 |}
                 {|
                   allocated := <[nid:=(addr, N.of_nat size)]> (allocated a);
                   next_free := next_free a `max` (nid + 1)
                 |})) with
    (gmap_of_segment
         {|
           seg_data :=
             {|
               segl_data :=
                 take (N.to_nat addr) (segl_data (seg_data s)) ++
                 repeat (#00%byte, Numeric) (N.to_nat (N.of_nat (S size))) ++
                 drop (N.to_nat (addr + N.of_nat (S size))) (segl_data (seg_data s))
             |};
           seg_max_opt := seg_max_opt s
         |}
         {|
           allocated := <[nid:=(addr, N.of_nat (S size))]> (allocated a);
           next_free := next_free a `max` (nid + 1)
         |}); first by iFrame.
  unfold gmap_of_segment.
  unfold live_locations. simpl.
  rewrite map_fold_insert; [| apply commutes | done].
  replace (N.to_nat (N.pos (Pos.of_succ_nat size))) with (S size); last lia.
  replace (iota (N.to_nat addr) (S size)) with (iota (N.to_nat addr) size ++ [N.to_nat addr + size]).
  2:{ remember (N.to_nat addr) as x. clear.
      generalize dependent x. induction size => //. intro; by rewrite Nat.add_0_r.
      intro. replace (iota x (S (S size))) with (x :: iota (S x) (S size)) => //.
      rewrite - (IHsize (S x)). simpl. replace (x + S size) with (S (x + size)).
      done. lia. } 
  simpl.
  rewrite fold_left_last.
  rewrite map_fold_insert; [| apply commutes|done]. rewrite Nat2N.id.
  apply map_eq.
  intros i. destruct (i =? N.of_nat (N.to_nat addr + size))%N eqn:Hi.
  { apply N.eqb_eq in Hi as ->.
    erewrite map_filter_lookup_Some_2.
    replace (N.of_nat (N.to_nat addr + size)) with (addr + N.of_nat size)%N ; last lia.
    rewrite lookup_insert. done.
    rewrite gmap_of_list_lookup.
    rewrite Nat2N.id.
    rewrite lookup_app_r.
    rewrite lookup_app_l.
    apply repeat_lookup.
    rewrite take_length_le. 
    lia. done. rewrite repeat_length. rewrite take_length_le. lia.
    done. rewrite take_length_le. lia. done.
    rewrite lookup_insert. done. }
  apply N.eqb_neq in Hi. rewrite lookup_insert_ne; last lia.
  destruct (filter _ _ !! _) eqn: Hfil.
  { symmetry. apply map_filter_lookup_Some.
    apply map_filter_lookup_Some in Hfil as [??].
    rewrite lookup_insert_ne in H1; last done.
    split => //. rewrite gmap_of_list_lookup. rewrite gmap_of_list_lookup in H0.
    destruct (i <? addr)%N eqn:Hi'.
    { apply N.ltb_lt in Hi'.
        rewrite lookup_app_l; last by rewrite take_length_le; lia.
        rewrite lookup_app_l in H0; last by rewrite take_length_le; lia.
        done. } 
      apply N.ltb_ge in Hi'.
      rewrite lookup_app_r; last by rewrite take_length_le; lia.
      rewrite lookup_app_r in H0; last by rewrite take_length_le; lia.
      destruct (i <? N.of_nat (N.to_nat addr + size))%N eqn:Hi''.
      { apply N.ltb_lt in Hi''.
        rewrite lookup_app_l; last by rewrite repeat_length take_length_le; lia.
        rewrite lookup_app_l in H0; last by rewrite repeat_length take_length_le; lia.
        rewrite take_length_le; last lia.
        rewrite take_length_le in H0; last lia.
        assert (N.to_nat i - N.to_nat addr < Pos.to_nat (Pos.of_succ_nat size)); first lia.
        apply (repeat_lookup (#00%byte, Numeric)) in H2.
        rewrite H2 in H0. 
        inversion H0; subst. apply repeat_lookup. lia. } 
      rewrite take_length_le; last lia.
      apply N.ltb_ge in Hi''.
      rewrite lookup_app_r; last by rewrite repeat_length; lia.
      rewrite lookup_app_r in H0; last by rewrite repeat_length take_length_le; lia.
      rewrite repeat_length. rewrite repeat_length in H0.
      rewrite lookup_drop. rewrite lookup_drop in H0.
      rewrite take_length_le in H0; last lia.
      replace (N.to_nat (addr + N.of_nat size) + (N.to_nat i - N.to_nat addr - size))
        with (N.to_nat (addr + N.pos (Pos.of_succ_nat size)) +
                (N.to_nat i - N.to_nat addr - Pos.to_nat (Pos.of_succ_nat size)));
        [done | lia]. } 
    symmetry. apply map_filter_lookup_None.
    apply map_filter_lookup_None in Hfil.
    destruct (gmap_of_list _ !! _) eqn:gmi.
    2:{ left.
        rewrite gmap_of_list_lookup. rewrite gmap_of_list_lookup in gmi.
        apply lookup_ge_None in gmi.
        apply lookup_ge_None.
        repeat rewrite app_length. repeat rewrite app_length in gmi.
        rewrite take_length_le; last lia. rewrite take_length_le in gmi; last lia.
        rewrite repeat_length. rewrite repeat_length in gmi.
        rewrite drop_length. rewrite drop_length in gmi. lia. }
    destruct Hfil as [? | Hfil] => //.
    right. intros x Hsome.
    rewrite lookup_insert_ne in Hfil; last done.
    apply (Hfil p) => //.
Qed. 


Lemma wp_segalloc (n: N) (c: i32) (f0: frame) (s: stuckness) (E: coPset) (* Φ : iris.val -> iProp Σ *):
  n = Wasm_int.N_of_uint i32m c ->
  ( ↪[frame] f0  ⊢
     (WP [AI_basic (BI_const (VAL_int32 c)) ;
          AI_basic BI_segalloc] @ s; E
    {{ w, (
            ∃ h , ⌜ w = immV [VAL_handle h] ⌝ ∗
                              ( ⌜ h = dummy_handle ⌝ ∨
                                
                                  h.(id) ↣[allocated] (base h, n) ∗
                                      ⌜ bound h = n ⌝ ∗
                                                    ⌜ offset h = 0%N ⌝ ∗
                            ⌜ valid h = true ⌝ ∗
                                       ↦[wss][ h.(base) ]repeat (#00%byte, Numeric) (N.to_nat n))) ∗
            ↪[frame] f0 }})).
Proof.
  iIntros (Hn) "Hf0".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hs & Ha & ? & Hframe & ? & Hγ & ? & ? & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0.
  inversion Hf0; subst; clear Hf0.
  (* iDestruct (gen_heap_valid with "Hslen Hlen") as "%Hslen".
  rewrite lookup_insert in Hslen.
  inversion Hslen; subst; clear Hslen. *)
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_basic (BI_const _)], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by eapply rm_segalloc_failure.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    remember [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_segalloc] as es0.
    remember {| f_locs := locs ; f_inst := winst |} as f.
    remember {| f_locs := locs' ; f_inst := inst' |} as f'.
    replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_segalloc] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_segalloc]) in Heqes0 => //=.
    induction H ; try by inversion Heqes0 ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    destruct H ; try by inversion Heqes0 ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    { destruct H ; try by inversion Heqes0 ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      rewrite Heqes0 in H0.
      filled_trap H0 Hxl1. }
    { (* segalloc succeeded *)
      inversion Heqes0 ; subst c0 ; clear Heqes0.
      subst.
      inversion H2. subst. simpl. 
      iFrame. 
      iMod (ghost_map_insert nid (a, Wasm_int.N_of_uint i32m c) with "Ha") as "[Ha Hid]".
      done.
      (* iMod (gen_heap_update with "Hslen Hlen") as "[Hslen Hlen]".  
      rewrite insert_insert. *)
      iMod (ghost_map_insert_wss with "Hs") as "[Hs Hwss]".
      done. done. lia.
      iModIntro.
      iSplitL "Ha Hs".
      iSplitL "Hs".
      iExact "Hs".
      iSplitL "Ha".
      iExact "Ha".
(*      iSplitL.
      iExact "Hslen". *)
      iPureIntro.
      eapply (reduce_preserves_wellformedness (f := {| f_locs := locs'; f_inst := inst' |})).
      exact HWF. eapply rm_segalloc_success => //.
      iExists _.
      iSplitR. done.
      (*iSplitL "Hlen".
      iExact "Hlen". *)
      iRight.
(*      iSplitR.
      iPureIntro. unfold seg_length => /=.
      repeat rewrite app_length.
      rewrite take_length_le; last lia.
      rewrite repeat_length. rewrite drop_length. lia. *)
      iSimpl.
      iSplitL "Hid".
      iExact "Hid".
      iSplit. done.
      iSplit. done.
      iSplit. done.
      (* iSplit. done. *)
      iExact "Hwss".
    }
    { (* segalloc failed *)
      inversion Heqes0; subst c0; clear Heqes0.
      subst.
      iFrame.
      simpl.
      iModIntro.
      iSplit; first done.
      iExists _.
      iSplitL; first done.
      iLeft.
      done.
    } 
    rewrite Heqes0 in H0.
    simple_filled H0 k lh bef aft nn ll ll'.
    destruct bef.
    { destruct es ; first by exfalso ; eapply empty_no_reduce.
      inversion H0.
      apply Logic.eq_sym, app_eq_unit in H4 as [[ -> _ ] | [-> ->]].
      by subst ; exfalso ; eapply values_no_reduce.
      subst.
      unfold lfilled, lfill in H1.
      simpl in H1.
      rewrite app_nil_r in H1.
      move/eqP in H1 ; subst.
      apply IHreduce => //=. }
    exfalso.
    inversion H0.
    apply Logic.eq_sym, app_eq_unit in H4 as [[ _ Hes ] | [ _ Hes]].
    apply app_eq_unit in Hes as [[ -> _ ] | [Hes _ ]].
    by eapply empty_no_reduce.
    rewrite <- app_nil_l in Hes.
    clear IHreduce H1 Heqes0 H0.
    induction H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
      inversion Habs.
     induction H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
      inversion Habs.
    { destruct H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
        inversion Habs.
      rewrite Hes in H0 ; filled_trap H0 Hxl1. }
    rewrite Hes in H0.
    simple_filled H0 k lh bef0 aft0 nnn lll lll'.
    apply Logic.eq_sym, app_eq_unit in H0 as [[ -> H0 ] | [_ H0]].
    apply app_eq_unit in H0 as [[ -> _ ] | [ -> -> ]].
    by eapply empty_no_reduce.
    apply IHreduce => //=.
    apply app_eq_nil in H0 as [ -> _].
    by eapply empty_no_reduce.
    apply app_eq_nil in Hes as [-> _].
    by eapply empty_no_reduce.
Qed.


End iris_rules_segment.
