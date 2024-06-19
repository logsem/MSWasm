From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_rules proofmode.
Require Export iris_example_helper.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50). 
   
Notation "{{{ P }}} es @ E {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗ (WP (es : iris.expr) @ NotStuck ; E {{ v, Φ v }}))%I (at level 50).

Definition i32const (n:Z) := BI_const (NVAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition value_of_int (n:Z) := VAL_int32 (Wasm_int.int_of_Z i32m n).
Definition nvalue_of_int (n:Z) := NVAL_int32 (Wasm_int.int_of_Z i32m n).

Definition u32const (n:N) := BI_const (NVAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n))).
Definition value_of_uint (n:N) := VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n)).
Definition value_of_handle (h: handle) := VAL_handle h.

(* Some useful constants *)
Definition two14 := 16384%N.
Definition two16 := 65536%N.
Definition two32 := 4294967296%N.
Definition ffff0000 := 4294901760%N.


Definition points_to_i32 `{!wasmG Σ} i v :=
  (∃ a b c d, ↦[ws][ i ] (a, Numeric) ∗ ↦[ws][N.add i 1] (b, Numeric) ∗
                ↦[ws][N.add i 2] (c, Numeric) ∗ ↦[ws][N.add i 3] (d, Numeric) ∗
                ⌜ serialise_i32 v = [a ; b ; c ; d] ⌝)%I.

Notation "↦[i32][ k ] v" := (points_to_i32 k v) (at level 50).

Lemma u32_modulus: Wasm_int.Int32.modulus = 4294967296%Z.
Proof.
  by lias.
Qed.

Lemma of_nat_to_nat_plus a b :
  N.of_nat (N.to_nat a + b) = (a + N.of_nat b)%N.
Proof. lia. Qed.

Lemma drop_is_nil {A} n (s : seq.seq A) :
  drop n s = [] -> n >= length s.
Proof.
  move => Hdrop.
  assert (length s - n = 0) as Hdroplen; first by rewrite - drop_length; rewrite Hdrop.
  by lias.
Qed.

Lemma in_take {A} n s (x : A) :
  In x (take n s) -> In x s.
Proof.
  move => Hin.
  apply elem_of_list_In, elem_of_take in Hin as [i [? ?]].
  apply elem_of_list_In, elem_of_list_lookup.
  by eexists.
Qed.

Lemma two16_div_i32 :
  (Z.of_N two16 | Wasm_int.Int32.modulus)%Z.
Proof.
  rewrite u32_modulus.
  unfold two16. exists 65536%Z. lia.
Qed.

Lemma wasm_int_signed x:
  (-2147483648 <= x <= 2147483647)%Z ->
  Wasm_int.Int32.signed (Wasm_int.Int32.repr x) = x.
Proof.
  move => Hbound.
  rewrite Wasm_int.Int32.signed_repr; first by lias.
  unfold Wasm_int.Int32.min_signed.
  unfold Wasm_int.Int32.max_signed.
  unfold Wasm_int.Int32.half_modulus.
  rewrite u32_modulus.
  replace (4294967296 `div` 2)%Z with (2147483648)%Z; by lias.
Qed.

Lemma wasm_int_unsigned x:
  (0 <= x <= 4294967295)%Z ->
  Wasm_int.Int32.unsigned (Wasm_int.Int32.repr x) = x.
Proof.
  move => Hbound.
  rewrite Wasm_int.Int32.unsigned_repr; first by lias.
  unfold Wasm_int.Int32.max_unsigned.
  rewrite u32_modulus.
  by lias.
Qed.

Lemma value_of_int_repr a :
  exists v, VAL_int32 a = value_of_int v.
Proof.
  intros. exists (Wasm_int.Z_of_uint i32m a).
  unfold value_of_int. simpl.
  rewrite Wasm_int.Int32.repr_unsigned.
  auto.
Qed.

Lemma value_of_uint_repr a :
  exists v, VAL_int32 a = value_of_uint v.
Proof.
  intros. exists (Z.to_N (Wasm_int.Z_of_uint i32m a)).
  unfold value_of_uint. simpl.
  rewrite Z2N.id.
  rewrite Wasm_int.Int32.repr_unsigned.
  auto.
  pose proof (Wasm_int.Int32.unsigned_range a) as [? ?]. auto.
Qed.

Lemma div_mod_i32 v:
  let k:=Wasm_int.N_of_uint i32m ((Wasm_int.int_of_Z i32m (Z.of_N v))) in
  (65536 | v)%N ->
  (65536 | k)%N.
Proof.
  intros k Hdiv. subst k.
  simpl. destruct Hdiv. subst.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  replace (Wasm_int.Int32.modulus) with (65536 * 65536)%Z => //.    (* 4294967296 *)
  rewrite Z2N.inj_mod;try lia.
  rewrite N2Z.id.
  rewrite Z2N.inj_mul;try lia.
  simpl Z.to_N.
  apply N.mod_divide;[lia|].
  rewrite N.mul_mod_distr_r;try lia.
  rewrite N.mul_mod_idemp_l;try lia.
  rewrite N.mod_mul;lia.
Qed.

Lemma int_of_Z_mod v :
  Wasm_int.int_of_Z i32m (Z.of_N v) =
  Wasm_int.int_of_Z i32m (Z.of_N (Z.to_N (Wasm_int.Int32.Z_mod_modulus (Z.of_N v)))).
Proof.
  simpl.
  rewrite Z2N.id;[|pose proof (Wasm_int.Int32.Z_mod_modulus_range (Z.of_N v)) as [? ?];auto].
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite - Wasm_int.Int32.unsigned_repr_eq.
  rewrite Wasm_int.Int32.repr_unsigned. auto.
Qed.
  
Section Stack.
  Set Bullet Behavior "Strict Subproofs".
  Context `{!wasmG Σ}.

Lemma points_to_i32_eq i1 v1 i2 v2:
   i1 = i2 ->
   v1 = v2 ->
   ↦[i32][i1] v1 -∗
   ↦[i32][i2] v2.
 Proof.
   intros -> ->.
   by iIntros.
 Qed.

Lemma points_to_wm_eq b1 k1 b2 k2:
   b1 = b2 ->
   k1 = k2 ->
   ↦[ws][k1] b1 -∗
   ↦[ws][k2] b2.
 Proof.
   intros -> ->.
   by iIntros.
 Qed.
 
Lemma points_to_wms_eq l1 k1 l2 k2:
   l1 = l2 ->
   k1 = k2 ->
   ↦[wss][k1] l1 -∗
   ↦[wss][k2] l2.
 Proof.
   intros -> ->.
   by iIntros.
 Qed.
 
Lemma i32_wss i v :
  ↦[i32][ i ] v ⊣⊢ ↦[wss][ i ] map (fun x => (x, Numeric)) (serialise_i32 v).
Proof.
  iSplit ; iIntros "H" ; unfold seg_block_at_pos, points_to_i32.
  - iDestruct "H" as (a b c d) "(? & ? & ? & ? & ->)".
    iSimpl.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    by iFrame.
  - remember (serialise_i32 v) as bs.
    repeat destruct bs => //=.
    repeat rewrite of_nat_to_nat_plus.
    rewrite N.add_0_r.
    iDestruct "H" as "(? & ? & ? & ? & _)".
    iExists _,_,_,_.
    iFrame.
    done.
Qed.

(* The isStack v l n predicate describe a stack starting at location v, containing
   the mathematical stack (l: list i32), at memory n, of size 1 page.
   The first cell v points to the current top cell of the stack, so the maximum 
   number of elements the stack could contain is 16383.
*)  
Definition isStack (h: handle) (l : seq.seq i32) :=
  (let st_p := (N.of_nat (length l) * 4)%N in
   ⌜ offset h = 0%N ⌝ ∗ ⌜ bound h = 65536%N ⌝ ∗ ⌜ valid h = true ⌝ ∗
  ⌜ (N.of_nat (length l) < two14)%N ⌝ ∗
  id h ↣[allocated] Some (base h, bound h) ∗ 
   ↦[i32][ base h ]
   (Wasm_int.Int32.repr (Z.of_N st_p)) ∗
   ([∗ list] i ↦ w ∈ l,
     ↦[i32][ base h + st_p - (4 * N.of_nat i)%N ] w) ∗
   ∃ bs, ⌜ (N.of_nat (length bs) = two16 - 4 - N.of_nat (length l) * 4)%N ⌝ ∗
           ↦[wss][base h + st_p + 4%N] bs
  )%I.

Definition stk : string := "STACK".
Definition stkN : namespace := nroot .@ stk.


Lemma N_divide_dec: ∀ a b : N, {(a | b)%N} + {¬ (a | b)%N}.
Proof.
  intros. destruct (decide ((N.to_nat a) | (N.to_nat b))).
  - left. destruct d. exists (N.of_nat x). lia.
  - right. intros Hcontr. apply n.
    destruct Hcontr. exists (N.to_nat x). lia.
Qed.


Inductive multiples_upto: N -> N -> list N -> Prop :=
| mu_base_nil n: (n > 0)%N -> multiples_upto n 0 []
| mu_ind n m l: multiples_upto n m l ->
                multiples_upto n (m + n) (m :: l).

Lemma multiples_upto_nil n m l :
  multiples_upto n m l -> (n > 0)%N.
Proof.
  intros. induction H;auto.
Qed.

Lemma multiples_upto_le n m l :
  (m > 0)%N ->
  multiples_upto n m l ->
  (n <= m)%N.
Proof.
  intros Hm.
  induction 1; by lias.
Qed.

Lemma le_mul x n :
  (2 <= x)%N ->
  (0 < n)%N ->
  (n < x * n)%N.
Proof.
  by lias.
Qed.

Lemma lt_mul x n :
  (x * n < n)%N ->
  x = 0%N.
Proof.
  by lias.
Qed.

Lemma multiples_upto_div :
  forall n m l,
    multiples_upto n m l ->
    (n | m)%N.
Proof.
  induction 1.
  - apply N.divide_0_r.
  - apply N.divide_add_r;auto.
    apply N.divide_refl.
Qed.

Lemma multiples_upto_in_lt :
  forall n m l i,
    multiples_upto n m l ->
    i ∈ l -> (i < m)%N.
Proof.
  induction 1;intros Hin.
  inversion Hin.
  inversion Hin;subst.
  { apply multiples_upto_nil in H. lia. }
  apply IHmultiples_upto in H2.
  lia.
Qed.

Lemma multiples_upto_in_div :
  forall n m l i,
    multiples_upto n m l ->
    i ∈ l -> (n | i)%N.
Proof.
  induction 1;intros Hin.
  inversion Hin.
  inversion Hin;subst.
  { apply multiples_upto_div in H. auto. }
  apply IHmultiples_upto in H2.
  auto.
Qed.
  
Lemma times_lt n1 n2 n3 :
  n1 * n3 < n2 * n3 ->
  n1 < n2.
Proof.
  by lias.
Qed.
  
Lemma times_lt_plus x x0 n :
  n > 0 ->
  (x * n < x0 * n + n) ->
  (x <= x0).
Proof.
  by lias.
Qed.

Lemma Nat2N_le_inj n1 n2 :
  n1 <= n2 <-> (N.of_nat n1 <= N.of_nat n2)%N.
Proof. lia. Qed.
Lemma Nat2N_lt_inj n1 n2 :
  n1 < n2 <-> (N.of_nat n1 < N.of_nat n2)%N.
Proof. lia. Qed.
Lemma N2Nat_le_inj n1 n2 :
  N.to_nat n1 <= N.to_nat n2 <-> (n1 <= n2)%N.
Proof. lia. Qed.
Lemma N2Nat_lt_inj n1 n2 :
  N.to_nat n1 < N.to_nat n2 <-> (n1 < n2)%N.
Proof. lia. Qed.

Lemma multiples_upto_in :
  forall n m l i, multiples_upto n m l ->
  (i < m)%N ->
  (n | i)%N ->
  i ∈ l.
Proof.
  intros n m l i H lt.
  assert (0 <= m)%N as lm. lia.
  revert H lm lt.
  generalize dependent i.
  generalize dependent l.
  generalize dependent m.
  generalize dependent n.
  induction 1.
  - lia.
  - intros lm lt div.
    apply multiples_upto_div in H as div'.
    destruct (decide (i = m));subst.
    + constructor.
    + constructor.
      apply IHmultiples_upto;auto.
      { destruct m;[|lia].
        lias.
      }
      destruct div,div';subst.
      apply N2Nat_lt_inj in lt.
      rewrite !N2Nat.inj_add !N2Nat.inj_mul in lt.
      apply times_lt_plus in lt;[|lia].
      apply N2Nat_le_inj in lt.
      apply N.mul_le_mono_r with _ _ n in lt.
      lia.
Qed.

Definition stackModuleInv (isStack : N -> seq.seq i32 -> iPropI Σ) (nextStackAddrIs : nat -> iPropI Σ) : iProp Σ :=
  ∃ (nextStack : nat), ⌜(page_size | N.of_nat nextStack)%N⌝ ∗ nextStackAddrIs nextStack ∗
                     ∃ l, ⌜multiples_upto page_size (N.of_nat nextStack) l⌝ ∗
                          [∗ list] s ∈ l, ∃ stk, isStack s stk.






  
Lemma stack_pure h s:
  isStack h s -∗ ⌜ offset h = 0%N ⌝ ∗
                  ⌜ bound h = 65536%N ⌝ ∗ 
                                ⌜ valid h = true ⌝ ∗
                 ⌜ (N.of_nat (length s) < two14)%N ⌝.
Proof.
  iIntros "Hs".
  repeat iSplit => //; iDestruct "Hs" as "(% & % & % & % & ?)" => //.
Qed.


Section proofs.
  Context `{ HHB : HandleBytes }.


  Lemma map_fst_map_pair { A B } (l: list A) (x : B) :
    map fst (map (fun y => (y, x)) l) = l.
  Proof.
    induction l => //=.
    by rewrite IHl.
  Qed.   
Lemma stack_load_0 v s f E:
  isStack v s -∗
  ↪[frame] f -∗
  WP [AI_handle v; AI_basic (BI_segload T_i32)] @ E
  {{ w, ⌜ w = immV [value_of_uint (N.of_nat (length s) * 4)] ⌝ ∗ isStack v s ∗ ↪[frame] f }}.
Proof.
  iIntros "Hs Hf" => /=.
 
  iDestruct (stack_pure with "Hs") as "(%Hoff & %Hbound & %Hvalid & %Hlen)".
  
  iApply (wp_wand with "[Hs Hf]").
  iApply wp_segload => //; last first.
  { unfold isStack.
    iDestruct "Hs" as "(_ & _ & _ & _ & Hid & Hbase & Hrest)".
    iDestruct (i32_wss with "Hbase") as "Hbase".
    unfold handle_addr; rewrite Hoff N.add_0_r.
    iFrame.
    iNext. iIntros "H".
    instantiate (2 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; first done. iCombine "Hrest H" as "Hrest". iExact "Hrest".
  }
  { rewrite Hoff Hbound; done. }
  { rewrite map_fst_map_pair. instantiate (1 := VAL_int32 _). done. }
  { done. } 
  { iIntros (w) "[(-> & Hrest & Hid & Hbase) Hf]". 
    iSplit => //.
    iFrame.
    repeat iSplit => //=.
    iApply i32_wss. done.
  }
Qed.

Lemma stack_load_0_alt v s f E k:
  ⌜ k = (N.of_nat (length s) * 4)%N ⌝ -∗
  isStack v s -∗
  ↪[frame] f -∗
  WP [AI_handle v; AI_basic (BI_segload T_i32)] @ E
  {{ w, ⌜ w = immV [value_of_uint k] ⌝ ∗ isStack v s ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hk Hs Hf" => /=.
  subst k.
  by iApply (stack_load_0 with "[$] [$]").
Qed.


Lemma stack_load_j v s f E j sv h:
  ⌜ s !! (N.to_nat j) = Some sv ⌝ -∗
                          ⌜ handle_add v (length s * 4 - 4 * Z.of_N j) = Some h ⌝ -∗
  isStack v s -∗
  ↪[frame] f -∗
  WP [AI_handle h; AI_basic (BI_segload T_i32)] @ E {{ w, ⌜ w = immV [VAL_int32 sv] ⌝ ∗ isStack v s ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hsv %Hadd Hs Hf" => /=.
  iDestruct "Hs" as "(%Hoff & %Hbound & %Hvalid & %Hlen & Ha & Hbase & Hs & Hrest)".
  unfold handle_add in Hadd. destruct (_ >=? _)%Z eqn:Hz => //.
  inversion Hadd; subst. 
   iApply (wp_wand with "[Hf Hs Ha]").
  { iApply wp_segload => //; last first.
    - iFrame. 
      iDestruct (big_sepL_lookup_acc with "Hs") as "(Hj & Hcrest)" => //.
      unfold handle_addr, handle_add. rewrite N2Nat.id.
      iSimpl. rewrite Hoff Z.add_0_l. 
      assert (base v + Z.to_N (length s * 4 - 4 * Z.of_N j) =
                base v + N.of_nat (length s) * 4 - 4 * j)%N as H; first lia.
      rewrite H. 
      iSplitL "Hcrest"; last first.
      iApply i32_wss. done.
      instantiate (2 := λ v, (⌜ v = immV _ ⌝ ∗ (↦[i32][ _ ] _ -∗ _) ∗ _)%I).
      iFrame. iNext. iIntros "H". iSplit; first done. iExact "H".
    - simpl. rewrite Hbound. unfold two14 in Hlen. rewrite Hoff Z.add_0_l.
      remember (length s) as x. rewrite - Heqx. lia.
    - rewrite map_fst_map_pair. instantiate (1 := VAL_int32 _) => //. 
    - done.
  } 
  iIntros (w) "[(-> & Hs & Ha & Hj) Hf]". 
  iSplit => //.
  iDestruct (i32_wss with "Hj") as "Hj". iFrame. 
  replace (base v + N.of_nat (length s) * 4 - 4 *j)%N
    with (handle_addr {|
                     base := base v;
                     offset :=
                       Z.to_N (length s * 4 - 4 * Z.of_N j);
                     bound := bound v;
                     valid := valid v;
                     id := id v
                   |}).
  iDestruct ("Hs" with "Hj") as "Hs".
  iFrame.
  repeat iSplit => //.
  unfold handle_addr => /=.
  fold (4 * j)%N. 
  remember (length s) as x. rewrite - Heqx. lia.
Qed.


  
Lemma stack_load_j_handle_add v s f E j sv:
  ⌜ s !! (N.to_nat j) = Some sv ⌝ -∗
  ⌜ (j < N.of_nat (length s))%N ⌝ -∗
  isStack v s -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (nvalue_of_int (length s * 4 - 4 * Z.of_N j))); AI_handle v ; AI_basic BI_handleadd ; AI_basic (BI_segload T_i32)] @ E
  {{ w, ⌜ w = immV [VAL_int32 sv] ⌝ ∗ isStack v s ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hsv %Hjbound Hs Hf" => /=.
  iDestruct (stack_pure with "Hs") as "(%Hoff & %Hbound & %Hvalid & %Hlen)". 

   assert ( (-2147483648 ≤ length s * 4 - 4 * Z.of_N j ≤ 2147483647)%Z) as Hjb'.
   {  unfold two14 in Hlen. lia. }
   assert (handle_add v (length s * 4 - 4 * Z.of_N j) =
  Some
    {|
      base := base v;
      offset := Z.to_N (length s * 4 - 4 * Z.of_N j);
      bound := bound v;
      valid := valid v;
      id := id v
    |}) as Hadd.
   {  unfold handle_add. rewrite Hoff.
      simpl. 
      rewrite Z.add_0_l.
      assert (0 <= length s * 4 - 4 * Z.of_N j)%Z as Hleq; first lia.
      apply Z.geb_le in Hleq. rewrite Hleq. done. } 
  rewrite separate3. iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf".
  { iApply (wp_wand with "[Hf]").
    iApply (wp_handleadd with "Hf").
    simpl. rewrite wasm_int_signed => //.
    by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
    iIntros (w) "[-> Hf]".
    instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ ↪[frame] f)%I).
    iFrame. done. }
  2: by iIntros "[% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  iApply (stack_load_j with "[] [] [$] [$]").
  done. done. 
Qed.


Lemma stack_load_j_alt v s f E j k sv:
  ⌜ k = (length s * 4 - 4 * Z.of_N j)%Z ⌝ -∗
  ⌜ s !! (N.to_nat j) = Some sv ⌝ -∗
  ⌜ (j < N.of_nat (length s))%N ⌝ -∗
  isStack v s -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (nvalue_of_int k)); AI_handle v; AI_basic BI_handleadd; AI_basic (BI_segload T_i32)] @ E
  {{ w, ⌜ w = immV [VAL_int32 sv] ⌝ ∗ isStack v s ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hk %Hsv %Hjbound Hs Hf" => /=.
  subst k.
  by iApply (stack_load_j_handle_add with "[] [] [$] [$]").
Qed.


Lemma stack_store_j v (s: list i32) f E j sv (v0: i32) h:
  ⌜ s !! (N.to_nat j) = Some sv ⌝ -∗
  ⌜ handle_add v (length s * 4 - 4 * Z.of_N j) = Some h ⌝ -∗
  isStack v s -∗
  ↪[frame] f -∗
  WP [AI_handle h ;
      AI_basic (BI_const (NVAL_int32 v0));
      AI_basic (BI_segstore T_i32)] @ E
  {{ w, ⌜ w = immV [] ⌝ ∗ isStack v (<[ N.to_nat j := v0 ]> s) ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hsv %Hadd Hs Hf" => /=.
  iDestruct "Hs" as "(%Hoff & %Hbound & %Hvalid & %Hlen & Ha & Hbase & Hs & Hrest)".
  unfold handle_add in Hadd. destruct (_ >=? _)%Z eqn:Hz => //.
  inversion Hadd; subst.
  iApply (wp_wand with "[Hs Hf Ha]").
  { fold_const; iApply wp_segstore => //; last first.
    - iFrame. iDestruct (big_sepL_insert_acc with "Hs") as "(Hj & Hcrest)" => //.
      unfold handle_addr, handle_add. rewrite N2Nat.id.
      iSimpl. rewrite Hoff Z.add_0_l.
      assert (base v + N.of_nat (length s) * 4 - 4 * j =
                base v + Z.to_N (length s * 4 - 4 * Z.of_N j))%N; first lia. 
      rewrite H.
      iSplitR "Hj"; last first.
      iApply i32_wss. done.
      instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ (∀ y, ↦[i32][ _ ] _ -∗ _) ∗ _)%I).
      iFrame. iNext. iIntros "H". iSplit; first done. iExact "H".
    - simpl. rewrite Hbound. unfold two14 in Hlen.
      rewrite Hoff Z.add_0_l.  remember (length s) as x. rewrite - Heqx. lia.
    - done.
  }
  iIntros (w) "[(-> & Hs & Ha & Hj) Hf]".
  iSplit => //.
  iFrame "Hf".
  repeat iSplit => //.
  { by rewrite insert_length. }
  repeat rewrite insert_length. 
  iFrame.
  iDestruct (i32_wss with "Hj") as "Hj". unfold handle_addr; iSimpl in "Hj".
  iDestruct ("Hs" with "Hj") as "Hs".
  done.   
Qed.

Lemma stack_store_j_handle_add v (s: list i32) f E j sv (v0: i32):
  ⌜ s !! (N.to_nat j) = Some sv ⌝ -∗
  ⌜ (j < N.of_nat (length s))%N ⌝ -∗
  isStack v s -∗
  ↪[frame] f -∗
  WP [AI_basic (BI_const (nvalue_of_int (length s *  4 - 4 * Z.of_N j)));
      AI_handle v ;
      AI_basic BI_handleadd ;
      AI_basic (BI_const (NVAL_int32 v0));
      AI_basic (BI_segstore T_i32)] @ E
  {{ w, ⌜ w = immV [] ⌝ ∗ isStack v (<[ N.to_nat j := v0 ]> s) ∗ ↪[frame] f }}.
Proof.
  iIntros "%Hsv %Hjbound Hs Hf" => /=.
  iDestruct (stack_pure with "Hs") as "(%Hoff & %Hbound & %Hvalid & %Hlen)". 

  assert ( (-2147483648 ≤ length s * 4 - 4 * Z.of_N j ≤ 2147483647)%Z) as Hjb'.
  {  unfold two14 in Hlen. lia. }
   assert (handle_add v (length s * 4 - 4 * Z.of_N j) =
  Some
    {|
      base := base v;
      offset := Z.to_N (length s * 4 - 4 * Z.of_N j);
      bound := bound v;
      valid := valid v;
      id := id v
    |}) as Hadd.
   {  unfold handle_add. rewrite Hoff.
      simpl. 
      rewrite Z.add_0_l.
      assert (0 <= length s * 4 - 4 * Z.of_N j)%Z as Hleq; first lia.
      apply Z.geb_le in Hleq. rewrite Hleq. done. } 
  rewrite separate3. iApply wp_seq.
  iSplitR; last first.
  iSplitL "Hf".
  { iApply (wp_wand with "[Hf]").
    iApply (wp_handleadd with "Hf").
    simpl. rewrite wasm_int_signed => //. 
    by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I).
    iIntros (w) "[-> Hf]".
    instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗ ↪[frame] f)%I).
    iFrame. done. }
  2: by iIntros "[% _]".
  iIntros (w) "[-> Hf]".
  iSimpl.
  iApply (stack_store_j with "[] [] [$] [$]"). done. done.
Qed.


  
Lemma positive_add a b :
  a + b = ssrnat.NatTrec.add a b.
Proof.
  by rewrite ssrnat.NatTrec.addE.
Qed.

Lemma nat_of_bin_to_N x :
  Z.to_N (ssrnat.nat_of_bin x) = x.
Proof.
  rewrite nat_bin.
  remember (N.to_nat x) as x'.
  assert (N.of_nat x' = x); first by rewrite Heqx'; rewrite N2Nat.id.
  subst x.
  rewrite - Z_nat_N.
  f_equal.
  by rewrite Nat2Z.id.
Qed.

Lemma divide_and_multiply a b :
  (b > 0)%N -> N.divide b a -> (a `div` b * b = a)%N.
Proof.
  intros ? [c ->].
  rewrite N.div_mul => //.
  lia.
Qed.
  

Lemma div_lt a b c :
  (a < b)%N -> (c > 0)%N -> N.divide c a -> N.divide c b -> (a `div` c < b `div` c)%N.
Proof.
  intros.
  apply divide_and_multiply in H1, H2 => //=.
  rewrite - H1 in H.
  rewrite - H2 in H.
  apply N.mul_lt_mono_pos_r in H => //=.
  lia.
Qed.
      
Fixpoint stackAll {A} (s : seq.seq A) (Φ : A -> iPropI Σ) : iPropI Σ :=
  match s with
  | [] => (True)%I
  | a :: s => (Φ a ∗ stackAll s Φ)%I
  end.


Fixpoint stackAll2 {A} s1 s2 (Ψ : A -> A -> iPropI Σ) :=
  match s1, s2 with
  | [], [] => True%I
  | a1 :: s1, a2 :: s2 => (Ψ a1 a2 ∗ stackAll2 s1 s2 Ψ)%I
  | _, _ => False%I
  end.


Lemma stackAll_app {A} (s : seq.seq A) s' Φ :
  ⊢ stackAll (s ++ s') Φ ∗-∗ stackAll s Φ ∗ stackAll s' Φ.
Proof.
  iSplit.
  - iIntros "H".
    induction s => //=.
    by iFrame.
    iDestruct "H" as "[? H]".
    iFrame.
    exact IHs.
  - iIntros "[Hs Hs']".
    induction s => //=.
    iDestruct "Hs" as "[? Hs]".
    iFrame.
    exact IHs.
Qed.

End proofs.
End Stack.

