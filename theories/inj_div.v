Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Lia.
Require Import Coq.Arith.Div2.
Require Import Coq.Arith.Plus.
From mathcomp Require Import ssreflect.
From Coq Require Import NArith. 


Lemma Nat2N_inj_div : forall a b : nat,
    b <> 0 ->
    N.of_nat (a / b) = (N.of_nat a / N.of_nat b)%N.
Proof.
  intros a b Hb. 
  assert (a = b * (a / b) + a mod b).
  { apply Nat.div_mod. done. }
  assert (N.of_nat a = N.of_nat b * (N.of_nat a / N.of_nat b) + N.modulo (N.of_nat a) (N.of_nat b))%N.
  { apply N.div_mod. lia. }
  assert (N.of_nat a = N.of_nat (b * (a / b) + a mod b)).
  { lia. }
  rewrite Nat2N.inj_add in H1.
  rewrite Nat2N.inj_mul in H1.
  rewrite H0 in H1.
  apply N.div_mod_unique in H1.
  lia.
  apply N.mod_upper_bound. lia. 
  assert (a mod b < b); last lia. 
  apply Nat.mod_upper_bound. done.
Qed. 

