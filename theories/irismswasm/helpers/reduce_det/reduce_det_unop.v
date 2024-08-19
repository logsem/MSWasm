From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From MSWasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.
From MSWasm Require Import operations opsem.


Section reduce_det_unop.
  Context `{ HHB : HandleBytes }.

Lemma unop_det v op t s f me s' f' es:
  reduce s f [AI_const v; AI_basic (BI_unop t op)] me s' f' es ->
  reduce_det_goal ME_empty s f [AI_const (app_unop op v)] me s' f' es [AI_const v; AI_basic (BI_unop t op)].
Proof.
  move => Hred.
  - (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
  by only_one [AI_const v ; AI_basic (BI_unop t op)] Hred.
Qed.


End reduce_det_unop.
