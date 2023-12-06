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


  Context `{!wasmG Σ, !logrel_na_invs Σ, HHB: HandleBytes, cancelg: cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* --------------------------------------- GETOFFSET -------------------------------------- *)



  Lemma typing_getoffset C : ⊢ semantic_typing C (to_e_list [BI_getoffset]) (Tf [T_handle] [T_i32]).
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
    destruct ws as [|w1 ws];[done|destruct ws;[|done]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv _]".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv" as (h) "(-> & Hv)".
    iSimpl.
    iApply (wp_wand _ _ _ (λne vs, interp_val [T_i32] vs ∗ ↪[frame] f )%I with "[Hf]").
    + iApply (wp_getoffset with "Hf") => //.
      iNext. iSimpl. iRight. iExists _; iSplit; first done. iSimpl. iSplit; last done.
      iExists _. done. 
    + iIntros (v) "[$ Hf]".
      iExists _, _ ;iFrame.
  Qed. 
    
End fundamental.
