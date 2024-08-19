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
 

  Context `{!wasmG Σ, !logrel_na_invs Σ, HHB: HandleBytes, cancelg: cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs". 
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ------------------------------------ UNREACHABLE -------------------------------------- *)

  Lemma typing_unreachable C ts ts' : ⊢ semantic_typing C (to_e_list [BI_unreachable]) (Tf ts ts').
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
    iApply wp_wasm_empty_ctx.
    iApply iRewrite_nil_r_ctx.
    rewrite -app_assoc.
    iApply wp_base_push;[apply const_list_of_val|].
    iApply iRewrite_nil_r_ctx.

    iApply (wp_wand_ctx with "[Hf]").
    { iApply wp_seq_trap_ctx. iFrame.
      iSplitR; last first. 
      - iIntros "Hf". 
        iApply (wp_unreachable with "Hf"). by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros "!>" (w) "->". done. }
    
    iIntros (v) "(-> & Hf)".
    iSplitR;[|iExists _,_;iFrame].
    iLeft. iLeft. auto.
  Qed.

End fundamental.
