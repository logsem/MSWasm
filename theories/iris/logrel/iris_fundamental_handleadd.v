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

  (* --------------------------------------- HANDLEADD -------------------------------------- *)



  Lemma typing_handleadd C : ⊢ semantic_typing C (to_e_list [BI_handleadd]) (Tf [T_i32; T_handle] [T_handle]).
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
    destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[done|destruct ws;[|done]]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 [Hv2 _]]".
    iDestruct "Hv1" as (z) "->".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv2" as (h) "(-> & #Hv)". 
    iSimpl.
*    destruct (handle_add h (Wasm_int.Z_of_sint i32m z)) eqn:Hhadd. 
    - (* Sucessful adding *)
      iApply (wp_wand _ _ _ (λne vs, interp_val [T_handle] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_handleadd with "Hf") => //.
        iNext. iSimpl. iRight. iExists _; iSplit; first done. iSimpl. iSplit; last done.
        rewrite fixpoint_interp_value_handle_eq.
        iSimpl. iExists h0.
        iSplit; first done.
        unfold handle_add in Hhadd. destruct (_ >=? _)%Z eqn:Hoff => //.
        apply Z.geb_le in Hoff.
        destruct h0; inversion Hhadd; subst; simpl.
        iDestruct "Hv" as "[-> | (%γ & %base' & %bound' & %base_all & %bound_all & %q & %Hq & Hw & %Hbase_all & %Hbase & %Hbound_all & %Hbound & Hinv)]";
          first by iLeft. iRight. iExists _,_,_,_,_,_. iFrame "Hw". iFrame "Hinv".
        done.
      + iIntros (v) "[$ Hf]".
        iExists _,_;iFrame.
    - (* Failed slicing *)
       iApply (wp_wand _ _ _ (λne vs, interp_val [T_handle] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_handleadd_failure with "Hf") => //.
        iNext. iSimpl. iLeft. done. 
      + iIntros (v) "[$ Hf]".
        iExists _,_;iFrame.
  Qed. 
    
End fundamental.
