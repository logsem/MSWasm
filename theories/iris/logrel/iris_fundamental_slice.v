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

  (* ----------------------------------------- SLICE -------------------------------------- *)



  Lemma typing_slice C : ⊢ semantic_typing C (to_e_list [BI_slice]) (Tf [T_handle; T_i32; T_i32] [T_handle]).
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
    destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[done|destruct ws as [|w3 ws];[done|destruct ws;[|done]]]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 [Hv2 [Hv3 _]]]".
    iDestruct "Hv3" as (z2) "->".
    iDestruct "Hv2" as (z1) "->".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv1" as (h γ base' bound') "(-> & #Hw & %Hbase' & %Hbound' & Hinv)".
    iSimpl.
    destruct (slice_handle h (Wasm_int.N_of_uint i32m z1) (Wasm_int.N_of_uint i32m z2)) eqn:Hslice.
    - (* Sucessful slicing *)
      iApply (wp_wand _ _ _ (λne vs, interp_val [T_handle] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_slice with "Hf") => //.
        iNext. iSimpl. iRight. iExists _; iSplit; first done. iSimpl. iSplit; last done.
        rewrite fixpoint_interp_value_handle_eq.
        iSimpl. iExists h0, γ, base', bound'.
        iSplit; first done.
        unfold slice_handle in Hslice. destruct (_ <? _)%N eqn:Hbound => //.
        destruct (_ <=? _)%N eqn:Hbound2 => //.
        apply N.ltb_lt in Hbound.
        apply N.leb_le in Hbound2.
        destruct h0; inversion Hslice; subst; simpl. iFrame "Hw". iFrame "Hinv".
        iSplit; iPureIntro; try lia.
        replace 
          (Z.to_N (Wasm_int.Int32.unsigned z1)) with (Wasm_int.N_of_uint i32m z1) ; last lias.
        replace
          (Z.to_N (Wasm_int.Int32.unsigned z2)) with (Wasm_int.N_of_uint i32m z2) ; last lias.
        lia.
      + iIntros (v) "[$ Hf]".
        iExists _;iFrame.
    - (* Failed slicing *)
       iApply (wp_wand _ _ _ (λne vs, interp_val [T_handle] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_slice_failure with "Hf") => //.
        iNext. iSimpl. iLeft. done. 
      + iIntros (v) "[$ Hf]".
        iExists _;iFrame.
  Qed. 
    
End fundamental.
