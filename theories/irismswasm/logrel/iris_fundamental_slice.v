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

  (* ----------------------------------------- SLICE -------------------------------------- *)



  Lemma typing_slice C : ⊢ semantic_typing C (to_e_list [BI_slice]) (Tf [T_handle; T_i32; T_i32] [T_handle]).
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
    destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[done|destruct ws as [|w3 ws];[done|destruct ws;[|done]]]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 [Hv2 [Hv3 _]]]".
    iDestruct "Hv3" as (z2) "->".
    iDestruct "Hv2" as (z1) "->".
    rewrite fixpoint_interp_value_handle_eq.
    iDestruct "Hv1" as (h) "(-> & #Hv)". 
    iSimpl.
    destruct (slice_handle h (Wasm_int.N_of_uint i32m z1) (Wasm_int.N_of_uint i32m z2)) eqn:Hslice.
    - (* Sucessful slicing *)
      iApply (wp_wand _ _ _ (λne vs, interp_val [T_handle] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_slice with "Hf") => //.
        iNext. iSimpl. iRight. iExists _; iSplit; first done. iSimpl. iSplit; last done.
        rewrite fixpoint_interp_value_handle_eq.
        iSimpl. iExists h0.
        iSplit; first done.
        unfold slice_handle in Hslice. destruct (_ <? _)%N eqn:Hbound => //.
        destruct (_ <=? _)%N eqn:Hbound2 => //.
        apply N.ltb_lt in Hbound.
        apply N.leb_le in Hbound2.
        destruct h0; inversion Hslice; subst; simpl.
        iDestruct "Hv" as "[-> | (%γ & %base' & %bound' & %base_all & %bound_all & %q & %Hq & Hw & %Hbase_all & %Hbase' & %Hbound_all & %Hbound' & Hinv)]"; first by iLeft.
        iRight. iExists _,_,_,_,_,_.
        iFrame "Hw". iFrame "Hinv".
        iSplit; iPureIntro; try lia.
        { destruct (base_all =? base h + _)%N eqn:Hbase.
          - apply N.eqb_eq in Hbase as ->.
            destruct (bound_all =? bound h - _)%N eqn:Hbounds.
            + apply N.eqb_eq in Hbounds as ->.
              simpl.
              destruct (base h + _ =? _)%N eqn:Hbase.
              * destruct (bound h - _ =? _)%N eqn:Hbounds; first done.
                apply N.eqb_neq in Hbounds. lia.
              * apply N.eqb_neq in Hbase. lia.
            + simpl. destruct (_ && _) ; [by left| done].
          - destruct (_ && _) ; [by left | done]. 
        }
        replace 
          (Z.to_N (Wasm_int.Int32.unsigned z1)) with (Wasm_int.N_of_uint i32m z1) ; last lias.
        replace
          (Z.to_N (Wasm_int.Int32.unsigned z2)) with (Wasm_int.N_of_uint i32m z2) ; last lias.
        lia.
      + iIntros (v) "[$ Hf]".
        iExists _,_;iFrame.
    - (* Failed slicing *)
       iApply (wp_wand _ _ _ (λne vs, interp_val [T_handle] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_slice_failure with "Hf") => //.
        iNext. iSimpl. iLeft. done. 
      + iIntros (v) "[$ Hf]".
        iExists _,_;iFrame.
  Qed. 
    
End fundamental.
