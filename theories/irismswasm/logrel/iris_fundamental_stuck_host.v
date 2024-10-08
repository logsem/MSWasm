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

    
  Lemma typing_local_stuck_host C es τ1 τ2 τs hl :
    (∀ C es τ, be_typing C es τ -> ⊢ semantic_typing C (to_e_list es) τ) ->
    (tc_label C) = [] ∧ (tc_return C) = None ->
    be_typing (upd_local_label_return C (τ1 ++ τs) [τ2] (Some τ2)) es (Tf [] τ2) ->
    ⊢ semantic_typing_local_stuck_host hl C es τs (Tf τ1 τ2).
  Proof.
    intros be_fundamental Hnil Htyping.
    iSplit;[auto|].
    iIntros (i) "#Hi". iIntros (f all vs) "Hf Hown Hall #Hv".
    apply be_fundamental in Htyping.
    iDestruct (Htyping) as "Ht".
    iDestruct (interp_instance_change_label [τ2] with "Hi") as "Hi'".
    iDestruct (interp_instance_change_return (Some τ2) with "Hi'") as "Hi''".
    iDestruct (interp_instance_change_local τ1 with "Hi''") as "Hi_final".
    iSpecialize ("Ht" $! _ (LH_rec [] (length τ2) [] (LH_base [] []) []) with "[$Hi_final] []").
    { unfold interp_ctx. iSimpl. repeat (iSplit;[by auto|]).
      iSplit =>//. unfold interp_ctx_continuation.
      iSimpl. iExists _,_,_,_,_,(LH_base [] []). iSplit;[eauto|].
      repeat (iSplit;[by auto|]). iModIntro.
      iIntros (v f' all') "#Hv' [Hf' Hfv'] Hall'".
      iExists τ2. rewrite app_nil_l !app_nil_r.
      iApply wp_value;[done|].
      iSplitR;[|iExists _,_;iFrame].
      iLeft. iFrame "Hv'". }

    destruct (iris.to_val [AI_local (length τ2) {| f_locs := vs; f_inst := i |}
                                    [AI_label (length τ2) [] (to_e_list es)]]) eqn:Hetov.
    { apply to_val_local_inv in Hetov as Heq.
      destruct Heq as [tf [h [w [vh Heq]]]]. subst v.
      apply to_val_call_host_rec_local in Hetov as Heq.
      destruct Heq as [LI [Heq HLI]].
      simpl in Heq. inversion Heq. subst.
      apply to_val_call_host_label_inv in HLI as Heq'.
      destruct Heq' as [vh' [Heq' Hvh']]. subst.
      apply to_es_list_llfill_contr in Hvh'. done.
    }

    unfold interp_expression_closure.
    iApply (wp_wand _ _ _ ((λ vs0,
               (interp_val τ2 vs0
                ∨ interp_call_host_cls hl τ2 vs0) ∗
               ↪[frame]f ∗ na_own logrel_nais ⊤ ∗ ∃ all, interp_allocator all)%I) with "[-]").
    { iApply (wp_frame_bind with "Hf");[auto|].
      iIntros "Hf".
      iApply wp_wasm_empty_ctx.
      iApply wp_label_push_nil.
      iApply wp_label_bind.
      iDestruct ("Ht" $! _ _ (immV []) with "[$Hf Hown] Hall []") as "Hcont".
      { iExists _. iFrame. iSplit;eauto. }
      { iRight. iExists _. iSplit;eauto. } 
      iSimpl in "Hcont". unfold interp_expression.
      iApply (wp_wand with "Hcont").
      iClear "Ht".
      iIntros (v) "[Hv' Hf0]".
      iDestruct "Hf0" as (f0 all0) "(Hf0 & Hf0v & Hall0)".
      iDestruct "Hv'" as "[[-> | Hv'] | [Hbr | [Hret | Hch] ]]";simpl language.of_val.
      { iDestruct (local_host_trap with "[$] [$] [$]") as "H".
        iApply (wp_wand_ctx with "H").
        iIntros (v) "(%f1 & H & Hf & Hall)".
        iExists _. iFrame. iIntros "Hf". iDestruct ("H" with "Hf Hall") as "H".
        iApply (wp_wand with "H"). iIntros (?) "(H & Hall & Hf & Hown)".
        iFrame. by iExists _.
      }
      { iDestruct(local_host_val with "[$] [$] [$] [$]") as "H".
        iApply (wp_wand_ctx with "H").
        iIntros (?) "(%f1 & H & Hf & Hall)".
        iExists _. iFrame. iIntros "Hf". iDestruct ("H" with "Hf Hall") as "H".
        iApply (wp_wand with "H"). iIntros (?) "(H & Hall & Hf & Hown)".
        iFrame. by iExists _. 
      }
      { iDestruct (local_host_br with "[$] [$] [$] Hall0") as "H".
        iApply (wp_wand_ctx with "H").
        iIntros (?) "(%f1 & H & Hf & Hall)".
        iExists _. iFrame. iIntros "Hf". iDestruct ("H" with "Hf Hall") as "H".
        iApply (wp_wand with "H"). iIntros (?) "(H & Hall & Hf & Hown)".
        iFrame. by iExists _.
      }
      { iDestruct (local_host_ret with "[$] [$] [$] [$]") as "H".
        iApply (wp_wand_ctx with "H").
        iIntros (?) "(%f1 & H & Hf & Hall)".
        iExists _. iFrame. iIntros "Hf". iDestruct ("H" with "Hf Hall") as "H".
        iApply (wp_wand with "H"). iIntros (?) "(H & Hall & Hf & Hown)".
        iFrame. by iExists _.
      }
      { iDestruct (local_host_call with "[$] [$] [$] [$]") as "H".
        iApply (wp_wand_ctx with "H").
        iIntros (?) "(%f1 & H & Hf & Hall)".
        iExists _. iFrame. iIntros "Hf". iDestruct ("H" with "Hf Hall") as "H".
        iApply (wp_wand with "H"). iIntros (?) "(H & Hall & Hf & Hown)".
        iFrame. by iExists _.
      }
    } 
    iIntros (v) "($ & $ & $ & $)".
  Qed. 
  
End fundamental.
