From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_rules iris_wp.
Require Export datatypes operations properties opsem typing.
Require Export iris_logrel iris_fundamental_helpers.
Import uPred.

Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ, HHB: HandleBytes, cancelg: cancelG Σ, !cinvG Σ}.
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ------------------------------------------ CALL --------------------------------------- *)

  Lemma typing_call C i tf : ssrnat.leq (S i) (length (tc_func_t C)) ->
                             nth_error (tc_func_t C) i = Some tf ->
                             ⊢ semantic_typing C (to_e_list [BI_call i]) tf.
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hleq Hlookup). destruct tf as [tf1 tf2].
    iIntros (j lh hl) "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f all vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _,_. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".

    iDestruct (interp_instance_function_lookup with "Hi") as (func Hfunc) "Hfunc";[eauto..|].
    unfold interp_function.
    iDestruct "Hfunc" as (cl) "[Hfunc Hcl]".
    iDestruct "Hfv" as (locs Hlocs) "[#Hlocs Hown]".

    (* we open the invariant containing the function reference *)
    iApply fupd_wp.
    iMod (na_inv_acc _ ⊤ with "Hfunc Hown") as "(>Ha & Hown & Hcls)";[solve_ndisj..|].
    iModIntro.

    iApply wp_wasm_empty_ctx.
    iApply iRewrite_nil_r_ctx;rewrite -app_assoc.
    iApply wp_base_push;[apply const_list_of_val|].
    iApply (wp_wand_ctx _ _ _ (λne (v : leibnizO val), ((interp_val tf2 v
                                                         ∨ interp_call_host (tc_local C) j (tc_return C) hl v lh (tc_label C) tf2) ∗ na_own logrel_nais ⊤ ∗ ∃ all, interp_allocator all) ∗ ↪[frame]f)%I with "[-]").
    { iApply (wp_call_ctx with "Hf").
      { rewrite Hlocs /= -nth_error_lookup. eauto. }
      iNext. iIntros "Hf".
      iIntros (LI Hfill%lfilled_Ind_Equivalent);inversion Hfill;simplify_eq.
      erewrite app_nil_r.

      destruct cl.
      { (* native function *)
        destruct f.
        iDestruct "Hcl" as (Heq) "Hcl". inversion Heq;subst r r0.
        iDestruct (big_sepL2_length with "Hv") as %Hlen.
        iApply (wp_invoke_native with "[$] [$]");eauto.
        { apply to_val_fmap. }
        iNext. iIntros "[Hf Ha]".
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iModIntro.

        iApply (wp_wand with "[Hf Hown Hall]").
        { iApply wp_wasm_empty_ctx_frame.
          take_drop_app_rewrite 0.
          iApply (wp_block_local_ctx with "Hf");eauto.
          iNext. iIntros "Hf".
          iApply wp_label_push_nil_local. simpl push_base.
          unfold interp_closure_native.
          erewrite app_nil_l.
          iApply ("Hcl" with "[] Hown Hf Hall").
          iRight. iExists _. eauto. }
        iIntros (v) "[[Hw | Hw] ($ & $ & %all1 & Hall)]".
        { iSplitR "Hall"; first by iLeft.
          by iExists _.
        }
        { iSplitR "Hall"; last by iExists _.
          iRight. iClear "Hi Hcont Hfunc Hcl Hlocs". iLöb as "IH" forall (v).
          rewrite fixpoint_interp_call_host_cls_eq.
          rewrite fixpoint_interp_call_host_eq.
          iDestruct "Hw" as (? ? ? ? ? ? ? ? ? ?) "[#? #H]".
          iExists _,_,_,_,_,_. repeat (iSplit;[eauto|]).
          iModIntro. iIntros (v2 f all0) "? [? Hfrv] Hall0".
          iDestruct "Hfrv" as (?) "[-> [Hv2 ?]]".
          iDestruct ("H" with "[$] [$] [$] [$]") as "H'".
          iApply (wp_wand with "H'").
          iIntros (w) "[[#Hw | Hw] ([%all2 Hall] & ? & ?)]".
          { iSplitR; first admit. (* iSplitR;[by iLeft|]. *)
            iExists _,_. iFrame. iExists _. iFrame. auto. }
          { iSplitL "Hw".
            { repeat iRight. iNext.
              iApply ("IH" with "Hw").  }
            iExists _,_. iFrame. iExists _. iFrame. auto. }          
        }
      }
      { (* host function *)
        destruct f.
        iDestruct "Hcl" as %[Heq HH]. inversion Heq;subst r r0.
        iDestruct (big_sepL2_length with "Hv") as %Hlen.
        iApply (wp_invoke_host with "[$] [$]");eauto.
        iIntros "!> Ha Hf".
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iModIntro.
        iApply wp_value.
        { instantiate (1:=callHostV _ _ _ _). eapply of_to_val. eauto. }
        iFrame. iSplitR; last by iExists _. iRight. iApply fixpoint_interp_call_host_eq.
        iExists _,_,_,_,_,_. do 3 (iSplit;[eauto|]).
        iSplit;[auto|].
        iSplit.
        { iRight. iExists _. eauto. }
        iModIntro. iIntros (v2 f all0) "#Hv2 [Hf Hfv] Hall".
        simpl llfill. rewrite app_nil_r. iApply wp_value;[done|].
        iSplitR;[|iExists _,_;iFrame].
        iLeft. done.
      }
    }

    iIntros (v) "[(Hw & Hown & %all0 & Hall) Hf]".
    iFrame. iSplitR "Hf Hall".
    { iDestruct "Hw" as "[Hw | Hw]";[by iLeft|by iRight;iRight;iRight]. }
    iExists _,_. iFrame. eauto.
Admitted. 
  
End fundamental.
