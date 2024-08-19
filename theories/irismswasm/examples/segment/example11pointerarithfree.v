From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From MSWasm.iris.language.iris Require Import iris iris_locations.
From MSWasm.iris.helpers Require Import iris_properties.
From MSWasm.iris.language Require Import iris_atomicity iris_wp_def.
From MSWasm Require Import stdpp_aux datatypes operations properties opsem type_checker_reflects_typing instantiation.
From MSWasm.iris.host Require Import iris_host.
From MSWasm.iris.rules Require Import iris_rules proofmode iris_example_helper.
From MSWasm.iris.logrel Require Import iris_fundamental iris_interp_instance_alloc.
From MSWasm.iris.instantiation Require Import iris_instantiation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section Example11.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Context `{!wasmG Σ,
      !logrel_na_invs Σ, HHB: HandleBytes, !cinvG Σ, !cancelG Σ}.


(* 
allocate a handle (h 0) with space for two i32s
define (h' 1) as h+4
free (h' 1)
*)


  
  Definition example_program :=
    [
      BI_const (xx 8);
      BI_segalloc;
      BI_set_local 0;
      BI_const (xx 4);
      BI_get_local 0;
      BI_handleadd;
      BI_tee_local 1;
      BI_segfree
    ].

  Definition example_function f :=
    [ AI_local 0 f [ AI_basic (BI_block (Tf [] []) example_program) ] ].


  Lemma program_spec f f0:
    length f.(f_locs) >= 2 ->

    ⊢ {{{ ↪[frame] f0 }}}
      example_function f
      {{{ v, ⌜ v = trapV ⌝ }}}.
  Proof.
    iIntros (Hlocs Φ) "!> Hf HΦ".

    iApply (wp_frame_bind with "Hf"); first done.
    iIntros "Hf". 
    rewrite - (app_nil_l [AI_basic _]).
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind. done. 
    
    iSimpl.
    rewrite (separate2 (AI_basic _)).
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf".
    unfold xx. fold_const.
    iApply (wp_wand with "[-]").
    iApply (wp_segalloc with "[$Hf]"); first done.
    iIntros "!>" (w) "H". iExact "H".
    iIntros (w) "[(%h & -> & H) Hf]".
    iSimpl.
    instantiate (1 := λ x, ((∃ h, ⌜ x = immV [VAL_handle h] ⌝ ∗ _) ∗ ↪[frame] f)%I).
    iSimpl. iFrame. iExists h. iSplit; first done. iExact "H".
    2: by iIntros "[(%h & % & _) _]". 
    iIntros (w) "[(%h & -> & Hh) Hf]".

    iSimpl. rewrite (separate2 (AI_handle h)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". fold_const. iApply (wp_set_local with "[] Hf").
    lia. 
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    2: by iIntros "[% _]". 
    iIntros (w) "[-> Hf]". iSimpl.
    
                               

    iSimpl. rewrite (separate2 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    rewrite (separate1 (AI_basic _)).
    iApply wp_val_app. done.
    iSplitR; last first.
    iApply (wp_wand with "[Hf]"). iApply (wp_get_local with "[] Hf").
    rewrite set_nth_read. done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    iIntros (w) "[-> Hf]".
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; [done | iExact "Hf"].
    by iIntros "!> [% _]". 
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate3 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_handleadd with "Hf").
    unfold handle_add. simpl. assert (Z.of_N (offset h) >= 0)%Z; first lia.
    rewrite Wasm_int.Int32.signed_repr. 
    assert (0 <= Z.of_N (offset h) + 4)%Z; first lia.
    apply Z.leb_le in H0. rewrite - Z.geb_leb in H0.
    rewrite H0. done.
    done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]". 
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite (separate2 (AI_handle _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". fold_const. iApply (wp_tee_local with "Hf").
    iIntros "!> Hf". rewrite (separate1 (AI_const _)).
    iApply (wp_val_app). done. iSplitR; last first.
    iApply (wp_wand with "[Hf]"). iApply (wp_set_local with "[] Hf").
    remember (f_locs f) as l. repeat (destruct l; first by simpl in Hlocs; lia).
    done. 
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iIntros (w) "[-> Hf]". iSimpl.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; first done. iExact "Hf".
    by iIntros "!> [% _]".
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". 
    iSimpl.
    iDestruct "Hh" as "[-> | (Ha & %Hbound & %Hoff & %Hvalid & Hs)]".
    { (* case 1: the allocation failed *)
      iApply (wp_wand with "[Hf]"). iApply (wp_segfree_failure1 with "[$Hf]").
      by right. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx. iApply (wp_wand with "[Hf]").
      iApply (wp_label_trap with "Hf"). done. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iExists _. iFrame. iIntros "Hf".
      iApply (wp_wand with "[Hf]"). iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iApply "HΦ". done. } 
    (* case 2: the allocation succeeded *)
    iApply (wp_wand with "[Hf]"). iApply (wp_segfree_failure1 with "[$Hf]").
    left. simpl. rewrite Hoff. lias.
    by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
    iIntros (w) "[-> Hf]".
    iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
    iApply wp_wasm_empty_ctx.
    iApply (wp_wand with "[Hf]"). iApply (wp_label_trap with "Hf").
    done. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
    iIntros (w) "[-> Hf]".
    iExists _. iFrame. iIntros "Hf". iSimpl.
    iApply (wp_wand with "[Hf]"). iApply (wp_frame_trap with "Hf").
    by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
    iIntros (w) "[-> Hf]". iApply "HΦ". done. 
  Qed. 
  
    
End Example11. 

Section Example11Host. 
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ,
        !logrel_na_invs Σ, HHB: HandleBytes, !cancelG Σ, !cinvG Σ}.

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).
  Notation "{{{ P }}} es {{{ Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q v -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Notation " n ↪[vis]{ q } v" := (ghost_map_elem (V := module_export) visGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[vis]{ q } v") .
  Notation " n ↪[vis] v" := (ghost_map_elem (V := module_export) visGName n (DfracOwn 1) v%V)
                          (at level 20, format " n ↪[vis] v").
  
  Notation " n ↪[mods]{ q } v" := (ghost_map_elem (V := module) msGName n q v%V)
                           (at level 20, q at level 5, format " n ↪[mods]{ q } v") .
  Notation " n ↪[mods] v" := (ghost_map_elem (V := module) msGName n (DfracOwn 1) v%V)
                               (at level 20, format " n ↪[mods] v").

  Lemma wp_wand_host s E (e : host_expr) (Φ Ψ : language.val wasm_host_lang -> iProp Σ) :
    WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
  Proof. iApply (weakestpre.wp_wand). Qed.


    Definition example_module :=
    {| mod_types := [Tf [] []];
       mod_funcs :=  [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_handle; T_handle; T_handle] ;
          modfunc_body := example_program
        |} ] ;
      mod_tables := [];
      mod_mems := [];
      mod_globals := [];
      mod_elem := [];
      mod_data := [];
      mod_start := Some {| modstart_func := Mk_funcidx 0 |};
      mod_imports := [];
      mod_exports := []
    |}.

  Definition example_func_impts : seq.seq extern_t := [].
  Definition example_glob_impts : seq.seq extern_t := []. 




  Ltac type_next :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop;
      eapply bet_composition;[|econstructor;eauto];simpl
  end.


  
  Lemma example_module_typing :
    module_typing example_module (example_func_impts ++ example_glob_impts)
      []. 
  Proof. 
    exists [Tf [] []],[  ]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      unfold example_program. rewrite (separate6 (BI_const _)).
      eapply bet_composition'.
      { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
      { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. } } 
  Qed.

   Lemma module_restrictions_example:
    module_restrictions example_module.
  Proof.
    unfold module_restrictions.
    repeat split; try by exists [] => //=.
  Qed.


  Definition example_instantiate :=
    [ ID_instantiate [] 0 [] ]. 


  Lemma instantiate_example :
    ⊢ {{{ ↪[frame] empty_frame ∗ 
            0%N ↪[mods] example_module 
      }}}
      ((example_instantiate,[]) : host_expr)
      {{{  λ v: language.val wasm_host_lang, ⌜v = trapHV ⌝ }}}. 
  Proof.
    iIntros "!>" (Φ) "(Hf & Hmod) HΦ".
    iApply (instantiation_spec_operational_start_seq with "Hf [$Hmod]").
    2: exact example_module_typing.
    2: exact module_restrictions_example.
    done. repeat iSplit ; try by iPureIntro; try constructor.  
    unfold import_resources_host => //.
    unfold import_func_resources => //=.
    unfold import_tab_resources => //.
    unfold import_mem_resources => //.
    unfold import_glob_resources => //. 
    unfold export_ownership_host => //. 
    iIntros (id) "Hf (Hmod & Himp & %inst & Hpost & Hexp)".
    iDestruct "Hpost" as (??????) "(Hirwt & %Htypr & %Htabinits & %Hwts'0 & %Hbounds_elem & %Hmem_init & %Hwms0' & %Hbounds_data & %Hglobsr & %Hglobinit & Hfuncs & Htabs & Hmems & Hglobs)".

    simpl in Htypr.
    destruct Htypr as (Hinst_types & Hextfunc & Hexttab & Hextmem & Hextglob & Hstart).

    
    iDestruct (big_sepL2_length with "Hfuncs") as "%Hlenfuncs".
    unfold get_import_func_count in Hlenfuncs. simpl in Hlenfuncs.
    rewrite drop_0 in Hlenfuncs.
    destruct (inst_funcs inst) eqn:Hfuncs => //.
    destruct l => //.
    iDestruct "Hfuncs" as "[Hfunc _]". rewrite Hinst_types. iSimpl in "Hfunc". 


    unfold check_start in Hstart. simpl in Hstart. rewrite Hfuncs in Hstart.
    move/eqP in Hstart. inversion Hstart; subst f. 

    iApply wp_lift_wasm.
    rewrite - (app_nil_l [AI_invoke _]).
    iApply (wp_invoke_native with "Hf Hfunc") => //.
    iIntros "!> [Hf Hfunc]".
    iApply (program_spec with "[$Hf]") => //=.
    lia.
    iIntros (w) "->". iApply iris_host.wp_value. done.
    iApply "HΦ". done. 
  Qed. 

    
    
    
    
End Example11Host.
