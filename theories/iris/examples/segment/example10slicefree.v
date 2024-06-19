From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_rules iris_fundamental iris_wp iris_interp_instance_alloc.
Require Export iris_example_helper proofmode.
Require Export datatypes operations properties opsem.
Require Export type_checker_reflects_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section Example10.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Context `{!wasmG Σ,
      !logrel_na_invs Σ, HHB: HandleBytes, !cinvG Σ, !cancelG Σ}.


(* 
allocate a handle (h 0) with space for two i32s
if allocation failed, trap
slice it into halves (h' 1) and (h'' 2)
free (h'' 2)
*)


  
  Definition example_program :=
    [
      BI_const (xx 8);
      BI_segalloc;
      BI_tee_local 0;
      BI_isdummy;
      BI_if (Tf [] []) [ BI_unreachable ] [];
      BI_get_local 0;
      BI_const (xx 0);
      BI_const (xx 4);
      BI_slice;
      BI_set_local 1;
      BI_get_local 0;
      BI_const (xx 4);
      BI_const (xx 4);
      BI_slice;
      BI_set_local 2;
      BI_get_local 2;
      BI_segfree
    ].

  Definition example_function f :=
    [ AI_local 0 f [ AI_basic (BI_block (Tf [] []) example_program) ] ].


  Lemma program_spec f f0:
    length f.(f_locs) >= 3 ->

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
    iSplitL "Hf". fold_const. iApply (wp_tee_local with "Hf").
    iIntros "!> Hf". rewrite (separate1 (AI_const _)).
    iApply (wp_val_app). done. iSplitR; last first.
    iApply (wp_wand with "[Hf]"). iApply (wp_set_local with "[] Hf"). lia. 
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iIntros (w) "[-> Hf]". iSimpl.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; first done. iExact "Hf".
    by iIntros "!> [% _]".
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". 
                               

    iSimpl. rewrite (separate2 (AI_handle h)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    iApply (wp_isdummy with "Hf").
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_basic _)).
        
    iDestruct "Hh" as "[-> | (Ha & %Hbound & %Hoff & %Hvalid & Hs)]".
    { (* Case 1: segalloc failed *)

      iApply (wp_wand with "[Hf]"). iApply wp_seq_trap.
      iFrame. iSplitR; last first. iIntros "Hf". 
      
      iApply (wp_if_true with "Hf"). done. 
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic _]). iApply (wp_block with "Hf") => //.
      iIntros "!> Hf".
      
      iApply wp_wasm_empty_ctx. iApply wp_label_push_nil. iApply wp_ctx_bind. done.
      iSimpl.
      iApply (wp_wand with "[Hf]"). iApply (wp_unreachable with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I). 
      iIntros (w) "(-> & Hf)".
      iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx.

      iApply (wp_label_trap with "Hf"). done.
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      by iIntros "!>" (?) "%".
      iIntros (w)  "(-> & Hf)".
      iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx.
      iApply (wp_wand with "[Hf]"). iApply (wp_label_trap with "Hf").
      done. by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]".
      iExists _. iFrame. iIntros "Hf". iSimpl.
      iApply (wp_wand with "[Hf]"). iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]". iApply "HΦ". done. 
    }

    (* Case 2: segalloc succeeded *)

    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf".
    iApply (wp_if_false with "Hf"). unfold is_dummy. rewrite Hvalid. simpl.
    rewrite andb_false_r. simpl. done.
    iIntros "!> Hf".
    rewrite - (app_nil_l [AI_basic _]).
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf".
    iApply (wp_label_value with "Hf"). done.
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". 

    
    iSimpl. rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    simpl. rewrite set_nth_read. done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]". 
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite (separate4 (AI_handle _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". 
         
    iApply (wp_slice with "Hf") => //=.
    unfold slice_handle. rewrite Hbound. simpl. done. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_handle _)).
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf". fold_const. iApply (wp_set_local with "[] Hf").
    simpl. destruct (f_locs f); try by simpl in Hlocs; lia.
    repeat (destruct l; first by simpl in Hlocs; lia). simpl. lia.
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I). iSimpl.
    2: by iIntros "[% _]". 
    iIntros (w) "[-> Hf]".

     iSimpl. rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    simpl. remember (f_locs f) as l.
    repeat (destruct l; first by simpl in Hlocs; lia). simpl. done. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]". 
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite (separate4 (AI_handle _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". 
         
    iApply (wp_slice with "Hf") => //=.
    unfold slice_handle. rewrite Hbound. simpl. done. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_handle _)).
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf". fold_const. iApply (wp_set_local with "[] Hf").
    simpl. destruct (f_locs f); try by simpl in Hlocs; lia.
    repeat (destruct l; first by simpl in Hlocs; lia). simpl. lia.
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I). iSimpl.
    2: by iIntros "[% _]". 
    iIntros (w) "[-> Hf]". 
    


    iSimpl. rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    simpl. remember (f_locs f) as l. repeat (destruct l; first by simpl in Hlocs; lia). done. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝ %I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.
    iApply (wp_wand with "[Hf Ha]"). iApply (wp_segfree_failure2 with "[$Hf Ha]").
    2:{ iSimpl. iFrame. iIntros "!> Ha". instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _)%I).
        iSplit; [done | iExact "Ha"]. }
    simpl. lia.
    iIntros (w) "[[-> Ha] Hf]".
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
    
    
End Example10. 

Section Example10Host. 
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
    exists [Tf [] []],[]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      unfold example_program. rewrite (separate6 (BI_const _)).
      eapply bet_composition'.
      { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
      { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. } } 
    { constructor. } 
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

    
    
    
    
End Example10Host.
