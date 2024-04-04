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

Section Example07.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Context `{!wasmG Σ,
      !logrel_na_invs Σ, HHB: HandleBytes, !cinvG Σ, !cancelG Σ}.

  Definition example_program :=
    [
      BI_get_global 1;
      BI_tee_local 0;
      BI_const (xx 42);
      BI_segstore T_i32;
      BI_get_local 0;
      BI_segload T_i32;
      BI_set_global 0 
    ].

  Definition example_function f :=
    [ AI_local 0 f [ AI_basic (BI_block (Tf [] []) example_program) ] ].


  Lemma program_spec f k k' h f0 gv bs x:
    f.(f_inst).(inst_globs) !! 0 = Some k ->
    f.(f_inst).(inst_globs) !! 1 = Some k' ->
    length f.(f_locs) >= 1 ->
    valid h ->
    (offset h + N.of_nat (t_length T_i32) <= bound h)%N ->

    ⊢ {{{ ↪[frame] f0 ∗ N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := gv |}
            ∗ N.of_nat k' ↦[wg] {| g_mut := MUT_mut ; g_val := VAL_handle h |}
            ∗ ↦[wss][ handle_addr h ] bs ∗ ⌜ length bs = 4 ⌝
            ∗ id h ↣[allocated] Some x
      }}}
      example_function f
      {{{ v, ⌜ v = immV [] ⌝
                     ∗ ↪[frame] f0 
                     ∗ N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := VAL_numeric (xx 42) |}
                     ∗ N.of_nat k' ↦[wg] {| g_mut := MUT_mut ; g_val := VAL_handle h |}
                     ∗ (∃ bs, ↦[wss][ handle_addr h ] bs ∗ ⌜ length bs = 4 ⌝)
                     ∗ id h ↣[allocated] Some x
      }}}.
  Proof.
    iIntros (Hglob Hglobh Hlocs Hvalid Hoff Φ) "!> (Hf & Hg & Hgh & Hws & %Hbs & Hall) HΦ".

    iApply (wp_frame_bind with "Hf"); first done.
    iIntros "Hf". 
    rewrite - (app_nil_l [AI_basic _]).
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind. done. 
    
    iSimpl.
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf Hgh".
    iApply (wp_get_global with "[] Hf Hgh") => //.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I). 
    2:by iIntros "[% _]". 
    iIntros (w) "(-> & Hgh & Hf)".

    iSimpl. rewrite (separate2 (AI_handle h)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". fold_const. iApply (wp_tee_local with "Hf").
    iIntros "!> Hf". rewrite (separate1 (AI_const _)).
    iApply (wp_val_app). done. iSplitR; last first.
    iApply (wp_wand with "[Hf]"). iApply (wp_set_local with "[] Hf"). done.
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iIntros (w) "[-> Hf]". iSimpl.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; first done. iExact "Hf".
    by iIntros "!> [% _]".
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". 
                               
    iSimpl. 
    rewrite (separate3 (AI_handle _)). 
    
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf Hall Hws".
    fold_const.
    
    iApply (wp_segstore with "[$Hall $Hws $Hf]") => //.
    iIntros "!> H". instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ _)%I).
    iSplit; [done | iExact "H"].
    2: by iIntros "[[% _] _]".
    iIntros (w) "[(-> & Ha & Hs) Hf]". iSimpl. 
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    simpl. rewrite set_nth_read. done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝ %I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite (separate2 (AI_handle _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Ha Hs Hf".
    iApply (wp_segload with "[$Ha $Hs $Hf]") => //.
    2:{ rewrite map_map. rewrite map_id. done. } 
    done. 
    iIntros "!> H".
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; [done | iExact "H"].
    2: by iIntros "[[% _] _]".
    iIntros (w) "[(-> & Ha & Hs) Hf]". iSimpl.
    fold_const. 
    iApply (wp_wand with "[Hf Hg]"). iApply (wp_set_global with "[] Hf Hg").
    done. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iIntros (w) "(-> & Hg & Hf)".
    
    iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
    iApply wp_wasm_empty_ctx.
    iApply (wp_wand with "[Hf]").
    iApply (wp_label_value with "Hf"). done.
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iIntros (w) "[-> Hf]".
    iExists _. iFrame. iIntros "Hf".
    iSimpl. iApply (wp_wand with "[Hf]").
    iApply (wp_frame_value with "Hf"). done. done.
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iIntros (w) "[-> Hf]". 
    
    iApply "HΦ". 
    iSplit; first done. iFrame. iExists _. iFrame.
    iPureIntro. rewrite map_length. erewrite length_bits.
    by instantiate (1 := T_i32). done. 
  Qed. 
    
    
End Example07. 

Section Example07Host. 
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
          modfunc_locals := [T_handle] ;
          modfunc_body := example_program
        |} ] ;
      mod_tables := [];
      mod_mems := [];
      mod_globals := [];
      mod_elem := [];
      mod_data := [];
      mod_start := Some {| modstart_func := Mk_funcidx 0 |};
      mod_imports := [   {| imp_module := list_byte_of_string "Ret";
                         imp_name := list_byte_of_string "ret_glob";
                           imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |};
                         {| imp_module := list_byte_of_string "Han";
                         imp_name := list_byte_of_string "handle_glob";
                         imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_handle |} |} ];
      mod_exports := []
    |}.

  Definition example_func_impts : seq.seq extern_t := [].
  Definition example_glob_impts : seq.seq extern_t :=
    [ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |};
     ET_glob {| tg_mut := MUT_mut; tg_t := T_handle |}
    ].




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
    exists [Tf [] []],[ ]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
    { apply Forall2_cons. split;auto. } 
  Qed.

   Lemma module_restrictions_example:
    module_restrictions example_module.
  Proof.
    unfold module_restrictions.
    repeat split; try by exists [] => //=.
  Qed.


  Definition example_instantiate g :=
    [ ID_instantiate [] 0 [0%N; 1%N] ;
      H_get_global g ].

  Lemma instantiate_example g_ret g_han wret h:
    typeof wret = T_i32 ->
    ⊢ {{{ ↪[frame] empty_frame ∗ 
            (N.of_nat g_ret) ↦[wg] {| g_mut := MUT_mut; g_val := wret |} ∗
            (N.of_nat g_han) ↦[wg] {| g_mut := MUT_mut; g_val := VAL_handle h |} ∗
            (∃ name, 0%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx g_ret) |}) ∗
            (∃ nameh, 1%N ↪[vis] {| modexp_name := nameh; modexp_desc := MED_global (Mk_globalidx g_han) |}) ∗
            0%N ↪[mods] example_module
      }}}
      ((example_instantiate g_ret,[]) : host_expr)
      {{{  λ v: language.val wasm_host_lang, ⌜v = immHV [xxv 0]⌝ ∨ ⌜v = immHV [xxv 42]⌝ }}} .
  Proof.
    iIntros "%Hret !>" (Φ) "(Hf & Hg & Hgh & Hexp & Hexph & Hmod) HΦ".
    iDestruct "Hexp" as (name) "Hexp".
    iDestruct "Hexph" as (nameh) "Hexph".
    iDestruct (mapsto_ne with "Hg Hgh") as "%Hgg". 
    
    iApply (instantiation_spec_operational_start_seq with "Hf [Hmod Hexp Hexph Hgh Hg]").
    2: exact example_module_typing.
    2: exact module_restrictions_example.
    done. iFrame. 
    iSplitL "Hexp Hexph". 
    unfold import_resources_host => //.
    instantiate (1 := [_;_]). iSimpl. iFrame. 
    iSplitL.
    iSplitL.
    iSplitR.
    repeat iSplit. 
    unfold import_func_resources => //=.
    iPureIntro. unfold func_typecheck => //=. constructor => //. constructor => //. 
    iPureIntro. unfold func_domcheck => //=.
    iSplitR.
    repeat iSplit. 
    unfold import_tab_resources => //.
    iPureIntro. unfold tab_typecheck => //=. constructor => //. constructor => //. 
    iPureIntro. unfold tab_domcheck => //.
    iSplitR.
    repeat iSplit. 
    unfold import_mem_resources => //.
    iPureIntro. unfold mem_typecheck => //=. constructor => //. constructor => //. 
    unfold mem_domcheck => //.
    instantiate (1 := <[ N.of_nat g_han := _ ]> (<[ N.of_nat g_ret := _ ]> ∅)).
    iSplitL. 
    unfold import_glob_resources.
    iApply big_sepM_insert. by rewrite lookup_insert_ne. iFrame. 
    iApply big_sepM_singleton. iFrame. 
    unfold glob_typecheck => //. iPureIntro. split. constructor => //=.
    eexists _,_.
    split. rewrite lookup_insert_ne => //. 
    by rewrite lookup_insert.
    split; first done. 
    unfold global_agree. simpl. by rewrite Hret.
    constructor => //=.
    eexists _,_.
    split; first by rewrite lookup_insert.
    split; first done.
    unfold global_agree. simpl. done. 
    unfold glob_domcheck => //=. by set_solver.
    iSplit; iPureIntro.
    unfold module_elem_bound_check_gmap => //. constructor => //.
    unfold module_data_bound_check_gmap => //. constructor => //.
    iSplit => //. 
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

    iDestruct "Himp" as "(Himp & Himph & _)".
    iDestruct "Hirwt" as "(Hirwtf & Hirwtm & Hirwtt & Hirwtg)".
    iDestruct "Hirwtg" as "(Hg & %Hgtypecheck & %Hgdomcheck)".
    unfold import_glob_resources.
    iDestruct (big_sepM_insert with "Hg") as "[Hgh Hg]".
    by rewrite lookup_insert_ne. 
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hg") as "Hg".
    iClear "Hsing". 

    simpl in Hglobinit.
    destruct (inst_globs inst) eqn:Hglobs => //.
    { inversion Hextglob. simpl in H. done. }
    destruct l.
    { inversion Hextglob. simpl in H. done. } 
    inversion Hextglob. simpl in H. inversion H; subst g g0. 


    unfold check_start in Hstart. simpl in Hstart. rewrite Hfuncs in Hstart.
    move/eqP in Hstart. inversion Hstart; subst f. 

    iApply wp_lift_wasm.
    rewrite - (app_nil_l [AI_invoke _]).
    iApply (wp_invoke_native with "Hf Hfunc") => //.
    iIntros "!> [Hf Hfunc]".
    iApply (program_spec with "[$Hf Hg Hgh]") => //=.
    by rewrite Hglobs. by rewrite Hglobs. lia.
    admit. admit. iFrame. admit. 
(*    iExists _. done. *)
    iIntros (w) "(-> & Hf & H)". iDestruct "H" as "(Hg & Hghan & Hss & Hall)".
    iSimpl.
    iApply (wp_get_global_host _ _ _ _ [] with "Hg").
    iIntros "!> Hg".
    iApply "HΦ". iSimpl.
    by iRight. 
  Admitted. 

    
    
    
    
End Example07Host.
