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

Section Example01.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Context `{!wasmG Σ,
      !logrel_na_invs Σ, HHB: HandleBytes, !cinvG Σ, !cancelG Σ}.

  (*
allocate a handle h with space for one i32
if allocation failed, set global variable g to 0 and return
write 42 to h
read from h
set global variable g to the read value
free h
*)

  Definition example_program :=
    [
      BI_const (xx 4);
      BI_segalloc;
      BI_tee_local 0;
      BI_isdummy;
      BI_if (Tf [] []) [ BI_const (xx 0) ; BI_set_global 0; BI_return ] [];
      BI_get_local 0;
      BI_const (xx 42);
      BI_segstore T_i32;
      BI_get_local 0;
      BI_segload T_i32;
      BI_set_global 0;
      BI_get_local 0;
      BI_segfree
    ].

  Definition example_function f :=
    [ AI_local 0 f [ AI_basic (BI_block (Tf [] []) example_program) ] ].


  Lemma program_spec f k f0 gv:
    f.(f_inst).(inst_globs) !! 0 = Some k ->
    length f.(f_locs) >= 1 ->

    ⊢ {{{ ↪[frame] f0 ∗ N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := gv |} }}}
      example_function f
      {{{ v, ⌜ v = immV [] ⌝ ∗ ↪[frame] f0 ∗ (∃ gv, N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := VAL_numeric (xx gv) |} ∗ ⌜ gv = 0 ∨ gv = 42 ⌝) }}}.
  Proof.
    iIntros (Hglob Hlocs Φ) "!> (Hf & Hg) HΦ".

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
    iApply (wp_wand with "[Hf]"). iApply (wp_set_local with "[] Hf"). done.
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

      iApply wp_seq.
      iSplitR; last first.
      iSplitL. 
    
      iApply (wp_if_true with "Hf"). done. 
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic _]). iApply (wp_block with "Hf") => //.
      iIntros "!> Hf".
      
      iApply wp_wasm_empty_ctx. iApply wp_label_push_nil. iApply wp_ctx_bind. done.
      iSimpl. rewrite (separate2 (AI_basic _)).
      iApply wp_seq.
      iSplitR; last first.
      iSplitL "Hf Hg".
      fold_const. iApply (wp_set_global with "[] Hf Hg"). done.
      by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
      2: by iIntros "[% _]".
      iIntros (w) "(-> & Hg & Hf)".
      iSimpl. iApply iris_wp.wp_value. apply iris.of_to_val. done.
      iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx. 

      iApply iris_wp.wp_value.
      unfold IntoVal. apply language.of_to_val. done.
      instantiate (1 := λ x, (⌜ x = retV _ ⌝ ∗ _)%I).
      iSplit; first done.
      iCombine "HΦ Hg Hf" as "H". iExact "H".
      2: by iIntros "[% _]".
      iIntros (w) "(-> & HΦ & Hg & Hf)".
      iSimpl. iApply iris_wp.wp_value. apply iris.of_to_val. done. 
           
      iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx. 
      iApply iris_wp.wp_value. apply iris.of_to_val. done.
      iExists _. iFrame. iIntros "Hf". iSimpl.
      iApply (wp_wand with "[Hf]").
      iApply wp_return.
      3:{ instantiate (3 := 2). instantiate (1 := []). 
          instantiate (1 := LH_rec [] _ _ (LH_rec [] _ _ (LH_base [] []) _) []).
          unfold lfilled, lfill. simpl. done. }
      done. done.
      iNext. iApply iris_wp.wp_value. apply iris.of_to_val => //. iFrame.
      by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
      iIntros (w) "[-> Hf]".
      iApply "HΦ". iSplit => //. iFrame. iExists _. iFrame.
      iPureIntro. by left. }

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

    
    iSimpl.
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    simpl. rewrite set_nth_read. done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝ %I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate3 (AI_handle _)). 
    
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf Ha Hs".
    fold_const.
    replace (base h) with (handle_addr h); last by unfold handle_addr; rewrite Hoff; lia.
    iApply (wp_segstore with "[$Ha $Hs $Hf]") => //.
    rewrite Hoff Hbound. simpl. lia.
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
    done. rewrite Hoff Hbound. simpl. lia.
    iIntros "!> H".
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; [done | iExact "H"].
    2: by iIntros "[[% _] _]".
    iIntros (w) "[(-> & Ha & Hs) Hf]". iSimpl.
    rewrite (separate2 (AI_basic _)).
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf Hg". 
    fold_const. 
    iApply (wp_set_global with "[] Hf Hg").
    done. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    2: by iIntros "[% _]". 
    iIntros (w) "(-> & Hg & Hf)".
    iSimpl. rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    rewrite set_nth_read. done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]".
    iSimpl. iApply (wp_wand with "[Hf Ha Hs]").
    unfold handle_addr. rewrite Hoff N.add_0_r.
    rewrite - Hbound. 
    iApply (wp_segfree with "[$Hf $Ha $Hs]") => //.
    rewrite map_length. rewrite (length_bits _ T_i32) => //.
    by rewrite Hbound. 
    iIntros "!> Ha". instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; [done | iExact "Ha"].
    iIntros (w) "[[-> Ha] Hf]". 
                                                      
    
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
    iPureIntro. by right. 
  Qed. 
    
    
End Example01. 

Section Example01Host. 
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
                         imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |} ];
      mod_exports := []
    |}.

  Definition example_func_impts : seq.seq extern_t := [].
  Definition example_glob_impts : seq.seq extern_t := [ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |}].




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
      unfold example_program. rewrite (separate6 (BI_const _)).
      eapply bet_composition'.
      { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
      { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. } } 
    { apply Forall2_cons. split;auto. } 
  Qed.

   Lemma module_restrictions_example:
    module_restrictions example_module.
  Proof.
    unfold module_restrictions.
    repeat split; try by exists [] => //=.
  Qed.


  Definition example_instantiate g :=
    [ ID_instantiate [] 0 [0%N] ;
      H_get_global g ].

  Lemma instantiate_example g_ret wret:
    typeof wret = T_i32 ->
    ⊢ {{{ ↪[frame] empty_frame ∗ 
            (N.of_nat g_ret) ↦[wg] {| g_mut := MUT_mut; g_val := wret |} ∗
             (∃ name, 0%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx g_ret) |}) ∗
            0%N ↪[mods] example_module 
      }}}
      ((example_instantiate g_ret,[]) : host_expr)
      {{{  λ v: language.val wasm_host_lang, ⌜v = immHV [xxv 0]⌝ ∨ ⌜v = immHV [xxv 42]⌝ }}} .
  Proof.
    iIntros "%Hret !>" (Φ) "(Hf & Hg & Hexp & Hmod) HΦ".
    iDestruct "Hexp" as (name) "Hexp".
    iApply (instantiation_spec_operational_start_seq with "Hf [Hmod Hexp Hg]").
    2: exact example_module_typing.
    2: exact module_restrictions_example.
    done. iFrame. 
    iSplitL "Hexp". 
    unfold import_resources_host => //.
    instantiate (1 := [_]). iSimpl. iSplit; last done.
    done.
    iSplitL.
    iSplitL.
    iSplitR.
    repeat iSplit. 
    unfold import_func_resources => //=.
    iPureIntro. unfold func_typecheck => //=. constructor => //. 
    iPureIntro. unfold func_domcheck => //=.
    iSplitR.
    repeat iSplit. 
    unfold import_tab_resources => //.
    iPureIntro. unfold tab_typecheck => //=. constructor => //.
    iPureIntro. unfold tab_domcheck => //.
    iSplitR.
    repeat iSplit. 
    unfold import_mem_resources => //.
    iPureIntro. unfold mem_typecheck => //=. constructor => //.
    unfold mem_domcheck => //.
    instantiate (1 := <[ N.of_nat g_ret := _ ]> ∅).
    iSplitL. 
    unfold import_glob_resources. 
    iApply big_sepM_singleton. iFrame. 
    unfold glob_typecheck => //. iPureIntro. split. constructor => //=.
    eexists _,_. 
    split; first by rewrite lookup_insert.
    split; first done. 
    unfold global_agree. simpl. by rewrite Hret.
    unfold glob_domcheck => //=. by set_solver.
    iSplit; iPureIntro.
    unfold module_elem_bound_check_gmap => //. 
    unfold module_data_bound_check_gmap => //. 
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

    iDestruct "Himp" as "[Himp _]".
    iDestruct "Hirwt" as "(Hirwtf & Hirwtm & Hirwtt & Hirwtg)".
    iDestruct "Hirwtg" as "(Hg & %Hgtypecheck & %Hgdomcheck)".
    unfold import_glob_resources.
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hg") as "Hg".
    iClear "Hsing". 
    
    simpl in Hglobinit.
    destruct (inst_globs inst) eqn:Hglobs => //.
    { inversion Hextglob. simpl in H. done. }
    inversion Hextglob. simpl in H. inversion H; subst g. 



    unfold check_start in Hstart. simpl in Hstart. rewrite Hfuncs in Hstart.
    move/eqP in Hstart. inversion Hstart; subst f. 

    iApply wp_lift_wasm.
    rewrite - (app_nil_l [AI_invoke _]).
    iApply (wp_invoke_native with "Hf Hfunc") => //.
    iIntros "!> [Hf Hfunc]".
    iApply (program_spec with "[$Hf $Hg]") => //=.
    by rewrite Hglobs. lia.
    iIntros (w) "(-> & Hf & H)". iDestruct "H" as (gf) "[Hg %Hgf]".
    iSimpl.
    iApply (wp_get_global_host _ _ _ _ [] with "Hg").
    iIntros "!> Hg".
    iApply "HΦ". iSimpl.
    destruct Hgf as [-> | ->]; [by iLeft | by iRight].
  Qed. 

    
    
    
    
End Example01Host.
