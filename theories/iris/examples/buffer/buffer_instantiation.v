From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux.
Require Export iris_host iris_rules iris_fundamental iris_wp iris_interp_instance_alloc.
Require Export iris_example_helper proofmode.
Require Export datatypes operations properties opsem.
Require Export typing type_checker_reflects_typing.
Require Export buffer_code.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.


Section Buffer_instantiation. 
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


    Definition buffer_module :=
    {| mod_types := [Tf [] []; Tf [T_handle] []];
       mod_funcs :=  [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_handle; T_handle] ;
          modfunc_body := buffer_program
        |} ] ;
      mod_tables := [];
      mod_mems := [];
      mod_globals := [ ];
      mod_elem := [];
      mod_data := [];
      mod_start := Some {| modstart_func := Mk_funcidx 1 |};
      mod_imports := [  {| imp_module := list_byte_of_string "adversary_module";
                          imp_name := list_byte_of_string "adversary_function";
                          imp_desc := ID_func 1 |};
                        {| imp_module := list_byte_of_string "Ret";
                         imp_name := list_byte_of_string "ret_glob";
                           imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |}
      ];
      mod_exports := []
    |}.

  Definition buffer_func_impts : seq.seq extern_t := [ET_func (Tf [T_handle] []) ].
  Definition buffer_glob_impts : seq.seq extern_t :=
    [ ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |}
    ].


 Ltac unfold_irwt_all :=
    unfold import_func_wasm_check;
    unfold import_tab_wasm_check;
    unfold import_mem_wasm_check;
    unfold import_glob_wasm_check;
    unfold import_func_resources;
    unfold import_tab_resources;
    unfold import_mem_resources;
    unfold import_glob_resources;
    unfold func_typecheck;
    unfold tab_typecheck;
    unfold mem_typecheck;
    unfold glob_typecheck;
    unfold func_domcheck;
    unfold tab_domcheck;
    unfold mem_domcheck;
    unfold glob_domcheck.

  Ltac type_next :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(list.take_drop (length e - 1) e);simpl take; simpl drop;
      eapply bet_composition;[|econstructor;eauto];simpl
  end.


  
  Lemma buffer_module_typing :
    module_typing buffer_module (buffer_func_impts ++ buffer_glob_impts)
      []. 
  Proof. 
    exists [Tf [] []], [ ]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      unfold buffer_program. rewrite (separate9 (BI_const _)).
      eapply bet_composition'.
      { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
      { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
    } 
    { apply Forall2_cons. split;auto.
      apply Forall2_cons. split;auto. } 
  Qed.

   Lemma module_restrictions_buffer:
    module_restrictions buffer_module.
  Proof.
    unfold module_restrictions.
    repeat split; try by exists [] => //=.
  Qed.


  Definition buffer_instantiate g :=
    [ ID_instantiate [0%N] 0 [];
      ID_instantiate [] 1 [0%N; 1%N] ;
      H_get_global g ].

  Lemma instantiate_buffer adv_module g_ret wret all:
     module_typing adv_module [] (buffer_func_impts) -> (* we assume the adversary module has an export of the type (handle) → () as well as one global variable containing a dummy handle *)
    mod_start adv_module = None -> (* that it does not have a start function *)
    module_restrictions adv_module -> (* that it adheres to the module restrictions (i.e. only constant initializers for globals) *)
    module_elem_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a table, there cannot be more initializers that its size *)
    module_data_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a memory, there cannot be more initializers that its size *)
    typeof wret = T_i32 -> (* the imported return global has type i32 *)
    ⊢ {{{ ↪[frame] empty_frame ∗ interp_allocator all ∗ 
            (N.of_nat g_ret) ↦[wg] {| g_mut := MUT_mut; g_val := wret |} ∗
            (∃ vs, 0%N ↪[vis] vs) ∗
            (∃ name, 1%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx g_ret) |}) ∗
            1%N ↪[mods] buffer_module ∗
            0%N ↪[mods] adv_module ∗
          na_own logrel_nais ⊤ 
      }}}
      ((buffer_instantiate g_ret,[]) : host_expr)
      {{{  λ v: language.val wasm_host_lang, ⌜ v = trapHV ⌝ ∨ ⌜v = immHV [xxv 42] ⌝ }}} .
  Proof.
    iIntros (Hadvtype Hadvstart Hadvrestr Hadvelem Hadvdata Hwret).
    iIntros "!>" (Φ) "(Hf & Hall & Hg & Hexp0 & Hexp1 & Hmod & Hmodadv & Hown) HΦ".
    iDestruct "Hexp1" as (name) "Hexp1".
    iDestruct "Hexp0" as (vs) "Hexp0".
    assert (exists exp_name ft, mod_exports adv_module = [ {| modexp_name := exp_name ; modexp_desc := MED_func ft |}  ]) as (exp_name & ft & Hexp). 
    { destruct Hadvtype as (fts & gts & Hadvtype).
      destruct adv_module; simpl in *.
      destruct Hadvtype as (_&_&_&_&_&_&_&_&Hadvtype).
      apply Forall2_length in Hadvtype as Hlen. 
      simpl in Hlen.
      destruct mod_exports eqn:Hexps => //. destruct l => //. 
      apply Forall2_cons in Hadvtype as [Hadvtype1 Hadvtype].
      unfold module_export_typing in Hadvtype1.
      destruct m => //. simpl in Hadvtype1. 
      destruct modexp_desc as [x|x|x|x]; destruct x => //.
      eexists _,_. done. }
    iApply (wp_seq_host_nostart NotStuck with "[] Hmodadv [Hexp0]") => //.
    2:{ iIntros "Hmodadv".
        iApply weakestpre.wp_mono.
        2: iApply instantiation_spec_operational_no_start => //.
        iIntros (w) "[Heq [$ H]]".
        iCombine "Heq H" as "H".
        iExact "H".

        unfold instantiation_resources_pre. iFrame. 
        iSplit => //. unfold import_resources_host => //.
        iSplit => //. unfold instantiation_resources_pre_wasm => //.
        iSplit => //. unfold import_resources_wasm_typecheck => //.
        repeat iSplit => //.
        unfold import_func_resources => //.
        unfold func_typecheck => //.
        unfold import_tab_resources => //.
        unfold tab_typecheck => //.
        unfold import_mem_resources => //.
        unfold mem_typecheck => //.
        unfold import_glob_resources => //.
        unfold glob_typecheck => //.
        iSplit => //. unfold export_ownership_host.
        iSimpl. iSplitL "Hexp0" => //. iExists _. iFrame.
        by rewrite Hexp. 
    }
    by iIntros "[% _]".
    iIntros (w) "(-> & _ & %advinst & Hres & Hexp0) Hmod0".
    unfold module_export_resources_host. rewrite Hexp.
    iSimpl in "Hexp0".
    iDestruct "Hexp0" as "([%name0 Hexp0] & _)".
    destruct ft. 
    unfold instantiation_resources_post_wasm.
    iDestruct "Hres" as (??????) "(Hadvirwt & %Hadvtypr & %Hadvtabinits & %Hadvwts'0 & %Hadvbounds_elem & %Hadvmem_init & %Hadvwsms0' & %Hadvbounds_data & %Hadvglobsr & %Hadvglobinit & Hadvfuncs & Hadvtabs & Hadvmems & Hadvglobs)".
    iDestruct "Hadvirwt" as "(Hadvirwtf & Hadvirwtt & Hadvirwtm & Hadvirwtg)".
    iDestruct "Hadvirwtt" as "(Hadvimpt & %Hadvttype & %Hadvtdom)".
    iDestruct "Hadvirwtm" as "(Hadvimpm & %Hadvmtype & %Hadvmdom)".
    unfold tab_domcheck in Hadvtdom.
    unfold mem_domcheck in Hadvmdom.
    simpl in Hadvtdom. simpl in Hadvmdom.
    apply dom_empty_inv in Hadvtdom.
    apply dom_empty_inv in Hadvmdom.
    subst wts' wms'. 
    iDestruct (big_sepL2_length with "Hadvfuncs") as "%Hlenadvfuncs".
    iDestruct (big_sepL2_length with "Hadvglobs") as "%Hlenadvglobs". 
    unfold get_import_func_count in Hlenadvfuncs.
    unfold get_import_global_count in Hlenadvglobs. 

    destruct Hadvtype as (fts & gts & Hadvtype).
    assert (Hadvtype' := Hadvtype). 
    remember adv_module as advm.
    destruct adv_module.
    rewrite Heqadvm in Hadvtype.
    simpl in Hadvtype.
    destruct Hadvtype as (Himpf & _ & _ & Himpg & _ & _ & _ & Hadvimps & Hadvexps).
    inversion Hadvimps. subst mod_imports. rewrite Heqadvm in Hlenadvfuncs.
    rewrite Heqadvm in Hlenadvglobs. 
    simpl in Hlenadvfuncs. simpl in Hlenadvglobs.
    rewrite drop_0 in Hlenadvfuncs.
    rewrite drop_0 in Hlenadvglobs. 
    rewrite Heqadvm in Hexp; simpl in Hexp.
    subst mod_exports.
    apply Forall2_cons in Hadvexps as [Hadvexpf Hadvexps].
    unfold module_export_typing in Hadvexpf.
    simpl in Hadvexpf. 
    apply andb_true_iff in Hadvexpf as [Hn Hnth].
    destruct (nth_error fts n) eqn:Hfts => //.
    apply b2p in Hnth. subst f.
    rewrite Heqadvm. 
    unfold get_import_func_count, get_import_global_count, get_import_mem_count, get_import_table_count. simpl.
    repeat rewrite drop_0.
    rewrite nth_error_lookup in Hfts. 
    eapply Forall2_lookup_r in Himpf as (mf & Hmf & Htypf); last exact Hfts.
    destruct mf; simpl in Htypf. 
    destruct modfunc_type. 
    destruct Htypf as (Hlef & Hnthf & Htypef).
    unfold module_inst_resources_func.

    apply lookup_lt_Some in Hmf as Hlenf.
    rewrite Hlenadvfuncs in Hlenf.

    apply lookup_lt_is_Some in Hlenf as [? Hinstfunc]. 
    iDestruct (big_sepL2_lookup_acc with "Hadvfuncs") as "[Hfunc Hrestorefuncs]".
    done. done. iSimpl in "Hfunc".


    apply b2p in Hnthf.

    destruct Hadvtypr as (Hadvtypes & Hadvtypfunc & Hadvtyptab & Hadvtypmem & Hadvtypglob & Hadvtypstart).
    rewrite Heqadvm in Hadvtypes; simpl in Hadvtypes. 
    rewrite - Hadvtypes in Hnthf.
    rewrite Hnthf.

    
    rewrite nth_lookup. rewrite Hinstfunc. 
        
    iApply (instantiation_spec_operational_start_seq with "Hf [Hmod Hexp0 Hexp1 Hg Hfunc]").
    2: exact buffer_module_typing.
    2: exact module_restrictions_buffer.
    done. iFrame. 
    iSplitR "Hg Hfunc". 
    unfold import_resources_host => //.
    instantiate (1 := [_;_]). iSimpl. iFrame. 
    iSplitL.
    iSplitL.
    iSplitL "Hfunc".
    iSplitL.
    
    unfold import_func_resources.
    instantiate (1 := <[ N.of_nat x := _ ]> ∅).
    iApply big_sepM_singleton. iFrame. 
    iPureIntro. split. unfold func_typecheck => //=. constructor => //=.
    eexists. 
    rewrite lookup_insert. split => //. constructor => //=.
    unfold func_domcheck => //=. 
    simpl. set_solver. 
    iSplitR.
    repeat iSplit. 
    unfold import_tab_resources => //.
    iPureIntro. unfold tab_typecheck => //=. constructor => //. 
    constructor => //. 
    iPureIntro. unfold tab_domcheck => //.
    iSplitR.
    repeat iSplit. 
    unfold import_mem_resources => //.
    iPureIntro. unfold mem_typecheck => //=. do 3 constructor => //.
    unfold mem_domcheck => //.
    instantiate (1 := <[ N.of_nat g_ret := _ ]> ∅).
    iSplitL. 
    unfold import_glob_resources.
    iApply big_sepM_singleton. iFrame. 
    unfold glob_typecheck => //. iPureIntro. split. constructor => //=.
    constructor => //=. 
    eexists _,_. 
    split; first by rewrite lookup_insert.
    split; first done. 
    unfold global_agree. simpl. by rewrite Hwret.
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
    destruct (inst_funcs inst) eqn:Hfuncs => //.
    destruct l => //. destruct l => //.
    inversion Hextfunc. unfold ext_func_addrs in H.
    simpl in H.
    inversion H; subst x x0. 
    iDestruct "Hfuncs" as "(Hfunc & _)". rewrite Hinst_types. iSimpl in "Hfunc".
    

    
    

    iDestruct "Himp" as "(Himp0 & Himp1 & _)".
    iDestruct "Hirwt" as "(Hirwtf & Hirwtm & Hirwtt & Hirwtg)".

    iDestruct "Hirwtf" as "(Hfs & %Hftypecheck & %Hfdomcheck)".
    unfold import_func_resources.
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hfs") as "Hfadv".
    iClear "Hsing".

     iDestruct "Hirwtg" as "(Hg & %Hgtypecheck & %Hgdomcheck)".
    unfold import_glob_resources.
                     
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hg") as "Hg".
    iClear "Hsing". 
    
    simpl in Hglobinit.


    iDestruct ("Hrestorefuncs" with "Hfadv") as "Hadvfuncs".
    
    iApply weakestpre.fupd_wp.
    iMod (interp_instance_alloc [] ⊤ with "[] [] [] [] [] [Hadvfuncs Hadvtabs Hadvmems Hadvglobs]") as "(#Hi & (#Hiresf & _ & _ & #Hiresg) & _)".
    apply Hadvtype'.
    repeat split => //=.
    by rewrite Heqadvm.
    destruct Hadvglobsr as [??] => //=. 
    by instantiate (1 := ∅).
    by instantiate (1 := ∅).
    by instantiate (1 := ∅).
    by instantiate (1 := ∅).
    unfold import_resources_wasm_typecheck => //=.
    unfold_irwt_all.
    rewrite module_import_init_tabs_dom.
    rewrite module_import_init_mems_dom. 
    repeat iSplitL => //=.
    rewrite Hadvtdom. done.
    rewrite Hadvmdom. done.
    rewrite Hadvtabinits.
    rewrite Hadvmem_init.
    rewrite Hadvglobinit.
    unfold module_inst_resources_wasm.
    unfold get_import_func_count.
    unfold get_import_table_count.
    unfold get_import_mem_count.
    unfold get_import_global_count.
    rewrite Heqadvm. iSimpl. iFrame. 
    
   
    iDestruct (big_sepL2_lookup with "Hiresf") as "Ha".
    by rewrite Heqadvm. by rewrite Heqadvm.

    destruct (inst_globs inst) eqn:Hglobs => //.
    { inversion Hextglob. done. }
    inversion Hextglob. inversion H0; subst g.



    unfold check_start in Hstart. simpl in Hstart. rewrite Hfuncs in Hstart.
    move/eqP in Hstart. inversion Hstart; subst f0.

   

    
    iModIntro. 

    iApply wp_lift_wasm.
    rewrite - (app_nil_l [AI_invoke _]).
    
    iApply (wp_invoke_native with "Hf Hfunc") => //.
    iIntros "!> [Hf Hfunc]".
    iSimpl in "Ha". rewrite Hnthf.

    iApply (wp_frame_bind with "Hf"); first done.
    iIntros "Hf". 
    rewrite - (app_nil_l [AI_basic _]).
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind. done. 
    
    iSimpl.
    
    iApply (buffer_spec with "[$Hf $Hg $Hall Hown $Hi $Ha]") => //=; try by rewrite Hglobs.
    by rewrite Hfuncs. lia.
    rewrite Heqadvm.
    exact Htypef.
    iIntros (w) "[[%f0 Hf] [-> | (-> & Hown & Hall & Hgret)]]".
    { iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx.
      iApply (wp_wand with "[Hf]"). 
      iApply (wp_label_trap with "Hf"). done.
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]".
      iExists _. iFrame. iIntros "Hf".
      iApply (wp_wand with "[Hf]"). iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]".
      iApply wp_get_global_trap_host.
      iApply "HΦ". iLeft. done. }
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
    
    iApply (wp_get_global_host _ _ _ _ [] with "Hgret").
    iIntros "!> Hg".
    iApply "HΦ". iSimpl. iRight. 
    done.
  Qed. 

End Buffer_instantiation.
