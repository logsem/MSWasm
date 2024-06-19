From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_host iris_fundamental_helpers segstack_specs.
Require Export type_checker_reflects_typing.
Require Export segstack_instantiation segstack_pop_robust iris_interp_instance_alloc. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section robust_instantiation.

  Context `{HHB: HandleBytes, !wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, cancelg: cancelG Σ, !cinvG Σ}.

  Set Bullet Behavior "Strict Subproofs".

  (*
Lemma instantiate_stack_spec_robust `{!logrel_na_invs Σ} (s : stuckness) (E: coPset) (exp_addrs: list N) (stack_mod_addr : N) hl (* (hfs : list (hostfuncidx * function_type)) *):
  length exp_addrs = 8 ->
  (* Knowing that we hold the stack module… *)
  stack_mod_addr ↪[mods] stack_module -∗
     (* … and we own the vis of the export targets … *)
   own_vis_pointers exp_addrs -∗
     (* … instantiating the stack-module, yields the following : *)
     WP ((stack_instantiate_para exp_addrs stack_mod_addr, []) : host_expr)
     @ s ; E
             {{ λ v : language.val wasm_host_lang,
                 (* Instantiation succeeds *)
                 ⌜ v = immHV [] ⌝ ∗
                 (* we still own the stack_module *)
                 stack_mod_addr ↪[mods] stack_module ∗ 
                  ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt : nat)
                    (name0 name1 name2 name3 name4 name5 name6 name7 : name)
                    (f0 f1 f2 f3 f4 f5 f6 : list basic_instruction)
                    (i0 : instance)
                    (l0 l1 l2 l3 l4 l5 l6: list value_type)
                    tab 
                    (isStack : handle -> seq.seq i32 -> iPropI Σ),
                    (* Our exports are in the vis stated. Note that everything is 
                       existantially quantified. In fact, all the f_i, i_i and l_i 
                       could be given explicitely, but we quantify them existantially 
                       to show modularity : we do not care what the functions are, 
                       we only care about their spec (see next comment). This also
                       makes this lemma more readable than if we stated explicitely all
                       the codes of the functions *)
                    let inst_vis := (map (λ '(name, idf),
                                                 {| modexp_name := name ;
                                                   modexp_desc := MED_func (Mk_funcidx idf)
                                                 |}) [(name0, idf0) ; (name1, idf1) ;
                                                      (name2, idf2) ; (name3, idf3) ;
                                                     (name4, idf4) ; (name5, idf5) ;
                                                     (name6, idf6) ])
                                        ++ [ {| modexp_name := name7 ;
                                                modexp_desc := MED_table (Mk_tableidx idt) |} ]
                    in let inst_map := (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6])
                                                    [(FC_func_native i0 (Tf [] [T_handle]) l0 f0) ;
                                                     (FC_func_native i0 (Tf [T_handle] [T_i32]) l1 f1) ;
                                                     (FC_func_native i0 (Tf [T_handle] [T_i32]) l2 f2) ;
                                                     (FC_func_native i0 (Tf [T_handle] [T_i32]) l3 f3) ;
                                                     (FC_func_native i0 (Tf [T_handle; T_i32] []) l4 f4) ;
                                                     (FC_func_native i0 (Tf [T_handle; T_i32] []) l5 f5) ;
                                                     (FC_func_native i0 (Tf [T_handle] [T_i32]) l6 f6)])) in
                    (* These two import functions state that all [vis] and [wf] point 
                       to the correct exports/functions, i.e. a client will be able 
                       to successfully import them *)
                       (∃ C, interp_instance C hl i0) ∗
                    import_resources_host exp_addrs inst_vis ∗
                    import_resources_wasm_typecheck_invs inst_vis expts inst_map
                    (<[ N.of_nat idt := tab ]> ∅) 
                    ∅ ∅ ∗
                    ⌜ NoDup (modexp_desc <$> inst_vis) ⌝ ∗
                    (* This is technically redundant, but is commonly used in other modules that import the stack *)
                    ⌜ NoDup [idf0; idf1; idf2; idf3; idf4; idf5; idf6] ⌝ ∗
                    ⌜ length tab.(table_data) >= 1 ⌝ ∗
                    (* And finally we have specs for all our exports : *)
                    (* Spec for new_stack (call 0) *)
                    spec0_new_stack idf0 i0 l0 f0 isStack E ∗
                    (* Spec for is_empty (call 1) *)
                    spec1_is_empty idf1 i0 l1 f1 isStack E ∗
                    (* Spec for is_full (call 2) *)
                    spec2_is_full idf2 i0 l2 f2 isStack E ∗
                    (* Spec for pop (call 3) *)
                    spec3_pop idf3 i0 l3 f3 isStack E ∗
(*                    (∀ hfs, interp_closure hfs (Tf [T_handle] [T_i32]) (FC_func_native i0 (Tf [T_handle] [T_i32]) l3 f3)) ∗  *)
                    (* Spec for push (call 4) *)
                    spec4_push idf4 i0 l4 f4 isStack E ∗
                    (* Spec of stack_map (call 5) *)
                    spec5_stack_map idf5 i0 l5 f5 isStack idt E ∗
                    spec5_stack_map_trap idf5 i0 l5 f5 isStack idt E ∗
                    (* Spec of stack_length (call 6) *)
                    spec6_stack_length idf6 i0 l6 f6 isStack E
             }}.
Proof.
 move => Hexpaddrlen.
  do 9 (destruct exp_addrs => //).
  iIntros "Hmod Hexps".
  iDestruct (own_vis_pointers_nodup with "Hexps") as "%Hnodupexp".
  iApply (weakestpre.wp_strong_mono s _ E with "[Hmod Hexps]") => //.
  iApply (instantiation_spec_operational_no_start with "[Hmod Hexps]"); (try exact module_typing_stack); auto => //.
  - unfold module_restrictions => /=.
    by repeat split => //=; eexists [] => //.
    
  - unfold instantiation_resources_pre.
    iSplitL "Hmod" ; first done.
    unfold instantiation_resources_pre_wasm.
    instantiate (1 := []).
    rewrite irwt_nodup_equiv => /=; last by apply NoDup_nil.
    repeat iSplit => //=; try by (iPureIntro; apply dom_empty).
    + by unfold import_resources_host. 
    + iPureIntro. by unfold module_elem_bound_check_gmap => //=. 
    + iPureIntro. by unfold module_data_bound_check_gmap => //=. 
      
  - iIntros (v) "(-> & Hinst)".
    unfold instantiation_resources_post.
    Opaque list_to_map interp_instance. 
    iDestruct "Hinst" as "(Hmod & _ & (%inst & Himpwasm & Hexphost))".
    iSplitR => //.
    iFrame "Hmod".
    iDestruct "Himpwasm" as (g_inits t_inits m_inits gms wts wms) "(Himpwasm & %Hinst & -> & -> & %Hbound & -> & -> & %Hbound' & %Hginit & -> & Hwasm)".
    destruct Hinst as (Hinsttype & Hpreff & Hpreft & Hprefm & Hprefg & Hstart).
    unfold module_inst_resources_wasm, module_export_resources_host => /=.
    remember inst as inst' in Hnodupexp. destruct inst => /=.
    iDestruct "Hwasm" as "(Hwf & Hwt & Hwm & Hwg)".
    iDestruct (module_inst_resources_func_nodup with "Hwf") as "%Hnodupwf".
    
    unfold module_inst_resources_func, module_inst_resources_tab, module_inst_resources_mem => /=.

    simpl in Hinsttype; subst inst_types.
    
    iDestruct (big_sepL2_length with "Hwf") as "%Hiflen".
    simpl in Hiflen.
    unfold get_import_func_count in * => /=; simpl in Hiflen.

    iDestruct (big_sepL2_length with "Hwt") as "%Hitlen".
    simpl in Hitlen.
    unfold get_import_table_count in * => /=; simpl in Hitlen.
    
    iDestruct (big_sepL2_length with "Hwm") as "%Himlen".
    simpl in Himlen.
    unfold get_import_mem_count in * => /=; simpl in Himlen.

    rewrite -> drop_0 in *.
    do 7 (destruct inst_funcs; first done).
    destruct inst_funcs; last done.
    do 2 (destruct inst_tab => //).
    do 2 (destruct inst_memory => //).

    
    iExists f, f0, f1, f2, f3, f4, f5, t.

    iSimpl in "Hexphost".
    iDestruct "Hexphost" as "(Hexp0 & Hexp1 & Hexp2 & Hexp3 & Hexp4 & Hexp5 & Hexp6 & Hexp7 & _)".
    iDestruct "Hexp0" as (name0) "Hexp0".
    iDestruct "Hexp1" as (name1) "Hexp1".
    iDestruct "Hexp2" as (name2) "Hexp2".
    iDestruct "Hexp3" as (name3) "Hexp3".
    iDestruct "Hexp4" as (name4) "Hexp4".
    iDestruct "Hexp5" as (name5) "Hexp5".
    iDestruct "Hexp6" as (name6) "Hexp6".
    iDestruct "Hexp7" as (name7) "Hexp7".
    iExists name0, name1, name2, name3, name4, name5, name6, name7.
    
    iExists _, _, _, _, _, _, _.
    iExists _.
    iExists _, _, _, _, _, _, _.
    iExists _.

    iExists isStack.

(*    edestruct module_typing_body_eq as [H ?]. module_typing_body
    destruct (H module_typing_stack) as (fts & gts & Hstack).
    clear H. *)

    iAssert ( module_inst_resources_wasm stack_module inst'
              (module_inst_build_tables stack_module inst')
              (module_inst_build_mems stack_module inst')
              (module_inst_global_init
                 (module_inst_build_globals (mod_globals stack_module)) g_inits))%I with "[Hwf Hwt Hwm Hwg]" as "Hwasm".
    { subst inst'. iFrame. }
    
    iMod (interp_instance_alloc with "[] [] [] [] Himpwasm [Hwasm]") as "(Hi & _ & Hinvs1 & Hinvs2)".
    + by apply module_typing_body_stack. 
    + repeat split => //.
    + by destruct Hginit as [? _].
    + done. 
    + done.
    + done. 
    + done.
    + subst inst'. done.
    + iSplitL "Hi".
      { iExists _. iFrame "Hi". done. } 
      
    iSplitL "Hexp0 Hexp1 Hexp2 Hexp3 Hexp4 Hexp5 Hexp6 Hexp7"; first by iFrame => /=.
    

      iDestruct "Hinvs1" as "(Hwf & Hwt & Hwm & Hwg)".
    iDestruct "Hwf" as "(Hf & Hf0 & Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & _)".
    iDestruct "Hwt" as "(Ht & _)".
(*    iDestruct "Hwm" as "(Hm & _)". *)

    
    iSplitL "Hf Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Ht".
    * unfold import_resources_wasm_typecheck_invs.
      iModIntro. iSplitR "Ht". 
      -- apply (NoDup_fmap_2 N.of_nat) in Hnodupwf.
         inversion Hnodupwf as [| ?? Hf Hrestf].
         inversion Hrestf as [| ?? Hf0 Hrestf0].
         inversion Hrestf0 as [| ?? Hf1 Hrestf1].
         inversion Hrestf1 as [| ?? Hf2 Hrestf2].
         inversion Hrestf2 as [| ?? Hf3 Hrestf3].
         inversion Hrestf3 as [| ?? Hf4 _].
        Transparent list_to_map.  iSimpl.
         unfold import_func_wasm_check_invs.
         iSplitL.
         ++ unfold import_func_nainv.
            iApply big_sepM_insert.
            { repeat (rewrite lookup_insert_ne; last by
                        intros Habs; rewrite Habs in Hf;
                      apply Hf; repeat ((by left) + right)).
              done. }
            iFrame "Hf".
            iApply big_sepM_insert.
            { repeat (rewrite lookup_insert_ne; last by 
                 intro Habs; rewrite Habs in Hf0; 
                apply Hf0; repeat ((by left) + right)).
              done. }
            iFrame "Hf0".
            iApply big_sepM_insert.
            { repeat (rewrite lookup_insert_ne; last by
                        intro Habs; rewrite Habs in Hf1; 
                      apply Hf1; repeat ((by left) + right)).
              done. }
            iFrame "Hf1".
            iApply big_sepM_insert.
            { repeat (rewrite lookup_insert_ne; last by
                        intro Habs; rewrite Habs in Hf2; 
                      apply Hf2 ; repeat ((by left) + right)).
              done. }
            iFrame "Hf2".
            iApply big_sepM_insert.
            { repeat (rewrite lookup_insert_ne; last by
                        intro Habs; rewrite Habs in Hf3; 
                      apply Hf3 ; repeat ((by left) + right)).
              done. }
            iFrame "Hf3".
            iApply big_sepM_insert.
            { repeat (rewrite lookup_insert_ne; last by
                        intro Habs; rewrite Habs in Hf4; 
                      apply Hf4; repeat ((by left) + right)).
              done. }
            iFrame "Hf4".
            iApply big_sepM_insert; first done.
            iFrame "Hf5". done.
         ++ iSplitR.
            unfold func_domcheck.
            by repeat rewrite dom_insert.
            iPureIntro.
            unfold func_typecheck.
            constructor => /=.
            { eexists. rewrite lookup_insert. done. }
            constructor => /=.
            { eexists.
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf;
                apply Hf; repeat ((by left) + right).
              rewrite lookup_insert.
              done. } 
            constructor => /=.
            { eexists.
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf;
                apply Hf; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf0;
                apply Hf0; repeat ((by left) + right).
              rewrite lookup_insert.
              done. }
            constructor => /=.
            { eexists.
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf;
                apply Hf; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf0;
                apply Hf0; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf1;
                apply Hf1; repeat ((by left) + right).
              rewrite lookup_insert.
              done.
            }
               constructor => /=.
            { eexists.
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf;
                apply Hf; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf0;
                apply Hf0; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf1;
                apply Hf1; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf2;
                apply Hf2; repeat ((by left) + right).
              rewrite lookup_insert.
              done.
            }
                  constructor => /=.
            { eexists.
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf;
                apply Hf; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf0;
                apply Hf0; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf1;
                apply Hf1; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf2;
                apply Hf2; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf3;
                apply Hf3; repeat ((by left) + right).
              rewrite lookup_insert.
              done.
            }
                       constructor => /=.
            { eexists.
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf;
                apply Hf; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf0;
                apply Hf0; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf1;
                apply Hf1; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf2;
                apply Hf2; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf3;
                apply Hf3; repeat ((by left) + right).
              rewrite lookup_insert_ne;
                last by intro Habs; rewrite Habs in Hf4;
                apply Hf4; repeat ((by left) + right).
              rewrite lookup_insert.
              done.
            }
            constructor => /=.
            done.
            constructor.
      -- iSplitL.
         { iSplitL. unfold import_tab_nainv. iApply big_sepM_insert.
           done. iFrame. done.
           iPureIntro. split. unfold tab_domcheck. rewrite dom_insert. done.
           unfold tab_typecheck. repeat (constructor => //=).
           eexists _,_. rewrite lookup_insert. done. }
         iSplit.
         iSplit. by unfold import_mem_nainv. iPureIntro. split. done.
         repeat (constructor => //).
         iSplit. by unfold import_glob_nainv. iPureIntro. split. done.
         repeat (constructor => //).
    * iSplitR.
      --  iPureIntro.
          eapply (NoDup_fmap_2 (λ x, (MED_func (Mk_funcidx x)))) in Hnodupwf.
          simpl in Hnodupwf.
          rewrite separate7.
          apply NoDup_app; split => //.
          split => //; last by apply NoDup_singleton.
          by set_solver+.
      -- Unshelve.
         2:{ move => x y Heq. by inversion Heq. }
         iSplitR => //.
         
         iSplitR; first by iPureIntro => /=; lia.
         
        
         (* Proving the parametric spec of each function in the post condition *)
         repeat iSplitR.
         ++ iIntros "!>" (fr Φ) "!> (Hf & Hwf) HΦ".
            iApply wp_wand_r.
            iSplitR "HΦ".
            ** rewrite - (app_nil_l [AI_invoke f]).
               iApply (wp_invoke_native with "Hf Hwf") => //.
               iIntros "!> [Hf Hf0]".
               iSimpl.
               iApply (wp_frame_bind with "Hf").
               unfold iris.to_val => //=.
               iIntros "Hf".
               rewrite - (app_nil_l [AI_basic _]).
               iApply (wp_block with "Hf") => //.
               iIntros "!> Hf".
               iApply (wp_label_bind with "[Hf Hf0]") ; last first.
              iPureIntro.
              unfold lfilled, lfill => /=.
              instantiate (5 := []) => /=.
              rewrite app_nil_r.
              done.
              iApply (spec_new_stack with "[Hf]").
              iFrame.
              iPureIntro => //=.
              lia.
              iIntros (w) "H".
              iDestruct "H" as "(H & Hf)" => /=.
              iDestruct "Hf" as (f6) "[Hf %Hf4]".
              iApply (wp_wand_ctx with "[H Hf Hf0]").
              iAssert (⌜const_list (iris.of_val w)⌝%I) as "%Hconstw".
              { by iDestruct "H" as "[-> | (%h & -> & _)]" => //. }
              iApply (wp_val_return with "Hf") => //.
              iIntros "Hf".
              rewrite app_nil_r app_nil_l.
               instantiate (1 :=  (λ w, (⌜w = immV [value_of_handle dummy_handle]⌝
                                       ∨ (∃ h : handle, ⌜w = immV [value_of_handle h]⌝ ∗ ⌜ h <> dummy_handle ⌝ ∗ isStack h [])) ∗
                                        N.of_nat f↦[wf]FC_func_native
                                        {|
                                          inst_types :=
                                            [Tf [] [T_handle]; Tf [T_handle] [T_i32]; 
                                             Tf [T_handle; T_i32] []; Tf [T_i32] [T_i32]];
                                          inst_funcs := [f; f0; f1; f2; f3; f4; f5];
                                          inst_tab := [t];
                                          inst_memory := [];
                                          inst_globs := inst_globs
                                        |} (Tf [] [T_handle]) [T_handle] new_stack ∗  ↪[frame]f6)%I).
              (*              instantiate (1 := (λ v, ((⌜ v = immV _ ⌝)%I ∨ ((∃ k, ⌜ v = immV [value_of_uint k]⌝ ∗ ⌜ (0 <= k <= ffff0000)%N⌝ ∗ isStack k [] m ∗ N.of_nat m↦[wmlength](N.of_nat addr + page_size)%N))) ∗ N.of_nat f↦[wf] _ ∗ ↪[frame] f6 )%I). *)
              iApply wp_value => //. iFrame.
              iDestruct "H" as "[ -> | (%h & -> & H)]"; first by iLeft.
              iDestruct (stack_pure with "H") as "(% & % & %Hvalid & %)".
              iRight. iExists _. iFrame. iSplit => //.
              iIntros "%". subst. done.
              iIntros (v) "(H & Hfunc & Hf)".
              iExists _.
              iFrame.       
              iIntros "Hf".
              iAssert (⌜exists kv, v = immV [kv] ⌝%I) as "%Hv".
              { iDestruct "H" as "[-> | H]" => //; try by iExists _.
                iDestruct "H" as (k) "(-> & ?)".
                by iExists _.
              }
              destruct Hv as [kv ->].
              iApply (wp_frame_value with "Hf") => //.
              destruct kv => //. 
              iNext.
              instantiate (1 := (λ w, ((⌜w = immV [value_of_handle dummy_handle]⌝
                                        ∨ (∃ h : handle, ⌜w = immV [value_of_handle h]⌝ ∗ ⌜ h <> dummy_handle ⌝ ∗ isStack h [])) ∗
                                         N.of_nat f↦[wf]FC_func_native
                                         {|
                                           inst_types :=
                                             [Tf [] [T_handle]; Tf [T_handle] [T_i32]; 
                                              Tf [T_handle; T_i32] []; Tf [T_i32] [T_i32]];
                                           inst_funcs := [f; f0; f1; f2; f3; f4; f5];
                                           inst_tab := [t];
                                           inst_memory := [];
                                           inst_globs := inst_globs
                                         |} (Tf [] [T_handle]) [T_handle] new_stack)%I)).
              iFrame. 
           ** iIntros (w) "[[H Hf0] Hf]".
              iApply "HΦ".
              iFrame.

        ++ iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
           iApply wp_wand_r.
           iSplitR "HΦ".
           ** rewrite (separate1 (AI_handle (_)) _).
              rewrite - (app_nil_r [AI_handle _]).
              iApply (wp_invoke_native with "Hf Hf0") => //.
              iIntros "!> [Hf Hf0]".
              iSimpl.
              iApply (wp_frame_bind with "Hf").
              done. iIntros "Hf".
              rewrite - (app_nil_l [AI_basic _]).
              iApply (wp_block with "Hf") => //.
              iIntros "!> Hf".
              iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
              iPureIntro.
              unfold lfilled, lfill => /=.
              instantiate (5 := []) => /=.
              rewrite app_nil_r.
              done.
              iApply (spec_is_empty with "[Hlen Hf]").
              iFrame.
              repeat iSplit ; iPureIntro => //=.
              (*        lia.
        lia. *)
              iIntros (w) "H".
              iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
              iApply (wp_wand_ctx with "[H Hf Hf0]").
              iApply (wp_val_return with "Hf") => //.
              iIntros "Hf".
              rewrite app_nil_r app_nil_l.
              iApply wp_value => //=.
              unfold IntoVal.
              apply of_to_val => //.
              iFrame.
              instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                              isStack v0 s0 ∗
                                              N.of_nat f0 ↦[wf] _ ∗ ↪[frame] _)%I).
              iSimpl.
              iFrame.
              done.
              iIntros (w) "(-> & H &  Hf0 & Hf)".
              iExists _.
              iFrame.
              iIntros "Hf".
              iSimpl.         
              iApply (wp_frame_value with "Hf") => //.
              iNext.
              instantiate (1 := λ v, ((∃ k, ⌜ v = immV [value_of_int k] ⌝ ∗
                                                    ⌜ k = 1 /\ s0 = [] \/ k = 0 /\ s0 <> [] ⌝) ∗
                                        isStack v0 s0 ∗
                                        N.of_nat f0↦[wf] _)%I).                            
              iSimpl.
              iFrame.
              iExists k.
              done. 
           ** iIntros (w) "[(H & Hs & Hf0) Hf]".
              iDestruct "H" as (k) "%Hk".
              iApply "HΦ".
              iFrame.
              by iExists _.
              
        ++ iIntros "!>" (v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Hlen & %Hdiv & Hlen) HΦ".
           iApply wp_wand_r.
           iSplitR "HΦ".
           ** rewrite (separate1 (AI_handle ( _)) _).
              rewrite - (app_nil_r [AI_handle _]).
              iApply (wp_invoke_native with "Hf Hf0") => //.
              iIntros "!> [Hf Hf0]".
              iSimpl.
              iApply (wp_frame_bind with "Hf").
              done. iIntros "Hf".
              rewrite - (app_nil_l [AI_basic _]).
              iApply (wp_block with "Hf") => //.
              iIntros "!> Hf".
              iApply (wp_label_bind with "[Hlen Hf Hf0]") ; last first.
              iPureIntro.
              unfold lfilled, lfill => /=.
              instantiate (5 := []) => /=.
              rewrite app_nil_r.
              done.
              iApply (spec_is_full with "[Hlen Hf]").
              iFrame.
              repeat iSplit ; iPureIntro => //=.
              iIntros (w) "H".
              iDestruct "H" as (k) "(-> & H & %Hk & Hf)" => /=.
              iApply (wp_wand_ctx with "[H Hf Hf0]").
              iApply (wp_val_return with "Hf") => //.
              iIntros "Hf".
              rewrite app_nil_r app_nil_l.
              iApply wp_value => //=.
              unfold IntoVal.
              apply of_to_val => //.
              iFrame.
              instantiate (1 := λ v, (⌜ v = immV [value_of_int k] ⌝ ∗
                                              isStack v0 s0 ∗
                                              N.of_nat f1↦[wf] _
                                              ∗ ↪[frame] _
                                     )%I).
              iSimpl.
              iFrame.
              done.
              iIntros (w) "(-> & H &  Hf0 & Hf)".
              iExists _.
              iFrame.
              iIntros "Hf".
              iSimpl.         
              iApply (wp_frame_value with "Hf") => //.
              iNext.
              instantiate (1 := λ v, ((∃ (k: Z), ⌜ v = immV [value_of_int k] ⌝ ∗
                                                         ⌜ (k = 1 /\ (N.of_nat (length s0) = two14 - 1)%N) \/ (k = 0 /\ (N.of_nat (length s0) < (two14 - 1))%N) ⌝) ∗
                                        isStack v0 s0  ∗
                                        N.of_nat f1↦[wf] _)%I). 
              iSimpl.
              iFrame.
              iExists k. done.
           ** iIntros (w) "[(H & Hs & Hf0) Hf]".
              iDestruct "H" as (k) "%Hk".
              iApply "HΦ".
              iFrame.
              by iExists _.
        ++ iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & Hs) HΦ". 
           iApply wp_wand_r.
           iSplitR "HΦ".
           ** rewrite (separate1 (AI_handle ( _)) _).
              rewrite - (app_nil_r [AI_handle _]).
              iApply (wp_invoke_native with "Hf Hf0") => //.
              iIntros "!> [Hf Hf0]".
              iSimpl.
              iApply (wp_frame_bind with "Hf").
              done. iIntros "Hf".
              rewrite - (app_nil_l [AI_basic _]).
              iApply (wp_block with "Hf") => //.
              iIntros "!> Hf".
              iApply (wp_label_bind with "[Hs Hf Hf0]") ; last first.
              iPureIntro.
              unfold lfilled, lfill => /=.
              instantiate (5 := []) => /=.
              rewrite app_nil_r.
              done.
              iApply (spec_pop with "[Hs Hf]").
              iFrame.
              repeat iSplit ; iPureIntro => //=.
              lia.
              
              iIntros (w) "H".
              iDestruct "H" as "(-> & Hs & Hf)" => /=.
              iDestruct "Hf" as (f6) "[Hf %Hf4]".
              iApply (wp_wand_ctx with "[Hs Hf Hf0]").
              iApply (wp_val_return with "Hf") => //.
              iIntros "Hf".
              rewrite app_nil_r app_nil_l.
              iApply wp_value => //=.
              unfold IntoVal.
              apply of_to_val => //.
              iFrame.
              instantiate (1 := λ v, (⌜ v = immV [_] ⌝ ∗
                                              isStack v0 s0 ∗
                                              N.of_nat f2↦[wf] _ ∗ ↪[frame] _)%I).
              iSimpl.
              iFrame.
              done.
              iIntros (w) "(-> & H &  Hf0 & Hf)".
              iExists _.
              iFrame.
              iIntros "Hf".
              iSimpl.         
              iApply (wp_frame_value with "Hf") => //.
              iNext.
              instantiate (1 := λ v,  (⌜ v = immV [_] ⌝ ∗
                                               isStack v0 s0 ∗
                                               N.of_nat f2↦[wf] _)%I).
              iSimpl.
              iFrame.
              done.
           ** iIntros (w) "[(-> & Hs & Hf0) Hf]".
              iApply "HΦ".
              by iFrame.
        ++ iIntros "!>" (a v0 s0 vs Φ) "!> (Hf & Hf0 & %H & %Ha & %Hlen & Hs) HΦ".
           iApply wp_wand_r.
           iSplitR "HΦ".
           ** rewrite (separate2 (AI_handle ( _)) _ _).
              rewrite - (app_nil_r [AI_basic _]).
              iApply (wp_invoke_native with "Hf Hf0") => //.
              iIntros "!> [Hf Hf0]".
              iSimpl.
              iApply (wp_frame_bind with "Hf").
              done. iIntros "Hf".
              rewrite - (app_nil_l [AI_basic _]).
              iApply (wp_block with "Hf") => //.
              iIntros "!> Hf".
              iApply (wp_label_bind with "[Hs Hf Hf0]") ; last first.
              iPureIntro.
              unfold lfilled, lfill => /=.
              instantiate (5 := []) => /=.
              rewrite app_nil_r.
              done.
              iApply (spec_push with "[Hs Hf]").
              iFrame.
              repeat iSplit ; iPureIntro => //=.
              lia.
              
              iIntros (w) "(-> & Hs & Hf)".
              iDestruct "Hf" as (f6) "[Hf %Hf4]".
              iApply (wp_wand_ctx with "[Hs Hf Hf0]").
              iApply (wp_val_return with "Hf") => //.
              iIntros "Hf".
              iSimpl.
              iApply wp_value => //=.
              unfold IntoVal.
              apply of_to_val => //.
              iFrame.
              instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                              isStack v0 (a :: s0) ∗
                                              N.of_nat f3↦[wf] _ ∗ ↪[frame] _)%I).
              iSimpl.
              iFrame.
              done.
              iIntros (w) "(-> & H &  Hf0 & Hf)".
              iExists _.
              iFrame.
              iIntros "Hf".
              iSimpl.         
              iApply (wp_frame_value with "Hf") => //.
              iNext.
              instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                              isStack v0 (a :: s0) ∗
                                              N.of_nat f3↦[wf] _)%I).
              iSimpl.
              iFrame.
              iFrame.
              done. 
           ** iIntros (w) "[(-> & Hs & Hf0) Hf]".
              iApply "HΦ".
              by iFrame.
        ++ iIntros "!>" (f6 fi v0 s0 a cl Φ Ψ all Ξ)
             "!> (Hf & Hall & Hf0 & Hs & HΦ & Htab & Hcl & %Hclt & #Hspec) HΞ".
           iApply wp_wand_r.
           iSplitR "HΞ".
           ** rewrite (separate2 (AI_handle (_)) _ _).
              rewrite - (app_nil_r [AI_basic _]).
              iApply (wp_invoke_native with "Hf Hf0") => //.
              iIntros "!> [Hf Hf0]".
              iSimpl.
              iApply (wp_frame_bind with "Hf").
              done. iIntros "Hf".
              rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
              iApply (wp_block with "Hf") => //.
              iIntros "!> Hf".
              iApply (wp_label_bind with "[Hs Hf Hf0 HΦ Htab Hcl Hall]") ; last first.
              iPureIntro.
              unfold lfilled, lfill => /=.
              instantiate (5 := []) => /=.
              rewrite app_nil_r.
              done.
              iApply (spec_stack_map with "[Hs Hf HΦ Hcl Htab Hall]").        
              iFrame.
              repeat iSplit ; try iPureIntro => //=.
              lia.
              iExact "Hspec".
              iIntros (w) "(-> & Hs & Hf & Hall & Ht & Ha)".
              iDestruct "Hf" as (f7) "[Hf %Hf4]".
              iApply (wp_wand_ctx with "[Hs Hf Hf0]").
              iApply (wp_val_return with "Hf") => //.
              iIntros "Hf".
              iSimpl.
              iApply wp_value => //=.
              unfold IntoVal.
              apply of_to_val => //.
              iFrame.
              instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗
                                              ( ∃ s', isStack v0 s' ∗ stackAll2 s0 s' Ψ) ∗
                                              N.of_nat f4↦[wf] _ ∗ ↪[frame] _ )%I).
              iSimpl.
              iFrame.
              done.
              iIntros (w) "(-> & H &  Hf0 & Hf)".
              iExists _.
              iFrame.
              iIntros "Hf".
              iSimpl.         
              iApply (wp_frame_value with "Hf") => //.
              iNext.
              instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗ (∃ all', interp_allocator all') ∗
                                              ( ∃ s', isStack v0 s' ∗ stackAll2 s0 s' Ψ) ∗
                                              N.of_nat t↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m fi)]Some a ∗
                                              N.of_nat a↦[wf]cl ∗
                                              N.of_nat f4↦[wf] _)%I).
              iSimpl.
              iFrame.
              iFrame.
              done. 
           ** iIntros (w) "[(-> & Hall & Hs & Ht & Ha & Hf0) Hf]".
              iApply "HΞ".
              by iFrame.
        (* Trap spec *)  
        ++ iIntros "!>" (f6 fi v0 s0 a cl γ Φ Ψ all Hsub Hsub2 Ξ)
             "!> (#Hf6 & Hs & HΦ & #Htab & #Hcl & Hown & Hf0 & Hall) HΞ".
           iApply wp_wand_r.
           iSplitR "HΞ".
           ** iApply fupd_wp.
              iMod (na_inv_acc with "Hf6 Hown") as "(>Hf5 & Hown & Hcls0)".
              done. solve_ndisj.
              iModIntro.
              rewrite (separate2 (AI_handle ( _)) _ _).
              rewrite - (app_nil_r [AI_basic _]).
              iApply (wp_invoke_native with "Hf0 Hf5") => //.
              iIntros "!> [Hf Hf0]".
              iSimpl.
              
              iApply fupd_wp.
              iMod ("Hcls0" with "[$Hf0 $Hown]") as "Hown".
              iModIntro. 

              iApply (wp_frame_bind with "Hf").
              done. iIntros "Hf".
              rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
              iApply (wp_block with "Hf") => //.
              iIntros "!> Hf".
              iApply (wp_label_bind with "[Hs Hf HΦ Htab Hown Hall]") ; last first.
              iPureIntro.
              unfold lfilled, lfill => /=.
              instantiate (5 := []) => /=.
              rewrite app_nil_r.
              done.
              iApply (spec_stack_map_trap _ _ v0 s0 _ _ _ Φ Ψ
                       with "[Hs Hf HΦ Htab Hown Hall]");[apply Hsub|..].
              iFrame "∗ #".
              repeat iSplit ; try iPureIntro => //=.
              lia. iFrame "Hcl".
              iIntros (w) "([-> | Hs] & Hf & Hall)";
                iDestruct "Hf" as (f7) "[Hf [Hown %Hf4]]".
              --- iApply (wp_wand_ctx with "[Hf]").
                 iSimpl. take_drop_app_rewrite_twice 0 0.
                 iApply wp_trap_ctx;auto.
                 iIntros (v1) "[-> Hf]".
                 iExists _. iFrame. iIntros "Hf".
                 iApply (wp_frame_trap with "Hf").
                 instantiate (1:=(λ v, (⌜v = trapV⌝ ∨ ⌜ v = immV [] ⌝ ∗ _) ∗ (∃ all', interp_allocator all') ∗ na_own logrel_nais ⊤)%I). iNext. iFrame.  eauto.
              --- iDestruct "Hs" as "[-> Hs]".
                 iApply (wp_wand_ctx with "[Hs Hf]").
                 iApply (wp_val_return with "Hf") => //.
                 iIntros "Hf".
                 iSimpl.
                 iApply wp_value => //=.
                 unfold IntoVal.
                 apply of_to_val => //.
                 iFrame.
                 instantiate (1 :=  (λ v, ⌜ v = immV [] ⌝ ∗
                                                  ( ∃ s', isStack v0 s' ∗ stackAll2 s0 s' Ψ) ∗
                                                  (* N.of_nat f4↦[wf] _ ∗ *) ↪[frame] _)%I).
                 iSimpl.
                 iFrame.
                 done.
                 iIntros (w) "(-> & H & Hf)".
                 iExists _.
                 iFrame.
                 iIntros "Hf".
                 iSimpl.         
                 iApply (wp_frame_value with "Hf") => //.
                 iNext. iRight.
                 instantiate (1 :=  (( ∃ s', isStack v0 s' ∗ stackAll2 s0 s' Ψ) (* ∗
                                       N.of_nat f4↦[wf] _ *) )%I).
                 iSimpl. iSplitR;[done|].
                 iFrame. 

           ** iSimpl.
              iIntros (w) "[([-> | (-> & Hs)] & Hall & Hown) Hf]".
              all: try iApply "HΞ";iFrame. by iLeft.
              iRight. iSplit;auto. 
        ++ (* length spec *)
          iIntros "!>" (v0 s0 f6 len Φ) "!> (Hf & Hf0 & %Hret & Hs) HΦ".
          iApply wp_wand_r.
          iSplitR "HΦ".
          ** rewrite (separate1 (AI_handle (_)) _).
             rewrite - (app_nil_r [AI_handle _]).
             iApply (wp_invoke_native with "Hf Hf0") => //.
             iIntros "!> [Hf Hf0]".
             iSimpl.
             iApply (wp_frame_bind with "Hf").
             done. iIntros "Hf".
             rewrite - (app_nil_l [AI_basic _]).
             iApply (wp_block with "Hf") => //.
             iIntros "!> Hf".
             iApply (wp_label_bind with "[Hs Hf Hf0]") ; last first.
             iPureIntro.
             unfold lfilled, lfill => /=.
             instantiate (5 := []) => /=.
             rewrite app_nil_r.
             done.
             iApply (spec_stack_length with "[Hs Hf]").
             iFrame.
             repeat iSplit ; iPureIntro => //=.
             iIntros (w) "(-> & Hs & Hf)".
             iApply (wp_wand_ctx with "[Hs Hf Hf0]").
             iApply (wp_val_return with "Hf") => //.
             iIntros "Hf".
             rewrite app_nil_r app_nil_l.
             iApply wp_value => //=.
             unfold IntoVal.
             apply of_to_val => //.
             iFrame.
             instantiate (1 := λ v, (⌜ v = immV _ ⌝ ∗
                                             isStack v0 s0 ∗
                                             N.of_nat f5 ↦[wf] _ ∗ ↪[frame] _)%I).
             iSimpl.
             iFrame.
             done.
             iIntros (w) "(-> & H &  Hf0 & Hf)".
             iExists _.
             iFrame.
             iIntros "Hf".
             iSimpl.         
             iApply (wp_frame_value with "Hf") => //.
             iNext.
             instantiate (1 := λ v, ( ⌜ v = immV [value_of_uint _] ⌝ ∗ isStack v0 s0 ∗ N.of_nat f5↦[wf] _)%I).
             iSimpl.
             iFrame.
             done. 
          ** iIntros (w) "[(-> & Hs & Hf0) Hf]".
             iApply "HΦ".
             by iFrame.
    + 
Qed. *)
  
End robust_instantiation.
