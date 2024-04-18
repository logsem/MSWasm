From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export segstack_instantiation_robust iris_interp_instance_alloc.
Require Export iris_example_helper.
Require Export type_checker_reflects_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Section Client.
  Context `{HHB: HandleBytes, !wasmG Σ, !hvisG Σ, !hmsG Σ}.

  Definition main :=
    [ BI_call 0 ;
      BI_tee_local 0 ;
      BI_isdummy ;
      (* If new_stack failed, set global v0 to -1 and return *)
      BI_if (Tf [] []) [BI_unreachable] [] ;
      BI_get_local 0 ;
      i32const 4 ;
      BI_call 4 ;
      BI_get_local 0 ;
      i32const 2 ;
      BI_call 4 ;
      BI_get_local 0 ;
      i32const 0 ;
      BI_call 5 ;
      BI_get_local 0 ;
      BI_call 6 ;
      BI_set_global 0
    ].

  Definition client_module :=
    {|
      mod_types := [ Tf [] [] ; Tf [] [T_i32] ; Tf [T_handle] [T_i32] ;
                     Tf [T_handle ; T_i32] [] ; Tf [] [T_handle] ;
                     Tf [T_i32] [T_i32]
      ] ;
      mod_funcs :=
      [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_handle] ;
          modfunc_body := main
        |} ] ;
      mod_tables := [] ; 
      mod_mems := [] ;
      mod_globals := [] ;
      mod_elem := [ {| modelem_table := Mk_tableidx 0 ;
                      modelem_offset := [i32const 0] ;
                      modelem_init := [Mk_funcidx 7] |} ] ;
      mod_data := [] ;
      mod_start := Some {| modstart_func := Mk_funcidx 8 |} ;
      mod_imports := [
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "new_stack" ;
          imp_desc := ID_func 4
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "is_empty" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "is_full" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "pop" ;
          imp_desc := ID_func 2
        |} ;
        {|
          imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "push" ;
          imp_desc := ID_func 3
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "stack_map" ;
          imp_desc := ID_func 3
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "stack_length" ;
          imp_desc := ID_func 2
        |} ;
        {| imp_module := list_byte_of_string "Stack" ;
          imp_name := list_byte_of_string "table" ;
          imp_desc := ID_table {| tt_limits := {| lim_min := 1%N ; lim_max := None |} ;
                                 tt_elem_type := ELT_funcref |}
        |} ;
        {| imp_module := list_byte_of_string "Adv";
          imp_name := list_byte_of_string "adv_call";
          imp_desc := ID_func 5
        |} ;
        {| imp_module := list_byte_of_string "Ret";
          imp_name := list_byte_of_string "ret_glob";
          imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |}
      ] ;
      mod_exports := []
    |}.

  Definition client_func_impts : seq.seq extern_t := expts ++ [ET_func (Tf [T_i32] [T_i32])].
  Definition client_glob_impts : seq.seq extern_t := [ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |} ].

  Lemma client_module_typing :
    module_typing client_module (client_func_impts ++ client_glob_impts) [].
  Proof.
    exists [Tf [] []],[]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      { unfold main.
        rewrite (separate8 (BI_call _ )).
        eapply bet_composition'.
        { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
        { apply/b_e_type_checker_reflects_typing => /=; by apply/eqP. }
      }
    }
    { apply Forall_cons. split;auto. cbn. repeat split;auto. constructor. }
    { repeat (apply Forall2_cons;split;auto). }
  Qed.

End Client.

Ltac take_drop_app_rewrite n :=
  match goal with
  | |- context [ WP ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ CTX _; _  {{ _, _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ WP ?e @ _; _ FRAME _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  end.
  
Ltac take_drop_app_rewrite_twice n m :=
  take_drop_app_rewrite n;
  match goal with
  | |- context [ WP _ ++ ?e @ _; _ CTX _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  | |- context [ WP _ ++ ?e @ _; _ {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  end.


Section Client_main.

  Context `{HHB: HandleBytes, !wasmG Σ, !logrel_na_invs Σ, cancelg : cancelG Σ, !cinvG Σ }.

  Lemma main_spec C k idt locs es f a i idf0 l0 f0 idf4 l4 f4 idf5 l5 f5 idf6 l6 f6
        istack isStack (* newStackAddrIs *) stacktab all :
    (tc_label C) = [] ∧ (tc_return C) = None ->

    f.(f_inst).(inst_globs) !! 0 = Some k ->
    f.(f_inst).(inst_tab) !! 0 = Some idt ->
    inst_funcs (f_inst f) !! 0 = Some idf0 ->
    inst_funcs (f_inst f) !! 4 = Some idf4 ->
    inst_funcs (f_inst f) !! 5 = Some idf5 ->
    inst_funcs (f_inst f) !! 6 = Some idf6 ->
    f.(f_locs) = n_zeros [T_handle] ->
    length (table_data stacktab) >= 1 ->
    
    be_typing (upd_local_label_return C (T_i32 :: locs) [[T_i32]] (Some [T_i32])) es (Tf [] [T_i32]) ->
    
    ⊢ {{{ ↪[frame] f ∗ interp_allocator all 
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_i32] [T_i32]) locs es))
         ∗ interp_instance C [] i
         ∗ (∃ gv, N.of_nat k ↦[wg] {| g_mut := MUT_mut; g_val := gv |})
         (* new stack *)
         ∗  na_inv logrel_nais (wfN (N.of_nat idf0))
         (N.of_nat idf0 ↦[wf]FC_func_native istack (Tf [] [T_handle]) l0 f0)
         ∗ spec0_new_stack idf0 istack l0 f0 isStack (* newStackAddrIs *) ⊤
         (* push *)
         ∗  na_inv logrel_nais (wfN (N.of_nat idf4))
         (N.of_nat idf4↦[wf]FC_func_native istack (Tf [T_handle; T_i32] []) l4 f4)
         ∗ spec4_push idf4 istack l4 f4 isStack ⊤
         (* map *)
          ∗ na_inv logrel_nais (wfN (N.of_nat idf5))
          (N.of_nat idf5↦[wf]FC_func_native istack (Tf [T_handle; T_i32] []) l5 f5)
         ∗ spec5_stack_map_trap idf5 istack l5 f5 isStack idt ⊤
         (* length *)
         ∗  na_inv logrel_nais (wfN (N.of_nat idf6))
         (N.of_nat idf6↦[wf]FC_func_native istack (Tf [T_handle] [T_i32]) l6 f6)
         ∗ spec6_stack_length idf6 istack l6 f6 isStack ⊤
         (* table *)
         ∗ N.of_nat idt↦[wtblock]table_init_replace_single stacktab (nat_of_int (Wasm_int.Int32.repr 0)) [Some a]
         (* new stack predicate *)
(*         ∗ newStackAddrIs 0 *)
      }}}
      to_e_list main
      {{{ w, (⌜w = trapV⌝ ∨ (⌜w = immV []⌝ ∗ (N.of_nat k) ↦[wg] {| g_mut := MUT_mut; g_val := xxv 2 |}
                                                               ∗ na_own logrel_nais ⊤))
               ∗ (∃ f', ↪[frame] f' ∗ ∃ r, ⌜f' = Build_frame (set_nth r (f_locs f) 0 r) (f_inst f)⌝) ∗ (∃ all', interp_allocator all') }}}.
  Proof.
    iIntros (HC Hglob Htab Hidf0 Hidf4 Hidf5 Hidf6 Hflocs Htablen Htyp Φ)
            "!> (Hf & Hall & Hown & #Hadv & #Hi & Hg & #Hidf0 & #Hnewstack & 
                 #Hidf4 & #Hpush & #Hidf5 & #Hmap & #Hidf6 & #Hstacklen & Hidt) HΦ".

    iApply fupd_wp.
    iMod (na_inv_acc with "Hidf0 Hown") as "(>Hf0 & Hown & Hcls0)"; [by solve_ndisj| by solve_ndisj|..].
    iModIntro.
    
    
    take_drop_app_rewrite 1.
    iApply wp_seq.
    (* new stack *)
    iSplitR;[|iSplitL "Hf0 Hf"];cycle 1.
    { iApply (wp_call with "Hf");[apply Hidf0|].
      iNext. iIntros "Hf".
      iApply ("Hnewstack" with "[$Hf $Hf0]").

      iIntros (v) "[Hres [Hidf Hf]]".
      instantiate (1:= (λ vs, _ ∗ ↪[frame] _)%I). iFrame "Hf".
      iCombine "Hres" "Hidf" as "Hres". iExact "Hres". }
    2: { iIntros "[[[% | Hcontr] _] _]". done. iDestruct "Hcontr" as (? Hcontr) "_";done. }
    iIntros (w) "[[Hres Hidf] Hf]".

    iApply fupd_wp.
    iMod ("Hcls0" with "[$Hidf $Hown]") as "Hown".
    iModIntro. 

    unfold i32const.
    iAssert (⌜∃ h, w = immV [VAL_handle h]⌝)%I as %Hw.
    { iDestruct "Hres" as "[->|Hres]";eauto. iDestruct "Hres" as (?) "[-> _]". eauto. }
    destruct Hw as [h ->].
    iSimpl.
    (* tee_local + set_local *)
    take_drop_app_rewrite 2.
    iApply wp_seq. iSplitR;[|iSplitL "Hf"];cycle 1.
    { fold_const. iApply (wp_tee_local with "[$]").
      iIntros "!> Hf".
      take_drop_app_rewrite 1.
      fold_const. iApply wp_val.
      iSplitR;cycle 1.
      { iApply (wp_wand _ _ _ (λ v, ⌜v = immV []⌝ ∗ _)%I with "[Hf]").
        iApply (wp_set_local with "[] [$Hf]");[rewrite Hflocs;simpl;lia|done|..].
        iIntros (v) "[-> Hf]". iSimpl.
        instantiate (1:=(λ v, ⌜v = immV _⌝ ∗ _)%I).
        iSplitR;eauto. iExact "Hf". }
      iIntros "[%Hcontr _]";done. }
    2: iIntros "[%Hcontr _]";done.
    iIntros (w) "[-> Hf]". iSimpl.
    (* relop *)
    take_drop_app_rewrite 2.
    iApply wp_seq. iSplitR;[|iSplitL "Hf"];cycle 1.
    { fold_const. iApply (wp_isdummy with "[$]");eauto.
      iNext. instantiate (1:=(λ v, ⌜v = immV _⌝)%I);eauto. }
    2: iIntros "[%Hcontr _]";done.
    iIntros (w) "[-> Hf]". iSimpl.

    (* CASES: new stack succeeded/failed *)
    iDestruct "Hres" as "[%Heq|Hres]".
    { (* failure *)
      inversion Heq;subst h.
      iSimpl.
      iApply wp_wasm_empty_ctx.
      (* if *)
      take_drop_app_rewrite_twice 0 (length main - 4).
      iApply wp_base_push;auto.
      iApply (wp_if_true_ctx with "Hf");[lias|..].
      iNext. iIntros "Hf".
      (* block *)
      take_drop_app_rewrite 0.
      iApply (wp_block_ctx with "Hf");[auto..|].
      iNext. iIntros "Hf".
      iApply wp_label_push_nil. iSimpl.
      iApply wp_ctx_bind;[simpl;auto|].
      (* trap *)
      iDestruct "Hg" as (gv) "Hg".
      iApply (wp_wand with "[Hf]").
      { iApply (wp_unreachable with "Hf");auto.
        iNext. instantiate (1:=(λ v, ⌜v = trapV⌝)%I);eauto. }
      iIntros (w) "[-> Hf]". iSimpl.
      take_drop_app_rewrite_twice 0 0.
      iApply (wp_wand_ctx with "[Hf]").
      { iApply (wp_trap_ctx with "Hf");auto. }
      iIntros (v) "[-> Hf]".
      iApply "HΦ". iSplitR "Hf Hall";[|iSplitL "Hf"; eauto]. by iLeft.
    }

    { (* success *)
      iDestruct "Hres" as (r) "[%Heq [%Hle HisStack]]". inversion Heq;subst r.
      destruct (is_dummy h) eqn:Hdummy.
      { apply is_dummy_true in Hdummy as ->. done. } 

      iSimpl.
      iApply wp_wasm_empty_ctx.
      (* if *)
      take_drop_app_rewrite_twice 0 (length main - 4).
      iApply wp_base_push;auto.
      iApply (wp_if_false_ctx with "Hf");[auto|..].
      iNext. iIntros "Hf".
      (* block *)
      take_drop_app_rewrite 0.
      iApply (wp_block_ctx with "Hf");[auto..|].
      iNext. iIntros "Hf". iSimpl.
      iApply wp_label_push_nil. iSimpl.
      iApply (wp_val_return with "Hf");auto.
      iIntros "Hf". iSimpl.
      (* get_local *)
      take_drop_app_rewrite 1.
      rewrite Hflocs. iSimpl in "Hf".
      iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
      iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
      { (* take_drop_app_rewrite 1. *)
        (* iApply wp_val. iSplitR;[by iIntros "[%Hcontr _]"|]. *)
        iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
      iIntros (w) "[-> Hf]".
      iSimpl.
      (* push *)
      take_drop_app_rewrite 3.

      iApply fupd_wp.
      iMod (na_inv_acc with "Hidf4 Hown") as "(>Hf4 & Hown & Hcls4)"; [by solve_ndisj| by solve_ndisj|..].
      iModIntro.

      
      iApply wp_seq. iSplitR;[|iSplitL "HisStack Hf Hf4"];cycle 1.
      { take_drop_app_rewrite_twice 2 0.
        iApply wp_wasm_empty_ctx.
        iApply wp_base_push;auto.
        iApply (wp_call_ctx with "Hf");[simpl;apply Hidf4|].
        iNext. iIntros "Hf".
        iApply wp_base_pull. iApply wp_wasm_empty_ctx.
        iSimpl. rewrite -/(u32const 4).
        iApply ("Hpush" with "[$Hf $Hf4 $HisStack]").
        { iPureIntro. simpl. lia. }
        iIntros (w). rewrite (bi.sep_assoc _ _ (↪[frame] _)%I).
        iIntros "[-> [HH Hf]]".
        instantiate (1:=(λ v, ⌜v = immV []⌝ ∗ ↪[frame] _ ∗ _)%I).
        iFrame "Hf".
        iSplit;[auto|]. iExact "HH". }
      iIntros (w) "( -> & Hf & HisStack & Hf4)".
      iSimpl. 2: by iIntros "[%Hcontr _]".
      (* get_local *)
      take_drop_app_rewrite 1.
      iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
      iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
      { (* take_drop_app_rewrite 1. *)
        (* iApply wp_val. iSplitR;[by iIntros "[%Hcontr _]"|]. *)
        iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
      iIntros (w) "[-> Hf]".
      iSimpl.
      (* push *)
      take_drop_app_rewrite 3.
      iApply wp_seq. iSplitR;[|iSplitL "HisStack Hf Hf4"];cycle 1.
      { take_drop_app_rewrite_twice 2 0.
        iApply wp_wasm_empty_ctx.
        iApply wp_base_push;auto.
        iApply (wp_call_ctx with "Hf");[simpl;apply Hidf4|].
        iNext. iIntros "Hf".
        iApply wp_base_pull. iApply wp_wasm_empty_ctx.
        iSimpl. iApply ("Hpush" with "[$Hf $Hf4 $HisStack]").
        { iPureIntro. simpl. lia. }
        iIntros (w). rewrite (bi.sep_assoc _ _ (↪[frame] _)%I).
        iIntros "[-> [HH Hf]]".
        instantiate (1:=(λ v, (⌜v = immV []⌝ ∗ _ ) ∗ ↪[frame] _)%I). iFrame "Hf".
        iSplit;[auto|]. iExact "HH". }
      iIntros (w) "[[-> [HisStack Hf4]] Hf]".

      iApply fupd_wp.
      iMod ("Hcls4" with "[$Hf4 $Hown]") as "Hown".
      iModIntro. 
      
      
      iSimpl. 2: by iIntros "[[%Hcontr _] _]".
      (* get_local *)
      take_drop_app_rewrite 1.
      iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
      iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
      { iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
      iIntros (w) "[-> Hf]".
      iSimpl.
      (* map *)
      iDestruct "Hidt" as "[Ht _]". iSimpl in "Ht".
      destruct (length (table_data stacktab));[lia|].
      rewrite firstn_cons. iDestruct "Ht" as "[Ht _]".
      
      take_drop_app_rewrite 3.
      iApply (wp_wand with "[-HΦ]").
      { 

(*        iApply fupd_wp.
        iMod (na_inv_acc with "Hidf5 Hown") as "(>Hf5 & Hown & Hcls5)"; [by solve_ndisj| by solve_ndisj|..].
        iModIntro. *)


        iApply wp_wasm_empty_ctx.
        iApply wp_seq_can_trap_ctx. iFrame "Hf".
        instantiate (2 := λ f', (⌜ f' = {|
                    f_locs :=
                      [_];
                    f_inst := f_inst f
                                        |}⌝ ∗ ∃ all, interp_allocator all)%I).
        
        iSplitR;[|iSplitR];cycle 2.
        iSplitL "HisStack Ht Hown Hall".
        { iIntros "Hf". iApply (wp_wand with "[-]").
          { take_drop_app_rewrite_twice 2 0.
            iApply wp_wasm_empty_ctx.
            iApply wp_base_push;auto.
            iApply (wp_call_ctx with "Hf");[simpl;apply Hidf5|].
            iNext. iIntros "Hf".
            iApply wp_base_pull. iApply wp_wasm_empty_ctx.
            iSimpl.
            iDestruct (be_fundamental_local _ _ [] _ (T_i32 :: locs) with "Hi") as "Hl";eauto.
            unfold interp_expression_closure.

            iApply fupd_wp.
            iMod (na_inv_alloc logrel_nais _ (wtN (N.of_nat idt) (N.of_nat 0)) with "Ht") as "#Ht".
            iApply ("Hmap" with "[] [] [$HisStack $Hf $Hidf5 Ht $Hown Hadv $Hall]");[iPureIntro;solve_ndisj|iPureIntro;solve_ndisj|..].
            { iSimpl. iFrame "Ht".
              instantiate (2:=(λ _, True)%I).
              instantiate (1:=(λ _ _, True)%I).
            
            repeat iSplit;[auto| |auto..|].
            { iPureIntro. auto. }
            { (* This is the most interesting part of the proof: since we do not assume a spec for the 
             imported function, we apply the ftlr to get a specifiction for the function *)
              iExists (wfN (N.of_nat a)). iFrame "Hadv".
              iSplitR;[iPureIntro;split;[solve_ndisj|]|].
              { apply namespaces.coPset_subseteq_difference_r;auto.
                unfold wfN,wtN.
                apply ndot_preserve_disjoint_r,ndot_preserve_disjoint_l.
                apply ndot_preserve_disjoint_r.
                unfold iris_logrel.wf,wt. solve_ndisj. }
              iSplitR;[auto|].
              iIntros (u fc all0). iModIntro.
              iIntros (Ψ) "(_ & %Histack & Hf & Hall & Hown) HΨ".
              iApply fupd_wp.
              iMod (na_inv_acc with "Hadv Hown") as "(>Ha & Hown & Hcls)";[solve_ndisj..|].
              take_drop_app_rewrite 1.
              iApply (wp_wand with "[-HΨ] [HΨ]");cycle 1.
              { iIntros (v). iSpecialize ("HΨ" $! v). rewrite bi.sep_assoc. iExact "HΨ". }
              iApply (wp_invoke_native with "Hf Ha");[eauto..|].
              iNext. iIntros "[Hf Ha]".
              iApply fupd_wp.
              iMod ("Hcls" with "[$]") as "Hown". iModIntro.
              
              rewrite -wp_frame_rewrite.
              iApply wp_wasm_empty_ctx_frame.
              take_drop_app_rewrite 0.
              iApply (wp_block_local_ctx with "Hf");[eauto..|].
              iNext. iIntros "Hf".
              iApply wp_wasm_empty_ctx_frame.
              rewrite wp_frame_rewrite.
              iDestruct ("Hl" $! _ _ ([VAL_int32 u] ++ n_zeros locs) with "Hf Hown Hall []") as "Hcont".
              { iSimpl. iRight. iExists _. iSplit;[eauto|].
                iSplit. iExists _. eauto.
                iApply n_zeros_interp_values. }
              iApply (wp_wand with "Hcont").
              iIntros (v) "([Hv ?] & ? & [%all' Hall])". iFrame.
              iSplitR "Hall"; last eauto.
              iDestruct "Hv" as "[? | Hv]";[by iLeft|iRight].
              iDestruct "Hv" as (ws ->) "Hw".
              iDestruct (big_sepL2_length with "Hw") as %Hwlen.
              destruct ws as [|w ws];[done|destruct ws;[|done]].
              iDestruct "Hw" as "[Hw _]". iDestruct "Hw" as (z) "->".
              unfold interp_value. eauto.
            }

            } 
            { iModIntro. iIntros (w) "(H & Hown & Hf & Hall)".
              iCombine "H Hown Hall " as "H". instantiate (1:=(λ vs, _ ∗ ↪[frame] _)%I).
              iFrame "Hf". iExact "H". }
          }
          iIntros (v) "[(Hv & Hown & Hall) Hf]".
          iSplitR "Hf Hall".
          iDestruct "Hv" as "[Htrap | [-> Hs]]";[by iLeft|].
          iRight. iCombine "Hs Hown" as "H".
          instantiate (1:=(λ v, ⌜v = immV []⌝ ∗ _ )%I). iSplit;auto. iExact "H".
          iFrame. eauto.
        }
        2: by iIntros "[%Hcontr _]".
        { iIntros (w f1) "((-> & Hs & Hown) & Hf & -> & Hall)".
          iSimpl. iApply wp_wasm_empty_ctx.
          (* get_local *)
          take_drop_app_rewrite 1.
          iApply (wp_seq _ _ _ (λ v, ⌜v = immV _⌝ ∗ _)%I).
          iSplitR;[|iSplitL "Hf"];[by iIntros "[%Hcontr _]"|..].
          { iApply (wp_get_local with "[] [$Hf]");simpl;eauto. }
          iIntros (w) "[-> Hf]".
          iSimpl.
          (* get_length *)
          (* we can infer the size of the new stack state *)
          iDestruct "Hs" as (s') "[HisStack Hstackall]".
          do 2 (destruct s';try done). { iDestruct "Hstackall" as "[? ?]";done. }
          destruct s';try done. 2: { iDestruct "Hstackall" as "[? [? ?]]";done. }
                              take_drop_app_rewrite 2.

          iApply fupd_wp.
          iMod (na_inv_acc with "Hidf6 Hown") as "(>Hf6 & Hown & Hcls6)"; [by solve_ndisj| by solve_ndisj|..].
          iModIntro.

          
          
          iApply wp_seq. iSplitR;[|iSplitL "HisStack Hf Hf6"];cycle 1.
          { take_drop_app_rewrite_twice 1 0.
            iApply wp_wasm_empty_ctx.
            iApply wp_base_push;auto.
            iApply (wp_call_ctx with "Hf");[simpl;apply Hidf6|].
            iNext. iIntros "Hf".
            iApply wp_base_pull. iApply wp_wasm_empty_ctx.
            iSimpl. unfold spec6_stack_length. unfold i32const.
            iApply ("Hstacklen" with "[$Hf $Hf6 $HisStack]").
            eauto.
            iIntros (w). rewrite (bi.sep_assoc _ _ (↪[frame] _)%I).
            iIntros "[-> [HH Hf]]". instantiate (1:=(λ vs, ⌜vs = immV [_]⌝ ∗ _ ∗ ↪[frame] _)%I). iFrame "Hf".
            iSplit;[auto|]. iExact "HH". }
          iIntros (w) "(-> & [HisStack Hf6] & Hf)".
          iSimpl. 2: by iIntros "[%Hcontr _]".

          iApply fupd_wp.
          iMod ("Hcls6" with "[$Hf6 $Hown]") as "Hown".
          iModIntro. 
          
          
          instantiate (1:=(λ v, (⌜v = trapV⌝
                                ∨ ⌜v = immV []⌝ ∗
                                         N.of_nat k↦[wg] {| g_mut := MUT_mut; g_val := xxv 2 |} ∗
                                         na_own logrel_nais ⊤) ∗ ↪[frame] _ ∗ (∃ all', interp_allocator all'))%I).
          iSimpl.
          iDestruct "Hg" as (gv) "Hg".
          iApply (wp_wand with "[Hf Hg]").
          { fold_const; iApply (wp_set_global with "[] Hf Hg");[simpl;auto|].
            instantiate (1:=(λ v, ⌜ v = immV [] ⌝)%I). iNext. auto. }
          iIntros (v) "[-> [Hg Hf]]". iFrame. iRight. iFrame. auto.
        }
        { iIntros (f1) "(Hf & -> & Hall)". iFrame. by iLeft. }
      }
      iIntros (v) "(Hv & Hf & Hall)".
      iApply "HΦ". iFrame. iExists _. iFrame. eauto. }
  Qed. 
      
    
End Client_main. 


Section Client_instantiation.

  Context `{HHB: HandleBytes, !wasmG Σ, !hvisG Σ, !hmsG Σ,
      !logrel_na_invs Σ, !hasG Σ, cancelg: !cancelG Σ, !cinvG Σ}.

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).
    Notation "{{{ P }}} es {{{ Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q v -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Definition stack_adv_client_instantiate (exp_addrs: list N) (stack_mod_addr adv_mod_addr client_mod_addr: N) :=
    [ ID_instantiate (take 8 exp_addrs) stack_mod_addr [] ;

      
      (* In Linstack, we needed adv to make no imports and export only one: *)
      (*      ID_instantiate [(exp_addrs !!! 8)] adv_mod_addr [] ; *)
      (* In Segstack, adv can import the stack operations: *)
      ID_instantiate [(exp_addrs !!! 8)] adv_mod_addr (take 7 exp_addrs);

      
      ID_instantiate [] client_mod_addr exp_addrs ].

  Lemma wp_wand_host s E (e : host_expr) (Φ Ψ : language.val wasm_host_lang -> iProp Σ) :
    WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
  Proof. iApply (weakestpre.wp_wand). Qed.

  Lemma instantiate_client adv_module g_ret wret (exp_addrs: list N) (stack_mod_addr adv_mod_addr client_mod_addr : N) all :
    length exp_addrs = 10 ->
    module_typing adv_module (fmap ET_func func_types) [ET_func (Tf [T_i32] [T_i32])] -> (* we assume the adversary module has an export of the () → () *)
    mod_start adv_module = None -> (* that it does not have a start function *)
    module_restrictions adv_module -> (* that it adheres to the module restrictions (i.e. only constant initializers for globals) *)
    module_elem_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a table, there cannot be more initializers that its size *)
    module_data_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a memory, there cannot be more initializers that its size *)
    typeof wret = T_i32 -> (* the imported return global has type i32 *)

    ⊢ {{{ g_ret ↦[wg] {| g_mut := MUT_mut; g_val := wret |} ∗
          stack_mod_addr ↪[mods] stack_module ∗
          adv_mod_addr ↪[mods] adv_module ∗
          client_mod_addr ↪[mods] client_module ∗
          na_own logrel_nais ⊤ ∗
          (∃ name, (exp_addrs !!! 9) ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx (N.to_nat g_ret)) |}) ∗
          (own_vis_pointers (take 8 exp_addrs)) ∗
          (∃ vs, (exp_addrs !!! 8) ↪[vis] vs) ∗
          ↪[frame] empty_frame ∗ interp_allocator all
      }}}
        ((stack_adv_client_instantiate exp_addrs stack_mod_addr adv_mod_addr client_mod_addr ,[]) : host_expr) 
      {{{ λ v: language.val wasm_host_lang, ⌜v = (trapHV : host_val)⌝ ∨ g_ret ↦[wg] {| g_mut := MUT_mut; g_val := xxv 2 |} }}} .
  Proof.
    iIntros (Hexpaddrlen Htyp Hnostart Hrestrict Hboundst Hboundsm Hgrettyp).
    do 11 (destruct exp_addrs => //); clear Hexpaddrlen.
    
    Opaque list_to_map.
    Opaque zip_with.
    
    iModIntro. iIntros (Φ) "(Hgret & Hmod_stack & Hmod_adv & Hmod_lse & Hown & Hvisglob & 
                        Hvisvst & Hvisadv & Hemptyframe & Hall) HΦ".
    iApply (wp_seq_host_nostart NotStuck with "[] [$Hmod_stack] [Hvisvst] ") => //.
    2: { iIntros "Hmod_stack".
         iApply weakestpre.wp_mono;cycle 1.
         iApply (instantiate_stack_spec_robust with "[$]") => //.
         iIntros (v) "[Hvsucc [$ Hv]]".
         iCombine "Hvsucc Hv" as "Hv".
         iExact "Hv". }
    { by iIntros "(% & ?)". }
    iIntros (w) "Hstack Hmod_stack".
    iDestruct "Hstack" as "(-> & Hstack)".
    
    iDestruct "Hstack" as (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt) "Hstack".
    iDestruct "Hstack" as (nm0 nm1 nm2 nm3 nm4 nm5 nm6 nm7 f0 f1) "Hstack".
    iDestruct "Hstack" as (f2 f3 f4 f5 f6 istack l0 l1 l2 l3) "Hstack".
    iDestruct "Hstack" as (l4 l5 l6 stacktab isStack) "Hstack".
    iDestruct "Hstack" as "(HimpsH & HimpsW & %Hnodup & %Hfnodup & %Htablen
    & #Hnewstack & #Hisempty & #Hisfull & #Hpop & #Hpoprobust & #Hpush & #Hmap & #Hmaptrap & #Hstacklen)".


       iDestruct "HimpsW" as "(_ & Hidf0 & Hidf1 & Hidf2 & Hidf3 & Hidf4 & Hidf5 & Hidf6 & Hidtab & _) /=".
    
    iDestruct "Hidf0" as (cl0) "[Himpfcl0 %Hcltype0]".
    iDestruct "Hidf1" as (cl1) "[Himpfcl1 %Hcltype1]".
    iDestruct "Hidf2" as (cl2) "[Himpfcl2 %Hcltype2]".
    iDestruct "Hidf3" as (cl3) "[Himpfcl3 %Hcltype3]".
    iDestruct "Hidf4" as (cl4) "[Himpfcl4 %Hcltype4]".
    iDestruct "Hidf5" as (cl5) "[Himpfcl5 %Hcltype5]".
    iDestruct "Hidf6" as (cl6) "[Himpfcl6 %Hcltype6]".
    iDestruct "Hidtab" as (tab0 tt) "[Htab %Htab0]".

    apply (NoDup_fmap_2 N.of_nat) in Hfnodup; simpl in Hfnodup.
    
    remember (list_to_map _) as mtmp.
    rewrite -> Heqmtmp in *.
    rewrite -> list_to_map_zip_lookup in Hcltype0, Hcltype1, Hcltype2, Hcltype3, Hcltype4, Hcltype5, Hcltype6 => //.
    invert_cllookup Hcltype0 0.
    invert_cllookup Hcltype1 1.
    invert_cllookup Hcltype2 2.
    invert_cllookup Hcltype3 3.
    invert_cllookup Hcltype4 4.
    invert_cllookup Hcltype5 5.
    invert_cllookup Hcltype6 6.

    remember (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6])
                             [FC_func_native istack (Tf [] [T_handle]) l0 f0 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l1 f1 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l2 f2 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l3 f3 ;
                              FC_func_native istack (Tf [T_handle; T_i32] []) l4 f4 ;
                              FC_func_native istack (Tf [T_handle; T_i32] []) l5 f5 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l6 f6 
                ]): gmap N function_closure) as mtmp0.

    iDestruct "HimpsH" as "(Hvis0 & Hvis1 & Hvis2 & Hvis3 & Hvis4 & Hvis5 & Hvis6 & Hvist & _)". 
    
    iApply (wp_seq_host_nostart NotStuck with "[] [$Hmod_adv] [Hvisadv Hvis1 Hvis2 Hvis3 Hvis0 Hvis4 Hvis5 Hvis6 Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Himpfcl6] ") => //.
    2: { iIntros "Hmod_adv".
         iApply weakestpre.wp_mono.
         2: iApply (instantiation_spec_operational_no_start).
         
         - iIntros (v) "[Hvsucc [$ Hv]]".
           iCombine "Hvsucc Hv" as "Hv".
           by iExact "Hv".
         - done.
         - done.
         - done.
         - iSimpl. iFrame "Hmod_adv".
           iSplitL "Hvis1 Hvis2 Hvis3 Hvis4 Hvis0 Hvis5 Hvis6".
           + instantiate (1 := [_;_;_;_;_;_;_]).
             iSplitL "Hvis0" ; first iExact "Hvis0". 
             iSplitL "Hvis1" ; first iExact "Hvis1".
             iSplitL "Hvis2" ; first iExact "Hvis2".
             iSplitL "Hvis3" ; first iExact "Hvis3".
             iSplitL "Hvis4" ; first iExact "Hvis4".
             iSplitL "Hvis5" ; first iExact "Hvis5".
             iSplitL "Hvis6" ; first iExact "Hvis6".
             done.
           + unfold instantiation_resources_pre_wasm.
             rewrite fmap_app in Hnodup.
             apply NoDup_app in Hnodup as (Hnodup & _ & _).
             
             rewrite irwt_nodup_equiv; last done.
             iSplitR "Hvisadv";[|auto]. iSplitL.
             { iSplit.
               { iPureIntro.
                 instantiate (1:=∅).
                 instantiate (1:=∅).
                 instantiate (1:=∅).
                 instantiate (1:= mtmp0).
                 subst.
                 cbn. rewrite !dom_insert_L !dom_empty_L.
                 auto. } 

               rewrite -> Heqmtmp0.
               iSplitL "Himpfcl0"; first by resolve_cl_lookup 0.
               iSplitL "Himpfcl1"; first by resolve_cl_lookup 1.
               iSplitL "Himpfcl2"; first by resolve_cl_lookup 2.
               iSplitL "Himpfcl3"; first by resolve_cl_lookup 3.
               iSplitL "Himpfcl4"; first by resolve_cl_lookup 4.
               iSplitL "Himpfcl5"; first by resolve_cl_lookup 5.
               iSplitL "Himpfcl6"; first by resolve_cl_lookup 6.
             done. 
             }
             iSplit; iPureIntro.
             done. done.
             iSplitL.
             iFrame. done.
             iPureIntro. simpl.
             destruct Htyp as [fts [gts Htyp]].
             destruct adv_module;simpl in *.
             destruct Htyp as (_&_&_&_&_&_&_&_&Htyp).
             apply Forall2_length in Htyp. auto. }


    { by iIntros "(% & ?)". }

    iIntros (w') "(-> & [Himps Hinst_adv]) Hmod_adv".
    iDestruct "Hinst_adv" as (inst_adv) "[Hinst_adv Hadv_exports]".
    iDestruct "Hinst_adv" as (g_adv_inits t_adv_inits m_adv_inits glob_adv_inits wts' wms')
                               "(Himpstyp & %HH & %Htyp_inits & %Hwts' & %Hbounds_elem & %Hmem_inits 
                               & %Hwms' & %Hbounds_data & %Hglob_inits_vals & %Hglob_inits & Hinst_adv_res)".

    iDestruct "Himps" as "(Hvis0 & Hvis1 & Hvis2 & Hvis3 & Hvis4 & Hvis5 & Hvis6 & _)". 
    
    destruct HH as (?&?&?&?&?&?).
    iDestruct (big_sepL2_length with "Hadv_exports") as %Hexp_len.
    destruct (mod_exports adv_module) eqn:Hexp;[done|].
    destruct l;[|done].
    iDestruct "Hadv_exports" as "[Hn _]".
    edestruct module_typing_body_eq as [Heq _]. 
    apply Heq in Htyp.
(*    revert Htyp. rewrite module_typing_body_eq => Htyp. *)
    destruct Htyp as [fts [gts Htyp]].
    assert (Hmod:=Htyp).
    remember adv_module as advm.
    destruct adv_module. rewrite Heqadvm in Hexp.
    rewrite Heqadvm in Hmod.
    
    simpl in Hexp. subst mod_exports.
    destruct Hmod as (Hmod&_&_&_&_&_&_&Himpts&Hexpts).
    apply Forall2_length in Himpts as Hlen.
    repeat (destruct mod_imports; first by simpl in Hlen; inversion Hlen).
    destruct mod_imports; last by simpl in Hlen; inversion Hlen.

    repeat (
        let Hm := fresh "Hm" in
        apply Forall2_cons in Himpts as [Hm Himpts];
        unfold module_import_typing in Hm
      ). 
    destruct (imp_desc m0) eqn:Hdesc0 ; (try by inversion Hm).
    destruct (imp_desc m1) eqn:Hdesc1 ; (try by inversion Hm0).
    destruct (imp_desc m2) eqn:Hdesc2 ; (try by inversion Hm1).
    destruct (imp_desc m3) eqn:Hdesc3 ; (try by inversion Hm2).
    destruct (imp_desc m4) eqn:Hdesc4 ; (try by inversion Hm3).
    destruct (imp_desc m5) eqn:Hdesc5 ; (try by inversion Hm4).
    destruct (imp_desc m6) eqn:Hdesc6 ; (try by inversion Hm5).

    apply andb_prop in Hm5 as [Hleq6 Hm6].
    apply andb_prop in Hm4 as [Hleq5 Hm5].
    apply andb_prop in Hm3 as [Hleq4 Hm4].
    apply andb_prop in Hm2 as [Hleq3 Hm3].
    apply andb_prop in Hm1 as [Hleq2 Hm2].
    apply andb_prop in Hm0 as [Hleq1 Hm1].
    apply andb_prop in Hm as [Hleq0 Hm0].

    simpl in Hleq6, Hleq5, Hleq4, Hleq3, Hleq2, Hleq1, Hleq0.
    simpl in Hm0; destruct (nth_error mod_types n9) eqn:Hnth0; last by inversion Hm0.
    simpl in Hm1; destruct (nth_error mod_types n10) eqn:Hnth1; last by inversion Hm1.
    simpl in Hm2; destruct (nth_error mod_types n11) eqn:Hnth2; last by inversion Hm2.
    simpl in Hm3; destruct (nth_error mod_types n12) eqn:Hnth3; last by inversion Hm3.
    simpl in Hm4; destruct (nth_error mod_types n13) eqn:Hnth4; last by inversion Hm4.
    simpl in Hm5; destruct (nth_error mod_types n14) eqn:Hnth5; last by inversion Hm5.
    simpl in Hm6; destruct (nth_error mod_types n15) eqn:Hnth6; last by inversion Hm6.

    apply b2p in Hm0 as <-.
    apply b2p in Hm1 as <-.
    apply b2p in Hm2 as <-.
    apply b2p in Hm3 as <-.
    apply b2p in Hm4 as <-.
    apply b2p in Hm5 as <-.
    apply b2p in Hm6 as <-.
    
    simpl in Hexpts.
    apply Forall2_cons in Hexpts as [He _].
    unfold module_export_typing in He. simpl in He.
    destruct (modexp_desc m) eqn:Hm;[destruct f|by destruct t|by destruct m7|by destruct g].
    apply andb_true_iff in He as [Hle He].
    destruct (nth_error _ n16) eqn:Hn;[|done].
    revert He. move/eqP=>He. subst f.
    iDestruct "Hn" as (name) "Hn".

    rewrite Heqadvm.
    iDestruct "Hinst_adv_res" as "(Hresf & Hrest & Hresm & Hresg) /=".
    rewrite /get_import_func_count
            /get_import_mem_count
            /get_import_table_count
            /get_import_global_count.

    simpl; rewrite Hdesc0 Hdesc1 Hdesc2 Hdesc3 Hdesc4 Hdesc5 Hdesc6; simpl.
    
    rewrite !drop_0 -Heqadvm.
    rewrite nth_error_lookup in Hn.

    repeat (destruct n16; first by inversion Hn).
    simpl in Hn.
    
    eapply Forall2_lookup_r in Hmod as [mf [Hmf Htypf]];[|exact Hn].
    destruct mf. simpl in Htypf.
    destruct modfunc_type. destruct Htypf as (Hlef & Hnthf & Htypf).
    revert Hlef. move/ssrnat.leP=>Hlef.
    assert (n17 < length mod_types) as Hlt;[lia|].
    rewrite Heqadvm /= in H.
    apply lookup_lt_is_Some in Hlt as [t Ht].
    rewrite - nth_error_lookup in Ht.
    erewrite nth_error_nth in Hnthf;eauto.
    revert Hnthf;move/eqP=>heq. subst t.
    iDestruct (big_sepL2_length with "Hresf") as %Hinstf_len.
    apply lookup_lt_Some in Hmf as Hlt'.
    rewrite Hinstf_len in Hlt'.
    apply lookup_lt_is_Some in Hlt' as [advf Hadv].
    iDestruct (big_sepL2_lookup_acc with "Hresf") as "[Hadvf Hcls]";[eauto..|].
    simpl.
    rewrite - nth_error_lookup in Hadv.
    rewrite H.
    erewrite !nth_error_nth ;eauto.
    2:{ remember (inst_funcs inst_adv) as l.
        apply lookup_lt_Some in Hmf.
        rewrite Hinstf_len in Hmf.

        do 7 (destruct l; first by (repeat destruct n16 => //)).
        simpl. simpl in Hadv. unfold drop in Hadv. done. } 
    
    iDestruct "Hvisglob" as (gr) "Hvisglob".

   
    rewrite irwt_nodup_equiv.
    2:{ rewrite fmap_app in Hnodup.
        apply NoDup_app in Hnodup as (Hnodup & _ & _).
        done. }

    iDestruct "Himpstyp" as "(_ & Hidf0 & Hidf1 & Hidf2 & Hidf3 & Hidf4 & Hidf5 & Hidf6 & _) /=".
    
    iDestruct "Hidf0" as (cl0) "[Himpfcl0 %Hcltype0]".
    iDestruct "Hidf1" as (cl1) "[Himpfcl1 %Hcltype1]".
    iDestruct "Hidf2" as (cl2) "[Himpfcl2 %Hcltype2]".
    iDestruct "Hidf3" as (cl3) "[Himpfcl3 %Hcltype3]".
    iDestruct "Hidf4" as (cl4) "[Himpfcl4 %Hcltype4]".
    iDestruct "Hidf5" as (cl5) "[Himpfcl5 %Hcltype5]".
    iDestruct "Hidf6" as (cl6) "[Himpfcl6 %Hcltype6]".

    rewrite -> Heqmtmp0 in *.
    rewrite -> list_to_map_zip_lookup in Hcltype0, Hcltype1, Hcltype2, Hcltype3, Hcltype4, Hcltype5, Hcltype6 => //.
    invert_cllookup Hcltype0 0.
    invert_cllookup Hcltype1 1.
    invert_cllookup Hcltype2 2.
    invert_cllookup Hcltype3 3.
    invert_cllookup Hcltype4 4.
    invert_cllookup Hcltype5 5.
    invert_cllookup Hcltype6 6.

    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl0") as "%Hadv0" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl1") as "%Hadv1" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl2") as "%Hadv2" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl3") as "%Hadv3" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl4") as "%Hadv4" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl5") as "%Hadv5" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Hadvf Himpfcl6") as "%Hadv6" ; first by eauto.

    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl1") as "%H01" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl2") as "%H02" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl3") as "%H03" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl4") as "%H04" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl5") as "%H05" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl0 Himpfcl6") as "%H06" ; first by eauto.

    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl2") as "%H12" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl3") as "%H13" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl4") as "%H14" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl5") as "%H15" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl1 Himpfcl6") as "%H16" ; first by eauto.

    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl3") as "%H23" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl4") as "%H24" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl5") as "%H25" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl2 Himpfcl6") as "%H26" ; first by eauto.

    iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl4") as "%H34" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl5") as "%H35" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl3 Himpfcl6") as "%H36" ; first by eauto.
    
    iDestruct (mapsto_frac_ne with "Himpfcl4 Himpfcl5") as "%H45" ; first by eauto.
    iDestruct (mapsto_frac_ne with "Himpfcl4 Himpfcl6") as "%H46" ; first by eauto.

    iDestruct (mapsto_frac_ne with "Himpfcl5 Himpfcl6") as "%H56" ; first by eauto.
    
    
    rewrite lookup_insert in Htab0.
    destruct Htab0 as [Hteq [Htt Htabt]].
    inversion Hteq; subst tab0; clear Hteq.
    inversion Htt; subst tt; clear Htt.

    assert (NoDup (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6; advf])) as Hnodupadvf.
    {  simpl. rewrite separate7. apply NoDup_app; repeat split; last by apply NoDup_singleton.
       { done. }
       { move => x Hin Hcontra.
         clear - Hadv0 Hadv1 Hadv2 Hadv3 Hadv4 Hadv5 Hadv6 Hin Hcontra.
         inversion Hcontra; subst;
         by set_solver. }
    }
    
    assert ( NoDup
               [MED_func (Mk_funcidx idf0); MED_func (Mk_funcidx idf1); MED_func (Mk_funcidx idf2); MED_func (Mk_funcidx idf3);
                MED_func (Mk_funcidx idf4); MED_func (Mk_funcidx idf5); MED_func (Mk_funcidx idf6); MED_table (Mk_tableidx idt);
                MED_func (Mk_funcidx advf); MED_global (Mk_globalidx (N.to_nat g_ret))]) as Hexpnodup.
    { clear - Hfnodup Hadv0 Hadv1 Hadv2 Hadv3 Hadv4 Hadv5 Hadv6.
      
      rewrite separate9. apply NoDup_app; repeat split; last by apply NoDup_singleton.
      2: { move => x Hin Hcontra. inversion Hcontra; subst; by set_solver. }

      rewrite separate8. apply NoDup_app; repeat split; last by apply NoDup_singleton.
      2: { move => x Hin Hcontra. inversion Hcontra; subst; by set_solver. }
      
      rewrite separate7. apply NoDup_app; repeat split; last by apply NoDup_singleton.
      2: { move => x Hin Hcontra. inversion Hcontra; subst; by set_solver. }


      assert (Inj eq eq (λ x : N, MED_func (Mk_funcidx (N.to_nat x)))).
      { move => x y Heq; inversion Heq; by lias. } 

      eapply (NoDup_fmap_2 (λ x, (MED_func (Mk_funcidx (N.to_nat x))))) in Hfnodup; simpl in Hfnodup.
      by repeat rewrite Nat2N.id in Hfnodup.
    }
    
    iApply (wp_wand_host _ _ _ (λ v, _ ∗ ↪[frame]empty_frame)%I with "[-HΦ] [HΦ]");cycle 1.
    { iIntros (v) "[Hv Hframe]". iApply "HΦ". iExact "Hv". }

    remember (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6; advf])
                               [FC_func_native istack (Tf [] [T_handle]) l0 f0 ;
                                FC_func_native istack (Tf [T_handle] [T_i32]) l1 f1 ;
                                FC_func_native istack (Tf [T_handle] [T_i32]) l2 f2 ;
                                FC_func_native istack (Tf [T_handle] [T_i32]) l3 f3 ;
                                FC_func_native istack (Tf [T_handle; T_i32] []) l4 f4 ;
                                FC_func_native istack (Tf [T_handle; T_i32] []) l5 f5 ;
                                FC_func_native istack (Tf [T_handle] [T_i32]) l6 f6 ;
                                (FC_func_native inst_adv (Tf [T_i32] [T_i32]) modfunc_locals modfunc_body)]): gmap N function_closure) as mtmp.


    
    iApply (instantiation_spec_operational_start with "[$Hemptyframe] [Hmod_lse Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6 Hvist Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Himpfcl6 Hadvf Htab Hn Hgret Hvisglob]")
    ; try exact client_module_typing;[eauto|..].
    { unfold module_restrictions.
      simpl.
      split; first by exists [].
      split; first by exists ([Wasm_int.int_of_Z i32m 0]).
      by exists [].
    }
    { iFrame. 
      instantiate (5:=[_;_;_;_;_;_;_;_;_;_]).
      iFrame "Hn Hvisglob Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6 Hvist". 
      iSplitR;[done|].
      unfold instantiation_resources_pre_wasm.
      rewrite irwt_nodup_equiv => /=; last done.
      
      iSplitL;[|auto]. iSplitL.
      { iSplit.
        { iPureIntro.
          instantiate (1:={[g_ret := {| g_mut := MUT_mut; g_val := wret |} ]}).
          instantiate (1:=∅).
          instantiate (1:={[N.of_nat idt := stacktab]}).
          instantiate (1:= mtmp).
          subst.
          cbn. rewrite !dom_insert_L !dom_empty_L.
          rewrite N2Nat.id. auto. }

        rewrite -> Heqmtmp.
        iSplitL "Himpfcl0"; first by resolve_cl_lookup 0.
        iSplitL "Himpfcl1"; first by resolve_cl_lookup 1.
        iSplitL "Himpfcl2"; first by resolve_cl_lookup 2.
        iSplitL "Himpfcl3"; first by resolve_cl_lookup 3.
        iSplitL "Himpfcl4"; first by resolve_cl_lookup 4.
        iSplitL "Himpfcl5"; first by resolve_cl_lookup 5.
        iSplitL "Himpfcl6"; first by resolve_cl_lookup 6.
        iSplitL "Htab". { iExists _, _; iFrame. rewrite lookup_insert. iPureIntro. done. }
        iSplitL "Hadvf"; first by resolve_cl_lookup 7.
        iSplitL "Hgret". { iExists _, _; rewrite N2Nat.id; iFrame. rewrite lookup_insert. iPureIntro. repeat split => //.
                         unfold global_agree; apply/andP => /=; split => //. by apply/eqP. }
        done.
      }

      unfold module_elem_bound_check_gmap,module_data_bound_check_gmap. cbn.
      iSplit;[|iPureIntro;apply Forall_nil].
      iPureIntro. apply Forall_cons.
      split;[|apply Forall_nil].
      simpl. rewrite lookup_insert;auto. done. done. cbn. done. }

    iIntros (idnstart) "Hf [Hmod_lse Hr]".
    iDestruct "Hr" as "((Himpf0 & Himpf1 & Himpf2 & Himpf3 & Himpf4 & Himpf5 & Himpf6 & Htab & Hadvf & Hg & _) & Hr)".
    iDestruct "Hr" as (?) "[Hr' _]".
    unfold instantiation_resources_post_wasm.
    iDestruct "Hr'" as (? ? ? ? ? ?) "Hr'".
    rewrite irwt_nodup_equiv => /=; last done.
    
    iDestruct "Hr'" as "([%Hdom (Himpr0 & Himpr1 & Himpr2 & Himpr3 & Himpr4 & Himpr5 & Himpr6 & Htabr & Hadv & Hgret & _)] & %Htypr & %Htab_inits & %Hwts'0 & %Hbounds_elemr & 
        %Hmem_initsr & %Hwms0' & %Hbounds_datar & %Hglobsr & %Hglob_initsr & Hr )".
    iDestruct "Hr" as "(Hr&_&_&_)".
    destruct Htypr as (Heq1&[? Heq2]&[? Heq3]&[? Heq4]&[? Heq6]&Heq5).
    rewrite Heq2.
    iSimpl in "Himpr0 Himpr1 Himpr2 Himpr3 Himpr4 Himpr5 Himpr6 Hadv Hgret Htabr".
    rewrite N2Nat.id.

    rewrite -> Heqmtmp.

    iDestruct "Himpr0" as (cl0) "[Himpfcl0 %Hcltype0]".
    iDestruct "Himpr1" as (cl1) "[Himpfcl1 %Hcltype1]".
    iDestruct "Himpr2" as (cl2) "[Himpfcl2 %Hcltype2]".
    iDestruct "Himpr3" as (cl3) "[Himpfcl3 %Hcltype3]".
    iDestruct "Himpr4" as (cl4) "[Himpfcl4 %Hcltype4]".
    iDestruct "Himpr5" as (cl5) "[Himpfcl5 %Hcltype5]".
    iDestruct "Himpr6" as (cl6) "[Himpfcl6 %Hcltype6]".
    iDestruct "Hadv" as (cladv) "[Himpfcladv %Hcltypeadv]".

    rewrite -> list_to_map_zip_lookup in Hcltype0, Hcltype1, Hcltype2, Hcltype3, Hcltype4, Hcltype5, Hcltype6, Hcltypeadv => //.
    clear Hexpnodup.
    invert_cllookup Hcltype0 0.
    invert_cllookup Hcltype1 1.
    invert_cllookup Hcltype2 2.
    invert_cllookup Hcltype3 3.
    invert_cllookup Hcltype4 4.
    invert_cllookup Hcltype5 5.
    invert_cllookup Hcltype6 6.
    invert_cllookup Hcltypeadv 7.
    
    iDestruct "Hgret" as (g gt) "(Hgret & %Hlookg & %Hgteq & %Hagree)".
    rewrite lookup_insert in Hlookg. inversion Hlookg;clear Hlookg.
    iDestruct (big_sepL2_length with "Hr") as %Himprlen.
    destruct x;[done|destruct x;[|done]].
    iDestruct "Hr" as "[Hr _] /=". rewrite Heq1 /=.
    iDestruct ("Hcls" with "Himpfcladv") as "Hresf".
    iDestruct "Htabr" as (tab tt0) "(Htabr & %Hwts'look & %Htt0 & %Htabtyp)".
    inversion Htt0;subst tt0;clear Htt0.
    apply module_import_init_tabs_Some in Hwts'look as HH; destruct HH as [? Hwtslook].
    eapply module_import_init_tabs_lookup in Hwtslook as Heqtab;[|eauto].
    rewrite lookup_singleton in Hwtslook. inversion Hwtslook;subst x.
    cbn in Heqtab. rewrite Heq3 in Heqtab. cbn in Heqtab.
    rewrite Nat2N.id decide_True /= // Heq2 /= in Heqtab.
    subst tab.

    remember (list_to_map (zip (fmap N.of_nat [idf0; idf1; idf2; idf3; idf4; idf5; idf6])
                             [FC_func_native istack (Tf [] [T_handle]) l0 f0 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l1 f1 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l2 f2 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l3 f3 ;
                              FC_func_native istack (Tf [T_handle; T_i32] []) l4 f4 ;
                              FC_func_native istack (Tf [T_handle; T_i32] []) l5 f5 ;
                              FC_func_native istack (Tf [T_handle] [T_i32]) l6 f6 
                ]): gmap N function_closure) as mtmp0.
    

    iApply weakestpre.fupd_wp.
    iMod (interp_instance_alloc with "[] [] [] [] [Himpfcl0 Himpfcl1 Himpfcl2 Himpfcl3 Himpfcl4 Himpfcl5 Himpfcl6] [Hrest Hresm Hresg Hresf]") as "(#Hi & [#Hires _] & Himps)";
      [apply Htyp|repeat split;eauto|eauto|..].
    (* 2,3,4,5: by instantiate (1:=∅). *)
    { destruct Hglob_inits_vals as [? ?];eauto. }
    {
      instantiate (1 := mtmp0).
      subst mtmp0.
      Transparent list_to_map. Transparent zip_with. iSimpl.
      iApply big_sepM_insert.
      by repeat (rewrite lookup_insert_ne => //).
      iSplit. admit.
      iApply big_sepM_insert.
      by repeat (rewrite lookup_insert_ne => //).
      iSplit. admit.
      iApply big_sepM_insert.
      by repeat (rewrite lookup_insert_ne => //).
      iSplit. admit.
      iApply big_sepM_insert.
      by repeat (rewrite lookup_insert_ne => //).
      iSplit. iExact "Hpoprobust". 
      iApply big_sepM_insert.
      by repeat (rewrite lookup_insert_ne => //).
      iSplit. admit.
      iApply big_sepM_insert.
      by repeat (rewrite lookup_insert_ne => //).
      iSplit. admit.
      iApply big_sepM_insert.
      done.
      iSplit. admit.
      done. 
    }
    1,2,3: by instantiate (1 := ∅).
    { rewrite irwt_nodup_equiv.
      2:{ rewrite fmap_app in Hnodup.
        apply NoDup_app in Hnodup as (Hnodup & _ & _).
        done. }
      repeat iSplit;auto.
      subst mtmp0. iPureIntro. Transparent list_to_map. Transparent zip_with. simpl.
      clear. 
      set_solver. 
      rewrite module_import_init_tabs_dom. auto.
      rewrite module_import_init_mems_dom. auto.
      iSimpl.
      iSplitL "Himpfcl0".
      iExists _; iFrame; iPureIntro; split => //; subst mtmp0; simpl; by repeat (rewrite lookup_insert_ne; last done); rewrite lookup_insert.
      iSplitL "Himpfcl1".
      iExists _; iFrame; iPureIntro; split => //; subst mtmp0; simpl; by repeat (rewrite lookup_insert_ne; last done); rewrite lookup_insert.
      iSplitL "Himpfcl2".
      iExists _; iFrame; iPureIntro; split => //; subst mtmp0; simpl; by repeat (rewrite lookup_insert_ne; last done); rewrite lookup_insert.
      iSplitL "Himpfcl3".
      iExists _; iFrame; iPureIntro; split => //; subst mtmp0; simpl; by repeat (rewrite lookup_insert_ne; last done); rewrite lookup_insert.
      iSplitL "Himpfcl4".
      iExists _; iFrame; iPureIntro; split => //; subst mtmp0; simpl; by repeat (rewrite lookup_insert_ne; last done); rewrite lookup_insert.
      iSplitL "Himpfcl5".
      iExists _; iFrame; iPureIntro; split => //; subst mtmp0; simpl; by repeat (rewrite lookup_insert_ne; last done); rewrite lookup_insert.
      iSplitL.
      iExists _; iFrame; iPureIntro; split => //; subst mtmp0; simpl; by repeat (rewrite lookup_insert_ne; last done); rewrite lookup_insert.
      done.
    }
    { rewrite /module_inst_resources_wasm /=
                  /get_import_table_count
                  /get_import_mem_count
                  /get_import_global_count
                  /get_import_func_count /=
                  Hdesc0 Hdesc1 Hdesc2 Hdesc3 Hdesc4 Hdesc5 Hdesc6 /=
                  !drop_0.
      iFrame. 
    }
    cbn in Heq5. rewrite Heq2 /= in Heq5.
    revert Heq5;move/eqP=>Heq5. subst n18.


    iDestruct "Himps" as "(Hfs & Hts & Hms & Hgs)".
    iDestruct "Hfs" as "[Hfs %Hdomtyp]".
    unfold import_func_nainv.
    subst mtmp0.
    Transparent list_to_map. Transparent zip_with.
    iSimpl in "Hfs".
    iDestruct (big_sepM_insert with "Hfs") as "[#Hf0 Hfs]"; first by repeat (rewrite lookup_insert_ne => //).
    iDestruct (big_sepM_insert with "Hfs") as "[#Hf1 Hfs]"; first by repeat (rewrite lookup_insert_ne => //).
    iDestruct (big_sepM_insert with "Hfs") as "[#Hf2 Hfs]"; first by repeat (rewrite lookup_insert_ne => //).
    iDestruct (big_sepM_insert with "Hfs") as "[#Hf3 Hfs]"; first by repeat (rewrite lookup_insert_ne => //).
    iDestruct (big_sepM_insert with "Hfs") as "[#Hf4 Hfs]"; first by repeat (rewrite lookup_insert_ne => //).
    iDestruct (big_sepM_insert with "Hfs") as "[#Hf5 Hfs]"; first by repeat (rewrite lookup_insert_ne => //).
    iDestruct (big_sepM_insert with "Hfs") as "[#Hf6 Hfs]"; first by repeat (rewrite lookup_insert_ne => //).


  


    iModIntro.
    
    iApply wp_lift_wasm.
    take_drop_app_rewrite 0.
    iApply (wp_invoke_native with "Hf Hr");[eauto|eauto..|].
    iNext. iIntros "[Hf Hidnstart]".
    iApply (wp_frame_bind with "Hf"). { cbn. auto. } iIntros "Hf".
    take_drop_app_rewrite 0. iApply (wp_block with "Hf");[auto..|].
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind;[simpl;auto|]. repeat erewrite app_nil_l.

    (* iApply (wp_wand with "[Hf Hgret Himpfcl0 Himpfcl3 Himpfcl4 Himpfcl5 Himpfcl6 Hown Htabr Hall]"). *)
    iApply (wp_wand with "[Hf Hgret Hown Htabr Hall]").
    { (*iApply (main_spec with "[$Hi $Hf $Hown Himpfcl0 Himpfcl3 Himpfcl4 Himpfcl5 Himpfcl6 Htabr Hgret Hall]"). *)
      iApply (main_spec with "[$Hi $Hf $Hown Htabr Hgret Hall]").
      { simpl. auto. }
      { simpl. rewrite Heq6. simpl. eauto. }
      { simpl. rewrite Heq3. simpl. eauto. }
      1,2,3,4: rewrite /= Heq2 /=;eauto.
      { eauto. }
      { apply Htablen. }
      { unfold upd_local_label_return. simpl.
        apply Htypf. }
      { iFrame. iSplit.
        { iDestruct (big_sepL2_lookup with "Hires") as "Ha".
          { eauto. }
          { rewrite /get_import_func_count /= Hdesc0 Hdesc1 Hdesc2 Hdesc3 Hdesc4 Hdesc5 Hdesc6 /=. rewrite - nth_error_lookup. done. }
          iSimpl in "Ha". erewrite nth_error_nth;eauto. }
        iSplitL "Hgret";[iExists _;rewrite N2Nat.id;iFrame|].
        iFrame "Hf0 Hf4 Hf5 Hf6 Hnewstack Hpush Hmaptrap Hstacklen".
        }
      iIntros (v) "HH". iExact "HH".
    }
    iIntros (v) "(HH & Hf & Hall)".
    iDestruct "Hf" as (f) "[Hf %Hfeq]".
    iDestruct "HH" as "[-> | Hres]".
    { take_drop_app_rewrite_twice 0 0.
      iApply (wp_wand_ctx with "[Hf]").
      { iApply (wp_trap_ctx with "Hf"). auto. }
      iIntros (v) "[-> Hf]".
      iExists f;iFrame.
      iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ _)%I with "[Hf]").
      { iApply (wp_frame_trap with "Hf"). iNext. auto. }
      iIntros (v) "[-> Hf]". iFrame.
      iApply weakestpre.wp_value. apply language.of_to_val. eauto.
      by iLeft. }
    { iDestruct "Hres" as "[-> Hgret]".
      iSimpl. iApply (wp_val_return with "Hf");[auto..|].
      iIntros "Hf".
      iSimpl. iApply iris_wp.wp_value;[eapply iris.of_to_val;eauto|].
      iExists _;iFrame.
      iIntros "Hf".
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = immV []⌝ ∗ _)%I with "[Hf]").
      { iApply (wp_frame_value with "Hf");[eauto|auto|..].
        iNext. auto. }
      iIntros (v) "[-> Hf]". iFrame.
      iApply weakestpre.wp_value. apply language.of_to_val. eauto.
      iRight. rewrite N2Nat.id. iDestruct "Hgret" as "[$ Hown]".
    }
  Qed.
  
End Client_instantiation. 
