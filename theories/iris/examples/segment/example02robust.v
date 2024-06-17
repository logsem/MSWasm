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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section Example02.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Context `{!wasmG Σ,
      !logrel_na_invs Σ, HHB: HandleBytes, !cinvG Σ, !cancelG Σ}.

(*
allocate a handle h with space for one i32
if allocation failed, set global variable g to 0 and return
write 42 to h
set global variable (g' 2) to 0
call an adversary function of type [handle] -> [], with argument dummy_handle (import dummy_handle as global 1 from adversary)
set global variable (g' 2) to 1 (this is so that if the adversary call fails, we can use g' to know that that was the point of failure)
read from h
set global variable g to the read value
free h
*)


  
  Definition example_program :=
    [
      BI_const (xx 1);
      BI_set_global 2;
      BI_const (xx 4);
      BI_segalloc;
      BI_tee_local 0;
      BI_isdummy;
      BI_if (Tf [] []) [ BI_const (xx 0) ; BI_set_global 0; BI_return ] [];
      BI_get_local 0;
      BI_const (xx 42);
      BI_segstore T_i32;
      BI_const (xx 0);
      BI_set_global 2;
      BI_get_global 1;
      BI_call 0;
      BI_const (xx 1);
      BI_set_global 2;
      BI_get_local 0;
      BI_segload T_i32;
      BI_set_global 0;
      BI_get_local 0;
      BI_segfree
    ].

  Definition example_function f :=
    [ AI_local 0 f [ AI_basic (BI_block (Tf [] []) example_program) ] ].


  Lemma program_spec f k kdummy k' f0 gv gv' a es i locs C all:
     (tc_label C) = [] ∧ (tc_return C) = None ->
    f.(f_inst).(inst_globs) !! 0 = Some k ->
    f.(f_inst).(inst_globs) !! 1 = Some kdummy ->
    f.(f_inst).(inst_globs) !! 2 = Some k' ->
    f.(f_inst).(inst_funcs) !! 0 = Some a ->
    length f.(f_locs) >= 1 ->
    be_typing (upd_local_label_return C (T_handle :: locs) [[]] (Some [])) es (Tf [] []) ->

    ⊢ {{{ ↪[frame] f0 ∗ interp_allocator all 
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_handle] []) locs es))
         ∗  na_inv logrel_nais (wgN (N.of_nat kdummy))
                (∃ w : value,
                   N.of_nat kdummy↦[wg] {|
                                     g_mut := tg_mut {| tg_mut := MUT_mut; tg_t := T_handle |};
                                     g_val := w
                                   |} ∗
                   interp_value_handle w)
         ∗ interp_instance C [] i
         ∗ N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := gv |}
         ∗ N.of_nat k' ↦[wg] {| g_mut := MUT_mut ; g_val := gv' |}
      }}}
      example_function f
      {{{ v, ⌜ v = trapV ⌝ ∗
                     N.of_nat k' ↦[wg] {| g_mut := MUT_mut ; g_val := (VAL_numeric (xx 0)) |}
             ∨
               ⌜ v = immV [] ⌝ ∗
                       ↪[frame] f0 ∗
                       na_own logrel_nais ⊤ ∗
                       (∃ all, interp_allocator all) ∗
                       N.of_nat k' ↦[wg] {| g_mut := MUT_mut ; g_val := VAL_numeric (xx 1) |} ∗
                       (∃ gv, N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := VAL_numeric (xx gv) |} ∗ ⌜ gv = 0 ∨ gv = 42 ⌝) }}}.
  Proof.
    iIntros (HC Hglob0 Hglob1 Hglob2 Hfunc Hlocs Hes Φ) "!> (Hf & Hall & Hown & #Hfinv & #Hginv & #Hi & Hg & Hg') HΦ".

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
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hg'".  unfold xx; fold_const.
    
    iApply (wp_set_global with "[] Hf Hg'"). done.
    by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "(-> & Hg' & Hf)". 
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
      iSimpl. iApply wp_value. apply of_to_val. done.
      iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx. 

      iApply wp_value.
      unfold IntoVal. apply language.of_to_val. done.
      instantiate (1 := λ x, (⌜ x = retV _ ⌝ ∗ _)%I).
      iSplit; first done.
      iCombine "Hall Hown Hg' HΦ Hg Hf" as "H". iExact "H".
      2: by iIntros "[% _]".
      iIntros (w) "(-> & Hall & Hown & Hg' & HΦ & Hg & Hf)".
      iSimpl. iApply wp_value. apply of_to_val. done. 
           
      iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx. 
      iApply wp_value. apply of_to_val. done.
      iExists _. iFrame. iIntros "Hf". iSimpl.
      iApply (wp_wand with "[Hf]").
      iApply wp_return.
      3:{ instantiate (3 := 2). instantiate (1 := []). 
          instantiate (1 := LH_rec [] _ _ (LH_rec [] _ _ (LH_base [] []) _) []).
          unfold lfilled, lfill. simpl. done. }
      done. done.
      iNext. iApply wp_value. apply of_to_val => //. iFrame.
      by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
      iIntros (w) "[-> Hf]".
      iApply "HΦ". iRight. iSplit => //. iFrame. iSplitL "Hall". iExists _. iFrame.
      iExists _. iFrame. 
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

    rewrite (separate2 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hg'".
    fold_const. iApply (wp_set_global with "[] Hf Hg'"). done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "(-> & Hg' & Hf)".
    iSimpl.
    rewrite (separate1 (AI_basic _)).

    
    iApply fupd_wp.
    iMod (na_inv_acc with "Hginv Hown") as "(H & Hown & Hcls)"; try solve_ndisj.
    iDestruct "H" as (hdummy) "[>Hgdummy #Hdummy]". iSimpl in "Hgdummy".
    fold (interp_value T_handle). 
    iDestruct (interp_value_agree with "Hdummy") as ">%H".
    destruct hdummy; first by destruct n => //. 
    iModIntro.
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hgdummy". 


    iApply (wp_get_global with "[] Hf Hgdummy").
    done. done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "(-> & Hgdummy & Hf)".
    
    iSimpl.
    iApply fupd_wp. iMod ("Hcls" with "[Hgdummy $Hown]") as "Hown".
    iExists _. iFrame. done.
    iModIntro. 
    
    rewrite (separate1 (AI_handle _)).
    rewrite (separate1 (AI_basic _)).
    iApply wp_wasm_empty_ctx. 
    iApply wp_base_push. done.
    iApply (wp_call_ctx with "Hf"). done.
    iIntros "!> Hf". iApply wp_base_pull.
    iSimpl.
    
    rewrite (separate2 (AI_handle _)).
    iApply (wp_wand_ctx with "[-HΦ]").
    iApply (wp_seq_can_trap_ctx with "[-]").
    iSplitR; last first.
    iSplitR; last first. iFrame "Hf". 
    iSplitL "Hown Hall Hg'". 
    iIntros "Hf". rewrite (separate1 (AI_handle _)).
    iApply fupd_wp.
    iMod (na_inv_acc with "Hfinv Hown") as "(>Haf & Hown & Hcls)"; try solve_ndisj.
    iModIntro. iApply (wp_invoke_native with "Hf Haf").

    
    done. done. done. iIntros "!> [Hf Haf]".
    iApply fupd_wp. iMod ("Hcls" with "[$]") as "Hown".
    iModIntro.

    rewrite -wp_frame_rewrite.
    iApply wp_wasm_empty_ctx_frame.
    take_drop_app_rewrite 0.
    iApply (wp_block_local_ctx with "Hf");[eauto..|].
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx_frame.
    erewrite wp_frame_rewrite.
    
    iDestruct (be_fundamental_local _ _ [_] _ locs with "Hi") as "Hl".
    done. done.
    iSpecialize ("Hl" $! _ _ (VAL_handle h0 :: n_zeros locs) with "Hf Hown Hall []").
    { iRight. iExists _. iSplit; first done. iSimpl.
      iSplitL.
      iExact "Hdummy". 
      iApply n_zeros_interp_values. }
    unfold interp_expression_closure_no_host. 
    iApply (wp_wand with "Hl").
    iIntros (w) "([Hw Hown] & Hf & Hall)".
    iSplitL "Hw". 
    iDestruct "Hw" as "[Hw | Hw]".
    iLeft. iExact "Hw". iRight.
    iDestruct "Hw" as (vs) "[-> H]".
    destruct vs; last done.
    iClear "H".
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    iExists _.
    iFrame.
        
    iCombine "Hown Hall Hg'" as "H".
    instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst :=  _ |} ⌝ ∗ _)%I). 
    iSplit; [done | iExact "H"]. 
    3: by iIntros "%".
    iIntros (w f1) "(-> & Hf & -> & Hown & Hall & Hg')". 

    iSimpl.
    rewrite (separate2 (AI_basic _)).
    iApply wp_wasm_empty_ctx. 
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hg' Hf".
    fold_const. iApply (wp_set_global with "[] Hf Hg'"). done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]". 
    iIntros (w) "(-> & Hg' & Hf)". 
    iSimpl.
    
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
    unfold handle_addr. rewrite Hoff N.add_0_r - Hbound. 
    iApply (wp_segfree with "[$Hf $Ha $Hs]") => //.
    rewrite map_length (length_bits _ T_i32) => //. rewrite Hbound. done. 
    iIntros "!> Ha". instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; [done | iExact "Ha"].
    iIntros (w) "[[-> Ha] Hf]". 
    iFrame.
    instantiate (1 := λ x, (⌜ x = trapV ⌝ ∗ _ ∨ ⌜ x = immV _ ⌝ ∗ _)%I).
    iRight. iSplit; first done.
    iCombine "Hf Hown Hall Hg' Hg Ha" as "H".
    iExact "H".
    iIntros (f1) "(Hf & -> & Hown & Hall & Hg')".
    iLeft. iSplit;first done. iCombine "Hf Hg'" as "H". iExact "H". 
    iIntros (w) "[(-> & Hf & Hg') | (-> & Hf & Hown & Hall & Hg' & Hg & Ha)]". 

    { (* Case 1: the adversary call failed *)
      iSimpl. iApply (wp_label_pull_nil _ _ _ _ _ (LH_base [] [])).
      iApply wp_wasm_empty_ctx.
      iApply (wp_wand with "[Hf]"). 
      iApply (wp_label_trap with "Hf"). done.
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]".
      iExists _. iFrame. iIntros "Hf".
      iApply (wp_wand with "[Hf]"). iApply (wp_frame_trap with "Hf").
      by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      iIntros (w) "[-> Hf]".
      iApply "HΦ". iLeft.
      iFrame. done.
    } 
    (* Case 2: the adversary call returned *)
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
    iRight. iSplit; first done. iFrame. iExists _. iFrame.
    iPureIntro. by right. 
  Qed. 

    
    
End Example02. 

Section Example02Host. 
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
    {| mod_types := [Tf [] []; Tf [T_handle] []];
       mod_funcs :=  [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [T_handle] ;
          modfunc_body := example_program
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
                           imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |};
                         {| imp_module := list_byte_of_string "Dummy";
                           imp_name := list_byte_of_string "dummy_handle";
                           imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_handle |} |};
                        {| imp_module := list_byte_of_string "Ret";
                          imp_name := list_byte_of_string "adv_call_witness";
                          imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |}
      ];
      mod_exports := []
    |}.

  Definition example_func_impts : seq.seq extern_t := [ET_func (Tf [T_handle] []) ].
  Definition example_glob_impts : seq.seq extern_t :=
    [ ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |};
      ET_glob {| tg_mut := MUT_mut; tg_t := T_handle |};
      ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |}
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


  
  Lemma example_module_typing :
    module_typing example_module (example_func_impts ++ example_glob_impts)
      []. 
  Proof. 
    exists [Tf [] []], [ ]. simpl.
    repeat split;eauto.
    { apply Forall2_cons. split;auto. cbn.
      repeat split;auto.
      unfold example_program. rewrite (separate9 (BI_const _)).
      eapply bet_composition'.
      { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. }
      { apply/b_e_type_checker_reflects_typing => /= ; by apply/eqP. } } 
    { apply Forall2_cons. split;auto.
      apply Forall2_cons. split;auto. } 
  Qed.

   Lemma module_restrictions_example:
    module_restrictions example_module.
  Proof.
    unfold module_restrictions.
    repeat split; try by exists [] => //=.
  Qed.


  Definition example_instantiate g :=
    [ ID_instantiate [0%N; 2%N] 0 [];
      ID_instantiate [] 1 [0%N; 1%N; 2%N; 3%N] ;
      H_get_global g ].

  Lemma instantiate_example g_ret wret g_wit wwit all name namew vs vsh adv_module:
     module_typing adv_module [] (example_func_impts ++ [ ET_glob {| tg_mut := MUT_mut; tg_t := T_handle |} ]) -> (* we assume the adversary module has an export of the type (handle) → () as well as one global variable containing a dummy handle *)
    mod_start adv_module = None -> (* that it does not have a start function *)
    module_restrictions adv_module -> (* that it adheres to the module restrictions (i.e. only constant initializers for globals) *)
    module_elem_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a table, there cannot be more initializers that its size *)
    module_data_bound_check_gmap ∅ [] adv_module -> (* if the adversary module declares a memory, there cannot be more initializers that its size *)
    typeof wret = T_i32 -> (* the imported return global has type i32 *)
    typeof wwit = T_i32 ->
    ⊢ {{{ ↪[frame] empty_frame ∗ interp_allocator all ∗ 
            (N.of_nat g_ret) ↦[wg] {| g_mut := MUT_mut; g_val := wret |} ∗
            (N.of_nat g_wit) ↦[wg] {| g_mut := MUT_mut; g_val := wwit |} ∗
            0%N ↪[vis] vs ∗
            1%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx g_ret) |} ∗
            2%N ↪[vis] vsh ∗
            3%N ↪[vis] {| modexp_name := namew; modexp_desc := MED_global (Mk_globalidx g_wit) |} ∗
            1%N ↪[mods] example_module ∗
            0%N ↪[mods] adv_module ∗
          na_own logrel_nais ⊤ 
      }}}
      ((example_instantiate g_ret,[]) : host_expr)
      {{{  λ v: language.val wasm_host_lang, ⌜ v = trapHV ⌝ ∗ (N.of_nat g_wit) ↦[wg] {| g_mut := MUT_mut; g_val := (xxv 0)|} ∨ ⌜v = immHV [xxv 0]⌝ ∨ ⌜v = immHV [xxv 42]⌝ }}} .
  Proof.
    iIntros (Hadvtype Hadvstart Hadvrestr Hadvelem Hadvdata Hwret Hwwit).
    iIntros "!>" (Φ) "(Hf & Hall & Hg & Hg' & Hexp0 & Hexp1 & Hexp2 & Hexp3 & Hmod & Hmodadv & Hown) HΦ".
    assert (exists exp_name ft exp_nameh ht, mod_exports adv_module = [ {| modexp_name := exp_name ; modexp_desc := MED_func ft |} ; {| modexp_name := exp_nameh ; modexp_desc := MED_global ht |} ]) as (exp_name & ft & exp_nameh & ht & Hexp). 
    { destruct Hadvtype as (fts & gts & Hadvtype).
      destruct adv_module; simpl in *.
      destruct Hadvtype as (_&_&_&_&_&_&_&_&Hadvtype).
      apply Forall2_length in Hadvtype as Hlen. 
      simpl in Hlen.
      destruct mod_exports eqn:Hexps => //. destruct l => //. destruct l => //. 
      apply Forall2_cons in Hadvtype as [Hadvtype1 Hadvtype].
      apply Forall2_cons in Hadvtype as [Hadvtype2 _]. 
      unfold module_export_typing in Hadvtype1.
      unfold module_export_typing in Hadvtype2. 
      destruct m => //. destruct m0 => //. simpl in Hadvtype1. simpl in Hadvtype2. 
      destruct modexp_desc as [x|x|x|x]; destruct x => //.
      destruct modexp_desc0 as [x|x|x|x]; destruct x => //. 
      eexists _,_,_,_. done. }
    iApply (wp_seq_host_nostart NotStuck with "[] Hmodadv [Hexp0 Hexp2]") => //.
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
        iSplit => //. iExists _; iFrame. 
        by rewrite Hexp. 
    }
    by iIntros "[% _]".
    iIntros (w) "(-> & _ & %advinst & Hres & Hexp0) Hmod0".
    unfold module_export_resources_host. rewrite Hexp.
    iSimpl in "Hexp0".
    iDestruct "Hexp0" as "([%name0 Hexp0] & [%name2 Hexp2] & _)".
    destruct ft. destruct ht. 
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
    apply Forall2_cons in Hadvexps as [Hadvexpg _]. 
    unfold module_export_typing in Hadvexpf.
    unfold module_export_typing in Hadvexpg. 
    simpl in Hadvexpf. simpl in Hadvexpg. 
    apply andb_true_iff in Hadvexpf as [Hn Hnth].
    apply andb_true_iff in Hadvexpg as [Hn0 Hnth0]. 
    destruct (nth_error fts n) eqn:Hfts => //.
    destruct (nth_error gts n0) eqn:Hgts => //. 
    apply b2p in Hnth. apply b2p in Hnth0. subst f g.
    rewrite Heqadvm. 
    unfold get_import_func_count, get_import_global_count, get_import_mem_count, get_import_table_count. simpl.
    repeat rewrite drop_0.
    rewrite nth_error_lookup in Hfts. rewrite nth_error_lookup in Hgts. 
    eapply Forall2_lookup_r in Himpf as (mf & Hmf & Htypf); last exact Hfts.
    eapply Forall2_lookup_r in Himpg as (mg & Hmg & Htypg); last exact Hgts. 
    destruct mf; simpl in Htypf. destruct mg; simpl in Htypg.
    destruct modfunc_type. destruct modglob_type. 
    destruct Htypf as (Hlef & Hnthf & Htypef).
    destruct Htypg as (Hleg & Hnthg & Htypeg). 
    unfold module_inst_resources_func.
    unfold module_inst_resources_glob. 

    apply lookup_lt_Some in Hmf as Hlenf.
    apply lookup_lt_Some in Hmg as Hleng. 
    rewrite Hlenadvfuncs in Hlenf.
    rewrite Heqadvm in Hadvglobinit.
    simpl in Hadvglobinit.
    assert (length glob_allocs = length mod_globals) as Hlenglob.
    { rewrite Hadvglobinit. 
      rewrite module_inst_global_init_length.
      rewrite map_length. done. }
    rewrite - Hlenglob in Hleng. 

    apply lookup_lt_is_Some in Hlenf as [? Hinstfunc]. 
    iDestruct (big_sepL2_lookup_acc with "Hadvfuncs") as "[Hfunc Hrestorefuncs]".
    done. done. iSimpl in "Hfunc".

    assert (Hleng' := Hleng). 
    apply lookup_lt_is_Some in Hleng' as [? Hinstglob].
    rewrite Hlenadvglobs in Hleng.
    apply lookup_lt_is_Some in Hleng as [? Hinstglob']. 
    iDestruct (big_sepL2_lookup_acc with "Hadvglobs") as "[Hgdumm Hrestoreglobs]".
    done. done. iSimpl in "Hgdumm".



    apply b2p in Hnthf.
    inversion Hnthg. subst tg_mut tg_t.

    assert (g_mut x0 = MUT_mut /\ typeof (g_val x0) = T_handle) as [Hxmut Hxtype]. 
    { rewrite Hadvglobinit in Hinstglob.
      apply module_inst_global_init_lookup in Hinstglob as [(v & g & Hinit & Hmodglob & ->) | Hmodglob].
      - unfold global_init_replace_single => /=.
        apply list_lookup_fmap_inv in Hmodglob as (? & -> & Hmodglob).
        rewrite Hmg in Hmodglob. inversion Hmodglob; subst x0. split => //=.
        destruct Hadvglobsr as [Htinit _].
        rewrite Heqadvm in Htinit; simpl in Htinit.
        specialize (Logic.eq_refl ((typeof_numerical <$> g_inits) !! n0)) as H.
        rewrite -> Htinit in H at 1.
        repeat rewrite list_lookup_fmap in H. rewrite Hinit in H.
        rewrite Hmg in H. simpl in H. by inversion H.
      - apply list_lookup_fmap_inv in Hmodglob as (? & -> & Hmodglob).
        rewrite Hmg in Hmodglob. inversion Hmodglob; subst x2. split => //=. } 

    destruct Hadvtypr as (Hadvtypes & Hadvtypfunc & Hadvtyptab & Hadvtypmem & Hadvtypglob & Hadvtypstart).
    rewrite Heqadvm in Hadvtypes; simpl in Hadvtypes. 
    rewrite - Hadvtypes in Hnthf.
    rewrite Hnthf.

    iDestruct (mapsto_ne with "Hg Hgdumm") as "%". 
    iDestruct (mapsto_ne with "Hg Hg'") as "%".
    iDestruct (mapsto_ne with "Hg' Hgdumm") as "%".
    do 2 rewrite nth_lookup. rewrite Hinstfunc Hinstglob'. 
        
    iApply (instantiation_spec_operational_start_seq with "Hf [Hmod Hexp0 Hexp1 Hexp2 Hexp3 Hg Hgdumm Hg' Hfunc]").
    2: exact example_module_typing.
    2: exact module_restrictions_example.
    done. iFrame. 
    iSplitR "Hg Hgdumm Hg' Hfunc". 
    unfold import_resources_host => //.
    instantiate (1 := [_;_;_;_]). iSimpl. iFrame. 
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
    constructor => //=.  constructor => //=. 
    unfold func_domcheck => //=. 
    simpl. set_solver. 
    iSplitR.
    repeat iSplit. 
    unfold import_tab_resources => //.
    iPureIntro. unfold tab_typecheck => //=. constructor => //. constructor => //.
    constructor => //. constructor => //. 
    iPureIntro. unfold tab_domcheck => //.
    iSplitR.
    repeat iSplit. 
    unfold import_mem_resources => //.
    iPureIntro. unfold mem_typecheck => //=. do 4 constructor => //.
    unfold mem_domcheck => //.
    instantiate (1 := <[ N.of_nat g_ret := _ ]> (<[ N.of_nat x1 := _ ]> (<[ N.of_nat g_wit := _ ]> ∅))).
    iSplitL. 
    unfold import_glob_resources.
    iApply big_sepM_insert.
    rewrite lookup_insert_ne => //. rewrite lookup_insert_ne => //.
    iFrame "Hg".
    iApply big_sepM_insert. 
    rewrite lookup_insert_ne => //.
    iFrame "Hgdumm".
    iApply big_sepM_singleton. iFrame. 
    unfold glob_typecheck => //. iPureIntro. split. constructor => //=.
    constructor => //=. 
    eexists _,_. 
    split; first by rewrite lookup_insert.
    split; first done. 
    unfold global_agree. simpl. by rewrite Hwret.
    constructor => //=.
    eexists _,_.
    split.
    rewrite lookup_insert_ne => //. rewrite lookup_insert => //.
    split; first done.
    unfold global_agree => //=.
    rewrite Hxmut Hxtype => //. 
    constructor => //=.
    eexists _,_.
    split. do 2 (rewrite lookup_insert_ne => //). rewrite lookup_insert => //.
    split; first done.
    unfold global_agree => //=. by rewrite Hwwit. 
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
    inversion Hextfunc. unfold ext_func_addrs in H2.
    simpl in H2.
    inversion H2; subst x x2. 
    iDestruct "Hfuncs" as "(Hfunc & _)". rewrite Hinst_types. iSimpl in "Hfunc".
    

    
    

    iDestruct "Himp" as "(Himp0 & Himp1 & Himp2 & Himp3 & _)".
    iDestruct "Hirwt" as "(Hirwtf & Hirwtm & Hirwtt & Hirwtg)".

    iDestruct "Hirwtf" as "(Hfs & %Hftypecheck & %Hfdomcheck)".
    unfold import_func_resources.
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hfs") as "Hfadv".
    iClear "Hsing".

     iDestruct "Hirwtg" as "(Hg & %Hgtypecheck & %Hgdomcheck)".
    unfold import_glob_resources.
    iDestruct (big_sepM_insert with "Hg") as "[Hg Hgs]".
    rewrite lookup_insert_ne => //. rewrite lookup_insert_ne => //.
    iDestruct (big_sepM_insert with "Hgs") as "[Hgdumm Hgs]".
    rewrite lookup_insert_ne => //.
                     
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hgs") as "Hg'".
    iClear "Hsing". 
    
    simpl in Hglobinit.


    iDestruct ("Hrestorefuncs" with "Hfadv") as "Hadvfuncs".
    iDestruct ("Hrestoreglobs" with "Hgdumm") as "Hadvglobs". 

    iApply weakestpre.fupd_wp.
    iMod (interp_instance_alloc [] ⊤ with "[] [] [] [] [] [Hadvfuncs Hadvtabs Hadvmems Hadvglobs]") as "(#Hi & _ & (#Hiresf & _ & _ & #Hiresg) & _)".
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
    iDestruct (big_sepL2_lookup with "Hiresg") as (τg) "[%Hgts' Hgdummv]".
    by rewrite Heqadvm - Hadvglobinit. by rewrite Heqadvm.
    rewrite Hgts in Hgts'.
    inversion Hgts'; subst τg.

    destruct (inst_globs inst) eqn:Hglobs => //.
    { inversion Hextglob. done. }
    destruct l => //.
    { inversion Hextglob. done. }
    destruct l => //.
    { inversion Hextglob. done. }
    inversion Hextglob. inversion H3; subst g g0 g1. 



    unfold check_start in Hstart. simpl in Hstart. rewrite Hfuncs in Hstart.
    move/eqP in Hstart. inversion Hstart; subst f0.

   

    
    iModIntro. 

    iApply wp_lift_wasm.
    rewrite - (app_nil_l [AI_invoke _]).
    
    iApply (wp_invoke_native with "Hf Hfunc") => //.
    iIntros "!> [Hf Hfunc]".
    iSimpl in "Ha". rewrite Hnthf.

    
    iApply (program_spec with "[$Hf $Hg $Hgdummv $Hall Hown $Hg' $Hi $Ha]") => //=; try by rewrite Hglobs.
    by rewrite Hfuncs. lia.
    rewrite Heqadvm.
    exact Htypef.
    iIntros (w) "[(-> & Hgwit) | (-> & Hf & Hown & Hall & Hgwit & H)]".
    iSimpl.
    iApply wp_get_global_trap_host.
    iApply "HΦ". iLeft. iSplit; first done. iFrame. 
    iDestruct "H" as (gf) "[Hg %Hgf]".
    iSimpl.
    iApply (wp_get_global_host _ _ _ _ [] with "Hg").
    iIntros "!> Hg".
    iApply "HΦ". iSimpl. iRight. 
    destruct Hgf as [-> | ->]; [by iLeft | by iRight].
  Qed. 

    
    
    
    
End Example02Host.
