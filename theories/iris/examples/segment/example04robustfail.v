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

Section Example04.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Context `{!wasmG Σ,
      !logrel_na_invs Σ, HHB: HandleBytes, !cinvG Σ, !cancelG Σ}.

(*
allocate a handle h with space for one i32
if allocation failed, return
write 42 to h
call an adversary function of type [handle] -> [], with argument h
read from h

Should be impossible to prove anything (adversary might have freed handle)
*)


  
  Definition example_program :=
    [
      BI_const (xx 1);
      BI_set_global 1;
      BI_const (xx 4);
      BI_segalloc;
      BI_tee_local 0;
      BI_isdummy;
      BI_if (Tf [] []) [ BI_const (xx 0) ; BI_set_global 0; BI_return ] [];
      BI_get_local 0;
      BI_const (xx 42);
      BI_segstore T_i32;
      BI_const (xx 0);
      BI_set_global 1;
      BI_get_local 0;
      BI_call 0;
      BI_const (xx 1);
      BI_set_global 1;
      BI_get_local 0;
      BI_segload T_i32;
      BI_set_global 0;
      BI_get_local 0;
      BI_segfree
    ].

  Definition example_function f :=
    [ AI_local 0 f [ AI_basic (BI_block (Tf [] []) example_program) ] ].


  Lemma program_spec f k k' f0 gv gv' a es i locs C all:
     (tc_label C) = [] ∧ (tc_return C) = None ->
    f.(f_inst).(inst_globs) !! 0 = Some k ->
    f.(f_inst).(inst_globs) !! 1 = Some k' ->
    f.(f_inst).(inst_funcs) !! 0 = Some a ->
    length f.(f_locs) >= 1 ->
    be_typing (upd_local_label_return C (T_handle :: locs) [[]] (Some [])) es (Tf [] []) ->

    ⊢ {{{ ↪[frame] f0 ∗ interp_allocator all 
         ∗ na_own logrel_nais ⊤
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_handle] []) locs es))
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
  (* WE EXPECT THIS TO FAIL *)
  Proof.
    iIntros (HC Hglob0 Hglob1 Hfunc Hlocs Hes Φ) "!> (Hf & Hall & Hown & #Hfinv & #Hi & Hg & Hg') HΦ".

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
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". 
    iApply (wp_get_local with "[] Hf").
    rewrite set_nth_read. 
    
    done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I). 
    2: by iIntros "[% _]". 
    iIntros (w) "[-> Hf]".
    iSimpl.
    iApply fupd_wp.
    iAssert (|={⊤}=> interp_value_handle (VAL_handle h) ∗ interp_allocator (allocator_insert (id h) (base h) (bound h) all))%I with "[Hs Ha Hall]" as "Hh0".

    { rewrite fixpoint_interp_value_handle_eq.
      iAssert (▷ (∃ tbs, ⌜ length tbs = N.to_nat (bound h) ⌝ ∗
                                          ↦[wss][ base h ] tbs ∗
                                          (∀ addr,
                                              ⌜ ((base h + addr) `mod` handle_size)%N = 0%N /\
                                                (addr + handle_size <= bound h)%N⌝ -∗
                                                  ⌜ ∃ addr' b,  (addr' < handle_size)%N /\
                                                                  tbs !! N.to_nat (addr + addr') = Some (b, Numeric)⌝ ∨ interp_value_handle (VAL_handle (handle_of_bytes (map fst (take (N.to_nat handle_size) (drop (N.to_nat addr) tbs))))))))%I with "[Hs]" as "HP".
      iNext. iExists _. unfold handle_addr.  rewrite Hoff N.add_0_r. iFrame.
      iSplit; first iPureIntro.
      rewrite map_length. rewrite (length_bits _ T_i32).
      rewrite Hbound. done. done. 
      
      iIntros (addr [Haddrlo Haddrhi]).
      iLeft. iPureIntro.
      rewrite Hbound in Haddrhi.
      simpl in Haddrhi.
      assert (H := hsnz). rewrite nat_bin in H. 
      assert (N.to_nat addr < 4); first lia.
      replace 4 with (length (bits (VAL_numeric (xx 42)))) in H0;
        last by erewrite (length_bits _ T_i32). 
      apply lookup_lt_is_Some in H0 as [??].
      exists 0%N, x.
      split. lia. 
      rewrite N.add_0_r.
      rewrite iris_fundamental_segstore.lookup_map.
      rewrite H0. done. 

      iMod (cinv_alloc with "HP") as (γ) "[#Hinv Hcown]".
      

      iDestruct "Hall" as (f1) "[Hblack Hmap]".
      iAssert ⌜ f1 !! (id h) = None ⌝%I with "[-]" as "%Hf1".
      { destruct (f1 !! (id h)) as [[[[??]?]?] |] eqn:Hf1 ; last done.
        iDestruct (big_sepM_lookup with "Hmap") as "Habs".
        done. iSimpl in "Habs". iDestruct "Habs" as (?) "(_ & Habs & _)".
        iDestruct (ghost_map_elem_combine with "Habs Ha") as "[Ha ->]".
        iDestruct (ghost_map_elem_valid with "Ha") as "%Habs".
        apply dfrac_valid_own_r in Habs. 
        done. } 

      
      iMod (ghost_map_insert_persist with "Hblack") as "[Hblack Hwhite]" ; first done.
      
      iSplitL "Hwhite".
      iExists _. iSplitR; first done. iRight.
      iExists γ, (base h), (bound h), (base h), (bound h), (DfracOwn 1).
      iFrame "Hinv Hwhite". iSplitL; iPureIntro; try lia.
      do 2 rewrite N.eqb_refl. done.
      iExists (<[ id h := _]> f1).
      iFrame "Hblack".
      iApply big_sepM_insert; first done.
      iSplitR "Hmap".
      iExists (Some (_,_)). iFrame. repeat iSplitL => //.
      iPureIntro. unfold allocator_insert => /=.
      rewrite lookup_insert Hbound . unfold handle_addr. rewrite Hoff N.add_0_r.
      done. unfold handle_addr. rewrite Hoff N.add_0_r. done. 
      iApply (big_sepM_impl with "Hmap").
      iIntros "!> !>" (k0 [[[??]?]?] Hk0) "H".
      iDestruct "H" as (y) "(%Halloc & Halloc & H)".
      iExists y. iFrame. iPureIntro.
      unfold allocator_insert => /=.
      rewrite lookup_insert_ne; first done.
      intros <-. by rewrite Hf1 in Hk0. } 

          
    iMod "Hh0" as "(#Hh0 & Hall)".
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
      iSpecialize ("Hl" $! _ _ (VAL_handle h :: n_zeros locs) with "Hf Hown Hall []").
      { iRight. iExists _. iSplit; first done. iSimpl.
        iSplitL.
        iExact "Hh0". 
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
    (* Where to get Ha and Hs from? Hh0 only knows the handle is safe to use, but it
       could have been freed *)
  Abort.
End Example04.
