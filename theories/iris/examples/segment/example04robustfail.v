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

Let us copy-paste the code from the equivalent functioning example, and see where the proof fails
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
(*    iSplitL "Ha Hs Hf".
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
    iApply (wp_segfree with "[$Hf $Ha $Hs]") => //.
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
  Qed. *)

    
    
End Example04. 

(*
Section Example04Host. 
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
                        {| imp_module := list_byte_of_string "Ret";
                          imp_name := list_byte_of_string "adv_call_witness";
                          imp_desc := ID_global {| tg_mut := MUT_mut; tg_t := T_i32 |} |}
      ];
      mod_exports := []
    |}.

  Definition example_func_impts : seq.seq extern_t := [ET_func (Tf [T_handle] []) ].
  Definition example_glob_impts : seq.seq extern_t :=
    [ ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |};
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
    [ ID_instantiate [0%N] 0 [];
      ID_instantiate [] 1 [0%N; 1%N; 2%N] ;
      H_get_global g ].

  Lemma instantiate_example g_ret wret g_wit wwit all name namew vs adv_module:
     module_typing adv_module [] (example_func_impts) -> (* we assume the adversary module has an export of the type (handle) → () as well as one global variable containing a dummy handle *)
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
            2%N ↪[vis] {| modexp_name := namew; modexp_desc := MED_global (Mk_globalidx g_wit) |} ∗
            1%N ↪[mods] example_module ∗
            0%N ↪[mods] adv_module ∗
          na_own logrel_nais ⊤ 
      }}}
      ((example_instantiate g_ret,[]) : host_expr)
      {{{  λ v: language.val wasm_host_lang, ⌜ v = trapHV ⌝ ∗ (N.of_nat g_wit) ↦[wg] {| g_mut := MUT_mut; g_val := (xxv 0)|} ∨ ⌜v = immHV [xxv 0]⌝ ∨ ⌜v = immHV [xxv 42]⌝ }}} .
  Proof.
    iIntros (Hadvtype Hadvstart Hadvrestr Hadvelem Hadvdata Hwret Hwwit).
    iIntros "!>" (Φ) "(Hf & Hall & Hg & Hg' & Hexp0 & Hexp1 & Hexp2 & Hmod & Hmodadv & Hown) HΦ".
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

    
    iDestruct (mapsto_ne with "Hg Hg'") as "%".
    rewrite nth_lookup. rewrite Hinstfunc. 
        
    iApply (instantiation_spec_operational_start_seq with "Hf [Hmod Hexp0 Hexp1 Hexp2 Hg Hg' Hfunc]").
    2: exact example_module_typing.
    2: exact module_restrictions_example.
    done. iFrame. 
    iSplitR "Hg Hg' Hfunc". 
    unfold import_resources_host => //.
    instantiate (1 := [_;_;_]). iSimpl. iFrame. 
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
    constructor => //=.  
    unfold func_domcheck => //=. 
    simpl. set_solver. 
    iSplitR.
    repeat iSplit. 
    unfold import_tab_resources => //.
    iPureIntro. unfold tab_typecheck => //=. constructor => //. constructor => //.
    constructor => //. 
    iPureIntro. unfold tab_domcheck => //.
    iSplitR.
    repeat iSplit. 
    unfold import_mem_resources => //.
    iPureIntro. unfold mem_typecheck => //=. do 3 constructor => //.
    unfold mem_domcheck => //.
    instantiate (1 := <[ N.of_nat g_ret := _ ]> ( (<[ N.of_nat g_wit := _ ]> ∅))).
    iSplitL. 
    unfold import_glob_resources.
    iApply big_sepM_insert.
    rewrite lookup_insert_ne => //. 
    iFrame "Hg".
    iApply big_sepM_singleton. iFrame. 
    unfold glob_typecheck => //. iPureIntro. split. constructor => //=.
    constructor => //=. 
    eexists _,_. 
    split; first by rewrite lookup_insert.
    split; first done. 
    unfold global_agree. simpl. by rewrite Hwret.
    constructor => //=.
    eexists _,_.
    split. (rewrite lookup_insert_ne => //). rewrite lookup_insert => //.
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
    inversion Hextfunc. unfold ext_func_addrs in H0.
    simpl in H0.
    inversion H0; subst x x0. 
    iDestruct "Hfuncs" as "(Hfunc & _)". rewrite Hinst_types. iSimpl in "Hfunc".
    

    
    

    iDestruct "Himp" as "(Himp0 & Himp1 & Himp2 & _)".
    iDestruct "Hirwt" as "(Hirwtf & Hirwtm & Hirwtt & Hirwtg)".

    iDestruct "Hirwtf" as "(Hfs & %Hftypecheck & %Hfdomcheck)".
    unfold import_func_resources.
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hfs") as "Hfadv".
    iClear "Hsing".

     iDestruct "Hirwtg" as "(Hg & %Hgtypecheck & %Hgdomcheck)".
    unfold import_glob_resources.
    iDestruct (big_sepM_insert with "Hg") as "[Hg Hgs]".
    rewrite lookup_insert_ne => //. 
                     
    iDestruct big_sepM_singleton as "[Hsing _]". 
    iDestruct ("Hsing" with "Hgs") as "Hg'".
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
    destruct l => //.
    { inversion Hextglob. done. }
    inversion Hextglob. inversion H1; subst g g0. 



    unfold check_start in Hstart. simpl in Hstart. rewrite Hfuncs in Hstart.
    move/eqP in Hstart. inversion Hstart; subst f0.

   

    
    iModIntro. 

    iApply wp_lift_wasm.
    rewrite - (app_nil_l [AI_invoke _]).
    
    iApply (wp_invoke_native with "Hf Hfunc") => //.
    iIntros "!> [Hf Hfunc]".
    iSimpl in "Ha". rewrite Hnthf.

    
    iApply (program_spec with "[$Hf $Hg $Hall Hown $Hg' $Hi $Ha]") => //=; try by rewrite Hglobs.
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

    
    
    
    
End Example04Host. *)
