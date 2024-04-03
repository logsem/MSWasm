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

Section Buffer_code.


Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Context `{!wasmG Σ,
      !logrel_na_invs Σ, HHB: HandleBytes, !cinvG Σ, !cancelG Σ}.


  Definition local_h := 0.
  Definition local_hpub := 1.
  Definition fun_adv := 0.
  Definition global_result := 0.
  
  Definition buffer_program :=
    [
      BI_const (xx 8);
      BI_segalloc;
      BI_set_local local_h;
      BI_get_local local_h;
      BI_const (xx 42);
      BI_segstore T_i32;
      BI_get_local local_h;
      BI_const (xx 4);
      BI_const (xx 4);
      BI_slice;
      BI_set_local local_hpub;
      BI_get_local local_hpub;
      BI_call fun_adv;
      BI_get_local local_h;
      BI_segload T_i32;
      BI_set_global global_result (* In order to later observe the return value, we store it in a global variable that the host code can examine *)
    ].

(**   (* Place the buffer code in the environment in which functions are executed *)
  Definition buffer_function f :=
    [ AI_local 0 f [ AI_basic (BI_block (Tf [] []) buffer_program) ] ]. *)


  (* Spec for the buffer example's code. Most premises will be provided later by instantiation *) 
  Lemma buffer_spec f k gv a es i locs C all:
    (tc_label C) = [] ∧ (tc_return C) = None -> (* Context C is shallow *)
    f.(f_inst).(inst_globs) !! fun_adv = Some k -> (* Desired global variable in the store *)
    f.(f_inst).(inst_funcs) !! global_result = Some a -> (* Desired function in the store *)
    length f.(f_locs) >= 2 -> (* At least two spots available for local variables *)
    be_typing (upd_local_label_return C (T_handle :: locs) [[]] (Some [])) es (Tf [] []) -> (* Adversary function typechecks *)

    ⊢ {{{ ↪[frame] f (* We own a frame *)
         ∗ interp_allocator all (* Our allocator is safe to use *)
         ∗ na_own logrel_nais ⊤ (* We can open non-atomic invariants *)
         ∗ na_inv logrel_nais (wfN (N.of_nat a)) ((N.of_nat a) ↦[wf] (FC_func_native i (Tf [T_handle] []) locs es)) (* We own the code for the adversary function inside a non-atomic invariant *)
         ∗ interp_instance C [] i (* Our instance is safe to use *)
         ∗ N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := gv |} (* We own global variable k *)
      }}}
       to_e_list buffer_program
       {{{ v, (∃ f, ↪[frame] f) ∗ (* we get a frame back, and *)
                (⌜ v = trapV ⌝ (* either we trap, or *)
                 ∨
               ⌜ v = immV [] ⌝ ∗ (* no return value *)

                       na_own logrel_nais ⊤ ∗ (* we get the non-atomic invariant token back *)
                       (∃ all, interp_allocator all) ∗ (* our allocator is still safe to use *)
                       N.of_nat k ↦[wg] {| g_mut := MUT_mut ; g_val := (xxv 42) |} (* and our global variable stores 42 *))
      }}}.
  Proof.
    iIntros (HC Hglob0 Hfunc Hlocs Hes Φ) "!> (Hf & Hall & Hown & #Hfinv & #Hi & Hg) HΦ".

(*    iApply (wp_frame_bind with "Hf"); first done.
    iIntros "Hf". 
    rewrite - (app_nil_l [AI_basic _]).
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf".
    iApply wp_wasm_empty_ctx.
    iApply wp_label_push_nil.
    iApply wp_ctx_bind. done.  *)
    
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
    unfold local_h; lia.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]".
    iSimpl.  rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    unfold local_h => /=. by rewrite set_nth_read. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite (separate3 (AI_handle _)).
        
    iDestruct "Hh" as "[-> | (Ha & %Hbound & %Hoff & %Hvalid & Hs)]".
    { (* Case 1: segalloc failed: we trap safely *)

      iApply (wp_wand with "[Hf]"). iApply wp_seq_trap.
      iFrame. iIntros "Hf". 

      fold_const. iApply (wp_segstore_failure1 with "[$Hf]") => //.
      by left.
      
      iIntros (w) "[-> Hf]".
      iApply "HΦ". iSplitL; last by iLeft. by iExists _. } 

    (* Case 2: segalloc succeeded *)


    iSimpl in "Hs".
    rewrite (separate4 (_, _)).
    iDestruct (big_sepL_app with "Hs") as "[Hsecret Hpublic]". (* Separating our segment memory resources into secret and public *)

    rewrite (separate3 (AI_handle _)). 
    
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf Ha Hsecret".
    fold_const.
    replace (base h) with (handle_addr h); last by unfold handle_addr; rewrite Hoff; lia.
    iApply (wp_segstore with "[$Ha $Hsecret $Hf]") => //.
    rewrite Hoff Hbound. simpl. lia.
    iIntros "!> H". instantiate (1 := λ x, (⌜ x = immV [] ⌝ ∗ _)%I).
    iSplit; [done | iExact "H"].
    2: by iIntros "[[% _] _]".
    iIntros (w) "[(-> & Ha & Hsecret) Hf]". iSimpl.

    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    simpl. rewrite set_nth_read => //.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite (separate4 (AI_handle _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". fold_const. iApply (wp_slice with "Hf").
    simpl. unfold slice_handle. rewrite Hbound. done.
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]".
    iSimpl.

    rewrite (separate2 (AI_handle _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". fold_const. iApply (wp_set_local with "[] Hf").
    unfold local_hpub, local_h => /=. destruct (f_locs f) => //. simpl in Hlocs; lia. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]".
    iSimpl. iSimpl in "Hf". rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    unfold local_h, local_hpub => /=. by rewrite set_nth_read. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]".
    iSimpl. 


    
    iApply fupd_wp.
    remember {| base := base h + 4; offset := offset h; bound := 4; valid := valid h; id := id h|} as h0.

    iAssert (|={⊤}=> interp_value_handle (VAL_handle h0) ∗ interp_allocator (allocator_insert (id h) (base h) (bound h) all) ∗  id h↣[allocated]{(DfracOwn (1 / 2))}Some (handle_addr h, 8%N) )%I with "[Hpublic Hall Ha]" as "Hh0".

    { rewrite fixpoint_interp_value_handle_eq.
      iAssert (▷ (∃ tbs, ⌜ length tbs = N.to_nat (bound h0) ⌝ ∗
                                          ↦[wss][ base h0 ] tbs ∗
                                          (∀ addr,
                                              ⌜ ((base h0 + addr) `mod` handle_size)%N = 0%N /\
                                                (addr + handle_size <= bound h0)%N⌝ -∗
                                                  ⌜ ∃ addr' b,  (addr' < handle_size)%N /\
                                                                  tbs !! N.to_nat (addr + addr') = Some (b, Numeric)⌝ ∨ interp_value_handle (VAL_handle (handle_of_bytes (map fst (take (N.to_nat handle_size) (drop (N.to_nat addr) tbs))))))))%I with "[Hpublic]" as "HP".
      iNext. iExists _.
      iSimpl in "Hpublic".
      iSplit; last first. iSplitL.
      instantiate (1 := [_;_;_;_]).
      rewrite Heqh0; iSimpl.
      iDestruct "Hpublic" as "(H1 & H2 & H3 & H4 & _)".
      iSplitL "H1". rewrite Nat.add_0_r. rewrite N2Nat.inj_add. done.
      iSplitL "H2". rewrite N2Nat.inj_add. repeat rewrite - Nat.add_assoc. done.
      iSplitL "H3". rewrite N2Nat.inj_add. repeat rewrite - Nat.add_assoc. done.
      iSplitL; last done. rewrite N2Nat.inj_add. repeat rewrite - Nat.add_assoc. done. 
      iIntros (addr [Haddrlo Haddrhi]).
      iLeft. iPureIntro. exists 0%N, #00%byte.
      split. assert (H:= hsnz). rewrite nat_bin in H. lia.
      rewrite N.add_0_r. 

      assert (N.to_nat addr < N.to_nat (bound h0)).
      subst h0.
      assert (H:=hsnz). rewrite nat_bin in H. simpl. simpl in Haddrhi. lia.
      remember (N.to_nat addr) as x.
      destruct x => //.  destruct x => //.  destruct x => //. destruct x => //.
      subst h0; simpl in H. lia.
      iPureIntro. simpl. by subst h0. 

      iMod (cinv_alloc with "HP") as (γ) "[#Hinv Hcown]".
      
      iDestruct "Hall" as (f1) "[Hblack Hmap]".
      iAssert ⌜ f1 !! (id h) = None ⌝%I with "[-]" as "%Hf1".
      { destruct (f1 !! (id h)) as [[[[??]?]?] |] eqn:Hf1 ; last done.
        iDestruct (big_sepM_lookup with "Hmap") as "Habs".
        done. iSimpl in "Habs". iDestruct "Habs" as (?) "(_ & Habs & _)".
        iDestruct (ghost_map_elem_combine with "Habs Ha") as "[Ha %]".
        iDestruct (ghost_map_elem_valid with "Ha") as "%Habs".
        apply dfrac_valid_own_r in Habs. 
        done. } 

      
      iMod (ghost_map_insert_persist with "Hblack") as "[Hblack Hwhite]" ; first done.
      
      iSplitL "Hwhite".
      iExists _. iSplitR; first done. iRight.
      iExists γ, (base h0), (bound h0), (base h), (bound h), (DfracOwn (1 / 2)).
      replace (id h0) with (id h); last by subst h0. 
      iFrame "Hinv Hwhite". iSplitL; iPureIntro.
      subst h0; simpl. rewrite Hbound. simpl. rewrite Bool.andb_false_r.
      by right.
      subst h0 => /=. rewrite Hbound. simpl. lia.

      iDestruct "Ha" as "[Ha Hasave]". iFrame "Hasave". 
      iExists (<[ id h0 := _]> f1).
      replace (id h0) with (id h); last by subst h0. 

      iFrame "Hblack".
      iApply big_sepM_insert; first done.
      iSplitR "Hmap".
      iExists (Some (_,_)). iFrame. repeat iSplitL => //.
      iPureIntro. unfold allocator_insert => /=.
      rewrite lookup_insert Hbound. unfold handle_addr. rewrite Hoff.
      rewrite N.add_0_r. done.
      unfold handle_addr. rewrite Hoff N.add_0_r. done. 
      iApply (big_sepM_impl with "Hmap").
      iIntros "!> !>" (k0 [[[??]?]?] Hk0) "H".
      iDestruct "H" as (y) "(%Halloc & Halloc & H)".
      iExists y. iFrame. iPureIntro.
      unfold allocator_insert => /=.
      rewrite lookup_insert_ne; first done.
      intros <-. by rewrite Hf1 in Hk0. } 

          
    iMod "Hh0" as "(#Hh0 & Hall & Hasave)".
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
      iSplitL "Hown Hall". 
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
      
      iCombine "Hown Hall" as "H".
      instantiate (1 := λ x, (⌜ x = {| f_locs := _ ; f_inst :=  _ |} ⌝ ∗ _)%I). 
      iSplit; [done | iExact "H"]. 
      3: by iIntros "%".
      iIntros (w f1) "(-> & Hf & -> & Hown & Hall)".

      iDestruct "Hall" as (all0 f1) "[Hbl Hall]".
      rewrite fixpoint_interp_value_handle_eq.
      iDestruct "Hh0" as (h1) "(%Hh & [%Habs | (%γ & %base' & %bound' & %base_all & %bound_all & %q & %Hq & Hw & %Hbase_all & %Hbase' & %Hbound_all & %Hbound' & Hinv)])";
        inversion Hh; subst; first by rewrite Hvalid in Habs.
      iDestruct (gamma_agree with "Hw Hbl") as "%Hf1".
      rewrite - (insert_delete _ _ _ Hf1). 
      iDestruct (big_sepM_insert with "Hall") as "[H Hrestore]"; first by rewrite lookup_delete.
      iSimpl in "H". iDestruct "H" as (y) "(%Hall & Ha & Hy)".
      iDestruct (ghost_map_elem_combine with "Ha Hasave") as "[Ha ->]". 
      destruct (_ && _).
      { subst q. iDestruct (ghost_map_elem_valid with "Ha") as "%" => //. }
      destruct Hq; subst q. { iDestruct (ghost_map_elem_valid with "Ha") as "%" => //. }
      rewrite dfrac_op_own.
      rewrite Qp_half_half.
      iDestruct "Hy" as "(-> & -> & Htok)".

      
      iSimpl.

      iApply wp_wasm_empty_ctx. 

    
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf". iApply (wp_get_local with "[] Hf").
    unfold local_h, local_hpub => /=. destruct (f_locs f) => //. 
    by instantiate (1 := λ x, ⌜ x = immV _ ⌝ %I).
    2: by iIntros "[% _]".
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite (separate2 (AI_handle _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hsecret Hf Ha". 
    
      
    iApply (wp_segload with "[$Ha $Hsecret $Hf]") => //.
    2:{ rewrite map_map. rewrite map_id. done. } 
    done. rewrite Hoff Hbound. simpl. lia.
    iIntros "!> H".
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ _)%I).
    iSplit; [done | iExact "H"].
    2: by iIntros "[[% _] _]".
    iIntros (w) "[(-> & Ha & Hs) Hf]". iSimpl.
(*     rewrite (separate2 (AI_basic _)).
    iApply wp_seq.
    iSplitR; last first.
    iSplitL "Hf Hg".  *)
    fold_const.
    iApply (wp_wand with "[Hf Hg]").
    iApply (wp_set_global with "[] Hf Hg").
    done. by instantiate (1 := λ x, ⌜ x = immV [] ⌝%I).
    iIntros (w) "(-> & Hg & Hf)".
    instantiate (1 := λ x, ((∃ f, ↪[frame] f) ∗ (⌜ x = trapV ⌝ ∨ ⌜ x = immV _ ⌝ ∗ _))%I).
    iSplitL "Hf"; first by iExists _. iRight. iSplit; first done.
    iDestruct "Ha" as "[Ha Ha']". 
    iAssert (∃ all1, interp_allocator all1)%I with "[Ha' Htok Hrestore Hbl]" as "Hall".
    { iExists all0. (* {| allocated := <[ id h := None ]> (allocated all0); next_free := next_free all0 |}. *)
      iExists _. iFrame.
      iApply (big_sepM_insert with "[Ha' Htok $Hrestore]"); first by rewrite lookup_delete.
      iSimpl.
      iExists _. iFrame. iFrame. iSplit; last done. iPureIntro. simpl. done. 
    }
    iCombine "Hs Hown Hall Hg Ha" as "H".
    iExact "H".


    iIntros (f1) "(Hf & -> & Hown & Hall)".
    iSplitL "Hf"; first by iExists _. by iLeft.

    

    iIntros (w) "[Hf [-> | (-> & Hs & Hown & Hall & Hg & Ha)]]"; iApply "HΦ"; iFrame.
    by iLeft.
    iRight. iSplit; first done. iFrame. 
  Qed. 

    
    
End Buffer_code. 

