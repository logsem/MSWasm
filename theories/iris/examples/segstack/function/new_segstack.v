From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export segstack_common iris_fundamental proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stack.


 Context `{!wasmG Σ, HHB: HandleBytes}. 

Section code.

(*
  new_stack: [] -> [handle]
  locals declared: [handle]

  Attempts to create a new stack of i32s, by allocating a new handle.

  Can fail non-deterministically if segalloc fails.
  Upon successful segalloc, store the offset to the top element of the stack at the start of stack (0th cell).
  The maximum number of elements that can be stored is therefore 2^14-1.

  Returns the handle to the start of stack as i32, or dummy_handle if memory allocation fails. Cannot trap.

  Parameters/Locals:
  0     local variable, storing the address to the start of the page for return
 *)

Definition new_stack :=
  [
    i32const 65536 ;
    BI_segalloc ;
    BI_tee_local 0 ;
    BI_isdummy ;
    BI_if (Tf [] [T_handle]) [
        BI_get_local 0
      ] [
        BI_get_local 0 ;
        i32const 0;
        BI_segstore T_i32 ;
        BI_get_local 0 
      ]                             
  ].

  
End code.

Section specs.

Lemma spec_new_stack f0 (* len *) E: 
  ⊢ {{{
          ⌜ length (f_locs f0) >= 1 ⌝ ∗
  (*        ⌜ (page_size | len)%N ⌝ ∗ *)
            ↪[frame] f0 (* ∗
            ↦[wslength] len *)
    }}}
    to_e_list new_stack @ E
    {{{ v , ((⌜ v = immV [value_of_handle dummy_handle] ⌝ (* ∗
                      ↦[wslength] len *)) ∨
               (∃ h (* len' *), ⌜ v = immV [value_of_handle h]⌝ ∗
                             isStack h [] (* ∗
                             ↦[wslength] len' ∗
                             ⌜ (len' >= len)%N ⌝ *)
            )) ∗
              ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f1 = f_inst f0 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hflocs & Hframe) HΦ".
  (*assert (page_size | len)%N as Hlenmod => //=.
  apply divide_and_multiply in Hlenmod => //=. *)
  simpl. rewrite separate2.
  iApply wp_seq => /=.
  iDestruct (wp_segalloc with "[$Hframe]") as "HWP" => //.
  iIntros "!>" (w) "H". iExact "H".
  iSplitR; last first.
  
  (* { iSplitL ; by instantiate (1 := λ v, ⌜ v = immV _ ⌝%I ). } *)
  iSplitL "HWP".
  by iApply "HWP".
  2:{ iIntros "[Habs _]". iDestruct "Habs" as (?) "[% _]".  done. }
  - iIntros (w) "(H & Hf)".
    iDestruct "H" as (h) "(-> & H)".
    iSimpl. 
    rewrite separate2.
    iApply (wp_seq _ E _ (λ x, (⌜ x = immV [_] ⌝
                                        ∗ ↪[frame] {|
                                          f_locs := set_nth _ (f_locs f0) 0 _;
                                          f_inst := f_inst f0
                                        |} )%I) ).
    iSplitR.
  - iIntros "[%Habs _]" ; done.
  - iSplitL "Hf". 
    fold_const; iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite list_extra.cons_app.
    iApply wp_val_app => //=.
    iSplitR => //=.
    iIntros "!> [%Habs _]" ; done.
    fold_const; iApply (wp_set_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    rewrite - separate1.
    rewrite separate2.
    iApply wp_seq.
    iSplitR.
    instantiate (1 := (λ x, (⌜ if (is_dummy h) then
                                 x = immV [value_of_int 1]
                               else x = immV [value_of_int 0] ⌝ ∗
                                          ↪[frame] {| f_locs := set_nth _
                                                                  (f_locs f0) 0 _ ;
                                                     f_inst := f_inst f0 |})%I)).
    iIntros "[%Habs _]".
    by destruct (is_dummy h). 
  - instantiate (1 := VAL_handle h). iSplitL "Hf".
    destruct (is_dummy h) eqn:Hh.
    + apply is_dummy_true in Hh as ->.
      iApply (wp_isdummy_true with "Hf").
      done.
    + apply is_dummy_false in Hh.
      iApply (wp_isdummy_false with "Hf") => //.

  (* If *)
  - iIntros (w) "[%Hw Hf]".
    destruct w ; try by destruct (is_dummy h).
    destruct l ; first by destruct (is_dummy h).
    destruct l ; last by destruct (is_dummy h).
    iSimpl.
    destruct (is_dummy h) eqn:Hv. 
    + (* segalloc failed *)
      apply is_dummy_true in Hv as ->. 
      inversion Hw ; subst v.
      iApply (wp_if_true with "Hf").
      intro.
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
      iApply wp_wand_r. 
      iSplitL "Hf".
      (*iApply (wp_block with "Hf") => //=. 
      iIntros "!> Hf". *)
      iApply wp_wasm_empty_ctx.
      iApply (wp_block_ctx with "Hf"). done. done. done. done.
      iIntros "!> Hf".
      iApply (wp_label_push_nil _ _ _ _ 0 (LH_base [] []) with "[Hf]") ;
        last unfold lfilled, lfill.
      simpl.
      rewrite (separate1 (AI_basic (BI_get_local 0))).
      iApply wp_seq_ctx; eauto.
      iSplitL ""; last first.
      iSplitL. 
      iApply (wp_get_local with "[] Hf").
      simpl. by rewrite set_nth_read.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (w) "[-> Hf]". iSimpl.
      fold_const.
      iApply (wp_val_return with "Hf") => //.
      iIntros "Hf". iApply wp_value.
      unfold IntoVal. erewrite language.of_to_val => //.
      instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
      by iFrame. by iIntros "[% _]".
      iIntros (v) "[-> Hf]".
      iApply "HΦ". iSplitR "Hf"; last by iExists _; iFrame. iLeft.  done. 
    + (* grow_memory succeeded *)
      inversion Hw ; subst v.
      iApply (wp_if_false with "Hf"). done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).

      iDestruct "H" as "[ %Hdum | (Hid & %Hbound & %Hoff & %Hval & Hs)]".
      subst h. unfold handle_eqb, dummy_handle in Hv; simpl in Hv. done.
      (* assert (len `div` page_size <= 65535)%N as Hpagebound.
      { unfold mem_in_bound, page_limit in Hbound.
        simpl in Hbound.
        by lias.
      }
      assert (len <= ffff0000)%N as Hlenbound.
      { rewrite <- Hlenmod.
        remember (len `div` page_size)%N as pagenum.
        replace page_size with 65536%N => //.
        unfold ffff0000.
        by lias.
      }
      unfold page_size at 3.
      replace (N.to_nat (_ * (64 * 1024))) with (4 + N.to_nat (65532)) ; last done. *)
      assert (Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m 65536) = 65536%N); first done.
      rewrite H.
      assert (N.to_nat 65536 = 4 + N.to_nat 65532); first done.
      rewrite H0.
      rewrite repeat_app.
      unfold repeat at 1. 
      rewrite - separate4.
      iDestruct (wss_append with "Hs") as "[H1 Hb]".
      iDestruct (wss_append with "Hb") as "[H2 Hb]".
      iDestruct (wss_append with "Hb") as "[H3 Hb]".
      iDestruct (wss_append with "Hb") as "[H4 Hb]".
      iAssert (↦[wss][ base h] [(#00%byte, Numeric) ; (#00%byte, Numeric) ; (#00%byte, Numeric) ; (#00%byte, Numeric)])%I with "[H1 H2 H3 H4]" as "Hbs".
      { unfold seg_block_at_pos, big_opL.
        repeat rewrite of_nat_to_nat_plus ; rewrite N.add_0_r.
        replace (base h + 1 + 1)%N with (base h + N.of_nat 2)%N ; last lia.
        replace (base h + N.of_nat 2 + 1)%N with (base h + N.of_nat 3)%N ; last lia.
        iFrame. }
(*      remember (Wasm_int.Int32.repr (ssrnat.nat_of_bin (len `div` page_size))) as c. *)
      iApply wp_wand_r.        
      (*      instantiate (1 := λ x, ((⌜ x = immV [value_of_uint len] ⌝ ∗ N.of_nat n↦[i32][ len ] (Wasm_int.Int32.repr (Z.of_N len))) ∗ ↪[frame] {| f_locs := set_nth (VAL_int32 c) (f_locs f0) 0 (VAL_int32 (Wasm_int.Int32.imul c (Wasm_int.Int32.repr 65536))); f_inst := f_inst f0 |} )%I). *)
      iSplitL "Hf Hbs Hid".
      * { iApply wp_wasm_empty_ctx.
          iApply (wp_block_ctx with "Hf"). done. done. done. done.
          iIntros "!> Hf".
          iApply (wp_label_push_nil _ _ _ _ 0 (LH_base [] []) with "[Hf Hbs Hid]") ;
            last unfold lfilled, lfill.
          simpl.
          rewrite (separate1 (AI_basic (BI_get_local 0))).
          iApply wp_seq_ctx; eauto.
          iSplitL ""; last first.
          - iSplitL "Hf".
            iApply (wp_get_local with "[] [$Hf]") => /=; first by rewrite set_nth_read.
            instantiate (1 := (λ x, ( ⌜x = immV [_] ⌝)%I)) => //=.
          - 2: { simpl. by iIntros "(%HContra & _ )". }
            iIntros (w) "[-> Hf]".
            unfold of_val, fmap, list_fmap.
            simpl. 
            rewrite (separate3 (AI_handle _)).
            iApply wp_seq_ctx.
            iSplitL ""; last first.
          - iSplitL.
            unfold i32const; fold_const; iApply (wp_segstore with "[Hf Hbs Hid]"); last first.
            unfold handle_addr. rewrite Hoff N.add_0_r.
            iFrame. 
            instantiate (1 := λ x, ( ⌜ x = immV _ ⌝ ∗ _)%I ).
            iIntros "!> H". iSplit; first done. iExact "H".
            rewrite Hoff Hbound. done. done. done. done. done.
          - 2: { simpl. by iIntros "([%HContra _] & _ )". }
            iIntros (w) "[(-> & Hid & Hbs) Hf]".
            unfold of_val, fmap, list_fmap.
            iSimpl.
            rewrite (separate1 (AI_basic _)).
            iApply wp_seq_ctx.
            iSplitR; last first.
            iSplitL "Hf".
            iApply (wp_get_local with "[] [$Hf]").
            simpl. rewrite set_nth_read. done.
            instantiate (1 := (λ x, (⌜ x = immV _ ⌝)%I)). done.
            2: by iIntros "[% _]".
          - iIntros (w) "[-> Hf]".
            simpl.
            iApply (wp_val_return with "Hf").
            done.
            iIntros "Hf".
            rewrite app_nil_r app_nil_l.
            iApply wp_value.
            unfold IntoVal.
            apply language.of_to_val.
            done.
            instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ id h↣[allocated] _ ∗ ↦[wss][handle_addr h] _ ∗ ↪[frame] _)%I).
            iFrame. iSplit; first done. unfold handle_addr; rewrite Hoff N.add_0_r.
            iExact "Hbs". }
      * iIntros (w) "(-> & Hid & Hbs & Hf)".
        iApply "HΦ".
        iSplitR "Hf"; last first.
        { iExists _.
          by iSplitL "Hf" => //.
        }
        iRight.
        iExists _. 
        iSplit; first done.
        unfold isStack.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done. 
        rewrite Hbound.
        iFrame "Hid".
        iSplitL "Hbs".
        iApply i32_wss.
        unfold handle_addr; rewrite Hoff N.add_0_r. simpl. done.
        iSimpl. 
        iSplit ; first done.
        iExists _. replace (base h + 0 + 4)%N with (base h + 1 + 1 + 1 + 1)%N; last lia.
        iFrame "Hb".
        rewrite repeat_length. iPureIntro. by rewrite N2Nat.id.
Qed.
        
End specs.

Section valid.
  Context `{!logrel_na_invs Σ, !cinvG Σ, cancelg: cancelG Σ}.
  Set Bullet Behavior "Strict Subproofs".

  Lemma interp_value_of_int i :
    ⊢ @interp_value Σ _ _ _ _ T_i32 (value_of_int i).
  Proof.
    iIntros "". unfold interp_value. simpl.
    iExists _. eauto. Qed.

  Lemma interp_value_of_uint i :
    ⊢ @interp_value Σ _ _ _ _ T_i32 (value_of_uint i).
  Proof.
    iIntros "". unfold interp_value. simpl.
    iExists _. eauto. Qed.

  (*
  Lemma valid_new_stack t funcs :
    let i0 := {| inst_types := [Tf [] [T_i32]; Tf [T_i32] [T_i32]; Tf [T_i32; T_i32] []];
                     inst_funcs := funcs;
                     inst_tab := [t];
                     inst_memory := [];
                     inst_globs := []
              |} in
    na_inv logrel_nais stkN (stackModuleInv (λ (a : handle) (b : seq.seq i32), isStack a b) (λ n : nat, ↦[wslength]N.of_nat n)) -∗
    interp_closure_native i0 [] [T_i32] [T_i32] (to_e_list new_stack) [].
  Proof.
    iIntros "#Hstk".
    iIntros (vcs f) "#Hv Hown Hf".
    iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8;subst;simpl.
    iApply (wp_frame_bind with "[$]");auto.
    iIntros "Hf".
    match goal with | |- context [ [AI_label _ _ ?l] ] => set (e:=l) end.
    build_ctx e.
    iApply wp_label_bind.
    subst e.
    iDestruct "Hv" as "[%Hcontr|Hws]";[done|iDestruct "Hws" as (ws) "[%Heq Hws]"].
    iDestruct (big_sepL2_length with "Hws") as %Hlen. inversion Heq. destruct ws;[|done]. simpl.
    iApply fupd_wp.
    iMod (na_inv_acc with "Hstk Hown") as "(>Hstkres & Hown & Hcls)";[solve_ndisj..|].
    iDestruct "Hstkres" as (len) "[% [Hlen Hstkres]]".
    iApply (spec_new_stack with "[$Hf $Hlen]") ;[auto|].
    iModIntro.
    iIntros (v) "HH".
    iDestruct "HH" as "[Hcases Hf]".
    iDestruct "Hf" as (f') "[Hf %Hfinst]". simpl in Hfinst.
    iAssert (⌜const_list (iris.of_val v)⌝)%I as %Hval.
    { iDestruct "Hcases" as "[[-> Hm] | [-> [Hs Hm]]]";auto. }
    apply const_list_to_val in Hval as Hvs. destruct Hvs as [vs Hvs].
    rewrite to_of_val in Hvs.
    iAssert (⌜length vs = 1⌝)%I as %Hlenvs.
    { inversion Hvs;subst v.
      iDestruct "Hcases" as "[[%eq1 Hm] | [%eq1 [Hs Hm]]]";inversion eq1;auto. }
    iAssert (interp_values [T_i32] v) as "#Hv".
    { iDestruct "Hcases" as "[[-> Hm] | [-> [Hs Hm]]]"; iSimpl.
      iExists _. iSplit;eauto. iSplit =>//. iApply interp_value_of_int.
      iExists _. iSplit;eauto. iSplit =>//. iApply interp_value_of_uint.
    }
    iApply (wp_val_return with "[$]");auto.
    iIntros "Hf /=".
    iApply wp_value;[rewrite app_nil_r;eapply of_to_val;eauto;eapply to_of_val|].
    iExists _. iFrame. iIntros "Hf".
    
    iApply fupd_wp.
    iMod ("Hcls" with "[$Hown Hcases Hstkres]") as "Hown".
    { iNext.
      iDestruct "Hcases" as "[[Heq Hm] | [% [Hs Hm]]]".
      - iExists _. iFrame. auto.
      - iExists _.
        rewrite <- (N2Nat.id page_size), <- Nat2N.inj_add.
        iFrame "Hm". repeat iSplit.
        + iPureIntro. rewrite N2Nat.id Nat2N.inj_add N2Nat.id.
          apply N.divide_add_r;auto. apply N.divide_refl.
        + iDestruct "Hstkres" as (l Hmul) "Hstkres".
          rewrite N2Nat.id in Hmul. iExists (N.of_nat len :: l).
          iSplit.
          { iPureIntro. rewrite Nat2N.inj_add N2Nat.id. constructor. auto. }
          iSimpl. iFrame. iExists _. iFrame. }
    iModIntro.
    inversion Hvs;subst v.
    iApply (wp_wand _ _ _ (λ v, ⌜v = immV vs⌝ ∗ _)%I with "[Hf]").
    { iApply (wp_frame_value with "[$]");eauto. apply to_of_val. simpl.
      rewrite v_to_e_length. auto. }
    iIntros (v) "[-> Hf]". iFrame.
    iLeft. iRight. iFrame "#". 
  Qed.
*)
End valid.


End stack.    
      

