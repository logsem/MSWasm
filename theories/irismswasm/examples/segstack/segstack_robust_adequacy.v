From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From MSWasm.iris.examples.segstack Require Import segstack_robust.
From MSWasm.iris.host Require Import iris_host.
From MSWasm Require Import opsem instantiation.
From MSWasm.iris.instantiation Require Import iris_instantiation.
From MSWasm.iris.logrel Require Import iris_logrel.
From MSWasm.iris.rules Require Import iris_rules proofmode iris_example_helper.
From MSWasm.iris.language Require Import iris_wp_def.

Class adv_module_record :=
  { adv_module : module;
    no_start : mod_start adv_module = None;
    restrictions : module_restrictions adv_module;
    elem_bounds : module_elem_bound_check_gmap ∅ [] adv_module;
    data_bounds : module_data_bound_check_gmap ∅ [] adv_module
  }.  

Section adequacy.
  Context `{HHB: HandleBytes}.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {na_invg: na_invG Σ}.
  Context {func_preg: gen_heapGpreS N function_closure Σ}.
  Context {tab_preg: gen_heapGpreS (N*N) funcelem Σ}.
  Context {tabsize_preg: gen_heapGpreS N nat Σ}.
  Context {tablimits_preg: gen_heapGpreS N (option N) Σ}.
  Context {mem_preg: gen_heapGpreS (N*N) byte Σ}.
  Context {memsize_preg: gen_heapGpreS N N Σ}.
  Context {memlimit_preg: gen_heapGpreS N (option N) Σ}.
  Context {seg_preg: gen_heapGpreS N (byte * btag) Σ}. 
  Context {cancel_tokens_preg: gen_heapGpreS N (gname * N * N * dfrac) Σ}. 
  Context {cinvg: cinvG Σ}.
  Context {all_preg: gen_heapGpreS N allocator_info Σ}. 
  Context {glob_preg: gen_heapGpreS N global Σ}.
  Context {locs_preg: gen_heapGpreS unit frame Σ}.
  Context {vis_preg: gen_heapGpreS N module_export Σ}.
  Context {ms_preg: gen_heapGpreS N module Σ}.
  Context {has_preg: gen_heapGpreS N host_action Σ}.


  Definition S := Build_store_record [] [] [] dummy_segment dummy_all [ {| g_mut := MUT_mut; g_val := xxv 0 |} ].
  Definition V (vs : module_export) : vi_store :=
    (<[0%N:=vs]>
                    (<[1%N:={|
                              modexp_name := ["000"%byte];
                              modexp_desc := MED_func (Mk_funcidx (N.to_nat 0))
                            |}]>
                       (<[2%N:={|
                                 modexp_name := ["000"%byte];
                                 modexp_desc := MED_func (Mk_funcidx (N.to_nat 1))
                               |}]>
                          (<[3%N:={|
                                    modexp_name := ["000"%byte];
                                    modexp_desc := MED_func (Mk_funcidx (N.to_nat 2))
                                  |}]>
                             (<[4%N:={|
                                       modexp_name := ["000"%byte];
                                       modexp_desc := MED_func (Mk_funcidx (N.to_nat 3))
                                     |}]>
                                (<[5%N:={|
                                          modexp_name := ["000"%byte];
                                          modexp_desc :=
                                            MED_func (Mk_funcidx (N.to_nat 4))
                                        |}]>
                                   (<[6%N:={|
                                             modexp_name := ["000"%byte];
                                             modexp_desc :=
                                               MED_func (Mk_funcidx (N.to_nat 5))
                                           |}]>
                                      (<[7%N:={|
                                                modexp_name := ["000"%byte];
                                                modexp_desc :=
                                                  MED_func (Mk_funcidx (N.to_nat 6))
                                              |}]>
                                         (<[8%N:={|
                                                   modexp_name := ["000"%byte];
                                                   modexp_desc :=
                                                     MED_func (Mk_funcidx (N.to_nat 7))
                                                 |}]>
                                            (<[9%N:={|
                                                      modexp_name := ["000"%byte];
                                                      modexp_desc :=
                                                        MED_global
                                                          (Mk_globalidx (N.to_nat 0))
                                                    |}]> ∅)))))))))).

  Definition M adv_module := [stack_module; adv_module; client_module].

  Definition exp_addrs := [0%N; 1%N; 2%N; 3%N; 4%N; 5%N; 6%N; 7%N; 8%N; 9%N].
  
  Lemma ex_adequacy `{Hadv:adv_module_record} he' S' V' M' HA' F vs :
    module_typing adv_module (fmap ET_func func_types) [ET_func (Tf [T_i32] [T_i32])] ->
    rtc erased_step (([(stack_adv_client_instantiate exp_addrs 0%N 1%N 2%N 0,[])],
                      (S,(V vs),(M adv_module),[],empty_frame)) : cfg wasm_host_lang)
        ([he'], (S',V', M', HA', F)) → 
    (∀ v, iris_host.to_val he' = Some v ->
          v = trapHV ∨ v = immHV [xxv 2] ).
  Proof.
    intros Hmodtyping Hstep.
    pose proof (wp_adequacy Σ wasm_host_lang NotStuck (stack_adv_client_instantiate exp_addrs  0%N 1%N 2%N 0,[])
                            (S,(V vs),(M adv_module),[],empty_frame)
    (λ v, v = trapHV ∨ v = immHV [xxv 2])).
    simpl in H.
    
    eassert _.
    { apply H.
      iIntros (Hinv κs).
      iMod (gen_heap_init (∅:gmap N function_closure)) as (func_heapg) "[Hfunc_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) funcelem)) as (tab_heapg) "[Htab_ctx _]".
      iMod (gen_heap_init (∅:gmap N nat)) as (tabsize_heapg) "[Htabsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ tablimits_preg (∅:gmap N (option N))) as (tablimit_heapg) "[Htablimit_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) byte)) as (mem_heapg) "[Hmem_ctx _]".
      iMod (gen_heap_init (∅:gmap N N)) as (memsize_heapg) "[Hmemsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ memlimit_preg (∅:gmap N (option N))) as (memlimit_heapg) "[Hmemlimit_ctx _]".
      apply (@gen_heapGpreS_heap) in seg_preg as seg_heapg.
      iMod (ghost_map_alloc (∅ : gmap N (byte * btag))) as (γseg) "[Hseg_ctx _]".
      apply (@gen_heapGpreS_heap) in all_preg as all_heapg.
      iMod (ghost_map_alloc (∅ : gmap N allocator_info)) as (γall) "[Hall_ctx _]".
      iMod (gen_heap_init (∅:gmap N global)) as (global_heapg) "[Hglobal_ctx _]".
      
      apply (@gen_heapGpreS_heap) in locs_preg as frame_heapg.
      iMod (ghost_map_alloc (∅:gmap unit frame)) as (γframe) "[Hframe_ctx _]".
      apply (@gen_heapGpreS_heap) in vis_preg as vis_heapg.
      iMod (ghost_map_alloc (∅:gmap N module_export)) as (γvis) "[Hvis_ctx _]".
      apply (@gen_heapGpreS_heap) in ms_preg as ms_heapg.
      iMod (ghost_map_alloc (∅:gmap N module)) as (γms) "[Hms_ctx _]".
      apply (@gen_heapGpreS_heap) in has_preg as has_heapg.
      iMod (ghost_map_alloc (∅:gmap N host_action)) as (γhas) "[Hhas_ctx _]".

      apply (@gen_heapGpreS_heap) in cancel_tokens_preg as cancel_tokens_heapg.
      iMod (ghost_map_alloc (∅: gmap N (gname * N * N * dfrac))) as (γtoks) "[Hblack _]". 

      iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".
      pose wasmg := WasmG Σ Hinv func_heapg tab_heapg tabsize_heapg 
                      tablimit_heapg mem_heapg memsize_heapg memlimit_heapg
                      γseg seg_heapg γall all_heapg 
                      global_heapg frame_heapg γframe.

      pose cancelg := CancelG Σ cancel_tokens_heapg γtoks.  
      
      pose visgg := HVisG Σ vis_heapg γvis.
      pose msgg := HMsG Σ ms_heapg γms.
      pose hasgg := HAsG Σ has_heapg γhas.
      pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
      assert (typeof (xxv 0) = T_i32) as Hwret;[auto|].
      assert (length exp_addrs = 10) as Hlen; first done.
      pose proof (instantiate_client (adv_module := adv_module) 0 (wret := xxv 0) (exp_addrs := exp_addrs) 0%N 1%N 2%N dummy_all Hlen Hmodtyping no_start restrictions elem_bounds data_bounds Hwret).

      iMod (ghost_map_insert tt empty_frame with "Hframe_ctx") as "[Hframe_ctx Hf]";[auto|].
      iMod (ghost_map_insert 9%N {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv9]";[auto|].
      iMod (ghost_map_insert 8%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 7)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv8]";[auto|].
      iMod (ghost_map_insert 7%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 6)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv7]";[auto|].
      iMod (ghost_map_insert 6%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 5)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv6]";[auto|].
      iMod (ghost_map_insert 5%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 4)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv5]";[auto|].
      iMod (ghost_map_insert 4%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 3)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv4]";[auto|].
      iMod (ghost_map_insert 3%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 2)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv3]";[auto|].
      iMod (ghost_map_insert 2%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 1)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv2]";[auto|].
      iMod (ghost_map_insert 1%N {| modexp_name := [Byte.x00]; modexp_desc := MED_func (Mk_funcidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv1]";[auto|].
      iMod (ghost_map_insert 0%N vs with "Hvis_ctx") as "[Hvis_ctx Hv0]";[auto|].
      iMod (ghost_map_insert 2%N client_module with "Hms_ctx") as "[Hms_ctx Hm2]";[auto|].
      iMod (ghost_map_insert 1%N adv_module with "Hms_ctx") as "[Hms_ctx Hm1]";[auto|].
      iMod (ghost_map_insert 0%N stack_module with "Hms_ctx") as "[Hms_ctx Hm0]";[auto|].
      iMod (gen_heap_alloc _ (N.of_nat 0) {| g_mut := MUT_mut; g_val := VAL_numeric (xx 0) |} with "Hglobal_ctx") as "[Hglobal_ctx [Hg _]]";[auto|].

      iDestruct (instantiate_client $! (λ v, ⌜v = trapHV ∨ v = immHV [xxv 2]⌝%I)
                  with "[$Hg $Hm1 $Hm0 $Hm2 $Hna $Hf Hv0 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hblack]") as "HH";
        [exact Hlen| eauto|apply no_start|apply restrictions|apply elem_bounds|apply data_bounds|eauto..].
      { iSplitL "Hv9".
        iExists _. iFrame.
        iSplitR "Hv8 Hblack".
        unfold own_vis_pointers.
        iSplitL "Hv0"; first by iExists _.
        iSplitL "Hv1"; first by iExists _.
        iSplitL "Hv2"; first by iExists _.
        iSplitL "Hv3"; first by iExists _.
        iSplitL "Hv4"; first by iExists _.
        iSplitL "Hv5"; first by iExists _.
        iSplitL "Hv6"; first by iExists _.
        iSplitL "Hv7"; first by iExists _.
        done.
        
        iSplitR "Hblack".
        - iExists _. done.
        - instantiate (1 := dummy_all). iSimpl. iExists ∅.
          iSplitL; last done. done.
      } 
      iDestruct ("HH" with "[]") as "HH";[auto|].
      iModIntro.
      iExists _,_. iFrame "HH". iFrame.
      done.
    }
    intros v Hval.
    destruct X. eapply adequate_result with (t2 := []).
    apply of_to_val in Hval as <-. eauto.
  Qed. 
          
End adequacy.

Theorem segstack_adequacy `{adv_module_record, HHB: HandleBytes}
  he' S' V' M' HA' F vs :
   module_typing adv_module (fmap ET_func func_types) [ET_func (Tf [T_i32] [T_i32])] ->
    rtc erased_step (([(stack_adv_client_instantiate exp_addrs 0%N 1%N 2%N 0,[])],
                      (S,(V vs),(M adv_module),[],empty_frame)) : cfg wasm_host_lang)
        ([he'], (S',V', M', HA', F)) → 
    (∀ v, iris_host.to_val he' = Some v -> v = trapHV ∨ v = immHV [xxv 2] ).
Proof.
  set (Σ := #[invΣ;
              na_invΣ;
              gen_heapΣ N function_closure;
              gen_heapΣ (N*N) funcelem;
              gen_heapΣ N nat;
              gen_heapΣ N (option N);
              gen_heapΣ (N*N) byte;
              gen_heapΣ N N;
              gen_heapΣ N (option N);
              gen_heapΣ N (byte * btag);
              gen_heapΣ unit N;
              gen_heapΣ unit (option N);
              gen_heapΣ N allocator_info;
              gen_heapΣ N (gname * N * N * dfrac);
              cinvΣ;
              gen_heapΣ N global;
              gen_heapΣ unit frame;
              gen_heapΣ N module_export;
              gen_heapΣ N module;
              gen_heapΣ N host_action
      ]).
  eapply (@ex_adequacy HHB Σ); typeclasses eauto.
Qed. 
