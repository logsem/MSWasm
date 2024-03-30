From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_locations iris iris_wp iris_properties stdpp_aux.

Import uPred.

Set Default Proof Using "Type".

Close Scope byte_scope.

Definition expr := iris.expr.
Definition val := iris.val.
Definition to_val := iris.to_val.

(* Defining a Wasm-specific WP with frame existence *)
Section wp_def.
  Context `{ HHB : HandleBytes }.

Canonical Structure wasm_lang := Language wasm_mixin.
 
Local Definition reducible := @reducible wasm_lang.

Implicit Type σ : state.

Class wasmG Σ :=
  WasmG {
      func_invG :> invGS Σ;
      func_gen_hsG :> gen_heapGS N function_closure Σ;
      
      tab_gen_hsG :> gen_heapGS (N*N) funcelem Σ;
      
      tabsize_hsG :> gen_heapGS N nat Σ;
      
      tablimit_hsG :> gen_heapGS N (option N) Σ;

      mem_gen_hsG :> gen_heapGS (N*N) byte Σ;

      memsize_gen_hsG :> gen_heapGS N N Σ;

      memlimit_hsG :> gen_heapGS N (option N) Σ;

      (*      seg_gen_hsG :> gen_heapGS N (byte * btag) Σ; *)
      segGName : gname;

      seg_gen_hsG :> ghost_mapG Σ N (byte * btag);

(*      segsize_gen_hsG :> gen_heapGS unit N Σ;

      seglimit_hsG :> gen_heapGS unit (option N) Σ; *)

      (*      alloc_gen_hsG :> gen_heapGS N (N*N) Σ; *)
      allGName : gname;

      all_gen_hsG :> ghost_mapG Σ N allocator_info;

      
      glob_gen_hsG :> gen_heapGS N global Σ;

      locs_gen_hsG :> ghost_mapG Σ unit frame;

      frameGName : gname
    }.

(* functor needed for NA invariants -- those used by the logical
relation have a separate name from general ones *)
Class logrel_na_invs Σ :=
  {
    logrel_na_invG :> na_invG Σ;
    logrel_nais : na_inv_pool_name
  }.

Definition proph_id := positive. (* ??? *)


Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.




Definition gen_heap_wasm_store `{!wasmG Σ} (s: store_record) : iProp Σ :=
  ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
   (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
   (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
   (*   (gen_heap_interp (gmap_of_segment s.(s_segs) s.(s_alls))) ∗ *)
(*   (ghost_map_auth segGName 1 (gmap_of_segment s.(s_segs) s.(s_alls))) ∗ *)
   (*   (gen_heap_interp (gmap_of_allocator s.(s_alls))) ∗ *)
(*   (ghost_map_auth allGName 1 (gmap_of_allocator s.(s_alls))) ∗ *)
   (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
   (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
(*   (gen_heap_interp ({[ () := seg_length s.(s_segs).(seg_data)]} : gmap unit N)) ∗ *)
   (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
   (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
(*   (@gen_heap_interp _ _ _ _ _ seglimit_hsG ({[ () := seg_max_opt s.(s_segs)]} : gmap unit (option N))) ∗ *)
   (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt s.(s_tables)))))%I.

Global Instance heapG_irisG `{!wasmG Σ} : irisGS wasm_lang Σ := {
  iris_invGS := func_invG; 
  state_interp σ _ κs _ :=
    let: (s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (*      (gen_heap_interp (gmap_of_segment s.(s_segs) s.(s_alls))) ∗ *)
      (ghost_map_auth segGName 1 (gmap_of_segment s.(s_segs) s.(s_alls))) ∗
      (*      (gen_heap_interp (gmap_of_allocator s.(s_alls))) ∗ *)
      (ghost_map_auth allGName 1 (gmap_of_allocator s.(s_alls))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth frameGName 1 (<[ tt := Build_frame locs inst ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap mem_length s.(s_mems)))) ∗
(*      (gen_heap_interp ({[ () := seg_length s.(s_segs).(seg_data) ]} : gmap unit N)) ∗ *)
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
      (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
(*      (@gen_heap_interp _ _ _ _ _ seglimit_hsG ({[ () := seg_max_opt s.(s_segs) ]} : gmap unit (option N))) ∗ *)
      (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt s.(s_tables)))) ∗
      ⌜ wellFormedState s ⌝
     )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.




End wp_def.


(* Resource ownerships *)
Notation "n ↦[wf]{ q } v" := (mapsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (mapsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wt]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (mapsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                           (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↪[wtsize] m" := (mapsto (L:=N) (V:=nat) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtsize] m") : bi_scope.
Notation "n ↪[wtlimit] m" := (mapsto (L:=N) (V:=option N) (hG:=tablimit_hsG) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtlimit] m") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (mapsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (mapsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↪[wmlimit] v" := (mapsto (L:=N) (V:=option N) (hG:=memlimit_hsG) n (DfracDiscarded) v% V)
                               (at level 20, format "n ↪[wmlimit] v") : bi_scope.
(*Notation " ↦[ws]{ q } [ i ] v" := (mapsto (L:=N) (V:=byte * btag) i q v%V)
                                    (at level 20, q at level 5, format " ↦[ws]{ q } [ i ] v"): bi_scope.
Notation " ↦[ws][ i ] v" := (mapsto (L:=N) (V:= byte * btag) i (DfracOwn 1) v%V)
                              (at level 20, format " ↦[ws][ i ] v"): bi_scope. *)
Notation " ↦[ws]{ q }[ i ] v" := (ghost_map_elem segGName i q v)
                                   (at level 20, q at level 5, format " ↦[ws]{ q }[ i ] v") : bi_scope.
Notation " ↦[ws][ i ] v" := (ghost_map_elem segGName i (DfracOwn 1) v)
                              (at level 20, format " ↦[ws][ i ] v"): bi_scope.
(*Notation " ↦[wslength] v" := (mapsto (L:=unit) (V:=N) () (DfracOwn 1) v%V)
                               (at level 20, format " ↦[wslength] v"): bi_scope.
Notation " ↪[wslimit] v" := (mapsto (L:=unit) (V:=option N) (hG:=seglimit_hsG) () (DfracDiscarded) v % V)  
                              (at level 20, format " ↪[wslimit] v") : bi_scope. *)
(* Notation "n ↣[allocated]{ q } v" := (mapsto (L:=N) (V:=N*N) n q v%V)
                                      (at level 20, q at level 5, format "n ↣[allocated]{ q } v") : bi_scope.
Notation "n ↣[allocated] v" := (mapsto (L:=N) (V:=N*N) n (DfracOwn 1) v%V)
                                 (at level 20, format "n ↣[allocated] v") : bi_scope. *)
Notation "n ↣[allocated]{ q } v" := (ghost_map_elem allGName n q v)
                                      (at level 20, q at level 5, format "n ↣[allocated]{ q } v") : bi_scope.
Notation "n ↣[allocated] v" := (ghost_map_elem allGName n (DfracOwn 1) v)
                                 (at level 20, format "n ↣[allocated] v") : bi_scope.

(* Notation "n ↣[freed]{ q } v" := (ghost_map_elem allGName n q (Free v))
                                  (at level 20, q at level 5, format "n ↣[freed]{ q } v") : bi_scope.

Notation "n ↣[freed] v" := (ghost_map_elem allGName n (DfracOwn 1) (Free v))
                             (at level 20, format "n ↣[freed] v") : bi_scope. *)

Notation "n ↦[wg]{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v").
Notation "n ↦[wg] v" := (mapsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") .
Notation " ↪[frame]{ q } v" := (ghost_map_elem frameGName tt q v%V)
                           (at level 20, q at level 5, format " ↪[frame]{ q } v") .
Notation " ↪[frame] v" := (ghost_map_elem frameGName tt (DfracOwn 1) v%V)
                           (at level 20, format " ↪[frame] v").




(* Predicates for memory blocks and whole tables *)  
Definition mem_block `{!wasmG Σ} (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] mem_length m ∗ n ↪[wmlimit] (mem_max_opt m))%I.

Definition mem_block_at_pos `{!wasmG Σ} (n: N) (l:bytes) k :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm][ (N.of_nat (N.to_nat k+i)) ] b)%I.

Definition seg_block `{!wasmG Σ} (s: segment) :=
  (([∗ list] i ↦ b ∈ (s.(seg_data).(segl_data)), ↦[ws][ (N.of_nat i) ] b ) (* ∗
       ↦[wslength] seg_length s.(seg_data) ∗  ↪[wslimit] (seg_max_opt s) *))%I.

Definition seg_block_at_pos `{!wasmG Σ} (l:list (byte * btag)) k :=
  ([∗ list] i ↦ b ∈ l, ↦[ws][ (N.of_nat (N.to_nat k+i)) ] b)%I.


Definition tab_block `{!wasmG Σ} (n: N) (tab: tableinst) :=
  (([∗ list] i ↦ tabelem ∈ (tab.(table_data)), n ↦[wt][ (N.of_nat i) ] tabelem ) ∗
     (n ↪[wtsize] (tab_size tab)) ∗ (n ↪[wtlimit] (table_max_opt tab)))%I.

Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)                    
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.

Notation " ↦[wsblock] s" := (seg_block s)
                              (at level 20, format " ↦[wsblock] s"): bi_scope.
Notation " ↦[wss][ i ] l" := (seg_block_at_pos l i)
                               (at level 20, format " ↦[wss][ i ] l"): bi_scope.


Notation "n ↦[wtblock] t" := (tab_block n t)
                           (at level 20, format "n ↦[wtblock] t"): bi_scope.

Definition mem_equiv (m1 m2: memory): Prop :=
  m1.(mem_max_opt) = m2.(mem_max_opt) /\
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Lemma mem_equiv_wmblock_rewrite `{!wasmG Σ} (m1 m2: memory) n:
  mem_equiv m1 m2 ->
  (n ↦[wmblock] m1)%I ≡ (n ↦[wmblock] m2)%I.
Proof.
  unfold mem_equiv, mem_block.
  destruct m1, m2.
  destruct mem_data, mem_data0 => //=.
  by move => [-> ->] => //.
Qed.

Definition seg_equiv (s1 s2: segment) : Prop :=
  (* s1.(seg_max_opt) = s2.(seg_max_opt) /\ *)
    s1.(seg_data).(segl_data) = s2.(seg_data).(segl_data).

Lemma seg_equiv_wsblock_rewrite `{!wasmG Σ} (s1 s2: segment):
  seg_equiv s1 s2 ->
  ( ↦[wsblock] s1)%I ≡ ( ↦[wsblock] s2)%I.
Proof.
  unfold seg_equiv, seg_block.
  destruct s1, s2.
  destruct seg_data, seg_data0 => //=.
  by intros ->. (* by move => [-> ->] => //. *)
Qed.




Section Wasm_wp.
  Context `{!wasmG Σ}.
  Context `{HHB : HandleBytes}.


  Global Instance wp_wasm : Wp (iProp Σ) (expr) (val) stuckness.
  Proof using Σ wasmG0 HHB.
    eapply wp'. Unshelve. exact frame. exact (λ f,  ↪[frame] f)%I. Defined.



(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm_ctx `{!wasmG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.


Definition wp_wasm_frame `{!wasmG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  
  WP [AI_local n f es] @ s; E {{ Φ }}.

Definition wp_wasm_ctx_frame `{!wasmG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) (i : nat) (lh : lholed) : iProp Σ :=
  
  ∀ LI, ⌜lfilled i lh es LI⌝ -∗ WP [AI_local n f LI] @ s; E {{ Φ }}.
End Wasm_wp.

(* Notations *)

(* Context wps for blocks *)
Notation "'WP' e @ s ; E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx s E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ Φ } }" := (wp_wasm_ctx s E e%E Φ 0 (LH_base [] []))
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.


Notation "'WP' e @ s ; E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Frame wps for Local *)

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ Φ } }" := (wp_wasm_frame s E e%E Φ n f)
  (at level 20, only parsing) : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ v , Q } }" := (wp_wasm_frame s E e%E (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
    format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Tactics *)
Ltac only_one_reduction H :=
  let Hstart := fresh "Hstart" in
  let a := fresh "a" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in 
  eapply reduce_det in H
      as [H | [ [i0 Hstart] | [[i0 Hstart] | (* [ [a [cl [tf [h [i0 [Hstart [Hnth Hcl]]]]]]] | *) (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)(* ] *)]]] ;
  last (by repeat econstructor; try rewrite const_const) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart; try rewrite first_instr_instr_const in Hstart) ; inversion Hstart.


