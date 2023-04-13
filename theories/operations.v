(** Basic operations over Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common memory_list segment_list.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require lib.Floats.
From Wasm Require Export datatypes_properties list_extra.
From Coq Require Import BinNat Eqdep_dec.
Require Import Lia Coq.Program.Equality handle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(** read `len` bytes from `m` starting at `start_idx` *)
Definition read_bytes (m : memory) (start_idx : N) (len : nat) : option bytes :=
  those
    (List.map
      (fun off =>
        let idx := BinNatDef.N.add start_idx (N.of_nat off) in
        mem_lookup idx m.(mem_data))
      (iota 0 len)).

Definition read_segbytes (s : segment) (start_idx : N) (len : nat) :=
  those
    (List.map
       (fun off =>
          let idx := BinNatDef.N.add start_idx (N.of_nat off) in
          seg_lookup idx s.(seg_data))
       (iota 0 len)).

(** write bytes `bs` to `m` starting at `start_idx` *)
Definition write_bytes (m : memory) (start_idx : N) (bs : bytes) : option memory :=
  let x :=
    list_extra.fold_lefti
      (fun off dat_o b =>
        match dat_o with
        | None => None
        | Some dat =>
          let idx := BinNatDef.N.add start_idx (N.of_nat off) in
          mem_update idx b dat
        end)
      bs
      (Some m.(mem_data)) in
  match x with
  | Some dat => Some {| mem_data := dat; mem_max_opt := m.(mem_max_opt); |}
  | None => None
  end.

Definition write_segbytes (s : segment) (start_idx : N) bs : option segment:=
  let x :=
    list_extra.fold_lefti
      (fun off dat_o b =>
        match dat_o with
        | None => None
        | Some dat =>
          let idx := BinNatDef.N.add start_idx (N.of_nat off) in
          seg_update idx b dat
        end)
      bs
      (Some s.(seg_data)) in
  match x with
  | Some dat => Some {| seg_data := dat; seg_max_opt := s.(seg_max_opt) |}
  | None => None
  end.


Definition upd_s_mem (s : store_record) (m : list memory) : store_record := {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := m;
  s_segs := s.(s_segs);
  s_alls := s.(s_alls);
  s_globals := s.(s_globals);
                                                                           |}.

Definition upd_s_seg (s : store_record) (m : segment) : store_record :=
  {|
    s_funcs := s.(s_funcs) ;
    s_tables := s.(s_tables) ;
    s_mems := s.(s_mems) ;
    s_segs := m ; s_alls := s.(s_alls);
    s_globals := s.(s_globals);
  |}.

Definition upd_s_all s m :=
  {|
    s_funcs := s.(s_funcs) ;
    s_tables := s.(s_tables) ;
    s_mems := s.(s_mems) ;
    s_segs := s.(s_segs) ;
    s_alls := m ;
    s_globals := s.(s_globals)
  |}.


Definition upd_seg_data seg data :=
  {| seg_data := data ; seg_max_opt := seg.(seg_max_opt) |}.




Definition page_size : N := (64 % N) * (1024 % N).

Definition page_limit : N := 65536%N.

Definition ml_valid (m: memory_list) : Prop :=
  N.modulo (memory_list.mem_length m) page_size = 0%N.

Definition mem_length (m : memory) : N :=
  mem_length m.(mem_data).

Definition mem_size (m : memory) : N :=
  N.div (mem_length m) page_size.

Definition sl_valid (s: segment_list) : Prop :=
  N.modulo (segment_list.seg_length s) page_size = 0%N.

Definition seg_length s :=
  seg_length s.(seg_data).

Definition seg_size s : N :=
  N.div (seg_length s) page_size.


(** Grow the memory a given number of pages.
  * @param len_delta: the number of pages to grow the memory by
  *)

Definition mem_grow (m : memory) (len_delta : N) : option memory :=
  let new_size := N.add (mem_size m) len_delta in
  let new_mem_data := mem_grow (N.mul len_delta page_size) m.(mem_data) in
  if N.leb new_size page_limit then
  match m.(mem_max_opt) with
  | Some maxlim =>
    if N.leb new_size maxlim then
        Some {|
          mem_data := new_mem_data;
          mem_max_opt := m.(mem_max_opt);
          |}
    else None
  | None =>
    Some {|
      mem_data := new_mem_data;
      mem_max_opt := m.(mem_max_opt);
      |}
  end
  else None.


(* seg_grow uses length, where mem_grow uses size *)
Definition seg_grow (s : segment) (len_delta : N) : option segment :=
  let new_size := N.add (seg_length s) len_delta in
  let new_seg_data := seg_grow len_delta s.(seg_data) in
  if N.leb (N.div new_size page_size) page_limit then
  match s.(seg_max_opt) with
  | Some maxlim =>
    if N.leb (N.div new_size page_size) maxlim then
        Some {|
          seg_data := new_seg_data;
          seg_max_opt := s.(seg_max_opt);
          |}
    else None
  | None =>
    Some {|
      seg_data := new_seg_data;
      seg_max_opt := s.(seg_max_opt);
      |}
  end
  else None.


Inductive salloc : segment -> allocator -> N -> N -> N -> segment -> allocator -> Prop
  :=
  Alloc : forall T A a n (nid : N) T' A',
      (a <= N.of_nat (length (segl_data (seg_data T))))%N ->
      ((a + n) / page_size <= page_limit)%N ->
      match T.(seg_max_opt) with
      | Some lim => ((a + n) / page_size <= lim)%N
      | None => True end ->
      isFree nid A ->
      compatible a n A.(allocated) ->
      T' = {| seg_data :=
               {| segl_data := take (N.to_nat a) (segl_data (seg_data T)) ++ List.repeat (#00, Numeric) (N.to_nat n) ++ drop (N.to_nat (a + n)) (segl_data (seg_data T)) |};
             seg_max_opt := seg_max_opt T |} ->
      A' = {| allocated := (nid, a, n) :: allocated A |} ->
      salloc T A a n nid T' A'.

Lemma length_is_size {A} (l : list A) : length l = size l.
Proof. done. Qed.



  
  
  
  



Inductive sfree : segment -> allocator -> N -> N -> segment -> allocator -> Prop :=
  Free : forall T A a nid l n A',
      find_and_remove nid A.(allocated) = Some (l, a, n) ->
      A' = {| allocated := l |} ->
      sfree T A a nid T A'.


  

(* TODO: We crucially need documentation here. *)

Definition load (m : memory) (n : N) (off : static_offset) (l : nat) : option bytes :=
  if N.leb (N.add n (N.add off (N.of_nat l))) (mem_length m)
  then read_bytes m (N.add n off) l
  else None.


Definition segload (s : segment) (h : handle) (l : nat) :=
  if N.leb (N.add h.(base) (N.add h.(offset) (N.of_nat l))) (seg_length s)
  then read_segbytes s (N.add h.(base) h.(offset)) l
  else None.


Definition sign_extend (s : sx) (l : nat) (bs : bytes) : bytes :=
  (* TODO: implement sign extension *) bs.
(* TODO
  let: msb := msb (msbyte bytes) in
  let: byte := (match sx with sx_U => O | sx_S => if msb then -1 else 0) in
  bytes_takefill byte l bytes
*)

Definition load_packed (s : sx) (m : memory) (n : N) (off : static_offset) (lp : nat) (l : nat) : option bytes :=
  option_map (sign_extend s l) (load m n off lp).

Definition store (m : memory) (n : N) (off : static_offset) (bs : bytes) (l : nat) : option memory :=
  if N.leb (n + off + N.of_nat l) (mem_length m)
  then write_bytes m (n + off) (bytes_takefill #00 l bs)
  else None.

Definition store_packed := store.

Fixpoint tagged_bytes_takefill (a : (byte * btag)) (n : nat) aas :=
  match n with
  | O => nil
  | S n' =>
    match aas with
    | nil => cons a (tagged_bytes_takefill a n' aas)
    | cons a' aas' => cons a' (tagged_bytes_takefill a n' aas')
    end
  end.


Definition segstore (s : segment) (h : handle) bs (l : nat) : option segment :=
  if N.leb (h.(base) + h.(offset) + N.of_nat l) (seg_length s)
  then write_segbytes s (h.(base) + h.(offset)) (tagged_bytes_takefill (#00, Numeric) l bs)
  else None.

(*
Lemma segstore_same_length s h bs l s' :
  segstore s h bs l = Some s' -> seg_length s = seg_length s'.
Proof.
  unfold segstore.
  destruct (_ <=? _)%N eqn:Hsize => //.
  destruct (write_segbytes _ _ _) eqn:Hbytes => //.
  intro H; inversion H; subst.
  unfold write_segbytes in Hbytes. *)

(* Definition handle_of_bytes bs :=
  match bs with
  | base1 :: base2 :: base3 :: base4 ::
      offset1 :: offset2 :: offset3 :: offset4 ::
      bound1 :: bound2 :: bound3 :: bound4 ::
      valid1 :: valid2 :: valid3 :: valid4 ::
      id1 :: id2 :: id3 :: id4 :: [::] =>
      let base := Wasm_int.Int32.repr (common.Memdata.decode_int [:: base1 ; base2 ; base3 ; base4]) in
      let offset := Wasm_int.Int32.repr (common.Memdata.decode_int [:: offset1 ; offset2 ; offset3 ; offset4]) in
      let bound := Wasm_int.Int32.repr (common.Memdata.decode_int [:: bound1 ; bound2 ; bound3 ; bound4]) in
      let valid := match BinInt.Z.to_N (common.Memdata.decode_int [:: valid1 ; valid2 ; valid3 ; valid4]) with
                     | 1%N => true | _ => false end in
      let id := Wasm_int.Int32.repr (common.Memdata.decode_int [:: id1 ; id2 ; id3 ; id4]) in
      {| base := base ; offset := offset ; bound := bound ; valid := valid ; id := id |}
  | _ => dummy_handle
  end. *)


Section WasmBytes.
  Context `{HandleBytes}.
Definition wasm_deserialise (bs : bytes) (vt : value_type) : value :=
  match vt with
  | T_i32 => VAL_int32 (Wasm_int.Int32.repr (common.Memdata.decode_int bs))
  | T_i64 => VAL_int64 (Wasm_int.Int64.repr (common.Memdata.decode_int bs))
  | T_f32 => VAL_float32 (Floats.Float32.of_bits (Integers.Int.repr (common.Memdata.decode_int bs)))
  | T_f64 => VAL_float64 (Floats.Float.of_bits (Integers.Int64.repr (common.Memdata.decode_int bs)))
  | T_handle => VAL_handle (handle_of_bytes bs)
  end.

Definition bits (v : value) : bytes :=
  match v with
  | VAL_int32 c => serialise_i32 c
  | VAL_int64 c => serialise_i64 c
  | VAL_float32 c => serialise_f32 c
  | VAL_float64 c => serialise_f64 c
  | VAL_handle h => serialise_handle h
  end.

Definition t_length (t : value_type) : nat :=
  match t with
  | T_i32 => 4
  | T_i64 => 8
  | T_f32 => 4
  | T_f64 => 8
  | T_handle => handle_size
  end.


Definition tp_length (tp : packed_type) : nat :=
  match tp with
  | Tp_i8 => 1
  | Tp_i16 => 2
  | Tp_i32 => 4
  end.

Definition is_int_t (t : value_type) : bool :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  | T_handle => false
  end.

Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : value_type) : bool :=
  match tp with
  | None => Nat.pow 2 a <= t_length t
  | Some tp' => (Nat.pow 2 a <= tp_length tp') && (tp_length tp' < t_length t) && (is_int_t t)
  end.


End WasmBytes.


Definition typeof (v : value) : value_type :=
  match v with
  | VAL_int32 _ => T_i32
  | VAL_int64 _ => T_i64
  | VAL_float32 _ => T_f32
  | VAL_float64 _ => T_f64
  | VAL_handle _ => T_handle
  end.

Definition option_projl (A B : Type) (x : option (A * B)) : option A :=
  option_map fst x.

Definition option_projr (A B : Type) (x : option (A * B)) : option B :=
  option_map snd x.






Definition is_float_t (t : value_type) : bool :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  | T_handle => false
  end.

Definition is_handle_t t :=
  match t with
  | T_handle => true | _ => false end.

Definition is_mut (tg : global_type) : bool :=
  tg_mut tg == MUT_mut.


Definition app_unop_i (e : Wasm_int.type) (iop : unop_i) : Wasm_int.sort e -> Wasm_int.sort e :=
  let: Wasm_int.Pack u (Wasm_int.Class eqmx intmx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' in
  match iop with
  | UOI_ctz => Wasm_int.int_ctz intmx
  | UOI_clz => Wasm_int.int_clz intmx
  | UOI_popcnt => Wasm_int.int_popcnt intmx
  end.

Definition app_unop_f (e : Wasm_float.type) (fop : unop_f) : Wasm_float.sort e -> Wasm_float.sort e :=
  let: Wasm_float.Pack u (Wasm_float.Class eqmx mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' in
  match fop with
  | UOF_neg => Wasm_float.float_neg mx
  | UOF_abs => Wasm_float.float_abs mx
  | UOF_ceil => Wasm_float.float_ceil mx
  | UOF_floor => Wasm_float.float_floor mx
  | UOF_trunc => Wasm_float.float_trunc mx
  | UOF_nearest => Wasm_float.float_nearest mx
  | UOF_sqrt => Wasm_float.float_sqrt mx
  end.

Definition app_unop (op: unop) (v: value) :=
  match op with
  | Unop_i iop =>
    match v with
    | VAL_int32 c => VAL_int32 (@app_unop_i i32t iop c)
    | VAL_int64 c => VAL_int64 (@app_unop_i i64t iop c)
    | _ => v
    end
  | Unop_f fop =>
    match v with
    | VAL_float32 c => VAL_float32 (@app_unop_f f32t fop c)
    | VAL_float64 c => VAL_float64 (@app_unop_f f64t fop c)
    | _ => v
    end
  end.

Definition app_binop_i (e : Wasm_int.type) (iop : binop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> option (Wasm_int.sort e) :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> option (Wasm_int.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match iop with
  | BOI_add => add_some (Wasm_int.int_add mx)
  | BOI_sub => add_some (Wasm_int.int_sub mx)
  | BOI_mul => add_some (Wasm_int.int_mul mx)
  | BOI_div SX_U => Wasm_int.int_div_u mx
  | BOI_div SX_S => Wasm_int.int_div_s mx
  | BOI_rem SX_U => Wasm_int.int_rem_u mx
  | BOI_rem SX_S => Wasm_int.int_rem_s mx
  | BOI_and => add_some (Wasm_int.int_and mx)
  | BOI_or => add_some (Wasm_int.int_or mx)
  | BOI_xor => add_some (Wasm_int.int_xor mx)
  | BOI_shl => add_some (Wasm_int.int_shl mx)
  | BOI_shr SX_U => add_some (Wasm_int.int_shr_u mx)
  | BOI_shr SX_S => add_some (Wasm_int.int_shr_s mx)
  | BOI_rotl => add_some (Wasm_int.int_rotl mx)
  | BOI_rotr => add_some (Wasm_int.int_rotr mx)
  end.

Definition app_binop_f (e : Wasm_float.type) (fop : binop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> option (Wasm_float.sort e) :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> option (Wasm_float.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match fop with
  | BOF_add => add_some (Wasm_float.float_add mx)
  | BOF_sub => add_some (Wasm_float.float_sub mx)
  | BOF_mul => add_some (Wasm_float.float_mul mx)
  | BOF_div => add_some (Wasm_float.float_div mx)
  | BOF_min => add_some (Wasm_float.float_min mx)
  | BOF_max => add_some (Wasm_float.float_max mx)
  | BOF_copysign => add_some (Wasm_float.float_copysign mx)
  end.

Definition app_binop (op: binop) (v1: value) (v2: value) :=
  match op with
  | Binop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => option_map (fun v => VAL_int32 v) (@app_binop_i i32t iop c1 c2)
      |  _ => None
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => option_map (fun v => VAL_int64 v) (@app_binop_i i64t iop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  | Binop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => option_map (fun v => VAL_float32 v) (@app_binop_f f32t fop c1 c2)
      |  _ => None
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => option_map (fun v => VAL_float64 v) (@app_binop_f f64t fop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  end.

Definition app_testop_i (e : Wasm_int.type) (o : testop) : Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> bool in
  match o with
  | Eqz => Wasm_int.int_eqz mx
  end.

Definition app_relop_i (e : Wasm_int.type) (rop : relop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> bool in
  match rop with
  | ROI_eq => Wasm_int.int_eq mx
  | ROI_ne => @Wasm_int.int_ne _
  | ROI_lt SX_U => Wasm_int.int_lt_u mx
  | ROI_lt SX_S => Wasm_int.int_lt_s mx
  | ROI_gt SX_U => Wasm_int.int_gt_u mx
  | ROI_gt SX_S => Wasm_int.int_gt_s mx
  | ROI_le SX_U => Wasm_int.int_le_u mx
  | ROI_le SX_S => Wasm_int.int_le_s mx
  | ROI_ge SX_U => Wasm_int.int_ge_u mx
  | ROI_ge SX_S => Wasm_int.int_ge_s mx
  end.

Definition app_relop_f (e : Wasm_float.type) (rop : relop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> bool :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> bool in
  match rop with
  | ROF_eq => Wasm_float.float_eq mx
  | ROF_ne => @Wasm_float.float_ne _
  | ROF_lt => Wasm_float.float_lt mx
  | ROF_gt => Wasm_float.float_gt mx
  | ROF_le => Wasm_float.float_le mx
  | ROF_ge => Wasm_float.float_ge mx
  end.

Definition app_relop (op: relop) (v1: value) (v2: value) :=
  match op with
  | Relop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => @app_relop_i i32t iop c1 c2
      |  _ => false
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => @app_relop_i i64t iop c1 c2
      |  _ => false
      end                              
    | _ => false
    end
  | Relop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => @app_relop_f f32t fop c1 c2
      |  _ => false
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => @app_relop_f f64t fop c1 c2
      |  _ => false
      end                              
    | _ => false
    end
  end.

Definition types_agree (t : value_type) (v : value) : bool :=
  (typeof v) == t.

Definition cl_type (cl : function_closure) : function_type :=
  match cl with
  | FC_func_native _ tf _ _ => tf
  | FC_func_host tf _ => tf
  end.

Definition rglob_is_mut (g : global) : bool :=
  g_mut g == MUT_mut.

Definition option_bind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some y => f y
  end.



Definition empty_instance := Build_instance [::] [::] [::] [::] [::].

Definition stypes (s : store_record) (i : instance) (j : nat) : option function_type :=
  List.nth_error (inst_types i) j.

Definition sfunc_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  List.nth_error (inst_funcs i) j.

Definition sfunc (s : store_record) (i : instance) (j : nat) : option function_closure :=
  option_bind (List.nth_error (s_funcs s)) (sfunc_ind s i j).

Definition sglob_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  List.nth_error (inst_globs i) j.

Definition sglob (s : store_record) (i : instance) (j : nat) : option global :=
  option_bind (List.nth_error (s_globals s))
    (sglob_ind s i j).

Definition sglob_val (s : store_record) (i : instance) (j : nat) : option value :=
  option_map g_val (sglob s i j).

Definition smem_ind (s : store_record) (i : instance) : option nat :=
  match i.(inst_memory) with
  | nil => None
  | cons k _ => Some k
  end.

(* Definition sseg_ind (s : store_record) i : option nat :=
  match i.(inst_segment) with
  | nil => None
  | cons k _ => Some k
  end.

Definition sall_ind (s : store_record) i :=
  match i.(inst_allocator) with
  | nil => None
  | cons k _ => Some k
  end. *)


Definition tab_size (t: tableinst) : nat :=
  length (table_data t).

(**
  Get the ith table in the store s, and then get the jth index in the table;
  in the end, retrieve the corresponding function closure from the store.
 **)
(**
  There is the interesting use of option_bind (fun x => x) to convert an element
  of type option (option x) to just option x.
**)
Definition stab_index (s: store_record) (i j: nat) : option nat :=
  let: stabinst := List.nth_error (s_tables s) i in
  option_bind (fun x => x) (
    option_bind
      (fun stab_i => List.nth_error (table_data stab_i) j)
  stabinst).

Definition stab_addr (s: store_record) (f: frame) (c: nat) : option nat :=
  match f.(f_inst).(inst_tab) with
  | nil => None
  | ta :: _ => stab_index s ta c
  end.


Definition stab_s (s : store_record) (i j : nat) : option function_closure :=
  let n := stab_index s i j in
  option_bind
    (fun id => List.nth_error (s_funcs s) id)
  n.

Definition stab (s : store_record) (i : instance) (j : nat) : option function_closure :=
  match i.(inst_tab) with
  | nil => None
  | k :: _ => stab_s s k j
  end.

Definition update_list_at {A : Type} (l : seq A) (k : nat) (a : A) :=
  take k l ++ [::a] ++ List.skipn (k + 1) l.

Definition supdate_glob_s (s : store_record) (k : nat) (v : value) : option store_record :=
  option_map
    (fun g =>
      let: g' := Build_global (g_mut g) v in
      let: gs' := update_list_at (s_globals s) k g' in
      Build_store_record (s_funcs s) (s_tables s) (s_mems s) (s_segs s) (s_alls s) gs')
    (List.nth_error (s_globals s) k).

Definition supdate_glob (s : store_record) (i : instance) (j : nat) (v : value) : option store_record :=
  option_bind
    (fun k => supdate_glob_s s k v)
    (sglob_ind s i j).

Definition is_const (e : administrative_instruction) : bool :=
  if e is AI_basic (BI_const _) then true else false.

Definition const_list (es : seq administrative_instruction) : bool :=
  List.forallb is_const es.

Definition those_const_list (es : list administrative_instruction) : option (list value) :=
  those (List.map (fun e => match e with | AI_basic (BI_const v) => Some v | _ => None end) es).

Definition glob_extension (g1 g2: global) : bool.
Proof.
  destruct (g_mut g1).
  - (* Immut *)
    exact ((g_mut g2 == MUT_immut) && (g_val g1 == g_val g2)).
  - (* Mut *)
    destruct (g_mut g2).
    + exact false.
    + destruct (g_val g1) eqn:T1;
      lazymatch goal with
      | H1: g_val g1 = ?T1 _ |- _ =>
        destruct (g_val g2) eqn:T2;
          lazymatch goal with
          | H2: g_val g2 = T1 _ |- _ => exact true
          | _ => exact false
          end
      | _ => exact false
      end.
Defined.

Definition tab_extension (t1 t2 : tableinst) :=
  (tab_size t1 <= tab_size t2) &&
  (t1.(table_max_opt) == t2.(table_max_opt)).

Definition mem_extension (m1 m2 : memory) :=
  (N.leb (mem_size m1) (mem_size m2)) && (mem_max_opt m1 == mem_max_opt m2).

Definition seg_extension (s1 s2 : segment) :=
  (N.leb (seg_size s1) (seg_size s2)) && (seg_max_opt s1 == seg_max_opt s2).

Definition all_extension (a1 a2 : allocator) :=
  true.

Definition store_extension (s s' : store_record) : bool :=
  (s_funcs s == s_funcs s') &&
  (all2 tab_extension s.(s_tables) s'.(s_tables)) &&
    (all2 mem_extension s.(s_mems) s'.(s_mems)) &&
    (seg_extension s.(s_segs) s'.(s_segs)) &&
    (all_extension s.(s_alls) s'.(s_alls)) &&
  (all2 glob_extension s.(s_globals) s'.(s_globals)).

Definition vs_to_vts (vs : seq value) := map typeof vs.

Definition to_e_list (bes : seq basic_instruction) : seq administrative_instruction :=
  map AI_basic bes.

Definition to_b_single (e: administrative_instruction) : basic_instruction :=
  match e with
  | AI_basic x => x
  | _ => BI_const (VAL_int32 (Wasm_int.Int32.zero))
  end.

Definition to_b_list (es: seq administrative_instruction) : seq basic_instruction :=
  map to_b_single es.

Definition e_is_basic (e: administrative_instruction) :=
  exists be, e = AI_basic be.

Fixpoint es_is_basic (es: seq administrative_instruction) :=
  match es with
  | [::] => True
  | e :: es' =>
    e_is_basic e /\ es_is_basic es'
  end.

(** [v_to_e_list]: 
    takes a list of [v] and gives back a list where each [v] is mapped to [Basic (EConst v)]. **)
Definition v_to_e_list (ves : seq value) : seq administrative_instruction :=
  map (fun v => AI_basic (BI_const v)) ves.

(* interpreter related *)

Fixpoint split_vals (es : seq basic_instruction) : seq value * seq basic_instruction :=
  match es with
  | (BI_const v) :: es' =>
    let: (vs', es'') := split_vals es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.



(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [Basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
Fixpoint split_vals_e (es : seq administrative_instruction) : seq value * seq administrative_instruction :=
  match es with
  | (AI_basic (BI_const v)) :: es' =>
    let: (vs', es'') := split_vals_e es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

Lemma split_vals_not_empty_res : forall es v vs es',
  split_vals_e es = (v :: vs, es') -> es <> [::].
Proof. by case. Qed.

Lemma split_vals_e_not_const es vs e es' :
  split_vals_e es = (vs, e :: es') -> is_const e -> False.
Proof.
  generalize dependent vs ; generalize dependent e ; generalize dependent es'. 
  induction es => //= ; intros.
  destruct a => //= ; try by inversion H ; subst. 
  destruct b => //= ; try by inversion H ; subst.
  destruct (split_vals_e es) as [??] eqn:Hes.
  destruct l0 => //=.
  inversion H ; subst. by eapply IHes.
Qed.




Fixpoint split_n (es : seq value) (n : nat) : seq value * seq value :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao with
  | Some a => f a
  | None => b
  end.

Definition vs_to_es (vs : seq value) : seq administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  match e with
  | AI_trap => true
  | _ => false
  end.

(** [es_is_trap es] is equivalent to [es == [:: Trap]]. **)
Definition es_is_trap (es : seq administrative_instruction) : bool :=
  match es with
  | [::e] => e_is_trap e
  | _ => false
  end.



(** Converting a result into a stack. **)
Definition result_to_stack (r : result) :=
  match r with
  | result_values vs => v_to_e_list vs
  | result_trap => [:: AI_trap]
  end.

Fixpoint lfill (k : nat) (lh : lholed) (es : seq administrative_instruction) : option (seq administrative_instruction) :=
  match k with
  | 0 =>
    if lh is LH_base vs es' then
      if const_list vs then Some (app vs (app es es')) else None
    else None
  | k'.+1 =>
    if lh is LH_rec vs n es' lh' es'' then
      if const_list vs then
        if lfill k' lh' es is Some lfilledk then
          Some (app vs (cons (AI_label n es' lfilledk) es''))
        else None
      else None
    else None
  end.

Definition lfilled (k : nat) (lh : lholed) (es : seq administrative_instruction) (es' : seq administrative_instruction) : bool :=
  if lfill k lh es is Some es'' then es' == es'' else false.

Inductive lfilledInd : nat -> lholed -> seq administrative_instruction -> seq administrative_instruction -> Prop :=
| LfilledBase: forall vs es es',
    const_list vs ->
    lfilledInd 0 (LH_base vs es') es (vs ++ es ++ es')
| LfilledRec: forall k vs n es' lh' es'' es LI,
    const_list vs ->
    lfilledInd k lh' es LI ->
    lfilledInd (k.+1) (LH_rec vs n es' lh' es'') es (vs ++ [ :: (AI_label n es' LI) ] ++ es'').

Lemma lfilled_Ind_Equivalent: forall k lh es LI,
    lfilled k lh es LI <-> lfilledInd k lh es LI.
Proof.
  move => k. split.
  - move: lh es LI. induction k; move => lh es LI HFix.
    + unfold lfilled in HFix. simpl in HFix. destruct lh => //=.
      * destruct (const_list l) eqn:HConst => //=.
        { replace LI with (l++es++l0); first by apply LfilledBase.
          symmetry. move: HFix. by apply/eqseqP. }
    + unfold lfilled in HFix. simpl in HFix. destruct lh => //=.
      * destruct (const_list l) eqn:HConst => //=.
        { destruct (lfill k lh es) eqn:HLF => //=.
          { replace LI with (l ++ [ :: (AI_label n l0 l2)] ++ l1).
          apply LfilledRec; first by [].
          apply IHk. unfold lfilled; first by rewrite HLF.
          symmetry. move: HFix. by apply/eqseqP. }
        }
  - move => HLF. induction HLF.
    + unfold lfilled. unfold lfill. by rewrite H.
    + unfold lfilled. unfold lfill. rewrite H. fold lfill.
      unfold lfilled in IHHLF. destruct (lfill k lh' es) => //=.
      * replace LI with l => //=.
        symmetry. by apply/eqseqP.
Qed.

Lemma lfilledP: forall k lh es LI,
    reflect (lfilledInd k lh es LI) (lfilled k lh es LI).
Proof.
  move => k lh es LI. destruct (lfilled k lh es LI) eqn:HLFBool.
  - apply ReflectT. by apply lfilled_Ind_Equivalent.
  - apply ReflectF. move=> HContra. apply lfilled_Ind_Equivalent in HContra.
    by rewrite HLFBool in HContra.
Qed.

Fixpoint lfill_exact (k : nat) (lh : lholed) (es : seq administrative_instruction) : option (seq administrative_instruction) :=
  match k with
  | 0 =>
    if lh is LH_base nil nil then Some es else None
  | k'.+1 =>
    if lh is LH_rec vs n es' lh' es'' then
      if const_list vs then
        if lfill_exact k' lh' es is Some lfilledk then
          Some (app vs (cons (AI_label n es' lfilledk) es''))
        else None
      else None
    else None
  end.

Definition lfilled_exact (k : nat) (lh : lholed) (es : seq administrative_instruction) (es' : seq administrative_instruction) : bool :=
  if lfill_exact k lh es is Some es'' then es' == es'' else false.

Fixpoint lh_depth lh :=
  match lh with
  | LH_base _ _ => 0
  | LH_rec _ _ _ lh _ => S (lh_depth lh)
  end.


Definition result_types_agree (ts : result_type) r :=
  match r with
  | result_values vs => all2 types_agree ts vs
  | result_trap => true
  end.




(* MAXIME: should cvt_[any type] of a handle value be something else than None ? *)
Definition cvt_i32 (s : option sx) (v : value) : option i32 :=
  match v with
  | VAL_int32 _ => None
  | VAL_int64 c => Some (wasm_wrap c)
  | VAL_float32 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f32m c
    | Some SX_S => Wasm_float.float_ui32_trunc f32m c
    | None => None
    end
  | VAL_float64 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f64m c
    | Some SX_S => Wasm_float.float_ui32_trunc f64m c
    | None => None
    end
  | VAL_handle h => None
  end.

Definition cvt_i64 (s : option sx) (v : value) : option i64 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (wasm_extend_u c)
    | Some SX_S => Some (wasm_extend_s c)
    | None => None
    end
  | VAL_int64 c => None
  | VAL_float32 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f32m c
    | Some SX_S => Wasm_float.float_si64_trunc f32m c
    | None => None
    end
  | VAL_float64 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f64m c
    | Some SX_S => Wasm_float.float_si64_trunc f64m c
    | None => None
    end
  | VAL_handle _ => None
  end.

Definition cvt_f32 (s : option sx) (v : value) : option f32 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f32m c)
    | None => None
    end
  | VAL_int64 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f32m c)
    | None => None
    end
  | VAL_float32 c => None
  | VAL_float64 c => Some (wasm_demote c)
  | VAL_handle _ => None
  end.

Definition cvt_f64 (s : option sx) (v : value) : option f64 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f64m c)
    | None => None
    end
  | VAL_int64 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f64m c)
    | None => None
    end
  | VAL_float32 c => Some (wasm_promote c)
  | VAL_float64 c => None
  | VAL_handle _ => None
  end.


Definition cvt (t : value_type) (s : option sx) (v : value) : option value :=
  match t with
  | T_i32 => option_map VAL_int32 (cvt_i32 s v)
  | T_i64 => option_map VAL_int64 (cvt_i64 s v)
  | T_f32 => option_map VAL_float32 (cvt_f32 s v)
  | T_f64 => option_map VAL_float64 (cvt_f64 s v)
  | T_handle => None
  end.
Search (i32).



Definition bitzero (t : value_type) : value :=
  match t with
  | T_i32 => VAL_int32 (Wasm_int.int_zero i32m)
  | T_i64 => VAL_int64 (Wasm_int.int_zero i64m)
  | T_f32 => VAL_float32 (Wasm_float.float_zero f32m)
  | T_f64 => VAL_float64 (Wasm_float.float_zero f64m)
  | T_handle => VAL_handle dummy_handle
  end.

Definition n_zeros (ts : seq value_type) : seq value :=
  map bitzero ts.

(* TODO: lots of lemmas *)


Definition is_none_or {A : Type} (p : A -> bool) (x : option A) : bool :=
  match x with
  | None => true
  | Some y => p y
  end.

Lemma b2p: forall {T:eqType} (a b:T), a==b -> a=b.
Proof. move => T a b Hb. by move/eqP in Hb. Qed.


Lemma cat_app {A} (l1 : list A) l2 :
  cat l1 l2 = app l1 l2.
Proof. done. Qed.









Lemma first_values vs1 e1 es1 vs2 e2 es2 :
  (is_const e1 = false) ->
  (is_const e2 = false) ->
  const_list vs1 ->
  const_list vs2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  intros He1 He2 Hvs1 Hvs2 Heq.
  generalize dependent vs2; induction vs1 ; intros.
  { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
    simpl in Hvs2. apply Bool.andb_true_iff in Hvs2 as [ Habs _ ].
    rewrite Habs in He1 => //.
  } 
  destruct vs2 ; inversion Heq.
  { rewrite H0 in Hvs1.
    simpl in Hvs1. apply Bool.andb_true_iff in Hvs1 as [ Habs _ ].
    rewrite Habs in He2 => //.
  }
  assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
  apply IHvs1 => //=.
  - by apply Bool.andb_true_iff in Hvs1 as [ _ Hvs1 ].
  - by apply Bool.andb_true_iff in Hvs2 as [ _ Hvs2 ].  
Qed.


