(** Wasm type checker **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
From MSWasm Require Import common handle.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing datatypes_properties.




Inductive checker_type_aux : Type :=
| CTA_any : checker_type_aux
| CTA_some : value_type -> checker_type_aux.

Scheme Equality for checker_type_aux.
Definition checker_type_aux_eqb v1 v2 := is_left (checker_type_aux_eq_dec v1 v2).
Definition eqchecker_type_auxP  : Equality.axiom checker_type_aux_eqb :=
  eq_dec_Equality_axiom checker_type_aux_eq_dec.

Canonical Structure checker_type_aux_eqMixin := EqMixin eqchecker_type_auxP.
Canonical Structure checker_type_aux_eqType :=
  Eval hnf in EqType checker_type_aux checker_type_aux_eqMixin.

Inductive checker_type : Type :=
| CT_top_type : seq checker_type_aux -> checker_type
| CT_type : seq value_type -> checker_type
| CT_bot : checker_type.

Definition checker_type_eq_dec : forall v1 v2 : checker_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition checker_type_eqb v1 v2 : bool := checker_type_eq_dec v1 v2.
Definition eqchecker_typeP : Equality.axiom checker_type_eqb :=
  eq_dec_Equality_axiom checker_type_eq_dec.

Canonical Structure checker_type_eqMixin := EqMixin eqchecker_typeP.
Canonical Structure checker_type_eqType := Eval hnf in EqType checker_type checker_type_eqMixin.

Definition to_ct_list (ts : seq value_type) : seq checker_type_aux :=
  map CTA_some ts.


Definition ct_compat (t1 t2: checker_type_aux) : bool :=
  match t1 with
  | CTA_any => true
  | CTA_some vt1 =>
    match t2 with
    | CTA_any => true
    | CTA_some vt2 => (vt1 == vt2)
    end
  end.

Definition ct_list_compat (l1 l2: list checker_type_aux) : bool :=
  all2 ct_compat l1 l2.

Definition ct_suffix (ts ts' : list checker_type_aux) : bool :=
  (size ts <= size ts') && (ct_list_compat (drop (size ts' - size ts) ts') ts).

(**
  It looks like CT_bot stands for an error in typing.

  CT_top_type xyz means a stack with the top part being xyz??? This is guessed
    by looking at 'produce'... CT_type should refer to the type of the entire stack.

  produce seems to be for the result of a concatenation of two stacks. 
**)

Definition consume (t : checker_type) (cons : seq checker_type_aux) : checker_type :=
  match t with
  | CT_type ts =>
    if ct_suffix cons (to_ct_list ts)
    then CT_type (take (size ts - size cons) ts)
    else CT_bot
  | CT_top_type cts =>
    if ct_suffix cons cts
    then CT_top_type (take (size cts - size cons) cts)
    else
      (if ct_suffix cts cons
       then CT_top_type [::]
       else CT_bot)
  | _ => CT_bot
  end.

Definition produce (t1 t2 : checker_type) : checker_type :=
  match (t1, t2) with
  | (CT_top_type ts, CT_type ts') => CT_top_type (ts ++ (to_ct_list ts'))
  | (CT_type ts, CT_type ts') => CT_type (ts ++ ts')
  | (CT_type ts', CT_top_type ts) => CT_top_type ts
  | (CT_top_type ts', CT_top_type ts) => CT_top_type ts
  | _ => CT_bot
  end.

Definition type_update (curr_type : checker_type) (cons : seq checker_type_aux) (prods : checker_type) : checker_type :=
  produce (consume curr_type cons) prods.

Definition select_return_top (ts : seq checker_type_aux) (cta1 cta2 : checker_type_aux) : checker_type :=
  match (cta1, cta2) with
  | (_, CTA_any) => CT_top_type (take (length ts - 3) ts ++ [::cta1])
  | (CTA_any, _) => CT_top_type (take (length ts - 3) ts ++ [::cta2])
  | (CTA_some t1, CTA_some t2) =>
    if t1 == t2
    then CT_top_type (take (length ts - 3) ts ++ [::CTA_some t1])
    else CT_bot
  end.

Definition type_update_select (t : checker_type) : checker_type :=
  match t with
  | CT_type ts =>
    if (length ts >= 3) && (List.nth_error ts (length ts - 2) == List.nth_error ts (length ts - 3))
    then (consume (CT_type ts) [::CTA_any; CTA_some T_i32])
    else CT_bot
  | CT_top_type ts =>
    match length ts with
    | 0 => CT_top_type [::CTA_any]
    | 1 => type_update (CT_top_type ts) [::CTA_some T_i32] (CT_top_type [::CTA_any])
    | 2 => consume (CT_top_type ts) [::CTA_some T_i32]
    | _ =>
      match List.nth_error ts (length ts - 2), List.nth_error ts (length ts - 3) with
      | Some ts_at_2, Some ts_at_3 =>
        type_update (CT_top_type ts) [::CTA_any; CTA_any; CTA_some T_i32]
                    (select_return_top ts ts_at_2 ts_at_3)
                (* UPD: this is now the correct verified version *)
                    
      | _, _ => CT_bot 
      end
    end
  | CT_bot => CT_bot
  end.

Fixpoint same_lab_h (iss : seq nat) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type) :=
  match iss with
  | [::] => Some ts
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | None => None 
      | Some xx =>
        if xx == ts then same_lab_h iss' lab_c xx
        else None
      end
  end.

(**
   So Br_table iss i needs to make sure that Br (each element in iss) and Br i would 
     consume the same type. Look at section 3.3.5.8 in the official spec.
**)
Definition same_lab (iss : seq nat) (lab_c : seq (seq value_type)) : option (seq value_type) :=
  match iss with
  | [::] => None
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | Some xx => same_lab_h iss' lab_c xx
      | None => None 
      end
  end.


Definition c_types_agree (ct : checker_type) (ts' : seq value_type) : bool :=
  match ct with
  | CT_type ts => ts == ts'
  | CT_top_type ts => ct_suffix ts (to_ct_list ts')
  | CT_bot => false
  end.

Definition is_int (t: value_type) :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  | T_handle => false 
  end.

Definition is_float (t: value_type) :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  | T_handle => false
  end.

Definition is_handle t :=
  match t with
  | T_handle => true
  | _ => false
  end.

Section Check.
  Context `{HandleBytes}.

Fixpoint check_single (C : t_context) (ts : checker_type) (be : basic_instruction) : checker_type :=
  let b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
    let: (Tf tn tm) := tf in
      c_types_agree (List.fold_left (check_single C) es (CT_type tn)) tm
in
  if ts == CT_bot then CT_bot
  else
  match be with
  | BI_const v =>
      type_update ts [::] (CT_type [::typeof_numerical v])
  | BI_unop t op =>
    match op with
    | Unop_i _ => if is_int t
                  then type_update ts [::CTA_some t] (CT_type [::t])
                  else CT_bot
    | Unop_f _ => if is_float t
                  then type_update ts [::CTA_some t] (CT_type [::t])
                  else CT_bot
    end
  | BI_binop t op =>
    match op with
    | Binop_i _ => if is_int t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::t])
                  else CT_bot
    | Binop_f _ => if is_float t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::t])
                  else CT_bot
    end
  | BI_slice =>
      type_update ts [::CTA_some T_handle; CTA_some T_i32; CTA_some T_i32] (CT_type [::T_handle])
  | BI_handleadd =>
      type_update ts [::CTA_some T_i32; CTA_some T_handle] (CT_type [::T_handle])
  | BI_getoffset =>
      type_update ts [::CTA_some T_handle] (CT_type [::T_i32])
  | BI_isdummy =>
      type_update ts [::CTA_some T_handle] (CT_type [::T_i32])

  | BI_testop t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t] (CT_type [::T_i32])
    else CT_bot
  | BI_relop t op =>
    match op with
    | Relop_i _ => if is_int t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::T_i32])
                  else CT_bot
    | Relop_f _ => if is_float t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::T_i32])
                  else CT_bot
    | Relop_h _ => if is_handle t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::T_i32])
                  else CT_bot
    end
  | BI_cvtop t1 CVO_convert t2 sx =>
    if typing.convert_cond t1 t2 sx
    then type_update ts [::CTA_some t2] (CT_type [::t1])
    else CT_bot
  | BI_cvtop t1 CVO_reinterpret t2 sxo =>
    if (t1 != t2) && (t1 != T_handle) && (t2 != T_handle) && (t_length t1 == t_length t2) && (sxo == None)
    then type_update ts [::CTA_some t2] (CT_type [::t1])
    else CT_bot
  | BI_unreachable => type_update ts [::] (CT_top_type [::])
  | BI_nop => ts
  | BI_drop => type_update ts [::CTA_any] (CT_type [::])
  | BI_select => type_update_select ts
  | BI_block (Tf tn tm) es =>
    if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es (Tf tn tm)
    then type_update ts (to_ct_list tn) (CT_type tm)
    else CT_bot
  | BI_loop (Tf tn tm) es =>
    if b_e_type_checker (upd_label C ([::tn] ++ tc_label C)) es (Tf tn tm)
    then type_update ts (to_ct_list tn) (CT_type tm)
    else CT_bot
  | BI_if (Tf tn tm) es1 es2 =>
    if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es1 (Tf tn tm)
                        && b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es2 (Tf tn tm)
    then type_update ts (to_ct_list (tn ++ [::T_i32])) (CT_type tm)
    else CT_bot
  | BI_br i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list xx) (CT_top_type [::])
      | None => CT_bot 
      end
    else CT_bot
  | BI_br_if i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list (xx ++ [::T_i32])) (CT_type xx)
      | None => CT_bot 
      end
    else CT_bot
  | BI_br_table iss i =>
    match same_lab (iss ++ [::i]) (tc_label C) with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list (tls ++ [::T_i32])) (CT_top_type [::])
    end
  | BI_return =>
    match tc_return C with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list tls) (CT_top_type [::])
    end
  | BI_call i =>
    if i < length (tc_func_t C)
    then
      match List.nth_error (tc_func_t C) i with
      | None => CT_bot 
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list tn) (CT_type tm)
      end
    else CT_bot
  | BI_call_indirect i =>
    if (1 <= length C.(tc_table)) && (i < length C.(tc_types_t))
    then
      match List.nth_error (tc_types_t C) i with
      | None => CT_bot 
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list (tn ++ [::T_i32])) (CT_type tm)
      end
    else CT_bot
  | BI_get_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot 
      | Some xx => type_update ts [::] (CT_type [::xx])
      end
    else CT_bot
  | BI_set_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot 
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::])
      end
    else CT_bot
  | BI_tee_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot 
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::xx])
      end
    else CT_bot
  | BI_get_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot 
      | Some xx => type_update ts [::] (CT_type [::tg_t xx])
      end
    else CT_bot
  | BI_set_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot 
      | Some xx =>
        if is_mut xx
        then type_update ts [::CTA_some (tg_t xx)] (CT_type [::])
        else CT_bot
      end
    else CT_bot
  | BI_load t tp_sx a off =>
    if (C.(tc_memory) != nil) && (t != T_handle) && load_store_t_bounds a (option_projl tp_sx) t
    then type_update ts [::CTA_some T_i32] (CT_type [::t])
    else CT_bot
  | BI_segload t =>
      type_update ts [::CTA_some T_handle] (CT_type [::t])
  | BI_store t tp a off =>
    if (C.(tc_memory) != nil) && load_store_t_bounds a tp t
    then type_update ts [::CTA_some T_i32; CTA_some t] (CT_type [::])
    else CT_bot
  | BI_segstore t =>
      type_update ts [::CTA_some T_handle; CTA_some t] (CT_type [::])
  | BI_current_memory =>
    if C.(tc_memory) != nil
    then type_update ts [::] (CT_type [::T_i32])
    else CT_bot
  | BI_grow_memory =>
    if C.(tc_memory) != nil
    then type_update ts [::CTA_some T_i32] (CT_type [::T_i32])
    else CT_bot
  | BI_segalloc =>
      type_update ts [::CTA_some T_i32] (CT_type [::T_handle])
  | BI_segfree =>
      type_update ts [::CTA_some T_handle] (CT_type [::])
  end.



Fixpoint collect_at_inds A (l : seq A) (ns : seq nat) : seq A :=
  match ns with
  | n :: ns' =>
    match (List.nth_error l n) with
    | Some x => x :: collect_at_inds l ns'
    | None => collect_at_inds l ns'
    end
  | [::] => [::]
  end.

Definition check (C : t_context) (es : list basic_instruction) (ts : checker_type): checker_type :=
  List.fold_left (check_single C) es ts.



Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
  let: (Tf tn tm) := tf in
  c_types_agree (List.fold_left (check_single C) es (CT_type tn)) tm  .

End Check.



