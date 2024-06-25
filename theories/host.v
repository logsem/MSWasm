(** Axiomatisation of the host. **)
(* (C) M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import common datatypes operations typing handle.
From ITree Require Import ITree ITreeFacts.

Import Monads.

Set Implicit Arguments.

(** * General host definitions **)

(** We provide two versions of the host.
  One based on a relation, to be used in the operational semantics,
  and one computable based on the [host_monad] monad, to be used in the interpreter.
  There is no host state in the host monad: it is entirely caught by the (state) monad. **)

(** ** Predicate Host **)

(** We start with a host expressed as a predicate, useful for proofs. **)

Section Predicate.
 Context `{HHB: HandleBytes}.

Record host := {
    host_state : eqType (** For the relation-based version, we assume some kind of host state. **) ;
    host_application : host_state -> store_record -> function_type -> hostfuncidx -> seq value ->
                       host_state -> option (store_record * result) -> Prop;
                       (** An application of the host function. **)

    host_application_extension : forall s t st h vs s' st' r,
      host_application s st t h vs s' (Some (st', r)) ->
      store_extension st st' (** The returned store must be an extension of the original one. **) ;
    host_application_typing : forall s t st h vs s' st' r,
      host_application s st t h vs s' (Some (st', r)) ->
      store_typing st ->
      store_typing st' (** [host_application] preserves store typing. **) ;
    host_application_respect : forall s t1s t2s st h vs s' st' r,
      all2 types_agree t1s vs ->
      host_application s st (Tf t1s t2s) h vs s' (Some (st', r)) ->
      result_types_agree t2s r (** [host_application] respects types. **)
  }.

End Predicate.

Arguments host_application [_ _].

(** ** Executable Host **)

(** We start with a host expressed as a predicate, useful for proofs. **)

Section Executable.

(** We assume a set of host functions.
  To help with the extraction, it is expressed as a [Type] and not an [eqType]. **)


Record executable_host := make_executable_host {
    host_event : Type -> Type (** The events that the host actions can yield. **) ;
    host_monad : Monad host_event (** They form a monad. **) ;
    host_apply : store_record -> function_type -> hostfuncidx -> seq value ->
                 host_event (option (store_record * result))
                 (** The application of a host function, returning a value in the monad. **)
  }.

End Executable.

Arguments host_apply [_ _].

(** ** Relation between both versions **)

Section Parameterised.
Context `{HHB: HandleBytes}.


Variable phost : host.
Variable ehost : executable_host.


End Parameterised.


(** * Extractible module **)

(** The definitions of the previous section are based on dependent types, which are very
  practical to manipulate them in Coq, but do not extract very well.
  The following is an extract-friendly adaptation using modules.
  We also require other useful hypotheses **)

Module Type Executable_Host.

  Definition hostfuncidx_eq_dec : forall f1 f2 : hostfuncidx, {f1 = f2} + {f1 <> f2}.
  Proof. intros. destruct f1. destruct f2.
         destruct (PeanoNat.Nat.eq_dec n n0).
         by left ; subst.
         right.
         intro.
         apply n1.
         by inversion H. Defined.
Parameter host_event : Type -> Type.
Parameter host_ret : forall t : Type, t -> host_event t.
Parameter host_bind : forall t u : Type, host_event t -> (t -> host_event u) -> host_event u.

Parameter host_apply : store_record -> function_type -> hostfuncidx -> seq value ->
                       host_event (option (store_record * result)).

End Executable_Host.

(** Such a module can easily be converted into an [executable_host] definition. **)

Module convert_to_executable_host (H : Executable_Host).

Export H.

Definition hostfuncidx_eqb f1 f2 : bool := hostfuncidx_eq_dec f1 f2.

Definition hostfuncidxP : Equality.axiom hostfuncidx_eqb :=
  eq_dec_Equality_axiom hostfuncidx_eq_dec.

Canonical Structure hostfuncidx_eqMixin := EqMixin hostfuncidxP.
Canonical Structure host_function :=
  Eval hnf in EqType _ hostfuncidx_eqMixin.

Definition host_monad : Monad host_event := {|
    ret := host_ret ;
    bind := host_bind
  |}.

Definition executable_host_instance : executable_host :=
  make_executable_host host_monad host_apply.

Definition host_functor := Functor_Monad (M := host_monad).

End convert_to_executable_host.



