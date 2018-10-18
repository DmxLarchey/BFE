(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega Wellfounded Extraction.

Set Implicit Arguments.

Section measure_rect.

  Variable (X : Type) (m : X -> nat) (P : X -> Type).

  Let R (x y: X): Prop := m x < m y.

  Fact Acc_measure : well_founded R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed.

  Theorem measure_rect : 
        (forall x, (forall y, m y < m x -> P y) -> P x) 
     -> (forall x,                                 P x).
  Proof.
    intros HP x.
    cut (Acc R x).
    + revert x.
      exact (fix loop x Hx { struct Hx } := @HP x (fun y Hy => loop y (Acc_inv Hx Hy))).
    + apply Acc_measure.
  Defined.

End measure_rect.

Section measure_double_rect.

  Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type).

  Let R (c d: X * Y): Prop := m (fst c) (snd c) < m (fst d) (snd d).

  Theorem measure_double_rect : 
        (forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y)
     -> (forall x y,                                               P x y).
  Proof.
    intros HP x y.
    cut (Acc R (x,y)).
    + revert x y.
      refine (fix loop x y H { struct H } := @HP x y (fun x' y' H' => loop x' y' (Acc_inv H _))).
      exact H'.
    + unfold R; apply wf_inverse_image, lt_wf.
  Defined.

End measure_double_rect.

(* Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH. *)

(* Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x, y; revert x y; apply measure_double_rect with (m := fun x y => f); intros x y IH. *)

Extraction Inline measure_rect measure_double_rect.

(** Solved the parasitic let/in issue with measure_rect with the black magic 
    Ltac hack that constructs the fixpoint and then hides it 

    This is a kind of inlining of measure_rect & measure_double_rect inside
    the Coq terms instead of inlining them at extraction.

    Beware that [define] below will not work well if "fresh" variable names
    clash with hyps x and y ... not sure of the exact semantics of Ltac ...

    I agree this inlining is ugly but I am not able to remove the let/in
    by using measure_rect ...
*)

Tactic Notation "define" ident(f) "of" hyp(n) "as" uconstr(t)  :=
  match type of n with ?N => pose (f (n : N) := t) end.

Tactic Notation "define" ident(f) "of" hyp(n) hyp(m) "as" uconstr(t)  :=
  match type of n with ?N =>  
    match type of m with ?M  => pose (f (n:N) (m:M) := t) end end.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  generalize I; intro IH;
  let mes := fresh "measure" in let rel := fresh "relation" in let loop := fresh "loop" in
  let u := fresh "u" in let Hu := fresh "Hu" in let v := fresh "v" in let Hv := fresh "Hv" 
  in clear IH;
     define mes of x as (f : nat);
     set (rel x y := mes x < mes y);
     pattern x; match goal with
       |- ?T _ => 
       refine ((fix loop u (Hu : Acc rel u) { struct Hu } : T u := _) x _);
       [ assert (forall v, rel v u -> T v) as IH;
         [ intros v Hv; apply (loop v), (Acc_inv Hu), Hv 
         | unfold rel, mes in *; clear mes rel Hu loop x; rename u into x ]
       | unfold rel; apply wf_inverse_image, lt_wf ]
     end.

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  generalize I; intro IH;
  let mes := fresh "measure" in let rel := fresh "relation" in let loop := fresh "loop" in
  let u := fresh "u" in let u' := fresh x in let Hu := fresh "Hu" in 
  let v := fresh "v" in let v' := fresh y in let Hv := fresh "Hv" 
  in clear IH; 
     define mes of x y as (f : nat);
     set (rel u v := mes (fst u) (snd u) < mes (fst v) (snd v)); unfold fst, snd in rel;
     pattern x, y; match goal with
       |- ?T _ _ => 
       refine ((fix loop u v (Hu : Acc rel (u,v)) { struct Hu } : T u v := _) x y _);
       [ assert (forall u' v', rel (u',v') (u,v) -> T u' v') as IH;
         [ intros u' v' Hv; apply (loop u' v'), (Acc_inv Hu), Hv 
         | unfold rel, mes in *; clear mes rel Hu loop x y; rename u into x; rename v into y ]
       | unfold rel; apply wf_inverse_image, lt_wf ]
     end.


