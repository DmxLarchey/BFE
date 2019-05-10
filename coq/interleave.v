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

(** Small example of interleave to compare
    our tailored fixpoint technique with
    "Program Fixpoint" and "Equations"

    You need Coq 8.9 + Equations installed for
    this to work *)

(** Summary:

    We have both the ability to prove properties of our defined
    function AND the extraction that we want.

    0) Function fails because no single argument
       decreases.

    1) Equations provides a framework where
       term are easy to define and the "simp" tactic
       gives the equations you want BUT
       extraction contains parasitic structures
       which are perhaps impossible to get rid of.

    2) Program Fixpoint allows easy definition
       with full specs but extraction presents
       the same problems as the Equations package.

    3) With induction ... on inlining a fixpoint,
       we can get equations and the intended 
       extraction

 *)

From Equations Require Import Equations Signature.
Require Import List Arith Omega Wellfounded Program Extraction.

Require Import wf_utils.

Set Implicit Arguments.

Section interleave_naive.

  (** Naive implementation of interleave which does not
      respect the intended algorithm *)

  Variable (X : Type).

  Implicit Types (l m : list X).

  Fixpoint itl_triv l m :=
    match l, m with
      | nil, _       => m
      | x::l', y::m' => x::y::itl_triv l' m'
      | _, _         => l
    end.

  Fact itl_triv_fix_0 m : itl_triv nil m = m.
  Proof. trivial. Qed.

  Fact itl_triv_fix_1 x l m : itl_triv (x::l) m = x::itl_triv m l.
  Proof.
    revert m x.
    induction l as [ | a l IHl ];
    induction m as [ | b m IHm ]; intros x; try (simpl; auto; fail).
    simpl itl_triv at 2; rewrite <- IHl; auto.
  Qed.

  Section interleave_equations.

    Variable (f : list X -> list X -> list X) (Hf : forall l m, f l m = itl_triv l m).

    Fact interleave_eq_triv_0 m : f nil m = m.
    Proof. rewrite Hf, itl_triv_fix_0; trivial. Qed.

    Fact interleave_eq_triv_1 x l m : f (x::l) m = x :: f m l.
    Proof. 
      do 2 rewrite Hf; apply itl_triv_fix_1. 
    Qed.
  
  End interleave_equations.

End interleave_naive.

Section interleave_trials.

  Variable (X : Type).

  Implicit Types (l m : list X).

  (** Implementation of interleave using Program Fixpoint *)

  Section itl_pfix.

    Program Fixpoint itl_pfix_full l m { measure (length l+length m) } : { k | k = itl_triv l m } :=
      match l with
        | nil  => m
        | x::l => x::itl_pfix_full m l
      end.
    Obligation 2. simpl; omega. Qed.
    Obligation 3.
      destruct m; simpl; f_equal.
      * f_equal; apply (@proj2_sig _).
      * rewrite <- itl_triv_fix_1.
        apply (@proj2_sig _).
    Qed.

    Definition itl_pfix l m := proj1_sig (itl_pfix_full l m).

    Fact itl_pfix_spec l m : itl_pfix l m = itl_triv l m.
    Proof. apply (proj2_sig (itl_pfix_full l m)). Qed.

  End itl_pfix.

  (** Implementation of interleave using Equations, needs Coq v8.9 *)

  Section itl_eqs.

    Equations itl_eqs l m : list X by wf (length l + length m) lt :=
      itl_eqs nil     m  := m;
      itl_eqs (cons x l) m  with itl_eqs m l => { | r := x::r }.
    Obligation 1. omega. Qed.

    Fact itl_eqs_fix_0 m : itl_eqs nil m = m.
    Proof. trivial. Qed.

    Fact itl_eqs_fix_1 x l m : itl_eqs (x::l) m = x::itl_eqs m l.
    Proof. simp itl_eqs. Qed.

    Fact itl_eqs_triv l m : itl_eqs l m = itl_triv l m.
    Proof.
      revert m.
      induction l as [ | x l IHl ]; intros m.
      + rewrite itl_eqs_fix_0; trivial.
      + rewrite itl_eqs_fix_1, itl_triv_fix_1; f_equal.
        destruct m as [ | y m ].
        * rewrite itl_eqs_fix_0; trivial.
        * rewrite itl_eqs_fix_1, itl_triv_fix_1; f_equal; auto.
    Qed.

  End itl_eqs.

End interleave_trials.

Extract Inductive list => "list" [ "[]" "(::)" ].

Extraction Inline itl_pfix_full itl_pfix_full_func.

Extraction itl_triv.

Extraction itl_pfix.
Extraction itl_eqs.

Section itl_induction_on.

  Variable (X : Type).

  Implicit Types (l m : list X).

  (** Implementation of interleave using our tailored "induction on" tactic *)

  Definition itl_on_full l m : { k | k = itl_triv l m }.
  Proof.
    induction on l m as loop with measure (length l+length m).
    revert loop; refine (match l with
      | nil   => fun _    => exist _ m _
      | x::w => fun loop => let (r,Hr) := loop m w _ in exist _ (x::r) _
    end).
    * trivial.
    * simpl; omega.
    * subst; rewrite itl_triv_fix_1; trivial.
  Defined.

  Definition itl_on l m := proj1_sig (itl_on_full l m).

  Fact itl_on_spec l m : itl_on l m = itl_triv l m.
  Proof. apply (proj2_sig (itl_on_full _ _)). Qed.

  Hint Immediate itl_on_spec.

  Fact itl_on_fix_0 m : itl_on nil m = m.
  Proof. apply interleave_eq_triv_0; auto. Qed.

  Fact itl_on_fix_1 x l m : itl_on (x::l) m = x::itl_on m l.
  Proof. apply interleave_eq_triv_1; auto. Qed.
 
End itl_induction_on.

Extraction Inline itl_on_full.

Extraction itl_on.

