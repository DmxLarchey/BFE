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

Require Import List Arith Omega Extraction.
Require Import wf_utils.

Set Implicit Arguments.

Section interleave.

  Variable (X : Type).

  Implicit Types (l m : list X).

  Fixpoint itl1 l m :=
    match l, m with
      | nil, _       => m
      | x::l', y::m' => x::y::itl1 l' m'
      | _, _         => l
    end.

  Fact itl1_eq x l m : itl1 (x::l) m = x::itl1 m l.
  Proof.
    revert m x.
    induction l as [ | a l IHl ]; 
    induction m as [ | b m IHm ]; intros x; try (simpl; auto; fail).
    simpl itl1 at 2; rewrite <- IHl; auto.
  Qed.

  Definition itl2_full l m : { r | r = itl1 l m }.
  Proof.
    induction on l m as loop with measure (length l+length m).
    revert loop; refine (match l with
      | nil   => fun _    => exist _ m _
      | x::l' => fun loop => let (r,Hr) := loop m l' _ in exist _ (x::r) _
    end).
    + trivial.
    + simpl; omega.
    + subst; rewrite itl1_eq; trivial.
  Defined.

  Definition itl2 l m := proj1_sig (itl2_full l m).

  Fact itl2_spec l m : itl2 l m = itl1 l m.
  Proof. apply (proj2_sig (itl2_full _ _)). Qed.

End interleave.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction Inline itl2_full.

Recursive Extraction itl1 itl2.
