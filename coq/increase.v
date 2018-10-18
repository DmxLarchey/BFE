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

Require Import List Arith Omega Wellfounded Permutation.

Require Import list_utils zip sorted.

Set Implicit Arguments.

Section increase.
 
  Variable (X : Type) (P : nat -> X -> Prop).

  Inductive increase : nat -> list X -> Prop :=
    | in_increase_0 : forall n, increase n nil
    | in_increase_1 : forall n x l, P n x -> increase (S n) l -> increase n (x::l).

  Fact increase_inv n l x : increase n l -> In x l -> exists k, n <= k /\ P k x.
  Proof.
    intros H Hx; revert H; induction 1 as [ n | n y l H1 H2 IH2 ]; simpl.
    + destruct Hx.
    + destruct Hx as [ | Hx ]; subst.
      * exists n; split; auto.
      * destruct IH2 as (k & ? & ?); auto.
        exists k; split; auto; omega.
  Qed.

  Section zip.

     Variable (f : X -> X -> X) (Hf : forall n x y, P n x -> P n y -> P n (f x y)).

     Fact zip_increase l m n : increase n l -> increase n m -> increase n (zip f l m).
     Proof.
       intros H; revert H m.
       induction 1 as [ n | n x l H1 H2 IH2 ]; simpl; intros m Hm; auto.
       destruct m as [ | y m ]; simpl.
       * constructor; auto.
       * constructor; inversion Hm; auto.
     Qed.

  End zip.

  Section map.

    Variable (f : X -> X) (Hf : forall n x, P n x -> P (S n) (f x)).

    Fact map_increase n l : increase n l -> increase (S n) (map f l).
    Proof. induction 1; simpl; constructor; auto. Qed.

  End map.

End increase.

Section sorted_concat.

  Variable (X : Type) (P : nat -> list X -> Prop) (R : X -> X -> Prop) 
           (HPR : forall i j x l y m, i < j -> P i l -> P j m -> In x l -> In y m -> R x y).

  Fact concat_sorted n ll : increase P n ll -> Forall (sorted R) ll -> sorted R (concat ll).
  Proof.
    induction 1 as [ n | n l ll H1 H2 IH2 ]; simpl.
    + constructor.
    + inversion 1; subst.
      apply sorted_app; auto.
      intros x y; rewrite in_concat_iff.
      intros G1 (m & G2 & G3).
      apply increase_inv with (2 := G3) in H2.
      destruct H2 as (k & H0 & H2).
      revert G1 G2; apply (@HPR n k); auto.
  Qed.

End sorted_concat.

