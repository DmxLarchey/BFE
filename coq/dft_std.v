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
Require Import list_utils bt sorted.

Set Implicit Arguments.

(** The very standard Depth First Search algorithm on a binary
    tree with a specification: it returns the values on nodes where
    nodes are sorted in lexicographic order of their corresponding
    branches. *)

Section dft_std.

  Variable X : Type.

  Implicit Types (l : list bool) (ll: list (list bool)) (t : bt X).

  (* Depth first traversal, VERY standard algo *)

  Fixpoint dft_std t : list X :=
    match t with 
      | leaf x => x::nil
      | node u x v => x::dft_std u++dft_std v
    end.

  Fact dft_std_length t : length (dft_std t) = m_bt t.
  Proof. induction t; simpl; repeat rewrite app_length; omega. Qed.

  (* The tree branches by Depth First Traversal *)

  Fixpoint dft_br t : list (list bool) :=
    nil::match t with 
           | leaf _     => nil
           | node u _ v => map (cons false) (dft_br u) ++ map (cons true) (dft_br v)
         end.

  (* dft_br corresponds to dft_std *)

  Theorem dft_br_std t : Forall2 (bt_path_node t) (dft_br t) (dft_std t).
  Proof.
    induction t as [ | ? Hu ? ? Hv ]; simpl; repeat constructor.
    apply Forall2_app; apply Forall2_map_left; [ revert Hu | revert Hv ];
      apply Forall2_mono; constructor; auto.
  Qed.

  (* number of branches equals size of tree *)

  Fact dft_br_length t : length (dft_br t) = m_bt t.
  Proof. rewrite (Forall2_length (dft_br_std t)), dft_std_length; trivial. Qed.

  (* dft_br lists the branches of t *)

  Fact dft_br_spec l t : In l (dft_br t) <-> btb t l.
  Proof.
    split.
    + intros Hl; rewrite btb_spec.
      destruct Forall2_In_inv_left with (1 := dft_br_std t) (2 := Hl) as (x & ? & ?).
      exists x; auto.
    + induction 1 as [ [] | | ]; simpl; auto; right; apply in_or_app;
        [ left | right ]; apply in_map; auto.
   Qed.

  Corollary dft_br_spec_1 t : Forall (btb t) (dft_br t).
  Proof. rewrite Forall_forall; intro; apply dft_br_spec. Qed.

  (* the branches of t in dft_br t are sorted according to lb_lex *)

  Fact dft_br_sorted t : sorted lb_lex (dft_br t).
  Proof.
    induction t; simpl.
    + do 2 constructor.
    + constructor.
      * apply Forall_app; rewrite Forall_forall; intro; 
          rewrite in_map_iff; intros (? & ? & ?); subst; constructor.
      * apply sorted_app.
        - intros ? ?; do 2 rewrite in_map_iff.
          intros (? & ? & ?) (? & ? & ?); subst; constructor.
        - apply sorted_map; auto; constructor; auto.
        - apply sorted_map; auto; constructor; auto.
  Qed.

End dft_std.

(*
Recursive Extraction dft_std.

Check dft_br_spec.
Check dft_br_sorted.
Check dft_br_std.
*)