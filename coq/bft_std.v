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

(** 
*)

Require Import List Arith Omega Extraction.
Require Import list_utils zip bt sorted increase.

Set Implicit Arguments.

(** The standard Breadth First Search algorithm on a binary
    tree with a specification: it returns the values on nodes where
    nodes are sorted in length order then lexicographic order on 
    their corresponding branches *)

Section breadth_first_traversal_standard.

  Context (X : Type).
 
  Implicit Type (t : bt X) (l : list bool) (ll : list (bt X)) (rl rm: list(list X)).

  (** This is the standard/obvious specification of breadth-first traversal *)

  Fixpoint niveaux t : list (list X) :=
    match t with 
      | leaf x     => (x::nil) :: nil
      | node a x b => (x::nil) :: zip (@app _) (niveaux a) (niveaux b)
    end.

  Fact length_niveaux t : list_sum (map (@length _) (niveaux t)) = m_bt t.
  Proof.
    induction t as [ x | a Ha x b Hb ]; simpl; auto.
    rewrite map_zip_length, zip_list_sum; do 2 f_equal; trivial.
  Qed.
    
  Definition bft_std t : list X := concat (niveaux t).

  Fact bft_std_length t : length (bft_std t) = m_bt t.
  Proof.
    unfold bft_std.
    rewrite length_concat.
    apply length_niveaux.
  Qed.

  (** Now for the branches instead of just the elements: niveaux and then breadth-first traversal *)

  Fixpoint niveaux_br (t : bt X) : list (list (list bool)) :=
    match t with 
      | leaf _     => (nil::nil) :: nil
      | node a _ b => (nil::nil) :: zip (@app _) (map (map (cons false)) (niveaux_br a))
                                                 (map (map (cons true))  (niveaux_br b))
    end.

  Lemma niveaux_br_niveaux t : Forall2 (Forall2 (bt_path_node t)) (niveaux_br t) (niveaux t).
  Proof.
    induction t as [ | ? Hu ? ? Hv ]; simpl; repeat constructor.
    apply Forall2_zip_app; apply Forall2_map_left;
      [ revert Hu | revert Hv ]; apply Forall2_mono;
      intros ? ? G; apply Forall2_map_left; revert G;
      apply Forall2_mono; constructor; auto.
  Qed.

  Lemma niveaux_br_spec_0 l t : btb t l -> In l (concat (niveaux_br t)).
  Proof.
    induction 1 as [ t | | ].
    + apply in_concat_iff; exists (nil::nil); destruct t; simpl; auto.
    + simpl; right; apply In_concat_zip_app_left; rewrite <- map_concat; apply in_map; assumption.
    + simpl; right; apply In_concat_zip_app_right; rewrite <- map_concat; apply in_map; assumption.
  Qed. 

  Corollary niveaux_br_spec_1 t : forall l llb, In l llb -> In llb (niveaux_br t) -> btb t l.
  Proof.
    intros l ll H1 H2.
    destruct Forall2_In_inv_left with (1 := niveaux_br_niveaux t) (2 := H2) as (? & ? & H3).
    destruct Forall2_In_inv_left with (1 := H3) (2 := H1) as (? & ? & ?).
    apply btb_spec; firstorder.
  Qed.
  
  Fact niveaux_br_increase t : increase (fun n llb => Forall (fun l => length l = n) llb) 0 (niveaux_br t).
  Proof.
    induction t as [ | u Hu x v Hv ]; simpl.
    + do 2 constructor; auto.
    + constructor.
      * constructor; auto.
      * apply zip_increase.
        1: intros; apply Forall_app; auto.
        1,2 : apply map_increase; try assumption; 
            intros ? ? G; apply Forall_map; simpl;
            revert G; apply Forall_impl; intros; omega.
  Qed.

  Fact niveaux_br_sorted t : Forall (sorted lb_lex) (niveaux_br t).
  Proof.
    induction t as [ x | u Hu x v Hv ]; simpl.
    + repeat constructor.
    + constructor.
      * repeat constructor.
      * apply zip_monotone.
        - apply Forall_map; revert Hu; apply Forall_impl.
          intros; apply sorted_map; auto.
          intros; constructor; auto.
        - apply Forall_map; revert Hv; apply Forall_impl.
          intros; apply sorted_map; auto.
          intros; constructor; auto.
        - rewrite Forall_forall in Hu, Hv.
          intros ? ?; do 2 rewrite in_map_iff;
            intros (? & ? & ?) (? & ? & ?); subst.
          apply sorted_app.
          ++ intros ? ?; do 2 rewrite in_map_iff;
             intros (? & ? & ?) (? & ? & ?); subst; constructor.
          ++ apply sorted_map; auto; intros; constructor; auto.
          ++ apply sorted_map; auto; intros; constructor; auto.
  Qed.

  Definition bft_br t : list (list bool) := concat (niveaux_br t).

  (** [bft_br] corresponds to [bft_std] *)

  Theorem bft_br_std t : Forall2 (bt_path_node t) (bft_br t) (bft_std t).
  Proof. apply Forall2_concat, niveaux_br_niveaux. Qed.

  Corollary bft_br_length t : length (bft_br t) = m_bt t.
  Proof.
    rewrite <- bft_std_length.
    generalize (bft_br_std t); apply Forall2_length.
  Qed.
 
  (** [bft_br t] contains the branches of [t] *)

  Fact bft_br_spec l t : In l (bft_br t) <-> btb t l.
  Proof.
    unfold bft_br; split.
    + rewrite in_concat_iff; intros (? & H1 & H2); revert H1 H2; apply niveaux_br_spec_1.
    + apply niveaux_br_spec_0.
  Qed.

  Hint Resolve niveaux_br_increase niveaux_br_sorted.

  (** The list of branches generated by [bft_br] is sorted according to [bft_order]. *)

  Theorem bft_br_sorted t : sorted bft_order (bft_br t).
  Proof.
    apply concat_sorted with (P := fun n llb => Forall (fun l => length l = n) llb) (n := 0); auto.
    + intros i j x l y m; do 2 rewrite Forall_forall; intros H1 H2 H3 H4 H5.
      apply H2 in H4; apply H3 in H5; left; omega.
    + generalize (niveaux_br_sorted t).
      do 2 rewrite Forall_forall.
      intros H l Hl; generalize (H _ Hl).
      apply sorted_mono.
      intros x y H1 H2 H3; right; split; auto.
      generalize (niveaux_br_increase t); intros H4.
      apply increase_inv with (2 := Hl) in H4.
      destruct H4 as (k & _ & H4).
      rewrite Forall_forall in H4.
      repeat rewrite H4; auto.
  Qed.

End breadth_first_traversal_standard.

(*
Check bft_br_spec.
Check bft_br_sorted.
Check bft_br_std.
*)

