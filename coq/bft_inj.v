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

Require Import List Arith Omega.
Require Import list_utils wf_utils bt bft_std bft_forest.

Section bft_any_inj.

  Variable X : Type.

  Implicit Types (l m : list (bt X)) (t : bt X).

  (** injectivity of [bft_f] given that the arguments are structurally equal *)

  Lemma bft_f_inj l m : l ~lt m -> bft_f l = bft_f m -> l = m.
  Proof.
    induction on l m as IH with measure (lsum (l++m)).
    revert l m IH; intros [ | t1 l ] [ | t2 m ] IH H; try (inversion H; fail); auto.
    Forall2 inv H as H12.
    do 2 rewrite bft_f_fix_4.
    destruct t1 as [ x | a1 x b1 ]; destruct t2 as [ y | a2 y b2 ]; try (inversion H12; fail); simpl.
    + intros E; inversion E; f_equal.
      do 2 rewrite <- app_nil_end in *.
      apply IH; auto.
      repeat rewrite lsum_app; simpl; omega.
    + apply bt_eq_node_inv in H12; destruct H12 as [ Ha Hb ].
      intros E; injection E; clear E; intros E ?; subst.
      apply IH in E.
      * apply f_equal with (f := @rev _) in E.
        repeat rewrite rev_app_distr in E; simpl in E.
        inversion E; subst; f_equal.
        rewrite <- (rev_involutive l), <- (rev_involutive m).
        f_equal; assumption.
      * repeat rewrite lsum_app; simpl; omega.
      * apply Forall2_app; auto.
  Qed.

  Theorem bft_forest_inj t1 t2 : t1 ~t t2 -> bft_forest t1 = bft_forest t2 -> t1 = t2.
  Proof. intros ? H; apply bft_f_inj in H; auto; inversion H; auto. Qed.

  Corollary bft_std_inj t1 t2 : t1 ~t t2 -> bft_std t1 = bft_std t2 -> t1 = t2.
  Proof. do 2 rewrite <- bft_forest_eq_bft_std; apply bft_forest_inj. Qed.

End bft_any_inj.

Fact lbt_is_bfn_from_eq n l m : l ~lt m -> is_bfn_from n l -> is_bfn_from n m -> l = m.
Proof.
  intros H1 H2 H3.
  apply bft_f_inj; auto.
  red in H2, H3.
  rewrite is_seq_from_spec in H2.
  rewrite is_seq_from_spec in H3.
  rewrite H2, H3.
  do 2 rewrite bft_f_length.
  f_equal.
  revert H1; apply lbt_eq_lsum.
Qed.

