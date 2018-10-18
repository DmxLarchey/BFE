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
Require Import list_utils wf_utils bt bft_forest bft_std bft_inj.

Set Implicit Arguments.

Section bfn_NC. (* necessary conditions *)

  (** We derive equations from the functional spec of BFN:

      the expected output of (bfn_f i l) is 
      a list ln such that l ~lt ln 
                      and is_bfn_from i ln *)

  Variable (X : Type) (bfn_f : nat -> list (bt X) -> list (bt nat))
           (H0 : forall i l, l ~lt rev (bfn_f i l))
           (H1 : forall i l, is_bfn_from i (rev (bfn_f i l))).

  Let H0' i l : rev l ~lt bfn_f i l.
  Proof.
    apply Forall2_rev_eq.
    rewrite rev_involutive.
    apply H0.
  Qed.

  Fact rev_inj K (l m : list K) : rev l = rev m -> l = m.
  Proof.
    intro. 
    rewrite <- (rev_involutive l), <- (rev_involutive m).
    f_equal; trivial.
  Qed.

  Theorem bfn_f_eq_0 i : bfn_f i nil = nil.
  Proof.
    apply rev_inj.
    symmetry; apply lbt_is_bfn_from_eq with i; simpl; auto.
    + apply lbt_eq_trans with (2 := H0 _ _); constructor.
    + red; rewrite bft_f_fix_0; simpl; constructor.
  Qed.

  Theorem bfn_f_eq_1 i x l : bfn_f i (leaf x::l) = bfn_f (S i) l ++ leaf i :: nil.
  Proof.
    apply rev_inj.
    rewrite rev_app_distr; simpl.
    apply lbt_is_bfn_from_eq with i; auto.
    + apply lbt_eq_sym, lbt_eq_trans with (2 := H0 _ _); repeat constructor.
      apply lbt_eq_sym, H0.
    + red; rewrite bft_f_fix_oka_1; simpl.
      split; auto; apply H1.
  Qed.

  Theorem bfn_f_eq_2 i a x b l : exists an bn ln,
               bfn_f (S i) (l++a::b::nil) = bn::an::ln
            /\ bfn_f i (node a x b::l) = ln ++ node an i bn :: nil.
  Proof.
    generalize (H0 (S i) (l++a::b::nil)); intros H.
    apply Forall2_rev in H.
    rewrite rev_involutive, rev_app_distr in H.
    simpl in H; revert H.
    case_eq (bfn_f (S i) (l ++ a :: b :: nil)).
    { inversion 2. }
    intros bn ln E H.
    apply Forall2_cons_inv in H.
    destruct H as (H2 & H).
    destruct ln as [ | an ln ].
    { inversion H. }
    apply Forall2_cons_inv in H.
    destruct H as (H3 & H4).
    exists an, bn, ln; split; auto.
    apply rev_inj.
    apply lbt_is_bfn_from_eq with i; auto.
    + apply lbt_eq_sym, lbt_eq_trans with (2 := H0 _ _), lbt_eq_sym.
      rewrite rev_app_distr.
      simpl; repeat constructor; auto.
      apply Forall2_rev_eq.
      rewrite rev_involutive; auto.
    + red; rewrite rev_app_distr; simpl. 
      rewrite bft_f_fix_oka_2; simpl.
      split; auto.
      generalize (H1 (S i) (l++a::b::nil)).
      rewrite E; simpl.
      rewrite app_ass; simpl; auto.
  Qed.

End bfn_NC.

Section bfn_SC. (* sufficient conditions, synthesis *)

  (* Assuming [bfn_f] satisfies the previous equations, 
     then [bfn_f] satisfies the functional spec of BFN *)
     
  Variable (X : Type) (bfn_f : nat -> list (bt X) -> list (bt nat))
           (H0 : forall i, bfn_f i nil = nil)
           (H1 : forall i x l, bfn_f i (leaf x::l) = bfn_f (S i) l ++ leaf i :: nil)
           (H2 : forall i a x b l, exists an bn ln,
                bfn_f (S i) (l++a::b::nil) = bn::an::ln
             /\ bfn_f i (node a x b::l) = ln ++ node an i bn :: nil).

  Theorem bfn_f_lt i l : l ~lt rev (bfn_f i l).
  Proof.
    induction on i l as IH with measure (lsum l).
    destruct l as [ | [ x | a x b ] l ].
    + rewrite H0; constructor.
    + rewrite H1, rev_app_distr; simpl. 
      repeat constructor.
      apply IH; simpl; omega.
    + destruct (H2 i a x b l) as (an & bn & ln & H3 & H4).
      rewrite H4, rev_app_distr; simpl.
      assert (lsum (l++a::b::nil) < lsum (node a x b :: l)) as D.
      { rewrite lsum_app; simpl; omega. }
      generalize (IH (S i) _ D); rewrite H3.
      simpl; rewrite app_ass; simpl; intros H5.
      apply Forall2_2snoc_inv in H5; destruct H5 as (? & ? & ?).
      repeat constructor; assumption.
  Qed.

  Theorem bfn_f_bfn i l : is_bfn_from i (rev (bfn_f i l)).
  Proof.
    induction on i l as IH with measure (lsum l).
    destruct l as [ | [ x | a x b ] l ].
    + rewrite H0; red; rewrite bft_f_fix_0; simpl; constructor.
    + rewrite H1, rev_app_distr; simpl; red.
      rewrite bft_f_fix_oka_1; split; auto.
      apply IH; simpl; omega.
    + destruct (H2 i a x b l) as (an & bn & ln & H3 & H4).
      rewrite H4, rev_app_distr; simpl; red.
      rewrite bft_f_fix_oka_2; split; auto.
      replace (rev ln++an::bn::nil) with (rev (bn::an::ln)).
      * rewrite <- H3; apply IH.
        rewrite lsum_app; simpl; omega.
      * simpl; rewrite app_ass; auto.
  Qed.

End bfn_SC.
