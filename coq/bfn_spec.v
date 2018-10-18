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
           (H0 : forall i l, l ~lt bfn_f i l)
           (H1 : forall i l, is_bfn_from i (bfn_f i l)).

  Theorem bfn_f_eq_0 i : bfn_f i nil = nil.
  Proof.
    symmetry; apply lbt_is_bfn_from_eq with i; auto.
    + (** there are two different [nil] in this goal *)
      apply lbt_eq_trans with (2 := H0 _ _); constructor.
    + red; rewrite bft_f_fix_0; simpl; constructor.
  Qed.

  Theorem bfn_f_eq_1 i x l : bfn_f i (leaf x::l) = leaf i :: bfn_f (S i) l.
  Proof.
    apply lbt_is_bfn_from_eq with i; auto.
    + apply lbt_eq_sym, lbt_eq_trans with (2 := H0 _ _); repeat constructor.
      apply lbt_eq_sym, H0.
    + red; rewrite bft_f_fix_oka_1; simpl.
      split; auto; apply H1.
  Qed.

  Theorem bfn_f_eq_2 i a x b l : exists an bn ln,
               bfn_f i (node a x b::l) = node an i bn :: ln
            /\  bfn_f (S i) (l++a::b::nil) = ln++an::bn::nil.
  Proof.
    generalize (H0 (S i) (l++a::b::nil)); intros H.
    apply Forall2_app_inv_l in H.
    destruct H as (ln & l1 & H2 & H3 & H4).
    destruct l1 as [ | an l1 ].
    { inversion H3. }
    apply Forall2_cons_inv in H3; destruct H3 as (H5 & H3).
    destruct l1 as [ | bn l1 ].
    { inversion H3. }
    apply Forall2_cons_inv in H3; destruct H3 as (H6 & H3).
    inversion H3; subst l1; clear H3.
    exists an, bn, ln; split; [| assumption].
    apply lbt_is_bfn_from_eq with i; [|apply H1|].
    + generalize (H0 (S i) (l++a::b::nil)); rewrite H4; intros G2.
      apply Forall2_2snoc_inv in G2; destruct G2 as (G2 & G3 & G4).
      apply lbt_eq_sym, lbt_eq_trans with (2 := H0 _ _), lbt_eq_sym; 
        repeat constructor; assumption.
    + red; rewrite bft_f_fix_oka_2; simpl.
      split; auto.
      generalize (H1 (S i) (l++a::b::nil)); rewrite H4; auto.
  Qed.

End bfn_NC.

Section bfn_SC. (* sufficient conditions, synthesis *)

  (* Assuming [bfn_f] satisfies the previous equations, 
     then [bfn_f] satisfies the functional spec of BFN *)
     
  Variable (X : Type) (bfn_f : nat -> list (bt X) -> list (bt nat))
           (H0 : forall i, bfn_f i nil = nil)
           (H1 : forall i x l, bfn_f i (leaf x::l) = leaf i :: bfn_f (S i) l)
           (H2 : forall i a x b l, exists an bn ln,
                 bfn_f i (node a x b::l) = node an i bn :: ln
               /\ bfn_f (S i) (l++a::b::nil) = ln++an::bn::nil).

  Theorem bfn_f_lt i l : l ~lt bfn_f i l.
  Proof.
    induction on i l as IH with measure (lsum l).
    destruct l as [ | [ x | a x b ] l ].
    + rewrite H0; constructor.
    + rewrite H1; repeat constructor.
      apply IH; simpl; omega.
    + destruct (H2 i a x b l) as (an & bn & ln & H3 & H4).
      rewrite H3.
      assert (lsum (l++a::b::nil) < lsum (node a x b :: l)) as D.
      { rewrite lsum_app; simpl; omega. }
      generalize (IH (S i) _ D); rewrite H4.
      intros H5.
      apply Forall2_2snoc_inv in H5; destruct H5 as (? & ? & ?).
      repeat constructor; assumption.
  Qed.

  Theorem bfn_f_bfn i l : is_bfn_from i (bfn_f i l).
  Proof.
    induction on i l as IH with measure (lsum l).
    destruct l as [ | [ x | a x b ] l ].
    + rewrite H0; red; rewrite bft_f_fix_0; simpl; constructor.
    + rewrite H1; red.
      rewrite bft_f_fix_oka_1; split; auto.
      apply IH; simpl; omega.
    + destruct (H2 i a x b l) as (an & bn & ln & H3 & H4).
      rewrite H3; red; rewrite bft_f_fix_oka_2; split; auto.
      rewrite <- H4; apply IH.
      rewrite lsum_app; simpl; omega.
  Qed.

End bfn_SC.
