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
Require Import list_utils wf_utils bt fifo bft_forest bft_std.

Set Implicit Arguments.

Module BFR_FIFO (Q: FIFO).

Section bfr_fifo.

  Export Q.

  Variable (X Y : Type).

  Implicit Type (q : fifo (bt X)) (ll : list Y).

  Fixpoint bfr_fifo_f q (ll : list Y) { struct ll } : 
            fifo_lsum q = length ll
         -> { q'  | f2l q ~lt rev (f2l q')
                /\ bft_f (rev (f2l q')) = ll }.
  Proof.
    refine (match ll with 
      | nil   => fun Hll => let (q',Hq')   := empty _ 
                            in  exist _ q' _
      | y::mm => fun Hll => let (d1,Hd1) := @deq _ q _ 
                            in  _
    end).
    all: cycle 2.
    revert Hd1; refine (match d1 with (t,p1) => _ end); intros Hp1.
    rewrite Hp1 in Hll; simpl in Hll; clear d1.
    revert Hll Hp1; refine (match t with 
      | leaf x     => fun Hll Hp1 => let (q',Hq')   := bfr_fifo_f p1 mm _ in 
                                     let (q1,Hq1) := enq q' (leaf y) 
                                     in  exist _ q1 _
      | node a x b => fun Hll Hp1 => let (p2,Hp2) := enq p1 a           in
                                     let (p3,Hp3) := enq p2 b           in
                                     let (q',Hq')   := bfr_fifo_f p3 mm _ in  
                                     let (d2,Hd2) := @deq _ q' _     
                                     in  _
    end); auto.
    all: cycle 3.
    revert Hd2; refine (match d2 with 
      | (u,q1) => fun Hd2 => let (d3,Hd3) := @deq _ q1 _ 
                             in  _ 
    end).
    all: cycle 1.
    revert Hd3; refine (match d3 with
      | (v,q2) => fun Hd3 => let (q3,Hq3) := enq q2 (node v y u) 
                             in  exist _ q3 _
    end).
    all: cycle 1.

    * revert Hll; rewrite Hq'; simpl.
      generalize (f2l q).
      intros [ | [] ? ]; simpl; try discriminate.
      split; auto.
      rewrite bft_f_fix_oka_0; reflexivity.
    * intros E; rewrite E in Hll; discriminate.
    * destruct Hq' as (Hq2 & Hq3).
      rewrite Hp1, Hq1, rev_app_distr; split; simpl; auto.
      rewrite bft_f_fix_oka_1, Hq3; auto.
    * rewrite Hp3, Hp2; do 2 rewrite lsum_app; simpl in Hll |- *; omega.
    * destruct Hq' as (Hq_1 & Hq_2); 
      apply Forall2_rev in Hq_1; rewrite rev_involutive in Hq_1.
      intros H; rewrite H, Hp3, rev_app_distr in Hq_1; inversion Hq_1.
    * destruct Hq' as (Hq_1 & Hq_2).
      apply Forall2_rev in Hq_1; rewrite rev_involutive in Hq_1.
      intros H; rewrite Hd2, H, Hp3, Hp2 in Hq_1. 
      do 2 rewrite rev_app_distr in Hq_1.
      inversion Hq_1.
      inversion H5.
    * destruct Hq' as (Hq_1 & Hq_2).
      apply Forall2_rev in Hq_1; rewrite rev_involutive in Hq_1.
      simpl in *.
      rewrite Hp1, Hq3, rev_app_distr; simpl.
      rewrite Hp3, Hp2, Hd2, Hd3 in Hq_1.
      do 2 rewrite rev_app_distr in Hq_1.
      simpl in Hq_1.
      apply Forall2_cons_inv in Hq_1; destruct Hq_1 as (Hq_3 & Hq_1).
      apply Forall2_cons_inv in Hq_1; destruct Hq_1 as (Hq_4 & Hq_1).
      apply Forall2_rev in Hq_1; rewrite rev_involutive in Hq_1.
      split; auto.
      rewrite bft_f_fix_oka_2; simpl; f_equal.
      rewrite <- Hq_2, Hd2, Hd3; f_equal; simpl.
      rewrite app_ass; reflexivity.
  Defined.
  
  Section bfr.

    Let bfr_fifo_full (t : bt X) (l : list Y) : m_bt t = length l -> { t' | t ~t t' /\ bft_forest t' = l }.
    Proof.
      intros H.
      refine (let (p,Hp) := @empty _         in
              let (q,Hq) := enq p t          in 
              let (r,Hr) := bfr_fifo_f q l _ in
              let (d1,Hd1) := @deq _ r _ 
              in _).
      all: cycle 2.
      revert Hd1; refine(match d1 with
        | (t',q') => fun Hd1 => exist _ t' _
      end).
      all: cycle 1.

      + rewrite Hq, Hp, <- H; simpl; omega.
      + intros E; rewrite E in Hr; apply proj2 in Hr; simpl in Hr.
        rewrite bft_f_fix_0 in Hr; subst.
        generalize (m_bt_ge_1 t); simpl in *; omega.
      + destruct Hr as (Hr_1 & Hr_2); simpl in Hd1.
        apply Forall2_rev in Hr_1.
        rewrite Hq, Hp, rev_involutive, Hd1 in Hr_1; simpl in Hr_1.
        apply Forall2_cons_inv in Hr_1.
        destruct Hr_1 as (Hr_3 & Hr_1).
        apply Forall2_nil_inv_right in Hr_1.
        split; auto.
        rewrite Hd1, Hr_1 in Hr_2.
        simpl in Hr_2; auto.
    Qed.

    Definition bfr_fifo t l H := proj1_sig (bfr_fifo_full t l H).

    Fact bfr_fifo_spec_1 t l H : t ~t bfr_fifo t l H.
    Proof. apply (proj2_sig (bfr_fifo_full t l H)). Qed.

    Fact bfr_fifo_spec_2 t l H : bft_std (bfr_fifo t l H) = l.
    Proof.
      rewrite <- bft_forest_eq_bft_std. 
      apply (proj2_sig (bfr_fifo_full t l H)). 
    Qed.

  End bfr.

End bfr_fifo.

(*
Check bfr_fifo.
Check bfr_fifo_spec_1.
Check bfr_fifo_spec_2.
*)

End BFR_FIFO.
