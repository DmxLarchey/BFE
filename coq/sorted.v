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

Require Import list_utils.

Set Implicit Arguments.

Section sorted.

  Variable (X : Type) (R : X -> X -> Prop).

  Inductive sorted : list X -> Prop :=
    | in_sorted_0 : sorted nil
    | in_sorted_1 : forall x l, Forall (R x) l -> sorted l -> sorted (x::l).

  Fact sorted_app l m : (forall x y, In x l -> In y m -> R x y) -> sorted l -> sorted m -> sorted (l++m).
  Proof.
    intros H H1 Hm; revert H1 H.
    induction 1 as [ | x l H1 H2 IH2 ]; intros H3; simpl; auto.
    constructor.
    + apply Forall_app; auto.
      apply Forall_forall; intros; apply H3; simpl; auto.
    + apply IH2; intros; apply H3; simpl; auto.
  Qed.

  Variable (f : X -> X) (Hf : forall x y, R x y -> R (f x) (f y)).

  Fact sorted_map l : sorted l -> sorted (map f l).
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; simpl; constructor; auto.
    apply Forall_forall.
    rewrite Forall_forall in H1.
    intros y; rewrite in_map_iff.
    intros (? & ? & ?); subst; auto.
  Qed.

End sorted.

Fact sorted_mono X (R S : X -> X -> Prop) l : (forall x y, In x l -> In y l -> R x y -> S x y) -> sorted R l -> sorted S l.
Proof.
  intros H1 H2; revert H2 H1.
  induction 1 as [ | x l H1 H2 IH2 ]; intros H3.
  + constructor.
  + constructor.
    * revert H1; do 2 rewrite Forall_forall.
      intros H1 y Hy; apply H3; simpl; auto.
    * apply IH2; intros ? ? ? ?; apply H3; simpl; auto.
Qed.

Section list_has_dup.

  Variable (X : Type).

  Implicit Types (l m : list X).
  
  Inductive list_has_dup : list X -> Prop :=
    | in_list_hd0 : forall l x, In x l -> list_has_dup (x::l)
    | in_list_hd1 : forall l x, list_has_dup l -> list_has_dup (x::l).
  
  Fact list_hd_cons_inv x l : list_has_dup (x::l) -> In x l \/ list_has_dup l.
  Proof. inversion 1; subst; auto. Qed.
  
  Fact list_has_dup_app_left l m : list_has_dup m -> list_has_dup (l++m).
  Proof. induction l; simpl; auto; constructor 2; auto. Qed.
  
  Fact list_has_dup_app_right l m : list_has_dup l -> list_has_dup (l++m).
  Proof. 
    induction 1; simpl.
    + constructor 1; apply in_or_app; left; auto.
    + constructor 2; auto.
  Qed.

  Fact perm_list_has_dup l m : l ~p m -> list_has_dup l -> list_has_dup m.
  Proof.
    induction 1 as [ | x l m H1 IH1 | x y l | ]; auto; 
      intros H; apply list_hd_cons_inv in H.
    + destruct H as [ H | H ].
      * apply Permutation_in with (1 := H1) in H.
        apply in_list_hd0; auto.
      * apply in_list_hd1; auto.
    + destruct H as [ [ H | H ] | H ]; subst.
      * apply in_list_hd0; left; auto.
      * apply in_list_hd1, in_list_hd0; auto.
      * apply list_hd_cons_inv in H.
        destruct H as [ H | H ].
        - apply in_list_hd0; right; auto.
        - do 2 apply in_list_hd1; auto.
  Qed.

  Fact list_has_dup_eq_duplicates m: list_has_dup m <-> exists x aa bb cc, m = aa++x::bb++x::cc.
  Proof.
    split.
    + induction 1 as [ m x Hm | m x _ IHm ].
      - apply in_split in Hm.
        destruct Hm as (bb & cc & Hm).
        exists x, nil, bb, cc; subst; auto.
      - destruct IHm as (y & aa & bb & cc & IHm).
        exists y, (x::aa), bb, cc; subst; auto.
    + intros (x & aa & bb & cc & Hm).
      subst m.
      apply list_has_dup_app_left.
      constructor 1; apply in_or_app; right.
      constructor 1; reflexivity.
  Qed.

End list_has_dup.

Section sorted_no_dup.
 
  Variables (X : Type) (R : X -> X -> Prop) (HR : forall x, ~ R x x).

  Lemma sorted_no_dup l : sorted R l -> ~ list_has_dup l.
  Proof.
    induction 1 as [ | x l H1 H2 IH2 ]; intros H.
    + inversion H.
    + apply list_hd_cons_inv in H.
      destruct H as [ H | H ]; try tauto.
      rewrite Forall_forall in H1; firstorder.
  Qed.

End sorted_no_dup.

Section no_dup_sorted_with_ineq.

  Variables (X : Type).
  
  Let R := fun (x y: X) => x <> y.

  (** for this specific relation, not having duplicates is equivalent to being sorted: *)

  Lemma no_dup_sorted_with_ineq l: sorted R l <-> ~ list_has_dup l.
  Proof.
    split.
    * apply sorted_no_dup; intros ? []; trivial.
    * induction l as [ | x l IHl].
      - constructor.
      - intros H; constructor.
        + rewrite Forall_forall.
          intros y Hy ?; subst.
          apply H.
          constructor 1; trivial.
        + apply IHl; contradict H.
          constructor 2; trivial.
  Qed.

End no_dup_sorted_with_ineq.

Section no_dups_eq_perm.
  
  Variables (X : Type). 

  Lemma no_dups_eq_perm (l m : list X) : 
        (forall x, In x l <-> In x m)
     -> ~ list_has_dup l
     -> ~ list_has_dup m
     -> l ~p m.
  Proof.
    revert m; induction l as [ | x l IH ]; intros m H1 H2 H3.
    * destruct m as [ | y m ].
      + constructor.
      + exfalso; apply (H1 y); simpl; auto.
    * assert (In x m) as Hm.
      { apply H1; simpl; auto. }
      apply in_split in Hm.
      destruct Hm as (m1 & m2 & ?); subst.
      assert (~ In x l) as H4.
      { contradict H2; constructor 1; auto. }
      assert (~ In x m1) as H5.
      { contradict H3.
        apply in_split in H3.
        destruct H3 as (p1 & p2 & ?); subst.
        apply list_has_dup_eq_duplicates.
        exists x,p1,p2,m2; rewrite app_ass; auto. }
      assert (~ In x m2) as H6.
      { contradict H3.
        apply in_split in H3.
        destruct H3 as (p1 & p2 & ?); subst.
        apply list_has_dup_eq_duplicates.
        exists x,m1,p1,p2; auto. }
      apply Permutation_cons_app, IH.
      + intros y; split.
        - intros G1.
          generalize (proj1 (H1 y) (or_intror G1)).
          intros G2.
          apply in_app_or in G2.
          apply in_or_app.
          destruct G2 as [|[|]]; subst; tauto.
        - intros G1.
          generalize (proj2 (H1 y)); intros G2.
          apply in_app_or in G1.
          destruct G2; subst; try tauto.
          apply in_or_app; simpl; tauto.
      + contradict H2; constructor 2; auto.
      + contradict H3.
        apply perm_list_has_dup with (1 := Permutation_middle _ _ _).
        constructor 2; auto.
  Qed.

End no_dups_eq_perm.

Section sorted_perm.

  Variables (X : Type) (R S : X -> X -> Prop) (l m : list X) 
            (Hlm : forall x, In x l <-> In x m)
            (HR : forall x, ~ R x x) 
            (HS : forall x, ~ S x x)
            (Hl : sorted R l) (Hm : sorted S m).

  Theorem sorted_perm : l ~p m.
  Proof. 
    apply no_dups_eq_perm; auto.
    + apply sorted_no_dup with (1 := HR); trivial.
    + apply sorted_no_dup with (1 := HS); trivial.
  Qed.

End sorted_perm.
