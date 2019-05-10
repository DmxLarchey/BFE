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

Require Import wf_utils.

Set Implicit Arguments.

Section lazy_list.

  (* Implementation of lazy lists as the subset of co-lists 
     characterized by a finiteness predicate *)

  Variable X : Type.

  CoInductive llist : Type :=
    | lnil : llist
    | lcons : X -> llist -> llist.

  Implicit Types (a: X) (s: llist) (l: list X).

  Unset Elimination Schemes.
    
  Inductive lfin : llist-> Prop :=
    | lfin_nil :  lfin lnil
    | lfin_cons : forall a ll, lfin ll -> lfin (lcons a ll).

  Arguments lfin_cons : clear implicits.

  Set Elimination Schemes.

  Section small_inversions.

    Let shape_inv s := match s with lnil => False | _         => True   end.
    Let pred_inv s  := match s with lnil => lnil  | lcons x s => s      end.
    
    Definition lfin_inv x s (H : lfin (lcons x s)) : lfin s :=
      match H in lfin s return shape_inv s -> lfin (pred_inv s) with
        | lfin_nil         => fun E => match E with end
        | lfin_cons _ _ H1 => fun _ => H1
      end I.

    Let output_invert s : lfin s -> Prop := 
      match s as s' return lfin s' -> _ with
        | lnil      => fun H => lfin_nil = H
        | lcons x s => fun H => exists H', lfin_cons x s H' = H
      end.

    Definition lfin_invert s H : @output_invert s H :=
      match H in lfin s return @output_invert s H with
        | lfin_nil         => eq_refl
        | lfin_cons _ _ H' => ex_intro _ H' eq_refl 
      end.

  End small_inversions.

  (** We show proof irrelevance for lfin by induction/inversion
      where inversion is obtained by dependent pattern matching 

      Interesting case because lfin is not a decidable predicate
      but nevertheless has provable PIRR 
    *)

  Fixpoint lfin_pirr s (H1 : lfin s) : forall H2, H1 = H2.
  Proof.
    destruct H1 as [ | x s H1 ]; intros H2.
    + apply (lfin_invert H2).
    + destruct (lfin_invert H2) as (H & E).
      subst; f_equal; apply lfin_pirr.
  Defined.

  Section lfin_rect.

    (** We show dependent recursion principle for lfin implementing
        what a command like

        Scheme lfin_rect := Induction for lfin Sort Type.

        But Scheme is not smart enough to invent PIRR ...
        Remark that we use singleton elimination here ... *)

    Variable P : forall s, lfin s -> Type.

    Hypothesis HP1 : @P _ lfin_nil.
    Hypothesis HP2 : forall x s H, @P s H -> P (@lfin_cons x s H).

    Ltac pirr := match goal with |- @P _ ?a -> @P _ ?b => rewrite (@lfin_pirr _ a b); trivial end.

    Fixpoint lfin_rect s H { struct H } : @P s H.
    Proof.
      revert H.
      refine (match s with
        | lnil      => fun H => _
        | lcons x s => fun H => _
      end).
      + generalize HP1; pirr.
      + generalize (@HP2 x s (lfin_inv H) (@lfin_rect s (lfin_inv H))); pirr.
    Defined.

  End lfin_rect.

  (* Now we define lazy lists *)

  Definition lazy_list := { s | lfin s }.

  Implicit Type ll : lazy_list.

  (* Constructors *)

  Definition lazy_nil : lazy_list := exist _ _ lfin_nil.
  Definition lazy_cons a : lazy_list -> lazy_list.
  Proof.
    intros (ll & H).
    exists (lcons a ll).
    apply lfin_cons, H.
  Defined.

  (* Injectivity of constructors *)

  Fact lazy_cons_inj a b ll1 ll2 : lazy_cons a ll1 = lazy_cons b ll2 -> a = b /\ ll1 = ll2.
  Proof.
    revert ll1 ll2; intros (s1 & H1) (s2 & H2); simpl.
    intros E; apply f_equal with (f := @proj1_sig _ _) in E; simpl in E.
    inversion E; subst; split; auto; f_equal.
    apply lfin_pirr.
  Qed.

  Fact lazy_nil_cons_discr a ll : lazy_nil <> lazy_cons a ll.
  Proof. destruct ll; discriminate. Qed.

  (** And a dependent recursion principle similar to list_rect *)

  Section lazy_list_rect.

    Variable P : lazy_list -> Type.
    
    Hypothesis (HP0 : P lazy_nil).
    Hypothesis (HP1 : forall a m, P m -> P (lazy_cons a m)).

    Theorem lazy_list_rect : forall ll, P ll.
    Proof. 
      intros (? & H). 
      induction H as [ | x s H IH ].
      + apply HP0.
      + apply HP1 with (1 := IH).
    Defined.

  End lazy_list_rect.

  (* We have everything to define an isomorphism between list and lazy_list *)

  Section list_lazy_iso.

    Fixpoint list2lazy l :=
      match l with
        | nil  => lazy_nil
        | x::l => lazy_cons x (list2lazy l)
      end.

    Fact list2lazy_inj l m : list2lazy l = list2lazy m -> l = m.
    Proof.
      revert m; induction l as [ | a l IH ]; intros [ | b m ]; simpl; auto.
      + intros H; exfalso; revert H; apply lazy_nil_cons_discr.
      + intros H; exfalso; symmetry in H; revert H; apply lazy_nil_cons_discr.
      + intros H; apply lazy_cons_inj in H; destruct H; f_equal; auto.
    Qed.

    Section lazy2list.

      Let lazy2list_rec ll : { l | ll = list2lazy l }.
      Proof.
        induction ll as [ | a ll (l & Hl) ] using lazy_list_rect.
        + exists nil; auto.
        + exists (a::l); simpl; f_equal; auto.
      Qed.

      Definition lazy2list ll := proj1_sig (lazy2list_rec ll).

      Fact list2lazy2list ll : ll = list2lazy (lazy2list ll).
      Proof. apply (proj2_sig (lazy2list_rec ll)). Qed.

    End lazy2list.

    Fact lazy2list2lazy l : l = lazy2list (list2lazy l).
    Proof. apply list2lazy_inj; rewrite <- list2lazy2list; trivial. Qed.

    (* Fixpoint equations *)

    Fact lazy2list_nil : lazy2list lazy_nil = nil.
    Proof. apply list2lazy_inj; rewrite <- list2lazy2list; auto. Qed.

    Fact lazy2list_cons a ll : lazy2list (lazy_cons a ll) = a :: lazy2list ll.
    Proof.
      apply list2lazy_inj.
      simpl; repeat rewrite <- list2lazy2list; trivial.
    Qed.

  End list_lazy_iso.

  Definition lazy_length ll := length (lazy2list ll).
  
  Fact lazy_length_nil : lazy_length lazy_nil = 0.
  Proof. unfold lazy_length; rewrite lazy2list_nil; auto. Qed.

  Fact lazy_length_cons x ll : lazy_length (lazy_cons x ll) = S (lazy_length ll).
  Proof. unfold lazy_length; rewrite lazy2list_cons; auto. Qed.

End lazy_list.

Arguments lazy_nil {X}.

Section Rotate.

  (** From "Simple and Efficient Purely Functional Queues and Deques" by Chris Okasaki 
      See application in file fifo_3llists.v *)

  Variable (X : Type).
  
  Implicit Type (l r m a : lazy_list X).
  
  Let prec l r := lazy_length r = 1 + lazy_length l.
  Let spec l r a m := lazy2list m = lazy2list l ++ rev (lazy2list r) ++ lazy2list a.

  Definition lazy_rotate l r : forall a, prec l r -> sig (spec l r a).
  Proof.
    induction on l r as loop with measure (lazy_length l); intros a.
    induction r as [ | y r' _ ] using lazy_list_rect; intros H.
    + exfalso; red in H; revert H; rewrite lazy_length_nil; intros; omega.
    + revert H.
      induction l as [ | x l' _ ] using lazy_list_rect; intros H.
      * exists (lazy_cons y a); red in H |- *.
        assert (r' = lazy_nil); [ | subst ].
        { revert H.
          induction r' as [ | ? r' ] using lazy_list_rect; auto.
          do 2 rewrite lazy_length_cons.
          rewrite lazy_length_nil; simpl; intros; omega. }
        do 2 rewrite lazy2list_cons, lazy2list_nil; auto.
      * refine (let (m,Hm) := loop l' r' _ (lazy_cons y a) _ in exist _ (lazy_cons x m) _).
        - rewrite lazy_length_cons; omega.
        - red in H |- *; do 2 rewrite lazy_length_cons in H; omega.
        - red in H, Hm |- *.
          repeat rewrite lazy2list_cons.
          rewrite Hm, lazy2list_cons; simpl.
          rewrite app_ass; auto.
  Defined.

End Rotate.

Arguments lazy_rotate {X}.

Extraction Inline lfin_rect lazy_nil lazy_cons lazy_list_rect.

 
