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

Require Import wf_utils llist fifo.

Set Implicit Arguments.

(* We provide an implementation of FIFO as a triple of lazy lists 
   satisfying the axioms in fifo_axm.v *)

Module FIFO_3llists <: FIFO.

Section fifo_three_lazy_lists.

  (** From "Simple and Efficient Purely Functional Queues and Deques" by Chris Okasaki 
          Journal of Functional Programming 5(4):583-592

      this implements and prove the spec from page 587 with lazy lists 
      with invariant (l,r,l') : lazy_length l' + lazy_length r = lazy_length l

      let rec lazy_rotate l r a := match r with
        | lcons y r -> match l with
          | lnil      -> lcons y a
          | lcons x l -> lcons x (lazy_rotate l' r' (lcons y a))

      let empty = (lnil,lnil,lnil)

      let make l r l' = match l' with
        | lnil       -> let l' = lazy_rotate l r lnil in (l',lnil,l')
        | lcons _ l' -> (l, r, l')

      let enq (l,r,l') x = make l (lcons x r) l'

      let deq (lcons x l,r,l') = (x,make l r l')

      let void (l,r,n) = l = lnil

    *)

  Variable X : Type.

  Implicit Types (l r : lazy_list X).

  Let Q_spec (c : lazy_list X * lazy_list X * lazy_list X) :=
    match c with (l,r,l') => lazy_length l' + lazy_length r = lazy_length l end.

  Definition fifo := sig Q_spec.

  Implicit Types (q : fifo) (x : X).

  Definition f2l : fifo -> list X.
  Proof.
    intros (((l,r),l') & H).
    exact (lazy2list l ++ rev (lazy2list r)).
  Defined.

  Definition empty : { q | f2l q = nil }.
  Proof.
    assert (H : Q_spec (lazy_nil,lazy_nil,lazy_nil)).
    { red; rewrite lazy_length_nil; auto. }
    exists (exist _ _ H).
    unfold f2l; simpl; auto.
  Defined.

  Definition make l r l' : lazy_length l' + lazy_length r = 1 + lazy_length l -> { m | lazy2list l ++ rev (lazy2list r) = f2l m }.
  Proof.
    induction l' as [ | x l'' _ ] using lazy_list_rect; intros E.
    + rewrite lazy_length_nil in E; simpl in E.
      destruct (lazy_rotate l r lazy_nil E) as (l'' & H'').
      assert (H : Q_spec (l'',lazy_nil,l'')).
      { red; rewrite lazy_length_nil; omega. }
      exists (exist _ _ H).
      unfold Q_spec; simpl.
      rewrite H''; simpl.
      rewrite lazy2list_nil.
      repeat rewrite <- app_nil_end; trivial.
    + assert (H : Q_spec (l,r,l'')).
      { red; rewrite lazy_length_cons in E; omega. }
      exists (exist _ _ H).
      unfold Q_spec; simpl; auto.
  Defined.

  Definition enq : forall q x, { q' | f2l q' = f2l q ++ x :: nil }.
  Proof.
    intros (((l,r),l') & H) x.
    refine (let (m,Hm) := make l (lazy_cons x r) l' _ in _).
    + red in H; rewrite lazy_length_cons; omega.
    + exists m.
      simpl; rewrite <- Hm.
      rewrite lazy2list_cons, app_ass; simpl; auto.
  Defined.

  Definition deq : forall q, f2l q <> nil -> { c : X * fifo | let (x,q') := c in f2l q = x::f2l q' }.
  Proof.
    intros (((l,r),l') & H); revert H; simpl.
    induction l as [ | x l _ ] using lazy_list_rect.
    + induction r as [ | y r _ ] using lazy_list_rect; intros H1 H2; exfalso.
      * destruct H2; rewrite lazy2list_nil; auto.
      * rewrite lazy_length_cons, lazy_length_nil in H1; omega.
    + intros H1 H2.
      refine (let (m,Hm) := @make l r l' _ in _).
      * rewrite lazy_length_cons in H1; omega.
      * exists (x,m).
        rewrite lazy2list_cons; simpl; f_equal; auto.
  Defined.

  Definition void : forall q, { b : bool | b = true <-> f2l q = nil }.
  Proof.
    intros (((l,r),l') & H).
    induction l as [ | x l _ ] using lazy_list_rect; red in H.
    + exists true; simpl.
      split; auto; intros _.
      induction r as [ | y r _ ] using lazy_list_rect.
      * rewrite lazy2list_nil; auto.
      * rewrite lazy_length_cons, lazy_length_nil in H; simpl in H; omega.
    + exists false; simpl.
      split; try discriminate.
      rewrite lazy2list_cons; discriminate.
  Defined.

End fifo_three_lazy_lists.

End FIFO_3llists.



