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

      this implements and prove the spec from page 587 with lazy lists (llist)
      with invariant (l,r,l') : llength l' + llength r = llength l


      let rec llist_rotate l r a := match r with
        | lcons y r -> match l with
          | lnil      -> lcons y a
          | lcons x l -> lcons x (llist_rotate l' r' (lcons y a))

      let fifo_3q_nil = (lnil,lnil,lnil)

      let fifo_3q_make l r l' = match l' with
        | lnil       -> let l' = llist_rotate l r lnil in (l',lnil,l')
        | lcons _ l' -> (l, r, l')

      let fifo_3q_enq (l,r,l') x = fifo_3q_make l (lcons x r) l'

      let fifo_3q_deq (lcons x l,r,l') = (x,fifo_3q_make l r l')

      let fifo_3q_void (l,r,n) = l = lnil

    *)

  Variable X : Type.

  Implicit Types (l r : llist X).

  Let Q_spec (c : llist X * llist X * llist X) :=
    match c with (l,r,l') => exists Hl Hr Hl', lfin_length l' Hl' + lfin_length r Hr = lfin_length l Hl end.

  Definition fifo := sig Q_spec.

  Implicit Types (q : fifo) (x : X).

  Definition f2l : fifo -> list X.
  Proof.
    intros (((l,r),l') & H).
    refine (llist_list l _ ++ rev (llist_list r _));
    destruct H as (? & ? & _); assumption.
  Defined.

  Let fifo_nil_val : fifo.
  Proof.
    refine (exist _ (lnil,lnil,lnil) _).
    exists (lfin_lnil _), (lfin_lnil _), (lfin_lnil _); simpl.
    rewrite lfin_length_fix_0; auto.
  Defined.

  Definition empty : { q | f2l q = nil }.
  Proof. exists fifo_nil_val; trivial. Defined.

  Definition make l r l' : (exists Hl Hr Hl', lfin_length l' Hl' + lfin_length r Hr = 1 + lfin_length l Hl) -> fifo.
  Proof.
    destruct l' as [ | x l'' ]; intros E.
    + cut (lfin l); [ intros Hl1 | ].
      cut (lfin r); [ intros Hr1 | ].
      2-3 : cycle 1.
      cut (lfin_length r Hr1 = 1 + lfin_length l Hl1); [ intros E1 | ].
      2-4 : cycle 1.
      refine (let l'' := @llist_rotate _ l r lnil Hl1 Hr1 (@lfin_lnil _) E1 
              in exist _ (l'',lnil,l'') _).
      all: cycle 1.
      * destruct E as (? & ? & _); assumption.
      * destruct E as (? & ? & _); assumption.
      * destruct E as (Hl & Hr & Hl' & E).
        rewrite lfin_length_fix_0 in E.
        rewrite (lfin_length_eq _ Hr), (lfin_length_eq _ Hl); auto.
      * exists (lfin_rotate _ _ (@lfin_lnil _) E1), 
             (@lfin_lnil _),
             (lfin_rotate _ _ (@lfin_lnil _) E1).
        unfold l''; rewrite llist_rotate_length; auto.
    + refine (exist _ (l,r,l'') _).
      destruct E as (Hl & Hr & Hl'' & E).
      exists Hl, Hr, (lfin_inv Hl'').
      rewrite lfin_length_fix_1 in E; omega.
  Defined.

  Hint Resolve llist_list_eq.

  Fact make_spec l r l' Hl Hr H : llist_list l Hl ++ rev (llist_list r Hr) = f2l (@make l r l' H).
  Proof.
    destruct H as (Hl1 & Hr1 & Hl' & E).
    unfold f2l, make; destruct l' as [ | x l' ].
    + rewrite (llist_rotate_eq _ _ (@lfin_lnil _) _).
      repeat rewrite llist_list_fix_0; simpl.
      repeat rewrite <- app_nil_end; repeat (f_equal; auto).
    + repeat (f_equal; auto).
  Qed.

  Let fifo_enq_val q x : fifo.
  Proof.
    destruct q as (((l,r),l') & H).
    refine (@make l (lcons x r) l' _).
    destruct H as (Hl & Hr & Hl' & E).
    exists Hl, (lfin_lcons _ Hr), Hl'.
    rewrite lfin_length_fix_1, (lfin_length_eq _ Hr); omega.
  Defined.

  Definition enq q x : { q' | f2l q' = f2l q ++ x :: nil }.
  Proof.  
    exists (fifo_enq_val q x).
    revert q x.
    unfold fifo_enq_val.
    intros  (((l,r),l') & Hl & Hr & Hl' & E) x.
    rewrite <- (@make_spec _ _ _ Hl (lfin_lcons _ Hr)).
    unfold f2l.
    rewrite llist_list_fix_1, app_ass; trivial.
  Defined.

  Let fifo_deq_val q : f2l q <> nil -> X * fifo.
  Proof.
    destruct q as (((l,r),l') & H); revert H.
    refine (match l with 
      | lnil      => fun H1 H2 => _
      | lcons x l => fun H1 H2 => (x,@make l r l' _)
    end); [ exfalso | ]; destruct H1 as (Hl & Hr & Hl' & E).
    + unfold f2l in H2.
      destruct r.
      * do 2 rewrite llist_list_fix_0 in H2; destruct H2; trivial.
      * rewrite lfin_length_fix_1, lfin_length_fix_0 in E; omega.
    + exists (lfin_inv Hl), Hr, Hl'.
      rewrite E, lfin_length_fix_1; auto.
  Defined.

  Definition deq q : f2l q <> nil -> { c : X * fifo | let (x,q') := c in f2l q = x::f2l q' }.
  Proof.
    intros Hq.
    exists (fifo_deq_val q Hq).
    revert q Hq.  
    unfold fifo_deq_val.
    intros ((([ | x l],r),n) & Hl & Hr & Hl' & E) Hq.
    + exfalso.
      unfold f2l in Hq.
      destruct r.
      * do 2 rewrite llist_list_fix_0 in Hq; destruct Hq; trivial.
      * rewrite lfin_length_fix_1, lfin_length_fix_0 in E; omega.
    + rewrite <- (@make_spec _ _ _ (lfin_inv Hl) Hr).
      unfold f2l.
      rewrite llist_list_fix_1; auto.
  Defined.

  Let fifo_void_val : fifo -> bool.
  Proof.
    intros ((([ | x l],_),_) & _).
    + exact true.
    + exact false.
  Defined.

  Definition void q : { b : bool | b = true <-> f2l q = nil }.
  Proof.
    exists (fifo_void_val q).
    revert q.
    unfold f2l, fifo_void_val.
    intros ((([ | x l],r),n) & Hl & Hr & Hl' & E).
    + split; auto; intros _. 
      rewrite llist_list_fix_0.
      destruct r.
      * rewrite llist_list_fix_0; auto.
      * rewrite lfin_length_fix_0, lfin_length_fix_1 in E; omega.
    + split; try discriminate.
      rewrite llist_list_fix_1; discriminate.
  Defined.

End fifo_three_lazy_lists.

End FIFO_3llists.



