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

Require Import wf_utils fifo.

Set Implicit Arguments.

(* We provide an implementation of FIFO as a pair of lists 
   satisfying the axioms in fifo_axm.v *)

Module FIFO_2lists <: FIFO.

Section fifo_two_lists.

  Variable X : Type.

  Let rev' := fix loop (l m : list X) :=
    match m with
      | nil  => l
      | x::m => loop (x::l) m
    end.

  Let rev'_spec l m : rev' l m = rev m ++ l.
  Proof.
    revert l; induction m as [ | x m IHm ]; simpl; intros l; auto.
    rewrite IHm, app_ass; auto.
  Qed.

  Definition rev_linear l: list X := rev' nil l.

  Fact rev_linear_spec l : rev_linear l = rev l.
  Proof.
    unfold rev_linear; rewrite rev'_spec, <- app_nil_end; auto.
  Qed.

  Definition fifo := (list X * list X)%type.

  Implicit Type q : fifo.

  Definition f2l q := let (l,r) := q in l++rev r.

  Definition empty : { q | f2l q = nil }.
  Proof. exists (nil,nil); trivial. Defined.

  Definition enq q x : { q' | f2l q' = f2l q ++ x :: nil }.
  Proof. 
    exists (let (l,r) := q in (l,x::r)).
    destruct q; simpl; rewrite app_ass; auto.
  Defined.

  (**  Beware that the extracted code loops forever if q = (nil,nil) 
       which is not problematic with the guard fifo_list q <> nil
       but this is an interesting example of extraction of a partial
       function ... 

       let rec deq = function (l,r) -> 
         match l with 
           | nil  => deq (rev_linear r,nil)
           | x::l => (x,(l,r))
         end

       *)

  Definition deq q : f2l q <> nil -> { c : X * fifo | let (x,q') := c in f2l q = x::f2l q' }.
  Proof.
    induction on q as deq with measure (length (fst q)+2*length (snd q)); intros Hq.
    refine (match q as q' return q = q' -> _ with 
      | (nil,r)   => fun E  => let (res,Hres) := deq (rev_linear r,nil) _ _ in exist _ res _
      | (x::l,r)  => fun _  => exist _ (x,(l,r)) _
    end eq_refl); subst; simpl in * |- *; trivial.
    + rewrite rev_linear_spec, rev_length.
      destruct r; simpl; try omega; destruct Hq; reflexivity.
    + rewrite rev_linear_spec, <- app_nil_end; trivial.
    + destruct res; rewrite <- Hres, rev_linear_spec, <- app_nil_end; reflexivity.
  Defined.

  Definition void q : { b : bool | b = true <-> f2l q = nil }.
  Proof.
    exists (match q with (nil,nil) => true | _ => false end).
    revert q.
    intros ([ | x l],[ | y r]); simpl; split; auto; try discriminate.
    generalize (rev r); clear r; intros [ | ]; discriminate.
  Defined.

End fifo_two_lists.

End FIFO_2lists.

