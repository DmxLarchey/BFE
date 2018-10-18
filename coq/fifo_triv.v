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

Require Import List Extraction.
Require Import fifo.

Set Implicit Arguments.

(* We provide a trivial implementation of FIFO as lists 
   satisfying the axioms in fifo_axm.v *)

Module FIFO_triv <: FIFO.

Section fifo_triv.

  Variable X : Type.

  Definition fifo := list X.

  Implicit Type q : fifo.

  Definition f2l : fifo -> list X := fun x => x.
  
  Definition empty : { q | f2l q = nil }.
  Proof. exists nil; trivial. Defined.

  Definition enq q x : { q' | f2l q' = f2l q ++ x :: nil }.
  Proof. exists (q++x::nil); trivial. Defined.
 
  Definition deq q : f2l q <> nil -> { c : X * fifo | let (x,q') := c in f2l q = x::f2l q' }.
  Proof.
    refine (match q with nil => _ | x::q => fun _ => exist _ (x,q) _ end); trivial.
    intros []; reflexivity.
  Defined.

  Definition void q : { b : bool | b = true <-> f2l q = nil }.
  Proof.
    exists (match q with nil => true | _ => false end).
    destruct q; split; try tauto; discriminate.
  Defined.
  
End fifo_triv.

End FIFO_triv.


