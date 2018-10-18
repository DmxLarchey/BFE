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

Require Import bt List Extraction.

Set Implicit Arguments.

Module Type FIFO.

  Parameters (fifo    : Type -> Type)
             (f2l  : forall X, fifo X -> list X)
             (empty   : forall X, { q : fifo X | f2l q = nil })
             (enq     : forall X q x, { q' : fifo X | f2l q' = f2l q ++ x :: nil })
             (deq     : forall X q, @f2l X q <> nil -> { c : X * fifo X | let (x,q') := c in f2l q = x::f2l q' })
             (void    : forall X q, { b : bool | b = true <-> @f2l X q = nil }).

  Notation fifo_lsum := ((fun X (q : fifo (bt X)) => lsum (f2l q)) _).

End FIFO.
