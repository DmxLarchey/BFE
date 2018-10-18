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

Require Import list_utils fifo fifo_triv bfn_fifo.

Module BFN_triv := BFN_FIFO FIFO_triv.

Definition bfn_f := BFN_triv.bfn_f_fifo.

Arguments bfn_f {X}.
