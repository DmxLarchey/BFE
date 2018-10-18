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

Require Import List Arith Omega Permutation.
Require Import list_utils bt sorted dft_std bft_std.

Set Implicit Arguments.

Section bt_branches.

  Variable X : Type.

  Implicit Type t : bt X.

  Hint Resolve dft_br_sorted bft_br_sorted lb_lex_irrefl bft_order_irrefl.

  (* dft_br and bft_br compute the same list of branches ... up to permutation *)

  Theorem bft_br_dft_br t : dft_br t ~p bft_br t.
  Proof.
    apply sorted_perm with (R := lb_lex) (S := bft_order); auto.
    intro; rewrite dft_br_spec, bft_br_spec; tauto.
  Qed.

End bt_branches.

(*
Check dft_br_spec.
Check dft_br_length.
Check dft_br_sorted.
Check dft_br_std.

Check bft_br_spec.
Check bft_br_length.
Check bft_br_sorted.
Check bft_br_std.

Check bft_br_dft_br.
*)