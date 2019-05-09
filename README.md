# Breadth-First Extraction: Lessons from a Small Exercice in Algorithmic Certification

## Copyright

```
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
```
## What is this repository for?

* Coq v8.8.1 or v8.8.2 implementation of breadth-first numbering à la Okasaki and variations thereof
* It is also possible to compile the project under Coq v8.7.* but the `Makefile` is not compatible
  and should be regenerated for v8.7.* with the command `coq_makefile -f _CoqProject -o Makefile`

## How do I use it?

* Inside the `coq` directory, just type `make all` or `make extraction.vo` or  `make wf_example.vo`.
* For convenience, all the OCaml generated files have been copied to the 
  directory [`extracted_ocaml`](extracted_ocaml). These are the very same files as those generated
  by the `make all` command above.
* You can consult the following [pre-print](https://members.loria.fr/DLarchey/files/papers/BFE_CPP19.pdf) submitted to CPP'19.

## Description of the Coq content

There are 26 Coq vernacular files, here presented in useful order (based on the [dependency graph](coq/dependency_graph.txt)). According to `coqwc` the whole code comprises a total of around 2500 lines of code: around 1130 loc for specifications, 1230 loc for proofs and 300 lines for comments.
  
* [`list_utils.v`](coq/list_utils.v) --- One of the biggest files, all concerning list operations, list permutations, the lifting of relations to lists and segments of the natural numbers -- auxiliary material with use at many places.
* [`wf_utils.v`](coq/wf_utils.v) --- The subtle tactics for measure recursion in one or two arguments with a nat-valued measure function -- this is crucial for smooth extraction throughout.
* [`llist.v`](coq/llist.v) --- Some general material on coinductive lists, in particular proven finite ones (including append for those), but also the rotate operation of Okasaki.
* [`interleave.v`](coq/interleave.v) --- The example of interleaving with three different methods.
* [`zip.v`](coq/zip.v) --- Zipping with a rich specification and relations with concatenation -- just auxiliary material.
* [`sorted.v`](coq/sorted.v) --- Consequences of a list being sorted, in particular absence of duplicates in case of strict orders -- auxiliary material.
* [`increase.v`](coq/increase.v) --- Small auxiliary file for full spec. of breadth-first traversal.
* [`bt.v`](coq/bt.v) --- The largest file in this library, describing binary trees, their branches and orders on those in relation with depth-first and breadth-first traversal and structural relations on trees and forests.
* [`fifo.v`](coq/fifo.v) --- Just the module type for abstract FIFOs.
* [`fifo_triv.v`](coq/fifo_triv.v) --- The trivial implementation of FIFO's through lists.
* [`fifo_2lists.v`](coq/fifo_2lists.v) --- An efficient implementation with amortized O(1) operations.
* [`fifo_3llists.v`](coq/fifo_3llists.v) --- The much more complicated FIFO implementation that is slower but has worst-case O(1) operations, invented by Okasaki.
* [`dft_std.v`](coq/dft_std.v) --- Depth-first traversal, not mentioned in the paper.
* [`bft_std.v`](coq/bft_std.v) --- Breadth-first traversal naively with levels (specified with the traversal of branches in suitable order).
* [`dft_bft_compare.v`](coq/dft_bft_compare.v) --- Only the result that the respective versions that compute branches compute the same branches, and their lists form a permutation, not mentioned in the paper.
* [`bft_forest.v`](coq/bft_forest.v) --- Breadth-first traversal for forests of trees, paying much attention to the recursive equations that can guide the definition and/or verification.
* [`bft_inj.v`](coq/bft_inj.v) --- Structurally equal forests with the same outcome of breadth-first traversal are equal.
* [`bft_fifo.v`](coq/bft_fifo.v) --- Breadth-first traversal given an abstract FIFO.
* [`bfn_spec_rev.v`](coq/bfn_spec_rev.v) --- A characterization of breadth-first numbering.
* [`bfn_fifo.v`](coq/bfn_fifo.v) --- The certified analogue of Okasaki's algorithm for breadth-first numbering.
* [`bfn_trivial.v`](coq/bfn_trivial.v) --- Just the instance of the previous with the trivial implementation of FIFOs.
* [`bfn_level.v`](coq/bfn_level.v) --- A certified reconstruction of `bfnum` on page 134 (section 4 and Figure 5) of Okasaki's article. For its full specification, we allow ourselves to use breadth-first numbering obtained in [`bfn_trivial.v`](coq/bfn_trivial.v).
* [`bfr_fifo.v`](coq/bfr_fifo.v) --- Breadth-first reconstruction, a slightly more general task (see next file) than breadth-first numbering.
* [`bfr_bfn_fifo.v`](coq/bfr_bfn_fifo.v) --- Shows the claim that breadth-first numbering is an instance of breadth-first reconstruction (although they have been obtained with different induction principles).
* [`extraction.v`](coq/extraction.v) --- This operates extraction on-the-fly.
* [`benchmarks.v`](coq/benchmarks.v) --- This operates the extraction towards `*.ml*` files.
