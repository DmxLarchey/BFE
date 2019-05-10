
val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val add : int -> int -> int

val rev : 'a1 list -> 'a1 list

type 'x bt =
| Leaf of 'x
| Node of 'x bt * 'x * 'x bt

module type FIFO =
 sig
  type 'x fifo

  val f2l : 'a1 fifo -> 'a1 list

  val empty : 'a1 fifo

  val enq : 'a1 fifo -> 'a1 -> 'a1 fifo

  val deq : 'a1 fifo -> ('a1*'a1 fifo)

  val void : 'a1 fifo -> bool
 end

module FIFO_2lists :
 sig
  val rev_linear : 'a1 list -> 'a1 list

  type 'x fifo = 'x list*'x list

  val f2l : 'a1 fifo -> 'a1 list

  val empty : 'a1 fifo

  val enq : 'a1 fifo -> 'a1 -> 'a1 fifo

  val deq : 'a1 fifo -> ('a1*'a1 fifo)

  val void : 'a1 fifo -> bool
 end

module BFN_FIFO :
 functor (Q:FIFO) ->
 sig
  val bfn_fifo_f : int -> 'a1 bt Q.fifo -> int bt Q.fifo

  val list2fifo : 'a1 bt list -> 'a1 bt Q.fifo

  val bfn_f_fifo : int -> 'a1 bt list -> int bt list

  val bfn_fifo : 'a1 bt -> int bt
 end

val forest_children : 'a1 bt list -> int*'a1 bt list

val forest_rebuild : int -> 'a1 bt list -> int bt list -> int bt list

val bfn_level_f : int -> 'a1 bt list -> int bt list

val bfn_level : 'a1 bt -> int bt

module BFN_2lists :
 sig
  val bfn_fifo_f : int -> 'a1 bt FIFO_2lists.fifo -> int bt FIFO_2lists.fifo

  val list2fifo : 'a1 bt list -> 'a1 bt FIFO_2lists.fifo

  val bfn_f_fifo : int -> 'a1 bt list -> int bt list

  val bfn_fifo : 'a1 bt -> int bt
 end

