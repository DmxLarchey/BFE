
val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val concat : 'a1 list list -> 'a1 list

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

module FIFO_triv :
 sig
  type 'x fifo = 'x list

  val f2l : 'a1 fifo -> 'a1 list

  val empty : 'a1 fifo

  val enq : 'a1 fifo -> 'a1 -> 'a1 fifo

  val deq : 'a1 fifo -> ('a1*'a1 fifo)

  val void : 'a1 fifo -> bool
 end

val zip : ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list -> 'a1 list

val niveaux : 'a1 bt -> 'a1 list list

val bft_std : 'a1 bt -> 'a1 list

val forest_decomp : 'a1 bt list -> 'a1 list*'a1 bt list

val bft_f : 'a1 bt list -> 'a1 list

val bft_forest : 'a1 bt -> 'a1 list

module BFT_FIFO :
 functor (Q:FIFO) ->
 sig
  val bft_fifo_f : 'a1 bt Q.fifo -> 'a1 list

  val bft_fifo : 'a1 bt -> 'a1 list
 end

module BFT_triv :
 sig
  val bft_fifo_f : 'a1 bt FIFO_triv.fifo -> 'a1 list

  val bft_fifo : 'a1 bt -> 'a1 list
 end

