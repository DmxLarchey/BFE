
val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

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

type 'x llist = 'x __llist Lazy.t
and 'x __llist =
| Lnil
| Lcons of 'x * 'x llist

val llist_list : 'a1 llist -> 'a1 list

val llist_rotate : 'a1 llist -> 'a1 llist -> 'a1 llist -> 'a1 llist

module FIFO_3llists :
 sig
  type 'x fifo = (('x llist*'x llist)*'x llist)

  val f2l : 'a1 fifo -> 'a1 list

  val empty : 'a1 fifo

  val make : 'a1 llist -> 'a1 llist -> 'a1 llist -> 'a1 fifo

  val enq : 'a1 fifo -> 'a1 -> 'a1 fifo

  val deq : 'a1 fifo -> ('a1*'a1 fifo)

  val void : 'a1 fifo -> bool
 end

module BFR_FIFO :
 functor (Q:FIFO) ->
 sig
  val bfr_fifo_f : 'a1 bt Q.fifo -> 'a2 list -> 'a2 bt Q.fifo

  val bfr_fifo : 'a1 bt -> 'a2 list -> 'a2 bt
 end

module BFR_3llists :
 sig
  val bfr_fifo_f :
    'a1 bt FIFO_3llists.fifo -> 'a2 list -> 'a2 bt FIFO_3llists.fifo

  val bfr_fifo : 'a1 bt -> 'a2 list -> 'a2 bt
 end
