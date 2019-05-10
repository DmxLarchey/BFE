
val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val rev : 'a1 list -> 'a1 list

module FIFO_triv :
 sig
  type 'x fifo = 'x list

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

type 'x llist = 'x __llist Lazy.t
and 'x __llist =
| Lnil
| Lcons of 'x * 'x llist

type 'x lazy_list = 'x llist

val lazy2list : 'a1 lazy_list -> 'a1 list

val lazy_rotate :
  'a1 lazy_list -> 'a1 lazy_list -> 'a1 lazy_list -> 'a1 lazy_list

module FIFO_3llists :
 sig
  type 'x fifo = (('x lazy_list*'x lazy_list)*'x lazy_list)

  val f2l : 'a1 fifo -> 'a1 list

  val empty : 'a1 fifo

  val make : 'a1 lazy_list -> 'a1 lazy_list -> 'a1 lazy_list -> 'a1 fifo

  val enq : 'a1 fifo -> 'a1 -> 'a1 fifo

  val deq : 'a1 fifo -> ('a1*'a1 fifo)

  val void : 'a1 fifo -> bool
 end

