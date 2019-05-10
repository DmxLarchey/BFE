
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

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

type 'x lazy_list = 'x llist

(** val lazy2list : 'a1 lazy_list -> 'a1 list **)

let rec lazy2list s =
  match Lazy.force
  s with
  | Lnil -> []
  | Lcons (x, s0) -> x::(lazy2list s0)

(** val lazy_rotate :
    'a1 lazy_list -> 'a1 lazy_list -> 'a1 lazy_list -> 'a1 lazy_list **)

let rec lazy_rotate u v a =
  match Lazy.force
  v with
  | Lnil -> assert false (* absurd case *)
  | Lcons (x, s) ->
    (match Lazy.force
     u with
     | Lnil -> lazy (Lcons (x, a))
     | Lcons (x0, s0) ->
       lazy (Lcons (x0, (lazy_rotate s0 s (lazy (Lcons (x, a)))))))

module FIFO_3llists =
 struct
  type 'x fifo = (('x lazy_list*'x lazy_list)*'x lazy_list)

  (** val f2l : 'a1 fifo -> 'a1 list **)

  let f2l = function
  | p,_ -> let l,r = p in app (lazy2list l) (rev (lazy2list r))

  (** val empty : 'a1 fifo **)

  let empty =
    ((lazy Lnil),(lazy Lnil)),(lazy Lnil)

  (** val make :
      'a1 lazy_list -> 'a1 lazy_list -> 'a1 lazy_list -> 'a1 fifo **)

  let make l r l' =
    match Lazy.force
    l' with
    | Lnil -> let s = lazy_rotate l r (lazy Lnil) in (s,(lazy Lnil)),s
    | Lcons (_, s) -> (l,r),s

  (** val enq : 'a1 fifo -> 'a1 -> 'a1 fifo **)

  let enq q x =
    let p,x0 = q in let l,r = p in make l (lazy (Lcons (x, r))) x0

  (** val deq : 'a1 fifo -> ('a1*'a1 fifo) **)

  let deq = function
  | p,x ->
    let l,r = p in
    (match Lazy.force
     l with
     | Lnil -> assert false (* absurd case *)
     | Lcons (x0, s) -> x0,(make s r x))

  (** val void : 'a1 fifo -> bool **)

  let void = function
  | p,_ ->
    let l,_ = p in
    (match Lazy.force
     l with
     | Lnil -> true
     | Lcons (_, _) -> false)
 end

module BFR_FIFO =
 functor (Q:FIFO) ->
 struct
  (** val bfr_fifo_f : 'a1 bt Q.fifo -> 'a2 list -> 'a2 bt Q.fifo **)

  let rec bfr_fifo_f q = function
  | [] -> Q.empty
  | y::mm ->
    let t,p1 = Q.deq q in
    (match t with
     | Leaf _ -> Q.enq (bfr_fifo_f p1 mm) (Leaf y)
     | Node (a, _, b) ->
       let u,q1 = Q.deq (bfr_fifo_f (Q.enq (Q.enq p1 a) b) mm) in
       let v,q2 = Q.deq q1 in Q.enq q2 (Node (v, y, u)))

  (** val bfr_fifo : 'a1 bt -> 'a2 list -> 'a2 bt **)

  let bfr_fifo t l =
    let t',_ = Q.deq (bfr_fifo_f (Q.enq Q.empty t) l) in t'
 end

module BFR_3llists = BFR_FIFO(FIFO_3llists)
