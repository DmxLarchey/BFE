
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

(** val llist_list : 'a1 llist -> 'a1 list **)

let rec llist_list ll =
  match Lazy.force
  ll with
  | Lnil -> []
  | Lcons (x, ll0) -> x::(llist_list ll0)

(** val llist_rotate : 'a1 llist -> 'a1 llist -> 'a1 llist -> 'a1 llist **)

let rec llist_rotate l r a =
  match Lazy.force
  r with
  | Lnil -> assert false (* absurd case *)
  | Lcons (y, r') ->
    (match Lazy.force
     l with
     | Lnil -> lazy (Lcons (y, a))
     | Lcons (x, l') ->
       lazy (Lcons (x, (llist_rotate l' r' (lazy (Lcons (y, a)))))))

module FIFO_3llists =
 struct
  type 'x fifo = (('x llist*'x llist)*'x llist)

  (** val f2l : 'a1 fifo -> 'a1 list **)

  let f2l = function
  | p,_ -> let l,r = p in app (llist_list l) (rev (llist_list r))

  (** val empty : 'a1 fifo **)

  let empty =
    ((lazy Lnil),(lazy Lnil)),(lazy Lnil)

  (** val make : 'a1 llist -> 'a1 llist -> 'a1 llist -> 'a1 fifo **)

  let make l r l' =
    match Lazy.force
    l' with
    | Lnil -> let l'' = llist_rotate l r (lazy Lnil) in (l'',(lazy Lnil)),l''
    | Lcons (_, l'') -> (l,r),l''

  (** val enq : 'a1 fifo -> 'a1 -> 'a1 fifo **)

  let enq q =
    let fifo_enq_val = fun q0 x ->
      let p,x0 = q0 in let l,r = p in make l (lazy (Lcons (x, r))) x0
    in
    (fun x -> fifo_enq_val q x)

  (** val deq : 'a1 fifo -> ('a1*'a1 fifo) **)

  let deq = function
  | p,x ->
    let l,r = p in
    (match Lazy.force
     l with
     | Lnil -> assert false (* absurd case *)
     | Lcons (x0, l0) -> x0,(make l0 r x))

  (** val void : 'a1 fifo -> bool **)

  let void = function
  | p,_ ->
    let l0,_ = p in
    (match Lazy.force
     l0 with
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
