
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

module FIFO_triv =
 struct
  type 'x fifo = 'x list

  (** val f2l : 'a1 fifo -> 'a1 list **)

  let f2l x =
    x

  (** val empty : 'a1 fifo **)

  let empty =
    []

  (** val enq : 'a1 fifo -> 'a1 -> 'a1 fifo **)

  let enq q x =
    app q (x::[])

  (** val deq : 'a1 fifo -> ('a1*'a1 fifo) **)

  let deq = function
  | [] -> assert false (* absurd case *)
  | x::q0 -> x,q0

  (** val void : 'a1 fifo -> bool **)

  let void = function
  | [] -> true
  | _::_ -> false
 end

module FIFO_2lists =
 struct
  (** val rev_linear : 'a1 list -> 'a1 list **)

  let rev_linear l =
    let rec loop l0 = function
    | [] -> l0
    | x::m0 -> loop (x::l0) m0
    in loop [] l

  type 'x fifo = 'x list*'x list

  (** val f2l : 'a1 fifo -> 'a1 list **)

  let f2l = function
  | l,r -> app l (rev r)

  (** val empty : 'a1 fifo **)

  let empty =
    [],[]

  (** val enq : 'a1 fifo -> 'a1 -> 'a1 fifo **)

  let enq q x =
    let l,r = q in l,(x::r)

  (** val deq : 'a1 fifo -> ('a1*'a1 fifo) **)

  let rec deq = function
  | l0,r -> (match l0 with
             | [] -> deq ((rev_linear r),[])
             | x::l -> x,(l,r))

  (** val void : 'a1 fifo -> bool **)

  let void = function
  | l,l0 ->
    (match l with
     | [] -> (match l0 with
              | [] -> true
              | _::_ -> false)
     | _::_ -> false)
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

