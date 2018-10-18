
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
