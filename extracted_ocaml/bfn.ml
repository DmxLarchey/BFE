
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val add : int -> int -> int **)

let rec add n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun p -> succ (add p m))
    n

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

module BFN_FIFO =
 functor (Q:FIFO) ->
 struct
  (** val bfn_fifo_f : int -> 'a1 bt Q.fifo -> int bt Q.fifo **)

  let rec bfn_fifo_f u v =
    if Q.void v
    then Q.empty
    else let t,p1 = Q.deq v in
         (match t with
          | Leaf _ -> Q.enq (bfn_fifo_f (succ u) p1) (Leaf u)
          | Node (a, _, b) ->
            let u0,q1 = Q.deq (bfn_fifo_f (succ u) (Q.enq (Q.enq p1 a) b)) in
            let v0,q2 = Q.deq q1 in Q.enq q2 (Node (v0, u, u0)))

  (** val list2fifo : 'a1 bt list -> 'a1 bt Q.fifo **)

  let rec list2fifo = function
  | [] -> Q.empty
  | y::l0 -> Q.enq (list2fifo l0) y

  (** val bfn_f_fifo : int -> 'a1 bt list -> int bt list **)

  let bfn_f_fifo n l =
    let s = list2fifo (rev l) in let s0 = bfn_fifo_f n s in rev (Q.f2l s0)

  (** val bfn_fifo : 'a1 bt -> int bt **)

  let bfn_fifo t =
    let x,_ = Q.deq (bfn_fifo_f (succ 0) (Q.enq Q.empty t)) in x
 end

(** val forest_children : 'a1 bt list -> int*'a1 bt list **)

let rec forest_children = function
| [] -> 0,[]
| t::l ->
  let n,ch = forest_children l in
  (match t with
   | Leaf _ -> (succ n),ch
   | Node (a, _, b) -> (succ n),(a::(b::ch)))

(** val forest_rebuild : int -> 'a1 bt list -> int bt list -> int bt list **)

let rec forest_rebuild i ts cs =
  match ts with
  | [] -> []
  | b::ts0 ->
    (match b with
     | Leaf _ -> (Leaf i)::(forest_rebuild (succ i) ts0 cs)
     | Node (_, _, _) ->
       (match cs with
        | [] -> []
        | a::l ->
          (match l with
           | [] -> []
           | b0::cs0 -> (Node (a, i, b0))::(forest_rebuild (succ i) ts0 cs0))))

(** val bfn_level_f : int -> 'a1 bt list -> int bt list **)

let rec bfn_level_f u v = match v with
| [] -> []
| _::_ ->
  let n,cs = forest_children v in
  forest_rebuild u v (bfn_level_f (add n u) cs)

(** val bfn_level : 'a1 bt -> int bt **)

let bfn_level t =
  match bfn_level_f (succ 0) (t::[]) with
  | [] -> assert false (* absurd case *)
  | t'::_ -> t'

module BFN_2lists = BFN_FIFO(FIFO_2lists)
