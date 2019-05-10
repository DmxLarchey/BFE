
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x::l0 -> app x (concat l0)

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

(** val zip : ('a1 -> 'a1 -> 'a1) -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec zip f l m =
  match l with
  | [] -> m
  | x::l0 -> (match m with
              | [] -> l
              | y::m0 -> (f x y)::(zip f l0 m0))

(** val niveaux : 'a1 bt -> 'a1 list list **)

let rec niveaux = function
| Leaf x -> (x::[])::[]
| Node (a, x, b) -> (x::[])::(zip app (niveaux a) (niveaux b))

(** val bft_std : 'a1 bt -> 'a1 list **)

let bft_std t =
  concat (niveaux t)

(** val forest_decomp : 'a1 bt list -> 'a1 list*'a1 bt list **)

let rec forest_decomp = function
| [] -> [],[]
| t::l ->
  let ro,sf = forest_decomp l in
  (match t with
   | Leaf x -> (x::ro),sf
   | Node (a, x, b) -> (x::ro),(a::(b::sf)))

(** val bft_f : 'a1 bt list -> 'a1 list **)

let rec bft_f u = match u with
| [] -> []
| _::_ -> let ro,st = forest_decomp u in app ro (bft_f st)

(** val bft_forest : 'a1 bt -> 'a1 list **)

let bft_forest t =
  bft_f (t::[])

module BFT_FIFO =
 functor (Q:FIFO) ->
 struct
  (** val bft_fifo_f : 'a1 bt Q.fifo -> 'a1 list **)

  let rec bft_fifo_f u =
    if Q.void u
    then []
    else let t,q' = Q.deq u in
         (match t with
          | Leaf x -> x::(bft_fifo_f q')
          | Node (a, x, b) -> x::(bft_fifo_f (Q.enq (Q.enq q' a) b)))

  (** val bft_fifo : 'a1 bt -> 'a1 list **)

  let bft_fifo t =
    bft_fifo_f (Q.enq Q.empty t)
 end

module BFT_triv = BFT_FIFO(FIFO_triv)

