
(** val itl1 : 'a1 list -> 'a1 list -> 'a1 list **)

let rec itl1 l m =
  match l with
  | [] -> m
  | x::l' -> (match m with
              | [] -> l
              | y::m' -> x::(y::(itl1 l' m')))

(** val itl2 : 'a1 list -> 'a1 list -> 'a1 list **)

let rec itl2 u v =
  match u with
  | [] -> v
  | x::l' -> x::(itl2 v l')
