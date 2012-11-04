exception Empty

module type ORDERED = Ch2.ORDERED

module type HEAP =
sig
  module Elem : ORDERED

  type heap

  val empty : heap
  val is_empty : heap -> bool

  val insert : Elem.t -> heap -> heap
  val merge : heap -> heap -> heap

  val find_min : heap -> Elem.t (* raises E if heap is empty *)
  val delete_min : heap -> heap (* raises E if heap if empty *)
end

module LeftistHeap (Element : ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  type heap =
    | E
    | T of int * Elem.t * heap * heap

  let rank = function
    | E -> 0
    | T (r, _, _, _) -> r
  let make_tree x a b =
    let ra = rank a in
    let rb = rank b in
      if ra >= rb then
        T (rb + 1, x, a, b)
      else
        T (ra + 1, x, b, a)

  let empty = E
  let is_empty = function
    | E -> true
    | _ -> false

  let rec merge h1 h2 =
    match (h1, h2) with
      | h, E -> h
      | E, h -> h
      | T (_, x, a1, b1), T (_, y, a2, b2) ->
          if Elem.compare x y <= 0 then
            make_tree x a1 (merge b1 h2)
          else
            make_tree y a2 (merge h1 b2)

  let insert x h =
    merge (T (1, x, E, E)) h

  let find_min = function
    | E -> raise Empty
    | T (_, x, _, _) -> x

  let delete_min = function
    | E -> raise Empty
    | T (_, _, a, b) -> merge a b
end

module BinomialHeap (Element: ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  type tree = Node of int * Elem.t * tree list
  type heap = tree list

  let empty = []
  let is_empty ts = ts = []

  let rank (Node (r, _, _)) = r
  let root (Node (_, x, _)) = x
  let link (Node (r, x1, c1) as t1) (Node (_, x2, c2) as t2) =
    if Elem.compare x1 x2 <= 0 then
      Node (r+1, x1, t2 :: c1)
    else
      Node (r+1, x2, t1 :: c2)
  let rec ins_tree t = function
    | [] -> [t]
    | t' :: ts' as ts ->
        if rank t < rank t' then t :: ts else ins_tree (link t t') ts'

  let insert x ts = ins_tree (Node (0, x, [])) ts
  let rec merge ts1 ts2 =
    match (ts1, ts2) with
      | _, [] -> ts1
      | [], _ -> ts2
      | (t1 :: ts1'), (t2 :: ts2') ->
          if rank t1 < rank t2 then t1 :: merge ts1' ts2
          else if rank t2 < rank t1 then t2 :: merge ts1 ts2'
          else ins_tree (link t1 t2) (merge ts1' ts2')

  let rec remove_min_tree = function
    | [] -> raise Empty
    | [t] -> (t, [])
    | t :: ts ->
        let t', ts' = remove_min_tree ts in
          if Elem.compare (root t) (root t') <= 0 then
            (t, ts)
          else
            (t', t :: ts')

  let find_min ts =
    root (fst (remove_min_tree ts))

  let delete_min ts =
    let (Node (_, x, ts1), ts2) = remove_min_tree ts in
      merge (List.rev ts1) ts2
end

module type SET = Ch2.SET

module RedBlackSet (Element : ORDERED) : (SET with type elem = Element.t) =
struct
  type elem = Element.t

  type color = R | B
  type tree =
    | E
    | T of color * tree * elem * tree
  type set = tree

  let empty = E

  let rec member x = function
    | E -> false
    | T (_, a, y, b) ->
        match Element.compare x y with
          | 0 -> true
          | n when n < 0 -> member x a
          | _ -> member x b

  let balance = function
    | (B, T (R, T (R, a, x, b), y, c), z, d)
    | (B, T (R, a, x, T (R, b, y, c)), z, d)
    | (B, a, x, T (R, T (R, b, y, c), z, d))
    | (B, a, x, T (R, b, y, T (R, c, z, d))) ->
        T (R, T (B, a, x, b), y, T (B, c, z, d))
    | (c, a, x, b) -> T (c, a, x, b)

  let insert x s =
    let rec ins = function
      | E -> T (R, E, x, E)
      | T (color, a, y, b) as s ->
          match Element.compare x y with
            | 0 -> s
            | n when n < 0 ->
                balance (color, ins a, y, b)
            | _ ->
                balance (color, a, y, ins b)
    in
      match ins s with
        | T (_, a, y, b) -> T (B, a, y, b)
        | _ -> failwith "unreachable"
end
