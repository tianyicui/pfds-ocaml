exception Empty
exception Subscript

module type RANDOM_ACCESS_LIST =
sig
  type 'a ra_list

  val empty : 'a ra_list
  val is_empty : 'a ra_list -> bool

  val cons : 'a -> 'a ra_list -> 'a ra_list
  val head : 'a ra_list -> 'a
  val tail : 'a ra_list -> 'a ra_list
    (* head and tail raise Empty if list is empty *)

  val lookup : int -> 'a ra_list -> 'a
  val update : int -> 'a -> 'a ra_list -> 'a ra_list
    (* lookup and update raise Subscript if index is out of bounds *)
end

module BinaryRandomAccessList : RANDOM_ACCESS_LIST =
struct
  type 'a tree =
    | Leaf of 'a
    | Node of int * 'a tree * 'a tree
  type 'a digit =
    | Zero
    | One of 'a tree
  type 'a ra_list = 'a digit list

  let empty = []
  let is_empty ts = ts = []

  let size = function
    | Leaf _ -> 1
    | Node (w, _, _) -> w
  let link t1 t2 =
    Node (size t1 + size t2, t1, t2)
  let rec cons_tree t = function
    | [] -> [One t]
    | Zero :: ts -> One t :: ts
    | One t' :: ts -> Zero :: cons_tree (link t t') ts
  let rec uncons_tree = function
    | [] -> raise Empty
    | [One t] -> t, []
    | One t :: ts -> t, Zero :: ts
    | Zero :: ts ->
        match uncons_tree ts with
          | Node (_, t1, t2), ts' ->
              t1, One t2 :: ts'
          | Leaf _, _ -> failwith "unreachable"

  let cons x ts = cons_tree (Leaf x) ts
  let head ts = match uncons_tree ts with
    | Leaf x, _ -> x
    | Node (_, _, _), _ -> failwith "unreachable"
  let tail ts =
    let _, ts' = uncons_tree ts in ts'

  let rec lookup_tree i t =
    match i, t with
      | 0, Leaf x -> x
      | _, Leaf _ -> raise Subscript
      | i, Node (w, t1, t2) ->
          if i < w/2 then lookup_tree i t1
          else lookup_tree (i-w/2) t2
  let rec update_tree i y t =
    match i, t with
      | 0, Leaf _ -> Leaf y
      | _, Leaf _ -> raise Subscript
      | i, Node (w, t1, t2) ->
          if i < w/2 then Node (w, update_tree i y t1, t2)
          else Node (w, t1, update_tree (i-w/2) y t2)

  let rec lookup i = function
    | [] -> raise Subscript
    | Zero :: ts -> lookup i ts
    | One t :: ts ->
        if i < size t then lookup_tree i t
        else lookup (i - size t) ts
  let rec update i y = function
    | [] -> raise Subscript
    | Zero :: ts -> Zero :: update i y ts
    | One t :: ts ->
        if i < size t then One (update_tree i y t) :: ts
        else One t :: update (i - size t) y ts
end

module SkewBinaryRandomAccessList : RANDOM_ACCESS_LIST =
struct
  type 'a tree =
    | Leaf of 'a
    | Node of 'a * 'a tree * 'a tree
  type 'a ra_list = (int * 'a tree) list (* integer is the weight of the tree *)

  let empty = []
  let is_empty ts = ts = []

  let cons x ts =
    match ts with
      | (w1, t1) :: (w2, t2) :: ts' when w1 = w2 ->
          (1+w1+w2, Node (x, t1, t2)) :: ts'
      | _ -> (1, Leaf x) :: ts
  let head = function
    | [] -> raise Empty
    | (_, Leaf x) :: _ -> x
    | (_, Node (x, _, _)) :: _ -> x
  let tail = function
    | [] -> raise Empty
    | (_, Leaf _) :: ts -> ts
    | (w, Node (x, t1, t2)) :: ts ->
        (w/2, t1) :: (w/2, t2) :: ts

  let rec lookup_tree w i t =
    match i, t with
      | 0, Leaf x -> x
      | _, Leaf _ -> raise Subscript
      | 0, Node (x, _, _) -> x
      | _, Node (_, t1, t2) ->
          if i <= w/2 then lookup_tree (w/2) (i-1) t1
          else lookup_tree (w/2) (i-1-w/2) t2
  let rec update_tree w i y t =
    match i, t with
      | 0, Leaf _ -> Leaf y
      | _, Leaf _ -> raise Subscript
      | 0, Node (_, t1, t2) -> Node (y, t1, t2)
      | _, Node (x, t1, t2) ->
          if i <= w/2 then Node (x, update_tree (w/2) (i-1) y t1, t2)
          else Node (x, t1, update_tree (w/2) (i-1-w/2) y t2)

  let rec lookup i = function
    | [] -> raise Subscript
    | (w, t) :: ts ->
        if i < w then lookup_tree w i t
        else lookup (i-w) ts
  let rec update i y = function
    | [] -> raise Subscript
    | (w, t) :: ts ->
        if i < w then (w, update_tree w i y t) :: ts
        else (w, t) :: update (i-1) y ts
end

module type ORDERED = Ch7.ORDERED
module type HEAP = Ch7.HEAP

module SkewBinomialHeap (Element : ORDERED) : HEAP with module Elem = Element =
struct
  module Elem = Element

  type tree = Node of int * Elem.t * Elem.t list * tree list
  type heap = tree list

  let empty = []
  let is_empty ts = ts = []

  let rank (Node (r, _, _, _)) = r
  let root (Node (_, x, _, _)) = x
  let link (Node (r, x1, xs1, c1) as t1) (Node (_, x2, xs2, c2) as t2) =
    if Elem.compare x1 x2 <= 0 then Node (r+1, x1, xs1, t2 :: c1)
    else Node (r+1, x2, xs2, t1 :: c2)
  let skew_link x t1 t2 =
    let Node (r, y, ys, c) = link t1 t2 in
      if Elem.compare x y <=0 then Node (r, x, y :: ys, c)
      else Node (r, y, x :: ys, c)
  let rec ins_tree t1 = function
    | [] -> [t1]
    | t2 :: ts ->
        if rank t1 < rank t2 then t1 :: t2 :: ts
        else ins_tree (link t1 t2) ts
  let rec merge_trees ts1 ts2 =
    match ts1, ts2 with
      | _, [] -> ts2
      | [], _ -> ts1
      | t1 :: ts1', t2 :: ts2' ->
          if rank t1 < rank t2 then t1 :: merge_trees ts1' ts2
          else if rank t2 < rank t1 then t2 :: merge_trees ts1 ts2'
          else ins_tree (link t1 t2) (merge_trees ts1' ts2')
  let normalize = function
    | [] -> []
    | t :: ts -> ins_tree t ts

  let insert x = function
    | t1 :: t2 :: rest when rank t1 = rank t2 ->
        (skew_link x t1 t2) :: rest
    | ts ->
        Node (0, x, [], []) :: ts
  let merge ts1 ts2 =
    merge_trees (normalize ts1) (normalize ts2)

  let rec remove_min_tree = function
    | [] -> raise Empty
    | [t] -> t, []
    | t :: ts ->
        let t', ts' = remove_min_tree ts in
          if Elem.compare (root t) (root t') <= 0 then t, ts else t', t :: ts'

  let find_min ts =
    root (fst (remove_min_tree ts))
  let delete_min ts =
    let Node (_, x, xs, ts1), ts2 = remove_min_tree ts in
    let rec insert_all ts = function
      | [] -> ts
      | x :: xs -> insert_all (insert x ts) xs
    in
  insert_all (merge (List.rev ts1) ts2) xs
end
