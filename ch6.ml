exception Empty

module type QUEUE = Ch5.QUEUE
module Stream = Ch4.Stream

module BankersQueue : QUEUE =
struct
  open Stream

  type 'a queue = int * 'a stream * int * 'a stream

  let empty = (0, lazy Nil, 0, lazy Nil)
  let is_empty (lenf, _, _, _) = (lenf = 0)

  let check ((lenf, f, lenr, r) as q) =
    if lenr <= lenf then q
    else (lenf + lenr, f ++ reverse r, 0, lazy Nil)

  let snoc (lenf, f, lenr, r) x =
    check (lenf, f, lenr+1, lazy (Cons (x, r)))

  let head = function
    | _, lazy Nil, _, _ -> raise Empty
    | _, lazy (Cons (x, _)), _, _ -> x

  let tail = function
    | _, lazy Nil, _, _ -> raise Empty
    | lenf, lazy (Cons (_, f')), lenr, r ->
        check (lenf-1, f', lenr, r)
end

module type ORDERED = Ch3.ORDERED
module type HEAP = Ch3.HEAP

module LazyBinomialHeap (Element: ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  type tree = Node of int * Elem.t * tree list
  type heap = tree list Lazy.t

  let empty = lazy []
  let is_empty (lazy ts) = ts = []

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

  let rec mrg ts1 ts2 =
    match (ts1, ts2) with
      | _, [] -> ts1
      | [], _ -> ts2
      | (t1 :: ts1'), (t2 :: ts2') ->
          if rank t1 < rank t2 then t1 :: mrg ts1' ts2
          else if rank t2 < rank t1 then t2 :: mrg ts1 ts2'
          else ins_tree (link t1 t2) (mrg ts1' ts2')

  let insert x ts = lazy (
    ins_tree (Node (0, x, [])) (Lazy.force ts)
  )
  let merge ts1 ts2 = lazy (
    mrg (Lazy.force ts1) (Lazy.force ts2)
  )

  let rec remove_min_tree = function
    | [] -> raise Empty
    | [t] -> (t, [])
    | t :: ts ->
        let t', ts' = remove_min_tree ts in
          if Elem.compare (root t) (root t') <= 0 then
            (t, ts)
          else
            (t', t :: ts')

  let find_min (lazy ts) =
    root (fst (remove_min_tree ts))
  let delete_min ts = lazy (
    let (Node (_, x, ts1), ts2) = remove_min_tree (Lazy.force ts) in
      mrg (List.rev ts1) ts2
  )
end

module PhysicistsQueue : QUEUE =
struct
  type 'a queue =
      'a list * int * 'a list Lazy.t * int * 'a list

  let empty = ([], 0, lazy [], 0, [])
  let is_empty (_, lenf, _, _, _) = (lenf = 0)

  let checkw = function
    | ([], lenf, f, lenr, r) ->
        (Lazy.force f, lenf, f, lenr, r)
    | q -> q
  let check ((w, lenf, f, lenr, r) as q) =
    if lenr <= lenf then checkw q
    else let f' = Lazy.force f in
      checkw (f', lenf+lenr, lazy (f' @ (List.rev r)), 0, [])

  let snoc (w, lenf, f, lenr, r) x =
    check (w, lenf, f, lenr+1, x :: r)

  let head = function
    | ([], _, _, _, _) -> raise Empty
    | (x :: _, _, _, _, _) -> x
  let tail = function
    | ([], _, _, _, _) -> raise Empty
    | (_ :: w, lenf, f, lenr, r) ->
        check (w, lenf-1, lazy (List.tl (Lazy.force f)), lenr, r)
end

module type SORTABLE =
sig
  module Elem : ORDERED

  type sortable

  val empty : sortable
  val add : Elem.t -> sortable -> sortable
  val sort : sortable -> Elem.t list
end

module BottomUpMergeSort (Element : ORDERED) : (SORTABLE with module Elem = Element) =
struct
  module Elem = Element

  type sortable = int * Elem.t list list Lazy.t

  let rec mrg xs ys =
    match xs, ys with
      | [], _ -> ys
      | _, [] -> xs
      | (x :: xs'), (y :: ys') ->
          if Elem.compare x y <= 0 then
            x :: (mrg xs' ys)
          else
            y :: (mrg xs ys')

  let empty = 0, lazy []
  let add x (size, segs) =
    let rec add_seg seg segs size =
      if size mod 2 = 0 then seg :: segs
      else add_seg (mrg seg (List.hd segs)) (List.tl segs) (size/2)
    in (size+1, lazy (add_seg [x] (Lazy.force segs) size))
  let sort (size, segs) =
    List.fold_left mrg [] (Lazy.force segs)
end

module LazyParingHeap (Element : ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  type heap =
    | E
    | T of Elem.t * heap * heap Lazy.t

  let empty = E
  let is_empty = function 
    | E -> true
    | _ -> false

  let rec merge a b =
    match a, b with
      | _, E -> a
      | E, _ -> b
      | T (x, _, _), T (y, _, _) ->
          if Elem.compare x y <= 0 then
            link a b
          else
            link b a
  and link t a =
    match t with
      | T (x, E, m) -> T (x, a, m)
      | T (x, b, m) -> T (x, E, lazy (merge (merge a b) (Lazy.force m)))
      | E -> failwith "unreachable"

  let insert x a =
    merge (T (x, E, lazy E)) a

  let find_min = function
    | E -> raise Empty
    | T (x, _, _) -> x

  let delete_min = function
    | E -> raise Empty
    | T (_, a, lazy b) -> merge a b
end
