exception Empty

module type QUEUE =
sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool

  val snoc : 'a queue -> 'a -> 'a queue
  val head : 'a queue -> 'a (* raises Empty if queue is empty *)
  val tail : 'a queue -> 'a queue (* raises Empty if queue is empty *)
end

module BatchedQueue : QUEUE =
struct
  type 'a queue = 'a list * 'a list

  let empty = [], []
  let is_empty (f, _) = f = []

  let checkf = function
    | [], r -> List.rev r, []
    | q -> q

  let snoc (f, r) x = checkf (f, x :: r)

  let head = function
    | [], _ -> raise Empty
    | (x :: _), _ -> x

  let tail = function
    | [], _ -> raise Empty
    | (_ :: f, r) -> checkf (f, r)
end

module type ORDERED = Ch3.ORDERED
module type HEAP = Ch3.HEAP

module SplayHeap (Element : ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  type heap =
    | E
    | T of heap * Elem.t * heap

  let empty = E
  let is_empty = function
    | E -> true
    | _ -> false

  let rec partition pivot = function
    | E -> E, E
    | T (a, x, b) as t ->
        if Elem.compare x pivot <= 0 then
          (match b with
             | E -> t, E
             | T (b1, y, b2) ->
                 if Elem.compare y pivot <= 0 then
                   (let small, big = partition pivot b2 in
                      T (T (a, x, b1), y, small), big)
                 else
                   (let small, big = partition pivot b1 in
                      T (a, x, small), T (big, y, b2))
          )
        else
          (match a with
             | E -> E, t
             | T (a1, y, a2) ->
                 if Elem.compare y pivot <= 0 then
                   (let small, big = partition pivot a2 in
                      T (a1, y, small), T (big, x, b))
                 else
                   (let small, big = partition pivot a1 in
                      small, T (big, y, T (a2, x, b)))
          )

  let insert x t =
    let a, b = partition x t in
      T (a, x, b)

  let rec merge t = function
    | E -> t
    | T (a, x, b) ->
        let ta, tb = partition x t in
          T (merge ta a, x, merge tb b)

  let rec find_min = function
    | E -> raise Empty
    | T (E, x, _) -> x
    | T (a, x, _) -> find_min a

  let rec delete_min = function
    | E -> raise Empty
    | T (E, _, b) -> b
    | T (T (E, _, b), y, c) -> T (b, y, c)
    | T (T (a, x, b), y, c) -> T (delete_min a, x, T (b, y, c))
end

module ParingHeap (Element : ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  type heap =
    | E
    | T of Elem.t * heap list

  let empty = E
  let is_empty = function
    | E -> true
    | _ -> false

  let merge h1 h2 =
    match h1, h2 with
      | _, E -> h1
      | E, _ -> h2
      | T (x, hs1), T (y, hs2) ->
          if Elem.compare x y <= 0 then
            T (x, h2 :: hs1)
          else
            T (y, h1 :: hs2)
  let insert x h =
    merge (T (x, [])) h

  let rec merge_pairs = function
    | [] -> E
    | [h] -> h
    | h1 :: h2 :: hs ->
        merge (merge h1 h2) (merge_pairs hs)
  let find_min = function
    | E -> raise Empty
    | T (x, _) -> x
  let delete_min = function
    | E -> raise Empty
    | T (_, hs) -> merge_pairs hs
end
