exception Empty
exception Subscript

module type RANDOM_ACCESS_LIST = Ch9.RANDOM_ACCESS_LIST

module AltBiinaryRandomAccessList : RANDOM_ACCESS_LIST =
struct
  type 'a ra_list =
    | Nil
    | Zero of ('a * 'a) ra_list
    | One of 'a * ('a * 'a) ra_list

  let empty = Nil
  let is_empty = function
    | Nil -> true
    | _ -> false

  let rec cons : 'a. 'a -> 'a ra_list -> 'a ra_list = fun x -> function
    | Nil -> One (x, Nil)
    | Zero ps -> One (x, ps)
    | One (y, ps) -> Zero (cons (x, y) ps)

  let rec uncons : 'a. 'a ra_list -> 'a * 'a ra_list = function
    | Nil -> raise Empty
    | One (x, Nil) -> x, Nil
    | One (x, ps) -> x, Zero ps
    | Zero ps ->
        let (x, y), ps' = uncons ps in
          x, One (y, ps')

  let head xs = fst (uncons xs)
  let tail xs = snd (uncons xs)

  let rec lookup : 'a. int -> 'a ra_list -> 'a = fun i -> function
    | Nil -> raise Subscript
    | One (x, _) when i = 0 -> x
    | One (x, ps) -> lookup (i-1) (Zero ps)
    | Zero ps ->
        let x, y = lookup (i/2) ps in
          if i mod 2 = 0 then x else y

  let rec fupdate : 'a. ('a -> 'a) -> int -> 'a ra_list -> 'a ra_list = fun f i -> function
    | Nil -> raise Subscript
    | One (x, ps) when i = 0 -> One (f x, ps)
    | One (x, ps) -> cons x (fupdate f (i-1) (Zero ps))
    | Zero ps ->
        let f' (x, y) = if i mod 2 = 0 then (f x, y) else (x, f y) in
          Zero (fupdate f' (i/2) ps)

  let update i y xs = fupdate (fun _ -> y) i xs
end

module type QUEUE = Ch8.QUEUE

module BootstrappedQueue : QUEUE =
struct
  type 'a queue =
    | E
    | Q of int * 'a list * 'a list Lazy.t queue * int * 'a list

  let empty = E
  let is_empty = function
    | E -> true
    | _ -> false

  let rec check_q : 'a. 'a queue -> 'a queue = function
    | Q (lenfm, f, m, lenr, r) as q ->
        if lenr <= lenfm then check_f q
        else check_f (Q (lenfm+lenr, f, snoc m (lazy (List.rev r)), 0, []))
    | E -> failwith "unreachable"
  and check_f : 'a. 'a queue -> 'a queue = function
    | Q (_, [], E, _, _) -> E
    | Q (lenfm, [], m, lenr, r) ->
        Q (lenfm, Lazy.force (head m), tail m, lenr, r)
    | q -> q

  and snoc : 'a. 'a queue -> 'a -> 'a queue = fun q x -> match q with
    | E -> Q (1, [x], E, 0, [])
    | Q (lenfm, f, m, lenr, r) ->
        check_q (Q (lenfm, f, m, lenr+1, x :: r))
  and head : 'a. 'a queue -> 'a = function
    | E -> raise Empty
    | Q (_, x :: _, _, _, _) -> x
    | Q (_, [], _, _, _) -> failwith "unreachable"
  and tail : 'a. 'a queue -> 'a queue = function
    | E -> raise Empty
    | Q (lenfm, x :: f', m, lenr, r) ->
        check_q (Q (lenfm-1, f', m, lenr, r))
    | Q (_, [], _, _, _) -> failwith "unreachable"
end

module type CATENABLE_LIST =
sig
  type 'a cat

  val empty : 'a cat
  val is_empty : 'a cat -> bool

  val cons : 'a -> 'a cat -> 'a cat
  val snoc : 'a cat -> 'a -> 'a cat
  val (++) : 'a cat -> 'a cat -> 'a cat

  val head : 'a cat -> 'a (* raises Empty if list is empty *)
  val tail : 'a cat -> 'a cat (* raises Empty if list is empty *)
end

module CatenableList (Q : QUEUE) : CATENABLE_LIST =
struct
  type 'a cat =
    | E
    | C of 'a * 'a cat Lazy.t Q.queue

  let empty = E
  let is_empty = function
    | E -> true
    | _ -> false

  let link t s = match t with
    | C (x, q) -> C (x, Q.snoc q s)
    | E -> failwith "unreachable"
  let rec link_all q =
    let lazy t = Q.head q in
    let q' = Q.tail q in
      if Q.is_empty q' then t else link t (lazy (link_all q'))

  let (++) xs ys = match xs, ys with
    | _, E -> xs
    | E, _ -> ys
    | _, _ -> link xs (lazy ys)
  let cons x xs =
    C (x, Q.empty) ++ xs
  let snoc xs x =
    xs ++ C (x, Q.empty)

  let head = function
    | E -> raise Empty
    | C (x, _) -> x
  let tail = function
    | E -> raise Empty
    | C (_, q) ->
        if Q.is_empty q then E else link_all q
end

module type ORDERED= Ch9.ORDERED
module type HEAP = Ch9.HEAP

module BootstrappedHeap
  (MakeH : functor (Element : ORDERED) -> HEAP with module Elem = Element)
  (Element : ORDERED) : (HEAP with module Elem = Element) =
struct
  module Elem = Element

  module rec BootstrappedElem : (ORDERED with type t = Elem.t * PrimH.heap) =
  struct
    type t = Elem.t * PrimH.heap
    let compare (x, _) (y, _) = Elem.compare x y
  end
  and PrimH : (HEAP with module Elem := BootstrappedElem) =
    MakeH(BootstrappedElem)

  type heap =
    | E
    | H of BootstrappedElem.t

  let empty = E
  let is_empty = function
    | E -> true
    | _ -> false

  let merge h1 h2 = match h1, h2 with
    | E, _ -> h2
    | _, E -> h1
    | H ((x, p1) as h1'), H ((y, p2) as h2') ->
        if Elem.compare x y <= 0 then
          H (x, PrimH.insert h2' p1)
        else
          H (y, PrimH.insert h1' p2)
  let insert x h =
    merge (H (x, PrimH.empty)) h

  let find_min = function
    | E -> raise Empty
    | H (x, _) -> x
  let delete_min = function
    | E -> raise Empty
    | H (_, p) ->
        if PrimH.is_empty p then E
        else
          let y, p1 = PrimH.find_min p in
          let p2 = PrimH.delete_min p in
            H (y, PrimH.merge p1 p2)
end

module type FINITE_MAP =
sig
  type key
  type 'a map

  val empty : 'a map
  val bind : key -> 'a -> 'a map -> 'a map
  val lookup : key -> 'a map -> 'a (* raise Not_found if key is not found *)
end

module Trie (M : FINITE_MAP) : FINITE_MAP =
struct
  type key = M.key list

  type 'a map =
    | Trie of 'a option * 'a map M.map

  let empty = Trie (None, M.empty)

  let rec lookup s t = match s, t with
    | [], Trie (None, _) -> raise Not_found
    | [], Trie (Some x, _) -> x
    | k :: ks, Trie (_, m) ->
        lookup ks (M.lookup k m)

  let rec bind s x (Trie (v, m)) = match s with
    | [] -> Trie (Some x, m)
    | k :: ks ->
        let t = try M.lookup k m with
          | Not_found -> empty
        in
        let t' = bind ks x t in
          Trie (v, M.bind k t' m)
end
