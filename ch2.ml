exception Empty
exception Subscript

module type STACK =
sig
  type 'a stack

  val empty : 'a stack
  val is_empty : 'a stack -> bool

  val cons : 'a -> 'a stack -> 'a stack
  val head : 'a stack -> 'a (* raises Empty if stack is empty *)
  val tail : 'a stack -> 'a stack (* raises Empty if stack is empty *)

  val (++) : 'a stack -> 'a stack -> 'a stack
  val update : 'a stack -> int -> 'a -> 'a stack
end

module ListStack : STACK =
struct
  type 'a stack = 'a list

  let empty = []
  let is_empty s =
    s = []

  let cons x s =
    x :: s
  let head = function
    | [] -> raise Empty
    | h :: _ -> h
  let tail = function
    | [] -> raise Empty
    | _ :: t -> t

  let rec (++) xs ys =
    match xs with
      | [] -> ys
      | xh :: xt -> xh :: (xt ++ ys)
  let rec update s i x =
    match s with
      | [] -> raise Subscript
      | h :: t ->
          if i = 0 then x :: t else h :: update t (i-1) x
end

module CustomStack : STACK =
struct
  type 'a stack =
    | Nil
    | Cons of 'a * 'a stack

  let empty = Nil
  let is_empty = function
    | Nil -> true
    | _ -> false

  let cons x s =
    Cons (x, s)
  let head = function
    | Nil -> raise Empty
    | Cons (h, _) -> h
  let tail = function
    | Nil -> raise Empty
    | Cons (_, t) -> t

  let rec (++) xs ys =
    match xs with
      | Nil -> ys
      | Cons (xh, xt) -> Cons (xh, xt ++ ys)
  let rec update s i x =
    match s with
      | Nil -> raise Subscript
      | Cons (h, t) ->
          if i = 0 then Cons (x, t) else Cons (h, update t (i-1) x)
end

module type SET =
sig
  type elem
  type set

  val empty : set
  val insert : elem -> set -> set
  val member : elem -> set -> bool
end

module type ORDERED =
sig
  type t

  val compare : t -> t -> int
end

module UnbalancedSet (Element : ORDERED) : (SET with type elem = Element.t) =
struct
  type elem = Element.t
  type set =
    | Empty
    | Tree of set * elem * set

  let empty = Empty

  let rec member x = function
    | Empty -> false
    | Tree (l, y, r) ->
        match Element.compare x y with
          | 0 -> true
          | n when n < 0 -> member x l
          | _ -> member x r

  let rec insert x = function
    | Empty -> Tree (Empty, x, Empty)
    | Tree (l, y, r) as s ->
        match Element.compare x y with
          | 0 -> s
          | n when n < 0 -> Tree (insert x l, y, r)
          | _ -> Tree (l, y, insert x r)
end
