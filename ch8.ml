exception Empty

module type QUEUE = Ch7.QUEUE

module HoodMelvilleQueue : QUEUE =
struct
  type 'a rotation_state =
    | Idle
    | Reversing of int * 'a list * 'a list * 'a list * 'a list
    | Appending of int * 'a list * 'a list
    | Done of 'a list

  type 'a queue = int * 'a list * 'a rotation_state * int * 'a list

  let exec = function
    | Reversing (ok, x :: f, f', y :: r, r') ->
        Reversing (ok+1, f, x :: f', r, y :: r')
    | Reversing (ok, [], f', [y], r') ->
        Appending (ok, f', y :: r')
    | Appending (0, f', r') ->
        Done r'
    | Appending (ok, x :: f', r') ->
        Appending (ok-1, f', x :: r')
    | state -> state

  let invalidate = function
    | Reversing (ok, f, f', r, r') ->
        Reversing (ok-1, f, f', r, r')
    | Appending (0, f', x :: r') ->
        Done r'
    | Appending (ok, f', r') ->
        Appending (ok-1, f', r')
    | state -> state

  let exec2 (lenf, f, state, lenr, r) =
    match exec (exec state) with
      | Done newf -> (lenf, newf, Idle, lenr, r)
      | newstate -> (lenf, f, newstate, lenr, r)

  let check (lenf, f, state, lenr, r as q) =
    if lenr <= lenf then exec2 q
    else let newstate = Reversing (0, f, [], r, []) in
      exec2 (lenf+lenr, f, newstate, 0, [])

  let empty = 0, [], Idle, 0, []
  let is_empty (lenf, _, _, _, _) = lenf = 0

  let snoc (lenf, f, state, lenr, r) x =
    check (lenf, f, state, lenr+1, x :: r)
  let head = function
    | _, [], _, _, _ -> raise Empty
    | _, x :: _, _, _, _ -> x
  let tail = function
    | _, [], _, _, _ -> raise Empty
    | lenf, x :: f, state, lenr, r ->
        check (lenf-1, f, invalidate state, lenr, r)
end

module type DEQUE =
sig
  type 'a queue

  val empty : 'a queue
  val is_empty : 'a queue -> bool

  val cons : 'a -> 'a queue -> 'a queue
  val head : 'a queue -> 'a (* raises Empty if queue is empty *)
  val tail : 'a queue -> 'a queue (* raises Empty if queue is empty *)

  val snoc : 'a queue -> 'a -> 'a queue
  val last : 'a queue -> 'a (* raises Empty if queue is empty *)
  val init : 'a queue -> 'a queue (* raises Empty if queue is empty *)
end

module Stream = Ch4.Stream

module BankersDeque (C : sig val c : int end) : DEQUE = (* c > 1 *)
struct
  let c = C.c
  open Stream

  type 'a queue = int * 'a stream * int * 'a stream

  let empty = 0, lazy Nil, 0, lazy Nil
  let is_empty (lenf, _, lenr, _) = lenf+lenr = 0

  let check (lenf, f, lenr, r as q) =
    if lenf > c * lenr + 1 then
      let i = (lenf+lenr)/2 in
      let j = lenf+lenr-i in
      let f' = take i f in
      let r' = r ++ reverse (drop i f) in
        i, f', j, r'
    else if lenr > c * lenf + 1 then
      let j = (lenf+lenr)/2 in
      let i = lenf+lenr-j in
      let r' = take j r in
      let f' = f ++ reverse (drop j r) in
        i, f', j, r'
    else q

  let cons x (lenf, f, lenr, r) =
    check (lenf+1, lazy (Cons (x,f)), lenr, r)
  let head = function
    | _, lazy Nil, _, lazy Nil -> raise Empty
    | _, lazy Nil, _, lazy (Cons (x, _)) -> x
    | _, lazy (Cons (x, _)), _, _ -> x
  let tail = function
    | _, lazy Nil, _, lazy Nil -> raise Empty
    | _, lazy Nil, _, lazy (Cons (_, _)) -> empty
    | lenf, lazy (Cons (_, f')), lenr, r ->
        check (lenf-1, f', lenr, r)

  let snoc (lenf, f, lenr, r) x =
    check (lenf, f, lenr+1, lazy (Cons (x,r)))
  let last = function
    | _, lazy Nil, _, lazy Nil -> raise Empty
    | _, lazy (Cons (x, _)), _, lazy Nil -> x
    | _, _, _, lazy (Cons (x, _)) -> x
  let init = function
    | _, lazy Nil, _, lazy Nil -> raise Empty
    | _, lazy (Cons (_, _)), _, lazy Nil -> empty
    | lenf, f, lenr, lazy (Cons (_, r')) ->
        check (lenf, f, lenr-1, r')
end

module RealTimeDeque (C : sig val c : int end) : DEQUE = (* c > 1 *)
struct
  let c = C.c
  open Stream

  type 'a queue =
      int * 'a stream * 'a stream * int * 'a stream * 'a stream

  let empty = (0, lazy Nil, lazy Nil, 0, lazy Nil, lazy Nil)
  let is_empty (lenf, _, _, lenr, _, _) = (lenf+lenr = 0)

  let exec1 = function
    | lazy (Cons (_, s)) -> s
    | s -> s
  let exec2 s = exec1 (exec1 s)

  let rec rotate_rev s r a = match s, r, a with
    | lazy Nil, _, _ -> reverse r ++ a
    | lazy (Cons (x, f)), _, _ ->
        lazy (Cons (x, rotate_rev f (drop c r) (reverse (take c r ++ a))))
  let rec rotate_drop f j r =
    if j < c then rotate_rev f (drop j r) (lazy Nil)
    else match f with
      | lazy (Cons (x, f')) ->
          lazy (Cons (x, rotate_drop f' (j-c) (drop c r)))
      | lazy Nil -> failwith "unreachable"

  let check (lenf, f, sf, lenr, r, sr as q) =
    if lenf > c * lenr + 1 then
      let i = (lenf+lenr)/2 in
      let j = lenf+lenr-i in
      let f' = take i f in
      let r' = rotate_drop r i f in
        i, f', f', j, r', r'
    else if lenr > c * lenf + 1 then
      let j = (lenf+lenr)/2 in
      let i = lenf+lenr-j in
      let r' = take j r in
      let f' = rotate_drop f j r in
        i, f', f', j, r', r'
    else q

  let cons x (lenf, f, sf, lenr, r, sr) =
    check (lenf+1, lazy (Cons (x, f)), exec1 sf, lenr, r, exec1 sr)
  let head = function
    | _, lazy Nil, _, _, lazy Nil, _ -> raise Empty
    | _, lazy Nil, _, _, lazy (Cons (x, _)), _ -> x
    | _, lazy (Cons (x, _)), _, _, _, _ -> x
  let tail = function
    | _, lazy Nil, _, _, lazy Nil, _ -> raise Empty
    | _, lazy Nil, _, _, lazy (Cons _), _ -> empty
    | lenf, lazy (Cons (x, f')), sf, lenr, r, sr ->
        check (lenf-1, f', exec2 sf, lenr, r, exec2 sr)

  let snoc (lenf, f, sf, lenr, r, sr) x =
    check (lenf, f, exec1 sf, lenr+1, lazy (Cons (x, r)), exec1 sr)
  let last = function
    | _, lazy Nil, _, _, lazy Nil, _ -> raise Empty
    | _, lazy (Cons (x, _)), _, _, lazy Nil, _ -> x
    | _, _, _, _, lazy (Cons (x, _)), _ -> x
  let init = function
    | _, lazy Nil, _, _, lazy Nil, _ -> raise Empty
    | _, lazy (Cons _), _, _, lazy Nil, _ -> empty
    | lenf, f, sf, lenr, lazy (Cons (_, r')), sr ->
        check (lenf, f, exec2 sf, lenr-1, r', exec2 sr)
end
