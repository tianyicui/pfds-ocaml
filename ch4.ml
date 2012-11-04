module type STREAM =
sig
  type 'a stream_cell =
    | Nil
    | Cons of 'a * 'a stream
  and 'a stream =
    'a stream_cell Lazy.t

  val (++) : 'a stream -> 'a stream -> 'a stream
  val take : int -> 'a stream -> 'a stream
  val drop : int -> 'a stream -> 'a stream
  val reverse : 'a stream -> 'a stream
end

module Stream : STREAM =
struct
  type 'a stream_cell =
    | Nil
    | Cons of 'a * 'a stream
  and 'a stream =
    'a stream_cell Lazy.t

  let rec (++) xs ys = lazy (
    match xs with
      | lazy Nil -> Lazy.force ys
      | lazy (Cons (x, s)) -> Cons (x, s ++ ys)
  )

  let rec take n l = lazy (
    match n, l with
      | 0, _
      | _, lazy Nil -> Nil
      | _, lazy (Cons (x, s)) ->
          Cons (x, take (n-1) s)
  )

  let drop n s = lazy (
    let rec drop' = function
      | (0, s) -> Lazy.force s
      | (n, lazy Nil) -> Nil
      | (n, lazy (Cons (x, s))) -> drop' (n-1, s)
    in drop' (n, s)
  )

  let reverse s = lazy (
    let rec reverse' l acc =
      match Lazy.force l with
        | Nil -> acc
        | Cons (x, s) -> reverse' s (Cons (x, lazy acc))
    in reverse' s Nil
  )
end
