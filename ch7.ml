exception Empty

module type QUEUE = Ch6.QUEUE
module Stream = Ch6.Stream

module RealTimeQueue : QUEUE =
struct
  open Stream

  type 'a queue = 'a stream * 'a list * 'a stream

  let empty =
    lazy Nil, [], lazy Nil
  let is_empty = function
    | lazy Nil, _, _ -> true
    | _ -> false

  let rec rotate = function
    | lazy Nil, y :: _, a -> lazy (Cons (y, a))
    | lazy (Cons (x, xs)), y :: ys, a ->
        lazy (Cons (x, rotate (xs, ys, lazy (Cons (y,a)))))
    | _ -> failwith "unreachable"

  let exec = function
    | f, r, lazy (Cons (_, s)) -> f, r, s
    | f, r, lazy Nil ->
        let f' = rotate (f, r, lazy Nil) in
          f', [], f'

  let snoc (f, r, s) x =
    exec (f, x :: r, s)

  let head = function
    | lazy Nil, _, _ -> raise Empty
    | lazy (Cons (x, _)), _, _ -> x
  let tail = function
    | lazy Nil, _, _ -> raise Empty
    | lazy (Cons (_, f)), r, s -> exec (f, r, s)
end

module type ORDERED = Ch6.ORDERED
module type HEAP = Ch6.HEAP

module ScheduledBinomialHeap (Element: ORDERED) : (HEAP with module Elem = Element) =
struct
  open Stream

  module Elem = Element

  type tree = Node of Elem.t * tree list
  type digit =
    | Zero
    | One of tree
  type schedule = digit stream list
  type heap = digit stream * schedule

  let empty = (lazy Nil, [])
  let is_empty = function
    | (lazy Nil, _) -> true
    | _ -> false

  let link (Node (x1, c1) as t1) (Node (x2, c2) as t2) =
    if Elem.compare x1 x2 <= 0 then
      Node (x1, t2 :: c1)
    else
      Node (x2, t1 :: c2)
  let rec ins_tree t = function
    | lazy Nil -> lazy (Cons (One t, lazy Nil))
    | lazy (Cons (Zero, ds)) -> lazy (Cons (One t, ds))
    | lazy (Cons (One t', ds)) ->
        lazy (Cons (Zero, ins_tree (link t t') ds))

  let rec mrg ts1 ts2 =
    match (ts1, ts2) with
      | _, lazy Nil -> ts1
      | lazy Nil, _ -> ts2
      | lazy (Cons (Zero, ds1)), lazy (Cons (d, ds2))
      | lazy (Cons (d, ds1)), lazy (Cons (Zero, ds2)) ->
          lazy (Cons (d, (mrg ds1 ds2)))
      | lazy (Cons (One t1, ds1)), lazy (Cons (One t2, ds2)) ->
          lazy (Cons (Zero, ins_tree (link t1 t2) (mrg ds1 ds2)))

  let rec normalize ds =
    match ds with
      | lazy Nil -> ds
      | lazy (Cons (_, ds')) -> (ignore (normalize ds'); ds)
  let exec = function
    | [] -> []
    | lazy (Cons (Zero, job)) :: sched -> job :: sched
    | _ :: sched -> sched

  let insert x (ds, sched) =
    let ds' = ins_tree (Node (x, [])) ds in
      ds', exec (exec (ds' :: sched))
  let merge (ds1, _) (ds2, _) =
    let ds = normalize (mrg ds1 ds2) in
      (ds, [])

  let rec remove_min_tree = function
    | lazy Nil -> raise Empty
    | lazy (Cons (Zero, ds)) ->
        let (t', ds') = remove_min_tree ds in
          (t', lazy (Cons (Zero, ds')))
    | lazy (Cons (One (Node (x, _) as t), ds)) ->
        let Node (x', _) as t', ds' = remove_min_tree ds in
          if Elem.compare x x' <= 0 then
            t, lazy (Cons (Zero, ds))
          else
            t', lazy (Cons (One t, ds'))

  let rec list_to_stream = function
    | [] -> lazy Nil
    | x :: xs -> lazy (Cons (x, list_to_stream xs))

  let find_min (ds, _) =
    let Node (x, _), _ = remove_min_tree ds in x
  let delete_min (ds, _) =
    let (Node (x, c), ds') = remove_min_tree ds in
    let ds'' =
      mrg (list_to_stream (List.map (fun e -> One e) (List.rev c))) ds' in
      normalize ds'', []
end

module type SORTABLE = Ch6.SORTABLE

module BottomUpMergeSort (Element : ORDERED) : (SORTABLE with module Elem = Element) =
struct
  open Stream

  module Elem = Element

  type schedule = Elem.t stream list
  type sortable = int * (Elem.t stream * schedule) list

  let rec mrg xs ys = lazy (
    match xs, ys with
      | lazy Nil, ys -> Lazy.force ys
      | xs, lazy Nil -> Lazy.force xs
      | lazy (Cons (x, xs')), lazy (Cons (y, ys')) ->
          if Elem.compare x y <= 0 then
            Cons (x, mrg xs' ys)
          else
            Cons (y, mrg xs ys')
  )

  let rec exec1 = function
    | [] -> []
    | lazy Nil :: sched -> exec1 sched
    | lazy (Cons (x, xs)) :: sched -> xs :: sched
  let exec2 (xs, sched) =
    (xs, exec1 (exec1 sched))

  let empty = 0, []
  let add x (size, segs) =
    let rec add_seg xs segs size rsched =
      if size mod 2 = 0 then (xs, List.rev rsched) :: segs
      else match segs with
        | (xs', []) :: segs' ->
            let xs'' = mrg xs xs' in
              add_seg xs'' segs' (size/2) (xs'' :: rsched)
        | _ -> failwith "unreachable"
    in
    let segs' = add_seg (lazy (Cons (x, lazy Nil))) segs size [] in
      size+1, List.map exec2 segs'

  let rec stream_to_list = function
    | lazy Nil -> []
    | lazy (Cons (x, xs)) -> x :: stream_to_list xs

  let sort (size, segs) =
    let rec mrg_all = function
      | xs, [] -> xs
      | xs, (xs', _) :: segs ->
          mrg_all ((mrg xs xs'), segs)
    in
      stream_to_list (mrg_all ((lazy Nil), segs))
end
