exception Empty

module type QUEUE = Ch8.QUEUE

module ImplicitQueue : QUEUE =
struct
  type 'a digit =
    | One of 'a
    | Two of 'a * 'a
  type 'a queue =
    | Shallow of 'a option
    | Deep of 'a digit * ('a * 'a) queue Lazy.t * 'a option

  let empty = Shallow None
  let is_empty = function
    | Shallow None-> true
    | _ -> false

  let force = Lazy.force

  let rec snoc : 'a. 'a queue -> 'a -> 'a queue = fun q y -> match q with
    | Shallow None -> Shallow (Some y)
    | Shallow (Some x) -> Deep (Two (x, y), lazy empty, None)
    | Deep (f, m, None) -> Deep (f, m, Some y)
    | Deep (f, m, Some x) -> Deep (f, lazy (snoc (force m) (x, y)), None)

  let head = function
    | Shallow None -> raise Empty
    | Shallow (Some x) -> x
    | Deep (One x, _, _) -> x
    | Deep (Two (x, _), _, _) -> x
  let rec tail : 'a. 'a queue -> 'a queue = function
    | Shallow None -> raise Empty
    | Shallow (Some x) -> empty
    | Deep (Two (_, y), m, r) -> Deep (One y, m, r)
    | Deep (One x, lazy q, r) ->
        if is_empty q then Shallow r
        else let y, z = head q in
          Deep (Two (y, z), lazy (tail q), r)
end

module type CATENABLE_DEQUE =
sig
  type 'a cat

  val empty : 'a cat
  val is_empty : 'a cat -> bool

  val cons : 'a -> 'a cat -> 'a cat
  val head : 'a cat -> 'a
  val tail : 'a cat -> 'a cat

  val snoc : 'a cat -> 'a -> 'a cat
  val last : 'a cat -> 'a
  val init : 'a cat -> 'a cat

  val (++) : 'a cat -> 'a cat -> 'a cat
end

module type DEQUE = Ch8.DEQUE

module SimpleCatenableDeque (D : DEQUE) : CATENABLE_DEQUE =
struct
  type 'a cat =
    | Shallow of 'a D.queue
    | Deep of 'a D.queue * 'a D.queue cat Lazy.t * 'a D.queue

  let too_small d = D.is_empty d || D.is_empty (D.tail d)

  let dappend_l d1 d2 =
    if D.is_empty d1 then d2 else D.cons (D.head d1) d2
  let dappend_r d1 d2 =
    if D.is_empty d2 then d1 else D.snoc d1 (D.head d2)

  let empty = Shallow D.empty
  let is_empty = function
    | Shallow d -> D.is_empty d
    | _ -> false

  let force = Lazy.force

  let cons x = function
    | Shallow d -> Shallow (D.cons x d)
    | Deep (f, m, r) -> Deep (D.cons x f, m, r)
  let head = function
    | Shallow d -> D.head d
    | Deep (f, _, _) -> D.head f
  let rec tail : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.tail d)
    | Deep (f, m, r) ->
        let f' = D.tail f in
          if not (too_small f') then Deep (f', m, r)
          else if is_empty (force m) then Shallow (dappend_l f' r)
          else Deep (dappend_r f' (head (force m)), lazy (tail (force m)), r)

  let snoc c x = match c with
    | Shallow d -> Shallow (D.snoc d x)
    | Deep (f, m, r) -> Deep (f, m, D.snoc r x)
  let last = function
    | Shallow d -> D.last d
    | Deep (_, _, r) -> D.last r
  let rec init : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.init d)
    | Deep (f, m, r) ->
        let r' = D.init r in
          if not (too_small r') then Deep (f, m, r')
          else if is_empty (force m) then Shallow (dappend_r f r')
          else Deep (f, lazy (init (force m)), dappend_l (last (force m)) r')

  let rec (++) : 'a. 'a cat -> 'a cat -> 'a cat = fun c1 c2 -> match c1, c2 with
    | Shallow d1, Shallow d2 ->
        if too_small d1 then Shallow (dappend_l d1 d2)
        else if too_small d2 then Shallow (dappend_r d1 d2)
        else Deep (d1, lazy empty, d2)
    | Shallow d, Deep (f, m, r) ->
        if too_small d then Deep (dappend_l d f, m, r)
        else Deep (d, lazy (cons f (force m)), r)
    | Deep (f, m, r), Shallow d ->
        if too_small d then Deep (f, m, dappend_r r d)
        else Deep (f, lazy (snoc (force m) r), d)
    | Deep (f1, m1, r1), Deep (f2, m2, r2) ->
        Deep (f1, lazy (snoc (force m1) r1 ++ cons f2 (force m2)), r2)
end

module ImplicitCatenableDeque (D : sig
                                 include DEQUE
                                 val size : 'a queue -> int
                               end)
  : CATENABLE_DEQUE =
struct
  type 'a cat =
    | Shallow of 'a D.queue
    | Deep of 'a D.queue * 'a cmpd_elem cat Lazy.t * 'a D.queue
                         * 'a cmpd_elem cat Lazy.t * 'a D.queue
  and 'a cmpd_elem =
    | Simple of 'a D.queue
    | Cmpd of 'a D.queue * 'a cmpd_elem cat Lazy.t * 'a D.queue

  let empty = Shallow D.empty
  let is_empty = function
    | Shallow d -> D.is_empty d
    | _ -> false

  let cons x = function
    | Shallow d -> Shallow (D.cons x d)
    | Deep (f, a, m, b, r) -> Deep (D.cons x f, a, m, b, r)
  let head = function
    | Shallow d -> D.head d
    | Deep (f, _, _, _, _) -> D.head f

  let snoc c x = match c with
    | Shallow d -> Shallow (D.snoc d x)
    | Deep (f, a, m, b, r) -> Deep (f, a, m, b, D.snoc r x)
  let last = function
    | Shallow d -> D.last d
    | Deep (_, _, _, _, r) -> D.last r

  let share f r =
    let m = D.cons (D.last f) (D.cons (D.head r) D.empty) in
      D.init f, m, D.tail r
  let rec dappend_l d1 d2 =
    if D.is_empty d1 then d2
    else dappend_l (D.init d1) (D.cons (D.last d1) d2)
  let rec dappend_r d1 d2 =
    if D.is_empty d2 then d1
    else dappend_r (D.snoc d1 (D.head d2)) (D.tail d2)

  let force = Lazy.force

  let (++) c1 c2 = match c1, c2 with
    | Shallow d1, Shallow d2 ->
        if D.size d1 < 4 then Shallow (dappend_l d1 d2)
        else if D.size d2 < 4 then Shallow (dappend_r d1 d2)
        else let f, m, r = share d1 d2 in
          Deep (f, lazy empty, m, lazy empty, r)
    | Shallow d, Deep (f, a, m, b, r) ->
        if D.size d < 4 then Deep (dappend_l d f, a, m, b, r)
        else Deep (d, lazy (cons (Simple f) (force a)), m, b, r)
    | Deep (f, a, m, b, r), Shallow d ->
        if D.size d < 4 then Deep (f, a, m, b, dappend_r r d)
        else Deep (f, a, m, lazy (snoc (force b) (Simple r)), d)
    | Deep (f1, a1, m1, b1, r1), Deep (f2, a2, m2, b2, r2) ->
        let r1', m, f2' = share r1 f2 in
        let a1' = lazy (snoc (force a1) (Cmpd (m1, b1, r1'))) in
        let b2' = lazy (cons (Cmpd (f2', a2, m2)) (force b2)) in
          Deep (f1, a1', m, b2', r2)

  let replace_head x = function
    | Shallow d -> Shallow (D.cons x (D.tail d))
    | Deep (f, a, m, b, r) ->
        Deep (D.cons x (D.tail f), a, m, b, r)

  let rec tail : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.tail d)
    | Deep (f, a, m, b, r) ->
        if D.size f > 3 then Deep (D.tail f, a, m, b, r)
        else if not (is_empty (force a)) then
          match head (force a) with
            | Simple d ->
                let f' = dappend_l (D.tail f) d in
                  Deep (f', lazy (tail (force a)), m, b, r)
            | Cmpd (f', c', r') ->
                let f'' = dappend_l (D.tail f) f' in
                let a'' = lazy (force c' ++ replace_head (Simple r') (force a)) in
                  Deep (f'', a'', m, b, r)
        else if not (is_empty (force b)) then
          match head (force b) with
            | Simple d ->
                let f' = dappend_l (D.tail f) m in
                  Deep (f', lazy empty, d, lazy (tail (force b)), r)
            | Cmpd (f', c', r') ->
                let f'' = dappend_l (D.tail f) m in
                let a'' = lazy (cons (Simple f') (force c')) in
                  Deep (f'', a'', r', lazy (tail (force b)), r)
        else Shallow (dappend_l (D.tail f) m) ++ Shallow r

  let replace_last x = function
    | Shallow d -> Shallow (D.snoc (D.init d) x)
    | Deep (f, a, m, b, r) ->
        Deep (f, a, m, b, D.snoc (D.init f) x)

  let rec init : 'a. 'a cat -> 'a cat = function
    | Shallow d -> Shallow (D.init d)
    | Deep (f, a, m, b, r) ->
        if D.size r > 3 then Deep (f, a, m, b, D.init r)
        else if not (is_empty (force b)) then
          match last (force b) with
            | Simple d ->
                let r' = dappend_r d (D.init r) in
                  Deep (f, a, m, lazy (init (force b)), r')
            | Cmpd (f', c', r') ->
                let r'' = dappend_r r' (D.init r) in
                let b'' = lazy (replace_last (Simple f') (force b) ++ force c') in
                  Deep (f, a, m, b'', r'')
        else if not (is_empty (force a)) then
          match last (force a) with
            | Simple d ->
                let r' = dappend_r m (D.init r) in
                  Deep (f, lazy (tail (force a)), d, lazy empty, r')
            | Cmpd (f', c', r') ->
                let r'' = dappend_r m (D.init r) in
                let b'' = lazy (snoc (force c') (Simple r')) in
                  Deep (f, lazy (init (force a)), f', b'', r'')
        else Shallow f ++ Shallow (dappend_r m (D.init r))
end
