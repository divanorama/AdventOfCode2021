let map = https://prelude.dhall-lang.org/v21.1.0/List/map
let fold = https://prelude.dhall-lang.org/v21.1.0/List/fold
let reverse = https://prelude.dhall-lang.org/v21.1.0/List/reverse
let head = https://prelude.dhall-lang.org/v21.1.0/List/head
let null = https://prelude.dhall-lang.org/v21.1.0/List/null
let filter = https://prelude.dhall-lang.org/v21.1.0/List/filter
let enumerate = https://prelude.dhall-lang.org/v21.1.0/Natural/enumerate
let sum = https://prelude.dhall-lang.org/v21.1.0/Natural/sum
let subtract = https://prelude.dhall-lang.org/v21.1.0/Natural/subtract
let equal = https://prelude.dhall-lang.org/v21.1.0/Natural/equal
let lt = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThan
let not = https://prelude.dhall-lang.org/v21.1.0/Bool/not
let or = https://prelude.dhall-lang.org/v21.1.0/Bool/or

let id = \(t : Type) -> \(x : t) -> x
let itype = \(t : Type) -> {index: Natural, value: t}
let at = \(t : Type) -> \(i : Natural) -> \(x : List t) -> head t ( map (itype t) t (\(q : itype t) -> q.value) (filter (itype t) (\(q : itype t) -> equal q.index i) (List/indexed t x))) : Optional t
let att = \(t : Type) -> \(def : t) -> \(i : Natural) -> \(x : List t) -> merge {Some = id t, None = def} (at t i x) : t
let notEqual = \(a : Natural) -> \(b : Natural) -> not (equal a b)

let cardt = List (List Natural)
let inpt = { picks: List Natural, cards: List cardt }

let ex : inpt = ./01.dhall
let main : inpt = ./input.dhall

let rowt = List Natural
let handt = {sum: Natural, rows: List rowt}

let conv = \(c : cardt) ->
  let sum = fold (List Natural) c Natural (\(x : List Natural) -> \(acc : Natural) -> acc + sum x) 0
  let f : Natural -> rowt = \(pos : Natural) -> map (List Natural) Natural (att Natural 666 pos) c
  let rows = c # (map Natural rowt f (enumerate 5))
  in {sum = sum, rows = rows  }

let state = {hands : List handt, won : Optional Natural}

let solve = \(inp : inpt) ->
  let st0 : state = {hands = map cardt handt conv inp.cards, won = None Natural}
  let won = \(x : state) -> merge { Some = \(x: Natural) -> True, None = False } x.won
  let act = \(x : Natural) -> \(h : handt) ->
    let flt = filter Natural (notEqual x)
    let rows1 = map rowt rowt flt h.rows
    let some1 = \(r : rowt) -> or (map Natural Bool (equal x) r)
    let some = or (map rowt Bool some1 h.rows)
    in {rows = rows1, sum = subtract (if some then x else 0) h.sum}
  let score = \(x: Natural) -> \(h : handt) -> if or (map rowt Bool (null Natural) h.rows) then Some (x * h.sum) else None Natural
  let step = \(x : Natural) -> \(s : state) -> if won s then s else
    let hands1 = map handt handt (act x) s.hands
    let scs = map handt (Optional Natural) (score x) hands1
    let up = \(a : Optional Natural) -> \(b : Optional Natural) -> merge { Some = \(bx : Natural) -> merge { Some = \(ax : Natural) -> if lt ax bx then b else a, None = b} a , None = a } b
    let bs = fold (Optional Natural) scs (Optional Natural) up (None Natural)
    in {hands = hands1, won = merge { Some = \(x: Natural) -> Some x, None = None Natural } bs}
  in (fold Natural (reverse Natural inp.picks) state step st0).won

let tex = assert : (solve ex) === Some 4512

in solve main
