let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let lnt = List Natural
let inpt = List lnt

let ex : inpt = ./01.dhall

let hd = \(t : Type) -> \(def : t) -> \(x : List t) -> merge { None = def, Some = \(x : t) -> x } (prelude.List.head t x)

let triplet = \(t : Type) -> {_1 : t, _2 : t, _3 : t}

let zip3 = \(t : Type) -> \(a : List t) -> \(b : List t) -> \(c : List t) ->
  let t2 = {_1: t, _2 : t}
  let t3 = {_1 : t, _2: t2}
  in prelude.List.map t3 (triplet t) (\(x : t3) -> {_1 = x._1, _2 = x._2._1, _3 = x._2._2}) (prelude.List.zip t a t2 (prelude.List.zip t b t c))

let slide3 = \(t : Type) -> \(a : List t) ->
  let a1 = prelude.List.drop 1 t a
  let a2 = prelude.List.drop 2 t a
  in zip3 t a a1 a2

let tl = triplet lnt
let tn = triplet Natural
let ttn = triplet tn

let lt = prelude.Natural.lessThan
let solve0 = \(m : ttn) -> 
  let zzz = [ m._1._2, m._2._1, m._2._3, m._3._2 ]
  let zz = prelude.List.map Natural Bool (lt m._2._2) zzz
  in if prelude.Bool.and zz then (m._2._2 + 1) else 0

let solve1 = \(inp : tl) ->
  let z3 = slide3 tn (zip3 Natural inp._1 inp._2 inp._3)
  in prelude.Natural.sum (prelude.List.map ttn Natural solve0 z3)

let solve = \(inp : inpt) -> 
  let inf = 10000
  let addlr = \(x : lnt) -> [inf] # x # [inf]
  let l0 = addlr (prelude.List.map Natural Natural (\(x : Natural) -> inf) (hd lnt ([] : lnt) inp))
  let m = [l0] # (prelude.List.map lnt lnt addlr inp) # [l0]
  in prelude.Natural.sum (prelude.List.map tl Natural solve1 (slide3 lnt m))

let tex = assert : solve ex === 15

in solve ./input.dhall
