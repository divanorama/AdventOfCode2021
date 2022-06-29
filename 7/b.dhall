let inpt = List Natural

let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let ex : inpt = ./01.dhall

let safeMin = \(x : List Natural) -> merge {None = 666, Some = \(x : Natural) -> x} (prelude.Natural.listMin x)
let safeHead = \(t : Type) -> \(def : t) -> \(x : List t) -> merge {Some = \(x : t) -> x, None = def} (prelude.List.head t x)

let div2 = \(x : Natural) ->
  safeHead Natural 666 (prelude.List.filter Natural (\(y : Natural) -> prelude.Natural.equal x (y * 2)) (prelude.Natural.enumerate (x + 1)))

let absd = \(a : Natural) -> \(b : Natural) -> if prelude.Natural.lessThan a b then prelude.Natural.subtract a b else prelude.Natural.subtract b a

let solve = \(lst : inpt) ->
  let n = prelude.List.length Natural lst
  let s = prelude.Natural.sum lst
  let mx = prelude.Natural.listMax lst
  let idxs = prelude.Natural.enumerate (s + 1)
  let almostMean = \(x : Natural) -> prelude.Bool.and [ prelude.Natural.lessThanEqual s (x * n + 2 * n), prelude.Natural.lessThanEqual (x * n) (s + 2 * n) ]
  let score = \(x : Natural) -> \(y : Natural) ->
    let d = absd x y
    in d * d + d
  let calc = \(x : Natural) -> prelude.Natural.sum (prelude.List.map Natural Natural (score x) lst)
  in (safeMin (prelude.List.map Natural Natural calc (prelude.List.filter Natural almostMean idxs)))

let tex = assert : solve ex === (168 * 2)

in solve ./input.dhall
