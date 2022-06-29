let inpt = List Natural

let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let ex : inpt = ./01.dhall

let solve = \(lst : inpt) ->
  let sorted = prelude.Natural.sort lst
  let n = prelude.List.length Natural lst
  let it = {index : Natural, value : Natural}
  let fv = \(kv : it) -> kv.value
  let almostn1 = \(x : Natural) -> prelude.Bool.or (prelude.List.map Natural Bool (prelude.Natural.equal (n)) [x, x + 1, x + 2])
  let goals = prelude.List.filter it (\(kv : it) -> almostn1 ((kv.index) * 2)) (prelude.List.indexed Natural sorted)
  let goalv = prelude.List.map it Natural fv goals
  let absd = \(a : Natural) -> \(b : Natural) -> if prelude.Natural.lessThan a b then prelude.Natural.subtract a b else prelude.Natural.subtract b a
  let score = \(x : Natural) -> prelude.Natural.sum (prelude.List.map Natural Natural (absd x) lst)
  in prelude.Natural.listMin (prelude.List.map Natural Natural score goalv)

let tex = assert : solve ex === Some 37

in solve ./input.dhall
