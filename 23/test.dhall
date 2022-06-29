let prelude = ../prelude.dhall

let ln = List Natural
let plus = \(a : Natural) -> \(b : Natural) -> a + b
let zipWith = \(f : Natural -> Natural -> Natural) -> \(a : ln) -> \(b : ln) ->
  let pt = {_1 : Natural, _2 : Natural}
  let l = prelude.List.zip Natural a Natural b
  in prelude.List.map pt Natural (\(x : pt) -> f x._1 x._2) l

let step = \(l : ln) -> zipWith plus ([0] # l) (l # [0])

in prelude.Natural.fold 400 ln step [1]
