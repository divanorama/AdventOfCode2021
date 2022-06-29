let prelude = ../prelude.dhall

let ft = forall (t : Type) -> forall (x : List t) -> Natural

let f0 : ft= prelude.List.length

let step : ft -> ft = \(f : ft) -> \(t : Type) -> \(x : List t) -> prelude.Natural.sum (prelude.List.map (List (List t)) Natural (f (List t)) [[x], [x]])

let f = prelude.Natural.fold 20 ft step f0

in f Natural [1,2]
