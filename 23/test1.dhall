let prelude = ../prelude.dhall

let t = List Natural
let a : t = prelude.Natural.enumerate 100000
let a = prelude.Natural.fold 100000 t (prelude.Function.identity t) a
in prelude.List.length Natural a
