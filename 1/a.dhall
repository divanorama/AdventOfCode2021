let lst = ./input.dhall
let drop = https://prelude.dhall-lang.org/v21.1.0/List/drop
let zip = https://prelude.dhall-lang.org/v21.1.0/List/zip
let filter = https://prelude.dhall-lang.org/v21.1.0/List/filter
let length = https://prelude.dhall-lang.org/v21.1.0/List/length
let lt = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThan

let seconds = drop (1) Natural lst
let pairs = zip Natural lst Natural seconds
let pairsT = {_1 : Natural, _2 : Natural}
let cmp = \(lr : pairsT) -> lt lr._1 lr._2 
let res = filter pairsT  cmp pairs
in length pairsT res
