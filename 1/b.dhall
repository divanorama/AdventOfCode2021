let lst0 = ./input.dhall

let drop = https://prelude.dhall-lang.org/v21.1.0/List/drop
let zip = https://prelude.dhall-lang.org/v21.1.0/List/zip
let map = https://prelude.dhall-lang.org/v21.1.0/List/map
let filter = https://prelude.dhall-lang.org/v21.1.0/List/filter
let length = https://prelude.dhall-lang.org/v21.1.0/List/length
let lt = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThan
let sum = https://prelude.dhall-lang.org/v21.1.0/Natural/sum

let pairsT = {_1 : Natural, _2 : Natural}

let lst1 = drop (1) Natural lst0
let lst2 = drop (1) Natural lst1
let s2l = zip Natural lst0 Natural lst1
let pairSum = \(lr : pairsT) -> sum [lr._1, lr._2]
let s2 = map pairsT Natural pairSum s2l
let s3l = zip Natural s2 Natural lst2
let s3 = map pairsT Natural pairSum s3l
let lst = s3

let seconds = drop (1) Natural lst
let pairs = zip Natural lst Natural seconds
let cmp = \(lr : pairsT) -> lt lr._1 lr._2 
let res = filter pairsT  cmp pairs
in length pairsT res
