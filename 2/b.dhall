let dir = < forward | up | down >
let step = {direction : dir, amount : Natural}
let lst = ./input.dhall
let fold = https://prelude.dhall-lang.org/v21.1.0/List/fold
let reverse = https://prelude.dhall-lang.org/v21.1.0/List/reverse
let add = https://prelude.dhall-lang.org/v21.1.0/Integer/add
let multiply = https://prelude.dhall-lang.org/v21.1.0/Integer/multiply
let subtract = https://prelude.dhall-lang.org/v21.1.0/Integer/subtract
let fromNatural = https://prelude.dhall-lang.org/v21.1.0/Natural/toInteger
let coord = {x: Natural, y: Integer, aim: Integer}
let move = \(dv : step) -> \(xy : coord) -> merge {
  forward = {x = xy.x + dv.amount, y = add xy.y (multiply xy.aim (fromNatural dv.amount)), aim = xy.aim},
  down    = {x = xy.x            , y = xy.y                                              , aim = add xy.aim (fromNatural (dv.amount))},
  up      = {x = xy.x            , y = xy.y                                              , aim = subtract (fromNatural (dv.amount)) xy.aim},
} dv.direction
let res = fold step (reverse step lst) coord  move {x = 0, y = +0, aim = +0}
in multiply (fromNatural res.x) res.y
