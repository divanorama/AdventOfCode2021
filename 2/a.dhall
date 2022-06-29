let dir = < forward | up | down >
let step = {direction : dir, amount : Natural}
let lst = ./input.dhall
let fold = https://prelude.dhall-lang.org/v21.1.0/List/fold
let add = https://prelude.dhall-lang.org/v21.1.0/Integer/add
let multiply = https://prelude.dhall-lang.org/v21.1.0/Integer/multiply
let subtract = https://prelude.dhall-lang.org/v21.1.0/Integer/subtract
let fromNatural = https://prelude.dhall-lang.org/v21.1.0/Natural/toInteger
let coord = {x: Natural, y: Integer}
let move = \(dv : step) -> \(xy : coord) -> merge {
  forward = {x = xy.x + dv.amount, y = xy.y},
  down    = {x = xy.x            , y = add xy.y (fromNatural (dv.amount))},
  up      = {x = xy.x            , y = subtract (fromNatural dv.amount) xy.y},
} dv.direction
let res = fold step lst coord  move {x = 0, y = +0}
in multiply (fromNatural res.x) res.y
