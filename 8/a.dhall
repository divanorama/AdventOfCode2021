let enum = < a | b | c | d | e | f | g>
let a = enum.a
let b = enum.b
let c = enum.c
let d = enum.d
let e = enum.e
let f = enum.f
let g = enum.g

let ledt = List enum
let listt = List ledt
let lrt = {left : listt, right : listt }
let inpt = List lrt

let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let ex : inpt = ./02.dhall

let eq = prelude.Natural.equal

let solve = \(inp : inpt) -> prelude.List.length Natural (prelude.List.filter Natural (\(x : Natural) -> prelude.Bool.or [eq x 2, eq x 3, eq x 4, eq x 7]) (prelude.List.map ledt Natural (prelude.List.length enum) (prelude.List.concatMap lrt ledt (\(lr : lrt) -> lr.right) inp)))

let tex = assert : solve ex === 26

in solve ./input.dhall
