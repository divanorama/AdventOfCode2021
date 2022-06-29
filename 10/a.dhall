let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let br = < so | sc | co | cc | ro | rc | ao | ac >
let lt = List br
let inpt = List lt

let ex : inpt = ./01.dhall

let eithert = \(a : Type) -> \(b : Type) -> < left : a | right : b >
let getr = \(a : Type) -> \(b : Type) -> \(def : b) -> \(x : eithert a b) -> merge { left = \(y : a) -> def, right = \(x : b) -> x } x

let stt = eithert (List br) Natural

let op = \(c : br) -> merge 
  {so = True, co = True, ro = True, ao = True,
  sc = False, cc = False, rc = False, ac = False}
  c

let score = \(c : br) -> merge
  { so = 666, co = 666, ro = 666, ao = 666,
  sc = 57, cc = 1197, rc = 3, ac = 25137 }
  c

let class = \(c : br) -> merge 
  {so = 1, co = 2, ro = 3, ao = 4,
  sc = 1, cc = 2, rc = 3, ac = 4}
  c

let pair = \(op : br) -> \(cl : br) -> prelude.Natural.equal (class op) (class cl)

let solve1 = \(lst : lt) -> 
  let f = \(x : stt) -> \(c : br) -> merge {
      right = \(z : Natural) -> x,
      left = \(st : List br) -> if op c then stt.left ([c] # st) else merge {
          None = stt.right (score c),
          Some = \(oo : br) -> if pair oo c then stt.left (prelude.List.drop 1 br st) else stt.right (score c)
        } (prelude.List.head br st)
    } x
  let s0 : stt = stt.left ([] : List br)
  in getr (List br) Natural 0 ( prelude.List.foldLeft br lst stt f s0 )

let solve = \(lst : inpt) -> prelude.Natural.sum (prelude.List.map lt Natural solve1 lst)

let tex = assert : solve ex === 26397

in solve ./input.dhall
