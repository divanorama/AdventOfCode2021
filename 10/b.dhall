let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let br = < so | sc | co | cc | ro | rc | ao | ac >
let lt = List br
let inpt = List lt

let ex : inpt = ./01.dhall

let eithert = \(a : Type) -> \(b : Type) -> < left : a | right : b >
let getl = \(a : Type) -> \(b : Type) -> \(def : a) -> \(x : eithert a b) -> merge { left = \(y : a) -> y, right = \(x : b) -> def } x
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

let score2 = \(c : br) -> merge
  { so = 2, co = 3, ro = 1, ao = 4,
  sc = 666, cc = 666, rc = 666, ac = 666 }
  c

let class = \(c : br) -> merge 
  {so = 1, co = 2, ro = 3, ao = 4,
  sc = 1, cc = 2, rc = 3, ac = 4}
  c

let pair = \(op : br) -> \(cl : br) -> prelude.Natural.equal (class op) (class cl)

let getmid = \(lst : List Natural) ->
  let n = prelude.List.length Natural lst
  let ixt = {index : Natural, value : Natural}
  let zz = prelude.List.filter ixt (\(x : ixt) -> prelude.Natural.equal (n) (x.index * 2 + 1)) (prelude.List.indexed Natural lst)
  in merge {None = 666, Some = \(x : ixt) -> x.value} (prelude.List.head ixt zz)

let solve3 = \(lst : List Natural) ->
  let x = prelude.Natural.sort (prelude.List.filter Natural (\(x : Natural) -> prelude.Natural.lessThan 0 x) lst)
  in getmid x

let solve2 = \(lst : List br) ->
  let f = \(acc : Natural) -> \(c : br) -> acc * 5 + score2 c
  in prelude.List.foldLeft br lst Natural f 0

let solve1 = \(lst : lt) -> 
  let f = \(x : stt) -> \(c : br) -> merge {
      right = \(z : Natural) -> x,
      left = \(st : List br) -> if op c then stt.left ([c] # st) else merge {
          None = stt.right (score c),
          Some = \(oo : br) -> if pair oo c then stt.left (prelude.List.drop 1 br st) else stt.right (score c)
        } (prelude.List.head br st)
    } x
  let s0 : stt = stt.left ([] : List br)
  in solve2 (getl (List br) Natural ([] : List br) ( prelude.List.foldLeft br lst stt f s0 ))

let solve = \(lst : inpt) -> solve3 (prelude.List.map lt Natural solve1 lst)

--in getmid [1, 2, 3, 4]
let tex = assert : solve ex === 288957

--in solve ex
in solve ./input.dhall
