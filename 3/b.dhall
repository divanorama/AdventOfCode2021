let map = https://prelude.dhall-lang.org/v21.1.0/List/map
let fold = https://prelude.dhall-lang.org/v21.1.0/List/fold
let reverse = https://prelude.dhall-lang.org/v21.1.0/List/reverse
let head = https://prelude.dhall-lang.org/v21.1.0/List/head
let filter = https://prelude.dhall-lang.org/v21.1.0/List/filter
let enumerate = https://prelude.dhall-lang.org/v21.1.0/Natural/enumerate
let equal = https://prelude.dhall-lang.org/v21.1.0/Natural/equal
let lt = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThan

let id = \(t : Type) -> \(x : t) -> x
let itype = \(t : Type) -> {index: Natural, value: t}
let at = \(t : Type) -> \(i : Natural) -> \(x : List t) -> head t ( map (itype t) t (\(q : itype t) -> q.value) (filter (itype t) (\(q : itype t) -> equal q.index i) (List/indexed t x))) : Optional t
let att = \(t : Type) -> \(def : t) -> \(i : Natural) -> \(x : List t) -> merge {Some = id t, None = def} (at t i x) : t
let optlen = \(t : Type) -> \(x : Optional (List t)) -> merge { Some = List/length t, None = 0 } x : Natural
let transpose = \(t : Type) -> \(def : t) -> \(x : List (List t)) -> let l = optlen t (at (List t) 0 x) in
  map Natural (List t) (\(pos : Natural) -> map (List t) t (att t def pos) x) (enumerate l)
let bacc = \(x : Natural) -> \(acc: Natural) -> acc * 2 + x
let fromBinary = \(l : List Natural) -> fold Natural (reverse Natural l) Natural bacc 0

let inpt : Type = List (List Natural)
let ex : inpt = ./01.dhall
let main : inpt = ./input.dhall

let solve = \(lst : inpt) ->
  let l = List/length Natural (merge {Some = id (List Natural), None = [] : List Natural} (List/head (List Natural) lst))
  let tacc = {zn: Natural, zz: inpt, on: Natural, oo: inpt}
  let f = \(pos : Natural) -> \(x : List Natural) -> \(acc: tacc) -> if equal (att Natural 0 pos x) 1 then
    {zn = acc.zn, zz = acc.zz, on = acc.on + 1, oo = [x] # acc.oo}
    else
    {zn = acc.zn + 1, zz = [x] # acc.zz, on = acc.on, oo= acc.oo}
  let acc0 : tacc = {zn = 0, zz = [] : inpt, on = 0, oo = [] : inpt}
  let picko = \(acc : tacc) -> if lt acc.on acc.zn then acc.zz else acc.oo
  let pickc = \(acc : tacc) -> if equal 0 acc.zn then acc.oo else if equal 0 acc.on then acc.zz else if lt acc.on acc.zn then acc.oo else acc.zz
  let stepo = \(pos : Natural) -> \(lst : inpt) -> picko (fold (List Natural) lst tacc (f pos) acc0)
  let stepc = \(pos : Natural) -> \(lst : inpt) -> pickc (fold (List Natural) lst tacc (f pos) acc0)
  let oxygen = att (List Natural) ([] : List Natural) 0 (fold Natural (reverse Natural (enumerate l)) inpt stepo lst)
  let co2 = att (List Natural) ([] : List Natural) 0 (fold Natural (reverse Natural (enumerate l)) inpt stepc lst)
  in (fromBinary oxygen) * (fromBinary co2)

let ext = assert : (solve ex) === 230

in solve main
