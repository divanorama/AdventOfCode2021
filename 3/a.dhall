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

let lst = ./input.dhall
let l = List/length Natural (merge {Some = id (List Natural), None = [] : List Natural} (List/head (List Natural) lst))
let lstt = transpose Natural 666 lst
let tacc = {o: Natural, z: Natural}
let f = \(v : Natural) -> \(acc : tacc) -> if equal v 0 then {o = acc.o, z = acc.z + 1 } else {o = acc.o + 1, z = acc.z}
let most = \(x : List Natural) -> (\(oz : tacc) -> if lt oz.z oz.o then 1 else 0) (List/fold Natural x tacc f {o = 0, z = 0})
let least = \(x : List Natural) -> (\(oz : tacc) -> if lt oz.o oz.z then 1 else 0) (List/fold Natural x tacc f {o = 0, z = 0})
let gammab = map (List Natural) Natural most lstt
let gamma = fold Natural (reverse Natural gammab) Natural (\(x : Natural) -> \(acc : Natural) -> acc * 2 + x) 0
let epsilonb = map (List Natural) Natural least lstt
let epsilon = fold Natural (reverse Natural epsilonb) Natural (\(x : Natural) -> \(acc : Natural) -> acc * 2 + x) 0
in gamma * epsilon
