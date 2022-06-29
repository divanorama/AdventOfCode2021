let map = https://prelude.dhall-lang.org/v21.1.0/List/map
let concatMap = https://prelude.dhall-lang.org/v21.1.0/List/concatMap
let head = https://prelude.dhall-lang.org/v21.1.0/List/head
let filter = https://prelude.dhall-lang.org/v21.1.0/List/filter
let fold = https://prelude.dhall-lang.org/v21.1.0/List/fold
let equal = https://prelude.dhall-lang.org/v21.1.0/Natural/equal
let drop = https://prelude.dhall-lang.org/v21.1.0/List/drop
let length = https://prelude.dhall-lang.org/v21.1.0/List/length
let deopt = https://prelude.dhall-lang.org/v21.1.0/List/unpackOptionals
let enumerate = https://prelude.dhall-lang.org/v21.1.0/Natural/enumerate
let lte = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThanEqual
let min = https://prelude.dhall-lang.org/v21.1.0/Natural/min
let max = https://prelude.dhall-lang.org/v21.1.0/Natural/max
let not = https://prelude.dhall-lang.org/v21.1.0/Bool/not
let or = https://prelude.dhall-lang.org/v21.1.0/Bool/or
let and = https://prelude.dhall-lang.org/v21.1.0/Bool/and
let lt = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThan
let notEqual = \(a : Natural) -> \(b : Natural) -> not (equal a b)

let id = \(t : Type) -> \(x : t) -> x
let itype = \(t : Type) -> {index: Natural, value: t}
let at = \(t : Type) -> \(i : Natural) -> \(x : List t) -> head t ( map (itype t) t (\(q : itype t) -> q.value) (filter (itype t) (\(q : itype t) -> equal q.index i) (List/indexed t x))) : Optional t
let att = \(t : Type) -> \(def : t) -> \(i : Natural) -> \(x : List t) -> merge {Some = id t, None = def} (at t i x) : t
let has2 = \(t : Type) -> \(x: List t) -> merge {Some = \(x: t) -> True, None = False} (at t 1 x)
let pairt = \(t : Type) -> { a : t, b : t }
let pairs = \(t : Type) -> \(x : List t) ->
  let n = length t x 
  let pt = pairt t
  let g : Natural -> Natural -> List pt = \(j : Natural) -> \(i : Natural) -> merge {
      None = [] : List pt,
      Some = \(a : t) -> merge {
          None = [] : List pt,
          Some = \(b : t) -> [{a = a, b = b}]
        } (at t i x)
    } (at t j x)
  let f : Natural -> List pt = \(j : Natural) -> concatMap Natural pt (g j) (enumerate j)
  in concatMap Natural pt f (enumerate n)
let inn = \(t : Type) -> \(eq : t -> t -> Bool) -> \(v : t) -> \(x : List t) -> or (map t Bool (eq v) x)
let dedup = \(t : Type) -> \(eq : t -> t -> Bool) -> \(x : List t) -> fold t x (List t) (\(x : t) -> \(acc : List t) -> if inn t eq x acc then acc else [x] # acc) ([] : List t)

let dot = {x: Natural, y : Natural}
let segt = {a: dot, b : dot}
let inp = List segt
let ex : inp = ./01.dhall

let vert = {x : Natural, y1 : Natural, y2 : Natural}
let hort = {y : Natural, x1 : Natural, x2 : Natural}
let horver = < hor : hort | ver : vert >

let ashv = \(p : segt) -> if equal p.a.x p.b.x then [horver.ver {x = p.a.x, y1 = min p.b.y p.a.y, y2 = max p.b.y p.a.y}] else if equal p.a.y p.b.y then [horver.hor {y = p.a.y, x1 = min p.b.x p.a.x, x2 = max p.b.x p.a.x}] else [] : List horver


let rng = \(mn : Natural) -> \(mx : Natural) -> drop mn Natural (enumerate (mx + 1))

let fverhor = \(a : vert) -> \(b : hort) -> if or [lt a.x b.x1, lt b.x2 a.x, lt b.y a.y1, lt a.y2 b.y] then [] : List dot else [{x=a.x, y = b.y}]
let fverver = \(a : vert) -> \(b : vert) -> if notEqual a.x b.x then [] : List dot else map Natural dot (\(y : Natural) -> {x = a.x, y=y}) (rng (max a.y1 b.y1) (min a.y2 b.y2))
let fhorhor = \(a : hort) -> \(b : hort) -> if notEqual a.y b.y then [] : List dot else map Natural dot (\(x : Natural) -> {x = x, y = a.y}) (rng (max a.x1 b.x1) (min a.x2 b.x2))
let fhorver = \(a : hort) -> \(b : vert) -> fverhor b a

let inters = \(a : horver) -> \(b : horver) ->
  merge {
    hor = merge {
      ver = \(b : vert) -> \(a : hort) -> fverhor b a,
      hor = \(b : hort) -> \(a : hort) -> fhorhor b a,
    } b,
    ver = merge {
      ver = \(b : vert) -> \(a : vert) -> fverver b a,
      hor = \(b : hort) -> \(a : vert) -> fhorver b a,
    } b,
  } a
let intersp = \(ab : pairt horver) -> inters ab.a ab.b

let eqd = \(a : dot) -> \(b : dot) -> and [equal a.x b.x, equal a.y b.y]

let solve = \(lst : inp) ->
  let lst1 = concatMap (pairt dot) horver ashv lst
  let ps = pairs horver lst1
  let is = concatMap (pairt horver) dot intersp ps
  in length dot (dedup dot eqd is)

let tex = assert : solve ex === 5

in solve ./input.dhall
