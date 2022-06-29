let map = https://prelude.dhall-lang.org/v21.1.0/List/map
let concatMap = https://prelude.dhall-lang.org/v21.1.0/List/concatMap
let head = https://prelude.dhall-lang.org/v21.1.0/List/head
let filter = https://prelude.dhall-lang.org/v21.1.0/List/filter
let fold = https://prelude.dhall-lang.org/v21.1.0/List/fold
let equal = https://prelude.dhall-lang.org/v21.1.0/Natural/equal
let equali = https://prelude.dhall-lang.org/v21.1.0/Integer/equal
let drop = https://prelude.dhall-lang.org/v21.1.0/List/drop
let length = https://prelude.dhall-lang.org/v21.1.0/List/length
let deopt = https://prelude.dhall-lang.org/v21.1.0/List/unpackOptionals
let enumerate = https://prelude.dhall-lang.org/v21.1.0/Natural/enumerate
let lte = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThanEqual
let min = https://prelude.dhall-lang.org/v21.1.0/Natural/min
let max = https://prelude.dhall-lang.org/v21.1.0/Natural/max
let odd = https://prelude.dhall-lang.org/v21.1.0/Natural/odd
let not = https://prelude.dhall-lang.org/v21.1.0/Bool/not
let or = https://prelude.dhall-lang.org/v21.1.0/Bool/or
let and = https://prelude.dhall-lang.org/v21.1.0/Bool/and
let subtract = https://prelude.dhall-lang.org/v21.1.0/Natural/subtract
let toInteger = https://prelude.dhall-lang.org/v21.1.0/Natural/toInteger
let subtracti = https://prelude.dhall-lang.org/v21.1.0/Integer/subtract
let negate = https://prelude.dhall-lang.org/v21.1.0/Integer/negate
let addi = https://prelude.dhall-lang.org/v21.1.0/Integer/add
let abs = https://prelude.dhall-lang.org/v21.1.0/Integer/abs
let lt = https://prelude.dhall-lang.org/v21.1.0/Natural/lessThan
let lti = https://prelude.dhall-lang.org/v21.1.0/Integer/lessThan
let notEqual = \(a : Natural) -> \(b : Natural) -> not (equal a b)
let notEquali = \(a : Integer) -> \(b : Integer) -> not (equali a b)

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
let spt = {mn : Natural, mx : Natural}
let bbt = {x : spt, y : spt}

let vert = {x : Natural, bb : bbt}
let hort = {y : Natural, bb : bbt}
let diast = {s : Natural, bb : bbt}
let diadt = {d : Integer, bb : bbt}
let horver = < hor : hort | ver : vert | dias : diast | diad : diadt >

let mkbb = \(a : dot) -> \(b : dot) -> {x = {mn = min a.x b.x, mx = max a.x b.x}, y = { mn = min a.y b.y, mx = max a.y b.y}}

let ashv = \(p : segt) -> let bb = mkbb p.a p.b in
  if equal p.a.x p.b.x then [horver.ver {x = p.a.x, bb = bb}] 
  else if equal p.a.y p.b.y then [horver.hor {y = p.a.y, bb = bb}] 
  else if equal (p.a.x + p.a.y) (p.b.x + p.b.y) then [horver.dias {s = p.a.x + p.a.y, bb = bb}] 
  else if equali (subtracti (toInteger p.a.x) (toInteger p.a.y)) (subtracti (toInteger p.b.x) (toInteger p.b.y)) then [horver.diad {d = subtracti (toInteger p.b.x) (toInteger p.b.y), bb = bb}]
  else [] : List horver


let disjsp = \(a : spt) -> \(b : spt) -> or [lt a.mx b.mn, lt b.mx a.mn]
let disjbb = \(a : bbt) -> \(b : bbt) -> or [disjsp a.x b.x, disjsp a.y b.y]

let rng = \(mn : Natural) -> \(mx : Natural) -> drop mn Natural (enumerate (mx + 1))
let rngx = \(a : bbt) -> \(b : bbt) -> rng (max a.x.mn b.x.mn) (min a.x.mx b.x.mx)
let rngy = \(a : bbt) -> \(b : bbt) -> rng (max a.y.mn b.y.mn) (min a.y.mx b.y.mx)

let scale2d = \(d : dot) -> {x = d.x * 2, y = d.y * 2}

let fverhor = \(a : vert) -> \(b : hort) -> if disjbb a.bb b.bb then [] : List dot else [scale2d {x=a.x, y = b.y}]

let fverver = \(a : vert) -> \(b : vert) -> if disjbb a.bb b.bb then [] : List dot else map Natural dot (\(y : Natural) -> scale2d {x = a.x, y = y}) (rngy a.bb b.bb)
let fhorhor = \(a : hort) -> \(b : hort) -> if disjbb a.bb b.bb then [] : List dot else map Natural dot (\(x : Natural) -> scale2d {x = x, y = a.y}) (rngx a.bb b.bb)
let fdiasdias = \(a : diast) -> \(b : diast) -> if or [disjbb a.bb b.bb, notEqual a.s b.s] then [] : List dot else map Natural dot (\(x : Natural) -> scale2d {x = x, y = subtract x a.s}) (rngx a.bb b.bb)
let fdiaddiad = \(a : diadt) -> \(b : diadt) -> if or [disjbb a.bb b.bb, notEquali a.d b.d] then [] : List dot else map Natural dot (\(x : Natural) -> scale2d {x = x, y = abs (addi (toInteger x) a.d)}) (rngx a.bb b.bb)

let oddi = \(x : Integer) -> odd (abs x)

let dflt = \(t : Type) -> \(x : t) -> \(ox : Optional t) -> merge { Some = \(v : t) -> v, None = x } ox


--let div2 = \(x : Natural) ->
--  let it = {index : Natural, value : Natural}
--  let lst : List it = filter it (\(iv : it) -> equal (iv.value * 2) x) (List/indexed Natural (enumerate (x + 1)))
--  let lstv : List Natural = map it Natural (\(iv : it) -> iv.value) lst 
--  in dflt Natural 777 (head Natural lstv)

let inbb = \(d : dot) -> \(bb : bbt) -> not (disjbb bb (mkbb d d))
let ninbb = \(d : dot) -> \(bb : bbt) -> disjbb bb (mkbb d d)

let scale2sp = \(a : spt) -> {mn = a.mn * 2, mx = a.mx * 2}
let scale2bb = \(a : bbt) -> {x = scale2sp a.x, y = scale2sp a.y}

let fdiasdiad = \(a : diast) -> \(b : diadt) -> if or [disjbb a.bb b.bb, oddi (addi (toInteger a.s) b.d)] then [] : List dot else 
  let yy = (abs (addi b.d (toInteger a.s))) --div2
  let xx = (abs (subtracti b.d (toInteger a.s))) --div2
  let d = {x = xx, y = yy}
  in if and [inbb d (scale2bb a.bb), inbb d (scale2bb b.bb)] then [d] else [] : List dot

let fdiasver = \(a : diast) -> \(b : vert) -> if disjbb a.bb b.bb then [] : List dot else
  let yi = subtracti (toInteger b.x) (toInteger a.s)
  let d = {x = b.x, y = abs yi}
  in if or [lti yi (toInteger 0), ninbb d a.bb, ninbb d b.bb] then [] : List dot else [scale2d d]
let fdiashor = \(a : diast) -> \(b : hort) -> if disjbb a.bb b.bb then [] : List dot else
  let xi = subtracti (toInteger b.y) (toInteger a.s)
  let d = {x = abs xi, y = b.y}
  in if or [lti xi (toInteger 0), ninbb d a.bb, ninbb d b.bb] then [] : List dot else [scale2d d]
let fdiadver = \(a : diadt) -> \(b : vert) -> if disjbb a.bb b.bb then [] : List dot else
  let yi = addi (toInteger b.x) a.d
  let d = {x = b.x, y = abs yi}
  in if or [lti yi (toInteger 0), ninbb d a.bb, ninbb d b.bb] then [] : List dot else [scale2d d]
let fdiadhor = \(a : diadt) -> \(b : hort) -> if disjbb a.bb b.bb then [] : List dot else
  let xi = addi (toInteger b.y) (negate a.d)
  let d = {x = abs xi, y = b.y}
  in if or [lti xi (toInteger 0), ninbb d a.bb, ninbb d b.bb] then [] : List dot else [scale2d d]

let fhordias = \(a : hort) -> \(b : diast) -> fdiashor b a
let fhordiad = \(a : hort) -> \(b : diadt) -> fdiadhor b a
let fverdias = \(a : vert) -> \(b : diast) -> fdiasver b a
let fverdiad = \(a : vert) -> \(b : diadt) -> fdiadver b a
let fdiaddias = \(a : diadt) -> \(b : diast) -> fdiasdiad b a
let fhorver = \(a : hort) -> \(b : vert) -> fverhor b a
let fverdias = \(a : vert) -> \(b : diast) -> fdiasver b a

let inters = \(a : horver) -> \(b : horver) ->
  merge {
    hor = merge {
      ver = \(b : vert) -> \(a : hort) -> fverhor b a,
      hor = \(b : hort) -> \(a : hort) -> fhorhor b a,
      dias = \(b  : diast) -> \(a : hort) -> fdiashor b a,
      diad = \(b  : diadt) -> \(a : hort) -> fdiadhor b a,
    } b,
    ver = merge {
      ver = \(b : vert) -> \(a : vert) -> fverver b a,
      hor = \(b : hort) -> \(a : vert) -> fhorver b a,
      dias = \(b  : diast) -> \(a : vert) -> fdiasver b a,
      diad = \(b  : diadt) -> \(a : vert) -> fdiadver b a,
    } b,
    dias = merge {
      ver = \(b : vert) -> \(a : diast) -> fverdias b a,
      hor = \(b : hort) -> \(a : diast) -> fhordias b a,
      dias = \(b  : diast) -> \(a : diast) -> fdiasdias b a,
      diad = \(b  : diadt) -> \(a : diast) -> fdiaddias b a,
    } b,
    diad = merge {
      ver = \(b : vert) -> \(a : diadt) -> fverdiad b a,
      hor = \(b : hort) -> \(a : diadt) -> fhordiad b a,
      dias = \(b  : diast) -> \(a : diadt) -> fdiasdiad b a,
      diad = \(b  : diadt) -> \(a : diadt) -> fdiaddiad b a,
    } b,
  } a
let intersp = \(ab : pairt horver) -> inters ab.a ab.b

let eqd = \(a : dot) -> \(b : dot) -> and [equal a.x b.x, equal a.y b.y]

let solve = \(lst : inp) ->
  let lst1 = concatMap (pairt dot) horver ashv lst
  let ps = pairs horver lst1
  let is = concatMap (pairt horver) dot intersp ps
--  in dedup dot eqd is
  in length dot (dedup dot eqd is)

let tex = assert : solve ex === 12

in solve ./input.dhall
