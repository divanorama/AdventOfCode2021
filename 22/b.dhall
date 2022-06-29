let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let rngt = \(t : Type) -> {mn : t, mx : t}
let itemt = \(t : Type) -> {on : Bool, x : rngt t, y : rngt t, z : rngt t}
let inpt = List (itemt Integer)

let ex : inpt = ./01.dhall
let ex0 : inpt = ./001.dhall
let ex2 : inpt = ./02.dhall
let ex3 : inpt = ./03.dhall
let input : inpt = ./input.dhall

let getmn = \(t : Type) -> \(x : rngt t) -> x.mn
let getmnmx = \(t : Type) -> \(x : rngt t) -> [x.mn,x.mx]
let getx = \(t : Type) -> \(q : itemt t) -> q.x
let gety = \(t : Type) -> \(q : itemt t) -> q.y
let getz = \(t : Type) -> \(q : itemt t) -> q.z
let is = \(t : Type) -> \(f : itemt t -> rngt t) -> \(l : List (itemt t)) -> prelude.List.map (itemt t) t (prelude.Function.compose (itemt t) (rngt t) t f (getmn t)) l
let iis = \(t : Type) -> \(f : itemt t -> rngt t) -> \(l : List (itemt t)) -> prelude.List.concatMap (itemt t) t (prelude.Function.compose (itemt t) (rngt t) (List t) f (getmnmx t)) l

let conv = \(l : List (itemt Integer)) ->
  let is = is Integer
  let xs = is (getx Integer) l
  let ys = is (gety Integer) l
  let zs = is (getz Integer) l
  let listmin = \(l : List Integer) ->
    let f = \(x : Integer) -> \(acc : Integer) -> if prelude.Integer.lessThan x acc then x else acc
    in prelude.List.fold Integer l Integer f (prelude.Optional.default Integer +0 (prelude.List.head Integer l))
  let x0 = listmin xs
  let y0 = listmin ys
  let z0 = listmin zs
  let shift = \(i0 : Integer) -> \(r : rngt Integer) -> {mn = prelude.Integer.abs (prelude.Integer.subtract i0 r.mn), mx = 1 + prelude.Integer.abs (prelude.Integer.subtract i0 r.mx)}
  let f = \(q : itemt Integer) -> {
    on = q.on,
    x = shift x0 q.x,
    y = shift y0 q.y,
    z = shift z0 q.z,
  }
  in prelude.List.map (itemt Integer) (itemt Natural) f l

let inpt = List (itemt Natural)
let ex : inpt = conv ex
let ex0 : inpt = conv ex0
let ex2 : inpt = conv ex2
let ex3 : inpt = conv ex3
let input : inpt = conv input

let uniqs = \(l0 : List Natural) ->
  let l0 = prelude.Natural.sort l0
  let pt = {_1 : Natural, _2 : Natural}
  let l : List pt = prelude.List.zip Natural l0 Natural (prelude.List.drop 1 Natural l0)
  in merge {
    Some = \(dh : pt) ->
      let f = \(x : pt) -> \(acc : List Natural) -> if prelude.Natural.lessThan x._1 x._2 then [x._1] # acc else acc
      in prelude.List.fold pt l (List Natural) f [dh._2],
    None = l0,
  } (prelude.List.last pt l)

let rngs = \(l : List Natural) ->
  let pt = {_1 : Natural, _2 : Natural}
  let l = prelude.List.zip Natural l Natural (prelude.List.drop 1 Natural l)
  let f = \(x : pt) -> {mn = x._1, mx = x._2}
  in prelude.List.map pt (rngt Natural) f l

let solve1 = \(l : List (itemt Natural)) -> 
  let rngt = rngt Natural
  let itemt = itemt Natural
  let li = List itemt
  let f = \(q : itemt) -> \(cur : li) ->
    let mk = \(z : rngt) -> {on = q.on, x=q.x, y=q.y, z = z}
    let st = { acc : li, rz : rngt }
    let g = \(ww : itemt) -> \(s : st) -> let w = ww.z in  {
      rz = {mn = s.rz.mn, mx = prelude.Natural.min s.rz.mx w.mn},
      acc = if prelude.Natural.lessThanEqual s.rz.mx w.mn then [ww] # s.acc else
            if prelude.Natural.lessThanEqual s.rz.mx s.rz.mn then [ww] # s.acc else
            if prelude.Natural.lessThanEqual w.mx s.rz.mn then [ww, mk s.rz] # s.acc else 
            if prelude.Natural.lessThanEqual s.rz.mx w.mx then [ww] # s.acc else
            [ww, mk {mn = w.mx, mx = s.rz.mx} ] # s.acc,
    }
    let s = prelude.List.fold itemt cur st g {acc = [] : li, rz = q.z } 
    in if prelude.Natural.lessThan s.rz.mn s.rz.mx then [mk s.rz] # s.acc else s.acc
  let l = prelude.List.fold itemt l li f ([] : li)
  let getw = \(q : itemt) -> if q.on then prelude.Natural.subtract q.z.mn q.z.mx else 0
  let l = prelude.List.map itemt Natural getw l
  let plus = \(a : Natural) -> \(b : Natural) -> a + b
  in prelude.List.fold Natural l Natural plus 0 

let solve = \(inp : inpt) ->
  let rngt = rngt Natural
  let itemt = itemt Natural
  let iis = iis Natural
  let xs = rngs (uniqs (iis (getx Natural) inp))
  let ys = rngs (uniqs (iis (gety Natural) inp))
  let zs = rngs (uniqs (iis (getz Natural) inp))
  let inters = \(a : rngt) -> \(b : rngt) -> {mn = prelude.Natural.max a.mn b.mn, mx = prelude.Natural.min a.mx b.mx}
  let okr = \(a : rngt) -> prelude.Natural.lessThan a.mn a.mx
  let getw = \(a : rngt) -> prelude.Natural.subtract a.mn a.mx
  let stepx = \(x : rngt) -> \(acc : Natural) ->
    let wx = getw x
    let f = \(q : itemt) -> {on = q.on, x = inters x q.x, y = q.y, z = q.z}
    let inp = prelude.List.map itemt itemt f inp
    let f = \(q : itemt) -> okr q.x
    let inp = prelude.List.filter itemt f inp
    let stepy = \(y : rngt) -> \(acc : Natural) ->
      let wyx = wx * getw y
      let f = \(q : itemt) -> {on = q.on, x = q.x, y = inters y q.y, z = q.z}
      let inp = prelude.List.map itemt itemt f inp
      let f = \(q : itemt) -> okr q.y
      let inp = prelude.List.filter itemt f inp
      in acc + wyx * (solve1 inp)
    in prelude.List.fold rngt ys Natural stepy acc
  in prelude.List.fold rngt xs Natural stepx 0

in solve input
