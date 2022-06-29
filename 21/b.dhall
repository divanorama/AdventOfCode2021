let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a
-- ARRAY
let arrOps = \(repr : Type) -> \(v : Type) -> { 
  empty : repr, 
  modify : repr -> Natural -> (Optional v -> Optional v) -> repr, 
  get : repr -> Natural -> Optional v,
  asList : repr -> List (Optional v)
}
let arrReprt = { repr : Type, size : Natural }

let dblRepr = \(repr : Type) -> {children : List repr}
let dblArr = \(fprev : Type -> arrReprt) -> \(v : Type) -> let prev = fprev v in { repr = dblRepr prev.repr, size = prev.size * 2 } : arrReprt
let dblOps = \(v : Type) -> \(prev : arrReprt) -> \(prevOps : arrOps prev.repr v) ->
  let repr = dblRepr prev.repr
  in {
    empty = {children = prelude.List.map Natural prev.repr (\(_ : Natural) -> prevOps.empty) (prelude.Natural.enumerate 10)},
    get = \(r : repr) -> \(i : Natural) ->
      let nch = prelude.Optional.default Natural 0 (prelude.List.head Natural (prelude.List.filter Natural (\(x : Natural) -> prelude.Natural.lessThan i ((x + 1) * prev.size)) (prelude.Natural.enumerate 10)))
      in merge { None = None v, Some = \(c : prev.repr) -> prevOps.get c (prelude.Natural.subtract (nch * prev.size) i)} (prelude.List.head prev.repr (prelude.List.drop nch prev.repr r.children)),
    modify = \(r : repr) -> \(i : Natural) -> \(f : Optional v -> Optional v) -> 
      let nch = prelude.Optional.default Natural 0 (prelude.List.head Natural (prelude.List.filter Natural (\(x : Natural) -> prelude.Natural.lessThan i ((x + 1) * prev.size)) (prelude.Natural.enumerate 10)))
      in merge { None = r, Some = \(c : prev.repr) -> {children = (prelude.List.take nch prev.repr r.children) # [prevOps.modify c (prelude.Natural.subtract (nch * prev.size) i) f] # (prelude.List.drop (nch + 1) prev.repr r.children)}} (prelude.List.head prev.repr (prelude.List.drop nch prev.repr r.children)),
    asList = \(r : repr) -> prelude.List.concatMap prev.repr (Optional v) prevOps.asList r.children,
  } : arrOps repr v

let arr1 = \(v : Type) -> { repr = Optional v, size = 1 } : arrReprt
let arr1ops = \(v : Type) -> 
  let k = arr1 v
  let repr : Type = k.repr
  in {
    empty = None v, 
    modify = \(r : repr) -> \(_i : Natural) -> \(f : Optional v -> Optional v) -> f r, 
    get = \(r : repr) -> \(_i : Natural) -> r,
    asList = \(r : repr) -> [r]
  } : arrOps repr v
let farr = \(v : Type) -> \(t : Type) -> forall (r : arrReprt) -> forall (ops : arrOps (r.repr) v) -> t
let getarr = \(v : Type) -> \(n : Natural) -> \(t : Type) -> \(f : farr v t) ->
  let t0 : arrReprt = arr1 v
  let o0 : arrOps t0.repr v = arr1ops v
  let st = { sz : Natural, f : farr v t }
  let step = \(s : st) -> if prelude.Natural.lessThanEqual n s.sz then s else
    { sz = s.sz * 10, f = \(r : arrReprt) -> \(ops : arrOps r.repr v) ->
      let repr1 : arrReprt = { repr = dblRepr r.repr, size = r.size * 10 }
      let ops1 : arrOps repr1.repr v = dblOps v r ops
      in s.f repr1 ops1
    }
  in (prelude.Natural.fold 10 st step { sz = 1, f = f }).f t0 o0
--

let inpt = {p1 : Natural, p2 : Natural}

let ex : inpt = ./01.dhall

let wpoint = 21

let wrap11 = \(x : Natural) -> if prelude.Natural.lessThan x 11 then x else (1 + (prelude.Natural.subtract 11 x))
let wrap10 = \(x : Natural) -> if prelude.Natural.lessThan x 10 then x else (prelude.Natural.subtract 10 x)
let plus = \(a : Natural) -> \(b : Natural) -> a + b

let capw = prelude.Natural.min wpoint

let solve = \(inp : inpt) ->
  let pt = { points : Natural, pos : Natural }
  let gt = { p1 : pt, p2 : pt, turn1 : Bool }
  let et = {from : gt, to : gt}
  let flipg = \(g : gt) -> {p1 = g.p2, p2 = g.p1, turn1 = prelude.Bool.not g.turn1}
  let npoint = wpoint + 1
  let npos = 10
  let npl = npoint * npos
  let ng = npl * npl * 2
  let codep = \(p : pt) -> p.points * npos + (prelude.Natural.subtract 1 p.pos)
  let code = \(g : gt) -> (npl * (codep g.p1) + (codep g.p2)) * 2 + (if g.turn1 then 1 else 0)
  let won = \(p : pt) -> prelude.Natural.lessThanEqual wpoint p.points
  let isfinal = \(g : gt) -> prelude.Bool.or [won g.p1, won g.p2]
  let dpt = { w1 : Natural, w2 : Natural }
  let dpsum = \(a : dpt) -> \(b : dpt) -> {w1 = a.w1 + b.w1, w2 = a.w2 + b.w2 }
  let score = \(g : gt) -> if won g.p2 then {w1 = 1, w2 = 0} else {w1 = 0, w2 = 1}
  let rolls = prelude.Natural.fold 3 (List Natural) (
      prelude.List.concatMap Natural Natural (\(x : Natural) -> prelude.List.map Natural Natural (prelude.Function.compose Natural Natural Natural (plus x) wrap10) [1,2,3]) 
    ) [0]
  let pcells = prelude.List.fold Natural (prelude.Natural.enumerate npoint) (List pt) (\(points : Natural) -> \(acc : List pt) -> 
      prelude.List.fold Natural (prelude.Natural.enumerate npos) (List pt) (\(x : Natural) -> \(acc : List pt) -> 
        let pos = x + 1
        in [{points = points, pos = pos}] # acc
      ) acc
    ) ([] : List pt)
  let gcells = prelude.List.fold pt pcells (List gt) (\(p1 : pt) ->\(acc : List gt) -> 
      prelude.List.fold pt pcells (List gt) (\(p2 : pt) -> \(acc : List gt) -> 
        [{p1 = p1, p2 = p2, turn1 = True}, {p1 = p1, p2 = p2, turn1 = False}] # acc
      ) acc
    ) ([] : List gt)
  let gcells = prelude.List.filter gt (\(g : gt) -> prelude.Bool.not (prelude.Bool.and [won g.p1, won g.p2])) gcells
  let flipe = \(e : et) -> {from = flipg e.from, to = flipg e.to}
  let es = prelude.List.concatMap gt et (\(g : gt) -> 
     let f = \(g : gt) ->
      let go = \(d : Natural) ->
        let p = g.p1
        let pos1 = wrap11 (p.pos + d)
        in {p1 = {points = capw (pos1 + p.points), pos = pos1}, p2 = g.p2, turn1 = False}
      let gs = prelude.List.map Natural gt go rolls
      in prelude.List.map gt et (\(gg : gt) -> {from = g, to = gg}) gs
     in if g.turn1 then f g else prelude.List.map et et flipe (f (flipg g))
    ) (prelude.List.filter gt (prelude.Function.compose gt Bool Bool isfinal prelude.Bool.not) gcells)
  in getarr dpt ng Natural (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr dpt) ->
--  in getarr dpt ng (List (Optional dpt)) (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr dpt) ->
--  in getarr dpt ng (List et) (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr dpt) ->
--  in getarr dpt ng (List Bool) (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr dpt) ->
    let dp0 = prelude.List.fold gt (prelude.List.filter gt isfinal gcells) arrt.repr (\(g : gt) -> \(a : arrt.repr) -> arrops.modify a (code g) (\(_ : Optional dpt) -> Some (score g))) arrops.empty
    let step = \(e : et) -> \(dp : arrt.repr) -> 
      merge {
        None = dp,
        Some = \(val : dpt) ->
          arrops.modify dp (code e.from) (\(curr : Optional dpt) -> Some (dpsum val (prelude.Optional.default dpt {w1=0,w2=0} curr)))
      } (arrops.get dp (code e.to))
    let dp = prelude.List.fold et es arrt.repr step dp0
    let start = {p1 = {points = 0, pos = inp.p1}, p2 = {points = 0, pos = inp.p2}, turn1 = True}
    let res = prelude.Optional.default dpt {w1=0,w2=0} (arrops.get dp (code start))
--    in prelude.List.map et Bool (\(e : et) -> prelude.Natural.lessThan (code e.from) (code e.to)) es
--    in rolls
--    in prelude.List.filter et (\(e : et) -> prelude.Bool.not (prelude.Optional.null dpt (arrops.get dp0 (code e.to)))) es
--    in prelude.List.filter et (\(e : et) -> isfinal e.to) es
--    in prelude.List.filter gt isfinal gcells
--    in arrops.asList dp
    in prelude.Natural.max res.w1 res.w2
  )

in solve ex
