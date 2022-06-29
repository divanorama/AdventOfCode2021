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
let set = \(t : Type) -> \(x : t) -> \(curr : Optional t) -> Some x
--

let enum = < D | R | E >
let D = enum.D
let R = enum.R
let E = enum.E
let e2i = \(e : enum) -> merge {
  D = 0,
  R = 1,
  E = 2,
} e
let eqe = \(a : enum) -> \(b : enum) -> prelude.Natural.equal (e2i a) (e2i b)

let le = List enum
let inpt = List le

let ex : inpt = ./01.dhall

let pt = \(a : Type) -> \(b : Type) -> {_1 : a, _2 : b}
let ijt = {i : Natural, j : Natural}
let ijxt = \(t : Type) -> {ij : ijt, x : t}
let addij = \(t : Type) -> \(n : Natural) -> \(m : Natural) -> \(l : List (List t)) ->
  let li = prelude.List.zip Natural (prelude.Natural.enumerate n) (List t) l
  let f = \(q : pt Natural (List t)) ->
    let lj = prelude.List.zip Natural (prelude.Natural.enumerate m) t q._2
    let f = \(w : pt Natural t) -> {ij = {i = q._1, j = w._1}, x = w._2}
    in prelude.List.map (pt Natural t) (ijxt t) f lj
  let li = prelude.List.map (pt Natural (List t)) (List (ijxt t)) f li
  in li

let wrap = \(n : Natural) -> \(i : Natural) -> if prelude.Natural.lessThan i n then i else prelude.Natural.subtract n i 

let solve = \(inp : inpt) ->
  let n = prelude.List.length le inp
  let m = prelude.List.length enum (prelude.Optional.default le ([] : le) (prelude.List.head le inp))
  let codeij = \(i : Natural) -> \(j : Natural) -> i * m + j
  let code = \(x : ijt) -> codeij x.i x.j
  let cells = 
    let addj = \(i : Natural) -> prelude.List.map Natural ijt (\(j : Natural) -> {i = i, j = j}) (prelude.Natural.enumerate m)
    in prelude.List.concatMap Natural ijt addj (prelude.Natural.enumerate n)
  let mover = \(ij : ijt) -> { i = ij.i, j = wrap m (ij.j + 1)}
  let moved = \(ij : ijt) -> { i = wrap n (ij.i + 1), j = ij.j}
  let movel = \(ij : ijt) -> { i = ij.i, j = wrap m (ij.j + (prelude.Natural.subtract 1 m))}
  let moveu = \(ij : ijt) -> { i = wrap n (ij.i + (prelude.Natural.subtract 1 n)), j = ij.j}
  in getarr enum (n * m) (Optional Natural) ( \(arr : arrReprt) -> \(ops : arrOps arr.repr enum) ->
    let ijxt = ijxt enum
    let inp = addij enum n m inp
    let inp = prelude.List.concat ijxt inp
    let addm = \(q : ijxt) -> \(a : arr.repr) -> ops.modify a (code q.ij) (set enum q.x)
    let map0 = prelude.List.fold ijxt inp arr.repr addm ops.empty
    let st = {map : arr.repr, steps : Natural, res : Optional Natural, active : List ijt}
    let step = \(s : st) -> if prelude.Bool.not (prelude.Optional.null Natural s.res) then s else
      let map = s.map

      let canr = \(map : arr.repr) ->
        let getm = \(ij : ijt) -> prelude.Optional.default enum E (ops.get map (code ij))
        in \(ij : ijt) -> prelude.Bool.and [ eqe R (getm ij), eqe E (getm (mover ij)) ]
      let rs = prelude.List.filter ijt (canr map) s.active
      let rmst = { rs : List ijt, map : arr.repr }
      let rm = \(ij : ijt) -> \(aa : rmst) -> if canr aa.map ij then { map = ops.modify aa.map (code ij) (set enum E), rs = [ij] # aa.rs } else aa
      let rsmap = prelude.List.fold ijt rs rmst rm {map = map, rs = [] : List ijt}
      let rs = rsmap.rs
      let map = rsmap.map
      let addr = \(ij : ijt) -> \(a : arr.repr) -> ops.modify a (code (mover ij)) (set enum R)
      let map = prelude.List.fold ijt rs arr.repr addr map
      
      let fr = \(ij : ijt) -> moveu ij
      let ract = prelude.List.map ijt ijt fr rs

      let cand = \(map : arr.repr) ->
        let getm = \(ij : ijt) -> prelude.Optional.default enum E (ops.get map (code ij))
        in \(ij : ijt) -> prelude.Bool.and [ eqe D (getm ij), eqe E (getm (moved ij)) ]
      let ds = prelude.List.filter ijt (cand map) (s.active # ract)
      let rmst = { ds : List ijt, map : arr.repr }
      let rm = \(ij : ijt) -> \(aa : rmst) -> if cand aa.map ij then { map = ops.modify aa.map (code ij) (set enum E), ds = [ij] # aa.ds } else aa
      let dsmap = prelude.List.fold ijt ds rmst rm {map = map, ds = [] : List ijt}
      let ds = dsmap.ds
      let map = dsmap.map
      let addd = \(ij : ijt) -> \(a : arr.repr) -> ops.modify a (code (moved ij)) (set enum D)
      let map = prelude.List.fold ijt ds arr.repr addd map

      let fd = \(ij : ijt) -> [movel ij, moveu ij, moved ij]
      let dact = prelude.List.concatMap ijt ijt fd ds
      let ract = (prelude.List.concatMap ijt ijt (\(ij : ijt) -> [mover ij, movel ij]) rs) # ract

      in {map = map, steps = s.steps + 1, res = if prelude.List.null ijt (rs # ds) then Some (s.steps + 1) else s.res, active = ract # dact }
    in (prelude.Natural.fold 10000 st step {map = map0, steps = 0, res = None Natural, active = cells} ).res
  )

--in solve ex
in solve ./input.dhall
