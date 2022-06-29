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
--
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

let inpt = List (List Natural)

let ex : inpt = ./01.dhall

let inc = \(x : Natural) -> \(curr : Optional Natural) -> Some (x + (prelude.Optional.default Natural 0 curr))
let const = \(a : Type) -> \(b : Type) -> \(x : b) -> \(_ : a) -> x

let pairt = \(a : Type) -> \(b : Type) -> {_1 : a, _2 : b}

let a2det = \(t : Type) -> { i : Natural, j : Natural, x : t }

let a2d = \(n : Natural) -> \(m : Natural) -> \(t : Type) -> \(x : List (List t)) ->
  let withi = prelude.List.zip Natural (prelude.Natural.enumerate n) (List t) x
  let f = \(irow : pairt Natural (List t)) ->
    let withj = prelude.List.zip Natural (prelude.Natural.enumerate m) t irow._2
    let g = \(z : pairt Natural t) -> { i = irow._1, j = z._1, x = z._2 }
    in prelude.List.map (pairt Natural t) (a2det t) g withj
  in prelude.List.concatMap (pairt Natural (List t)) (a2det t) f withi

let rep5 = \(t : Type) -> \(f : t -> t) -> \(x : List t) ->
  let x1 = prelude.List.map t t f x
  let x2 = prelude.List.map t t f x1
  let x3 = prelude.List.map t t f x2
  let x4 = prelude.List.map t t f x3
  in x # x1 # x2 # x3 # x4

let incwrap = \(x : Natural) ->
  let y = x + 1
  in if prelude.Natural.lessThan y 10 then y else 1

let rep5i = rep5 Natural incwrap
let rep5ii = \(x : List (List Natural)) -> rep5 (List Natural) (prelude.List.map Natural Natural incwrap) (prelude.List.map (List Natural) (List Natural) rep5i x)

let solve = \(inp : inpt) ->
  let n = prelude.List.length (List Natural) inp
  let m = prelude.List.length Natural (prelude.Optional.default (List Natural) ([] : List Natural) (prelude.List.head (List Natural) inp))
  let maxd = (n + m) * 40
  let maxcode = n * m * 10
  in getarr Natural maxcode (Optional Natural) (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr Natural) -> 
  --let arrt = arr4000000 Natural
--  let arrops = arr4000000ops Natural
--  in prelude.Natural.lessThan arrt.size maxd
  let codeij = \(i : Natural) -> \(j : Natural) -> j + i * m
  let a = prelude.List.fold (a2det Natural) (a2d n m Natural inp) arrt.repr (\(z : a2det Natural) -> \(a : arrt.repr) -> arrops.modify a (codeij z.i z.j) (inc z.x)) arrops.empty
  let geta = \(i : Natural) -> \(j : Natural) -> prelude.Optional.default Natural 0 (arrops.get a (codeij i j))
  let ijpt = { i : Natural, j : Natural, p : Natural }
  let final = \(ijp : ijpt) -> prelude.Bool.and [prelude.Natural.equal n (ijp.i + 1), prelude.Natural.equal m (ijp.j + 1)]
  let codeijp = \(ijp : ijpt) -> ijp.p + 10 * (codeij ijp.i ijp.j)
  let statet = { d : arrt.repr, q : List ijpt, res : Optional Natural, ub : Natural }
  let start : ijpt = {i = 0, j = 0, p = 0 }
  let bnd1 = \(u : Natural) -> \(x : Natural) -> prelude.Bool.and [ prelude.Natural.lessThan 0 x, prelude.Natural.lessThanEqual x u]
  let decl = prelude.List.map Natural Natural (prelude.Natural.subtract 1)
  let pairs = \(ta : Type) -> \(a : List ta) -> \(tb : Type) -> \(b : List tb) ->
    let pt = pairt ta tb
    let f = \(b : tb) -> prelude.List.map ta pt (\(a : ta) -> {_1 = a, _2 = b}) a
    in prelude.List.concatMap tb pt f b
  let step = \(s : statet) ->
    merge {
      Some = const Natural statet s,
      None = if prelude.List.null ijpt s.q then s else 
        let gettos = \(from : ijpt) ->
          let top = if prelude.Natural.lessThan from.p 9 then [{i = from.i, j = from.j, p = 1 + from.p}] else ([] : List ijpt)
          let toadj =
            let ii = decl (prelude.List.filter Natural (bnd1 n) [from.i, from.i + 1, from.i + 2])
            let jj = decl (prelude.List.filter Natural (bnd1 m) [from.j, from.j + 1, from.j + 2])
            let pt = pairt Natural Natural
            let ok = \(x : pt) -> prelude.Bool.and [prelude.Bool.or [prelude.Natural.equal x._1 from.i, prelude.Natural.equal x._2 from.j], prelude.Natural.lessThanEqual (geta x._1 x._2) (1 + from.p)]
            let iijj = prelude.List.filter pt ok (pairs Natural ii Natural jj)
            in prelude.List.map pt ijpt (\(ij : pt) -> {i = ij._1, j = ij._2, p = 0}) iijj
          in top # toadj
        let tos = prelude.List.concatMap ijpt ijpt gettos s.q
        let newd = 1 + (prelude.Optional.default Natural 0 (arrops.get s.d (codeijp (prelude.Optional.default ijpt start (prelude.List.head ijpt s.q)))))
        let step = \(ijp : ijpt) -> \(s : statet) -> 
          if prelude.Bool.or [
               prelude.Bool.not (prelude.Optional.null Natural (arrops.get s.d (codeijp ijp))), 
               prelude.Bool.not (prelude.Optional.null Natural s.res),
               prelude.Natural.lessThan s.ub (newd + (prelude.Natural.subtract ijp.i n) + (prelude.Natural.subtract ijp.j m) + 1)
            ] then s else
            { d = arrops.modify s.d (codeijp ijp) (inc newd), 
              q = [ijp] # s.q, 
              res = if final ijp then Some newd else s.res,
              ub = prelude.Natural.min s.ub (newd + 10 * ((prelude.Natural.subtract ijp.i n) + (prelude.Natural.subtract ijp.j m) + 1)),
            }
        in prelude.List.fold ijpt tos statet step { d = s.d, q = [] : List ijpt, res = s.res, ub = s.ub }
    } s.res 
--  in arrops.asList a
--  in (prelude.Natural.fold maxd statet step { d = arrops.modify arrops.empty (codeijp start) (inc 0), q = [start], res = None Natural}).q
  in (prelude.Natural.fold maxd statet step { d = arrops.modify arrops.empty (codeijp start) (inc 0), q = [start], res = None Natural, ub = maxd}).res
  )

--let tex = assert : solve ex === Some 40   
--let tex2 = assert : solve (rep5ii ex) === Some 315   

--in solve (rep5ii ./input.dhall)
--in solve ./input.dhall
--in solve ex
in solve (rep5ii ex)
--./input.dhall
--in rep5ii [[1,2]]
--  in getarr Natural 200 (List (Optional Natural)) (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr Natural) -> arrops.asList arrops.empty)
--in ex
