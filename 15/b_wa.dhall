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

let wraponce = \(y : Natural) -> if prelude.Natural.lessThan y 10 then y else (1 + (prelude.Natural.subtract 10 y))

let incbywrap = \(w : Natural) -> \(x : Natural) ->
  let x = wraponce (x + w)
  in wraponce x

let without = \(t : Type) -> \(code : t -> Natural) -> \(torem : List t) -> \(x : List t) ->
  let pt = {code : Natural, value : t}
  let withcode = \(a : t) -> {code = code a, value = a}
  let lwithcode = prelude.List.map t pt withcode
  let torem = lwithcode torem
  let x = lwithcode x
  let mx = prelude.Optional.default Natural 1 (prelude.Natural.listMax (prelude.List.map pt Natural (\(x : pt) -> x.code) (torem # x)))
  let st = {pw : Natural, res : List Natural}
  let pws = (prelude.Natural.fold 30 st (\(s : st) -> if prelude.Natural.lessThan mx s.pw then s else {pw = s.pw * 2, res = [s.pw] # s.res}) {pw = 1, res = [] : List Natural}).res
  let itemt = { torem : List pt, x : List pt }
  let st = List itemt
  let step = \(s : st) -> \(pw : Natural) ->
    let step = \(s : itemt) -> --if prelude.Bool.or [prelude.List.null pt s.torem, prelude.List.null pt s.x] then [s] else
      let f = prelude.Natural.lessThanEqual pw
      let ff = \(x : pt) -> f x.code
      let g = prelude.List.map pt pt (\(x : pt) -> if ff x then {value = x.value, code = prelude.Natural.subtract pw x.code} else x)
      let torem = prelude.List.partition pt ff s.torem
      let x = prelude.List.partition pt ff s.x
      in [ {torem = g torem.true, x = g x.true}, {torem = g torem.false, x = g x.false} ]
    in prelude.List.concatMap itemt itemt step s
  let res = prelude.List.foldLeft Natural pws st step [{torem = torem, x = x}]
--  in res
  let simple = \(x : itemt) -> if prelude.List.null pt x.torem then prelude.List.take 1 pt x.x else [] : List pt
  let res = prelude.List.concatMap itemt pt simple res
  in prelude.List.map pt t (\(x : pt) -> x.value) res

let solve = \(inp : inpt) ->
  let n = prelude.List.length (List Natural) inp
  let m = prelude.List.length Natural (prelude.Optional.default (List Natural) ([] : List Natural) (prelude.List.head (List Natural) inp))
  in getarr Natural (n*m) (Optional Natural) (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr Natural) -> 
  let codeij = \(i : Natural) -> \(j : Natural) -> j + i * m
  let a = prelude.List.foldLeft (a2det Natural) (a2d n m Natural inp) arrt.repr (\(a : arrt.repr) -> \(z : a2det Natural) -> arrops.modify a (codeij z.i z.j) (inc z.x)) arrops.empty
  let geta = \(i : Natural) -> \(j : Natural) ->
     let st = {i : Natural, j : Natural, wraps : Natural}
     let step = \(s : st) ->
       if prelude.Natural.lessThanEqual n s.i then {i = prelude.Natural.subtract n s.i, j = s.j, wraps = s.wraps + 1} else
       if prelude.Natural.lessThanEqual m s.j then {i = s.i, j = prelude.Natural.subtract m s.j, wraps = s.wraps + 1} else
       s
     let w = prelude.Natural.fold 10 st step {i=i,j=j,wraps=0}
--     in (prelude.Optional.default Natural 0 (arrops.get a (codeij w.i w.j)))
     in incbywrap w.wraps (prelude.Optional.default Natural 0 (arrops.get a (codeij w.i w.j)))
  let ijpt = { i : Natural, j : Natural, p : Natural }
  let tn = n * 5
  let tm = m * 5
  let final = \(ijp : ijpt) -> prelude.Bool.and [prelude.Natural.equal tn (ijp.i + 1), prelude.Natural.equal tm (ijp.j + 1)]
  let maxd = (tn + tm) * 40
  let codeij = \(i : Natural) -> \(j : Natural) -> j + i * tm
  let codeijp = \(ijp : ijpt) -> ijp.p + 10 * (codeij ijp.i ijp.j)
  let statet = { pq : List ijpt, q : List ijpt, res : Optional Natural, curr : Natural }
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
          let top = 
            (if prelude.Natural.lessThan from.p 9 then [{i = from.i, j = from.j, p = 1 + from.p}] else ([] : List ijpt))
            #
            (if prelude.Natural.lessThan 0 from.p then [{i = from.i, j = from.j, p = prelude.Natural.subtract 1 from.p}] else ([] : List ijpt))
          let toadj =
            let ii = decl (prelude.List.filter Natural (bnd1 tn) [from.i, from.i + 1, from.i + 2])
            let jj = decl (prelude.List.filter Natural (bnd1 tm) [from.j, from.j + 1, from.j + 2])
            let pt = pairt Natural Natural
            let okij = \(x : pt) -> prelude.Bool.and [prelude.Bool.or [prelude.Natural.equal x._1 from.i, prelude.Natural.equal x._2 from.j]]
            let iijj = prelude.List.filter pt okij (pairs Natural ii Natural jj)
            
            let ok = \(x : pt) -> prelude.Natural.equal (geta x._1 x._2) (1 + from.p)
            let l1 = prelude.List.map pt ijpt (\(ij : pt) -> {i = ij._1, j = ij._2, p = 0}) (prelude.List.filter pt ok iijj)
            let l2 = if prelude.Natural.lessThan 0 from.p then [] : List ijpt else
              prelude.List.map pt ijpt (\(ij : pt) -> {i = ij._1, j = ij._2, p = prelude.Natural.subtract 1 (geta from.i from.j)}) iijj
            in l1 # l2
          in top # toadj
        let tos = prelude.List.concatMap ijpt ijpt gettos s.q
        let tos = without ijpt codeijp s.q tos
        let tos = without ijpt codeijp s.pq tos
        in { pq = s.q, q = tos, res = if prelude.Bool.or (prelude.List.map ijpt Bool final tos) then Some (s.curr + 1) else None Natural, curr = s.curr + 1 }
    } s.res 
 in (prelude.Natural.fold maxd statet step { pq = [] : List ijpt, q = [start], res = None Natural, curr = 0}).res
--  in Some (incbywrap (getaa n m).wraps 1)
--  in Some (getaa n m).wraps
--  in Some (geta n m)
  )

--let tex = assert : solve ex === Some 40   

--in without Natural (prelude.Function.identity Natural) [1,2,3] [0,2,5,7]
in solve ex
--in incbywrap 10 9

--in solve ./input.dhall
--./input.dhall
--  in getarr Natural 200 (List (Optional Natural)) (\(arrt : arrReprt) -> \(arrops : arrOps arrt.repr Natural) -> arrops.asList arrops.empty)
--in ex
