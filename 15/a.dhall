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
    empty = {children = [prevOps.empty, prevOps.empty]},
    get = \(r : repr) -> \(i : Natural) -> 
      if prelude.Natural.lessThan i prev.size 
      then merge { None = None v, Some = \(c : prev.repr) -> prevOps.get c i} (prelude.List.head prev.repr r.children) else
      merge { None = None v, Some = \(c : prev.repr) -> prevOps.get c (prelude.Natural.subtract prev.size i)} (prelude.List.head prev.repr (prelude.List.drop 1 prev.repr r.children)),
    modify = \(r : repr) -> \(i : Natural) -> \(f : Optional v -> Optional v) -> 
      if prelude.Natural.lessThan i prev.size 
      then merge {
        None = r,
        Some = \(c : prev.repr) -> { children = [prevOps.modify c i f] # (prelude.List.drop 1 prev.repr r.children) },
        } (prelude.List.head prev.repr r.children)
      else merge {
        None = r,
        Some = \(c : prev.repr) -> { children = (prelude.List.take 1 prev.repr r.children) # [prevOps.modify c (prelude.Natural.subtract prev.size i) f] },
        } (prelude.List.head prev.repr (prelude.List.drop 1 prev.repr r.children)),
    asList = \(r : repr) -> prelude.List.concatMap prev.repr (Optional v) prevOps.asList r.children
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
let arr2 = dblArr arr1
let arr2ops = \(v : Type) -> dblOps v (arr1 v) (arr1ops v)
let arr4 = dblArr arr2
let arr4ops = \(v : Type) -> dblOps v (arr2 v) (arr2ops v)
let arr8 = dblArr arr4
let arr8ops = \(v : Type) -> dblOps v (arr4 v) (arr4ops v)
let arr16 = dblArr arr8
let arr16ops = \(v : Type) -> dblOps v (arr8 v) (arr8ops v)
let arr32 = dblArr arr16
let arr32ops = \(v : Type) -> dblOps v (arr16 v) (arr16ops v)
let arr64 = dblArr arr32
let arr64ops = \(v : Type) -> dblOps v (arr32 v) (arr32ops v)
let arr128 = dblArr arr64
let arr128ops = \(v : Type) -> dblOps v (arr64 v) (arr64ops v)
let arr256 = dblArr arr128
let arr256ops = \(v : Type) -> dblOps v (arr128 v) (arr128ops v)
let arr512 = dblArr arr256
let arr512ops = \(v : Type) -> dblOps v (arr256 v) (arr256ops v)
let arr1024 = dblArr arr512
let arr1024ops = \(v : Type) -> dblOps v (arr512 v) (arr512ops v)
let arr2048 = dblArr arr1024
let arr2048ops = \(v : Type) -> dblOps v (arr1024 v) (arr1024ops v)
let arr4096 = dblArr arr2048
let arr4096ops = \(v : Type) -> dblOps v (arr2048 v) (arr2048ops v)
let arr8192 = dblArr arr4096
let arr8192ops = \(v : Type) -> dblOps v (arr4096 v) (arr4096ops v)
let arr16384 = dblArr arr8192
let arr16384ops = \(v : Type) -> dblOps v (arr8192 v) (arr8192ops v)
let arr32768 = dblArr arr16384
let arr32768ops = \(v : Type) -> dblOps v (arr16384 v) (arr16384ops v)
let arr65536 = dblArr arr32768
let arr65536ops = \(v : Type) -> dblOps v (arr32768 v) (arr32768ops v)
let arr131072 = dblArr arr65536
let arr131072ops = \(v : Type) -> dblOps v (arr65536 v) (arr65536ops v)
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

let solve = \(inp : inpt) ->
  let n = prelude.List.length (List Natural) inp
  let m = prelude.List.length Natural (prelude.Optional.default (List Natural) ([] : List Natural) (prelude.List.head (List Natural) inp))
  let arrt = arr131072 Natural
  let arrops = arr131072ops Natural
  let maxd = n * m * 10
--  in prelude.Natural.lessThan arrt.size maxd
  let codeij = \(i : Natural) -> \(j : Natural) -> j + i * m
  let a = prelude.List.foldLeft (a2det Natural) (a2d n m Natural inp) arrt.repr (\(a : arrt.repr) -> \(z : a2det Natural) -> arrops.modify a (codeij z.i z.j) (inc z.x)) arrops.empty
  let geta = \(i : Natural) -> \(j : Natural) -> prelude.Optional.default Natural 0 (arrops.get a (codeij i j))
  let ijpt = { i : Natural, j : Natural, p : Natural }
  let final = \(ijp : ijpt) -> prelude.Bool.and [prelude.Natural.equal n (ijp.i + 1), prelude.Natural.equal m (ijp.j + 1)]
  let codeijp = \(ijp : ijpt) -> ijp.p + 10 * (codeij ijp.i ijp.j)
  let statet = { d : arrt.repr, q : List ijpt, res : Optional Natural }
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
        let step = \(s : statet) -> \(ijp : ijpt) ->
          if prelude.Bool.or [prelude.Bool.not (prelude.Optional.null Natural (arrops.get s.d (codeijp ijp))), prelude.Bool.not (prelude.Optional.null Natural s.res)] then s else
            { d = arrops.modify s.d (codeijp ijp) (inc newd), q = [ijp] # s.q, res = if final ijp then Some newd else s.res }
        in prelude.List.foldLeft ijpt tos statet step { d = s.d, q = [] : List ijpt, res = s.res }
    } s.res 
--  in arrops.asList a
--  in (prelude.Natural.fold maxd statet step { d = arrops.modify arrops.empty (codeijp start) (inc 0), q = [start], res = None Natural}).q
  in (prelude.Natural.fold maxd statet step { d = arrops.modify arrops.empty (codeijp start) (inc 0), q = [start], res = None Natural}).res

let tex = assert : solve ex === Some 40   

in solve ./input.dhall
