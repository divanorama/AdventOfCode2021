let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let inpt = { start : Natural, end : Natural, edges : List (List Natural), caves : List (List Natural) }

let ex : inpt = /home/divankov/advent/2021/12/01.dhall
let ex2 : inpt = ./02.dhall
let ex3 : inpt = ./03.dhall

let bmitemt = { i : Natural, p : Natural }

let pw2 = \(n : Natural) -> prelude.Natural.fold n Natural (\(x : Natural) -> x * 2) 1

let bmt = List bmitemt

let powerset = \(n : Natural) ->
  let items = prelude.List.reverse bmitemt (prelude.List.map Natural bmitemt (\(i : Natural) -> {i = i, p = pw2 i}) (prelude.Natural.enumerate n)) 
  let decode = \(x : Natural) ->
    let st = { res : List bmitemt, x : Natural }
    let f = \(s : st) -> \(i : bmitemt) ->
      if prelude.Natural.lessThan s.x i.p then s
      else { res = [i] # s.res, x = prelude.Natural.subtract i.p s.x }
    in (prelude.List.foldLeft bmitemt items st f { x = x, res = [] : bmt } ).res
  in prelude.List.map Natural bmt decode (prelude.Natural.enumerate (pw2 n))

let id = \(t : Type) -> \(a : t) -> a

let dpt = { bits : bmt, last : Natural }

let pairt = \(a : Type) -> \(b : Type) -> {a : a, b : b}

let pairs = \(a : List Natural) ->
  let n = prelude.List.length Natural a
  let pt = pairt Natural Natural
  let f = \(pa : Natural) -> prelude.List.concatMap Natural pt (\(pb : Natural) -> if prelude.Natural.equal pa pb then [] : List pt else [{a = pa, b = pb}]) a
  in prelude.List.concatMap Natural pt f a

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

let smallt = {want : Natural, have : Natural}
let outt = < smalle : smallt | smalldp : smallt | ok : Natural >

let solve = \(inp : inpt) ->
  let n = 1 + (prelude.List.foldLeft Natural (prelude.List.concat Natural (inp.edges # inp.caves)) Natural prelude.Natural.max 0)
  let pn = pw2 n
  let earrt = arr128 Natural
  let earrops = arr128ops Natural
  in if prelude.Natural.lessThan earrt.size (n * n) then outt.smalle {want = n * n, have = earrt.size} else --None Natural else
    let dparrt = arr8192 Natural
    let dparrops = arr8192ops Natural
    in if prelude.Natural.lessThan dparrt.size (n * pn) then outt.smalldp {want = n * pn, have = dparrt.size} else
      let codecell = \(s : dpt) -> s.last + n * (prelude.Natural.sum (prelude.List.map bmitemt Natural (\(x : bmitemt) -> x.p) s.bits)) 
      let codee = \(i : Natural) -> \(j : Natural) -> i * n + j
      let cells = prelude.List.concatMap bmt dpt (\(x : bmt) -> prelude.List.map bmitemt dpt (\(i : bmitemt) -> {bits = x, last = i.i}) x) (powerset n)
      let et = pairt Natural Natural
      let es = prelude.List.concatMap (List Natural) et pairs (inp.edges # inp.caves)
      let adde = \(a : earrt.repr) -> \(e : et) -> earrops.modify a (codee e.a e.b) (\(curr : Optional Natural) -> Some (1 + merge {None = 0, Some = id Natural} curr))
      let e = prelude.List.foldLeft et es earrt.repr adde earrops.empty

      let dp0 = dparrops.modify dparrops.empty (codecell {last = inp.start, bits = [{i = inp.start, p = pw2 inp.start}]}) (\(_curr : Optional Natural) -> Some 1)
      let cpt = {from : dpt, to : dpt}
      let getcp = \(c : dpt) ->
        let items = prelude.List.filter bmitemt (\(x : bmitemt) -> prelude.Bool.not (prelude.Natural.equal x.i c.last)) c.bits
        let f = \(x : bmitemt) -> { to = c, from = { last = x.i, bits = prelude.List.filter bmitemt (\(y : bmitemt) -> prelude.Bool.not (prelude.Natural.equal y.i c.last)) c.bits } }
        in prelude.List.map bmitemt cpt f items
      let cellsteps = prelude.List.concatMap dpt cpt getcp cells
      let step = \(dp : dparrt.repr) -> \(ft : cpt) ->
        merge {
          None = dp,
          Some = \(mul : Natural) ->
            merge {
              None = dp,
              Some = \(x : Natural) ->
                dparrops.modify dp (codecell ft.to) (\(curr : Optional Natural) -> Some (x * mul + (prelude.Optional.default Natural 0 curr) ))
            } (dparrops.get dp (codecell ft.from))
        } (earrops.get e (codee ft.from.last ft.to.last))
--      in Some 1
--      in prelude.List.map cpt {a : Natural, b : Natural, c : Optional Natural} (\(ft : cpt) -> {a = codecell ft.from, b = codecell ft.to, c = earrops.get e (codee ft.from.last ft.to.last)}) cellsteps
--      in dp0
--      in cellsteps
      let dp = prelude.List.foldLeft cpt cellsteps dparrt.repr step dp0
      let finalcells = prelude.List.filter dpt (\(x : dpt) -> prelude.Natural.equal x.last inp.end) cells
      --in e
      --in Some 1
      in outt.ok (prelude.Natural.sum (prelude.List.map dpt Natural (\(x : dpt) -> prelude.Optional.default Natural 0 (dparrops.get dp (codecell x))) finalcells))

let tex = assert : solve ex === outt.ok 10
let tex2 = assert : solve ex2 === outt.ok 19
let tex3 = assert : solve ex3 === outt.ok 226

in solve ./input.dhall

--in solve ./input.dhall
