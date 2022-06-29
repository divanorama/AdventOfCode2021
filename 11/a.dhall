let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let lnt = List Natural
let inpt = List lnt

let ex0 : inpt = ./00.dhall
let ex : inpt = ./01.dhall

let id = \(t : Type) -> \(x : t) -> x


let head = \(t : Type) -> \(def : t) -> \(x : List t) -> merge {
    Some = id t,
    None = def
  } (prelude.List.head t x)

let zipWith = \(a : Type) -> \(la : List a) -> \(b : Type) -> \(lb : List b) -> \(c : Type) -> \(f : a -> b -> c) ->
  let pt = {_1 : a, _2 : b}
  let g = \(p : pt) -> f p._1 p._2
  in prelude.List.map pt c g (prelude.List.zip a la b lb)

let ijt = {i : Natural, j : Natural}
let ijxt = {ij : ijt, x : Natural}

let arrOps = \(repr : Type) -> \(v : Type) -> { 
  empty : repr, 
  modify : repr -> Natural -> (Optional v -> Optional v) -> repr, 
  get : repr -> Natural -> Optional v,
  asList : repr -> List (Optional v)
}
let arrReprt = { repr : Type, size : Natural }

let dblRepr = \(repr : Type) -> {left : repr, right : repr}
let dblArr = \(fprev : Type -> arrReprt) -> \(v : Type) -> let prev = fprev v in { repr = dblRepr prev.repr, size = prev.size * 2 } : arrReprt
let dblOps = \(v : Type) -> \(prev : arrReprt) -> \(prevOps : arrOps prev.repr v) ->
  let repr = dblRepr prev.repr
  in {
    empty = {left = prevOps.empty, right = prevOps.empty},
    get = \(r : repr) -> \(i : Natural) -> 
      if prelude.Natural.lessThan i prev.size 
      then prevOps.get r.left i else 
      prevOps.get r.right (prelude.Natural.subtract prev.size i),
    modify = \(r : repr) -> \(i : Natural) -> \(f : Optional v -> Optional v) -> 
      if prelude.Natural.lessThan i prev.size 
      then {left = prevOps.modify r.left i f, right = r.right} 
      else {left = r.left, right = prevOps.modify r.right (prelude.Natural.subtract prev.size i) f},
    asList = \(r : repr) -> prevOps.asList r.left # prevOps.asList r.right
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

let solve = \(maxt : Natural) -> \(inp : inpt) ->
--  let maxt = 100
  let n = prelude.List.length lnt inp
  let m = prelude.List.length Natural (head lnt ([] : lnt) inp)
  let code = \(x : ijt) -> x.i * m + x.j
  let withi = prelude.List.zip Natural (prelude.Natural.enumerate n) lnt inp
  let it = {_1 : Natural, _2 : lnt}
  let f = \(i : it) -> zipWith Natural (prelude.Natural.enumerate m) Natural i._2 ijxt (\(j : Natural) -> \(x : Natural) -> {ij = {i = i._1, j = j}, x = x})
  let withij = prelude.List.concatMap it ijxt f withi
  let nm = n * m
  let arrt = arr128 Natural
  let arrops = arr128ops Natural
  in if prelude.Natural.lessThan arrt.size nm then None Natural else
    let arrbt = arr128 Bool
    let arrbops = arr128ops Bool
    let f = \(a : arrt.repr) -> \(x : ijxt) -> arrops.modify a (code x.ij) (\(_curr : Optional Natural) -> Some x.x)
    let map = prelude.List.foldLeft ijxt withij arrt.repr f arrops.empty
    let ixs = prelude.List.map ijxt ijt (\(x : ijxt) -> x.ij) withij
    let statet = { score : Natural, map : arrt.repr, isBooming : arrbt.repr, numBooming : Natural, currT : Natural }
    let mInc = \(a : arrt.repr) -> \(ij : ijt) -> arrops.modify a (code ij) (\(curr : Optional Natural) -> Some (1 + (merge { None = 0, Some = id Natural} curr)))
    let step = \(s : statet) ->
      let isNewBoom = \(ij : ijt) -> prelude.Bool.and [
          prelude.Bool.not (prelude.Optional.default Bool False (arrbops.get s.isBooming (code ij))),
          prelude.Natural.lessThan 9 (prelude.Optional.default Natural 0 (arrops.get s.map (code ij))),
        ]
      let toBoom = prelude.List.filter ijt isNewBoom ixs
      let newBooms = prelude.List.length ijt toBoom
      in if prelude.Natural.lessThan 0 newBooms
        then
          let fn = \(up : Natural) -> \(x : Natural) -> prelude.List.filter Natural (prelude.Natural.greaterThan up) (if prelude.Natural.lessThan 0 x then [prelude.Natural.subtract 1 x, x, x + 1] else [x, x + 1])
          let fi = \(ij : ijt) -> prelude.List.map Natural ijt (\(i : Natural) -> {i = i, j = ij.j}) (fn n ij.i)
          let fj = \(ij : ijt) -> prelude.List.map Natural ijt (\(j : Natural) -> {i = ij.i, j = j}) (fn m ij.j)
          let f = \(ij : ijt) -> prelude.List.concatMap ijt ijt fi (prelude.List.concatMap ijt ijt fj [ij])
          let toInc = prelude.List.concatMap ijt ijt f toBoom
          let newMap = prelude.List.foldLeft ijt toInc arrt.repr mInc s.map
          let mMark = \(a : arrbt.repr) -> \(ij : ijt) -> arrbops.modify a (code ij) (\(_curr : Optional Bool) -> Some True)
          let newB = prelude.List.foldLeft ijt toBoom arrbt.repr mMark s.isBooming
          in { score = s.score, map = newMap, isBooming = newB, numBooming = s.numBooming + newBooms, currT = s.currT }
        else if prelude.Natural.lessThan 0 s.numBooming
          then 
            let mZero = \(a : arrt.repr) -> \(ij : ijt) -> arrops.modify a (code ij) (\(curr : Optional Natural) -> if prelude.Natural.lessThan 9 (prelude.Optional.default Natural 0 curr) then Some 0 else curr)
            let newMap = prelude.List.foldLeft ijt ixs arrt.repr mZero s.map
            in { score = s.score + s.numBooming, map = newMap, isBooming = arrbops.empty, numBooming = 0, currT = s.currT }
          else if prelude.Natural.lessThan s.currT maxt 
            then
              let newMap = prelude.List.foldLeft ijt ixs arrt.repr mInc s.map
              in { score = s.score, map = newMap, isBooming = s.isBooming, numBooming = s.numBooming, currT = s.currT + 1 } 
            else s
    in Some (prelude.Natural.fold (maxt * 10) statet step { score = 0, map = map, isBooming = arrbops.empty, numBooming = 0, currT = 0 }).score

let tex0 = assert : solve 2 ex0 === Some 9
let tex1 = assert : solve 2 ex === Some 35
let tex = assert : solve 100 ex === Some 1656
--in solve 2 ex0
in solve 100 ./input.dhall
