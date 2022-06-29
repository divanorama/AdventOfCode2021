let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let lnt = List Natural
let inpt = List lnt

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

let solve = \(inp : inpt) ->
  let n = prelude.List.length lnt inp
  let m = prelude.List.length Natural (head lnt ([] : lnt) inp)
  let code = \(x : ijt) -> x.i * m + x.j
  let withi = prelude.List.zip Natural (prelude.Natural.enumerate n) lnt inp
  let it = {_1 : Natural, _2 : lnt}
  let f = \(i : it) -> zipWith Natural (prelude.Natural.enumerate m) Natural i._2 ijxt (\(j : Natural) -> \(x : Natural) -> {ij = {i = i._1, j = j}, x = x})
  let withij = prelude.List.concatMap it ijxt f withi
  let nm = n * m
  let arrt = arr16384 Natural
--  let arrt = arr64 Natural
  let arrops = arr16384ops Natural
--  let arrops = arr64ops Natural
  in if prelude.Natural.lessThan arrt.size nm then None Natural else
    let arr0t = arr16 (List ijt)
    let arr0ops = arr16ops (List ijt)
    let f = \(a : arrt.repr) -> \(x : ijxt) -> arrops.modify a (code x.ij) (\(_curr : Optional Natural) -> Some x.x)
    let map = prelude.List.foldLeft ijxt withij arrt.repr f arrops.empty
    let basincellt = { ij : ijt, id : Natural }
    let basinst = List basincellt
    let g = \(a : arr0t.repr) -> \(x : ijxt) -> arr0ops.modify a x.x (\(curr : Optional (List ijt)) ->
      Some ([x.ij] # (prelude.List.default ijt curr)))
    let revmap = prelude.List.foldLeft ijxt withij arr0t.repr g arr0ops.empty
    let statet = { basins : basinst, nextBasin : Natural, map : arrt.repr }
    let h = \(s : statet) -> \(h : Natural) -> 
      let stepCell = \(s : statet) -> \(cell : basincellt) ->
        let stepTo = \(s : statet) -> \(titj : ijt) ->
          merge {
            None = s,
            Some = \(x : Natural) -> 
              if prelude.Bool.not (prelude.Natural.equal h x) 
              then s 
              else { basins = [{ij = titj, id = cell.id}] # s.basins, nextBasin = s.nextBasin, map = arrops.modify s.map (code titj) (\(_cuur : Optional Natural) -> None Natural) }
          } (arrops.get s.map (code titj)) 
        in prelude.List.foldLeft ijt [
             {i = cell.ij.i + 1, j = cell.ij.j},
             {i = cell.ij.i, j = cell.ij.j + 1},
             {i = prelude.Natural.subtract 1 cell.ij.i, j = cell.ij.j},
             {i = cell.ij.i, j = prelude.Natural.subtract 1 cell.ij.j},
           ] statet stepTo s
      let s1 = prelude.List.foldLeft basincellt s.basins statet stepCell s
      let stepSink = \(s : statet) -> \(ij : ijt) ->
        merge {
          None = s,
          Some = \(_x : Natural) -> { basins = [{ij = ij, id = s.nextBasin}] # s.basins, nextBasin = 1 + s.nextBasin, map = s.map }
        } (arrops.get s.map (code ij))
      let revs : List ijt = prelude.List.default ijt (arr0ops.get revmap h)
      in prelude.List.foldLeft ijt revs statet stepSink s1
    let res = prelude.List.foldLeft Natural (prelude.Natural.enumerate 9) statet h {basins = [] : basinst, nextBasin = 0, map = map}
    in if prelude.Natural.lessThan arrt.size res.nextBasin then None Natural else
      let basins = prelude.List.map basincellt Natural (\(c : basincellt) -> c.id) res.basins
      let ff = \(a : arrt.repr) -> \(x : Natural) -> arrops.modify a x (\(curr : Optional Natural) -> Some (1 + (prelude.Optional.default Natural 0 curr)))
      let counts = prelude.List.concatMap (Optional Natural) Natural (prelude.Optional.toList Natural) (arrops.asList (prelude.List.foldLeft Natural basins arrt.repr ff arrops.empty))
      in Some (prelude.Natural.product (prelude.List.take 3 Natural (prelude.List.reverse Natural (prelude.Natural.sort counts))))
    


let tex = assert : solve ex === Some 1134
in solve ./input.dhall
--in solve ex
--in arr1024ops Bool
--in \(v : Type) -> arr1 v
--in arrOps Text Bool
