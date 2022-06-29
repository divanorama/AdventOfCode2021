let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let dott = { x : Integer, y : Integer }
let foldt = < x : Integer | y : Integer >
let inpt = { dots : List dott, folds : List foldt }

let ex : inpt = ./01.dhall

let bndt = { l : Integer, r : Integer }

let bnds = \(l : List Integer) ->
  let f = \(lr : bndt) -> \(x : Integer) -> {
      l = if prelude.Integer.lessThan x lr.l then x else lr.l,
      r = if prelude.Integer.lessThan lr.r x then x else lr.r,
    } : bndt
  in merge {
    None = { l = +0, r = +0 },
    Some = \(x : Integer) -> prelude.List.foldLeft Integer l bndt f { l = x, r = x }
  } (prelude.List.head Integer l)

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
let arr32768 = dblArr arr16384
let arr32768ops = \(v : Type) -> dblOps v (arr16384 v) (arr16384ops v)
let arr65536 = dblArr arr32768
let arr65536ops = \(v : Type) -> dblOps v (arr32768 v) (arr32768ops v)
let arr131072 = dblArr arr65536
let arr131072ops = \(v : Type) -> dblOps v (arr65536 v) (arr65536ops v)
let arr262144 = dblArr arr131072
let arr262144ops = \(v : Type) -> dblOps v (arr131072 v) (arr131072ops v)
let arr524288 = dblArr arr262144
let arr524288ops = \(v : Type) -> dblOps v (arr262144 v) (arr262144ops v)

let solve = \(inp : inpt) ->
  let g = \(d : dott) -> \(f : foldt) -> 
    merge {
      x = \(x : Integer) -> if prelude.Integer.lessThan d.x x then d else {x = prelude.Integer.subtract d.x (prelude.Integer.add x x), y = d.y},
      y = \(y : Integer) -> if prelude.Integer.lessThan d.y y then d else {x = d.x, y = prelude.Integer.subtract d.y (prelude.Integer.add y y)},
    } f
  let f = prelude.List.foldLeft foldt (prelude.List.take 1 foldt inp.folds) dott g
  let dst = prelude.List.map dott dott f inp.dots
  let bx = bnds (prelude.List.map dott Integer (\(d : dott) -> d.x) dst)
  let by = bnds (prelude.List.map dott Integer (\(d : dott) -> d.x) dst)
  let yspan = prelude.Integer.subtract by.l (prelude.Integer.add by.r +1)
  let g = \(d : dott) -> prelude.Integer.add (prelude.Integer.multiply (prelude.Integer.subtract bx.l d.x) yspan) (prelude.Integer.subtract by.l d.y)
  let ds = prelude.List.map dott Integer g dst
  let mx = bnds ds
  let arrt = arr524288 Bool
  let arrops = arr524288ops Bool
  in if prelude.Natural.lessThan arrt.size (1 + (prelude.Integer.abs mx.r)) then None Natural else
     let d2 = prelude.List.map Integer Natural prelude.Integer.abs ds
     let h = \(a : arrt.repr) -> \(x : Natural) -> arrops.modify a x (\(_curr : Optional Bool) -> Some True)
     let a = prelude.List.foldLeft Natural d2 arrt.repr h arrops.empty
--     in dst
     in Some (prelude.List.length Bool (prelude.List.concatMap (Optional Bool) Bool (prelude.Optional.toList Bool) (arrops.asList a)))

let tex = assert :  solve ex === Some 17

in solve ./input.dhall
