let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

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

let enum = < N | C | B | H | S | O | K | P | F | V >
let N = enum.N
let C = enum.C
let B = enum.B
let H = enum.H
let S = enum.S
let O = enum.O
let K = enum.K
let P = enum.P
let F = enum.F
let V = enum.V

let enumi = \(x : enum) -> 
  merge {
    N = 0,
    C = 1,
    B = 2,
    H = 3,
    S = 4,
    O = 5,
    K = 6,
    P = 7,
    F = 8,
    V = 9
  } x

let enumn = 10

let pairt = { left : enum, right : enum }

let enums = [N, C, B, H, S, O, K, P, F, V]
let pairs = 
  let f = \(l : enum) -> prelude.List.map enum pairt (\(r : enum) -> {left = l, right = r}) enums
  in prelude.List.concatMap enum pairt f enums

let rulet = { left : enum, right : enum, insert : enum }
let inpt = { initial : List enum, rules : List rulet }

let ex : inpt = ./01.dhall

let inc = \(x : Natural) -> \(curr : Optional Natural) -> Some (x + (prelude.Optional.default Natural 0 curr))
let dec = \(x : Natural) -> \(curr : Optional Natural) -> Some (prelude.Natural.subtract x (prelude.Optional.default Natural 0 curr))
let set = \(t : Type) -> \(x : t) -> \(_curr : Optional t) -> Some x

let solve = \(inp : inpt) ->
  let t = 10
  let larrt = arr16 Natural
  let larrops = arr16ops Natural
  let parrt = arr128 Natural
  let parrops = arr128ops Natural
  let rarrt = arr128 enum
  let rarrops = arr128ops enum
  let codep = \(x : pairt) -> (enumi x.left) * enumn + (enumi x.right)
  let ep = { _1 : enum, _2 : enum }
  let la = prelude.List.foldLeft enum inp.initial larrt.repr (
    \(a : larrt.repr) -> \(e : enum) -> 
      larrops.modify a (enumi e) (inc 1)
    ) larrops.empty
  let pa = prelude.List.foldLeft ep (prelude.List.zip enum inp.initial enum (prelude.List.drop 1 enum inp.initial)) parrt.repr (
    \(a : parrt.repr) -> \(p : ep) ->
      parrops.modify a (codep {left = p._1, right = p._2}) (inc 1)
    ) parrops.empty
  let ra = prelude.List.foldLeft rulet inp.rules rarrt.repr (
    \(a : rarrt.repr) -> \(r : rulet) ->
      rarrops.modify a (codep {left = r.left, right = r.right}) (set enum r.insert)
    ) rarrops.empty
  let statet = { la : larrt.repr, pa : parrt.repr }
  let step = \(s : statet) ->
    let step1 = \(la : larrt.repr) -> \(p : pairt) ->
      merge {
        None = la,
        Some = \(mid : enum) -> 
          let z = prelude.Optional.default Natural 0 (parrops.get s.pa (codep p))
          in larrops.modify la (enumi mid) (inc z)
      } (rarrops.get ra (codep p))
    let step2 = \(pa : parrt.repr) -> \(p : pairt) ->
      merge {
        None = pa,
        Some = \(mid : enum) ->
          let z = prelude.Optional.default Natural 0 (parrops.get s.pa (codep p))
          let pa1 = parrops.modify pa (codep {left = p.left, right = mid}) (inc z)
          let pa2 = parrops.modify pa1 (codep {left = mid, right = p.right}) (inc z)
          let pa3 = parrops.modify pa2 (codep p) (dec z)
          in pa3
      } (rarrops.get ra (codep p))
    let la1 = prelude.List.foldLeft pairt pairs larrt.repr step1 s.la
    let pa1 = prelude.List.foldLeft pairt pairs parrt.repr step2 s.pa
    in { la = la1, pa = pa1 }
  let s = prelude.Natural.fold t statet step { la = la, pa = pa }
  let lst = prelude.List.map (Optional Natural) Natural (prelude.Optional.default Natural 0) (prelude.List.filter (Optional Natural) (\(x : Optional Natural) -> prelude.Bool.not (prelude.Optional.null Natural x)) (larrops.asList s.la))
  let mn = prelude.Optional.default Natural 0 (prelude.List.head Natural (prelude.Natural.sort lst)) 
  let mx = prelude.Optional.default Natural 0 (prelude.List.head Natural (prelude.List.reverse Natural (prelude.Natural.sort lst)))
  in prelude.Natural.subtract mn mx
--  in prelude.Natural.lessThan larrt.size enumn
--  in prelude.Natural.lessThan parrt.size (enumn * enumn)

let tex = assert : solve ex === 1588

in solve ./input.dhall
