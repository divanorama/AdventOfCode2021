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
  in (prelude.Natural.fold 3 st step { sz = 1, f = f }).f t0 o0
--

let inpt = { algo : List Natural, map : List (List Natural) }

let ex : inpt = ./01.dhall

let pt = \(a : Type) -> \(b : Type) -> {_1 : a, _2 : b}
let concat3 = \(t : Type) -> \(a : List t) -> \(b : List t) -> \(c : List t) -> a # b # c
let zip3with = \(t : Type) -> \(f : t -> t -> t -> t) -> \(a : List t) -> \(b : List t) -> \(c : List t) -> 
  let lab = prelude.List.zip t a t b
  let labc = prelude.List.zip (pt t t) lab t c
  in prelude.List.map (pt (pt t t) t) t (\(x : pt (pt t t) t) -> f x._1._1 x._1._2 x._2) labc
  
let slide3with = \(t : Type) -> \(f : t -> t -> t -> t) -> \(l : List t) ->
  let d1 = prelude.List.drop 1 t l
  let d2 = prelude.List.drop 2 t l
  in zip3with t f l d1 d2


let solve = \(inp : inpt) ->
  getarr Natural 512 Natural ( \(arrt : arrReprt) -> \(arrops : arrOps (arrt.repr) Natural) -> 
    let ixt = \(t : Type) -> {index : Natural, value : t}
    let a = prelude.List.foldLeft (ixt Natural) (prelude.List.indexed Natural inp.algo) arrt.repr (\(a : arrt.repr) -> \(x : ixt Natural) -> arrops.modify a x.index (\(_ : Optional Natural) -> Some x.value)) arrops.empty
    let ln = List Natural
    let lln = List ln
    let st = {map : lln, outer : Natural}
    let apply = \(l : ln) ->
      let i = prelude.List.foldLeft Natural l Natural (\(acc : Natural) -> \(x : Natural) -> acc * 2 + x) 0
      in prelude.Optional.default Natural 0 (arrops.get a i)
    let step = \(s : st) ->
      let l = s.map
      let h = prelude.List.length ln l
      let w = prelude.List.length Natural (prelude.Optional.default (List Natural) ([] : List Natural) (prelude.List.head ln l))
      let zz = prelude.List.replicate w Natural s.outer
      let l = [zz,zz] # l # [zz,zz]
      let l = prelude.List.map ln ln (\(l : ln) -> [s.outer, s.outer] # l # [s.outer, s.outer]) l
      let l = prelude.List.map ln lln (prelude.List.map Natural ln (\(x : Natural) -> [x])) l
      let l = prelude.List.map lln lln (slide3with ln (concat3 Natural)) l
      let l = slide3with lln (zip3with ln (concat3 Natural)) l
      let l = prelude.List.map lln ln (prelude.List.map ln Natural apply) l
      let outer = prelude.Optional.default Natural 0 (arrops.get a (if prelude.Natural.equal s.outer 0 then 0 else 511))
      in {map = l, outer = outer}
    let res = prelude.Natural.fold 50 st step {map = inp.map, outer = 0}
    in prelude.Natural.sum (prelude.List.concat Natural res.map)
  )

--in solve ex
in solve ./input.dhall
