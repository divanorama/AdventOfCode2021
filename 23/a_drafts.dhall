let prelude = ../prelude.dhall

-- IntMap

let nodeinfo = {min : Natural, max : Natural}
let combinfos = \(a : nodeinfo) -> \(b : nodeinfo) -> {min = prelude.Natural.min a.min b.min, max = prelude.Natural.max a.max b.max}
let joininfos = \(l : List nodeinfo) -> 
  merge {
    None = {min = 0, max = 0},
    Some = \(x : nodeinfo) -> prelude.List.fold nodeinfo l nodeinfo combinfos x
  } (prelude.List.head nodeinfo l)
let mapt = { repr : Type, v : Type }
let growt = \(t : Type) -> < fits : t | extend : List t >
let grow2l = \(t : Type) -> \(x : growt t) ->
  merge {
    fits = \(x : t) -> [x],
    extend = prelude.Function.identity (List t),
  } x
let _mapops = \(m : mapt) -> {
  upsert  : m.repr -> Natural -> (Optional m.v -> m.v) -> growt m.repr,
  get     : m.repr -> Natural -> Optional m.v,
  getinfo : m.repr -> nodeinfo,
}
let mapcb = \(x : Type) -> \(v : Type) -> forall (repr : Type) -> forall (ops : _mapops {repr = repr, v = v}) -> forall (m : repr) -> x


let kvt = \(v : Type) -> {key : Natural, value : v}
let getv = \(v : Type) -> \(x : kvt v) -> x.value


let m1 = \(v : Type) -> { repr = {info : nodeinfo, nodes : List (kvt v)}, v = v}
let mkm1 = \(v : Type) -> \(l : List (kvt v)) -> {
  nodes = l,
  info = joininfos (prelude.List.map (kvt v) nodeinfo (\(x : kvt v) -> {min = x.key, max = x.key}) l),
} : (m1 v).repr
let _m1ops = \(v : Type) -> 
  let repr = (m1 v).repr
  let kvt = kvt v
  let getv = getv v
  let split = \(x : repr) -> prelude.List.map (List kvt) repr (mkm1 v) [prelude.List.take 5 kvt x.nodes, prelude.List.drop 5 kvt x.nodes]
  in {
    getinfo = \(m : repr) -> m.info,
    get = 
      let f = \(k : Natural) -> \(x : kvt) -> prelude.Natural.equal k x.key
      in \(m : repr) -> \(k : Natural) -> prelude.List.head v (prelude.List.map kvt v getv (prelude.List.filter kvt (f k) m.nodes)),
    upsert =
      let lek = \(k : Natural) -> \(x : kvt) -> prelude.Natural.lessThan (x.key) k
      in \(m : repr) -> \(k : Natural) -> \(f : Optional v -> v) ->
        let pt = prelude.List.partition kvt (lek k) m.nodes
        let a = pt.true
        let b = pt.false
        let vb = merge {
          None = {_1 = None v, _2 = b},
          Some = \(x : kvt) -> if prelude.Natural.equal k x.key then {_1 = Some x.value, _2 = prelude.List.drop 1 kvt b} else {_1 = None v, _2 = b}
        } (prelude.List.head kvt b)
        let z = {key = k, value = f vb._1}
        let b = vb._2
        let res = { nodes = a # [z] # b, info = {min = prelude.Natural.min z.key m.info.min, max = prelude.Natural.max z.key m.info.max}}
        in if prelude.Natural.lessThan 10 (prelude.List.length kvt res.nodes) then (growt repr).extend (split res)
        else (growt repr).fits res
        
  } : _mapops (m1 v)

let m2 = \(m : mapt) -> { repr = {info : nodeinfo, nodes : List m.repr}, v = m.v } : mapt

let mkm2 = \(m : mapt) -> \(ops : _mapops m) -> \(l : List m.repr) -> {
  info = joininfos (prelude.List.map m.repr nodeinfo ops.getinfo l),
  nodes = l,
} : (m2 m).repr

let droplast = \(t : Type) -> \(l : List t) ->
  let n = prelude.List.length t l
  in prelude.List.take (prelude.Natural.subtract 1 n) t l

let _m2ops = \(prev : mapt) -> \(ops : _mapops prev) -> 
  let repr = (m2 prev).repr
  let v = prev.v
  let ov = Optional v
  let split = \(l : List prev.repr) -> prelude.List.map (List prev.repr) repr (mkm2 prev ops) [prelude.List.take 5 prev.repr l, prelude.List.drop 5 prev.repr l]
  in {
    getinfo = \(m : repr) -> m.info,
    get = 
      let unopt = \(x : Optional ov) -> merge {
        None = None prev.v,
        Some = prelude.Function.identity ov,
      } x
      let inr = \(k : Natural) -> \(i : nodeinfo) -> prelude.Bool.and [prelude.Natural.lessThanEqual i.min k, prelude.Natural.lessThanEqual k i.max]
      let f = \(k : Natural) -> \(p : prev.repr) -> inr k (ops.getinfo p)
      in \(m : repr) -> \(k : Natural) -> unopt (prelude.List.head ov (prelude.List.map prev.repr ov (\(m : prev.repr) -> ops.get m k) (prelude.List.filter prev.repr (f k) m.nodes))),
    upsert =
      let x = 1
      let pf = \(k : Natural) -> \(x : prev.repr) -> prelude.Natural.lessThanEqual (ops.getinfo x).min k
      in \(m : repr) -> \(k : Natural) -> \(f : ov -> v) -> 
        let pt = prelude.List.partition prev.repr (pf k) m.nodes
        let a = pt.false
        let b = pt.true
        let acb = merge {
          None = {a = droplast prev.repr a, c = prelude.Optional.toList prev.repr (prelude.List.last prev.repr a), b = b},
          Some = \(hd : prev.repr) -> {a = a, c = grow2l prev.repr (ops.upsert hd k f), b = prelude.List.drop 1 prev.repr b},
        } (prelude.List.head prev.repr b)
        let a = acb.a
        let b = acb.b
        let c = acb.c
        let res = {nodes = a # c # b, info = joininfos (prelude.List.map prev.repr nodeinfo ops.getinfo (a # c # b))}
        in if prelude.Natural.lessThan 10 (prelude.List.length prev.repr res.nodes) then (growt repr).extend (split res.nodes)
        else (growt repr).fits res
      ,
  } : _mapops (m2 prev)

let mapops = \(v : Type) -> \(repr : Type) -> {
  get : repr -> Natural -> Optional v,
  upsert : repr -> Natural -> (Optional v -> v) -> repr
}

let wrapper = \(v : Type) -> {
  get : Natural -> Optional v,
  upsert : forall (x : Type) -> forall (cb : mapcb x v) -> x
}

let m1w = \(v : Type) -> \(m : (m1 v).repr) -> let ops = _m1ops v in {
  get = ops.get m,
  upsert = \(x : Type) -> \(cb : mapcb x v) -> cb (m1 v).repr ops m,
} : (wrapper v)

let wrapperops = \(v : Type) -> let wt = wrapper v in {
  get = \(w : wt) -> w.get,
  upsert = \(w : wt) -> \(k : Natural) -> \(f : Optional v -> v) ->
    w.upsert wt (\(repr : Type) -> \(ops : _mapops {repr = repr, v = v}) -> \(m : repr) -> {
      get = ops.get m,
      upsert = \(x : Type) -> \(cb : mapcb x v) -> (
        merge {
          fits = cb repr ops,
          extend = \(l : List repr) ->
            let m2 = m2 {repr=repr, v = v}
            let ops2 = _m2ops {repr=repr, v = v} ops
            in cb m2.repr ops2 (mkm2 {repr=repr, v=v} ops l)
        } (ops.upsert m k f)
      ) : x,
    } : wt),
} : (mapops v wt)

--


let enum = < A|B|C|D>
let it = \(t : Type) -> {index : Natural, value : t}
let A = enum.A
let B = enum.B
let C = enum.C
let D = enum.D

let e2i = \(e : enum) ->
  merge {
    A = 0,
    B = 1,
    C = 2, 
    D = 3
  } e

let plus = \(a : Natural) -> \(b : Natural) -> a + b
let pw = \(x : Natural) -> \(n : Natural) -> prelude.Natural.fold n Natural (\(acc : Natural) -> acc * x) 1
let le = List enum
let inpt = {rooms : List le}
let roomt = < initial : le | filling : le >
let inroom = \(x : roomt) -> merge {
  initial = prelude.Function.identity le,
  filling = prelude.Function.identity le,
} x
let spacet = Optional enum
let nrooms = 4
let nspaces = 7
let post = { rooms : List roomt, spaces : List spacet }


let codespace = \(x : spacet) -> merge {
  None = 0,
  Some = \(e : enum) -> 1 + e2i e
} x
let ncodespace = 5
let codespaces = \(l : List spacet) -> prelude.List.fold spacet l Natural (\(r : spacet) -> \(acc : Natural) -> acc * ncodespace + codespace r) 0
let ncodespaces = pw ncodespace nspaces
let coderoom = \(x : roomt) -> merge {
  filling = prelude.List.length enum,
  initial = prelude.Function.compose le Natural Natural (prelude.List.length enum) (plus 2) -- 3
} x
let ncoderoom = 5
let coderooms = \(l : List roomt) -> prelude.List.fold roomt l Natural (\(r : roomt) -> \(acc : Natural) -> acc * ncoderoom + coderoom r) 0
let ncoderooms = pw ncoderoom nrooms
let codepos = \(x : post) -> (coderooms x.rooms) * ncodespaces + codespaces x.spaces
let ncodepos = ncodespaces * ncoderooms


let solve = \(inp : inpt) ->
  let rest = Optional Natural
  let pos0 = {rooms = prelude.List.map le roomt roomt.initial inp.rooms, spaces = prelude.List.replicate nspaces spacet (None enum)}
  let code0 = codepos pos0
  let m = m1w Natural (mkm1 Natural ([] : List (kvt Natural)))
  let ops = wrapperops Natural
--  in (convcb rest Natural ( \(repr : Type) -> \(ops : mapops {repr = repr, v = Natural}) -> \(m : repr) -> 
  in   Some 1
--    let st = \(repr : Type) -> {res : rest, curd : Natural, m : repr}
--    let stcb = {cb : st -> forall (repr : Type) -> forall (ops : mapops {repr = repr, v = Natural}) -> repr -> st} 
--    let step = \(s : st) -> if prelude.Bool.not (prelude.Optional.null Natural s.res) then s else
      
--    in (prelude.Natural.fold 2 st step {f = ..., res : rest, q = ...}).cb repr ops m
--  )) (m1 Natural).repr (_m1ops Natural) (mkm1 Natural ([{key = code0, value = 0}]))

in solve ./01.dhall
