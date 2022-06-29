let prelude = ../prelude.dhall

-- IntMap

let cmbt = \(t : Type) -> (t -> t -> t)
let monot = \(t : Type) -> {cmb : cmbt t, zero : t}
let nodeinfo = \(e : Type) -> {min : Natural, max : Natural, extra : e}
let combinfos = \(e : Type) -> \(em : monot e) -> \(a : nodeinfo e) -> \(b : nodeinfo e) -> {
  min = prelude.Natural.min a.min b.min,
  max = prelude.Natural.max a.max b.max,
  extra = em.cmb a.extra b.extra,
}
let joininfos = \(e : Type) -> \(em : monot e) -> \(l : List (nodeinfo e)) -> 
  merge {
    None = {min = 0, max = 0, extra = em.zero},
    Some = \(x : nodeinfo e) -> prelude.List.fold (nodeinfo e) l (nodeinfo e) (combinfos e em) x
  } (prelude.List.head (nodeinfo e) l)
let mapt = { repr : Type, v : Type, e : Type }
let growt = \(t : Type) -> < fits : t | extend : List t >
let grow2l = \(t : Type) -> \(x : growt t) ->
  merge {
    fits = \(x : t) -> [x],
    extend = prelude.Function.identity (List t),
  } x
let shrinkt = \(t : Type) -> < fits : t | shrink : t >
let _mapops = \(m : mapt) -> {
  upsert  : m.repr -> Natural -> (Optional m.v -> m.v) -> growt m.repr,
  get     : m.repr -> Natural -> Optional m.v,
--  remove  : m.repr -> Natural -> shrinkt m.repr,
  join    : m.repr -> m.repr -> growt m.repr,
  getinfo : m.repr -> nodeinfo m.e,
}


let kvt = \(v : Type) -> \(e : Type) -> {key : Natural, value : v, extra : e}
let getk = \(v : Type) -> \(e : Type) -> \(x : kvt v e) -> x.key
let getv = \(v : Type) -> \(e : Type) -> \(x : kvt v e) -> x.value
let getextra = \(v : Type) -> \(e : Type) -> \(x : kvt v e) -> x.extra

let n = 8
let n2 = 4

let m1 = \(v : Type) -> \(e : Type) -> { repr = {info : nodeinfo e, nodes : List (kvt v e)}, v = v, e = e}
let mkm1 = \(v : Type) -> \(e : Type) -> \(em : monot e) -> \(l : List (kvt v e)) -> {
  nodes = l,
  info = (joininfos e em) (prelude.List.map (kvt v e) (nodeinfo e) (\(x : kvt v e) -> {min = x.key, max = x.key, extra = x.extra}) l),
} : (m1 v e).repr
let _m1ops = \(v : Type) -> \(e : Type) -> \(em : monot e) -> \(kv2e : Natural -> v -> e) ->
  let repr = (m1 v e).repr
  let kvt = kvt v e
  let getv = getv v e
  let nodeinfo = nodeinfo e
  let split = \(x : repr) -> prelude.List.map (List kvt) repr (mkm1 v e em) [prelude.List.take n2 kvt x.nodes, prelude.List.drop n2 kvt x.nodes]
  let withgrow = \(res : repr) ->
    if prelude.Natural.lessThan n (prelude.List.length kvt res.nodes) then (growt repr).extend (split res)
    else (growt repr).fits res
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
        let z = let v = f vb._1 in {key = k, value = v, extra = kv2e k v}
        let b = vb._2
        let res = { nodes = a # [z] # b, info = {min = prelude.Natural.min z.key m.info.min, max = prelude.Natural.max z.key m.info.max, extra = em.cmb z.extra m.info.extra}}
        in withgrow res,
    join = \(a : repr) -> \(b : repr) ->
      let res = { nodes = a.nodes # b.nodes, info = combinfos e em a.info b.info }        
      in withgrow res,
--    remove = \(m : repr) -> \(k : Natural) ->
--      let nodes = prelude.List.filter kvt (prelude.Function.compose kvt Natural Bool (getk v e) (prelude.Natural.equal k)) m.nodes
--      let res = mkm1 v e em nodes
--      in if prelude.Natural.lessThan 1 (prelude.List.length kvt nodes) then (shrinkt repr).fits res else (shrinkt repr).shrink res 
  } : _mapops (m1 v e)

let m2 = \(m : mapt) -> { repr = {info : nodeinfo m.e, nodes : List m.repr}, v = m.v, e = m.e } : mapt

let mkm2 = \(m : mapt) -> \(em : monot m.e) -> \(ops : _mapops m) -> \(l : List m.repr) -> {
  info = joininfos m.e em (prelude.List.map m.repr (nodeinfo m.e) ops.getinfo l),
  nodes = l,
} : (m2 m).repr

let droplast = \(t : Type) -> \(l : List t) ->
  let n = prelude.List.length t l
  in prelude.List.take (prelude.Natural.subtract 1 n) t l

let _m2ops = \(prev : mapt) -> \(em : monot prev.e) -> \(ops : _mapops prev) -> 
  let repr = (m2 prev).repr
  let v = prev.v
  let ov = Optional v
  let split = \(l : List prev.repr) -> prelude.List.map (List prev.repr) repr (mkm2 prev em ops) [prelude.List.take n2 prev.repr l, prelude.List.drop n2 prev.repr l]
  let maybegrow = \(res : repr) ->
    if prelude.Natural.lessThan n (prelude.List.length prev.repr res.nodes) then (growt repr).extend (split res.nodes)
    else (growt repr).fits res
  in {
    getinfo = \(m : repr) -> m.info,
    get = 
      let unopt = \(x : Optional ov) -> merge {
        None = None prev.v,
        Some = prelude.Function.identity ov,
      } x
      let inr = \(k : Natural) -> \(i : nodeinfo prev.e) -> prelude.Bool.and [prelude.Natural.lessThanEqual i.min k, prelude.Natural.lessThanEqual k i.max]
      let f = \(k : Natural) -> \(p : prev.repr) -> inr k (ops.getinfo p)
      in \(m : repr) -> \(k : Natural) -> unopt (prelude.List.head ov (prelude.List.map prev.repr ov (\(m : prev.repr) -> ops.get m k) (prelude.List.filter prev.repr (f k) m.nodes))),
    upsert =
      let pf = \(k : Natural) -> \(x : prev.repr) -> prelude.Natural.lessThanEqual (ops.getinfo x).min k
      in \(m : repr) -> \(k : Natural) -> \(f : ov -> v) -> 
        let pt = prelude.List.partition prev.repr (pf k) m.nodes
        let a = pt.true
        let b = pt.false
        let acb = merge {
          None = {a = droplast prev.repr a, c = prelude.List.concatMap prev.repr prev.repr (prelude.Function.compose prev.repr (growt prev.repr) (List prev.repr) (\(m : prev.repr) -> ops.upsert m k f) (grow2l prev.repr)) (prelude.Optional.toList prev.repr (prelude.List.last prev.repr a)), b = b},
          Some = \(hd : prev.repr) -> {a = a, c = grow2l prev.repr (ops.upsert hd k f), b = prelude.List.drop 1 prev.repr b},
        } (prelude.List.head prev.repr b)
        let a = acb.a
        let b = acb.b
        let c = acb.c
        let res = {nodes = a # c # b, info = joininfos (prev.e) em (prelude.List.map prev.repr (nodeinfo prev.e) ops.getinfo (a # c # b))}
        in maybegrow res
      ,
    join = \(a : repr) -> \(b : repr) ->
      let res = {nodes = a.nodes # b.nodes, info = combinfos prev.e em a.info b.info}
      in maybegrow res
      ,
--    remove = \(m : repr) -> \(k : Natural) -> (shrinkt repr).fits m -- XXX
  } : _mapops (m2 prev)

let mapops = \(v : Type) -> \(repr : Type) -> {
  get : repr -> Natural -> Optional v,
  upsert : repr -> Natural -> (Optional v -> v) -> repr,
--  remove : repr -> Natural -> repr,
}

let mapcb = \(x : Type) -> \(v : Type) -> \(e : Type) -> forall (repr : Type) -> forall (ops : _mapops {repr = repr, v = v, e = e}) -> forall (m : repr) -> x
let wrapper = \(v : Type) -> \(e : Type) -> {
  get : Natural -> Optional v,
  callback : forall (x : Type) -> forall (cb : mapcb x v e) -> x,
}

let m1w = \(v : Type) -> \(e : Type) -> \(em : monot e) -> \(kv2e : Natural -> v -> e) -> \(m : (m1 v e).repr) -> let ops = _m1ops v e em kv2e in {
  get = ops.get m,
  callback = \(x : Type) -> \(cb : mapcb x v e) -> cb (m1 v e).repr ops m,
} : (wrapper v e)

let wrapperops = \(v : Type) -> \(e : Type) -> \(em : monot e) -> let wt = wrapper v e in {
  get = \(w : wt) -> w.get,
  upsert = \(w : wt) -> \(k : Natural) -> \(f : Optional v -> v) ->
    w.callback wt (\(repr : Type) -> \(ops : _mapops {repr = repr, v = v, e = e}) -> \(m : repr) -> 
      {
        get = ops.get m,
        callback = \(x : Type) -> \(cb : mapcb x v e) -> (
          merge {
            fits = cb repr ops,
            extend = \(l : List repr) ->
              let m2 = m2 {repr=repr, v = v, e=e}
              let ops2 = _m2ops {repr=repr, v = v, e=e} em ops
              in cb m2.repr ops2 (mkm2 {repr=repr, v=v,e=e} em ops l)
          } (ops.upsert m k f)
        ) : x
      } : wt),
--  remove = \(w : wt) -> \(k : Natural) ->
--    w.callback wt (\(repr : Type) -> \(ops : _mapops {repr = repr, v = v, e = e}) -> \(m : repr) -> 
--      {
--        get = ops.get m,
--        callback = \(x : Type) -> \(cb : mapcb x v e) -> (
--          merge {
--            fits = cb repr ops,
--            shrink = \(r : repr) -> cb repr ops r --- XXX
--          } (ops.remove m k)
--        ) : x
--      } : wt),
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
  let v = Natural
  let e = {minval : Natural, minvalkey : Natural}
  let em = {cmb= (\(a : e) -> \(b : e) -> if prelude.Natural.lessThan a.minval b.minval then a else b), zero = {minval = 0, minvalkey = 0}}
  let kv2e = \(k : Natural) -> \(x : v) -> {minval = x, minvalkey = k}
  let m = m1w v e em kv2e (mkm1 v e em ([] : List (kvt v e)))
  let ops = wrapperops v e em
--  in (convcb rest Natural ( \(repr : Type) -> \(ops : mapops {repr = repr, v = Natural}) -> \(m : repr) -> 
  let f = \(i : Natural) -> \(m : wrapper v e) -> ops.upsert m i (\(_ : Optional v) -> i)
--  in  ops.get (prelude.List.fold Natural (prelude.Natural.enumerate 50000) (wrapper v e) f m) 12 --ops.upsert m 1 (\(_ : Optional Natural) -> 2)
  in  prelude.List.fold Natural (prelude.Natural.enumerate 4) (wrapper v e) f m --ops.upsert m 1 (\(_ : Optional Natural) -> 2)
--    let st = \(repr : Type) -> {res : rest, curd : Natural, m : repr}
--    let stcb = {cb : st -> forall (repr : Type) -> forall (ops : mapops {repr = repr, v = Natural}) -> repr -> st} 
--    let step = \(s : st) -> if prelude.Bool.not (prelude.Optional.null Natural s.res) then s else
      
--    in (prelude.Natural.fold 2 st step {f = ..., res : rest, q = ...}).cb repr ops m
--  )) (m1 Natural).repr (_m1ops Natural) (mkm1 Natural ([{key = code0, value = 0}]))

in solve ./01.dhall
