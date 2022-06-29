let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let e = < op | cl | x : Natural >

let itemt = { x : Natural, d : Natural }
let numt = List itemt


let conv = \(l : List e) ->
  let st = { d : Natural, res : numt }
  let f = \(s : st) -> \(c : e) ->
    merge {
      op = {d = s.d + 1, res = s.res},
      cl = {d = prelude.Natural.subtract 1 s.d, res = s.res},
      x = \(x : Natural) -> {d = s.d, res = s.res # [{x = x, d = s.d}]}
    } c
  in (prelude.List.foldLeft e l st f {d = 0, res = [] : numt} ).res

let iadd = \(x : Natural) -> \(c : itemt) -> { x = c.x + x, d = c.d }
let dinc = \(c : itemt) -> { x = c.x, d = c.d + 1 }
let zinc = prelude.List.map itemt itemt dinc

let it = {index : Natural, value : itemt}
let zind = \(z : numt) -> \(f : it -> Bool) -> 
  prelude.List.head Natural (prelude.List.map it Natural (\(x : it) -> x.index) (prelude.List.filter it f (prelude.List.indexed itemt z)))
let zit = \(z : numt) -> \(i : Natural) ->
  prelude.Optional.default itemt {x=0,d=0} (prelude.List.head itemt (prelude.List.drop i itemt z))

let explode = \(z : numt) ->
  let it = {index : Natural, value : itemt}
  let i = zind z (\(x : it) -> prelude.Natural.lessThanEqual 5 x.value.d)
  in merge {
    None = None numt,
    Some = \(i : Natural) -> 
      let a = zit z i
      let b = zit z (i + 1)
      in Some (
        (prelude.List.take (prelude.Natural.subtract 1 i) itemt z) #
        (prelude.List.map itemt itemt (iadd a.x) (prelude.List.drop (prelude.Natural.subtract 1 i) itemt (prelude.List.take i itemt z)) ) # 
        [{x=0, d = prelude.Natural.subtract 1 a.d}] # 
        (prelude.List.map itemt itemt (iadd b.x) (prelude.List.take 1 itemt (prelude.List.drop (i + 2) itemt z)) ) # 
        (prelude.List.drop (i + 3) itemt z)
      )
  } i

let div2 = \(x : Natural) ->
  let r = prelude.Optional.default Natural 0 (prelude.List.head Natural (prelude.List.filter Natural (\(i : Natural) -> prelude.Natural.lessThanEqual x (2 * i)) (prelude.Natural.enumerate x)))
  let l = prelude.Natural.subtract r x
  in {l = l, r = r}

let split = \(z : numt) ->
  let i = zind z (\(x : it) -> prelude.Natural.lessThanEqual 10 x.value.x)
  in merge {
    None = None numt,
    Some = \(i : Natural) -> 
      let a = zit z i
      let lr = div2 a.x
      in Some (
        (prelude.List.take i itemt z) #
        [{x = lr.l, d = a.d + 1}, {x = lr.r, d = a.d + 1}] #
        (prelude.List.drop (i + 1) itemt z)
      )
  } i

let norm = \(z : numt) ->
  let st = { cur : numt, res : Optional numt }
  let steps = 1 + 40 * (prelude.List.length itemt z)
  let step = \(s : st) -> if prelude.Bool.not (prelude.Optional.null numt s.res) then s else
    merge {
      None = merge {
        None = {cur = s.cur, res = Some s.cur},
        Some = \(z : numt) -> {cur = z, res = None numt},
      } (split s.cur),
      Some = \(z : numt) -> {cur = z, res = None numt},
    } (explode s.cur)
  in (prelude.Natural.fold steps st step {cur = z, res = None numt}).res

let add = \(a : numt) -> \(b : numt) ->
  let c = (zinc a) # (zinc b)
  in norm c

let magn = \(z : numt) ->
  let steps = prelude.List.length itemt z
  let step = \(z : numt) -> if prelude.Natural.lessThanEqual (prelude.List.length itemt z) 1 then z else
    let maxd = prelude.Optional.default Natural 0 (prelude.Natural.listMax (prelude.List.map itemt Natural (\(x : itemt) -> x.d) z))
    let i = prelude.Optional.default Natural 0 (zind z (\(x : it) -> prelude.Natural.equal x.value.d maxd))
    let a = zit z i
    let b = zit z (i + 1)
    in (prelude.List.take i itemt z) #
       [{d = prelude.Natural.subtract 1 a.d, x = 3 * a.x + 2 * b.x}] #
       (prelude.List.drop (i + 2) itemt z)
  let zz = prelude.Natural.fold steps numt step z
  in (prelude.Optional.default itemt {x=0,d=0} (prelude.List.head itemt zz)).x : Natural

let solve = \(inp : List (List e)) ->
  let inp = prelude.List.map (List e) numt conv inp
  let it = {index : Natural, value : numt}
  let iinp = prelude.List.indexed numt inp
  let itera = \(cur : Natural) -> \(a : it) -> 
    let iterb = \(cur : Natural) -> \(b : it) ->
      if prelude.Natural.equal a.index b.index then cur else
        let z : Natural = merge {
          None = 0,
          Some = magn
        } (add a.value b.value)
        in prelude.Natural.max z cur
    in prelude.List.foldLeft it iinp Natural iterb cur
  in prelude.List.foldLeft it iinp Natural itera 0

--in solve ./01.dhall
in solve ./input.dhall
--let foo = conv [e.op, e.x 10, e.x 20, e.cl]
--in add foo foo
--in div2 6
