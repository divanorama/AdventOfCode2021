let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let vi = List Integer
let inpt = List (List vi)

let dott = {x : Integer, y : Integer, z : Integer}
let ldott = List dott

let dotf = dott -> dott

let projx = \(d : dott) -> d.x
let projy = \(d : dott) -> d.y
let projz = \(d : dott) -> d.z

let att = \(t : Type) -> \(d : t) -> \(i : Natural) -> \(l : List t) -> prelude.Optional.default t d (prelude.List.head t (prelude.List.drop i t l))

let fact = \(n : Natural) -> prelude.List.foldLeft Natural (prelude.Natural.enumerate n) Natural (\(acc : Natural) -> \(x : Natural) -> acc * (x + 1)) 1

let bdiv = \(n : Natural) -> \(a : Natural) -> \(b : Natural) ->
  let f = \(x : Natural) -> prelude.Natural.lessThanEqual (b * x) a 
  let lst = prelude.List.filter Natural f (prelude.List.reverse Natural (prelude.Natural.enumerate n))
  in prelude.Optional.default Natural 0 (prelude.List.head Natural lst)

let perms = \(t : Type) -> \(l : List t) ->
  let n = prelude.List.length t l
  let n1 = n + 1
  let facts = prelude.List.reverse Natural (prelude.List.map Natural Natural fact (prelude.Natural.enumerate n))
  let st = { res : List t, l : List t, rst : Natural }
  let step = \(s : st) -> \(z : Natural) ->
    let i = bdiv n1 s.rst z
    in { 
      res = (prelude.List.take 1 t (prelude.List.drop i t s.l)) # s.res, 
      rst = prelude.Natural.subtract (i * z) s.rst,
      l = (prelude.List.take i t s.l) # (prelude.List.drop (i + 1) t s.l)
    }
  let perm = \(x : Natural) -> (prelude.List.foldLeft Natural facts st step { res = [] : List t, l = l, rst = x }).res
  in prelude.List.map Natural (List t) perm (prelude.Natural.enumerate (fact n))

let e1 = {x = +1, y = +0, z = +0 }
let e2 = {x = +0, y = +1, z = +0 }
let e3 = {x = +0, y = +0, z = +1 }

let sp = \(a : dott) -> \(b : dott) ->
  prelude.Integer.add (prelude.Integer.add (prelude.Integer.multiply a.x b.x) (prelude.Integer.multiply a.y b.y)) (prelude.Integer.multiply a.z b.z)

let vp = \(a : dott) -> \(b : dott) -> {
  x = prelude.Integer.subtract (prelude.Integer.multiply a.z b.y) (prelude.Integer.multiply a.y b.z),
  y = prelude.Integer.subtract (prelude.Integer.multiply a.x b.z) (prelude.Integer.multiply a.z b.x),
  z = prelude.Integer.subtract (prelude.Integer.multiply a.y b.x) (prelude.Integer.multiply a.x b.y),
}
  

let det = \(e1 : dott) -> \(e2 : dott) -> \(e3 : dott) ->
  sp e3 (vp e1 e2)

let dotfs = 
  let doti = dott -> Integer
  let ldoti = List doti
  let conv = \(l : ldoti) -> \(d : dott) -> {x = (att doti projx 0 l) d, y = (att doti projy 1 l) d, z = (att doti projz 2 l) d}
  let refls = \(x : ldoti) ->
    let refls = \(z : Natural) ->
      let pt = {_1 : Natural, _2 : doti}
      let xx = prelude.List.zip Natural [4,2,1] doti x
      let st = {rem : Natural, res : ldoti}
      let step = \(s : st) -> \(f : pt) ->
        if prelude.Natural.lessThanEqual f._1 s.rem then {rem = prelude.Natural.subtract f._1 s.rem, res = s.res # [prelude.Function.compose dott Integer Integer f._2 prelude.Integer.negate]}
        else { rem = s.rem, res = s.res # [f._2] }
      in (prelude.List.foldLeft pt xx st step {rem = z, res = [] : ldoti}).res
    in prelude.List.map Natural ldoti refls (prelude.Natural.enumerate 8)
  let nomirror = \(f : dotf) ->
    let a = f {x = +1, y = +0, z = +0 }
    let b = f {x = +0, y = +1, z = +0 }
    let c = f {x = +0, y = +0, z = +1 }
    in prelude.Integer.equal +1 (det a b c)
  in prelude.List.filter dotf nomirror (prelude.List.map ldoti dotf conv (prelude.List.concatMap ldoti ldoti refls (perms doti [projx, projy, projz])))

let conv = \(l : vi) -> 
  { x = att Integer +0 0 l, y = att Integer +0 1 l, z = att Integer +0 2 l}

let ex : inpt = ./01.dhall

let elem = \(x : Natural) -> \(l : List Natural) ->
  prelude.Bool.or (prelude.List.map Natural Bool (prelude.Natural.equal x) l)

let dir = \(a : dott) -> \(b : dott) -> {x = prelude.Integer.subtract a.x b.x, y = prelude.Integer.subtract a.y b.y, z = prelude.Integer.subtract a.z b.z}
let add = \(a : dott) -> \(b : dott) -> {x = prelude.Integer.add a.x b.x, y = prelude.Integer.add a.y b.y, z = prelude.Integer.add a.z b.z}

let rngt = {mn : Integer, mx : Integer}
let getrng = \(l : List Integer) ->
  let go = \(f : Integer -> Integer -> Bool) ->
    let x0 = att Integer +0 0 l
    let f = \(bst : Integer) -> \(x : Integer) -> if f x bst then x else bst
    in prelude.List.foldLeft Integer l Integer f x0
  in { mn = go prelude.Integer.lessThan, mx = go prelude.Integer.greaterThan }

let freqt = {value : Natural, times : Natural}
let freqs = \(l : List Natural) ->
  let l = prelude.Natural.sort l
  let st = {cur : freqt, res : List freqt}
  let step = \(s : st) -> \(x : Natural) ->
    if prelude.Natural.equal x s.cur.value then { cur = {value = s.cur.value, times = 1 + s.cur.times} , res = s.res}
    else { cur = {value = x, times = 1}, res = [s.cur] # s.res }
  let r = prelude.List.foldLeft Natural l st step {cur = {value = att Natural 0 0 l,times = 0}, res = [] : List freqt}
  in [r.cur] # r.res

let dotcnt = \(l : ldott) ->
  let getrng = \(f : dott -> Integer) -> getrng (prelude.List.map dott Integer f l)
  let rngw = \(a : rngt) -> 1 + (prelude.Integer.abs (prelude.Integer.subtract a.mn a.mx))
  let rx = getrng projx
  let xw = rngw rx 
  let ry = getrng projy
  let yw = rngw ry
  let rz = getrng projz
  let zw = rngw rz
  let torng = \(r : rngt) -> \(x : Integer) -> prelude.Integer.abs (prelude.Integer.subtract r.mn x)
  let code = \(d : dott) ->
    let xx = torng rx d.x
    let yy = torng ry d.y
    let zz = torng rz d.z
    in zz + zw * (yy + yw * xx)
  let nums = freqs (prelude.List.map dott Natural code l)
  in { code = code, nums = nums } 

let attempt = \(a : ldott) -> \(b : ldott) ->
  let f = \(b : dott) -> prelude.List.map dott dott (dir b) a
  let vecs = prelude.List.concatMap dott dott f b 
  let cnts = dotcnt vecs
  let okf = \(x : freqt) -> prelude.Natural.lessThanEqual 12 x.times
  let oks = prelude.List.filter freqt okf cnts.nums
  in merge {
    None = None ldott,
    Some = \(x : freqt) -> 
      let v = prelude.Optional.default dott {x=+0,y=+0,z=+0} (prelude.List.head dott (prelude.List.filter dott (\(v : dott) -> prelude.Natural.equal x.value (cnts.code v)) vecs))
      in Some (prelude.List.map dott dott (add v) b)
  } (prelude.List.head freqt oks)


let unopt = \(t : Type) -> \(l : List (Optional t)) ->
  let f = \(acc : List t) -> \(x : Optional t) ->
    merge {
      None = acc,
      Some = \(x : t) -> [x] # acc
    } x
  in prelude.List.reverse t (prelude.List.foldLeft (Optional t) l (List t) f ([] : List t))

let solve = \(inp : inpt) ->
  let inp = prelude.List.map (List vi) (List dott) (prelude.List.map vi dott conv) inp
  let n = prelude.List.length ldott inp
  let elemt = { i : Natural, minj : Natural, dots : ldott }
  let st = { q : List elemt, saw : List Natural, beacons : ldott }
  let dfs = \(s : st) -> let rq = prelude.List.drop 1 elemt s.q
    in merge {
      None = s,
      Some = \(hd : elemt) -> if prelude.Natural.lessThanEqual n hd.minj then {q = rq, saw = s.saw, beacons = s.beacons} else
        if elem hd.minj s.saw then {q = [{i = hd.i, minj = hd.minj + 1, dots = hd.dots }] # rq, saw = s.saw, beacons = s.beacons} else
          let to = att ldott ([] : ldott) hd.minj inp
          let rots = prelude.List.map dotf ldott (\(f : dotf) -> prelude.List.map dott dott f to) dotfs
          let rotres = prelude.List.map ldott (Optional ldott) (attempt hd.dots) rots
          let oks = unopt ldott rotres
          in merge {
            None = {q = [{i = hd.i, minj = hd.minj + 1, dots = hd.dots }] # rq, saw = s.saw, beacons = s.beacons},
            Some = \(tos : ldott) -> {q = [{i = hd.minj, minj = 1, dots = tos}, {i = hd.i, minj = hd.minj + 1, dots = hd.dots }] # rq, saw = [hd.minj] # s.saw, beacons = tos # s.beacons}
          } (prelude.List.head ldott oks)
        
    } (prelude.List.head elemt s.q) 
  let d0 = att ldott ([] : ldott) 0 inp
  in prelude.List.length freqt (dotcnt (prelude.Natural.fold (n * n) st dfs { q = [{i = 0, minj = 1, dots = d0}], saw = [0], beacons = d0}).beacons).nums
--  let d1 = prelude.List.map dott dott (att dotf (prelude.Function.identity dott) 6 dotfs) (att ldott ([] : ldott) 1 inp)
--  let f = \(b : dott) -> prelude.List.map dott dott (dir b) d0
--  let vecs = prelude.List.concatMap dott dott f d1 
--  let getrng = \(f : dott -> Integer) -> getrng (prelude.List.map dott Integer f vecs)
--  let rngw = \(a : rngt) -> 1 + (prelude.Integer.abs (prelude.Integer.subtract a.mn a.mx))
--  let rx = getrng projx
--  let xw = rngw rx 
--  let ry = getrng projy
--  let yw = rngw ry
--  let rz = getrng projz
--  let zw = rngw rz
--  let torng = \(r : rngt) -> \(x : Integer) -> prelude.Integer.abs (prelude.Integer.subtract r.mn x)
--  let code = \(d : dott) ->
--    let xx = torng rx d.x
--    let yy = torng ry d.y
--    let zz = torng rz d.z
--    in zz + zw * (yy + yw * xx)
--  let nums = freqs (prelude.List.map dott Natural code vecs)
--  let okf = \(x : freqt) -> prelude.Natural.lessThanEqual 12 x.times
--  let oks = prelude.List.filter freqt okf nums
--  let rots = prelude.List.map dotf ldott (\(f : dotf) -> prelude.List.map dott dott f d1) dotfs
--  let rotres = prelude.List.map ldott (Optional ldott) (attempt d0) rots
--  in unopt ldott rotres --attempt d0 d1

--in solve ex
in solve ./input.dhall
--in det e1 e2 e3
--in solve ./00.dhall
--in dotfs
--in getrng [+1,+2,-1,-2,+3,-3]
--in freqs [1,2,3,3,2,1,2,2,2,4]
