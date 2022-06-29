let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let rngt = {mn : Integer, mx : Integer}
let itemt = {on : Bool, x : rngt, y : rngt, z : rngt}
let inpt = List itemt

let ex : inpt = ./01.dhall
let ex2 : inpt = ./02.dhall

let xrange = \(r : rngt) ->
  let n = 1 + (prelude.Integer.abs (prelude.Integer.subtract r.mn r.mx))
  let f = \(i : Natural) -> prelude.Integer.add r.mn (prelude.Natural.toInteger i)
  in prelude.List.map Natural Integer f (prelude.Natural.enumerate n)

let rW = {mn = -50, mx = +50}

let solve = \(inp : inpt) ->
  let sane1 = \(r : rngt) -> prelude.Bool.and [ prelude.Integer.lessThanEqual -50 r.mx, prelude.Integer.lessThanEqual r.mn +50]
  let sane = \(i : itemt) -> prelude.Bool.and [ sane1 i.x, sane1 i.y, sane1 i.z]
  let inp = prelude.List.filter itemt sane inp
  let xr = xrange rW
  let yr = xrange rW
  let zr = xrange rW
  let inr = \(r : rngt) -> \(t : Integer) -> prelude.Bool.and [ prelude.Integer.lessThanEqual r.mn t, prelude.Integer.lessThanEqual t r.mx ]
  let on = \(x : Integer) -> \(y : Integer) -> \(z : Integer) ->
    let f = \(i : itemt) -> \(res : Optional Bool) -> if prelude.Bool.not (prelude.Optional.null Bool res) then res else
      if prelude.Bool.and [ inr i.x x, inr i.y y, inr i.z z ] then Some (i.on) else res
    let res = prelude.List.fold itemt inp (Optional Bool) f (None Bool)
    in prelude.Optional.default Bool False res
  let acct = Natural
  let doacc = \(a : acct) -> \(x : Integer) -> \(y : Integer) -> \(z : Integer) -> a + 1
  let acc0 = 0
--  let acct = List (List Integer)
--  let doacc = \(a : acct) -> \(x : Integer) -> \(y : Integer) -> \(z : Integer) -> [[x,y,z]] # a
--  let acc0 = [] : acct
  let stepx = \(x : Integer) -> \(acc : acct) ->
    let stepy = \(y : Integer) -> \(acc : acct) ->
      let stepz = \(z : Integer) -> \(acc : acct) ->
        if on x y z then doacc acc x y z else acc
      in prelude.List.fold Integer zr acct stepz acc
    in prelude.List.fold Integer yr acct stepy acc
  in prelude.List.fold Integer xr acct stepx acc0
--  in prelude.List.length itemt inp

--in solve ex
in solve ./input.dhall
