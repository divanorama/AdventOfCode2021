let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let rngt = {mn : Natural, mx : Natural}
let inpt = {x : rngt, ny : rngt}
let ex : inpt = ./01.dhall

let irngt = {mn : Integer, mx : Integer}

let ienum = \(r : irngt) -> prelude.List.map Natural Integer (\(x : Natural) -> prelude.Integer.add r.mn (prelude.Natural.toInteger x)) (prelude.Natural.enumerate (1 + (prelude.Integer.abs (prelude.Integer.subtract r.mn r.mx))))

let nmax = \(a : Natural) -> \(b : Natural) -> if prelude.Natural.lessThan a b then b else a
let omax = \(a : Optional Natural) -> \(b : Optional Natural) ->
  merge {
    None = b,
    Some = \(a : Natural) -> merge {
        None = Some a,
        Some = \(b : Natural) -> Some (nmax a b)
      } b
  } a

let inr = \(r : irngt) -> \(x : Integer) -> prelude.Bool.and [ prelude.Integer.lessThanEqual r.mn x, prelude.Integer.lessThanEqual x r.mx] 

let solve = \(inp : inpt) ->
  let xr : irngt = {mn = +1, mx = prelude.Natural.toInteger inp.x.mx}
  let yr : irngt = {mn = prelude.Integer.negate (prelude.Natural.toInteger inp.ny.mx), mx = prelude.Natural.toInteger inp.ny.mx}
  let inx = inr ({mn = prelude.Natural.toInteger inp.x.mn, mx = prelude.Natural.toInteger inp.x.mx} : irngt)
  let iny = inr ({mn = prelude.Integer.negate (prelude.Natural.toInteger inp.ny.mx), mx  = prelude.Integer.negate (prelude.Natural.toInteger inp.ny.mn)} : irngt)
  let shoot = \(vx : Integer)  -> \(vy : Integer) ->
    let st = {x : Integer, y : Integer, vx : Integer, vy : Integer, res : Optional Bool, score : Natural}
    let step = \(s : st) -> 
      if prelude.Bool.not (prelude.Optional.null Bool s.res) then s else
      if prelude.Bool.or [ 
           prelude.Bool.and [ prelude.Integer.lessThanEqual s.vx +0, prelude.Bool.not (inx s.x) ],
           prelude.Integer.lessThan xr.mx s.x,
           prelude.Bool.and [ prelude.Integer.lessThan s.y yr.mn, prelude.Integer.lessThanEqual s.vy +0 ],
      ] then {x = s.x, y = s.y, vx = s.vx, vy = s.vy, res = Some False, score = s.score} else
      if prelude.Bool.and [inx s.x, iny s.y] then {x = s.x, y = s.y, vx = s.vx, vy = s.vy, res = Some True, score = s.score}
      else {x = prelude.Integer.add s.x s.vx, y = prelude.Integer.add s.y s.vy, vx = if prelude.Integer.lessThan +0 s.vx then prelude.Integer.subtract +1 s.vx else s.vx, vy = prelude.Integer.subtract +1 s.vy, res = s.res, score = if prelude.Integer.lessThan (prelude.Natural.toInteger s.score) s.y then prelude.Integer.abs s.y else s.score}
    let r = prelude.Natural.fold (inp.ny.mx * 2 + 1) st step { x = +0, y = +0, vx = vx, vy = vy, res = None Bool, score = 0 }
    in merge {
      None = None Natural,
      Some = \(b : Bool) -> if b then Some r.score else None Natural
    } r.res
    
  let itery = \(s : Optional Natural) -> \(vy : Integer) ->
    let iterx = \(s : Optional Natural) -> \(vx : Integer) ->
      let cur = shoot vx vy
      in omax cur s
    in prelude.List.foldLeft Integer (ienum xr) (Optional Natural) iterx s
  in prelude.List.foldLeft Integer (ienum yr) (Optional Natural) itery (None Natural)
--  in ienum yr 

in solve ./input.dhall
