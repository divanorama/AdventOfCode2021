let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let inpt = {p1 : Natural, p2 : Natural}

let ex : inpt = ./01.dhall

let wrap11 = \(x : Natural) -> if prelude.Natural.lessThan x 11 then x else (1 + (prelude.Natural.subtract 11 x))
let wrap10 = \(x : Natural) -> if prelude.Natural.lessThan x 10 then x else (prelude.Natural.subtract 10 x)

let solve = \(inp : inpt) ->
  let pt = { points : Natural, pos : Natural }
  let gt = { p1 : pt, p2 : pt, turn : Natural, die : Natural }
--  let st = < game : gt | res : gt >
  let st = < game : gt | res : Natural >
  let step = \(s : st) ->
    merge {
      res = \(x : Natural) -> s,
--      res = \(x : gt) -> s,
      game = \(g : gt) ->
        if prelude.Natural.lessThanEqual 1000 g.p2.points then st.res (3 * g.turn * g.p1.points) else
--        if prelude.Natural.lessThanEqual 1000 g.p1.points then st.res g else
          let pos1 = wrap11 (g.p1.pos + g.die)
          let point1 = g.p1.points + pos1
          let die1 = wrap10 (g.die + 9)
          in st.game {p1 = g.p2, p2 = {pos = pos1, points = point1}, die = die1, turn = g.turn + 1}
    } s
  in prelude.Natural.fold 1000 st step (st.game {p1 = {points = 0, pos = inp.p1}, p2 = {points = 0, pos = inp.p2}, turn = 0, die = 6})

in solve ./input.dhall
