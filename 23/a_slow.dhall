let prelude = ../prelude.dhall

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

let inpt = {rooms : List (List enum)}

let ex : inpt = ./01.dhall
let ex0 : inpt = ./00.dhall
let ex1 : inpt = ./001.dhall

let le = List enum
let roomt = < initial : le | filling : le >
let spacet = Optional enum
let mapt = {rooms : List roomt, spaces : List spacet}

let nspaces = 2 + 3 + 2
let nrooms = 4

let conv = \(inp : inpt) ->
  {
    spaces = prelude.List.replicate nspaces (Optional enum) (None enum),
    rooms = prelude.List.map le roomt roomt.initial inp.rooms
  }

let rle = \(r : roomt) ->
  merge {
    initial = prelude.Function.identity le,
    filling = prelude.Function.identity le
  } r

let sre = \(s : spacet) ->
  merge {
    None = [] : le,
    Some = \(e : enum) -> [e]
  } s

let it = \(t : Type) -> {index : Natural, value : t}

let combinations = \(n : Natural) -> \(t : Type) -> \(l : List t) ->
  let rest = List (List t)
  let step = \(r : rest) ->
    let f = \(r : List t) ->
      let g = \(x : t) -> [x] # r
      in (prelude.List.map t (List t) g l) : rest
    in (prelude.List.concatMap (List t) (List t) f r) : rest
  in prelude.Natural.fold n rest step ([[] : List t] : rest)

let solve = \(inp : inpt) ->
  let ri = \(i : Natural) -> prelude.Optional.default le ([] : le) (prelude.List.head le (prelude.List.drop i le inp.rooms))
  let r1 = ri 0
  let r2 = ri 1
  let r3 = ri 2
  let r4 = ri 3
  let getrs = \(e : enum) -> \(l : List enum) -> 
    (prelude.List.map le roomt roomt.filling [[] : List enum, [e], [e, e]])
    #
    (prelude.List.map le roomt roomt.initial [l, prelude.List.drop 1 enum l])
  let r1s = getrs A r1
  let r2s = getrs B r2
  let r3s = getrs C r3
  let r4s = getrs D r4
  let spaces = [None enum, Some A, Some B, Some C, Some D]
  let mspaces = combinations nspaces spacet spaces
  let lm = List mapt
  let ls = List spacet
  let lr = List roomt
  let toofullf = \(f : List Natural -> Bool) -> \(rr : lr) -> \(ss : ls) ->
    let l = (prelude.List.concatMap roomt enum rle rr) # (prelude.List.concatMap spacet enum sre ss)
    let l = prelude.List.map enum Natural e2i l
    let toofull = \(e : enum) ->
      let e = e2i e
      let ll = prelude.List.filter Natural (prelude.Natural.equal e) l
      in f ll
    in prelude.Bool.or (prelude.List.map enum Bool toofull [A,B,C,D])
  let toofull = toofullf (prelude.Function.compose (List Natural) Natural Bool (prelude.List.length Natural) (prelude.Natural.lessThan 2))
  let somemissing = toofullf (prelude.Function.compose (List Natural) Natural Bool (prelude.List.length Natural) (prelude.Natural.greaterThan 2))
  let mspaces = prelude.List.filter (List spacet) (prelude.Function.compose ls Bool Bool (toofull ([] : lr)) prelude.Bool.not) mspaces
  let maps =
    let stepr1 = \(r1 : roomt) -> \(acc : lm) -> --if toofull [r1] ([] : ls) then acc else
      let stepr2 = \(r2 : roomt) -> \(acc : lm) -> --if toofull [r1, r2] ([] : ls) then acc else
        let stepr3 = \(r3 : roomt) -> \(acc : lm) -> --if toofull [r1, r2, r3] ([] : ls) then acc else
          let stepr4 = \(r4 : roomt) -> \(acc : lm) -> --if toofull [r1, r2, r3, r4] ([] : ls) then acc else
            let stepss = \(ss : ls) -> \(acc : lm) -> if toofull [r1, r2, r3, r4] ss then acc
              else if somemissing [r1, r2, r3, r4] ss then acc else
                [{spaces = ss, rooms = [r1, r2, r3, r4]}] # acc
            in prelude.List.fold ls mspaces lm stepss acc 
          in prelude.List.fold roomt r4s lm stepr4 acc
        in prelude.List.fold roomt r3s lm stepr3 acc
      in prelude.List.fold roomt r2s lm stepr2 acc
    in prelude.List.fold roomt r1s lm stepr1 ([] : lm)
  in prelude.List.length Natural (prelude.Natural.enumerate 50000000) --prelude.List.length mapt maps

in solve ex
