let inpt = List Natural

let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let map = prelude.Map.Type

let statet = map Natural Natural
let stateet = prelude.Map.Entry Natural Natural
let inc = \(d : Natural) -> \(x : Natural) -> \(m : map Natural Natural) ->
  let iskey = \(kv : stateet) -> prelude.Natural.equal kv.mapKey x
  in merge {
    None = [{mapKey = x, mapValue = d}] # m,
    Some = \(kv : stateet) -> prelude.List.map stateet stateet (\(kv : stateet) -> if iskey kv then {mapKey = x, mapValue = kv.mapValue + d} else kv) m
  } (prelude.List.head stateet (prelude.List.filter stateet iskey m)) : map Natural Natural
let dec = \(d : Natural) -> \(x : Natural) -> \(m : map Natural Natural) ->
  let iskey = \(kv : stateet) -> prelude.Natural.equal kv.mapKey x
  in merge {
    None = m,
    Some = \(kv : stateet) -> prelude.List.map stateet stateet (\(kv : stateet) -> if iskey kv then {mapKey = x, mapValue = prelude.Natural.subtract d kv.mapValue} else kv) m
  } (prelude.List.head stateet (prelude.List.filter stateet iskey m)) : map Natural Natural

let conv = \(lst : List Natural) -> prelude.List.fold Natural lst statet (inc 1) ([] : statet) : statet


let ex : inpt = ./01.dhall

let score = \(s : statet) -> prelude.Natural.sum (prelude.List.map stateet Natural (\(kv : stateet) -> kv.mapValue) s)

let act = \(s : statet) ->
  let addt = {plus : Natural, to : Natural}
  let addf = \(kv : stateet) -> if prelude.Natural.equal 0 kv.mapKey then [{plus= kv.mapValue, to = 8},{plus=kv.mapValue, to = 6}] else [{plus = kv.mapValue, to= prelude.Natural.subtract 1 kv.mapKey}]
  let adds = prelude.List.concatMap stateet addt addf s
  let s1 = prelude.List.fold addt adds statet (\(a : addt) -> \(acc : statet) -> inc a.plus a.to acc) s
  let subt = {sub : Natural, to : Natural}
  let subf = \(kv : stateet) -> {sub = kv.mapValue, to = kv.mapKey}
  let subs = prelude.List.map stateet subt subf s
  let s2 = prelude.List.fold subt subs statet (\(a : subt) -> \(acc : statet) -> dec a.sub a.to acc) s1
  in s2

let solve = \(inp : inpt) ->
  let state0 = conv inp
  in score (prelude.Natural.fold 256 statet act state0)

let tex = assert : solve ex === 26984457539

in solve ./input.dhall
