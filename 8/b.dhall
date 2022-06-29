let enum = < a | b | c | d | e | f | g>
let a = enum.a
let b = enum.b
let c = enum.c
let d = enum.d
let e = enum.e
let f = enum.f
let g = enum.g

let ledt = List enum
let listt = List ledt
let lrt = {left : listt, right : listt }
let inpt = List lrt

let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let ex : inpt = ./03.dhall

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

let mapet = {_1 : enum, _2 : enum}
let mapt = List mapet

let ecost = \(x : enum) -> merge {
    a = 1,
    b = 2,
    c = 4,
    d = 8,
    e = 16,
    f = 32,
    g = 64,
  } x

let escost = \(x : List enum) -> prelude.Natural.sum (prelude.List.map enum Natural ecost x)

let digitt = {d : Natural, ledCost : Natural}

let digits = [
{d = 0, ledCost = escost [a,b,c,e,f,g]},
{d = 1, ledCost = escost [c,f]},
{d = 2, ledCost = escost [a,c,d,e,g]},
{d = 3, ledCost = escost [a,c,d,f,g]},
{d = 4, ledCost = escost [b,c,d,f]},
{d = 5, ledCost = escost [a,b,d,f,g]},
{d = 6, ledCost = escost [a,b,d,e,f,g]},
{d = 7, ledCost = escost [a,c,f]},
{d = 8, ledCost = escost [a,b,c,d,e,f,g]},
{d = 9, ledCost = escost [a,b,c,d,f,g]},
] : List digitt

let cost2digit = \(x : Natural) -> prelude.List.head Natural (prelude.List.map digitt Natural (\(x : digitt) -> x.d) (prelude.List.filter digitt (\(y : digitt) -> prelude.Natural.equal y.ledCost x) digits))

let applymap = \(m : mapt) -> \(l : List enum) -> prelude.List.map enum enum (\(z : enum) -> prelude.Optional.default enum a (prelude.List.head enum (prelude.List.map mapet enum (\(x : mapet) -> x._2) (prelude.List.filter mapet (\(x : mapet) -> prelude.Natural.equal (ecost z) (ecost x._1)) m)))) l

let solve1 = \(lr : lrt) ->
  let ag = [a,b,c,d,e,f,g]
  let f = \(l : List enum) -> prelude.List.zip enum ag enum l
  let maps = prelude.List.map (List enum) mapt f (perms enum ag)
  let solve2 = \(m : mapt) ->
    let decode = \(l : List enum) -> cost2digit ( escost ( applymap m l ) )
    let allok = \(l : List (Optional Natural)) -> prelude.Bool.not (prelude.Bool.or (prelude.List.map (Optional Natural) Bool (prelude.Optional.null Natural) l))
    let picks = prelude.List.map (List enum) (Optional Natural) decode lr.left
    let num = \(l : List Natural) -> prelude.List.foldLeft Natural l Natural (\(acc : Natural) -> \(x : Natural) -> acc * 10 + x) 0
    in if allok picks then Some (num (prelude.List.map (Optional Natural) Natural (prelude.Optional.default Natural 0) (prelude.List.map (List enum) (Optional Natural) decode lr.right))) else None Natural
  let ok = \(t : Type) -> \(x : Optional t) -> prelude.Bool.not (prelude.Optional.null t x)
  let oks = prelude.List.filter (Optional Natural) (ok Natural) (prelude.List.map mapt (Optional Natural) solve2 maps)
  in prelude.Optional.default Natural 0 (prelude.List.head Natural (prelude.List.map (Optional Natural) Natural (prelude.Optional.default Natural 0) oks))

let solve = \(inp : inpt) ->
  prelude.Natural.sum (prelude.List.map lrt Natural solve1 inp)


let tex = assert : solve ex === 5353
let tex2 = assert : solve ./02.dhall === 61229

in solve ./input.dhall
--in perms Natural [1,2, 3]

--let tex = assert : solve ex === 26

--in solve ./input.dhall
