let prelude = https://prelude.dhall-lang.org/v21.1.0/package.dhall sha256:0fed19a88330e9a8a3fbe1e8442aa11d12e38da51eb12ba8bcb56f3c25d0854a

let enum = < h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | hA | hB | hC | hD | hE | hF >
let h0 = enum.h0
let h1 = enum.h1
let h2 = enum.h2
let h3 = enum.h3
let h4 = enum.h4
let h5 = enum.h5
let h6 = enum.h6
let h7 = enum.h7
let h8 = enum.h8
let h9 = enum.h9
let hA = enum.hA
let hB = enum.hB
let hC = enum.hC
let hD = enum.hD
let hE = enum.hE
let hF = enum.hF

let h2b = \(x : enum) -> merge {
  h0 = [0,0,0,0],
  h1 = [0,0,0,1],
  h2 = [0,0,1,0],
  h3 = [0,0,1,1],
  h4 = [0,1,0,0],
  h5 = [0,1,0,1],
  h6 = [0,1,1,0],
  h7 = [0,1,1,1],
  h8 = [1,0,0,0],
  h9 = [1,0,0,1],
  hA = [1,0,1,0],
  hB = [1,0,1,1],
  hC = [1,1,0,0],
  hD = [1,1,0,1],
  hE = [1,1,1,0],
  hF = [1,1,1,1],
} x

let inpt = List enum
let bitst = List Natural

let conv = prelude.List.concatMap enum Natural h2b

let ex0 : inpt = [hD,h2,hF,hE,h2,h8,]
let ex01 : inpt = [h3,h8,h0,h0,h6,hF,h4,h5,h2,h9,h1,h2,h0,h0,]
let ex1 : inpt = [hE,hE,h0,h0,hD,h4,h0,hC,h8,h2,h3,h0,h6,h0,]
let exx1 : inpt = [h8,hA,h0,h0,h4,hA,h8,h0,h1,hA,h8,h0,h0,h2,hF,h4,h7,h8,]
let exx2 : inpt = [h6,h2,h0,h0,h8,h0,h0,h0,h1,h6,h1,h1,h5,h6,h2,hC,h8,h8,h0,h2,h1,h1,h8,hE,h3,h4,]
let exx3 : inpt = [hC,h0,h0,h1,h5,h0,h0,h0,h0,h1,h6,h1,h1,h5,hA,h2,hE,h0,h8,h0,h2,hF,h1,h8,h2,h3,h4,h0,]
let exx4 : inpt = [hA,h0,h0,h1,h6,hC,h8,h8,h0,h1,h6,h2,h0,h1,h7,hC,h3,h6,h8,h6,hB,h1,h8,hA,h3,hD,h4,h7,h8,h0,]

let ylim = \(n : Natural) -> \(a : Type) -> \(b : Type) -> \(f : (a -> b) -> a -> b) -> \(f0 : a -> b) ->
  prelude.Natural.fold n (a -> b) f f0
  
let eop = < single | listop >

let parset = \(t : Type) -> bitst -> { res : t, rest : bitst, read : Natural }
let readN = \(n : Natural) -> \(l : bitst) -> { res = prelude.List.take n Natural l, rest = prelude.List.drop n Natural l, read = n }
let b2dec = \(l : bitst) -> prelude.List.foldLeft Natural l Natural (\(acc : Natural) -> \(x : Natural) -> acc * 2 + x) 0
let readV : parset Natural = \(l : bitst) ->
  let vr = readN 3 l
  in { res = b2dec vr.res, rest = vr.rest, read = vr.read }
let readT : parset eop = \(l : bitst) ->
  let vr = readN 3 l
  in { res = if prelude.Natural.equal 4 (b2dec vr.res) then eop.single else eop.listop, rest = vr.rest, read = vr.read }
let readBit : parset Bool = \(l : bitst) ->
  let br = readN 1 l
  in { res = prelude.Natural.equal 1 (prelude.Optional.default Natural 0 (prelude.List.head Natural br.res)), rest = br.rest, read = br.read }
let readLen : parset Natural = \(l : bitst) ->
  let xr = readN 15 l
  in { res = b2dec xr.res, rest = xr.rest, read = xr.read }
let readNum : parset Natural = \(l : bitst) ->
  let xr = readN 11 l
  in { res = b2dec xr.res, rest = xr.rest, read = xr.read }
let readLit : parset Natural = \(l : bitst) ->
  let xr = readN 4 l
  in { res = b2dec xr.res, rest = xr.rest, read = xr.read }

let solve = \(inp : bitst) ->
  let n = prelude.List.length Natural inp
  let rest = Natural
  let argt = < num : Natural | pos : Natural | bit >
  let opt = { kind : eop, args : List rest, restspec : argt }
  let statet = { stack : List opt, inp : bitst, pos : Natural }
  let rootop = { kind = eop.listop, args = [0], restspec = argt.num 2 }
  let performSingle = \(l : List rest) -> prelude.Natural.sum l : rest
  let performListop = \(l : List rest) -> prelude.Natural.sum l : rest
  let topOp = \(stack : List opt) -> prelude.Optional.default opt rootop (prelude.List.head opt stack)
  let propagate = \(x : rest) -> \(l : List opt) ->
    let o = topOp l
    in [{ kind = o.kind, args = o.args # [x], restspec = o.restspec }] # (prelude.List.drop 1 opt l)
  let isFull = \(p : Natural) -> \(o : opt) -> merge {
      bit = False,
      num = \(n : Natural) -> prelude.Natural.equal (prelude.List.length rest o.args) (n + 1),
      pos = prelude.Natural.equal p,
    } o.restspec
  let step = \(s : statet) -> if prelude.Bool.and [prelude.List.null Natural s.inp, prelude.Natural.equal 1 (prelude.List.length opt s.stack)] then s else
    let curop = topOp s.stack 
    in merge {
      single =
        let br = readBit s.inp
        let xr = readLit br.rest
        in 
          if br.res then { stack = s.stack, inp = xr.rest, pos = s.pos + br.read + xr.read } 
                    else { stack = propagate (performSingle curop.args) (prelude.List.drop 1 opt s.stack), inp = xr.rest, pos = s.pos + br.read + xr.read }
        ,
      listop = if isFull s.pos curop then { stack = propagate (performListop curop.args) (prelude.List.drop 1 opt s.stack), inp = s.inp, pos = s.pos } else
        let vr = readV s.inp
        let tr = readT vr.rest
        in merge {
          single = { stack = [{ kind = eop.single, args = [vr.res], restspec = argt.bit }] # s.stack, inp = tr.rest, pos = s.pos + vr.read + tr.read },
          listop =
            let ar = readBit tr.rest
            in
              if ar.res then
                let nr = readNum ar.rest
                in { stack = [{ kind = eop.listop, args = [vr.res], restspec = argt.num nr.res }] # s.stack, inp = nr.rest, pos = s.pos + vr.read + tr.read + ar.read + nr.read }
              else
                let lr = readLen ar.rest
                let newpos = s.pos + vr.read + tr.read + ar.read + lr.read
                in { stack = [{ kind = eop.listop, args = [vr.res], restspec = argt.pos (newpos + lr.res) }] # s.stack, inp = lr.rest, pos = newpos }
        } tr.res
    } curop.kind
  in prelude.Natural.fold n statet step { stack = [rootop], inp = inp, pos = 0 }

in solve (conv ./input.dhall)
--in conv exx3
