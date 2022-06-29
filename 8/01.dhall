let enum = < a | b | c | d | e | f | g>
let a = enum.a
let b = enum.b
let c = enum.c
let d = enum.d
let e = enum.e
let f = enum.f
let g = enum.g
in {
left = [
[a,c,e,d,g,f,b,],
[c,d,f,b,e,],
[g,c,d,f,a,],
[f,b,c,a,d,],
[d,a,b,],
[c,e,f,a,b,d,],
[c,d,f,g,e,b,],
[e,a,f,b,],
[c,a,g,e,d,b,],
[a,b,],
],
right = [
[c,d,f,e,b,],
[f,c,a,d,b,],
[c,d,f,e,b,],
[c,d,b,a,f,],
]
}
