let enum = < N | C | B | H | S | O | K | P | F | V >
let N = enum.N
let C = enum.C
let B = enum.B
let H = enum.H
let S = enum.S
let O = enum.O
let K = enum.K
let P = enum.P
let F = enum.F
let V = enum.V

in {
initial = [N,N,C,B],
rules = [
{ left = C, right = H, insert = B },
{ left = H, right = H, insert = N },
{ left = C, right = B, insert = H },
{ left = N, right = H, insert = C },
{ left = H, right = B, insert = C },
{ left = H, right = C, insert = B },
{ left = H, right = N, insert = C },
{ left = N, right = N, insert = C },
{ left = B, right = H, insert = H },
{ left = N, right = C, insert = B },
{ left = N, right = B, insert = B },
{ left = B, right = N, insert = B },
{ left = B, right = B, insert = N },
{ left = B, right = C, insert = B },
{ left = C, right = C, insert = N },
{ left = C, right = N, insert = C },
]
}
