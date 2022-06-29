let enum = < A|B|C|D>
let A = enum.A
let B = enum.B
let C = enum.C
let D = enum.D
in {
  rooms = [
    [B, A],
    [A, B],
    [C, C],
    [D, D],
  ],
}
