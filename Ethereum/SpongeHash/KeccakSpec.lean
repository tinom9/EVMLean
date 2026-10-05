/-!
Mathematical specification of Ethereum Keccak-256, transcribed from the
Keccak reference and FIPS 202.

This is `KECCAK[c = 512]`: Keccak-f[1600], rate 1088, capacity 512, and the
original domain suffix `0x01`. It is not SHA3-256, which uses the suffix `0x06`.

Round constants are the FIPS 202 LFSR, not a copied table. Rotation offsets are
the published `r[x, y]` matrix. The sponge steps are `θ`, `ρ`, `π`, `χ`, and `ι`,
then pad10*1, absorb, and a 256-bit squeeze.
-/

namespace Ethereum.KeccakSpec

abbrev Lane := BitVec 64
abbrev Lanes := Vector Lane 25

abbrev rateBytes : Nat := 136
abbrev digestBytes : Nat := 32

def laneIdx (x y : Fin 5) : Fin 25 :=
  ⟨x.val + 5 * y.val, by
    have := x.isLt
    have := y.isLt
    omega⟩

def lane (A : Lanes) (x y : Fin 5) : Lane :=
  A[laneIdx x y]

/-- Coordinates of lane `i` in the 5×5 state. -/
def coords (i : Fin 25) : Fin 5 × Fin 5 :=
  (⟨i.val % 5, Nat.mod_lt _ (by decide)⟩, ⟨i.val / 5, by omega⟩)

theorem laneIdx_coords (i : Fin 25) : laneIdx (coords i).1 (coords i).2 = i := by
  ext
  simp [laneIdx, coords]
  omega

/-- Published Keccak rotation offsets `r[x, y]`. -/
def rotationOffset (x y : Fin 5) : Nat :=
  match x.val, y.val with
  | 0, 0 => 0  | 1, 0 => 1  | 2, 0 => 62 | 3, 0 => 28 | 4, 0 => 27
  | 0, 1 => 36 | 1, 1 => 44 | 2, 1 => 6  | 3, 1 => 55 | 4, 1 => 20
  | 0, 2 => 3  | 1, 2 => 10 | 2, 2 => 43 | 3, 2 => 25 | 4, 2 => 39
  | 0, 3 => 41 | 1, 3 => 45 | 2, 3 => 15 | 3, 3 => 21 | 4, 3 => 8
  | 0, 4 => 18 | 1, 4 => 2  | 2, 4 => 61 | 3, 4 => 56 | 4, 4 => 14
  | _, _ => 0

theorem rotationOffset_lt_64 (x y : Fin 5) : rotationOffset x y < 64 := by
  unfold rotationOffset
  split <;> omega

/-! ### Round constants from the FIPS 202 LFSR -/

/-- One step of the FIPS 202 `rc` LFSR on an 8-bit register. -/
def lfsrStep (r : BitVec 8) : BitVec 8 :=
  let b (i : Nat) : BitVec 8 := if r.getLsbD i then 1 else 0
  b 7
    ||| (b 0 <<< 1)
    ||| (b 1 <<< 2)
    ||| (b 2 <<< 3)
    ||| ((b 3 ^^^ b 7) <<< 4)
    ||| ((b 4 ^^^ b 7) <<< 5)
    ||| ((b 5 ^^^ b 7) <<< 6)
    ||| (b 6 <<< 7)

/-- `rc(t)` from FIPS 202. The `t % 255 = 0` base case is the initial register bit. -/
def rcBit (t : Nat) : Bool :=
  let rec go (k : Nat) (r : BitVec 8) : BitVec 8 :=
    match k with
    | 0 => r
    | k + 1 => go k (lfsrStep r)
  (go (t % 255) 1#8).getLsbD 0

/-- Lane round constant `RC[ir]`, with bit `2^j - 1` equal to `rc(j + 7·ir)`. -/
def roundConstant (ir : Fin 24) : Lane :=
  let rec go (j : Nat) (acc : Lane) : Lane :=
    match j with
    | 0 => acc
    | j + 1 =>
      let bit := rcBit (j + 7 * ir.val)
      let acc := go j acc
      if bit then acc ||| (1#64 <<< (2 ^ j - 1)) else acc
  go 7 0

/-! ### Keccak-f[1600] -/

def column (A : Lanes) (x : Fin 5) : Lane :=
  lane A x 0 ^^^ lane A x 1 ^^^ lane A x 2 ^^^ lane A x 3 ^^^ lane A x 4

/-- θ: `A[x, y] := A[x, y] ⊕ C[x − 1] ⊕ rot(C[x + 1], 1)`. -/
def theta (A : Lanes) : Lanes :=
  Vector.ofFn fun i =>
    let x := (coords i).1
    let d := column A (x - 1) ^^^ (column A (x + 1)).rotateLeft 1
    A[i] ^^^ d

/-- ρ: `A[x, y] := rot(A[x, y], r[x, y])`. -/
def rho (A : Lanes) : Lanes :=
  Vector.ofFn fun i =>
    let (x, y) := coords i
    (A[i]).rotateLeft (rotationOffset x y)

/-- π: `A[x, y] := A[(x + 3y) mod 5, x]`. -/
def pi (A : Lanes) : Lanes :=
  Vector.ofFn fun i =>
    let (x, y) := coords i
    let srcX := x + 3 * y
    let srcY := x
    A[laneIdx srcX srcY]

/-- χ: `A[x, y] := A[x, y] ⊕ (¬A[x + 1, y] ∧ A[x + 2, y])`. -/
def chi (A : Lanes) : Lanes :=
  Vector.ofFn fun i =>
    let (x, y) := coords i
    lane A x y ^^^ ((~~~lane A (x + 1) y) &&& lane A (x + 2) y)

/-- ι: XOR the round constant into lane `(0, 0)`. -/
def iota (A : Lanes) (rc : Lane) : Lanes :=
  A.set 0 (A[0] ^^^ rc)

def round (A : Lanes) (rc : Lane) : Lanes :=
  iota (chi (pi (rho (theta A)))) rc

def keccakF (A : Lanes) : Lanes :=
  (List.finRange 24).foldl (fun A ir => round A (roundConstant ir)) A

/-! ### Pad10*1 with domain suffix `0x01` -/

/-- Byte `j` of a `q`-byte pad10*1 block whose first byte is the `0x01` suffix. -/
def padByte (q j : Nat) : UInt8 :=
  if q = 1 then 0x81
  else if j = 0 then 0x01
  else if j + 1 = q then 0x80
  else 0

/-- Byte `i` of the final rate block, including the `0x81` fusion. -/
def finalByte (input : ByteArray) (i : Fin rateBytes) : UInt8 :=
  let rem := input.size % rateBytes
  if rem = 0 then
    padByte rateBytes i.val
  else if h : i.val < rem then
    input[input.size - rem + i.val]'(by
      have hrem : rem ≤ input.size := Nat.mod_le _ _
      omega)
  else
    padByte (rateBytes - rem) (i.val - rem)

def finalBlock (input : ByteArray) : Vector UInt8 rateBytes :=
  Vector.ofFn (finalByte input)

def messageBlock (input : ByteArray) (offset : Nat) : Vector UInt8 rateBytes :=
  Vector.ofFn fun i =>
    if h : offset + i.val < input.size then input[offset + i.val]
    else 0

/-! ### Sponge -/

def decodeLane (block : Vector UInt8 rateBytes) (i : Fin 17) : Lane :=
  (List.range' 0 8).foldl (fun acc j =>
    acc ||| (BitVec.ofNat 64 (block[Fin.ofNat rateBytes (8 * i.val + j)]).toNat <<< (8 * j))) 0

def mixBlock (A : Lanes) (block : Vector UInt8 rateBytes) : Lanes :=
  (List.finRange 17).foldl (fun A i =>
    A.set i.val (A[i.val]'(by
      have hi : i.val < 17 := i.isLt
      omega) ^^^ decodeLane block i) (by
      have hi : i.val < 17 := i.isLt
      omega)) A

def absorbBlock (A : Lanes) (block : Vector UInt8 rateBytes) : Lanes :=
  keccakF (mixBlock A block)

def absorb (input : ByteArray) : Lanes :=
  let full := input.size / rateBytes
  let mixed :=
    (List.range full).foldl (fun A k => absorbBlock A (messageBlock input (k * rateBytes)))
      (Vector.replicate 25 0)
  absorbBlock mixed (finalBlock input)

def digest (A : Lanes) : ByteArray :=
  ByteArray.mk <| Array.ofFn fun i : Fin digestBytes =>
    let laneNumber := i.val / 8
    let byteNumber := i.val % 8
    ((A[laneNumber]'(by
      have hi : i.val < 32 := by simp [digestBytes]
      omega) >>> (8 * byteNumber)).toNat).toUInt8

/-- Ethereum Keccak-256. -/
def keccak256 (input : ByteArray) : ByteArray :=
  digest (absorb input)

private def hexDigit (n : Nat) : Char :=
  "0123456789abcdef".toList.toArray[n]!

private def hex (bytes : ByteArray) : String :=
  String.ofList <| bytes.data.toList.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

-- Kernel checks against `cast keccak`. These audit the transcription; they are
-- not the equivalence proof.
#guard hex (keccak256 ByteArray.empty) ==
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

#guard hex (keccak256 "abc".toUTF8) ==
  "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

end Ethereum.KeccakSpec
