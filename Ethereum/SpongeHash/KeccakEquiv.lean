import Ethereum.SpongeHash.Keccak256
import Ethereum.SpongeHash.KeccakSpec
import Init.Data.Range.Lemmas
import Init.Control.Lawful.Basic
import Mathlib.Tactic.SplitIfs

namespace Ethereum.Keccak256

open KeccakSpec

/-!
Equivalence between the imperative Keccak-256 in `Keccak256.lean` and the
specification in `KeccakSpec.lean`.

These lemmas reduce the imperative loops to folds and identify the tables,
padding, and lane decoding. `KeccakHash.lean` transports the folds onto
`KeccakSpec` and proves `hash input = KeccakSpec.keccak256 input`.
-/

/-! ### Loops as folds -/

theorem id_forIn'_range'_eq_foldl {β : Type} (start n : Nat) (init : β)
    (body : Nat → β → β) :
    (forIn' (List.range' start n) init fun a _ b =>
      (do
        pure PUnit.unit
        pure (ForInStep.yield (body a b)) : Id (ForInStep β)))
    =
    (pure (List.foldl (fun b a => body a b) init (List.range' start n)) : Id β) := by
  induction n generalizing start init with
  | zero => simp [List.range'_zero, List.foldl_nil]
  | succ n ih =>
    simp only [List.range'_succ, List.forIn'_cons, pure_bind, List.foldl_cons]
    exact ih (start + 1) (body start init)

theorem forIn'_yield_range'_eq_foldl {β : Type} (start n : Nat) (init : β)
    (body : Nat → β → β) :
    (forIn' (List.range' start n) init fun a _ b =>
      (pure (ForInStep.yield (body a b)) : Id (ForInStep β)))
    =
    (pure (List.foldl (fun b a => body a b) init (List.range' start n)) : Id β) := by
  induction n generalizing start init with
  | zero => simp [List.range'_zero, List.foldl_nil]
  | succ n ih =>
    simp only [List.range'_succ, List.forIn'_cons, pure_bind, List.foldl_cons]
    exact ih (start + 1) (body start init)

theorem forIn'_of_pure_yield {β : Type} (start n : Nat) (init : β)
    (body : Nat → β → β) :
    (forIn' (List.range' start n) init fun a _ b =>
      (do
        let r ← (pure (body a b) : Id β)
        pure PUnit.unit
        pure (ForInStep.yield r) : Id (ForInStep β))) =
      (pure (List.foldl (fun b a => body a b) init (List.range' start n)) : Id β) := by
  simp only [pure_bind, forIn'_yield_range'_eq_foldl]

def toLanes (s : State) : Lanes :=
  Vector.ofFn fun i => (s[i]).toBitVec

/-! ### Tables -/

theorem rotationOffsets_eq_spec :
    rotationOffsets = Vector.ofFn fun i : Fin 25 =>
      rotationOffset (coords i).1 (coords i).2 := by
  decide +revert

set_option maxRecDepth 20000 in
theorem roundConstants_eq_spec (i : Fin 24) :
    (roundConstants[i]).toBitVec = roundConstant i := by
  match i with
  | ⟨0, _⟩ => decide +revert
  | ⟨1, _⟩ => decide +revert
  | ⟨2, _⟩ => decide +revert
  | ⟨3, _⟩ => decide +revert
  | ⟨4, _⟩ => decide +revert
  | ⟨5, _⟩ => decide +revert
  | ⟨6, _⟩ => decide +revert
  | ⟨7, _⟩ => decide +revert
  | ⟨8, _⟩ => decide +revert
  | ⟨9, _⟩ => decide +revert
  | ⟨10, _⟩ => decide +revert
  | ⟨11, _⟩ => decide +revert
  | ⟨12, _⟩ => decide +revert
  | ⟨13, _⟩ => decide +revert
  | ⟨14, _⟩ => decide +revert
  | ⟨15, _⟩ => decide +revert
  | ⟨16, _⟩ => decide +revert
  | ⟨17, _⟩ => decide +revert
  | ⟨18, _⟩ => decide +revert
  | ⟨19, _⟩ => decide +revert
  | ⟨20, _⟩ => decide +revert
  | ⟨21, _⟩ => decide +revert
  | ⟨22, _⟩ => decide +revert
  | ⟨23, _⟩ => decide +revert
  | ⟨n + 24, h⟩ => omega

theorem rotateLeft_toBitVec (w : UInt64) {n : Nat} (hn : n < 64) :
    (rotateLeft w n).toBitVec = w.toBitVec.rotateLeft n := by
  unfold rotateLeft
  by_cases h0 : n = 0
  · simp [h0, BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.shiftLeft_zero,
      BitVec.ushiftRight_eq_zero]
  · simp [h0, BitVec.rotateLeft, BitVec.rotateLeftAux, UInt64.shiftLeft, UInt64.shiftRight]
    have hdiv : 64 ∣ 2 ^ 64 := by decide
    rw [show ((UInt64.ofNat n).mod (64 : UInt64)).toNat = n % 64 by
      simp [UInt64.mod, UInt64.toNat_ofNat, Nat.mod_mod_of_dvd _ hdiv]]
    rw [show ((UInt64.ofNat (64 - n)).mod (64 : UInt64)).toNat = 64 - n % 64 by
      simp [UInt64.mod, UInt64.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 64 - n < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 64 - n < 64),
        Nat.mod_eq_of_lt hn]]

theorem id_vector_forIn_yield {α : Type} {β : Type} {n : Nat}
    (xs : Vector α n) (init : β) (f : α → β → β) :
    (do
        let r ← forIn xs init fun a r => do
          pure PUnit.unit
          pure (ForInStep.yield (f a r))
        pure r : Id β)
    = xs.toArray.attach.foldl (fun acc p => f p.1 acc) init := by
  simp only [forIn_eq_forIn', Bind.bind, Pure.pure]
  simpa using Array.forIn'_pure_yield_eq_foldl (xs := xs.toArray)
    (fun a _ b => f a b) init

theorem permute_eq_foldl (s : State) :
    permute s = roundConstants.toArray.attach.foldl (fun acc p => round acc p.1) s := by
  unfold permute
  simp only [Id.run, id_vector_forIn_yield]

theorem finalBlock_eq (input : ByteArray) :
    finalBlock input (input.size / rateBytes * rateBytes) = KeccakSpec.finalBlock input := by
  have hrem : input.size - input.size / rateBytes * rateBytes = input.size % rateBytes := by
    have h := Nat.div_add_mod input.size rateBytes
    unfold rateBytes at h ⊢
    omega
  unfold rateBytes at hrem
  ext i
  simp [finalBlock, KeccakSpec.finalBlock, KeccakSpec.finalByte, Vector.getElem_ofFn, hrem,
    KeccakSpec.padByte, KeccakSpec.rateBytes, rateBytes]
  by_cases hzero : input.size % 136 = 0
  · simp [hzero]
    split_ifs <;> first | rfl | omega
  · simp [hzero]
    split_ifs with hlt heq hlast
    · have hidx : input.size / 136 * 136 + i = input.size - input.size % 136 + i := by omega
      rw [hidx]
      rw [getElem!_pos input (input.size - input.size % 136 + i) (by omega)]
    all_goals (first | rfl | omega)

theorem messageBlock_eq (input : ByteArray) (k : Nat) (hk : k < input.size / rateBytes) :
    blockAt input (k * rateBytes) = KeccakSpec.messageBlock input (k * rateBytes) := by
  ext j
  have hidx : k * 136 + j < input.size := by
    unfold rateBytes at hk
    omega
  simp [blockAt, KeccakSpec.messageBlock, Vector.getElem_ofFn, rateBytes, KeccakSpec.rateBytes, hidx]

/-! ### Lane decoding -/

theorem shiftLeft_toBitVec (w : UInt64) {n : Nat} (hn : n < 64) :
    (w.shiftLeft n.toUInt64).toBitVec = w.toBitVec <<< n := by
  simp [UInt64.shiftLeft]
  have hdiv : 64 ∣ 2 ^ 64 := by decide
  rw [show ((UInt64.ofNat n).mod (64 : UInt64)).toNat = n by
    simp [UInt64.mod, UInt64.toNat_ofNat, Nat.mod_mod_of_dvd _ hdiv, Nat.mod_eq_of_lt hn]]

theorem shiftRight_toBitVec (w : UInt64) {n : Nat} (hn : n < 64) :
    (w.shiftRight n.toUInt64).toBitVec = w.toBitVec >>> n := by
  simp [UInt64.shiftRight]
  have hdiv : 64 ∣ 2 ^ 64 := by decide
  rw [show ((UInt64.ofNat n).mod (64 : UInt64)).toNat = n by
    simp [UInt64.mod, UInt64.toNat_ofNat, Nat.mod_mod_of_dvd _ hdiv, Nat.mod_eq_of_lt hn]]

theorem uint8_toUInt64_toBitVec (a : UInt8) :
    a.toUInt64.toBitVec = BitVec.ofNat 64 a.toNat := by
  apply BitVec.eq_of_toNat_eq
  unfold UInt8.toUInt64 UInt8.toNat
  simp [BitVec.toNat_ofNat]

theorem decodeLane_eq_foldl (block : Block) (i : Nat) :
    decodeLane block i =
      (List.range' 0 8).foldl (fun acc j =>
        acc ||| block[Fin.ofNat 136 (8 * i + j)].toUInt64.shiftLeft (8 * j).toUInt64) 0 := by
  unfold decodeLane
  simp only [forIn_eq_forIn', Std.Legacy.Range.forIn'_eq_forIn'_range',
    id_forIn'_range'_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  simp only [Id.run, Pure.pure, Bind.bind]

theorem decode_prefix_toBitVec (block : Block) (i k : Nat) (_hi : i < 17) (hk : k ≤ 8) :
    ((List.range' 0 k).foldl (fun acc j =>
      acc ||| block[Fin.ofNat 136 (8 * i + j)].toUInt64.shiftLeft (8 * j).toUInt64) 0).toBitVec =
    (List.range' 0 k).foldl (fun acc j =>
      acc ||| (BitVec.ofNat 64 (block[Fin.ofNat 136 (8 * i + j)]).toNat <<< (8 * j))) 0 := by
  induction k with
  | zero => simp [List.range'_zero, List.foldl_nil]
  | succ k ih =>
    have hk' : k < 8 := by omega
    have hshift : 8 * k < 64 := by omega
    simp only [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    have hor : ∀ (a b : UInt64), (a ||| b).toBitVec = a.toBitVec ||| b.toBitVec := by
      intro a b
      change (UInt64.lor a b).toBitVec = a.toBitVec ||| b.toBitVec
      rfl
    rw [hor, ih (by omega)]
    rw [shiftLeft_toBitVec _ hshift, uint8_toUInt64_toBitVec]

theorem spec_decodeLane_eq_foldl (block : Block) (i : Fin 17) :
    KeccakSpec.decodeLane block i =
      (List.range' 0 8).foldl (fun acc j =>
        acc ||| (BitVec.ofNat 64 (block[Fin.ofNat 136 (8 * i.val + j)]).toNat <<< (8 * j))) 0 := by
  simp [KeccakSpec.decodeLane, KeccakSpec.rateBytes]

theorem decodeLane_toBitVec (block : Block) (i : Fin 17) :
    (decodeLane block i.val).toBitVec = KeccakSpec.decodeLane block i := by
  rw [decodeLane_eq_foldl, spec_decodeLane_eq_foldl, decode_prefix_toBitVec _ _ _ i.isLt (by omega)]

/-! ### One round -/

def columnValue (state : State) (x : Nat) : UInt64 :=
  lane state x 0 ^^^ lane state x 1 ^^^ lane state x 2 ^^^ lane state x 3 ^^^ lane state x 4

def columnsFold (state : State) : Vector UInt64 5 :=
  (List.range' 0 5).foldl (fun columns x =>
    let index := Fin.ofNat 5 x
    columns.set index.val (columnValue state x) index.isLt) (Vector.replicate 5 0)

def thetaValue (state : State) (columns : Vector UInt64 5) (x y : Nat) : UInt64 :=
  lane state x y ^^^
    (columns[Fin.ofNat 5 (x + 4)] ^^^ rotateLeft columns[Fin.ofNat 5 (x + 1)] 1)

def thetaFold (state : State) (columns : Vector UInt64 5) : State :=
  (List.range' 0 5).foldl (fun acc y =>
    (List.range' 0 5).foldl (fun acc x =>
      let index := laneIndex x y
      acc.set index.val (thetaValue state columns x y) index.isLt) acc) state

def piValue (afterTheta : State) (x y : Nat) : UInt64 :=
  rotateLeft (lane afterTheta x y) rotationOffsets[laneIndex x y]

def rhoPiFold (afterTheta : State) : State :=
  (List.range' 0 5).foldl (fun acc y =>
    (List.range' 0 5).foldl (fun acc x =>
      let destination := laneIndex y (2 * x + 3 * y)
      acc.set destination.val (piValue afterTheta x y) destination.isLt) acc)
    (Vector.replicate 25 0)

def chiValue (afterPi : State) (x y : Nat) : UInt64 :=
  lane afterPi x y ^^^
    ((~~~lane afterPi ((x + 1) % 5) y) &&& lane afterPi ((x + 2) % 5) y)

def chiFold (afterPi : State) : State :=
  (List.range' 0 5).foldl (fun acc y =>
    (List.range' 0 5).foldl (fun acc x =>
      let index := laneIndex x y
      acc.set index.val (chiValue afterPi x y) index.isLt) acc) afterPi

def roundFold (state : State) (roundConstant : UInt64) : State :=
  let columns := columnsFold state
  let afterTheta := thetaFold state columns
  let afterPi := rhoPiFold afterTheta
  let afterChi := chiFold afterPi
  afterChi.set 0 (afterChi[0] ^^^ roundConstant)

theorem round_eq_fold (state : State) (roundConstant : UInt64) :
    round state roundConstant = roundFold state roundConstant := by
  unfold round roundFold columnsFold thetaFold rhoPiFold chiFold
    columnValue thetaValue piValue chiValue
  -- Reduce inner loops before `pure_bind`, which would erase the shape the
  -- fold lemma matches. Two passes cover the nested 5×5 loops.
  simp only [forIn_eq_forIn', Std.Legacy.Range.forIn'_eq_forIn'_range',
    id_forIn'_range'_eq_foldl, forIn'_of_pure_yield, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [Id.run, Pure.pure, Bind.bind]

theorem toBitVec_xor (a b : UInt64) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := by
  change (UInt64.xor a b).toBitVec = a.toBitVec ^^^ b.toBitVec
  rfl

theorem toBitVec_and (a b : UInt64) : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := by
  change (UInt64.land a b).toBitVec = a.toBitVec &&& b.toBitVec
  rfl

theorem toBitVec_not (a : UInt64) : (~~~a).toBitVec = ~~~a.toBitVec := by
  change (UInt64.complement a).toBitVec = ~~~a.toBitVec
  rfl

theorem laneIndex_val {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (laneIndex x y).val = x + 5 * y := by
  simp [laneIndex, Fin.ofNat, Nat.mod_eq_of_lt (show x + 5 * y < 25 by omega)]

theorem lane_toBitVec (s : State) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (lane s x y).toBitVec = KeccakSpec.lane (toLanes s) ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [lane, KeccakSpec.lane, toLanes, Vector.getElem_ofFn, laneIdx, laneIndex_val hx hy]

theorem columns_prefix_get (state : State) (k : Nat) (hk : k ≤ 5) (j : Nat) (hj : j < 5) :
    ((List.range' 0 k).foldl (fun columns x =>
      let index := Fin.ofNat 5 x
      columns.set index.val (columnValue state x) index.isLt) (Vector.replicate 5 0))[j] =
    if j < k then columnValue state j else 0 := by
  induction k with
  | zero =>
    simp [List.range'_zero, List.foldl_nil, Vector.getElem_replicate]
  | succ k ih =>
    have hk' : k < 5 := by omega
    rw [show List.range' 0 (k + 1) = List.range' 0 k ++ [0 + k] from List.range'_1_concat]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    have hval : (Fin.ofNat 5 k).val = k := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt hk']
    simp only [hval]
    rw [Vector.getElem_set]
    by_cases hjk : k = j
    · simp [hjk]
    · simp [hjk]
      have hpre := ih (by omega)
      simp only [Fin.ofNat] at hpre
      rw [hpre]
      by_cases hlt : j < k
      · simp [hlt, show j < k + 1 by omega]
      · have hge : ¬ j < k + 1 := by
          intro hlt'
          have : j = k := by omega
          exact hjk this.symm
        simp [hlt, hge]

theorem columnsFold_get (state : State) (x : Fin 5) :
    (columnsFold state)[x] = columnValue state x.val := by
  have h := columns_prefix_get state 5 (by omega) x.val x.isLt
  simpa [columnsFold] using h

theorem columnsFold_toBitVec (state : State) (x : Fin 5) :
    ((columnsFold state)[x]).toBitVec = column (toLanes state) x := by
  rw [columnsFold_get]
  unfold columnValue column
  rw [toBitVec_xor, toBitVec_xor, toBitVec_xor, toBitVec_xor]
  rw [lane_toBitVec state (x := x.val) (y := 0) x.isLt (by decide)]
  rw [lane_toBitVec state (x := x.val) (y := 1) x.isLt (by decide)]
  rw [lane_toBitVec state (x := x.val) (y := 2) x.isLt (by decide)]
  rw [lane_toBitVec state (x := x.val) (y := 3) x.isLt (by decide)]
  rw [lane_toBitVec state (x := x.val) (y := 4) x.isLt (by decide)]
  simp [Fin.eta]

theorem row_prefix_get (f : Nat → Nat → UInt64) (init : State) (y k : Nat)
    (hy : y < 5) (hk : k ≤ 5) (j : Nat) (hj : j < 25) :
    ((List.range' 0 k).foldl (fun acc x =>
      let index := laneIndex x y
      acc.set index.val (f x y) index.isLt) init)[j] =
    if 5 * y ≤ j ∧ j < 5 * y + k then f (j - 5 * y) y else init[j] := by
  induction k generalizing init with
  | zero =>
    simp [List.range'_zero, List.foldl_nil]
    intro hle hlt
    omega
  | succ k ih =>
    have hk' : k < 5 := by omega
    rw [show List.range' 0 (k + 1) = List.range' 0 k ++ [0 + k] from List.range'_1_concat]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    have hidx : (laneIndex k y).val = k + 5 * y := laneIndex_val hk' hy
    simp only [hidx]
    rw [Vector.getElem_set]
    by_cases hjk : k + 5 * y = j
    · have hj : j = k + 5 * y := hjk.symm
      subst hj
      simp
      intro h
      omega
    · simp [hjk]
      have hpre := ih init (by omega)
      simp only [] at hpre
      rw [hpre]
      by_cases hspan : 5 * y ≤ j ∧ j < 5 * y + k
      · simp [hspan, show 5 * y ≤ j ∧ j < 5 * y + (k + 1) by omega]
      · have hnew : ¬ (5 * y ≤ j ∧ j < 5 * y + (k + 1)) := by
          intro h
          have : j = k + 5 * y := by omega
          exact hjk this.symm
        simp [hspan, hnew]

theorem grid_foldl_get (f : Nat → Nat → UInt64) (init : State) (rows : Nat)
    (hrows : rows ≤ 5) (j : Nat) (hj : j < 25) :
    ((List.range' 0 rows).foldl (fun acc y =>
      (List.range' 0 5).foldl (fun acc x =>
        let index := laneIndex x y
        acc.set index.val (f x y) index.isLt) acc) init)[j] =
    if j < 5 * rows then f (j % 5) (j / 5) else init[j] := by
  induction rows generalizing init with
  | zero =>
    simp [List.range'_zero, List.foldl_nil]
  | succ rows ih =>
    have hy : rows < 5 := by omega
    rw [show List.range' 0 (rows + 1) = List.range' 0 rows ++ [0 + rows] from List.range'_1_concat]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    rw [row_prefix_get f _ rows 5 hy (by decide) j hj]
    by_cases hrow : 5 * rows ≤ j ∧ j < 5 * rows + 5
    · simp [hrow]
      have hdiv : j / 5 = rows := by omega
      have hmod : j % 5 = j - 5 * rows := by omega
      simp [hdiv, hmod]
      intro h
      omega
    · simp [hrow]
      have hpre := ih (init := init) (by omega)
      simp only [] at hpre
      rw [hpre]
      by_cases hlt : j < 5 * rows
      · simp [hlt, show j < 5 * (rows + 1) by omega]
      · have hge : ¬ j < 5 * (rows + 1) := by
          intro hlt'
          exact hrow ⟨by omega, by omega⟩
        simp [hlt, hge]

theorem thetaFold_get (state : State) (columns : Vector UInt64 5) (j : Nat) (hj : j < 25) :
    (thetaFold state columns)[j] = thetaValue state columns (j % 5) (j / 5) := by
  unfold thetaFold
  rw [grid_foldl_get (thetaValue state columns) state 5 (by decide) j hj]
  simp [show j < 5 * 5 by omega]

theorem chiFold_get (afterPi : State) (j : Nat) (hj : j < 25) :
    (chiFold afterPi)[j] = chiValue afterPi (j % 5) (j / 5) := by
  unfold chiFold
  rw [grid_foldl_get (chiValue afterPi) afterPi 5 (by decide) j hj]
  simp [show j < 5 * 5 by omega]

end Ethereum.Keccak256
