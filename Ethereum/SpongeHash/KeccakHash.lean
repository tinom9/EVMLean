import Ethereum.SpongeHash.KeccakEquiv

namespace Ethereum.Keccak256

open KeccakSpec

/-!
`hash input = KeccakSpec.keccak256 input` for every byte string.
The imperative Keccak-256 in `Keccak256.lean` matches the specification in
`KeccakSpec.lean`: one round, the 24-round permutation, pad10*1 absorption,
and the 32-byte squeeze.
-/

theorem fin_get_nat {α n} (xs : Vector α n) (i : Fin n) :
    xs[i] = xs[i.val] := by
  rfl

theorem finOfNat_sub_one (x : Fin 5) : Fin.ofNat 5 (x.val + 4) = x - 1 := by
  ext
  simp only [Fin.val_sub, Fin.ofNat]
  omega

theorem finOfNat_add_one (x : Fin 5) : Fin.ofNat 5 (x.val + 1) = x + 1 := by
  ext
  simp only [Fin.val_add, Fin.ofNat]
  omega

theorem toLanes_get (s : State) (j : Nat) (hj : j < 25) :
    (toLanes s)[j] = (s[j]).toBitVec := by
  simp [toLanes, Vector.getElem_ofFn]

theorem lane_coords_eq (A : Lanes) (j : Nat) (hj : j < 25) :
    KeccakSpec.lane A ⟨j % 5, Nat.mod_lt _ (by decide)⟩ ⟨j / 5, by omega⟩ = A[j] := by
  have hidx : (⟨j % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5).val +
      5 * (⟨j / 5, by omega⟩ : Fin 5).val = j := by
    simp
    omega
  simp [KeccakSpec.lane, laneIdx, hidx]

theorem thetaFold_toLanes (state : State) :
    toLanes (thetaFold state (columnsFold state)) = theta (toLanes state) := by
  apply Vector.ext
  intro j hj
  have hx : j % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : j / 5 < 5 := by omega
  let x : Fin 5 := ⟨j % 5, hx⟩
  rw [toLanes_get _ j hj]
  simp only [theta, Vector.getElem_ofFn, fin_get_nat]
  rw [toLanes_get state j hj]
  rw [thetaFold_get state (columnsFold state) j hj]
  unfold thetaValue
  rw [toBitVec_xor, toBitVec_xor, rotateLeft_toBitVec _ (by decide : 1 < 64)]
  rw [lane_toBitVec state hx hy]
  rw [columnsFold_toBitVec state (Fin.ofNat 5 (j % 5 + 4))]
  rw [columnsFold_toBitVec state (Fin.ofNat 5 (j % 5 + 1))]
  rw [show Fin.ofNat 5 (j % 5 + 4) = x - 1 from finOfNat_sub_one x]
  rw [show Fin.ofNat 5 (j % 5 + 1) = x + 1 from finOfNat_add_one x]
  have hcoords : (coords ⟨j, hj⟩).1 = ⟨j % 5, hx⟩ := by
    ext
    simp [coords]
  simp [hcoords, x, lane_coords_eq _ j hj, toLanes_get state j hj]

/-! ### ρ and π -/

def sourceX (j : Nat) : Nat := (j % 5 + 3 * (j / 5)) % 5

def destIndex (x y : Nat) : Nat := y + 5 * ((2 * x + 3 * y) % 5)

theorem sourceX_lt (j : Nat) : sourceX j < 5 :=
  Nat.mod_lt _ (by decide)

theorem laneIndex_rhoPi (x y : Fin 5) :
    (laneIndex y.val (2 * x.val + 3 * y.val)).val = destIndex x.val y.val := by
  decide +revert

theorem destIndex_source (j : Fin 25) :
    destIndex (sourceX j.val) (j.val % 5) = j.val := by
  decide +revert

theorem destIndex_eq_iff (x y : Fin 5) (j : Fin 25) :
    destIndex x.val y.val = j.val ↔ j.val % 5 = y.val ∧ sourceX j.val = x.val := by
  decide +revert

theorem rhoPi_row_get (afterTheta init : State) (y k : Nat) (hy : y < 5) (hk : k ≤ 5)
    (j : Nat) (hj : j < 25) :
    ((List.range' 0 k).foldl (fun acc x =>
      let destination := laneIndex y (2 * x + 3 * y)
      acc.set destination.val (piValue afterTheta x y) destination.isLt) init)[j] =
    if j % 5 = y ∧ sourceX j < k then piValue afterTheta (sourceX j) y else init[j] := by
  induction k generalizing init with
  | zero =>
    simp [List.range'_zero, List.foldl_nil]
  | succ k ih =>
    have hk' : k < 5 := by omega
    rw [show List.range' 0 (k + 1) = List.range' 0 k ++ [0 + k] from List.range'_1_concat]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    have hdest : (laneIndex y (2 * k + 3 * y)).val = destIndex k y :=
      laneIndex_rhoPi ⟨k, hk'⟩ ⟨y, hy⟩
    simp only [hdest]
    rw [Vector.getElem_set]
    by_cases hdj : destIndex k y = j
    · have hxy := (destIndex_eq_iff ⟨k, hk'⟩ ⟨y, hy⟩ ⟨j, hj⟩).1 hdj
      simp [hdj, hxy]
    · simp [hdj]
      have hpre := ih init (by omega)
      simp only [] at hpre
      rw [hpre]
      by_cases hcond : j % 5 = y ∧ sourceX j < k
      · simp [hcond, show j % 5 = y ∧ sourceX j < k + 1 by omega]
      · have hcond' : ¬ (j % 5 = y ∧ sourceX j < k + 1) := by
          intro h
          have hxeq : sourceX j = k := by omega
          exact hdj ((destIndex_eq_iff ⟨k, hk'⟩ ⟨y, hy⟩ ⟨j, hj⟩).2 ⟨h.1, hxeq⟩)
        simp [hcond, hcond']

theorem rhoPi_rows_get (afterTheta : State) (rows : Nat) (hrows : rows ≤ 5)
    (j : Nat) (hj : j < 25) :
    ((List.range' 0 rows).foldl (fun acc y =>
      (List.range' 0 5).foldl (fun acc x =>
        let destination := laneIndex y (2 * x + 3 * y)
        acc.set destination.val (piValue afterTheta x y) destination.isLt) acc)
      (Vector.replicate 25 0))[j] =
    if j % 5 < rows then piValue afterTheta (sourceX j) (j % 5) else 0 := by
  induction rows with
  | zero =>
    simp [List.range'_zero, List.foldl_nil, Vector.getElem_replicate]
  | succ rows ih =>
    have hy : rows < 5 := by omega
    rw [show List.range' 0 (rows + 1) = List.range' 0 rows ++ [0 + rows] from List.range'_1_concat]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    rw [rhoPi_row_get afterTheta _ rows 5 hy (by decide) j hj]
    by_cases hrow : j % 5 = rows ∧ sourceX j < 5
    · simp [hrow]
    · simp [hrow]
      have hpre := ih (by omega)
      simp only [] at hpre
      rw [hpre]
      by_cases hlt : j % 5 < rows
      · simp [hlt, show j % 5 < rows + 1 by omega]
      · have hge : ¬ j % 5 < rows + 1 := by
          intro hlt'
          exact hrow ⟨by omega, sourceX_lt j⟩
        simp [hlt, hge]

theorem rhoPiFold_get (afterTheta : State) (j : Nat) (hj : j < 25) :
    (rhoPiFold afterTheta)[j] = piValue afterTheta (sourceX j) (j % 5) := by
  unfold rhoPiFold
  rw [rhoPi_rows_get afterTheta 5 (by decide) j hj]
  simp [show j % 5 < 5 from Nat.mod_lt _ (by decide)]

theorem laneIndex_eq_laneIdx (x y : Fin 5) : laneIndex x.val y.val = laneIdx x y := by
  ext
  simp [laneIdx, laneIndex_val x.isLt y.isLt]

theorem coords_laneIdx (x y : Fin 5) : coords (laneIdx x y) = (x, y) := by
  ext
  · simp [coords, laneIdx]
  · simp [coords, laneIdx]
    omega

theorem rotationOffsets_get (i : Fin 25) :
    rotationOffsets[i] = rotationOffset (coords i).1 (coords i).2 := by
  rw [rotationOffsets_eq_spec]
  simp [Vector.getElem_ofFn]

theorem src_pair (j : Fin 25) :
    ((coords j).1 + 3 * (coords j).2, (coords j).1) =
      (⟨sourceX j.val, sourceX_lt j.val⟩, ⟨j.val % 5, Nat.mod_lt _ (by decide)⟩) := by
  decide +revert

theorem pi_rho_get (A : Lanes) (j : Nat) (hj : j < 25) :
    (pi (rho A))[j] =
      (KeccakSpec.lane A ⟨sourceX j, sourceX_lt j⟩ ⟨j % 5, Nat.mod_lt _ (by decide)⟩).rotateLeft
        (rotationOffset ⟨sourceX j, sourceX_lt j⟩ ⟨j % 5, Nat.mod_lt _ (by decide)⟩) := by
  have hsrc := src_pair ⟨j, hj⟩
  have hsrcX : (coords ⟨j, hj⟩).1 + 3 * (coords ⟨j, hj⟩).2 = ⟨sourceX j, sourceX_lt j⟩ :=
    congrArg Prod.fst hsrc
  have hsrcY : (coords ⟨j, hj⟩).1 = ⟨j % 5, Nat.mod_lt _ (by decide)⟩ :=
    congrArg Prod.snd hsrc
  simp only [pi, rho, Vector.getElem_ofFn, fin_get_nat]
  simp only [hsrcX]
  simp only [hsrcY]
  have hc :
      coords ⟨(laneIdx ⟨sourceX j, sourceX_lt j⟩ ⟨j % 5, Nat.mod_lt _ (by decide)⟩).val,
        (laneIdx _ _).isLt⟩ =
      (⟨sourceX j, sourceX_lt j⟩, ⟨j % 5, Nat.mod_lt _ (by decide)⟩) := by
    simp [coords_laneIdx]
  simp [hc, KeccakSpec.lane]

theorem rhoPiFold_toLanes (afterTheta : State) :
    toLanes (rhoPiFold afterTheta) = pi (rho (toLanes afterTheta)) := by
  apply Vector.ext
  intro j hj
  rw [toLanes_get _ j hj, rhoPiFold_get _ j hj]
  unfold piValue
  have hsx : sourceX j < 5 := sourceX_lt j
  have hsy : j % 5 < 5 := Nat.mod_lt _ (by decide)
  have hi : laneIndex (sourceX j) (j % 5) = laneIdx ⟨sourceX j, hsx⟩ ⟨j % 5, hsy⟩ :=
    laneIndex_eq_laneIdx ⟨sourceX j, hsx⟩ ⟨j % 5, hsy⟩
  have hlt : rotationOffsets[laneIndex (sourceX j) (j % 5)] < 64 := by
    simp only [hi, rotationOffsets_get, coords_laneIdx]
    exact rotationOffset_lt_64 _ _
  rw [rotateLeft_toBitVec _ hlt, lane_toBitVec afterTheta hsx hsy]
  simp only [hi, rotationOffsets_get, coords_laneIdx]
  exact (pi_rho_get (toLanes afterTheta) j hj).symm

/-! ### χ, ι, and the round -/

theorem chiFold_toLanes (afterPi : State) :
    toLanes (chiFold afterPi) = chi (toLanes afterPi) := by
  apply Vector.ext
  intro j hj
  have hx : j % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : j / 5 < 5 := by omega
  let x : Fin 5 := ⟨j % 5, hx⟩
  let y : Fin 5 := ⟨j / 5, hy⟩
  rw [toLanes_get _ j hj]
  simp only [chi, Vector.getElem_ofFn]
  rw [chiFold_get _ j hj]
  unfold chiValue
  rw [toBitVec_xor, toBitVec_and, toBitVec_not]
  rw [lane_toBitVec afterPi hx hy]
  rw [lane_toBitVec afterPi (Nat.mod_lt _ (by decide) : (j % 5 + 1) % 5 < 5) hy]
  rw [lane_toBitVec afterPi (Nat.mod_lt _ (by decide) : (j % 5 + 2) % 5 < 5) hy]
  have h1 : (⟨(j + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨j % 5, hx⟩ + 1 := by
    ext
    simp [Fin.val_add]
  have h2 : (⟨(j + 2) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨j % 5, hx⟩ + 2 := by
    ext
    simp [Fin.val_add]
  have hc1 : (coords ⟨j, hj⟩).1 = x := by
    ext
    simp [coords, x]
  have hc2 : (coords ⟨j, hj⟩).2 = y := by
    ext
    simp [coords, y]
  simp [h1, h2, hc1, hc2, x, y]

theorem toLanes_set (s : State) (i : Nat) (hi : i < 25) (v : UInt64) :
    toLanes (s.set i v hi) = (toLanes s).set i v.toBitVec hi := by
  apply Vector.ext
  intro j hj
  simp [toLanes, Vector.getElem_ofFn, Vector.getElem_set]
  split <;> rfl

theorem round_toLanes (state : State) (rc : UInt64) :
    toLanes (round state rc) = KeccakSpec.round (toLanes state) rc.toBitVec := by
  rw [round_eq_fold]
  unfold roundFold KeccakSpec.round
  simp only []
  rw [toLanes_set, toBitVec_xor]
  rw [← toLanes_get (chiFold (rhoPiFold (thetaFold state (columnsFold state)))) 0 (by decide)]
  rw [chiFold_toLanes, rhoPiFold_toLanes, thetaFold_toLanes]
  simp [iota]

/-! ### The 24-round permutation -/

theorem foldl_ofFn_finRange {α β : Type} {n : Nat} (f : Fin n → α) (g : β → α → β) (init : β) :
    (List.ofFn f).foldl g init =
      (List.finRange n).foldl (fun acc i => g acc (f i)) init := by
  induction n generalizing init with
  | zero => simp [List.ofFn_zero, List.finRange_zero]
  | succ n ih =>
    simp [List.ofFn_succ, List.finRange_succ, List.foldl_cons, List.foldl_map]
    exact ih (fun i => f i.succ) (g init (f 0))

theorem vector_toList_ofFn_get {α : Type} {n : Nat} (xs : Vector α n) :
    xs.toList = List.ofFn (fun i : Fin n => xs[i.val]) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getElem_ofFn]

theorem vector_foldl_finRange {α β : Type} {n : Nat} (xs : Vector α n) (g : β → α → β) (init : β) :
    xs.toArray.foldl g init =
      (List.finRange n).foldl (fun acc i => g acc xs[i]) init := by
  rw [← Array.foldl_toList, Vector.toList_toArray, vector_toList_ofFn_get]
  simpa [fin_get_nat] using foldl_ofFn_finRange (fun i => xs[i.val]) g init

theorem foldl_round_toLanes (ids : List (Fin 24)) (state : State) :
    toLanes (ids.foldl (fun acc i => round acc roundConstants[i]) state) =
      ids.foldl (fun acc i => KeccakSpec.round acc (roundConstant i)) (toLanes state) := by
  induction ids generalizing state with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih (round state roundConstants[i])]
    rw [round_toLanes, roundConstants_eq_spec]

theorem permute_toLanes (state : State) :
    toLanes (permute state) = keccakF (toLanes state) := by
  rw [permute_eq_foldl, Array.foldl_attach (f := fun acc rc => round acc rc), vector_foldl_finRange,
    foldl_round_toLanes]
  rfl

/-! ### Absorbing a block -/

def mixFold (state : State) (block : Block) : State :=
  (List.range' 0 17).foldl (fun result i =>
    let index := Fin.ofNat 25 i
    result.set index.val (result[index] ^^^ decodeLane block i) index.isLt) state

theorem absorbBlock_eq (state : State) (block : Block) :
    absorbBlock state block = permute (mixFold state block) := by
  unfold absorbBlock mixFold
  simp only [forIn_eq_forIn', Std.Legacy.Range.forIn'_eq_forIn'_range',
    id_forIn'_range'_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  simp only [Id.run, Pure.pure, Bind.bind]

theorem mix_prefix_get (state : State) (block : Block) (k : Nat) (hk : k ≤ 17)
    (j : Nat) (hj : j < 25) :
    ((List.range' 0 k).foldl (fun result i =>
      let index := Fin.ofNat 25 i
      result.set index.val (result[index] ^^^ decodeLane block i) index.isLt) state)[j] =
    if j < k then state[j] ^^^ decodeLane block j else state[j] := by
  induction k with
  | zero => simp [List.range'_zero, List.foldl_nil]
  | succ k ih =>
    have hk' : k < 17 := by omega
    rw [show List.range' 0 (k + 1) = List.range' 0 k ++ [0 + k] from List.range'_1_concat]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    have hval : (Fin.ofNat 25 k).val = k := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : k < 25)]
    simp only [hval]
    rw [Vector.getElem_set]
    by_cases hjk : k = j
    · subst hjk
      have hpre := ih (by omega)
      simp only [Fin.ofNat, fin_get_nat, Nat.mod_eq_of_lt hj] at hpre ⊢
      rw [hpre]
      simp
    · have hpre := ih (by omega)
      simp only [Fin.ofNat, fin_get_nat] at hpre ⊢
      simp only [hjk]
      rw [hpre]
      by_cases hlt : j < k
      · simp [hlt, show j < k + 1 by omega]
      · have hge : ¬ j < k + 1 := by
          intro hlt'
          exact hjk (by omega)
        simp [hlt, hge]

theorem spec_mix_prefix (block : Block) (k : Nat) (hk : k ≤ 17) (A : Lanes)
    (j : Nat) (hj : j < 25) :
    ((List.finRange k).foldl (fun acc (i : Fin k) =>
      acc.set i.val
        (acc[i.val]'(by have h : i.val < k := i.isLt; omega) ^^^
          KeccakSpec.decodeLane block ⟨i.val, by have h : i.val < k := i.isLt; omega⟩)
        (by have h : i.val < k := i.isLt; omega)) A)[j] =
    if h : j < k then A[j] ^^^ KeccakSpec.decodeLane block ⟨j, by omega⟩ else A[j] := by
  induction k generalizing A with
  | zero => simp [List.finRange_zero, List.foldl_nil]
  | succ k ih =>
    have hk' : k < 17 := by omega
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.foldl_map]
    have hlast : (Fin.last k).val = k := by simp
    simp only [hlast, Fin.val_castSucc]
    have hmid := ih (by omega) A
    rw [Vector.getElem_set]
    by_cases hjk : k = j
    · subst hjk
      rw [hmid]
      simp
    · simp [hjk]
      rw [hmid]
      by_cases hlt : j < k
      · simp [hlt, show j < k + 1 by omega]
      · have hge : ¬ j < k + 1 := by
          intro hlt'
          exact hjk (by omega)
        simp [hlt, hge]

theorem spec_mix_get (A : Lanes) (block : Block) (j : Nat) (hj : j < 25) :
    (KeccakSpec.mixBlock A block)[j] =
      if h : j < 17 then A[j] ^^^ KeccakSpec.decodeLane block ⟨j, h⟩ else A[j] := by
  unfold KeccakSpec.mixBlock
  exact spec_mix_prefix block 17 (by decide) A j hj

theorem mixFold_toLanes (state : State) (block : Block) :
    toLanes (mixFold state block) = KeccakSpec.mixBlock (toLanes state) block := by
  apply Vector.ext
  intro j hj
  rw [toLanes_get _ j hj]
  unfold mixFold
  rw [mix_prefix_get state block 17 (by decide) j hj, spec_mix_get _ _ j hj]
  by_cases hlt : j < 17
  · rw [if_pos hlt, dif_pos hlt, toBitVec_xor, decodeLane_toBitVec block ⟨j, hlt⟩,
      toLanes_get state j hj]
  · rw [if_neg hlt, dif_neg hlt, toLanes_get state j hj]

theorem absorbBlock_toLanes (state : State) (block : Block) :
    toLanes (absorbBlock state block) = KeccakSpec.absorbBlock (toLanes state) block := by
  rw [absorbBlock_eq, permute_toLanes, mixFold_toLanes]
  rfl

/-! ### The sponge -/

theorem toLanes_zero : toLanes (Vector.replicate 25 0) = Vector.replicate 25 0 := by
  apply Vector.ext
  intro j hj
  simp [toLanes, Vector.getElem_ofFn, Vector.getElem_replicate]

theorem absorb_eq_fold (input : ByteArray) :
    absorb input =
      absorbBlock
        ((List.range (input.size / rateBytes)).foldl
          (fun state i => absorbBlock state (blockAt input (i * rateBytes)))
          (Vector.replicate 25 0))
        (finalBlock input (input.size / rateBytes * rateBytes)) := by
  unfold absorb
  simp only [forIn_eq_forIn', Std.Legacy.Range.forIn'_eq_forIn'_range',
    id_forIn'_range'_eq_foldl, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [Id.run, Pure.pure, Bind.bind, List.range_eq_range']

theorem absorb_prefix_toLanes (input : ByteArray) (k : Nat) (hk : k ≤ input.size / rateBytes) :
    toLanes ((List.range k).foldl
        (fun state i => absorbBlock state (blockAt input (i * rateBytes)))
        (Vector.replicate 25 0)) =
      (List.range k).foldl
        (fun A i => KeccakSpec.absorbBlock A (KeccakSpec.messageBlock input (i * rateBytes)))
        (Vector.replicate 25 0) := by
  induction k with
  | zero => simp [toLanes_zero]
  | succ k ih =>
    have hk' : k < input.size / rateBytes := by omega
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [absorbBlock_toLanes, ih (by omega), messageBlock_eq _ _ hk']

theorem absorb_toLanes (input : ByteArray) :
    toLanes (absorb input) = KeccakSpec.absorb input := by
  rw [absorb_eq_fold]
  rw [absorbBlock_toLanes, absorb_prefix_toLanes _ _ (Nat.le_refl _), finalBlock_eq]
  simp [KeccakSpec.absorb, rateBytes, KeccakSpec.rateBytes]

theorem encodeDigest_eq (state : State) :
    encodeDigest state = digest (toLanes state) := by
  unfold encodeDigest digest
  apply congrArg ByteArray.mk
  apply Array.ext
  · simp [digestBytes, KeccakSpec.digestBytes]
  · intro j hj1 hj2
    have hj : j < 32 := by simpa [Array.size_ofFn, digestBytes] using hj1
    simp only [Array.getElem_ofFn]
    have hshift : 8 * (j % 8) < 64 := by omega
    have hlane : j / 8 < 25 := by omega
    have hfin : Fin.ofNat 25 (j / 8) = ⟨j / 8, hlane⟩ := by
      ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt hlane]
    simp only [hfin]
    unfold UInt64.toUInt8 UInt64.toNat
    rw [shiftRight_toBitVec _ hshift, fin_get_nat state ⟨j / 8, hlane⟩,
      ← toLanes_get state (j / 8) hlane]

theorem hash_eq_spec (input : ByteArray) :
    hash input = KeccakSpec.keccak256 input := by
  simp [hash, KeccakSpec.keccak256, absorb_toLanes, encodeDigest_eq]

end Ethereum.Keccak256

theorem Ethereum.KEC_eq_spec (input : ByteArray) :
    KEC input = KeccakSpec.keccak256 input :=
  Keccak256.hash_eq_spec input
