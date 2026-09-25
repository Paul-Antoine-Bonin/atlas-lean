import Code.Transcription.Minrun
import Mathlib

/-!
# Adaptive-minrun equivalence

The theorems in this file project the reviewed 64-bit transcription to the
quotient-and-remainder description in CPython's `Objects/listsort.txt`.
-/

namespace CPythonListsort

/-- Arbitrary-precision specification of the `merge_init` exponent loop. -/
def minrunExponentSpecLoop : Nat → Nat → Nat → Nat × Bool
  | 0, _, exponent => (exponent, false)
  | fuel + 1, listSize, exponent =>
      if listSize >>> exponent < 64 then
        (exponent, true)
      else
        minrunExponentSpecLoop fuel listSize (exponent + 1)

private theorem maxMinrun_msb : MAX_MINRUN.msb = false := by decide

private theorem maxMinrun_toNat : MAX_MINRUN.toNat = 64 := by decide

private theorem shifted_slt_maxMinrun (x : PySSize) (exponent : Nat)
    (hx : x.Nonnegative) :
    (x.sshiftRight exponent).slt MAX_MINRUN = decide (x.toNat >>> exponent < 64) := by
  have hshift : (x.sshiftRight exponent).msb = false := by
    simpa [PySSize.Nonnegative] using hx
  rw [BitVec.slt_eq_decide]
  rw [BitVec.toInt_eq_toNat_of_msb hshift]
  rw [BitVec.toInt_eq_toNat_of_msb maxMinrun_msb]
  rw [BitVec.toNat_sshiftRight_of_msb_false hx]
  simp only [maxMinrun_toNat]
  norm_cast

/-- The finite-width and arbitrary-precision exponent loops take the same branches. -/
theorem minrunExponentLoop_eq_spec (fuel : Nat) (listSize : PySSize) (exponent : Nat)
    (hlistSize : listSize.Nonnegative) :
    minrunExponentLoop fuel listSize exponent =
      minrunExponentSpecLoop fuel listSize.toNat exponent := by
  induction fuel generalizing exponent with
  | zero => rfl
  | succ fuel ih =>
      simp only [minrunExponentLoop, minrunExponentSpecLoop]
      rw [shifted_slt_maxMinrun listSize exponent hlistSize]
      split <;> simp_all

private theorem minrunExponentSpecLoop_le (fuel listSize exponent : Nat) :
    (minrunExponentSpecLoop fuel listSize exponent).1 ≤ exponent + fuel := by
  induction fuel generalizing exponent with
  | zero => simp [minrunExponentSpecLoop]
  | succ fuel ih =>
      simp only [minrunExponentSpecLoop]
      split
      · omega
      · have := ih (exponent + 1)
        omega

/--
The transcribed initialization stores the mathematical exponent and its exact
bit-mask, starts with zero residual, and reports the same bounded-loop status.
-/
theorem minrunInit_eq_spec (listSize : PySSize) (hlistSize : listSize.Nonnegative) :
    let specified := minrunExponentSpecLoop 64 listSize.toNat 0
    (minrunInit listSize).mr_e.toNat = specified.1 ∧
      (minrunInit listSize).mr_mask = ((1 : PySSize) <<< specified.1) - 1 ∧
      (minrunInit listSize).mr_current = 0 ∧
      (minrunInitTraced listSize).stopped = specified.2 := by
  simp only [minrunInit, minrunInitTraced]
  rw [minrunExponentLoop_eq_spec 64 listSize 0 hlistSize]
  have hbound := minrunExponentSpecLoop_le 64 listSize.toNat 0
  have hlt : (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 2 ^ 64 := by
    norm_num at hbound ⊢
    omega
  have hshift :
      BitVec.ofNat 64 (1 <<< (minrunExponentSpecLoop 64 listSize.toNat 0).1) =
        ((1 : PySSize) <<< (minrunExponentSpecLoop 64 listSize.toNat 0).1) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  constructor
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  constructor
  · exact congrArg (fun x : PySSize => x - 1) hshift
  simp

/-- Mathematical quotient-and-remainder result of one adaptive-minrun step. -/
structure MinrunNextSpec where
  result : Nat
  residual : Nat
  deriving DecidableEq, Repr

/-- The exact-arithmetic specification described by CPython's integer generator. -/
def minrunNextSpec (listlen current exponent : Nat) : MinrunNextSpec :=
  let total := current + listlen
  { result := total / 2 ^ exponent
    residual := total % 2 ^ exponent }

private theorem one_shift_toNat {exponent : Nat} (hexponent : exponent < 64) :
    (((1 : PySSize) <<< exponent).toNat) = 2 ^ exponent := by
  have hpow : 2 ^ exponent < 2 ^ 64 :=
    Nat.pow_lt_pow_right (a := 2) (by omega) hexponent
  have hone : (1 : PySSize).toNat = 1 := by decide
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [hone, one_mul, Nat.mod_eq_of_lt hpow]

private theorem mask_toNat {exponent : Nat} (hexponent : exponent < 64) :
    ((((1 : PySSize) <<< exponent) - 1).toNat) = 2 ^ exponent - 1 := by
  have honeToNat : (1 : PySSize).toNat = 1 := by decide
  have hone : (1 : PySSize) ≤ (1 : PySSize) <<< exponent := by
    rw [BitVec.le_def, one_shift_toNat hexponent]
    simpa using Nat.one_le_two_pow
  rw [BitVec.toNat_sub_of_le hone, one_shift_toNat hexponent]
  rw [honeToNat]

/--
Under the C assertion's representability premise, `minrun_next` computes the
specified quotient and remainder and its signed-overflow assertion succeeds.
-/
theorem minrunNext_eq_spec (state : MinrunState)
    (hexponent : state.mr_e.toNat < 64)
    (hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1)
    (hnoOverflow : state.mr_current.toNat + state.listlen.toNat < 2 ^ 63) :
    let specified :=
      minrunNextSpec state.listlen.toNat state.mr_current.toNat state.mr_e.toNat
    (minrunNext state).result.toNat = specified.result ∧
      (minrunNext state).state.mr_current.toNat = specified.residual ∧
      (minrunNext state).assertionPassed = true := by
  let total : PySSize := state.mr_current + state.listlen
  have htotal64 : state.mr_current.toNat + state.listlen.toNat < 2 ^ 64 := by
    norm_num at hnoOverflow ⊢
    omega
  have htotalNat : total.toNat = state.mr_current.toNat + state.listlen.toNat := by
    exact BitVec.toNat_add_of_lt htotal64
  have htotalMbs : total.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, htotalNat]
    norm_num at hnoOverflow ⊢
    omega
  dsimp [minrunNextSpec]
  constructor
  · simp only [minrunNext, total, BitVec.toNat_sshiftRight_of_msb_false htotalMbs,
      htotalNat, Nat.shiftRight_eq_div_pow]
  constructor
  · change (total &&& state.mr_mask).toNat =
      (state.mr_current.toNat + state.listlen.toNat) % 2 ^ state.mr_e.toNat
    rw [BitVec.toNat_and, hmask, mask_toNat hexponent,
      Nat.and_two_pow_sub_one_eq_mod, htotalNat]
  · simp [minrunNext, total, htotalMbs]

end CPythonListsort
