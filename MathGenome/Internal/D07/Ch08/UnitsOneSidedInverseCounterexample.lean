import MathGenome.Internal.Specs.D07.Ch08.UnitsOneSidedInverseCounterexample

/-!
# One-sided inverses need not be two-sided

K07.08.units, paper.tex:1220–1226. The forward and backward shifts act on
the countably generated free vector space over any field. The product `S*T`
is the identity; the opposite product kills the nonzero vector `e_0`.
If either factor were a unit, cancellation would force the opposite product
to be the identity as well. Left and right inverses of a common element
coincide in every ring, without assuming that ring to be nontrivial.
-/

universe u v

namespace D07.Ch08.UnitsOneSidedInverseCounterexample

open Specs.D07.Ch08.UnitsOneSidedInverseCounterexample

theorem standardBasisVectors : StandardBasisVectors.{u} := by
  intro K _ i
  exact congr_fun Finsupp.coe_basisSingleOne i

theorem shiftOnBasis : ShiftOnBasis.{u} := by
  intro K _ i
  simp [T, e]

theorem backwardShiftZero : BackwardShiftZero.{u} := by
  intro K _
  apply Finsupp.ext
  intro i
  simp [S, e]

theorem backwardShiftOnSucc : BackwardShiftOnSucc.{u} := by
  intro K _ i
  apply Finsupp.ext
  intro j
  simp [S, e]

theorem backwardShiftMulShift : BackwardShiftMulShift.{u} := by
  intro K _
  apply LinearMap.ext
  intro x
  exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := K) (M := K)
    Nat.succ Nat.succ_injective x

theorem basisZeroNeZero : BasisZeroNeZero.{u} := by
  intro K _ h
  have h0 := congrArg (fun x : FreeSpace K => x 0) h
  exact (one_ne_zero : (1 : K) ≠ 0)
    (by simpa only [e, Finsupp.single_eq_same, Finsupp.zero_apply] using h0)

theorem shiftMulBackwardShiftAtZero : ShiftMulBackwardShiftAtZero.{u} := by
  intro K _
  change T K (S K (e K 0)) = 0
  rw [backwardShiftZero K, map_zero]

theorem shiftMulBackwardShiftNeOne : ShiftMulBackwardShiftNeOne.{u} := by
  intro K _ h
  have h0 := congrArg (fun f : Module.End K (FreeSpace K) => f (e K 0)) h
  rw [shiftMulBackwardShiftAtZero K] at h0
  exact basisZeroNeZero K h0.symm

theorem shiftNotIsUnit : ShiftNotIsUnit.{u} := by
  intro K _ h
  apply shiftMulBackwardShiftNeOne K
  apply h.mul_right_cancel
  calc
    (T K * S K) * T K = T K * (S K * T K) := mul_assoc _ _ _
    _ = 1 * T K := by rw [backwardShiftMulShift K, mul_one, one_mul]

theorem backwardShiftNotIsUnit : BackwardShiftNotIsUnit.{u} := by
  intro K _ h
  apply shiftMulBackwardShiftNeOne K
  apply h.mul_left_cancel
  calc
    S K * (T K * S K) = (S K * T K) * S K := (mul_assoc _ _ _).symm
    _ = S K * 1 := by rw [backwardShiftMulShift K, one_mul, mul_one]

theorem leftRightInverseUnique : LeftRightInverseUnique.{v} := by
  intro R _ a s t hs ht
  calc
    s = s * 1 := (mul_one s).symm
    _ = s * (a * t) := by rw [ht]
    _ = (s * a) * t := (mul_assoc s a t).symm
    _ = t := by rw [hs, one_mul]

end D07.Ch08.UnitsOneSidedInverseCounterexample
