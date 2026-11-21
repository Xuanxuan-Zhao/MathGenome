import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Holder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
Discrete Hölder and Minkowski, including the endpoint exponents.

For Hölder, scalar multiplication is a bilinear map of norm at most one.
Mathlib's extended-exponent Hölder theorem sends this map to the corresponding
map `ℓᵖ × ℓᑫ → ℓ¹`. The ℓ¹ norm formula gives absolute summability and the
required estimate. No conjugation is inserted in the complex product.

For Minkowski, `Memℓp.add` establishes membership independently of the normed
group structure. Mathlib proves the latter's triangle inequality from the
power-sum formula (and from the supremum formula at infinity).
-/

noncomputable section
open scoped ENNReal NNReal

universe u
namespace ExpandedFA.P1.C01Holder
open C01SequenceSpaces C01Norm

theorem discrete_holder : Spec.Holder.{u} := by
  intro 𝕜 _ p q _ _ hpq x y
  have : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr hpq
  let B : ℕ → 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜 := fun _ => ContinuousLinearMap.mul 𝕜 𝕜
  have hB : ∀ n, ‖B n‖ ≤ (1 : ℝ≥0) :=
    fun _ => ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let z : SequenceLp 𝕜 1 := lp.holder 1 B hB x y
  have hz : Summable (fun n => ‖x n * y n‖) := by
    simpa [z, B] using (lp.memℓp z).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  refine ⟨hz, hz.of_norm, ?_⟩
  have hznorm : ‖z‖ = ∑' n, ‖x n * y n‖ := by
    simpa [z, B] using lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) z
  rw [← hznorm]
  exact (lp.holderL (p := p) (q := q) 1 B hB).le_of_opNorm₂_le_of_le
    (lp.norm_holderL_le 1 B hB) le_rfl le_rfl |>.trans (by simp)

theorem sequence_add_membership : Spec.AddMembership.{u} := by
  intro 𝕜 _ p _ x y hx hy
  exact hx.add hy

theorem discrete_minkowski : Spec.Minkowski.{u} := by
  intro 𝕜 _ p _ x y
  exact ⟨fun _ => rfl, norm_add_le x y⟩

theorem finite_formula_norm : Spec.FiniteFormulaNorm.{u} := by
  intro 𝕜 _ p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  have hformula : (fun x : SequenceLp 𝕜 (ENNReal.ofReal p) =>
      (∑' n, ‖x n‖ ^ p) ^ (1 / p)) = norm := by
    funext x
    symm
    simpa [ENNReal.toReal_ofReal hp0.le] using
      lp.norm_eq_tsum_rpow (by simpa [ENNReal.toReal_ofReal hp0.le] using hp0) x
  rw [hformula]
  exact canonical_norm_axioms 𝕜 (SequenceLp 𝕜 (ENNReal.ofReal p))

theorem infinity_formula_norm : Spec.InfinityFormulaNorm.{u} := by
  intro 𝕜 _
  exact canonical_norm_axioms 𝕜 (SequenceLInfinity 𝕜)

end ExpandedFA.P1.C01Holder
