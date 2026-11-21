import MathGenome.Internal.LinearPDE.P201Specs.Heat.SpectralSemigroup
import MathGenome.Internal.LinearPDE.P201.Heat.FormOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup

noncomputable section
open scoped InnerProductSpace NNReal
universe u v
namespace P201.Heat
open ExpandedFA.Semigroups ExpandedFA.Unbounded
open SelfAdjointSmoothing

namespace CoerciveForm
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (d : CoerciveForm V H)

/-- Bridge to the pinned smoothing theorem. Its adjoint is exactly Mathlib's
partial-map adjoint; its real part is the identity over ℝ. -/
theorem operator_nonnegativeSelfAdjoint : NonnegativeSelfAdjoint d.operator := by
  obtain ⟨hd, hs, hn, _⟩ := form_operator_representation d
  exact ⟨hd, hs.symm, hn⟩

end CoerciveForm

/-- The spectral heat exponential of the canonical associated operator,
including its full generator domain and the sharp bounds for partial powers. -/
theorem spectral_semigroup : SpectralSemigroupExpected.SemigroupTheorem.{u, v} := by
  intro V H _ _ _ _ _ _ d
  have hB := d.operator_nonnegativeSelfAdjoint
  obtain ⟨S, hS⟩ := real_selfadjoint_smoothing d.operator hB
  have hExp : SpectralSemigroupExpected.SpectralExponential d S := by
    obtain ⟨U, hU, hrep⟩ := complex_selfadjoint_smoothing
      (Complexification.lift d.operator)
      (Complexification.lift_nonnegativeSelfAdjoint d.operator hB)
    let R := Complexification.restrictSemigroup d.operator hB U hU
    have hR : C0SemigroupSpec.generatorValue R = -d.operator :=
      Complexification.restrict_generator d.operator hB U hU
    refine ⟨U, hrep, fun t x => ?_⟩
    have he : R.operators t = S.operators t :=
      GeneratorDeterminesSemigroup.generator_determines_semigroup R S
        (hR.trans hS.1.symm) t
    rw [← he]
    exact Complexification.preserves_real d.operator hB U hU t x
  refine ⟨S, hExp, S.continuous_orbit, hS.2.1, hS.1, ?_, ?_, ?_⟩
  · rw [hS.1]
    rfl
  · intro t ht m hm
    obtain ⟨A, hgraph, hnorm⟩ := hS.2.2.1 t ht m hm
    refine ⟨fun x => ?_, A, hgraph, hnorm⟩
    exact LinearPMap.mem_domain_iff.mpr ⟨A x, hgraph x⟩
  · intro U hU t
    exact GeneratorDeterminesSemigroup.generator_determines_semigroup U S
      (hU.trans hS.1.symm) t

end P201.Heat
