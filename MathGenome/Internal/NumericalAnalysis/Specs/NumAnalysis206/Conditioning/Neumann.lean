import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! Independent statements for paper.tex, Theorem W10 (including its Banach algebra form).
`HasSum` is convergence in the norm topology, and units/equivalences bundle both inverse laws.
No nontriviality of the algebra or of the spaces is assumed. -/
namespace NumAnalysis206.Conditioning.Specs

/-- Neumann series in a complete unital normed ring with subunit identity norm. -/
def neumannSeries : Prop :=
  ∀ {R : Type*} [NormedRing R] [CompleteSpace R], ‖(1 : R)‖ ≤ 1 →
    ∀ E : R, ‖E‖ < 1 → ∃ u : Rˣ,
      (u : R) = 1 + E ∧
      HasSum (fun j : ℕ => (-E) ^ j) (↑u⁻¹ : R) ∧
      ‖(↑u⁻¹ : R)‖ ≤ 1 / (1 - ‖E‖)

/-- The full inverse perturbation result in the same unital Banach algebra setting. -/
def algebraInversePerturbation : Prop :=
  ∀ {R : Type*} [NormedRing R] [CompleteSpace R], ‖(1 : R)‖ ≤ 1 →
    ∀ (A : Rˣ) (D : R), ‖(↑A⁻¹ : R) * D‖ < 1 → ∃ B : Rˣ,
      (B : R) = (A : R) + D ∧
      ‖(↑B⁻¹ : R)‖ ≤ ‖(↑A⁻¹ : R)‖ / (1 - ‖(↑A⁻¹ : R) * D‖) ∧
      (↑B⁻¹ : R) - (↑A⁻¹ : R) = -(↑B⁻¹ : R) * D * (↑A⁻¹ : R)

/-- Banach spaces over either real or complex scalars, with possibly distinct source and target.
The endomorphism `E` is exactly `A⁻¹ ∘ D`. -/
def operatorInversePerturbation : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : X ≃L[𝕜] Y) (D : X →L[𝕜] Y),
    let E := A.symm.toContinuousLinearMap.comp D
    ‖E‖ < 1 → ∃ (U : X ≃L[𝕜] X) (B : X ≃L[𝕜] Y),
      U.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 X + E ∧
      HasSum (fun j : ℕ => (-E) ^ j) U.symm.toContinuousLinearMap ∧
      ‖U.symm.toContinuousLinearMap‖ ≤ 1 / (1 - ‖E‖) ∧
      B.toContinuousLinearMap = A.toContinuousLinearMap + D ∧
      ‖B.symm.toContinuousLinearMap‖ ≤ ‖A.symm.toContinuousLinearMap‖ / (1 - ‖E‖) ∧
      B.symm.toContinuousLinearMap - A.symm.toContinuousLinearMap =
        -(B.symm.toContinuousLinearMap.comp D).comp A.symm.toContinuousLinearMap

end NumAnalysis206.Conditioning.Specs
