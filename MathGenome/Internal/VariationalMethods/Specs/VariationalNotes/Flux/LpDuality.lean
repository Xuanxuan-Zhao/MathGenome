import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Basic.Real.ConjExponents

/-!
The real Euclidean Lp duality used in paper.tex, §v09-01, lines 4348–4352.
The measure is Lebesgue measure restricted to Ω. Native Bochner Lp is the
space of a.e. classes, with the Euclidean (not coordinate supremum) fiber norm.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace VariationalNotes.Flux.LpDualitySpec

/-- The conjugate exponent is literally p/(p-1). The equivalence has the
integral dot-product formula, represents every functional with its exact norm,
and determines the density up to ordinary Lebesgue-a.e. equality on Ω. -/
def Statement : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (Ω : Set (EuclideanSpace ℝ (Fin d))),
    MeasurableSet Ω → volume Ω < ∞ → ∀ (p : ℝ) (hp : 1 < p),
    let P := ENNReal.ofReal p
    let Q := ENNReal.ofReal (p / (p - 1))
    let μ := volume.restrict Ω
    letI : ENNReal.HolderConjugate P Q :=
      (Real.HolderConjugate.conjExponent hp).ennrealOfReal
    letI : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
    letI : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
    ∃ T : Lp (EuclideanSpace ℝ (Fin d)) Q μ ≃ₗᵢ[ℝ]
        (Lp (EuclideanSpace ℝ (Fin d)) P μ →L[ℝ] ℝ),
      (∀ (σ : Lp (EuclideanSpace ℝ (Fin d)) Q μ)
          (v : Lp (EuclideanSpace ℝ (Fin d)) P μ),
        Integrable (fun x => inner ℝ (σ x) (v x)) μ ∧
          T σ v = ∫ x, inner ℝ (σ x) (v x) ∂μ) ∧
      (∀ L : Lp (EuclideanSpace ℝ (Fin d)) P μ →L[ℝ] ℝ,
        ∃! σ : Lp (EuclideanSpace ℝ (Fin d)) Q μ,
          (∀ v : Lp (EuclideanSpace ℝ (Fin d)) P μ,
            L v = ∫ x, inner ℝ (σ x) (v x) ∂μ) ∧ ‖σ‖ = ‖L‖) ∧
      (∀ σ τ : Lp (EuclideanSpace ℝ (Fin d)) Q μ,
        (∀ v : Lp (EuclideanSpace ℝ (Fin d)) P μ,
          (∫ x, inner ℝ (σ x) (v x) ∂μ) = ∫ x, inner ℝ (τ x) (v x) ∂μ) ↔
          (σ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) =ᵐ[μ]
            (τ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)))

end VariationalNotes.Flux.LpDualitySpec
