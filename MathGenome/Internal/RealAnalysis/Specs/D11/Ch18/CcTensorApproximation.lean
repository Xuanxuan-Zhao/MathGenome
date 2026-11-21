import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductSigma
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! Independent statements for paper.tex:5436. The source measurable space is
explicitly the product of the two factor Borel spaces, even when it is smaller
than the Borel space of the product topology. Supports are closed supports in
the original spaces. The open product neighborhood is chosen before ε. -/
namespace Specs.D11.Ch18.CcTensorApproximation

universe u v w
open scoped BigOperators

/-- Finite tensor approximation with a common precompact open product neighborhood.
The common real bound δ expresses approximation in the uniform norm. -/
def tensor_approximation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (𝕜 : Type w) [RCLike 𝕜] (f : CompactlySupportedContinuousMap (X × Y) 𝕜),
    ∃ O : Set X, ∃ P : Set Y,
      IsOpen O ∧ IsOpen P ∧ IsCompact (closure O) ∧ IsCompact (closure P) ∧
      tsupport f ⊆ O ×ˢ P ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (n : ℕ) (g : Fin n → CompactlySupportedContinuousMap X 𝕜)
          (h : Fin n → CompactlySupportedContinuousMap Y 𝕜) (δ : ℝ),
          (∀ j, tsupport (g j) ⊆ O) ∧ (∀ j, tsupport (h j) ⊆ P) ∧
          tsupport (fun p : X × Y => ∑ j, g j p.1 * h j p.2) ⊆ O ×ˢ P ∧
          0 ≤ δ ∧ δ < ε ∧ ∀ p : X × Y, ‖f p - ∑ j, g j p.1 * h j p.2‖ ≤ δ

/-- No second countability assumption and no equality of Borel sigma-algebras. -/
def product_borel_measurable : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (𝕜 : Type w) [RCLike 𝕜] (f : CompactlySupportedContinuousMap (X × Y) 𝕜),
    @Measurable (X × Y) 𝕜 ((borel X).prod (borel Y)) (borel 𝕜) f

end Specs.D11.Ch18.CcTensorApproximation
