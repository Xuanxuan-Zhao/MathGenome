import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.LevelCylinderMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Integral identification for the canonical cylinder extension, paper.tex:6252–6270.
The measurable structure is A_V, not a completion or a sigma-finite replacement. -/
noncomputable section
universe u
open Set MeasureTheory
open scoped ENNReal
namespace D11.Ch23.Specs

/-- Nonnegative functions have the prescribed finite integral, also equal to
mass of their actual half-open undergraph in the canonical auxiliary measure. -/
def NonnegativeCylinderIntegral : Prop := ∀ {X : Type u}
    (V : Submodule ℝ (X → ℝ)), IsVectorLattice V → IsStone V →
    ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L → ∀ f : V,
    (∀ x, 0 ≤ (f : X → ℝ) x) →
    letI := positiveLevelMeasurableSpace V
    UndergraphMeasure V L (Undergraph 0 (f : X → ℝ)) = ENNReal.ofReal (L f) ∧
    (∫⁻ x, ENNReal.ofReal ((f : X → ℝ) x) ∂LevelCylinderMeasure V L) =
      ENNReal.ofReal (L f)

/-- Every original finite-valued function is measurable and absolutely integrable;
the scalar identity is accompanied by integrability, independently of totalization. -/
def LevelCylinderIntegralRepresentation : Prop := ∀ {X : Type u}
    (V : Submodule ℝ (X → ℝ)), IsVectorLattice V → IsStone V →
    ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L → ∀ f : V,
    letI := positiveLevelMeasurableSpace V
    Measurable (f : X → ℝ) ∧ Integrable (f : X → ℝ) (LevelCylinderMeasure V L) ∧
      (∫ x, (f : X → ℝ) x ∂LevelCylinderMeasure V L) = L f

end D11.Ch23.Specs
