import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuity
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statements for the conditioning interface, paper.tex:5009–5024.
`P.trim hT` is the restriction to the sub-sigma-algebra, rather than restriction
of the domain to a set. The signed measure is the restriction of the genuine
countably additive measure of set integrals. The conditional expectation is
measurable on T itself, and both integrability and uniqueness refer to P. -/

open Set MeasureTheory
universe u
noncomputable section

namespace Specs.D11.Ch15.ConditioningRoute

abbrev signedMeasure_type :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : MeasurableSpace Ω) (hT : T ≤ mΩ)
    (X : Ω → ℝ), Integrable X P → @SignedMeasure Ω T

def signedMeasure_value : signedMeasure_type.{u} :=
  fun P _ hT X _ => (P.withDensityᵥ X).trim hT

def signedMeasure_apply : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : MeasurableSpace Ω) (hT : T ≤ mΩ)
    (X : Ω → ℝ) (hX : Integrable X P) (B : Set Ω), MeasurableSet[T] B →
    @signedMeasure_value Ω mΩ P T hT X hX B = ∫ ω in B, X ω ∂P

def signedMeasure_absolutelyContinuous : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : MeasurableSpace Ω) (hT : T ≤ mΩ)
    (X : Ω → ℝ) (hX : Integrable X P),
    AbsoluteContinuity.scalarAbsolutelyContinuous_value
      (@signedMeasure_value Ω mΩ P T hT X hX) (P.trim hT)

def conditioning_route : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : MeasurableSpace Ω) (hT : T ≤ mΩ) (X : Ω → ℝ),
    Measurable X → Integrable X P →
    ∃ Y : Ω → ℝ, Measurable[T] Y ∧ Integrable Y P ∧
      (∀ B : Set Ω, MeasurableSet[T] B →
        ∫ ω in B, Y ω ∂P = ∫ ω in B, X ω ∂P) ∧
      ∀ Z : Ω → ℝ, Measurable[T] Z → Integrable Z P →
        (∀ B : Set Ω, MeasurableSet[T] B →
          ∫ ω in B, Z ω ∂P = ∫ ω in B, X ω ∂P) → Y =ᵐ[P] Z

end Specs.D11.Ch15.ConditioningRoute
