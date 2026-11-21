import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalPVM

/-! The norm and spectral mapping clauses of paper.tex 12429–12454.
Nullity refers to zero spectral projection, with no scalar control measure.
The infimum is over nonnegative bounds, so it is zero on the zero space;
the essential range is empty there. -/
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set
namespace ExpandedFA.SpectralMeasure.BorelNormSpectrum.Spec
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The E-essential supremum of the modulus, with the nonnegative convention. -/
def essentialSup (E : ProjectionValuedMeasure S H) (f : S → ℂ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ E {s | C < ‖f s‖} = 0}

/-- Every positive-radius neighbourhood has a nonzero inverse-image projection. -/
def essentialRange (E : ProjectionValuedMeasure S H) (f : S → ℂ) : Set ℂ :=
  {z | ∀ ε : ℝ, 0 < ε → E {s | ‖f s - z‖ < ε} ≠ 0}

/-- Algebra laws on all actual bounded measurable functions. -/
def BorelCalculus (E : ProjectionValuedMeasure S H)
    (Φ : (S → ℂ) → H →L[ℂ] H) : Prop :=
  Φ (fun _ => 1) = 1 ∧
  (∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
    SpectralMeasure.Spec.IsBoundedMeasurable g → Φ (f + g) = Φ f + Φ g) ∧
  (∀ (c : ℂ) f, SpectralMeasure.Spec.IsBoundedMeasurable f → Φ (c • f) = c • Φ f) ∧
  (∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
    SpectralMeasure.Spec.IsBoundedMeasurable g → Φ (f * g) = Φ f * Φ g) ∧
  (∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f → Φ (star f) = star (Φ f)) ∧
  (∃ μ : H → H → ComplexMeasure S,
    (∀ x y B, MeasurableSet B → μ x y B = ⟪x, E B y⟫_ℂ) ∧
    (∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f → ∀ x y,
      ⟪x, Φ f y⟫_ℂ = (μ x y).integral f (ContinuousLinearMap.mul ℝ ℂ)))

/-- Stronger general form, for an arbitrary measurable-space PVM. -/
def PVMNormSpectrum : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : ProjectionValuedMeasure S H),
    ∃ Φ : (S → ℂ) → H →L[ℂ] H, BorelCalculus E Φ ∧
      ∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f →
        ‖Φ f‖ = essentialSup E f ∧ spectrum ℂ (Φ f) = essentialRange E f

/-- The required calculus for the normal operator and its spectral resolution. -/
def NormalNormSpectrum : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N →
    ∃ (E : ProjectionValuedMeasure (spectrum ℂ N) H)
      (Φ : ((spectrum ℂ N) → ℂ) → H →L[ℂ] H),
      NormalPVM.Spec.Resolves N E ∧ BorelCalculus E Φ ∧
      Φ (fun z => (z : ℂ)) = N ∧
      ∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f →
        ‖Φ f‖ = essentialSup E f ∧ spectrum ℂ (Φ f) = essentialRange E f

/-- Explicit compatible conventions in the zero Hilbert space. -/
def ZeroSpace : Prop :=
  ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Subsingleton H] (E : ProjectionValuedMeasure S H) (f : S → ℂ),
      SpectralMeasure.Spec.IsBoundedMeasurable f →
      essentialSup E f = 0 ∧ essentialRange E f = ∅
end ExpandedFA.SpectralMeasure.BorelNormSpectrum.Spec
