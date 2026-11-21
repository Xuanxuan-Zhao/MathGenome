import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.BorelNormSpectrum

/-!
The complete bounded normal spectral theorem, paper.tex
`fa2:p2:normal-spectral`. H is arbitrary, including zero and nonseparable
spaces. Almost everywhere means outside a measurable set whose spectral
projection is zero; no common finite scalar control measure is assumed.
Functions belong to the bounded Borel calculus, and uniform boundedness of
a sequence is a single pointwise bound on all its members.
-/
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set Filter
namespace ExpandedFA.SpectralMeasure.NormalSpectral.Spec
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The completion of the null ideal of the PVM. -/
def AlmostEverywhere (E : ProjectionValuedMeasure S H) (p : S → Prop) : Prop :=
  ∃ Z : Set S, MeasurableSet Z ∧ E Z = 0 ∧ ∀ s ∉ Z, p s

/-- Bounded convergence in the strong operator topology. -/
def StrongConvergence (E : ProjectionValuedMeasure S H)
    (Φ : (S → ℂ) → H →L[ℂ] H) : Prop :=
  ∀ (f : S → ℂ) (a : ℕ → S → ℂ),
    SpectralMeasure.Spec.IsBoundedMeasurable f →
    (∀ n, SpectralMeasure.Spec.IsBoundedMeasurable (a n)) →
    (∃ C : ℝ, ∀ n s, ‖a n s‖ ≤ C) →
    AlmostEverywhere E (fun s => Tendsto (fun n => a n s) atTop (nhds (f s))) →
    ∀ x : H, Tendsto (fun n => Φ (a n) x) atTop (nhds (Φ f x))

/-- Every operator in the joint commutant commutes with all Borel projections. -/
def SpectralCommutation (N : H →L[ℂ] H)
    (E : ProjectionValuedMeasure S H) : Prop :=
  ∀ T : H →L[ℂ] H, Commute T N → Commute T (star N) →
    ∀ B : Set S, MeasurableSet B → Commute T (E B)

/-- Existence, regularity, uniqueness, the coordinate identity, the Borel
*-homomorphism, both exact norm/spectrum formulas, strong bounded convergence,
and the commutant conclusion for the same resolution and calculus. -/
def NormalSpectralTheorem : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N →
    ∃ (E : ProjectionValuedMeasure (spectrum ℂ N) H)
      (Φ : ((spectrum ℂ N) → ℂ) → H →L[ℂ] H),
      NormalPVM.Spec.Resolves N E ∧
      (∀ F : ProjectionValuedMeasure (spectrum ℂ N) H,
        NormalPVM.Spec.Resolves N F → ∀ B, MeasurableSet B → F B = E B) ∧
      BorelNormSpectrum.Spec.BorelCalculus E Φ ∧
      Φ (fun z => (z : ℂ)) = N ∧
      (∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f →
        ‖Φ f‖ = BorelNormSpectrum.Spec.essentialSup E f ∧
        spectrum ℂ (Φ f) = BorelNormSpectrum.Spec.essentialRange E f) ∧
      StrongConvergence E Φ ∧ SpectralCommutation N E
end ExpandedFA.SpectralMeasure.NormalSpectral.Spec
