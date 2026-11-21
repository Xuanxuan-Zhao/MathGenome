import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RepresentationBorelExtension

/-! Independent statements for `fa2:p2:representation-pvm`, paper.tex
12402–12434. Regularity means regularity of every scalar coefficient's
variation. Equality and uniqueness of PVMs concern measurable sets, since the
shared PVM interface deliberately leaves nonmeasurable values unconstrained.
Neither the compact space nor the Hilbert space is assumed separable/nonzero. -/
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set

namespace ExpandedFA.SpectralMeasure.RepresentationPVM.Spec
universe u v
variable {S : Type u} {H : Type v} [TopologicalSpace S] [CompactSpace S]
  [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A regular Borel PVM whose scalar integrals represent the given continuous
calculus. This predicate imposes no uniqueness or norm bound as an assumption. -/
def Represents (E : ProjectionValuedMeasure S H)
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∃ μ : H → H → ComplexMeasure S,
    (∀ x y, FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon (μ x y)) ∧
    (∀ x y B, MeasurableSet B → μ x y B = ⟪x, E B y⟫_ℂ) ∧
    (∀ x y (f : C(S, ℂ)), Integrable f (μ x y).variation ∧
      ⟪x, π f y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral (μ x y) f)

/-- The extension is on all actual bounded Borel functions, not on an a.e.
quotient. Its values on indicators are the PVM. -/
def BorelCalculus (E : ProjectionValuedMeasure S H)
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (Φ : (S → ℂ) → H →L[ℂ] H) : Prop :=
  (∀ f : C(S, ℂ), Φ f = π f) ∧
  (∀ B, MeasurableSet B → Φ (B.indicator (fun _ => (1 : ℂ))) = E B) ∧
  Φ (fun _ => 1) = 1 ∧
  (∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
    SpectralMeasure.Spec.IsBoundedMeasurable g → Φ (f + g) = Φ f + Φ g) ∧
  (∀ (c : ℂ) f, SpectralMeasure.Spec.IsBoundedMeasurable f → Φ (c • f) = c • Φ f) ∧
  (∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
    SpectralMeasure.Spec.IsBoundedMeasurable g → Φ (f * g) = Φ f * Φ g) ∧
  (∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f → Φ (star f) = star (Φ f)) ∧
  (∀ f C, SpectralMeasure.Spec.IsBoundedMeasurable f →
    0 ≤ C → (∀ s, ‖f s‖ ≤ C) → ‖Φ f‖ ≤ C)

/-- Existence, regularity, continuous spectral integral identity, uniqueness,
and extension as a contractive unital complex *-homomorphism. The PVM structure
itself supplies orthogonal projections, intersection and strong countable
additivity. Coefficients identify the extension with integration against E. -/
def RepresentationTheorem : Prop :=
  ∀ (S : Type u) (H : Type v) [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [MeasurableSpace S] [BorelSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)),
    ∃ (E : ProjectionValuedMeasure S H) (μ : H → H → ComplexMeasure S)
      (Φ : (S → ℂ) → H →L[ℂ] H),
      RepresentationBorelExtension.Spec.RepresentsCoefficients π μ ∧
      (∀ x y B, MeasurableSet B → μ x y B = ⟪x, E B y⟫_ℂ) ∧
      BorelCalculus E π Φ ∧
      (∀ g, SpectralMeasure.Spec.IsBoundedMeasurable g → ∀ x y,
        Integrable g (μ x y).variation ∧
        ⟪x, Φ g y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral (μ x y) g) ∧
      (∀ F : ProjectionValuedMeasure S H, Represents F π →
        ∀ B, MeasurableSet B → F B = E B)

end ExpandedFA.SpectralMeasure.RepresentationPVM.Spec
