import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.HamburgerExistence

/-! Independent statements for paper.tex:15661–15689 (the determinacy equivalence).
The sufficient exponential-moment criteria are separately allocated. The Hilbert space and
minimal multiplication operator are exactly the shared polynomial construction.
No positive mass, strict Hankel positivity, or density in a representing L² space
is imposed. -/
noncomputable section
universe u v
open MeasureTheory
namespace ExpandedFA.Moments.HamburgerDeterminacySpec

/-- Existence and uniqueness among all positive Borel measures with the prescribed
moments and finite absolute moments. This includes the zero measure. -/
def Determinate (m : ℕ → ℝ) : Prop :=
  ∃! μ : Measure ℝ, RepresentsHamburgerMoments m μ

/-- Cauchy transform with the manuscript's z − t sign. -/
def cauchyTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (z - (t : ℂ))⁻¹ ∂μ

def Determinacy : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  Determinate m ↔ Unbounded.SymmetryAndDeficienciesSpec.essentiallySelfAdjointValue
    (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h)

/-- This is a theorem about arbitrary finite positive measures, with no moment
or polynomial-density hypothesis. -/
def CauchyTransformInjectivity : Prop :=
  ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
    (∀ z : ℂ, z.im ≠ 0 → cauchyTransform μ z = cauchyTransform ν z) → μ = ν

/-- General embedded-subspace resolvent lemma used by the printed argument.
The ambient extension is only required to be symmetric; in the application it
is the full self-adjoint real multiplier on L²(μ). -/
def ResolventRangeInvariance : Prop :=
  ∀ {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (S : Unbounded.Operator ℂ H H)
    (_ : Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue S)
    (T : Unbounded.Operator ℂ K K)
    (_ : Unbounded.SymmetryAndDeficienciesSpec.symmetricValue T)
    (J : H →ₗᵢ[ℂ] K),
    (∀ y : S.domain, (J (y : H), J (S y)) ∈ T.graph) →
    ∀ (z : ℂ), z.im ≠ 0 → ∀ (x : H) (w : T.domain),
    z • (w : K) - T w = J x → (w : K) ∈ J.toLinearMap.range

end ExpandedFA.Moments.HamburgerDeterminacySpec
