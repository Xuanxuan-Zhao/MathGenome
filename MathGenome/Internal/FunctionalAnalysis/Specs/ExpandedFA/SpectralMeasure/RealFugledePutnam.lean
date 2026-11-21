import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealFugledeIntertwining
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.FugledePutnam
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification

/-! Real Fuglede–Putnam on the original complete real Hilbert spaces.
Complex symbols act on the shared genuine Hilbert complexifications. Only
conjugation-compatible symbols, on conjugation-stable common spectral sets,
are asserted to have real restrictions. All calculus values are the existing
PVM integrals or calculi anchored to those integrals. -/
noncomputable section
namespace ExpandedFA.SpectralMeasure.RealFugledePutnam.Spec
universe u v
open TraceIdeals.RealComplexification
local instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

abbrev AdjointIntertwining : Prop := RealFugledeIntertwining.Spec.AdjointIntertwining.{u,v}

/-- Every complex symbol remains an operator on the complexification. -/
def BorelIntertwining : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K) (T : K →L[ℝ] H),
    IsStarNormal N → IsStarNormal M → N.comp T = T.comp M →
    ∀ (E : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) (Space H))
      (F : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M)) (Space K)),
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator N) E →
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator M) F →
    ∀ (Φ : ((spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) → ℂ) → Space H →L[ℂ] Space H)
      (Ψ : ((spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M)) → ℂ) → Space K →L[ℂ] Space K),
    BorelNormSpectrum.Spec.BorelCalculus E Φ → BorelNormSpectrum.Spec.BorelCalculus F Ψ →
    ∀ (s : Set ℂ) [CompactSpace s] (hNs : spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N) ⊆ s)
      (hMs : spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M) ⊆ s) (f : s → ℂ),
    SpectralMeasure.Spec.IsBoundedMeasurable f →
    (Φ (f ∘ FugledePutnam.Spec.inclusion (TraceIdeals.RealComplexification.Spec.operator N) s hNs)).comp (TraceIdeals.RealComplexification.Spec.operator T) =
      (TraceIdeals.RealComplexification.Spec.operator T).comp (Ψ (f ∘ FugledePutnam.Spec.inclusion (TraceIdeals.RealComplexification.Spec.operator M) s hMs))

def SpectralProjections : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K) (T : K →L[ℝ] H),
    IsStarNormal N → IsStarNormal M → N.comp T = T.comp M →
    ∀ (E : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) (Space H))
      (F : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M)) (Space K)),
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator N) E →
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator M) F →
    ∀ B : Set ℂ, MeasurableSet B →
      (E (Subtype.val ⁻¹' B)).comp (TraceIdeals.RealComplexification.Spec.operator T) =
        (TraceIdeals.RealComplexification.Spec.operator T).comp (F (Subtype.val ⁻¹' B))

/-- Spectrum symmetry, with no normality assumption needed. -/
def SpectrumConjugation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H) (z : ℂ),
    z ∈ spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N) ↔
      star z ∈ spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)

/-- Set-image conjugation is ambient: PVM values use the spectrum subtype. -/
def ConjugationCovariance : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
    (∀ z : ℂ, z ∈ spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N) ↔
      star z ∈ spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) ∧
    ∀ E : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) (Space H),
      NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator N) E →
      ∀ B : Set ℂ, MeasurableSet B → ∀ p : Space H,
        TraceIdeals.RealComplexification.Spec.conjugation (E (Subtype.val ⁻¹' B) (TraceIdeals.RealComplexification.Spec.conjugation p)) =
          E (Subtype.val ⁻¹' (star '' B)) p

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A real restriction is anchored by its values on the canonical inclusion. -/
def IsRealRestriction (A : Space H →L[ℂ] Space H) (R : H →L[ℝ] H) : Prop :=
  ∀ x : H, A (TraceIdeals.RealComplexification.Spec.inclusion x) = TraceIdeals.RealComplexification.Spec.inclusion (R x)

def UniqueRealRestriction (A : Space H →L[ℂ] Space H) (R : H →L[ℝ] H) : Prop :=
  IsRealRestriction A R ∧ ∀ S : H →L[ℝ] H, IsRealRestriction A S → S = R

/-- The one-space analytic assertion needed for real descent. -/
def CompatibleBorelInvariance : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
    ∀ E : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) (Space H),
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator N) E →
    ∀ Φ : ((spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) → ℂ) → Space H →L[ℂ] Space H,
    BorelNormSpectrum.Spec.BorelCalculus E Φ →
    ∀ (s : Set ℂ) [CompactSpace s] (hNs : spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N) ⊆ s)
      (hs : ∀ z ∈ s, star z ∈ s) (f : s → ℂ),
    SpectralMeasure.Spec.IsBoundedMeasurable f →
    (∀ z : s, f ⟨star z.val, hs z.val z.property⟩ = star (f z)) →
    ∀ p : Space H, TraceIdeals.RealComplexification.Spec.conjugation p = p →
      TraceIdeals.RealComplexification.Spec.conjugation
        (Φ (f ∘ FugledePutnam.Spec.inclusion (TraceIdeals.RealComplexification.Spec.operator N) s hNs) p) =
      Φ (f ∘ FugledePutnam.Spec.inclusion (TraceIdeals.RealComplexification.Spec.operator N) s hNs) p

/-- Compatible Borel functions preserve precisely the fixed real form and
have unique bounded restrictions on H and K whose complexifications are the
original complex integrals. T intertwines those actual real restrictions. -/
def RealBorelTransport : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K) (T : K →L[ℝ] H),
    IsStarNormal N → IsStarNormal M → N.comp T = T.comp M →
    ∀ (E : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) (Space H))
      (F : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M)) (Space K)),
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator N) E →
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator M) F →
    ∀ (Φ : ((spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) → ℂ) → Space H →L[ℂ] Space H)
      (Ψ : ((spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M)) → ℂ) → Space K →L[ℂ] Space K),
    BorelNormSpectrum.Spec.BorelCalculus E Φ → BorelNormSpectrum.Spec.BorelCalculus F Ψ →
    ∀ (s : Set ℂ) [CompactSpace s] (hNs : spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N) ⊆ s)
      (hMs : spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M) ⊆ s) (hs : ∀ z ∈ s, star z ∈ s) (f : s → ℂ),
    SpectralMeasure.Spec.IsBoundedMeasurable f →
    (∀ z : s, f ⟨star z.val, hs z.val z.property⟩ = star (f z)) →
    let A := Φ (f ∘ FugledePutnam.Spec.inclusion (TraceIdeals.RealComplexification.Spec.operator N) s hNs)
    let B := Ψ (f ∘ FugledePutnam.Spec.inclusion (TraceIdeals.RealComplexification.Spec.operator M) s hMs)
    (∀ p : Space H, TraceIdeals.RealComplexification.Spec.conjugation p = p → TraceIdeals.RealComplexification.Spec.conjugation (A p) = A p) ∧
    (∀ p : Space K, TraceIdeals.RealComplexification.Spec.conjugation p = p → TraceIdeals.RealComplexification.Spec.conjugation (B p) = B p) ∧
    ∃ (R : H →L[ℝ] H) (S : K →L[ℝ] K),
      UniqueRealRestriction A R ∧ UniqueRealRestriction B S ∧
      TraceIdeals.RealComplexification.Spec.operator R = A ∧ TraceIdeals.RealComplexification.Spec.operator S = B ∧ R.comp T = T.comp S

/-- Invariant ambient Borel sets yield real orthogonal projections. -/
def RealSpectralProjections : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K) (T : K →L[ℝ] H),
    IsStarNormal N → IsStarNormal M → N.comp T = T.comp M →
    ∀ (E : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator N)) (Space H))
      (F : ProjectionValuedMeasure (spectrum ℂ (TraceIdeals.RealComplexification.Spec.operator M)) (Space K)),
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator N) E →
    NormalPVM.Spec.Resolves (TraceIdeals.RealComplexification.Spec.operator M) F →
    ∀ B : Set ℂ, MeasurableSet B → star '' B = B →
    ∃ (P : H →L[ℝ] H) (Q : K →L[ℝ] K),
      UniqueRealRestriction (E (Subtype.val ⁻¹' B)) P ∧
      UniqueRealRestriction (F (Subtype.val ⁻¹' B)) Q ∧
      TraceIdeals.RealComplexification.Spec.operator P = E (Subtype.val ⁻¹' B) ∧
      TraceIdeals.RealComplexification.Spec.operator Q = F (Subtype.val ⁻¹' B) ∧
      P.adjoint = P ∧ P.comp P = P ∧ Q.adjoint = Q ∧ Q.comp Q = Q ∧
      P.comp T = T.comp Q

def SimilarityOrthogonal : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K) (T : K ≃L[ℝ] H),
    IsStarNormal N → IsStarNormal M →
    N.comp T.toContinuousLinearMap = T.toContinuousLinearMap.comp M →
    ∃ U : K ≃ₗᵢ[ℝ] H,
      PolarDecomposition.Spec.IsPolarFactorValue T.toContinuousLinearMap
        U.toLinearIsometry.toContinuousLinearMap ∧
      N.comp U.toLinearIsometry.toContinuousLinearMap =
        U.toLinearIsometry.toContinuousLinearMap.comp M

/-- Both scalar specializations; the fixed complex Props remain unchanged. -/
def FullScalarConclusion : Prop :=
  FugledePutnam.Spec.AdjointIntertwining.{u,v} ∧
  FugledePutnam.Spec.BorelIntertwining.{u,v} ∧
  FugledePutnam.Spec.SpectralProjections.{u,v} ∧
  FugledePutnam.Spec.SimilarityUnitary.{u,v} ∧
  AdjointIntertwining.{u,v} ∧ BorelIntertwining.{u,v} ∧ SpectralProjections.{u,v} ∧
  ConjugationCovariance.{u} ∧ ConjugationCovariance.{v} ∧
  RealBorelTransport.{u,v} ∧ RealSpectralProjections.{u,v} ∧ SimilarityOrthogonal.{u,v}

end ExpandedFA.SpectralMeasure.RealFugledePutnam.Spec
