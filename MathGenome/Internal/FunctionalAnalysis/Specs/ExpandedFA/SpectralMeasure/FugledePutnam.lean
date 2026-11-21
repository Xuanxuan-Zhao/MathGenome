import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.FugledeIntertwining
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.BorelNormSpectrum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.PolarDecomposition

/-!
Fuglede--Putnam, paper.tex 12507--12528. All complex Hilbert spaces are
allowed, including zero and nonseparable spaces. T is rectangular and need
not be injective. Corresponding functions are functions on any common compact
superset of the two spectra, restricted to each spectrum. In particular one
can take their union. Thus every bounded Borel function on that union, and
every ambient Borel spectral projection, is included. The calculi are tied to
the actual PVMs by their scalar integral identities, not merely algebra laws.
The similarity conclusion uses the polar factor of the given invertible T.
-/
noncomputable section
namespace ExpandedFA.SpectralMeasure.FugledePutnam.Spec
universe u v

abbrev AdjointIntertwining : Prop := FugledeIntertwining.Spec.AdjointIntertwining.{u, v}

/-- The inclusion of the actual spectrum in a common spectral parameter set. -/
def inclusion {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : H →L[ℂ] H) (s : Set ℂ) (hs : spectrum ℂ N ⊆ s) :
    C(spectrum ℂ N, s) :=
  ⟨fun z => ⟨z.val, hs z.property⟩, continuous_subtype_val.subtype_mk _⟩

def BorelIntertwining : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : H →L[ℂ] H) (M : K →L[ℂ] K) (T : K →L[ℂ] H),
    IsStarNormal N → IsStarNormal M → N.comp T = T.comp M →
    ∀ (E : ProjectionValuedMeasure (spectrum ℂ N) H)
      (F : ProjectionValuedMeasure (spectrum ℂ M) K),
    NormalPVM.Spec.Resolves N E → NormalPVM.Spec.Resolves M F →
    ∀ (Φ : ((spectrum ℂ N) → ℂ) → H →L[ℂ] H)
      (Ψ : ((spectrum ℂ M) → ℂ) → K →L[ℂ] K),
    BorelNormSpectrum.Spec.BorelCalculus E Φ → BorelNormSpectrum.Spec.BorelCalculus F Ψ →
    ∀ (s : Set ℂ) [CompactSpace s] (hNs : spectrum ℂ N ⊆ s)
      (hMs : spectrum ℂ M ⊆ s) (f : s → ℂ),
    SpectralMeasure.Spec.IsBoundedMeasurable f →
    (Φ (f ∘ inclusion N s hNs)).comp T = T.comp (Ψ (f ∘ inclusion M s hMs))

def SpectralProjections : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : H →L[ℂ] H) (M : K →L[ℂ] K) (T : K →L[ℂ] H),
    IsStarNormal N → IsStarNormal M → N.comp T = T.comp M →
    ∀ (E : ProjectionValuedMeasure (spectrum ℂ N) H)
      (F : ProjectionValuedMeasure (spectrum ℂ M) K),
    NormalPVM.Spec.Resolves N E → NormalPVM.Spec.Resolves M F →
    ∀ B : Set ℂ, MeasurableSet B →
      (E (Subtype.val ⁻¹' B)).comp T = T.comp (F (Subtype.val ⁻¹' B))

def SimilarityUnitary : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : H →L[ℂ] H) (M : K →L[ℂ] K) (T : K ≃L[ℂ] H),
    IsStarNormal N → IsStarNormal M →
    N.comp T.toContinuousLinearMap = T.toContinuousLinearMap.comp M →
    ∃ U : K ≃ₗᵢ[ℂ] H,
      PolarDecomposition.Spec.IsPolarFactorValue T.toContinuousLinearMap
        U.toLinearIsometry.toContinuousLinearMap ∧
      N.comp U.toLinearIsometry.toContinuousLinearMap =
        U.toLinearIsometry.toContinuousLinearMap.comp M

end ExpandedFA.SpectralMeasure.FugledePutnam.Spec
