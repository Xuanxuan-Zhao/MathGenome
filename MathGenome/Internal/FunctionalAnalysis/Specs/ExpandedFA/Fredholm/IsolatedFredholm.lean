import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.RieszPoles

/-! Isolated points and finite Riesz rank, paper.tex:10801–10820.
The projection is the actual Riesz–Dunford value for any admissible cutoff.
No normality, compactness, separability, or finite multiplicity is assumed. -/
noncomputable section
namespace ExpandedFA.Fredholm.IsolatedFredholm.Spec
open Set
open ExpandedFA.BanachAlgebra
open ContourCalculus.Spec
universe u

/-- Three equivalent conditions at an isolated spectral point on an arbitrary
complex Hilbert space. Finite rank means finite dimension of the actual range. -/
def IsolatedFiniteRieszRank : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (lam : ℂ), RieszPoles.Spec.IsolatedSpectralPoint T lam →
    ∀ (U₁ U₂ : Set ℂ) (f : ℂ → ℂ),
      IsOpen U₁ → IsOpen U₂ → Disjoint U₁ U₂ → lam ∈ U₁ →
      spectrum ℂ T \ {lam} ⊆ U₂ →
      EqOn f (fun _ => 1) U₁ → EqOn f (fun _ => 0) U₂ →
      let P := HolomorphicValueValue (H →L[ℂ] H) T (U₁ ∪ U₂) f
      (DefinitionsSpec.IsSemiFredholmValue (T - lam • (1 : H →L[ℂ] H)) ↔
        FiniteDimensional ℂ P.range) ∧
      (FiniteDimensional ℂ P.range ↔
        ∃ h : DefinitionsSpec.IsFredholmValue (T - lam • (1 : H →L[ℂ] H)),
          DefinitionsSpec.fredholmIndexValue (T - lam • (1 : H →L[ℂ] H)) h = 0)

end ExpandedFA.Fredholm.IsolatedFredholm.Spec
