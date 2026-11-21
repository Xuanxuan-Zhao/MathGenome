import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ContourCalculus
import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! Riesz projections and the spectral splitting clause of
`fa2:p2:riesz-projection`, paper.tex:10125–10149. Spectra are the native
algebraic spectra of bounded endomorphisms with the inherited subspace norms.
The zero space and empty compact pieces are allowed. -/
noncomputable section
namespace ExpandedFA.BanachAlgebra.RieszSplitting.Spec
open Set
open Specs.ExpandedFA.BanachAlgebra.Conventions
open ContourCalculus.Spec
universe u

/-- Compact disjoint pieces admit the neighborhoods on which the cutoff is
locally constant. No nonemptiness of either piece is required. -/
def SeparatingNeighborhoods : Prop :=
  ∀ (K₁ K₂ : Set ℂ), IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ →
    ∃ U₁ U₂ : Set ℂ, IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
      K₁ ⊆ U₁ ∧ K₂ ⊆ U₂ ∧
      DifferentiableOn ℂ (U₁.indicator (fun _ => (1 : ℂ))) (U₁ ∪ U₂)

/-- Observable bounded projection, closed direct sum, and exact block spectra.
The equivalence has precisely the two projections as its coordinates, and
its inverse adds the two included vectors. Thus this is a topological direct
sum of the actual ranges in the original space. -/
def SplittingData {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T P : X →L[ℂ] X) (K₁ K₂ : Set ℂ) : Prop :=
  P * P = P ∧ Commute T P ∧
  IsClosed (P.range : Set X) ∧ IsClosed ((1 - P).range : Set X) ∧
  ∃ (T₁ : P.range →L[ℂ] P.range) (T₂ : (1 - P).range →L[ℂ] (1 - P).range),
    (∀ x : P.range, (T₁ x : X) = T x) ∧
    (∀ x : (1 - P).range, (T₂ x : X) = T x) ∧
    AlgebraSpectrumValue ℂ (P.range →L[ℂ] P.range) T₁ = K₁ ∧
    AlgebraSpectrumValue ℂ ((1 - P).range →L[ℂ] (1 - P).range) T₂ = K₂ ∧
    ∃ e : X ≃L[ℂ] (P.range × (1 - P).range),
      (∀ x : X, ((e x).1 : X) = P x ∧ ((e x).2 : X) = (1 - P) x) ∧
      (∀ y : P.range × (1 - P).range, e.symm y = (y.1 : X) + (y.2 : X))

/-- Every cutoff equal to one and zero on disjoint open neighborhoods gives
this splitting through the actual upstream contour integral. Holomorphy of
the cutoff follows from the stated local constant values. Exact spectra
are also valid on a zero summand, whose operator spectrum is empty. -/
def SpectralSplitting : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X) (K₁ K₂ : Set ℂ),
    IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ →
    AlgebraSpectrumValue ℂ (X →L[ℂ] X) T = K₁ ∪ K₂ →
    ∀ (U₁ U₂ : Set ℂ) (f : ℂ → ℂ),
      IsOpen U₁ → IsOpen U₂ → Disjoint U₁ U₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      EqOn f (fun _ => 1) U₁ → EqOn f (fun _ => 0) U₂ →
      SplittingData T (HolomorphicValueValue (X →L[ℂ] X) T (U₁ ∪ U₂) f) K₁ K₂

/-- The same result for any original holomorphy neighborhood and any cutoff
which has the prescribed values on some disjoint neighborhoods of the two
pieces. Its calculus value is unchanged when shrinking to those neighborhoods. -/
def SplittingOnNeighborhood : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X) (K₁ K₂ : Set ℂ),
    IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ →
    AlgebraSpectrumValue ℂ (X →L[ℂ] X) T = K₁ ∪ K₂ →
    ∀ (U : Set ℂ) (f : ℂ → ℂ),
      IsOpen U → AlgebraSpectrumValue ℂ (X →L[ℂ] X) T ⊆ U →
      DifferentiableOn ℂ f U →
      (∃ U₁ U₂ : Set ℂ, IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
        K₁ ⊆ U₁ ∧ K₂ ⊆ U₂ ∧ EqOn f (fun _ => 1) U₁ ∧ EqOn f (fun _ => 0) U₂) →
      SplittingData T (HolomorphicValueValue (X →L[ℂ] X) T U f) K₁ K₂

end ExpandedFA.BanachAlgebra.RieszSplitting.Spec
