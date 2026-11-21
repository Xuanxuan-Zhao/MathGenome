import MathGenome.Internal.LinearPDE.P201Specs.Heat.SpectralSemigroup
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Compact-resolvent expansion for the same canonical form operator and heat
semigroup as in the preceding results. The index is a subset of ℕ, which may
be finite or empty; compactness is required only for this expansion. -/
noncomputable section
open scoped InnerProductSpace NNReal
universe u v
namespace P201.Heat.CompactSpectralExpansionExpected
open ExpandedFA.Semigroups

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Compactness of the actual shifted inverse (I+B)⁻¹, specified by both
directions of its exact graph identity. -/
def CompactResolvent (d : CoerciveForm V H) : Prop :=
  ∃ K : H →L[ℝ] H, IsCompactOperator K ∧
    ∀ x f : H, (x, f - x) ∈ d.operator.graph ↔ K f = x

/-- A complete orthonormal eigenbasis, with convergence in the Hilbert norm.
The real coefficient `inner ℝ (b i) g` is the paper's `(g,φᵢ)`.
The finite and zero dimensional cases are explicitly retained. -/
def EigenExpansion (d : CoerciveForm V H) (S : C0Semigroup ℝ H) : Prop :=
  ∃ (I : Set ℕ) (b : HilbertBasis I ℝ H) (eigenvalue : I → ℝ),
    (∀ i, 0 ≤ eigenvalue i) ∧
    (∀ i, (b i, eigenvalue i • b i) ∈ d.operator.graph) ∧
    (∀ (g : H) (t : ℝ≥0),
      HasSum (fun i => (Real.exp (-(t : ℝ) * eigenvalue i) * inner ℝ (b i) g) • b i)
        (S.operators t g)) ∧
    (FiniteDimensional ℝ H → ∃ F : Fintype I, letI := F;
      ∀ (g : H) (t : ℝ≥0), S.operators t g =
        ∑ i, (Real.exp (-(t : ℝ) * eigenvalue i) * inner ℝ (b i) g) • b i) ∧
    (Subsingleton H → I = ∅)

/-- Full heat-semigroup theorem: general spectral exponential, exact generator,
sharp smoothing, and eigenbasis expansion conditional on compact resolvent. -/
def FullTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : CoerciveForm V H), ∃ S : C0Semigroup ℝ H,
      SpectralSemigroupExpected.HeatSemigroup d S ∧
      (CompactResolvent d → EigenExpansion d S)

end P201.Heat.CompactSpectralExpansionExpected
