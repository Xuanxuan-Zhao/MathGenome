import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzExtension
import Mathlib.Topology.MetricSpace.Bounded

/-! The two compactness assertions of paper.tex, Theorem
`thm:sobolev-compact-affine`. The graph-coordinate isometry in the first
assertion merely expresses the usual one-sided Lipschitz boundary geometry
in Euclidean dimension n+1; it adds no connectedness requirement.
Relative compactness means compactness of the closure in the strong Lp topology.
The exponent type includes p=1 and every finite real p>=1. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Sobolev.CompactnessExpected

/-- Bounded subsets of W¹ᵖ on a bounded Lipschitz open set are relatively
compact in vector-valued Lp. Dimension n+1 ranges over all positive dimensions. -/
def Lipschitz : Prop :=
  ∀ (n : ℕ)
    (e : P102.U4.GraphPieces.Ambient n ≃ₗᵢ[ℝ] Domain (n+1))
    (Ω : Opens (Domain (n+1))),
    P102.Sobolev.Geometry.IsLipschitzOpen
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient n)) →
    ∀ (m : ℕ) (p : Exponent) (A : Set (W1p Ω m p)),
      Bornology.IsBounded A → IsCompact (closure ((value Ω m p) '' A))

/-- No boundary regularity is required for bounded subsets of a fixed affine
zero-boundary class on a bounded open set. Empty domains are allowed. -/
def Affine : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (m : ℕ) (p : Exponent) (u₀ : W1p Ω m p) (A : Set (W1p Ω m p)),
      Bornology.IsBounded A → A ⊆ affineClass Ω m p u₀ →
      IsCompact (closure ((value Ω m p) '' A))

end VariationalNotes.Sobolev.CompactnessExpected
