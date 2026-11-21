import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertBesselParseval
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
The annihilator boundary in paper.tex 7749–7806. The finite projection,
Bessel and Parseval statements are those of the imported independent Spec.
The explicit counterexample uses ℓ²(Option ℕ, 𝕜), the coordinate realization
of 𝕜 ⊕ ℓ²(ℕ, 𝕜): `none` is the first coordinate and `some n` the tail.
No completeness assumption is attached to the graph subspace.
-/
noncomputable section
open scoped InnerProductSpace
open Filter Topology

namespace ExpandedFA.Hilbert.PreHilbertTotalityBoundary
universe u v w

abbrev Ambient (𝕜 : Type u) [RCLike 𝕜] := lp (fun _ : Option ℕ => 𝕜) 2

def graphGenerator (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : Ambient 𝕜 :=
  lp.single 2 none 1 + lp.single 2 (some n) 1

def graphMap (𝕜 : Type u) [RCLike 𝕜] : (ℕ →₀ 𝕜) →ₗ[𝕜] Ambient 𝕜 :=
  Finsupp.linearCombination 𝕜 (graphGenerator 𝕜)

def graphSpace (𝕜 : Type u) [RCLike 𝕜] : Submodule 𝕜 (Ambient 𝕜) :=
  (graphMap 𝕜).range

abbrev GraphSpace (𝕜 : Type u) [RCLike 𝕜] := ↥(graphSpace 𝕜)

def firstCoordinate (𝕜 : Type u) [RCLike 𝕜] : GraphSpace 𝕜 →L[𝕜] 𝕜 :=
  (lp.evalCLM 𝕜 (fun _ : Option ℕ => 𝕜) 2 none).comp (graphSpace 𝕜).subtypeL

def zeroSumSpace (𝕜 : Type u) [RCLike 𝕜] : Submodule 𝕜 (GraphSpace 𝕜) :=
  (firstCoordinate 𝕜).ker

def generator (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : GraphSpace 𝕜 :=
  ⟨graphGenerator 𝕜 n, Finsupp.single n 1, by simp [graphMap]⟩

/-- The manuscript's (0,e_j-e_{j+1}), with indices starting at zero. -/
def differenceSequence (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : GraphSpace 𝕜 :=
  generator 𝕜 n - generator 𝕜 (n + 1)

def normalizedSequence (𝕜 : Type u) [RCLike 𝕜] : ℕ → GraphSpace 𝕜 :=
  InnerProductSpace.gramSchmidtNormed 𝕜 (differenceSequence 𝕜)

namespace Spec

def Expansions : Prop :=
  PreHilbertBesselParseval.Spec.FiniteProjectionIdentity.{u,v,w} ∧
  PreHilbertBesselParseval.Spec.Bessel.{u,v,w} ∧
  PreHilbertBesselParseval.Spec.CountableCoefficientSupport.{u,v,w} ∧
  PreHilbertBesselParseval.Spec.ClosedSpanIffNetConvergence.{u,v,w} ∧
  PreHilbertBesselParseval.Spec.NetConvergenceIffParseval.{u,v,w} ∧
  PreHilbertBesselParseval.Spec.TotalIffParseval.{u,v,w}

/-- This implication holds for every subspace, without completeness. -/
def DenseImpliesZeroAnnihilator : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (M : Submodule 𝕜 E),
    M.topologicalClosure = ⊤ → M.orthogonal = ⊥

def HilbertConverse : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (M : Submodule 𝕜 E), M.orthogonal = ⊥ → M.topologicalClosure = ⊤

/-- Exact identification with the graph of the finite summation functional. -/
def GraphCoordinates : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (f : Ambient 𝕜),
    f ∈ graphSpace 𝕜 ↔ ∃ a : ℕ →₀ 𝕜,
      f none = a.sum (fun _ c => c) ∧ ∀ n, f (some n) = a n

/-- The graph carries precisely the inherited Hilbert direct-sum norm. -/
def GraphNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (a : ℕ →₀ 𝕜),
    ‖graphMap 𝕜 a‖ ^ 2 = ‖a.sum (fun _ c => c)‖ ^ 2 +
      ∑ n ∈ a.support, ‖a n‖ ^ 2

/-- Exact coordinate description of M, inside the graph E. -/
def ZeroSumCoordinates : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : GraphSpace 𝕜),
    x ∈ zeroSumSpace 𝕜 ↔ ∃ a : ℕ →₀ 𝕜,
      x.val none = 0 ∧ a.sum (fun _ c => c) = 0 ∧ ∀ n, x.val (some n) = a n

def ClosedProper : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    IsClosed (zeroSumSpace 𝕜 : Set (GraphSpace 𝕜)) ∧ zeroSumSpace 𝕜 ≠ ⊤

def ZeroAnnihilator : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], (zeroSumSpace 𝕜).orthogonal = ⊥

def Incomplete : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ CompleteSpace (GraphSpace 𝕜)

/-- The actual normalized finite Gram–Schmidt recursion, without deleting indices. -/
def GramSchmidtBoundary : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    LinearIndependent 𝕜 (differenceSequence 𝕜) ∧
    Orthonormal 𝕜 (normalizedSequence 𝕜) ∧
    Submodule.span 𝕜 (Set.range (differenceSequence 𝕜)) = zeroSumSpace 𝕜 ∧
    Submodule.span 𝕜 (Set.range (normalizedSequence 𝕜)) = zeroSumSpace 𝕜 ∧
    (Submodule.span 𝕜 (Set.range (normalizedSequence 𝕜))).topologicalClosure =
      zeroSumSpace 𝕜 ∧
    (Submodule.span 𝕜 (Set.range (normalizedSequence 𝕜))).orthogonal = ⊥

end Spec
end ExpandedFA.Hilbert.PreHilbertTotalityBoundary
