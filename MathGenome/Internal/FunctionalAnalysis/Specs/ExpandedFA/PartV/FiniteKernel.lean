import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm

/-!
Independent specification of `fa2:p5:finite-kernel`, paper.tex:21795–21812.
The dual consists of continuous scalar-linear functionals. `Fin m` indexes all
terms, including the empty representation when `m = 0`. No independence of
either family, or nonzero condition on the parameter, is imposed.
-/

namespace ExpandedFA.PartV.FiniteKernel

open scoped BigOperators

universe u v

variable {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] {m : ℕ}

/-- The finite-rank operator with the given, possibly redundant representation. -/
noncomputable def finiteRankOperator (a : Fin m → X)
    (ℓ : Fin m → X →L[𝕜] 𝕜) : X →L[𝕜] X :=
  ∑ j, (ℓ j).smulRight (a j)

/-- Coordinates are functional values, not coefficients in a chosen basis. -/
def coordinates (ℓ : Fin m → X →L[𝕜] 𝕜) (u : X) : Fin m → 𝕜 :=
  fun i => ℓ i u

/-- The affine reconstruction map for the given right-hand side. -/
def reconstruct (a : Fin m → X) (z : 𝕜) (f : X) (c : Fin m → 𝕜) : X :=
  f + z • ∑ j, c j • a j

/-- All solutions of the original operator equation. -/
def operatorSolutions (a : Fin m → X) (ℓ : Fin m → X →L[𝕜] 𝕜)
    (z : 𝕜) (f : X) : Set X :=
  {u | u - z • finiteRankOperator a ℓ u = f}

/-- All solutions of the scalar matrix equation, with entries `ℓ i (a j)`. -/
def matrixSolutions (a : Fin m → X) (ℓ : Fin m → X →L[𝕜] 𝕜)
    (z : 𝕜) (f : X) : Set (Fin m → 𝕜) :=
  {c | ∀ i, c i - z * ∑ j, ℓ i (a j) * c j = ℓ i f}

namespace Spec

/-- The two equations in the source, with the coordinates fixed as `ℓ i u`. -/
def ExactReduction : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (m : ℕ) (a : Fin m → X)
    (ℓ : Fin m → X →L[𝕜] 𝕜) (z : 𝕜) (f u : X),
    u ∈ operatorSolutions a ℓ z f ↔
      coordinates ℓ u ∈ matrixSolutions a ℓ z f ∧
      u = reconstruct a z f (coordinates ℓ u)

/-- Every matrix solution reconstructs a solution with exactly those coordinates;
it is the unique operator solution having those coordinates. -/
def UniqueReconstruction : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (m : ℕ) (a : Fin m → X)
    (ℓ : Fin m → X →L[𝕜] 𝕜) (z : 𝕜) (f : X) (c : Fin m → 𝕜),
    c ∈ matrixSolutions a ℓ z f →
      (reconstruct a z f c ∈ operatorSolutions a ℓ z f ∧
        coordinates ℓ (reconstruct a z f c) = c) ∧
      ∃! u : X, u ∈ operatorSolutions a ℓ z f ∧ coordinates ℓ u = c

/-- The full solution sets correspond bijectively, via the stated coordinate
and reconstruction maps. In particular, no spurious matrix solutions occur
even for redundant representations. This also includes empty solution sets. -/
def SolutionSetEquivalence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (m : ℕ) (a : Fin m → X)
    (ℓ : Fin m → X →L[𝕜] 𝕜) (z : 𝕜) (f : X),
    ∃ e : {u // u ∈ operatorSolutions a ℓ z f} ≃
        {c // c ∈ matrixSolutions a ℓ z f},
      (∀ u, (e u).val = coordinates ℓ u.val) ∧
      (∀ c, (e.symm c).val = reconstruct a z f c.val)

end Spec
end ExpandedFA.PartV.FiniteKernel
