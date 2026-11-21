import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14BallCharacterization
import Mathlib.Analysis.Convex.Basic

/-! Independent statements for `fa2:p2:minty-compact-domain`, paper.tex
13432–13466, including the sign qualifications at 13469–13483.
The continuous real-linear dual is taken in the original norm topology.
The operator is defined exactly on D; D need not be convex or nonempty.
-/
namespace Specs.ExpandedFA.Geometry.MintyCompactDomain
open Set
universe u

section
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {D : Set X}

/-- Monotonicity of a possibly nonlinear operator on its exact domain. -/
def DomainMonotone (A : D → (X →L[ℝ] ℝ)) : Prop :=
  ∀ x y : D, 0 ≤ (A x - A y) ((x : X) - y)

/-- Values outside D are used only to write segment continuity without
proof-dependent subtypes. Every evaluated segment in the theorem lies in D. -/
noncomputable def operatorValue (A : D → (X →L[ℝ] ℝ)) (x : X) : X →L[ℝ] ℝ := by
  classical
  exact if h : x ∈ D then A ⟨x, h⟩ else 0

/-- Scalar continuity along each closed segment of K, tested on each vector
of X (the usual weak-star hemicontinuity of an operator into X′). -/
def SegmentHemicontinuous (A : D → (X →L[ℝ] ℝ)) (K : Set X) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ z : X,
    ContinuousOn (fun t : ℝ => operatorValue A ((1-t) • x + t • y) z) (Icc 0 1)

def WeakMinty (A : D → (X →L[ℝ] ℝ)) (K : Set X) (u : X) : Prop :=
  ∀ v : D, (v : X) ∈ K → A v (u - v) ≤ 0

def VariationalInequality (A : D → (X →L[ℝ] ℝ)) (K : Set X) (u : X) : Prop :=
  ∀ v ∈ K, 0 ≤ operatorValue A u (v-u)
end

/-- Existence retains arbitrary domains and the empty D ∩ K case. -/
def WeakMintyExistence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (D K : Set X) (A : D → (X →L[ℝ] ℝ)),
      K.Nonempty → IsClosed K → Bornology.IsBounded K → Convex ℝ K →
      DomainMonotone A → ∃ u ∈ K, WeakMinty A K u

/-- Equivalence at every u ∈ K under the additional domain and continuity
hypotheses. This formulation also records which point solves both problems. -/
def MintyEquivalence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (D K : Set X) (A : D → (X →L[ℝ] ℝ)),
      K.Nonempty → IsClosed K → Bornology.IsBounded K → Convex ℝ K →
      DomainMonotone A → K ⊆ D → SegmentHemicontinuous A K →
      ∀ u ∈ K, (WeakMinty A K u ↔ VariationalInequality A K u)

end Specs.ExpandedFA.Geometry.MintyCompactDomain
