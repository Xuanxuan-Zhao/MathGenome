import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set
open scoped Topology ContDiff

namespace VariationalNotes.Ch06.EqualityChart.Specs

/-- Coordinates on the complement are in `Y`: the actual correction in `X`
is `k ↦ R (η k)`. The open cylinder is transported to `X` by the splitting
isomorphism in `SplittingType`, then translated by `a`. -/
def LocalEqualityGraph {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : X →L[ℝ] Y) (R : Y →L[ℝ] X) (r : ℕ∞ω)
    (U : Set X) (h : X → Y) (a : X) : Prop :=
  ∃ (V : Set B.ker) (W : Set Y) (η : B.ker → Y),
    IsOpen V ∧ IsOpen W ∧ (0 : B.ker) ∈ V ∧ (0 : Y) ∈ W ∧
    (∀ k ∈ V, ∀ y ∈ W, a + (k : X) + R y ∈ U) ∧
    η 0 = 0 ∧ MapsTo η V W ∧ ContDiffOn ℝ r η V ∧
    HasFDerivAt η (0 : B.ker →L[ℝ] Y) 0 ∧
    ContDiffOn ℝ r (fun k => R (η k)) V ∧
    HasFDerivAt (fun k => R (η k)) (0 : B.ker →L[ℝ] X) 0 ∧
    (∀ k ∈ V, ∀ y ∈ W, h (a + (k : X) + R y) = 0 ↔ y = η k)

/-- The same graph stated directly in an open neighborhood in the ambient space. -/
def AmbientEqualityGraph {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : X →L[ℝ] Y) (R : Y →L[ℝ] X) (r : ℕ∞ω)
    (U : Set X) (h : X → Y) (a : X) : Prop :=
  ∃ (V : Set B.ker) (N : Set X) (ψ : B.ker → X),
    IsOpen V ∧ (0 : B.ker) ∈ V ∧ IsOpen N ∧ a ∈ N ∧ N ⊆ U ∧
    ContDiffOn ℝ r ψ V ∧ ψ 0 = 0 ∧ HasFDerivAt ψ (0 : B.ker →L[ℝ] X) 0 ∧
    (∀ k ∈ V, ψ k ∈ R.range ∧ a + (k : X) + ψ k ∈ N ∧
      h (a + (k : X) + ψ k) = 0) ∧
    (∀ x ∈ N, h x = 0 ↔ ∃ k ∈ V, x = a + (k : X) + ψ k)

/-- A curve on an open, two-sided interval, with its ambient derivative. -/
def FeasibleCurves {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : X →L[ℝ] Y) (r : ℕ∞ω) (U : Set X) (h : X → Y) (a : X) : Prop :=
  ∀ d : B.ker, ∃ (ε : ℝ) (γ : ℝ → X), 0 < ε ∧
    γ 0 = a ∧ ContDiffOn ℝ r γ (Ioo (-ε) ε) ∧ HasDerivAt γ (d : X) 0 ∧
    ∀ t ∈ Ioo (-ε) ε, γ t ∈ U ∧ h (γ t) = 0

def SplittingType : Prop :=
  ∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : X →L[ℝ] Y) (R : Y →L[ℝ] X), B.comp R = ContinuousLinearMap.id ℝ Y →
    IsCompl B.ker R.range ∧ IsClosed (R.range : Set X) ∧
    ∃ e : (B.ker × Y) ≃L[ℝ] X, ∀ p, e p = (p.1 : X) + R p.2

def LocalEqualityChartType : Prop :=
  ∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (r : ℕ∞ω), 1 ≤ r → ∀ (U : Set X), IsOpen U →
    ∀ (h : X → Y), ContDiffOn ℝ r h U → ∀ a ∈ U, h a = 0 →
    ∀ (B : X →L[ℝ] Y), HasFDerivAt h B a →
    ∀ (R : Y →L[ℝ] X), B.comp R = ContinuousLinearMap.id ℝ Y →
    LocalEqualityGraph B R r U h a ∧ AmbientEqualityGraph B R r U h a ∧
      FeasibleCurves B r U h a

def FiniteTargetRightInverseType : Prop :=
  ∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (B : X →L[ℝ] Y), Function.Surjective B →
    ∃ R : Y →L[ℝ] X, B.comp R = ContinuousLinearMap.id ℝ Y

/-- Surjectivity suffices with a finite target, without restricting the domain dimension. -/
def FiniteTargetEqualityChartType : Prop :=
  ∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [FiniteDimensional ℝ Y]
    (r : ℕ∞ω), 1 ≤ r → ∀ (U : Set X), IsOpen U →
    ∀ (h : X → Y), ContDiffOn ℝ r h U → ∀ a ∈ U, h a = 0 →
    ∀ (B : X →L[ℝ] Y), HasFDerivAt h B a → Function.Surjective B →
    ∃ R : Y →L[ℝ] X, B.comp R = ContinuousLinearMap.id ℝ Y ∧
      LocalEqualityGraph B R r U h a ∧ AmbientEqualityGraph B R r U h a ∧
      FeasibleCurves B r U h a

end VariationalNotes.Ch06.EqualityChart.Specs
