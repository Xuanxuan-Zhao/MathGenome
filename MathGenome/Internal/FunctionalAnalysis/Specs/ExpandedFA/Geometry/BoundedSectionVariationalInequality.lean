import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! Independent statements for `paper.tex`, fa2:p2:noncoercive-vi,
lines 13356–13397. The Hilbert space is real, with its given norm and
inner product. Monotonicity does not include strict monotonicity. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Geometry.BoundedSectionVariationalInequality.Spec
universe u

/-- The section tested against the specified feasible point. -/
def sectionSet {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (f : H) (K : Set H) (v₀ : H) : Set H :=
  {x | x ∈ K ∧ 0 ≤ ⟪A x - f, v₀ - x⟫_ℝ}

def Existence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H),
    (∀ x y : H, 0 ≤ ⟪A x - A y, x - y⟫_ℝ) →
    ∀ (K : Set H), K.Nonempty → IsClosed K → Convex ℝ K →
    ∀ (f : H), (∃ v₀ ∈ K, Bornology.IsBounded (sectionSet A f K v₀)) →
      ∃ x ∈ K, ∀ v ∈ K, 0 ≤ ⟪A x - f, v - x⟫_ℝ

def BoundedSetSection : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (f : H) (K : Set H),
    K.Nonempty → Bornology.IsBounded K →
      ∃ v₀ ∈ K, Bornology.IsBounded (sectionSet A f K v₀)

def CoerciveSection : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (α : ℝ), 0 < α →
    (∀ x : H, α * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ) →
    ∀ (f : H) (K : Set H), K.Nonempty →
      ∃ v₀ ∈ K, Bornology.IsBounded (sectionSet A f K v₀)

end ExpandedFA.Geometry.BoundedSectionVariationalInequality.Spec
