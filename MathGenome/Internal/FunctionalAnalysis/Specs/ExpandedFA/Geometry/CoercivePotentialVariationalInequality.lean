import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ExtendedConvexFunctions
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Independent statements for paper.tex, `fa2:p2:potential-vi`.
The finite heights r and s express the displayed real-valued difference on
D(φ), without assigning any meaning to infinity minus infinity.
No symmetry, nontriviality, or separability hypothesis is imposed. -/
noncomputable section
open Classical
open scoped InnerProductSpace
namespace ExpandedFA.Geometry.CoercivePotentialVariationalInequality.Spec
open P1.ExtendedConvexFunctions
universe u

/-- The source variational inequality, with its finite-domain guard. -/
def IsSolution {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (φ : ExtendedFunction H) (u : H) : Prop :=
  φ u ≠ ⊤ ∧ ∀ (v : H) (r s : ℝ), φ u = (r : WithTop ℝ) →
    φ v = (s : WithTop ℝ) → 0 ≤ ⟪A u, v - u⟫_ℝ + s - r

/-- I_K minus the continuous linear functional represented by f. -/
def ForcingPotential {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Set H) (f : H) : ExtendedFunction H :=
  fun v => if v ∈ K then ((-⟪f, v⟫_ℝ : ℝ) : WithTop ℝ) else ⊤

def PotentialVI : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (α : ℝ), 0 < α →
    (∀ x, α * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ) →
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∃! u, IsSolution A φ u

def ForcingProperties : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Set H), K.Nonempty → IsClosed K → Convex ℝ K → ∀ f : H,
    P1.ExtendedConvexFunctions.Spec.ProperValue H (ForcingPotential K f) ∧
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H (ForcingPotential K f) ∧
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H (ForcingPotential K f)

def ForcingSolutionIff : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) (K : Set H) (f u : H),
    IsSolution A (ForcingPotential K f) u ↔
      u ∈ K ∧ ∀ v ∈ K, 0 ≤ ⟪A u - f, v - u⟫_ℝ

def Stampacchia : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (α : ℝ), 0 < α →
    (∀ x, α * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ) →
    ∀ (K : Set H), K.Nonempty → IsClosed K → Convex ℝ K → ∀ f : H,
    ∃! u, u ∈ K ∧ ∀ v ∈ K, 0 ≤ ⟪A u - f, v - u⟫_ℝ

end ExpandedFA.Geometry.CoercivePotentialVariationalInequality.Spec
