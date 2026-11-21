import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent statements for `fa2:p2:minimax`, paper.tex:13296–13359.
The reflexive and bilinear specializations are allocated to `ops_minimax_reflexive`.
All suprema/infima below are real. The boundedness and attainment clauses ensure
that they are genuine finite extrema, rather than default conditional suprema.
-/
namespace Specs.ExpandedFA.Geometry.CompactConvexMinimax
open Set
universe u v

noncomputable def sectionSup {E : Type u} {G : Type v}
    (L : Set G) (F : E → G → ℝ) (x : E) : ℝ := sSup (F x '' L)

noncomputable def sectionInf {E : Type u} {G : Type v}
    (K : Set E) (F : E → G → ℝ) (y : G) : ℝ := sInf ((fun x => F x y) '' K)

/-- The four attained extrema, their finite common value, and the saddle
inequalities for every pair of outer optimizers. -/
def MinimaxConclusion {E : Type u} {G : Type v}
    (K : Set E) (L : Set G) (F : E → G → ℝ) : Prop :=
  (∀ x ∈ K, BddAbove (F x '' L) ∧
    ∃ y ∈ L, IsMaxOn (F x) L y ∧ sectionSup L F x = F x y) ∧
  (∀ y ∈ L, BddBelow ((fun x => F x y) '' K) ∧
    ∃ x ∈ K, IsMinOn (fun x => F x y) K x ∧ sectionInf K F y = F x y) ∧
  BddBelow (sectionSup L F '' K) ∧
  BddAbove (sectionInf K F '' L) ∧
  sInf (sectionSup L F '' K) = sSup (sectionInf K F '' L) ∧
  (∃ x ∈ K, IsMinOn (sectionSup L F) K x ∧
    sectionSup L F x = sInf (sectionSup L F '' K)) ∧
  (∃ y ∈ L, IsMaxOn (sectionInf K F) L y ∧
    sectionInf K F y = sSup (sectionInf K F '' L)) ∧
  (∀ x₀ ∈ K, ∀ y₀ ∈ L,
    IsMinOn (sectionSup L F) K x₀ → IsMaxOn (sectionInf K F) L y₀ →
    ∀ x ∈ K, ∀ y ∈ L, F x₀ y ≤ F x₀ y₀ ∧ F x₀ y₀ ≤ F x y₀)

def compactConvexMinimaxType : Prop :=
  ∀ {E : Type u} {G : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [T2Space G]
    (K : Set E) (L : Set G) (F : E → G → ℝ),
    K.Nonempty → IsCompact K → Convex ℝ K →
    L.Nonempty → IsCompact L → Convex ℝ L →
    (∀ y ∈ L, ConvexOn ℝ K (fun x => F x y)) →
    (∀ y ∈ L, LowerSemicontinuousOn (fun x => F x y) K) →
    (∀ x ∈ K, ConcaveOn ℝ L (F x)) →
    (∀ x ∈ K, UpperSemicontinuousOn (F x) L) →
    MinimaxConclusion K L F

/-- Extending a payoff whose domain is exactly K × L adds no condition outside
K × L: every regularity/convexity assumption is relative to the indicated set. -/
noncomputable def extendPayoff {E : Type u} {G : Type v}
    {K : Set E} {L : Set G} (F : K → L → ℝ) (x : E) (y : G) : ℝ :=
  by
    classical
    exact if hx : x ∈ K then if hy : y ∈ L then F ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0

def restrictedMinimaxType : Prop :=
  ∀ {E : Type u} {G : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [T2Space G]
    (K : Set E) (L : Set G) (F : K → L → ℝ),
    K.Nonempty → IsCompact K → Convex ℝ K →
    L.Nonempty → IsCompact L → Convex ℝ L →
    (∀ y : L, ConvexOn ℝ K (fun x => extendPayoff F x y)) →
    (∀ y : L, LowerSemicontinuous (fun x : K => F x y)) →
    (∀ x : K, ConcaveOn ℝ L (extendPayoff F x)) →
    (∀ x : K, UpperSemicontinuous (F x)) →
    MinimaxConclusion K L (extendPayoff F)

end Specs.ExpandedFA.Geometry.CompactConvexMinimax
