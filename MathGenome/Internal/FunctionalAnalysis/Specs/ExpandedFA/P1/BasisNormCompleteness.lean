import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Independent specification for the completeness stage of the coordinate theorem,
paper.tex 3824–3860. All operations below are the original operations on E.
Completeness is stated using the Cauchy-sequence criterion for the displayed norm;
no continuity of the algebraic coordinates or projections is a hypothesis. -/

open Filter Topology
noncomputable section
universe u v
namespace ExpandedFA.P1.BasisNormCompleteness.Spec

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The source's supremum includes P₀. Boundedness is part of the conclusion. -/
def partialSumSupNorm (P : ℕ → E → E) (x : E) : ℝ := ⨆ N, ‖P N x‖

/-- A finite complete norm on the original vector space, dominating its given norm.
The scalar, addition, subtraction, zero and limits in the Cauchy criterion use
exactly the original vector-space operations, not new operations on a copy. -/
structure CompleteSupremumNorm (P : ℕ → E → E) : Prop where
  bounded : ∀ x, ∃ M : ℝ, ∀ N, ‖P N x‖ ≤ M
  nonneg : ∀ x, 0 ≤ partialSumSupNorm P x
  eq_zero : ∀ x, partialSumSupNorm P x = 0 ↔ x = 0
  add_le : ∀ x y, partialSumSupNorm P (x + y) ≤
    partialSumSupNorm P x + partialSumSupNorm P y
  smul : ∀ (c : 𝕜) x, partialSumSupNorm P (c • x) = ‖c‖ * partialSumSupNorm P x
  dominates : ∀ x, ‖x‖ ≤ partialSumSupNorm P x
  complete : ∀ (s : ℕ → E),
    (∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ k ≥ J,
      partialSumSupNorm P (s j - s k) < ε) →
    ∃ x : E, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J,
      partialSumSupNorm P (s j - x) < ε

namespace Expected

def partialSumSupNormType : Type _ :=
  ∀ {E : Type v} [NormedAddCommGroup E], (ℕ → E → E) → E → ℝ

def partialSumSupNormValue : partialSumSupNormType := @partialSumSupNorm

def raw_basis_complete : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    CompleteSupremumNorm (𝕜 := 𝕜) (ExpandedFA.P1.C15Basis.Spec.rawPartialSum h)

def finite_basis_complete : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e),
    CompleteSupremumNorm (𝕜 := 𝕜) (ExpandedFA.P1.C15Basis.Spec.finitePartialSum h)

def empty_basis_norm : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) (ExpandedFA.P1.C15Basis.Spec.emptyFamily (E := E)))
    (x : E), partialSumSupNorm (ExpandedFA.P1.C15Basis.Spec.finitePartialSum h) x = 0

end Expected
end ExpandedFA.P1.BasisNormCompleteness.Spec
