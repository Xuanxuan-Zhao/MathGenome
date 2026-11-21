import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Independent statements for paper.tex 16719–16750, `fa2:p4:sequence-duals`.
The coordinates and norms are exactly the canonical Part I spaces. Natural
coordinate n denotes manuscript coordinate n+1. All pairings are bilinear.
The space c below is the subspace of ℓ∞ consisting of convergent sequences,
with the inherited supremum norm. -/
noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.FunctionSpaces.SequenceDuals
open ExpandedFA.P1.C01SequenceSpaces

def c0Coordinate (𝕜 : Type u) [RCLike 𝕜] (j : ℕ) : SequenceC0 𝕜 :=
  ⟨lp.single ∞ j 1, by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop j] with n hn
    exact (lp.single_apply_ne (E := fun _ : ℕ => 𝕜) ∞ j 1 (ne_of_gt hn)).symm⟩

def convergentSubmodule (𝕜 : Type u) [RCLike 𝕜] :
    Submodule 𝕜 (SequenceLInfinity 𝕜) where
  carrier := {x | ∃ l, Tendsto (fun n => x n) atTop (𝓝 l)}
  zero_mem' := ⟨0, tendsto_const_nhds⟩
  add_mem' := by
    rintro x y ⟨l, hl⟩ ⟨m, hm⟩
    exact ⟨l + m, hl.add hm⟩
  smul_mem' := by
    rintro a x ⟨l, hl⟩
    exact ⟨a • l, hl.const_smul a⟩

abbrev SequenceConvergent (𝕜 : Type u) [RCLike 𝕜] := ↥(convergentSubmodule 𝕜)

/-- The actual (unique) limit of the coordinates. -/
def sequenceLimit {𝕜 : Type u} [RCLike 𝕜] (x : SequenceConvergent 𝕜) : 𝕜 :=
  Classical.choose x.property

namespace Spec

/-- The new c object includes every convergent scalar sequence and carries its
supremum norm; the chosen limit is the actual coordinate limit. -/
def ConvergentIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ x : ℕ → 𝕜,
      (∃ y : SequenceConvergent 𝕜, (fun n => y.val n) = x) ↔
        ∃ l, Tendsto x atTop (𝓝 l)) ∧
    (∀ y : SequenceConvergent 𝕜, ‖y‖ = ⨆ n, ‖y.val n‖) ∧
    (∀ y : SequenceConvergent 𝕜,
      Tendsto (fun n => y.val n) atTop (𝓝 (sequenceLimit y)))

def C0Duality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ U : SequenceLp 𝕜 1 ≃ₗᵢ[𝕜] (SequenceC0 𝕜 →L[𝕜] 𝕜),
      (∀ a x, Summable (fun n => ‖a n * x.val n‖) ∧
        U a x = ∑' n, a n * x.val n) ∧
      (∀ a, ‖U a‖ = ‖a‖) ∧
      (∀ f n, U.symm f n = f (c0Coordinate 𝕜 n)) ∧
      (∀ f : SequenceC0 𝕜 →L[𝕜] 𝕜,
        ∃! a : SequenceLp 𝕜 1, ∀ x, f x = ∑' n, a n * x.val n)

def L1Duality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ U : SequenceLInfinity 𝕜 ≃ₗᵢ[𝕜] (SequenceLp 𝕜 1 →L[𝕜] 𝕜),
      (∀ a x, Summable (fun n => ‖a n * x n‖) ∧ U a x = ∑' n, a n * x n) ∧
      (∀ a, ‖U a‖ = ‖a‖) ∧
      (∀ f n, U.symm f n = f (lp.single 1 n (1 : 𝕜)))

/-- Extended exponents retain every finite real p>1; the inverse equation
forces the finite conjugate q. The two Fact instances are automatic for these
exponents and only provide Mathlib's normed-space structures. -/
def LpDuality : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    1 < p → p ≠ ∞ → p⁻¹ + q⁻¹ = 1 →
    ∃ U : SequenceLp 𝕜 q ≃ₗᵢ[𝕜] (SequenceLp 𝕜 p →L[𝕜] 𝕜),
      (∀ a x, Summable (fun n => ‖a n * x n‖) ∧ U a x = ∑' n, a n * x n) ∧
      (∀ a, ‖U a‖ = ‖a‖) ∧
      (∀ f n, U.symm f n = f (lp.single p n (1 : 𝕜))) ∧
      (∀ f : SequenceLp 𝕜 p →L[𝕜] 𝕜,
        ∃! a : SequenceLp 𝕜 q, ∀ x, f x = ∑' n, a n * x n)

def ConvergentDual : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (L : SequenceConvergent 𝕜 →L[𝕜] 𝕜),
    ∃ ab : SequenceLp 𝕜 1 × 𝕜,
      (∀ x, Summable (fun n => ‖ab.1 n * x.val n‖) ∧
        L x = (∑' n, ab.1 n * x.val n) + ab.2 * sequenceLimit x) ∧
      ‖L‖ = (∑' n, ‖ab.1 n‖) + ‖ab.2‖ ∧
      ∀ cd : SequenceLp 𝕜 1 × 𝕜,
        (∀ x, L x = (∑' n, cd.1 n * x.val n) + cd.2 * sequenceLimit x) → cd = ab

/-- Conversely, every pair defines a continuous functional, with this norm.
Together with ConvergentDual this states the algebraic direct decomposition. -/
def ConvergentPairing : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (a : SequenceLp 𝕜 1) (b : 𝕜),
    ∃ L : SequenceConvergent 𝕜 →L[𝕜] 𝕜,
      (∀ x, Summable (fun n => ‖a n * x.val n‖) ∧
        L x = (∑' n, a n * x.val n) + b * sequenceLimit x) ∧
      ‖L‖ = (∑' n, ‖a n‖) + ‖b‖

end Spec
end ExpandedFA.FunctionSpaces.SequenceDuals
