import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Independent statements for `fa2:p1:c05:linfinity-counterexample`,
paper.tex:1013–1025. Scalars range over both ℝ and ℂ. Coordinates use the
shared convention: natural index n denotes manuscript index n+1.
The counting-measure spaces are the ordinary almost-everywhere quotients;
the integral pairing is bilinear, without complex conjugation. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

universe u
namespace ExpandedFA.P1.C05LinfinityCounterexample
open C01SequenceSpaces

/-- The whole subspace c of convergent bounded scalar sequences. -/
def convergentSequences (𝕜 : Type u) [RCLike 𝕜] :
    Submodule 𝕜 (SequenceLInfinity 𝕜) where
  carrier := {x | ∃ l, Tendsto (fun n => x n) atTop (𝓝 l)}
  zero_mem' := ⟨0, tendsto_const_nhds⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, ha.add hb⟩
  smul_mem' := by
    rintro a x ⟨l, hl⟩
    exact ⟨a • l, hl.const_smul a⟩

namespace Spec

/-- The ordinary scalar limit is a continuous scalar-linear functional on c,
with its inherited supremum norm, and has operator norm one. -/
def LimitFunctional : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ f : convergentSequences 𝕜 →L[𝕜] 𝕜,
      (∀ (x : convergentSequences 𝕜) (l : 𝕜),
        Tendsto (fun n => x.val n) atTop (𝓝 l) → f x = l) ∧ ‖f‖ = 1

/-- A norm-one extension of the limit, including its values on every coordinate
vector and on the constant sequence, with no ℓ¹ coefficient representation. -/
def ExtensionCounterexample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ L : SequenceLInfinity 𝕜 →L[𝕜] 𝕜,
      ‖L‖ = 1 ∧
      (∀ (x : SequenceLInfinity 𝕜) (l : 𝕜),
        Tendsto (fun n => x n) atTop (𝓝 l) → L x = l) ∧
      (∀ j, L (lp.single ∞ j (1 : 𝕜)) = 0) ∧
      L (1 : SequenceLInfinity 𝕜) = 1 ∧
      ¬ ∃ a : SequenceLp 𝕜 1, ∀ x : SequenceLInfinity 𝕜,
        L x = ∑' n, a n * x n

/-- The two endpoint spaces identify isometrically with their ordinary
counting-measure Lp spaces, preserving all coordinates and the integral pairing.
In particular the pairing is integrable, not just a formal tsum. -/
def CountingIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ (Utop : SequenceLInfinity 𝕜 ≃ₗᵢ[𝕜] Lp 𝕜 ∞ (Measure.count : Measure ℕ))
      (U₁ : SequenceLp 𝕜 1 ≃ₗᵢ[𝕜] Lp 𝕜 1 (Measure.count : Measure ℕ)),
      (∀ x n, Utop x n = x n) ∧ (∀ a n, U₁ a n = a n) ∧
      (∀ a x, Integrable (fun n => Utop x n * U₁ a n) Measure.count ∧
        (∫ n, Utop x n * U₁ a n ∂Measure.count) = ∑' n, a n * x n)

/-- A continuous scalar-linear functional on ordinary L∞ of counting measure,
of norm one, which no ordinary L¹ density represents. -/
def MeasureCounterexample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ L : Lp 𝕜 ∞ (Measure.count : Measure ℕ) →L[𝕜] 𝕜,
      ‖L‖ = 1 ∧
      ¬ ∃ g : Lp 𝕜 1 (Measure.count : Measure ℕ),
        ∀ f : Lp 𝕜 ∞ (Measure.count : Measure ℕ),
          L f = ∫ n, f n * g n ∂Measure.count

end Spec
end ExpandedFA.P1.C05LinfinityCounterexample
