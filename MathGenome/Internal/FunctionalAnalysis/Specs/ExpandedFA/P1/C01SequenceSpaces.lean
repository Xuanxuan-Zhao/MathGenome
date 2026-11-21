import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.PNat.Basic

/-!
Independent interface for Definition `fa2:p1:c01:sequence-spaces`, paper.tex 222–230.
All four spaces use the same coordinates: natural index `n` means manuscript
index `n+1`. `lp` uses extended exponents; the finite-exponent specification below
explicitly identifies every real `p ≥ 1` with `ENNReal.ofReal p`.

The `c₀` object is literally a submodule of bounded sequences, with the induced
norm and topology. `c₀₀` has no distinguished norm in the definition: its maps
into the various normed sequence spaces specify each inherited norm separately.
-/

noncomputable section
open Filter
open scoped Topology ENNReal

universe u
namespace ExpandedFA.P1.C01SequenceSpaces

abbrev ScalarSequence (𝕜 : Type u) := ℕ → 𝕜

abbrev SequenceLp (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) :=
  lp (fun _ : ℕ => 𝕜) p

abbrev SequenceLInfinity (𝕜 : Type u) [RCLike 𝕜] := SequenceLp 𝕜 ∞

def sequenceC0Submodule (𝕜 : Type u) [RCLike 𝕜] :
    Submodule 𝕜 (SequenceLInfinity 𝕜) where
  carrier := {x | Tendsto (fun n => x n) atTop (𝓝 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' hx hy := by simpa using hx.add hy
  smul_mem' a x hx := by simpa using hx.const_smul a

abbrev SequenceC0 (𝕜 : Type u) [RCLike 𝕜] := ↥(sequenceC0Submodule 𝕜)

abbrev SequenceC00 (𝕜 : Type u) [Zero 𝕜] := ℕ →₀ 𝕜

namespace Spec

def LpType := ∀ (𝕜 : Type u) [RCLike 𝕜], ℝ≥0∞ → Type u
def LpValue : LpType := fun 𝕜 _ p => SequenceLp 𝕜 p
def LInfinityType := ∀ (𝕜 : Type u) [RCLike 𝕜], Type u
def LInfinityValue : LInfinityType := fun 𝕜 _ => SequenceLInfinity 𝕜
def C0Type := ∀ (𝕜 : Type u) [RCLike 𝕜], Type u
def C0Value : C0Type := fun 𝕜 _ => SequenceC0 𝕜
def C00Type := ∀ (𝕜 : Type u) [RCLike 𝕜], Type u
def C00Value : C00Type := fun 𝕜 _ => SequenceC00 𝕜

/-- No restriction to integer or rational exponents: all finite real `p ≥ 1`. -/
def FiniteLpIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (_hp : 1 ≤ p),
    (∀ x : ScalarSequence 𝕜,
      (∃ y : SequenceLp 𝕜 (ENNReal.ofReal p), (fun n => y n) = x) ↔
        Summable (fun n => ‖x n‖ ^ p)) ∧
    (∀ y : SequenceLp 𝕜 (ENNReal.ofReal p),
      ‖y‖ = (∑' n, ‖y n‖ ^ p) ^ (1 / p))

def BoundedIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ x : ScalarSequence 𝕜,
      (∃ y : SequenceLInfinity 𝕜, (fun n => y n) = x) ↔
        ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C) ∧
    (∀ y : SequenceLInfinity 𝕜,
      ‖y‖ = ⨆ n, ‖y n‖) ∧
    (∀ y : SequenceLInfinity 𝕜, IsLUB (Set.range fun n => ‖y n‖) ‖y‖)

def C0Identification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ x : ScalarSequence 𝕜,
      (∃ y : SequenceC0 𝕜, (fun n => y.val n) = x) ↔ Tendsto x atTop (𝓝 0)) ∧
    (∀ y : SequenceC0 𝕜, ‖y‖ = ‖y.val‖ ∧ ‖y‖ = ⨆ n, ‖y.val n‖) ∧
    Isometry (fun y : SequenceC0 𝕜 => y.val)

def C00Identification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : ScalarSequence 𝕜),
    (∃ y : SequenceC00 𝕜, (fun n => y n) = x) ↔ (Function.support x).Finite

def C00ToLpType :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞), SequenceC00 𝕜 →ₗ[𝕜] SequenceLp 𝕜 p
def C00ToLpValue : C00ToLpType := fun _ _ _ =>
  { toFun := fun x => ⟨(fun n => x n), (memℓp_zero x.hasFiniteSupport).of_exponent_ge bot_le⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def C00ToC0Type :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], SequenceC00 𝕜 →ₗ[𝕜] SequenceC0 𝕜

def LpToC0Type :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ∞ → SequenceLp 𝕜 p →ₗ[𝕜] SequenceC0 𝕜

/-- All inclusions are injective linear maps with precisely the same coordinates.
The last clause also records the canonical `ℓᵖ → ℓᑫ` inclusions for `p ≤ q`. -/
def Coercions : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ p : ℝ≥0∞, ∃ i : SequenceC00 𝕜 →ₗ[𝕜] SequenceLp 𝕜 p,
      (∀ x n, i x n = x n) ∧ Function.Injective i) ∧
    (∃ i : SequenceC00 𝕜 →ₗ[𝕜] SequenceC0 𝕜,
      (∀ x n, (i x).val n = x n) ∧ Function.Injective i) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
      ∃ i : SequenceLp 𝕜 p →ₗ[𝕜] SequenceC0 𝕜,
        (∀ x n, (i x).val n = x n) ∧ Function.Injective i) ∧
    (∀ (p q : ℝ≥0∞) (h : p ≤ q),
      (∀ (x : SequenceLp 𝕜 p) n,
        lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) h x n = x n) ∧
      Function.Injective (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) h))

def ZeroSequences : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      (∀ n, (0 : SequenceLp 𝕜 p) n = 0) ∧ ‖(0 : SequenceLp 𝕜 p)‖ = 0) ∧
    ((∀ n, (0 : SequenceC0 𝕜).val n = 0) ∧ ‖(0 : SequenceC0 𝕜)‖ = 0) ∧
    (∀ n, (0 : SequenceC00 𝕜) n = 0)

/-- The shift really is a bijection with the manuscript positive integers;
it preserves the norm formula, not just the names of coordinates. -/
def Reindexing : Prop :=
  (∀ n : ℕ, (Equiv.pnatEquivNat.symm n : ℕ) = n + 1) ∧
  (∀ (𝕜 : Type u) [RCLike 𝕜] (x : ℕ+ → 𝕜) (p : ℝ),
    (Summable (fun n : ℕ => ‖x (Equiv.pnatEquivNat.symm n)‖ ^ p) ↔
      Summable (fun j : ℕ+ => ‖x j‖ ^ p)) ∧
    (∑' n : ℕ, ‖x (Equiv.pnatEquivNat.symm n)‖ ^ p) =
      ∑' j : ℕ+, ‖x j‖ ^ p) ∧
  (∀ (𝕜 : Type u) [RCLike 𝕜] (x : ℕ+ → 𝕜),
    (⨆ n : ℕ, ‖x (Equiv.pnatEquivNat.symm n)‖) = ⨆ j : ℕ+, ‖x j‖) ∧
  (∀ (𝕜 : Type u) [RCLike 𝕜] (x : ℕ+ → 𝕜),
    Tendsto (fun n : ℕ => x (Equiv.pnatEquivNat.symm n)) atTop (𝓝 0) ↔
      Tendsto x atTop (𝓝 0)) ∧
  (∀ (𝕜 : Type u) [RCLike 𝕜] (x : ℕ+ → 𝕜),
    (Function.support (fun n : ℕ => x (Equiv.pnatEquivNat.symm n))).Finite ↔
      (Function.support x).Finite)

end Spec
end ExpandedFA.P1.C01SequenceSpaces
