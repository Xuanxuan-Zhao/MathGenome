import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit

/-!
Independent specification of K03.01.limit_algebra (paper.tex:226–236).
Scalars are exactly ℝ and ℂ. Sequence limits use the upstream epsilon
predicates, with Lean index n representing the manuscript's term n+1.
All limits are finite. The denominator need only have a nonzero limit;
nonvanishing of its terms is a conclusion on a tail, not a hypothesis.
The real order assertion uses an eventual weak inequality. The explicit
strict counterexample has positive terms at every shifted index.
-/

namespace Specs.SingleVariableAnalysis.Ch01.LimitAlgebra

open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

def realAdd : Prop :=
  ∀ (u v : ℕ → ℝ) (a b : ℝ) (_hu : realSequenceConvergesValue u a) (_hv : realSequenceConvergesValue v b),
    realSequenceConvergesValue (fun n => u n + v n) (a + b)

def realMul : Prop :=
  ∀ (u v : ℕ → ℝ) (a b : ℝ) (_hu : realSequenceConvergesValue u a) (_hv : realSequenceConvergesValue v b),
    realSequenceConvergesValue (fun n => u n * v n) (a * b)

def realConstMul : Prop :=
  ∀ (u : ℕ → ℝ) (a : ℝ) (_hu : realSequenceConvergesValue u a) (c : ℝ),
    realSequenceConvergesValue (fun n => c * u n) (c * a)

def realLinearCombination : Prop :=
  ∀ (u v : ℕ → ℝ) (a b : ℝ) (_hu : realSequenceConvergesValue u a) (_hv : realSequenceConvergesValue v b) (c d : ℝ),
    realSequenceConvergesValue (fun n => c * u n + d * v n) (c * a + d * b)

def realAbs : Prop :=
  ∀ (u : ℕ → ℝ) (a : ℝ) (_hu : realSequenceConvergesValue u a),
    realSequenceConvergesValue (fun n => |u n|) |a|

def realEventuallyNeZero : Prop :=
  ∀ (u : ℕ → ℝ) (a : ℝ) (_hu : realSequenceConvergesValue u a) (_ha : a ≠ 0),
    sequenceEventuallyValue (fun n => u n ≠ 0)

def realDenominatorBound : Prop :=
  ∀ (u : ℕ → ℝ) (a : ℝ) (_hu : realSequenceConvergesValue u a) (_ha : a ≠ 0),
    sequenceEventuallyValue (fun n => |a| / 2 ≤ |u n|)

def realInv : Prop :=
  ∀ (u : ℕ → ℝ) (a : ℝ) (_hu : realSequenceConvergesValue u a) (_ha : a ≠ 0),
    realSequenceConvergesValue (fun n => (u n)⁻¹) a⁻¹

def realDiv : Prop :=
  ∀ (u v : ℕ → ℝ) (a b : ℝ) (_hu : realSequenceConvergesValue u a) (_hv : realSequenceConvergesValue v b) (_hb : b ≠ 0),
    realSequenceConvergesValue (fun n => u n / v n) (a / b)

def complexAdd : Prop :=
  ∀ (u v : ℕ → ℂ) (a b : ℂ) (_hu : complexSequenceConvergesValue u a) (_hv : complexSequenceConvergesValue v b),
    complexSequenceConvergesValue (fun n => u n + v n) (a + b)

def complexMul : Prop :=
  ∀ (u v : ℕ → ℂ) (a b : ℂ) (_hu : complexSequenceConvergesValue u a) (_hv : complexSequenceConvergesValue v b),
    complexSequenceConvergesValue (fun n => u n * v n) (a * b)

def complexConstMul : Prop :=
  ∀ (u : ℕ → ℂ) (a : ℂ) (_hu : complexSequenceConvergesValue u a) (c : ℂ),
    complexSequenceConvergesValue (fun n => c * u n) (c * a)

def complexLinearCombination : Prop :=
  ∀ (u v : ℕ → ℂ) (a b : ℂ) (_hu : complexSequenceConvergesValue u a) (_hv : complexSequenceConvergesValue v b) (c d : ℂ),
    complexSequenceConvergesValue (fun n => c * u n + d * v n) (c * a + d * b)

def complexNorm : Prop :=
  ∀ (u : ℕ → ℂ) (a : ℂ) (_hu : complexSequenceConvergesValue u a),
    realSequenceConvergesValue (fun n => ‖u n‖) ‖a‖

def complexEventuallyNeZero : Prop :=
  ∀ (u : ℕ → ℂ) (a : ℂ) (_hu : complexSequenceConvergesValue u a) (_ha : a ≠ 0),
    sequenceEventuallyValue (fun n => u n ≠ 0)

def complexDenominatorBound : Prop :=
  ∀ (u : ℕ → ℂ) (a : ℂ) (_hu : complexSequenceConvergesValue u a) (_ha : a ≠ 0),
    sequenceEventuallyValue (fun n => ‖a‖ / 2 ≤ ‖u n‖)

def complexInv : Prop :=
  ∀ (u : ℕ → ℂ) (a : ℂ) (_hu : complexSequenceConvergesValue u a) (_ha : a ≠ 0),
    complexSequenceConvergesValue (fun n => (u n)⁻¹) a⁻¹

def complexDiv : Prop :=
  ∀ (u v : ℕ → ℂ) (a b : ℂ) (_hu : complexSequenceConvergesValue u a) (_hv : complexSequenceConvergesValue v b) (_hb : b ≠ 0),
    complexSequenceConvergesValue (fun n => u n / v n) (a / b)

def realLimitLeOfEventuallyLe : Prop :=
  ∀ (u v : ℕ → ℝ) (a b : ℝ),
    realSequenceConvergesValue u a → realSequenceConvergesValue v b →
    sequenceEventuallyValue (fun n => u n ≤ v n) → a ≤ b

/-- With shifted indexing, the positive-indexed sequence `1/n` is `1/(n+1)`. -/
def realStrictOrderCounterexample : Prop :=
  (∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1)) ∧
    realSequenceConvergesValue (fun _ => 0) 0 ∧
    realSequenceConvergesValue (fun n => 1 / ((n : ℝ) + 1)) 0 ∧
    ¬ (0 : ℝ) < 0

end Specs.SingleVariableAnalysis.Ch01.LimitAlgebra
