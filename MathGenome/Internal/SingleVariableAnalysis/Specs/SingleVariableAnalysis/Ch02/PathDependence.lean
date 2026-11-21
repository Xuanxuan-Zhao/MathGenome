import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided

/-!
Independent specifications for K03.02.path_dependence, paper.tex:474–480.
The ambient quotient is tested on ℝ \ {0}; its totalized value at zero
plays no role. Shifted index n denotes the positive source index n+1.
-/
namespace Specs.SingleVariableAnalysis.Ch02.PathDependence

open RelativeLimit OneSided
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit

def ratioAbsPositive : Prop :=
  ∀ x : ℝ, 0 < x → x / |x| = 1

def ratioAbsNegative : Prop :=
  ∀ x : ℝ, x < 0 → x / |x| = -1

def ratioAbsRightLimit : Prop :=
  rightRelativeLimitValue (fun x : ℝ => x / |x|) ({0}ᶜ : Set ℝ) 0 1

def ratioAbsLeftLimit : Prop :=
  leftRelativeLimitValue (fun x : ℝ => x / |x|) ({0}ᶜ : Set ℝ) 0 (-1)

def ratioAbsNoTwoSidedLimit : Prop :=
  ¬ ∃ L : ℝ, relativePuncturedLimitValue (fun x : ℝ => x / |x|)
    ({0}ᶜ : Set ℝ) 0 L

def ratioAbsReciprocalValues : Prop :=
  ∀ n : ℕ, 0 < n → (1 / (n : ℝ)) / |1 / (n : ℝ)| = 1

def ratioAbsNegReciprocalValues : Prop :=
  ∀ n : ℕ, 0 < n → (-(1 / (n : ℝ))) / |-(1 / (n : ℝ))| = -1

def ratioAbsSamplingApproaches : Prop :=
  (∀ n : ℕ, (1 / ((n : ℝ) + 1)) ∈ ({0}ᶜ : Set ℝ) ∧
    (-(1 / ((n : ℝ) + 1))) ∈ ({0}ᶜ : Set ℝ)) ∧
  realSequenceConvergesValue (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 ∧
  realSequenceConvergesValue (fun n : ℕ => -(1 / ((n : ℝ) + 1))) 0

def ratioAbsSamplingLimits : Prop :=
  realSequenceConvergesValue
    (fun n : ℕ => (1 / ((n : ℝ) + 1)) / |1 / ((n : ℝ) + 1)|) 1 ∧
  realSequenceConvergesValue
    (fun n : ℕ => (-(1 / ((n : ℝ) + 1))) / |-(1 / ((n : ℝ) + 1))|) (-1) ∧
  (1 : ℝ) ≠ -1

end Specs.SingleVariableAnalysis.Ch02.PathDependence
