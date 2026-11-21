import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.MobiusInversion
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.HarmonicBasel

/-! The absolutely convergent series and quantitative input used in
paper.tex:1166–1202. Index `n` in each full series denotes the positive
integer `n+1`. Tail sums use natural indices selected by the real cutoff;
for the asserted cutoffs `y ≥ 1`, every selected index is positive. -/
namespace P203Specs.Ch03.MobiusReciprocalSquares

open P203Specs.ClassicalFunctions

noncomputable def mobiusTerm (n : ℕ) : ℝ :=
  (mu (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2

noncomputable def squareTerm (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℕ) : ℝ) ^ 2

noncomputable def squareTail (y : ℝ) : ℝ :=
  ∑' n : ℕ, if y < (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0

noncomputable def absoluteMobiusTail (y : ℝ) : ℝ :=
  ∑' n : ℕ, if y < (n : ℝ) then |(mu n : ℝ)| / (n : ℝ) ^ 2 else 0

noncomputable def mobiusTail (y : ℝ) : ℝ :=
  ∑' n : ℕ, if y < (n : ℝ) then (mu n : ℝ) / (n : ℝ) ^ 2 else 0

def AbsoluteConvergence : Prop := Summable (fun n => |mobiusTerm n|)

def ConvolutionProduct : Prop :=
  (∑' n, mobiusTerm n) * (∑' n, squareTerm n) = 1

def MobiusHasSum : Prop := HasSum mobiusTerm (6 / Real.pi ^ 2)

/-- Summability is included so that the totalized tsum cannot hide divergence. -/
def ReciprocalSquareTailBound : Prop :=
  ∀ y : ℝ, 1 ≤ y →
    Summable (fun n : ℕ => if y < (n : ℝ) then 1 / (n : ℝ) ^ 2 else 0) ∧
    squareTail y ≤ 2 / y

def AbsoluteMobiusTailBound : Prop :=
  ∀ y : ℝ, 1 ≤ y →
    Summable (fun n : ℕ => if y < (n : ℝ) then |(mu n : ℝ)| / (n : ℝ) ^ 2 else 0) ∧
    absoluteMobiusTail y ≤ 2 / y

def MobiusTailBound : Prop :=
  ∀ y : ℝ, 1 ≤ y →
    Summable (fun n : ℕ => if y < (n : ℝ) then (mu n : ℝ) / (n : ℝ) ^ 2 else 0) ∧
    |mobiusTail y| ≤ 2 / y

end P203Specs.Ch03.MobiusReciprocalSquares
