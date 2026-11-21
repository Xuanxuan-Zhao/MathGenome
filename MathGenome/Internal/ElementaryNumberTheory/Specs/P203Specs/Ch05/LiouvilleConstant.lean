import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section

namespace P203Specs

/-- The source constant, with the index shifted so that the first factorial is `1!`.
This is precisely `∑_{j=1}^∞ 10^{-j!}` in paper.tex, §5.9. -/
def liouvilleConstant : ℝ :=
  ∑' n : ℕ, 1 / (10 : ℝ) ^ (n + 1).factorial

def LiouvilleConstantType : Type := ℝ

/-- Convergence of the exact series starting at `j = 1`. -/
def LiouvilleConstantSummable : Prop :=
  Summable (fun n : ℕ => 1 / (10 : ℝ) ^ (n + 1).factorial)

/-- The convergent series has the stated constant as its sum. -/
def LiouvilleConstantHasSum : Prop :=
  HasSum (fun n : ℕ => 1 / (10 : ℝ) ^ (n + 1).factorial) liouvilleConstant

/-- The explicit transcendental corollary, paper.tex lines 2566–2569. -/
def LiouvilleConstantTranscendental : Prop :=
  Transcendental ℚ liouvilleConstant

/-- The irrationality conclusion included in the source proof. -/
def LiouvilleConstantIrrational : Prop :=
  Irrational liouvilleConstant

end P203Specs
