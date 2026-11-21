import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.WallisRecurrence
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Basic

/-!
K03.18.wallis, paper.tex:4206–4231, the two limits. The finite integral
identities and the sandwich are supplied by WallisRecurrence. The product
uses indices k = j + 1, j ∈ range n, so it is exactly the product from 1 to n
in the manuscript (and equals 1 at n = 0). The coefficient is the same
normalized central binomial coefficient as in the upstream specification.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.Wallis
open Filter
open scoped Topology
open WallisRecurrence

def productType : Type := ℕ → ℝ

def productValue : productType := fun n =>
  ∏ j ∈ Finset.range n,
    (2 * (j : ℝ) + 2) ^ 2 / ((2 * j + 1) * (2 * j + 3))

/-- The exact finite algebra connecting the product and central binomial coefficient. -/
def productCoefficientIdentity : Prop := ∀ n : ℕ,
  productValue n = 1 / ((2 * (n : ℝ) + 1) * coefficientValue n ^ 2)

/-- The squeeze uses the proper Darboux Wallis integrals, not a new integral. -/
def integralRatioLimit : Prop :=
  Tendsto (fun n => integralValue (2 * n + 1) / integralValue (2 * n)) atTop (𝓝 1)

/-- The finite identity connecting the product with the squeezed integral ratio. -/
def productRatioIdentity : Prop := ∀ n : ℕ,
  productValue n = (Real.pi / 2) * (integralValue (2 * n + 1) / integralValue (2 * n))

def productLimit : Prop := Tendsto productValue atTop (𝓝 (Real.pi / 2))

def coefficientLimit : Prop :=
  Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * coefficientValue n)
    atTop (𝓝 (1 / Real.sqrt Real.pi))

end Specs.SingleVariableAnalysis.Ch18.Wallis
