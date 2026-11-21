import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.PositiveRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
K03.07.real_powers, paper.tex:1626–1655, including order and endpoint
properties used subsequently. The exponential/logarithm representatives
have no asserted meaning for nonpositive bases. `partialRealPowerValue`
records the mathematical domain: positive bases with any real exponent,
and zero with strictly positive exponent only. Negative rational powers
are a separate algebraic interpretation, asserted only for negative bases
and odd reduced denominator. No comparison with the arbitrary negative-base
values of `Real.rpow` is claimed.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.RealPowers
open Set Filter
open scoped Topology

def realPowerType : Type := ℝ → ℝ → ℝ
def realPowerValue : realPowerType := fun x α => ExpConstruction.realSeriesExpValue (α * LogConstruction.seriesLogValue x)

def partialRealPowerType : Type := ℝ → ℝ → Option ℝ
def partialRealPowerValue : partialRealPowerType := fun x α => if 0 < x then some (realPowerValue x α)
  else if x = 0 ∧ 0 < α then some 0 else none

def negativeRationalPowerType : Type := ℝ → ℚ → ℝ
def negativeRationalPowerValue : negativeRationalPowerType := fun x q => (-Ch01.PositiveRoots.nonnegativeRootValue q.den (-x)) ^ q.num

def realPower_eq_rpow : Prop :=
  ∀ x : ℝ, 0 < x → ∀ α : ℝ, realPowerValue x α = x ^ α

def realPower_pos : Prop :=
  ∀ x : ℝ, 0 < x → ∀ α : ℝ, 0 < realPowerValue x α

def realPower_add : Prop :=
  ∀ x : ℝ, 0 < x → ∀ α β : ℝ,
  realPowerValue x (α + β) = realPowerValue x α * realPowerValue x β

def realPower_mul_base : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → ∀ α : ℝ,
  realPowerValue (x * y) α = realPowerValue x α * realPowerValue y α

def realPower_mul_exponent : Prop :=
  ∀ x : ℝ, 0 < x → ∀ α β : ℝ,
  realPowerValue (realPowerValue x α) β = realPowerValue x (α * β)

def realPower_zero_exponent : Prop :=
  ∀ x : ℝ, 0 < x → realPowerValue x 0 = 1

def realPower_one_exponent : Prop :=
  ∀ x : ℝ, 0 < x → realPowerValue x 1 = x

def realPower_int : Prop :=
  ∀ x : ℝ, 0 < x → ∀ p : ℤ, realPowerValue x (p : ℝ) = x ^ p

def realPower_rat : Prop :=
  ∀ x : ℝ, 0 < x → ∀ q : ℚ, realPowerValue x (q : ℝ) = Ch01.PositiveRoots.rationalPowerValue x q

def realPower_fraction : Prop :=
  ∀ x : ℝ, 0 < x → ∀ (p : ℤ) (d : ℕ), 0 < d →
  realPowerValue x ((p : ℝ) / d) = Ch01.PositiveRoots.nonnegativeRootValue d x ^ p

def realPower_fraction_pow : Prop :=
  ∀ x : ℝ, 0 < x → ∀ (p : ℤ) (d : ℕ), 0 < d →
  realPowerValue x ((p : ℝ) / d) ^ d = x ^ p

def realPower_root : Prop :=
  ∀ x : ℝ, 0 < x → ∀ d : ℕ, 0 < d →
  realPowerValue x (1 / (d : ℝ)) = Ch01.PositiveRoots.nonnegativeRootValue d x

def realPower_joint_continuous : Prop :=
  ContinuousOn (fun p : ℝ × ℝ => realPowerValue p.1 p.2)
  {p | 0 < p.1}

def realPower_continuous_base : Prop :=
  ∀ α : ℝ, ContinuousOn (fun x => realPowerValue x α) (Ioi 0)

def realPower_continuous_exponent : Prop :=
  ∀ x : ℝ, 0 < x → Continuous (realPowerValue x)

def realPower_strictMono_base : Prop :=
  ∀ α : ℝ, 0 < α → StrictMonoOn (fun x => realPowerValue x α) (Ioi 0)

def realPower_strictAnti_base : Prop :=
  ∀ α : ℝ, α < 0 → StrictAntiOn (fun x => realPowerValue x α) (Ioi 0)

def realPower_strictMono_exponent : Prop :=
  ∀ x : ℝ, 1 < x → StrictMono (realPowerValue x)

def realPower_strictAnti_exponent : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → StrictAnti (realPowerValue x)

def realPower_pos_tendsto_zero_right : Prop :=
  ∀ α : ℝ, 0 < α → Tendsto (fun x => realPowerValue x α) (𝓝[>] 0) (𝓝 0)

def realPower_pos_tendsto_atTop : Prop :=
  ∀ α : ℝ, 0 < α → Tendsto (fun x => realPowerValue x α) atTop atTop

def realPower_neg_tendsto_zero_right : Prop :=
  ∀ α : ℝ, α < 0 → Tendsto (fun x => realPowerValue x α) (𝓝[>] 0) atTop

def realPower_neg_tendsto_atTop : Prop :=
  ∀ α : ℝ, α < 0 → Tendsto (fun x => realPowerValue x α) atTop (𝓝 0)

def realPower_zero_continuous_extension : Prop :=
  ∀ α : ℝ, 0 < α → ∃ f : ℝ → ℝ,
  f 0 = 0 ∧ (∀ x : ℝ, 0 < x → f x = realPowerValue x α) ∧ ContinuousOn f (Ici 0)

def partialRealPower_positive : Prop :=
  ∀ x : ℝ, 0 < x → ∀ α : ℝ,
  partialRealPowerValue x α = some (realPowerValue x α)

def partialRealPower_zero : Prop :=
  ∀ α : ℝ, 0 < α → partialRealPowerValue 0 α = some 0

def partialRealPower_domain : Prop :=
  ∀ x α : ℝ, (partialRealPowerValue x α).isSome = true ↔
  0 < x ∨ (x = 0 ∧ 0 < α)

def partialRealPower_zero_undefined : Prop :=
  ∀ α : ℝ, α ≤ 0 → partialRealPowerValue 0 α = none

def partialRealPower_negative_undefined : Prop :=
  ∀ x : ℝ, x < 0 → ∀ α : ℝ, partialRealPowerValue x α = none

def negativeRationalPower_root : Prop :=
  ∀ x : ℝ, x < 0 → ∀ q : ℚ, Odd q.den →
  negativeRationalPowerValue x q ^ q.den = x ^ q.num

def negativeRationalPower_unique : Prop :=
  ∀ x : ℝ, x < 0 → ∀ q : ℚ, Odd q.den →
  ∀ y : ℝ, y ^ q.den = x ^ q.num → y = negativeRationalPowerValue x q

def negativeRationalPower_int : Prop :=
  ∀ x : ℝ, x < 0 → ∀ p : ℤ,
  negativeRationalPowerValue x (p : ℚ) = x ^ p

def negative_base_no_all_real_power_laws : Prop :=
  ∀ x : ℝ, x < 0 →
  ¬ ∃ P : ℝ → ℝ, P 1 = x ∧ ∀ α β : ℝ, P (α + β) = P α * P β

end Specs.SingleVariableAnalysis.Ch07.RealPowers
