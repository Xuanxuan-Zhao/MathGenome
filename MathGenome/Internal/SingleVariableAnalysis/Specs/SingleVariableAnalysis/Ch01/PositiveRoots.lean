import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Archimedean

/-!
Independent specification of K03.01.positive_roots (paper.tex:201–215).
The canonical objects here are defined by real suprema and integer powers,
without using the candidate or assuming a root certificate. All root claims
have `0 ≤ a` and positive integer degree. The rational power laws have
strictly positive bases; at zero only strictly positive rational exponents
are part of the specified extension. No negative exponent law at zero is
asserted. The natural degree `m > 0` represents the source's integer `m ≥ 1`.
-/
namespace Specs.SingleVariableAnalysis.Ch01.PositiveRoots

def nonnegativeRootType : Type := ℕ → ℝ → ℝ
noncomputable def nonnegativeRootValue : nonnegativeRootType :=
  fun m a => sSup {t : ℝ | 0 ≤ t ∧ t ^ m ≤ a}

def rationalPowerType : Type := ℝ → ℚ → ℝ
noncomputable def rationalPowerValue : rationalPowerType :=
  fun a q => nonnegativeRootValue q.den a ^ q.num

def rootNonneg : Prop := ∀ m : ℕ, 0 < m → ∀ a : ℝ, 0 ≤ a →
  0 ≤ nonnegativeRootValue m a

def rootPow : Prop := ∀ m : ℕ, 0 < m → ∀ a : ℝ, 0 ≤ a →
  nonnegativeRootValue m a ^ m = a

def rootIsLUB : Prop := ∀ m : ℕ, 0 < m → ∀ a : ℝ, 0 ≤ a →
  IsLUB {t : ℝ | 0 ≤ t ∧ t ^ m ≤ a} (nonnegativeRootValue m a)

def rootUnique : Prop := ∀ m : ℕ, 0 < m → ∀ a : ℝ, 0 ≤ a →
  ∀ r : ℝ, 0 ≤ r → r ^ m = a → r = nonnegativeRootValue m a

def rootExistsUnique : Prop := ∀ a : ℝ, 0 ≤ a → ∀ m : ℕ, 0 < m →
  ∃! r : ℝ, 0 ≤ r ∧ r ^ m = a

def rootPos : Prop := ∀ m : ℕ, 0 < m → ∀ a : ℝ, 0 < a →
  0 < nonnegativeRootValue m a

def rootZero : Prop := ∀ m : ℕ, 0 < m → nonnegativeRootValue m 0 = 0

def rootSqrt : Prop := ∀ a : ℝ, 0 ≤ a → nonnegativeRootValue 2 a = Real.sqrt a

def powerFraction : Prop := ∀ a : ℝ, 0 < a → ∀ (p : ℤ) (d : ℕ), 0 < d →
  rationalPowerValue a ((p : ℚ) / d) = nonnegativeRootValue d a ^ p

def powerFractionIndependent : Prop := ∀ a : ℝ, 0 < a →
  ∀ (p s : ℤ) (d e : ℕ), 0 < d → 0 < e →
  (p : ℚ) / d = (s : ℚ) / e →
  nonnegativeRootValue d a ^ p = nonnegativeRootValue e a ^ s

def powerPos : Prop := ∀ a : ℝ, 0 < a → ∀ q : ℚ, 0 < rationalPowerValue a q

def powerInt : Prop := ∀ a : ℝ, 0 < a → ∀ p : ℤ,
  rationalPowerValue a (p : ℚ) = a ^ p

def powerZeroExponent : Prop := ∀ a : ℝ, 0 < a → rationalPowerValue a 0 = 1

def powerOneExponent : Prop := ∀ a : ℝ, 0 < a → rationalPowerValue a 1 = a

def powerAdd : Prop := ∀ a : ℝ, 0 < a → ∀ q r : ℚ,
  rationalPowerValue a (q + r) = rationalPowerValue a q * rationalPowerValue a r

def powerNeg : Prop := ∀ a : ℝ, 0 < a → ∀ q : ℚ,
  rationalPowerValue a (-q) = (rationalPowerValue a q)⁻¹

def powerSub : Prop := ∀ a : ℝ, 0 < a → ∀ q r : ℚ,
  rationalPowerValue a (q - r) = rationalPowerValue a q / rationalPowerValue a r

def powerMulBase : Prop := ∀ a b : ℝ, 0 < a → 0 < b → ∀ q : ℚ,
  rationalPowerValue (a * b) q = rationalPowerValue a q * rationalPowerValue b q

def powerDivBase : Prop := ∀ a b : ℝ, 0 < a → 0 < b → ∀ q : ℚ,
  rationalPowerValue (a / b) q = rationalPowerValue a q / rationalPowerValue b q

def powerMulExponent : Prop := ∀ a : ℝ, 0 < a → ∀ q r : ℚ,
  rationalPowerValue (rationalPowerValue a q) r = rationalPowerValue a (q * r)

def powerZeroBase : Prop := ∀ q : ℚ, 0 < q → rationalPowerValue 0 q = 0

end Specs.SingleVariableAnalysis.Ch01.PositiveRoots
