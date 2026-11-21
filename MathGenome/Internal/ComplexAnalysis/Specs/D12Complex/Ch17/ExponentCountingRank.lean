import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.OrderDivisorDefinitions
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Independent obligations for paper.tex:2954–2975 (the counting/exponent
identity and the canonical rank bounds). The index type retains repetitions.
No assertion of convergence at the infimum is part of these definitions. -/
noncomputable section
open Filter Set
open scoped Topology ENNReal

namespace D12Complex.ExponentCountingRank
open OrderDivisorDefinitions

/-- Finitely many entries, including repetitions, in every bounded disk. -/
def LocallyFiniteDivisor {ι : Type} (a : ι → ℂ) : Prop :=
  ∀ r : ℝ, Set.Finite {i | ‖a i‖ ≤ r}

/-- Closed-disk counting function; entries of the divisor are counted separately. -/
def countingFunction {ι : Type} (a : ι → ℂ) (r : ℝ) : ℕ :=
  Nat.card {i // ‖a i‖ ≤ r}

def countingQuotient {ι : Type} (a : ι → ℂ) (r : ℝ) : ℝ :=
  Real.log (max 1 (countingFunction a r : ℝ)) / Real.log r

def countingExponent {ι : Type} (a : ι → ℂ) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ENNReal.ofReal (countingQuotient a r)) atTop

/-- For positive radii, adding the multiplicity at the center counts all zeros. -/
def allZeroCountingFunction (f : NonzeroEntireFunction) (r : ℝ) : ℕ :=
  countingFunction (zeroLocation f) r + (analyticOrderAt f.toFun 0).toNat

end D12Complex.ExponentCountingRank

namespace Specs.D12Complex.Ch17.ExponentCountingRank
open _root_.D12Complex.OrderDivisorDefinitions _root_.D12Complex.ExponentCountingRank

def countingQuotient_nonneg_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (r : ℝ),
  1 < r → 0 ≤ countingQuotient a r

def zeros_locallyFinite_type : Prop := ∀ f : NonzeroEntireFunction,
  LocallyFiniteDivisor (zeroLocation f)

def summable_exponent_mono_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → ∀ {s t : ℝ}, s ≤ t →
  Summable (fun i => ‖a i‖ ^ (-s)) → Summable (fun i => ‖a i‖ ^ (-t))

def summable_bounds_counting_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → (∀ i, a i ≠ 0) → ∀ {s : ℝ}, 0 < s →
  Summable (fun i => ‖a i‖ ^ (-s)) →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → (countingFunction a r : ℝ) ≤ C * r ^ s

def counting_bound_summable_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → ∀ {u s : ℝ}, u < s →
  (∃ C : ℝ, ∀ᶠ r : ℝ in atTop, (countingFunction a r : ℝ) ≤ C * r ^ u) →
  Summable (fun i => ‖a i‖ ^ (-s))

def divisorExponent_eq_countingExponent_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → (∀ i, a i ≠ 0) →
  divisorExponent a = countingExponent a

def zero_divisorExponent_eq_limsup_type : Prop := ∀ f : NonzeroEntireFunction,
  divisorExponent (zeroLocation f) = countingExponent (zeroLocation f)

def finite_center_correction_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → ∀ m : ℕ,
  limsup (fun r : ℝ => ENNReal.ofReal
    (Real.log (max 1 ((countingFunction a r + m : ℕ) : ℝ)) / Real.log r)) atTop =
    countingExponent a

def all_zeros_eq_limsup_type : Prop := ∀ f : NonzeroEntireFunction,
  divisorExponent (zeroLocation f) =
    limsup (fun r : ℝ => ENNReal.ofReal
      (Real.log (max 1 (allZeroCountingFunction f r : ℝ)) / Real.log r)) atTop

def canonicalRank_bounds_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  LocallyFiniteDivisor a → ∀ q : ℕ, canonicalRank a = (q : ℕ∞) →
  (q : ℝ≥0∞) ≤ divisorExponent a ∧ divisorExponent a ≤ ((q + 1 : ℕ) : ℝ≥0∞)

def finite_divisor_bounds_type : Prop := ∀ {ι : Type} [Finite ι] (a : ι → ℂ),
  canonicalRank a = 0 ∧ divisorExponent a = 0

end Specs.D12Complex.Ch17.ExponentCountingRank
