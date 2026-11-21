import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.CanonicalFactors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Polynomial.Basic

/-! Independent specification of paper.tex:2859–2860,2937–2952.
The repeated divisor is intrinsic: a nonzero zero together with a position
below its analytic multiplicity. Order is only assigned to nonzero entire
functions. Finite rank lives in ℕ, extended rank in ℕ∞, and growth order
and convergence exponent in ℝ≥0∞. -/
noncomputable section
open Filter
open scoped Topology ENNReal

namespace D12Complex.OrderDivisorDefinitions

/-- Entire functions with the identically zero function explicitly excluded. -/
structure NonzeroEntireFunction where
  toFun : ℂ → ℂ
  holomorphic : HolomorphicOn Set.univ toFun
  nonzero : ∃ z, toFun z ≠ 0

/-- The intrinsic list of nonzero zeros, each repeated by its multiplicity. -/
def RepeatedZero (f : NonzeroEntireFunction) :=
  (z : {z : ℂ // z ≠ 0 ∧ f.toFun z = 0}) ×
    Fin (analyticOrderAt f.toFun z.val).toNat

end D12Complex.OrderDivisorDefinitions

namespace Specs.D12Complex.Ch17.OrderDivisorDefinitions
open _root_.D12Complex _root_.D12Complex.OrderDivisorDefinitions

/-- Supremum of the actual values on the radius-r circle. For continuous
functions and r>0, the implementation proves that it is an attained maximum. -/
def maximumModulus_type := (ℂ → ℂ) → ℝ → ℝ
def maximumModulus_value : maximumModulus_type := fun f r =>
  sSup ((fun z => ‖f z‖) '' Metric.sphere 0 r)

def growthQuotient_type := (ℂ → ℂ) → ℝ → ℝ
def growthQuotient_value : growthQuotient_type := fun f r =>
  Real.log (Real.log (max (Real.exp 1) (maximumModulus_value f r))) / Real.log r

/-- ofReal merely totalizes the quotient at small radii. For r>1 the
quotient is nonnegative, as separately verified. -/
def order_type := NonzeroEntireFunction → ℝ≥0∞
def order_value : order_type := fun f =>
  Filter.limsup (fun r : ℝ => ENNReal.ofReal (growthQuotient_value f.toFun r)) atTop

def zeroLocation_type := (f : NonzeroEntireFunction) → RepeatedZero f → ℂ
def zeroLocation_value : zeroLocation_type := fun _ i => i.1.val

def AdmissibleExponent_type := {ι : Type} → (ι → ℂ) → ℝ → Prop
def AdmissibleExponent_value : AdmissibleExponent_type := fun a s =>
  0 < s ∧ Summable (fun i => ‖a i‖ ^ (-s))

/-- The infimum of the positive summability exponents; sInf ∅ = ∞. -/
def divisorExponent_type := {ι : Type} → (ι → ℂ) → ℝ≥0∞
def divisorExponent_value : divisorExponent_type := fun a =>
  sInf {x | ∃ s : ℝ, AdmissibleExponent_value a s ∧ x = ENNReal.ofReal s}

def RankSummable_type := {ι : Type} → (ι → ℂ) → ℕ → Prop
def RankSummable_value : RankSummable_type := fun a q =>
  Summable (fun i => ‖a i‖ ^ (-((q : ℝ) + 1)))

/-- Least admissible nonnegative integer, with ∞ when none exists. -/
def canonicalRank_type := {ι : Type} → (ι → ℂ) → ℕ∞
def canonicalRank_value : canonicalRank_type := by
  classical
  exact fun a => if h : ∃ q, RankSummable_value a q then (Nat.find h : ℕ∞) else ⊤

/-- Source genus formula; natDegree assigns degree zero to constants. -/
def genus_type := ℕ → Polynomial ℂ → ℕ
def genus_value : genus_type := fun q Q => max q Q.natDegree

/-- An actual factorization at minimal canonical rank. Product convergence
is part of the meaning of the displayed product, not an existence assumption. -/
def IsCanonicalFactorization_type :=
  NonzeroEntireFunction → ℕ → ℕ → Polynomial ℂ → Prop
def IsCanonicalFactorization_value : IsCanonicalFactorization_type := fun f m q Q =>
  analyticOrderAt f.toFun 0 = (m : ℕ∞) ∧
  canonicalRank_value (zeroLocation_value f) = (q : ℕ∞) ∧
  ∃ P : ℂ → ℂ,
    (∀ z, HasProd (fun i : RepeatedZero f =>
      Specs.D12Complex.Ch16.CanonicalFactors.factor_value q (z / zeroLocation_value f i)) (P z)) ∧
    ∀ z, f.toFun z = z ^ m * P z * Complex.exp (Q.eval z)

/-- Genus attached to the displayed canonical-rank factorization. -/
def factorizationGenus_type := (f : NonzeroEntireFunction) → (m q : ℕ) →
  (Q : Polynomial ℂ) → IsCanonicalFactorization_value f m q Q → ℕ
def factorizationGenus_value : factorizationGenus_type := fun _ _ q Q _ => genus_value q Q

def polynomial_function_exists_type : Prop := ∀ (P : Polynomial ℂ), P ≠ 0 →
  ∃ f : NonzeroEntireFunction, f.toFun = P.eval

def zeroLocation_nonzero_type : Prop := ∀ (f : NonzeroEntireFunction) (i : RepeatedZero f),
  zeroLocation_value f i ≠ 0

def zeroLocation_is_zero_type : Prop := ∀ (f : NonzeroEntireFunction) (i : RepeatedZero f),
  f.toFun (zeroLocation_value f i) = 0

def maximumModulus_attained_type : Prop := ∀ (f : ℂ → ℂ), Continuous f →
  ∀ r : ℝ, 0 < r → ∃ z ∈ Metric.sphere (0 : ℂ) r,
    ‖f z‖ = maximumModulus_value f r ∧
    ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖f w‖ ≤ maximumModulus_value f r

def growthQuotient_nonneg_type : Prop := ∀ (f : ℂ → ℂ) (r : ℝ), 1 < r →
  0 ≤ growthQuotient_value f r

def order_polynomial_type : Prop := ∀ (P : Polynomial ℂ) (f : NonzeroEntireFunction),
  P ≠ 0 → f.toFun = P.eval → order_value f = 0

def order_constant_type : Prop := ∀ (c : ℂ) (f : NonzeroEntireFunction),
  c ≠ 0 → f.toFun = (fun _ => c) → order_value f = 0

def zero_multiplicity_finite_type : Prop := ∀ (f : NonzeroEntireFunction) (z : ℂ),
  analyticOrderAt f.toFun z ≠ ⊤

def repeatedZero_fiber_type : Prop := ∀ (f : NonzeroEntireFunction) (z : ℂ), z ≠ 0 →
  Nonempty ({i : RepeatedZero f // zeroLocation_value f i = z} ≃
    Fin (analyticOrderAt f.toFun z).toNat)

def divisorExponent_eq_top_of_no_exponent_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  (¬ ∃ s, AdmissibleExponent_value a s) → divisorExponent_value a = ⊤

def divisorExponent_finite_type : Prop := ∀ {ι : Type} [Finite ι] (a : ι → ℂ),
  divisorExponent_value a = 0

def canonicalRank_eq_top_iff_type : Prop := ∀ {ι : Type} (a : ι → ℂ),
  canonicalRank_value a = ⊤ ↔ ¬ ∃ q, RankSummable_value a q

def canonicalRank_eq_nat_iff_type : Prop := ∀ {ι : Type} (a : ι → ℂ) (q : ℕ),
  canonicalRank_value a = (q : ℕ∞) ↔
    RankSummable_value a q ∧ ∀ p < q, ¬ RankSummable_value a p

def canonicalRank_finite_type : Prop := ∀ {ι : Type} [Finite ι] (a : ι → ℂ),
  canonicalRank_value a = 0

def genus_constant_type : Prop := ∀ (q : ℕ) (c : ℂ), genus_value q (Polynomial.C c) = q

end Specs.D12Complex.Ch17.OrderDivisorDefinitions
