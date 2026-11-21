import MathGenome.Internal.Specs.D05.M08.Annihilating
import MathGenome.Internal.Specs.D05.Foundations.IdealsGcd
import Mathlib.FieldTheory.Minpoly.Basic

/-!
Independent specifications for K05.08.minpoly, paper.tex:1137–1143.
The scalar polynomials, evaluation map, and annihilator ideal are those of
the prerequisite interfaces. The endomorphism algebra is not assumed
commutative or nontrivial. All finite-dimensional spaces, including zero,
are in the domain of the definition.
-/

noncomputable section

namespace Specs.D05.M08.Minpoly

def minimalPolynomial_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Module.End K V → Polynomial K

/-- Mathlib's least-degree monic annihilator. Its existence in the present
setting and its agreement with the ideal-generator definition are obligations
below, rather than assumptions in this definition. -/
def minimalPolynomial_value : minimalPolynomial_type :=
  fun K _ _ _ _ _ T => minpoly K T

def monic : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (minimalPolynomial_value K V T).Monic

def ne_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    minimalPolynomial_value K V T ≠ 0

def annihilates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Evaluation.evaluation_value K V T (minimalPolynomial_value K V T) = 0

def ideal_generated : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Annihilating.annihilator_value K V T =
      Ideal.span {minimalPolynomial_value K V T}

/-- Uniqueness is among all monic generators, without a separate minimality
assumption on a competing polynomial. -/
def unique_monic_generator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    ∃! m : Polynomial K,
      m.Monic ∧ Annihilating.annihilator_value K V T = Ideal.span {m}

def least_degree : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (p : Polynomial K),
    p ∈ Annihilating.annihilator_value K V T → p ≠ 0 →
      (minimalPolynomial_value K V T).natDegree ≤ p.natDegree

/-- Both directions: every annihilator is a multiple, and every multiple
annihilates. In particular this includes the zero polynomial. -/
def divides_iff_annihilates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (p : Polynomial K),
    minimalPolynomial_value K V T ∣ p ↔
      p ∈ Annihilating.annihilator_value K V T

def multiples_annihilate : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (q : Polynomial K),
    Evaluation.evaluation_value K V T (q * minimalPolynomial_value K V T) = 0

def zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Subsingleton V] (T : Module.End K V),
    minimalPolynomial_value K V T = 1

def zero_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Module.finrank K V = 0 → minimalPolynomial_value K V T = 1

def positive_degree : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    0 < Module.finrank K V → 1 ≤ (minimalPolynomial_value K V T).natDegree

/-- The constant-polynomial argument used in the final sentence of the source
proof is valid precisely in positive dimension. -/
def nonzero_constant_not_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    0 < Module.finrank K V → ∀ a : K, a ≠ 0 →
      Polynomial.C a ∉ Annihilating.annihilator_value K V T

end Specs.D05.M08.Minpoly
