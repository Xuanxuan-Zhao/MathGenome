import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open Polynomial Complex
namespace ExpandedFA.Moments

/-- The linear functional whose values on monomials are the prescribed real moments. -/
def momentFunctional (m : ℕ → ℝ) : ℂ[X] →ₗ[ℂ] ℂ :=
  { toFun := fun p => p.sum (fun n c => c * (m n : ℂ))
    map_add' := fun p q => Polynomial.sum_add_index p q _ (by simp) (by
      intros; exact add_mul _ _ _)
    map_smul' := fun c p => by
      rw [Polynomial.sum_smul_index]
      simp only [RingHom.id_apply, smul_eq_mul, mul_assoc, Polynomial.sum, Finset.mul_sum]
      simp }

@[simp] theorem momentFunctional_monomial (m : ℕ → ℝ) (n : ℕ) (c : ℂ) :
    momentFunctional m (monomial n c) = c * (m n : ℂ) := by
  simp [momentFunctional]

@[simp] theorem momentFunctional_X_pow (m : ℕ → ℝ) (n : ℕ) :
    momentFunctional m (X ^ n) = (m n : ℂ) := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, momentFunctional_monomial, one_mul]

/-- The conjugate-linear-first moment form. -/
def momentForm (m : ℕ → ℝ) (p q : ℂ[X]) : ℂ :=
  momentFunctional m (p.map (starRingEnd ℂ) * q)

/-- Finite Hankel positivity in the manuscript's coefficient notation. -/
def FiniteHankelNonnegative (m : ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (c : ℕ → ℂ), 0 ≤
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      (m (j + k) : ℂ) * star (c j) * c k).re

/-- All finite Hankel forms are nonnegative. The polynomial coefficients have
finite support, so this quantifies over exactly the finite coefficient vectors. -/
def HankelNonnegative (m : ℕ → ℝ) : Prop :=
  ∀ p : ℂ[X], 0 ≤ (momentForm m p p).re

@[simp] theorem momentFunctional_conj (m : ℕ → ℝ) (p : ℂ[X]) :
    momentFunctional m (p.map (starRingEnd ℂ)) = star (momentFunctional m p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [mul_comm]

theorem momentForm_conj_symm (m : ℕ → ℝ) (p q : ℂ[X]) :
    star (momentForm m q p) = momentForm m p q := by
  rw [momentForm, ← momentFunctional_conj]
  simp [momentForm, Polynomial.map_map, mul_comm]

theorem momentForm_add_left (m : ℕ → ℝ) (p q r : ℂ[X]) :
    momentForm m (p + q) r = momentForm m p r + momentForm m q r := by
  simp [momentForm, add_mul]

theorem momentForm_smul_left (m : ℕ → ℝ) (p q : ℂ[X]) (c : ℂ) :
    momentForm m (c • p) q = star c * momentForm m p q := by
  simp only [momentForm, ← Polynomial.C_mul', Polynomial.map_mul, Polynomial.map_C,
    mul_assoc]
  rw [Polynomial.C_mul', map_smul, smul_eq_mul]
  rfl

/-- The raw polynomials, with their moment seminorm rather than any coefficient norm. -/
def MomentPolynomials (m : ℕ → ℝ) (_ : HankelNonnegative m) := ℂ[X]

instance (m : ℕ → ℝ) (h : HankelNonnegative m) : CommRing (MomentPolynomials m h) :=
  inferInstanceAs (CommRing ℂ[X])
instance (m : ℕ → ℝ) (h : HankelNonnegative m) : Algebra ℂ (MomentPolynomials m h) :=
  inferInstanceAs (Algebra ℂ ℂ[X])

instance momentCore (m : ℕ → ℝ) (h : HankelNonnegative m) :
    PreInnerProductSpace.Core ℂ (MomentPolynomials m h) where
  inner := momentForm m
  conj_inner_symm := momentForm_conj_symm m
  re_inner_nonneg := h
  add_left := momentForm_add_left m
  smul_left := momentForm_smul_left m

instance (m : ℕ → ℝ) (h : HankelNonnegative m) :
    SeminormedAddCommGroup (MomentPolynomials m h) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance (m : ℕ → ℝ) (h : HankelNonnegative m) :
    InnerProductSpace ℂ (MomentPolynomials m h) := InnerProductSpace.ofCore (momentCore m h)

/-- Quotient by the null seminorm, including the zero quotient. -/
abbrev PolynomialQuotient (m : ℕ → ℝ) (h : HankelNonnegative m) :=
  SeparationQuotient (MomentPolynomials m h)

/-- The Hilbert completion of the polynomial quotient. -/
abbrev MomentHilbertSpace (m : ℕ → ℝ) (h : HankelNonnegative m) :=
  UniformSpace.Completion (PolynomialQuotient m h)

/-- The polynomial class in its Hilbert completion. -/
def polynomialClass (m : ℕ → ℝ) (h : HankelNonnegative m) :
    MomentPolynomials m h →ₗ[ℂ] MomentHilbertSpace m h :=
  (UniformSpace.Completion.toComplₗᵢ.toLinearMap).comp
    (SeparationQuotient.mkCLM ℂ (MomentPolynomials m h)).toLinearMap

/-- Forget the moment seminorm, retaining the underlying polynomial. -/
def rawPolynomial {m : ℕ → ℝ} {h : HankelNonnegative m}
    (p : MomentPolynomials m h) : ℂ[X] := p

/-- Regard an ordinary polynomial as a vector carrying the moment seminorm. -/
def ofPolynomial {m : ℕ → ℝ} {h : HankelNonnegative m}
    (p : ℂ[X]) : MomentPolynomials m h := p

@[simp] theorem rawPolynomial_ofPolynomial {m : ℕ → ℝ} {h : HankelNonnegative m}
    (p : ℂ[X]) : rawPolynomial (ofPolynomial (m := m) (h := h) p) = p := rfl

@[simp] theorem ofPolynomial_rawPolynomial {m : ℕ → ℝ} {h : HankelNonnegative m}
    (p : MomentPolynomials m h) : ofPolynomial (rawPolynomial p) = p := rfl

/-- Linear multiplication by the indeterminate on the raw polynomials. -/
def multiplyX (m : ℕ → ℝ) (h : HankelNonnegative m) :
    MomentPolynomials m h →ₗ[ℂ] MomentPolynomials m h :=
  { toFun := fun p => ofPolynomial ((X : ℂ[X]) * rawPolynomial p)
    map_add' := by intro p q; exact mul_add (X : ℂ[X]) p q
    map_smul' := by
      intro c p
      change (X : ℂ[X]) * (c • rawPolynomial p) = c • ((X : ℂ[X]) * rawPolynomial p)
      simp only [Algebra.smul_def]
      ring }

namespace PolynomialMomentHilbertSpaceSpec

/-- A linear section selecting polynomial representatives. Its eventual action
under multiplication will be independent of this choice. -/
def representative (m : ℕ → ℝ) (h : HankelNonnegative m) :
    (polynomialClass m h).range →ₗ[ℂ] MomentPolynomials m h :=
  Classical.choose ((polynomialClass m h).rangeRestrict.exists_rightInverse_of_surjective
    (polynomialClass m h).range_rangeRestrict)

/-- Multiplication on exactly the polynomial classes. -/
def multiplicationValue (m : ℕ → ℝ) (h : HankelNonnegative m) :
    Unbounded.Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h) :=
  { domain := (polynomialClass m h).range
    toFun := ((polynomialClass m h).comp (multiplyX m h)).comp (representative m h) }

/-- The null-polynomial submodule. -/
def nullSpaceValue (m : ℕ → ℝ) (h : HankelNonnegative m) :
    Submodule ℂ (MomentPolynomials m h) := (polynomialClass m h).ker

/-- The constant polynomial vector, with no normalization by m₀. -/
def constantValue (m : ℕ → ℝ) (h : HankelNonnegative m) : MomentHilbertSpace m h :=
  polynomialClass m h 1

def FormTypeExpected := (ℕ → ℝ) → ℂ[X] → ℂ[X] → ℂ
def QuotientTypeExpected := (m : ℕ → ℝ) → HankelNonnegative m → Type
def HilbertTypeExpected := (m : ℕ → ℝ) → HankelNonnegative m → Type
def NullTypeExpected := (m : ℕ → ℝ) → (h : HankelNonnegative m) →
  Submodule ℂ (MomentPolynomials m h)
def OperatorTypeExpected := (m : ℕ → ℝ) → (h : HankelNonnegative m) →
  Unbounded.Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h)
def ConstantTypeExpected := (m : ℕ → ℝ) → (h : HankelNonnegative m) → MomentHilbertSpace m h

def PositivityExpected : Prop := ∀ m : ℕ → ℝ,
  HankelNonnegative m ↔ FiniteHankelNonnegative m

def ZeroMassExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  m 0 = 0 → constantValue m h = 0 ∧ ∀ n, m n = 0

def FormFormulaExpected : Prop := ∀ (m : ℕ → ℝ) (p q : ℂ[X]),
  momentForm m p q = ∑ j ∈ p.support, ∑ k ∈ q.support,
    (m (j + k) : ℂ) * star (p.coeff j) * q.coeff k

def NullExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h),
  p ∈ nullSpaceValue m h ↔ momentForm m p p = 0

def NullMultiplicationExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h),
  p ∈ nullSpaceValue m h → multiplyX m h p ∈ nullSpaceValue m h

def ClassInnerExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p q : MomentPolynomials m h),
  inner ℂ (polynomialClass m h p) (polynomialClass m h q) = momentForm m p q

def DomainExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  (multiplicationValue m h).domain = (polynomialClass m h).range

def DenseExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  Dense ((multiplicationValue m h).domain : Set (MomentHilbertSpace m h))

def MultiplicationExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h),
  (multiplicationValue m h) ⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ =
    polynomialClass m h (ofPolynomial ((X : ℂ[X]) * rawPolynomial p))

def SymmetricExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m)
    (x y : (multiplicationValue m h).domain),
  inner ℂ (multiplicationValue m h x) (y : MomentHilbertSpace m h) =
    inner ℂ (x : MomentHilbertSpace m h) (multiplicationValue m h y)

/-- Exact operator powers with the shared domain-carrying product convention. -/
def PowersExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ)
    (p : MomentPolynomials m h),
  ∃ hp : polynomialClass m h p ∈
      (Unbounded.OperatorDomainsSpec.powerValue (multiplicationValue m h) n).domain,
    Unbounded.OperatorDomainsSpec.powerValue (multiplicationValue m h) n
      ⟨polynomialClass m h p, hp⟩ = polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n * rawPolynomial p))

def ConstantPowersExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ),
  ∃ he : constantValue m h ∈
      (Unbounded.OperatorDomainsSpec.powerValue (multiplicationValue m h) n).domain,
    Unbounded.OperatorDomainsSpec.powerValue (multiplicationValue m h) n
      ⟨constantValue m h, he⟩ = polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n))

def MomentsExpected : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ),
  inner ℂ (constantValue m h) (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n))) = (m n : ℂ)

end PolynomialMomentHilbertSpaceSpec
end ExpandedFA.Moments
