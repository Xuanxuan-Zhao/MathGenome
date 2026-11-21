import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OAlgebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum

/-!
Independent specification of K03.06.composition (paper.tex:2839–2855).
The independent values below define ordinary finite polynomial operations.
Every theorem obligation is its full Prop type, with no assumed certificate.

All increment filters refine the real neighborhood of zero, including punctured,
one-sided, and domain-restricted approaches. The outer relative domain is a set
of scalar increments; eventual membership in insert 0 D permits inner zeros.
The equality F b = Q.eval 0 supplies the actual outer remainder at zero.
Compatible normed scalar towers cover real→real, real→complex, and complex→complex.
No differentiability or nonvanishing of the inner function is assumed. The source
order-n little-o and next-order big-O statements are kept separate. Comparison
with the real h^n has exactly the norm of its scalar embedding.

For division the explicit finite geometric reciprocal is multiplied by the
numerator and truncated. The denominator constant is assumed nonzero, while
nonvanishing of the denominator function is a conclusion. Theorems even permit
polynomials with higher degrees, as their discarded tails have higher order.
-/
namespace Specs.SingleVariableAnalysis.Ch06.Composition
open Polynomial Filter Asymptotics
open scoped Topology
open Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial (realPolynomialEvalValue)
universe u v

def truncatePolynomialType : Type (u+1) :=
  ∀ {K : Type u} [RCLike K], ℕ → Polynomial K → Polynomial K

noncomputable def truncatePolynomialValue {K : Type u} [RCLike K] (n : ℕ) (p : Polynomial K) : Polynomial K :=
  ∑ k ∈ Finset.range (n+1), monomial k (p.coeff k)

def compositionPolynomialType : Type (max (u+1) (v+1)) :=
  ∀ {K : Type u} [RCLike K] {L : Type v} [RCLike L] [NormedAlgebra K L], ℕ → Polynomial K → Polynomial L → Polynomial L

noncomputable def compositionPolynomialValue {K : Type u} [RCLike K] {L : Type v} [RCLike L] [NormedAlgebra K L] (n : ℕ) (P : Polynomial K) (Q : Polynomial L) : Polynomial L :=
  truncatePolynomialValue n (Q.comp (P.map (algebraMap K L)))

def reciprocalPolynomialType : Type (u+1) :=
  ∀ {K : Type u} [RCLike K], ℕ → Polynomial K → Polynomial K

noncomputable def reciprocalPolynomialValue {K : Type u} [RCLike K] (n : ℕ) (Q : Polynomial K) : Polynomial K :=
  C (Q.coeff 0)⁻¹ * ∑ j ∈ Finset.range (n+1), (1 - C (Q.coeff 0)⁻¹ * Q)^j

def quotientPolynomialType : Type (u+1) :=
  ∀ {K : Type u} [RCLike K], ℕ → Polynomial K → Polynomial K → Polynomial K

noncomputable def quotientPolynomialValue {K : Type u} [RCLike K] (n : ℕ) (P Q : Polynomial K) : Polynomial K :=
  truncatePolynomialValue n (P * reciprocalPolynomialValue n Q)

def truncatePolynomial_coeff : Prop :=
  ∀ {K : Type u} [RCLike K] (n : ℕ) (p : Polynomial K) (k : ℕ),
    (truncatePolynomialValue n p).coeff k = if k ≤ n then p.coeff k else 0

def truncatePolynomial_degree_le : Prop :=
  ∀ {K : Type u} [RCLike K] (n : ℕ) (p : Polynomial K),
    (truncatePolynomialValue n p).degree ≤ (n : WithBot ℕ)

def truncatePolynomial_dvd_remainder : Prop :=
  ∀ {K : Type u} [RCLike K] (n : ℕ) (p : Polynomial K),
    X ^ (n+1) ∣ p - truncatePolynomialValue n p

def reciprocalPolynomial_mul : Prop :=
  ∀ {K : Type u} [RCLike K] (n : ℕ) (Q : Polynomial K),
    Q * reciprocalPolynomialValue n Q = 1 - (1 - C (Q.coeff 0)⁻¹ * Q)^(n+1)

def quotientPolynomial_dvd_remainder : Prop :=
  ∀ {K : Type u} [RCLike K] (n : ℕ) (P Q : Polynomial K)
    (_hQ : Q.coeff 0 ≠ 0),
    X^(n+1) ∣ P - Q * quotientPolynomialValue n P Q

def compositionPolynomial_degree_le : Prop :=
  ∀ {K : Type u} [RCLike K] {L : Type v} [RCLike L] [NormedAlgebra K L] (n : ℕ) (P : Polynomial K) (Q : Polynomial L),
    (compositionPolynomialValue n P Q).degree ≤ (n : WithBot ℕ)

def quotientPolynomial_degree_le : Prop :=
  ∀ {K : Type u} [RCLike K] (n : ℕ) (P Q : Polynomial K),
    (quotientPolynomialValue n P Q).degree ≤ (n : WithBot ℕ)

def finite_composition_littleO : Prop :=
  ∀ {K : Type u} [RCLike K] {L : Type v} [RCLike L] [NormedAlgebra K L] [IsScalarTower ℝ K L] {l : Filter ℝ} (_hl : l ≤ 𝓝 0)
    (D : Set K) (n : ℕ) (_hn : 1 ≤ n) (u : ℝ → K) (b : K)
    (P : Polynomial K) (Q : Polynomial L) (F : K → L)
    (_hP : P.coeff 0 = 0) (_hQ : Q.degree ≤ (n : WithBot ℕ))
    (_hi : (fun h => u h - b - realPolynomialEvalValue P h) =o[l] (fun h : ℝ => h^n))
    (_hF : (fun z => F (b+z) - Q.eval (algebraMap K L z)) =o[𝓝[D \ {0}] 0]
      (fun z => z^n))
    (_hF0 : F b = Q.eval 0)
    (_hD : ∀ᶠ h in l, u h - b ∈ insert 0 D),
    (fun h => F (u h) - realPolynomialEvalValue (compositionPolynomialValue n P Q) h)
      =o[l] (fun h : ℝ => h^n)

def finite_composition_bigO : Prop :=
  ∀ {K : Type u} [RCLike K] {L : Type v} [RCLike L] [NormedAlgebra K L] [IsScalarTower ℝ K L] {l : Filter ℝ} (_hl : l ≤ 𝓝 0)
    (D : Set K) (n : ℕ) (_hn : 1 ≤ n) (u : ℝ → K) (b : K)
    (P : Polynomial K) (Q : Polynomial L) (F : K → L)
    (_hP : P.coeff 0 = 0) (_hQ : Q.degree ≤ (n : WithBot ℕ))
    (_hi : (fun h => u h - b - realPolynomialEvalValue P h) =O[l] (fun h : ℝ => h^(n+1)))
    (_hF : (fun z => F (b+z) - Q.eval (algebraMap K L z)) =O[𝓝[D \ {0}] 0]
      (fun z => z^(n+1)))
    (_hF0 : F b = Q.eval 0)
    (_hD : ∀ᶠ h in l, u h - b ∈ insert 0 D),
    (fun h => F (u h) - realPolynomialEvalValue (compositionPolynomialValue n P Q) h)
      =O[l] (fun h : ℝ => h^(n+1))

def finite_division_littleO : Prop :=
  ∀ {K : Type u} [RCLike K] {l : Filter ℝ} (_hl : l ≤ 𝓝 0)
    (n : ℕ) (_hn : 1 ≤ n) (f g : ℝ → K) (P Q : Polynomial K)
    (_hq : Q.coeff 0 ≠ 0)
    (_hf : (fun h => f h - realPolynomialEvalValue P h) =o[l] (fun h : ℝ => h^n))
    (_hg : (fun h => g h - realPolynomialEvalValue Q h) =o[l] (fun h : ℝ => h^n)),
    (∀ᶠ h in l, g h ≠ 0) ∧
      (fun h => f h / g h - realPolynomialEvalValue (quotientPolynomialValue n P Q) h)
        =o[l] (fun h : ℝ => h^n)

def finite_division_bigO : Prop :=
  ∀ {K : Type u} [RCLike K] {l : Filter ℝ} (_hl : l ≤ 𝓝 0)
    (n : ℕ) (_hn : 1 ≤ n) (f g : ℝ → K) (P Q : Polynomial K)
    (_hq : Q.coeff 0 ≠ 0)
    (_hf : (fun h => f h - realPolynomialEvalValue P h) =O[l] (fun h : ℝ => h^(n+1)))
    (_hg : (fun h => g h - realPolynomialEvalValue Q h) =O[l] (fun h : ℝ => h^(n+1))),
    (∀ᶠ h in l, g h ≠ 0) ∧
      (fun h => f h / g h - realPolynomialEvalValue (quotientPolynomialValue n P Q) h)
        =O[l] (fun h : ℝ => h^(n+1))

end Specs.SingleVariableAnalysis.Ch06.Composition
