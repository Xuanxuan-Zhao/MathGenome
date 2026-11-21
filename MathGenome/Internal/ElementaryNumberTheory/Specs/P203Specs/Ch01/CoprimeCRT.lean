import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.CompatibleCRT
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Int.Basic

/-! The coprime part of Theorem 1.6, paper.tex:268–322.
Positive integer moduli, arbitrary finite index types (including empty), and
integer ideal quotients realize exactly the source's residue rings. -/
namespace P203Specs.Ch01

universe u
open scoped BigOperators

/-- The ordinary integer residue ring, also defined for modulus one. -/
abbrev CRTResidue (m : ℤ) := ℤ ⧸ Ideal.span ({m} : Set ℤ)

/-- The source's sum, omitting all modulus-one factors. -/
noncomputable def coprimeCRTSum {ι : Type u} [Fintype ι]
    (m a u : ι → ℤ) : ℤ :=
  ∑ i, if 1 < m i then a i * ((∏ j, m j) / m i) * u i else 0

/-- Coefficients are required only at the nontrivial factors; the cofactors
are the actual integer quotients M/m_i. -/
def CoprimeCRTCofactors : Prop :=
  ∀ {ι : Type u} [Fintype ι] (m : ι → ℤ), (∀ i, 0 < m i) →
    (∀ i j, i ≠ j → Int.gcd (m i) (m j) = 1) →
    ∃ u : ι → ℤ, ∀ i, 1 < m i →
      m i ∣ ((∏ j, m j) / m i) * u i - 1

/-- The natural coordinate reduction is a ring isomorphism, with the
explicit inverse for every choice of coefficients and integer representatives. -/
def CoprimeCRTRing : Prop :=
  ∀ {ι : Type u} [Fintype ι] (m : ι → ℤ), (∀ i, 0 < m i) →
    (∀ i j, i ≠ j → Int.gcd (m i) (m j) = 1) →
    ∃ e : CRTResidue (∏ i, m i) ≃+* ∀ i, CRTResidue (m i),
      (∀ (r : ℤ) i, e (Ideal.Quotient.mk _ r) i = Ideal.Quotient.mk _ r) ∧
      ∀ u : ι → ℤ, (∀ i, 1 < m i → m i ∣ ((∏ j, m j) / m i) * u i - 1) →
        ∀ a : ι → ℤ,
          e.symm (fun i => Ideal.Quotient.mk _ (a i)) =
            Ideal.Quotient.mk _ (coprimeCRTSum m a u)

/-- Changing representatives or valid inverse coefficients does not change
the resulting residue class modulo M. -/
def CoprimeCRTChoiceIndependent : Prop :=
  ∀ {ι : Type u} [Fintype ι] (m : ι → ℤ), (∀ i, 0 < m i) →
    (∀ i j, i ≠ j → Int.gcd (m i) (m j) = 1) →
    ∀ (u v a b : ι → ℤ),
      (∀ i, 1 < m i → m i ∣ ((∏ j, m j) / m i) * u i - 1) →
      (∀ i, 1 < m i → m i ∣ ((∏ j, m j) / m i) * v i - 1) →
      (∀ i, m i ∣ a i - b i) →
      (∏ i, m i) ∣ coprimeCRTSum m a u - coprimeCRTSum m b v

/-- In the coprime case the nonnegative finite lcm is the product. -/
def CoprimeCRTLcm : Prop :=
  ∀ {ι : Type u} [Fintype ι] (m : ι → ℤ), (∀ i, 0 < m i) →
    (∀ i j, i ≠ j → Int.gcd (m i) (m j) = 1) →
    finiteCRTLcm Finset.univ m = ∏ i, m i

/-- Explicit degenerate cases: a modulus-one factor is a one-element ring;
in an empty family M=L=1, both rings are one-element rings, and the sum is zero. -/
def CoprimeCRTBoundary : Prop :=
  (Subsingleton (CRTResidue 1)) ∧
  (∀ {ι : Type u} [Fintype ι] [IsEmpty ι] (m a u : ι → ℤ),
    (∏ i, m i) = 1 ∧ finiteCRTLcm Finset.univ m = 1 ∧
    coprimeCRTSum m a u = 0 ∧
    Subsingleton (CRTResidue (∏ i, m i)) ∧
    Subsingleton (∀ i, CRTResidue (m i)))

end P203Specs.Ch01
