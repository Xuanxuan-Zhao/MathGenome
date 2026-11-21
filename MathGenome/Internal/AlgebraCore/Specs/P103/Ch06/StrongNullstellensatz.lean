import Mathlib.RingTheory.Nullstellensatz

/-!
Independent statements for the geometric assertions of Theorem 6.7,
`paper.tex:1100–1105,1112`. The polynomial ring in n variables is
`MvPolynomial (Fin n) k`, and affine n-space is `Fin n → k`.
`MvPolynomial.zeroLocus` is the common zero set, and
`MvPolynomial.vanishingIdeal` consists of the polynomials vanishing
at every point of the given set. Both use evaluation in the base field.
No positivity hypothesis on n or properness hypothesis on J is imposed.
-/
namespace P103.Specs.Ch06.StrongNullstellensatz

universe u

/-- Maximal ideals are exactly kernels of evaluation at base-field points. -/
def maximal_iff_evaluation_kernelType : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) k)),
    m.IsMaximal ↔ ∃ x : Fin n → k, m = RingHom.ker (MvPolynomial.eval x)

/-- Evaluation at any point has maximal kernel, over any field. -/
def evaluation_kernel_maximalType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (x : Fin n → k),
    (RingHom.ker (MvPolynomial.eval x)).IsMaximal

/-- The strong Nullstellensatz, for every ideal, including the unit ideal. -/
def vanishingIdeal_zeroLocusType : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) k)),
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k J) = J.radical

/-- The unit ideal has no common zeroes, and its zero set has unit vanishing ideal. -/
def unit_idealType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    MvPolynomial.zeroLocus k (⊤ : Ideal (MvPolynomial (Fin n) k)) = ∅ ∧
    MvPolynomial.vanishingIdeal k
      (MvPolynomial.zeroLocus k (⊤ : Ideal (MvPolynomial (Fin n) k))) = ⊤

/-- Vanishing on the empty set imposes no condition. -/
def vanishingIdeal_emptyType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    MvPolynomial.vanishingIdeal k (∅ : Set (Fin n → k)) = ⊤

/-- Affine zero-space is a singleton. The main statements include this n. -/
def zero_variablesType : Prop :=
  ∀ (k : Type u) [Field k],
    (Set.univ : Set (Fin 0 → k)) = {fun i => Fin.elim0 i}

end P103.Specs.Ch06.StrongNullstellensatz
