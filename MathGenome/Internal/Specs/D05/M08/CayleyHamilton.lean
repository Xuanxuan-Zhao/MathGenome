import MathGenome.Internal.Specs.D05.M05.Adjugate
import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M08.Minpoly

/-!
Independent specifications for K05.08.cayley_hamilton, paper.tex:1152–1162.
The characteristic and minimal polynomials and the evaluation homomorphism
are the shared prerequisite objects. The endomorphism algebra can be
noncommutative or the zero algebra. No splitting or characteristic assumption
is imposed, and finite dimension includes dimension zero.
-/

noncomputable section
namespace Specs.D05.M08.CayleyHamilton
open scoped BigOperators

/-- Cayley–Hamilton for every finite-dimensional endomorphism. -/
def annihilates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Evaluation.evaluation_value K V T (Charpoly.charpoly_value T) = 0

/-- The consequence for the monic generator of the annihilator ideal. -/
def minpoly_divides_charpoly : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Minpoly.minimalPolynomial_value K V T ∣ Charpoly.charpoly_value T

/-- The two conclusions of the source theorem, together. -/
def cayley_hamilton : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Evaluation.evaluation_value K V T (Charpoly.charpoly_value T) = 0 ∧
      Minpoly.minimalPolynomial_value K V T ∣ Charpoly.charpoly_value T

/-- The coefficient formulation with the paper's upper bound n = dim V. -/
def coefficient_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (∑ j ∈ Finset.range (Module.finrank K V + 1),
      (Charpoly.charpoly_value T).coeff j • T ^ j) = 0

/-- The zero-space case spells out chi = 1 and I = 0. -/
def zero_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Module.finrank K V = 0 →
      Charpoly.charpoly_value T = 1 ∧
      (LinearMap.id : Module.End K V) = 0 ∧
      Evaluation.evaluation_value K V T (Charpoly.charpoly_value T) = 0

/-- The adjugate coefficient recurrence from the source proof. B_j is
literally the coefficient matrix of the shared cofactor adjugate of xI-A.
The missing coefficient B_{-1} is zero. Stating the recurrence for all
natural j includes both endpoints of the source range 0 ≤ j ≤ n. -/
def adjugate_recurrence : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (j : ℕ),
    let B : ℕ → Matrix (Fin n) (Fin n) K := fun k i l =>
      (D05.M05.adjugate
        (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) -
          A.map Polynomial.C) i l).coeff k
    (if j = 0 then 0 else B (j - 1)) - A * B j =
      (Matrix.charpoly A).coeff j • (1 : Matrix (Fin n) (Fin n) K)

/-- Coefficients at and beyond n vanish: in particular B_n = 0, as
used at the upper endpoint of the source recurrence. Size zero is allowed. -/
def adjugate_coeff_vanish : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (j : ℕ), n ≤ j →
    (fun i l => (D05.M05.adjugate
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) -
        A.map Polynomial.C) i l).coeff j : Matrix (Fin n) (Fin n) K) = 0

/-- The finite polynomial-matrix expansion of the adjugate uses exactly
indices 0,...,n-1, with no noncommutative substitution. -/
def adjugate_expansion : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    let Q := D05.M05.adjugate
      (Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) - A.map Polynomial.C)
    Q = ∑ j ∈ Finset.range n,
      (fun i l => Polynomial.monomial j ((Q i l).coeff j) :
        Matrix (Fin n) (Fin n) (Polynomial K))

end Specs.D05.M08.CayleyHamilton
