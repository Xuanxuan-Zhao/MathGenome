import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.SupNormAlgebras
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent statements for paper.tex, `d10:16:polynomial`.
The Euclidean topology is represented by the finite product `Fin n → ℝ`.
Polynomial evaluation uses actual multivariate polynomials, not arbitrary
functions in an unspecified separating algebra. The closure below is in the
canonical chapter 13 uniform topology. No nonemptiness or positive-dimension
hypothesis is imposed. Intervals with reversed endpoints are allowed.
-/

namespace Specs.D10Topology.Ch16.PolynomialApproximation

/-- The statement on Euclidean space with its usual L² metric and topology. -/
def euclidean_polynomial_uniform_approximation : Prop :=
  ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K →
    ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε →
      ∃ p : MvPolynomial (Fin n) ℝ,
        ∀ x : K, |f x - MvPolynomial.eval (fun i => x.val i) p| < ε

def polynomial_uniform_approximation : Prop :=
  ∀ (n : ℕ) (K : Set (Fin n → ℝ)), IsCompact K →
    ∀ (f : C(K, ℝ)) (ε : ℝ), 0 < ε →
      ∃ p : MvPolynomial (Fin n) ℝ,
        ∀ x : K, |f x - MvPolynomial.eval x.val p| < ε

def polynomial_restrictions_dense : Prop :=
  ∀ (n : ℕ) (K : Set (Fin n → ℝ)), IsCompact K →
    SupNormAlgebras.uniformClosure
      {g : C(K, ℝ) | ∃ p : MvPolynomial (Fin n) ℝ,
        ∀ x : K, g x = MvPolynomial.eval x.val p} = Set.univ

def weierstrass_interval : Prop :=
  ∀ (a b : ℝ) (f : C(Set.Icc a b, ℝ)) (ε : ℝ), 0 < ε →
    ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |f x - p.eval x.val| < ε

/-- In dimension zero every continuous function is exactly a constant polynomial. -/
def zero_dimensional_constant : Prop :=
  ∀ (K : Set (Fin 0 → ℝ)) (f : C(K, ℝ)),
    ∃ c : ℝ, ∀ x : K, f x = MvPolynomial.eval x.val (MvPolynomial.C c)

/-- The zero constant is exact on an empty compact set in every dimension. -/
def empty_polynomial_exact : Prop :=
  ∀ (n : ℕ) (f : C((∅ : Set (Fin n → ℝ)), ℝ)),
    ∀ x : (∅ : Set (Fin n → ℝ)),
      f x = MvPolynomial.eval x.val (MvPolynomial.C (0 : ℝ))

end Specs.D10Topology.Ch16.PolynomialApproximation
