import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M06.DirectSum
import Mathlib.RingTheory.Coprime.Basic

/-!
Independent specifications for K05.08.bezout_decomposition, paper.tex:1172–1181.
The evaluation is the canonical `Polynomial.aeval` of the upstream interface.
Multiplication in `Module.End` is composition, even when the algebra is
noncommutative or is the zero algebra. Coprimality is the ordinary Bézout
predicate on K[x]; no splitting or characteristic condition is imposed.
The assertions hold for arbitrary vector spaces, thus in particular for all
finite-dimensional spaces in the chapter, including the zero space.
-/

noncomputable section

namespace Specs.D05.M08.BezoutDecomposition

/-- Coprimality supplies polynomial coefficients, without assuming projections. -/
def bezout_coefficients : Prop :=
  ∀ {K : Type*} [Field K] (p q : Polynomial K), IsCoprime p q →
    ∃ a b : Polynomial K, a * p + b * q = 1

/-- Evaluate the Bézout identity and apply it to an arbitrary vector. -/
def decomposition_formula : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q a b : Polynomial K), a * p + b * q = 1 →
    ∀ v : V,
      v = Polynomial.aeval T b (Polynomial.aeval T q v) +
        Polynomial.aeval T a (Polynomial.aeval T p v)

/-- The two explicit terms lie in the stated kernels. -/
def component_membership : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K),
    Polynomial.aeval T (p * q) = 0 → ∀ (a b : Polynomial K) (v : V),
      Polynomial.aeval T b (Polynomial.aeval T q v) ∈
        LinearMap.ker (Polynomial.aeval T p) ∧
      Polynomial.aeval T a (Polynomial.aeval T p v) ∈
        LinearMap.ker (Polynomial.aeval T q)

/-- The internal direct sum means actual unique subspace components. -/
def kernel_direct_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K), IsCoprime p q →
    Polynomial.aeval T (p * q) = 0 →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun c : Bool => if c then LinearMap.ker (Polynomial.aeval T q)
          else LinearMap.ker (Polynomial.aeval T p))

/-- For every choice of Bézout coefficients these formulas give complementary
projections, with their exact images, kernels and commutation identities. -/
def projection_properties : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q a b : Polynomial K), a * p + b * q = 1 →
    Polynomial.aeval T (p * q) = 0 →
    let P := Polynomial.aeval T b * Polynomial.aeval T q
    let Q := Polynomial.aeval T a * Polynomial.aeval T p
    P + Q = 1 ∧ P ^ 2 = P ∧ Q ^ 2 = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧
      LinearMap.range P = LinearMap.ker (Polynomial.aeval T p) ∧
      LinearMap.ker P = LinearMap.ker (Polynomial.aeval T q) ∧
      LinearMap.range Q = LinearMap.ker (Polynomial.aeval T q) ∧
      LinearMap.ker Q = LinearMap.ker (Polynomial.aeval T p) ∧
      P * T = T * P ∧ Q * T = T * Q

/-- In particular both summands in the decomposition are T-invariant.
This follows for every polynomial kernel individually. -/
def kernel_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) (v : V),
    v ∈ LinearMap.ker (Polynomial.aeval T p) →
      T v ∈ LinearMap.ker (Polynomial.aeval T p)

end Specs.D05.M08.BezoutDecomposition
