import MathGenome.Internal.Specs.D05.M08.Minpoly
import MathGenome.Internal.Specs.D05.M06.InvariantDecomposition

/-!
Independent specifications for K05.08.primary, paper.tex:1183–1191.
An arbitrary finite index type represents the factors, including the empty
factorization. The summands are the actual kernels of powers of evaluated
irreducibles. The projections below are the canonical component projections
of the external-to-internal summation map, not arbitrary idempotents having
the same image. No characteristic or splitting hypothesis is imposed.
-/

noncomputable section

namespace Specs.D05.M08.Primary

/-- Full primary decomposition, with unique expansions, invariant summands,
and polynomial formulas for the genuine component projections. -/
def primary_decomposition : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (T : Module.End K V) (p : ι → Polynomial K) (a : ι → ℕ),
    (∀ i, (p i).Monic) → (∀ i, Irreducible (p i)) → Function.Injective p →
    (∀ i, 1 ≤ a i) →
    Minpoly.minimalPolynomial_value K V T = ∏ i, p i ^ a i →
    let U := fun i => LinearMap.ker (Polynomial.aeval T (p i ^ a i))
    Specs.D05.M06.DirectSum.UniqueDecomposition U ∧
      (∀ i, U i = LinearMap.ker ((Polynomial.aeval T (p i)) ^ a i)) ∧
      (∀ i, Specs.D05.M06.Invariant.invariant_value K V (U i) T) ∧
      ∃ h : Function.Bijective (Specs.D05.M06.ExternalSum.summationMap U),
        ∀ i, ∃ e : Polynomial K,
          Polynomial.aeval T e = Specs.D05.M06.InvariantDecomposition.componentProjection U h i ∧
          (Specs.D05.M06.InvariantDecomposition.componentProjection U h i) ^ 2 =
            Specs.D05.M06.InvariantDecomposition.componentProjection U h i ∧
          LinearMap.range (Specs.D05.M06.InvariantDecomposition.componentProjection U h i) = U i ∧
          ∀ v, Specs.D05.M06.InvariantDecomposition.componentProjection U h i v = v ↔ v ∈ U i

/-- The empty factorization is precisely the zero-space convention for the
minimal polynomial. This assertion includes both directions. -/
def minimalPolynomial_eq_one_iff_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Minpoly.minimalPolynomial_value K V T = 1 ↔ ∀ v : V, v = 0

end Specs.D05.M08.Primary
