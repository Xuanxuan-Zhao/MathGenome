import MathGenome.Internal.Specs.D05.M10.Cyclic

/-! K05.10.cyclic_test, paper.tex:1534–1539.
The commutant criterion over the original arbitrary field. Cyclicity is the
shared span of all iterates; polynomial means actual evaluation in End_K(V).
Finite dimension includes zero, without splitting or characteristic assumptions.
-/
noncomputable section
namespace Specs.D05.M10.CyclicTest.Commutant

/-- A commuting map on a cyclic space is a polynomial in the operator. -/
def polynomial_of_commutes_of_cyclic : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V),
    Cyclic.cyclicSpace_value K V T v = ⊤ →
    ∀ S : Module.End K V, S * T = T * S →
      ∃ p : Polynomial K, S = Polynomial.aeval T p

/-- Full equivalence, including the zero space. -/
def cyclic_iff_commutant_polynomial : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (∃ v : V, Cyclic.cyclicSpace_value K V T v = ⊤) ↔
    ∀ S : Module.End K V, S * T = T * S →
      ∃ p : Polynomial K, S = Polynomial.aeval T p

/-- The converse provides a commuting nonpolynomial operator whenever no
cyclic vector exists. No nonzero-space hypothesis is needed. -/
def noncyclic_counterexample : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (¬ ∃ v : V, Cyclic.cyclicSpace_value K V T v = ⊤) →
    ∃ S : Module.End K V, S * T = T * S ∧
      ∀ p : Polynomial K, S ≠ Polynomial.aeval T p

end Specs.D05.M10.CyclicTest.Commutant
