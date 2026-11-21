import MathGenome.Internal.Specs.D05.M10.Cyclic
import MathGenome.Internal.Specs.D05.M08.Charpoly

/-! K05.10.cyclic_test, paper.tex:1529–1534. Cyclicity means that the
original span of the iterates is all of V. No nonzero-vector, positive-dimension,
splitting, or characteristic hypothesis is imposed. -/
noncomputable section
namespace Specs.D05.M10.CyclicTest

open Polynomial

def cyclic_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    Cyclic.cyclicSpace_value K V T v = ⊤ →
      Cyclic.vectorAnnihilator_value K V T v = minpoly K T

def cyclic_degree : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    Cyclic.cyclicSpace_value K V T v = ⊤ →
      (minpoly K T).natDegree = Module.finrank K V

def minpoly_eq_charpoly_of_cyclic : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    Cyclic.cyclicSpace_value K V T v = ⊤ → minpoly K T = T.charpoly

def exists_cyclic_of_minpoly_eq_charpoly : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    minpoly K T = T.charpoly → ∃ v : V, Cyclic.cyclicSpace_value K V T v = ⊤

def cyclic_iff_minpoly_eq_charpoly : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (∃ v : V, Cyclic.cyclicSpace_value K V T v = ⊤) ↔ minpoly K T = T.charpoly

/-- The zero vector is cyclic on the zero space, and both annihilators and
the characteristic polynomial are the constant polynomial one. -/
def zero_case : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Module.finrank K V = 0 →
      Cyclic.cyclicSpace_value K V T 0 = ⊤ ∧
      Cyclic.vectorAnnihilator_value K V T 0 = 1 ∧
      minpoly K T = 1 ∧ T.charpoly = 1

end Specs.D05.M10.CyclicTest
