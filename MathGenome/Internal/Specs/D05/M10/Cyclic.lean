import MathGenome.Internal.Specs.D05.M08.Minpoly
import MathGenome.Internal.Specs.D05.Foundations.QuotientBasisUnits
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Isomorphisms

/-! Independent specification of K05.10.cyclic (paper.tex:1455–1458).
`AEval' T` changes only the scalar action: X acts as T. The explicit bridge
below identifies its cyclic polynomial submodule with the original span in V.
No nonzero vector, positive dimension, or splitting assumption is imposed. -/

noncomputable section

namespace Specs.D05.M10.Cyclic

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Polynomial evaluation on one vector, with the canonical polynomial action. -/
def orbitMap (T : Module.End K V) (v : V) :
    K[X] →ₗ[K[X]] Module.AEval' T :=
  LinearMap.toSpanSingleton K[X] (Module.AEval' T) (Module.AEval'.of T v)

def cyclicSpace_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
    Module.End K V → V → Submodule K V

def cyclicSpace_value : cyclicSpace_type := fun K _ _ _ _ T v =>
  Submodule.span K (Set.range (fun j : ℕ => (T ^ j) v))

def cyclicModule_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V), V → Submodule K[X] (Module.AEval' T)

def cyclicModule_value : cyclicModule_type := fun _ _ _ _ _ T v =>
  (orbitMap T v).range

def annihilator_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
    Module.End K V → V → Ideal K[X]

def annihilator_value : annihilator_type := fun _ _ _ _ _ T v =>
  (orbitMap T v).ker

/-- Monic normalization of the principal-ideal generator. Nonvanishing and
monicity in finite dimension are conclusions to be proved, not hypotheses. -/
def vectorAnnihilator_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
    Module.End K V → V → K[X]

def vectorAnnihilator_value : vectorAnnihilator_type := by
  classical
  exact fun K V _ _ _ T v =>
    normalize (Submodule.IsPrincipal.generator (annihilator_value K V T v))

def orbit_evaluation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (p : K[X]),
    (Module.AEval'.of T).symm (orbitMap T v p) =
      Specs.D05.M08.Evaluation.evaluation_value K V T p v

def module_bridge : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v w : V),
    Module.AEval'.of T w ∈ cyclicModule_value K V T v ↔
      w ∈ cyclicSpace_value K V T v

/-- This identification also verifies the operator action on the actual span. -/
def module_identification : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V),
    ∃ e : cyclicModule_value K V T v ≃ₗ[K] cyclicSpace_value K V T v,
      (∀ w, (e w : V) = (Module.AEval'.of T).symm (w : Module.AEval' T)) ∧
      (∀ w, (e ((X : K[X]) • w) : V) = T (e w : V))

def invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v w : V),
    w ∈ cyclicSpace_value K V T v → T w ∈ cyclicSpace_value K V T v

def evaluation_surjective : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V),
    ∃ f : K[X] →ₗ[K] cyclicSpace_value K V T v,
      Function.Surjective f ∧
      ∀ p, (f p : V) = Specs.D05.M08.Evaluation.evaluation_value K V T p v

def mem_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) (p : K[X]),
    p ∈ annihilator_value K V T v ↔ Specs.D05.M08.Evaluation.evaluation_value K V T p v = 0

def nonzero_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    annihilator_value K V T v ≠ ⊥ ∧
      Specs.D05.M08.Minpoly.minimalPolynomial_value K V T ∈ annihilator_value K V T v

def monic_generator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    (vectorAnnihilator_value K V T v).Monic ∧
      annihilator_value K V T v = Ideal.span {vectorAnnihilator_value K V T v}

def unique_monic_generator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    ∃! d : K[X], d.Monic ∧ annihilator_value K V T v = Ideal.span {d}

def least_degree : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V) (p : K[X]),
    p ∈ annihilator_value K V T v → p ≠ 0 →
      (vectorAnnihilator_value K V T v).natDegree ≤ p.natDegree

def divides_iff_annihilates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V) (p : K[X]),
    vectorAnnihilator_value K V T v ∣ p ↔
      Specs.D05.M08.Evaluation.evaluation_value K V T p v = 0

/-- A reduced representative in the vector-annihilator ideal is zero. -/
def reduced_annihilator_eq_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V) (p : K[X]),
    p.degree < (vectorAnnihilator_value K V T v).degree →
    p ∈ annihilator_value K V T v → p = 0

/-- The quotient is the polynomial-ring module quotient by the actual ideal.
The target retains the X-action inherited from T, and the map is prescribed
on every representative. The preceding bridge identifies it with C_T(v). -/
def quotient_iso : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    ∃ e : (K[X] ⧸ (Ideal.span {vectorAnnihilator_value K V T v} : Ideal K[X]))
        ≃ₗ[K[X]] cyclicModule_value K V T v,
      ∀ p : K[X], (e (Submodule.Quotient.mk p) : Module.AEval' T) = orbitMap T v p

def representatives : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    ∀ z : AdjoinRoot (vectorAnnihilator_value K V T v),
      ∃! p : K[X], p.degree < (vectorAnnihilator_value K V T v).degree ∧
        AdjoinRoot.mk (vectorAnnihilator_value K V T v) p = z

def iterate_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    ∃ b : Module.Basis (Fin (vectorAnnihilator_value K V T v).natDegree)
        K (cyclicSpace_value K V T v),
      ∀ j, (b j : V) = (T ^ (j : ℕ)) v

def dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (v : V),
    Module.finrank K (cyclicSpace_value K V T v) =
      (vectorAnnihilator_value K V T v).natDegree

def zero_vector : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V),
    vectorAnnihilator_value K V T 0 = 1 ∧
      cyclicSpace_value K V T 0 = ⊥ ∧
      (vectorAnnihilator_value K V T 0).natDegree = 0

end Specs.D05.M10.Cyclic
