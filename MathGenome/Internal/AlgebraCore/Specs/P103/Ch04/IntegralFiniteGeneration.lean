import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

/-!
Independent statements for the first two assertions of Theorem 4.5
(paper.tex:893–899). All rings are commutative and unital; no nontriviality
or injectivity of the structure map is assumed.

`IsIntegral` means a monic polynomial equation over the given structure map.
`Module.Finite` means that the top submodule has a finite spanning set.
`Algebra.FiniteType` means that the top subalgebra has a finite generating set.
-/

namespace P103.Ch04.IntegralFiniteGeneration.Specs

open Polynomial

universe u v

/-- The source definition of an integral element, expressed using algebra evaluation. -/
def integral_iff_monic_equation : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (a : A),
  IsIntegral R a ↔ ∃ p : R[X], p.Monic ∧ aeval a p = 0

/-- The first assertion: the simple subalgebra is finite exactly for integral elements. -/
def integral_iff_finite_adjoin : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (a : A),
  IsIntegral R a ↔ Module.Finite R (Algebra.adjoin R ({a} : Set A))

/-- The second assertion, with integrality quantified over every element of the algebra. -/
def finite_iff_integral_and_finiteType : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A],
  Module.Finite R A ↔ (∀ a : A, IsIntegral R a) ∧ Algebra.FiniteType R A

open scoped Classical in
/-- A monic relation bounds the powers needed to span the simple subalgebra. -/
def bounded_powers_span : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (a : A) (p : R[X]),
  p.Monic → aeval a p = 0 →
    Submodule.span R (↑((Finset.range p.natDegree).image (fun n => a ^ n)) : Set A) =
      (Algebra.adjoin R ({a} : Set A)).toSubmodule

/-- Finite families of integral elements generate module-finite subalgebras,
including the empty family. -/
def finite_adjoin_of_integral : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (s : Set A),
  s.Finite → (∀ a ∈ s, IsIntegral R a) → Module.Finite R (Algebra.adjoin R s)

end P103.Ch04.IntegralFiniteGeneration.Specs
