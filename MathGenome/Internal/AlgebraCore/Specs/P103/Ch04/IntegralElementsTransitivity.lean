import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
Independent statements for the first two assertions of Theorem 4.6
(`paper.tex`, the theorem labelled `p103:ALG-05-C01-R03`).

All rings are commutative and unital, with the zero ring permitted.
`IsIntegral R a` means that `a` satisfies a monic polynomial over the
structure map, and `RingHom.IsIntegral` quantifies this over all elements.
No structure map is required to be injective.
-/

namespace P103.Ch04.IntegralElementsTransitivity.Specs

universe u v w

/-- The set of all integral elements is exactly the carrier of an
`R`-subalgebra. In particular it contains scalar images and is closed under
addition, additive inverse, and multiplication. -/
def integral_elements_form_subalgebra : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A],
    ∃ S : Subalgebra R A, ∀ a : A, a ∈ S ↔ IsIntegral R a

/-- Elementwise transitivity for every compatible tower `R → B → C`. -/
def integral_transitivity : Prop :=
  ∀ (R : Type u) (B : Type v) (C : Type w)
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C],
    (∀ b : B, IsIntegral R b) → ∀ c : C, IsIntegral B c → IsIntegral R c

/-- Consequently the composite of any two integral ring maps is integral. -/
def integral_ringHom_comp : Prop :=
  ∀ (R : Type u) (B : Type v) (C : Type w)
    [CommRing R] [CommRing B] [CommRing C]
    (f : R →+* B) (g : B →+* C),
    f.IsIntegral → g.IsIntegral → (g.comp f).IsIntegral

end P103.Ch04.IntegralElementsTransitivity.Specs
