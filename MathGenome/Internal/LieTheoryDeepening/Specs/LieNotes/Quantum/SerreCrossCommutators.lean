import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Presentation

namespace Specs.LieNotes.Quantum.SerreCrossCommutators

open SerrePresentation (serrePolynomial)
open Presentation

universe u v

/-- Both Serre polynomials commute with the opposite root generators in the
quotient by the basic relations. -/
def CrossCommutators {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
    (C : Cartan A T) : Prop :=
  ∀ i j : Root, i ≠ j → ∀ l : Root,
    Commute (serrePolynomial C.q (E₀ C i) (E₀ C j)) (F₀ C l) ∧
    Commute (serrePolynomial C.q (F₀ C i) (F₀ C j)) (E₀ C l)

def GenericProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    CrossCommutators (generic q hq)

def IndeterminateProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k], CrossCommutators (indeterminate k)

def TruncatedProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N →
    CrossCommutators (truncated k N)

end Specs.LieNotes.Quantum.SerreCrossCommutators
