import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Presentation
import Mathlib.Algebra.Algebra.Opposite

namespace Specs.LieNotes.Quantum.PresentationSymmetries

open Presentation MulOpposite

universe u v w

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

/-- The identities of the Cartan inversion used in the presentation. -/
structure InvertsCartan (C : Cartan A T) : Prop where
  involutive : Function.Involutive C.kappa
  tau (i : Root) (t : T) : C.kappa (C.tau i t) = (C.tau i).symm (C.kappa t)
  D (i : Root) : C.kappa (C.D i) = -C.D i

/-- Actions on the generators and order-two laws for the two symmetries. -/
structure SymmetryLaws {B : Type w} [Ring B] [Algebra A B]
    (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (omega : B →ₐ[A] B) (eta : B →ₐ[A] Bᵐᵒᵖ) : Prop where
  omega_cartan (x : T) : omega (t x) = t (C.kappa x)
  omega_E (i : Root) : omega (e i) = f i
  omega_F (i : Root) : omega (f i) = e i
  omega_square : Function.Involutive omega
  eta_cartan (x : T) : eta (t x) = op (t x)
  eta_E (i : Root) : eta (e i) = op (f i)
  eta_F (i : Root) : eta (f i) = op (e i)
  eta_square : Function.Involutive (fun b => unop (eta b))

/-- The symmetries exist before imposing Serre relations, preserve the ideal,
and induce the stated symmetries of the Serre quotient. -/
def HasSymmetries (C : Cartan A T) : Prop :=
  InvertsCartan C ∧
    ∃ (omega₀ : B₀ C →ₐ[A] B₀ C) (eta₀ : B₀ C →ₐ[A] (B₀ C)ᵐᵒᵖ)
      (omega : U C →ₐ[A] U C) (eta : U C →ₐ[A] (U C)ᵐᵒᵖ),
      SymmetryLaws C (cartan₀ C) (E₀ C) (F₀ C) omega₀ eta₀ ∧
      SymmetryLaws C (cartan C) (E C) (F C) omega eta ∧
      (∀ b, omega₀ b ∈ serreIdeal C ↔ b ∈ serreIdeal C) ∧
      (∀ b, unop (eta₀ b) ∈ serreIdeal C ↔ b ∈ serreIdeal C) ∧
      (∀ b, serreQuotient C (omega₀ b) = omega (serreQuotient C b)) ∧
      (∀ b, op (serreQuotient C (unop (eta₀ b))) = eta (serreQuotient C b))

def GenericProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    let C := generic q hq
    HasSymmetries C ∧ ∀ i, C.kappa (C.K i : Laurent k) = ↑(C.K i)⁻¹

def IndeterminateProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    let C := indeterminate k
    HasSymmetries C ∧ ∀ i, C.kappa (C.K i : Laurent (RatFunc k)) = ↑(C.K i)⁻¹

def TruncatedProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N →
    let C := truncated k N
    HasSymmetries C ∧ ∀ i : Root, C.kappa (MvPolynomial.X i) = -MvPolynomial.X i

end Specs.LieNotes.Quantum.PresentationSymmetries
