import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.PresentationSymmetries
import Mathlib.Algebra.Algebra.Bilinear

noncomputable section

open scoped TensorProduct

namespace Specs.LieNotes.Quantum.BasicNormalForm

open Presentation PresentationSymmetries MulOpposite

universe u v

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

/-- The free negative algebra, the Cartan algebra, and the free positive algebra,
in multiplication order. -/
abbrev OrderedTensor (A : Type u) [CommRing A] (T : Type v) [CommRing T]
    [Algebra A T] :=
  (FreeAlgebra A Root ⊗[A] T) ⊗[A] FreeAlgebra A Root

def negative (C : Cartan A T) : FreeAlgebra A Root →ₐ[A] B₀ C :=
  FreeAlgebra.lift A (F₀ C)

def positive (C : Cartan A T) : FreeAlgebra A Root →ₐ[A] B₀ C :=
  FreeAlgebra.lift A (E₀ C)

/-- Multiplication in the basic presentation, before imposing Serre relations. -/
def multiplication (C : Cartan A T) : OrderedTensor A T →ₗ[A] B₀ C :=
  let m := LinearMap.mul' A (B₀ C)
  let lower := m.comp (TensorProduct.map (negative C).toLinearMap (cartan₀ C).toLinearMap)
  m.comp (TensorProduct.map lower (positive C).toLinearMap)

@[simp] theorem multiplication_tmul (C : Cartan A T)
    (f : FreeAlgebra A Root) (t : T) (e : FreeAlgebra A Root) :
    multiplication C ((f ⊗ₜ[A] t) ⊗ₜ[A] e) =
      negative C f * cartan₀ C t * positive C e := by
  simp [multiplication]

def HasNormalForm (C : Cartan A T) : Prop :=
  Function.Bijective (multiplication C)

def normalFormEquiv (C : Cartan A T) (h : HasNormalForm C) :
    OrderedTensor A T ≃ₗ[A] B₀ C :=
  LinearEquiv.ofBijective (multiplication C) h

@[simp] theorem normalFormEquiv_tmul (C : Cartan A T) (h : HasNormalForm C)
    (f : FreeAlgebra A Root) (t : T) (e : FreeAlgebra A Root) :
    normalFormEquiv C h ((f ⊗ₜ[A] t) ⊗ₜ[A] e) =
      negative C f * cartan₀ C t * positive C e :=
  multiplication_tmul C f t e

/-- Symmetries of the basic presentation. Mapping into the opposite algebra
expresses reversal of products by the anti-involution. -/
def HasBasicSymmetries (C : Cartan A T) : Prop :=
  ∃ (omega : B₀ C →ₐ[A] B₀ C) (eta : B₀ C →ₐ[A] (B₀ C)ᵐᵒᵖ),
    SymmetryLaws C (cartan₀ C) (E₀ C) (F₀ C) omega eta

def GenericNormalForm : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    HasNormalForm (generic q hq)

def IndeterminateNormalForm : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    HasNormalForm (indeterminate k)

def TruncatedNormalForm : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N →
    HasNormalForm (truncated k N)

def GenericSymmetries : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    let C := generic q hq
    HasBasicSymmetries C ∧ ∀ i, C.kappa (C.K i : Laurent k) = ↑(C.K i)⁻¹

def IndeterminateSymmetries : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    let C := indeterminate k
    HasBasicSymmetries C ∧ ∀ i, C.kappa (C.K i : Laurent (RatFunc k)) = ↑(C.K i)⁻¹

def TruncatedSymmetries : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N →
    let C := truncated k N
    HasBasicSymmetries C ∧ ∀ i : Root, C.kappa (MvPolynomial.X i) = -MvPolynomial.X i

end Specs.LieNotes.Quantum.BasicNormalForm
