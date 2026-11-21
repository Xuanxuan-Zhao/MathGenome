import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import Mathlib.RingTheory.Polynomial.Basic

/-! Independent statements for the polynomial clause of CM-15,
`paper.tex:3762–3768,3779–3789`. The action on `M ⊗[R] R[T₁,…,Tₙ]`
is the canonical action on the right tensor factor. Neither the zero module
nor the empty set of variables is excluded. -/
universe u
open scoped TensorProduct
noncomputable section
namespace AdvCommAlg.CohenMacaulay.Specs

/-- Hilbert's basis theorem, also for no variables and the zero ring. -/
def polynomial_noetherianType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ),
    IsNoetherianRing (MvPolynomial (Fin n) R)

/-- Scalar extension of an arbitrary finite module to finitely many
polynomial variables preserves and reflects global Cohen–Macaulayness. -/
def mvPolynomial_cohenMacaulay_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ),
  let P := MvPolynomial (Fin n) R
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := P) M P
  letI := rightTensorFinite R P M P
  IsCohenMacaulayValue P (M ⊗[R] P) ↔ IsCohenMacaulayValue R M

end AdvCommAlg.CohenMacaulay.Specs
