import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.NullHomotopy
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Pi

/-! RK-13: the dual number example and the unit boundary case.
The polynomial presentation is explicitly identified with Mathlib's dual numbers,
with the class of X sent to ε. The residue module is k with action through the
constant-coordinate homomorphism, so the homology statements are R-linear. -/
open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul

/-- The source's polynomial quotient k[ε]/(ε²). -/
abbrev dualPolynomialQuotient (k : Type u) [Field k] :=
  Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}

/-- The residue field k, as a module over the dual numbers. -/
def dualResidue (k : Type u) [Field k] : ModuleCat (DualNumber k) := by
  letI : Module (DualNumber k) k :=
    Module.compHom k (TrivSqZeroExt.fstHom k k k).toRingHom
  exact ModuleCat.of (DualNumber k) k

/-- Standard coordinate in degree zero of a singleton complex. -/
def singletonZeroEquiv {R : Type u} [CommRing R] (_a : R) :
    ((⋀[R]^0 (Fin 1 → R)) ⊗[R] R) ≃ₗ[R] R :=
  (TensorProduct.congr (exteriorPower.zeroEquiv R (Fin 1 → R))
    (LinearEquiv.refl R R)).trans (TensorProduct.lid R R)

/-- Standard coordinate in degree one of the coefficient-ring singleton complex. -/
def singletonOneEquiv {R : Type u} [CommRing R] (_a : R) :
    ((⋀[R]^1 (Fin 1 → R)) ⊗[R] R) ≃ₗ[R] R :=
  (TensorProduct.congr
    ((exteriorPower.oneEquiv R (Fin 1 → R)).trans
      (LinearEquiv.piUnique R (fun _ : Fin 1 => R)))
    (LinearEquiv.refl R R)).trans (TensorProduct.lid R R)
end AdvCommAlg.Koszul

namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

def dualPresentation : Prop := ∀ (k : Type u) [Field k],
  ∃ e : dualPolynomialQuotient k ≃ₐ[k] DualNumber k,
    e (Ideal.Quotient.mk _ Polynomial.X) = DualNumber.eps

def singletonDescription : Prop := ∀ {R : Type u} [CommRing R] (a : R),
  (∀ z : (coefficientComplex R [a]).X 1,
    singletonZeroEquiv a (coefficientDifferential R [a] 0 z) =
      a * singletonOneEquiv a z) ∧
  (∀ q : ℕ, 1 < q → Subsingleton ((coefficientComplex R [a]).X q))

def dualHomologyOne : Prop := ∀ (k : Type u) [Field k],
  Nonempty (homology (DualNumber k) [(DualNumber.eps : DualNumber k)] 1 ≃ₗ[DualNumber k]
    (Ideal.span {DualNumber.eps} : Ideal (DualNumber k)))

def dualHomologyZero : Prop := ∀ (k : Type u) [Field k],
  Nonempty (homology (DualNumber k) [(DualNumber.eps : DualNumber k)] 0 ≃ₗ[DualNumber k] dualResidue k)

def dualNonzero : Prop := ∀ (k : Type u) [Field k],
  (DualNumber.eps : DualNumber k) ≠ 0 ∧
    (Ideal.span {DualNumber.eps} : Ideal (DualNumber k)) ≠ ⊥

def containsUnitContractible : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  (∃ a ∈ x, IsUnit a) → Nonempty (Homotopy (𝟙 (coefficientComplex M x)) 0)
end Specs.AdvCommAlg.Koszul
