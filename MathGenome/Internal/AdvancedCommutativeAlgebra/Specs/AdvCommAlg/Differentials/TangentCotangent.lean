import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! KD-23. All scalar extensions and derivations use the specified point.
The dual-number model is explicitly compared with K[T]/(T²). No finite type
or finite dimension assumptions are imposed. -/
namespace Specs.AdvCommAlg.Differentials.Tangent

universe u v w
noncomputable section
open TensorProduct

/-- A polynomial quotient model for the dual numbers in the source. -/
abbrev DualQuotient (K : Type w) [CommRing K] :=
  Polynomial K ⧸ Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial K))

/-- The usual coordinate model represents exactly the displayed quotient. -/
def dualNumbersModel : Prop := ∀ (K : Type w) [Field K],
  ∃ e : DualQuotient K ≃ₐ[K] DualNumber K,
    e (Ideal.Quotient.mk _ Polynomial.X) = DualNumber.eps ∧
    ∀ a : K, e (Ideal.Quotient.mk _ (Polynomial.C a)) = TrivSqZeroExt.inl a

/-- Extension of scalars followed by the universal property, including its
canonical evaluation formula, as an equivalence of K-vector spaces. -/
def dualDerivations : Prop := ∀ (A : Type u) (B : Type v) (K : Type w)
  [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
  (x : B →ₐ[A] K),
  letI := x.toRingHom.toAlgebra
  ∃ e : ((K ⊗[B] KaehlerDifferential A B) →ₗ[K] K) ≃ₗ[K] Derivation A B K,
    ∀ L b, e L b = L (1 ⊗ₜ[B] KaehlerDifferential.D A B b)

/-- Algebra maps reducing to the given point; the constant lift is the origin. -/
abbrev PointLifts (A : Type u) (B : Type v) (K : Type w)
    [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    (x : B →ₐ[A] K) :=
  {f : B →ₐ[A] DualNumber K // (TrivSqZeroExt.fstHom A K K).comp f = x}

def tangentLifts : Prop := ∀ (A : Type u) (B : Type v) (K : Type w)
  [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
  (x : B →ₐ[A] K),
  letI := x.toRingHom.toAlgebra
  ∃ e : Derivation A B K ≃ PointLifts A B K x,
    (∀ D b, (e D).1 b = (x b, D b)) ∧
    (e 0).1 = (TrivSqZeroExt.inlAlgHom A K K).comp x

/-- The resulting direct identification with lifts, with its evaluation
formula and the constant lift as the zero tangent vector. -/
def dualLifts : Prop := ∀ (A : Type u) (B : Type v) (K : Type w)
  [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
  (x : B →ₐ[A] K),
  letI := x.toRingHom.toAlgebra
  ∃ e : ((K ⊗[B] KaehlerDifferential A B) →ₗ[K] K) ≃ PointLifts A B K x,
    (∀ L b, (e L).1 b = (x b, L (1 ⊗ₜ[B] KaehlerDifferential.D A B b))) ∧
    (e 0).1 = (TrivSqZeroExt.inlAlgHom A K K).comp x

/-- At a rational point m = ker(x), the map [b] ↦ 1 ⊗ db is
an isomorphism of k-vector spaces. The action on m/m² is the one inherited
from the structural map k → B. -/
def rationalCotangent : Prop := ∀ (k : Type u) (B : Type v)
  [Field k] [CommRing B] [Algebra k B] (x : B →ₐ[k] k),
  letI := x.toRingHom.toAlgebra
  ∃ e : (RingHom.ker x.toRingHom).Cotangent ≃ₗ[k]
      k ⊗[B] KaehlerDifferential k B,
    ∀ b : RingHom.ker x.toRingHom,
      e (Ideal.toCotangent _ b) = 1 ⊗ₜ[B] KaehlerDifferential.D k B b.val

end
end Specs.AdvCommAlg.Differentials.Tangent
