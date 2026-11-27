import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing
import Mathlib.RingTheory.TensorProduct.Basic

namespace GaloisFormalization.PV.Specs

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- The action on pure tensors and compatibility with the two factor maps. -/
def tensorLaws {kind : OperatorKind} (E : operator kind S) (F : operator kind T)
    (G : operator kind (S ⊗[R] T)) : Prop :=
  (match kind with
   | .differential =>
     ∀ s t, apply G (s ⊗ₜ[R] t) = apply E s ⊗ₜ[R] t + s ⊗ₜ[R] apply F t
   | .difference =>
     (∀ s t, apply G (s ⊗ₜ[R] t) = apply E s ⊗ₜ[R] apply F t) ∧
     (∀ s t, (toRingEquiv G).symm (s ⊗ₜ[R] t) =
       (toRingEquiv E).symm s ⊗ₜ[R] (toRingEquiv F).symm t)) ∧
  commutes E G (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T) ∧
  commutes F G (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)

/-- A common operator on the base induces the unique stated operator on the tensor product. -/
def tensorExistsUnique :=
  ∀ {kind : OperatorKind} {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {D : operator kind R} {E : operator kind S} {F : operator kind T},
    isAlgebra D E → isAlgebra D F → ∃! G, tensorLaws (R := R) E F G

/-- Over a base of constants, any algebra of constants can be the right factor. -/
def tensorConstantExistsUnique :=
  ∀ {kind : OperatorKind} {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {E : operator kind S}, isAlgebra (trivial kind R) E →
    ∃! G, tensorLaws (R := R) E (trivial kind T) G

/-- The same laws hold when the left structure map is precomposed by an operator automorphism. -/
def tensorTwistedExistsUnique :=
  ∀ {kind : OperatorKind} {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {D : operator kind R} {E : operator kind S} {F : operator kind T}
    (τ : ringEquiv D D), isAlgebra D E → isAlgebra D F →
    letI : Algebra R S := Algebra.compHom S τ.val.toRingHom
    ∃! G, tensorLaws (R := R) E F G

end GaloisFormalization.PV.Specs
