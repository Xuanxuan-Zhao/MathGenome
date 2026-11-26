import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalArtinAlgebras
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftDefinitions

noncomputable section

open scoped TensorProduct
open CommutativeAlgebraNotes.SquareZeroLift

namespace CommutativeAlgebraNotes.FlatSquareZeroLifts

/-- The coefficient module, written with the algebra factor on the left so
that it carries the canonical left tensor product action. The symmetry of
the (A)-tensor product takes (b ⊗ i) to (i ⊗ b). -/
abbrev Coefficients {R A : Type*} [CommRing R] [CommRing A]
    (e : BaseExtension R A) (B : Type*) [CommRing B] [Algebra A B] :=
  B ⊗[A] e.I

/-- A pure tensor in the coefficient module. -/
abbrev coefficientTensor {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] (e : BaseExtension R A) (b : B) (i : e.I) : Coefficients e B :=
  b ⊗ₜ[A] i

/-- The prescribed coefficient map, corresponding under tensor symmetry to
(i \mapsto i ⊗ 1). -/
def coefficientMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra A B]
    (e : BaseExtension R A) : e.CoefficientMap (B := B) (Coefficients e B) := by
  letI : Module A (Coefficients e B) := Module.compHom _ (algebraMap A B)
  exact {
    toFun := fun i => (1 : B) ⊗ₜ[A] i
    map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
    map_smul' := fun a i => by
      change (1 : B) ⊗ₜ[A] (a • i) = (algebraMap A B a •
        ((1 : B) ⊗ₜ[A] i) : B ⊗[A] e.I)
      rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, Algebra.smul_def]
      rfl
  }

/-- Reduction along the base extension, with its required compatibility
with the map on the total algebra. -/
def ReducesTo {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] [CommRing D] [Algebra R D] (e : BaseExtension R A) (g : D →+* B) : Prop :=
  letI := e.baseAlgebra
  ∃ E : A ⊗[R] D ≃ₐ[A] B, ∀ d : D, E ((1 : A) ⊗ₜ[R] d) = g d

/-- The given local morphism as the square-zero extension used by Theorem 6.1. -/
abbrev extension {k : Type*} [Field k] {R A : LocalArtinAlgebra k}
    (f : LocalArtinAlgebra.Hom R A) (hf : Function.Surjective f)
    (hs : RingHom.ker (f : R →ₐ[k] A).toRingHom ^ 2 = ⊥) : BaseExtension R A :=
  ⟨(f : R →ₐ[k] A).toRingHom, hf, hs⟩

/-- The image of a base coefficient in the kernel of the reduction of the lift. -/
def coefficientInKernel {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] [CommRing D] [Algebra R D]
    (e : BaseExtension R A) (g : D →+* B)
    (over : ∀ a, g (algebraMap R D a) = algebraMap A B (e.hom a)) (i : e.I) :
    RingHom.ker g :=
  ⟨algebraMap R D i, by
    rw [RingHom.mem_ker, over, RingHom.mem_ker.mp i.property, map_zero]⟩

end CommutativeAlgebraNotes.FlatSquareZeroLifts

namespace Specs.CommutativeAlgebraNotes.FlatSquareZeroLifts

open _root_.CommutativeAlgebraNotes
open _root_.CommutativeAlgebraNotes.FlatSquareZeroLifts

universe u v w z

def FlatIsFree : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M], Module.Free R M

def FlatToSquareZero : Prop :=
  ∀ {k : Type u} [Field k] {R A : LocalArtinAlgebra.{u,v} k}
    (f : LocalArtinAlgebra.Hom R A) (hf : Function.Surjective f)
    (hs : RingHom.ker (f : R →ₐ[k] A).toRingHom ^ 2 = ⊥)
    {B : Type w} [CommRing B] [Algebra A B] [Module.Flat A B]
    {D : Type z} [CommRing D] [Algebra R D] [Module.Flat R D]
    (g : D →+* B),
    let e : BaseExtension R A := extension f hf hs
    ReducesTo e g →
    ∃ (L : Lift.{v,v,w,max v w,z} e (coefficientMap (B := B) e))
      (j : D ≃ₐ[R] L.Ring),
      (∀ d, L.map (j d) = g d) ∧
      (∀ (i : e.I) (d : D),
        L.marking (j d • coefficientInKernel e L.map L.over i) = coefficientTensor e (g d) i)

def SquareZeroToFlat : Prop :=
  ∀ {k : Type u} [Field k] {R A : LocalArtinAlgebra.{u,v} k}
    (f : LocalArtinAlgebra.Hom R A) (hf : Function.Surjective f)
    (hs : RingHom.ker (f : R →ₐ[k] A).toRingHom ^ 2 = ⊥)
    {B : Type w} [CommRing B] [Algebra A B] [Module.Flat A B],
    let e : BaseExtension R A := extension f hf hs
    ∀ L : Lift.{v,v,w,max v w,z} e (coefficientMap (B := B) e), Module.Flat R L.Ring ∧ ReducesTo e L.map

end Specs.CommutativeAlgebraNotes.FlatSquareZeroLifts
