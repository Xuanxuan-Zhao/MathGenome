import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.SquareZeroLifts
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Derivations
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.Tactic.LinearCombination

namespace AdvCommAlg.Differentials

open Specs.AdvCommAlg.Differentials.SquareZero
attribute [local instance] rightModule central rightTower

universe u v w

/-- B ⊕ M with Mathlib's trivial extension ring structure. -/
abbrev TrivialExtension (B : Type v) (M : Type w) [CommRing B] [AddCommGroup M]
    [Module B M] := TrivSqZeroExt B M

theorem trivial_extension_law : trivialLaw.{u,v,w} := by
  intro A B M _ _ _ _ _ _ _
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

section Trivial
variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
variable [Module B M] [Module A M] [IsScalarTower A B M]

def derivationSection (D : Derivation A B M) : Sections A B M :=
  ⟨{ toFun := fun b => (b, D b)
     map_one' := by apply TrivSqZeroExt.ext <;> simp
     map_mul' := by
       intro x y
       apply TrivSqZeroExt.ext
       · rfl
       · exact D.leibniz x y
     map_zero' := by apply TrivSqZeroExt.ext <;> simp
     map_add' := by
       intro x y
       apply TrivSqZeroExt.ext
       · rfl
       · exact D.map_add x y
     commutes' := by
       intro a
       apply TrivSqZeroExt.ext
       · rfl
       · exact D.map_algebraMap a }, by ext; rfl⟩

def sectionDerivation (s : Sections A B M) : Derivation A B M := by
  have hfst (b : B) : (s.1 b).fst = b := congrArg (fun f : B →ₐ[A] B => f b) s.2
  refine Derivation.mk'
    { toFun := fun b => (s.1 b).snd
      map_add' := fun x y => by simp
      map_smul' := fun a b => by simp } ?_
  intro x y
  change (s.1 (x*y)).snd = x • (s.1 y).snd + y • (s.1 x).snd
  rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
  rfl

theorem trivial_extension_correspondence : trivialCorrespondence.{u,v,w} := by
  intro A B M _ _ _ _ _ _ _
  refine ⟨⟨derivationSection, sectionDerivation, ?_, ?_⟩, fun _ _ => rfl⟩
  · intro D; apply Derivation.ext; intro b; rfl
  · intro s
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    apply TrivSqZeroExt.ext
    · exact (congrArg (fun f : B →ₐ[A] B => f b) s.2).symm
    · rfl

end Trivial

theorem quotient_scalar_law : quotientScalarLaw.{w} := by
  intro C _ I hI c x
  rfl

theorem induced_scalar_law : inducedScalarLaw.{u,v,w} := by
  intro A B C _ _ _ _ _ I hI fbar b x
  rfl

section General
variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Ideal C) (hI : I ^ 2 = ⊥) (fbar : B →ₐ[A] C ⧸ I)

/-- The quotient action can be calculated using any lift of fbar. -/
theorem ideal_smul_using_lift (f : B →ₐ[A] C)
    (hf : (Ideal.Quotient.mkₐ A I).comp f = fbar) :
    letI := idealModule I hI fbar
    ∀ (b : B) (x : I), (b • x : I).val = f b * (x : C) := by
  letI := idealModule I hI fbar
  intro b x
  have hb := congrArg (fun g : B →ₐ[A] C ⧸ I => g b) hf
  change ((quotientAction I hI) (fbar b) x : C) = _
  rw [← hb]
  rfl

include hI in
private theorem ideal_product_zero (x y : I) : (x : C) * (y : C) = 0 := by
  have h := Ideal.mul_mem_mul x.property y.property
  rw [← pow_two, hI] at h
  exact h

/-- The difference of two lifts, with the prescribed quotient coefficient action. -/
def differenceDerivation (f : B →ₐ[A] C)
    (hf : (Ideal.Quotient.mkₐ A I).comp f = fbar) (g : Lifts I fbar) :
    IdealDerivations I hI fbar := by
  letI := idealModule I hI fbar
  letI := idealTower I hI fbar
  let L := diffToIdealOfQuotientCompEq I g.1 f (g.2.trans hf.symm)
  refine Derivation.mk' L ?_
  intro x y
  have hz := ideal_product_zero I hI (L x) (L y)
  apply Subtype.ext
  change g.1 (x*y) - f (x*y) = ((x • L y : I) : C) + ((y • L x : I) : C)
  rw [ideal_smul_using_lift I hI fbar f hf, ideal_smul_using_lift I hI fbar f hf]
  change (g.1 x - f x) * (g.1 y - f y) = 0 at hz
  change g.1 (x*y) - f (x*y) = f x * (g.1 y - f y) + f y * (g.1 x - f x)
  rw [map_mul, map_mul]
  linear_combination hz

/-- Add a derivation to the chosen reference lift. -/
def addDerivationLift (f : B →ₐ[A] C)
    (hf : (Ideal.Quotient.mkₐ A I).comp f = fbar)
    (D : IdealDerivations I hI fbar) : Lifts I fbar := by
  letI := idealModule I hI fbar
  letI := idealTower I hI fbar
  refine ⟨{
    toFun := fun b => f b + (D b : C)
    map_one' := by simp
    map_mul' := ?_
    map_zero' := by simp
    map_add' := ?_
    commutes' := by intro a; simp }, ?_⟩
  · intro x y
    have hz := ideal_product_zero I hI (D x) (D y)
    simp only [map_mul, D.leibniz, Submodule.coe_add,
      ideal_smul_using_lift I hI fbar f hf]
    linear_combination -hz
  · intro x y
    simp only [map_add, Submodule.coe_add]
    abel
  · apply AlgHom.ext
    intro b
    change Ideal.Quotient.mk I (f b + (D b : C)) = fbar b
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (D b).property, add_zero]
    exact congrArg (fun g : B →ₐ[A] C ⧸ I => g b) hf

theorem square_zero_lift_correspondence : liftCorrespondence.{u,v,w} := by
  intro A B C _ _ _ _ _ I hI fbar f hf
  letI := idealModule I hI fbar
  letI := idealTower I hI fbar
  refine ⟨⟨addDerivationLift I hI fbar f hf,
    differenceDerivation I hI fbar f hf, ?_, ?_⟩, ?_, ?_⟩
  · intro D
    apply Derivation.ext
    intro b
    apply Subtype.ext
    change f b + (D b : C) - f b = (D b : C)
    abel
  · intro g
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    change f b + (g.1 b - f b) = g.1 b
    abel
  · intro D b; rfl
  · intro g b; rfl

end General

end AdvCommAlg.Differentials
