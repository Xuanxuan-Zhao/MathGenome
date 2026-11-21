import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Derivations
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Independent statements for KD-04. The coefficient action in the general
case is constructed from the quotient map, before a reference lift is chosen. -/
namespace Specs.AdvCommAlg.Differentials.SquareZero

universe u v w

/-- The underlying type of the trivial square-zero extension. -/
def trivialExtensionType :=
  ∀ (B : Type v) (M : Type w) [CommRing B] [AddCommGroup M] [Module B M],
    Type (max v w)

def trivialExtensionValue : trivialExtensionType.{v,w} :=
  fun B M _ _ _ => TrivSqZeroExt B M

/-- The right action associated to a module over a commutative ring. -/
abbrev rightModule (B : Type v) (M : Type w) [CommRing B] [AddCommGroup M]
    [Module B M] : Module Bᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id B).fromOpposite (fun x y => Commute.all x y))
attribute [local instance] rightModule

local instance central (B : Type v) (M : Type w) [CommRing B] [AddCommGroup M]
    [Module B M] : IsCentralScalar B M := ⟨fun _ _ => rfl⟩

local instance rightTower (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] : IsScalarTower A Bᵐᵒᵖ M :=
  ⟨fun a b m => smul_assoc a b.unop m⟩

abbrev Sections (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] :=
  {s : B →ₐ[A] TrivSqZeroExt B M //
    (TrivSqZeroExt.fstHom A B M).comp s = AlgHom.id A B}

def trivialLaw : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  (∀ x y : TrivSqZeroExt B M,
    x * y = (x.fst * y.fst, x.fst • y.snd + y.fst • x.snd)) ∧
  (∀ a : A, algebraMap A (TrivSqZeroExt B M) a = (algebraMap A B a, 0))

def trivialCorrespondence : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  ∃ e : Derivation A B M ≃ Sections A B M,
    ∀ (D : Derivation A B M) (b : B), (e D).1 b = (b, D b)

section Quotient
variable {C : Type w} [CommRing C]

/-- The quotient acts on I since multiplication by any element of I kills I. -/
def quotientAction (I : Ideal C) (hI : I ^ 2 = ⊥) : C ⧸ I →+* AddMonoid.End I :=
  Ideal.Quotient.lift I (Module.toAddMonoidEnd C I) (by
    intro c hc
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    change c * (x : C) = 0
    have h := Ideal.mul_mem_mul hc x.property
    rw [← pow_two, hI] at h
    exact h)

abbrev quotientModule (I : Ideal C) (hI : I ^ 2 = ⊥) : Module (C ⧸ I) I :=
  Module.compHom I (quotientAction I hI)

end Quotient

section General
variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- Restriction of the quotient action along the given map to C/I. -/
abbrev idealModule (I : Ideal C) (hI : I ^ 2 = ⊥) (fbar : B →ₐ[A] C ⧸ I) : Module B I :=
  letI := quotientModule I hI
  Module.compHom I fbar.toRingHom

/-- Compatibility with the original A-action on the ideal. -/
theorem idealTower (I : Ideal C) (hI : I ^ 2 = ⊥) (fbar : B →ₐ[A] C ⧸ I) :
    letI := idealModule I hI fbar
    IsScalarTower A B I := by
  letI := idealModule I hI fbar
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  apply Subtype.ext
  change ((quotientAction I hI) (fbar (algebraMap A B a)) x : C) = a • (x : C)
  rw [fbar.commutes]
  change algebraMap A C a * (x : C) = a • (x : C)
  rw [Algebra.smul_def]

abbrev IdealDerivations (I : Ideal C) (hI : I ^ 2 = ⊥) (fbar : B →ₐ[A] C ⧸ I) :=
  letI := idealModule I hI fbar
  letI := idealTower I hI fbar
  Derivation A B I

abbrev Lifts (I : Ideal C) (fbar : B →ₐ[A] C ⧸ I) :=
  {g : B →ₐ[A] C // (Ideal.Quotient.mkₐ A I).comp g = fbar}

def quotientScalarLaw : Prop :=
  ∀ {C : Type w} [CommRing C] (I : Ideal C) (hI : I ^ 2 = ⊥),
    letI := quotientModule I hI
    ∀ (c : C) (x : I), (Ideal.Quotient.mk I c) • x = c • x

def inducedScalarLaw : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (fbar : B →ₐ[A] C ⧸ I),
    letI := quotientModule I hI
    letI := idealModule I hI fbar
    ∀ (b : B) (x : I), b • x = (fbar b) • x

def liftCorrespondence : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (fbar : B →ₐ[A] C ⧸ I)
    (f : B →ₐ[A] C) (_hf : (Ideal.Quotient.mkₐ A I).comp f = fbar),
    ∃ e : IdealDerivations I hI fbar ≃ Lifts I fbar,
      (∀ (D : IdealDerivations I hI fbar) (b : B), (e D).1 b = f b + (D b : C)) ∧
      (∀ (g : Lifts I fbar) (b : B), (e.symm g b : C) = g.1 b - f b)

end General
end Specs.AdvCommAlg.Differentials.SquareZero
