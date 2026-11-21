import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Naturality
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! KD-17, paper.tex:355–371. Arbitrary scalar extension, with its generator
formula and coherence. A pushout C of R → S and R → B is a presentation-free
way of writing C = S ⊗[R] B; it includes the canonical tensor product, and
allows canonical unitors and associators without equality of ring types.
All rings may be zero. No flatness or finiteness hypothesis is imposed. -/
namespace Specs.AdvCommAlg.Differentials

open TensorProduct
universe u v w z t q
noncomputable section

def baseChangeEquivType :=
  ∀ (R : Type u) (S : Type v) (B : Type w) (C : Type z)
  [CommRing R] [CommRing S] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
  [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C],
  C ⊗[B] KaehlerDifferential R B ≃ₗ[C] KaehlerDifferential S C

def baseChangeEquivValue : baseChangeEquivType.{u,v,w,z} :=
  fun R S B C _ _ _ _ _ _ _ _ _ _ _ _ =>
    KaehlerDifferential.tensorKaehlerEquiv R S B C

def baseChangeFormula : Prop :=
  ∀ (R : Type u) (S : Type v) (B : Type w) (C : Type z)
  [CommRing R] [CommRing S] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
  [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C],
  ∀ (c : C) (b : B),
    baseChangeEquivValue R S B C (c ⊗ₜ KaehlerDifferential.D R B b) =
      c • KaehlerDifferential.D S C (algebraMap B C b)

def baseChangeNaturality : Prop :=
  ∀ (R : Type u) (S : Type v) (B : Type w) (C : Type z)
  [CommRing R] [CommRing S] [CommRing B] [CommRing C]
  [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
  [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C],
  ∀ (c : C) (ω : KaehlerDifferential R B),
    baseChangeEquivValue R S B C (c ⊗ₜ ω) =
      c • algebraDifferentialMapValue (algebraMap R S) (algebraMap B C)
        (by rw [← IsScalarTower.algebraMap_eq R B C, ← IsScalarTower.algebraMap_eq R S C]) ω

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- In the canonical tensor model, the right structural map is b ↦ 1 ⊗ b. -/
def baseChangeTensorFormula : Prop :=
  ∀ (R : Type u) (S : Type v) (B : Type w)
  [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  (c : S ⊗[R] B) (b : B),
    baseChangeEquivValue R S B (S ⊗[R] B) (c ⊗ₜ KaehlerDifferential.D R B b) =
      c • KaehlerDifferential.D S (S ⊗[R] B) (1 ⊗ₜ b)

/-- The identity pushout is B itself; this is the tensor unitor compatibility. -/
def baseChangeIdentity : Prop :=
  ∀ (R : Type u) (B : Type w) [CommRing R] [CommRing B] [Algebra R B],
    baseChangeEquivValue R R B B = TensorProduct.lid B (KaehlerDifferential R B)

/-- Pasting two pushouts gives the outer pushout (comp_iff). The equality is on
all elements of the iterated scalar extension; cancelBaseChange is the canonical
module associator followed by the tensor unitor. The ring pushout comparison is
likewise the tensor associativity isomorphism, so arbitrary successive base
changes, including their canonical tensor models, are covered. -/
def baseChangeComposition : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type t)
    (B : Type w) (C : Type z) (F : Type q)
  [CommRing R] [CommRing S] [CommRing T] [CommRing B] [CommRing C] [CommRing F]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
  [IsScalarTower R S C] [IsScalarTower R B C]
  [Algebra R F] [Algebra S F] [Algebra T F] [Algebra B F] [Algebra C F]
  [IsScalarTower R T F] [IsScalarTower S T F] [IsScalarTower S C F]
  [IsScalarTower R B F] [IsScalarTower R C F] [IsScalarTower B C F]
  [Algebra.IsPushout R S B C] [Algebra.IsPushout S T C F],
  letI : Algebra.IsPushout R T B F :=
    (Algebra.IsPushout.comp_iff R S B C (T := T)).mpr inferInstance
  ∀ x : F ⊗[C] (C ⊗[B] KaehlerDifferential R B),
    baseChangeEquivValue R T B F
        (AlgebraTensorModule.cancelBaseChange B C F F (KaehlerDifferential R B) x) =
      baseChangeEquivValue S T C F
        ((baseChangeEquivValue R S B C).toLinearMap.baseChange F x)

/-- The concrete identity-base-change comparison through R ⊗[R] B ≃ B,
on the extended differential generators. Together with baseChangeIdentity
this identifies the unitor in both realizations of the identity pushout. -/
def baseChangeTensorIdentity : Prop :=
  ∀ (R : Type u) (B : Type w) [CommRing R] [CommRing B] [Algebra R B]
  (c : R ⊗[R] B) (b : B),
  algebraDifferentialMapValue (RingHom.id R) (Algebra.TensorProduct.lid R B).toRingHom
    (by ext a; exact (Algebra.TensorProduct.lid R B).commutes a)
    (baseChangeEquivValue R R B (R ⊗[R] B) (c ⊗ₜ KaehlerDifferential.D R B b)) =
    Algebra.TensorProduct.lid R B c • KaehlerDifferential.D R B b

/-- The concrete ring comparison for composition is the canonical associator
T ⊗[S] (S ⊗[R] B) ≃ T ⊗[R] B. This states its compatibility on all scalar
multiples of extended db, which generate the source of baseChangeComposition. -/
def baseChangeTensorComposition : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type t) (B : Type w)
  [CommRing R] [CommRing S] [CommRing T] [CommRing B]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R B]
  (c : T ⊗[S] (S ⊗[R] B)) (b : B),
  algebraDifferentialMapValue (RingHom.id T)
    (Algebra.TensorProduct.cancelBaseChange R S T T B).toRingHom
    (by ext a; exact (Algebra.TensorProduct.cancelBaseChange R S T T B).commutes a)
    (baseChangeEquivValue S T (S ⊗[R] B) (T ⊗[S] (S ⊗[R] B))
      (c ⊗ₜ baseChangeEquivValue R S B (S ⊗[R] B)
        (1 ⊗ₜ KaehlerDifferential.D R B b))) =
  baseChangeEquivValue R T B (T ⊗[R] B)
    (Algebra.TensorProduct.cancelBaseChange R S T T B c ⊗ₜ KaehlerDifferential.D R B b)

end
end Specs.AdvCommAlg.Differentials
