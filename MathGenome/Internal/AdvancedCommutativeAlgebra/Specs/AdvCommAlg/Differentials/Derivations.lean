import Mathlib.RingTheory.Derivation.Basic

/-! Independent specifications for paper.tex, Definition KD-01 (lines 145–154).
All rings are commutative and unital; no nontriviality is assumed. The A-action
on each coefficient module is the restriction of the B-action, expressed by
IsScalarTower. We use Mathlib's canonical relative derivations throughout. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w z

def relativeDerivationType :=
  ∀ (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M], Type (max v w)

def relativeDerivationValue : relativeDerivationType.{u,v,w} :=
  fun A B M _ _ _ _ _ _ _ => Derivation A B M

def linearCharacterization : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  ∀ f : B →ₗ[A] M,
    (∃! D : Derivation A B M, D.toLinearMap = f) ↔
      ∀ x y : B, f (x * y) = x • f y + y • f x

def additiveCharacterization : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  ∀ f : B → M,
    (∃! D : Derivation A B M, (D : B → M) = f) ↔
      (∀ x y : B, f (x + y) = f x + f y) ∧
      (∀ x y : B, f (x * y) = x • f y + y • f x) ∧
      (∀ a : A, f (algebraMap A B a) = 0)

def vanishesOnBase : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  ∀ D : Derivation A B M, D 1 = 0 ∧ ∀ a : A, D (algebraMap A B a) = 0

def pointwiseOperations : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  (∀ x : B, (0 : Derivation A B M) x = 0) ∧
  (∀ (D E : Derivation A B M) (x : B), (D + E) x = D x + E x) ∧
  (∀ (D : Derivation A B M) (x : B), (-D) x = -D x) ∧
  (∀ (b : B) (D : Derivation A B M) (x : B), (b • D) x = b • D x)

def extOnGenerators : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  ∀ (s : Set B), Algebra.adjoin A s = ⊤ →
    ∀ D E : Derivation A B M, (∀ x ∈ s, D x = E x) → D = E

def extOnFamily : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M],
  ∀ {ι : Type z} (g : ι → B), Algebra.adjoin A (Set.range g) = ⊤ →
    ∀ D E : Derivation A B M, (∀ i, D (g i) = E (g i)) → D = E

def postcomposeType :=
  ∀ {A : Type u} {B : Type v} {M : Type w} {N : Type z}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N],
  (M →ₗ[B] N) → Derivation A B M →ₗ[B] Derivation A B N

def postcomposeValue : postcomposeType.{u,v,w,z} :=
  fun {_ _ _ _} _ _ _ _ _ _ _ _ _ _ _ f => f.compDer

def postcomposeApply : Prop :=
  ∀ {A : Type u} {B : Type v} {M : Type w} {N : Type z}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N],
  ∀ (f : M →ₗ[B] N) (D : Derivation A B M) (x : B), f.compDer D x = f (D x)

end Specs.AdvCommAlg.Differentials
