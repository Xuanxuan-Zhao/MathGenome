import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal

/-! Independent specifications for KD-05 (paper.tex, Naturality in the algebra).
The structural maps are the two displayed algebra structures. The horizontal
maps are arbitrary unital ring homomorphisms, with only commutativity of the
square assumed. Restriction of the target module is along the horizontal map f.
No finiteness, injectivity, surjectivity or nonzero-ring condition is imposed. -/
namespace Specs.AdvCommAlg.Differentials

universe u v u' v' u'' v''
noncomputable section

def algebraDifferentialMapType :=
  ∀ {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g),
    letI : Algebra B B' := f.toAlgebra
    KaehlerDifferential A B →ₗ[B] KaehlerDifferential A' B'

/-- The universal factorization of d ∘ f, using the canonical Mathlib map.
The two scalar-tower witnesses express exactly the given commuting square. -/
def algebraDifferentialMapValue : algebraDifferentialMapType.{u,v,u',v'} := by
  intro A B A' B' _ _ _ _ _ _ g f h
  letI : Algebra A A' := g.toAlgebra
  letI : Algebra B B' := f.toAlgebra
  letI : Algebra A B' := (f.comp (algebraMap A B)).toAlgebra
  letI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' h
  exact KaehlerDifferential.map A A' B B'

def algebraDifferentialMapApply : Prop :=
  ∀ {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g) (b : B),
    algebraDifferentialMapValue g f h (KaehlerDifferential.D A B b) =
      KaehlerDifferential.D A' B' (f b)

def algebraDifferentialMapUnique : Prop :=
  ∀ {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g),
    letI : Algebra B B' := f.toAlgebra
    ∀ L : KaehlerDifferential A B →ₗ[B] KaehlerDifferential A' B',
      (∀ b, L (KaehlerDifferential.D A B b) = KaehlerDifferential.D A' B' (f b)) →
      L = algebraDifferentialMapValue g f h

def algebraDifferentialMapId : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    ∀ x : KaehlerDifferential A B,
      algebraDifferentialMapValue (RingHom.id A) (RingHom.id B) (by ext; rfl) x = x

/-- Equality on every element, with scalar restriction implicit in the
function composition. This covers every pair of composable commuting squares. -/
def algebraDifferentialMapComp : Prop :=
  ∀ {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    {A'' : Type u''} {B'' : Type v''}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [CommRing A''] [CommRing B'']
    [Algebra A B] [Algebra A' B'] [Algebra A'' B'']
    (g : A →+* A') (f : B →+* B') (g' : A' →+* A'') (f' : B' →+* B'')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g)
    (h' : f'.comp (algebraMap A' B') = (algebraMap A'' B'').comp g')
    (x : KaehlerDifferential A B),
    algebraDifferentialMapValue (g'.comp g) (f'.comp f) (by
      rw [RingHom.comp_assoc, h, ← RingHom.comp_assoc, h', RingHom.comp_assoc]) x =
      algebraDifferentialMapValue g' f' h' (algebraDifferentialMapValue g f h x)

end
end Specs.AdvCommAlg.Differentials
