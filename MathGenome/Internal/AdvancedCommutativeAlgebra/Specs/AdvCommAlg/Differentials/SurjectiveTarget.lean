import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Naturality

/-! KD-10, paper.tex 265–272. The horizontal target map is surjective;
the base map is arbitrary. Scalars on the target differential module are
restricted along the target map. All commutative unital rings, including the
zero ring, are allowed. -/
namespace Specs.AdvCommAlg.Differentials

universe u v u' v'
noncomputable section

/-- Every differential in the target lifts through a surjective target map. -/
def surjectiveTargetMap : Prop :=
  ∀ {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g),
    Function.Surjective f → Function.Surjective (algebraDifferentialMapValue g f h)

/-- The kernel is the B-span of exactly the differentials whose images come
from the new base A'. No surjectivity condition is imposed on the base map. -/
def surjectiveTargetKernel : Prop :=
  ∀ {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g),
    Function.Surjective f →
    letI : Algebra B B' := f.toAlgebra
    LinearMap.ker (algebraDifferentialMapValue g f h) =
      Submodule.span B
        {x | ∃ b : B, f b ∈ Set.range (algebraMap A' B') ∧
          x = KaehlerDifferential.D A B b}

end
end Specs.AdvCommAlg.Differentials
