import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerConditions

universe u v w

namespace CommutativeAlgebraNotes.ArtinSurjectionsAndGluingSpec

open LocalArtinAlgebra SchlessingerConditionsSpec

variable {k : Type u} [Field k]

/-- A factorisation into the indicated number of small extensions.
Length zero identifies the endpoints by an isomorphism, including the identity.
A positive length records only small extensions, with the original endpoints. -/
inductive SmallExtensionChainModel :
    {A B : LocalArtinAlgebra.{u,v} k} → Hom A B → ℕ → Prop
  | zero {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) (hf : Function.Bijective f) :
      SmallExtensionChainModel f 0
  | single {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) (hf : SmallExtensionModel f) :
      SmallExtensionChainModel f 1
  | cons {A B C : LocalArtinAlgebra.{u,v} k} {n : ℕ} (f : Hom A B) (g : Hom B C)
      (hf : SmallExtensionModel f) (hg : SmallExtensionChainModel g (n + 1)) :
      SmallExtensionChainModel (g.comp f) ((n + 1) + 1)

set_option linter.checkUnivs false in
def SmallExtensionChainType :=
  ∀ {k : Type u} [Field k] {A B : LocalArtinAlgebra.{u,v} k}, Hom A B → ℕ → Prop

abbrev smallExtensionChainValue {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) (n : ℕ) :=
  SmallExtensionChainModel f n

def SmallExtensionChainIdentity : Prop :=
  ∀ {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,v} k),
    SmallExtensionChainModel (Hom.id A) 0

def SurjectionFactorization : Prop :=
  ∀ {k : Type u} [Field k] {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B),
    Function.Surjective f → ∃ n : ℕ, SmallExtensionChainModel f n

def ComparisonSurjective : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k), H1Model F →
    ∀ {A₁ A A₂ : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom A₂ A),
      Function.Surjective g → Function.Surjective (comparisonModel F f g)

end CommutativeAlgebraNotes.ArtinSurjectionsAndGluingSpec
