import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerConditions

/-! Statement of the largest Artin quotient admitting a prescribed lift. -/

universe u w

namespace CommutativeAlgebraNotes.LargestArtinLiftQuotientSpec

open LocalArtinAlgebra SchlessingerConditionsSpec CategoryTheory

variable {k : Type u} [Field k] {A B : LocalArtinAlgebra.{u,u} k}

/-- The kernel of a local algebra map, viewed as a vector subspace of its source. -/
abbrev kernelSubspace (f : Hom B A) : Submodule k B :=
  (RingHom.ker f.val.toRingHom).restrictScalars k

/-- A lift over B/J, using a presentation of B/J by a surjective local algebra map
out of B whose kernel is exactly J. The map to A is the one induced by f. -/
def LiftsModuloModel (F : ArtinFunctorModel.{u,w} k) (f : Hom B A)
    (x : F.toFunctor.obj A) (J : Submodule k B) : Prop :=
  ∃ (Q : LocalArtinAlgebra.{u,u} k) (q : Hom B Q) (g : Hom Q A),
    Function.Surjective q ∧ kernelSubspace q = J ∧ g.comp q = f ∧
      ∃ y : F.toFunctor.obj Q, F.toFunctor.map g y = x

set_option linter.checkUnivs false in
def LiftsModuloType :=
  ∀ {k : Type u} [Field k] {A B : LocalArtinAlgebra.{u,u} k}
    (F : ArtinFunctorModel.{u,w} k), Hom B A →
      F.toFunctor.obj A → Submodule k B → Prop

/-- Lemma 6.8. No condition on the dimension of the kernel is imposed. -/
def ExistsLeastLiftSubspace : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k) (_ : H1Model F)
    {A B : LocalArtinAlgebra.{u,u} k} (f : Hom B A),
    Function.Surjective f →
    (∀ a ∈ IsLocalRing.maximalIdeal B, ∀ b ∈ RingHom.ker f.val.toRingHom, a * b = 0) →
    ∀ x : F.toFunctor.obj A,
      ∃ J : Submodule k B,
        IsLeast {L | L ≤ kernelSubspace f ∧ LiftsModuloModel F f x L} J

end CommutativeAlgebraNotes.LargestArtinLiftQuotientSpec
