import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler

namespace CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity.Specs

open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs (intersectionEuler)

universe u v w

/-- Additivity in the first variable along a short exact sequence of finite modules
whose supports intersect that of the fixed module only at the closed point. -/
def addLeft : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (A M C : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R A] [Module.Finite R M] [Module.Finite R C] [Module.Finite R N]
    (f : A →ₗ[R] M) (g : M →ₗ[R] C),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    Module.support R A ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} →
    Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} →
    Module.support R C ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} →
      intersectionEuler M N = intersectionEuler A N + intersectionEuler C N

/-- Additivity in the second variable under the same isolated-support condition. -/
def addRight : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (A M C : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R A] [Module.Finite R M] [Module.Finite R C] [Module.Finite R N]
    (f : A →ₗ[R] M) (g : M →ₗ[R] C),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    Module.support R N ∩ Module.support R A ⊆ {IsLocalRing.closedPoint R} →
    Module.support R N ∩ Module.support R M ⊆ {IsLocalRing.closedPoint R} →
    Module.support R N ∩ Module.support R C ⊆ {IsLocalRing.closedPoint R} →
      intersectionEuler N M = intersectionEuler N A + intersectionEuler N C

end CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity.Specs
