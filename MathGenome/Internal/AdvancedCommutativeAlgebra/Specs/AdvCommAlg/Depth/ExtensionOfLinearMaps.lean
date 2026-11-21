import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.Algebra.Module.Equiv.Basic

/-! DP-15, paper.tex:3208–3222. The actual restriction map along the ideal
inclusion, and evaluation at one. Bijectivity of this linear map is equivalent
to its being a linear isomorphism. No properness or nonzero assumptions occur. -/

universe u
namespace AdvCommAlg.Depth

/-- Restriction along the inclusion `I ↪ R`. -/
def restrictionMap {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] :
    (R →ₗ[R] M) →ₗ[R] (I →ₗ[R] M) where
  toFun f := f.comp I.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical identification `Hom_R(R,M) ≃ M` by evaluation at one. -/
def evaluationAtOne {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] : (R →ₗ[R] M) ≃ₗ[R] M :=
  LinearMap.ringLmapEquivSelf R R M

namespace Specs

def grade_ge_two_iff_restriction_bijectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    (2 : ℕ∞) ≤ gradeValue I M ↔ Function.Bijective (restrictionMap I M)

def grade_ge_two_iff_restriction_isomorphismType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    (2 : ℕ∞) ≤ gradeValue I M ↔
      ∃ e : (R →ₗ[R] M) ≃ₗ[R] (I →ₗ[R] M), e.toLinearMap = restrictionMap I M

def restrictionMap_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] (f : R →ₗ[R] M) (x : I),
    restrictionMap I M f x = f (x : R)

def evaluationAtOne_applyType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (f : R →ₗ[R] M), evaluationAtOne M f = f 1

def restrictionMap_evaluationAtOne_symmType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] (m : M) (x : I),
    restrictionMap I M ((evaluationAtOne M).symm m) x = (x : R) • m

end Specs
end AdvCommAlg.Depth
