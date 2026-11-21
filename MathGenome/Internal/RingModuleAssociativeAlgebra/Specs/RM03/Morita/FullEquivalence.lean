import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.FullGenerator
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.CornerTensor
import Mathlib.CategoryTheory.Equivalence

/-! The full-corner equivalence with its specified functors and multiplication. -/

universe u v

namespace RM03.Morita

open CategoryTheory MulOpposite
open P103.BalancedTensor (Tensor tmul)

variable {R : Type u} [Ring R]

/-- Extension from the corner by the (eRe, R)-bimodule eR. -/
abbrev fromCornerFunctor (e : Idempotent R) :
    ModuleCat.{max u v} (Corner e)ᵐᵒᵖ ⥤ ModuleCat.{max u v} Rᵐᵒᵖ :=
  tensorWithBimodule (rightIdeal e)

namespace FullEquivalenceSpec

/-- Multiplication and its inverse on every right module, independently of the
universe of the ring. -/
def multiplicationEquivType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R), IsFull e →
    ∀ (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
      let T := Tensor (Corner e) (moduleCorner (M := M) e) (rightIdeal e)
      letI : Module Rᵐᵒᵖ T := P103.BalancedTensor.rightModule
      ∃ E : T ≃ₗ[Rᵐᵒᵖ] M,
        (∀ (m : moduleCorner (M := M) e) (x : rightIdeal e),
          E (tmul (Corner e) m x) = op x.val • m.val) ∧
        (∀ (n : ℕ) (r s : Fin n → R), (∑ i, r i * e.val * s i) = 1 →
          ∀ m : M, E.symm m =
            ∑ i, tmul (Corner e) (toModuleCorner e (op (r i) • m))
              (op (s i) • rightGenerator e))

/-- The equivalence along a full idempotent, with both functors fixed and
multiplication as the comparison on right R-modules. The inverse formula holds
for every finite expression exhibiting fullness. -/
def fullEquivalenceType : Prop :=
  ∀ {R : Type u} [Ring R] (e : Idempotent R), IsFull e →
    ∃ (E : ModuleCat.{max u v} Rᵐᵒᵖ ≌ ModuleCat.{max u v} (Corner e)ᵐᵒᵖ)
      (hF : E.functor = CornerSpec.cornerFunctorValue e)
      (hG : E.inverse = fromCornerFunctor e),
      let η : 𝟭 _ ≅ CornerSpec.cornerFunctorValue e ⋙ fromCornerFunctor e :=
        cast (by rw [hF, hG]) E.unitIso
      (∀ (M : ModuleCat.{max u v} Rᵐᵒᵖ) (m : moduleCorner (M := M) e)
          (x : rightIdeal e),
        η.inv.app M (tmul (Corner e) m x) = op x.val • m.val) ∧
      (∀ (M : ModuleCat.{max u v} Rᵐᵒᵖ) (n : ℕ) (r s : Fin n → R),
        (∑ i, r i * e.val * s i) = 1 →
          ∀ m : M, η.hom.app M m =
            ∑ i, tmul (Corner e) (toModuleCorner e (op (r i) • m))
              (op (s i) • rightGenerator e))

end FullEquivalenceSpec
end RM03.Morita
