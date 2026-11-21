import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.Corner
import Mathlib.RingTheory.Finiteness.Basic

/-! The corner of a unital ring at an arbitrary idempotent. -/

universe u v

namespace RM03.Morita

open MulOpposite CategoryTheory

variable {R : Type u} [Ring R]

theorem carriers : CornerSpec.carriersType.{u} := by
  intro R _ e
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change e.val * x = x ↔ ∃ r, e.val * r = x
    constructor
    · exact fun hx => ⟨x, hx⟩
    · rintro ⟨r, rfl⟩
      rw [← mul_assoc, e.property.eq]
  · intro x
    change x * e.val = x ↔ ∃ r, r * e.val = x
    constructor
    · exact fun hx => ⟨x, hx⟩
    · rintro ⟨r, rfl⟩
      rw [mul_assoc, e.property.eq]
  · intro x
    change (e.val * x = x ∧ x * e.val = x) ↔ ∃ r, e.val * r * e.val = x
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨x, by rw [hx, hy]⟩
    · rintro ⟨r, rfl⟩
      constructor
      · rw [← mul_assoc e.val (e.val * r), ← mul_assoc e.val e.val, e.property.eq]
      · rw [mul_assoc, e.property.eq]

theorem moduleCorner_image : CornerSpec.moduleCornerImageType.{u, v} := by
  intro R _ e M _ _
  ext m
  change op e.val • m = m ↔ ∃ n, op e.val • n = m
  constructor
  · exact fun hm => ⟨m, hm⟩
  · rintro ⟨n, rfl⟩
    exact (toModuleCorner e n).property

/-- Left multiplication by (e) from the free right module of rank one. -/
def rightIdealProjection (e : Idempotent R) : Rᵐᵒᵖ →ₗ[Rᵐᵒᵖ] rightIdeal e where
  toFun r := r • rightGenerator e
  map_add' r s := add_smul r s _
  map_smul' r s := mul_smul r s _

/-- The inclusion of (eR), written using opposite-ring coordinates in the free module. -/
def rightIdealInclusion (e : Idempotent R) : rightIdeal e →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun x := op x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rightIdeal_projection_inclusion (e : Idempotent R) :
    (rightIdealProjection e).comp (rightIdealInclusion e) = LinearMap.id :=
  LinearMap.ext fun x => Subtype.ext x.property

theorem finite_projective : CornerSpec.finiteProjectiveType.{u} := by
  intro R _ e
  refine ⟨Module.Finite.of_surjective (rightIdealProjection e) ?_, ?_⟩
  · exact fun x => ⟨rightIdealInclusion e x,
      LinearMap.congr_fun (rightIdeal_projection_inclusion e) x⟩
  · exact Module.Projective.of_split _ _ (rightIdeal_projection_inclusion e)

/-- Evaluation at (e) lands in the corner because (f(e)e=f(e)). -/
def evaluateAtIdempotent (e : Idempotent R) (f : Module.End Rᵐᵒᵖ (rightIdeal e)) :
    Corner e :=
  ⟨(f (rightGenerator e)).val, (f (rightGenerator e)).property, by
    have h : op e.val • rightGenerator e = rightGenerator e := Subtype.ext e.property
    have hf := f.map_smul (op e.val) (rightGenerator e)
    rw [h] at hf
    exact (congrArg Subtype.val hf).symm⟩

/-- Left multiplication identifies (eRe) with (operatorname{End}_R(eR)). -/
def cornerEndEquiv (e : Idempotent R) : Corner e ≃+* Module.End Rᵐᵒᵖ (rightIdeal e) where
  toFun := cornerToEnd e
  invFun := evaluateAtIdempotent e
  left_inv a := Subtype.ext a.property.2
  right_inv f := LinearMap.ext fun x => by
    apply Subtype.ext
    change (f (rightGenerator e)).val * x.val = (f x).val
    have hx : op x.val • rightGenerator e = x := Subtype.ext x.property
    have hf := f.map_smul (op x.val) (rightGenerator e)
    rw [hx] at hf
    exact (congrArg Subtype.val hf).symm
  map_add' := map_add (cornerToEnd e)
  map_mul' := map_mul (cornerToEnd e)

@[simp] theorem cornerEndEquiv_apply_val (e : Idempotent R) (a : Corner e)
    (x : rightIdeal e) : (cornerEndEquiv e a x).val = a.val * x.val := rfl

@[simp] theorem cornerEndEquiv_symm_val (e : Idempotent R)
    (f : Module.End Rᵐᵒᵖ (rightIdeal e)) :
    ((cornerEndEquiv e).symm f).val = (f (rightGenerator e)).val := rfl

theorem corner_endomorphisms : CornerSpec.cornerEndomorphismsType.{u} :=
  fun e => ⟨cornerEndEquiv e, fun _ _ => rfl, fun _ => rfl⟩

/-- The functor of taking the image of right multiplication by the idempotent. -/
def cornerFunctor (e : Idempotent R) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} (Corner e)ᵐᵒᵖ :=
  CornerSpec.cornerFunctorValue e

@[simp] theorem cornerFunctor_map_val (e : Idempotent R) {M N : ModuleCat.{v} Rᵐᵒᵖ}
    (f : M ⟶ N) (m : moduleCorner (M := M) e) :
    ((cornerFunctor e).map f m).val = f m.val := rfl

end RM03.Morita
