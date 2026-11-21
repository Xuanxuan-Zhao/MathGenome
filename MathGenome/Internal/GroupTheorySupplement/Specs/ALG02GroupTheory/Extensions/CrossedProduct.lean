import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.SectionFactorSystem

/-!
The converse in Proposition GR02-C04.01 of paper.tex, including the prescribed
end maps, the canonical normalized section, and the coordinate equivalence.
-/

namespace Specs.ALG02GroupTheory.Extensions

universe u v w

-- The expected types quantify over kernel and quotient in independent universes.
set_option linter.checkUnivs false

/-- The pair carrier, indexed by its factor system so distinct laws can coexist. -/
@[ext]
structure CrossedProductModel {N : Type u} {Q : Type w} [Group N] [Group Q]
    (_ : NormalizedFactorSystem N Q) where
  left : N
  right : Q

variable {N : Type u} {Q : Type w} [Group N] [Group Q]

def CrossedProductType :=
  ∀ {N : Type u} {Q : Type w} [Group N] [Group Q], NormalizedFactorSystem N Q → Type (max u w)

abbrev crossedProductValue : CrossedProductType.{u, w} := fun D => CrossedProductModel D

namespace CrossedProductModel

variable {D : NormalizedFactorSystem N Q}

instance : Mul (CrossedProductModel D) :=
  ⟨fun x y => ⟨x.left * D.alpha x.right y.left * D.factor x.right y.right, x.right * y.right⟩⟩

instance : One (CrossedProductModel D) := ⟨⟨1, 1⟩⟩

instance : Inv (CrossedProductModel D) :=
  ⟨fun x =>
    ⟨(D.factor x.right⁻¹ x.right)⁻¹ * (D.alpha x.right⁻¹ x.left)⁻¹, x.right⁻¹⟩⟩

@[simp] theorem mul_left (x y : CrossedProductModel D) :
    (x * y).left = x.left * D.alpha x.right y.left * D.factor x.right y.right := rfl

@[simp] theorem mul_right (x y : CrossedProductModel D) :
    (x * y).right = x.right * y.right := rfl

@[simp] theorem one_left : (1 : CrossedProductModel D).left = 1 := rfl

@[simp] theorem one_right : (1 : CrossedProductModel D).right = 1 := rfl

@[simp] theorem inv_left (x : CrossedProductModel D) :
    x⁻¹.left = (D.factor x.right⁻¹ x.right)⁻¹ * (D.alpha x.right⁻¹ x.left)⁻¹ := rfl

@[simp] theorem inv_right (x : CrossedProductModel D) : x⁻¹.right = x.right⁻¹ := rfl

private theorem alpha_apply_alpha (q r : Q) (n : N) :
    D.alpha q (D.alpha r n) =
      D.factor q r * D.alpha (q * r) n * (D.factor q r)⁻¹ := by
  simpa only [MulAut.mul_apply, MulAut.conj_apply] using
    congrArg (fun a : MulAut N => a n) (D.alpha_mul q r)

private theorem mul_assoc_left (x y z : CrossedProductModel D) :
    ((x * y) * z).left = (x * (y * z)).left := by
  simp only [mul_left, mul_right, map_mul, mul_assoc]
  rw [alpha_apply_alpha, ← D.factor_assoc]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- The factor-system identities make the prescribed operation a group law. -/
instance instGroup : Group (CrossedProductModel D) where
  mul_assoc x y z := CrossedProductModel.ext (mul_assoc_left x y z) (mul_assoc _ _ _)
  one_mul x := CrossedProductModel.ext (by simp [D.alpha_one, D.factor_one_left]) (one_mul _)
  mul_one x := CrossedProductModel.ext (by simp [D.factor_one_right]) (mul_one _)
  inv_mul_cancel x := CrossedProductModel.ext (by simp [mul_assoc]) (inv_mul_cancel _)

end CrossedProductModel

def CrossedProductGroupType :=
  ∀ {N : Type u} {Q : Type w} [Group N] [Group Q] (D : NormalizedFactorSystem N Q),
    Group (crossedProductValue D)

abbrev crossedProductGroupValue : CrossedProductGroupType.{u, w} :=
  fun _ => CrossedProductModel.instGroup

/-- The model short exact sequence with inclusion (n mapsto (n,1)) and projection
((n,q) mapsto q). -/
def crossedProductExtensionValue (D : NormalizedFactorSystem N Q) :
    GroupExtension N (crossedProductValue D) Q where
  inl :=
    { toFun := fun n => ⟨n, 1⟩
      map_one' := rfl
      map_mul' := fun n m => CrossedProductModel.ext
        (by simp [D.alpha_one, D.factor_one_left]) (by simp) }
  rightHom :=
    { toFun := CrossedProductModel.right
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  inl_injective := fun _ _ h => congrArg CrossedProductModel.left h
  range_inl_eq_ker_rightHom := by
    ext x
    change (∃ n, CrossedProductModel.mk n 1 = x) ↔ x.right = 1
    constructor
    · rintro ⟨n, rfl⟩
      rfl
    · intro hx
      exact ⟨x.left, CrossedProductModel.ext rfl hx.symm⟩
  rightHom_surjective := fun q => ⟨⟨1, q⟩, rfl⟩

def CrossedProductExtensionType :=
  ∀ {N : Type u} {Q : Type w} [Group N] [Group Q] (D : NormalizedFactorSystem N Q),
    GroupExtension N (crossedProductValue D) Q

/-- The section (q mapsto (1,q)) of the model extension. -/
def crossedProductSectionValue (D : NormalizedFactorSystem N Q) :
    normalizedSectionValue (crossedProductExtensionValue D) :=
  ⟨{ toFun := fun q => ⟨1, q⟩
     rightInverse_rightHom := fun _ => rfl }, rfl⟩

def CrossedProductSectionType :=
  ∀ {N : Type u} {Q : Type w} [Group N] [Group Q] (D : NormalizedFactorSystem N Q),
    normalizedSectionValue (crossedProductExtensionValue D)

def CrossedProductRecoversFactorSystem : Prop :=
  ∀ {N : Type u} {Q : Type w} [Group N] [Group Q] (D : NormalizedFactorSystem N Q),
    sectionAlphaValue (crossedProductExtensionValue D) (crossedProductSectionValue D) = D.alpha ∧
    sectionFactorValue (crossedProductExtensionValue D) (crossedProductSectionValue D) = D.factor

/-- The middle map is the coordinate formula and the bundled equivalence fixes the ends. -/
def CrossedProductCoordinateEquivalence : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s : normalizedSectionValue S),
    ∃ D : NormalizedFactorSystem N Q,
      D.alpha = sectionAlphaValue S s ∧ D.factor = sectionFactorValue S s ∧
      ∃ e : (crossedProductExtensionValue D).Equiv S,
        ∀ x : crossedProductValue D, e x = S.inl x.left * s.val x.right

end Specs.ALG02GroupTheory.Extensions
