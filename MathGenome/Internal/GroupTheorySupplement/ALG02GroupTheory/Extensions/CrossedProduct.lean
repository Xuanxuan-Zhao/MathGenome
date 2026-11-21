import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.SectionFactorSystem
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.CrossedProduct
import Mathlib.Tactic.Group

namespace ALG02GroupTheory.Extensions

open Specs.ALG02GroupTheory.Extensions
  (CrossedProductModel crossedProductExtensionValue crossedProductSectionValue)

variable {N E Q : Type*} [Group N] [Group E] [Group Q]

/-- The group on pairs associated to a normalized factor system. -/
abbrev CrossedProduct (D : FactorSystem N Q) := CrossedProductModel D

/-- The group structure with twisted multiplication on the pair carrier. -/
abbrev crossedProductGroup (D : FactorSystem N Q) : Group (CrossedProduct D) :=
  CrossedProductModel.instGroup

/-- The crossed product as an exact extension with the prescribed end maps. -/
def crossedProductExtension (D : FactorSystem N Q) : GroupExtension N (CrossedProduct D) Q :=
  crossedProductExtensionValue D

/-- The normalized section whose first coordinate is the identity. -/
def crossedProductSection (D : FactorSystem N Q) : NormalizedSection (crossedProductExtension D) :=
  crossedProductSectionValue D

@[simp] theorem crossedProductExtension_inl (D : FactorSystem N Q) (n : N) :
    (crossedProductExtension D).inl n = ⟨n, 1⟩ := rfl

@[simp] theorem crossedProductExtension_rightHom (D : FactorSystem N Q) (x : CrossedProduct D) :
    (crossedProductExtension D).rightHom x = x.right := rfl

@[simp] theorem crossedProductSection_apply (D : FactorSystem N Q) (q : Q) :
    (crossedProductSection D).val q = ⟨1, q⟩ := rfl

/-- Extracting from the canonical normalized section recovers both input functions. -/
theorem crossedProductRecoversFactorSystem (D : FactorSystem N Q) :
    sectionAlpha (crossedProductExtension D) (crossedProductSection D) = D.alpha ∧
    sectionFactor (crossedProductExtension D) (crossedProductSection D) = D.factor := by
  constructor
  · funext q
    ext n
    apply (crossedProductExtension D).inl_injective
    rw [inl_sectionAlpha]
    have h : (crossedProductSection D).val q * (crossedProductExtension D).inl n =
        (crossedProductExtension D).inl (D.alpha q n) * (crossedProductSection D).val q := by
      apply CrossedProductModel.ext <;>
        simp [D.alpha_one, D.factor_one_left, D.factor_one_right]
    rw [h, mul_inv_cancel_right]
  · funext q r
    apply (crossedProductExtension D).inl_injective
    rw [inl_sectionFactor]
    have h : (crossedProductSection D).val q * (crossedProductSection D).val r =
        (crossedProductExtension D).inl (D.factor q r) * (crossedProductSection D).val (q * r) := by
      apply CrossedProductModel.ext <;> simp [D.factor_one_left]
    rw [h, mul_inv_cancel_right]

variable (S : GroupExtension N E Q) (s : NormalizedSection S)

private def coordinateHom : CrossedProduct (factorSystemOfSection S s) →* E where
  toFun x := S.inl x.left * s.val x.right
  map_one' := by
    change S.inl 1 * s.val 1 = 1
    simp [s.property]
  map_mul' x y := by
    change S.inl (x.left * sectionAlpha S s x.right y.left * sectionFactor S s x.right y.right) *
      s.val (x.right * y.right) = (S.inl x.left * s.val x.right) * (S.inl y.left * s.val y.right)
    simp only [map_mul, inl_sectionAlpha, inl_sectionFactor]
    group

/-- Reconstruct an extension with a chosen section by an equivalence fixing the end groups. -/
noncomputable def coordinateEquiv :
    (crossedProductExtension (factorSystemOfSection S s)).Equiv S :=
  GroupExtension.Equiv.ofMonoidHom (coordinateHom S s)
    (by
      ext n
      change S.inl n * s.val 1 = S.inl n
      rw [s.property, mul_one])
    (by
      ext x
      change S.rightHom (S.inl x.left * s.val x.right) = x.right
      simp)

@[simp] theorem coordinateEquiv_apply (x : CrossedProduct (factorSystemOfSection S s)) :
    coordinateEquiv S s x = S.inl x.left * s.val x.right := rfl

theorem crossedProductCoordinateEquivalence :
    ∃ D : FactorSystem N Q,
      D.alpha = sectionAlpha S s ∧ D.factor = sectionFactor S s ∧
      ∃ e : (crossedProductExtension D).Equiv S,
        ∀ x : CrossedProduct D, e x = S.inl x.left * s.val x.right :=
  ⟨factorSystemOfSection S s, rfl, rfl, coordinateEquiv S s, coordinateEquiv_apply S s⟩

end ALG02GroupTheory.Extensions
