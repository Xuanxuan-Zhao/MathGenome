import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Realization.RationalFunctionAction
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.CompactActions.FixedFieldTheorem
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Realization.Tate
import Mathlib.Algebra.Field.ZMod

/-! Tate's realization theorem (FT-C12). We apply the compact fixed-field
theorem to the accepted faithful action on the prescribed rational function
field. No restriction is placed on the chosen coefficient field. -/

universe u v
noncomputable section
namespace AdvancedFieldTheory.Realization

open AdvancedFieldTheory.CompactActions

/-- Tate's construction over an arbitrary chosen coefficient field. -/
theorem tate_realization
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : Type v) [Field k] :
    IsGalois (fixedBase G (RationalField G k)) (RationalField G k) ∧
    ringChar (fixedBase G (RationalField G k)) = ringChar k ∧
    ringChar (RationalField G k) = ringChar k ∧
    ∃! e : G ≃ₜ* (RationalField G k ≃ₐ[fixedBase G (RationalField G k)] RationalField G k),
      e.toMulEquiv.toMonoidHom =
        MulSemiringAction.toAlgAut G (fixedBase G (RationalField G k)) (RationalField G k) ∧
      ∀ (g : G) (x : CosetPoint G),
        e g (indeterminate G k x) = indeterminate G k (g • x) := by
  let := rationalField_faithful (G := G) k
  have hOpen := rationalField_stabilizer_open (G := G) k
  have hChar := rationalField_characteristic (G := G) k
  refine ⟨isGalois_compact_fixedBase G (RationalField G k) hOpen,
    (Algebra.ringChar_eq (fixedBase G (RationalField G k)) (RationalField G k)).trans hChar,
    hChar, ?_⟩
  obtain ⟨e, he, hu⟩ := compactAction_topologicalIsomorphism G (RationalField G k) hOpen
  refine ⟨e, ⟨he, ?_⟩, fun e' he' => hu e' he'.1⟩
  intro g x
  have h := DFunLike.congr_fun he g
  have hx := congrArg (fun f : RationalField G k ≃ₐ[fixedBase G (RationalField G k)]
    RationalField G k => f (indeterminate G k x)) h
  exact hx.trans (rationalAction_indeterminate (G := G) k g x)

/-- Both zero and every prime characteristic can be specified in advance. -/
theorem tate_realization_in_characteristic :
    Specs.AdvancedFieldTheory.Realization.tate_realization_in_characteristic_type := by
  intro G _ _ _ _ _ _ c hc
  have construct (k : Type) [Field k] (hk : ringChar k = c) :
      ∃ (k : Type) (_ : Field k),
        ringChar k = c ∧
        IsGalois (fixedBase G (RationalField G k)) (RationalField G k) ∧
        ringChar (fixedBase G (RationalField G k)) = c ∧
        ringChar (RationalField G k) = c ∧
        ∃! e : G ≃ₜ* (RationalField G k ≃ₐ[fixedBase G (RationalField G k)] RationalField G k),
          e.toMulEquiv.toMonoidHom =
            MulSemiringAction.toAlgAut G (fixedBase G (RationalField G k)) (RationalField G k) ∧
          ∀ (g : G) (x : CosetPoint G),
            e g (indeterminate G k x) = indeterminate G k (g • x) := by
    refine ⟨k, inferInstance, hk, ?_⟩
    simpa only [hk] using tate_realization G k
  rcases hc with rfl | hp
  · exact construct ℚ (by exact ringChar.eq_zero)
  · let : Fact (Nat.Prime c) := ⟨hp⟩
    exact construct (ZMod c) (ZMod.ringChar_zmod_n c)

end AdvancedFieldTheory.Realization
