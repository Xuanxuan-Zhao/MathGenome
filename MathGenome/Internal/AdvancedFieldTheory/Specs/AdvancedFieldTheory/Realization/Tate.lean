import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Realization.RationalFunctionAction
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.CompactActions.FixedFieldTheorem

/-! Independent specification of Tate's realization theorem, FT-C12,
notes/003/advanced-field-theory.tex:1013–1044. The extension is the fraction
field on the prescribed coset variables over any chosen coefficient field.
Its base is the literal fixed subfield, and automorphisms carry the Krull topology.
-/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory.Realization

open _root_.AdvancedFieldTheory.Realization
open Specs.AdvancedFieldTheory.CompactActions

/-- The construction works over every chosen field, preserves its characteristic
in both fields, and identifies the topological isomorphism with variable permutation. -/
def tate_realization_type : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (k : Type v) [Field k],
    IsGalois (fixedBase G (RationalField G k)) (RationalField G k) ∧
    ringChar (fixedBase G (RationalField G k)) = ringChar k ∧
    ringChar (RationalField G k) = ringChar k ∧
    ∃! e : G ≃ₜ* (RationalField G k ≃ₐ[fixedBase G (RationalField G k)] RationalField G k),
      e.toMulEquiv.toMonoidHom =
        MulSemiringAction.toAlgAut G (fixedBase G (RationalField G k)) (RationalField G k) ∧
      ∀ (g : G) (x : CosetPoint G),
        e g (indeterminate G k x) = indeterminate G k (g • x)

/-- Every realizable specified characteristic is attained by this same construction.
The coefficient field is exhibited; K and E remain the prescribed fixed and rational fields. -/
def tate_realization_in_characteristic_type : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (c : ℕ), c = 0 ∨ Nat.Prime c →
    ∃ (k : Type) (_ : Field k),
      ringChar k = c ∧
      IsGalois (fixedBase G (RationalField G k)) (RationalField G k) ∧
      ringChar (fixedBase G (RationalField G k)) = c ∧
      ringChar (RationalField G k) = c ∧
      ∃! e : G ≃ₜ* (RationalField G k ≃ₐ[fixedBase G (RationalField G k)] RationalField G k),
        e.toMulEquiv.toMonoidHom =
          MulSemiringAction.toAlgAut G (fixedBase G (RationalField G k)) (RationalField G k) ∧
        ∀ (g : G) (x : CosetPoint G),
          e g (indeterminate G k x) = indeterminate G k (g • x)

end Specs.AdvancedFieldTheory.Realization
