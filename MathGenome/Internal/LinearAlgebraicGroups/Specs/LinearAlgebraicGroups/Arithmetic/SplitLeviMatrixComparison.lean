import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.SplitLeviMatrixComparison

open GeometricRadicals (IsSemisimple IsSplitReductive)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Pinning (SplitBorelPair AttachedDatum)
open GeneralLinearStructure (SpecialMatrixPoints)

/-- Cartan entries in the natural numbering of the type A chain. -/
def chainCartan {r : ℕ} (i j : Fin r) : ℤ :=
  if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

/-- The isolated A₁ vertex and the A₅ chain, with both cross blocks zero. -/
def productCartan : (Fin 1 ⊕ Fin 5) → (Fin 1 ⊕ Fin 5) → ℤ
  | .inl i, .inl j => chainCartan i j
  | .inr i, .inr j => chainCartan i j
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

/-- The split reference with a simply connected absolute A₅ marking is SL₆. -/
def SingleChain : Prop :=
  ∀ {F : Type u} [Field F] (R : AffineAlgebraicGroup F), IsSplitReductive R →
    ∀ (P : SplitBorelPair (SeparableClosure F)),
      IsSemisimple P.G → GeometricallySimplyConnected P.G →
      (P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj R.val) →
      ∀ (D : AttachedDatum P) (e : Fin 5 ≃ D.toBased.base.support),
        (∀ i j, D.toBased.datum.pairing (e i) (e j) = chainCartan i j) →
        ∃ Q₂ : AffineAlgebraicGroup F, IsSplitReductive Q₂ ∧
          Nonempty (SpecialMatrixPoints Q₂ 6) ∧ Nonempty (R.val ≅ Q₂.val)

/-- The split reference with simply connected absolute A₁ and A₅ blocks is the
scheme product of SL₂ and SL₆ over the ground field. -/
def TwoBlocks : Prop :=
  ∀ {F : Type u} [Field F] (R : AffineAlgebraicGroup F), IsSplitReductive R →
    ∀ (P : SplitBorelPair (SeparableClosure F)),
      IsSemisimple P.G → GeometricallySimplyConnected P.G →
      (P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj R.val) →
      ∀ (D : AttachedDatum P) (e : (Fin 1 ⊕ Fin 5) ≃ D.toBased.base.support),
        (∀ i j, D.toBased.datum.pairing (e i) (e j) = productCartan i j) →
        ∃ Q₁ Q₂ : AffineAlgebraicGroup F,
          IsSplitReductive Q₁ ∧ IsSplitReductive Q₂ ∧
          Nonempty (SpecialMatrixPoints Q₁ 2) ∧ Nonempty (SpecialMatrixPoints Q₂ 6) ∧
          Nonempty (R.val ≅ Limits.prod Q₁.val Q₂.val)

end LinearAlgebraicGroups.Specs.SplitLeviMatrixComparison
