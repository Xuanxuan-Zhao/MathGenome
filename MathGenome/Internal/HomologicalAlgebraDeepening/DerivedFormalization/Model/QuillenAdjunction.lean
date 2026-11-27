import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

namespace DerivedFormalization.Model

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable {L : C ⥤ D} {U : D ⥤ C} in
private theorem map_llp_iff_map_rlp (adj : L ⊣ U) (P : MorphismProperty C)
    (Q : MorphismProperty D) :
    P ≤ Q.llp.inverseImage L ↔ Q ≤ P.rlp.inverseImage U := by
  constructor
  · intro h X Y p hp A B i hi
    exact (adj.hasLiftingProperty_iff i p).mp (h i hi p hp)
  · intro h A B i hi X Y p hp
    exact (adj.hasLiftingProperty_iff i p).mpr (h p hp i hi)

variable [ModelCategory C] [ModelCategory D] {L : C ⥤ D} {U : D ⥤ C}

/-- An adjunction is Quillen if its left adjoint preserves cofibrations and trivial cofibrations. -/
def IsQuillen (_adj : L ⊣ U) : Prop :=
  cofibrations C ≤ (cofibrations D).inverseImage L ∧
    trivialCofibrations C ≤ (trivialCofibrations D).inverseImage L

/-- An adjunction is Quillen exactly when its right adjoint preserves fibrations and trivial
fibrations. -/
theorem isQuillen_iff_right (adj : L ⊣ U) :
    IsQuillen adj ↔ fibrations D ≤ (fibrations C).inverseImage U ∧
      trivialFibrations D ≤ (trivialFibrations C).inverseImage U := by
  obtain ⟨_, hTrivialFib, _, hFib⟩ := liftingClasses C
  obtain ⟨hCof, _, hTrivialCof, _⟩ := liftingClasses D
  have h₁ := map_llp_iff_map_rlp adj (cofibrations C) (trivialFibrations D)
  rw [hCof, hTrivialFib] at h₁
  have h₂ := map_llp_iff_map_rlp adj (trivialCofibrations C) (fibrations D)
  rw [hTrivialCof, hFib] at h₂
  exact (h₁.and h₂).trans and_comm

/-- The left adjoint of a Quillen adjunction preserves cofibrant objects. -/
theorem IsQuillen.isCofibrant_obj {adj : L ⊣ U} (h : IsQuillen adj)
    {X : C} (hX : IsCofibrant X) : IsCofibrant (L.obj X) := by
  let _ := adj.isLeftAdjoint
  rw [isCofibrant_iff_of_isInitial (L.map (initial.to X)) (initialIsInitial.isInitialObj L),
    cofibration_iff]
  exact h.1 _ ((isCofibrant_iff X).mp hX)

/-- The right adjoint of a Quillen adjunction preserves fibrant objects. -/
theorem IsQuillen.isFibrant_obj {adj : L ⊣ U} (h : IsQuillen adj)
    {Y : D} (hY : IsFibrant Y) : IsFibrant (U.obj Y) := by
  let _ := adj.isRightAdjoint
  rw [isFibrant_iff_of_isTerminal (U.map (terminal.from Y)) (terminalIsTerminal.isTerminalObj U),
    fibration_iff]
  exact ((isQuillen_iff_right adj).mp h).1 _ ((isFibrant_iff Y).mp hY)

end DerivedFormalization.Model
