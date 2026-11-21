import MathGenome.Internal.Specs.D07.Ch15.RadicalDefinition

/-! Radical steps, finite radical towers, and radical elements in a specified
algebraic overfield, with the source's zero-length and repeated-step conventions.
All embeddings are fixed by `Algebra K Ω` and intermediate-field inclusions.
-/

universe u v

namespace D07.Ch15.RadicalDefinition

open Specs.D07.Ch15.RadicalDefinition

/-- A positive power of one generator belongs to the preceding field. -/
def IsRadicalStep (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (E F : IntermediateField K Ω) : Prop :=
  ∃ (a : Ω) (n : ℕ), 0 < n ∧ a ^ n ∈ E ∧
    F = IntermediateField.adjoin K ((E : Set Ω) ∪ {a})

/-- A tower with r radical adjunctions, starting at the embedded base field. -/
def IsRadicalTower (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (r : ℕ)
    (T : Fin (r + 1) → IntermediateField K Ω) : Prop :=
  T 0 = ⊥ ∧ ∀ i : Fin r, IsRadicalStep K Ω (T i.castSucc) (T i.succ)

/-- E is the final field of a finite radical tower in Ω. -/
def IsRadicalExtension (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (E : IntermediateField K Ω) : Prop :=
  ∃ (r : ℕ) (T : Fin (r + 1) → IntermediateField K Ω),
    IsRadicalTower K Ω r T ∧ T (Fin.last r) = E

/-- An element is solvable by radicals if a finite radical tower contains it. -/
def SolvableByRadicals (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (x : Ω) : Prop :=
  ∃ E : IntermediateField K Ω, IsRadicalExtension K Ω E ∧ x ∈ E

theorem radical_step_iff_simple_adjoin : StepIffSimpleAdjoin.{u, v} := by
  intro K Ω _ _ _ _ E F
  simp only [radicalStepValue, IntermediateField.restrictScalars_adjoin]

theorem radical_step_inclusion : StepInclusion.{u, v} := by
  intro K Ω _ _ _ _ E F h
  obtain ⟨a, n, hn, hp, rfl⟩ := h
  intro x hx
  exact IntermediateField.subset_adjoin K _ (Or.inl hx)

theorem radical_tower_monotone : TowerMonotone.{u, v} := by
  intro K Ω _ _ _ _ r T h
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  exact radical_step_inclusion K Ω _ _ (h.2 i)

theorem repeated_step : RepeatedStep.{u, v} := by
  intro K Ω _ _ _ _ E a ha
  have hp : a ^ (1 : ℕ) ∈ E := by simpa only [pow_one] using ha
  have he : E = IntermediateField.adjoin K ((E : Set Ω) ∪ {a}) := by
    apply le_antisymm
    · intro x hx
      exact IntermediateField.subset_adjoin K _ (Or.inl hx)
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro x (hx | hx)
      · exact hx
      · exact (Set.mem_singleton_iff.mp hx) ▸ ha
  exact ⟨hp, he, a, 1, Nat.zero_lt_one, hp, he⟩

theorem constant_base_tower : ConstantBaseTower.{u, v} := by
  intro K Ω _ _ _ _ r
  refine ⟨rfl, ?_⟩
  intro i
  exact (repeated_step K Ω ⊥ 0 (zero_mem _)).2.2

theorem base_radical_extension : BaseRadicalExtension.{u, v} := by
  intro K Ω _ _ _ _
  exact ⟨0, fun _ => ⊥, constant_base_tower K Ω 0, rfl⟩

theorem base_solvable : BaseSolvable.{u, v} := by
  intro K Ω _ _ _ _ a
  exact ⟨⊥, base_radical_extension K Ω, IntermediateField.algebraMap_mem _ a⟩

theorem solvable_iff_tower : SolvableIffTower.{u, v} := by
  intro K Ω _ _ _ _ x
  constructor
  · rintro ⟨E, ⟨r, T, hT, hE⟩, hx⟩
    exact ⟨r, T, hT, Fin.last r, hE.symm ▸ hx⟩
  · rintro ⟨r, T, hT, i, hx⟩
    refine ⟨T (Fin.last r), ⟨r, T, hT, rfl⟩, ?_⟩
    exact radical_tower_monotone K Ω r T hT (Fin.le_last i) hx

end D07.Ch15.RadicalDefinition
