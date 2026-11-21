import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Canonical separation conventions for paper.tex, d10:07:axioms. The exact
Mathlib predicates are reused for T0, T1, T2, regularity, normality and G_delta.
The paper's T3, T4 and complete regularity are connected to Mathlib by the
equivalences below. No nonemptiness or T1 condition is added to regularity,
normality or complete regularity.
-/

open Set
open scoped Topology
universe u

namespace D10Topology.Ch07

abbrev T0 (X : Type u) [TopologicalSpace X] : Prop := T0Space X
abbrev T1 (X : Type u) [TopologicalSpace X] : Prop := T1Space X
abbrev T2 (X : Type u) [TopologicalSpace X] : Prop := T2Space X
abbrev Regular (X : Type u) [TopologicalSpace X] : Prop := RegularSpace X
abbrev Normal (X : Type u) [TopologicalSpace X] : Prop := NormalSpace X

def T3 (X : Type u) [TopologicalSpace X] : Prop := Regular X ∧ T1 X
def T4 (X : Type u) [TopologicalSpace X] : Prop := Normal X ∧ T1 X

/-- The separating function is 1 at x and 0 on the prescribed closed set. -/
def CompletelyRegular (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (F : Set X), IsClosed F → ∀ x : X, x ∉ F →
    ∃ f : X → unitInterval, Continuous f ∧ f x = 1 ∧ ∀ y ∈ F, f y = 0

def Tychonoff (X : Type u) [TopologicalSpace X] : Prop := CompletelyRegular X ∧ T2 X

abbrev GDelta {X : Type u} [TopologicalSpace X] (A : Set X) : Prop := IsGδ A

variable (X : Type u) [TopologicalSpace X]

theorem t0_iff_open_distinguishes : T0 X ↔
    ∀ x y : X, x ≠ y → ∃ U : Set X, IsOpen U ∧
      ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U)) := by
  simpa only [T0, Pairwise, Xor, and_comm] using
    t0Space_iff_exists_isOpen_xor_mem X

theorem t1_iff_closed_singletons : T1 X ↔ ∀ x : X, IsClosed ({x} : Set X) :=
  ⟨fun h => h.t1, fun h => ⟨h⟩⟩

theorem t2_iff_disjoint_open : T2 X ↔
    ∀ x y : X, x ≠ y → ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V :=
  t2Space_iff X

theorem regular_iff_disjoint_open : Regular X ↔
    ∀ (F : Set X), IsClosed F → ∀ x : X, x ∉ F →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ F ⊆ V ∧ Disjoint U V := by
  constructor
  · intro h F hF x hx
    have hd := @RegularSpace.regular X _ h F x hF hx
    have hs : SeparatedNhds ({x} : Set X) F :=
      separatedNhds_iff_disjoint.mpr (by simpa only [nhdsSet_singleton] using hd.symm)
    simpa only [SeparatedNhds, singleton_subset_iff] using hs
  · intro h
    refine ⟨fun {F} {x} hF hx => ?_⟩
    have hs : SeparatedNhds ({x} : Set X) F := by
      simpa only [SeparatedNhds, singleton_subset_iff] using h F hF x hx
    simpa only [nhdsSet_singleton] using hs.disjoint_nhdsSet.symm

theorem normal_iff_disjoint_open : Normal X ↔
    ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V :=
  ⟨fun h => h.normal, fun h => ⟨h⟩⟩

theorem t3_iff_mathlib : T3 X ↔ T3Space X := by
  constructor
  · rintro ⟨hR, h1⟩
    let := hR
    let := h1
    infer_instance
  · intro h
    let := h
    exact ⟨inferInstance, inferInstance⟩

theorem t4_iff_mathlib : T4 X ↔ T4Space X := by
  constructor
  · rintro ⟨hN, h1⟩
    exact { toNormalSpace := hN, toT1Space := h1 }
  · intro h
    exact ⟨h.toNormalSpace, h.toT1Space⟩

/-- Compose with the unit interval symmetry to reverse the prescribed values. -/
theorem completelyRegular_iff_mathlib : CompletelyRegular X ↔ CompletelyRegularSpace X := by
  constructor
  · intro h
    refine ⟨fun x F hF hx => ?_⟩
    obtain ⟨f, hf, hfx, hfF⟩ := h F hF x hx
    refine ⟨unitInterval.symm ∘ f, unitInterval.continuous_symm.comp hf, ?_, ?_⟩
    · simp [Function.comp_apply, hfx]
    · intro y hy
      simp [Function.comp_apply, hfF y hy]
  · intro h F hF x hx
    obtain ⟨f, hf, hfx, hfF⟩ := h.completely_regular x F hF hx
    refine ⟨unitInterval.symm ∘ f, unitInterval.continuous_symm.comp hf, ?_, ?_⟩
    · simp [Function.comp_apply, hfx]
    · intro y hy
      simp [Function.comp_apply, hfF hy]

theorem tychonoff_iff_mathlib : Tychonoff X ↔ T35Space X := by
  constructor
  · rintro ⟨hC, h2⟩
    let := (completelyRegular_iff_mathlib X).mp hC
    let := h2
    exact { }
  · intro h
    let := h
    exact ⟨(completelyRegular_iff_mathlib X).mpr inferInstance, inferInstance⟩

variable {X}

theorem gdelta_iff_countable_open_intersection (A : Set X) : GDelta A ↔
    ∃ U : Set (Set X), U.Countable ∧ (∀ V ∈ U, IsOpen V) ∧ A = ⋂₀ U := by
  simp only [GDelta, IsGδ, and_left_comm]

theorem gdelta_iff_sequence_open_intersection (A : Set X) : GDelta A ↔
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ A = ⋂ n, U n :=
  isGδ_iff_eq_iInter_nat

variable (X)

theorem empty_separation_axioms [IsEmpty X] :
    T0 X ∧ T1 X ∧ T2 X ∧ Regular X ∧ Normal X ∧
      T3 X ∧ T4 X ∧ CompletelyRegular X ∧ Tychonoff X := by
  have hC : CompletelyRegular X := fun _ _ x => isEmptyElim x
  have hR : RegularSpace X := ⟨fun {s} {x} => isEmptyElim x⟩
  have hN : NormalSpace X := ⟨fun A B _ _ _ => by
    refine ⟨∅, ∅, isOpen_empty, isOpen_empty, ?_, ?_, by simp⟩ <;>
      intro x <;> exact isEmptyElim x⟩
  exact ⟨inferInstance, inferInstance, inferInstance, hR, hN,
    ⟨hR, inferInstance⟩, ⟨hN, inferInstance⟩, hC, ⟨hC, inferInstance⟩⟩

end D10Topology.Ch07
