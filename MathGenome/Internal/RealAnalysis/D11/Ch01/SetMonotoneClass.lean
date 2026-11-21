import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetMonotoneClass
import MathGenome.Internal.RealAnalysis.D11.Ch01.SetSystems
import Mathlib.Data.Finset.Range

/-! # The set monotone-class theorem

The shared definitions are in the independent Specs. We first establish the
minimality and closure properties of their intersection construction. Complement
and intersection tests then show that the generated monotone class of an algebra
is an algebra. Increasing finite partial unions give countable-union closure.
-/

open Set
open scoped MeasureTheory

universe u

namespace D11.Ch01.SetMonotoneClass

abbrev IsMonotoneClass {α : Type u} (M : Set (Set α)) : Prop :=
  Specs.D11.Ch01.SetMonotoneClass.IsMonotoneClass M

abbrev monotoneClosure {α : Type u} (A : Set (Set α)) : Set (Set α) :=
  Specs.D11.Ch01.SetMonotoneClass.monotoneClosure A

theorem closure_contains {α : Type u} (A : Set (Set α)) : A ⊆ monotoneClosure A := by
  intro s hs M _ hAM
  exact hAM hs

theorem closure_minimal {α : Type u} {A M : Set (Set α)}
    (hM : IsMonotoneClass M) (hAM : A ⊆ M) : monotoneClosure A ⊆ M := by
  intro s hs
  exact hs M hM hAM

theorem closure_isMonotoneClass {α : Type u} (A : Set (Set α)) :
    IsMonotoneClass (monotoneClosure A) := by
  constructor
  · intro E hE hm M hM hAM
    exact hM.1 E hE (fun n => hm n M hM hAM)
  · intro E hE hm M hM hAM
    exact hM.2 E hE (fun n => hm n M hM hAM)

theorem measurableSets_isMonotoneClass {α : Type u} (m : MeasurableSpace α) :
    IsMonotoneClass {s : Set α | MeasurableSet[m] s} := by
  exact ⟨fun _ _ hE => MeasurableSet.iUnion hE, fun _ _ hE => MeasurableSet.iInter hE⟩

/-- Taking the inverse image of a monotone class under complementation preserves
both monotone closure properties, exchanging their roles. -/
theorem IsMonotoneClass.compl_preimage {α : Type u} {M : Set (Set α)}
    (hM : IsMonotoneClass M) : IsMonotoneClass {s : Set α | sᶜ ∈ M} := by
  constructor
  · intro E hE hm
    change (⋃ n, E n)ᶜ ∈ M
    rw [compl_iUnion]
    exact hM.2 _ (fun i j hij => compl_subset_compl.mpr (hE hij)) hm
  · intro E hE hm
    change (⋂ n, E n)ᶜ ∈ M
    rw [compl_iInter]
    exact hM.1 _ (fun i j hij => compl_subset_compl.mpr (hE hij)) hm

/-- Intersection with a fixed set commutes with both sequence operations. The
intersection statement uses the nonempty index type ℕ, not a nonempty space. -/
theorem IsMonotoneClass.inter_preimage {α : Type u} {M : Set (Set α)}
    (hM : IsMonotoneClass M) (s : Set α) :
    IsMonotoneClass {t : Set α | s ∩ t ∈ M} := by
  constructor
  · intro E hE hm
    change (s ∩ ⋃ n, E n) ∈ M
    rw [inter_iUnion]
    exact hM.1 _ (fun i j hij => inter_subset_inter_right s (hE hij)) hm
  · intro E hE hm
    change (s ∩ ⋂ n, E n) ∈ M
    rw [inter_iInter]
    exact hM.2 _ (fun i j hij => inter_subset_inter_right s (hE hij)) hm

theorem closure_compl {α : Type u} {A : Set (Set α)}
    (hA : MeasureTheory.IsSetAlgebra A) {s : Set α} (hs : s ∈ monotoneClosure A) :
    sᶜ ∈ monotoneClosure A := by
  exact closure_minimal (closure_isMonotoneClass A).compl_preimage
    (fun _ ht => closure_contains A (hA.compl_mem ht)) hs

theorem closure_inter {α : Type u} {A : Set (Set α)}
    (hA : MeasureTheory.IsSetAlgebra A) {s t : Set α}
    (hs : s ∈ monotoneClosure A) (ht : t ∈ monotoneClosure A) :
    s ∩ t ∈ monotoneClosure A := by
  have hbase (a : Set α) (ha : a ∈ A) {b : Set α} (hb : b ∈ monotoneClosure A) :
      a ∩ b ∈ monotoneClosure A :=
    closure_minimal ((closure_isMonotoneClass A).inter_preimage a)
      (fun _ hc => closure_contains A (hA.inter_mem ha hc)) hb
  apply closure_minimal ((closure_isMonotoneClass A).inter_preimage s) ?_ ht
  intro a ha
  change s ∩ a ∈ monotoneClosure A
  rw [inter_comm]
  exact hbase a ha hs

theorem closure_isSetAlgebra {α : Type u} {A : Set (Set α)}
    (hA : MeasureTheory.IsSetAlgebra A) : MeasureTheory.IsSetAlgebra (monotoneClosure A) where
  empty_mem := closure_contains A hA.empty_mem
  compl_mem := fun _ hs => closure_compl hA hs
  union_mem := by
    intro s t hs ht
    rw [union_eq_compl_compl_inter_compl]
    exact closure_compl hA (closure_inter hA (closure_compl hA hs) (closure_compl hA ht))

/-- An algebra with increasing-union closure is closed under arbitrary countable
unions: take the increasing sequence of unions over `Finset.range n`. -/
theorem IsMonotoneClass.countable_union {α : Type u} {M : Set (Set α)}
    (hM : IsMonotoneClass M) (hAlg : MeasureTheory.IsSetAlgebra M)
    (E : ℕ → Set α) (hE : ∀ n, E n ∈ M) : (⋃ n, E n) ∈ M := by
  let F : ℕ → Set α := fun n => ⋃ i ∈ Finset.range n, E i
  have hF : ∀ n, F n ∈ M := fun n => hAlg.biUnion_mem (Finset.range n) (fun i _ => hE i)
  have hmono : Monotone F := by
    intro i j hij x hx
    rcases mem_iUnion.mp hx with ⟨k, hk⟩
    rcases mem_iUnion.mp hk with ⟨hk, hx⟩
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.range_mono hij hk, hx⟩⟩
  have heq : (⋃ n, F n) = ⋃ n, E n := by
    ext x
    simp only [F, mem_iUnion]
    constructor
    · rintro ⟨n, k, _, hx⟩
      exact ⟨k, hx⟩
    · rintro ⟨k, hx⟩
      exact ⟨k + 1, k, Finset.mem_range.mpr (Nat.lt_succ_self k), hx⟩
  rw [← heq]
  exact hM.1 F hmono hF

theorem monotoneClosure_eq_generated {α : Type u} {A : Set (Set α)}
    (hA : MeasureTheory.IsSetAlgebra A) :
    monotoneClosure A = {s : Set α | MeasurableSet[MeasurableSpace.generateFrom A] s} := by
  apply Subset.antisymm
  · exact closure_minimal (measurableSets_isMonotoneClass _) (SetSystems.generated_contains A)
  · have hM := closure_isMonotoneClass A
    have hAlg := closure_isSetAlgebra hA
    obtain ⟨m, hm⟩ := (SetSystems.sigmaAlgebra_iff (monotoneClosure A)).mpr
      ⟨hAlg, hM.countable_union hAlg⟩
    have hle : MeasurableSpace.generateFrom A ≤ m :=
      (SetSystems.generated_le_iff A m).mpr (fun s hs => (hm s).mpr (closure_contains A hs))
    intro s hs
    exact (hm s).mp (hle s hs)

theorem monotone_class {α : Type u} {A M : Set (Set α)}
    (hA : MeasureTheory.IsSetAlgebra A) (hM : IsMonotoneClass M) (hAM : A ⊆ M)
    {s : Set α} (hs : MeasurableSet[MeasurableSpace.generateFrom A] s) : s ∈ M := by
  apply closure_minimal hM hAM
  rw [monotoneClosure_eq_generated hA]
  exact hs

end D11.Ch01.SetMonotoneClass
