import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.Finite
import MathGenome.Internal.ExtremalOptimization.P205.Ramsey.Infinite
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.Pigeonhole
import Lean.Elab.Tactic.Omega

universe u v

namespace P205.Ramsey

private def TotalHomogeneous {X C : Type*} (c : Finset X → C) (k : ℕ)
    (t : Finset X) : Prop :=
  ∃ a, ∀ s ⊆ t, s.card = k → c s = a

private theorem total_homogeneous_map {X : Type u} {Y : Type v} {C : Type*}
    (c : Finset Y → C) (k : ℕ) (f : X ↪ Y) (t : Finset X)
    (h : TotalHomogeneous (fun s => c (s.map f)) k t) :
    TotalHomogeneous c k (t.map f) := by
  classical
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  intro s hs hk
  obtain ⟨q, hq, rfl⟩ := Finset.subset_map_iff.mp hs
  exact ha q hq (by simpa using hk)

private theorem isOpen_total_homogeneous {C : Type*} [TopologicalSpace C]
    [DiscreteTopology C] (k : ℕ) (t : Finset ℕ) :
    IsOpen {c : Finset ℕ → C | TotalHomogeneous c k t} := by
  classical
  have heq : {c : Finset ℕ → C | TotalHomogeneous c k t} =
      ⋃ a : C, ⋂ s ∈ t.powersetCard k, {c | c s = a} := by
    ext c
    simp [TotalHomogeneous, Finset.mem_powersetCard]
  rw [heq]
  exact isOpen_iUnion fun a => isOpen_biInter_finset fun s _ => by
    exact (show Continuous (fun c : Finset ℕ → C => c s) from continuous_apply s).isOpen_preimage
      {a} (isOpen_discrete _)

/-- Compactness of the product of finite discrete color sets turns infinite
Ramsey into a uniform finite bound. -/
private theorem finite_bound_total (k r m : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    ∃ N : ℕ, m ≤ N ∧ ∀ c : Finset ℕ → Fin r,
      ∃ t ⊆ Finset.range N, t.card = m ∧ TotalHomogeneous c k t := by
  classical
  let : TopologicalSpace (Fin r) := ⊥
  let : DiscreteTopology (Fin r) := ⟨rfl⟩
  let U (n : ℕ) : Set (Finset ℕ → Fin r) :=
    {c | ∃ t ⊆ Finset.range n, t.card = m ∧ TotalHomogeneous c k t}
  have hopen (n : ℕ) : IsOpen (U n) := by
    have heq : U n = ⋃ (t : Finset ℕ) (_ : t ⊆ Finset.range n) (_ : t.card = m),
        {c : Finset ℕ → Fin r | TotalHomogeneous c k t} := by
      ext c
      simp [U, and_left_comm]
    rw [heq]
    exact isOpen_iUnion fun t => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
      isOpen_total_homogeneous k t
  have hcover : (Set.univ : Set (Finset ℕ → Fin r)) ⊆ ⋃ n, U n := by
    intro c _
    obtain ⟨H, hH, a, ha⟩ := infinite_ramsey_nat k r hk hr (fun s => c s.val)
    obtain ⟨t, ht, htm⟩ := hH.exists_subset_card_eq m
    refine Set.mem_iUnion.mpr ⟨t.sup id + 1, t, ?_, htm, a, ?_⟩
    · intro x hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
    · intro s hs hsk
      exact ha ⟨s, hsk⟩ (fun x hx => ht (hs hx))
  have hdir : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · rintro c ⟨t, ht, htm, htc⟩
      exact ⟨t, ht.trans (Finset.range_mono (le_max_left _ _)), htm, htc⟩
    · rintro c ⟨t, ht, htm, htc⟩
      exact ⟨t, ht.trans (Finset.range_mono (le_max_right _ _)), htm, htc⟩
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover U hopen hcover hdir
  refine ⟨max m n, le_max_left _ _, ?_⟩
  intro c
  obtain ⟨t, ht, htm, htc⟩ := hn (Set.mem_univ c)
  exact ⟨t, ht.trans (Finset.range_mono (le_max_right _ _)), htm, htc⟩

/-- The finite multicolor Ramsey theorem on arbitrary finite ground sets. -/
theorem finite_ramsey : Specs.FiniteRamsey.{u} := by
  classical
  intro k r m hk hr _
  obtain ⟨N, hmN, hN⟩ := finite_bound_total k r m hk hr
  refine ⟨N, hmN, ?_⟩
  intro X S hS c
  let R := ↥(Finset.range N)
  let e : R ≃ S := Finset.equivOfCardEq (by simpa using hS.symm)
  let f : R ↪ X := e.toEmbedding.trans (Function.Embedding.subtype _)
  let j : Finset R ↪ Finset ℕ :=
    ⟨fun q => q.map (Function.Embedding.subtype _), Finset.map_injective _⟩
  let total : Finset X → Fin r := fun q =>
    if hq : q.card = k then c ⟨q, hq⟩ else ⟨0, hr⟩
  let g : Finset R → Fin r := fun q => total (q.map f)
  let d : Finset ℕ → Fin r := Function.extend j g (fun _ => ⟨0, hr⟩)
  obtain ⟨t, ht, htm, a, ha⟩ := hN d
  let q : Finset R := t.subtype (· ∈ Finset.range N)
  have hqt : q.map (Function.Embedding.subtype _) = t :=
    Finset.subtype_map_of_mem ht
  have hqm : q.card = m := by
    rw [← hqt, Finset.card_map] at htm
    exact htm
  have hq : TotalHomogeneous g k q := by
    refine ⟨a, ?_⟩
    intro s hs hsk
    have hst : j s ⊆ t := by
      rw [← hqt]
      exact Finset.map_subset_map.mpr hs
    have hcolor := ha (j s) hst (by simpa [j] using hsk)
    simpa only [d, j.injective.extend_apply] using hcolor
  obtain ⟨b, hb⟩ := total_homogeneous_map total k f q hq
  refine ⟨q.map f, ?_, by simpa using hqm, b, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e y).property
  · intro s hs
    have hcolor := hb s.val hs s.property
    simpa [total, s.property] using hcolor

/-- Below the arity, the whole ground set is vacuously homogeneous. -/
theorem finite_ramsey_of_lt : Specs.FiniteRamseyOfLt.{u} := by
  intro k r m _ hr _ hmk X S hS c
  exact ⟨S, Finset.Subset.refl _, hS,
    homogeneous_of_card_lt X k r hr c S (by omega)⟩

/-- With one color, the whole ground set is homogeneous. -/
theorem finite_ramsey_one_color : Specs.FiniteRamseyOneColor.{u} := by
  intro k m _ _ X S hS c
  exact ⟨S, Finset.Subset.refl _, hS, 0, fun _ _ => Subsingleton.elim _ _⟩

/-- The singleton case has the pigeonhole bound `r * (m - 1) + 1`. -/
theorem finite_ramsey_singleton : Specs.FiniteRamseySingleton.{u} := by
  classical
  intro r m hr hm
  refine ⟨?_, ?_⟩
  · have := Nat.mul_le_mul_right (m - 1) hr
    omega
  · intro X S hS c
    let f : X → Fin r := fun x => c ⟨{x}, Finset.card_singleton x⟩
    obtain ⟨a, _, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := S) (t := Finset.univ) (f := f) (n := m - 1)
      (fun _ _ => Finset.mem_univ _) (by simp [hS])
    obtain ⟨t, ht, htm⟩ := Finset.exists_subset_card_eq (show m ≤ (S.filter (f · = a)).card by omega)
    refine ⟨t, ht.trans (Finset.filter_subset _ _), htm, a, ?_⟩
    intro s hs
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp s.property
    have hxt : x ∈ t := hs (by simp [hx])
    have hfx := (Finset.mem_filter.mp (ht hxt)).2
    have heq : s = ⟨{x}, Finset.card_singleton x⟩ := Subtype.ext hx
    simpa only [heq] using hfx

end P205.Ramsey
