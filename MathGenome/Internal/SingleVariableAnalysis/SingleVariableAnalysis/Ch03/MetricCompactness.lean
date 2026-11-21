import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.MetricCompactness

/-!
# Compactness in arbitrary metric spaces

General metric-space portion of K03.03.compact_interval, paper.tex:529–540.
We identify finite open subcovers and strictly indexed convergent subsequences
with the exact canonical compactness notions, then reuse Mathlib's metric
compactness equivalence. Mathlib's converse proves total boundedness and
completeness from sequential compactness; it assumes neither as a hypothesis.
We expose the source's finite-net and Lebesgue-number consequences separately,
and verify explicitly how they give a finite subcover, even in an empty space.
-/
namespace SingleVariableAnalysis

open scoped Topology
universe u v

/-- Finite subcovers express compactness on the whole metric space. -/
theorem metric_compact_iff_finite_subcover
    {X : Type u} [MetricSpace X] :
    IsCompact (Set.univ : Set X) ↔
      ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) →
        (∀ x, ∃ i, x ∈ U i) →
        ∃ t : Finset ι, ∀ x, ∃ i ∈ t, x ∈ U i := by
  constructor
  · intro hc ι U hU hcover
    obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hU
      (fun x _ => Set.mem_iUnion.mpr (hcover x))
    exact ⟨t, fun x => by
      simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)⟩
  · intro h
    apply isCompact_of_finite_subcover
    intro ι U hU hcover
    obtain ⟨t, ht⟩ := h ι U hU
      (fun x => Set.mem_iUnion.mp (hcover (Set.mem_univ x)))
    exact ⟨t, fun x _ => by
      simpa only [Set.mem_iUnion, exists_prop] using ht x⟩

/-- On univ the membership clauses in IsSeqCompact carry no extra condition. -/
private theorem isSeqCompact_univ_iff_subsequence
    {X : Type u} [MetricSpace X] :
    IsSeqCompact (Set.univ : Set X) ↔
      ∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x) := by
  constructor
  · intro h a
    obtain ⟨x, _, φ, hφ, hlim⟩ := h (fun n => Set.mem_univ (a n))
    exact ⟨x, φ, hφ, hlim⟩
  · intro h a _
    obtain ⟨x, φ, hφ, hlim⟩ := h a
    exact ⟨x, Set.mem_univ x, φ, hφ, hlim⟩

/-- Compactness is equivalent to the full subsequence property. -/
theorem metric_compact_iff_sequentially_compact
    {X : Type u} [MetricSpace X] :
    IsCompact (Set.univ : Set X) ↔
      ∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x) :=
  isCompact_iff_isSeqCompact.trans isSeqCompact_univ_iff_subsequence

/-- The ε-net is internal: all its centers are points of X. -/
theorem metric_sequentially_compact_finite_net
    {X : Type u} [MetricSpace X]
    (h : ∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset X, ∀ x : X, ∃ y ∈ t, dist x y < ε := by
  classical
  have hs : IsSeqCompact (Set.univ : Set X) :=
    isSeqCompact_univ_iff_subsequence.mpr h
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hs.totallyBounded ε hε
  refine ⟨ht.toFinset, ?_⟩
  intro x
  have hx := hcover (Set.mem_univ x)
  simpa only [Set.mem_iUnion, Metric.mem_ball, Set.Finite.mem_toFinset, exists_prop] using hx

/-- A Lebesgue radius for any open cover; the index type may be empty. -/
theorem metric_sequentially_compact_lebesgue_number
    {X : Type u} [MetricSpace X]
    (h : ∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x))
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∃ i, Metric.ball x δ ⊆ U i := by
  have hc := metric_compact_iff_sequentially_compact.mpr h
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hc hU
    (fun x _ => Set.mem_iUnion.mpr (hcover x))
  exact ⟨δ, hδ, fun x => hball x (Set.mem_univ x)⟩

/-- Selecting a cover member for each center of a finite net gives a subcover.
The choice is indexed by points of X, so it needs no inhabitant of the
cover index type when the space is empty. -/
theorem metric_finite_subcover_of_net_lebesgue
    {X : Type u} [MetricSpace X]
    (hnet : ∀ ε : ℝ, 0 < ε → ∃ t : Finset X,
      ∀ x : X, ∃ y ∈ t, dist x y < ε)
    {ι : Type v} (U : ι → Set X)
    (hleb : ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∃ i, Metric.ball x δ ⊆ U i) :
    ∃ t : Finset ι, ∀ x : X, ∃ i ∈ t, x ∈ U i := by
  classical
  obtain ⟨δ, hδ, hball⟩ := hleb
  obtain ⟨centers, hcenters⟩ := hnet δ hδ
  choose i hi using hball
  refine ⟨centers.image i, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := hcenters x
  exact ⟨i y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hi y hxy⟩

/-- Empty spaces satisfy both sides, without choosing a point. -/
theorem metric_empty_compactness
    {X : Type u} [MetricSpace X] [IsEmpty X] :
    IsCompact (Set.univ : Set X) ∧
      (∀ a : ℕ → X, ∃ x : X, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x)) := by
  refine ⟨?_, fun a => isEmptyElim (a 0)⟩
  have he : (Set.univ : Set X) = ∅ := by
    ext x
    exact isEmptyElim x
  rw [he]
  exact isCompact_empty

end SingleVariableAnalysis
