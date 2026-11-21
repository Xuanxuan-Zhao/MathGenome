import MathGenome.Internal.RealAnalysis.D11.Ch23.ElementaryMonotoneProperties
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.UndergraphContent

/-! The under-graph semiring and its finite, countably additive content.
One-dimensional Lebesgue measure is used only for individual vertical sections;
no representing measure for L is assumed. -/

noncomputable section
universe u
open Set MeasureTheory Function
open scoped ENNReal BigOperators

namespace D11.Ch23

abbrev undergraph {X : Type u} (f g : X → ℝ) : Set (X × ℝ) := Specs.Undergraph f g
abbrev undergraphFamily {X : Type u} (V : Submodule ℝ (X → ℝ)) := Specs.UndergraphFamily V
abbrev undergraphLength {X : Type u} (s : Set (X × ℝ)) : X → ℝ := Specs.UndergraphLength s
abbrev undergraphContent {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) (s : Set (X × ℝ)) : ℝ≥0∞ := Specs.UndergraphContent V L s

theorem undergraph_normalize : Specs.UndergraphNormalize := by
  intro X f g
  ext p
  change (min (f p.1) (g p.1) ≤ p.2 ∧ p.2 < g p.1) ↔ _
  constructor
  · rintro ⟨h, ht⟩
    rcases min_le_iff.mp h with hf | hg
    · exact ⟨hf, ht⟩
    · exact False.elim (not_le_of_gt ht hg)
  · intro h
    exact ⟨(min_le_left _ _).trans h.1, h.2⟩

theorem undergraph_length_formula : Specs.UndergraphLengthFormula := by
  intro X f g
  funext x
  change (volume (Ico (f x) (g x))).toReal = _
  rw [Real.volume_Ico, ENNReal.toReal_ofReal' ]
  by_cases h : f x ≤ g x
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h), sub_self, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

theorem undergraph_representation_independent : Specs.UndergraphRepresentationIndependent := by
  intro X f g f' g' h
  rw [← undergraph_length_formula f g, ← undergraph_length_formula f' g', h]

theorem undergraph_length_mem : Specs.UndergraphLengthMem := by
  intro X V hV s hs
  obtain ⟨f, g, rfl⟩ := hs
  rw [undergraph_length_formula]
  exact V.sub_mem g.property (IsVectorLattice.min_mem hV f.property g.property)


/-- Intersection is given by max of lower and min of upper endpoints. -/
theorem undergraph_inter {X : Type u} (f g c d : X → ℝ) :
    undergraph f g ∩ undergraph c d =
      undergraph (fun x => max (f x) (c x)) (fun x => min (g x) (d x)) := by
  ext p
  change ((f p.1 ≤ p.2 ∧ p.2 < g p.1) ∧ (c p.1 ≤ p.2 ∧ p.2 < d p.1)) ↔ _
  simp only [undergraph, Specs.Undergraph, mem_ofPred_eq, max_le_iff, lt_min_iff]
  constructor
  · rintro ⟨⟨hf, hg⟩, ⟨hc, hd⟩⟩
    exact ⟨⟨hf, hc⟩, hg, hd⟩
  · rintro ⟨⟨hf, hc⟩, hg, hd⟩
    exact ⟨⟨hf, hg⟩, hc, hd⟩

/-- A normalized subtrahend splits a difference into two disjoint intervals. -/
theorem undergraph_sdiff {X : Type u} (f g c d : X → ℝ) (_hcd : ∀ x, c x ≤ d x) :
    undergraph f g \ undergraph c d =
      undergraph f (fun x => min (g x) (c x)) ∪
        undergraph (fun x => max (f x) (d x)) g := by
  ext p
  change ((f p.1 ≤ p.2 ∧ p.2 < g p.1) ∧ ¬ (c p.1 ≤ p.2 ∧ p.2 < d p.1)) ↔ _
  simp only [mem_union, undergraph, Specs.Undergraph, mem_ofPred_eq, max_le_iff, lt_min_iff]
  constructor
  · rintro ⟨⟨hf, hg⟩, hn⟩
    by_cases hc : p.2 < c p.1
    · exact Or.inl ⟨hf, hg, hc⟩
    · exact Or.inr ⟨⟨hf, le_of_not_gt (fun hd => hn ⟨le_of_not_gt hc, hd⟩)⟩, hg⟩
  · rintro (⟨hf, hg, hc⟩ | ⟨⟨hf, hd⟩, hg⟩)
    · exact ⟨⟨hf, hg⟩, fun h => not_le_of_gt hc h.1⟩
    · exact ⟨⟨hf, hg⟩, fun h => not_le_of_gt h.2 hd⟩

private theorem undergraph_sdiff_disjoint {X : Type u} (f g c d : X → ℝ)
    (hcd : ∀ x, c x ≤ d x) :
    Disjoint (undergraph f (fun x => min (g x) (c x)))
      (undergraph (fun x => max (f x) (d x)) g) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact not_le_of_gt ((lt_min_iff.mp hp.2).2.trans_le (hcd p.1))
    ((max_le_iff.mp hq.1).2)

theorem undergraph_isSetSemiring : Specs.UndergraphSemiring := by
  classical
  intro X V hV
  constructor
  · refine ⟨0, 0, ?_⟩
    ext p
    simp [Specs.Undergraph]
  · rintro s ⟨f, g, rfl⟩ t ⟨c, d, rfl⟩
    refine ⟨⟨_, IsVectorLattice.max_mem hV f.property c.property⟩,
      ⟨_, IsVectorLattice.min_mem hV g.property d.property⟩, ?_⟩
    exact (undergraph_inter _ _ _ _).symm
  · rintro s ⟨f, g, rfl⟩ t ⟨c, d, rfl⟩
    let c' : V := ⟨fun x => min ((c : X → ℝ) x) ((d : X → ℝ) x),
      IsVectorLattice.min_mem hV c.property d.property⟩
    let b : V := ⟨fun x => min ((g : X → ℝ) x) ((c' : X → ℝ) x),
      IsVectorLattice.min_mem hV g.property c'.property⟩
    let a : V := ⟨fun x => max ((f : X → ℝ) x) ((d : X → ℝ) x),
      IsVectorLattice.max_mem hV f.property d.property⟩
    let A := undergraph (f : X → ℝ) (b : X → ℝ)
    let B := undergraph (a : X → ℝ) (g : X → ℝ)
    have hAB : Disjoint A B := undergraph_sdiff_disjoint _ _ _ _ (fun x => min_le_right _ _)
    refine ⟨{A, B}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨f, b, rfl⟩
      · exact ⟨a, g, rfl⟩
    · intro z hz w hw hne
      simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hz hw
      rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
      · exact False.elim (hne rfl)
      · exact hAB
      · exact hAB.symm
      · exact False.elim (hne rfl)
    · change undergraph _ _ \ undergraph _ _ = _
      calc
        _ = undergraph (f : X → ℝ) (g : X → ℝ) \ undergraph (c' : X → ℝ) (d : X → ℝ) :=
          congrArg (fun t => undergraph (f : X → ℝ) (g : X → ℝ) \ t)
            (undergraph_normalize (c : X → ℝ) (d : X → ℝ)).symm
        _ = A ∪ B := undergraph_sdiff _ _ _ _ (fun x => min_le_right _ _)
        _ = _ := by simp only [Finset.coe_pair, Set.sUnion_pair]


/-- The real section length is nonnegative even before restriction to the semiring. -/
theorem undergraph_length_nonneg {X : Type u} (s : Set (X × ℝ)) (x : X) :
    0 ≤ undergraphLength s x := ENNReal.toReal_nonneg

theorem undergraph_content_eq {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) (s : Set (X × ℝ)) (hs : undergraphLength s ∈ V) :
    undergraphContent V L s = ENNReal.ofReal (L ⟨undergraphLength s, hs⟩) := by
  classical
  exact dite_eq_left hs

theorem undergraph_content_of_le : Specs.UndergraphContentOfLe := by
  intro X V L f g hfg
  have heq : undergraphLength (undergraph (f : X → ℝ) (g : X → ℝ)) =
      ((g - f : V) : X → ℝ) := by
    funext x
    have h := congrFun (undergraph_length_formula (f : X → ℝ) (g : X → ℝ)) x
    simpa only [Submodule.coe_sub, Pi.sub_apply, min_eq_left (hfg x)] using h
  have hm : undergraphLength (undergraph (f : X → ℝ) (g : X → ℝ)) ∈ V :=
    heq.symm ▸ (g - f).property
  exact (undergraph_content_eq V L _ hm).trans
    (congrArg ENNReal.ofReal (congrArg L (Subtype.ext heq)))

theorem undergraph_content_empty : Specs.UndergraphContentEmpty := by
  intro X V L
  have heq : undergraphLength (∅ : Set (X × ℝ)) = 0 := by
    funext x
    simp [undergraphLength, Specs.UndergraphLength]
  have hm : undergraphLength (∅ : Set (X × ℝ)) ∈ V := heq.symm ▸ V.zero_mem
  have hzero : (⟨undergraphLength (∅ : Set (X × ℝ)), hm⟩ : V) = 0 := Subtype.ext heq
  calc
    _ = ENNReal.ofReal (L ⟨undergraphLength (∅ : Set (X × ℝ)), hm⟩) :=
      undergraph_content_eq V L _ hm
    _ = 0 := by rw [hzero, map_zero, ENNReal.ofReal_zero]

theorem undergraph_content_finite : Specs.UndergraphContentFinite := by
  classical
  intro X V L s
  simp only [Specs.UndergraphContent]
  split
  · exact ENNReal.ofReal_lt_top
  · exact ENNReal.zero_lt_top

theorem undergraph_integral_length_nonneg : Specs.UndergraphIntegralLengthNonneg := by
  intro X V L hL s hs
  exact IsElementaryIntegral.nonneg hL _ (undergraph_length_nonneg s)

/-- On an interval, the extended section length agrees with Lebesgue length.
Finiteness is essential here: toReal of an infinite mass would be zero. -/
theorem undergraph_section_volume {X : Type u} (V : Submodule ℝ (X → ℝ))
    (s : Set (X × ℝ)) (hs : s ∈ undergraphFamily V) (x : X) :
    ENNReal.ofReal (undergraphLength s x) = volume ((fun t : ℝ => (x, t)) ⁻¹' s) := by
  obtain ⟨f, g, rfl⟩ := hs
  change ENNReal.ofReal ((volume (Ico ((f : X → ℝ) x) ((g : X → ℝ) x))).toReal) = _
  apply ENNReal.ofReal_toReal
  rw [Real.volume_Ico]
  exact ENNReal.ofReal_ne_top

theorem undergraph_section_measurable {X : Type u} (V : Submodule ℝ (X → ℝ))
    (s : Set (X × ℝ)) (hs : s ∈ undergraphFamily V) (x : X) :
    MeasurableSet ((fun t : ℝ => (x, t)) ⁻¹' s) := by
  obtain ⟨f, g, rfl⟩ := hs
  change MeasurableSet (Ico ((f : X → ℝ) x) ((g : X → ℝ) x))
  exact measurableSet_Ico

/-- A cover in the product induces a length domination at every x. -/
theorem undergraph_length_cover {X : Type u} (V : Submodule ℝ (X → ℝ))
    (s : Set (X × ℝ)) (a : ℕ → Set (X × ℝ))
    (hs : s ∈ undergraphFamily V) (ha : ∀ n, a n ∈ undergraphFamily V)
    (hcover : s ⊆ ⋃ n, a n) (x : X) :
    ENNReal.ofReal (undergraphLength s x) ≤ ∑' n, ENNReal.ofReal (undergraphLength (a n) x) := by
  simp_rw [undergraph_section_volume V s hs x, undergraph_section_volume V (a _) (ha _) x]
  calc
    _ ≤ volume ((fun t : ℝ => (x, t)) ⁻¹' ⋃ n, a n) := measure_mono (preimage_mono hcover)
    _ = volume (⋃ n, (fun t : ℝ => (x, t)) ⁻¹' a n) := by rw [preimage_iUnion]
    _ ≤ _ := measure_iUnion_le _

/-- Disjoint unions in the product induce exact nonnegative section series. -/
theorem undergraph_length_countable {X : Type u} (V : Submodule ℝ (X → ℝ))
    (s : Set (X × ℝ)) (a : ℕ → Set (X × ℝ))
    (hs : s ∈ undergraphFamily V) (ha : ∀ n, a n ∈ undergraphFamily V)
    (hd : Pairwise (Disjoint on a)) (heq : (⋃ n, a n) = s) (x : X) :
    ENNReal.ofReal (undergraphLength s x) = ∑' n, ENNReal.ofReal (undergraphLength (a n) x) := by
  simp_rw [undergraph_section_volume V s hs x, undergraph_section_volume V (a _) (ha _) x]
  rw [← heq, preimage_iUnion]
  exact measure_iUnion (fun i j hij => (hd hij).preimage _)
    (fun n => undergraph_section_measurable V (a n) (ha n) x)

theorem undergraph_content_cover : Specs.UndergraphContentCover := by
  intro X V hV L hL s a hs ha hcover
  let f : V := ⟨undergraphLength s, undergraph_length_mem V hV s hs⟩
  let b : ℕ → V := fun n => ⟨undergraphLength (a n), undergraph_length_mem V hV (a n) (ha n)⟩
  have h := elementary_series_comparison V hV L hL f b
    (undergraph_length_nonneg s) (fun n => undergraph_length_nonneg (a n))
    (undergraph_length_cover V s a hs ha hcover)
  simpa only [undergraph_content_eq V L s f.property,
    undergraph_content_eq V L (a _) (b _).property] using h

theorem undergraph_content_countable : Specs.UndergraphContentCountable := by
  intro X V hV L hL s a hs ha hd heq
  let f : V := ⟨undergraphLength s, undergraph_length_mem V hV s hs⟩
  let b : ℕ → V := fun n => ⟨undergraphLength (a n), undergraph_length_mem V hV (a n) (ha n)⟩
  have h := elementary_series_equality V hV L hL f b
    (undergraph_length_nonneg s) (fun n => undergraph_length_nonneg (a n))
    (undergraph_length_countable V s a hs ha hd heq)
  simpa only [undergraph_content_eq V L s f.property,
    undergraph_content_eq V L (a _) (b _).property] using h

/-- Finite disjoint unions use ordinary finite linearity of L. -/
theorem undergraph_content_finite_additive : Specs.UndergraphContentFiniteAdditive := by
  classical
  intro X ι _ V hV L hL s a hs ha hd heq
  let f : V := ⟨undergraphLength s, undergraph_length_mem V hV s hs⟩
  let b : ι → V := fun i => ⟨undergraphLength (a i), undergraph_length_mem V hV (a i) (ha i)⟩
  have hsections (x : X) : ENNReal.ofReal (undergraphLength s x) =
      ∑ i, ENNReal.ofReal (undergraphLength (a i) x) := by
    simp_rw [undergraph_section_volume V s hs x, undergraph_section_volume V (a _) (ha _) x]
    rw [← heq, preimage_iUnion, ← tsum_fintype (L := SummationFilter.unconditional ι)]
    exact measure_iUnion (fun i j hij => (hd hij).preimage _)
      (fun i => undergraph_section_measurable V (a i) (ha i) x)
  have hsum : f = ∑ i, b i := by
    apply Subtype.ext
    funext x
    have h := hsections x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => undergraph_length_nonneg (a i) x)] at h
    have hr := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (undergraph_length_nonneg s x),
      ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => undergraph_length_nonneg (a i) x))] at hr
    simpa [f, b] using hr
  calc
    undergraphContent V L s = ENNReal.ofReal (L f) := undergraph_content_eq V L s f.property
    _ = ENNReal.ofReal (∑ i, L (b i)) := by rw [hsum, map_sum]
    _ = ∑ i, ENNReal.ofReal (L (b i)) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        IsElementaryIntegral.nonneg hL (b i) (undergraph_length_nonneg (a i)))
    _ = _ := Finset.sum_congr rfl (fun i _ => (undergraph_content_eq V L (a i) (b i).property).symm)

end D11.Ch23
