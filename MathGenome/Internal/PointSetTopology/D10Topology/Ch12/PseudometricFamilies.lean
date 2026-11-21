import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricFamilies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.EntourageCalculus
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set Filter
open scoped Uniformity Topology
universe u v
namespace D10Topology.Ch12

abbrev familyUniformity := @Specs.D10Topology.Ch12.PseudometricFamilies.familyUniformity
abbrev familyEntourage := @Specs.D10Topology.Ch12.PseudometricFamilies.familyEntourage
noncomputable abbrev weightedDistance := @Specs.D10Topology.Ch12.PseudometricFamilies.weightedDistance
abbrev SeparatesPairs := @Specs.D10Topology.Ch12.PseudometricFamilies.SeparatesPairs
abbrev zeroPseudometric := Specs.D10Topology.Ch12.PseudometricFamilies.zeroPseudometric
abbrev zeroPadding := @Specs.D10Topology.Ch12.PseudometricFamilies.zeroPadding

/-- The term indexed by n has the paper's weight 2^{-(n+1)}. -/
private noncomputable abbrev weight (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (n + 1)

private theorem weight_pos (n : ℕ) : 0 < weight n := by positivity

private theorem weight_sum : HasSum weight 1 := by
  have hs : HasSum (fun n : ℕ => (2 : ℝ)⁻¹ ^ n * 2⁻¹) 1 := by
    convert hasSum_geometric_two.mul_right (1 / 2 : ℝ) using 1 <;> norm_num
  exact hs.congr_fun (fun n => (pow_succ _ n).symm)

private theorem term_nonneg {X : Type u} (p : ℕ → PseudoMetricSpace X) (x y : X) (n : ℕ) :
    0 ≤ weight n * min 1 (@dist X (p n).toDist x y) := by
  let := p n
  exact mul_nonneg (weight_pos n).le (le_min (by norm_num) dist_nonneg)

private theorem term_le_weight {X : Type u} (p : ℕ → PseudoMetricSpace X) (x y : X) (n : ℕ) :
    weight n * min 1 (@dist X (p n).toDist x y) ≤ weight n := by
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (weight_pos n).le).trans_eq (mul_one _)

theorem weighted_summable : Specs.D10Topology.Ch12.PseudometricFamilies.weighted_summable := by
  intro X p x y
  exact weight_sum.summable.of_nonneg_of_le (term_nonneg p x y) (term_le_weight p x y)

theorem family_uniformity_basis : Specs.D10Topology.Ch12.PseudometricFamilies.family_uniformity_basis := by
  intro X I p U
  change U ∈ @uniformity X (⨅ i, (p i).toUniformSpace) ↔ _
  rw [iInf_uniformity]
  have h := Filter.HasBasis.iInf' (fun i : I => @Metric.uniformity_basis_dist X (p i))
  simpa only [familyUniformity, Specs.D10Topology.Ch12.PseudometricFamilies.familyUniformity,
    iInf_uniformity, familyEntourage, Specs.D10Topology.Ch12.PseudometricFamilies.familyEntourage,
    Prod.exists, exists_and_left, and_assoc] using h.mem_iff (t := U)

theorem family_empty : Specs.D10Topology.Ch12.PseudometricFamilies.family_empty := by
  intro X I hI p
  simp [Specs.D10Topology.Ch12.PseudometricFamilies.familyUniformity]

/-- Truncating a nonnegative triangle inequality at one preserves it. -/
theorem min_one_triangle {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : c ≤ a + b) : min 1 c ≤ min 1 a + min 1 b := by
  by_cases hA : a ≤ 1
  · by_cases hB : b ≤ 1
    · simpa only [min_eq_right hA, min_eq_right hB] using (min_le_right 1 c).trans hc
    · rw [min_eq_left (le_of_not_ge hB)]
      have := min_le_left (1 : ℝ) c
      have := le_min (by norm_num : (0 : ℝ) ≤ 1) ha
      linarith
  · rw [min_eq_left (le_of_not_ge hA)]
    have := min_le_left (1 : ℝ) c
    have := le_min (by norm_num : (0 : ℝ) ≤ 1) hb
    linarith

theorem weighted_pseudometric_axioms :
    Specs.D10Topology.Ch12.PseudometricFamilies.weighted_pseudometric_axioms := by
  intro X p
  refine ⟨fun x y => tsum_nonneg (term_nonneg p x y), ?_, ?_, ?_⟩
  · intro x
    simp [Specs.D10Topology.Ch12.PseudometricFamilies.weightedDistance]
  · intro x y
    apply tsum_congr
    intro n
    rw [(p n).dist_comm x y]
  · intro x y z
    change (∑' n, weight n * min 1 (@dist X (p n).toDist x z)) ≤ _
    dsimp only [Specs.D10Topology.Ch12.PseudometricFamilies.weightedDistance]
    rw [← (weighted_summable p x y).tsum_add (weighted_summable p y z)]
    apply (weighted_summable p x z).tsum_le_tsum _
      ((weighted_summable p x y).add (weighted_summable p y z))
    intro n
    rw [← mul_add]
    let := p n
    exact mul_le_mul_of_nonneg_left (min_one_triangle dist_nonneg dist_nonneg
      (dist_triangle x y z)) (weight_pos n).le

theorem weighted_bounded : Specs.D10Topology.Ch12.PseudometricFamilies.weighted_bounded := by
  intro X p x y
  exact ⟨tsum_nonneg (term_nonneg p x y),
    ((weighted_summable p x y).tsum_le_tsum (term_le_weight p x y)
      weight_sum.summable).trans_eq weight_sum.tsum_eq⟩

/-- Each individual weighted truncated distance is bounded by the whole sum. -/
theorem weighted_term_le {X : Type u} (p : ℕ → PseudoMetricSpace X) (x y : X) (n : ℕ) :
    (2 : ℝ)⁻¹ ^ (n + 1) * min 1 (@dist X (p n).toDist x y) ≤ weightedDistance p x y := by
  exact (weighted_summable p x y).le_tsum n (fun m _ => term_nonneg p x y m)

theorem weighted_zero_iff : Specs.D10Topology.Ch12.PseudometricFamilies.weighted_zero_iff := by
  intro X p x y
  constructor
  · intro h n
    change weightedDistance p x y = 0 at h
    have ht := weighted_term_le p x y n
    rw [h] at ht
    have hz : min 1 (@dist X (p n).toDist x y) = 0 := by
      have hn := term_nonneg p x y n
      have hm : weight n * min 1 (@dist X (p n).toDist x y) = 0 := le_antisymm ht hn
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt (weight_pos n))
    rcases min_eq_iff.mp hz with h1 | h2
    · norm_num at h1
    · exact h2.1
  · intro h
    simp [Specs.D10Topology.Ch12.PseudometricFamilies.weightedDistance, h]

/-- Domination by the summable geometric series permits passing the entourage
filter limit through the sum. This proves the infinite-head/tail refinement
without a nonemptiness assumption on the filter or underlying space. -/
theorem weighted_distance_tendsto {X : Type u} (p : ℕ → PseudoMetricSpace X) :
    Tendsto (fun xy : X × X => weightedDistance p xy.1 xy.2)
      (@uniformity X (familyUniformity p)) (𝓝 (0 : ℝ)) := by
  have hterm (n : ℕ) : Tendsto
      (fun xy : X × X => weight n * min 1 (@dist X (p n).toDist xy.1 xy.2))
      (@uniformity X (familyUniformity p)) (𝓝 (0 : ℝ)) := by
    have hd : Tendsto (fun xy : X × X => @dist X (p n).toDist xy.1 xy.2)
        (@uniformity X (p n).toUniformSpace) (𝓝 (0 : ℝ)) :=
      (@tendsto_uniformity_iff_dist_tendsto_zero X (X × X) (p n) id
        (@uniformity X (p n).toUniformSpace)).mp tendsto_id
    have hle : @uniformity X (familyUniformity p) ≤
        @uniformity X (p n).toUniformSpace := by
      change @uniformity X (⨅ i, (p i).toUniformSpace) ≤ _
      rw [iInf_uniformity]
      exact iInf_le _ n
    simpa only [min_eq_right (by norm_num : (0 : ℝ) ≤ 1), mul_zero] using
      ((tendsto_const_nhds (x := weight n)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).min (hd.mono_left hle)))
  have hs := tendsto_tsum_of_dominated_convergence
    (f := fun xy : X × X => fun n => weight n * min 1 (@dist X (p n).toDist xy.1 xy.2))
    (g := fun _ : ℕ => (0 : ℝ)) weight_sum.summable hterm
    (Eventually.of_forall fun xy n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg p xy.1 xy.2 n)]
      exact term_le_weight p xy.1 xy.2 n)
  change Tendsto (fun xy : X × X => ∑' n, weight n * min 1 (@dist X (p n).toDist xy.1 xy.2)) _ _
  simpa only [tsum_zero] using hs

theorem weighted_uniformity : Specs.D10Topology.Ch12.PseudometricFamilies.weighted_uniformity := by
  intro X p
  have ha := weighted_pseudometric_axioms p
  let d : PseudoMetricSpace X :=
    { dist := weightedDistance p
      dist_self := ha.2.1
      dist_comm := ha.2.2.1
      dist_triangle := ha.2.2.2 }
  refine ⟨d, rfl, UniformSpace.ext (le_antisymm ?_ ?_)⟩
  · change @uniformity X d.toUniformSpace ≤ @uniformity X (⨅ i, (p i).toUniformSpace)
    rw [iInf_uniformity]
    refine le_iInf fun n => (@Metric.uniformity_basis_dist X (p n)).ge_iff.mpr ?_
    intro ε hε
    have hδ : 0 < weight n * min 1 ε := mul_pos (weight_pos n) (lt_min (by norm_num) hε)
    refine mem_of_superset (@Metric.dist_mem_uniformity X d _ hδ) ?_
    intro xy hxy
    have hsum : weight n * min 1 (@dist X (p n).toDist xy.1 xy.2) <
        weight n * min 1 ε := (weighted_term_le p xy.1 xy.2 n).trans_lt hxy
    exact (min_lt_min_right_iff.mp ((mul_lt_mul_iff_right₀ (weight_pos n)).mp hsum)).1
  · change Tendsto id (@uniformity X (familyUniformity p)) (@uniformity X d.toUniformSpace)
    exact (@tendsto_uniformity_iff_dist_tendsto_zero X (X × X) d id
      (@uniformity X (familyUniformity p))).mpr (weighted_distance_tendsto p)

theorem weighted_metric_iff : Specs.D10Topology.Ch12.PseudometricFamilies.weighted_metric_iff := by
  intro X p
  constructor
  · rintro ⟨_, hmetric⟩ x y hne
    by_contra hn
    have hdist : ∀ n, @dist X (p n).toDist x y = 0 := by
      intro n
      apply le_antisymm _ (@dist_nonneg X (p n) x y)
      exact le_of_not_gt (fun hp => hn ⟨n, hp⟩)
    exact hne ((hmetric x y).mp ((weighted_zero_iff p x y).mpr hdist))
  · intro hsep
    refine ⟨weighted_pseudometric_axioms p, fun x y => ⟨?_, ?_⟩⟩
    · intro hz
      by_contra hne
      obtain ⟨n, hn⟩ := hsep x y hne
      have := (weighted_zero_iff p x y).mp hz n
      linarith
    · rintro rfl
      exact (weighted_pseudometric_axioms p).2.1 x

theorem zero_uniformity : Specs.D10Topology.Ch12.PseudometricFamilies.zero_uniformity := by
  intro X
  apply UniformSpace.ext
  rw [top_uniformity]
  apply (@Metric.uniformity_basis_dist X (zeroPseudometric X)).eq_top_iff.mpr
  intro ε hε
  ext xy
  change (0 < ε) ↔ True
  exact iff_true_intro hε

theorem zero_padding_uniformity :
    Specs.D10Topology.Ch12.PseudometricFamilies.zero_padding_uniformity := by
  intro X n p
  change (⨅ k, (zeroPadding p k).toUniformSpace) = ⨅ i, (p i).toUniformSpace
  apply le_antisymm
  · refine le_iInf fun i => ?_
    have h := iInf_le (fun k => (zeroPadding p k).toUniformSpace) i.val
    unfold zeroPadding Specs.D10Topology.Ch12.PseudometricFamilies.zeroPadding at h
    rw [dite_eq_left i.isLt] at h
    exact h
  · refine le_iInf fun k => ?_
    unfold zeroPadding Specs.D10Topology.Ch12.PseudometricFamilies.zeroPadding
    by_cases h : k < n
    · rw [dite_eq_left h]
      exact iInf_le (fun i : Fin n => (p i).toUniformSpace) ⟨k, h⟩
    · rw [dite_eq_right h, zero_uniformity]
      exact le_top

theorem zero_padding_separates_iff {X : Type u} {n : ℕ} (p : Fin n → PseudoMetricSpace X) :
    SeparatesPairs (zeroPadding p) ↔ SeparatesPairs p := by
  constructor
  · intro h x y hne
    obtain ⟨k, hk⟩ := h x y hne
    unfold zeroPadding Specs.D10Topology.Ch12.PseudometricFamilies.zeroPadding at hk
    by_cases hkn : k < n
    · rw [dite_eq_left hkn] at hk
      exact ⟨⟨k, hkn⟩, hk⟩
    · rw [dite_eq_right hkn] at hk
      exact (lt_irrefl (0 : ℝ) hk).elim
  · intro h x y hne
    obtain ⟨i, hi⟩ := h x y hne
    refine ⟨i.val, ?_⟩
    unfold zeroPadding Specs.D10Topology.Ch12.PseudometricFamilies.zeroPadding
    rw [dite_eq_left i.isLt]
    exact hi

theorem finite_weighted_uniformity :
    Specs.D10Topology.Ch12.PseudometricFamilies.finite_weighted_uniformity := by
  intro X n p
  obtain ⟨d, hd, hu⟩ := weighted_uniformity (zeroPadding p)
  refine ⟨d, hd, hu.trans (zero_padding_uniformity p), ?_⟩
  rw [hd]
  exact (weighted_metric_iff (zeroPadding p)).trans (zero_padding_separates_iff p)

/-- Relabeling a family by an equivalence preserves its whole uniformity. -/
theorem family_uniformity_reindex {X : Type u} {I : Type v} {J : Type*}
    (p : I → PseudoMetricSpace X) (e : J ≃ I) :
    familyUniformity (fun j => p (e j)) = familyUniformity p := by
  change (⨅ j, (p (e j)).toUniformSpace) = ⨅ i, (p i).toUniformSpace
  exact e.iInf_comp (g := fun i : I => (p i).toUniformSpace)

theorem separates_pairs_reindex {X : Type u} {I : Type v} {J : Type*}
    (p : I → PseudoMetricSpace X) (e : J ≃ I) :
    SeparatesPairs (fun j => p (e j)) ↔ SeparatesPairs p := by
  constructor
  · intro h x y hne
    obtain ⟨j, hj⟩ := h x y hne
    exact ⟨e j, hj⟩
  · intro h x y hne
    obtain ⟨i, hi⟩ := h x y hne
    refine ⟨e.symm i, ?_⟩
    change 0 < @dist X (p (e (e.symm i))).toDist x y
    rw [e.apply_symm_apply]
    exact hi

theorem finite_indexed_uniformity :
    Specs.D10Topology.Ch12.PseudometricFamilies.finite_indexed_uniformity := by
  intro X I hI p
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨d, hd, hu, hm⟩ := finite_weighted_uniformity (fun j => p (e.symm j))
  exact ⟨n, e.symm, d, hd, hu.trans (family_uniformity_reindex p e.symm),
    hm.trans (separates_pairs_reindex p e.symm)⟩

theorem empty_weighted_distance :
    Specs.D10Topology.Ch12.PseudometricFamilies.empty_weighted_distance := by
  intro X
  funext x y
  change (∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * min 1 (0 : ℝ)) = 0
  simp

end D10Topology.Ch12
