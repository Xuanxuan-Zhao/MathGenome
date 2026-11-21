import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsMetrization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsNormability
import Mathlib.Analysis.SpecificLimits.Basic

/-! Metrization of real and complex Hausdorff topological vector spaces.
The general construction takes a bounded compatible distance and enforces
translation invariance and balance by a supremum. In the locally convex
case, a supremum of truncated continuous seminorms also gives convex balls.
Both constructions preserve the original topology; no completeness or
normability is assumed. -/

open Set Filter TopologicalSpace
open scoped Topology Uniformity Pointwise

namespace ExpandedFA.P1

theorem tvs_metrizable_iff_countable_local_base : TvsMetrizationSpec.Metrization := by
  intro 𝕜 E _ _ _ _ _ hE
  let : IsTopologicalAddGroup E := hE.1
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.metrizableSpace

theorem lcs_normable_iff_bounded_zero_neighborhood : TvsMetrizationSpec.Normability :=
  normable_iff_bounded_neighborhood

/-- A symmetric subadditive radial function whose small sublevel sets form
exactly the zero neighborhoods yields a compatible invariant metric. -/
private theorem metric_of_radial {E : Type*} [AddCommGroup E]
    [t : TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
    (p : E → ℝ) (hzero : p 0 = 0) (hneg : ∀ x, p (-x) = p x)
    (hadd : ∀ x y, p (x + y) ≤ p x + p y)
    (hsmall : ∀ r > 0, {x | p x < r} ∈ 𝓝 (0 : E))
    (hcontrol : ∀ U ∈ 𝓝 (0 : E), ∃ r > 0, {x | p x < r} ⊆ U) :
    ∃ m : MetricSpace E, m.toUniformSpace.toTopologicalSpace = t ∧
      ∀ x y : E, @dist E m.toPseudoMetricSpace.toDist x y = p (y - x) := by
  let m₀ : PseudoMetricSpace E := PseudoMetricSpace.ofDistTopology
    (fun x y => p (y - x)) (by simpa using fun x : E => hzero)
    (fun x y => by rw [← neg_sub y x, hneg])
    (fun x y z => by
      have heq : (y - x) + (z - y) = z - x := by abel
      simpa only [heq] using hadd (y - x) (z - y))
    (by
      intro s
      constructor
      · intro hs x hx
        have hU : {v : E | x + v ∈ s} ∈ 𝓝 (0 : E) := by
          exact (hs.preimage (continuous_const_add x)).mem_nhds
            (show x + (0 : E) ∈ s by simpa using hx)
        obtain ⟨r, hr, hsub⟩ := hcontrol _ hU
        refine ⟨r, hr, fun y hy => ?_⟩
        have := hsub hy
        simpa only [mem_ofPred_eq, add_sub_cancel] using this
      · intro hs
        rw [isOpen_iff_mem_nhds]
        intro x hx
        obtain ⟨r, hr, hsub⟩ := hs x hx
        have hU : {y : E | p (y - x) < r} ∈ 𝓝 x := by
          have hc : ContinuousAt (fun y : E => y - x) x :=
            (continuous_id.sub continuous_const).continuousAt
          have := hc.preimage_mem_nhds (by simpa using hsmall r hr)
          exact this
        exact mem_of_superset hU hsub)
  let := m₀
  exact ⟨MetricSpace.ofT0PseudoMetricSpace E, rfl, fun _ _ => rfl⟩

section BalancedConstruction
variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [MetricSpace E]

private instance unitDisk_nonempty : Nonempty {a : 𝕜 // ‖a‖ ≤ 1} :=
  ⟨⟨0, by simp⟩⟩

omit [AddCommGroup E] in
/-- Truncating a distance at one preserves its triangle inequality. -/
private theorem truncated_triangle (x y z : E) :
    min 1 (dist x z) ≤ min 1 (dist x y) + min 1 (dist y z) := by
  have h := dist_triangle x y z
  have hxy := dist_nonneg (x := x) (y := y)
  have hyz := dist_nonneg (x := y) (y := z)
  by_cases h₁ : dist x y ≤ 1
  · by_cases h₂ : dist y z ≤ 1
    · rw [min_eq_right h₁, min_eq_right h₂]
      exact (min_le_right _ _).trans h
    · rw [min_eq_left (le_of_not_ge h₂)]
      exact (min_le_left _ _).trans (by
        have hm : 0 ≤ min 1 (dist x y) := le_min zero_le_one hxy
        linarith)
  · rw [min_eq_left (le_of_not_ge h₁)]
    exact (min_le_left _ _).trans (by
      have hm : 0 ≤ min 1 (dist y z) := le_min zero_le_one hyz
      linarith)

/-- The supremum simultaneously enforces translation invariance and
contraction under all scalars in the closed unit disk. -/
private noncomputable def balancedRadial (𝕜 : Type*) [RCLike 𝕜]
    [Module 𝕜 E] (v : E) : ℝ :=
  ⨆ i : {a : 𝕜 // ‖a‖ ≤ 1} × E,
    min 1 (dist i.2 (i.2 + i.1.1 • v))

private theorem balancedRadial_bdd (v : E) :
    BddAbove (Set.range (fun i : {a : 𝕜 // ‖a‖ ≤ 1} × E =>
      min 1 (dist i.2 (i.2 + i.1.1 • v)))) :=
  ⟨1, by rintro _ ⟨i, rfl⟩; exact min_le_left _ _⟩

private theorem balancedRadial_term (v : E) (a : 𝕜) (ha : ‖a‖ ≤ 1) (z : E) :
    min 1 (dist z (z + a • v)) ≤ balancedRadial 𝕜 v :=
  le_ciSup (balancedRadial_bdd v) (⟨a, ha⟩, z)

private theorem balancedRadial_zero : balancedRadial 𝕜 (0 : E) = 0 := by
  simp [balancedRadial]

private theorem balancedRadial_neg_le (v : E) :
    balancedRadial 𝕜 (-v) ≤ balancedRadial 𝕜 v := by
  apply ciSup_le
  intro i
  have heq : dist i.2 (i.2 + i.1.1 • (-v)) =
      dist (i.2 + i.1.1 • (-v)) ((i.2 + i.1.1 • (-v)) + i.1.1 • v) := by
    simp only [smul_neg, neg_add_cancel_right]
    rw [dist_comm]
  rw [heq]
  exact balancedRadial_term v i.1.1 i.1.2 _

private theorem balancedRadial_neg (v : E) :
    balancedRadial 𝕜 (-v) = balancedRadial 𝕜 v := by
  apply le_antisymm (balancedRadial_neg_le v)
  simpa only [neg_neg] using balancedRadial_neg_le (𝕜 := 𝕜) (-v)

private theorem balancedRadial_add (v w : E) :
    balancedRadial 𝕜 (v + w) ≤ balancedRadial 𝕜 v + balancedRadial 𝕜 w := by
  apply ciSup_le
  intro i
  have h := truncated_triangle i.2 (i.2 + i.1.1 • v)
    ((i.2 + i.1.1 • v) + i.1.1 • w)
  rw [show i.2 + i.1.1 • (v + w) = (i.2 + i.1.1 • v) + i.1.1 • w by
    rw [smul_add, add_assoc]]
  exact h.trans (add_le_add
    (balancedRadial_term v i.1.1 i.1.2 _)
    (balancedRadial_term w i.1.1 i.1.2 _))

private theorem balancedRadial_smul (v : E) (c : 𝕜) (hc : ‖c‖ ≤ 1) :
    balancedRadial 𝕜 (c • v) ≤ balancedRadial 𝕜 v := by
  apply ciSup_le
  intro i
  rw [smul_smul]
  exact balancedRadial_term v (i.1.1 * c)
    (by rw [norm_mul]; exact (mul_le_mul_of_nonneg_right i.1.2 (norm_nonneg c)).trans (by simpa using hc)) i.2

variable [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]

private theorem balancedRadial_small (r : ℝ) (hr : 0 < r) :
    {v : E | balancedRadial 𝕜 v < r} ∈ 𝓝 (0 : E) := by
  have hEnt : {p : E × E | dist p.1 p.2 < r / 2} ∈ 𝓤 E :=
    Metric.dist_mem_uniformity (half_pos hr)
  rw [uniformity_eq_comap_nhds_zero] at hEnt
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.mp hEnt
  obtain ⟨W, ⟨hW, hb⟩, hWV⟩ := (nhds_basis_balanced 𝕜 E).mem_iff.mp hV
  apply mem_of_superset hW
  intro v hv
  have hbnd : balancedRadial 𝕜 v ≤ r / 2 := by
    apply ciSup_le
    intro i
    have hav : i.1.1 • v ∈ V := hWV (hb.smul_mem i.1.2 hv)
    have hd : dist i.2 (i.2 + i.1.1 • v) < r / 2 :=
      hsub (show (i.2, i.2 + i.1.1 • v) ∈
        (fun p : E × E => p.2 - p.1) ⁻¹' V by simpa using hav)
    exact (min_le_right _ _).trans hd.le
  exact hbnd.trans_lt (half_lt_self hr)

omit [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem balancedRadial_control (U : Set E) (hU : U ∈ 𝓝 (0 : E)) :
    ∃ r > 0, {v : E | balancedRadial 𝕜 v < r} ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min 1 ε, lt_min one_pos hε, fun v hv => hεU ?_⟩
  have h := (balancedRadial_term v (1 : 𝕜) (by simp) 0).trans_lt hv
  simp only [one_smul, zero_add] at h
  have hd : dist 0 v < ε := by
    rcases lt_or_ge (dist 0 v) 1 with hd | hd
    · simpa only [min_eq_right hd.le] using h.trans_le (min_le_right _ _)
    · rw [min_eq_left hd] at h
      exact False.elim ((not_lt_of_ge (min_le_left 1 ε)) h)
  simpa only [Metric.mem_ball, dist_comm] using hd

end BalancedConstruction

theorem tvs_exists_balanced_invariant_metric : TvsMetrizationSpec.BalancedMetric := by
  intro 𝕜 E _ _ _ t _ hE hc
  let : IsTopologicalAddGroup E := hE.1
  let : ContinuousSMul 𝕜 E := hE.2
  let : (𝓝 (0 : E)).IsCountablyGenerated := hc
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let : MetricSpace E := UniformSpace.metricSpace E
  let p : E → ℝ := balancedRadial 𝕜
  have hpneg : ∀ v, p (-v) = p v := balancedRadial_neg
  have hpsmul : ∀ (v : E) (c : 𝕜), ‖c‖ ≤ 1 → p (c • v) ≤ p v :=
    balancedRadial_smul
  obtain ⟨m, hm, hd⟩ := metric_of_radial p
    (balancedRadial_zero (𝕜 := 𝕜)) (balancedRadial_neg (𝕜 := 𝕜))
    (balancedRadial_add (𝕜 := 𝕜))
    (balancedRadial_small (𝕜 := 𝕜)) (balancedRadial_control (𝕜 := 𝕜))
  refine ⟨m, hm, ?_, ?_⟩
  · intro x y z
    simp only [hd, add_sub_add_right_eq_sub]
  · intro r hr
    rw [balanced_iff_smul_mem]
    intro c hc v hv
    change @dist E m.toPseudoMetricSpace.toDist (c • v) 0 < r
    rw [hd, zero_sub, hpneg]
    exact (hpsmul v c hc).trans_lt (by
      simpa only [Metric.mem_ball, hd, zero_sub, hpneg] using hv)

section SeminormConstruction
variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The minimum of a nonnegative cap and a sum is subadditive. -/
private theorem min_add_le (C a b : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min C (a + b) ≤ min C a + min C b := by
  by_cases h₁ : a ≤ C
  · by_cases h₂ : b ≤ C
    · rw [min_eq_right h₁, min_eq_right h₂]
      exact min_le_right _ _
    · rw [min_eq_left (le_of_not_ge h₂)]
      have hm : 0 ≤ min C a := le_min hC ha
      exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (le_of_not_ge h₁)]
    have hm : 0 ≤ min C b := le_min hC hb
    exact (min_le_left _ _).trans (by linarith)

/-- A supremum rather than a sum keeps the balls convex. -/
private noncomputable def seminormRadial (q : ℕ → Seminorm 𝕜 E) (v : E) : ℝ :=
  ⨆ n : ℕ, min ((1 / 2 : ℝ) ^ n) (q n v)

private theorem seminormRadial_bdd (q : ℕ → Seminorm 𝕜 E) (v : E) :
    BddAbove (Set.range (fun n : ℕ => min ((1 / 2 : ℝ) ^ n) (q n v))) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (min_le_left _ _).trans (pow_le_one₀ (by norm_num) (by norm_num))

private theorem seminormRadial_term (q : ℕ → Seminorm 𝕜 E) (v : E) (n : ℕ) :
    min ((1 / 2 : ℝ) ^ n) (q n v) ≤ seminormRadial q v :=
  le_ciSup (seminormRadial_bdd q v) n

private theorem seminormRadial_zero (q : ℕ → Seminorm 𝕜 E) :
    seminormRadial q 0 = 0 := by
  unfold seminormRadial
  have ht : ∀ n : ℕ, min ((1 / 2 : ℝ) ^ n) (q n 0) = 0 := by
    intro n
    rw [map_zero, min_eq_right (by positivity)]
  simp only [ht, ciSup_const]

private theorem seminormRadial_neg (q : ℕ → Seminorm 𝕜 E) (v : E) :
    seminormRadial q (-v) = seminormRadial q v := by
  simp only [seminormRadial, map_neg_eq_map]

private theorem seminormRadial_add (q : ℕ → Seminorm 𝕜 E) (v w : E) :
    seminormRadial q (v + w) ≤ seminormRadial q v + seminormRadial q w := by
  apply ciSup_le
  intro n
  calc
    min ((1 / 2 : ℝ) ^ n) (q n (v + w)) ≤
        min ((1 / 2 : ℝ) ^ n) (q n v + q n w) :=
      min_le_min_left _ (map_add_le_add (q n) v w)
    _ ≤ min ((1 / 2 : ℝ) ^ n) (q n v) + min ((1 / 2 : ℝ) ^ n) (q n w) :=
      min_add_le _ _ _ (by positivity) (apply_nonneg _ _) (apply_nonneg _ _)
    _ ≤ seminormRadial q v + seminormRadial q w :=
      add_le_add (seminormRadial_term q v n) (seminormRadial_term q w n)

private theorem seminormRadial_smul (q : ℕ → Seminorm 𝕜 E)
    (v : E) (c : 𝕜) (hc : ‖c‖ ≤ 1) :
    seminormRadial q (c • v) ≤ seminormRadial q v := by
  apply ciSup_le
  intro n
  calc
    min ((1 / 2 : ℝ) ^ n) (q n (c • v)) ≤ min ((1 / 2 : ℝ) ^ n) (q n v) := by
      apply min_le_min_left
      rw [map_smul_eq_mul]
      exact mul_le_of_le_one_left (apply_nonneg _ _) hc
    _ ≤ seminormRadial q v := seminormRadial_term q v n

variable [TopologicalSpace E]

private theorem seminormRadial_small (q : ℕ → Seminorm 𝕜 E)
    (hcont : ∀ n, Continuous (q n : E → ℝ)) (r : ℝ) (hr : 0 < r) :
    {v : E | seminormRadial q v < r} ∈ 𝓝 (0 : E) := by
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hr)))
  have hhead : ∀ᶠ v in 𝓝 (0 : E), ∀ n ∈ Finset.range N, q n v < r / 2 := by
    apply (Finset.range N).eventually_all.mpr
    intro n hn
    have hc : Tendsto (fun v : E => q n v) (𝓝 (0 : E)) (𝓝 0) := by
      simpa only [map_zero] using (hcont n).tendsto (0 : E)
    exact hc.eventually (gt_mem_nhds (half_pos hr))
  apply mem_of_superset hhead
  intro v hv
  apply lt_of_le_of_lt (b := r / 2) _ (half_lt_self hr)
  apply ciSup_le
  intro n
  by_cases hn : n < N
  · exact (min_le_right _ _).trans (hv n (Finset.mem_range.mpr hn)).le
  · exact (min_le_left _ _).trans (hN n (Nat.le_of_not_gt hn)).le

private theorem seminormRadial_control (q : ℕ → Seminorm 𝕜 E)
    (hbase : ∀ U ∈ 𝓝 (0 : E), ∃ n : ℕ, {v | q n v < 1} ⊆ U)
    (U : Set E) (hU : U ∈ 𝓝 (0 : E)) :
    ∃ r > 0, {v : E | seminormRadial q v < r} ⊆ U := by
  obtain ⟨n, hn⟩ := hbase U hU
  refine ⟨min ((1 / 2 : ℝ) ^ n) 1, lt_min (by positivity) one_pos, fun v hv => hn ?_⟩
  have h := (seminormRadial_term q v n).trans_lt hv
  change q n v < 1
  by_contra! hvn
  have hcap : (1 / 2 : ℝ) ^ n ≤ q n v :=
    (pow_le_one₀ (by norm_num) (by norm_num)).trans hvn
  rw [min_eq_left hcap] at h
  exact (not_lt_of_ge (min_le_left _ _)) h

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [TopologicalSpace E] in
private theorem seminormRadial_convex (q : ℕ → Seminorm 𝕜 E)
    (v w : E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    seminormRadial q (a • v + b • w) ≤ max (seminormRadial q v) (seminormRadial q w) := by
  apply ciSup_le
  intro n
  have hq : q n (a • v + b • w) ≤ max (q n v) (q n w) := by
    calc
      q n (a • v + b • w) ≤ a * q n v + b * q n w :=
        (q n).convexOn.2 (mem_univ v) (mem_univ w) ha hb hab
      _ ≤ a * max (q n v) (q n w) + b * max (q n v) (q n w) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = max (q n v) (q n w) := by rw [← add_mul, hab, one_mul]
  calc
    min ((1 / 2 : ℝ) ^ n) (q n (a • v + b • w)) ≤
        min ((1 / 2 : ℝ) ^ n) (max (q n v) (q n w)) := min_le_min_left _ hq
    _ = max (min ((1 / 2 : ℝ) ^ n) (q n v))
        (min ((1 / 2 : ℝ) ^ n) (q n w)) := min_max_distrib_left ..
    _ ≤ max (seminormRadial q v) (seminormRadial q w) :=
      max_le_max (seminormRadial_term q v n) (seminormRadial_term q w n)

end SeminormConstruction

/-- Select gauges of absolutely convex neighborhoods from a countable local
base, then take the supremum of their dyadically truncated seminorms. -/
theorem lcs_exists_convex_balanced_invariant_metric : TvsMetrizationSpec.ConvexMetric := by
  intro 𝕜 E _ _ _ _ _ t _ hE hc
  let : IsTopologicalAddGroup E := hE.1.1
  let : ContinuousSMul 𝕜 E := hE.1.2
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let : (𝓝 (0 : E)).IsCountablyGenerated := hc
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have hex : ∀ n : ℕ, ∃ q : Seminorm 𝕜 E,
      Continuous (q : E → ℝ) ∧ {v : E | q v < 1} ⊆ U n := by
    intro n
    obtain ⟨V, hV, ho, hb, hvconv, hVU⟩ :=
      absolutely_convex_neighborhood_basis 𝕜 E hE.2 (U n) (hU.mem n)
    have h0 : (0 : E) ∈ V := mem_of_mem_nhds hV
    obtain ⟨⟨q, hq, hcont⟩, _⟩ :=
      C06.minkowskiGauge_continuous_seminorm V hvconv h0 ho hb
    refine ⟨q, hcont, ?_⟩
    have heq : {v : E | q v < 1} = V := by
      rw [C06.minkowskiGauge_open_unit V hvconv h0 ho]
      simp only [hq]
    exact heq ▸ hVU
  choose q hcont hqU using hex
  have hbase : ∀ V ∈ 𝓝 (0 : E), ∃ n : ℕ, {v : E | q n v < 1} ⊆ V := by
    intro V hV
    obtain ⟨n, hn⟩ := hU.mem_iff.mp hV
    exact ⟨n, (hqU n).trans hn⟩
  let p : E → ℝ := seminormRadial q
  obtain ⟨m, hm, hd⟩ := metric_of_radial p (seminormRadial_zero q)
    (seminormRadial_neg q) (seminormRadial_add q)
    (seminormRadial_small q hcont) (seminormRadial_control q hbase)
  refine ⟨m, hm, ?_, ?_, ?_⟩
  · intro x y z
    simp only [hd, add_sub_add_right_eq_sub]
  · intro r hr
    rw [balanced_iff_smul_mem]
    intro c hc v hv
    change @dist E m.toPseudoMetricSpace.toDist (c • v) 0 < r
    rw [hd, zero_sub]
    change seminormRadial q (-(c • v)) < r
    rw [seminormRadial_neg]
    exact (seminormRadial_smul q v c hc).trans_lt (by
      simpa only [Metric.mem_ball, hd, p, zero_sub, seminormRadial_neg] using hv)
  · intro x r hr v hv w hw a b ha hb hab
    change @dist E m.toPseudoMetricSpace.toDist (a • v + b • w) x < r
    have heq : x - (a • v + b • w) = a • (x - v) + b • (x - w) := by
      calc
        x - (a • v + b • w) = (a + b) • x - (a • v + b • w) := by
          rw [hab, one_smul]
        _ = a • (x - v) + b • (x - w) := by
          rw [add_smul, smul_sub, smul_sub]
          abel
    rw [hd, heq]
    exact (seminormRadial_convex q (x - v) (x - w) a b ha hb hab).trans_lt
      (max_lt (by simpa only [Metric.mem_ball, hd] using hv)
        (by simpa only [Metric.mem_ball, hd] using hw))

end ExpandedFA.P1
