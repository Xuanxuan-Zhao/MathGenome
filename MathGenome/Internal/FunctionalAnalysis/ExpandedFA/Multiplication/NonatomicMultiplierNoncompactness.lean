import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.NonatomicMultiplierNoncompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.SemifiniteMultiplierBounds
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ExpandedFA.Multiplication

variable {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A nonzero measurable multiplier has a finite positive set on which its
norm is bounded above and uniformly bounded away from zero. -/
theorem exists_multiplier_band (hμ : Semifinite μ) (a : Ω → 𝕜)
    (ha : Measurable a) (hnz : ¬ (a =ᵐ[μ] 0)) :
    ∃ (F : Set Ω) (δ C : ℝ), MeasurableSet F ∧ 0 < μ F ∧ μ F < ∞ ∧
      0 < δ ∧ ∀ x ∈ F, δ ≤ ‖a x‖ ∧ ‖a x‖ ≤ C := by
  classical
  let E : ℕ × ℕ → Set Ω := fun k =>
    {x | 1 / ((k.1 : ℝ) + 1) ≤ ‖a x‖ ∧ ‖a x‖ ≤ (k.2 : ℝ)}
  have hE : ∀ k, MeasurableSet (E k) := fun k =>
    (measurableSet_le measurable_const ha.norm).inter
      (measurableSet_le ha.norm measurable_const)
  have hcover : {x | a x ≠ 0} ⊆ ⋃ k, E k := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hx)
    obtain ⟨m, hm⟩ := exists_nat_gt ‖a x‖
    exact Set.mem_iUnion.mpr ⟨(n, m), hn.le, hm.le⟩
  have hpos : ∃ k, 0 < μ (E k) := by
    by_contra h
    have hnull : ∀ k, μ (E k) = 0 := by simpa only [not_exists, not_lt, le_zero_iff] using h
    have hz := measure_mono_null hcover (measure_iUnion_null hnull)
    exact hnz (by simpa only [Filter.EventuallyEq, ae_iff, Pi.zero_apply] using hz)
  obtain ⟨k, hk⟩ := hpos
  obtain ⟨F, hsub, hF, hF0, hFtop⟩ := hμ (E k) (hE k) hk
  exact ⟨F, 1 / ((k.1 : ℝ) + 1), k.2, hF, hF0, hFtop, by positivity,
    fun x hx => hsub hx⟩

/-- Repeatedly split a positive remainder. No countability or regularity of
the original measure space is assumed. -/
theorem exists_disjoint_positive_subsets (hμ : Nonatomic μ) {F : Set Ω}
    (hF : MeasurableSet F) (hF0 : 0 < μ F) :
    ∃ E : ℕ → Set Ω, (∀ n, E n ⊆ F ∧ MeasurableSet (E n) ∧ 0 < μ (E n)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) := by
  classical
  let P := {E : Set Ω // E ⊆ F ∧ MeasurableSet E ∧ 0 < μ E}
  have split (E : P) : ∃ A : Set Ω,
      A ⊆ E.val ∧ MeasurableSet A ∧ 0 < μ A ∧ 0 < μ (E.val \ A) :=
    hμ E.val E.property.2.1 E.property.2.2
  let A (E : P) := (split E).choose
  have hA (E : P) := (split E).choose_spec
  let next (E : P) : P := ⟨E.val \ A E,
    (Set.sdiff_subset.trans E.property.1), E.property.2.1.diff (hA E).2.1, (hA E).2.2.2⟩
  let R : ℕ → P := fun n => next^[n] ⟨F, Set.Subset.rfl, hF, hF0⟩
  have hR (n : ℕ) : R (n + 1) = next (R n) := by
    exact Function.iterate_succ_apply' next n _
  have hdec : Antitone (fun n => (R n).val) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hR]
    exact Set.sdiff_subset
  refine ⟨fun n => A (R n), ?_, ?_⟩
  · intro n
    exact ⟨(hA (R n)).1.trans (R n).property.1, (hA (R n)).2.1,
      (hA (R n)).2.2.1⟩
  · apply Pairwise.of_lt
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hxR : x ∈ (R (i + 1)).val := hdec (Nat.succ_le_of_lt hij) ((hA (R j)).1 hxj)
    rw [hR] at hxR
    exact hxR.2 hxi

/-- A normalized indicator is in the maximal domain whenever the multiplier
is bounded on its finite-measure support. -/
theorem exists_domain_unit_indicator (hp : p ≠ ∞) (a : Ω → 𝕜) (ha : Measurable a)
    {E : Set Ω} (hE : MeasurableSet E) (hE0 : 0 < μ E) (hEtop : μ E < ∞)
    {C : ℝ} (hC : ∀ x ∈ E, ‖a x‖ ≤ C) :
    ∃ f : (maximalMultiplier μ p a).domain,
      ‖(f : Lp 𝕜 p μ)‖ = 1 ∧ ∀ᵐ x ∂μ, x ∉ E → (f : Lp 𝕜 p μ) x = 0 := by
  let v : Lp 𝕜 p μ := indicatorConstLp p hE hEtop.ne 1
  have hv : 0 < ‖v‖ := indicator_norm_pos hp hE hE0 hEtop
  let f : Lp 𝕜 p μ := ‖v‖⁻¹ • v
  have hfs : ∀ᵐ x ∂μ, x ∉ E → f x = 0 := by
    filter_upwards [Lp.coeFn_smul (‖v‖⁻¹) v,
      indicatorConstLp_coeFn_notMem (p := p) (hs := hE) (hμs := hEtop.ne)
        (c := (1 : 𝕜))] with x hx hz hnot
    rw [hx]
    change ‖v‖⁻¹ • v x = 0
    rw [show v x = 0 from hz hnot, smul_zero]
  have hD : f ∈ (maximalMultiplier μ p a).domain := by
    apply (Lp.memLp f).of_le_mul (c := C) (ha.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards [hfs] with x hx
    change ‖a x * f x‖ ≤ C * ‖f x‖
    rw [norm_mul]
    by_cases hxe : x ∈ E
    · exact mul_le_mul_of_nonneg_right (hC x hxe) (norm_nonneg _)
    · simp [hx hxe]
  refine ⟨⟨f, hD⟩, ?_, hfs⟩
  change ‖‖v‖⁻¹ • v‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv), inv_mul_cancel₀ hv.ne']

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
/-- Images of disjoint domain unit vectors have a uniform separation whenever
the multiplier is bounded below on the first vector's support. -/
theorem multiplier_images_separated (a : Ω → 𝕜) {δ : ℝ} (hδ : 0 < δ)
    {E F : Set Ω} (hEF : Disjoint E F) (hlow : ∀ x ∈ E, δ ≤ ‖a x‖)
    (f g : (maximalMultiplier μ p a).domain)
    (hf : ‖(f : Lp 𝕜 p μ)‖ = 1)
    (hfs : ∀ᵐ x ∂μ, x ∉ E → (f : Lp 𝕜 p μ) x = 0)
    (hgs : ∀ᵐ x ∂μ, x ∉ F → (g : Lp 𝕜 p μ) x = 0) :
    δ ≤ dist (maximalMultiplier μ p a f) (maximalMultiplier μ p a g) := by
  have hnorm : ‖(f : Lp 𝕜 p μ)‖ ≤
      δ⁻¹ * ‖maximalMultiplier μ p a f - maximalMultiplier μ p a g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hfs, hgs, maximalLpMultiplier_apply μ p a f,
      maximalLpMultiplier_apply μ p a g,
      Lp.coeFn_sub (maximalMultiplier μ p a f) (maximalMultiplier μ p a g)]
      with x hfx hgx hyf hyg hsub
    rw [hsub]
    change ‖(f : Lp 𝕜 p μ) x‖ ≤ δ⁻¹ *
      ‖maximalMultiplier μ p a f x - maximalMultiplier μ p a g x‖
    rw [hyf, hyg]
    by_cases hx : x ∈ E
    · have hxF : x ∉ F := fun hxF => Set.disjoint_left.mp hEF hx hxF
      rw [hgx hxF, mul_zero, sub_zero, norm_mul]
      apply (le_inv_mul_iff₀ hδ).mpr
      exact mul_le_mul_of_nonneg_right (hlow x hx) (norm_nonneg _)
    · rw [hfx hx, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg _)
  rw [hf] at hnorm
  rw [dist_eq_norm]
  simpa only [mul_one] using (le_inv_mul_iff₀ hδ).mp hnorm

theorem nonatomic_multiplier_noncompact : NonatomicMultiplierNoncompactnessSpec.Noncompactness := by
  intro Ω 𝕜 _ _ _ _ μ hsemi hnonatomic p _ _hp1 hp a ha hnz hcompact
  obtain ⟨F, δ, C, hF, hF0, hFtop, hδ, hband⟩ := exists_multiplier_band hsemi a ha hnz
  obtain ⟨E, hE, hdisj⟩ := exists_disjoint_positive_subsets hnonatomic hF hF0
  have htest (n : ℕ) := exists_domain_unit_indicator (p := p) hp a ha (hE n).2.1
    (hE n).2.2 (lt_of_le_of_lt (measure_mono (hE n).1) hFtop)
    (fun x hx => (hband x ((hE n).1 hx)).2)
  choose f hfnorm hfsupport using htest
  let y : ℕ → Lp 𝕜 p μ := fun n => maximalMultiplier μ p a (f n)
  have hsep (i j : ℕ) (hij : i ≠ j) : δ ≤ dist (y i) (y j) :=
    multiplier_images_separated a hδ (hdisj hij)
      (fun x hx => (hband x ((hE i).1 hx)).1) (f i) (f j)
      (hfnorm i) (hfsupport i) (hfsupport j)
  obtain ⟨z, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq (fun n =>
    subset_closure (show y n ∈ multiplierUnitImage μ p a from
      ⟨f n, (hfnorm n).le, rfl⟩))
  have hc : CauchySeq (y ∘ φ) := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc δ hδ
  have hlt := hN N (le_refl N) (N + 1) (Nat.le_succ N)
  exact (not_lt_of_ge (hsep (φ N) (φ (N + 1)) (hφ.injective.ne (Nat.ne_of_lt (Nat.lt_succ_self N))))) hlt

theorem nonatomic_multiplier_compact_iff_zero : NonatomicMultiplierNoncompactnessSpec.CompactIffZero := by
  intro Ω 𝕜 _ _ _ _ μ hsemi hnonatomic p _ hp1 hp a ha T hT
  constructor
  · intro hcompact
    by_contra hnz
    apply nonatomic_multiplier_noncompact μ hsemi hnonatomic p hp1 hp a ha hnz
    have himage : multiplierUnitImage μ p a ⊆ T '' Metric.closedBall 0 1 := by
      rintro _ ⟨f, hf, rfl⟩
      refine ⟨f, ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          (show ‖(f : Lp 𝕜 p μ)‖ ≤ 1 from hf)
      · apply Lp.ext
        exact (hT f).trans (maximalLpMultiplier_apply μ p a f).symm
    exact (hcompact.isCompact_closure_image_closedBall 1).of_isClosed_subset
      isClosed_closure (closure_mono himage)
  · intro hzero
    have hTzero : T = 0 := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      filter_upwards [hT f, hzero, Lp.coeFn_zero 𝕜 p μ] with x hx hz h0
      simp_all
    rw [hTzero]
    exact isCompactOperator_zero

/-- Counting measure is semifinite, with a singleton as finite test set. -/
theorem counting_semifinite : Semifinite (Measure.count : Measure ℕ) := by
  intro E _ hE
  obtain ⟨n, hn⟩ := nonempty_of_measure_ne_zero hE.ne'
  exact ⟨{n}, Set.singleton_subset_iff.mpr hn, measurableSet_singleton n, by simp, by simp⟩

/-- Bounded diagonal multiplication on the actual counting-measure Lp quotient. -/
def countingBoundedMultiplier (a : ℕ → 𝕜) (C : ℝ) (hC : ∀ n, ‖a n‖ ≤ C) :
    Lp 𝕜 p (Measure.count : Measure ℕ) →L[𝕜] Lp 𝕜 p (Measure.count : Measure ℕ) :=
  fullMultiplier a (full_domain_of_memLp_top a (measurable_of_countable a)
    (memLp_top_of_bound (measurable_of_countable a).aestronglyMeasurable C
      (Measure.ae_count_iff.mpr hC)))

theorem countingBoundedMultiplier_apply (a : ℕ → 𝕜) (C : ℝ) (hC : ∀ n, ‖a n‖ ≤ C)
    (f : Lp 𝕜 p (Measure.count : Measure ℕ)) (n : ℕ) :
    countingBoundedMultiplier (p := p) a C hC f n = a n * f n :=
  Measure.ae_count_iff.mp (fullMultiplier_apply a _ f) n

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
/-- A counting-measure multiplier supported on the first m coordinates has
finite-dimensional range. Representative evaluation is linear here because
counting measure has no nonempty null sets. -/
theorem counting_finite_rank (T : Lp 𝕜 p (Measure.count : Measure ℕ) →L[𝕜] Lp 𝕜 p (Measure.count : Measure ℕ))
    (m : ℕ) (hT : ∀ f n, m ≤ n → T f n = 0) :
    FiniteDimensional 𝕜 T.toLinearMap.range := by
  let R := T.toLinearMap.range
  let eval : R →ₗ[𝕜] (Fin m → 𝕜) :=
    { toFun := fun x i => (x : Lp 𝕜 p (Measure.count : Measure ℕ)) i
      map_add' := by
        intro x y
        funext i
        exact Measure.ae_count_iff.mp (Lp.coeFn_add (x : Lp 𝕜 p (Measure.count : Measure ℕ)) y) i
      map_smul' := by
        intro c x
        funext i
        exact Measure.ae_count_iff.mp (Lp.coeFn_smul c (x : Lp 𝕜 p (Measure.count : Measure ℕ))) i }
  apply FiniteDimensional.of_injective eval
  intro x y hxy
  apply Subtype.ext
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro n
  by_cases hn : n < m
  · exact congrFun hxy ⟨n, hn⟩
  · obtain ⟨f, hf⟩ := x.property
    obtain ⟨g, hg⟩ := y.property
    rw [← hf, ← hg]
    change T f n = T g n
    rw [hT f n (Nat.le_of_not_gt hn), hT g n (Nat.le_of_not_gt hn)]

/-- The norm of any counting-measure multiplier is bounded below by each
coordinate of its symbol. -/
theorem counting_multiplier_coordinate_le (hp : p ≠ ∞)
    (T : Lp 𝕜 p (Measure.count : Measure ℕ) →L[𝕜] Lp 𝕜 p (Measure.count : Measure ℕ))
    (a : ℕ → 𝕜) (hT : ∀ f n, T f n = a n * f n) (n : ℕ) : ‖a n‖ ≤ ‖T‖ := by
  apply Measure.ae_count_iff.mp (multiplier_bound_test counting_semifinite hp a
    (measurable_of_countable a) T (fun f => Measure.ae_count_iff.mpr (hT f))) n

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
private theorem reciprocal_coordinate_norm (n : ℕ) :
    ‖((n : 𝕜) + 1)⁻¹‖ = 1 / ((n : ℝ) + 1) := by
  rw [← Nat.cast_one (R := 𝕜), ← Nat.cast_add, norm_inv, RCLike.norm_natCast]
  simp only [Nat.cast_add, Nat.cast_one, one_div]

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
private theorem reciprocal_coordinate_bound (n : ℕ) : ‖((n : 𝕜) + 1)⁻¹‖ ≤ 1 := by
  rw [reciprocal_coordinate_norm]
  exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))

/-- The reciprocal diagonal is compact for every finite p in the source range,
with the exact norm of every finite-rank truncation error. -/
theorem counting_reciprocal_compact : NonatomicMultiplierNoncompactnessSpec.CountingExample := by
  intro 𝕜 _ _ _ p _ _hp1 hp
  let a : ℕ → 𝕜 := fun n => ((n : 𝕜) + 1)⁻¹
  let b : ℕ → ℕ → 𝕜 := fun m n => if n < m then a n else 0
  have ha : ∀ n, ‖a n‖ ≤ 1 := reciprocal_coordinate_bound
  have hb : ∀ m n, ‖b m n‖ ≤ 1 := by
    intro m n
    dsimp [b]
    split_ifs <;> simp [ha n]
  let T := countingBoundedMultiplier (p := p) a 1 ha
  let S : ℕ → Lp 𝕜 p (Measure.count : Measure ℕ) →L[𝕜] Lp 𝕜 p (Measure.count : Measure ℕ) :=
    fun m => countingBoundedMultiplier (p := p) (b m) 1 (hb m)
  have hT (f : Lp 𝕜 p (Measure.count : Measure ℕ)) (n : ℕ) : T f n = a n * f n :=
    countingBoundedMultiplier_apply a 1 ha f n
  have hS (m : ℕ) (f : Lp 𝕜 p (Measure.count : Measure ℕ)) (n : ℕ) :
      S m f n = if n < m then a n * f n else 0 := by
    rw [countingBoundedMultiplier_apply]
    dsimp [b]
    split_ifs <;> simp
  have hsub (m : ℕ) (f : Lp 𝕜 p (Measure.count : Measure ℕ)) (n : ℕ) :
      (T - S m) f n = (a n - b m n) * f n := by
    have hc := Measure.ae_count_iff.mp (Lp.coeFn_sub (T f) (S m f)) n
    change (T - S m) f n = _
    rw [sub_apply, hc]
    change T f n - S m f n = _
    rw [hT, countingBoundedMultiplier_apply, sub_mul]
  have hfin (m : ℕ) : FiniteDimensional 𝕜 (S m).toLinearMap.range := by
    apply counting_finite_rank (S m) m
    intro f n hn
    rw [hS, ite_eq_right (Nat.not_lt.mpr hn)]
  have herror (m : ℕ) : ‖T - S m‖ = 1 / ((m : ℝ) + 1) := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro f
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      apply Measure.ae_count_iff.mpr
      intro n
      rw [hsub, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [b]
      by_cases hn : n < m
      · rw [ite_eq_left hn, sub_self, norm_zero]
        positivity
      · rw [ite_eq_right hn, sub_zero, reciprocal_coordinate_norm]
        exact one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (Nat.le_of_not_gt hn) 1)
    · have hle := counting_multiplier_coordinate_le hp (T - S m)
        (fun n => a n - b m n) (hsub m) m
      change ‖a m - (if m < m then a m else 0)‖ ≤ ‖T - S m‖ at hle
      simp only [lt_self_iff_false, ite_false, sub_zero] at hle
      rw [show ‖a m‖ = 1 / ((m : ℝ) + 1) from reciprocal_coordinate_norm m] at hle
      exact hle
  have hcompact (m : ℕ) : IsCompactOperator (S m) := by
    let := hfin m
    let : LocallyCompactSpace (S m).toLinearMap.range :=
      LocallyCompactSpace.of_finiteDimensional_of_complete 𝕜 _
    have hc : IsCompactOperator (S m).rangeRestrict :=
      isCompactOperator_of_locallyCompactSpace_dom (S m).rangeRestrict
    exact hc.continuous_comp continuous_subtype_val
  have hlim : Tendsto S atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hn (m : ℕ) : ‖S m - T‖ = 1 / ((m : ℝ) + 1) := by
      rw [norm_sub_rev, herror]
    simp_rw [hn]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨T, S, fun f => Measure.ae_count_iff.mpr (hT f), ?_,
    isCompactOperator_of_tendsto hlim (Eventually.of_forall hcompact), ?_⟩
  · intro hz
    have hle := counting_multiplier_coordinate_le hp T a hT 0
    norm_num [hz, a] at hle
  · intro m
    exact ⟨fun f => Measure.ae_count_iff.mpr (hS m f), hfin m, herror m⟩

end ExpandedFA.Multiplication
