import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.InjectiveCurveArea
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology

namespace D12Complex.Ch04.InjectiveCurveArea

theorem real_normalization : Specs.D12Complex.Ch04.InjectiveCurveArea.real_normalization_type :=
  MeasureTheory.hausdorffMeasure_real


/-- A strict derivative controls every chord in a neighborhood, including chords
whose endpoints are both different from the base point. -/
theorem strict_deriv_chord {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (h : HasStrictDerivAt γ v t) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∀ x ∈ V, ∀ y ∈ V,
        (‖v‖ - δ) * ‖x - y‖ ≤ ‖γ x - γ y‖ ∧
        ‖γ x - γ y‖ ≤ (‖v‖ + δ) * ‖x - y‖ := by
  obtain ⟨W, hW, happ⟩ := h.hasStrictFDerivAt.approximates_deriv_on_nhds (Or.inr hδ)
  obtain ⟨V, hVW, hVo, htV⟩ := _root_.mem_nhds_iff.mp hW
  refine ⟨V, hVo, htV, ?_⟩
  intro x hx y hy
  have he := happ x (hVW hx) y (hVW hy)
  change ‖γ x - γ y - (x - y) • v‖ ≤ (δ : ℝ) * ‖x - y‖ at he
  have hv : ‖(x - y) • v‖ = ‖x - y‖ * ‖v‖ := norm_smul _ _
  constructor
  · have hh := norm_le_norm_add_norm_sub (γ x - γ y) ((x - y) • v)
    nlinarith
  · have hh := norm_le_norm_add_norm_sub ((x - y) • v) (γ x - γ y)
    rw [norm_sub_rev ((x - y) • v)] at hh
    nlinarith

/-- Two-sided Hausdorff distortion on arbitrary subsets of a regular local arc.
No measurability is used for these outer-measure inequalities. -/
theorem local_hausdorff_bounds {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (h : HasStrictDerivAt γ v t) {δ : ℝ≥0} (hδ : 0 < δ) (hδv : (δ : ℝ) < ‖v‖) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∀ A ⊆ V,
        (μH[1] : Measure ℂ) (γ '' A) ≤ ENNReal.ofReal (‖v‖ + δ) * volume A ∧
        ENNReal.ofReal (‖v‖ - δ) * volume A ≤ (μH[1] : Measure ℂ) (γ '' A) := by
  obtain ⟨V, hVo, htV, hV⟩ := strict_deriv_chord h hδ
  refine ⟨V, hVo, htV, ?_⟩
  intro A hAV
  have ha : 0 < ‖v‖ - δ := sub_pos.mpr hδv
  have hb : 0 ≤ ‖v‖ + δ := add_nonneg (norm_nonneg _) δ.2
  have hLip : LipschitzOnWith (Real.toNNReal (‖v‖ + δ)) γ A := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    simpa only [Real.coe_toNNReal _ hb] using (hV x (hAV hx) y (hAV hy)).2
  have hAnti : AntilipschitzWith (Real.toNNReal (‖v‖ - δ))⁻¹ (fun x : V => γ x) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖(x : ℝ) - y‖ ≤ _ * ‖γ x - γ y‖
    rw [NNReal.coe_inv, Real.coe_toNNReal _ ha.le]
    exact (le_inv_mul_iff₀ ha).mpr (by simpa [mul_comm] using (hV x x.2 y y.2).1)
  constructor
  · simpa only [ENNReal.rpow_one, hausdorffMeasure_real, ENNReal.ofReal] using
      hLip.hausdorffMeasure_image_le (d := 1) (by norm_num)
  · have H := hAnti.le_hausdorffMeasure_image (d := 1) (by norm_num)
      ((Subtype.val : V → ℝ) ⁻¹' A)
    have himage : (fun x : V => γ x) '' ((Subtype.val : V → ℝ) ⁻¹' A) = γ '' A := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hAV hx⟩, hx, rfl⟩
    have hsource : (μH[1] : Measure V) ((Subtype.val : V → ℝ) ⁻¹' A) = volume A := by
      rw [← isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num))]
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hAV, hausdorffMeasure_real]
    rw [himage, hsource, ENNReal.rpow_one, ENNReal.coe_inv (by positivity)] at H
    have hne : (Real.toNNReal (‖v‖ - δ) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]; exact ha
    have htop : (Real.toNNReal (‖v‖ - δ) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    have HH := mul_le_mul (le_refl (Real.toNNReal (‖v‖ - δ) : ℝ≥0∞)) H (by positivity) (by positivity)
    simpa only [← mul_assoc, ENNReal.mul_inv_cancel hne htop, one_mul, ENNReal.ofReal] using HH


/-- A local comparison with any prescribed multiplicative error greater than one. -/
theorem local_speed_comparison {γ : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ 1 γ U) {t : ℝ} (ht : t ∈ U) (hv : deriv γ t ≠ 0)
    {c : ℝ} (hc : 1 < c) :
    ∃ (V : Set ℝ) (a b : ℝ), IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧ 0 < a ∧
      b ≤ c * a ∧ (∀ x ∈ V, a ≤ ‖deriv γ x‖ ∧ ‖deriv γ x‖ ≤ b) ∧
      ∀ A ⊆ V,
        (μH[1] : Measure ℂ) (γ '' A) ≤ ENNReal.ofReal b * volume A ∧
        ENNReal.ofReal a * volume A ≤ (μH[1] : Measure ℂ) (γ '' A) := by
  have hvpos : 0 < ‖deriv γ t‖ := norm_pos_iff.mpr hv
  let d : ℝ := (c - 1) * ‖deriv γ t‖ / (2 * c + 2)
  have hden : 0 < 2 * c + 2 := by linarith
  have hdpos : 0 < d := div_pos (mul_pos (by linarith) hvpos) hden
  have hdmul : d * (2 * c + 2) = (c - 1) * ‖deriv γ t‖ :=
    div_mul_cancel₀ _ hden.ne'
  have hdlt : d < ‖deriv γ t‖ := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  let δ : ℝ≥0 := ⟨d, hdpos.le⟩
  obtain ⟨W, hWo, htW, hW⟩ := local_hausdorff_bounds
    ((hγ.contDiffAt (hU.mem_nhds ht)).hasStrictDerivAt (by norm_num))
    (δ := δ) hdpos hdlt
  have hscont : ContinuousAt (fun x => ‖deriv γ x‖) t :=
    ((hγ.continuousOn_deriv_of_isOpen hU (by norm_num)).continuousAt
      (hU.mem_nhds ht)).norm
  have hN : {x | |‖deriv γ x‖ - ‖deriv γ t‖| < d} ∈ 𝓝 t := by
    simpa only [ball, Real.dist_eq, preimage_ofPred_eq] using hscont.preimage_mem_nhds (ball_mem_nhds _ hdpos)
  obtain ⟨N, hNsub, hNo, htN⟩ := _root_.mem_nhds_iff.mp hN
  refine ⟨W ∩ N ∩ U, ‖deriv γ t‖ - d, ‖deriv γ t‖ + d,
    (hWo.inter hNo).inter hU, ⟨⟨htW, htN⟩, ht⟩, inter_subset_right,
    sub_pos.mpr hdlt, ?_, ?_, ?_⟩
  · nlinarith
  · intro x hx
    have := abs_lt.mp (show |‖deriv γ x‖ - ‖deriv γ t‖| < d from hNsub hx.1.2)
    constructor <;> linarith
  · intro A hA
    exact hW A (hA.trans (inter_subset_left.trans inter_subset_left))

/-- A countable disjoint Borel refinement of any open cover carrying a
hereditary property. The source itself need not be measurable. -/
theorem measurable_partition_of_local {s : Set ℝ} {P : Set ℝ → Prop}
    (hempty : P ∅) (hmono : ∀ {A B}, A ⊆ B → P B → P A)
    (hlocal : ∀ x ∈ s, ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧ P V) :
    ∃ Q : ℕ → Set ℝ, (∀ n, MeasurableSet (Q n)) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧ s ⊆ ⋃ n, Q n ∧ (∀ n, P (Q n)) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, ?_, by simp, fun _ => hempty⟩
    intro i j hij; simp
  let : Nonempty s := hs.to_subtype
  choose V hVo hxV hV using fun x : s => hlocal x x.2
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover V hVo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  refine ⟨disjointed (fun n => V (f n)), ?_, disjoint_disjointed _, ?_, ?_⟩
  · intro n
    exact MeasurableSet.disjointed (fun n => (hVo (f n)).measurableSet) n
  · simpa only [iUnion_disjointed] using hf
  · intro n
    exact hmono (disjointed_subset _ _) (hV (f n))

/-- C1 maps send null subsets of their regular locus to H1-null subsets.
The parameter set may be non-Borel, and need not be bounded. -/
theorem hausdorff_null_image {γ : ℝ → ℂ} {U s : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ 1 γ U) (hsU : s ⊆ U) (hv : ∀ t ∈ s, deriv γ t ≠ 0)
    (hs : volume s = 0) : (μH[1] : Measure ℂ) (γ '' s) = 0 := by
  let P : Set ℝ → Prop := fun V => ∃ b : ℝ, ∀ A ⊆ V,
    (μH[1] : Measure ℂ) (γ '' A) ≤ ENNReal.ofReal b * volume A
  obtain ⟨Q, hQm, hQd, hQs, hQ⟩ := measurable_partition_of_local (s := s) (P := P)
    ⟨0, by intro A hA; have : A = ∅ := subset_empty_iff.mp hA; simp [this]⟩
    (fun hAB ⟨b, hb⟩ => ⟨b, fun A hA => hb A (hA.trans hAB)⟩) (by
      intro t ht
      obtain ⟨V, a, b, hVo, htV, -, -, -, -, hV⟩ :=
        local_speed_comparison hU hγ (hsU ht) (hv t ht) (c := 2) (by norm_num)
      exact ⟨V, hVo, htV, b, fun A hA => (hV A hA).1⟩)
  have hcover : s = ⋃ n, s ∩ Q n := by
    rw [← inter_iUnion, inter_eq_self_of_subset_left hQs]
  apply le_antisymm _ bot_le
  calc
    (μH[1] : Measure ℂ) (γ '' s) = (μH[1] : Measure ℂ) (⋃ n, γ '' (s ∩ Q n)) := by
      congr 1; conv_lhs => rw [hcover, image_iUnion]
    _ ≤ ∑' n, (μH[1] : Measure ℂ) (γ '' (s ∩ Q n)) := measure_iUnion_le _
    _ = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro n
      obtain ⟨b, hb⟩ := hQ n
      have hz : volume (s ∩ Q n) = 0 := measure_mono_null inter_subset_left hs
      exact le_antisymm (by simpa only [hz, mul_zero] using hb (s ∩ Q n) inter_subset_right)
        bot_le


/-- On Borel restrictions, the Hausdorff measure and the speed integral
approximate each other with arbitrarily small multiplicative error. -/
theorem image_area_comparison {γ : ℝ → ℂ} {U s : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ 1 γ U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn γ s) (hv : ∀ t ∈ s, deriv γ t ≠ 0)
    {c : ℝ≥0} (hc : 1 < c) :
    (μH[1] : Measure ℂ) (γ '' s) ≤ c * (∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖) ∧
    (∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖) ≤ c * (μH[1] : Measure ℂ) (γ '' s) := by
  let P : Set ℝ → Prop := fun V => ∀ A ⊆ V, MeasurableSet A →
    (μH[1] : Measure ℂ) (γ '' A) ≤ c * (∫⁻ t in A, ENNReal.ofReal ‖deriv γ t‖) ∧
    (∫⁻ t in A, ENNReal.ofReal ‖deriv γ t‖) ≤ c * (μH[1] : Measure ℂ) (γ '' A)
  obtain ⟨Q, hQm, hQd, hQs, hQ⟩ := measurable_partition_of_local (s := s) (P := P)
    (by intro A hA hAm; have : A = ∅ := subset_empty_iff.mp hA; simp [this])
    (fun hAB hB A hA => hB A (hA.trans hAB)) (by
      intro t ht
      obtain ⟨V, a, b, hVo, htV, hVU, ha, hba, hspeed, hV⟩ :=
        local_speed_comparison hU hγ (hsU ht) (hv t ht) hc
      refine ⟨V, hVo, htV, ?_⟩
      intro A hA hAm
      have hlow : ENNReal.ofReal a * volume A ≤ ∫⁻ t in A, ENNReal.ofReal ‖deriv γ t‖ := by
        rw [← setLIntegral_const]
        exact setLIntegral_mono' hAm fun x hx => ENNReal.ofReal_le_ofReal (hspeed x (hA hx)).1
      have hupp : (∫⁻ t in A, ENNReal.ofReal ‖deriv γ t‖) ≤ ENNReal.ofReal b * volume A := by
        rw [← setLIntegral_const]
        exact setLIntegral_mono' hAm fun x hx => ENNReal.ofReal_le_ofReal (hspeed x (hA hx)).2
      have hba' : ENNReal.ofReal b ≤ (c : ℝ≥0∞) * ENNReal.ofReal a := by
        calc
          ENNReal.ofReal b ≤ ENNReal.ofReal ((c : ℝ) * a) := ENNReal.ofReal_le_ofReal hba
          _ = c * ENNReal.ofReal a := by
            rw [ENNReal.ofReal_mul (p := (c : ℝ)) (q := a) c.2, ENNReal.ofReal_coe_nnreal]
      have hcoeff : ENNReal.ofReal b * volume A ≤ c * (ENNReal.ofReal a * volume A) := by
        rw [← mul_assoc]
        gcongr
      constructor
      · exact (hV A hA).1.trans (hcoeff.trans (by gcongr))
      · exact hupp.trans (hcoeff.trans (by gcongr; exact (hV A hA).2)))
  have hcover : s = ⋃ n, s ∩ Q n := by
    rw [← inter_iUnion, inter_eq_self_of_subset_left hQs]
  have hpartm : ∀ n, MeasurableSet (s ∩ Q n) := fun n => hs.inter (hQm n)
  have hpartd : Pairwise (fun i j => Disjoint (s ∩ Q i) (s ∩ Q j)) :=
    pairwise_disjoint_mono hQd fun _ => inter_subset_right
  have hImagem : ∀ n, MeasurableSet (γ '' (s ∩ Q n)) := fun n =>
    (hpartm n).image_of_continuousOn_injOn
      (hγ.continuousOn.mono (inter_subset_left.trans hsU)) (hinj.mono inter_subset_left)
  have hImaged : Pairwise (fun i j => Disjoint (γ '' (s ∩ Q i)) (γ '' (s ∩ Q j))) := by
    intro i j hij
    exact Disjoint.image (hpartd hij) hinj inter_subset_left inter_subset_left
  have hsumH : (μH[1] : Measure ℂ) (γ '' s) =
      ∑' n, (μH[1] : Measure ℂ) (γ '' (s ∩ Q n)) := by
    conv_lhs => rw [hcover, image_iUnion]
    exact measure_iUnion hImaged hImagem
  have hsumI : (∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖) =
      ∑' n, ∫⁻ t in s ∩ Q n, ENNReal.ofReal ‖deriv γ t‖ := by
    conv_lhs => rw [hcover]
    exact lintegral_iUnion hpartm hpartd _
  constructor
  · rw [hsumH, hsumI, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n => (hQ n (s ∩ Q n) inter_subset_right (hpartm n)).1
  · rw [hsumH, hsumI, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n => (hQ n (s ∩ Q n) inter_subset_right (hpartm n)).2

/-- The injective C1 area formula for Borel source sets. No compactness,
boundedness, or finiteness of either side is required. -/
theorem image_area_of_measurableSet {γ : ℝ → ℂ} {U s : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ 1 γ U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hinj : InjOn γ s) (hv : ∀ t ∈ s, deriv γ t ≠ 0) :
    MeasurableSet (γ '' s) ∧ (μH[1] : Measure ℂ) (γ '' s) =
      ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖ := by
  refine ⟨hs.image_of_continuousOn_injOn (hγ.continuousOn.mono hsU) hinj, ?_⟩
  have squeeze (X Y : ℝ≥0∞) (h : ∀ c : ℝ≥0, 1 < c → X ≤ c * Y) : X ≤ Y := by
    have hlim : Tendsto (fun c : ℝ≥0 => (c : ℝ≥0∞) * Y) (𝓝[>] 1) (𝓝 Y) := by
      have H : Tendsto (fun c : ℝ≥0 => (c : ℝ≥0∞) * Y) (𝓝 1) (𝓝 ((1 : ℝ≥0∞) * Y)) := by
        apply ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.mpr tendsto_id)
        exact Or.inl (by norm_num)
      simpa only [one_mul] using H.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact h c hc
  exact le_antisymm
    (squeeze _ _ fun c hc => (image_area_comparison hU hγ hs hsU hinj hv hc).1)
    (squeeze _ _ fun c hc => (image_area_comparison hU hγ hs hsU hinj hv hc).2)


/-- Completed Lebesgue measurable restrictions satisfy the same formula. The
null remainder is sent to an H1-null set, so its image is null measurable. -/
theorem image_area_of_nullMeasurableSet {γ : ℝ → ℂ} {U s : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ 1 γ U) (hs : NullMeasurableSet s volume) (hsU : s ⊆ U)
    (hinj : InjOn γ s) (hv : ∀ t ∈ s, deriv γ t ≠ 0) :
    NullMeasurableSet (γ '' s) (μH[1] : Measure ℂ) ∧
      (μH[1] : Measure ℂ) (γ '' s) = ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖ := by
  obtain ⟨B, hBs, hBm, hBae⟩ := hs.exists_measurable_subset_ae_eq
  have hnull : (μH[1] : Measure ℂ) (γ '' (s \ B)) = 0 :=
    hausdorff_null_image hU hγ (sdiff_subset.trans hsU)
      (fun t ht => hv t ht.1) (ae_eq_set.mp hBae).2
  have hImgAE : γ '' s =ᵐ[μH[1]] γ '' B := by
    have hsplit : s = B ∪ (s \ B) := by simp [union_eq_self_of_subset_left hBs]
    rw [hsplit, image_union]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hnull)
  have hB := image_area_of_measurableSet hU hγ hBm (hBs.trans hsU)
    (hinj.mono hBs) (fun t ht => hv t (hBs ht))
  refine ⟨hB.1.nullMeasurableSet.congr hImgAE.symm, ?_⟩
  rw [measure_congr hImgAE, hB.2]
  exact setLIntegral_congr hBae

/-- The requested bounded-set specialization; the stronger theorem above
also covers unbounded parameter sets and infinite integrals. -/
theorem image_area : Specs.D12Complex.Ch04.InjectiveCurveArea.image_area_type := by
  intro γ U s hU hγ _hbounded hs hsU hinj hv
  exact image_area_of_nullMeasurableSet hU hγ hs hsU hinj hv

/-- The actual pushforward measure identity. Continuity is required only on
U; no measurability of arbitrary exterior values of the curve is asserted. -/
theorem map_weighted_volume_of_nullMeasurableSet {γ : ℝ → ℂ} {U s : Set ℝ}
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U) (hs : NullMeasurableSet s volume)
    (hsU : s ⊆ U) (hinj : InjOn γ s) (hv : ∀ t ∈ s, deriv γ t ≠ 0) :
    AEMeasurable γ ((volume.restrict s).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)) ∧
      Measure.map γ ((volume.restrict s).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)) =
        (μH[1] : Measure ℂ).restrict (γ '' s) := by
  have hmeas : AEMeasurable γ (volume.restrict s) :=
    (hγ.continuousOn.mono hsU).aemeasurable₀ hs
  have hweighted : AEMeasurable γ
      ((volume.restrict s).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)) :=
    hmeas.mono_ac (withDensity_absolutelyContinuous _ _)
  refine ⟨hweighted, Measure.ext fun T hT => ?_⟩
  have hpre : NullMeasurableSet (γ ⁻¹' T) (volume.restrict s) :=
    hmeas.nullMeasurableSet_preimage hT
  rw [map_apply_of_aemeasurable hweighted hT, withDensity_apply₀ _ hpre,
    Measure.restrict_apply hT, restrict_restrict₀ hpre]
  rw [← (image_area_of_nullMeasurableSet hU hγ
    ((nullMeasurableSet_restrict hs).mp hpre) (inter_subset_right.trans hsU)
    (hinj.mono inter_subset_right) (fun t ht => hv t ht.2)).2, image_preimage_inter]

theorem map_weighted_volume : Specs.D12Complex.Ch04.InjectiveCurveArea.map_weighted_volume_type := by
  intro γ U s hU hγ _hbounded hs hsU hinj hv
  exact map_weighted_volume_of_nullMeasurableSet hU hγ hs hsU hinj hv

end D12Complex.Ch04.InjectiveCurveArea
