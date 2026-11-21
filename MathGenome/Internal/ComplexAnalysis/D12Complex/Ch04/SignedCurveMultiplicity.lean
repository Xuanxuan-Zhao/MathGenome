import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.InjectiveCurveArea
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.CountableFiberTransport
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.SignedCurveMultiplicity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal
namespace D12Complex.SignedCurveMultiplicity

/- Implementation-owned exports of the canonical objects shared with the independent Specs.
The canonical definitions stay in the Specs so that expected theorem types are independent
of this implementation. These aliases provide candidate-owned definition/value targets. -/
namespace Definitions

abbrev regularFiber := D12Complex.SignedCurveMultiplicity.regularFiber
abbrev unitVelocity := D12Complex.SignedCurveMultiplicity.unitVelocity
abbrev multiplicity := D12Complex.SignedCurveMultiplicity.multiplicity
abbrev signedDensity := D12Complex.SignedCurveMultiplicity.signedDensity
abbrev pathDensity := D12Complex.SignedCurveMultiplicity.pathDensity
abbrev chainDensity := D12Complex.SignedCurveMultiplicity.chainDensity
abbrev chainMultiplicity := D12Complex.SignedCurveMultiplicity.chainMultiplicity

end Definitions

local instance : NullSingletonClass (μH[1] : Measure ℂ) :=
  MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ zero_lt_one

theorem regularFiber_countable :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.regularFiber_countable_type := by
  intro γ s z
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  rw [isDiscrete_iff_nhdsNE]
  intro t ht
  have hdiff : DifferentiableAt ℝ γ t := differentiableAt_of_deriv_ne_zero ht.2.2
  have hne : ∀ᶠ u in 𝓝[≠] t, γ u ≠ z := hdiff.hasDerivAt.eventually_ne ht.2.2
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [hne] with u hu
  exact fun h => hu h.2.1

theorem ae_velocity_zero_on_countable_image :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.ae_velocity_zero_on_countable_image_type := by
  intro γ S hS
  have hbad : {t | γ t ∈ S ∧ deriv γ t ≠ 0}.Countable := by
    apply (hS.biUnion fun z _ => regularFiber_countable γ univ z).mono
    intro t ht
    exact mem_iUnion₂.mpr ⟨γ t, ht.1, mem_univ _, rfl, ht.2⟩
  have hae : ∀ᵐ t ∂volume, t ∉ {t | γ t ∈ S ∧ deriv γ t ≠ 0} :=
    (ae_iff).2 (by simpa using hbad.measure_zero volume)
  filter_upwards [hae] with t ht hmem
  by_contra hne
  exact ht ⟨hmem, hne⟩

theorem norm_unitVelocity :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.norm_unitVelocity_type := by
  intro γ t ht
  simp [unitVelocity, Complex.norm_real, norm_ne_zero_iff.mpr ht]

theorem unitVelocity_mul_speed :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.unitVelocity_mul_speed_type := by
  intro γ t
  by_cases ht : deriv γ t = 0
  · simp [unitVelocity, ht]
  · exact div_mul_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr ht)

theorem norm_summable_iff_finite :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.norm_summable_iff_finite_type := by
  intro γ s z
  have heq : (fun t : regularFiber γ s z => ‖unitVelocity γ t‖) = fun _ => (1 : ℝ) := by
    funext t
    exact norm_unitVelocity γ t t.property.2.2
  rw [heq]
  constructor
  · intro hs
    have : Finite (regularFiber γ s z) := Finite.of_summable_const zero_lt_one hs
    exact Set.toFinite _
  · intro hs
    let := hs.fintype
    exact (hasSum_fintype _).summable

theorem density_off_image :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.density_off_image_type := by
  intro γ s z hz
  have he : regularFiber γ s z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact hz ⟨t, ht.1, ht.2.1⟩
  simp [signedDensity, he]

theorem density_off_trace :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.density_off_trace_type := by
  intro γ z hz
  apply density_off_image
  exact fun ⟨t, ht, he⟩ => hz ⟨t, ⟨ht.1.le, ht.2.le⟩, he⟩

theorem contour_integral_off_countable :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.contour_integral_off_countable_type := by
  classical
  intro γ q hq S hS
  rw [PiecewiseC1Path.integral, C1Partition.integral_eq_intervalIntegral _ _ _ hq]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_velocity_zero_on_countable_image γ S hS] with t ht
  intro _
  by_cases hmem : γ t ∈ S
  · simp [hmem, ht hmem]
  · simp [hmem]

theorem hausdorff_real_normalization :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_real_normalization_type :=
  MeasureTheory.hausdorffMeasure_real

theorem hausdorff_complex_segment :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_complex_segment_type := by
  intro z w
  exact MeasureTheory.hausdorffMeasure_segment z w

theorem hausdorff_scalar_isometry :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_scalar_isometry_type := by
  intro E _ _ _ e he s
  simpa using he.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) s

theorem summable_iff_finite :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.summable_iff_finite_type := by
  intro γ s z
  rw [← summable_norm_iff]
  exact norm_summable_iff_finite γ s z

theorem hausdorff_e1_coordinates :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_e1_coordinates_type := by
  intro s
  have he : (fun t : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => t)) =
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr := by
    funext t
    ext i
    simp
  rw [he]
  exact hausdorff_scalar_isometry _
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.isometry s

theorem local_injective_at_nonstationary :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.local_injective_at_nonstationary_type := by
  intro γ U hU hγ t ht hvel
  obtain ⟨L, hL⟩ : ∃ L : ℂ →L[ℝ] ℝ, L (deriv γ t) ≠ 0 := by
    by_cases hre : (deriv γ t).re = 0
    · refine ⟨Complex.imCLM, ?_⟩
      intro him
      apply hvel
      exact Complex.ext hre him
    · exact ⟨Complex.reCLM, hre⟩
  have hd : HasStrictDerivAt γ (deriv γ t) t :=
    (hγ.contDiffAt (hU.mem_nhds ht)).hasStrictDerivAt one_ne_zero
  have hp : HasStrictDerivAt (fun u => L (γ u)) (L (deriv γ t)) t :=
    L.hasStrictFDerivAt.comp_hasStrictDerivAt t hd
  have hleft := hp.eventually_left_inverse hL
  obtain ⟨V, hV, hVo, htV⟩ := mem_nhds_iff.mp hleft
  refine ⟨U ∩ V, hU.inter hVo, ⟨ht, htV⟩, inter_subset_left, ?_⟩
  intro x hx y hy hxy
  calc x = hp.localInverse _ _ _ hL (L (γ x)) := (hV hx.2).symm
       _ = hp.localInverse _ _ _ hL (L (γ y)) := by rw [hxy]
       _ = y := hV hy.2

theorem countable_injective_cover :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.countable_injective_cover_type := by
  classical
  intro γ U hU hγ
  let R := {t | t ∈ U ∧ deriv γ t ≠ 0}
  have hlocal : ∀ t : R, ∃ V : Set ℝ,
      IsOpen V ∧ (t : ℝ) ∈ V ∧ V ⊆ U ∧ Set.InjOn γ V :=
    fun t => local_injective_at_nonstationary γ U hU hγ t t.property.1 t.property.2
  choose V hVo htV hVU hVi using hlocal
  obtain ⟨I, hI, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  refine ⟨V '' I, hI.image V, ?_, ?_⟩
  · rintro W ⟨t, _, rfl⟩
    exact ⟨hVo t, hVU t, hVi t⟩
  · intro t ht
    have hm : t ∈ ⋃ r : R, V r := mem_iUnion.mpr ⟨⟨t, ht⟩, htV ⟨t, ht⟩⟩
    rw [← hcover] at hm
    obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp hm
    exact mem_sUnion.mpr ⟨V r, ⟨r, hr, rfl⟩, htr⟩

theorem hausdorff_c1_image_finite :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_c1_image_finite_type := by
  intro γ a b hγ
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  have hb := hK.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
  rw [ENNReal.rpow_one, MeasureTheory.hausdorffMeasure_real] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top isCompact_Icc.measure_lt_top)

/-- A finite node list covers its full interval, including a zero-piece list. -/
private theorem interval_nodes_cover : ∀ (n : ℕ) (v : Fin (n + 1) → ℝ),
    Monotone v → ∀ t ∈ Icc (v 0) (v (Fin.last n)),
    t = v 0 ∨ ∃ i : Fin n, t ∈ Icc (v i.castSucc) (v i.succ) := by
  intro n
  induction n with
  | zero =>
    intro v _ t ht
    exact Or.inl (le_antisymm ht.2 ht.1)
  | succ n ih =>
    intro v hv t ht
    by_cases hle : t ≤ v (Fin.succ 0)
    · exact Or.inr ⟨0, ht.1, hle⟩
    · have hh := ih (fun i => v i.succ) (fun _ _ h => hv (by simpa using h)) t
        ⟨(not_le.mp hle).le, ht.2⟩
      rcases hh with he | ⟨i, hi⟩
      · exact (hle (he.le)).elim
      · exact Or.inr ⟨i.succ, by simpa only [Fin.succ_castSucc] using hi⟩

theorem hausdorff_path_trace_finite :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_path_trace_finite_type := by
  intro γ
  let P := γ.partition
  have hc : γ.trace ⊆ {γ γ.path.a} ∪ ⋃ i : Fin P.count, γ '' P.pieceSet i := by
    rintro z ⟨t, ht, rfl⟩
    have htp : t ∈ Icc (P.node 0) (P.node (Fin.last P.count)) := by
      simpa only [P.first, P.last] using ht
    rcases interval_nodes_cover P.count P.node P.strictMono.monotone t htp with h | ⟨i, hi⟩
    · exact Or.inl (by simp [h, P.first])
    · exact Or.inr (mem_iUnion.mpr ⟨i, ⟨t, hi, rfl⟩⟩)
  have hpiece (i : Fin P.count) :
      (μH[1] : Measure ℂ) (γ '' P.pieceSet i) < ∞ :=
    hausdorff_c1_image_finite γ _ _ (P.smooth i)
  have hsum : (∑' i : Fin P.count, (μH[1] : Measure ℂ) (γ '' P.pieceSet i)) < ∞ := by
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.mpr (fun i _ => hpiece i)
  exact ((measure_mono hc).trans (measure_union_le _ _)).trans_lt (by
    simpa using (measure_iUnion_le (fun i : Fin P.count => γ '' P.pieceSet i)).trans_lt hsum)

theorem path_speed_integrable :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.path_speed_integrable_type := by
  intro γ
  have hi : IntervalIntegrable (fun t => deriv γ t) volume γ.path.a γ.path.b := by
    simpa using C1Partition.parameter_integrable γ.path γ.partition (fun _ => 1)
      continuousOn_const
  exact hi.norm.1.mono_set Ioo_subset_Ioc_self

theorem hausdorff_chain_trace_finite :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_chain_trace_finite_type := by
  intro Γ
  have hc : Γ.trace = ⋃ γ ∈ Γ.support, γ.trace := by
    ext z
    simp [IntegralChain.trace]
  rw [hc]
  exact measure_biUnion_lt_top Γ.support.finite_toSet
    (fun γ _ => hausdorff_path_trace_finite γ)

theorem chainDensity_off_trace :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.chainDensity_off_trace_type := by
  intro Γ z hz
  apply Finset.sum_eq_zero
  intro γ hγ
  have hnot : z ∉ γ.trace := fun h => hz
    ((IntegralChain.mem_trace_iff Γ z).mpr ⟨γ, Finsupp.mem_support_iff.mp hγ, h⟩)
  rw [density_off_trace γ z hnot, mul_zero]

theorem density_remove_countable :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.density_remove_countable_type := by
  intro γ s S hS
  have hae : ∀ᵐ z ∂(μH[1] : Measure ℂ), z ∉ S :=
    (ae_iff).mpr (by simpa using hS.measure_zero (μH[1] : Measure ℂ))
  filter_upwards [hae] with z hz
  have hf : regularFiber γ (s \ γ ⁻¹' S) z = regularFiber γ s z := by
    ext t
    simp only [regularFiber, mem_ofPred_eq, Set.mem_sdiff, mem_preimage]
    constructor
    · rintro ⟨⟨ht, _⟩, he, hd⟩
      exact ⟨ht, he, hd⟩
    · rintro ⟨ht, he, hd⟩
      exact ⟨⟨ht, by simpa only [he] using hz⟩, he, hd⟩
  exact (Set.equivOfEq hf).tsum_eq (fun t : regularFiber γ s z => unitVelocity γ t)

theorem hausdorff_c1_image_null :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.hausdorff_c1_image_null_type := by
  intro γ a b hγ s hs
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  have hb := (hK.mono (inter_subset_right (s := s) (t := Icc a b))).hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ) ≤ 1)
  have hsource : (μH[1] : Measure ℝ) (s ∩ Icc a b) = 0 := by
    rw [MeasureTheory.hausdorffMeasure_real]
    exact measure_mono_null inter_subset_left hs
  rw [hsource, mul_zero] at hb
  exact le_antisymm hb bot_le

theorem multiplicity_lt_top_iff :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.multiplicity_lt_top_iff_type := by
  intro γ s z
  simp [multiplicity]

theorem density_norm_le_multiplicity :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.density_norm_le_multiplicity_type := by
  intro γ s z hf
  let := hf.fintype
  have hm : multiplicity γ s z = (Fintype.card (regularFiber γ s z) : ℝ≥0∞) := by
    exact (congrArg (fun n : ℕ∞ => (n : ℝ≥0∞))
      (Set.coe_fintypeCard (regularFiber γ s z)).symm).trans (ENat.toENNReal_coe _)
  have hn : ∀ t : regularFiber γ s z, ‖unitVelocity γ t‖ = 1 :=
    fun t => norm_unitVelocity γ t t.property.2.2
  have hb := norm_tsum_le_tsum_norm ((norm_summable_iff_finite γ s z).mpr hf)
  simp_rw [hn] at hb
  simpa [signedDensity, hm, tsum_fintype] using hb

theorem regularFiber_congr :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.regularFiber_congr_type := by
  intro γ η s hs he z
  ext t
  by_cases ht : t ∈ s
  · have hd : deriv γ t = deriv η t :=
      he.deriv hs ht
    simp only [regularFiber, mem_ofPred_eq, ht, he ht, hd]
  · simp [regularFiber, ht]

theorem density_congr :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.density_congr_type := by
  intro γ η s hs he
  funext z
  have hf := regularFiber_congr γ η s hs he z
  have hvel (t : regularFiber γ s z) : unitVelocity γ t = unitVelocity η t := by
    have hd : deriv γ t = deriv η t :=
      he.deriv hs t.property.1
    simp only [unitVelocity, hd]
  exact (tsum_congr hvel).trans
    ((Set.equivOfEq hf).tsum_eq (fun t : regularFiber η s z => unitVelocity η t))

theorem stationary_density_zero :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.stationary_density_zero_type := by
  intro γ s hvel
  funext z
  have he : regularFiber γ s z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact ht.2.2 (hvel t ht.1)
  simp [signedDensity, he]

theorem degenerate_path_pushforward :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.degenerate_path_pushforward_type := by
  intro γ hab q
  have he : pathDensity γ = 0 := by
    apply stationary_density_zero
    intro t ht
    exact (lt_irrefl γ.path.b ((hab ▸ ht.1).trans ht.2)).elim
  simp only [he, Pi.zero_apply, mul_zero]
  exact ⟨integrable_zero _ _ _, by simpa using γ.integral_degenerate hab q⟩

theorem constant_path_pushforward :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.constant_path_pushforward_type := by
  intro a b hab z q
  have he : pathDensity (PiecewiseC1Path.const a b hab z) = 0 := by
    apply stationary_density_zero
    intro t _
    exact deriv_const _ _
  simp only [he, Pi.zero_apply, mul_zero]
  exact ⟨integrable_zero _ _ _, by simpa using PiecewiseC1Path.const_integral a b hab z q⟩

/-- Strict differentiation controls all chords in one neighborhood, including
chords with neither endpoint equal to the base point. -/
theorem strict_deriv_distortion (γ : ℝ → ℂ) (v : ℂ) (t : ℝ)
    (hd : HasStrictDerivAt γ v t) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∀ x ∈ V, ∀ y ∈ V,
        (‖v‖ - ε) * ‖x - y‖ ≤ ‖γ x - γ y‖ ∧
        ‖γ x - γ y‖ ≤ (‖v‖ + ε) * ‖x - y‖ := by
  obtain ⟨S, hS, happrox⟩ :=
    hd.hasStrictFDerivAt.approximates_deriv_on_nhds (Or.inr hε)
  obtain ⟨V, hVS, hVo, htV⟩ := mem_nhds_iff.mp hS
  refine ⟨V, hVo, htV, ?_⟩
  intro x hx y hy
  have hb : ‖γ x - γ y - (x - y) • v‖ ≤ (ε : ℝ) * ‖x - y‖ :=
    happrox x (hVS hx) y (hVS hy)
  have hv : ‖(x - y) • v‖ = ‖v‖ * ‖x - y‖ := by
    rw [norm_smul, mul_comm]
  have hlo := norm_sub_norm_le ((x - y) • v) (γ x - γ y)
  have hre := norm_sub_rev ((x - y) • v) (γ x - γ y)
  rw [hre] at hlo
  have hhi := norm_sub_norm_le (γ x - γ y) ((x - y) • v)
  rw [hv] at hlo hhi
  constructor <;> nlinarith

/-- Sharp local Hausdorff upper and lower estimates, for EVERY subset of a
small neighborhood, without a measurability assumption on that subset. -/
theorem local_hausdorff_bounds (γ : ℝ → ℂ) (v : ℂ) (t : ℝ)
    (hd : HasStrictDerivAt γ v t) (ε : ℝ≥0) (hε : 0 < ε)
    (hsmall : (ε : ℝ) < ‖v‖) :
    ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧ Set.InjOn γ V ∧
      ∀ A ⊆ V,
        (μH[1] : Measure ℂ) (γ '' A) ≤ (‖v‖₊ + ε : ℝ≥0) * volume A ∧
        volume A ≤ (((Real.toNNReal (‖v‖ - ε))⁻¹ : ℝ≥0) : ℝ≥0∞) *
          (μH[1] : Measure ℂ) (γ '' A) := by
  obtain ⟨V, hVo, htV, hdist⟩ := strict_deriv_distortion γ v t hd ε hε
  let c : ℝ≥0 := Real.toNNReal (‖v‖ - ε)
  have hcval : (c : ℝ) = ‖v‖ - ε := Real.coe_toNNReal _ (sub_nonneg.mpr hsmall.le)
  have hc : 0 < (c : ℝ) := hcval ▸ sub_pos.mpr hsmall
  have hanti : AntilipschitzWith c⁻¹ (fun x : V => γ x) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simp only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_inv]
    change ‖(x : ℝ) - (y : ℝ)‖ ≤ (c : ℝ)⁻¹ * ‖γ x - γ y‖
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    simpa only [hcval, mul_comm] using
      (hdist x x.property y y.property).1
  have hlip : LipschitzOnWith (‖v‖₊ + ε) γ V := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro x hx y hy
    exact (hdist x hx y hy).2
  refine ⟨V, hVo, htV, ?_, ?_⟩
  · intro x hx y hy he
    exact congrArg Subtype.val (hanti.injective (show γ (⟨x, hx⟩ : V) =
      γ (⟨y, hy⟩ : V) from he))
  · intro A hAV
    constructor
    · simpa only [ENNReal.rpow_one, MeasureTheory.hausdorffMeasure_real] using
        (hlip.mono hAV).hausdorffMeasure_image_le zero_le_one
    · let B : Set V := Subtype.val ⁻¹' A
      have hB : Subtype.val '' B = A := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hAV hx⟩, hx, rfl⟩
      have hγB : (fun x : V => γ x) '' B = γ '' A := by
        rw [← hB, Set.image_image]
      have hvol : (μH[1] : Measure V) B = volume A := by
        rw [← (isometry_subtype_coe : Isometry (Subtype.val : V → ℝ)).hausdorffMeasure_image
          (Or.inl zero_le_one) B, hB, MeasureTheory.hausdorffMeasure_real]
      simpa only [ENNReal.rpow_one, hγB, hvol] using
        hanti.le_hausdorffMeasure_image zero_le_one B

/-- A disjoint Borel partition counts each original nonstationary parameter
exactly once. Images of its pieces are Borel; the images need not be disjoint. -/
theorem countable_injective_partition (γ : ℝ → ℂ) (U : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U) :
    ∃ P : ℕ → Set ℝ,
      (∀ n, MeasurableSet (P n) ∧ P n ⊆ U ∧ Set.InjOn γ (P n) ∧
        MeasurableSet (γ '' P n)) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (⋃ n, P n) = {t | t ∈ U ∧ deriv γ t ≠ 0} := by
  classical
  let R : Set ℝ := {t | t ∈ U ∧ deriv γ t ≠ 0}
  have hRo : IsOpen R :=
    (hγ.continuousOn_deriv_of_isOpen hU le_rfl).isOpen_inter_preimage hU
      (isClosed_singleton.isOpen_compl)
  obtain ⟨C, hC, hprop, hcover⟩ := countable_injective_cover γ U hU hγ
  let V : ℕ → Set ℝ := enumerateCountable hC ∅
  have hV (n : ℕ) : IsOpen (V n) ∧ V n ⊆ U ∧ Set.InjOn γ (V n) := by
    have hn := range_enumerateCountable_subset hC ∅ (mem_range_self n)
    rcases hn with he | hn
    · simp only [V, he, isOpen_empty, empty_subset, injOn_empty, and_self]
    · exact hprop _ hn
  let W : ℕ → Set ℝ := fun n => V n ∩ R
  have hW (n : ℕ) : MeasurableSet (W n) := ((hV n).1.inter hRo).measurableSet
  have hunion : (⋃ n, W n) = R := by
    apply subset_antisymm
    · intro t ht
      obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      exact hn.2
    · intro t ht
      obtain ⟨S, hSC, htS⟩ := mem_sUnion.mp (hcover ht)
      obtain ⟨n, hn⟩ := subset_range_enumerate hC ∅ hSC
      refine mem_iUnion.mpr ⟨n, ?_⟩
      change t ∈ V n ∩ R
      rw [show V n = S from hn]
      exact ⟨htS, ht⟩
  refine ⟨disjointed W, ?_, disjoint_disjointed W, ?_⟩
  · intro n
    have hsub : disjointed W n ⊆ V n :=
      (disjointed_subset W n).trans inter_subset_left
    have hi := (hV n).2.2.mono hsub
    have hm := MeasurableSet.disjointed hW n
    exact ⟨hm, hsub.trans (hV n).2.1, hi,
      hm.image_of_continuousOn_injOn (hγ.continuousOn.mono
        (hsub.trans (hV n).2.1)) hi⟩
  · rw [iUnion_disjointed, hunion]

/-- Null-image transfer on an arbitrary open C1 domain, with no compactness,
nonstationarity, measurability, or injectivity assumption on the null subset. -/
theorem hausdorff_c1_null_image (γ : ℝ → ℂ) (U : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U) (s : Set ℝ)
    (hsU : s ⊆ U) (hs : volume s = 0) :
    (μH[1] : Measure ℂ) (γ '' s) = 0 := by
  classical
  have hlocal (t : U) : ∃ V : Set ℝ, IsOpen V ∧ (t : ℝ) ∈ V ∧
      ∃ K : ℝ≥0, LipschitzOnWith K γ V := by
    have hd := (hγ.contDiffAt (hU.mem_nhds t.property)).hasStrictDerivAt one_ne_zero
    obtain ⟨K, S, hS, hK⟩ := hd.hasStrictFDerivAt.exists_lipschitzOnWith
    obtain ⟨V, hVS, hVo, htV⟩ := mem_nhds_iff.mp hS
    exact ⟨V, hVo, htV, K, hK.mono hVS⟩
  choose V hVo htV K hK using hlocal
  obtain ⟨I, hI, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hnull (i : U) : (μH[1] : Measure ℂ) (γ '' (s ∩ V i)) = 0 := by
    have hsource : (μH[1] : Measure ℝ) (s ∩ V i) = 0 := by
      rw [MeasureTheory.hausdorffMeasure_real]
      exact measure_mono_null inter_subset_left hs
    have hb := ((hK i).mono (inter_subset_right (s := s))).hausdorffMeasure_image_le
      (show (0 : ℝ) ≤ 1 from zero_le_one)
    rw [hsource, mul_zero] at hb
    exact le_antisymm hb bot_le
  have hsub : γ '' s ⊆ ⋃ i ∈ I, γ '' (s ∩ V i) := by
    rintro z ⟨t, ht, rfl⟩
    have hm : t ∈ ⋃ i : U, V i := mem_iUnion.mpr ⟨⟨t, hsU ht⟩, htV ⟨t, hsU ht⟩⟩
    rw [← hcover] at hm
    obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp hm
    exact mem_iUnion₂.mpr ⟨i, hi, ⟨t, ⟨ht, hti⟩, rfl⟩⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hI).mpr (fun i _ => hnull i))

/-- The extended cardinality is the sum of image indicators for a disjoint
injective parameter partition. No finiteness or integral identity is assumed. -/
theorem multiplicity_partition (γ : ℝ → ℂ) (s : Set ℝ) (P : ℕ → Set ℝ)
    (hinj : ∀ n, Set.InjOn γ (P n))
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hcover : (⋃ n, P n) = {t | t ∈ s ∧ deriv γ t ≠ 0}) (z : ℂ) :
    multiplicity γ s z = ∑' n, (γ '' P n).indicator (fun _ => (1 : ℝ≥0∞)) z := by
  classical
  let Q : ℕ → Set ℝ := fun n => P n ∩ γ ⁻¹' {z}
  have hQ : regularFiber γ s z = ⋃ n, Q n := by
    ext t
    simp only [regularFiber, mem_ofPred_eq, mem_iUnion, Q, mem_inter_iff,
      mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨ht, he, hd⟩
      have hm : t ∈ ⋃ n, P n := hcover.symm ▸ ⟨ht, hd⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hm
      exact ⟨n, hn, he⟩
    · rintro ⟨n, hn, he⟩
      have hm : t ∈ {t | t ∈ s ∧ deriv γ t ≠ 0} :=
        hcover ▸ mem_iUnion.mpr ⟨n, hn⟩
      exact ⟨hm.1, he, hm.2⟩
  have hdQ : univ.PairwiseDisjoint Q := by
    intro i _ j _ hij
    exact (hdis hij).mono inter_subset_left inter_subset_left
  have hcard (n : ℕ) : (∑' _ : Q n, (1 : ℝ≥0∞)) =
      (γ '' P n).indicator (fun _ => (1 : ℝ≥0∞)) z := by
    rw [ENNReal.tsum_set_one]
    by_cases hz : z ∈ γ '' P n
    · obtain ⟨t, ht, htz⟩ := hz
      have heq : Q n = {t} := by
        ext u
        constructor
        · intro hu
          exact (hinj n hu.1 ht (hu.2.trans htz.symm))
        · rintro rfl
          exact ⟨ht, htz⟩
      simp [heq, show z ∈ γ '' P n from ⟨t, ht, htz⟩]
    · have heq : Q n = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact hz ⟨t, ht.1, ht.2⟩
      simp [heq, hz]
  calc multiplicity γ s z = ∑' _ : regularFiber γ s z, (1 : ℝ≥0∞) :=
         (ENNReal.tsum_set_one _).symm
       _ = ∑' n, ∑' _ : Q n, (1 : ℝ≥0∞) := by
         rw [hQ]
         exact ENNReal.tsum_biUnion (f := fun _ : ℝ => (1 : ℝ≥0∞)) hdQ
       _ = _ := tsum_congr hcard

/-- Borel measurability of the actual multiplicity on any Borel restriction
of an open C1 domain. This does not assert the area identity. -/
theorem measurable_multiplicity (γ : ℝ → ℂ) (U s : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) : Measurable (multiplicity γ s) := by
  classical
  obtain ⟨P, hP, hdis, hcover⟩ := countable_injective_partition γ U hU hγ
  let Q : ℕ → Set ℝ := fun n => P n ∩ s
  have hQinj (n : ℕ) : Set.InjOn γ (Q n) := (hP n).2.2.1.mono inter_subset_left
  have hQdis : Pairwise (fun i j => Disjoint (Q i) (Q j)) :=
    fun i j hij => (hdis hij).mono inter_subset_left inter_subset_left
  have hQcover : (⋃ n, Q n) = {t | t ∈ s ∧ deriv γ t ≠ 0} := by
    ext t
    simp only [Q, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨n, hn, ht⟩
      have hm := hcover ▸ mem_iUnion.mpr ⟨n, hn⟩
      exact ⟨ht, hm.2⟩
    · rintro ⟨ht, hd⟩
      have hm : t ∈ ⋃ n, P n := by
        rw [hcover]
        exact ⟨hsU ht, hd⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hm
      exact ⟨n, hn, ht⟩
  have hm (n : ℕ) : MeasurableSet (γ '' Q n) :=
    ((hP n).1.inter hs).image_of_continuousOn_injOn
      (hγ.continuousOn.mono (inter_subset_left.trans (hP n).2.1)) (hQinj n)
  have heq : multiplicity γ s = fun z =>
      ∑' n, (γ '' Q n).indicator (fun _ => (1 : ℝ≥0∞)) z :=
    funext (multiplicity_partition γ s Q hQinj hQdis hQcover)
  rw [heq]
  exact Measurable.tsum (fun n => measurable_const.indicator (hm n))

/-- Completed Lebesgue restrictions give Hausdorff-a.e. measurable actual
multiplicity, by transferring the discarded null source set to a null image. -/
theorem aemeasurable_multiplicity (γ : ℝ → ℂ) (U s : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U)
    (hs : NullMeasurableSet s volume) (hsU : s ⊆ U) :
    AEMeasurable (multiplicity γ s) (μH[1] : Measure ℂ) := by
  obtain ⟨B, hBs, hBm, hBae⟩ := hs.exists_measurable_subset_ae_eq
  have hnull : volume (s \ B) = 0 := ae_le_set.mp hBae.symm.le
  have himage : (μH[1] : Measure ℂ) (γ '' (s \ B)) = 0 :=
    hausdorff_c1_null_image γ U hU hγ _ (sdiff_subset.trans hsU) hnull
  apply (measurable_multiplicity γ U B hU hγ hBm (hBs.trans hsU)).aemeasurable.congr
  have hae : ∀ᵐ z ∂(μH[1] : Measure ℂ), z ∉ γ '' (s \ B) :=
    measure_eq_zero_iff_ae_notMem.mp himage
  filter_upwards [hae] with z hz
  have hf : regularFiber γ B z = regularFiber γ s z := by
    ext t
    constructor
    · intro ht
      exact ⟨hBs ht.1, ht.2⟩
    · intro ht
      have htB : t ∈ B := by
        by_contra hn
        exact hz ⟨t, ⟨ht.1, hn⟩, ht.2.1⟩
      exact ⟨htB, ht.2⟩
  simp only [multiplicity, hf]


/-- The genuine speed-weighted source measure, used only to apply the proved
injective area theorem. The target measure remains metric Hausdorff measure. -/
private def speedMeasure (γ : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)

private lemma transport_partition (γ : ℝ → ℂ) (U s : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    ∃ P : ℕ → Set ℝ,
      Specs.D12Complex.Ch04.CountableFiberTransport.TransportHyp γ (speedMeasure γ) μH[1] P ∧
      (⋃ n, P n) = {t | t ∈ s ∧ deriv γ t ≠ 0} := by
  classical
  obtain ⟨P, hP, hdis, hcover⟩ := countable_injective_partition γ U hU hγ
  let Q : ℕ → Set ℝ := fun n => P n ∩ s
  have hQ (n : ℕ) : Q n ⊆ U := inter_subset_left.trans (hP n).2.1
  have hQm (n : ℕ) : MeasurableSet (Q n) := (hP n).1.inter hs
  have hQi (n : ℕ) : InjOn γ (Q n) := (hP n).2.2.1.mono inter_subset_left
  have hQv (n : ℕ) : ∀ t ∈ Q n, deriv γ t ≠ 0 := by
    intro t ht
    have hm : t ∈ ⋃ n, P n := mem_iUnion.mpr ⟨n, ht.1⟩
    rw [hcover] at hm
    exact hm.2
  refine ⟨Q, ⟨hQm, fun i j hij => (hdis hij).mono inter_subset_left inter_subset_left,
    fun n => hγ.continuousOn.mono (hQ n), hQi,
    fun n => (hQm n).image_of_continuousOn_injOn (hγ.continuousOn.mono (hQ n)) (hQi n),
    ?_⟩, ?_⟩
  · intro n
    rw [speedMeasure, restrict_withDensity (hQm n)]
    exact (Ch04.InjectiveCurveArea.map_weighted_volume_of_nullMeasurableSet hU hγ
      (hQm n).nullMeasurableSet (hQ n) (hQi n) (hQv n)).2
  · ext t
    simp only [Q, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨n, hn, ht⟩
      have hm : t ∈ ⋃ n, P n := mem_iUnion.mpr ⟨n, hn⟩
      rw [hcover] at hm
      exact ⟨ht, hm.2⟩
    · rintro ⟨ht, hv⟩
      have hm : t ∈ ⋃ n, P n := hcover.symm ▸ ⟨hsU ht, hv⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hm
      exact ⟨n, hn, ht⟩

private lemma transport_fiber_eq (γ : ℝ → ℂ) (s : Set ℝ) (P : ℕ → Set ℝ)
    (hcover : (⋃ n, P n) = {t | t ∈ s ∧ deriv γ t ≠ 0}) (z : ℂ) :
    Ch04.CountableFiberTransport.fiber γ P z = regularFiber γ s z := by
  ext t
  change (t ∈ ⋃ n, P n) ∧ γ t = z ↔ t ∈ s ∧ γ t = z ∧ deriv γ t ≠ 0
  rw [hcover]
  simp only [mem_ofPred_eq]
  tauto

/-- The extended area identity on Borel subsets; no finiteness of speed or
multiplicity is presumed. -/
theorem area_of_measurableSet (γ : ℝ → ℂ) (U s : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    AEMeasurable (multiplicity γ s) μH[1] ∧
      (∫⁻ z, multiplicity γ s z ∂μH[1]) =
        ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖ := by
  obtain ⟨P, H, hcover⟩ := transport_partition γ U s hU hγ hs hsU
  have hu := Ch04.CountableFiberTransport.unsigned_transport γ (speedMeasure γ) μH[1] P H
    (fun _ => 1) aemeasurable_const
  have heq (z : ℂ) : (∑' _ : Ch04.CountableFiberTransport.fiber γ P z, (1 : ℝ≥0∞)) =
      multiplicity γ s z := by
    rw [transport_fiber_eq γ s P hcover z, ENNReal.tsum_set_one]
    rfl
  change AEMeasurable (fun z => ∑' _ : Ch04.CountableFiberTransport.fiber γ P z, (1 : ℝ≥0∞)) μH[1] ∧
    (∫⁻ z, ∑' _ : Ch04.CountableFiberTransport.fiber γ P z, (1 : ℝ≥0∞) ∂μH[1]) =
      ∫⁻ t in ⋃ n, P n, (1 : ℝ≥0∞) ∂speedMeasure γ at hu
  simp_rw [heq] at hu
  refine ⟨hu.1, hu.2.trans ?_⟩
  rw [speedMeasure, restrict_withDensity (MeasurableSet.iUnion H.measurableSet),
    lintegral_withDensity_eq_lintegral_mul _ ((measurable_deriv γ).norm.ennreal_ofReal) measurable_const]
  simp only [Pi.mul_apply, mul_one]
  rw [hcover]
  rw [show {t | t ∈ s ∧ deriv γ t ≠ 0} = s ∩ {t | deriv γ t ≠ 0} from rfl,
    Set.inter_comm s {t | deriv γ t ≠ 0},
    ← Measure.restrict_restrict (show MeasurableSet {t | deriv γ t ≠ 0} from
      (measurable_deriv γ) isClosed_singleton.measurableSet.compl),
    ← lintegral_indicator (show MeasurableSet {t | deriv γ t ≠ 0} from
      (measurable_deriv γ) isClosed_singleton.measurableSet.compl)]
  apply lintegral_congr
  intro t
  by_cases hv : deriv γ t = 0 <;> simp [hv]

/-- Arbitrary completed Lebesgue restrictions have the same extended area
identity. Null source remainders are removed by a proved null-image theorem. -/
theorem area_of_nullMeasurableSet (γ : ℝ → ℂ) (U s : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U)
    (hs : NullMeasurableSet s volume) (hsU : s ⊆ U) :
    AEMeasurable (multiplicity γ s) μH[1] ∧
      (∫⁻ z, multiplicity γ s z ∂μH[1]) =
        ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖ := by
  obtain ⟨B, hBs, hBm, hBae⟩ := hs.exists_measurable_subset_ae_eq
  have hnull : (μH[1] : Measure ℂ) (γ '' (s \ B)) = 0 :=
    hausdorff_c1_null_image γ U hU hγ _ (sdiff_subset.trans hsU) (ae_eq_set.mp hBae).2
  have hf : ∀ᵐ z ∂(μH[1] : Measure ℂ), regularFiber γ s z = regularFiber γ B z := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz
    ext t
    constructor
    · intro ht
      exact ⟨by by_contra hn; exact hz ⟨t, ⟨ht.1, hn⟩, ht.2.1⟩, ht.2⟩
    · intro ht
      exact ⟨hBs ht.1, ht.2⟩
  have hm : multiplicity γ s =ᵐ[μH[1]] multiplicity γ B :=
    hf.mono fun z hz => congrArg (fun A : Set ℝ => (A.encard : ℝ≥0∞)) hz
  have hB := area_of_measurableSet γ U B hU hγ hBm (hBs.trans hsU)
  exact ⟨hB.1.congr hm.symm, (lintegral_congr_ae hm).trans
    (hB.2.trans (setLIntegral_congr hBae))⟩

theorem measurable_restriction_area :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.measurable_restriction_area_type := by
  intro γ U s hU hγ hsU _ hs
  exact area_of_nullMeasurableSet γ U s hU hγ hs hsU


private lemma speed_smul_weight (γ : ℝ → ℂ) (q : ℂ → ℂ) (t : ℝ) :
    (ENNReal.ofReal ‖deriv γ t‖).toReal • (q (γ t) * unitVelocity γ t) =
      q (γ t) * deriv γ t := by
  rw [ENNReal.toReal_ofReal (norm_nonneg _), Complex.real_smul]
  calc
    (‖deriv γ t‖ : ℂ) * (q (γ t) * unitVelocity γ t) =
      q (γ t) * (unitVelocity γ t * (‖deriv γ t‖ : ℂ)) := by ring
    _ = _ := by rw [unitVelocity_mul_speed]

/-- Signed transport on Borel restrictions, with the exact necessary source
integrability assumption. It imposes no global injectivity or nonzero speed. -/
theorem pushforward_of_measurableSet (γ : ℝ → ℂ) (U s : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (q : ℂ → ℂ) (hq : IntegrableOn (fun t => q (γ t) * deriv γ t) s volume) :
    Integrable (fun z => q z * signedDensity γ s z) μH[1] ∧
      (∫ t in s, q (γ t) * deriv γ t) = ∫ z, q z * signedDensity γ s z ∂μH[1] := by
  classical
  obtain ⟨P, H, hcover⟩ := transport_partition γ U s hU hγ hs hsU
  have hRm : MeasurableSet (⋃ n, P n) := MeasurableSet.iUnion H.measurableSet
  have hRs : (⋃ n, P n) ⊆ s := by rw [hcover]; exact fun _ h => h.1
  have hi : Integrable (fun t => q (γ t) * unitVelocity γ t)
      ((speedMeasure γ).restrict (⋃ n, P n)) := by
    rw [speedMeasure, restrict_withDensity hRm,
      integrable_withDensity_iff_integrable_smul' ((measurable_deriv γ).norm.ennreal_ofReal)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [speed_smul_weight]
    exact hq.mono_set hRs
  have ht := Ch04.CountableFiberTransport.signed_transport γ (speedMeasure γ) μH[1] P H
    (fun t => q (γ t) * unitVelocity γ t) hi
  have heq (z : ℂ) :
      (∑' t : Ch04.CountableFiberTransport.fiber γ P z, q (γ t) * unitVelocity γ t) =
        q z * signedDensity γ s z := by
    rw [transport_fiber_eq γ s P hcover z]
    simp only [signedDensity, fun t : regularFiber γ s z => t.property.2.1, tsum_mul_left]
  change _ ∧ Integrable (fun z => ∑' t : Ch04.CountableFiberTransport.fiber γ P z,
      q (γ t) * unitVelocity γ t) μH[1] ∧
    (∫ z, ∑' t : Ch04.CountableFiberTransport.fiber γ P z,
      q (γ t) * unitVelocity γ t ∂μH[1]) =
        ∫ t in ⋃ n, P n, q (γ t) * unitVelocity γ t ∂speedMeasure γ at ht
  simp_rw [heq] at ht
  refine ⟨ht.2.1, ?_⟩
  rw [ht.2.2, speedMeasure, restrict_withDensity hRm,
    integral_withDensity_eq_integral_toReal_smul ((measurable_deriv γ).norm.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [speed_smul_weight]
  rw [hcover]
  rw [show {t | t ∈ s ∧ deriv γ t ≠ 0} = s ∩ {t | deriv γ t ≠ 0} from rfl,
    Set.inter_comm s {t | deriv γ t ≠ 0},
    ← Measure.restrict_restrict (show MeasurableSet {t | deriv γ t ≠ 0} from
      (measurable_deriv γ) isClosed_singleton.measurableSet.compl),
    ← integral_indicator (show MeasurableSet {t | deriv γ t ≠ 0} from
      (measurable_deriv γ) isClosed_singleton.measurableSet.compl)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases hv : deriv γ t = 0 <;> simp [hv]

/-- Completed measurable restrictions, with no finiteness assumptions beyond
integrability of the actual weighted original derivative. -/
theorem pushforward_of_nullMeasurableSet (γ : ℝ → ℂ) (U s : Set ℝ)
    (hU : IsOpen U) (hγ : ContDiffOn ℝ 1 γ U)
    (hs : NullMeasurableSet s volume) (hsU : s ⊆ U)
    (q : ℂ → ℂ) (hq : IntegrableOn (fun t => q (γ t) * deriv γ t) s volume) :
    Integrable (fun z => q z * signedDensity γ s z) μH[1] ∧
      (∫ t in s, q (γ t) * deriv γ t) = ∫ z, q z * signedDensity γ s z ∂μH[1] := by
  obtain ⟨B, hBs, hBm, hBae⟩ := hs.exists_measurable_subset_ae_eq
  have hnull : (μH[1] : Measure ℂ) (γ '' (s \ B)) = 0 :=
    hausdorff_c1_null_image γ U hU hγ _ (sdiff_subset.trans hsU) (ae_eq_set.mp hBae).2
  have hd : (fun z => q z * signedDensity γ s z) =ᵐ[μH[1]]
      (fun z => q z * signedDensity γ B z) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz
    have hf : regularFiber γ s z = regularFiber γ B z := by
      ext t
      constructor
      · intro ht
        exact ⟨by by_contra hn; exact hz ⟨t, ⟨ht.1, hn⟩, ht.2.1⟩, ht.2⟩
      · intro ht
        exact ⟨hBs ht.1, ht.2⟩
    exact congrArg (fun v : ℂ => q z * v)
      ((Set.equivOfEq hf).tsum_eq (fun t : regularFiber γ B z => unitVelocity γ t))
  have hB := pushforward_of_measurableSet γ U B hU hγ hBm (hBs.trans hsU) q (hq.mono_set hBs)
  refine ⟨hB.1.congr hd.symm, ?_⟩
  exact (setIntegral_congr_set hBae.symm).trans (hB.2.trans (integral_congr_ae hd.symm))


/-- Integrable speed and the unsigned area identity imply finite actual fibers
almost everywhere, and hence summability of the actual unit tangents. -/
theorem ae_finite_of_area (γ : ℝ → ℂ) (s : Set ℝ)
    (hm : AEMeasurable (multiplicity γ s) μH[1])
    (ha : (∫⁻ z, multiplicity γ s z ∂μH[1]) =
      ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖)
    (hi : IntegrableOn (fun t => ‖deriv γ t‖) s volume) :
    ∀ᵐ z ∂(μH[1] : Measure ℂ), (regularFiber γ s z).Finite := by
  have hlt : (∫⁻ z, multiplicity γ s z ∂μH[1]) < ∞ := by
    rw [ha]
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => norm_nonneg _)).mp hi.2
  filter_upwards [ae_lt_top' hm hlt.ne] with z hz
  exact (multiplicity_lt_top_iff γ s z).mp hz

/-- The full weighted formula for completed restrictions compactly contained
in an open C1 domain, including stationary points and repeated traversal. -/
theorem measurable_restriction_pushforward :
    Specs.D12Complex.Ch04.SignedCurveMultiplicity.measurable_restriction_pushforward_type := by
  intro γ U K s hU hγ hK hKU hsK hs q hq
  have hc : ContinuousOn (fun t => q (γ t)) K :=
    hq.comp (hγ.continuousOn.mono hKU) (fun t ht => ⟨t, ht, rfl⟩)
  have hd : ContinuousOn (deriv γ) K :=
    (hγ.continuousOn_deriv_of_isOpen hU le_rfl).mono hKU
  have hi : IntegrableOn (fun t => q (γ t) * deriv γ t) s volume :=
    ((hc.mul hd).integrableOn_compact hK).mono_set hsK
  have hv : IntegrableOn (fun t => ‖deriv γ t‖) s volume :=
    (hd.norm.integrableOn_compact hK).mono_set hsK
  have ha := area_of_nullMeasurableSet γ U s hU hγ hs (hsK.trans hKU)
  have hp := pushforward_of_nullMeasurableSet γ U s hU hγ hs (hsK.trans hKU) q hi
  exact ⟨ha.1, ae_finite_of_area γ s ha.1 ha.2 hv, ha.2, hi, hp⟩

/-- Remove only finitely many original parameter nodes to obtain an open C1
locus. This keeps the original total representative and original interval. -/
private lemma path_c1_locus (γ : PiecewiseC1Path) :
    ∃ U : Set ℝ, IsOpen U ∧ ContDiffOn ℝ 1 γ U ∧
      U ⊆ Ioo γ.path.a γ.path.b ∧ (Ioo γ.path.a γ.path.b \ U).Finite := by
  classical
  let P := γ.partition
  let V : Fin P.count → Set ℝ := fun i => Ioo (P.node i.castSucc) (P.node i.succ)
  let U := ⋃ i, V i
  have hsub : U ⊆ Ioo γ.path.a γ.path.b := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    constructor
    · have hh := (P.strictMono.monotone (Fin.zero_le i.castSucc)).trans_lt hi.1
      simpa only [P.first] using hh
    · have := hi.2.trans_le (P.strictMono.monotone (Fin.le_last i.succ))
      simpa only [P.last] using this
  refine ⟨U, isOpen_iUnion (fun _ => isOpen_Ioo),
    ContDiffOn.iUnion_of_isOpen (fun i => (P.smooth i).mono Ioo_subset_Icc_self)
      (fun _ => isOpen_Ioo), hsub, ?_⟩
  apply (Set.finite_range P.node).subset
  intro t ht
  have hc : t ∈ Icc (P.node 0) (P.node (Fin.last P.count)) := by
    simpa only [P.first, P.last] using (show t ∈ Icc γ.path.a γ.path.b from ⟨ht.1.1.le, ht.1.2.le⟩)
  rcases interval_nodes_cover P.count P.node P.strictMono.monotone t hc with he | ⟨i, hi⟩
  · exact ⟨0, he.symm⟩
  · by_cases ha : t = P.node i.castSucc
    · exact ⟨i.castSucc, ha.symm⟩
    · by_cases hb : t = P.node i.succ
      · exact ⟨i.succ, hb.symm⟩
      · exact (ht.2 (mem_iUnion.mpr ⟨i, lt_of_le_of_ne hi.1 (Ne.symm ha),
          lt_of_le_of_ne hi.2 hb⟩)).elim

private lemma fibers_ae_of_finite_sdiff (γ : ℝ → ℂ) (s u : Set ℝ)
    (hus : u ⊆ s) (hfinite : (s \ u).Finite) :
    ∀ᵐ z ∂(μH[1] : Measure ℂ), regularFiber γ s z = regularFiber γ u z := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    ((hfinite.image γ).countable.measure_zero (μH[1] : Measure ℂ))] with z hz
  ext t
  constructor
  · intro ht
    exact ⟨by by_contra hn; exact hz ⟨t, ⟨ht.1, hn⟩, ht.2.1⟩, ht.2⟩
  · intro ht
    exact ⟨hus ht.1, ht.2⟩

private lemma sets_ae_of_finite_sdiff (s u : Set ℝ) (hus : u ⊆ s)
    (hfinite : (s \ u).Finite) : s =ᵐ[volume] u := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfinite.countable.measure_zero volume)] with t ht
  apply propext
  exact ⟨fun hs => by by_contra hu; exact ht ⟨hs, hu⟩, fun hu => hus hu⟩

theorem path_area : Specs.D12Complex.Ch04.SignedCurveMultiplicity.path_area_type := by
  intro γ
  obtain ⟨U, hU, hγ, hUs, hfinite⟩ := path_c1_locus γ
  have ha := area_of_measurableSet γ U U hU hγ hU.measurableSet Subset.rfl
  have hf := fibers_ae_of_finite_sdiff γ _ U hUs hfinite
  have hm : multiplicity γ (Ioo γ.path.a γ.path.b) =ᵐ[μH[1]] multiplicity γ U :=
    hf.mono fun z hz => congrArg (fun A : Set ℝ => (A.encard : ℝ≥0∞)) hz
  have hs := sets_ae_of_finite_sdiff _ U hUs hfinite
  have ha' : (∫⁻ z, multiplicity γ (Ioo γ.path.a γ.path.b) z ∂μH[1]) =
      ∫⁻ t in Ioo γ.path.a γ.path.b, ENNReal.ofReal ‖deriv γ t‖ :=
    (lintegral_congr_ae hm).trans (ha.2.trans (setLIntegral_congr hs.symm))
  have hm' := ha.1.congr hm.symm
  exact ⟨hm', ae_finite_of_area γ _ hm' ha' (path_speed_integrable γ), ha'⟩

theorem path_pushforward : Specs.D12Complex.Ch04.SignedCurveMultiplicity.path_pushforward_type := by
  intro γ q hq
  obtain ⟨U, hU, hγ, hUs, hfinite⟩ := path_c1_locus γ
  have hi : IntegrableOn (fun t => q (γ t) * deriv γ t) (Ioo γ.path.a γ.path.b) volume :=
    (C1Partition.parameter_integrable γ.path γ.partition q hq).1.mono_set Ioo_subset_Ioc_self
  have hp := pushforward_of_measurableSet γ U U hU hγ hU.measurableSet Subset.rfl q (hi.mono_set hUs)
  have hf := fibers_ae_of_finite_sdiff γ _ U hUs hfinite
  have hd : (fun z => q z * pathDensity γ z) =ᵐ[μH[1]] (fun z => q z * signedDensity γ U z) := by
    filter_upwards [hf] with z hz
    exact congrArg (fun v : ℂ => q z * v)
      ((Set.equivOfEq hz).tsum_eq (fun t : regularFiber γ U z => unitVelocity γ t))
  refine ⟨hp.1.congr hd.symm, ?_⟩
  rw [PiecewiseC1Path.integral, C1Partition.integral_eq_intervalIntegral _ _ _ hq,
    intervalIntegral.integral_of_le γ.path.ordered, integral_Ioc_eq_integral_Ioo]
  exact (setIntegral_congr_set (sets_ae_of_finite_sdiff _ U hUs hfinite)).trans
    (hp.2.trans (integral_congr_ae hd.symm))


/-- Every original signed integer coefficient is retained. In particular this
applies to unchanged closed-path cycles, with no geometric replacement. -/
theorem chain_pushforward : Specs.D12Complex.Ch04.SignedCurveMultiplicity.chain_pushforward_type := by
  classical
  intro Γ q hq
  have hp (γ : PiecewiseC1Path) (hγ : γ ∈ Γ.support) :
      Integrable (fun z => q z * pathDensity γ z) μH[1] ∧
        γ.integral q = ∫ z, q z * pathDensity γ z ∂μH[1] :=
    path_pushforward γ q (hq.mono (fun _ hz => ⟨γ, hγ, hz⟩))
  have hi (γ : PiecewiseC1Path) (hγ : γ ∈ Γ.support) :
      Integrable (fun z => (Γ γ : ℂ) * (q z * pathDensity γ z)) μH[1] :=
    (hp γ hγ).1.const_mul _
  have heq : (fun z => q z * chainDensity Γ z) =
      fun z => ∑ γ ∈ Γ.support, (Γ γ : ℂ) * (q z * pathDensity γ z) := by
    funext z
    simp only [chainDensity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hf : ∀ᵐ z ∂(μH[1] : Measure ℂ), ∀ γ ∈ Γ.support,
        (regularFiber γ (Ioo γ.path.a γ.path.b) z).Finite :=
      (Γ.support.eventually_all).mpr (fun γ _ => (path_area γ).2.1)
    filter_upwards [hf] with z hz
    apply ENNReal.sum_lt_top.mpr
    intro γ hγ
    exact ENNReal.mul_lt_top (by simp) ((multiplicity_lt_top_iff γ _ z).mpr (hz γ hγ))
  · rw [heq]
    exact integrable_finsetSum Γ.support hi
  · rw [heq, integral_finsetSum Γ.support hi]
    change (∑ γ ∈ Γ.support, (Γ γ : ℂ) * γ.integral q) = _
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [integral_const_mul, (hp γ hγ).2]


/-- The absolute multiplicity has finite integral, with its exact coefficient
weighted speed formula. This controls all signed chain occurrences. -/
theorem chain_absolute_area (Γ : IntegralChain) :
    AEMeasurable (chainMultiplicity Γ) μH[1] ∧
    (∫⁻ z, chainMultiplicity Γ z ∂μH[1]) =
      ∑ γ ∈ Γ.support, (Γ γ).natAbs *
        ∫⁻ t in Ioo γ.path.a γ.path.b, ENNReal.ofReal ‖deriv γ t‖ ∧
    (∫⁻ z, chainMultiplicity Γ z ∂μH[1]) < ∞ := by
  classical
  have hm (γ : PiecewiseC1Path) :
      AEMeasurable (fun z => (Γ γ).natAbs * multiplicity γ (Ioo γ.path.a γ.path.b) z) μH[1] :=
    aemeasurable_const.mul (path_area γ).1
  have heq : (∫⁻ z, chainMultiplicity Γ z ∂μH[1]) =
      ∑ γ ∈ Γ.support, (Γ γ).natAbs *
        ∫⁻ t in Ioo γ.path.a γ.path.b, ENNReal.ofReal ‖deriv γ t‖ := by
    simp only [chainMultiplicity]
    rw [lintegral_finsetSum' Γ.support (fun γ _ => hm γ)]
    apply Finset.sum_congr rfl
    intro γ _
    rw [lintegral_const_mul'' _ (path_area γ).1, (path_area γ).2.2]
  refine ⟨Γ.support.aemeasurable_fun_sum (fun γ _ => hm γ), heq, ?_⟩
  rw [heq]
  apply ENNReal.sum_lt_top.mpr
  intro γ _
  apply ENNReal.mul_lt_top (by simp)
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => norm_nonneg _)).mp
    (path_speed_integrable γ).2

theorem path_summable : Specs.D12Complex.Ch04.SignedCurveMultiplicity.path_summable_type := by
  intro γ
  filter_upwards [(path_area γ).2.1] with z hz
  exact (summable_iff_finite γ _ z).mpr hz

theorem cycle_pushforward : Specs.D12Complex.Ch04.SignedCurveMultiplicity.cycle_pushforward_type := by
  intro Γ q hq
  exact chain_pushforward Γ.chain q hq

end D12Complex.SignedCurveMultiplicity
