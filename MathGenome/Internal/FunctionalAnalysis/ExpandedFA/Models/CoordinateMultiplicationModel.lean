import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.CoordinateMultiplicationModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.TranslationFourierModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.StoneTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Coordinate multiplication on Bochner L². The whole-line generator is identified
through pointwise derivative necessity and the full adjoint graph. Indicator
multipliers construct the restricted spectral measure directly; its bounded
and unbounded spectral integrals are identified on the actual L² quotient.
-/
noncomputable section
open MeasureTheory Filter Set Topology
open scoped InnerProductSpace

namespace ExpandedFA.Models.CoordinateMultiplicationModel
open FullTranslationModel ExpandedFA.Semigroups.Stone
open ExpandedFA.Unbounded ExpandedFA.Unbounded.SymmetryAndDeficienciesSpec
open ExpandedFA.Unbounded.MeasurableSpectralCalculus
universe u

variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

/-- The pointwise quotient formula, using the continuous divided difference
of the exponential. It applies to arbitrary Bochner representatives. -/
theorem quotient_representative (U : UnitaryGroup (L2 M)) (hU : IsCoordinateGroup U)
    (h : ℝ) (hh : h ≠ 0) (f : L2 M) :
    (⇑(differenceQuotient U h f)) =ᵐ[volume]
      fun r => derivativeMultiplier h r • (Complex.I • ((r : ℂ) • f r)) := by
  filter_upwards [Lp.coeFn_smul (h : ℂ)⁻¹ (U.operators h f - f),
    Lp.coeFn_sub (U.operators h f) f, hU h f] with r h₁ h₂ h₃
  simp only [differenceQuotient, h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃]
  have he : Complex.exp (Complex.I * (h : ℂ) * (r : ℂ)) • f r - f r =
      (Complex.exp (Complex.I * (h : ℂ) * (r : ℂ)) - 1) • f r := by
    rw [sub_smul, one_smul]
  rw [he, smul_smul, smul_smul, smul_smul]
  congr 1
  have hid := derivativeMultiplier_identity h r
  change (h : ℂ)⁻¹ * (exponentialSymbol h r - 1) =
    derivativeMultiplier h r * Complex.I * (r : ℂ)
  rw [← hid]
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp

/-- Necessity and the value of a strong derivative, with no separability
assumption: norm convergence supplies an almost everywhere subsequence. -/
theorem derivative_coordinate_value (U : UnitaryGroup (L2 M)) (hU : IsCoordinateGroup U)
    (f y : L2 M) (hy : HasDerivative U f y) :
    (y : ℝ → M) =ᵐ[volume] fun r => Complex.I • ((r : ℂ) • f r) := by
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ha : Tendsto a atTop (𝓝 (0 : ℝ)) := by
    simpa [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hane : ∀ n, a n ≠ 0 := fun n => inv_ne_zero (by positivity)
  have ha' : Tendsto a atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha, Eventually.of_forall hane⟩
  have hnorm := hy.comp ha'
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hnorm).exists_seq_tendsto_ae
  have hrep : ∀ᵐ r ∂volume, ∀ n, (differenceQuotient U (a (ns n)) f) r =
      derivativeMultiplier (a (ns n)) r • (Complex.I • ((r : ℂ) • f r)) :=
    ae_all_iff.mpr fun n => quotient_representative U hU _ (hane _) f
  filter_upwards [hlim, hrep] with r hr hrep
  have ht := ((derivativeMultiplier_tendsto r).comp (ha.comp hns.tendsto_atTop)).smul_const
    (Complex.I • ((r : ℂ) • f r))
  simp only [one_smul] at ht
  exact tendsto_nhds_unique hr (ht.congr (fun n => (hrep n).symm))

/-- A self-adjoint operator whose derivatives are the coordinate derivatives
has the entire maximal coordinate graph. The reverse inclusion uses its
adjoint, so no domain sufficiency is assumed. -/
theorem coordinate_graph_of_derivative (U : UnitaryGroup (L2 M)) (hU : IsCoordinateGroup U)
    (B : Operator ℂ (L2 M) (L2 M)) (hB : selfAdjointValue B)
    (hd : DerivativeGraph U B) :
    ∀ f g : L2 M, (f, g) ∈ B.graph ↔ CoordinateGraph f g := by
  have hnec : ∀ f g : L2 M, (f, g) ∈ B.graph → CoordinateGraph f g := by
    intro f g hfg
    obtain ⟨hf, hval⟩ := (mem_graph_iff B (f, g)).mp hfg
    have hder : HasDerivative U f (Complex.I • g) := by
      apply (hd f _).mpr
      exact (mem_graph_iff (Complex.I • B) _).mpr ⟨hf, by simpa using congrArg (Complex.I • ·) hval⟩
    have hae := derivative_coordinate_value U hU f _ hder
    filter_upwards [hae, Lp.coeFn_smul Complex.I g] with r hr hs
    exact (smul_right_injective M Complex.I_ne_zero) (hs.symm.trans hr)
  intro f g
  refine ⟨hnec f g, fun hfg => ?_⟩
  have hadj : (f, g) ∈ (hilbertAdjoint B).graph := by
    apply (mem_hilbertAdjoint_graph_iff B hB.1 f g).mpr
    intro x
    have hx := hnec x (B x) ((mem_graph_iff B _).mpr ⟨x.2, rfl⟩)
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hx, hfg] with r hr hs
    rw [hr, hs, inner_smul_left, inner_smul_right]
    simp
  have he : hilbertAdjoint B = B := hB.2.symm
  rwa [he] at hadj

/-- The actual whole-line coordinate Stone model, including its PVM formula
and its exact two-sided norm-derivative graph. -/
theorem coordinate_generator : CoordinateSpec.CoordinateGenerator.{u} := by
  intro M _ _ _
  let W := TranslationFourierModel.coordinateGroup (M := M)
  have hW : IsCoordinateGroup W := TranslationFourierModel.coordinateGroup_formula
  obtain ⟨B, hB, hs, hd, _⟩ := stone_forward (L2 M) W
  exact ⟨W, B, hW, hB, hs, hd, coordinate_graph_of_derivative W hW B hB hd⟩


section Multipliers
variable (μ : Measure ℝ)

/-- Bounded measurable multipliers act on the actual Bochner L² quotient. -/
theorem multiplierMemLp (m : ℝ → ℂ) (hm : SpectralMeasure.Spec.IsBoundedMeasurable m)
    (f : Lp M 2 μ) : MemLp (fun r => m r • f r) 2 μ := by
  obtain ⟨C, hC, hb⟩ := hm.nonneg_bound
  exact (Lp.memLp f).of_le_mul
    (hm.1.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun r => by
      simpa only [norm_smul] using (mul_le_mul_of_nonneg_right (hb r) (norm_nonneg (f r))))

def multiplierLinear (m : ℝ → ℂ) (hm : SpectralMeasure.Spec.IsBoundedMeasurable m) :
    Lp M 2 μ →ₗ[ℂ] Lp M 2 μ where
  toFun f := (multiplierMemLp μ m hm f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(multiplierMemLp μ m hm (f+g)).coeFn_toLp,
      Lp.coeFn_add f g, Lp.coeFn_add
        ((multiplierMemLp μ m hm f).toLp _) ((multiplierMemLp μ m hm g).toLp _),
      (multiplierMemLp μ m hm f).coeFn_toLp,
      (multiplierMemLp μ m hm g).coeFn_toLp] with r h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, Pi.add_apply, h₄, h₅, smul_add]
  map_smul' c f := by
    change (multiplierMemLp μ m hm (c • f)).toLp _ = c • (multiplierMemLp μ m hm f).toLp _
    apply Lp.ext
    filter_upwards [(multiplierMemLp μ m hm (c • f)).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((multiplierMemLp μ m hm f).toLp _),
      (multiplierMemLp μ m hm f).coeFn_toLp] with r h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, Pi.smul_apply, h₄]
    exact smul_comm _ _ _

theorem multiplierLinear_bound (m : ℝ → ℂ)
    (hm : SpectralMeasure.Spec.IsBoundedMeasurable m) (C : ℝ)
    (hb : ∀ r, ‖m r‖ ≤ C) (f : Lp M 2 μ) :
    ‖multiplierLinear μ m hm f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(multiplierMemLp μ m hm f).coeFn_toLp] with r hr
  change ‖((multiplierMemLp μ m hm f).toLp _) r‖ ≤ C * ‖f r‖
  rw [hr, norm_smul]
  exact mul_le_mul_of_nonneg_right (hb r) (norm_nonneg _)

def multiplier (m : ℝ → ℂ) (hm : SpectralMeasure.Spec.IsBoundedMeasurable m) :
    Lp M 2 μ →L[ℂ] Lp M 2 μ :=
  (multiplierLinear μ m hm).mkContinuous hm.nonneg_bound.choose
    (multiplierLinear_bound μ m hm _ hm.nonneg_bound.choose_spec.2)

theorem multiplier_representative (m : ℝ → ℂ)
    (hm : SpectralMeasure.Spec.IsBoundedMeasurable m) (f : Lp M 2 μ) :
    (multiplier μ m hm f : ℝ → M) =ᵐ[μ] fun r => m r • f r :=
  (multiplierMemLp μ m hm f).coeFn_toLp

end Multipliers
theorem l2_norm_sq (f : Lp M 2 μ) : ‖f‖ ^ 2 = ∫ r, ‖f r‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq]

theorem tendsto_l2_of_dominated (F : ℕ → Lp M 2 μ) (f : Lp M 2 μ)
    (b : ℝ → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ r ∂μ, ‖F n r - f r‖ ^ 2 ≤ b r)
    (hlim : ∀ᵐ r ∂μ, Tendsto (fun n => F n r) atTop (𝓝 (f r))) :
    Tendsto F atTop (𝓝 f) := by
  have hi : Tendsto (fun n => ∫ r, ‖F n r - f r‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    convert tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) b
      (fun n => ((Lp.aestronglyMeasurable (F n)).sub (Lp.aestronglyMeasurable f)).norm.pow 2)
      hb (fun n => (hbound n).mono fun r hr => by simpa only [Pi.pow_apply, Pi.sub_apply, Real.norm_eq_abs, abs_pow, abs_norm] using hr) ?_ using 1
    · simp
    · filter_upwards [hlim] with r hr
      simpa using ((hr.sub (tendsto_const_nhds (x := f r))).norm.pow 2)
  have he (n : ℕ) : ‖F n - f‖ ^ 2 = ∫ r, ‖F n r - f r‖ ^ 2 ∂μ := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F n) f] with r hr
    rw [hr]; rfl
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hi
  simp only [Function.comp_def, ← he, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs
section Projections
variable (μ : Measure ℝ)

def indicatorSymbol (B : Set ℝ) : ℝ → ℂ := B.indicator (fun _ => 1)

theorem bounded_indicatorSymbol {B : Set ℝ} (hB : MeasurableSet B) :
    SpectralMeasure.Spec.IsBoundedMeasurable (indicatorSymbol B) := by
  refine ⟨measurable_const.indicator hB, 1, fun r => ?_⟩
  by_cases hr : r ∈ B <;> simp [indicatorSymbol, hr]

def indicatorOperator (B : Set ℝ) : Lp M 2 μ →L[ℂ] Lp M 2 μ := by
  classical
  exact if hB : MeasurableSet B then multiplier μ (indicatorSymbol B) (bounded_indicatorSymbol hB) else 0

theorem indicator_representative {B : Set ℝ} (hB : MeasurableSet B) (f : Lp M 2 μ) :
    ⇑(indicatorOperator μ B f) =ᵐ[μ] B.indicator (fun r => f r) := by
  rw [indicatorOperator, dite_eq_left hB]
  filter_upwards [multiplier_representative μ _ (bounded_indicatorSymbol hB) f] with r hr
  rw [hr]
  by_cases h : r ∈ B <;> simp [indicatorSymbol, h]

theorem indicator_selfAdjoint {B : Set ℝ} (hB : MeasurableSet B) :
    IsSelfAdjoint (indicatorOperator (M := M) μ B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (indicatorOperator μ B f) g = inner ℂ f (indicatorOperator μ B g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicator_representative μ hB f, indicator_representative μ hB g] with r hr hs
  rw [hr, hs]
  by_cases h : r ∈ B <;> simp [h]

theorem indicator_inter {B C : Set ℝ} (hB : MeasurableSet B) (hC : MeasurableSet C) :
    indicatorOperator (M := M) μ B * indicatorOperator μ C = indicatorOperator μ (B ∩ C) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [indicator_representative μ hB (indicatorOperator μ C f),
    indicator_representative μ hC f, indicator_representative μ (hB.inter hC) f] with r h₁ h₂ h₃
  change (indicatorOperator μ B (indicatorOperator μ C f)) r = _
  rw [h₁, h₃]
  by_cases hr : r ∈ B <;> by_cases hs : r ∈ C <;> simp [hr, hs, h₂]

theorem disjoint_sum_indicator (B : ℕ → Set ℝ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (s : Finset ℕ) (f : ℝ → M) (r : ℝ) :
    (∑ i ∈ s, (B i).indicator f r) = (⋃ i ∈ s, B i).indicator f r := by
  classical
  by_cases hr : ∃ i ∈ s, r ∈ B i
  · obtain ⟨i, hi, hri⟩ := hr
    rw [Set.indicator_of_mem (by simpa using ⟨i, hi, hri⟩)]
    rw [Finset.sum_eq_single i]
    · simp [hri]
    · intro j hj hji
      have hjr : r ∉ B j := fun hjr => Set.disjoint_left.mp (hB hji) hjr hri
      simp [hjr]
    · exact fun h => (h hi).elim
  · have hnone : r ∉ ⋃ i ∈ s, B i := by simpa using hr
    rw [Set.indicator_of_notMem hnone]
    apply Finset.sum_eq_zero
    intro i hi
    exact Set.indicator_of_notMem (fun h => hr ⟨i, hi, h⟩) _

theorem indicator_iUnion (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) (f : Lp M 2 μ) :
    HasSum (fun n => indicatorOperator μ (B n) f) (indicatorOperator μ (⋃ n, B n) f) := by
  classical
  apply (SpectralMeasure.ProjectionValuedMeasure.hasSum_iff_partialSums_of_orthogonal _ ?_ _).mpr
  · have hrep : ∀ᵐ r ∂μ, ∀ N, (∑ n ∈ Finset.range N, indicatorOperator μ (B n) f) r =
        (⋃ n ∈ Finset.range N, B n).indicator (fun r => f r) r := by
      apply ae_all_iff.mpr
      intro N
      filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range N) (fun n => indicatorOperator μ (B n) f),
        ae_all_iff.mpr (fun n => indicator_representative μ (hB n) f)] with r hr hs
      rw [hr]
      simp_rw [hs]
      exact disjoint_sum_indicator B hdis _ _ r
    have hbig := indicator_representative μ (MeasurableSet.iUnion hB) f
    apply tendsto_l2_of_dominated _ _ (fun r => 4 * ‖f r‖ ^ 2)
      (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).const_mul 4)
    · intro N
      filter_upwards [hrep, hbig] with r hr hs
      rw [hr N, hs]
      have hsmall : ‖(⋃ n ∈ Finset.range N, B n).indicator (fun r => f r) r‖ ≤ ‖f r‖ :=
        norm_indicator_le_norm_self _ _
      have hlarge : ‖(⋃ n, B n).indicator (fun r => f r) r‖ ≤ ‖f r‖ :=
        norm_indicator_le_norm_self _ _
      have ht := norm_sub_le ((⋃ n ∈ Finset.range N, B n).indicator (fun r => f r) r)
        ((⋃ n, B n).indicator (fun r => f r) r)
      nlinarith [norm_nonneg ((⋃ n ∈ Finset.range N, B n).indicator (fun r => f r) r -
        (⋃ n, B n).indicator (fun r => f r) r), norm_nonneg (f r)]
    · filter_upwards [hrep, hbig] with r hr hs
      apply tendsto_const_nhds.congr'
      change ∀ᶠ N in atTop, (indicatorOperator μ (⋃ n, B n) f) r =
        (∑ n ∈ Finset.range N, indicatorOperator μ (B n) f) r
      by_cases hm : r ∈ ⋃ n, B n
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hm
        filter_upwards [eventually_gt_atTop i] with N hN
        rw [hr N, hs, Set.indicator_of_mem hm,
          Set.indicator_of_mem (show r ∈ ⋃ n ∈ Finset.range N, B n by simp; exact ⟨i, hN, hi⟩)]
      · exact Eventually.of_forall fun N => by
          rw [hr N, hs, Set.indicator_of_notMem hm,
            Set.indicator_of_notMem (show r ∉ ⋃ n ∈ Finset.range N, B n from
              fun h => hm (by obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp h; exact Set.mem_iUnion.mpr ⟨i, hi⟩))]
  · intro i j hij
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [indicator_representative μ (hB i) f,
      indicator_representative μ (hB j) f] with r hr hs
    rw [hr, hs]
    by_cases hi : r ∈ B i
    · have hj : r ∉ B j := fun hj => Set.disjoint_left.mp (hdis hij) hi hj
      simp [hj]
    · simp [hi]

def coordinatePVM : SpectralMeasure.ProjectionValuedMeasure ℝ (Lp M 2 μ) where
  toFun := indicatorOperator μ
  univ := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    simpa using indicator_representative μ MeasurableSet.univ f
  selfAdjoint := fun _ hB => indicator_selfAdjoint μ hB
  inter := fun _ _ hB hC => indicator_inter μ hB hC
  iUnion := indicator_iUnion μ

end Projections
section IntegralIdentification
variable (μ : Measure ℝ)

theorem simple_integral_representative (m : SimpleFunc ℝ ℂ) (f : Lp M 2 μ) :
    ⇑(SpectralMeasure.Spec.SimpleIntegralValue (coordinatePVM μ) m f) =ᵐ[μ]
      fun r => m r • f r := by
  classical
  have hrep : ∀ᵐ r ∂μ, ∀ c ∈ m.range,
      (c • indicatorOperator μ (m ⁻¹' {c}) f) r = c • (m ⁻¹' {c}).indicator (fun r => f r) r := by
    apply m.range.eventually_all.mpr
    intro c hc
    filter_upwards [Lp.coeFn_smul c (indicatorOperator μ (m ⁻¹' {c}) f),
      indicator_representative μ (m.measurableSet_fiber c) f] with r hr hs
    simp only [hr, Pi.smul_apply, hs]
  have he : SpectralMeasure.Spec.SimpleIntegralValue (coordinatePVM (M := M) μ) m f =
      ∑ c ∈ m.range, c • indicatorOperator μ (m ⁻¹' {c}) f := by
    simp [SpectralMeasure.Spec.SimpleIntegralValue, coordinatePVM]
  rw [he]
  filter_upwards [hrep, Lp.coeFn_fun_finsetSum m.range
    (fun c => c • indicatorOperator μ (m ⁻¹' {c}) f)] with r hr hs
  rw [hs]
  simp_rw [Finset.sum_congr rfl hr]
  rw [Finset.sum_eq_single (m r)]
  · simp
  · intro c hc hcr
    simp [hcr.symm]
  · exact fun h => (h (m.mem_range_self r)).elim

theorem bounded_integral_representative (C : BoundedRealization (coordinatePVM (M := M) μ))
    (m : ℝ → ℂ) (hm : SpectralMeasure.Spec.IsBoundedMeasurable m) (f : Lp M 2 μ) :
    ⇑(C.integral m f) =ᵐ[μ] fun r => m r • f r := by
  obtain ⟨a, ha⟩ := SpectralMeasure.exists_uniform_simple_approx m hm
  have hlim : Tendsto (fun n => SpectralMeasure.Spec.SimpleIntegralValue (coordinatePVM μ) (a n) f)
      atTop (𝓝 (C.integral m f)) :=
    ((ContinuousLinearMap.apply ℂ (Lp M 2 μ) f).continuous.tendsto _).comp
      (C.uniform_limit m hm a ha)
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep := ae_all_iff.mpr (fun n => simple_integral_representative μ (a (ns n)) f)
  filter_upwards [hlim, hrep] with r hr hs
  have ht := ((ha.tendsto_at r).comp hns.tendsto_atTop).smul_const (f r)
  exact tendsto_nhds_unique hr (ht.congr fun n => (hs n).symm)

/-- The coordinate spectral integral has its maximal weighted L² graph.
Necessity comes from its convergent truncations; self-adjointness supplies
sufficiency by testing the adjoint against the whole original domain. -/
theorem coordinate_integral_graph (C : BoundedRealization (coordinatePVM (M := M) μ)) :
    ∀ f g : Lp M 2 μ,
      (f, g) ∈ (measurableIntegral C (fun r : ℝ => (r : ℂ))).graph ↔
        (g : ℝ → M) =ᵐ[μ] fun r => (r : ℂ) • f r := by
  let A := measurableIntegral C (fun r : ℝ => (r : ℂ))
  have hA : selfAdjointValue A := ⟨measurableIntegral_dense C Complex.measurable_ofReal,
    (measurableIntegral_selfAdjoint C Complex.measurable_ofReal (fun _ => rfl)).symm⟩
  have hnec : ∀ f g : Lp M 2 μ, (f, g) ∈ A.graph →
      (g : ℝ → M) =ᵐ[μ] fun r => (r : ℂ) • f r := by
    intro f g hfg
    obtain ⟨hf, hval⟩ := (mem_graph_iff A (f,g)).mp hfg
    have ht := measurableIntegral_tendsto C (fun r : ℝ => (r : ℂ)) ⟨f,hf⟩
    change Tendsto _ atTop (𝓝 (A ⟨f,hf⟩)) at ht
    rw [hval] at ht
    obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
    have hrep := ae_all_iff.mpr fun n => bounded_integral_representative μ C
      (truncation (fun r : ℝ => (r : ℂ)) (ns n))
      (boundedMeasurable_truncation Complex.measurable_ofReal _) f
    filter_upwards [hlim, hrep] with r hr hs
    have ht := ((truncation_tendsto (fun r : ℝ => (r : ℂ)) r).comp
      hns.tendsto_atTop).smul_const (f r)
    exact tendsto_nhds_unique hr (ht.congr fun n => (hs n).symm)
  intro f g
  refine ⟨hnec f g, fun hfg => ?_⟩
  have hadj : (f, g) ∈ (hilbertAdjoint A).graph := by
    apply (mem_hilbertAdjoint_graph_iff A hA.1 f g).mpr
    intro x
    have hx := hnec x (A x) ((mem_graph_iff A _).mpr ⟨x.2, rfl⟩)
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hx, hfg] with r hr hs
    rw [hr, hs, inner_smul_left, inner_smul_right]
    simp
  have he : hilbertAdjoint A = A := hA.2.symm
  rwa [he] at hadj

theorem coordinate_measure_absolutelyContinuous
    (C : BoundedRealization (coordinatePVM (M := M) μ)) (f : Lp M 2 μ) : C.measure f ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hzero
  have hp : coordinatePVM μ B f = 0 := by
    apply Lp.ext
    exact (indicator_representative μ hB f).trans
      ((indicator_meas_zero hzero).trans (Lp.coeFn_zero _ _ _).symm)
  rw [C.measure_apply f B hB, hp]
  simp

end IntegralIdentification
theorem restricted_interval_projection_ne_zero (E : Set ℝ) (a b : ℝ)
    (hpos : 0 < volume (E ∩ Ioo a b)) :
    coordinatePVM (M := ℂ) (volume.restrict E) (Ioo a b) ≠ 0 := by
  let μ := volume.restrict E
  have hμ : μ (Ioo a b) ≠ 0 := by
    simpa [μ, Measure.restrict_apply measurableSet_Ioo, inter_comm] using hpos.ne'
  have hfin : μ (Ioo a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact measure_Ioo_lt_top.ne) (Measure.restrict_apply_le _ _)
  let f : Lp ℂ 2 μ := indicatorConstLp 2 measurableSet_Ioo hfin 1
  have hf : f ≠ 0 := by
    intro he
    have he' : indicatorConstLp 2 measurableSet_Ioo hfin (1 : ℂ) =
        indicatorConstLp 2 MeasurableSet.empty (by simp) (1 : ℂ) := by simpa [f] using he
    have hae := (indicatorConstLp_inj measurableSet_Ioo hfin MeasurableSet.empty
      (by simp) one_ne_zero).mp he'
    exact hμ (ae_eq_empty.mp hae)
  intro hz
  have hfix : coordinatePVM μ (Ioo a b) f = f := by
    change indicatorOperator μ (Ioo a b) f = f
    apply Lp.ext
    filter_upwards [indicator_representative μ (show MeasurableSet (Ioo a b) from measurableSet_Ioo) f,
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioo) (hμs := hfin) (c := (1 : ℂ)))]
      with r hr hs
    change f r = _ at hs
    rw [hr]
    by_cases h : r ∈ Ioo a b
    · simp [h]
    · simpa only [Set.indicator_of_notMem h] using hs.symm
  rw [hz, zero_apply] at hfix
  exact hf hfix.symm

/-- Every measurable restriction, including empty and null restrictions, has
its concrete absolutely continuous coordinate spectral model. -/
theorem restricted_spectral_model : CoordinateSpec.RestrictedModelExistence := by
  intro E _hE
  let μ := volume.restrict E
  let P := coordinatePVM (M := ℂ) μ
  obtain ⟨C⟩ := exists_boundedRealization P
  let A := measurableIntegral C (fun r : ℝ => (r : ℂ))
  refine ⟨P, C, A, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro B hB f
    exact indicator_representative μ hB f
  · intro m hm f
    simpa only [smul_eq_mul] using bounded_integral_representative μ C m hm f
  · exact ⟨measurableIntegral_dense C Complex.measurable_ofReal,
      (measurableIntegral_selfAdjoint C Complex.measurable_ofReal (fun _ => rfl)).symm⟩
  · intro f g
    constructor
    · intro hfg
      have he := (coordinate_integral_graph μ C f g).mp hfg
      have he' : (g : ℝ → ℂ) =ᵐ[μ] fun r => (r : ℂ) * f r := by
        simpa only [smul_eq_mul] using he
      exact ⟨(memLp_congr_ae he').mp (Lp.memLp g), he'⟩
    · intro hfg
      exact (coordinate_integral_graph μ C f g).mpr (by simpa only [smul_eq_mul] using hfg.2)
  · intro f
    exact (coordinate_measure_absolutelyContinuous μ C f).trans
      Measure.restrict_le_self.absolutelyContinuous
  · exact restricted_interval_projection_ne_zero E

end ExpandedFA.Models.CoordinateMultiplicationModel

