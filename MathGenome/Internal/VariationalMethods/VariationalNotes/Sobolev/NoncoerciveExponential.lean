import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.NoncoerciveExponential
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology ENNReal
namespace VariationalNotes.Sobolev.NoncoerciveExponential
local instance admissibleNormedSpace : NormedSpace ℝ Admissible := inferInstance
open P102.Trace.Ordinary

/-- The accepted coordinate bridge restricted to the closure-defined zero space. -/
def scalarZero : Admissible →L[ℝ]
    P102.U4.SobolevZero ℝ unitInterval 1 Exponent.two.ennreal :=
  ContinuousLinearMap.codRestrict
    (((ContinuousLinearMap.proj (0 : Fin 1)).comp
      (coordinateEquiv unitInterval Exponent.two).toContinuousLinearMap).comp
      (zeroSubmodule unitInterval 1 Exponent.two).subtypeL)
    (P102.U4.sobolevZeroSubmodule ℝ unitInterval 1 Exponent.two.ennreal)
    (fun (u : Admissible) => (zero_mem_iff_coordinates unitInterval Exponent.two u.val).mp u.property 0)

def zeroExtension :
    P102.U4.SobolevZero ℝ unitInterval 1 Exponent.two.ennreal →ₗᵢ[ℝ]
    P102.U4.Sobolev ℝ (⊤ : Opens (Domain 1)) 1 Exponent.two.ennreal :=
  Classical.choose (P102.U4.zeroExtension_operator unitInterval 1 Exponent.two.ennreal
    (by simp [Exponent.ennreal]))

def wholeMap : Admissible →L[ℝ]
    P102.U4.Sobolev ℝ (⊤ : Opens (Domain 1)) 1 Exponent.two.ennreal :=
  zeroExtension.toContinuousLinearMap.comp scalarZero

/-- The unique continuous representative of the zero extension. -/
def representative (u : Admissible) (t : ℝ) : ℝ :=
  wholeLineRepresentative (wholeMap u) t

lemma representative_continuous (u : Admissible) : Continuous (representative u) :=
  wholeLineRepresentative_continuous (wholeMap u)

lemma representative_evaluation (t : ℝ) : Continuous (fun u => representative u t) :=
  (wholeLineEvaluation t).continuous.comp wholeMap.continuous

lemma representative_bound (u : Admissible) (t : ℝ) :
    ‖representative u t‖ ≤ 2 * ‖wholeMap‖ * ‖u‖ := by
  exact (wholeLineRepresentative_norm_le (wholeMap u) t).trans
    (by nlinarith [wholeMap.le_opNorm u])

@[simp] lemma linePoint_preimage :
    linePoint ⁻¹' (unitInterval : Set (Domain 1)) = Ioo (0 : ℝ) 1 := rfl

lemma representative_ae (u : Admissible) :
    scalarField u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] representative u := by
  have hext := (Classical.choose_spec (P102.U4.zeroExtension_operator unitInterval 1
    Exponent.two.ennreal (by simp [Exponent.ennreal]))).1 (scalarZero u)
  have hcoord : P102.U4.sobolevUnderlying (scalarZero u).val =
      coordinateLp unitInterval Exponent.two 0
        (value unitInterval 1 Exponent.two u.val) :=
    toCoordinates_value unitInterval Exponent.two u.val 0
  have hraw := P102.U4.lpZeroExtension_ae unitInterval Exponent.two.ennreal
    (P102.U4.sobolevUnderlying (scalarZero u).val)
  rw [← hext] at hraw
  have hpull := lineIsometry.measurePreserving.quasiMeasurePreserving.ae hraw
  have hrep := (wholeLineRepresentative_spec (wholeMap u)).1
  filter_upwards [ae_restrict_of_ae hpull, ae_restrict_of_ae hrep,
    ae_restrict_mem measurableSet_Ioo] with t ht hr hmem
  change P102.U4.sobolevUnderlying (zeroExtension (scalarZero u))
    (P102.Trace.Ordinary.linePoint t) = _ at ht
  simp only [lineIsometry_apply] at ht
  rw [Set.indicator_of_mem (show P102.Trace.Ordinary.linePoint t ∈
    (unitInterval : Set (Domain 1)) from hmem), hcoord] at ht
  exact ht.symm.trans hr

lemma functional_eq_representative (u : Admissible) :
    functional u = ∫ t in Ioo (0 : ℝ) 1, Real.exp (-representative u t) := by
  apply integral_congr_ae
  filter_upwards [representative_ae u] with t ht
  rw [ht]

lemma representative_integrable (u : Admissible) :
    IntegrableOn (fun t => Real.exp (-representative u t)) (Ioo (0 : ℝ) 1) :=
  (((Real.continuous_exp.comp (representative_continuous u).neg).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self)

theorem finite : Expected.Finite := by
  intro u
  apply (representative_integrable u).congr
  filter_upwards [representative_ae u] with t ht
  rw [ht]

theorem positive : Expected.Positive := by
  intro u
  have : NeZero (volume.restrict (Ioo (0 : ℝ) 1)) := by
    constructor
    intro h
    have hh := congrArg (fun μ : Measure ℝ => μ Set.univ) h
    norm_num at hh
  exact integral_exp_pos (finite u)

theorem continuity : Expected.Continuity := by
  have h : Continuous (fun u : Admissible =>
      ∫ t in Ioo (0 : ℝ) 1, Real.exp (-representative u t)) := by
    apply continuous_iff_continuousAt.mpr
    intro u₀
    apply continuousAt_of_dominated (bound := fun _ =>
      Real.exp (2 * ‖wholeMap‖ * (‖u₀‖ + 1)))
    · exact Eventually.of_forall fun u =>
        ((Real.continuous_exp.comp (representative_continuous u).neg).aestronglyMeasurable)
    · have hnear : ∀ᶠ u in 𝓝 u₀, ‖u‖ < ‖u₀‖ + 1 :=
        (continuous_norm.tendsto u₀).eventually (gt_mem_nhds (by linarith))
      filter_upwards [hnear] with u hu
      apply Eventually.of_forall
      intro t
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        -representative u t ≤ ‖representative u t‖ := neg_le_abs _
        _ ≤ 2 * ‖wholeMap‖ * ‖u‖ := representative_bound u t
        _ ≤ _ := mul_le_mul_of_nonneg_left hu.le (by positivity)
    · exact integrableOn_const (by simp)
    · exact Eventually.of_forall fun t =>
        (Real.continuous_exp.comp (representative_evaluation t).neg).continuousAt
  exact h.congr (fun u => (functional_eq_representative u).symm)

lemma representative_add (u v : Admissible) (t : ℝ) :
    representative (u + v) t = representative u t + representative v t := by
  exact ((wholeLineEvaluation t).comp wholeMap).map_add u v

lemma representative_smul (c : ℝ) (u : Admissible) (t : ℝ) :
    representative (c • u) t = c * representative u t := by
  exact ((wholeLineEvaluation t).comp wholeMap).map_smul c u

theorem convexity : Expected.Convexity := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  simp only [functional_eq_representative]
  calc
    (∫ t in Ioo (0 : ℝ) 1, Real.exp (-representative (a • u + b • v) t)) ≤
        ∫ t in Ioo (0 : ℝ) 1,
          a * Real.exp (-representative u t) + b * Real.exp (-representative v t) := by
      apply integral_mono (representative_integrable _)
        (((representative_integrable u).const_mul a).add
          ((representative_integrable v).const_mul b))
      intro t
      have hc := convexOn_exp.2 (Set.mem_univ (-representative u t))
        (Set.mem_univ (-representative v t)) ha hb hab
      simpa only [representative_add, representative_smul, smul_eq_mul,
        mul_neg, neg_add_rev, add_comm, Pi.add_apply] using hc
    _ = a * (∫ t in Ioo (0 : ℝ) 1, Real.exp (-representative u t)) +
        b * (∫ t in Ioo (0 : ℝ) 1, Real.exp (-representative v t)) := by
      rw [integral_add ((representative_integrable u).const_mul a)
        ((representative_integrable v).const_mul b), integral_const_mul, integral_const_mul]
    _ = _ := rfl

lemma linePoint_coordinate (x : Domain 1) : linePoint (x 0) = x := by
  ext i
  exact congrArg x (Subsingleton.elim _ _)

lemma interval_subset_compact : (unitInterval : Set (Domain 1)) ⊆
    lineIsometry '' Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨x 0, ⟨hx.1.le, hx.2.le⟩, linePoint_coordinate x⟩

instance intervalFinite : IsFiniteMeasure (domainMeasure unitInterval) := by
  apply isFiniteMeasure_restrict.mpr
  exact ne_top_of_le_ne_top (isCompact_Icc.image lineIsometry.continuous).measure_ne_top
    (measure_mono interval_subset_compact)

lemma continuous_memLp (f : Domain 1 → ℝ) (hf : Continuous f) :
    MemLp f Exponent.two.ennreal (domainMeasure unitInterval) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image lineIsometry.continuous).bddAbove_image
    hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem unitInterval.isOpen.measurableSet] with x hx
  exact hC (Set.mem_image_of_mem _ (interval_subset_compact hx))

/-- Smooth restrictions with their actual distributional derivatives. -/
lemma smooth_sobolev (f : Domain 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ u : P102.U4.Sobolev ℝ unitInterval 1 Exponent.two.ennreal,
      (P102.U4.sobolevUnderlying u : Domain 1 → ℝ) =ᵐ[domainMeasure unitInterval] f := by
  open P102.U4 in
  let v (α : SobolevIndex 1 1) : DomainLp ℝ unitInterval Exponent.two.ennreal :=
    (continuous_memLp (multiPartial f α.val)
      (partialWord_contDiff hf _).continuous).toLp (multiPartial f α.val)
  have hv (α : P102.U4.SobolevIndex 1 1) :
      (v α : Domain 1 → ℝ) =ᵐ[domainMeasure unitInterval]
        P102.U4.multiPartial f α.val := MemLp.coeFn_toLp _
  have hv0 : (v (P102.U4.zeroSobolevIndex 1 1) : Domain 1 → ℝ)
      =ᵐ[domainMeasure unitInterval] f := by
    simpa [P102.U4.zeroSobolevIndex, P102.U4.multiPartial, P102.U4.partialWord] using
      hv (P102.U4.zeroSobolevIndex 1 1)
  have hreg0 := (P102.U4.regular_injectivity 1 ℝ unitInterval _ _
    (P102.U4.domainLp_locallyIntegrable unitInterval Exponent.two.ennreal _)
    (hf.continuous.continuousOn.locallyIntegrableOn unitInterval.isOpen.measurableSet)).mpr hv0
  have heq (α : P102.U4.SobolevIndex 1 1) :
      P102.U4.distributionPartial α.val
        (P102.U4.regularDistribution unitInterval (v (P102.U4.zeroSobolevIndex 1 1))) =
      P102.U4.regularDistribution unitInterval (v α) := by
    rw [hreg0, P102.U4.derivative_classicalCompatibility 1 ℝ unitInterval α.val f
      (hf.of_le (by simp)).contDiffOn]
    exact ((P102.U4.regular_injectivity 1 ℝ unitInterval _ _
      (P102.U4.domainLp_locallyIntegrable unitInterval Exponent.two.ennreal _)
      ((P102.U4.partialWord_contDiff hf _).continuous.continuousOn.locallyIntegrableOn
        unitInterval.isOpen.measurableSet)).mpr (hv α)).symm
  refine ⟨⟨WithLp.toLp 1 v,
    (P102.U4.mem_sobolevSubmodule_iff unitInterval 1 Exponent.two.ennreal _).mpr ?_⟩, hv0⟩
  intro α φ
  exact (P102.U4.distributionPartial_eq_regularLp_iff unitInterval Exponent.two.ennreal
    α.val _ _).mp (heq α) φ

lemma interval_lipschitz : P102.Sobolev.Geometry.IsLipschitzOpen
    (P102.Sobolev.Extension.geometricOpen
      (P102.Sobolev.Geometry.verticalLine.trans lineIsometry) unitInterval :
        Set (P102.U4.GraphPieces.Ambient 0)) := by
  have h := P102.Sobolev.Geometry.interval_union_lipschitz
    (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => by norm_num) (by
      intro x y h
      rcases x with x | x <;> rcases y with y | y
      · congr 1; exact Subsingleton.elim _ _
      · norm_num at h
      · norm_num at h
      · congr 1; exact Subsingleton.elim _ _)
    (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
  rw [Set.iUnion_const] at h
  simpa [P102.Sobolev.Extension.geometricOpen, unitInterval,
    P102.Sobolev.Geometry.verticalLine, lineIsometry,
    P102.Trace.Ordinary.linePoint] using h

lemma frontier_coordinate {x : Domain 1}
    (hx : x ∈ frontier (unitInterval : Set (Domain 1))) : x 0 = 0 ∨ x 0 = 1 := by
  have hpre : (unitInterval : Set (Domain 1)) =
      lineIsometry.toHomeomorph.symm ⁻¹' Ioo (0 : ℝ) 1 := rfl
  rw [hpre, ← lineIsometry.toHomeomorph.symm.preimage_frontier,
    frontier_Ioo (by norm_num : (0 : ℝ) < 1)] at hx
  change lineIsometry.symm x ∈ ({0, 1} : Set ℝ) at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change x 0 = 0 ∨ x 0 = 1 at hx
  exact hx

lemma exists_base_profile : ∃ u : Admissible,
    scalarField u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] profile 1 := by
  let f : Domain 1 → ℝ := fun x => x 0 * (1 - x 0)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contDiff.mul
      (contDiff_const.sub (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contDiff)
  obtain ⟨u, hu⟩ := smooth_sobolev f hf
  obtain ⟨C, hC, T, hT, _, _⟩ := trace_exists 0
    (P102.Sobolev.Geometry.verticalLine.trans lineIsometry) unitInterval
    interval_lipschitz ℝ Exponent.two.ennreal (by simp [Exponent.ennreal])
  have hTu : T u = 0 := by
    apply Lp.ext
    have ht := hT u f (hf.of_le (by simp)) hu
    filter_upwards [ht, boundaryMeasure_ae_frontier unitInterval,
      Lp.coeFn_zero ℝ Exponent.two.ennreal (boundaryMeasure unitInterval)] with x hx hfront hz
    rw [hx, hz]
    rcases frontier_coordinate hfront with h | h <;> simp [f, h]
  have hu0 : u ∈ P102.U4.sobolevZeroSubmodule ℝ unitInterval 1 Exponent.two.ennreal := by
    rw [← ordinary_trace.2.1 0 (P102.Sobolev.Geometry.verticalLine.trans lineIsometry)
      unitInterval interval_lipschitz ℝ Exponent.two.ennreal
      (by simp [Exponent.ennreal]) T hT]
    exact hTu
  let v := (coordinateEquiv unitInterval Exponent.two).symm (fun _ : Fin 1 => u)
  have hv : coordinateEquiv unitInterval Exponent.two v = fun _ : Fin 1 => u :=
    (coordinateEquiv unitInterval Exponent.two).apply_symm_apply _
  have hv0 : v ∈ zeroSubmodule unitInterval 1 Exponent.two := by
    rw [zero_mem_iff_coordinates]
    intro i
    rw [hv]
    exact hu0
  refine ⟨⟨v, hv0⟩, ?_⟩
  have hval : coordinateLp unitInterval Exponent.two 0
      (value unitInterval 1 Exponent.two v) = P102.U4.sobolevUnderlying u := by
    rw [← toCoordinates_value]
    exact congrArg P102.U4.sobolevUnderlying (congrFun hv 0)
  have hpull := linePoint_ae_restrict hu
  change ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
    P102.U4.sobolevUnderlying u (linePoint t) = f (linePoint t) at hpull
  unfold scalarField
  rw [hval]
  exact hpull.mono fun t ht => by simpa [f, profile, linePoint] using ht

lemma profile_integrals_tendsto :
    Tendsto (fun n => ∫ t in Ioo (0 : ℝ) 1, Real.exp (-profile n t)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun n t => Real.exp (-profile n t)) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (by unfold profile; fun_prop : Continuous (fun t => Real.exp (-profile n t))).aestronglyMeasurable)
    (integrableOn_const (by simp))
    (fun n => ?_) ?_
  · simpa using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ profile n t := mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) ht.1.le) (sub_nonneg.mpr ht.2.le)
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hq : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
    have hn : Tendsto (fun n : ℕ => (n : ℝ) * (t * (1 - t))) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hq
    have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hn)
    simpa only [profile, mul_assoc, Function.comp_def] using he

lemma representative_eq_of_profile (u : Admissible) (n : ℕ)
    (hu : scalarField u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] profile n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : representative u t = profile n t := by
  exact Measure.eqOn_open_of_ae_eq ((representative_ae u).symm.trans hu)
    isOpen_Ioo (representative_continuous u).continuousOn
    (by unfold profile; fun_prop : Continuous (profile n)).continuousOn ht

theorem minimizingSequence : Expected.MinimizingSequence := by
  obtain ⟨u, hu⟩ := exists_base_profile
  let w : ℕ → Admissible := fun n => (n : ℝ) • u
  have hw (n : ℕ) : scalarField (w n) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] profile n := by
    filter_upwards [representative_ae (w n), representative_ae u, hu] with t hw hu' hprofile
    rw [hw]
    change representative ((n : ℝ) • u) t = profile n t
    rw [representative_smul, ← hu', hprofile]
    simp [profile]
    ring
  refine ⟨w, hw, ?_, ?_⟩
  · have he (n : ℕ) : functional (w n) =
        ∫ t in Ioo (0 : ℝ) 1, Real.exp (-profile n t) := by
      apply integral_congr_ae
      filter_upwards [hw n] with t ht
      rw [ht]
    simpa only [he] using profile_integrals_tendsto
  · have hbound (n : ℕ) : (n : ℝ) / 4 ≤ 2 * ‖wholeMap‖ * ‖w n‖ := by
      have he := representative_eq_of_profile (w n) n (hw n)
        (t := (1 / 2 : ℝ)) (by norm_num)
      have hb := representative_bound (w n) (1 / 2)
      have hp : profile n (1 / 2) = (n : ℝ) / 4 := by unfold profile; ring
      rw [he, hp, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (by norm_num))] at hb
      exact hb
    have hC : 0 < 2 * ‖wholeMap‖ := by
      have hb := hbound 1
      have hn := norm_nonneg (w 1)
      have hm := norm_nonneg wholeMap
      norm_num only [Nat.cast_one] at hb
      nlinarith
    have hlow (n : ℕ) : (n : ℝ) / (4 * (2 * ‖wholeMap‖)) ≤ ‖w n‖ := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * (2 * ‖wholeMap‖))).mpr
      have hb := hbound n
      nlinarith
    exact tendsto_atTop_mono hlow
      (tendsto_natCast_atTop_atTop.atTop_div_const (by positivity))

theorem infimum : Expected.Infimum := by
  obtain ⟨w, _, hw, _⟩ := minimizingSequence
  refine ⟨?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact (positive u).le
  · intro b hb
    apply ge_of_tendsto hw
    exact Eventually.of_forall fun n => hb (show functional (w n) ∈ Set.range functional from ⟨w n, rfl⟩)

theorem noMinimizer : Expected.NoMinimizer := by
  rintro ⟨u, hu⟩
  have hle : functional u ≤ 0 := infimum.2 (by rintro _ ⟨v, rfl⟩; exact hu v)
  exact (not_lt_of_ge hle) (positive u)

end VariationalNotes.Sobolev.NoncoerciveExponential
