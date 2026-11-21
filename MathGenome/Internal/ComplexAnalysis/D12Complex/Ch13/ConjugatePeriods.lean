import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.ConjugatePeriods
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.LocalConjugateRegularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.HomotopyIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyFormula
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PrincipalLogarithm
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Batteries.Tactic.OpenPrivate

noncomputable section
open Complex Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology BigOperators
open private partialX_eq partialY_eq from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential

namespace D12Complex.ConjugatePeriods
abbrev conjugateField := D12Complex.conjugateField
abbrev conjugateForm := D12Complex.conjugateForm
abbrev conjugatePeriod := D12Complex.conjugatePeriod

lemma conjugateForm_apply :
    Specs.D12Complex.Ch13.ConjugatePeriods.conjugateForm_apply_type := by
  intro u z w
  simp [D12Complex.conjugateForm]

lemma field_mul_im (u : ℂ → ℝ) (z w : ℂ) :
    (conjugateField u z * w).im = conjugateForm u z w := by
  simp [D12Complex.conjugateField, D12Complex.conjugateForm, mul_im]
  ring

lemma field_eq_fderiv {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u)
    {z : ℂ} (hz : z ∈ U) :
    conjugateField u z = (fderiv ℝ u z 1 : ℂ) - I * (fderiv ℝ u z I : ℂ) := by
  have hd := ((hu.2.1 z hz).contDiffAt (hu.1.mem_nhds hz)).differentiableAt
    (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  simp only [conjugateField, D12Complex.conjugateField, partialX_eq u z hd, partialY_eq u z hd]

lemma field_holomorphic {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u) :
    HolomorphicOn U (conjugateField u) := by
  have hh := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hu.1).mp hu
  refine ⟨hu.1, fun z hz => ?_⟩
  apply (HarmonicAt.differentiableAt_complex_partial (hh z hz)).congr_of_eventuallyEq
  filter_upwards [hu.1.mem_nhds hz] with w hw
  exact field_eq_fderiv hu hw

lemma field_continuous {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u) :
    ContinuousOn (conjugateField u) U :=
  HomotopyIntegrals.continuousOn_of_holomorphic (field_holomorphic hu)

lemma conjugatePeriod_coordinates :
    Specs.D12Complex.Ch13.ConjugatePeriods.conjugatePeriod_coordinates_type := by
  intro U u hu γ hγ
  unfold D12Complex.conjugatePeriod PiecewiseC1Path.integral C1Partition.integral
  rw [show (∑ i : Fin γ.partition.count,
      ∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
        D12Complex.conjugateField u (γ t) *
          derivWithin γ (γ.partition.pieceSet i) t).im =
      ∑ i : Fin γ.partition.count,
        (∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
          D12Complex.conjugateField u (γ t) *
            derivWithin γ (γ.partition.pieceSet i) t).im from map_sum imAddGroupHom _ _]
  apply Finset.sum_congr rfl
  intro i _
  have hi := γ.partition.piece_integrable (D12Complex.conjugateField u)
    ((field_continuous hu).mono hγ) i
  rw [← imCLM_apply (∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
    D12Complex.conjugateField u (γ t) * derivWithin γ (γ.partition.pieceSet i) t)]
  rw [← imCLM.intervalIntegral_comp_comm hi]
  congr 1
  funext t
  exact (field_mul_im u (γ t) (derivWithin γ (γ.partition.pieceSet i) t)).trans
    (conjugateForm_apply u (γ t) (derivWithin γ (γ.partition.pieceSet i) t))

/-- Multiplication by the complex gradient has real coordinate du. -/
lemma field_mul_re {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u)
    {z : ℂ} (hz : z ∈ U) (w : ℂ) :
    (conjugateField u z * w).re = fderiv ℝ u z w := by
  rw [field_eq_fderiv hu hz]
  calc
    _ = fderiv ℝ u z 1 * w.re + fderiv ℝ u z I * w.im := by simp [mul_re, mul_im]
    _ = fderiv ℝ u z (w.re • (1 : ℂ) + w.im • I) := by
      simp only [map_add, map_smul, smul_eq_mul]; ring
    _ = _ := by congr 1; simp

lemma field_real_part {U : Set ℂ} {F : ℂ → ℂ} (hF : HolomorphicOn U F)
    {z : ℂ} (hz : z ∈ U) :
    conjugateField (fun w => (F w).re) z = deriv F z := by
  have hd := hF.2 z hz
  obtain ⟨hX, hY, _, _⟩ := coordinate_partials F z (hd.restrictScalars ℝ)
  have hr (w : ℂ) : fderiv ℝ F z w = deriv F z * w := by
    rw [hd.hasDerivAt.complexToReal_fderiv.fderiv]; simp
  simp only [D12Complex.conjugateField, hX, hY, hr, mul_one]
  apply Complex.ext <;> simp [mul_re, mul_im]

lemma conjugate_isPrimitive {U : Set ℂ} {u v : ℂ → ℝ}
    (hv : HarmonicConjugateOn U u v) :
    Primitives.IsPrimitive U (conjugateField u) (fun z => (u z : ℂ) + I * (v z : ℂ)) := by
  refine ⟨hv, fun z hz => ?_⟩
  simpa using (field_real_part hv hz).symm

lemma conjugate_period_endpoint :
    Specs.D12Complex.Ch13.ConjugatePeriods.conjugate_period_endpoint_type := by
  intro U u v hv γ hγ
  have hu := (LocalConjugateRegularity.conjugate_harmonic U u v hv).1
  have he := Primitives.piecewise_endpoint U _ _ (field_continuous hu)
    (conjugate_isPrimitive hv) γ hγ
  simpa [D12Complex.conjugatePeriod] using congrArg Complex.im he

/-- FTC for the real coordinate, proved on the smooth pieces and telescoped. -/
lemma field_re_endpoint {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ U) :
    (γ.integral (conjugateField u)).re = u γ.path.target - u γ.path.source := by
  let P := γ.partition
  have hf := (field_continuous hu).mono hγ
  have huc : ContinuousOn u U := hu.2.1.continuousOn
  have hcomp : ContinuousOn (u ∘ γ) (Icc γ.path.a γ.path.b) :=
    huc.comp γ.path.continuousOn (fun t ht => hγ ⟨t, ht, rfl⟩)
  have hpieces (i : Fin P.count) :
      (∫ t in P.node i.castSucc..P.node i.succ,
        (conjugateField u (γ t) * deriv γ t).re) =
        u (γ (P.node i.succ)) - u (γ (P.node i.castSucc)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (P.piece_lt i).le
      (hcomp.mono (P.piece_subset i))
    · intro t ht
      have hz := hγ ⟨t, P.piece_subset i ⟨ht.1.le, ht.2.le⟩, rfl⟩
      have hd := ((hu.2.1 _ hz).contDiffAt (hu.1.mem_nhds hz)).differentiableAt
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
      rw [field_mul_re hu hz]
      exact hd.hasFDerivAt.comp_hasDerivAt t (P.differentiableAt_piece i ht).hasDerivAt
    · have hi := P.piece_integrable_deriv (conjugateField u) hf i
      exact ⟨reCLM.integrable_comp hi.1, reCLM.integrable_comp hi.2⟩
  change reCLM (P.integral (conjugateField u)) = _
  rw [C1Partition.integral_eq_intervalIntegral γ.path P (conjugateField u) hf,
    ← reCLM.intervalIntegral_comp_comm (P.parameter_integrable _ _ hf)]
  simp only [reCLM_apply]
  rw [← P.first, ← P.last,
    ← (intervalIntegral_fin_partition P.node
      (fun t => (conjugateField u (γ t) * deriv γ t).re)
      (fun i => by
        have hi := P.piece_integrable_deriv (conjugateField u) hf i
        exact ⟨reCLM.integrable_comp hi.1, reCLM.integrable_comp hi.2⟩)).2]
  simp_rw [hpieces]
  rw [Finset.sum_sub_distrib]
  have h := (Fin.sum_univ_succ (fun i => u (γ (P.node i)))).symm.trans
    (Fin.sum_univ_castSucc (fun i => u (γ (P.node i))))
  simp only [ComplexPath.target, ComplexPath.source, ← P.first, ← P.last]
  linarith

lemma primitive_re_fderiv {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u)
    {F : ℂ → ℂ} (hF : Primitives.IsPrimitive U (conjugateField u) F)
    {z : ℂ} (hz : z ∈ U) :
    fderiv ℝ (fun w => (F w).re) z = fderiv ℝ u z := by
  have hd := (hF.1.2 z hz).hasDerivAt.complexToReal_fderiv
  have hr := reCLM.hasFDerivAt.comp z hd
  change fderiv ℝ (reCLM ∘ F) z = _
  rw [hr.fderiv, hF.2 z hz]
  ext w
  simpa using field_mul_re hu hz w

lemma conjugate_of_primitive {U : Set ℂ} {u : ℂ → ℝ}
    (hU : IsDomain U) (hu : HarmonicOn U u)
    {F : ℂ → ℂ} (hF : Primitives.IsPrimitive U (conjugateField u) F) :
    ∃ v : ℂ → ℝ, HarmonicConjugateOn U u v := by
  have hdF : DifferentiableOn ℝ (fun z => (F z).re) U :=
    fun z hz => (reCLM.differentiableAt.comp z
      ((hF.1.2 z hz).restrictScalars ℝ)).differentiableWithinAt
  obtain ⟨c, hc⟩ := hU.2.1.exists_eq_add_of_fderiv_eq hU.2.2
    (hu.2.1.differentiableOn (by norm_num)) hdF
    (fun z hz => (primitive_re_fderiv hu hF hz).symm)
  refine ⟨fun z => (F z).im, hU.2.1, fun z hz => ?_⟩
  apply ((hF.1.2 z hz).add_const (c : ℂ)).congr_of_eventuallyEq
  filter_upwards [hU.2.1.mem_nhds hz] with w hw
  apply Complex.ext <;> simp [hc hw]

lemma global_conjugate_iff_zero_periods :
    Specs.D12Complex.Ch13.ConjugatePeriods.global_conjugate_iff_zero_periods_type := by
  intro U u hU hu
  constructor
  · rintro ⟨v, hv⟩ γ hγ hclosed
    rw [conjugate_period_endpoint U u v hv γ hγ, hclosed, sub_self]
  · intro hperiod
    have hp : Primitives.ZeroPeriods U (conjugateField u) := by
      intro γ hγ hclosed
      apply Complex.ext
      · rw [field_re_endpoint hu γ hγ, hclosed, sub_self]; rfl
      · exact hperiod γ hγ hclosed
    obtain ⟨F, hF⟩ := (Primitives.primitive_criterion U _ hU (field_continuous hu)).1.mpr
      ((Primitives.endpointIndependent_iff_zeroPeriods U _ (field_continuous hu)).mpr hp)
    exact conjugate_of_primitive hU hu hF

lemma conjugate_unique :
    Specs.D12Complex.Ch13.ConjugatePeriods.conjugate_unique_type := by
  intro U u v w hU hv hw
  obtain ⟨c, hc⟩ := Primitives.primitive_unique U (conjugateField u)
    (fun z => (u z : ℂ) + I * (v z : ℂ))
    (fun z => (u z : ℂ) + I * (w z : ℂ)) hU
    (conjugate_isPrimitive hv) (conjugate_isPrimitive hw)
  exact ⟨c.im, fun z hz => by simpa using congrArg Complex.im (hc z hz)⟩

/-- Normalize an arbitrary compact parameter interval before contracting it.
No differentiability is required of the contraction. -/
lemma zeroPeriods_of_simplyConnected {U : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn U f) (hU : IsSimplyConnected U) :
    Primitives.ZeroPeriods U f := by
  intro γ hγ hclosed
  have ht (t : unitInterval) : γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ) ∈
      Icc γ.path.a γ.path.b := by
    have hd := sub_nonneg.mpr γ.path.ordered
    constructor <;> nlinarith [t.property.1, t.property.2]
  let p : Path γ.path.source γ.path.source := {
    toFun := fun t => γ (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ))
    continuous_toFun := γ.path.continuousOn.comp_continuous (by fun_prop) ht
    source' := by simp [ComplexPath.source]
    target' := by simpa [ComplexPath.source, ComplexPath.target] using (show γ.path.target = γ.path.source from hclosed) }
  obtain ⟨H, hH⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hU).2
    γ.path.source p (fun t => hγ ⟨_, ht t, rfl⟩)
  apply HomotopyIntegrals.null_homotopic_integral U f hf γ hγ hclosed
  refine ⟨γ.path.source, H.toContinuousMap, hH, ?_, ?_, ?_⟩
  · intro t; exact H.apply_zero t
  · intro t; exact H.apply_one t
  · intro t; simp

lemma simply_connected_conjugate :
    Specs.D12Complex.Ch13.ConjugatePeriods.simply_connected_conjugate_type := by
  intro U u hU hu hsc
  apply (global_conjugate_iff_zero_periods U u hU hu).mpr
  intro γ hγ hclosed
  have h := zeroPeriods_of_simplyConnected (field_holomorphic hu) hsc γ hγ hclosed
  exact congrArg Complex.im h

lemma log_norm_harmonic :
    Specs.D12Complex.Ch13.ConjugatePeriods.log_norm_harmonic_type := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _
    isClosed_singleton.isOpen_compl).mpr
  intro z hz
  exact (analyticAt_id (𝕜 := ℂ)).harmonicAt_log_norm (by simpa using hz)

/-- Both z and -z have the same logarithmic modulus, and at least one lies
in the slit plane. Thus the computation applies at every nonzero point. -/
lemma log_norm_field {z : ℂ} (hz : z ≠ 0) :
    conjugateField (fun w => Real.log ‖w‖) z = z⁻¹ := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with h | h
  · have hz' : z ∈ PrincipalSlitPlane := by
      rwa [PrincipalLogarithm.principalSlitPlane_eq_slitPlane]
    have hh := field_real_part PrincipalLogarithm.holomorphicOn_principalLog hz'
    rw [PrincipalLogarithm.deriv_principalLog z hz'] at hh
    simpa [PrincipalLog, one_div] using hh
  · let V : Set ℂ := {w | -w ∈ PrincipalSlitPlane}
    have hV : IsOpen V := PrincipalLogarithm.isOpen_principalSlitPlane.preimage
      (by fun_prop)
    have hF : HolomorphicOn V (fun w => PrincipalLog (-w)) := by
      refine ⟨hV, fun w hw => ?_⟩
      exact ((PrincipalLogarithm.hasDerivAt_principalLog (-w) hw).comp w
        (hasDerivAt_id w).neg).differentiableAt
    have hz' : z ∈ V := by
      change -z ∈ PrincipalSlitPlane
      rwa [PrincipalLogarithm.principalSlitPlane_eq_slitPlane]
    have hh := field_real_part hF hz'
    have hd : HasDerivAt (fun w => PrincipalLog (-w)) (z⁻¹) z := by
      convert (PrincipalLogarithm.hasDerivAt_principalLog (-z) hz').comp z
        (hasDerivAt_id z).neg using 1 <;> simp [Function.comp_def]
    rw [hd.deriv] at hh
    simpa [PrincipalLog] using hh

lemma path_integral_congr (γ : PiecewiseC1Path) {f g : ℂ → ℂ}
    (h : EqOn f g γ.trace) : γ.integral f = γ.integral g := by
  unfold PiecewiseC1Path.integral C1Partition.integral
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr_Ioo_of_le (γ.partition.piece_lt i).le
  intro t ht
  exact congrArg (fun a => a * derivWithin γ (γ.partition.pieceSet i) t)
    (h ⟨t, γ.partition.piece_subset i ⟨ht.1.le, ht.2.le⟩, rfl⟩)

lemma circle_trace_ne_zero (c : ℂ) (r : ℝ) (hr : 0 < r) (hc : ‖c‖ < r) :
    (DiskCauchyFormula.circlePath c r).trace ⊆ ({0}ᶜ : Set ℂ) := by
  rw [DiskCauchyFormula.circlePath_trace c r hr.le]
  intro z hz
  simp only [mem_compl_iff, mem_singleton_iff]
  intro he
  subst z
  have hzr : ‖c‖ = r := by simpa [mem_sphere, dist_eq_norm] using hz
  linarith

lemma log_norm_circle_period :
    Specs.D12Complex.Ch13.ConjugatePeriods.log_norm_circle_period_type := by
  intro c r hr hc
  have htrace := circle_trace_ne_zero c r hr hc
  have he : (DiskCauchyFormula.circlePath c r).integral
      (conjugateField (fun z => Real.log ‖z‖)) =
      (DiskCauchyFormula.circlePath c r).integral (fun z => (z - 0)⁻¹) := by
    apply path_integral_congr
    intro z hz
    simpa using log_norm_field (by simpa using htrace hz)
  unfold D12Complex.conjugatePeriod
  rw [he, DiskCauchyFormula.circle_integral_sub_inv c 0 r hr (by simpa using hc)]
  simp

lemma log_norm_no_conjugate :
    Specs.D12Complex.Ch13.ConjugatePeriods.log_norm_no_conjugate_type := by
  rintro ⟨v, hv⟩
  have he := conjugate_period_endpoint _ _ v hv (DiskCauchyFormula.circlePath 0 1)
    (circle_trace_ne_zero 0 1 zero_lt_one (by simp))
  rw [log_norm_circle_period 0 1 zero_lt_one (by simp),
    DiskCauchyFormula.circlePath_closed 0 1, sub_self] at he
  linarith [Real.pi_pos]

end D12Complex.ConjugatePeriods
