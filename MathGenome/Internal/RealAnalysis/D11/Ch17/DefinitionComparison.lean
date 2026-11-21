import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.DefinitionComparison
import MathGenome.Internal.RealAnalysis.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.D11.Ch05.MarkovZeroFinite

open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace D11.Ch17.DefinitionComparison
open D11.Ch17.UniformControls

variable {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Split at an amplitude cutoff, uniformly in the measurable set of integration. -/
theorem absoluteIntegral_le_cutoff (μ : Measure X) (f : X → 𝕜)
    (hf : Measurable f) (A : Set X) (R : ℝ) :
    absoluteIntegral μ f A ≤ ENNReal.ofReal R * μ A +
      absoluteIntegral μ f {x | R < ‖f x‖} := by
  let T := {x | R < ‖f x‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const hf.norm
  simp only [absoluteIntegral_formula]
  calc
    ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ ≤
        ∫⁻ x in A, ENNReal.ofReal R + T.indicator (fun x => ENNReal.ofReal ‖f x‖) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ T
      · simp only [indicator_of_mem hx]
        exact le_add_left le_rfl
      · simp only [indicator_of_notMem hx, add_zero]
        exact ENNReal.ofReal_le_ofReal (le_of_not_gt hx)
    _ = ENNReal.ofReal R * μ A +
        ∫⁻ x in A, T.indicator (fun x => ENNReal.ofReal ‖f x‖) x ∂μ := by
      rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal R * μ A + ∫⁻ x, T.indicator (fun x => ENNReal.ofReal ‖f x‖) x ∂μ := by
      gcongr
      exact Measure.restrict_le_self
    _ = ENNReal.ofReal R * μ A + ∫⁻ x in T, ENNReal.ofReal ‖f x‖ ∂μ := by
      rw [lintegral_indicator hT]

theorem integralSup_le_cutoff (μ : Measure X) (F : ι → X → 𝕜)
    (hF : integrableFamily μ F) (A : Set X) (R : ℝ) :
    integralSup μ F A ≤ ENNReal.ofReal R * μ A + amplitudeSup μ F R := by
  apply iSup_le
  intro i
  exact (absoluteIntegral_le_cutoff μ (F i) (hF i).1 A R).trans
    (add_le_add le_rfl (le_iSup (fun i => absoluteIntegral μ (F i) {x | R < ‖F i x‖}) i))

theorem tail_implies_small : Specs.D11.Ch17.DefinitionComparison.tail_implies_small := by
  intro X ι 𝕜 _ _ _ _ μ F h
  change uiTail μ F at h
  change uiSmall μ F
  refine ⟨h.1, ?_⟩
  intro ε hε
  have hhalf : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (half_pos hε)
  obtain ⟨R, hR⟩ := ((tendsto_order.1 h.2).2 _ hhalf).exists
  obtain ⟨δ, hδ, hδR⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (ENNReal.ofReal_ne_top (r := R)) hhalf.ne'
  refine ⟨(δ : ℝ), hδ, ?_⟩
  intro A _hA hA
  apply (integralSup_le_cutoff μ F h.1 A R).trans_lt
  have hprod : ENNReal.ofReal R * μ A < ENNReal.ofReal (ε / 2) := by
    apply lt_of_le_of_lt (mul_le_mul' le_rfl hA.le) _
    simpa only [ENNReal.ofReal_coe_nnreal, mul_comm] using hδR
  calc
    ENNReal.ofReal R * μ A + amplitudeSup μ F R <
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hprod hR
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- The strict amplitude set has the usual Markov bound. -/
theorem measure_amplitude_le (μ : Measure X) (f : X → 𝕜)
    (hf : Measurable f) (R : ℝ) (hR : 0 < R) :
    μ {x | R < ‖f x‖} ≤ absoluteIntegral μ f univ / ENNReal.ofReal R := by
  rw [absoluteIntegral_formula, Measure.restrict_univ]
  apply le_trans (measure_mono ?_) (meas_ge_le_lintegral_div
    hf.norm.ennreal_ofReal.aemeasurable (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top)
  intro x hx
  exact ENNReal.ofReal_le_ofReal (le_of_lt hx)

theorem small_and_bound_implies_tail :
    Specs.D11.Ch17.DefinitionComparison.small_and_bound_implies_tail := by
  intro X ι 𝕜 _ _ _ _ μ F hs hb
  change uiSmall μ F at hs
  change uniformL1Bound μ F at hb
  change uiTail μ F
  refine ⟨hs.1, ENNReal.tendsto_atTop_zero.mpr ?_⟩
  intro ε hε
  obtain ⟨e, he, heε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hepos : 0 < (e : ℝ) := by exact_mod_cast he
  obtain ⟨δ, hδ, hsmall⟩ := hs.2 (e : ℝ) hepos
  let M := integralSup μ F univ
  let R : ℝ := (M.toReal + 1) / δ
  have hR : 0 < R := div_pos (by positivity) hδ
  have hMR : M < ENNReal.ofReal δ * ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_mul hδ.le]
    dsimp [R]
    rw [mul_div_cancel₀ _ hδ.ne']
    calc
      M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal (show M ≠ ∞ from hb.2.ne)).symm
      _ < ENNReal.ofReal (M.toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (lt_add_one _)
  refine ⟨R, ?_⟩
  intro r hRr
  have hr : 0 < r := hR.trans_le hRr
  apply le_trans (iSup_le fun i => ?_) heε.le
  have hmeasure : μ {x | r < ‖F i x‖} < ENNReal.ofReal δ := by
    calc
      μ {x | r < ‖F i x‖} ≤ absoluteIntegral μ (F i) univ / ENNReal.ofReal r :=
        measure_amplitude_le μ (F i) (hs.1 i).1 r hr
      _ ≤ M / ENNReal.ofReal r :=
        ENNReal.div_le_div_right (le_iSup (fun i => absoluteIntegral μ (F i) univ) i) _
      _ < ENNReal.ofReal δ := ENNReal.div_lt_of_lt_mul
        (hMR.trans_le (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hRr)))
  exact (le_iSup (fun j => absoluteIntegral μ (F j) {x | r < ‖F i x‖}) i).trans
    ((hsmall _ (measurableSet_lt measurable_const (hs.1 i).1.norm) hmeasure).le.trans_eq
      (ENNReal.ofReal_coe_nnreal))

theorem tail_implies_bound_of_finite :
    Specs.D11.Ch17.DefinitionComparison.tail_implies_bound_of_finite := by
  intro X ι 𝕜 _ _ _ _ μ F hμ h
  change uiTail μ F at h
  change uniformL1Bound μ F
  obtain ⟨R, hR⟩ := ((tendsto_order.1 h.2).2 1 zero_lt_one).exists
  refine ⟨h.1, (integralSup_le_cutoff μ F h.1 univ R).trans_lt ?_⟩
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ,
    hR.trans ENNReal.one_lt_top⟩

theorem atomic_ui_counterexample :
    Specs.D11.Ch17.DefinitionComparison.atomic_ui_counterexample := by
  classical
  let μ : Measure Unit := Measure.dirac ()
  let F : ℕ → Unit → ℝ := fun n _ => (n : ℝ)
  have hconst (n : ℕ) (A : Set Unit) :
      absoluteIntegral μ (F n) A = (n : ℝ≥0∞) * μ A := by
    rw [absoluteIntegral_formula]
    simp only [F, Real.norm_natCast, ENNReal.ofReal_natCast, setLIntegral_const]
  have hnorm (n : ℕ) : absoluteIntegral μ (F n) univ = (n : ℝ≥0∞) := by
    simp [hconst, μ]
  have hfamily : integrableFamily μ F := by
    intro n
    refine ⟨measurable_const, ?_⟩
    have hh := hnorm n
    unfold absoluteIntegral at hh
    rw [Measure.restrict_univ] at hh
    rw [hh]
    exact ENNReal.natCast_lt_top n
  have hsmall : uiSmall μ F := by
    refine ⟨hfamily, fun ε hε => ⟨1, zero_lt_one, ?_⟩⟩
    intro A _hA hA
    have hempty : A = ∅ := by
      have hnot : () ∉ A := by
        intro hx
        have : μ A = 1 := Measure.dirac_apply_of_mem hx
        simp only [this, ENNReal.ofReal_one, lt_self_iff_false] at hA
      ext x
      cases x
      simp [hnot]
    simp only [hempty, integralSup, hconst, measure_empty, mul_zero, iSup_const]
    exact ENNReal.ofReal_pos.mpr hε
  have hsup : integralSup μ F univ = ∞ := by
    simp only [integralSup, hnorm, ENNReal.iSup_natCast]
  have htail (R : ℝ) : amplitudeSup μ F R = ∞ := by
    apply top_unique
    rw [← ENNReal.iSup_natCast]
    apply iSup_le
    intro n
    obtain ⟨k, hk⟩ := exists_nat_gt R
    let m := max n k
    have hRm : R < (m : ℝ) := hk.trans_le (by exact_mod_cast (le_max_right n k))
    have hset : {x : Unit | R < ‖F m x‖} = univ := by
      ext x
      simp [F, hRm]
    calc
      (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast (le_max_left n k)
      _ = absoluteIntegral μ (F m) {x | R < ‖F m x‖} := by rw [hset, hnorm]
      _ ≤ amplitudeSup μ F R := le_iSup (fun j =>
        absoluteIntegral μ (F j) {x | R < ‖F j x‖}) m
  change μ univ = 1 ∧ uiSmall μ F ∧
    (∀ n, absoluteIntegral μ (F n) univ = (n : ℝ≥0∞)) ∧
    integralSup μ F univ = ∞ ∧ (∀ R, amplitudeSup μ F R = ∞) ∧
    ¬ uniformL1Bound μ F ∧ ¬ uiTail μ F
  refine ⟨by simp [μ], hsmall, hnorm, hsup, htail, ?_, ?_⟩
  · intro hb
    have hfin := hb.2
    rw [hsup] at hfin
    exact (lt_irrefl _) hfin
  · intro ht
    obtain ⟨R, hR⟩ := ((tendsto_order.1 ht.2).2 1 zero_lt_one).exists
    rw [htail] at hR
    exact (not_lt_of_ge le_top) hR

end D11.Ch17.DefinitionComparison
