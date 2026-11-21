import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ProkhorovMetric
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.BoundedLipschitzMetric
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.SeparableWeakMetrization

open MeasureTheory Filter Topology Set Metric BoundedContinuousFunction
open scoped ENNReal

namespace ProbabilityFoundations.Ch06

universe u
noncomputable section
variable {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [BorelSpace S] in
private lemma integrableOn_mass_antitone (ν : ProbabilityMeasure S)
    (F : ℝ → Set S) (hF : Antitone F) (M : ℝ) :
    IntegrableOn (fun t => (ν : Measure S).real (F t)) (Ioc 0 M) := by
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
  · exact (Measurable.ennreal_toReal (Antitone.measurable
      (fun s t hst => measure_mono (hF hst)))).aestronglyMeasurable
  · exact Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
        (measureReal_le_one (μ := (ν : Measure S)) (s := F t)))

/-- A layer-cake estimate, valid without any separability or tightness assumption. -/
private lemma integral_le_of_prokhorov_lt (μ ν : ProbabilityMeasure S)
    (f : S →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (hLip : LipschitzWith 1 f)
    {ε : ℝ} (hε : prokhorovDist μ ν < ε) :
    (∫ x, f x ∂(μ : Measure S)) ≤
      (∫ x, f x ∂(ν : Measure S)) + (1 + ‖f‖) * ε := by
  have εpos : 0 < ε := (prokhorovDist_nonneg μ ν).trans_lt hε
  have he : levyProkhorovEDist (μ : Measure S) (ν : Measure S) < ENNReal.ofReal ε := by
    apply (ENNReal.toReal_lt_toReal (levyProkhorovEDist_ne_top _ _)
      ENNReal.ofReal_ne_top).mp
    simpa [levyProkhorovDist, ENNReal.toReal_ofReal εpos.le,
      prokhorovDist_eq_levyProkhorovDist] using hε
  let g : S →ᵇ ℝ := f + BoundedContinuousFunction.const S ε
  have hg (x : S) : g x = f x + ε := rfl
  have gpos (x : S) : 0 ≤ g x := by rw [hg]; exact add_nonneg (hf x) εpos.le
  have normle : ‖f‖ ≤ ‖g‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf x)]
    exact (le_add_of_nonneg_right εpos.le).trans (g.apply_le_norm x)
  have hsub (t : ℝ) : thickening ε {x | t ≤ f x} ⊆ {x | t ≤ g x} := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
    change t ≤ f y at hy
    have hdist := hLip.dist_le_mul y x
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hdist
    have hdiff := (le_abs_self (f y - f x)).trans hdist
    rw [dist_comm] at hxy
    change t ≤ f x + ε
    linarith
  have hi₁ := integrableOn_mass_antitone ν
    (fun t => thickening ε {x | t ≤ f x})
    (fun s t hst => thickening_subset_of_subset ε (fun x hx => hst.trans hx)) ‖f‖
  have hi₂ := integrableOn_mass_antitone ν (fun t => {x | t ≤ g x})
    (fun s t hst x hx => hst.trans hx) ‖f‖
  have hi₃ := integrableOn_mass_antitone ν (fun t => {x | t ≤ g x})
    (fun s t hst x hx => hst.trans hx) ‖g‖
  have hmono : (∫ t in Ioc 0 ‖f‖, (ν : Measure S).real
      (thickening ε {x | t ≤ f x})) ≤ ∫ x, g x ∂(ν : Measure S) := by
    calc
      _ ≤ ∫ t in Ioc 0 ‖f‖, (ν : Measure S).real {x | t ≤ g x} :=
        setIntegral_mono hi₁ hi₂ (fun t => measureReal_mono (hsub t))
      _ ≤ ∫ t in Ioc 0 ‖g‖, (ν : Measure S).real {x | t ≤ g x} :=
        setIntegral_mono_set hi₃ (Eventually.of_forall (fun _ => measureReal_nonneg))
          (Eventually.of_forall (fun t ht => ⟨ht.1, ht.2.trans normle⟩))
      _ = ∫ x, g x ∂(ν : Measure S) :=
        (g.integral_eq_integral_meas_le (ν : Measure S) (Eventually.of_forall gpos)).symm
  have hmain := f.integral_le_of_levyProkhorovEDist_lt
    (μ : Measure S) (ν : Measure S) εpos he (Eventually.of_forall hf)
  have hgint : (∫ x, g x ∂(ν : Measure S)) = (∫ x, f x ∂(ν : Measure S)) + ε := by
    simp only [hg]
    rw [integral_add (f.integrable _) (integrable_const ε)]
    simp
  rw [hgint] at hmono
  linarith

/-- The comparison uses the two separate unit bounds in the source definition. -/
theorem boundedLipschitzDist_le_three_prokhorovDist (μ ν : ProbabilityMeasure S) :
    boundedLipschitzDist μ ν ≤ 3 * prokhorovDist μ ν := by
  have htest (μ ν : ProbabilityMeasure S) (f : S → ℝ)
      (hf : IsBoundedLipschitzTest f) {ε : ℝ} (hε : prokhorovDist μ ν < ε) :
      (∫ x, f x ∂(μ : Measure S)) - (∫ x, f x ∂(ν : Measure S)) ≤ 3 * ε := by
    let f' : S →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf.2.continuous⟩ 2
      (fun x y => by
        change dist (f x) (f y) ≤ 2
        rw [Real.dist_eq]
        linarith [abs_sub (f x) (f y), hf.1 x, hf.1 y])
    let g : S →ᵇ ℝ := f' + BoundedContinuousFunction.const S 1
    have hg (x : S) : g x = f x + 1 := rfl
    have gpos (x : S) : 0 ≤ g x := by
      rw [hg]
      linarith [(abs_le.mp (hf.1 x)).1]
    have gnorm : ‖g‖ ≤ 2 := by
      apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (gpos x), hg]
      linarith [(abs_le.mp (hf.1 x)).2]
    have gLip : LipschitzWith 1 g := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      simpa only [hg, Real.dist_eq, add_sub_add_right_eq_sub] using hf.2.dist_le_mul x y
    have hmain := integral_le_of_prokhorov_lt μ ν g gpos gLip hε
    have gint (ξ : ProbabilityMeasure S) :
        (∫ x, g x ∂(ξ : Measure S)) = (∫ x, f x ∂(ξ : Measure S)) + 1 := by
      simp only [hg]
      rw [integral_add (boundedLipschitzTest_integrable f hf ξ) (integrable_const 1)]
      simp
    rw [gint μ, gint ν] at hmain
    have εpos := (prokhorovDist_nonneg μ ν).trans_lt hε
    nlinarith
  apply csSup_le (boundedLipschitzValues_nonempty μ ν)
  rintro r ⟨f, hf, rfl⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  have hε : prokhorovDist μ ν < a / 3 := by linarith
  have h₁ := htest μ ν f hf hε
  have h₂ := htest ν μ f hf (by simpa only [prokhorovDist_comm] using hε)
  apply (abs_le.mpr ⟨by linarith, by linarith⟩)

open TopologicalSpace

/-- Weak-to-π continuity, on arbitrary separable metric state spaces. -/
theorem weak_continuous_prokhorov_identity [SeparableSpace S] :
    @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
      (weakTopology (S := S))
      (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace id := by
  rw [weakTopology_eq]
  exact continuous_induced_rng.mpr LevyProkhorov.continuous_ofMeasure_probabilityMeasure

/-- Equality with the weak topology, including its neighborhood structure. -/
theorem prokhorovMetricSpace_topology_eq_weak [SeparableSpace S] :
    (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace =
      weakTopology (S := S) := by
  exact le_antisymm (continuous_id_iff_le.mp prokhorov_continuous_identity)
    (continuous_id_iff_le.mp weak_continuous_prokhorov_identity)

/-- A Lipschitz identity from π to the bounded Lipschitz metric. -/
private lemma continuous_prokhorov_to_boundedLipschitz :
    @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
      (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace
      (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace id := by
  have h : @LipschitzWith (ProbabilityMeasure S) (ProbabilityMeasure S)
      (prokhorovMetricSpace (S := S)).toPseudoEMetricSpace
      (boundedLipschitzMetric (S := S)).toPseudoEMetricSpace 3 id := by
    apply (@lipschitzWith_iff_dist_le_mul (ProbabilityMeasure S) (ProbabilityMeasure S)
      (prokhorovMetricSpace (S := S)).toPseudoMetricSpace
      (boundedLipschitzMetric (S := S)).toPseudoMetricSpace 3 id).mpr
    intro μ ν
    change boundedLipschitzDist μ ν ≤
      3 * @dist _ (prokhorovMetricSpace (S := S)).toDist μ ν
    rw [prokhorovMetricSpace_dist]
    exact boundedLipschitzDist_le_three_prokhorovDist μ ν
  exact @LipschitzWith.continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
    (prokhorovMetricSpace (S := S)).toPseudoEMetricSpace
    (boundedLipschitzMetric (S := S)).toPseudoEMetricSpace 3 id h

/-- Weak-to-BL continuity follows from the metric comparison and weak-to-π continuity. -/
theorem weak_continuous_boundedLipschitz_identity [SeparableSpace S] :
    @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
      (weakTopology (S := S))
      (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace id := by
  exact @Continuous.comp (ProbabilityMeasure S) (ProbabilityMeasure S) (ProbabilityMeasure S)
    (weakTopology (S := S))
    (prokhorovMetricSpace (S := S)).toUniformSpace.toTopologicalSpace
    (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace id id
    continuous_prokhorov_to_boundedLipschitz weak_continuous_prokhorov_identity

/-- Equality with the initial weak topology, without completeness assumptions. -/
theorem boundedLipschitzMetric_topology_eq_weak [SeparableSpace S] :
    (boundedLipschitzMetric (S := S)).toUniformSpace.toTopologicalSpace =
      weakTopology (S := S) := by
  exact le_antisymm (continuous_id_iff_le.mp boundedLipschitzMetric_continuous_id)
    (continuous_id_iff_le.mp weak_continuous_boundedLipschitz_identity)

/-- The original Prokhorov distance induces exactly the weak topology. -/
theorem prokhorov_metrizes_weak [SeparableSpace S] :
    ∃ m : MetricSpace (ProbabilityMeasure S),
      (∀ μ ν, @dist _ m.toDist μ ν = prokhorovDist μ ν) ∧
      m.toUniformSpace.toTopologicalSpace = weakTopology (S := S) :=
  ⟨prokhorovMetricSpace, prokhorovMetricSpace_dist, prokhorovMetricSpace_topology_eq_weak⟩

/-- The original bounded Lipschitz distance induces exactly the weak topology. -/
theorem boundedLipschitz_metrizes_weak [SeparableSpace S] :
    ∃ m : MetricSpace (ProbabilityMeasure S),
      (∀ μ ν, @dist _ m.toDist μ ν = boundedLipschitzDist μ ν) ∧
      m.toUniformSpace.toTopologicalSpace = weakTopology (S := S) :=
  ⟨boundedLipschitzMetric, fun _ _ => rfl, boundedLipschitzMetric_topology_eq_weak⟩

end
end ProbabilityFoundations.Ch06
