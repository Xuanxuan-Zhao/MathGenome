import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.VitaliLpConvergence
import MathGenome.Internal.RealAnalysis.D11.Ch17.VitaliLpCauchy
import MathGenome.Internal.RealAnalysis.D11.Ch10.Completeness
import MathGenome.Internal.RealAnalysis.D11.Ch07.NormToMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch07.SubsequenceUniqueness

/-! Vitali convergence on an arbitrary positive measure space. Completeness
produces a quotient limit, and uniqueness of the global limit in measure
identifies the originally given measurable function with that limit a.e.
Thus no integrability hypothesis on the candidate limit is assumed. -/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u v
noncomputable section
namespace D11.Ch17.VitaliLpConvergence
open D11.Ch17.UniformControls D11.Ch07.ConvergenceDefinitions
open D11.Ch07.SubsequenceUniqueness D11.Ch10.LpDefinition

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The triangle inequality gives global Cauchyness in measure, without
restricting μ to any set of finite measure. -/
theorem cauchyInMeasure_of_inMeasureConverges (μ : Measure X)
    (G : ℕ → X → 𝕜) (f : X → 𝕜) (h : inMeasureConverges μ G f) :
    cauchyInMeasure μ G := by
  intro ε hε δ hδ
  have hev := (h (ε / 2) (half_pos hε)).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hδ)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun m hm n hn => ?_⟩
  have hsub : deviationSet (G n) (G m) ε ⊆
      deviationSet (G n) f (ε / 2) ∪ deviationSet (G m) f (ε / 2) := by
    intro x hx
    by_contra hnot
    have hparts := not_or.mp hnot
    have hn' : ‖G n x - f x‖ ≤ ε / 2 := le_of_not_gt hparts.1
    have hm' : ‖G m x - f x‖ ≤ ε / 2 := le_of_not_gt hparts.2
    have hnorm : ‖G n x - G m x‖ ≤ ‖G n x - f x‖ + ‖G m x - f x‖ :=
      by simpa only [norm_sub_rev (f x) (G m x)] using
        norm_sub_le_norm_sub_add_norm_sub (G n x) (f x) (G m x)
    change ε < ‖G n x - G m x‖ at hx
    linarith
  calc
    _ ≤ μ (deviationSet (G n) f (ε / 2) ∪ deviationSet (G m) f (ε / 2)) :=
      measure_mono hsub
    _ ≤ μ (deviationSet (G n) f (ε / 2)) + μ (deviationSet (G m) f (ε / 2)) :=
      measure_union_le _ _
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      ENNReal.add_lt_add (hN n hn) (hN m hm)
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- Norm convergence also converges globally in measure for every choice
of measurable representatives and every a.e. version of the limit. -/
theorem inMeasureConverges_of_tendsto_Lp (μ : Measure X) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ)
    (g : Lp 𝕜 (ENNReal.ofReal p) μ) (G : ℕ → X → 𝕜) (f : X → 𝕜)
    (hGF : ∀ n, G n =ᵐ[μ] F n) (hfg : f =ᵐ[μ] g)
    (hlim : Tendsto F atTop (𝓝 g)) : inMeasureConverges μ G f := by
  apply (inMeasureConverges_iff_native μ G f).mpr
  exact (tendstoInMeasure_of_tendsto_Lp hlim).congr
    (fun n => (hGF n).symm) hfg.symm

theorem vitali_lp_convergence :
    Specs.D11.Ch17.VitaliLpConvergence.vitali_lp_convergence.{u} := by
  intro X 𝕜 _ _ _ _ μ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  intro F G f hG hGF hf
  constructor
  · rintro ⟨_, g, hfg, hlim⟩
    have hcontrols := D11.Ch17.NormConvergenceControls.lp_norm_convergence_controls
      μ p hp F g G hG hGF hlim
    exact ⟨inMeasureConverges_of_tendsto_Lp μ p F g G f hGF hfg hlim,
      hcontrols.1, hcontrols.2.1⟩
  · rintro ⟨hmeasure, hsmall, htails⟩
    have hc : CauchySeq F :=
      (D11.Ch17.VitaliLpCauchy.vitali_lp_cauchy μ p hp F G hG hGF).mpr
        ⟨cauchyInMeasure_of_inMeasureConverges μ G f hmeasure, hsmall, htails⟩
    obtain ⟨g, hlim⟩ := cauchySeq_tendsto_of_complete hc
    have hgmeasure : inMeasureConverges μ G g :=
      inMeasureConverges_of_tendsto_Lp μ p F g G g hGF Filter.EventuallyEq.rfl hlim
    have hfg : f =ᵐ[μ] g :=
      (D11.Ch04.AeCommonException.aeEq_iff_native μ f g).mp
        (limit_unique μ G f g hmeasure hgmeasure)
    refine ⟨(rawLp_iff_memLp μ p f hp).mpr ⟨hf, ?_⟩, g, hfg, hlim⟩
    exact (memLp_congr_ae hfg).mpr (Lp.memLp g)

theorem finite_measure_spatial_tails :
    Specs.D11.Ch17.VitaliLpConvergence.finite_measure_spatial_tails.{u,v} := by
  intro X ι 𝕜 _ _ _ _ μ p G hμ hfamily
  change lpSpatialTails μ p G
  refine ⟨hfamily, (lpFamily_iff μ p G).mp hfamily |>.2.2, ?_⟩
  intro ε hε
  refine ⟨univ, MeasurableSet.univ, hμ, ?_⟩
  simp only [compl_univ, integralSup, absoluteIntegral_formula, Measure.restrict_empty,
    lintegral_zero_measure]
  exact (iSup_le fun _ => le_rfl).trans_lt (ENNReal.ofReal_pos.mpr hε)

theorem finite_measure_vitali_lp_convergence :
    Specs.D11.Ch17.VitaliLpConvergence.finite_measure_vitali_lp_convergence.{u} := by
  intro X 𝕜 _ _ _ _ μ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  intro F G f hμ hG hGF hf
  rw [vitali_lp_convergence μ p hp F G f hG hGF hf]
  constructor
  · rintro ⟨hm, hs, _⟩
    exact ⟨hm, hs⟩
  · rintro ⟨hm, hs⟩
    exact ⟨hm, hs, finite_measure_spatial_tails μ p G hμ hs.1⟩

/-- Explicitly transport the quotient criterion back to the original
representative definition, including the finite p-power integral of f. -/
theorem vitali_lp_convergence_on_representatives :
    Specs.D11.Ch17.VitaliLpConvergence.vitali_lp_convergence_on_representatives.{u} := by
  intro X 𝕜 _ _ _ _ μ p hp G f hG hf
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmeas : ∀ n, Measurable (G n) := fun n => (hG n).1
  change lpConverges μ p G f ↔ inMeasureConverges μ G f ∧
    lpUiSmall μ p G ∧ lpSpatialTails μ p G
  constructor
  · intro h
    have hrawf : f ∈ rawLp μ p := (rawLp_iff_finite_integral μ p f hp).mpr h.2.1
    have hroot := h.2.2.2.ennrpow_const (1 / p)
    rw [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] at hroot
    change Tendsto (fun n => powerNorm μ p (G n - f)) atTop (𝓝 0) at hroot
    have hnorm : Tendsto (fun n => eLpNorm (G n - f) (ENNReal.ofReal p) μ)
        atTop (𝓝 0) := by
      convert hroot using 1
      funext n
      exact (powerNorm_eq_eLpNorm μ p (G n - f) hp ((hmeas n).sub hf)).symm
    have hc := D11.Ch17.NormConvergenceControls.power_controls_of_tendsto_eLpNorm
      μ p hp G f hG hrawf hnorm
    exact ⟨D11.Ch07.NormToMeasure.lp_to_measure μ G f p h,
      ⟨⟨hp, hG⟩, hc.1⟩, ⟨⟨hp, hG⟩, hc.2.1⟩⟩
  · intro h
    have hmem : ∀ n, MemLp (G n) (ENNReal.ofReal p) μ :=
      fun n => ((rawLp_iff_memLp μ p (G n) hp).mp (hG n)).2
    let F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ := fun n => (hmem n).toLp (G n)
    have hGF : ∀ n, G n =ᵐ[μ] F n := fun n => (hmem n).coeFn_toLp.symm
    obtain ⟨hrawf, g, hfg, hlim⟩ :=
      (vitali_lp_convergence μ p hp F G f hmeas hGF hf).mpr h
    refine ⟨hp, (rawLp_iff_finite_integral μ p f hp).mp hrawf,
      fun n => (rawLp_iff_finite_integral μ p (G n) hp).mp (hG n), ?_⟩
    have hdist := tendsto_iff_dist_tendsto_zero.mp hlim
    have hpower := ((ENNReal.continuous_ofReal.tendsto 0).comp hdist).ennrpow_const p
    simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp0] at hpower
    convert hpower using 1
    funext n
    rw [powerIntegral_eq_lintegral]
    exact D11.Ch17.VitaliLpCauchy.difference_integral_eq_dist_rpow
      μ p hp (F n) g (G n) f (hmeas n) hf (hGF n) hfg

theorem finite_measure_vitali_lp_convergence_on_representatives :
    Specs.D11.Ch17.VitaliLpConvergence.finite_measure_vitali_lp_convergence_on_representatives.{u} := by
  intro X 𝕜 _ _ _ _ μ p hp G f hμ hG hf
  rw [vitali_lp_convergence_on_representatives μ p hp G f hG hf]
  constructor
  · rintro ⟨hm, hs, _⟩
    exact ⟨hm, hs⟩
  · rintro ⟨hm, hs⟩
    exact ⟨hm, hs, finite_measure_spatial_tails μ p G hμ hs.1⟩

end D11.Ch17.VitaliLpConvergence
