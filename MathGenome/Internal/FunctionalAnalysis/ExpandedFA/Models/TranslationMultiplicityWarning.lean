import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.TranslationMultiplicityWarning
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.CoordinateMultiplicationModel
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Instances.Rat

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace ExpandedFA.Models.TranslationMultiplicityWarning
open ExpandedFA.Models.FullTranslationModel
open ExpandedFA.Unbounded ExpandedFA.Semigroups.Stone
open ExpandedFA.Unbounded.MeasurableSpectralCalculus
open CoordinateMultiplicationModel
universe u

/-- Outer regularity gives a dense open set of finite measure. It has positive measure
in every nonempty interval, and its complement has positive measure. -/
theorem warning_set : Spec.WarningSetExists := by
  have hnull : volume (range (fun q : ℚ => (q : ℝ))) = 0 :=
    (countable_range _).measure_zero volume
  obtain ⟨E, hQE, hE, hvol⟩ :=
    (range (fun q : ℚ => (q : ℝ))).exists_isOpen_lt_of_lt (μ := volume) 1
      (by rw [hnull]; exact zero_lt_one)
  refine ⟨E, hE.measurableSet, ?_, ?_⟩
  · intro a b hab
    have hne : (E ∩ Ioo a b).Nonempty := by
      obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
      exact ⟨q, hQE ⟨q, rfl⟩, haq, hqb⟩
    exact (hE.inter isOpen_Ioo).measure_pos volume hne
  · by_contra h
    have hz : volume Eᶜ = 0 := le_antisymm (le_of_not_gt h) bot_le
    have ht : volume (univ : Set ℝ) < ⊤ := by
      rw [← union_compl_self E, measure_union disjoint_compl_right hE.measurableSet.compl,
        hz, add_zero]
      exact hvol.trans (by simp)
    simp at ht

section Transport
variable {H : Type*} {K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Transport an entire real-time unitary group through a unitary. -/
def conjugateGroup (W : H ≃ₗᵢ[ℂ] K) (U : UnitaryGroup K) : UnitaryGroup H where
  operators t := (W.trans (U.operators t)).trans W.symm
  at_zero x := by simp [U.at_zero]
  add_time t s x := by simp [U.add_time]
  continuous_orbit x := W.symm.continuous.comp (U.continuous_orbit (W x))

theorem derivative_conjugate (W : H ≃ₗᵢ[ℂ] K) (U : UnitaryGroup K) (f y : H) :
    HasDerivative (conjugateGroup W U) f y ↔ HasDerivative U (W f) (W y) := by
  have he (h : ℝ) : W (differenceQuotient (conjugateGroup W U) h f) =
      differenceQuotient U h (W f) := by
    simp [differenceQuotient, conjugateGroup]
  constructor
  · intro h
    simpa only [HasDerivative, Function.comp_def, he] using (W.continuous.tendsto y).comp h
  · intro h
    have he' (h : ℝ) : W.symm (differenceQuotient U h (W f)) =
        differenceQuotient (conjugateGroup W U) h f := by
      rw [← he, W.symm_apply_apply]
    simpa only [HasDerivative, Function.comp_def, he', W.symm_apply_apply] using (W.symm.continuous.tendsto (W y)).comp h

theorem mem_smul_graph_iff (A : Operator ℂ H H) (c : ℂ) (hc : c ≠ 0) (f y : H) :
    (f, y) ∈ (c • A).graph ↔ (f, c⁻¹ • y) ∈ A.graph := by
  constructor
  · intro h
    obtain ⟨hf, hy⟩ := (ExpandedFA.Unbounded.mem_graph_iff (c • A) (f,y)).mp h
    apply (ExpandedFA.Unbounded.mem_graph_iff A (f, c⁻¹ • y)).mpr
    refine ⟨hf, ?_⟩
    change c • A ⟨f, hf⟩ = y at hy
    rw [← hy, inv_smul_smul₀ hc]
  · intro h
    obtain ⟨hf, hy⟩ := (ExpandedFA.Unbounded.mem_graph_iff A (f, c⁻¹ • y)).mp h
    apply (ExpandedFA.Unbounded.mem_graph_iff (c • A) (f,y)).mpr
    refine ⟨hf, ?_⟩
    change c • A ⟨f, hf⟩ = y
    rw [hy, smul_inv_smul₀ hc]

/-- Equality of entire graphs forces conjugacy of the entire groups. -/
theorem group_conjugacy_of_graph (W : H ≃ₗᵢ[ℂ] K)
    (U : UnitaryGroup H) (V : UnitaryGroup K)
    (A : Operator ℂ H H) (B : Operator ℂ K K)
    (hU : DerivativeGraph U A) (hV : DerivativeGraph V B)
    (hW : ∀ f g, (f, g) ∈ A.graph ↔ (W f, W g) ∈ B.graph) :
    ∀ t f, W (U.operators t f) = V.operators t (W f) := by
  have hgen : U.infinitesimalGenerator = (conjugateGroup W V).infinitesimalGenerator := by
    apply LinearPMap.eq_of_eq_graph
    ext p
    rw [← U.hasDerivative_iff_mem_graph, ← (conjugateGroup W V).hasDerivative_iff_mem_graph,
      derivative_conjugate, hU, hV,
      mem_smul_graph_iff A Complex.I Complex.I_ne_zero,
      mem_smul_graph_iff B Complex.I Complex.I_ne_zero]
    simpa only [map_smul] using hW p.1 (Complex.I⁻¹ • p.2)
  intro t f
  have he := congrArg (fun T : H ≃ₗᵢ[ℂ] H => W (T f))
    (operators_eq_of_generator_eq U (conjugateGroup W V) hgen t)
  simpa [conjugateGroup] using he
end Transport

section EnergyMeasures
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
variable (μ : Measure ℝ)

/-- The finite scalar spectral measure of a vector in a coordinate model. -/
def energyMeasure (f : Lp M 2 μ) : Measure ℝ :=
  μ.withDensity (fun r => ENNReal.ofReal (‖f r‖ ^ 2))

theorem energyMeasure_finite (f : Lp M 2 μ) : IsFiniteMeasure (energyMeasure μ f) := by
  apply isFiniteMeasure_withDensity
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  exact ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun r => sq_nonneg ‖f r‖)).mp hi.2).ne

theorem energyMeasure_charFun (f g : Lp M 2 μ) (t : ℝ)
    (hg : (g : ℝ → M) =ᵐ[μ] fun r =>
      Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) • f r) :
    charFun (energyMeasure μ f) t = inner ℂ f g := by
  rw [charFun_apply_real, energyMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun r => ENNReal.ofReal (‖f r‖ ^ 2))
    (((Lp.aestronglyMeasurable f).norm.pow 2).aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg] with r hr
  rw [hr, inner_smul_right, inner_self_eq_norm_sq_to_K, ENNReal.toReal_ofReal (sq_nonneg _)]
  have he : (t : ℂ) * (r : ℂ) * Complex.I = Complex.I * (t : ℂ) * (r : ℂ) := by ring
  rw [Complex.real_smul, Complex.ofReal_pow, he, mul_comm]
  rfl

end EnergyMeasures

/-- Graph equivalence preserves the actual scalar energy measures. This is
proved through the unitary groups and uniqueness of characteristic functions,
so it works for arbitrary Hilbert multiplicity. -/
theorem energyMeasure_eq_of_graph_equivalence {E : Set ℝ}
    (hmodel : RestrictedSpectralModel E)
    {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    (W : RestrictedL2 E ≃ₗᵢ[ℂ] L2 M) (hW : Spec.CoordinateGraphEquivalence E M W)
    (f : RestrictedL2 E) :
    energyMeasure (volume.restrict E) f = energyMeasure volume (W f) := by
  obtain ⟨P, C, A, _hP, hmult, hAeq, hA, hgraph, _hac, _hsupp⟩ := hmodel
  let U := spectralGroup C
  have hs : SpectralExponential A U := ⟨P, C, hAeq, fun _ => rfl⟩
  have hd := spectral_derivative (RestrictedL2 E) A U hA hs
  obtain ⟨V, B, hV, _hB, _hsB, hdB, hgraphB⟩ := coordinate_generator M
  have hconj := group_conjugacy_of_graph W U V A B hd hdB
    (fun f g => (hgraph f g).trans ((hW f g).trans (hgraphB (W f) (W g)).symm))
  haveI := energyMeasure_finite (volume.restrict E) f
  haveI := energyMeasure_finite volume (W f)
  apply Measure.ext_of_charFun
  funext t
  have hU : (U.operators t f : ℝ → ℂ) =ᵐ[volume.restrict E]
      fun r => Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) • f r := by
    simpa only [U, spectralGroup, spectralUnitary_apply, spectralOperator, exponentialSymbol,
      smul_eq_mul] using hmult (exponentialSymbol t) (bounded_exponentialSymbol t) f
  rw [energyMeasure_charFun (volume.restrict E) f _ t hU,
    energyMeasure_charFun volume (W f) _ t (hV t (W f)), ← hconj t f]
  exact (W.inner_map_map f (U.operators t f)).symm

/-- A positive-measure missing subset rules out every nonzero full-line
multiplicity, with no countability assumption on its Hilbert space. -/
theorem no_coordinate_graph_equivalence {E : Set ℝ} (hE : MeasurableSet E)
    (hcompl : 0 < volume Eᶜ) (hmodel : RestrictedSpectralModel E)
    (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    [Nontrivial M] :
    ¬ ∃ W : RestrictedL2 E ≃ₗᵢ[ℂ] L2 M, Spec.CoordinateGraphEquivalence E M W := by
  rintro ⟨W, hW⟩
  obtain ⟨S, hS, hSE, hpos, hfin⟩ := Measure.exists_subset_measure_lt_top hE.compl hcompl
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  let g : L2 M := indicatorConstLp 2 hS hfin.ne v
  have hg : (g : ℝ → M) =ᵐ[volume] S.indicator (fun _ => v) := indicatorConstLp_coeFn
  let f := W.symm g
  have hmeas := energyMeasure_eq_of_graph_equivalence hmodel W hW f
  have he : W f = g := W.apply_symm_apply g
  rw [he] at hmeas
  have hz : energyMeasure (volume.restrict E) f S = 0 := by
    apply withDensity_absolutelyContinuous _ _
    rw [Measure.restrict_apply hS]
    have hempty : S ∩ E = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact (hSE hr.1) hr.2
    rw [hempty, measure_empty]
  have hval : energyMeasure volume g S = ENNReal.ofReal (‖v‖ ^ 2) * volume S := by
    rw [energyMeasure, withDensity_apply _ hS]
    calc
      _ = ∫⁻ r in S, ENNReal.ofReal (‖v‖ ^ 2) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem hS] with r hr hs
        rw [hr, indicator_of_mem hs]
      _ = _ := by simp
  rw [hmeas, hval] at hz
  have hpositive : 0 < ENNReal.ofReal (‖v‖ ^ 2) * volume S :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hv))).ne' hpos.ne'
  exact hpositive.ne' hz

/-- The absolutely continuous full-support restricted coordinate operator is
not any nonzero constant-multiplicity Lebesgue coordinate model. -/
theorem nonconstant_multiplicity_warning : Spec.NonconstantMultiplicityWarning.{u} := by
  obtain ⟨E, hE⟩ := warning_set
  have hmodel := restricted_spectral_model E hE.1
  refine ⟨E, hE, hmodel, ?_⟩
  intro M _ _ _ _
  exact no_coordinate_graph_equivalence hE.1 hE.2.2 hmodel M

end ExpandedFA.Models.TranslationMultiplicityWarning
