import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.AntisymmetricSets
import Mathlib.Order.Zorn
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ExtremeScalarMeasures
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

set_option maxHeartbeats 800000

noncomputable section
namespace ExpandedFA.PartV.AntisymmetricSets
open Set MeasureTheory Filter
open scoped ENNReal Topology ZeroAtInfty
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.ScalarRieszMarkov
open AntisymmetricSetsSpec
universe u

/-- Antisymmetry for a possibly nonunital complex function algebra. -/
def isAntisymmetric : AntisymmetricType.{u} := AntisymmetricValue

variable {K : Type u} [TopologicalSpace K]
  {A : NonUnitalSubalgebra ℂ C(K, ℂ)}

theorem antisymmetric_closure : ClosureProperty.{u} := by
  intro K _ A S hS f hf hreal
  have hconst := hS f hf (fun x hx => hreal x (subset_closure hx))
  intro x hx y hy
  by_cases hne : S.Nonempty
  · obtain ⟨z, hz⟩ := hne
    have hclosed : IsClosed {w : K | f w = f z} :=
      isClosed_eq f.continuous continuous_const
    have hsub : closure S ⊆ {w : K | f w = f z} :=
      closure_minimal (fun w hw => hconst w hw z hz) hclosed
    exact (hsub hx).trans (hsub hy).symm
  · have : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [this] at hx

theorem antisymmetric_chain_union : ChainUnionProperty.{u} := by
  intro K _ A c hc hanti f hf hreal x hx y hy
  obtain ⟨S, hSc, hxS⟩ := mem_sUnion.mp hx
  obtain ⟨T, hTc, hyT⟩ := mem_sUnion.mp hy
  rcases hc.total hSc hTc with hST | hTS
  · exact hanti T hTc f hf (fun z hz => hreal z (mem_sUnion.mpr ⟨T, hTc, hz⟩))
      x (hST hxS) y hyT
  · exact hanti S hSc f hf (fun z hz => hreal z (mem_sUnion.mpr ⟨S, hSc, hz⟩))
      x hxS y (hTS hyT)

theorem maximal_closed_extension : MaximalExtension.{u} := by
  intro K _ A S hS
  obtain ⟨T, hST, hT, hmax⟩ := zorn_subset_nonempty
    {T : Set K | IsClosed T ∧ IsAntisymmetric A T}
    (fun c hc hchain _ => by
      refine ⟨closure (⋃₀ c), ⟨isClosed_closure, ?_⟩, ?_⟩
      · exact antisymmetric_closure K A _
          (antisymmetric_chain_union K A c hchain (fun U hU => (hc hU).2))
      · intro U hUc
        exact (subset_sUnion_of_mem hUc).trans subset_closure)
    (closure S) ⟨isClosed_closure, antisymmetric_closure K A S hS⟩
  exact ⟨T, subset_closure.trans hST, hT.1, hT.2,
    fun U hUclosed hU hTU => hmax ⟨hUclosed, hU⟩ hTU⟩

theorem maximal_among_all : MaximalAmongAll.{u} := by
  intro K _ A S hS T hT hST
  exact subset_closure.trans
    (hS.2.2 (closure T) isClosed_closure (antisymmetric_closure K A T hT)
      (hST.trans subset_closure))

section WeightedMeasures
variable [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

lemma continuous_integrable (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h : C(K, ℂ)) : Integrable (h : K → ℂ) ν.variation := by
  exact (BoundedContinuousFunction.mkOfCompact h).integrable ν.variation

/-- Multiplication of a scalar measure by a continuous complex function. -/
def weightedMeasure (ν : VectorMeasure K ℂ) (h : C(K, ℂ)) : VectorMeasure K ℂ :=
  ν.withDensity h (ContinuousLinearMap.mul ℝ ℂ)

lemma weighted_variation (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h : C(K, ℂ)) :
    (weightedMeasure ν h).variation = ν.variation.withDensity (fun x => ‖h x‖ₑ) := by
  rw [weightedMeasure, VectorMeasure.variation_withDensity (continuous_integrable ν h)
    (by intro x y; exact nnnorm_mul x y),
    VectorMeasure.variation_transpose_eq _ _ (by intro x y; exact nnnorm_mul x y)]

lemma weighted_variation_le (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h : C(K, ℂ)) :
    (weightedMeasure ν h).variation ≤ ‖h‖₊ • ν.variation := by
  rw [weighted_variation]
  calc
    _ ≤ ν.variation.withDensity (fun _ => (‖h‖₊ : ℝ≥0∞)) :=
      withDensity_mono (Eventually.of_forall (fun x => by
        exact ENNReal.coe_le_coe.mpr (show ‖h x‖₊ ≤ ‖h‖₊ from h.norm_coe_le_norm x)))
    _ = _ := by rw [withDensity_const]; rfl

lemma weighted_finite_radon (ν : VectorMeasure K ℂ) (hν : FiniteScalarRadon ν)
    (h : C(K, ℂ)) : FiniteScalarRadon (weightedMeasure ν h) := by
  have := ExtremeScalarMeasures.finite_variation ν hν
  have : ν.variation.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  have : IsFiniteMeasure (weightedMeasure ν h).variation :=
    isFiniteMeasure_of_le _ (weighted_variation_le ν h)
  exact ⟨measure_lt_top _ _,
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
      (regular_of_le (weighted_variation_le ν h))⟩

lemma weighted_mass (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h : C(K, ℂ)) :
    (weightedMeasure ν h).variation.real univ = ∫ x, ‖h x‖ ∂ν.variation := by
  rw [Measure.real, weighted_variation, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact (integral_norm_eq_lintegral_enorm (continuous_integrable ν h).aestronglyMeasurable).symm

lemma weighted_add (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h k : C(K, ℂ)) :
    weightedMeasure ν (h + k) = weightedMeasure ν h + weightedMeasure ν k := by
  ext s hs
  change ν.withDensity (fun x => h x + k x) (ContinuousLinearMap.mul ℝ ℂ) s =
    ν.withDensity h (ContinuousLinearMap.mul ℝ ℂ) s +
    ν.withDensity k (ContinuousLinearMap.mul ℝ ℂ) s
  erw [VectorMeasure.withDensity_apply ((continuous_integrable ν h).add (continuous_integrable ν k)),
    VectorMeasure.withDensity_apply (continuous_integrable ν h),
    VectorMeasure.withDensity_apply (continuous_integrable ν k)]
  exact VectorMeasure.integral_fun_add
    (μ := ν.restrict s) (B := ContinuousLinearMap.mul ℝ ℂ)
    (show ν.Integrable (h : K → ℂ) from continuous_integrable ν h).integrableOn
    (show ν.Integrable (k : K → ℂ) from continuous_integrable ν k).integrableOn

lemma weighted_const (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation] (c : ℂ) :
    weightedMeasure ν (ContinuousMap.const K c) = c • ν := by
  ext s hs
  change ν.withDensity (fun _ => c) (ContinuousLinearMap.mul ℝ ℂ) s = (c • ν) s
  rw [VectorMeasure.withDensity_apply (integrable_const c)]
  simp [VectorMeasure.integral_const, VectorMeasure.restrict_apply, hs]

lemma weighted_eq_zero_iff (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h : C(K, ℂ)) :
    weightedMeasure ν h = 0 ↔ ∀ᵐ x ∂ν.variation, h x = 0 := by
  rw [← VectorMeasure.variation_eq_zero, weighted_variation,
    withDensity_eq_zero_iff h.continuous.measurable.enorm.aemeasurable]
  change (∀ᵐ x ∂ν.variation, ‖h x‖ₑ = 0) ↔ _
  simp only [enorm_eq_zero]

lemma weighted_integral_simple (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h : C(K, ℂ)) (g : SimpleFunc K ℂ) :
    scalarIntegral (weightedMeasure ν h) g =
      scalarIntegral ν (fun x => g x * h x) := by
  have : IsFiniteMeasure (weightedMeasure ν h).variation :=
    isFiniteMeasure_of_le _ (weighted_variation_le ν h)
  induction g using SimpleFunc.induction with
  | @const c s hs =>
    change scalarIntegral (weightedMeasure ν h) (s.indicator (fun _ => c)) =
      scalarIntegral ν (fun x => s.indicator (fun _ => c) x * h x)
    have he : (fun x => s.indicator (fun _ => c) x * h x) =
        s.indicator (fun x => c * h x) := by
      funext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [he]
    calc
      _ = c * weightedMeasure ν h s :=
        VectorMeasure.integral_indicator_const c hs
      _ = c * scalarIntegral (ν.restrict s) h := by
        rw [weightedMeasure, VectorMeasure.withDensity_apply (continuous_integrable ν h)]
        rfl
      _ = scalarIntegral (ν.restrict s) (fun x => c * h x) :=
        (scalarIntegral_smul (ν.restrict s) c h).symm
      _ = _ := (VectorMeasure.integral_indicator hs).symm

  | @add f g _ hf hg =>
    have hfm := f.integrable_of_isFiniteMeasure (μ := ν.variation)
    have hgm := g.integrable_of_isFiniteMeasure (μ := ν.variation)
    have hfh := hfm.mul_bdd h.continuous.aestronglyMeasurable
      (Eventually.of_forall h.norm_coe_le_norm)
    have hgh := hgm.mul_bdd h.continuous.aestronglyMeasurable
      (Eventually.of_forall h.norm_coe_le_norm)
    change scalarIntegral (weightedMeasure ν h) (fun x => f x + g x) = _
    rw [show (fun x => (f + g) x * h x) =
      (fun x => f x * h x + g x * h x) by funext x; simp [add_mul]]
    rw [show scalarIntegral (weightedMeasure ν h) (fun x => f x + g x) =
        scalarIntegral (weightedMeasure ν h) f + scalarIntegral (weightedMeasure ν h) g from
      VectorMeasure.integral_fun_add f.integrable_of_isFiniteMeasure g.integrable_of_isFiniteMeasure,
      hf, hg]
    exact (VectorMeasure.integral_fun_add hfh hgh).symm

/-- Multiplication of measures agrees with the ordinary scalar-linear pairing.
The proof uses bounded simple-function approximation and dominated convergence. -/
lemma weighted_integral (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h g : C(K, ℂ)) :
    scalarIntegral (weightedMeasure ν h) g = scalarIntegral ν (g * h) := by
  have : IsFiniteMeasure (weightedMeasure ν h).variation :=
    isFiniteMeasure_of_le _ (weighted_variation_le ν h)
  let hg := g.continuous.stronglyMeasurable
  let G := hg.approxBounded ‖g‖
  have hbound (n : ℕ) (x : K) : ‖G n x‖ ≤ ‖g‖ :=
    hg.norm_approxBounded_le (norm_nonneg g) n x
  have hlim (x : K) : Tendsto (fun n => G n x) atTop (𝓝 (g x)) :=
    hg.tendsto_approxBounded_of_norm_le (g.norm_coe_le_norm x)
  have hl : Tendsto (fun n => scalarIntegral (weightedMeasure ν h) (G n)) atTop
      (𝓝 (scalarIntegral (weightedMeasure ν h) g)) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
      (fun n => (G n).stronglyMeasurable.aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall (hbound n))
      (Eventually.of_forall hlim)
  have hr : Tendsto (fun n => scalarIntegral ν (fun x => G n x * h x)) atTop
      (𝓝 (scalarIntegral ν (g * h))) := by
    apply VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => ‖g‖ * ‖h‖)
    · intro n
      exact ((G n).stronglyMeasurable.mul h.continuous.stronglyMeasurable).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall (fun x => by
        rw [norm_mul]
        exact mul_le_mul (hbound n x) (h.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _))
    · exact Eventually.of_forall (fun x => (hlim x).mul_const (h x))
  exact tendsto_nhds_unique
    ((tendsto_congr' (Eventually.of_forall (fun n => weighted_integral_simple ν h (G n)))).mp hl) hr

lemma weighted_sub (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (h k : C(K, ℂ)) :
    weightedMeasure ν (h - k) = weightedMeasure ν h - weightedMeasure ν k := by
  ext s hs
  change ν.withDensity (fun x => h x - k x) (ContinuousLinearMap.mul ℝ ℂ) s =
    ν.withDensity h (ContinuousLinearMap.mul ℝ ℂ) s -
    ν.withDensity k (ContinuousLinearMap.mul ℝ ℂ) s
  erw [VectorMeasure.withDensity_apply ((continuous_integrable ν h).sub (continuous_integrable ν k)),
    VectorMeasure.withDensity_apply (continuous_integrable ν h),
    VectorMeasure.withDensity_apply (continuous_integrable ν k)]
  exact VectorMeasure.integral_fun_sub
    (μ := ν.restrict s) (B := ContinuousLinearMap.mul ℝ ℂ)
    (show ν.Integrable (h : K → ℂ) from continuous_integrable ν h).integrableOn
    (show ν.Integrable (k : K → ℂ) from continuous_integrable ν k).integrableOn

lemma weighted_const_real (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation] (a : ℝ) :
    weightedMeasure ν (ContinuousMap.const K (a : ℂ)) = a • ν := by
  rw [weighted_const]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) a ν).symm

lemma eq_on_support_of_weighted_eq_smul (ν : VectorMeasure K ℂ)
    [IsFiniteMeasure ν.variation] (h : C(K, ℂ)) (a : ℝ)
    (heq : weightedMeasure ν h = a • ν) :
    ∀ x ∈ ν.variation.support, h x = (a : ℂ) := by
  have hz : weightedMeasure ν (h - ContinuousMap.const K (a : ℂ)) = 0 := by
    rw [weighted_sub, weighted_const_real, heq, sub_self]
  have hae := (weighted_eq_zero_iff ν _).mp hz
  have hclosed : IsClosed {x : K | h x = (a : ℂ)} :=
    isClosed_eq h.continuous continuous_const
  apply ν.variation.support_subset_of_isClosed hclosed
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx

/-- Multiplying an annihilator by an affine expression in one algebra member
still annihilates the algebra. Constants need not belong to the algebra. -/
lemma weighted_affine_annihilates (ν : VectorMeasure K ℂ) [IsFiniteMeasure ν.variation]
    (hν : ∀ g ∈ A, scalarIntegral ν g = 0) (f : C(K, ℂ)) (hf : f ∈ A)
    (b c : ℂ) :
    ∀ g ∈ A, scalarIntegral (weightedMeasure ν (ContinuousMap.const K b + c • f)) g = 0 := by
  intro g hg
  rw [weighted_integral]
  have heq : g * (ContinuousMap.const K b + c • f) = b • g + c • (g * f) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.const_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  change scalarIntegral ν (g * (ContinuousMap.const K b + c • f) : C(K, ℂ)) = 0
  rw [heq]
  exact hν _ (A.add_mem (A.smul_mem b hg) (A.smul_mem c (A.mul_mem hg hf)))

/-- The convex splitting argument for weights strictly between zero and one
on the variation support. Both annihilation hypotheses concern measures. -/
lemma extreme_weight_constant (ν : VectorMeasure K ℂ)
    (hν : ν ∈ (annihilatorBall A).extremePoints ℝ)
    (hm : ν.variation univ = 1) (h : C(K, ℂ)) (δ : ℝ) (hδ : 0 < δ)
    (hvals : ∀ x ∈ ν.variation.support,
      (h x).im = 0 ∧ δ ≤ (h x).re ∧ (h x).re ≤ 1 - δ)
    (hann : ∀ g ∈ A, scalarIntegral (weightedMeasure ν h) g = 0)
    (hkann : ∀ g ∈ A, scalarIntegral (weightedMeasure ν (1 - h)) g = 0) :
    ∃ a : ℝ, ∀ x ∈ ν.variation.support, h x = (a : ℂ) := by
  have hrad := hν.1.1.1
  have := ExtremeScalarMeasures.finite_variation ν hrad
  have : ν.variation.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hrad.2
  have hconull : ∀ᵐ x ∂ν.variation, x ∈ ν.variation.support :=
    ν.variation.support_mem_ae_of_regular
  have hnorms : ∀ᵐ x ∂ν.variation,
      δ ≤ ‖h x‖ ∧ δ ≤ ‖(1 - h) x‖ ∧ ‖h x‖ + ‖(1 - h) x‖ = 1 := by
    filter_upwards [hconull] with x hx
    obtain ⟨him, hlo, hhi⟩ := hvals x hx
    have he : h x = ((h x).re : ℂ) := Complex.ext (by simp) (by simpa using him)
    have he' : (1 - h) x = ((1 - (h x).re : ℝ) : ℂ) := by
      change 1 - h x = _
      rw [he, Complex.ofReal_sub, Complex.ofReal_one]
      simp only [Complex.ofReal_re]
    rw [he', Complex.norm_of_nonneg (by linarith : 0 ≤ 1 - (h x).re)]
    have hn : ‖h x‖ = (h x).re := by
      conv_lhs => rw [he]
      exact Complex.norm_of_nonneg (hδ.le.trans hlo)
    rw [hn]
    exact ⟨hlo, by linarith, by ring⟩
  let a := (weightedMeasure ν h).variation.real univ
  let b := (weightedMeasure ν (1 - h)).variation.real univ
  have hamass : a = ∫ x, ‖h x‖ ∂ν.variation := weighted_mass ν h
  have hbmass : b = ∫ x, ‖(1 - h) x‖ ∂ν.variation := weighted_mass ν (1 - h)
  have hmass : ν.variation.real univ = 1 := by simp [Measure.real, hm]
  have ha : 0 < a := by
    apply hδ.trans_le
    have hc : (∫ _ : K, δ ∂ν.variation) = δ := by simp [integral_const, hmass]
    rw [hamass, ← hc]
    exact integral_mono_ae (integrable_const _) (continuous_integrable ν h).norm
      (hnorms.mono fun x hx => hx.1)
  have hb : 0 < b := by
    apply hδ.trans_le
    have hc : (∫ _ : K, δ ∂ν.variation) = δ := by simp [integral_const, hmass]
    rw [hbmass, ← hc]
    exact integral_mono_ae (integrable_const _) (continuous_integrable ν (1 - h)).norm
      (hnorms.mono fun x hx => hx.2.1)
  have hab : a + b = 1 := by
    rw [hamass, hbmass, ← integral_add (continuous_integrable ν h).norm
      (continuous_integrable ν (1 - h)).norm,
      integral_congr_ae (hnorms.mono fun x hx => hx.2.2)]
    simpa using hmass
  have hradh := weighted_finite_radon ν hrad h
  have hradk := weighted_finite_radon ν hrad (1 - h)
  have h₁ : a⁻¹ • weightedMeasure ν h ∈ annihilatorBall A := by
    refine ⟨ExtremeScalarMeasures.normalize_mem _ hradh ha, ?_⟩
    intro g hg
    change VectorMeasure.integral _ _ _ = 0
    rw [VectorMeasure.integral_smul_vectorMeasure]
    change a⁻¹ • scalarIntegral (weightedMeasure ν h) g = 0
    rw [hann g hg, smul_zero]
  have h₂ : b⁻¹ • weightedMeasure ν (1 - h) ∈ annihilatorBall A := by
    refine ⟨ExtremeScalarMeasures.normalize_mem _ hradk hb, ?_⟩
    intro g hg
    change VectorMeasure.integral _ _ _ = 0
    rw [VectorMeasure.integral_smul_vectorMeasure]
    change b⁻¹ • scalarIntegral (weightedMeasure ν (1 - h)) g = 0
    rw [hkann g hg, smul_zero]
  have hsum : weightedMeasure ν h + weightedMeasure ν (1 - h) = ν := by
    rw [← weighted_add, add_sub_cancel, show (1 : C(K, ℂ)) = ContinuousMap.const K 1 from rfl,
      weighted_const, one_smul]
  have heq : a⁻¹ • weightedMeasure ν h = ν := hν.2 h₁ h₂
    ⟨a, b, ha, hb, hab, by
      rw [smul_smul, smul_smul, mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne',
        one_smul, one_smul]
      exact hsum⟩
  refine ⟨a, eq_on_support_of_weighted_eq_smul ν h a ?_⟩
  calc
    weightedMeasure ν h = a • (a⁻¹ • weightedMeasure ν h) := by
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    _ = a • ν := congrArg (fun μ : VectorMeasure K ℂ => a • μ) heq

/-- Norm-one extreme annihilating measures have antisymmetric variation support.
The proof never requires the affine weight itself to belong to the algebra. -/
theorem extreme_annihilator_support : ExtremeAnnihilatorSupport.{u} := by
  intro K _ _ _ _ _ A _hclosed ν hν hm f hf hreal
  have := ExtremeScalarMeasures.finite_variation ν hν.1.1.1
  let t : ℝ := (4 * (1 + ‖f‖))⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have htn : t * ‖f‖ ≤ 1 / 4 := by
    dsimp [t]
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity : 0 < 4 * (1 + ‖f‖))]
    nlinarith [norm_nonneg f]
  let h : C(K, ℂ) := ContinuousMap.const K (1 / 2) + (t : ℂ) • f
  have hre (x : K) : (h x).re = 1 / 2 + t * (f x).re := by
    simp [h, Complex.mul_re]
  have him (x : K) : (h x).im = t * (f x).im := by
    simp [h, Complex.mul_im]
  have hk : 1 - h = ContinuousMap.const K (1 / 2 : ℂ) + (-(t : ℂ)) • f := by
    ext x
    simp only [h, ContinuousMap.sub_apply, ContinuousMap.one_apply,
      ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  obtain ⟨a, ha⟩ := extreme_weight_constant ν hν hm h (1 / 4) (by norm_num)
    (fun x hx => by
      have hb : |(f x).re| ≤ ‖f‖ :=
        (Complex.abs_re_le_norm _).trans (f.norm_coe_le_norm x)
      have hb' := abs_le.mp hb
      rw [hre, him, hreal x hx, mul_zero]
      exact ⟨rfl, by nlinarith [mul_le_mul_of_nonneg_left hb'.1 ht.le],
        by nlinarith [mul_le_mul_of_nonneg_left hb'.2 ht.le]⟩)
    (weighted_affine_annihilates ν hν.1.2 f hf (1 / 2) (t : ℂ))
    (by rw [hk]; exact weighted_affine_annihilates ν hν.1.2 f hf (1 / 2) (-(t : ℂ)))
  intro x hx y hy
  have he : h x = h y := (ha x hx).trans (ha y hy).symm
  change (1 / 2 : ℂ) + (t : ℂ) * f x = (1 / 2 : ℂ) + (t : ℂ) * f y at he
  exact mul_left_cancel₀ (show (t : ℂ) ≠ 0 by exact_mod_cast ht.ne') (add_left_cancel he)

/-- The annihilator ball is compact for the topology of integration against
continuous functions, including on the empty compact space. -/
theorem annihilator_ball_weakStar_compact : AnnihilatorBallCompactness.{u} := by
  intro K _ _ _ _ _ A
  let D := C₀(K, ℂ) →L[ℂ] ℂ
  letI : TopologicalSpace D :=
    ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue ℂ C₀(K, ℂ)
  letI : TopologicalSpace (VectorMeasure K ℂ) := measureWeakStarTopology K
  let lift : C(K, ℂ) → C₀(K, ℂ) :=
    ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  have heval (f : C₀(K, ℂ)) : Continuous (fun L : D => L f) := by
    rw [continuous_iff_le_induced]
    change ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue ℂ C₀(K, ℂ) ≤ _
    rw [ExpandedFA.P1.C12WeakStar.weakStarTopology_evaluations]
    exact iInf_le _ f
  let B : Set D := {L | ‖L‖ ≤ 1 ∧ ∀ f ∈ A, L (lift f) = 0}
  have hclosed : IsClosed {L : D | ∀ f ∈ A, L (lift f) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun f => isClosed_iInter (fun _ =>
      isClosed_eq (heval (lift f)) continuous_const))
  have hcompact : IsCompact B :=
    (ExpandedFA.P1.C13Alaoglu.banach_alaoglu ℂ C₀(K, ℂ)).inter_right hclosed
  choose ρ hrad hrep hnorm huniq using
    (fun L : D => complex_representation K L)
  have hcont : Continuous ρ := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro f
    have he : (fun L : D => scalarIntegral (ρ L) f) = (fun L : D => L f) := by
      funext L
      exact (hrep L f).2.symm
    change Continuous (fun L : D => scalarIntegral (ρ L) f)
    rw [he]
    exact heval f
  have himage : ρ '' B = annihilatorBall A := by
    ext ν
    constructor
    · rintro ⟨L, hL, rfl⟩
      refine ⟨⟨hrad L, ?_⟩, ?_⟩
      · rw [← ENNReal.ofReal_toReal (hrad L).1.ne]
        apply ENNReal.ofReal_le_one.mpr
        change (ρ L).variation.real univ ≤ 1
        rw [← hnorm L]
        exact hL.1
      · intro f hf
        exact ((hrep L (lift f)).2.symm).trans (hL.2 f hf)
    · intro hν
      have := ExtremeScalarMeasures.finite_variation ν hν.1.1
      have : ν.variation.Regular :=
        (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.1.1.2
      let L : D := scalarMeasureFunctional ν
      have hL : L ∈ B := by
        refine ⟨?_, ?_⟩
        · rw [show ‖L‖ = ν.variation.real univ from scalarMeasureFunctional_norm_eq ν]
          exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hν.1.2)
        · intro f hf
          exact hν.2 f hf
      refine ⟨L, hL, ?_⟩
      apply scalarIntegral_injective _ _ (hrad L) hν.1.1
      intro f
      exact (hrep L f).2.symm
  rw [← himage]
  exact hcompact.image hcont

end WeightedMeasures
end ExpandedFA.PartV.AntisymmetricSets
