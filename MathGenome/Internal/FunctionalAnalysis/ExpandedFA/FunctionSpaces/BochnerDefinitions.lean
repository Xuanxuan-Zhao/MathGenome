import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDefinitions

/-!
Bochner definitions from paper.tex:17017–17024, with the strongly measurable
Lᵖ a.e. quotient used in 17036–17040. The source convention of strong
measurability includes an a.e. exceptional set. The underlying measure is
arbitrary, and the codomain need not be separable. Definitions are made at
normed-group generality whenever no scalar structure or completeness is needed.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.FunctionSpaces

/-- A.e. pointwise approximation in norm by measurable finite-valued functions. -/
def StrongMeasurable : BochnerDefinitionsSpec.StrongMeasurableType.{u,v} :=
  fun μ f => ∃ s : ℕ → SimpleFunc _ _,
    ∀ᵐ x ∂μ, Tendsto (fun n => ‖s n x - f x‖) atTop (𝓝 0)

/-- Integrable simple functions; only nonzero level sets need finite measure. -/
def IntegrableSimple : BochnerDefinitionsSpec.IntegrableSimpleType.{u,v} :=
  fun μ s => ∀ y, y ≠ 0 → μ (s ⁻¹' {y}) < ∞

/-- L¹-norm limit of integrable simple functions. Infinite approximation error
is retained as ∞, so that it cannot spuriously count as a zero error. -/
def BochnerIntegrable : BochnerDefinitionsSpec.BochnerIntegrableType.{u,v} :=
  fun μ f => ∃ s : ℕ → SimpleFunc _ _,
    (∀ n, IntegrableSimple μ (s n)) ∧
      Tendsto (fun n => eLpNorm (f - ⇑(s n)) 1 μ) atTop (𝓝 0)

/-- Simple integration on the canonical disjoint level-set partition.
The intended domain is `IntegrableSimple μ s`; a total extension is convenient. -/
def simpleIntegral : BochnerDefinitionsSpec.SimpleIntegralType.{u,v} :=
  fun μ s => ∑ y ∈ s.range, μ.real (s ⁻¹' {y}) • y

/-- Strongly measurable functions of finite p-norm, modulo a.e. equality,
for 1 ≤ p ≤ ∞. All the canonical normed-group and scalar-space instances
are inherited from `MeasureTheory.Lp`. -/
abbrev BochnerLp : BochnerDefinitionsSpec.BochnerLpType.{u,v} :=
  fun E _ _ p _ μ => Lp E p μ

/-- The usual norm on the a.e. quotient. -/
def lpNorm : BochnerDefinitionsSpec.LpNormType.{u,v} := fun _ _ _ f => ‖f‖

/-- Identification with Mathlib's a.e. (rather than everywhere) convention. -/
theorem strongMeasurable_identification :
    BochnerDefinitionsSpec.StrongMeasurableIdentification.{u,v} := by
  intro X E _ _ μ f
  constructor
  · rintro ⟨s, hs⟩
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (s n).aestronglyMeasurable)
      (hs.mono fun _ hx => tendsto_iff_norm_sub_tendsto_zero.mpr hx)
  · rintro ⟨g, hg, hfg⟩
    refine ⟨hg.approx, ?_⟩
    filter_upwards [hfg] with x hx
    rw [hx]
    exact tendsto_iff_norm_sub_tendsto_zero.mp (hg.tendsto_approx x)

theorem integrableSimple_identification :
    BochnerDefinitionsSpec.IntegrableSimpleIdentification.{u,v} := by
  intro X E _ _ μ s
  exact SimpleFunc.integrable_iff.symm

private theorem simpleIntegral_eq_native {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (s : SimpleFunc X E) :
    BochnerDefinitionsSpec.SimpleIntegralValue μ s = s.integral μ :=
  (SimpleFunc.integral_eq μ s).symm

private theorem simple_integral_finsetSum {X : Type u} {E : Type v} {ι : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (s : Finset ι) (f : ι → SimpleFunc X E)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (∑ i ∈ s, f i).integral μ = ∑ i ∈ s, (f i).integral μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (SimpleFunc.const X (0 : E)).integral μ = 0
    simp only [SimpleFunc.integral_const, smul_zero]
  | @insert a s ha ih =>
    have has : ∀ i ∈ s, Integrable (f i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs : Integrable (∑ i ∈ s, f i : SimpleFunc X E) μ := by
      exact Finset.sum_induction f (fun g : SimpleFunc X E => Integrable g μ)
        (fun _ _ h₁ h₂ => by simpa only [SimpleFunc.coe_add] using h₁.add h₂)
        (by simpa only [SimpleFunc.coe_zero] using integrable_zero X E μ) has
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      SimpleFunc.integral_add (hf a (Finset.mem_insert_self _ _)) hs, ih has]

/-- The stated partition formula is independent of repeated or zero values.
Linearity even makes disjointness unnecessary for this computation. -/
theorem simpleIntegral_partition : BochnerDefinitionsSpec.SimpleIntegralPartition.{u,v} := by
  intro X E _ _ _ μ n A hA hfin _hdisj x
  let s : Fin n → SimpleFunc X E := fun j =>
    SimpleFunc.piecewise (A j) (hA j) (SimpleFunc.const X (x j)) 0
  have hs : ∀ j, Integrable (s j) μ := by
    intro j
    apply SimpleFunc.integrable_iff_finMeasSupp.mpr
    rw [SimpleFunc.finMeasSupp_iff_support]
    refine lt_of_le_of_lt (measure_mono ?_) (hfin j)
    intro t ht
    by_contra h
    apply ht
    simp [s, SimpleFunc.coe_piecewise, h]
  rw [simpleIntegral_eq_native, simple_integral_finsetSum μ Finset.univ s (fun j _ => hs j)]
  apply Finset.sum_congr rfl
  intro j _
  simp [s, SimpleFunc.integral_piecewise_zero, SimpleFunc.integral_const,
    Measure.real]

theorem lp_membership : BochnerDefinitionsSpec.LpMembership.{u,v} := by
  intro X E _ _ p _ μ f
  constructor
  · intro hf
    exact ⟨(strongMeasurable_identification μ f).mpr hf.aestronglyMeasurable, hf⟩
  · exact fun hf => hf.2

theorem lp_equality : BochnerDefinitionsSpec.LpEquality.{u,v} := by
  intro X E _ _ p _ μ f g
  exact ⟨fun h => h ▸ Filter.EventuallyEq.rfl, Lp.ext⟩

theorem lpNorm_finite : BochnerDefinitionsSpec.LpNormFinite.{u,v} := by
  intro X E _ _ p hp μ htop f
  have hzero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hp.out)
  exact congrArg ENNReal.toReal
    (eLpNorm_eq_lintegral_rpow_enorm_toReal hzero htop (Lp.aestronglyMeasurable f))

theorem lpNorm_infinity : BochnerDefinitionsSpec.LpNormInfinity.{u,v} := by
  intro X E _ _ μ f
  exact congrArg ENNReal.toReal (eLpNorm_exponent_top (Lp.aestronglyMeasurable f))

end ExpandedFA.FunctionSpaces
