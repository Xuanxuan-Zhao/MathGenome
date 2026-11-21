import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.ScalarSpectralMoments
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace

namespace ExpandedFA.Unbounded.ScalarSpectralMoments
open MeasurableSpectralCalculus OperatorDomainsSpec
open UnboundedNormalSpectralTheorem.SpectralRepresentation
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section ScalarIntegral
variable {S : Type v} [MeasurableSpace S]
  {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

/-- Polarization of the bounded norm identity gives the scalar integral. -/
theorem bounded_scalar_integral (f : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (x : H) :
    (∫ s, (f s).re ∂C.measure x) = (inner ℂ x (C.integral f x)).re := by
  have := C.finite x
  have hone : SpectralMeasure.Spec.IsBoundedMeasurable (fun _ : S => (1 : ℂ)) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  have hire : Integrable (fun s => (f s).re) (C.measure x) := by
    obtain ⟨M, hM, hb⟩ := hf.nonneg_bound
    exact Integrable.mono' (integrable_const M) ((Complex.measurable_re.comp hf.1).stronglyMeasurable.aestronglyMeasurable)
      (Eventually.of_forall fun s => (Complex.abs_re_le_norm (f s)).trans (hb s))
  have h := C.norm_sq ((fun _ => 1) + f) (hone.add hf) x
  rw [C.add _ _ hone hf, C.one] at h
  change ‖x + C.integral f x‖ ^ 2 = _ at h
  rw [norm_add_sq (𝕜 := ℂ)] at h
  have hpoint : (fun s => ‖((fun _ : S => (1 : ℂ)) + f) s‖ ^ 2) =
      (fun s => (1 : ℝ) + 2 * (f s).re + ‖f s‖ ^ 2) := by
    funext s
    simpa using (norm_add_sq (𝕜 := ℂ) (1 : ℂ) (f s))
  rw [hpoint, integral_add (f := fun s => (1 : ℝ) + 2 * (f s).re)
    (g := fun s => ‖f s‖ ^ 2) ((integrable_const 1).add (hire.const_mul 2))
    (C.integrable_norm_sq f hf x),
    integral_add (f := fun _ => (1 : ℝ)) (g := fun s => 2 * (f s).re)
      (integrable_const 1) (hire.const_mul 2),
    integral_const_mul, ← C.norm_sq f hf x] at h
  have hmass := C.norm_sq (fun _ : S => (1 : ℂ)) hone x
  rw [C.one] at hmass
  simp only [one_apply_eq_self, norm_one, one_pow] at hmass
  simp only [RCLike.re_eq_complex_re] at h
  linarith

/-- On a finite scalar spectral measure, a square-integrable symbol is integrable. -/
theorem integrable_of_domain {f : S → ℂ} (hf : Measurable f)
    (x : (measurableIntegral C f).domain) : Integrable f (C.measure x) := by
  have := C.finite x
  have hs := squareIntegrable_of_mem_domain C hf x
  have hi : Integrable (fun s => ‖f s‖ ^ 2) (C.measure x) :=
    ⟨(hf.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => sq_nonneg ‖f s‖)).mpr hs⟩
  exact ((memLp_two_iff_integrable_sq_norm hf.stronglyMeasurable.aestronglyMeasurable).mpr hi).integrable
    (by norm_num)

/-- Scalar coefficient identity on the maximal unbounded integral domain. -/
theorem scalar_integral {f : S → ℂ} (hf : Measurable f)
    (x : (measurableIntegral C f).domain) :
    (∫ s, (f s).re ∂C.measure x) = (inner ℂ (x : H) (measurableIntegral C f x)).re := by
  have hi := integrable_of_domain C hf x
  have hlim : Tendsto (fun n => ∫ s, (truncation f n s).re ∂C.measure x) atTop
      (nhds (∫ s, (f s).re ∂C.measure x)) := by
    apply tendsto_integral_of_dominated_convergence (fun s => ‖f s‖)
    · intro n
      exact (Complex.measurable_re.comp (measurable_truncation hf n)).stronglyMeasurable.aestronglyMeasurable
    · exact hi.norm
    · intro n
      apply Eventually.of_forall
      intro s
      classical
      by_cases hs : ‖f s‖ ≤ (n : ℝ)
      · simpa [truncation, hs] using Complex.abs_re_le_norm (f s)
      · simp [truncation, hs]
    · exact Eventually.of_forall fun s => (Complex.continuous_re.tendsto _).comp (truncation_tendsto f s)
  have hcoeff := (Complex.continuous_re.tendsto _).comp
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (x : H)) atTop (nhds (x : H))).inner
      (𝕜 := ℂ) (measurableIntegral_tendsto C f x))
  simp only [bounded_scalar_integral C _ (boundedMeasurable_truncation hf _)] at hlim
  exact tendsto_nhds_unique hlim hcoeff

end ScalarIntegral
section Powers
variable {S : Type v} [MeasurableSpace S]
  {E : SpectralMeasure.ProjectionValuedMeasure S H} (C : BoundedRealization E)

omit [CompleteSpace H] in
private theorem identity_graph (x : H) :
    (x, x) ∈ (identityValue (𝕜 := ℂ)).graph := by
  exact (identityValue (𝕜 := ℂ)).mem_graph_iff.mpr ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩

/-- Spectral projections preserve graphs of the actual partial powers. -/
theorem projection_power_graph {f : S → ℂ} (hf : Measurable f)
    (B : Set S) (hB : MeasurableSet B) (n : ℕ) {x y : H}
    (h : (x, y) ∈ (powerValue (measurableIntegral C f) n).graph) :
    (E B x, E B y) ∈ (powerValue (measurableIntegral C f) n).graph := by
  induction n generalizing x y with
  | zero =>
      have heq : x = y := (identityValue (𝕜 := ℂ)).mem_graph_snd_inj
        (identity_graph x) h rfl
      subst y
      exact identity_graph _
  | succ n ih =>
      change (x, y) ∈ (productValue (measurableIntegral C f)
        (powerValue (measurableIntegral C f) n)).graph at h
      obtain ⟨z, hz, hy⟩ := (mem_product_graph_iff _ _ _ _).mp h
      change (E B x, E B y) ∈ (productValue (measurableIntegral C f)
        (powerValue (measurableIntegral C f) n)).graph
      apply (mem_product_graph_iff _ _ _ _).mpr
      refine ⟨E B z, ih hz, ?_⟩
      obtain ⟨z', rfl, rfl⟩ := (measurableIntegral C f).mem_graph_iff.mp hy
      exact projection_commutes C hf B hB z'

/-- A symbol bounded on B has bounded localized powers of every order. -/
theorem bounded_indicator_power {f : S → ℂ} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) {M : ℝ} (hM : ∀ s ∈ B, ‖f s‖ ≤ M)
    (n : ℕ) : SpectralMeasure.Spec.IsBoundedMeasurable
      (B.indicator (fun s => f s ^ n)) := by
  refine ⟨(hf.pow_const n).indicator hB, (max M 0) ^ n, ?_⟩
  intro s
  classical
  by_cases hs : s ∈ B
  · simp only [Set.indicator_of_mem hs, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hM s hs).trans (le_max_left _ _)) n
  · simp only [Set.indicator_of_notMem hs, norm_zero]
    positivity

/-- On a bounded spectral set, repeated action is bounded multiplication. -/
theorem localized_power_graph {f : S → ℂ} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) {M : ℝ} (hM : ∀ s ∈ B, ‖f s‖ ≤ M)
    (n : ℕ) (x : H) :
    (E B x, C.integral (B.indicator (fun s => f s ^ n)) x) ∈
      (powerValue (measurableIntegral C f) n).graph := by
  induction n with
  | zero =>
      simp only [pow_zero, integral_indicator_one C B hB]
      exact identity_graph _
  | succ n ih =>
      change _ ∈ (productValue (measurableIntegral C f)
        (powerValue (measurableIntegral C f) n)).graph
      apply (mem_product_graph_iff _ _ _ _).mpr
      refine ⟨C.integral (B.indicator (fun s => f s ^ n)) x, ih, ?_⟩
      have heq : f * B.indicator (fun s => f s ^ n) =
          B.indicator (fun s => f s ^ (n + 1)) := by
        classical
        funext s
        by_cases hs : s ∈ B <;> simp [hs, pow_succ']
      have hg := bounded_indicator_power hf hB hM n
      have hfg : SpectralMeasure.Spec.IsBoundedMeasurable
          (f * B.indicator (fun s => f s ^ n)) := by
        rw [heq]
        exact bounded_indicator_power hf hB hM (n + 1)
      simpa only [heq] using bounded_product_graph C hf hg hfg x

/-- The localized bounded power is the projection of the domain-carrying power. -/
theorem localized_power {f : S → ℂ} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) {M : ℝ} (hM : ∀ s ∈ B, ‖f s‖ ≤ M)
    (n : ℕ) (x : (powerValue (measurableIntegral C f) n).domain) :
    C.integral (B.indicator (fun s => f s ^ n)) x =
      E B (powerValue (measurableIntegral C f) n x) := by
  apply (powerValue (measurableIntegral C f) n).mem_graph_snd_inj
    (localized_power_graph C hf hB hM n x)
    (projection_power_graph C hf B hB n
      ((powerValue (measurableIntegral C f) n).mem_graph_iff.mpr ⟨x, rfl, rfl⟩)) rfl

/-- Each partial power is contained in the maximal integral of the power symbol.
This is an inclusion of graphs, without asserting an unbounded product rule. -/
theorem power_graph_integral {f : S → ℂ} (hf : Measurable f) (n : ℕ)
    (x : (powerValue (measurableIntegral C f) n).domain) :
    ((x : H), powerValue (measurableIntegral C f) n x) ∈
      (measurableIntegral C (fun s => f s ^ n)).graph := by
  by_cases hn : n = 0
  · subst n
    have hone : SpectralMeasure.Spec.IsBoundedMeasurable (fun _ : S => (1 : ℂ)) :=
      ⟨measurable_const, 1, fun _ => by simp⟩
    have hmul : ((fun _ : S => (1 : ℂ)) * (fun _ : S => (1 : ℂ))) =
        (fun _ => (1 : ℂ)) := by ext s; simp
    have hh := bounded_product_graph C (f := fun _ : S => (1 : ℂ))
      (g := fun _ : S => (1 : ℂ)) measurable_const hone
      (hmul.symm ▸ hone) (x : H)
    simp only [hmul, C.one, one_apply_eq_self] at hh
    change ((x : H), (x : H)) ∈ (measurableIntegral C (fun s => f s ^ 0)).graph
    simpa only [pow_zero] using hh
  · rw [measurableIntegral, mem_limitOperator_graph_iff]
    have heq (k : ℕ) : C.integral (truncation (fun s => f s ^ n) k) x =
        C.integral (cutoffIndicator (fun s => f s ^ n) k)
          (powerValue (measurableIntegral C f) n x) := by
      let B : Set S := {s | ‖f s ^ n‖ ≤ (k : ℝ)}
      have hB : MeasurableSet B := measurableSet_le ((hf.pow_const n).norm) measurable_const
      have hbound : ∀ s ∈ B, ‖f s‖ ≤ max (k : ℝ) 1 := by
        intro s hs
        by_cases hsmall : ‖f s‖ ≤ 1
        · exact hsmall.trans (le_max_right _ _)
        · have hh := le_self_pow₀ (le_of_lt (lt_of_not_ge hsmall)) hn
          have hs' : ‖f s‖ ^ n ≤ (k : ℝ) := by
            simpa only [B, Set.mem_ofPred_eq, norm_pow] using hs
          exact hh.trans (hs'.trans (le_max_left _ _))
      rw [show truncation (fun s => f s ^ n) k = B.indicator (fun s => f s ^ n) from rfl,
        localized_power C hf hB hbound n x]
      rw [show cutoffIndicator (fun s => f s ^ n) k = B.indicator (fun _ => 1) from rfl,
        integral_indicator_one C B hB]
    simpa only [heq] using C.cutoff_tendsto (hf.pow_const n)
      (powerValue (measurableIntegral C f) n x)

end Powers

/-- The scalar spectral measure of an all-power vector has all the required moments. -/
theorem scalar_moments : Spec.ScalarMoments.{u} := by
  intro H _ _ _ A E C hA e he
  subst A
  refine ⟨C.finite e, fun n => ?_⟩
  let x : (powerValue (measurableIntegral C (fun t : ℝ => (t : ℂ))) n).domain := ⟨e, he n⟩
  have hf : Measurable (fun t : ℝ => (t : ℂ) ^ n) := Complex.measurable_ofReal.pow_const n
  have hg := power_graph_integral C Complex.measurable_ofReal n x
  obtain ⟨z, hz, hval⟩ := (measurableIntegral C (fun t : ℝ => (t : ℂ) ^ n)).mem_graph_iff.mp hg
  have hi := integrable_of_domain C hf z
  have hs := scalar_integral C hf z
  have hz' : (z : H) = e := hz
  have hv := hval
  rw [hz'] at hi hs
  refine ⟨?_, ?_⟩
  · simpa only [RCLike.re_eq_complex_re, ← Complex.ofReal_pow, Complex.ofReal_re] using hi.re
  · simpa only [← Complex.ofReal_pow, Complex.ofReal_re, hv] using hs

end ExpandedFA.Unbounded.ScalarSpectralMoments
