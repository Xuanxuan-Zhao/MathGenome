import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.WeightedConfiningEnergySpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.LaxMilgramSolvability
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open Set TopologicalSpace MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace ComplexConjugate Topology

attribute [local instance 2000] NormedAddCommGroup.toSeminormedAddCommGroup

namespace ExpandedFA.Models.WeightedConfiningEnergySpace
open ExpandedFA.Sobolev ExpandedFA.Distributions

/-- The actual weighted energy space, using the shared independent graph. -/
def weightedEnergySpace : Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.SpaceType :=
  fun 𝕜 _ p => weightedGraph 𝕜 p

variable {𝕜 : Type} [RCLike 𝕜]

/-- The two ordinary derivatives, of orders zero and one, with no repetitions. -/
def indexEquiv : DerivativeIndex 1 1 ≃ Fin 2 where
  toFun α := α.val 0
  invFun i := ⟨fun _ => i, by simpa using Nat.le_of_lt_succ i.isLt⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl

lemma sum_indices {M : Type*} [AddCommMonoid M] (f : DerivativeIndex 1 1 → M) :
    ∑ α, f α = f (zeroIndex 1 1) + f firstIndex := by
  rw [← Equiv.sum_comp indexEquiv.symm]
  simp [Fin.sum_univ_two, indexEquiv, zeroIndex, firstIndex]

def h1Value : H1 𝕜 →L[𝕜] L2 𝕜 :=
  (PiLp.proj 2 _ (zeroIndex 1 1)).comp (hilbertDerivativeGraph 𝕜 (⊤ : Opens Line) 1).subtypeL

def h1Derivative : H1 𝕜 →L[𝕜] L2 𝕜 :=
  (PiLp.proj 2 _ firstIndex).comp (hilbertDerivativeGraph 𝕜 (⊤ : Opens Line) 1).subtypeL

lemma h1_inner (h k : H1 𝕜) : ⟪h, k⟫_𝕜 =
    ⟪h1Value h, h1Value k⟫_𝕜 + ⟪h1Derivative h, h1Derivative k⟫_𝕜 := by
  change ⟪h.val, k.val⟫_𝕜 = _
  rw [PiLp.inner_apply, sum_indices]
  rfl

lemma h1_norm_sq (h : H1 𝕜) : ‖h‖ ^ 2 = ‖h1Value h‖ ^ 2 + ‖h1Derivative h‖ ^ 2 := by
  change ‖h.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, sum_indices]
  rfl

def valueL (p : Potential) : Space 𝕜 p →L[𝕜] L2 𝕜 :=
  h1Value.comp ((WithLp.fstL 2 𝕜 (H1 𝕜) (L2 𝕜)).comp (weightedGraph 𝕜 p).subtypeL)

def derivativeL (p : Potential) : Space 𝕜 p →L[𝕜] L2 𝕜 :=
  h1Derivative.comp ((WithLp.fstL 2 𝕜 (H1 𝕜) (L2 𝕜)).comp (weightedGraph 𝕜 p).subtypeL)

def weightedL (p : Potential) : Space 𝕜 p →L[𝕜] L2 𝕜 :=
  (WithLp.sndL 2 𝕜 (H1 𝕜) (L2 𝕜)).comp (weightedGraph 𝕜 p).subtypeL

@[simp] lemma valueL_apply (p : Potential) (u : Space 𝕜 p) : valueL p u = value u := rfl
@[simp] lemma derivativeL_apply (p : Potential) (u : Space 𝕜 p) : derivativeL p u = derivative u := rfl
@[simp] lemma weightedL_apply (p : Potential) (u : Space 𝕜 p) : weightedL p u = weighted u := rfl

theorem weighted_membership : Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.Membership := by
  intro 𝕜 _ p h
  constructor
  · rintro ⟨u, hu⟩
    have hw := u.property
    change u.val.snd =ᵐ[lineMeasure] (fun x => weight 𝕜 p x * u.val.fst.val (zeroIndex 1 1) x) at hw
    rw [hu] at hw
    exact MemLp.ae_eq hw (Lp.memLp u.val.snd)
  · intro hw
    refine ⟨⟨WithLp.toLp 2 (h, hw.toLp _), ?_⟩, rfl⟩
    exact hw.coeFn_toLp

theorem weighted_inner_formula : Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.InnerFormula := by
  intro 𝕜 _ p v u
  change ⟪v.val, u.val⟫_𝕜 = _
  rw [WithLp.prod_inner_apply, h1_inner]
  change ⟪value v, value u⟫_𝕜 + ⟪derivative v, derivative u⟫_𝕜 + _ = _
  rw [add_comm (⟪value v, value u⟫_𝕜)]
  rfl

theorem weighted_norm_formula : Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.NormFormula := by
  intro 𝕜 _ p u
  change ‖u.val‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, h1_norm_sq]
  change ‖value u‖ ^ 2 + ‖derivative u‖ ^ 2 + ‖weighted u‖ ^ 2 = _
  ring

theorem weighted_underlying_injective :
    Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.UnderlyingInjective := by
  intro 𝕜 _ p u v huv
  have hh : u.val.fst = v.val.fst := by
    apply (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm.injective
    apply sobolev_underlying_injective 𝕜 1 (⊤ : Opens Line) 1 2
    exact huv
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext hh
  apply Lp.ext
  filter_upwards [u.property, v.property] with x hx hy
  change u.val.snd x = v.val.snd x
  rw [hx, hy, hh]

/-- Closedness uses a common a.e.-convergent subsequence for the two components,
so no bounded-multiplier assumption on the potential is introduced. -/
theorem weightedGraph_closed (p : Potential) :
    IsClosed (weightedGraph 𝕜 p : Set (Ambient 𝕜)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro z w hz hzw
  have hv : Tendsto (fun n => h1Value (z n).fst) atTop (𝓝 (h1Value w.fst)) :=
    (h1Value.continuous.comp (WithLp.continuous_fst 2 (H1 𝕜) (L2 𝕜))).continuousAt.tendsto.comp hzw
  have hs : Tendsto (fun n => (z n).snd) atTop (𝓝 w.snd) :=
    (WithLp.continuous_snd 2 (H1 𝕜) (L2 𝕜)).continuousAt.tendsto.comp hzw
  obtain ⟨ns, hns, hv'⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hs'⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hs.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have heq : ∀ᵐ x ∂lineMeasure, ∀ n, (z n).snd x =
      weight 𝕜 p x * h1Value (z n).fst x := ae_all_iff.mpr hz
  filter_upwards [hv', hs', heq] with x hvx hsx heqx
  exact tendsto_nhds_unique hsx
    (((tendsto_const_nhds.mul (hvx.comp hms.tendsto_atTop))).congr
      (fun n => (heqx (ns (ms n))).symm))

instance spaceComplete (p : Potential) : CompleteSpace (Space 𝕜 p) := by
  let := hilbertDerivativeGraph_complete 𝕜 1 (⊤ : Opens Line) 1
  exact (weightedGraph_closed p).completeSpace_coe

instance spaceSeparable (p : Potential) : SeparableSpace (Space 𝕜 p) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (L2 𝕜) := by
    unfold L2 DomainLp
    infer_instance
  infer_instance

theorem weighted_hilbert : Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.Hilbert := by
  intro 𝕜 _ p
  exact ⟨inferInstance, inferInstance⟩

lemma weight_continuous (p : Potential) : Continuous (weight 𝕜 p) :=
  RCLike.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (p.toContinuousMap.continuous.comp (continuous_apply 0)))

/-- Every compactly supported smooth function lies in the actual weighted space,
even for unbounded p: only continuity on its compact support is needed. -/
theorem weighted_smooth_inclusion :
    Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.SmoothInclusion := by
  intro 𝕜 _ p φ
  let h := sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1 (testToSobolev (p := 2) 1 φ)
  have hh : h1Value h =ᵐ[lineMeasure] φ := by
    change (testToSobolev (p := 2) 1 φ).val (zeroIndex 1 1) =ᵐ[lineMeasure] φ
    rw [testToSobolev_underlying]
    exact testToDomainLp_coe φ
  have hw : MemLp (fun x => weight 𝕜 p x * φ x) 2 lineMeasure :=
    ((weight_continuous p).mul φ.continuous).memLp_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  have hw' : MemLp (fun x => weight 𝕜 p x * h1Value h x) 2 lineMeasure := by
    apply MemLp.ae_eq (hf_Lp := hw)
    filter_upwards [hh] with x hx
    rw [hx]
  obtain ⟨u, hu⟩ := (weighted_membership 𝕜 p h).mpr hw'
  refine ⟨u, ?_⟩
  change h1Value u.val.fst =ᵐ[lineMeasure] φ
  rw [hu]
  exact hh

lemma weighted_ae (p : Potential) (u : Space 𝕜 p) :
    weighted u =ᵐ[lineMeasure] (fun x => weight 𝕜 p x * value u x) := u.property

lemma potential_product_ae (p : Potential) (v u : Space 𝕜 p) :
    (fun x => conj (weighted v x) * weighted u x) =ᵐ[lineMeasure]
      (fun x => (p.toContinuousMap (x 0) : 𝕜) * conj (value v x) * value u x) := by
  filter_upwards [weighted_ae p v, weighted_ae p u] with x hv hu
  rw [hv, hu]
  simp only [weight, map_mul, RCLike.conj_ofReal]
  have hs : (Real.sqrt (p.toContinuousMap (x 0)) : 𝕜) *
      (Real.sqrt (p.toContinuousMap (x 0)) : 𝕜) = (p.toContinuousMap (x 0) : 𝕜) := by
    rw [← RCLike.ofReal_mul, ← pow_two, Real.sq_sqrt (p.nonneg _)]
  calc
    _ = ((Real.sqrt (p.toContinuousMap (x 0)) : 𝕜) *
      (Real.sqrt (p.toContinuousMap (x 0)) : 𝕜)) * conj (value v x) * value u x := by ring
    _ = _ := by rw [hs]

lemma scalar_inner_integrable (f g : L2 𝕜) :
    Integrable (fun x => conj (f x) * g x) lineMeasure := by
  simpa only [RCLike.inner_apply, mul_comm] using L2.integrable_inner (𝕜 := 𝕜) f g

lemma scalar_inner_integral (f g : L2 𝕜) :
    ⟪f, g⟫_𝕜 = ∫ x, conj (f x) * g x ∂lineMeasure := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, mul_comm]

theorem weighted_form_integral :
    Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.FormIntegral := by
  intro 𝕜 _ p v u
  have hd := scalar_inner_integrable (derivative v) (derivative u)
  have hw := scalar_inner_integrable (weighted v) (weighted u)
  have hp := hw.congr (potential_product_ae p v u)
  refine ⟨hd.add hp, ?_⟩
  rw [energyForm, scalar_inner_integral, scalar_inner_integral,
    integral_congr_ae (potential_product_ae p v u), integral_add hd hp]

/-- Pulling back the native L² inner product gives a bounded sesquilinear form. -/
def pullInner {p : Potential} (L : Space 𝕜 p →L[𝕜] L2 𝕜) :
    Space 𝕜 p →L⋆[𝕜] Space 𝕜 p →L[𝕜] 𝕜 :=
  ((ContinuousLinearMap.compL 𝕜 (Space 𝕜 p) (L2 𝕜) 𝕜).flip L).comp ((innerSL 𝕜).comp L)

@[simp] lemma pullInner_apply {p : Potential} (L : Space 𝕜 p →L[𝕜] L2 𝕜)
    (v u : Space 𝕜 p) : pullInner L v u = ⟪L v, L u⟫_𝕜 := rfl

def energyFormL (p : Potential) : Space 𝕜 p →L⋆[𝕜] Space 𝕜 p →L[𝕜] 𝕜 :=
  pullInner (derivativeL p) + pullInner (weightedL p)

@[simp] lemma energyFormL_apply (p : Potential) (v u : Space 𝕜 p) :
    energyFormL p v u = energyForm v u := rfl

/-- The two components occurring in the energy, with their Euclidean norm. -/
def energyPair {p : Potential} (u : Space 𝕜 p) : WithLp 2 (L2 𝕜 × L2 𝕜) :=
  WithLp.toLp 2 (derivative u, weighted u)

lemma energyPair_norm_le {p : Potential} (u : Space 𝕜 p) : ‖energyPair u‖ ≤ ‖u‖ := by
  have hn := weighted_norm_formula 𝕜 p u
  have he : ‖energyPair u‖ ^ 2 = ‖derivative u‖ ^ 2 + ‖weighted u‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 _
  nlinarith [sq_nonneg ‖value u‖, norm_nonneg (energyPair u), norm_nonneg u]

theorem weighted_form_bound : Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.FormBound := by
  intro 𝕜 _ p v u
  have he : energyForm v u = ⟪energyPair v, energyPair u⟫_𝕜 := rfl
  rw [he]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul (energyPair_norm_le v) (energyPair_norm_le u) (norm_nonneg _) (norm_nonneg _))

lemma energyForm_diagonal (p : Potential) (u : Space 𝕜 p) :
    RCLike.re (energyForm u u) = ‖derivative u‖ ^ 2 + ‖weighted u‖ ^ 2 := by
  simp only [energyForm, map_add, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The full variational conclusion follows once the exterior-potential
Poincaré estimate has been established. This lemma does not assert that estimate. -/
theorem variational_of_coercive (p : Potential) {α : ℝ} (hα : 0 < α)
    (hc : ∀ u : Space 𝕜 p, α * ‖u‖ ^ 2 ≤ RCLike.re (energyForm u u))
    (f : L2 𝕜) : ∃! u : Space 𝕜 p,
      ∀ v : Space 𝕜 p, energyForm v u = ⟪value v, f⟫_𝕜 := by
  let F : Space 𝕜 p →L⋆[𝕜] 𝕜 := (innerSLFlip 𝕜 f).comp (valueL p)
  obtain ⟨u, hu, _, huniq⟩ := ExpandedFA.Hilbert.LaxMilgramSolvability.solvability
    𝕜 (Space 𝕜 p) (energyFormL p) α ⟨hα, hc⟩ F
  exact ⟨u, hu, fun w hw => huniq w hw⟩

/-- Assembly interface for weighted approximation of an H¹ jet. The input is
an approximation theorem, not a certificate stored in the definition of V. -/
theorem weighted_density_of_jet_approximation (p : Potential)
    (ha : ∀ h : H1 𝕜, ∀ w : L2 𝕜,
      w =ᵐ[lineMeasure] (fun x => weight 𝕜 p x * h1Value h x) →
      ∀ ε : ℝ, 0 < ε → ∃ φ : Tests 𝕜 (⊤ : Opens Line), ∃ k : H1 𝕜,
        h1Value k =ᵐ[lineMeasure] φ ∧ ∃ z : L2 𝕜,
          z =ᵐ[lineMeasure] (fun x => weight 𝕜 p x * φ x) ∧
          ‖h - k‖ ^ 2 + ‖w - z‖ ^ 2 < ε ^ 2) : Dense (SmoothMembers 𝕜 p) := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨φ, k, hk, z, hz, herr⟩ := ha u.val.fst u.val.snd u.property ε hε
  have hv : WithLp.toLp 2 (k, z) ∈ weightedGraph 𝕜 p := by
    filter_upwards [hk, hz] with x hkx hzx
    change z x = weight 𝕜 p x * h1Value k x
    rw [hkx, hzx]
  let v : Space 𝕜 p := ⟨WithLp.toLp 2 (k, z), hv⟩
  have hnorm : ‖u - v‖ ^ 2 = ‖u.val.fst - k‖ ^ 2 + ‖u.val.snd - z‖ ^ 2 := by
    change ‖u.val - v.val‖ ^ 2 = _
    rw [WithLp.prod_norm_sq_eq_of_L2]
    rfl
  refine ⟨v, ⟨φ, hk⟩, ?_⟩
  rw [dist_eq_norm]
  rw [← hnorm] at herr
  exact (sq_lt_sq₀ (norm_nonneg (u - v)) hε.le).mp herr

/-- A uniform classical-test estimate extends to V by its weighted-norm
 density; neither completeness nor pointwise representatives are assumed here. -/
theorem coercivity_of_dense_smooth (p : Potential) (hd : Dense (SmoothMembers 𝕜 p))
    {α : ℝ} (hc : ∀ u ∈ SmoothMembers 𝕜 p,
      α * ‖u‖ ^ 2 ≤ ‖derivative u‖ ^ 2 + ‖weighted u‖ ^ 2) :
    ∀ u : Space 𝕜 p, α * ‖u‖ ^ 2 ≤ RCLike.re (energyForm u u) := by
  intro u
  rw [energyForm_diagonal]
  have hclosed : IsClosed {u : Space 𝕜 p |
      α * ‖u‖ ^ 2 ≤ ‖derivative u‖ ^ 2 + ‖weighted u‖ ^ 2} :=
    isClosed_le (continuous_const.mul (continuous_norm.pow 2))
      (((continuous_norm.comp (derivativeL p).continuous).pow 2).add
        ((continuous_norm.comp (weightedL p).continuous).pow 2))
  exact closure_minimal hc hclosed (hd u)

open ExpandedFA.Sobolev.Smoothing

lemma firstIndex_word : multiIndexWord (natIndex firstIndex) = [0] := by
  simp [multiIndexWord, natIndex, firstIndex]

lemma h1_cutoff_derivative (η : Tests 𝕜 (⊤ : Opens Line)) (h : H1 𝕜) :
    h1Derivative (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1
      (cutoffSobolev η ((sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm h))) =
    cutoffLp (testPartialCLM [0] η) (h1Value h) + cutoffLp η (h1Derivative h) := by
  change cutoffJet _ (multiIndexWord (natIndex firstIndex)) η [] = _
  rw [firstIndex_word]
  simp only [cutoffJet, wordLp_nil, List.nil_append]
  have hw : wordLp ((sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm h) [0] =
      h1Derivative h := by
    rw [wordLp, dite_eq_left (by simp)]
    have hi : wordIndex (d := 1) (m := 1) [0] (by simp) = firstIndex := by
      apply Subtype.ext
      funext i
      fin_cases i
      simp [wordIndex, boundedIndex, firstIndex]
    rw [hi]
    rfl
  rw [hw]
  rfl

/-- Multiplication by an ordinary compact smooth cutoff in the weighted graph. -/
def cutoffSpace (p : Potential) (η : Tests 𝕜 (⊤ : Opens Line)) (u : Space 𝕜 p) :
    Space 𝕜 p :=
  ⟨WithLp.toLp 2
    (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1
      (cutoffSobolev η ((sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm u.val.fst)),
     cutoffLp η (weighted u)), by
    filter_upwards [cutoffLp_coe η (weighted u),
      cutoffSobolev_coe η ((sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm u.val.fst),
      weighted_ae p u] with x hx hy hz
    change cutoffLp η (weighted u) x = weight 𝕜 p x *
      underlyingLp (cutoffSobolev η
        ((sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm u.val.fst)) x
    rw [hx, hy]
    change η x * weighted u x = weight 𝕜 p x * (η x * value u x)
    rw [hz]
    ring⟩

@[simp] lemma value_cutoffSpace (p : Potential) (η : Tests 𝕜 (⊤ : Opens Line))
    (u : Space 𝕜 p) : value (cutoffSpace p η u) = cutoffLp η (value u) := by
  exact cutoffSobolev_underlying η _

@[simp] lemma derivative_cutoffSpace (p : Potential) (η : Tests 𝕜 (⊤ : Opens Line))
    (u : Space 𝕜 p) : derivative (cutoffSpace p η u) =
      cutoffLp (testPartialCLM [0] η) (value u) + cutoffLp η (derivative u) :=
  h1_cutoff_derivative η u.val.fst

@[simp] lemma weighted_cutoffSpace (p : Potential) (η : Tests 𝕜 (⊤ : Opens Line))
    (u : Space 𝕜 p) : weighted (cutoffSpace p η u) = cutoffLp η (weighted u) := rfl

namespace L2Approximation

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {𝕜 : Type*} [RCLike 𝕜]

lemma l2_norm_sq_integral (f : Lp 𝕜 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := 𝕜) f f)]
  simp only [inner_self_eq_norm_sq]

/-- An integrable square majorant and a.e. convergence imply L² convergence to zero. -/
theorem l2_tendsto_zero_of_dominated
    (f : ℕ → Lp 𝕜 2 μ) (b : X → ℝ)
    (hb : Integrable (fun x => b x ^ 2) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hint : Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) (fun x => b x ^ 2)
      (fun n => ((Lp.aestronglyMeasurable (f n)).norm.pow 2)) hb
      (fun n => ?_) ?_
    · simpa using hh
    · filter_upwards [hbound n] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    · filter_upwards [hlim] with x hx
      simpa using hx.norm.pow 2
  have hsq : Tendsto (fun n => ‖f n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [← l2_norm_sq_integral] using hint
  have hn : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

/-- A common L² majorant and a.e. convergence imply convergence in L². -/
theorem l2_tendsto_of_dominated
    (f : ℕ → Lp 𝕜 2 μ) (f₀ : Lp 𝕜 2 μ) (b : X → ℝ)
    (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x))) :
    Tendsto f atTop (𝓝 f₀) := by
  have hh : Tendsto (fun n => f n - f₀) atTop (𝓝 0) := by
    apply l2_tendsto_zero_of_dominated (fun n => f n - f₀)
      (fun x => b x + ‖f₀ x‖)
      (hb.add (Lp.memLp f₀).norm).integrable_sq
    · intro n
      filter_upwards [hbound n, Lp.coeFn_sub (f n) f₀] with x hx hsub
      rw [hsub]
      exact (norm_sub_le _ _).trans (add_le_add hx (le_refl ‖f₀ x‖))
    · have hsub : ∀ᵐ x ∂μ, ∀ n, (f n - f₀) x = f n x - f₀ x :=
        ae_all_iff.mpr (fun n => Lp.coeFn_sub (f n) f₀)
      filter_upwards [hlim, hsub] with x hx hs
      have hx' : Tendsto (fun n => f n x - f₀ x) atTop (𝓝 0) := by
        simpa only [sub_self] using hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f₀ x) atTop (𝓝 (f₀ x)))
      exact hx'.congr (fun n => (hs n).symm)
  exact tendsto_sub_nhds_zero_iff.mp hh

end L2Approximation



lemma h1Value_norm_le (h : H1 𝕜) : ‖h1Value h‖ ≤ ‖h‖ := by
  have hn := h1_norm_sq h
  nlinarith [sq_nonneg ‖h1Derivative h‖, norm_nonneg h, norm_nonneg (h1Value h)]

lemma norm_le_components {p : Potential} (u : Space 𝕜 p) :
    ‖u‖ ≤ ‖u.val.fst‖ + ‖weighted u‖ := by
  have hn : ‖u‖ ^ 2 = ‖u.val.fst‖ ^ 2 + ‖weighted u‖ ^ 2 := by
    change ‖u.val‖ ^ 2 = _
    exact WithLp.prod_norm_sq_eq_of_L2 _
  nlinarith [norm_nonneg u, norm_nonneg u.val.fst, norm_nonneg (weighted u)]

lemma cutoffSpace_mem_closure (p : Potential) (η : Tests 𝕜 (⊤ : Opens Line))
    (u : Space 𝕜 p) : cutoffSpace p η u ∈ closure (SmoothMembers 𝕜 p) := by
  classical
  obtain ⟨C₀, hC₀⟩ := η.hasCompactSupport.isCompact.exists_bound_of_continuousOn
    (weight_continuous (𝕜 := 𝕜) p).continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ x ∈ tsupport η, ‖weight 𝕜 p x‖ ≤ C :=
    fun x hx => (hC₀ x hx).trans (le_max_left _ _)
  let L := (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).toContinuousLinearMap
  let q := (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm u.val.fst
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let τ : ℝ := ε / ((1 + C) * (‖L‖ + 1))
  have hτ : 0 < τ := div_pos hε (mul_pos (by linarith) (by positivity))
  obtain ⟨δ, hδ, Hδ⟩ := compact_cutoff_error_canonical_of_words q
    (compact_cutoff_error_words q) η τ hτ
  obtain ⟨ρ, hρ⟩ := exists_mollifier 1
  obtain ⟨r, hr, herr⟩ := exists_regularization_jet_error_lt (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    ρ hρ q η.hasCompactSupport.isCompact η.tsupport_subset hδ
  let f := regularize ρ r (q.val (zeroIndex 1 1))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := regularize_contDiff ρ hρ hr _
  obtain ⟨e, he, hen⟩ := Hδ f hf herr
  let φ := smoothMulTest η f hf
  obtain ⟨v, hv⟩ := weighted_smooth_inclusion 𝕜 p φ
  let a := cutoffSpace p η u
  have hval : value (v - a) =ᵐ[lineMeasure]
      fun x => η x * (f x - value u x) := by
    filter_upwards [Lp.coeFn_sub (value v) (value a), hv,
      cutoffLp_coe η (value u)] with x hx hxv hxa
    change ((value v - value a) : L2 𝕜) x = _
    rw [hx]
    change value v x - cutoffLp η (value u) x = _
    rw [hxv, hxa]
    change η x * f x - η x * value u x = _
    ring
  have hjet : (v - a).val.fst = L e := by
    apply (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm.injective
    apply sobolev_underlying_injective 𝕜 1 (⊤ : Opens Line) 1 2
    apply Lp.ext
    exact hval.trans he.symm
  have hw : ‖weighted (v - a)‖ ≤ C * ‖value (v - a)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [weighted_ae p (v - a), hval] with x hx heq
    rw [hx, norm_mul]
    by_cases hs : x ∈ tsupport η
    · exact mul_le_mul_of_nonneg_right (hbound x hs) (norm_nonneg _)
    · have hz : value (v - a) x = 0 := by
        rw [heq, image_eq_zero_of_notMem_tsupport hs, zero_mul]
      simp [hz]
  have hvL : value (v - a) = h1Value (L e) := by
    change h1Value ((v - a).val.fst) = _
    rw [hjet]
  rw [hvL] at hw
  have hnv : ‖v - a‖ ≤ (1 + C) * ‖L e‖ := by
    calc
      ‖v - a‖ ≤ ‖(v - a).val.fst‖ + ‖weighted (v - a)‖ := norm_le_components _
      _ ≤ ‖L e‖ + C * ‖h1Value (L e)‖ := by
        rw [hjet]
        exact add_le_add le_rfl hw
      _ ≤ ‖L e‖ + C * ‖L e‖ := by
        gcongr
        exact h1Value_norm_le _
      _ = _ := by ring
  refine ⟨v, ⟨φ, hv⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖v - a‖ ≤ (1 + C) * ‖L e‖ := hnv
    _ ≤ (1 + C) * (‖L‖ * ‖e‖) := mul_le_mul_of_nonneg_left (L.le_opNorm e) (by linarith)
    _ ≤ (1 + C) * ((‖L‖ + 1) * ‖e‖) := by gcongr; linarith
    _ < (1 + C) * ((‖L‖ + 1) * τ) := by gcongr
    _ = ε := by dsimp [τ]; field_simp




def exhaustionBump (n : ℕ) : ContDiffBump (0 : Line) :=
  ⟨(n : ℝ) + 1, 2 * ((n : ℝ) + 1), by positivity, by nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩

def exhaustionRealTest (n : ℕ) : Tests ℝ (⊤ : Opens Line) :=
  ⟨exhaustionBump n, (exhaustionBump n).contDiff,
    (exhaustionBump n).hasCompactSupport, subset_univ _⟩

def exhaustionCutoff (n : ℕ) : Tests 𝕜 (⊤ : Opens Line) :=
  liftRealTest (exhaustionRealTest n)

lemma exhaustionCutoff_apply (n : ℕ) (x : Line) :
    exhaustionCutoff (𝕜 := 𝕜) n x = (exhaustionBump n x : 𝕜) := rfl

lemma exhaustionBump_scale (n : ℕ) (x : Line) :
    exhaustionBump n x = exhaustionBump 0 (((n : ℝ) + 1)⁻¹ • x) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [ContDiffBump.apply, exhaustionBump, sub_zero, Nat.cast_zero, zero_add,
    inv_one, one_smul, mul_one, div_one]
  rw [mul_div_cancel_right₀ _ hn]

lemma exhaustionCutoff_norm_le (n : ℕ) (x : Line) :
    ‖exhaustionCutoff (𝕜 := 𝕜) n x‖ ≤ 1 := by
  rw [exhaustionCutoff_apply, RCLike.norm_ofReal, abs_of_nonneg (exhaustionBump n).nonneg]
  exact (exhaustionBump n).le_one

lemma exhaustionCutoff_eventually_one (x : Line) :
    ∀ᶠ n : ℕ in atTop, exhaustionCutoff (𝕜 := 𝕜) n x = 1 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  filter_upwards [ht.eventually (eventually_ge_atTop ‖x‖)] with n hn
  rw [exhaustionCutoff_apply, (exhaustionBump n).one_of_mem_closedBall]
  · simp
  · simpa only [mem_closedBall, dist_zero_right, exhaustionBump] using hn

lemma exhaustionCutoff_eventually_partial_zero (x : Line) :
    ∀ᶠ n : ℕ in atTop, testPartialCLM [0] (exhaustionCutoff (𝕜 := 𝕜) n) x = 0 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  filter_upwards [ht.eventually (eventually_gt_atTop ‖x‖)] with n hn
  rw [testPartial_single_apply]
  have he : (exhaustionCutoff (𝕜 := 𝕜) n : Line → 𝕜) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [(exhaustionBump n).eventuallyEq_one_of_mem_ball
      (by simpa only [mem_ball, dist_zero_right, exhaustionBump] using hn)] with y hy
    change (exhaustionBump n y : 𝕜) = 1
    rw [hy]
    simp
  rw [he.fderiv_eq]
  simp

lemma exhaustionCutoff_partial_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖testPartialCLM [0] (exhaustionCutoff (𝕜 := 𝕜) n) x‖ ≤ C := by
  let f : Line → 𝕜 := fun x => (exhaustionBump 0 x : 𝕜)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (exhaustionBump 0).contDiff
  have hs : HasCompactSupport f :=
    (exhaustionBump 0).hasCompactSupport.comp_left (by simp)
  obtain ⟨C, hC⟩ := (hf.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hs.fderiv ℝ)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro n x
  rw [testPartial_single_apply]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  let S : Line →L[ℝ] Line := ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ Line
  have he : (exhaustionCutoff (𝕜 := 𝕜) n : Line → 𝕜) = f ∘ S := by
    funext y
    exact congrArg (fun r : ℝ => (r : 𝕜)) (exhaustionBump_scale n y)
  rw [he, fderiv_comp x (hf.differentiable (by simp) _) S.differentiableAt, S.fderiv]
  change ‖(fderiv ℝ f (S x)) (S (coordinateVector 0))‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ f (S x)‖ * ‖S (coordinateVector 0)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ max C 0 * 1 := by
      apply mul_le_mul
      · exact (hC _).trans (le_max_left _ _)
      · simp only [S, smul_apply, ContinuousLinearMap.id_apply,
          norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
        have hd : ‖coordinateVector (d := 1) 0‖ = 1 := by simp only [coordinateVector, Pi.norm_single, norm_one]
        rw [hd, mul_one]
        exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
      · exact norm_nonneg _
      · exact le_max_right _ _
    _ = _ := mul_one _


lemma exhaustionCutoff_lp_tendsto (v : L2 𝕜) :
    Tendsto (fun n => cutoffLp (exhaustionCutoff n) v) atTop (𝓝 v) := by
  apply L2Approximation.l2_tendsto_of_dominated _ v (fun x => ‖v x‖) (Lp.memLp v).norm
  · intro n
    filter_upwards [cutoffLp_coe (exhaustionCutoff n) v] with x hx
    rw [hx, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (exhaustionCutoff_norm_le n x)
  · have he : ∀ᵐ x ∂lineMeasure, ∀ n, cutoffLp (exhaustionCutoff n) v x =
        exhaustionCutoff n x * v x := ae_all_iff.mpr fun n => cutoffLp_coe _ _
    filter_upwards [he] with x hx
    have hlim : Tendsto (fun n : ℕ => exhaustionCutoff (𝕜 := 𝕜) n x) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (exhaustionCutoff_eventually_one x))
    have hlim' := hlim.mul (tendsto_const_nhds (x := v x))
    simpa only [one_mul] using hlim'.congr (fun n => (hx n).symm)

lemma exhaustionCutoff_partial_lp_tendsto (v : L2 𝕜) :
    Tendsto (fun n => cutoffLp (testPartialCLM [0] (exhaustionCutoff n)) v)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exhaustionCutoff_partial_bound (𝕜 := 𝕜)
  apply L2Approximation.l2_tendsto_of_dominated _ 0
    (fun x => C * ‖v x‖) ((Lp.memLp v).norm.const_mul C)
  · intro n
    filter_upwards [cutoffLp_coe (testPartialCLM [0] (exhaustionCutoff n)) v] with x hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)
  · have he : ∀ᵐ x ∂lineMeasure, ∀ n,
        cutoffLp (testPartialCLM [0] (exhaustionCutoff n)) v x =
          testPartialCLM [0] (exhaustionCutoff n) x * v x :=
      ae_all_iff.mpr fun n => cutoffLp_coe _ _
    filter_upwards [he, Lp.coeFn_zero 𝕜 2 lineMeasure] with x hx hz
    have hz' : (0 : L2 𝕜) x = 0 := hz
    change Tendsto _ _ (𝓝 ((0 : L2 𝕜) x))
    rw [hz']
    have hlim : Tendsto (fun n : ℕ => testPartialCLM [0] (exhaustionCutoff (𝕜 := 𝕜) n) x)
        atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (exhaustionCutoff_eventually_partial_zero x))
    have hlim' := hlim.mul (tendsto_const_nhds (x := v x))
    simpa only [zero_mul] using hlim'.congr (fun n => (hx n).symm)




lemma h1_tendsto_of_components {h : ℕ → H1 𝕜} {u : H1 𝕜}
    (hv : Tendsto (fun n => h1Value (h n)) atTop (𝓝 (h1Value u)))
    (hd : Tendsto (fun n => h1Derivative (h n)) atTop (𝓝 (h1Derivative u))) :
    Tendsto h atTop (𝓝 u) := by
  have ha (α : DerivativeIndex 1 1) : α = zeroIndex 1 1 ∨ α = firstIndex := by
    have hsmall := (indexEquiv α).isLt
    have hi : (indexEquiv α).val = 0 ∨ (indexEquiv α).val = 1 := by omega
    rcases hi with hi | hi
    · left
      apply indexEquiv.injective
      exact Fin.ext hi
    · right
      apply indexEquiv.injective
      exact Fin.ext hi
  apply tendsto_subtype_rng.mpr
  have hpi : Tendsto (fun n α => (h n).val α) atTop (𝓝 (fun α => u.val α)) := by
    apply tendsto_pi_nhds.mpr
    intro α
    rcases ha α with rfl | rfl
    · exact hv
    · exact hd
  exact (PiLp.continuous_toLp 2 (fun _ : DerivativeIndex 1 1 => L2 𝕜)).continuousAt.tendsto.comp hpi

lemma cutoffSpace_tendsto (p : Potential) (η : ℕ → Tests 𝕜 (⊤ : Opens Line))
    (hη : ∀ v : L2 𝕜, Tendsto (fun n => cutoffLp (η n) v) atTop (𝓝 v))
    (hη' : ∀ v : L2 𝕜,
      Tendsto (fun n => cutoffLp (testPartialCLM [0] (η n)) v) atTop (𝓝 0))
    (u : Space 𝕜 p) : Tendsto (fun n => cutoffSpace p (η n) u) atTop (𝓝 u) := by
  have hv : Tendsto (fun n => value (cutoffSpace p (η n) u)) atTop (𝓝 (value u)) := by
    simpa only [value_cutoffSpace] using hη (value u)
  have hd : Tendsto (fun n => derivative (cutoffSpace p (η n) u)) atTop
      (𝓝 (derivative u)) := by
    simpa only [derivative_cutoffSpace, zero_add] using
      (hη' (value u)).add (hη (derivative u))
  have hw : Tendsto (fun n => weighted (cutoffSpace p (η n) u)) atTop
      (𝓝 (weighted u)) := by
    simpa only [weighted_cutoffSpace] using hη (weighted u)
  have hh : Tendsto (fun n => (cutoffSpace p (η n) u).val.fst) atTop (𝓝 u.val.fst) :=
    h1_tendsto_of_components hv hd
  apply tendsto_subtype_rng.mpr
  exact (WithLp.prod_continuous_toLp 2 (H1 𝕜) (L2 𝕜)).continuousAt.tendsto.comp (hh.prodMk_nhds hw)

lemma weighted_smooth_density_of_cutoffs (p : Potential)
    (η : ℕ → Tests 𝕜 (⊤ : Opens Line))
    (hη : ∀ v : L2 𝕜, Tendsto (fun n => cutoffLp (η n) v) atTop (𝓝 v))
    (hη' : ∀ v : L2 𝕜,
      Tendsto (fun n => cutoffLp (testPartialCLM [0] (η n)) v) atTop (𝓝 0)) :
    Dense (SmoothMembers 𝕜 p) := by
  intro u
  exact isClosed_closure.mem_of_tendsto (cutoffSpace_tendsto p η hη hη' u)
    (Filter.Eventually.of_forall (fun n => cutoffSpace_mem_closure p (η n) u))



/-- Compactly supported smooth functions are dense in the full weighted energy norm. -/
theorem weighted_smooth_density :
    Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.SmoothDensity := by
  intro 𝕜 _ p
  exact weighted_smooth_density_of_cutoffs p exhaustionCutoff
    exhaustionCutoff_lp_tendsto exhaustionCutoff_partial_lp_tendsto



def multiplier (x : Line) : ℝ := Real.arctan (x 0)
def multiplierDerivative (x : Line) : ℝ := 1 / (1 + (x 0)^2)

lemma multiplier_contDiff : ContDiff ℝ (⊤ : ℕ∞) multiplier :=
  Real.contDiff_arctan.comp (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)

lemma multiplier_fderiv (x : Line) :
    fderiv ℝ multiplier x (coordinateVector (0 : Fin 1)) = multiplierDerivative x := by
  have h : HasFDerivAt (fun x : Line => x 0) (ContinuousLinearMap.proj (0 : Fin 1)) x :=
    hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) x
  unfold multiplier
  rw [(h.arctan).fderiv]
  simp [multiplierDerivative, coordinateVector]

lemma test_norm_sq_fderiv (φ : Tests 𝕜 (⊤ : Opens Line)) (x : Line) :
    fderiv ℝ (fun y => ‖φ y‖^2) x (coordinateVector (0 : Fin 1)) =
      2 * ⟪φ x, testPartialCLM [0] φ x⟫_ℝ := by
  rw [((φ.contDiff.differentiable (by simp) x).hasFDerivAt.norm_sq).fderiv]
  simp [testPartial_single_apply]

lemma multiplier_bound (x : Line) : |multiplier x| ≤ Real.pi := by
  apply (abs_le).mpr
  constructor
  · have := Real.neg_pi_div_two_lt_arctan (x 0)
    have := Real.pi_pos
    dsimp [multiplier]
    linarith
  · exact (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])

lemma multiplier_positive (x : Line) : 0 < multiplierDerivative x := by
  unfold multiplierDerivative
  positivity

lemma multiplier_potential_lower_bound (p : Potential) (hp : PositiveAtInfinity p) :
    ∃ β : ℝ, 0 < β ∧ ∀ x : Line,
      β ≤ multiplierDerivative x + p.toContinuousMap (x 0) := by
  obtain ⟨δ, hδ, R, hR⟩ := hp
  refine ⟨min δ (1 / (1 + R^2)), lt_min hδ (by positivity), ?_⟩
  intro x
  by_cases hx : R ≤ |x 0|
  · exact (min_le_left _ _).trans ((hR _ hx).trans (le_add_of_nonneg_left (multiplier_positive x).le))
  · have hxR : |x 0| < R := lt_of_not_ge hx
    have hs : (x 0)^2 ≤ R^2 := sq_le_sq.mpr (hxR.le.trans (le_abs_self _))
    have hi : 1 / (1 + R^2) ≤ multiplierDerivative x := by
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact (min_le_right _ _).trans (hi.trans (le_add_of_nonneg_right (p.nonneg _)))

lemma multiplier_ibp (φ : Tests 𝕜 (⊤ : Opens Line)) :
    (∫ x : Line, multiplierDerivative x * ‖φ x‖^2) =
      -(∫ x : Line, multiplier x * (2 * ⟪φ x, testPartialCLM [0] φ x⟫_ℝ)) := by
  let g : Line → ℝ := fun x => ‖φ x‖^2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := φ.contDiff.norm_sq 𝕜
  have hgs : HasCompactSupport g := φ.hasCompactSupport.comp_left (g := fun z : 𝕜 => ‖z‖^2) (by simp)
  have hg' : Continuous (fun x => fderiv ℝ g x (coordinateVector (0 : Fin 1))) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ : Integrable (fun x => fderiv ℝ multiplier x (coordinateVector (0 : Fin 1)) * g x) :=
    (((multiplier_contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  have hi₂ : Integrable (fun x => multiplier x * fderiv ℝ g x (coordinateVector (0 : Fin 1))) :=
    (multiplier_contDiff.continuous.mul hg').integrable_of_hasCompactSupport
      (hgs.fderiv_apply ℝ (coordinateVector (0 : Fin 1))).mul_left
  have hi₃ : Integrable (fun x => multiplier x * g x) :=
    (multiplier_contDiff.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun x _ => multiplier_contDiff.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)
  simp only [multiplier_fderiv] at h
  change (∫ x, multiplier x * fderiv ℝ (fun y => ‖φ y‖^2) x (coordinateVector (0 : Fin 1))) = -_ at h
  simp_rw [test_norm_sq_fderiv] at h
  linarith

lemma multiplier_young {β : ℝ} (hβ : 0 < β) (a b : ℝ) :
    2 * Real.pi * a * b ≤ β / 2 * a^2 + (2 * Real.pi^2 / β) * b^2 := by
  apply (mul_le_mul_iff_right₀ hβ).mp
  have hdiv : (2 * Real.pi^2 / β) * β = 2 * Real.pi^2 := div_mul_cancel₀ _ hβ.ne'
  nlinarith [sq_nonneg (β*a - 2*Real.pi*b)]

lemma test_value_estimate_integral (p : Potential) (hp : PositiveAtInfinity p) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Tests 𝕜 (⊤ : Opens Line),
      (∫ x : Line, ‖φ x‖^2) ≤ C * ((∫ x : Line, ‖testPartialCLM [0] φ x‖^2) +
        ∫ x : Line, p.toContinuousMap (x 0) * ‖φ x‖^2) := by
  obtain ⟨β, hβ, hlower⟩ := multiplier_potential_lower_bound p hp
  let K := 2 * Real.pi^2 / β
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := 2 * (K + 1) / β
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro φ
  let ψ := testPartialCLM [0] φ
  have hv : Integrable (fun x : Line => ‖φ x‖^2) :=
    (φ.contDiff.norm_sq 𝕜).continuous.integrable_of_hasCompactSupport
      (φ.hasCompactSupport.comp_left (g := fun z : 𝕜 => ‖z‖^2) (by simp))
  have hd : Integrable (fun x : Line => ‖ψ x‖^2) :=
    (ψ.contDiff.norm_sq 𝕜).continuous.integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.comp_left (g := fun z : 𝕜 => ‖z‖^2) (by simp))
  have hw : Integrable (fun x : Line => p.toContinuousMap (x 0) * ‖φ x‖^2) :=
    ((p.toContinuousMap.continuous.comp (continuous_apply 0)).mul (φ.contDiff.norm_sq 𝕜).continuous).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.comp_left (g := fun z : 𝕜 => ‖z‖^2) (by simp)).mul_left
  have hq' : Continuous multiplierDerivative := by
    unfold multiplierDerivative
    exact continuous_const.div (continuous_const.add ((continuous_apply 0).pow 2)) (fun x => by positivity)
  have hq : Integrable (fun x : Line => multiplierDerivative x * ‖φ x‖^2) :=
    (hq'.mul (φ.contDiff.norm_sq 𝕜).continuous).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.comp_left (g := fun z : 𝕜 => ‖z‖^2) (by simp)).mul_left
  have hcross : Integrable (fun x : Line => -(multiplier x * (2 * ⟪φ x, ψ x⟫_ℝ))) := by
    apply Integrable.neg
    exact (multiplier_contDiff.continuous.mul (continuous_const.mul (φ.continuous.inner ψ.continuous))).integrable_of_hasCompactSupport
      ((φ.hasCompactSupport.comp₂_left ψ.hasCompactSupport (m := fun a b => ⟪a,b⟫_ℝ) (by simp)).mul_left).mul_left
  have hcross_le : ∀ x : Line, -(multiplier x * (2 * ⟪φ x, ψ x⟫_ℝ)) ≤
      β / 2 * ‖φ x‖^2 + K * ‖ψ x‖^2 := by
    intro x
    calc
      _ ≤ |multiplier x| * (2 * |⟪φ x, ψ x⟫_ℝ|) := by
        calc
          _ ≤ |multiplier x * (2 * ⟪φ x, ψ x⟫_ℝ)| := neg_le_abs _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ Real.pi * (2 * (‖φ x‖ * ‖ψ x‖)) := by
        gcongr
        · exact multiplier_bound x
        · exact abs_real_inner_le_norm _ _
      _ ≤ _ := by simpa [K, mul_assoc, mul_left_comm, mul_comm] using multiplier_young hβ ‖φ x‖ ‖ψ x‖
  have hbound₂ : β * (∫ x : Line, ‖φ x‖^2) ≤
      (∫ x : Line, multiplierDerivative x * ‖φ x‖^2) + (∫ x : Line, p.toContinuousMap (x 0) * ‖φ x‖^2) := by
    rw [← integral_const_mul, ← integral_add hq hw]
    apply integral_mono (hv.const_mul β) (hq.add hw)
    intro x
    change β * ‖φ x‖^2 ≤ multiplierDerivative x * ‖φ x‖^2 + p.toContinuousMap (x 0) * ‖φ x‖^2
    nlinarith [mul_le_mul_of_nonneg_right (hlower x) (sq_nonneg ‖φ x‖)]
  have hbound₃ : (∫ x : Line, multiplierDerivative x * ‖φ x‖^2) ≤
      β/2 * (∫ x : Line, ‖φ x‖^2) + K * (∫ x : Line, ‖ψ x‖^2) := by
    rw [multiplier_ibp, ← integral_neg, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hv.const_mul (β/2)) (hd.const_mul K)]
    exact integral_mono hcross ((hv.const_mul (β/2)).add (hd.const_mul K)) hcross_le
  have hD : 0 ≤ (∫ x : Line, ‖ψ x‖^2) := integral_nonneg (fun _ => sq_nonneg _)
  have hW : 0 ≤ (∫ x : Line, p.toContinuousMap (x 0) * ‖φ x‖^2) :=
    integral_nonneg (fun x => mul_nonneg (p.nonneg _) (sq_nonneg _))
  dsimp only [C]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hβ).mpr
  change (∫ x : Line, ‖φ x‖^2) * β ≤ 2 * (K + 1) * ((∫ x : Line, ‖ψ x‖^2) + ∫ x : Line, p.toContinuousMap (x 0) * ‖φ x‖^2)
  nlinarith [mul_nonneg hK hW]

lemma l2_norm_sq_integral (f : L2 𝕜) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂lineMeasure := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma smooth_derivative_ae {p : Potential} (u : Space 𝕜 p)
    (φ : Tests 𝕜 (⊤ : Opens Line)) (hu : value u =ᵐ[lineMeasure] φ) :
    derivative u =ᵐ[lineMeasure] testPartialCLM [0] φ := by
  let h := sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1 (testToSobolev (p := 2) 1 φ)
  have hh : u.val.fst = h := by
    apply (sobolevToHilbert 𝕜 1 (⊤ : Opens Line) 1).symm.injective
    apply sobolev_underlying_injective 𝕜 1 (⊤ : Opens Line) 1 2
    apply Lp.ext
    exact hu.trans (testToDomainLp_coe φ).symm
  change h1Derivative u.val.fst =ᵐ[lineMeasure] _
  rw [hh]
  change testToDomainLp (testPartialCLM (multiIndexWord (natIndex firstIndex)).reverse φ) =ᵐ[lineMeasure] _
  rw [firstIndex_word]
  exact testToDomainLp_coe _

lemma smooth_value_estimate (p : Potential) (hp : PositiveAtInfinity p) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ SmoothMembers 𝕜 p,
      ‖value u‖^2 ≤ C * (‖derivative u‖^2 + ‖weighted u‖^2) := by
  obtain ⟨C, hC, hestimate⟩ := test_value_estimate_integral (𝕜 := 𝕜) p hp
  refine ⟨C, hC, ?_⟩
  rintro u ⟨φ, hu⟩
  have hd := smooth_derivative_ae u φ hu
  have hw := weighted_ae p u
  rw [l2_norm_sq_integral, l2_norm_sq_integral, l2_norm_sq_integral]
  have h₀ : (∫ x, ‖value u x‖^2 ∂lineMeasure) = ∫ x : Line, ‖φ x‖^2 := by
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    simpa only [lineMeasure, Opens.coe_top, Measure.restrict_univ, Function.comp_def] using hu.fun_comp (fun z => ‖z‖^2)
  have h₁ : (∫ x, ‖derivative u x‖^2 ∂lineMeasure) = ∫ x : Line, ‖testPartialCLM [0] φ x‖^2 := by
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    simpa only [lineMeasure, Opens.coe_top, Measure.restrict_univ, Function.comp_def] using hd.fun_comp (fun z => ‖z‖^2)
  have h₂ : (∫ x, ‖weighted u x‖^2 ∂lineMeasure) =
      ∫ x : Line, p.toContinuousMap (x 0) * ‖φ x‖^2 := by
    simp only [lineMeasure, Opens.coe_top, Measure.restrict_univ]
    apply integral_congr_ae
    have heq : ∀ᵐ x ∂lineMeasure, ‖weighted u x‖^2 = p.toContinuousMap (x 0) * ‖φ x‖^2 := by
      filter_upwards [hw, hu] with x hwx hux
      rw [hwx, hux, norm_mul, mul_pow]
      simp only [weight, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (p.nonneg _)]
    change (fun x => ‖weighted u x‖^2) =ᵐ[lineMeasure] (fun x => p.toContinuousMap (x 0) * ‖φ x‖^2) at heq
    simpa only [lineMeasure, Opens.coe_top, Measure.restrict_univ] using heq
  rw [h₀, h₁, h₂]
  exact hestimate φ

lemma coercivity_given_density (p : Potential) (hp : PositiveAtInfinity p)
    (hd : Dense (SmoothMembers 𝕜 p)) : ∃ α : ℝ, 0 < α ∧
      ∀ u : Space 𝕜 p, α * ‖u‖^2 ≤ RCLike.re (energyForm u u) := by
  obtain ⟨C, hC, hc⟩ := smooth_value_estimate (𝕜 := 𝕜) p hp
  refine ⟨1 / (C + 1), by positivity, coercivity_of_dense_smooth p hd ?_⟩
  intro u hu
  have he := hc u hu
  rw [weighted_norm_formula]
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by linarith : 0 < C+1)).mpr
  nlinarith


/-- Exterior positivity of the potential gives coercivity, with no confinement assumption. -/
theorem weighted_coercivity :
    Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.Coercivity := by
  intro 𝕜 _ p hp
  exact coercivity_given_density p hp (weighted_smooth_density 𝕜 p)

/-- The original variational equation has exactly one weighted energy solution. -/
theorem weighted_variational_solvability :
    Specs.ExpandedFA.Models.WeightedConfiningEnergySpace.VariationalSolvability := by
  intro 𝕜 _ p hp f
  obtain ⟨α, hα, hc⟩ := weighted_coercivity 𝕜 p hp
  exact variational_of_coercive p hα hc f

end ExpandedFA.Models.WeightedConfiningEnergySpace
