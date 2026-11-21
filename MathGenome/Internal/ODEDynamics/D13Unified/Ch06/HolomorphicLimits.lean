import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.HolomorphicLimits
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.TorusIntegral

namespace D13Unified.Ch06.HolomorphicLimits

open Filter Metric Set
open scoped Topology

/-- Compact convergence and the locally uniform convergence API agree here.
Finite dimensionality supplies local compactness, including dimension zero. -/
theorem compactUniformlyOn_iff {d n : ℕ} {V : Set (Fin d → ℂ)}
    {F : ℕ → (Fin d → ℂ) → Fin n → ℂ} {f : (Fin d → ℂ) → Fin n → ℂ}
    (hV : IsOpen V) :
    CompactUniformlyOn V F f ↔ TendstoLocallyUniformlyOn F f atTop V := by
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hV).symm

/-- Pullback along any continuous map preserves compact-uniform convergence.
Compact subsets are mapped to actual compact subsets inside `V`. -/
theorem compactUniformlyOn_comp {d n : ℕ} {V : Set (Fin d → ℂ)}
    {F : ℕ → (Fin d → ℂ) → Fin n → ℂ} {f : (Fin d → ℂ) → Fin n → ℂ}
    (h : CompactUniformlyOn V F f) {W : Set ℂ} (q : ℂ → Fin d → ℂ)
    (hq : Continuous q) (hqV : MapsTo q W V) :
    ∀ K : Set ℂ, K ⊆ W → IsCompact K →
      TendstoUniformlyOn (fun k => F k ∘ q) (f ∘ q) atTop K := by
  intro K hKW hK
  have hi := h (q '' K) (image_subset_iff.mpr (fun z hz => hqV (hKW hz)))
    (hK.image hq)
  exact (hi.comp q).mono (fun z hz => mem_preimage.mpr (mem_image_of_mem q hz))

/-- A vector-valued one-variable analytic limit. This uses Mathlib's theorem
only in its actual one-complex-dimensional source scope. -/
theorem analytic_limit_one_variable {n : ℕ} {W : Set ℂ}
    {F : ℕ → ℂ → Fin n → ℂ} {f : ℂ → Fin n → ℂ}
    (hW : IsOpen W) (hF : ∀ k, AnalyticOnNhd ℂ (F k) W)
    (hc : ∀ K : Set ℂ, K ⊆ W → IsCompact K → TendstoUniformlyOn F f atTop K) :
    AnalyticOnNhd ℂ f W := by
  have hl : TendstoLocallyUniformlyOn F f atTop W :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hW).mpr hc
  exact (hl.differentiableOn (Eventually.of_forall fun k => (hF k).differentiableOn)
    hW).analyticOnNhd hW

/-- A locally uniform limit of maps represented by formal analytic series is
continuous on the original open domain. -/
theorem continuous_limit {d n : ℕ} {V : Set (Fin d → ℂ)}
    {F : ℕ → (Fin d → ℂ) → Fin n → ℂ} {f : (Fin d → ℂ) → Fin n → ℂ}
    (hV : IsOpen V) (hF : ∀ k, AnalyticOnNhd ℂ (F k) V)
    (hc : CompactUniformlyOn V F f) : ContinuousOn f V := by
  exact ((compactUniformlyOn_iff hV).mp hc).continuousOn
    (Filter.Eventually.of_forall fun k => (hF k).continuousOn).frequently

/-- An affine complex line, also allowing the constant line `v = 0`. -/
def affineLine {d : ℕ} (a v : Fin d → ℂ) (z : ℂ) : Fin d → ℂ := a + z • v

lemma analyticAt_affineLine {d : ℕ} (a v : Fin d → ℂ) (z : ℂ) :
    AnalyticAt ℂ (affineLine a v) z := by
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)

lemma continuous_affineLine {d : ℕ} (a v : Fin d → ℂ) :
    Continuous (affineLine a v) := by
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- Every affine-line restriction of the limit is analytic on the exact
preimage of `V`; no assertion is made outside that preimage. -/
theorem analytic_limit_on_affineLine {d n : ℕ} {V : Set (Fin d → ℂ)}
    {F : ℕ → (Fin d → ℂ) → Fin n → ℂ} {f : (Fin d → ℂ) → Fin n → ℂ}
    (hV : IsOpen V) (hF : ∀ k, AnalyticOnNhd ℂ (F k) V)
    (hc : CompactUniformlyOn V F f) (a v : Fin d → ℂ) :
    AnalyticOnNhd ℂ (f ∘ affineLine a v) (affineLine a v ⁻¹' V) := by
  apply analytic_limit_one_variable (hV.preimage (continuous_affineLine a v))
  · intro k z hz
    exact (hF k _ hz).comp (analyticAt_affineLine a v z)
  · exact compactUniformlyOn_comp hc _ (continuous_affineLine a v) (fun _ hz => hz)

/-- The convergence hypothesis also holds for each target coordinate. -/
theorem compactUniformlyOn_component {d n : ℕ} {V : Set (Fin d → ℂ)}
    {F : ℕ → (Fin d → ℂ) → Fin n → ℂ} {f : (Fin d → ℂ) → Fin n → ℂ}
    (hc : CompactUniformlyOn V F f) (i : Fin n) (K : Set (Fin d → ℂ))
    (hKV : K ⊆ V) (hK : IsCompact K) :
    TendstoUniformlyOn (fun k z => F k z i) (fun z => f z i) atTop K := by
  exact (ContinuousLinearMap.proj (R := ℂ) i).uniformContinuous.comp_tendstoUniformlyOn
    (hc K hKV hK)

/-- Formal analytic representation of a finite-dimensional target is
componentwise, by the actual finite-pi power-series theorem in Mathlib. -/
theorem analyticOnNhd_componentwise {d n : ℕ} {V : Set (Fin d → ℂ)}
    {f : (Fin d → ℂ) → Fin n → ℂ} :
    AnalyticOnNhd ℂ f V ↔ ∀ i : Fin n, AnalyticOnNhd ℂ (fun z => f z i) V := by
  exact analyticOnNhd_pi_iff

/-- The zero-dimensional target is included, with no convergence assumption. -/
theorem coordinateHolomorphicOn_zero_target {d : ℕ} {V : Set (Fin d → ℂ)}
    (hV : IsOpen V) (f : (Fin d → ℂ) → Fin 0 → ℂ) :
    CoordinateHolomorphicOn V f := by
  intro a ha
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a ha
  exact ⟨r, hr, hball, fun i => Fin.elim0 i⟩

/-- With a zero-dimensional source every map is constant, so the full
coordinate-series conclusion holds without any convergence assumption. -/
theorem coordinateHolomorphicOn_zero_source {n : ℕ} {V : Set (Fin 0 → ℂ)}
    (hV : IsOpen V) (f : (Fin 0 → ℂ) → Fin n → ℂ) :
    CoordinateHolomorphicOn V f := by
  intro a ha
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a ha
  refine ⟨r, hr, hball, fun i => ⟨fun _ => f a i, ?_⟩⟩
  intro z hz
  have hza : z = a := Subsingleton.elim _ _
  subst z
  let : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun j : Fin 0 => j.elim0 : Fin 0 → ℕ)
  simp only [Fin.prod_univ_zero, mul_one]
  exact ⟨Summable.of_finite, by simp⟩

/-- Absolute convergence at one point with equal positive coordinate
increments gives a summable majorant throughout a smaller polydisc. -/
lemma coordinate_series_majorant {d : ℕ} (a : Fin d → ℂ) (r : ℝ)
    (c : (Fin d → ℕ) → ℂ) (hr : 0 < r)
    (hs : ∀ z ∈ ball a r,
      Summable (fun α => ‖c α * ∏ j : Fin d, (z j - a j) ^ α j‖)) :
    ∃ u : (Fin d → ℕ) → ℝ, Summable u ∧
      ∀ α z, z ∈ ball a (r / 2) →
        ‖c α * ∏ j : Fin d, (z j - a j) ^ α j‖ ≤ u α := by
  let q : Fin d → ℂ := fun j => a j + (r / 2 : ℝ)
  have hq : q ∈ ball a r := by
    rw [mem_ball_iff_norm]
    apply lt_of_le_of_lt _ (half_lt_self hr)
    apply (pi_norm_le_iff_of_nonneg (half_pos hr).le).mpr
    intro j
    simp [q, abs_of_pos hr]
  refine ⟨fun α => ‖c α * ∏ j : Fin d, (q j - a j) ^ α j‖, hs q hq, ?_⟩
  intro α z hz
  rw [mem_ball_iff_norm] at hz
  simp only [norm_mul, norm_prod, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
  intro j _
  have hj : ‖z j - a j‖ ≤ r / 2 :=
    (norm_le_pi_norm (z - a) j).trans hz.le
  simpa [q, abs_of_pos hr] using
    pow_le_pow_left₀ (norm_nonneg _) hj (α j)

/-- The monomials in a coordinate power series are genuine analytic
polynomials in the finite tuple of complex variables. -/
lemma analyticAt_coordinate_term {d : ℕ} (a : Fin d → ℂ)
    (c : (Fin d → ℕ) → ℂ) (α : Fin d → ℕ) (z : Fin d → ℂ) :
    AnalyticAt ℂ (fun w => c α * ∏ j : Fin d, (w j - a j) ^ α j) z := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro j _
  exact (((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z).sub analyticAt_const).pow _

/-- The absolute coordinate-series definition implies continuity, by the
summable majorant rather than by pointwise convergence alone. -/
theorem CoordinateHolomorphicOn.continuousOn {d n : ℕ} {V : Set (Fin d → ℂ)}
    {f : (Fin d → ℂ) → Fin n → ℂ} (hf : CoordinateHolomorphicOn V f) :
    ContinuousOn f V := by
  intro a ha
  obtain ⟨r, hr, _, hcomp⟩ := hf a ha
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro i
  obtain ⟨c, hc⟩ := hcomp i
  obtain ⟨u, hu, hub⟩ := coordinate_series_majorant a r c hr (fun z hz => (hc z hz).1)
  have hsmall : ball a (r / 2) ⊆ ball a r := ball_subset_ball (half_le_self hr.le)
  have ht : ContinuousOn (fun z => ∑' α, c α * ∏ j : Fin d, (z j - a j) ^ α j)
      (ball a (r / 2)) := by
    apply continuousOn_tsum _ hu hub
    intro α z _
    exact (analyticAt_coordinate_term a c α z).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun z => f z i) (ball a (r / 2)) :=
    ht.congr (fun z hz => (hc z (hsmall hz)).2.tsum_eq.symm)
  exact hfc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))

/-- Restriction of an absolutely convergent coordinate expansion to an
affine complex line is analytic. The proof uses normal convergence and
only the one-variable holomorphic-series theorem. -/
theorem CoordinateHolomorphicOn.analyticOnNhd_affineLine {d n : ℕ}
    {V : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → Fin n → ℂ}
    (hf : CoordinateHolomorphicOn V f) (a v : Fin d → ℂ) :
    AnalyticOnNhd ℂ (f ∘ affineLine a v) (affineLine a v ⁻¹' V) := by
  intro z hz
  obtain ⟨r, hr, _, hcomp⟩ := hf (affineLine a v z) hz
  apply AnalyticAt.pi
  intro i
  obtain ⟨c, hc⟩ := hcomp i
  obtain ⟨u, hu, hub⟩ := coordinate_series_majorant (affineLine a v z) r c hr
    (fun w hw => (hc w hw).1)
  let W := affineLine a v ⁻¹' ball (affineLine a v z) (r / 2)
  have hW : IsOpen W := isOpen_ball.preimage (continuous_affineLine a v)
  have hzW : z ∈ W := mem_ball_self (half_pos hr)
  have hdiff : DifferentiableOn ℂ
      (fun t => ∑' α, c α * ∏ j : Fin d,
        (affineLine a v t j - affineLine a v z j) ^ α j) W := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu ?_ hW ?_
    · intro α t _
      exact ((analyticAt_coordinate_term (affineLine a v z) c α (affineLine a v t)).comp
        (analyticAt_affineLine a v t)).differentiableAt.differentiableWithinAt
    · intro α t ht
      exact hub α _ ht
  apply (hdiff.analyticAt (hW.mem_nhds hzW)).congr
  filter_upwards [hW.mem_nhds hzW] with t ht
  exact (hc _ (ball_subset_ball (half_le_self hr.le) ht)).2.tsum_eq

/-- Continuity of the limit using the paper's coordinate-series hypothesis. -/
theorem continuous_coordinate_limit {d n : ℕ} {V : Set (Fin d → ℂ)}
    {F : ℕ → (Fin d → ℂ) → Fin n → ℂ} {f : (Fin d → ℂ) → Fin n → ℂ}
    (hV : IsOpen V) (hF : ∀ k, CoordinateHolomorphicOn V (F k))
    (hc : CompactUniformlyOn V F f) : ContinuousOn f V := by
  exact ((compactUniformlyOn_iff hV).mp hc).continuousOn
    (Eventually.of_forall fun k => (hF k).continuousOn).frequently

/-- Analyticity of the limit on every affine line, using the original
coordinate-series hypothesis for the approximating maps. -/
theorem coordinate_limit_on_affineLine {d n : ℕ} {V : Set (Fin d → ℂ)}
    {F : ℕ → (Fin d → ℂ) → Fin n → ℂ} {f : (Fin d → ℂ) → Fin n → ℂ}
    (hV : IsOpen V) (hF : ∀ k, CoordinateHolomorphicOn V (F k))
    (hc : CompactUniformlyOn V F f) (a v : Fin d → ℂ) :
    AnalyticOnNhd ℂ (f ∘ affineLine a v) (affineLine a v ⁻¹' V) := by
  apply analytic_limit_one_variable (hV.preimage (continuous_affineLine a v))
  · intro k
    exact (hF k).analyticOnNhd_affineLine a v
  · exact compactUniformlyOn_comp hc _ (continuous_affineLine a v) (fun _ hz => hz)

open MeasureTheory


lemma summable_norm_finPi_prod {R : Type*} [NormedCommRing R] (d : ℕ)
    (g : Fin d → ℕ → R) (hg : ∀ j, Summable (fun k => ‖g j k‖)) :
    Summable (fun α : Fin d → ℕ => ‖∏ j, g j (α j)‖) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)).summable_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ] using
      (hg 0).mul_norm (ih (fun j => g j.succ) (fun j => hg j.succ))

lemma hasSum_finPi_prod (d : ℕ) (g : Fin d → ℕ → ℂ) (s : Fin d → ℂ)
    (hg : ∀ j, Summable (fun k => ‖g j k‖)) (hs : ∀ j, HasSum (g j) (s j)) :
    HasSum (fun α : Fin d → ℕ => ∏ j, g j (α j)) (∏ j, s j) := by
  induction d with
  | zero =>
    let : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun j : Fin 0 => j.elim0 : Fin 0 → ℕ)
    simp
  | succ d ih =>
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ] using
      (hs 0).mul (ih (fun j => g j.succ) (fun j => s j.succ)
        (fun j => hg j.succ) (fun j => hs j.succ))
        (((hg 0).mul_norm (summable_norm_finPi_prod d (fun j => g j.succ)
          (fun j => hg j.succ))).of_norm)

lemma norm_torusMap_sub (d : ℕ) (a : Fin d → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin d → ℝ) (j : Fin d) :
    ‖torusMap a (fun _ => R) θ j - a j‖ = R := by
  simp [torusMap, abs_of_nonneg hR]

lemma torusMap_mem_closedBall {d : ℕ} (a : Fin d → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (θ : Fin d → ℝ) : torusMap a (fun _ => R) θ ∈ closedBall a R := by
  rw [mem_closedBall_iff_norm]
  exact (pi_norm_le_iff_of_nonneg hR).mpr (fun j => (norm_torusMap_sub d a hR θ j).le)

lemma torusMap_ne_of_mem_ball {d : ℕ} (a z : Fin d → ℂ) {R : ℝ} (hR : 0 < R)
    (hz : z ∈ ball a R) (θ : Fin d → ℝ) (j : Fin d) :
    torusMap a (fun _ => R) θ j ≠ z j := by
  intro heq
  have hj : ‖z j - a j‖ < R :=
    (norm_le_pi_norm (z - a) j).trans_lt (mem_ball_iff_norm.mp hz)
  rw [← heq, norm_torusMap_sub d a hR.le θ j] at hj
  exact hj.false

lemma torusIntegrable_cauchy {d : ℕ} {f : (Fin d → ℂ) → ℂ}
    {a z : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (closedBall a R)) (hz : z ∈ ball a R) :
    TorusIntegrable (fun w => f w / ∏ j, (w j - z j)) a (fun _ => R) := by
  have hT : Continuous (torusMap a (fun _ => R)) := by fun_prop [torusMap]
  have hn : Continuous (fun θ => f (torusMap a (fun _ => R) θ)) :=
    hf.comp_continuous hT (fun θ => torusMap_mem_closedBall a hR.le θ)
  have hd : Continuous (fun θ => ∏ j, (torusMap a (fun _ => R) θ j - z j)) := by
    fun_prop [torusMap]
  have hnz : ∀ θ, (∏ j, (torusMap a (fun _ => R) θ j - z j)) ≠ 0 := by
    intro θ
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr
      (torusMap_ne_of_mem_ball a z hR hz θ j))
  exact (hn.div hd hnz).continuousOn.integrableOn_Icc


/-- Product geometric expansion, indexed by all coordinate multiindices. -/
lemma hasSum_coordinate_geometric {d : ℕ} (q : Fin d → ℂ) (hq : ∀ j, ‖q j‖ < 1) :
    HasSum (fun α : Fin d → ℕ => ∏ j, q j ^ α j) (∏ j, (1 - q j)⁻¹) := by
  exact hasSum_finPi_prod d (fun j k => q j ^ k) (fun j => (1 - q j)⁻¹)
    (fun j => summable_norm_geometric_of_norm_lt_one (hq j))
    (fun j => hasSum_geometric_of_norm_lt_one (hq j))

lemma summable_coordinate_geometric {d : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun α : Fin d → ℕ => ∏ j, ρ ^ α j) := by
  have hg := summable_norm_geometric_of_norm_lt_one (R := ℝ)
    (show ‖ρ‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using hρ1)
  simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using
    summable_norm_finPi_prod d (fun _ k => ρ ^ k) (fun _ => hg)

/-- The Cauchy kernel expansion may be integrated term by term against a
bounded measurable density on any finite measure space. Both absolute
convergence and the actual sum identity are retained. -/
lemma integrated_coordinate_kernel {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (a z : Fin d → ℂ) {R : ℝ} (hR : 0 < R)
    (hz : z ∈ ball a R) (T : X → Fin d → ℂ)
    (hT : ∀ j, Measurable (fun θ => T θ j))
    (hTR : ∀ θ j, ‖T θ j - a j‖ = R)
    (b : X → ℂ) (hb : Measurable b) {M : ℝ} (hbM : ∀ θ, ‖b θ‖ ≤ M) :
    let c := fun α : Fin d → ℕ => ∫ θ, b θ * ∏ j, (T θ j - a j)⁻¹ ^ α j ∂μ
    Summable (fun α => ‖c α * ∏ j, (z j - a j) ^ α j‖) ∧
    HasSum (fun α => c α * ∏ j, (z j - a j) ^ α j)
      (∫ θ, b θ * ∏ j, ((T θ j - a j) / (T θ j - z j)) ∂μ) := by
  let ρ := ‖z - a‖ / R
  have hρ : 0 ≤ ρ := div_nonneg (norm_nonneg _) hR.le
  have hρ1 : ρ < 1 := (div_lt_one hR).mpr (mem_ball_iff_norm.mp hz)
  let u : (Fin d → ℕ) → ℝ := fun α => M * ∏ j, ρ ^ α j
  have hu : Summable u := (summable_coordinate_geometric (d := d) hρ hρ1).mul_left M
  let A := fun (α : Fin d → ℕ) θ => b θ * ∏ j, ((z j - a j) / (T θ j - a j)) ^ α j
  have hq : ∀ θ j, ‖(z j - a j) / (T θ j - a j)‖ ≤ ρ := by
    intro θ j
    rw [norm_div, hTR]
    exact div_le_div_of_nonneg_right (norm_le_pi_norm (z - a) j) hR.le
  have hA : ∀ α θ, ‖A α θ‖ ≤ u α := by
    intro α θ
    dsimp [A, u]
    rw [norm_mul, norm_prod]
    apply mul_le_mul (hbM θ) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      ((norm_nonneg _).trans (hbM θ))
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hq θ j) _
  have hAm : ∀ α, AEStronglyMeasurable (A α) μ := by
    intro α
    apply Measurable.aestronglyMeasurable
    exact hb.mul (Finset.measurable_prod _ fun j _ =>
      (measurable_const.div ((hT j).sub measurable_const)).pow_const _)
  have hAsum : ∀ θ, HasSum (fun α => A α θ)
      (b θ * ∏ j, (T θ j - a j) / (T θ j - z j)) := by
    intro θ
    have h := (hasSum_coordinate_geometric (fun j => (z j - a j) / (T θ j - a j))
      (fun j => (hq θ j).trans_lt hρ1)).mul_left (b θ)
    convert h using 1
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    have hne : T θ j - a j ≠ 0 := by
      intro he
      have := hTR θ j
      rw [he, norm_zero] at this
      exact hR.ne this
    field_simp
    ring
  have hI : HasSum (fun α => ∫ θ, A α θ ∂μ)
      (∫ θ, b θ * ∏ j, (T θ j - a j) / (T θ j - z j) ∂μ) := by
    apply hasSum_integral_of_dominated_convergence (fun α _ => u α) hAm
    · intro α
      exact ae_of_all _ (hA α)
    · exact ae_of_all _ (fun _ => hu)
    · exact integrable_const _
    · exact ae_of_all _ hAsum
  have hIabs : Summable (fun α => ‖∫ θ, A α θ ∂μ‖) := by
    apply (hu.mul_right (μ.real univ)).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro α
    exact norm_integral_le_of_norm_le_const (ae_of_all _ (hA α))
  have hterm : ∀ α, (∫ θ, A α θ ∂μ) =
      (∫ θ, b θ * ∏ j, (T θ j - a j)⁻¹ ^ α j ∂μ) * ∏ j, (z j - a j) ^ α j := by
    intro α
    rw [← integral_mul_const]
    congr 1
    funext θ
    dsimp [A]
    simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib]
    ring
  simpa only [hterm] using And.intro hIabs hI

lemma continuous_finCons {d : ℕ} (x : ℂ) :
    Continuous (fun y : Fin d → ℂ => Fin.cons (α := fun _ => ℂ) x y) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact continuous_const
  · exact continuous_apply k

set_option maxHeartbeats 800000 in
lemma finCons_mem_closedBall {d : ℕ} {a : Fin (d+1) → ℂ} {R : ℝ} (hR : 0 ≤ R)
    {x : ℂ} (hx : x ∈ closedBall (a 0) R) {y : Fin d → ℂ}
    (hy : y ∈ closedBall (fun j => a j.succ) R) : Fin.cons (α := fun _ => ℂ) x y ∈ closedBall a R := by
  rw [mem_closedBall_iff_norm, pi_norm_le_iff_of_nonneg hR]
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact mem_closedBall_iff_norm.mp hx
  · exact (norm_le_pi_norm (y - fun j => a j.succ) k).trans (mem_closedBall_iff_norm.mp hy)

lemma finCons_affineLine {d : ℕ} (x : ℂ) (a v : Fin d → ℂ) (t : ℂ) :
    Fin.cons (α := fun _ => ℂ) x (affineLine a v t) = affineLine (Fin.cons (α := fun _ => ℂ) x a) (Fin.cons (α := fun _ => ℂ) 0 v) t := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [affineLine]
  · rfl

/-- Iteration of the one-variable Cauchy formula over a closed polydisc. -/
lemma torus_cauchy_of_lineAnalytic (d : ℕ) {V : Set (Fin d → ℂ)}
    {f : (Fin d → ℂ) → ℂ} (hV : IsOpen V) (hf : ContinuousOn f V)
    (hl : ∀ a v, AnalyticOnNhd ℂ (f ∘ affineLine a v) (affineLine a v ⁻¹' V))
    (a : Fin d → ℂ) {R : ℝ} (hR : 0 < R) (hball : closedBall a R ⊆ V)
    (z : Fin d → ℂ) (hz : z ∈ ball a R) :
    torusIntegral (fun w => f w / ∏ j, (w j - z j)) a (fun _ => R) =
      (2 * Real.pi * Complex.I : ℂ) ^ d * f z := by
  induction d with
  | zero => simp [Subsingleton.elim z a]
  | succ d ih =>
    have hz0 : z 0 ∈ ball (a 0) R := by
      rw [mem_ball_iff_norm]
      exact (norm_le_pi_norm (z - a) 0).trans_lt (mem_ball_iff_norm.mp hz)
    have hzt : (fun j : Fin d => z j.succ) ∈ ball (fun j => a j.succ) R := by
      rw [mem_ball_iff_norm]
      apply lt_of_le_of_lt _ (mem_ball_iff_norm.mp hz)
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg (z-a))).mpr
      intro j
      exact norm_le_pi_norm (z-a) j.succ
    rw [torusIntegral_succ (torusIntegrable_cauchy hR (hf.mono hball) hz)]
    have hi : ∀ x ∈ sphere (a 0) R,
        torusIntegral (fun y : Fin d → ℂ => f (Fin.cons (α := fun _ => ℂ) x y) / ∏ j, (Fin.cons (α := fun _ => ℂ) x y j - z j))
          (a ∘ Fin.succ) ((fun _ => R) ∘ Fin.succ) =
          (x-z 0)⁻¹ * ((2 * Real.pi * Complex.I : ℂ)^d * f (Fin.cons (α := fun _ => ℂ) x (fun j => z j.succ))) := by
      intro x hx
      let q : (Fin d → ℂ) → (Fin (d+1) → ℂ) := fun y => Fin.cons (α := fun _ => ℂ) x y
      have hq : Continuous q := continuous_finCons x
      have hqline : ∀ b v : Fin d → ℂ,
          AnalyticOnNhd ℂ ((f ∘ q) ∘ affineLine b v) (affineLine b v ⁻¹' (q ⁻¹' V)) := by
        intro b v t ht
        have he : q ∘ affineLine b v = affineLine (Fin.cons (α := fun _ => ℂ) x b) (Fin.cons (α := fun _ => ℂ) 0 v) :=
          funext (finCons_affineLine x b v)
        change AnalyticAt ℂ (f ∘ (q ∘ affineLine b v)) t
        rw [he]
        apply hl
        change affineLine (Fin.cons (α := fun _ => ℂ) x b) (Fin.cons (α := fun _ => ℂ) 0 v) t ∈ V
        rw [← he]
        exact ht
      have hqb : closedBall (fun j => a j.succ) R ⊆ q ⁻¹' V := by
        intro y hy
        exact hball (finCons_mem_closedBall hR.le (sphere_subset_closedBall hx) hy)
      have hh := ih (hV.preimage hq) (hf.comp hq.continuousOn (fun _ hy => hy)) hqline
        (fun j => a j.succ) hqb (fun j => z j.succ) hzt
      have he : (fun y : Fin d → ℂ => f (Fin.cons (α := fun _ => ℂ) x y) / ∏ j, (Fin.cons (α := fun _ => ℂ) x y j - z j)) =
          (fun y : Fin d → ℂ => (x-z 0)⁻¹ * (f (Fin.cons (α := fun _ => ℂ) x y) / ∏ j : Fin d, (y j-z j.succ))) := by
        funext y
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, div_eq_mul_inv, mul_inv_rev]
        ring
      rw [he, torusIntegral_const_mul]
      exact congrArg ((x-z 0)⁻¹ * ·) hh
    rw [circleIntegral.integral_congr hR.le hi]
    simp_rw [mul_left_comm _ ((2 * Real.pi * Complex.I : ℂ)^d)]
    rw [circleIntegral.integral_const_mul]
    have hdiff : DifferentiableOn ℂ (fun x => f (Fin.cons (α := fun _ => ℂ) x (fun j => z j.succ)))
        (closedBall (a 0) R) := by
      intro x hx
      let b := Fin.cons (α := fun _ => ℂ) 0 (fun j : Fin d => z j.succ)
      let v := Fin.cons (α := fun _ => ℂ) 1 (fun _ : Fin d => (0 : ℂ))
      have he : (fun x => Fin.cons (α := fun _ => ℂ) x (fun j => z j.succ)) = affineLine b v := by
        funext t
        ext j
        refine Fin.cases ?_ (fun k => ?_) j <;> simp [affineLine, b, v]
      change DifferentiableWithinAt ℂ (f ∘ (fun x => Fin.cons (α := fun _ => ℂ) x (fun j => z j.succ))) _ x
      rw [he]
      apply (hl b v x ?_).differentiableAt.differentiableWithinAt
      rw [← he]
      exact hball (finCons_mem_closedBall hR.le hx (ball_subset_closedBall hzt))
    have hh := hdiff.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at hh
    rw [hh, pow_succ]
    have he : Fin.cons (α := fun _ => ℂ) (z 0) (fun j => z j.succ) = z := by
      ext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [he]
    ring

/-- An iterated Cauchy formula gives one coordinate expansion on the entire
open polydisc, with coefficients independent of its evaluation point. -/
lemma coordinate_series_of_torus_cauchy {d : ℕ} {f : (Fin d → ℂ) → ℂ}
    (a : Fin d → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (closedBall a R))
    (hC : ∀ z ∈ ball a R,
      torusIntegral (fun w => f w / ∏ j, (w j - z j)) a (fun _ => R) =
        (2 * Real.pi * Complex.I : ℂ)^d * f z) :
    ∃ c : (Fin d → ℕ) → ℂ, ∀ z ∈ ball a R,
      Summable (fun α => ‖c α * ∏ j, (z j-a j)^α j‖) ∧
      HasSum (fun α => c α * ∏ j, (z j-a j)^α j) (f z) := by
  let T := torusMap a (fun _ => R)
  let L : ℂ := ((2 * Real.pi * Complex.I : ℂ)^d)⁻¹
  let b : (Fin d → ℝ) → ℂ := fun θ => L * Complex.I^d * f (T θ)
  let μ : Measure (Fin d → ℝ) := volume.restrict (Icc 0 (fun _ => 2 * Real.pi))
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hT : Continuous T := by dsimp [T]; fun_prop [torusMap]
  have hfc : Continuous (fun θ => f (T θ)) :=
    hf.comp_continuous hT (fun θ => torusMap_mem_closedBall a hR.le θ)
  have hb : Continuous b := continuous_const.mul hfc
  obtain ⟨M, hM⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hf
  have hbM : ∀ θ, ‖b θ‖ ≤ ‖L‖ * M := by
    intro θ
    dsimp [b]
    simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left (hM _ (torusMap_mem_closedBall a hR.le θ)) (norm_nonneg L)
  refine ⟨fun α => ∫ θ, b θ * ∏ j, (T θ j - a j)⁻¹ ^ α j ∂μ, ?_⟩
  intro z hz
  have hh := integrated_coordinate_kernel μ a z hR hz T
    (fun j => (continuous_apply j |>.comp hT).measurable)
    (fun θ j => norm_torusMap_sub d a hR.le θ j) b hb.measurable hbM
  have hval : (∫ θ, b θ * ∏ j, (T θ j - a j) / (T θ j - z j) ∂μ) = f z := by
    calc
      _ = L * torusIntegral (fun w => f w / ∏ j, (w j-z j)) a (fun _ => R) := by
        rw [torusIntegral, ← integral_const_mul]
        apply integral_congr_ae
        apply ae_of_all
        intro θ
        have hj : (∏ j : Fin d, (R : ℂ) * Complex.exp (θ j * Complex.I) * Complex.I) =
            (∏ j, (T θ j-a j)) * Complex.I^d := by
          simp [T, torusMap, Finset.prod_mul_distrib]
        simp only [b, Finset.prod_div_distrib, smul_eq_mul, hj]
        ring
      _ = f z := by
        rw [hC z hz]
        have hn : (2 * Real.pi * Complex.I : ℂ)^d ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        exact inv_mul_cancel_left₀ hn _
  exact hval ▸ hh

/-- Several-variable bridge. Iterate the one-variable Cauchy
formula on a closed polydisc inside `V`, then integrate its absolutely
convergent geometric kernel expansion. Continuity
is retained explicitly, so a continuity-free Hartogs theorem is unnecessary. -/
theorem coordinateHolomorphicOn_of_continuous_lineAnalytic {d n : ℕ}
    {V : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → Fin n → ℂ} (hV : IsOpen V)
    (hc : ContinuousOn f V)
    (hl : ∀ a v : Fin d → ℂ,
      AnalyticOnNhd ℂ (f ∘ affineLine a v) (affineLine a v ⁻¹' V)) :
    CoordinateHolomorphicOn V f := by
  intro a ha
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV a ha
  have hsmall : closedBall a (r / 2) ⊆ V :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrV
  refine ⟨r / 2, half_pos hr, ball_subset_closedBall.trans hsmall, ?_⟩
  intro i
  have hfi : ContinuousOn (fun z => f z i) V :=
    (continuous_apply i).comp_continuousOn hc
  apply coordinate_series_of_torus_cauchy a (half_pos hr) (hfi.mono hsmall)
  intro z hz
  apply torus_cauchy_of_lineAnalytic d hV hfi _ a (half_pos hr) hsmall z hz
  intro b v
  exact (analyticOnNhd_pi_iff.mp (hl b v)) i

/-- The full statement in paper.tex, d13:06:polydisc-limit, with arbitrary
finite source and target dimensions and literal absolute coordinate series. -/
theorem holomorphic_limit :
    Specs.D13Unified.Ch06.HolomorphicLimits.holomorphic_limit_type := by
  intro d n V F f hV hF hc
  exact coordinateHolomorphicOn_of_continuous_lineAnalytic hV
    (continuous_coordinate_limit hV hF hc) (coordinate_limit_on_affineLine hV hF hc)

end D13Unified.Ch06.HolomorphicLimits
