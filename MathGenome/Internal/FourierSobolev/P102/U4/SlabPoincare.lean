import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SlabPoincare
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.LIntegral

noncomputable section
set_option maxHeartbeats 800000
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal InnerProductSpace Topology
namespace P102.U4

open SlabPoincareData
namespace SlabPoincareProof

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bundled gradient has the expected coordinate representative. -/
theorem sobolevGradient_ae (u : Sobolev 𝕜 Ω 1 p) :
    (sobolevGradient u : Space d → EuclideanSpace 𝕜 (Fin d)) =ᵐ[
      volume.restrict (Ω : Set (Space d))] sobolevGradientRepresentative u :=
  MemLp.coeFn_toLp _

/-- Coordinate derivatives are continuous linear projections of the canonical tuple. -/
def sobolevFirstDerivativeCLM (j : Fin d) : Sobolev 𝕜 Ω 1 p →L[𝕜] DomainLp 𝕜 Ω p :=
  (PiLp.proj 1 _ (firstSobolevIndex j)).comp (sobolevSubmodule 𝕜 Ω 1 p).subtypeL

/-- The directional derivative is a finite linear combination of weak derivatives. -/
def sobolevDirectionalDerivativeCLM (e : Space d) :
    Sobolev 𝕜 Ω 1 p →L[𝕜] DomainLp 𝕜 Ω p :=
  ∑ j : Fin d, (RCLike.ofReal (e j) : 𝕜) • sobolevFirstDerivativeCLM j

@[simp] theorem sobolevDirectionalDerivativeCLM_apply (e : Space d)
    (u : Sobolev 𝕜 Ω 1 p) :
    sobolevDirectionalDerivativeCLM e u = sobolevDirectionalDerivative u e := by
  simp [sobolevDirectionalDerivativeCLM, sobolevDirectionalDerivative,
    sobolevFirstDerivativeCLM, sobolevFirstDerivative, sobolevDerivative]

/-- The directional representative is the coordinate sum, on the restricted measure. -/
theorem sobolevDirectionalDerivative_ae (u : Sobolev 𝕜 Ω 1 p) (e : Space d) :
    (sobolevDirectionalDerivative u e : Space d → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space d))]
      fun x => ∑ j : Fin d, (RCLike.ofReal (e j) : 𝕜) * sobolevFirstDerivative u j x := by
  unfold sobolevDirectionalDerivative
  exact (Lp.coeFn_finsetSum _ _).trans
    ((eventuallyEq_sum (fun j _ => Lp.coeFn_smul (RCLike.ofReal (e j))
      (sobolevFirstDerivative u j))).trans (Filter.Eventually.of_forall (fun _ => by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul])))

/-- Extending a real vector to the scalar field preserves its Euclidean length. -/
theorem norm_euclidean_ofReal (e : Space d) :
    ‖(WithLp.toLp 2 (fun j => (RCLike.ofReal (e j) : 𝕜)) : EuclideanSpace 𝕜 (Fin d))‖ = ‖e‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [RCLike.norm_ofReal, Real.norm_eq_abs]

/-- Pointwise Cauchy--Schwarz for a real direction and a real or complex gradient. -/
theorem norm_directional_sum_le (e : Space d) (v : EuclideanSpace 𝕜 (Fin d)) :
    ‖∑ j : Fin d, (RCLike.ofReal (e j) : 𝕜) * v j‖ ≤ ‖e‖ * ‖v‖ := by
  have h := norm_inner_le_norm (𝕜 := 𝕜)
    (WithLp.toLp 2 (fun j => (RCLike.ofReal (e j) : 𝕜)) : EuclideanSpace 𝕜 (Fin d)) v
  simpa only [PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply,
    RCLike.conj_ofReal, mul_comm, norm_euclidean_ofReal] using h

/-- Unit-direction weak derivatives are bounded by the Euclidean gradient. -/
theorem sobolevDirectionalDerivative_norm_le (u : Sobolev 𝕜 Ω 1 p)
    (e : Space d) (he : ‖e‖ = 1) :
    ‖sobolevDirectionalDerivative u e‖ ≤ ‖sobolevGradient u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sobolevDirectionalDerivative_ae u e, sobolevGradient_ae u] with x hx hg
  rw [hx, hg]
  simpa only [he, one_mul, sobolevGradientRepresentative, PiLp.toLp_apply] using norm_directional_sum_le e (sobolevGradientRepresentative u x)

/-- Every coordinate is bounded by the Euclidean gradient, at all exponents. -/
theorem sobolevFirstDerivative_norm_le_gradient (u : Sobolev 𝕜 Ω 1 p) (j : Fin d) :
    ‖sobolevFirstDerivative u j‖ ≤ ‖sobolevGradient u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sobolevGradient_ae u] with x hx
  rw [hx]
  exact PiLp.norm_apply_le (sobolevGradientRepresentative u x) j

/-- A single-coordinate Euclidean inclusion. -/
def euclideanSingleCLM (j : Fin d) : 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  LinearMap.mkContinuous
    { toFun := fun c : 𝕜 => (PiLp.single 2 j c : EuclideanSpace 𝕜 (Fin d))
      map_add' _ _ := PiLp.single_add 2 j
      map_smul' c x := by
        apply PiLp.ext
        intro i
        by_cases hi : i = j <;> simp [hi] }
    1 (fun x => by simp)

@[simp] theorem euclideanSingleCLM_norm (j : Fin d) (c : 𝕜) :
    ‖euclideanSingleCLM (𝕜 := 𝕜) j c‖ = ‖c‖ := by
  change ‖(PiLp.single 2 j c : EuclideanSpace 𝕜 (Fin d))‖ = ‖c‖
  exact PiLp.norm_single 2 (fun _ : Fin d => 𝕜) j c

/-- The gradient is the finite sum of the lifted coordinate Lp classes. -/
theorem sobolevGradient_eq_sum (u : Sobolev 𝕜 Ω 1 p) :
    sobolevGradient u = ∑ j : Fin d, (euclideanSingleCLM (𝕜 := 𝕜) j).compLp (sobolevFirstDerivative u j) := by
  apply Lp.ext
  have hc := eventuallyEq_sum (s := Finset.univ) (fun j _ =>
    (euclideanSingleCLM (𝕜 := 𝕜) j).coeFn_compLp (sobolevFirstDerivative u j))
  filter_upwards [sobolevGradient_ae u, Lp.coeFn_finsetSum Finset.univ
    (fun j : Fin d => (euclideanSingleCLM (𝕜 := 𝕜) j).compLp (sobolevFirstDerivative u j)), hc]
    with x hx hs hc
  rw [hx, hs, hc]
  apply PiLp.ext
  intro i
  simp [sobolevGradientRepresentative, euclideanSingleCLM]

omit [Fact (1 ≤ p)] in
/-- The Lp norm of a single-coordinate lift is unchanged. -/
theorem norm_euclideanSingle_compLp (j : Fin d) (f : DomainLp 𝕜 Ω p) :
    ‖(euclideanSingleCLM (𝕜 := 𝕜) j).compLp f‖ = ‖f‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(euclideanSingleCLM (𝕜 := 𝕜) j).coeFn_compLp f] with x hx
    simp only [hx, euclideanSingleCLM_norm, le_refl]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(euclideanSingleCLM (𝕜 := 𝕜) j).coeFn_compLp f] with x hx
    simp only [hx, euclideanSingleCLM_norm, le_refl]

/-- Minkowski for the finite coordinate decomposition of the gradient. -/
theorem sobolevGradient_norm_le_sum (u : Sobolev 𝕜 Ω 1 p) :
    ‖sobolevGradient u‖ ≤ ∑ j : Fin d, ‖sobolevFirstDerivative u j‖ := by
  rw [sobolevGradient_eq_sum]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun j _ =>
    norm_euclideanSingle_compLp j _))

/-- Order at most one means either the zeroth multi-index or exactly one coordinate. -/
def firstOrderIndexEquiv : Option (Fin d) ≃ SobolevIndex d 1 := by
  let f : Option (Fin d) → SobolevIndex d 1 := fun o =>
    match o with
    | none => zeroSobolevIndex d 1
    | some j => firstSobolevIndex j
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    cases a <;> cases b
    · rfl
    · have hv := congrArg (fun α : SobolevIndex d 1 => α.val.card) h
      simp [f, firstSobolevIndex, zeroSobolevIndex] at hv
    · have hv := congrArg (fun α : SobolevIndex d 1 => α.val.card) h
      simp [f, firstSobolevIndex, zeroSobolevIndex] at hv
    · apply congrArg some
      simpa [f, firstSobolevIndex] using congrArg Subtype.val h
  · intro α
    by_cases hz : α.val = 0
    · exact ⟨none, Subtype.ext hz.symm⟩
    · have hn : α.val.card ≠ 0 := fun h => hz (Multiset.card_eq_zero.mp h)
      have hle : α.val.card ≤ 1 := α.property
      have hcard : α.val.card = 1 := by omega
      obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hcard
      exact ⟨some j, Subtype.ext hj.symm⟩

/-- In order one the source's sum norm has one zeroth-order and d first-order terms. -/
theorem sobolev_one_norm (u : Sobolev 𝕜 Ω 1 p) :
    ‖u‖ = ‖sobolevUnderlying u‖ + ∑ j : Fin d, ‖sobolevFirstDerivative u j‖ := by
  rw [sobolev_norm Ω 1 p, ← (firstOrderIndexEquiv (d := d)).sum_comp]
  rw [Fintype.sum_option]
  rfl

/-- One side of norm equivalence does not require a slab or zero boundary values. -/
theorem sobolevGradient_norm_le (u : Sobolev 𝕜 Ω 1 p) : ‖sobolevGradient u‖ ≤ ‖u‖ := by
  rw [sobolev_one_norm]
  exact (sobolevGradient_norm_le_sum u).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- The Euclidean gradient is a linear map of Lp classes. -/
def sobolevGradientLM : Sobolev 𝕜 Ω 1 p →ₗ[𝕜]
    Lp (EuclideanSpace 𝕜 (Fin d)) p (volume.restrict (Ω : Set (Space d))) :=
  ∑ j : Fin d, ((euclideanSingleCLM (𝕜 := 𝕜) j).compLpₗ p
    (volume.restrict (Ω : Set (Space d)))).comp (sobolevFirstDerivativeCLM j).toLinearMap

@[simp] theorem sobolevGradientLM_apply (u : Sobolev 𝕜 Ω 1 p) :
    sobolevGradientLM u = sobolevGradient u := by
  simpa [sobolevGradientLM, sobolevFirstDerivativeCLM, sobolevFirstDerivative,
    sobolevDerivative] using (sobolevGradient_eq_sum u).symm

/-- The gradient is continuous for the full Sobolev norm. -/
def sobolevGradientCLM : Sobolev 𝕜 Ω 1 p →L[𝕜]
    Lp (EuclideanSpace 𝕜 (Fin d)) p (volume.restrict (Ω : Set (Space d))) :=
  (sobolevGradientLM (𝕜 := 𝕜) (Ω := Ω) (p := p)).mkContinuous 1
    (fun u => by simpa using sobolevGradient_norm_le u)

@[simp] theorem sobolevGradientCLM_apply (u : Sobolev 𝕜 Ω 1 p) :
    sobolevGradientCLM u = sobolevGradient u := sobolevGradientLM_apply u

/-- Completeness of W₀ for the full Sobolev norm follows from its definition as a closure. -/
instance sobolevZeroCompleteSpace {m : ℕ} : CompleteSpace (SobolevZero 𝕜 Ω m p) :=
  (smoothSobolevSubmodule 𝕜 Ω m p).isClosed_topologicalClosure.completeSpace_coe

/-- All coordinate derivative norms can be controlled by a single gradient norm. -/
theorem sum_sobolevFirstDerivative_norm_le (u : Sobolev 𝕜 Ω 1 p) :
    (∑ j : Fin d, ‖sobolevFirstDerivative u j‖) ≤ (d : ℝ) * ‖sobolevGradient u‖ := by
  calc
    _ ≤ ∑ _ : Fin d, ‖sobolevGradient u‖ :=
      Finset.sum_le_sum (fun j _ => sobolevFirstDerivative_norm_le_gradient u j)
    _ = _ := by simp

/-- Functional-analytic consequence of the exact directional estimate. -/
theorem sobolev_norm_le_of_directional_bound (u : Sobolev 𝕜 Ω 1 p)
    (e : Space d) (he : ‖e‖ = 1) {w : ℝ} (hw : 0 ≤ w)
    (hu : ‖sobolevUnderlying u‖ ≤ w * ‖sobolevDirectionalDerivative u e‖) :
    ‖u‖ ≤ (w + (d : ℝ)) * ‖sobolevGradient u‖ := by
  rw [sobolev_one_norm, add_mul]
  exact add_le_add (hu.trans (mul_le_mul_of_nonneg_left
    (sobolevDirectionalDerivative_norm_le u e he) hw))
    (sum_sobolevFirstDerivative_norm_le u)

/-- The source integral is precisely the reversed Mathlib L² inner product. -/
theorem sobolevGradientPairing_eq_inner (u v : SobolevZero 𝕜 Ω 1 2) :
    sobolevGradientPairing u v = inner 𝕜 (sobolevGradient v.val) (sobolevGradient u.val) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sobolevGradient_ae u.val, sobolevGradient_ae v.val] with x hu hv
  simp only [hu, hv, PiLp.inner_apply, RCLike.inner_apply,
    sobolevGradientRepresentative]
  rfl

/-- The gradient defines a Hilbert norm whenever it controls the inherited norm.
This lemma has no geometric assumptions: the slab estimate supplies its one bound. -/
theorem sobolevZero_hilbert_of_bound {C : ℝ≥0}
    (hb : ∀ u : SobolevZero 𝕜 Ω 1 2, ‖u‖ ≤ (C : ℝ) * ‖sobolevGradient u.val‖) :
    ∃ (N : NormedAddCommGroup (SobolevZero 𝕜 Ω 1 2))
      (I : @InnerProductSpace 𝕜 (SobolevZero 𝕜 Ω 1 2) _ N.toSeminormedAddCommGroup),
      N.toAddCommGroup = (inferInstance : AddCommGroup (SobolevZero 𝕜 Ω 1 2)) ∧
      (∀ (c : 𝕜) (u : SobolevZero 𝕜 Ω 1 2), @SMul.smul _ _ I.toSMul c u = c • u) ∧
      @CompleteSpace (SobolevZero 𝕜 Ω 1 2) N.toUniformSpace ∧
      N.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (SobolevZero 𝕜 Ω 1 2)) ∧
      (∀ u, @norm _ N.toNorm u = ‖sobolevGradient u.val‖) ∧
      (∀ u v, @inner 𝕜 _ I.toInner v u = sobolevGradientPairing u v) := by
  let G : SobolevZero 𝕜 Ω 1 2 →L[𝕜]
      Lp (EuclideanSpace 𝕜 (Fin d)) 2 (volume.restrict (Ω : Set (Space d))) :=
    (sobolevGradientCLM (𝕜 := 𝕜) (Ω := Ω) (p := 2)).comp
      (sobolevZeroSubmodule 𝕜 Ω 1 2).subtypeL
  have hG (u : SobolevZero 𝕜 Ω 1 2) : G u = sobolevGradient u.val :=
    sobolevGradientCLM_apply u.val
  have hanti : AntilipschitzWith C G := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    rw [dist_eq_norm, dist_eq_norm, ← map_sub G]
    exact (hb (u - v)).trans_eq (congrArg (fun z => (C : ℝ) * ‖z‖) (hG (u - v)).symm)
  have hinj : Function.Injective G := hanti.injective
  let N := NormedAddCommGroup.induced _ _ G hinj
  let I : @InnerProductSpace 𝕜 (SobolevZero 𝕜 Ω 1 2) _ N.toSeminormedAddCommGroup :=
    InnerProductSpace.induced G.toLinearMap
  have hU : N.toUniformSpace = (inferInstance : UniformSpace (SobolevZero 𝕜 Ω 1 2)) :=
    (hanti.isUniformInducing G.uniformContinuous).comap_uniformSpace
  have hc : @CompleteSpace (SobolevZero 𝕜 Ω 1 2) N.toUniformSpace := by
    rw [hU]
    infer_instance
  refine ⟨N, I, rfl, (fun _ _ => rfl), hc,
    congrArg (fun U : UniformSpace (SobolevZero 𝕜 Ω 1 2) => U.toTopologicalSpace) hU, ?_, ?_⟩
  · intro u
    change ‖G u‖ = ‖sobolevGradient u.val‖
    rw [hG]
  · intro u v
    change inner 𝕜 (G v) (G u) = _
    rw [hG, hG, sobolevGradientPairing_eq_inner]

/-- The full Sobolev norm estimate gives the claimed gradient Hilbert space. -/
theorem slab_hilbert_of_inequality (h : SlabPoincareExpected.Inequality) :
    SlabPoincareExpected.Hilbert := by
  intro d hd 𝕜 _ Ω e a b he hab hΩ
  let C : ℝ≥0 := ⟨b - a + (d : ℝ), by positivity⟩
  apply sobolevZero_hilbert_of_bound (C := C)
  intro u
  exact sobolev_norm_le_of_directional_bound u.val e he (sub_nonneg.mpr hab.le)
    (h hd Ω 2 (by norm_num) e a b he hab hΩ u).1

/-- The quantitative norm comparison follows from the directional inequality. -/
theorem slab_normEquivalence_of_inequality (h : SlabPoincareExpected.Inequality) :
    SlabPoincareExpected.NormEquivalence := by
  intro d hd 𝕜 _ Ω p _ hp e a b he hab hΩ u
  exact ⟨sobolevGradient_norm_le u.val,
    sobolev_norm_le_of_directional_bound u.val e he (sub_nonneg.mpr hab.le)
      (h hd Ω p hp e a b he hab hΩ u).1⟩

lemma lintegral_enorm_rpow_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E}
    (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ t, ‖f t‖ₑ ∂μ) ^ q ≤ μ univ ^ (q - 1) * ∫⁻ t, ‖f t‖ₑ ^ q ∂μ := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ zero_lt_one hq hf
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm] at h
  simp only [ENNReal.rpow_one, div_one] at h
  have h' := ENNReal.rpow_le_rpow h hqpos.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hqpos.ne', ENNReal.rpow_one] at h'
  have he : (1 - 1 / q) * q = q - 1 := by field_simp
  simpa only [he, mul_comm] using h'
lemma eLpNorm_le_translation_integral {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f g : Space d → 𝕜} (hf : AEStronglyMeasurable f volume) (hg : Continuous g)
    (e : Space d) {w : ℝ} (hw : 0 < w) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (h : ∀ x, ‖f x‖ₑ ≤ ∫⁻ t in Ioc 0 w, ‖g (x + t • e)‖ₑ) :
    eLpNorm f p volume ≤ ENNReal.ofReal w * eLpNorm g p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by exact_mod_cast (ENNReal.toReal_mono hpt hp)
  have hqp : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hq
  let c := ENNReal.ofReal w
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hw
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hmass : (volume.restrict (Ioc 0 w)) univ = c := by simp [c]
  have hpow (x : Space d) :
      ‖f x‖ₑ ^ p.toReal ≤ c ^ (p.toReal - 1) *
        ∫⁻ t in Ioc 0 w, ‖g (x + t • e)‖ₑ ^ p.toReal := by
    have hline : AEStronglyMeasurable (fun t : ℝ => g (x + t • e))
        (volume.restrict (Ioc 0 w)) :=
      (hg.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable
    exact (ENNReal.rpow_le_rpow (h x) hqp.le).trans (by
      simpa only [hmass] using lintegral_enorm_rpow_bound hline hq)
  have hswap :
      (∫⁻ x, ∫⁻ t in Ioc 0 w, ‖g (x + t • e)‖ₑ ^ p.toReal) =
        c * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
    calc
      _ = ∫⁻ t in Ioc 0 w, ∫⁻ x, ‖g (x + t • e)‖ₑ ^ p.toReal :=
        lintegral_lintegral_swap
          ((hg.comp (continuous_fst.add (continuous_snd.smul continuous_const))).enorm.measurable.pow_const _).aemeasurable
      _ = ∫⁻ _t in Ioc 0 w, ∫⁻ x, ‖g x‖ₑ ^ p.toReal :=
        lintegral_congr (fun t => lintegral_add_right_eq_self
          (fun x : Space d => ‖g x‖ₑ ^ p.toReal) (t • e))
      _ = _ := by rw [lintegral_const, hmass, mul_comm]
  have hpowint : (∫⁻ x, ‖f x‖ₑ ^ p.toReal) ≤ c ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
    calc
      _ ≤ ∫⁻ x, c ^ (p.toReal - 1) * ∫⁻ t in Ioc 0 w,
          ‖g (x + t • e)‖ₑ ^ p.toReal := lintegral_mono hpow
      _ = c ^ (p.toReal - 1) * (c * ∫⁻ x, ‖g x‖ₑ ^ p.toReal) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc0 hct), hswap]
      _ = (c ^ (p.toReal - 1) * c ^ (1 : ℝ)) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
        simp only [ENNReal.rpow_one, mul_assoc]
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ hc0 hct, sub_add_cancel]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hg.aestronglyMeasurable]
  have hh := ENNReal.rpow_le_rpow hpowint (by positivity : 0 ≤ 1 / p.toReal)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p.toReal),
    ← ENNReal.rpow_mul, mul_one_div_cancel hqp.ne', ENNReal.rpow_one] using hh

lemma slab_pointwise_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ 1 f) (e : Space d) {a b : ℝ}
    (he : ‖e‖ = 1) (hab : a < b)
    (hslab : ∀ x, f x ≠ 0 → a < inner ℝ x e ∧ inner ℝ x e < b) (x : Space d) :
    ‖f x‖ₑ ≤ ∫⁻ t in Ioc 0 (b - a), ‖fderiv ℝ f (x + t • e) e‖ₑ := by
  by_cases hx : f x = 0
  · simp only [hx, enorm_zero, zero_le]
  have hstop : f (x + (b - a) • e) = 0 := by
    by_contra h
    have h0 := (hslab x hx).1
    have h1 := (hslab _ h).2
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, he] at h1
    norm_num at h1
    linarith
  have hg : Continuous (fun t : ℝ => fderiv ℝ f (x + t • e) e) :=
    ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hder (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • e))
      (fderiv ℝ f (x + t • e) e) t := by
    convert ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const e).const_add x)) using 1 <;> simp [Function.comp_def]
  have hid : (∫ t in (0 : ℝ)..(b - a), fderiv ℝ f (x + t • e) e) = -f x := by
    simpa only [hstop, zero_smul, add_zero, zero_sub] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hg.intervalIntegrable 0 (b - a))
  calc
    ‖f x‖ₑ = ‖∫ t in (0 : ℝ)..(b - a), fderiv ℝ f (x + t • e) e‖ₑ := by rw [hid, enorm_neg]
    _ = ‖∫ t in Ioc 0 (b - a), fderiv ℝ f (x + t • e) e‖ₑ := by
      rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hab.le)]
    _ ≤ _ := enorm_integral_le_lintegral_enorm _

lemma smooth_sobolev_firstDerivative (u : Sobolev 𝕜 Ω 1 p) (φ : TestSpace 𝕜 Ω)
    (hu : sobolevUnderlying u = testToDomainLp Ω p φ) (j : Fin d) :
    sobolevFirstDerivative u j = testToDomainLp Ω p (testPartialWord Ω [j] φ) := by
  symm
  apply sobolev_derivative_unique Ω 1 p u (firstSobolevIndex j)
  change distributionPartial ({j} : MultiIndex d) (regularDistribution Ω (sobolevUnderlying u)) = _
  rw [hu, regular_testToDomainLp, regular_testToDomainLp]
  rw [derivative_classicalCompatibility d 𝕜 Ω {j} φ
    (φ.contDiff.of_le (by simp)).contDiffOn]
  congr 1
  simp [multiPartial, testPartialWord_coe]

lemma fderiv_apply_eq_coordinate_sum (L : Space d →L[ℝ] 𝕜) (e : Space d) :
    L e = ∑ j : Fin d, (RCLike.ofReal (e j) : 𝕜) * L (coordinateVector d j) := by
  have he : (∑ j : Fin d, e j • coordinateVector d j) = e :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr e
  calc
    L e = L (∑ j : Fin d, e j • coordinateVector d j) := congrArg L he.symm
    _ = _ := by simp only [map_sum, map_smul, RCLike.real_smul_eq_coe_mul]

lemma smooth_sobolev_directional_ae (u : Sobolev 𝕜 Ω 1 p) (φ : TestSpace 𝕜 Ω)
    (hu : sobolevUnderlying u = testToDomainLp Ω p φ) (e : Space d) :
    (sobolevDirectionalDerivative u e : Space d → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space d))] fun x => fderiv ℝ φ x e := by
  have hj (j : Fin d) : (sobolevFirstDerivative u j : Space d → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space d))] fun x => fderiv ℝ φ x (coordinateVector d j) := by
    rw [smooth_sobolev_firstDerivative u φ hu]
    simpa only [testPartialWord_coe, partialWord] using testToDomainLp_ae Ω p (testPartialWord Ω [j] φ)
  have hall := ae_all_iff.mpr hj
  filter_upwards [sobolevDirectionalDerivative_ae u e, hall] with x hx hcoord
  rw [hx, fderiv_apply_eq_coordinate_sum]
  exact Finset.sum_congr rfl (fun j _ => congrArg ((RCLike.ofReal (e j) : 𝕜) * ·) (hcoord j))

/-- The exact slab-width estimate for smooth Sobolev classes, identified through their
actual weak derivatives and ambient smooth representatives. -/
theorem smooth_slab_poincare (hp : p ≠ ∞) (e : Space d) {a b : ℝ}
    (he : ‖e‖ = 1) (hab : a < b) (hΩ : InSlab Ω e a b)
    (u : Sobolev 𝕜 Ω 1 p) (φ : TestSpace 𝕜 Ω)
    (hu : sobolevUnderlying u = testToDomainLp Ω p φ) :
    ‖sobolevUnderlying u‖ ≤ (b - a) * ‖sobolevDirectionalDerivative u e‖ := by
  have hf : ContDiff ℝ 1 (φ : Space d → 𝕜) := φ.contDiff.of_le (by simp)
  let g : Space d → 𝕜 := fun x => fderiv ℝ φ x e
  have hg : Continuous g := (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsφ : Function.support (φ : Space d → 𝕜) ⊆ Ω :=
    subset_tsupport _ |>.trans φ.tsupport_subset
  have hsg : Function.support g ⊆ Ω :=
    (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ e).trans φ.tsupport_subset)
  have hraw := eLpNorm_le_translation_integral φ.continuous.aestronglyMeasurable hg e
    (sub_pos.mpr hab) (Fact.out : 1 ≤ p) hp
    (slab_pointwise_bound hf e he hab (fun x hx => hΩ x (hsφ hx)))
  have hrestricted : eLpNorm φ p (volume.restrict (Ω : Set (Space d))) ≤
      ENNReal.ofReal (b - a) * eLpNorm g p (volume.restrict (Ω : Set (Space d))) := by
    rwa [eLpNorm_restrict_eq_of_support_subset φ.continuous.aestronglyMeasurable hsφ,
      eLpNorm_restrict_eq_of_support_subset hg.aestronglyMeasurable hsg]
  have hclass : eLpNorm (sobolevUnderlying u) p (volume.restrict (Ω : Set (Space d))) ≤
      ENNReal.ofReal (b - a) * eLpNorm (sobolevDirectionalDerivative u e) p
        (volume.restrict (Ω : Set (Space d))) := by
    rw [eLpNorm_congr_ae (smooth_sobolev_directional_ae u φ hu e), hu,
      eLpNorm_congr_ae (testToDomainLp_ae Ω p φ)]
    exact hrestricted
  have hr := ENNReal.toReal_mono (by finiteness) hclass
  simpa only [Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] using hr

end SlabPoincareProof

open SlabPoincareProof

/-- Pass the smooth estimate to the norm closure defining W₀. -/
theorem slab_poincare : SlabPoincareExpected.Inequality := by
  intro d hd 𝕜 _ Ω p _ hp e a b he hab hΩ u
  refine ⟨?_, mul_le_mul_of_nonneg_left
    (sobolevDirectionalDerivative_norm_le u.val e he) (sub_nonneg.mpr hab.le)⟩
  let S : Set (Sobolev 𝕜 Ω 1 p) :=
    {v | ‖sobolevUnderlying v‖ ≤ (b - a) * ‖sobolevDirectionalDerivative v e‖}
  have hdcont : Continuous (fun v : Sobolev 𝕜 Ω 1 p => sobolevDirectionalDerivative v e) := by
    exact (sobolevDirectionalDerivativeCLM (𝕜 := 𝕜) (Ω := Ω) (p := p) e).continuous.congr
      (fun v => sobolevDirectionalDerivativeCLM_apply e v)
  have hc : IsClosed S := isClosed_le
    (sobolevUnderlyingCLM Ω 1 p).continuous.norm (continuous_const.mul hdcont.norm)
  have hs : (smoothSobolevSubmodule 𝕜 Ω 1 p : Set (Sobolev 𝕜 Ω 1 p)) ⊆ S := by
    intro v hv
    change ∃ φ, testToDomainLp Ω p φ = sobolevUnderlying v at hv
    obtain ⟨φ, hφ⟩ := hv
    exact smooth_slab_poincare hp e he hab hΩ v φ hφ.symm
  exact closure_minimal hs hc u.property

theorem slab_norm_equivalence : SlabPoincareExpected.NormEquivalence :=
  slab_normEquivalence_of_inequality slab_poincare

theorem slab_hilbert : SlabPoincareExpected.Hilbert :=
  slab_hilbert_of_inequality slab_poincare

end P102.U4
