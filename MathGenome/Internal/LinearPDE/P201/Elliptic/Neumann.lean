import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.Neumann
import MathGenome.Internal.LinearPDE.P201.Common.NormalTrace
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionSupport
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace P201.Neumann
open P201Specs.Neumann

/-- The connectedness bridge is a proved distribution theorem, not a premise. -/
theorem zeroGradient : ZeroGradientStatement := by
  intro n Ω hconn u hu hd
  exact P102.Sobolev.zero_gradient_unique_constant n ℝ Ω u hconn hu hd

lemma constant_underlying {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (c : ℝ) :
    (P201Specs.hUnderlying Ω 1 (constant Ω hΩ c) : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω]
      fun _ => c := by
  letI := finiteVolume Ω hΩ
  have h := (P102.Sobolev.MeanZeroPoincare.exists_constant Ω 2 c).choose_spec.1
  change P102.U4.sobolevUnderlying
    (P201Specs.hToW ℝ Ω 1 ((P201Specs.hToW ℝ Ω 1).symm _)) =ᵐ[_] _
  rw [ContinuousLinearEquiv.apply_symm_apply, h]
  exact Lp.coeFn_const _ _ _

lemma constant_firstDerivative {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (c : ℝ) (i : Fin (m + 1)) :
    P201Specs.hFirstDerivative (constant Ω hΩ c) i = 0 := by
  letI := finiteVolume Ω hΩ
  have h := (P102.Sobolev.MeanZeroPoincare.exists_constant Ω 2 c).choose_spec.2
  have hi : (⟨{i}, by simp⟩ : P102.U4.SobolevIndex (m + 1) 1) ≠
      P102.U4.zeroSobolevIndex (m + 1) 1 := by
    intro he
    have := congrArg Subtype.val he
    simp [P102.U4.zeroSobolevIndex] at this
  have he := congrArg (fun v : P102.U4.SobolevTuple ℝ Ω 1 2 =>
    v ⟨{i}, by simp⟩) h
  simp only [P102.Sobolev.MeanZeroPoincare.positiveDerivatives_apply, hi,
    ite_false, WithLp.ofLp_zero, Pi.zero_apply] at he
  change P102.U4.sobolevDerivative
    (P201Specs.hToW ℝ Ω 1 ((P201Specs.hToW ℝ Ω 1).symm _)) _ = 0
  rwa [ContinuousLinearEquiv.apply_symm_apply]

lemma gradient_eq_zero_of_firstDerivative {n : ℕ} (Ω : Domain n)
    (u : H ℝ Ω 1) (hu : ∀ i, P201Specs.hFirstDerivative u i = 0) :
    P201Specs.hGradient u = 0 := by
  apply Lp.ext
  have hg : (P201Specs.hGradient u : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => WithLp.toLp 2 (fun i => P201Specs.hFirstDerivative u i x)) :=
    MemLp.coeFn_toLp _
  have hz (i : Fin n) : (P201Specs.hFirstDerivative u i : Space n → ℝ) =ᵐ[domainMeasure Ω] 0 := by
    rw [hu i]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hg, ae_all_iff.mpr hz, Lp.coeFn_zero (Space n) 2 (domainMeasure Ω)] with x hx hi hx0
  rw [hx, hx0]
  apply PiLp.ext
  exact hi

lemma constant_gradient {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (c : ℝ) :
    P201Specs.hGradient (constant Ω hΩ c) = 0 :=
  gradient_eq_zero_of_firstDerivative Ω _ (constant_firstDerivative Ω hΩ c)

lemma trace_constant {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (D : P201Specs.NormalTrace.TraceData Ω hΩ) (c : ℝ) :
    (P201Specs.Trace.inclusion Ω hΩ (D.trace (constant Ω hΩ c)) : Space (m + 1) → ℝ)
      =ᵐ[P201Specs.boundaryMeasure Ω] fun _ => c :=
  D.smooth _ _ contDiff_const (constant_underlying Ω hΩ c)

lemma solution_compatible {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (D : P201Specs.NormalTrace.TraceData Ω hΩ)
    (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ) (u : H ℝ Ω 1)
    (hu : IsSolution D f g u) : Compatible D f g := by
  have h := hu (constant Ω hΩ 1)
  have hz : (∫ x in Ω, inner ℝ (P201Specs.hGradient u x)
      (P201Specs.hGradient (constant Ω hΩ 1) x)) = 0 := by
    rw [constant_gradient]
    have he := Lp.coeFn_zero (Space (m + 1)) 2 (domainMeasure Ω)
    apply integral_eq_zero_of_ae
    filter_upwards [he] with x hx
    exact (congrArg (fun z : Space (m + 1) => inner ℝ (P201Specs.hGradient u x) z) hx).trans (by simp)
  have hf : (∫ x in Ω, f x * P201Specs.hUnderlying Ω 1 (constant Ω hΩ 1) x) =
      ∫ x in Ω, f x := by
    apply integral_congr_ae
    filter_upwards [constant_underlying Ω hΩ 1] with x hx
    rw [hx, mul_one]
  rw [hz, hf] at h
  exact h.symm

lemma underlying_toW {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    P102.U4.sobolevUnderlying (P201Specs.hToW ℝ Ω 1 u) = P201Specs.hUnderlying Ω 1 u := rfl

lemma gradient_norm {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    ‖P201Specs.hGradient u‖ =
      (eLpNorm (P102.Sobolev.weakGradientOn (P201Specs.hToW ℝ Ω 1 u)) 2
        (domainMeasure Ω)).toReal := by
  exact Lp.norm_toLp _ _

lemma volume_pos {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (hconn : IsConnected (Ω : Set (Space (m + 1)))) :
    0 < (domainMeasure Ω).real univ := by
  letI := finiteVolume Ω hΩ
  simp only [domainMeasure, P201Specs.domainMeasure, Measure.real, Measure.restrict_apply_univ]
  exact ENNReal.toReal_pos (Ω.isOpen.measure_pos volume hconn.nonempty).ne'
    ((P102.Sobolev.Rellich.bounded_domain (P201Specs.graphFrame m) Ω hΩ).measure_lt_top.ne)

/-- Poincaré is transferred from the concrete distribution-defined W¹,²
space, preserving its Euclidean weak gradient and controlling the full H¹ norm. -/
theorem poincare : PoincareStatement := by
  intro m Ω hΩ hconn
  letI := finiteVolume Ω hΩ
  obtain ⟨C, hC, hb⟩ := P102.Sobolev.MeanZeroPoincare.inequality
    m (P201Specs.graphFrame m) Ω hΩ hconn.isPreconnected ℝ 2 (by norm_num)
  let N : ℝ := Fintype.card (P102.U4.SobolevIndex (m + 1) 1)
  let K : ℝ := ‖(P201Specs.hToW ℝ Ω 1).symm.toContinuousLinearMap‖ + 1
  refine ⟨K * (C + N + 1), ?_, ?_⟩
  · have : 0 ≤ N := Nat.cast_nonneg _
    dsimp [K]
    positivity
  intro u hu
  have hm : P102.Sobolev.MeanZeroPoincare.average Ω
      (P102.U4.sobolevUnderlying (P201Specs.hToW ℝ Ω 1 u)) = 0 := by
    simpa only [mean, P102.Sobolev.MeanZeroPoincare.average, domainMeasure,
      P201Specs.domainMeasure, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul, underlying_toW] using hu
  have hU : ‖P201Specs.hUnderlying Ω 1 u‖ ≤ C * ‖P201Specs.hGradient u‖ := by
    have h := hb (P201Specs.hToW ℝ Ω 1 u)
    rw [hm] at h
    simp only [sub_zero] at h
    rw [← gradient_norm Ω u] at h
    exact h
  have hD : ‖P102.Sobolev.MeanZeroPoincare.positiveDerivatives Ω 2
      (P201Specs.hToW ℝ Ω 1 u)‖ ≤ N * ‖P201Specs.hGradient u‖ := by
    simpa only [← gradient_norm Ω u] using
      P102.Sobolev.MeanZeroPoincare.positive_le_gradient Ω 2
        (P201Specs.hToW ℝ Ω 1 u)
  have hW : ‖P201Specs.hToW ℝ Ω 1 u‖ ≤ (C + N) * ‖P201Specs.hGradient u‖ := by
    rw [P102.Sobolev.MeanZeroPoincare.norm_split]
    change ‖P102.U4.sobolevUnderlying (P201Specs.hToW ℝ Ω 1 u)‖ ≤ _ at hU
    nlinarith
  calc
    ‖u‖ = ‖(P201Specs.hToW ℝ Ω 1).symm (P201Specs.hToW ℝ Ω 1 u)‖ := by simp
    _ ≤ ‖(P201Specs.hToW ℝ Ω 1).symm.toContinuousLinearMap‖ *
        ‖P201Specs.hToW ℝ Ω 1 u‖ := by
      exact (P201Specs.hToW ℝ Ω 1).symm.toContinuousLinearMap.le_opNorm
        (P201Specs.hToW ℝ Ω 1 u)
    _ ≤ K * ((C + N) * ‖P201Specs.hGradient u‖) := by
      apply mul_le_mul (by dsimp [K]; linarith) hW (norm_nonneg _) (by dsimp [K]; positivity)
    _ ≤ K * (C + N + 1) * ‖P201Specs.hGradient u‖ := by
      dsimp [K]
      nlinarith [norm_nonneg (P201Specs.hGradient u), norm_nonneg (P201Specs.hToW ℝ Ω 1).symm.toContinuousLinearMap]

lemma eq_constant_of_underlying {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (u : H ℝ Ω 1) (c : ℝ)
    (hc : (P201Specs.hUnderlying Ω 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] fun _ => c) :
    u = constant Ω hΩ c := by
  apply hilbertUnderlyingInjective Ω 1
  apply Lp.ext
  exact hc.trans (constant_underlying Ω hΩ c).symm


/-- The energy form is bounded on the full H¹ space. -/
def energy {n : ℕ} (Ω : Domain n) : H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ :=
  ∑ i : Fin n, (innerSL ℝ).bilinearComp
    (InteriorTesting.firstDerivativeMap Ω i) (InteriorTesting.firstDerivativeMap Ω i)

lemma inner_toLp {n : ℕ} (a b : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 a) (WithLp.toLp 2 b) = ∑ i, a i * b i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => Real.inner_apply (a i) (b i))

set_option maxHeartbeats 200000 in
lemma energy_integral {n : ℕ} (Ω : Domain n) (u v : H ℝ Ω 1) :
    energy Ω u v = ∫ x in Ω, inner ℝ (P201Specs.hGradient u x) (P201Specs.hGradient v x) := by
  have hg (w : H ℝ Ω 1) : (P201Specs.hGradient w : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => WithLp.toLp 2 (fun i => P201Specs.hFirstDerivative w i x)) :=
    MemLp.coeFn_toLp _
  have hi (i : Fin n) : Integrable (fun x =>
      P201Specs.hFirstDerivative u i x * P201Specs.hFirstDerivative v i x) (domainMeasure Ω) :=
    (Lp.memLp (P201Specs.hFirstDerivative u i)).integrable_mul
      (Lp.memLp (P201Specs.hFirstDerivative v i))
  rw [show (∫ x in Ω, inner ℝ (P201Specs.hGradient u x) (P201Specs.hGradient v x)) =
      ∫ x in Ω, ∑ i, P201Specs.hFirstDerivative u i x * P201Specs.hFirstDerivative v i x from by
    apply integral_congr_ae
    filter_upwards [hg u, hg v] with x hu hv
    rw [hu, hv]
    exact inner_toLp (fun i => P201Specs.hFirstDerivative u i x)
      (fun i => P201Specs.hFirstDerivative v i x)]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [energy, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    InteriorTesting.firstDerivativeMap_apply, innerSL_apply_apply, L2.inner_def]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with x
  exact Real.inner_apply _ _

lemma energy_self {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    energy Ω u u = ‖P201Specs.hGradient u‖ ^ 2 := by
  rw [energy_integral, ← L2.inner_def, real_inner_self_eq_norm_sq]

lemma energy_constant_right {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (u : H ℝ Ω 1) (c : ℝ) :
    energy Ω u (constant Ω hΩ c) = 0 := by
  simp [energy, InteriorTesting.firstDerivativeMap_apply, constant_firstDerivative]

lemma energy_constant_left {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (u : H ℝ Ω 1) (c : ℝ) :
    energy Ω (constant Ω hΩ c) u = 0 := by
  simp [energy, InteriorTesting.firstDerivativeMap_apply, constant_firstDerivative]

/-- The volume and boundary forcing as one bounded functional. -/
def forcing {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ) :
    H ℝ Ω 1 →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (P201Specs.hUnderlying Ω 1) + g.comp D.trace

lemma forcing_apply {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (v : H ℝ Ω 1) :
    forcing D f g v = (∫ x in Ω, f x * P201Specs.hUnderlying Ω 1 v x) + g (D.trace v) := by
  simp only [forcing, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp [RCLike.inner_apply, mul_comm]

lemma solution_iff {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u : H ℝ Ω 1) : IsSolution D f g u ↔ ∀ v, energy Ω u v = forcing D f g v := by
  simp only [IsSolution, energy_integral, forcing_apply]

lemma constant_smul_one {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (c : ℝ) :
    constant Ω hΩ c = c • constant Ω hΩ 1 := by
  apply hilbertUnderlyingInjective Ω 1
  rw [map_smul]
  apply Lp.ext
  filter_upwards [constant_underlying Ω hΩ c, constant_underlying Ω hΩ 1,
    Lp.coeFn_smul c (P201Specs.hUnderlying Ω 1 (constant Ω hΩ 1))] with x hc h1 hs
  rw [hc, hs]
  change c = c * P201Specs.hUnderlying Ω 1 (constant Ω hΩ 1) x
  rw [h1, mul_one]

lemma constants_span {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω) :
    constants Ω = Submodule.span ℝ {constant Ω hΩ 1} := by
  apply le_antisymm
  · rintro u ⟨c, hc⟩
    have he : u = c • constant Ω hΩ 1 :=
      (eq_constant_of_underlying Ω hΩ u c hc).trans (constant_smul_one Ω hΩ c)
    rw [he]
    exact (Submodule.span ℝ {constant Ω hΩ 1}).smul_mem c
      (Submodule.subset_span (Set.mem_singleton (constant Ω hΩ 1)))
  · apply Submodule.span_le.mpr
    rintro u (rfl : u = constant Ω hΩ 1)
    exact ⟨1, constant_underlying Ω hΩ 1⟩

lemma constants_closed {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω) :
    IsClosed (constants Ω : Set (H ℝ Ω 1)) := by
  rw [constants_span Ω hΩ]
  exact Submodule.closed_of_finiteDimensional _


lemma forcing_constant {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (hc : Compatible D f g) (c : ℝ) : forcing D f g (constant Ω hΩ c) = 0 := by
  rw [constant_smul_one, map_smul]
  have h1 : forcing D f g (constant Ω hΩ 1) = 0 := by
    rw [forcing_apply]
    have hf : (∫ x in Ω, f x * P201Specs.hUnderlying Ω 1 (constant Ω hΩ 1) x) =
        ∫ x in Ω, f x := by
      apply integral_congr_ae
      filter_upwards [constant_underlying Ω hΩ 1] with x hx
      rw [hx, mul_one]
    rwa [hf]
  rw [h1, smul_zero]

/-- Mean as a continuous functional, so its kernel is a closed Hilbert space. -/
def meanMap {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω) :
    H ℝ Ω 1 →L[ℝ] ℝ := by
  letI := finiteVolume Ω hΩ
  exact ((domainMeasure Ω).real univ)⁻¹ •
    (P102.Sobolev.MeanZeroPoincare.integralLp Ω 2).comp (P201Specs.hUnderlying Ω 1)

lemma meanMap_apply {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (u : H ℝ Ω 1) : meanMap Ω hΩ u = mean Ω u := by
  simp only [meanMap, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    P102.Sobolev.MeanZeroPoincare.integralLp_eq, mean]

lemma mean_constant {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (hconn : IsConnected (Ω : Set (Space (m + 1)))) (c : ℝ) :
    mean Ω (constant Ω hΩ c) = c := by
  unfold mean
  rw [integral_congr_ae (constant_underlying Ω hΩ c), integral_const, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (volume_pos Ω hΩ hconn).ne', one_mul]

/-- Subtract the mean without changing the weak gradient. -/
def center {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (u : H ℝ Ω 1) : H ℝ Ω 1 := u - constant Ω hΩ (mean Ω u)

lemma mean_center {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (hconn : IsConnected (Ω : Set (Space (m + 1)))) (u : H ℝ Ω 1) :
    mean Ω (center Ω hΩ u) = 0 := by
  rw [← meanMap_apply Ω hΩ, center, map_sub, meanMap_apply, meanMap_apply,
    mean_constant Ω hΩ hconn, sub_self]

lemma energy_center_left {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (u v : H ℝ Ω 1) : energy Ω (center Ω hΩ u) v = energy Ω u v := by
  simp [center, map_sub, sub_apply, energy_constant_left]

lemma energy_center_right {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (u v : H ℝ Ω 1) : energy Ω u (center Ω hΩ v) = energy Ω u v := by
  simp [center, map_sub, energy_constant_right]

lemma mean_sub {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (u v : H ℝ Ω 1) : mean Ω (u - v) = mean Ω u - mean Ω v := by
  simp only [← meanMap_apply Ω hΩ, map_sub]

lemma zero_energy_constant {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (hconn : IsConnected (Ω : Set (Space (m + 1)))) (u : H ℝ Ω 1)
    (hu : energy Ω u u = 0) : u = constant Ω hΩ (mean Ω u) := by
  obtain ⟨C, _, hb⟩ := poincare Ω hΩ hconn
  have hc : ‖P201Specs.hGradient (center Ω hΩ u)‖ = 0 := by
    have he : ‖P201Specs.hGradient (center Ω hΩ u)‖ ^ 2 = 0 := by
      rw [← energy_self, energy_center_left, energy_center_right, hu]
    nlinarith [sq_nonneg ‖P201Specs.hGradient (center Ω hΩ u)‖]
  have hz : center Ω hΩ u = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa [hc] using hb (center Ω hΩ u) (mean_center Ω hΩ hconn u)
  exact sub_eq_zero.mp hz

lemma solutions_differ {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (hconn : IsConnected (Ω : Set (Space (m + 1))))
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u v : H ℝ Ω 1) (hu : IsSolution D f g u) (hv : IsSolution D f g v) :
    ∃! c : ℝ, u = v + constant Ω hΩ c := by
  have he : energy Ω (u - v) (u - v) = 0 := by
    simp only [map_sub, sub_apply, (solution_iff D f g u).mp hu,
      (solution_iff D f g v).mp hv, sub_self]
  have hc := zero_energy_constant Ω hΩ hconn (u - v) he
  refine ⟨mean Ω (u - v), ?_, ?_⟩
  · exact sub_eq_iff_eq_add'.mp hc
  intro c hc'
  have hh : u - v = constant Ω hΩ c := sub_eq_iff_eq_add'.mpr hc'
  rw [hh, mean_constant Ω hΩ hconn]

lemma mean_zero_unique {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (hconn : IsConnected (Ω : Set (Space (m + 1))))
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u v : H ℝ Ω 1) (hu : IsSolution D f g u) (hv : IsSolution D f g v)
    (hmu : mean Ω u = 0) (hmv : mean Ω v = 0) : u = v := by
  have he : energy Ω (u - v) (u - v) = 0 := by
    simp only [map_sub, sub_apply, (solution_iff D f g u).mp hu,
      (solution_iff D f g v).mp hv, sub_self]
  obtain ⟨C, _, hb⟩ := poincare Ω hΩ hconn
  have hgrad : ‖P201Specs.hGradient (u - v)‖ = 0 := by
    rw [energy_self] at he
    nlinarith [norm_nonneg (P201Specs.hGradient (u - v))]
  have hm : mean Ω (u - v) = 0 := by rw [mean_sub Ω hΩ, hmu, hmv, sub_self]
  have hnorm : ‖u - v‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa [hgrad] using hb (u - v) hm
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Continuous forcing bound in the full H¹ norm. -/
lemma forcing_bound {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (v : H ℝ Ω 1) :
    ‖forcing D f g v‖ ≤ (1 + ‖D.trace‖) * (‖f‖ + ‖g‖) * ‖v‖ := by
  have hf : ‖inner ℝ f (P201Specs.hUnderlying Ω 1 v)‖ ≤ ‖f‖ * ‖v‖ :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (NormalTrace.underlying_norm_le Ω v) (norm_nonneg f))
  have hg : ‖g (D.trace v)‖ ≤ ‖g‖ * (‖D.trace‖ * ‖v‖) :=
    (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left (D.trace.le_opNorm v) (norm_nonneg g))
  change ‖inner ℝ f (P201Specs.hUnderlying Ω 1 v) + g (D.trace v)‖ ≤ _
  calc
    _ ≤ ‖inner ℝ f (P201Specs.hUnderlying Ω 1 v)‖ + ‖g (D.trace v)‖ := norm_add_le _ _
    _ ≤ ‖f‖ * ‖v‖ + ‖g‖ * (‖D.trace‖ * ‖v‖) := add_le_add hf hg
    _ ≤ _ := by nlinarith [norm_nonneg f, norm_nonneg g, norm_nonneg D.trace, norm_nonneg v,
      mul_nonneg (norm_nonneg f) (norm_nonneg D.trace)]

/-- Any mean-zero variational solution satisfies the quantitative estimate. -/
lemma solution_bound {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ u : H ℝ Ω 1, mean Ω u = 0 → ‖u‖ ≤ C * ‖P201Specs.hGradient u‖)
    (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ) (u : H ℝ Ω 1)
    (hu : IsSolution D f g u) (hm : mean Ω u = 0) :
    ‖u‖ ≤ C ^ 2 * (1 + ‖D.trace‖) * (‖f‖ + ‖g‖) := by
  have hp := hb u hm
  have he := (solution_iff D f g u).mp hu u
  rw [energy_self] at he
  have hf := forcing_bound D f g u
  rw [← he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hf
  have hs : ‖u‖ ^ 2 ≤ C ^ 2 * ‖P201Specs.hGradient u‖ ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg u) hp
    nlinarith
  by_cases hz : ‖u‖ = 0
  · rw [hz]; positivity
  · have hp0 : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hmul := mul_le_mul_of_nonneg_left hf (sq_nonneg C)
    nlinarith


/-- Lax–Milgram on the closed kernel of the mean, followed by centering every
H¹ test. No compactness or connectedness certificate is assumed. -/
lemma exists_solution {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (hconn : IsConnected (Ω : Set (Space (m + 1))))
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (hc : Compatible D f g) : ∃ u, IsSolution D f g u ∧ mean Ω u = 0 := by
  obtain ⟨C, hC, hb⟩ := poincare Ω hΩ hconn
  let Z := (meanMap Ω hΩ).ker
  letI : CompleteSpace Z := (meanMap Ω hΩ).isClosed_ker.completeSpace_coe
  let B : Z →L[ℝ] Z →L[ℝ] ℝ := (energy Ω).bilinearComp Z.subtypeL Z.subtypeL
  have hco : IsCoercive B := by
    refine ⟨(C ^ 2)⁻¹, by positivity, ?_⟩
    intro z
    have hm : mean Ω z.val = 0 := (meanMap_apply Ω hΩ z.val).symm.trans z.property
    have hp := hb z.val hm
    have hs := mul_self_le_mul_self (norm_nonneg z.val) hp
    change (C ^ 2)⁻¹ * ‖z.val‖ * ‖z.val‖ ≤ energy Ω z.val z.val
    rw [energy_self]
    calc
      _ = ‖z.val‖ ^ 2 / C ^ 2 := by ring
      _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hC)).mpr (by nlinarith)
  let ℓ : Z →L[ℝ] ℝ := (forcing D f g).comp Z.subtypeL
  let R : Z := (InnerProductSpace.toDual ℝ Z).symm ℓ
  let z : Z := hco.continuousLinearEquivOfBilin.symm R
  have hz : ∀ v : Z, B z v = ℓ v := by
    intro v
    calc
      B z v = inner ℝ (hco.continuousLinearEquivOfBilin z) v :=
        (hco.continuousLinearEquivOfBilin_apply z v).symm
      _ = inner ℝ R v := by
        congr 1
        exact hco.continuousLinearEquivOfBilin.apply_symm_apply R
      _ = ℓ v := InnerProductSpace.toDual_symm_apply
  refine ⟨z.val, (solution_iff D f g z.val).mpr ?_, ?_⟩
  · intro v
    have hvZ : center Ω hΩ v ∈ Z := by
      change meanMap Ω hΩ (center Ω hΩ v) = 0
      rw [meanMap_apply, mean_center Ω hΩ hconn]
    have h := hz ⟨center Ω hΩ v, hvZ⟩
    change energy Ω z.val (center Ω hΩ v) = forcing D f g (center Ω hΩ v) at h
    rw [energy_center_right] at h
    simpa only [center, map_sub, forcing_constant D f g hc, sub_zero] using h
  · exact (meanMap_apply Ω hΩ z.val).symm.trans z.property

lemma solution_center {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u : H ℝ Ω 1) (hu : IsSolution D f g u) : IsSolution D f g (center Ω hΩ u) := by
  apply (solution_iff D f g _).mpr
  intro v
  rw [energy_center_left]
  exact (solution_iff D f g u).mp hu v

lemma quotient_center {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (u : H ℝ Ω 1) :
    (Submodule.Quotient.mk (center Ω hΩ u) : P201Specs.Neumann.Quotient Ω) =
      Submodule.Quotient.mk u := by
  apply (Submodule.Quotient.eq _).mpr
  change center Ω hΩ u - u ∈ constants Ω
  refine ⟨-mean Ω u, ?_⟩
  have hc := constant_underlying Ω hΩ (mean Ω u)
  have he : center Ω hΩ u - u = -constant Ω hΩ (mean Ω u) := by
    dsimp [center]; abel
  rw [he, map_neg]
  filter_upwards [Lp.coeFn_neg (P201Specs.hUnderlying Ω 1 (constant Ω hΩ (mean Ω u))), hc] with x hn hc
  change (-P201Specs.hUnderlying Ω 1 (constant Ω hΩ (mean Ω u))) x = -mean Ω u
  rw [hn]
  change -(P201Specs.hUnderlying Ω 1 (constant Ω hΩ (mean Ω u)) x) = -mean Ω u
  rw [hc]

/-- All conclusions of the Neumann compatibility theorem, including the
standard quotient norm, use one domain constant uniform over f and g. -/
theorem solvability : SolvabilityStatement := by
  intro m Ω hΩ hconn D
  obtain ⟨C, hC, hb⟩ := poincare Ω hΩ hconn
  refine ⟨C ^ 2 * (1 + ‖D.trace‖), by positivity, ?_⟩
  intro f g
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨u, hu⟩
      exact solution_compatible Ω hΩ D f g u hu
    · intro hc
      obtain ⟨u, hu, _⟩ := exists_solution Ω hΩ hconn D f g hc
      exact ⟨u, hu⟩
  · exact solutions_differ hconn D f g
  · intro hc
    obtain ⟨u, hu, hm⟩ := exists_solution Ω hΩ hconn D f g hc
    refine ⟨u, ⟨hu, hm⟩, ?_⟩
    rintro v ⟨hv, hmv⟩
    exact mean_zero_unique hconn D f g v u hv hu hmv hm
  · intro u hu hm
    exact solution_bound D C hC hb f g u hu hm
  · intro u hu
    rw [← quotient_center Ω hΩ u]
    exact (Submodule.Quotient.norm_mk_le (constants Ω) (center Ω hΩ u)).trans
      (solution_bound D C hC hb f g _ (solution_center D f g u hu) (mean_center Ω hΩ hconn u))


/-- The equality relating the two canonical distribution operators, using the
actual first derivative coordinates of H¹. -/
lemma divergence_gradient {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    P201Specs.negativeDivergenceDistribution Ω (P201Specs.hGradient u) =
      -P201Specs.distributionLaplacian (P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 u)) := by
  change -∑ i : Fin n, P201Specs.distributionDerivative {i}
    (P201Specs.regularDistribution Ω (fun x => P201Specs.hGradient u x i)) =
      -∑ i : Fin n, P201Specs.distributionDerivative {i, i}
        (P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 u))
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [NormalTrace.regular_gradient_component]
  have he := hilbertDerivativeDistribution Ω 1 u
    (⟨{i}, by simp⟩ : P102.U4.SobolevIndex n 1)
  change P201Specs.distributionDerivative {i}
    (P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 u)) =
      P201Specs.regularDistribution Ω (P201Specs.hFirstDerivative u i) at he
  rw [← he]
  exact (P102.U4.derivative_add n ℝ Ω {i} {i} _).symm

/-- Compact tests eliminate the trace term, giving the actual distributional
negative divergence, with the manuscript's sign. -/
lemma solution_distribution {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u : H ℝ Ω 1) (hu : IsSolution D f g u) :
    P201Specs.negativeDivergenceDistribution Ω (P201Specs.hGradient u) =
      P201Specs.regularDistribution Ω f := by
  ext φ
  obtain ⟨v, hv⟩ := InteriorTesting.exists_test_class Ω φ
  have hv0 : D.trace v.val = 0 := by
    have h : v.val ∈ P201Specs.hZeroSubmodule ℝ Ω := v.property
    have hk : v.val ∈ D.trace.ker := by
      simpa only [D.kernel] using h
    exact hk
  have h := hu v.val
  rw [hv0, map_zero, add_zero] at h
  rw [InteriorTesting.negativeDivergenceDistribution_pairing]
  rw [P102.U4.regular_pairing (m + 1) ℝ Ω f (P102.U4.domainLp_locallyIntegrable Ω 2 f) φ]
  change P201Specs.weakNegativeDivergence Ω (P201Specs.hGradient u) φ = _
  have hv' : P201Specs.hUnderlying Ω 1 v.val = P102.U4.testToDomainLp Ω 2 φ := hv
  calc
    _ = ∫ x in Ω, inner ℝ (P201Specs.hGradient u x) (P201Specs.hGradient v.val x) := by
      apply integral_congr_ae
      filter_upwards [InteriorTesting.smooth_gradient_ae Ω v.val φ hv'] with x hx
      rw [hx]
    _ = ∫ x in Ω, f x * P201Specs.hUnderlying Ω 1 v.val x := h
    _ = ∫ x in Ω, f x * φ x := by
      apply integral_congr_ae
      have he : (P201Specs.hUnderlying Ω 1 v.val : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] φ := by
        rw [hv']; exact P102.U4.testToDomainLp_ae Ω 2 φ
      filter_upwards [he] with x hx
      rw [hx]

lemma regular_neg {n : ℕ} (Ω : Domain n) (f : Lp ℝ Ω 2) :
    P201Specs.regularDistribution Ω ((-f : Lp ℝ Ω 2) : Space n → ℝ) = -P201Specs.regularDistribution Ω f := by
  ext φ
  change P201Specs.regularDistribution Ω ((-f : Lp ℝ Ω 2) : Space n → ℝ) φ =
    -(P201Specs.regularDistribution Ω f φ)
  rw [P102.U4.regular_pairing n ℝ Ω ((-f : Lp ℝ Ω 2) : Space n → ℝ)
    (P102.U4.domainLp_locallyIntegrable Ω 2 (-f)) φ,
    P102.U4.regular_pairing n ℝ Ω f (P102.U4.domainLp_locallyIntegrable Ω 2 f) φ,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg f] with x hx
  change (-f : Lp ℝ Ω 2) x * φ x = -(f x * φ x)
  rw [hx]
  change -f x * φ x = -(f x * φ x)
  ring

/-- The weak equation identifies both the Laplacian and the normal trace. -/
theorem identification : IdentificationStatement := by
  intro m Ω hΩ D f g u hu
  have hdist := solution_distribution D f g u hu
  have hlap : P201Specs.NormalTrace.HasLaplacian Ω u (-f) := by
    rw [divergence_gradient] at hdist
    change P201Specs.distributionLaplacian (P201Specs.regularDistribution Ω (P201Specs.hUnderlying Ω 1 u)) =
      P201Specs.regularDistribution Ω (-f)
    rw [regular_neg]
    exact neg_eq_iff_eq_neg.mp hdist
  refine ⟨hlap, NormalTrace.gradientDivergence Ω u (-f) hlap, ?_⟩
  intro v
  have hi : Integrable (fun x => inner ℝ (P201Specs.hGradient u x) (P201Specs.hGradient v x))
      (domainMeasure Ω) := L2.integrable_inner _ _
  have hf : Integrable (fun x => (-f) x * P201Specs.hUnderlying Ω 1 v x) (domainMeasure Ω) :=
    (Lp.memLp (-f)).integrable_mul (Lp.memLp (P201Specs.hUnderlying Ω 1 v))
  rw [integral_add hi hf]
  have hn : (∫ x in Ω, (-f) x * P201Specs.hUnderlying Ω 1 v x) =
      -(∫ x in Ω, f x * P201Specs.hUnderlying Ω 1 v x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg f] with x hx
    rw [hx]
    change -f x * P201Specs.hUnderlying Ω 1 v x = -(f x * P201Specs.hUnderlying Ω 1 v x)
    ring
  rw [hn, hu v]
  ring

/-- The common normal-trace construction equals g on every boundary datum;
its uniqueness uses the right inverse, hence trace surjectivity. -/
lemma normalTrace_eq {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : P201Specs.NormalTrace.TraceData Ω hΩ) (f : Lp ℝ Ω 2) (g : HminusHalf Ω hΩ)
    (u : H ℝ Ω 1) (hu : IsSolution D f g u) :
    NormalTrace.normalTrace D (P201Specs.hGradient u) (-f) = g := by
  obtain ⟨_, hd, hp⟩ := identification Ω hΩ D f g u hu
  exact NormalTrace.pairing_unique D _ _ _ _
    (NormalTrace.normalTrace_pairing Ω hΩ D _ _ hd) hp

/-- Independent constants and compatibility conditions on a finite family of
disjoint connected components with their separate physical traces. -/
theorem components : ComponentsStatement := by
  intro m k Ω hΩ hconn hdisj D f g
  constructor
  · constructor
    · rintro ⟨u, hu⟩ i
      exact solution_compatible (Ω i) (hΩ i) (D i) (f i) (g i) (u i) (hu i)
    · intro hc
      choose u hu using fun i => exists_solution (Ω i) (hΩ i) (hconn i) (D i) (f i) (g i) (hc i)
      exact ⟨u, fun i => (hu i).1⟩
  · intro u v hu hv
    have he := fun i => solutions_differ (hconn i) (D i) (f i) (g i) (u i) (v i) (hu i) (hv i)
    choose c hc huniq using he
    refine ⟨c, hc, ?_⟩
    intro d hd
    funext i
    exact huniq i (d i) (hd i)



open P201Specs

private def restrictH {n : ℕ} {U V : Domain n} (hVU : V ≤ U)
    (u : H ℝ U 1) : H ℝ V 1 := by
  let w : P102.U4.SobolevIndex n 1 → Lp ℝ V 2 := fun α =>
    ((MeasureTheory.Lp.memLp (u.val α)).mono_measure
      (Measure.restrict_mono hVU le_rfl)).toLp (u.val α)
  refine ⟨WithLp.toLp 2 w, ?_⟩
  change P201Specs.hilbertTupleToSum ℝ V 1 (WithLp.toLp 2 w) ∈
    P102.U4.sobolevSubmodule ℝ V 1 2
  apply (P102.U4.mem_sobolevSubmodule_iff V 1 2 _).mpr
  intro α φ
  let φ' : P102.U4.TestSpace ℝ U :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
  have hw := (P102.U4.mem_sobolevSubmodule_iff U 1 2 _).mp u.property α φ'
  simp only [P102.U4.lpTestPairing_eq_integral] at hw ⊢
  change (∫ x in V, w α x * φ x) = (-1 : ℝ) ^ α.val.card *
    ∫ x in V, w (P102.U4.zeroSobolevIndex n 1) x *
      P102.U4.testPartialWord V (α.val.sort (· ≤ ·)) φ x
  have hwrep (β : P102.U4.SobolevIndex n 1) :
      (w β : Space n → ℝ) =ᵐ[domainMeasure V] u.val β :=
    MemLp.coeFn_toLp _
  have hl : (∫ x in V, w α x * φ x) = ∫ x in V, u.val α x * φ x := by
    apply integral_congr_ae
    filter_upwards [hwrep α] with x hx
    rw [hx]
  have hr : (∫ x in V, w (P102.U4.zeroSobolevIndex n 1) x *
      P102.U4.testPartialWord V (α.val.sort (· ≤ ·)) φ x) =
      ∫ x in V, u.val (P102.U4.zeroSobolevIndex n 1) x *
        P102.U4.testPartialWord V (α.val.sort (· ≤ ·)) φ x := by
    apply integral_congr_ae
    filter_upwards [hwrep (P102.U4.zeroSobolevIndex n 1)] with x hx
    rw [hx]
  rw [hl, hr]
  rw [P102.U4.setIntegral_mul_test V, P102.U4.setIntegral_mul_test V]
  rw [P102.U4.setIntegral_mul_test U, P102.U4.setIntegral_mul_test U] at hw
  have he : (P102.U4.testPartialWord V (α.val.sort (· ≤ ·)) φ : Space n → ℝ) =
      P102.U4.testPartialWord U (α.val.sort (· ≤ ·)) φ' := by
    rw [P102.U4.testPartialWord_coe, P102.U4.testPartialWord_coe]
    rfl
  rw [he]
  exact hw

private lemma restrictH_underlying {n : ℕ} {U V : Domain n} (hVU : V ≤ U)
    (u : H ℝ U 1) :
    (hUnderlying V 1 (restrictH hVU u) : Space n → ℝ) =ᵐ[domainMeasure V]
      hUnderlying U 1 u := by
  change ((MeasureTheory.Lp.memLp (u.val (P102.U4.zeroSobolevIndex n 1))).mono_measure
      (Measure.restrict_mono hVU le_rfl)).toLp
      (u.val (P102.U4.zeroSobolevIndex n 1)) =ᵐ[domainMeasure V] _
  exact MemLp.coeFn_toLp _

private lemma restrictH_firstDerivative {n : ℕ} {U V : Domain n} (hVU : V ≤ U)
    (u : H ℝ U 1) (i : Fin n) :
    (hFirstDerivative (restrictH hVU u) i : Space n → ℝ) =ᵐ[domainMeasure V]
      hFirstDerivative u i := by
  change ((MeasureTheory.Lp.memLp (u.val (⟨{i}, by simp⟩ : P102.U4.SobolevIndex n 1))).mono_measure
      (Measure.restrict_mono hVU le_rfl)).toLp
      (u.val (⟨{i}, by simp⟩ : P102.U4.SobolevIndex n 1)) =ᵐ[domainMeasure V] _
  exact MemLp.coeFn_toLp _
lemma exists_restriction {n : ℕ} (U V : Domain n) (hVU : (V : Set (Space n)) ⊆ U)
    (u : H ℝ U 1) : ∃ v : H ℝ V 1, P201Specs.Neumann.RestrictsTo U V u v := by
  refine ⟨restrictH hVU u, ?_, ?_⟩
  · exact (restrictH_underlying hVU u).symm
  · intro i
    exact (restrictH_firstDerivative hVU u i).symm


lemma restrictsTo_gradient {n : ℕ} (U V : Domain n) (hVU : V ≤ U)
    (u : H ℝ U 1) (v : H ℝ V 1) (h : RestrictsTo U V u v) :
    (hGradient u : Space n → Space n) =ᵐ[domainMeasure V] hGradient v := by
  have hu : (hGradient u : Space n → Space n) =ᵐ[domainMeasure U]
      (fun x => WithLp.toLp 2 (fun j => hFirstDerivative u j x)) :=
    MemLp.coeFn_toLp _
  have huV : (hGradient u : Space n → Space n) =ᵐ[domainMeasure V]
      (fun x => WithLp.toLp 2 (fun j => hFirstDerivative u j x)) :=
    ae_restrict_of_ae_restrict_of_subset hVU hu
  have hv : (hGradient v : Space n → Space n) =ᵐ[domainMeasure V]
      (fun x => WithLp.toLp 2 (fun j => hFirstDerivative v j x)) :=
    MemLp.coeFn_toLp _
  filter_upwards [huV, hv, ae_all_iff.mpr h.2] with x hux hvx hx
  rw [hux, hvx]
  exact congrArg (WithLp.toLp 2) (funext hx)

lemma union_energy_integral {n k : ℕ} (Ω : Fin k → Domain n)
    (hdisj : Pairwise fun i j => Disjoint (Ω i : Set (Space n)) (Ω j : Set (Space n)))
    (u v : H ℝ (⨆ i, Ω i) 1) (us vs : ∀ i, H ℝ (Ω i) 1)
    (hu : ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) u (us i))
    (hv : ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) v (vs i)) :
    (∫ x in (⨆ i, Ω i : Domain n), inner ℝ (hGradient u x) (hGradient v x)) =
      ∑ i, ∫ x in Ω i, inner ℝ (hGradient (us i) x) (hGradient (vs i) x) := by
  have hi (i : Fin k) : IntegrableOn
      (fun x => inner ℝ (hGradient u x) (hGradient v x)) (Ω i : Set (Space n)) volume := by
    apply (L2.integrable_inner (hGradient u) (hGradient v)).mono_measure
    exact Measure.restrict_mono (le_iSup Ω i) le_rfl
  rw [Opens.coe_iSup, integral_iUnion_fintype (fun i => (Ω i).isOpen.measurableSet) hdisj hi]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [restrictsTo_gradient _ _ (le_iSup Ω i) u (us i) (hu i),
    restrictsTo_gradient _ _ (le_iSup Ω i) v (vs i) (hv i)] with x hux hvx
  rw [hux, hvx]




private def glueFunction {n k : ℕ} (Ω : Fin k → Domain n)
    (f : ∀ i, Lp ℝ (Ω i) 2) (x : Space n) : ℝ := by
  classical
  exact ∑ i, (Ω i : Set (Space n)).indicator (f i) x

private lemma glueFunction_memLp {n k : ℕ} (Ω : Fin k → Domain n)
    (f : ∀ i, Lp ℝ (Ω i) 2) : MemLp (glueFunction Ω f) 2 (domainMeasure (⨆ i, Ω i)) := by
  classical
  let F : Fin k → Space n → ℝ := fun i => (Ω i : Set (Space n)).indicator (f i)
  have hF (i : Fin k) : MemLp (F i) 2 (volume : Measure (Space n)) :=
    (memLp_indicator_iff_restrict (Ω i).isOpen.measurableSet.nullMeasurableSet).mpr
      (MeasureTheory.Lp.memLp (f i))
  have hsum : MemLp (fun x => ∑ i, F i x) 2 (volume : Measure (Space n)) := by
    exact memLp_finsetSum Finset.univ (fun i _ => hF i)
  exact hsum.restrict ((⨆ i, Ω i : Domain n) : Set (Space n))

private def glueLp {n k : ℕ} (Ω : Fin k → Domain n)
    (f : ∀ i, Lp ℝ (Ω i) 2) : Lp ℝ (⨆ i, Ω i) 2 :=
  (glueFunction_memLp Ω f).toLp (glueFunction Ω f)

private lemma glueLp_restrict {n k : ℕ} (Ω : Fin k → Domain n)
    (hd : Pairwise fun i j => Disjoint (Ω i : Set (Space n)) (Ω j))
    (f : ∀ i, Lp ℝ (Ω i) 2) (i : Fin k) :
    (glueLp Ω f : Space n → ℝ) =ᵐ[domainMeasure (Ω i)] f i := by
  classical
  have hrep : (glueLp Ω f : Space n → ℝ) =ᵐ[domainMeasure (⨆ i, Ω i)]
      (fun x => ∑ j, (Ω j : Set (Space n)).indicator (f j) x) := (glueFunction_memLp Ω f).coeFn_toLp
  have hrep' := ae_restrict_of_ae_restrict_of_subset (show (Ω i : Set (Space n)) ⊆ ((⨆ i, Ω i : Domain n) : Set (Space n)) from le_iSup Ω i) hrep
  filter_upwards [hrep', ae_restrict_mem (Ω i).isOpen.measurableSet] with x hx hxi
  rw [hx]
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hxi _
  · intro j _ hji
    apply Set.indicator_of_notMem
    exact fun hxj => (Set.disjoint_left.mp (hd hji)) hxj hxi
  · simp

private lemma regular_pairing_local {n : ℕ} (U V : Domain n)
    (f : Lp ℝ U 2) (g : Lp ℝ V 2)
    (hfg : (f : Space n → ℝ) =ᵐ[domainMeasure V] g)
    (φ : P102.U4.TestSpace ℝ U) (hφ : tsupport φ ⊆ V) :
    P102.U4.regularDistribution U f φ = ∫ x in V, g x * φ x := by
  let ψ : P102.U4.TestSpace ℝ V := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
  rw [P102.U4.regular_pairing n ℝ U f (P102.U4.domainLp_locallyIntegrable U 2 f)]
  rw [P102.U4.setIntegral_mul_test U]
  change (∫ x, f x * ψ x) = _
  rw [← P102.U4.setIntegral_mul_test V]
  exact integral_congr_ae (hfg.mul EventuallyEq.rfl)

theorem exists_gluing {n k : ℕ} (Ω : Fin k → Domain n)
    (hd : Pairwise fun i j => Disjoint (Ω i : Set (Space n)) (Ω j))
    (us : ∀ i, H ℝ (Ω i) 1) :
    ∃ u : H ℝ (⨆ i, Ω i) 1,
      ∀ i, P201Specs.Neumann.RestrictsTo (⨆ i, Ω i) (Ω i) u (us i) := by
  classical
  let U : Domain n := ⨆ i, Ω i
  let w : P102.U4.SobolevIndex n 1 → Lp ℝ U 2 := fun α => glueLp Ω (fun i => (us i).val α)
  have hwrep (i : Fin k) (α : P102.U4.SobolevIndex n 1) :
      (w α : Space n → ℝ) =ᵐ[domainMeasure (Ω i)] (us i).val α :=
    glueLp_restrict Ω hd (fun i => (us i).val α) i
  have hw : WithLp.toLp 2 w ∈ hilbertSubmodule ℝ U 1 := by
    change hilbertTupleToSum ℝ U 1 (WithLp.toLp 2 w) ∈ P102.U4.sobolevSubmodule ℝ U 1 2
    apply (P102.U4.mem_sobolevSubmodule_iff U 1 2 _).mpr
    intro α φ
    change P102.U4.lpTestPairing U 2 φ (w α) = (-1 : ℝ) ^ α.val.card *
      P102.U4.lpTestPairing U 2 (P102.U4.testPartialWord U (α.val.sort (· ≤ ·)) φ)
        (w (P102.U4.zeroSobolevIndex n 1))
    apply (P102.U4.distributionPartial_eq_regularLp_iff U 2 α.val _ _).mp ?_ φ
    let T := P102.U4.distributionPartial α.val
      (P102.U4.regularDistribution U (w (P102.U4.zeroSobolevIndex n 1))) -
      P102.U4.regularDistribution U (w α)
    have hlocal (i : Fin k) : P102.U4.VanishesOn T (Ω i) := by
      intro ψ hψ
      let ψi : P102.U4.TestSpace ℝ (Ω i) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩
      have he := congrArg (fun S : P102.U4.DistributionSpace ℝ (Ω i) => S ψi)
        (P102.U4.sobolev_derivative_distribution (Ω i) 1 2
          (hToW ℝ (Ω i) 1 (us i)) α)
      simp only [P102.U4.distributionPartial, smul_apply,
        ContinuousLinearMap.comp_apply, smul_eq_mul] at he ⊢
      change (-1 : ℝ) ^ α.val.card *
        P102.U4.regularDistribution U (w (P102.U4.zeroSobolevIndex n 1))
          (P102.U4.testPartialWord U (α.val.sort (· ≤ ·)) ψ) -
        P102.U4.regularDistribution U (w α) ψ = 0
      rw [regular_pairing_local U (Ω i) _ _ (hwrep i _) _
        ((P102.U4.testPartialWord_tsupport _ ψ).trans hψ),
        regular_pairing_local U (Ω i) _ _ (hwrep i α) ψ hψ]
      rw [P102.U4.regular_pairing n ℝ (Ω i) _
          (P102.U4.domainLp_locallyIntegrable (Ω i) 2 _),
        P102.U4.regular_pairing n ℝ (Ω i) _
          (P102.U4.domainLp_locallyIntegrable (Ω i) 2 _)] at he
      have htest : (P102.U4.testPartialWord U (α.val.sort (· ≤ ·)) ψ : Space n → ℝ) =
          P102.U4.testPartialWord (Ω i) (α.val.sort (· ≤ ·)) ψi := by
        rw [P102.U4.testPartialWord_coe, P102.U4.testPartialWord_coe]
        rfl
      rw [htest]
      exact sub_eq_zero.mpr he
    have hall := P102.U4.vanishesOn_iUnion T (fun i => (Ω i : Set (Space n)))
      (fun i => (Ω i).isOpen) hlocal
    apply sub_eq_zero.mp
    apply ContinuousLinearMap.ext
    intro ψ
    exact hall ψ (by simpa only [U, Opens.coe_iSup] using ψ.tsupport_subset)
  refine ⟨⟨WithLp.toLp 2 w, hw⟩, fun i => ⟨?_, fun j => ?_⟩⟩
  · exact hwrep i (P102.U4.zeroSobolevIndex n 1)
  · exact hwrep i ⟨{j}, by simp⟩


private lemma energy_zero_test {n : ℕ} (U : Domain n) (u : H ℝ U 1) :
    (∫ x in U, inner ℝ (hGradient u x) (hGradient (0 : H ℝ U 1) x)) = 0 := by
  rw [← energy_integral]
  exact map_zero _

private lemma forcing_zero_test {m : ℕ} (U : Domain (m + 1))
    (hU : IsBoundedLipschitzOpen U) (D : P201Specs.NormalTrace.TraceData U hU)
    (f : Lp ℝ U 2) (g : HminusHalf U hU) :
    ((∫ x in U, f x * hUnderlying U 1 (0 : H ℝ U 1) x) + g (D.trace 0)) = 0 := by
  rw [← forcing_apply]
  exact map_zero _

lemma union_solution_iff_components_aux {m k : ℕ} (Ω : Fin k → Domain (m + 1))
    (hΩ : ∀ i, IsBoundedLipschitzOpen (Ω i))
    (D : ∀ i, P201Specs.NormalTrace.TraceData (Ω i) (hΩ i))
    (f : ∀ i, Lp ℝ (Ω i) 2) (g : ∀ i, HminusHalf (Ω i) (hΩ i))
    (u : H ℝ (⨆ i, Ω i) 1) (us : ∀ i, H ℝ (Ω i) 1)
    (hu : ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) u (us i))
    (hglue : ∀ vs : ∀ i, H ℝ (Ω i) 1, ∃ v : H ℝ (⨆ i, Ω i) 1,
      ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) v (vs i))
    (he : ∀ (v : H ℝ (⨆ i, Ω i) 1) (vs : ∀ i, H ℝ (Ω i) 1),
      (∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) v (vs i)) →
      (∫ x in (⨆ i, Ω i : Domain (m + 1)), inner ℝ (hGradient u x) (hGradient v x)) =
        ∑ i, (∫ x in Ω i, inner ℝ (hGradient (us i) x) (hGradient (vs i) x))) :
    IsUnionSolution Ω hΩ D f g u ↔ ∀ i, IsSolution (D i) (f i) (g i) (us i) := by
  classical
  constructor
  · intro hsol i vi
    let vs : ∀ j, H ℝ (Ω j) 1 := Pi.single i vi
    obtain ⟨v, hv⟩ := hglue vs
    have hh := hsol.2 v vs hv
    rw [he v vs hv] at hh
    have hl : (∑ j, (∫ x in Ω j, inner ℝ (hGradient (us j) x) (hGradient (vs j) x))) =
        ∫ x in Ω i, inner ℝ (hGradient (us i) x) (hGradient vi x) := by
      rw [Finset.sum_eq_single i]
      · simp [vs]
      · intro j _ hji
        simp only [vs, Pi.single_eq_of_ne hji]
        exact energy_zero_test (Ω j) (us j)
      · simp
    have hr : (∑ j, ((∫ x in Ω j, f j x * hUnderlying (Ω j) 1 (vs j) x) +
        g j ((D j).trace (vs j)))) =
        (∫ x in Ω i, f i x * hUnderlying (Ω i) 1 vi x) + g i ((D i).trace vi) := by
      rw [Finset.sum_eq_single i]
      · simp [vs]
      · intro j _ hji
        simp only [vs, Pi.single_eq_of_ne hji]
        exact forcing_zero_test (Ω j) (hΩ j) (D j) (f j) (g j)
      · simp
    rwa [hl, hr] at hh
  · intro hs
    refine ⟨⟨us, hu⟩, ?_⟩
    intro v vs hv
    rw [he v vs hv]
    exact Finset.sum_congr rfl fun i _ => hs i (vs i)



lemma restrictsTo_difference_constant_iff {m : ℕ}
    (U V : Domain (m + 1))
    (hV : IsBoundedLipschitzOpen V)
    (u v : H ℝ U 1) (us vs : H ℝ V 1)
    (hu : RestrictsTo U V u us)
    (hv : RestrictsTo U V v vs) (c : ℝ) :
    ((fun x => P201Specs.hUnderlying U 1 u x -
      P201Specs.hUnderlying U 1 v x) =ᵐ[domainMeasure V] fun _ => c) ↔
      us = vs + constant V hV c := by
  constructor
  · intro h
    apply hilbertUnderlyingInjective V 1
    rw [map_add]
    apply Lp.ext
    filter_upwards [hu.1, hv.1, h,
      Lp.coeFn_add (P201Specs.hUnderlying V 1 vs)
        (P201Specs.hUnderlying V 1 (constant V hV c)),
      constant_underlying V hV c] with x hux hvx hx hadd hc
    rw [hadd, Pi.add_apply, hc]
    exact sub_eq_iff_eq_add'.mp (by rwa [hux, hvx] at hx)
  · intro h
    have he : P201Specs.hUnderlying V 1 us =
        P201Specs.hUnderlying V 1 vs + P201Specs.hUnderlying V 1 (constant V hV c) := by
      rw [h, map_add]
    filter_upwards [hu.1, hv.1,
      Lp.coeFn_add (P201Specs.hUnderlying V 1 vs)
        (P201Specs.hUnderlying V 1 (constant V hV c)),
      constant_underlying V hV c] with x hux hvx hadd hc
    rw [hux, hvx, he, hadd, Pi.add_apply, hc]
    exact add_sub_cancel_left _ _

lemma union_solution_constants_unique {m k : ℕ} (Ω : Fin k → Domain (m + 1))
    (hΩ : ∀ i, IsBoundedLipschitzOpen (Ω i))
    (hconn : ∀ i, IsConnected (Ω i : Set (Space (m + 1))))
    (D : ∀ i, P201Specs.NormalTrace.TraceData (Ω i) (hΩ i))
    (f : ∀ i, Lp ℝ (Ω i) 2) (g : ∀ i, HminusHalf (Ω i) (hΩ i))
    (u v : H ℝ (⨆ i, Ω i) 1) (us vs : ∀ i, H ℝ (Ω i) 1)
    (hu : ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) u (us i))
    (hv : ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) v (vs i))
    (hus : ∀ i, IsSolution (D i) (f i) (g i) (us i))
    (hvs : ∀ i, IsSolution (D i) (f i) (g i) (vs i)) :
    ∃! c : Fin k → ℝ, ∀ i,
      (fun x => P201Specs.hUnderlying (⨆ i, Ω i) 1 u x -
        P201Specs.hUnderlying (⨆ i, Ω i) 1 v x)
        =ᵐ[domainMeasure (Ω i)] fun _ => c i := by
  have he := fun i => solutions_differ (hconn i) (D i) (f i) (g i)
    (us i) (vs i) (hus i) (hvs i)
  choose c hc huniq using he
  refine ⟨c, ?_, ?_⟩
  · intro i
    exact (restrictsTo_difference_constant_iff (⨆ i, Ω i) (Ω i) (hΩ i)
      u v (us i) (vs i) (hu i) (hv i) (c i)).mpr (hc i)
  · intro d hd
    funext i
    exact huniq i (d i)
      ((restrictsTo_difference_constant_iff (⨆ i, Ω i) (Ω i) (hΩ i)
        u v (us i) (vs i) (hu i) (hv i) (d i)).mp (hd i))



/-- Testing the union equation is equivalent to testing separately on each
component: arbitrary component tests glue to an actual global H¹ class. -/
lemma union_solution_iff_components {m k : ℕ} (Ω : Fin k → Domain (m + 1))
    (hΩ : ∀ i, IsBoundedLipschitzOpen (Ω i))
    (hdisj : Pairwise fun i j => Disjoint (Ω i : Set (Space (m + 1))) (Ω j))
    (D : ∀ i, P201Specs.NormalTrace.TraceData (Ω i) (hΩ i))
    (f : ∀ i, Lp ℝ (Ω i) 2) (g : ∀ i, HminusHalf (Ω i) (hΩ i))
    (u : H ℝ (⨆ i, Ω i) 1) (us : ∀ i, H ℝ (Ω i) 1)
    (hu : ∀ i, RestrictsTo (⨆ i, Ω i) (Ω i) u (us i)) :
    IsUnionSolution Ω hΩ D f g u ↔ ∀ i, IsSolution (D i) (f i) (g i) (us i) :=
  union_solution_iff_components_aux Ω hΩ D f g u us hu
    (exists_gluing Ω hdisj)
    (fun v vs hv => union_energy_integral Ω hdisj u v us vs hu hv)

/-- The finite-component conclusion on the canonical Sobolev space of the
actual union. No regularity of the union boundary or separation of closures
is required; each component retains its own physical trace. -/
theorem finiteUnion : FiniteUnionStatement := by
  intro m k Ω hΩ hconn hdisj D
  constructor
  · intro v
    choose vs hvs using fun i =>
      exists_restriction (⨆ i, Ω i) (Ω i) (le_iSup Ω i) v
    exact ⟨vs, hvs⟩
  intro f g
  constructor
  · constructor
    · rintro ⟨u, hu⟩
      obtain ⟨us, hus⟩ := hu.1
      have hs := (union_solution_iff_components Ω hΩ hdisj D f g u us hus).mp hu
      intro i
      exact solution_compatible (Ω i) (hΩ i) (D i) (f i) (g i) (us i) (hs i)
    · intro hc
      obtain ⟨us, hus⟩ := (components Ω hΩ hconn hdisj D f g).1.mpr hc
      obtain ⟨u, hu⟩ := exists_gluing Ω hdisj us
      exact ⟨u, (union_solution_iff_components Ω hΩ hdisj D f g u us hu).mpr hus⟩
  · intro u v hu hv
    obtain ⟨us, hus⟩ := hu.1
    obtain ⟨vs, hvs⟩ := hv.1
    exact union_solution_constants_unique Ω hΩ hconn D f g u v us vs hus hvs
      ((union_solution_iff_components Ω hΩ hdisj D f g u us hus).mp hu)
      ((union_solution_iff_components Ω hΩ hdisj D f g v vs hvs).mp hv)

end P201.Neumann
