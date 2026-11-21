import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.LegendreHadamard
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace FourierTransform
open scoped Topology ContDiff

namespace VariationalNotes.Classical.LegendreHadamard
open LegendreHadamardData

/-- The determinant really is a quadratic form, not just homogeneous of degree two. -/
def determinantQuadratic : QuadraticForm ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  QuadraticMap.ofPolar Matrix.det
    (by intro a F; simp only [Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]; ring)
    (by intro F G H; simp [QuadraticMap.polar, Matrix.det_fin_two, Matrix.add_apply]; ring)
    (by intro a F G; simp [QuadraticMap.polar, Matrix.det_fin_two,
                          Matrix.add_apply, Matrix.smul_apply]; ring)

@[simp] theorem determinantQuadratic_apply (F : Matrix (Fin 2) (Fin 2) ℝ) :
    determinantQuadratic F = Matrix.det F := rfl

theorem determinant_outerMatrix (e b : Fin 2 → ℝ) :
    Matrix.det (outerMatrix e b) = 0 := by
  simp only [Matrix.det_fin_two, outerMatrix]
  ring

theorem determinantExample : LegendreHadamardSpec.determinantExampleType := by
  refine ⟨⟨determinantQuadratic, determinantQuadratic_apply⟩,
    determinant_outerMatrix, ?_, ?_, ?_⟩
  · intro F hF
    by_contra hdet
    have hfull := Matrix.rank_of_det_ne_zero hdet
    norm_num at hfull
    omega
  · exact ⟨1, by norm_num⟩
  · refine ⟨!![1, 0; 0, -1], ?_⟩
    norm_num [Matrix.det_fin_two]

@[simp] theorem rankOne_zero_left {d m : ℕ} (b : State d) :
    rankOne (0 : State m) b = 0 := by
  ext v
  simp [rankOne]

@[simp] theorem rankOne_zero_right {d m : ℕ} (e : State m) :
    rankOne e (0 : State d) = 0 := by
  ext v
  simp [rankOne]

@[simp] theorem gradientHessian_zero {d m : ℕ} (L : FieldLagrangian d m)
    (u : State d → State m) (x : State d) :
    gradientHessian L u x 0 0 = 0 := by
  change stateGradientHessian L u x 0 0 = 0
  simp

/-- The boundary cases need no nonzero-direction assumptions or regularity. -/
theorem necessity_zero_directions {d m : ℕ} (L : FieldLagrangian d m)
    (u : State d → State m) (x : State d) (e : State m) (b : State d)
    (h : e = 0 ∨ b = 0) :
    0 ≤ gradientHessian L u x (rankOne e b) (rankOne e b) := by
  rcases h with rfl | rfl <;> simp

/-- The operator model of e ⊗ b has the expected matrix coordinates. -/
theorem rankOne_coordinates (e b : State 2) :
    Matrix.toEuclideanLin.symm (rankOne e b) = outerMatrix e b := by
  rw [rankOne, InnerProductSpace.symm_toEuclideanLin_rankOne]
  ext i j
  simp [Matrix.vecMulVec, outerMatrix]

/-- Compactly supported smooth tests have smooth scalar multiples with the same
allowed support. -/
theorem smoothTest_smul {d m : ℕ} {Ω : Set (State d)}
    {η : State d → State m} (hη : smoothTest Ω η) (s : ℝ) :
    smoothTest Ω (s • η) := by
  refine ⟨hη.1.const_smul s, hη.2.1.smul_left, ?_⟩
  exact (tsupport_smul_subset_right (fun _ : State d => s) η).trans hη.2.2

/-- At an interior point the derivative of a perturbed field is the sum of
its actual derivatives; no choice of extension outside Ω enters this formula. -/
theorem graphPoint_add_smul {d m : ℕ} {Ω : Set (State d)} (hΩ : IsOpen Ω)
    {u η : State d → State m} (hu : ContDiffOn ℝ 1 u Ω)
    (hη : ContDiff ℝ ∞ η) (s : ℝ) {x : State d} (hx : x ∈ Ω) :
    LegendreHadamardData.graphPoint (u + s • η) x =
      (x, u x + s • η x, fderiv ℝ u x + s • fderiv ℝ η x) := by
  have hu' : DifferentiableAt ℝ u x :=
    (hu.differentiableOn (by norm_num) x hx).differentiableAt (hΩ.mem_nhds hx)
  have hη' : DifferentiableAt ℝ η x := (hη.differentiable (by simp)).differentiableAt
  simp only [LegendreHadamardData.graphPoint, Pi.add_apply, Pi.smul_apply,
    fderiv_add hu' (hη'.const_smul s), fderiv_const_smul hη' s]

/-- The support is compact, so sufficiently small parameters keep the perturbed
graph in any prescribed open neighborhood of the original graph. -/
theorem eventually_graphAdmissible {d m : ℕ} {Ω : Set (State d)} (hΩ : IsOpen Ω)
    (L : FieldLagrangian d m) {u η : State d → State m}
    (hu : ContDiffOn ℝ 1 u Ω) (hη : smoothTest Ω η)
    (hadm : LegendreHadamardData.graphAdmissible L Ω u) :
    ∀ᶠ s : ℝ in 𝓝 0, LegendreHadamardData.graphAdmissible L Ω (u + s • η) := by
  have h0 : ∀ T : Gradient d m, (0 : ℝ) • T = 0 := by
    intro T
    ext v
    simp
  have hs0 : ∀ s : ℝ, s • (0 : Gradient d m) = 0 := by
    intro s
    ext v
    simp
  have hDu := hu.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hDη := hη.1.continuous_fderiv (by simp)
  have hcomp : ∀ᶠ s : ℝ in 𝓝 0, ∀ x ∈ tsupport η,
      (x, u x + s • η x, fderiv ℝ u x + s • fderiv ℝ η x) ∈ L.domain := by
    apply hη.2.1.eventually_forall_of_forall_eventually
    intro x hx
    have hxu := hu.continuousOn.continuousAt (hΩ.mem_nhds (hη.2.2 hx))
    have hxDu := hDu.continuousAt (hΩ.mem_nhds (hη.2.2 hx))
    have hc : ContinuousAt (fun p : ℝ × State d =>
        (p.2, u p.2 + p.1 • η p.2,
          fderiv ℝ u p.2 + p.1 • fderiv ℝ η p.2)) (0, x) :=
      continuousAt_snd.prodMk
        ((hxu.comp continuousAt_snd).add
          (continuousAt_fst.smul (hη.1.continuous.continuousAt.comp continuousAt_snd)) |>.prodMk
        ((hxDu.comp continuousAt_snd).add
          (continuousAt_fst.smul (hDη.continuousAt.comp continuousAt_snd))))
    apply hc.eventually
    apply L.isOpen_domain.mem_nhds
    simpa only [h0, zero_smul, add_zero, LegendreHadamardData.graphPoint] using hadm x (hη.2.2 hx)
  filter_upwards [hcomp] with s hs x hx
  rw [graphPoint_add_smul hΩ hu hη.1 s hx]
  by_cases hxK : x ∈ tsupport η
  · exact hs x hxK
  · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hxK
    have hDz : fderiv ℝ η x = 0 := fderiv_of_notMem_tsupport ℝ hxK
    simpa only [hz, hDz, hs0, smul_zero, add_zero, LegendreHadamardData.graphPoint] using hadm x hx

/-- Uniform C¹ smallness along each fixed smooth compactly supported direction. -/
theorem eventually_test_small {d m : ℕ} {Ω : Set (State d)}
    {η : State d → State m} (hη : smoothTest Ω η) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ x ∈ Ω, ‖((s • η) x, fderiv ℝ (s • η) x)‖ < ε := by
  have h0 : ∀ T : Gradient d m, (0 : ℝ) • T = 0 := by
    intro T
    ext v
    simp
  have hDη := hη.1.continuous_fderiv (by simp)
  have hcomp : ∀ᶠ s : ℝ in 𝓝 0, ∀ x ∈ tsupport η,
      ‖(s • η x, s • fderiv ℝ η x)‖ < ε := by
    apply hη.2.1.eventually_forall_of_forall_eventually
    intro x hx
    have hc : ContinuousAt (fun p : ℝ × State d =>
        ‖(p.1 • η p.2, p.1 • fderiv ℝ η p.2)‖) (0, x) :=
      ((continuousAt_fst.smul (hη.1.continuous.continuousAt.comp continuousAt_snd)).prodMk
        (continuousAt_fst.smul (hDη.continuousAt.comp continuousAt_snd))).norm
    have hz : ‖((0 : ℝ) • η x, (0 : ℝ) • fderiv ℝ η x)‖ < ε := by
      simpa only [h0, zero_smul, Prod.mk_zero_zero, norm_zero] using hε
    exact hc.eventually (isOpen_Iio.mem_nhds hz)
  filter_upwards [hcomp] with s hs x hx
  rw [fderiv_const_smul ((hη.1.differentiable (by simp)).differentiableAt) s]
  by_cases hxK : x ∈ tsupport η
  · exact hs x hxK
  · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hxK
    have hDz : fderiv ℝ η x = 0 := fderiv_of_notMem_tsupport ℝ hxK
    simpa [hz, hDz]

/-- A scalar second derivative at a continuous two-sided local minimum is
nonnegative. The totalized derivative causes no extra assumption here. -/
theorem second_derivative_nonnegative {f : ℝ → ℝ} {a : ℝ}
    (hmin : IsLocalMin f a) (hc : ContinuousAt f a) :
    0 ≤ deriv (deriv f) a := by
  by_contra h
  have hn : deriv (deriv f) a < 0 := lt_of_not_ge h
  have hmax := isLocalMax_of_deriv_deriv_neg hn hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hmin, hmax] with x hx hy
    exact le_antisymm hy hx
  have hzero : deriv (deriv f) a = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  exact hn.ne hzero

/-- On a compact spatial set, joint continuity of the parameter derivative
supplies the uniform domination needed for differentiation under the integral. -/
theorem hasDerivAt_setIntegral_compact {d : ℕ} {K : Set (State d)}
    (hK : IsCompact K) {F F₁ : ℝ → State d → ℝ} {a l r : ℝ} (ha : a ∈ Ioo l r)
    (hF : ContinuousOn (fun p : ℝ × State d => F p.1 p.2) (Icc l r ×ˢ K))
    (hF₁ : ContinuousOn (fun p : ℝ × State d => F₁ p.1 p.2) (Icc l r ×ˢ K))
    (hd : ∀ x ∈ K, ∀ s ∈ Ioo l r, HasDerivAt (fun t => F t x) (F₁ s x) s) :
    HasDerivAt (fun s => ∫ x in K, F s x) (∫ x in K, F₁ a x) a := by
  have hcF (s : ℝ) (hs : s ∈ Icc l r) : ContinuousOn (F s) K :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun x hx => ⟨hs, hx⟩)
  have hcF₁ : ContinuousOn (F₁ a) K :=
    hF₁.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => ⟨Ioo_subset_Icc_self ha, hx⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF₁
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Ioo_mem_nhds ha.1 ha.2)
    (Filter.Eventually.mono (Ioo_mem_nhds ha.1 ha.2) (fun s hs =>
        ((hcF s (Ioo_subset_Icc_self hs)).integrableOn_compact hK).aestronglyMeasurable))
    ((hcF a (Ioo_subset_Icc_self ha)).integrableOn_compact hK)
    (hcF₁.integrableOn_compact hK).aestronglyMeasurable
    ?_ (integrableOn_const hK.measure_ne_top) ?_).2
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx s hs
    exact hC (s, x) ⟨Ioo_subset_Icc_self hs, hx⟩
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx s hs
    exact hd x hx s hs

/-- A second derivative under an integral on a compact set, with all domination
provided by the stated continuity hypotheses. -/
theorem second_derivative_setIntegral_compact {d : ℕ} {K : Set (State d)}
    (hK : IsCompact K) {F F₁ F₂ : ℝ → State d → ℝ} {a l r : ℝ}
    (ha : a ∈ Ioo l r)
    (hF : ContinuousOn (fun p : ℝ × State d => F p.1 p.2) (Icc l r ×ˢ K))
    (hF₁ : ContinuousOn (fun p : ℝ × State d => F₁ p.1 p.2) (Icc l r ×ˢ K))
    (hF₂ : ContinuousOn (fun p : ℝ × State d => F₂ p.1 p.2) (Icc l r ×ˢ K))
    (hd₁ : ∀ x ∈ K, ∀ s ∈ Ioo l r, HasDerivAt (fun t => F t x) (F₁ s x) s)
    (hd₂ : ∀ x ∈ K, ∀ s ∈ Ioo l r, HasDerivAt (fun t => F₁ t x) (F₂ s x) s) :
    deriv (deriv (fun s => ∫ x in K, F s x)) a = ∫ x in K, F₂ a x := by
  have heq : deriv (fun s => ∫ x in K, F s x) =ᶠ[𝓝 a]
      (fun s => ∫ x in K, F₁ s x) := by
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with s hs
    exact (hasDerivAt_setIntegral_compact hK hs hF hF₁ hd₁).deriv
  rw [heq.deriv_eq]
  exact (hasDerivAt_setIntegral_compact hK ha hF₁ hF₂ hd₂).deriv

/-- Differentiating in the second variable retains joint regularity. -/
theorem partial_fderiv_contDiffAt
    {X V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : X × V → W} {p : X × V} {k n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hkn : k + 1 ≤ n) :
    ContDiffAt ℝ k (fun q : X × V => fderiv ℝ (fun v => f (q.1, v)) q.2) p := by
  apply ContDiffAt.fderiv (f := fun q : X × V => fun v => f (q.1, v))
    (g := fun q => q.2) ?_ contDiffAt_snd hkn
  exact hf.comp (p, p.2) ((contDiffAt_fst.fst).prodMk contDiffAt_snd)

/-- The same joint regularity statement on an open domain. -/
theorem partial_fderiv_contDiffOn
    {X V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : X × V → W} {U : Set (X × V)} {k n : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hkn : k + 1 ≤ n) :
    ContDiffOn ℝ k (fun q : X × V => fderiv ℝ (fun v => f (q.1, v)) q.2) U := by
  intro p hp
  exact (partial_fderiv_contDiffAt (hf.contDiffAt (hU.mem_nhds hp)) hkn).contDiffWithinAt

-- These abbreviations expose the inherited normed structures during synthesis
-- of the doubly curried operator space.
local instance jetNormedGroup (d m : ℕ) : NormedAddCommGroup (StateGradient d m) := inferInstance
local instance jetNormedSpace (d m : ℕ) : NormedSpace ℝ (StateGradient d m) := inferInstance
local instance jetDualNormedGroup (d m : ℕ) :
    NormedAddCommGroup (StateGradient d m →L[ℝ] ℝ) := inferInstance
local instance jetDualNormedSpace (d m : ℕ) :
    NormedSpace ℝ (StateGradient d m →L[ℝ] ℝ) := inferInstance

/-- Only continuity of u and Du is used to obtain continuity of the Hessian
along the graph; no second derivative of u is required. -/
theorem stateGradientHessian_continuousOn {d m : ℕ} {Ω : Set (State d)}
    (hΩ : IsOpen Ω) (L : FieldLagrangian d m) {u : State d → State m}
    (hu : ContDiffOn ℝ 1 u Ω) (hreg : LegendreHadamardData.regularNearGraph L Ω u) :
    ContinuousOn (stateGradientHessian L u) Ω := by
  obtain ⟨U, hU, hgraph, _, hL⟩ := hreg
  have hD := partial_fderiv_contDiffOn hU hL (k := 1) (by norm_num)
  have hDD := partial_fderiv_contDiffOn hU hD (k := 0) (by norm_num)
  exact hDD.continuousOn.comp
    (continuousOn_id.prodMk (hu.continuousOn.prodMk
      (hu.continuousOn_fderiv_of_isOpen hΩ (by norm_num)))) hgraph

/-- A whole closed parameter interval of perturbed graphs lies in the original
C² neighborhood, even when the full domain and graph are unbounded. -/
theorem exists_graph_tube {d m : ℕ} {Ω : Set (State d)} (hΩ : IsOpen Ω)
    {u η : State d → State m} (hu : ContDiffOn ℝ 1 u Ω) (hη : smoothTest Ω η)
    {U : Set (State d × StateGradient d m)} (hU : IsOpen U)
    (hgraph : ∀ x ∈ Ω, LegendreHadamardData.graphPoint u x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (-r) r, ∀ x ∈ Ω,
      (x, (u x, fderiv ℝ u x) + s • (η x, fderiv ℝ η x)) ∈ U := by
  let L' : FieldLagrangian d m := ⟨U, hU, fun _ => 0⟩
  have hev := eventually_graphAdmissible hΩ L' hu hη hgraph
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ / 2, by linarith, ?_⟩
  intro s hs x hx
  have hsb : s ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hg := hball hsb x hx
  rw [graphPoint_add_smul hΩ hu hη.1 s hx] at hg
  exact hg

/-- Twice differentiating a locally C² integrand along continuous affine fibers
on a compact spatial set requires no spatial derivatives of the base fiber. -/
theorem second_derivative_affine_integral {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set (State d)} (hK : IsCompact K)
    {f : State d × V → ℝ} {U : Set (State d × V)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {z w : State d → V} (hz : ContinuousOn z K) (hw : ContinuousOn w K)
    {r : ℝ} (hr : 0 < r)
    (htube : ∀ s ∈ Icc (-r) r, ∀ x ∈ K, (x, z x + s • w x) ∈ U) :
    DifferentiableAt ℝ (fun s : ℝ => ∫ x in K, f (x, z x + s • w x)) 0 ∧
    deriv (deriv (fun s : ℝ => ∫ x in K, f (x, z x + s • w x))) 0 =
      ∫ x in K, fderiv ℝ (fderiv ℝ (fun v => f (x, v))) (z x) (w x) (w x) := by
  let D : State d × V → V →L[ℝ] ℝ :=
    fun p => fderiv ℝ (fun v => f (p.1, v)) p.2
  let H : State d × V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun p => fderiv ℝ (fun v => D (p.1, v)) p.2
  let T : ℝ × State d → State d × V := fun p => (p.2, z p.2 + p.1 • w p.2)
  let F : ℝ → State d → ℝ := fun s x => f (T (s, x))
  let F₁ : ℝ → State d → ℝ := fun s x => D (T (s, x)) (w x)
  let F₂ : ℝ → State d → ℝ := fun s x => H (T (s, x)) (w x) (w x)
  have hD : ContDiffOn ℝ 1 D U := partial_fderiv_contDiffOn hU hf (by norm_num)
  have hH : ContDiffOn ℝ 0 H U := partial_fderiv_contDiffOn hU hD (by norm_num)
  have hT : ContinuousOn T (Icc (-r) r ×ˢ K) :=
    continuousOn_snd.prodMk
      ((hz.comp continuousOn_snd (fun p hp => hp.2)).add
        (continuousOn_fst.smul (hw.comp continuousOn_snd (fun p hp => hp.2))))
  have hTU : MapsTo T (Icc (-r) r ×ˢ K) U := fun p hp => htube p.1 hp.1 p.2 hp.2
  have hw' : ContinuousOn (fun p : ℝ × State d => w p.2) (Icc (-r) r ×ˢ K) :=
    hw.comp continuousOn_snd (fun p hp => hp.2)
  have hF : ContinuousOn (fun p : ℝ × State d => F p.1 p.2) (Icc (-r) r ×ˢ K) :=
    hf.continuousOn.comp hT hTU
  have hF₁ : ContinuousOn (fun p : ℝ × State d => F₁ p.1 p.2) (Icc (-r) r ×ˢ K) :=
    (hD.continuousOn.comp hT hTU).clm_apply hw'
  have hF₂ : ContinuousOn (fun p : ℝ × State d => F₂ p.1 p.2) (Icc (-r) r ×ˢ K) :=
    ((hH.continuousOn.comp hT hTU).clm_apply hw').clm_apply hw'
  have hd₁ : ∀ x ∈ K, ∀ s ∈ Ioo (-r) r,
      HasDerivAt (fun t => F t x) (F₁ s x) s := by
    intro x hx s hs
    have hfs : ContDiffAt ℝ 2 (fun v => f (x, v)) (z x + s • w x) :=
      (hf.contDiffAt (hU.mem_nhds (htube s (Ioo_subset_Icc_self hs) x hx))).comp
        (z x + s • w x) (contDiffAt_const.prodMk contDiffAt_id)
    have ht : HasDerivAt (fun t : ℝ => z x + t • w x) (w x) s := by
      simpa only [one_smul, id_eq] using (((hasDerivAt_id s).smul_const (w x)).const_add (z x))
    exact (hfs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s ht
  have hd₂ : ∀ x ∈ K, ∀ s ∈ Ioo (-r) r,
      HasDerivAt (fun t => F₁ t x) (F₂ s x) s := by
    intro x hx s hs
    have hfs : ContDiffAt ℝ 1 (fun v => D (x, v)) (z x + s • w x) :=
      (hD.contDiffAt (hU.mem_nhds (htube s (Ioo_subset_Icc_self hs) x hx))).comp
        (z x + s • w x) (contDiffAt_const.prodMk contDiffAt_id)
    have ht : HasDerivAt (fun t : ℝ => z x + t • w x) (w x) s := by
      simpa only [one_smul, id_eq] using (((hasDerivAt_id s).smul_const (w x)).const_add (z x))
    have hcomp := (hfs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s ht
    simpa only [ContinuousLinearMap.map_zero, add_zero, Function.comp_apply, F₁, F₂, H, T] using
      hcomp.clm_apply (hasDerivAt_const s (w x))
  have hfirst := hasDerivAt_setIntegral_compact hK
    (show (0 : ℝ) ∈ Ioo (-r) r from ⟨by linarith, hr⟩) hF hF₁ hd₁
  have hresult := second_derivative_setIntegral_compact hK
    (show (0 : ℝ) ∈ Ioo (-r) r from ⟨by linarith, hr⟩) hF hF₁ hF₂ hd₁ hd₂
  refine ⟨hfirst.differentiableAt, ?_⟩
  simpa only [F, F₂, T, H, D, zero_smul, add_zero] using hresult


/-- A compactly supported perturbation changes only the compact part of a finite
energy. The integral over the rest of Ω is retained as an actual finite integral. -/
theorem energy_add_smul_eq {d m : ℕ} {Ω : Set (State d)} (hΩ : IsOpen Ω)
    (L : FieldLagrangian d m) {u η : State d → State m}
    (hu : ContDiffOn ℝ 1 u Ω) (hη : smoothTest Ω η) (hE : finiteEnergy L Ω u)
    (s : ℝ)
    (hK : IntegrableOn
      (fun x => L.value (x, (u x, fderiv ℝ u x) + s • (η x, fderiv ℝ η x))) (tsupport η)) :
    energy L Ω (u + s • η) =
      (∫ x in tsupport η, L.value (x, (u x, fderiv ℝ u x) + s • (η x, fderiv ℝ η x))) +
      ∫ x in Ω \ tsupport η, L.value (LegendreHadamardData.graphPoint u x) := by
  have heq : ∀ x ∈ Ω \ tsupport η,
      LegendreHadamardData.graphPoint (u + s • η) x = LegendreHadamardData.graphPoint u x := by
    intro x hx
    rw [graphPoint_add_smul hΩ hu hη.1 s hx.1]
    have hz := image_eq_zero_of_notMem_tsupport hx.2
    have hDz := fderiv_of_notMem_tsupport ℝ hx.2
    have hs0 : s • (0 : Gradient d m) = 0 := by ext; simp
    simp only [hz, hDz, hs0, smul_zero, add_zero, LegendreHadamardData.graphPoint]
  have hK' : IntegrableOn (fun x => L.value (LegendreHadamardData.graphPoint (u + s • η) x))
      (tsupport η) := hK.congr_fun (fun x hx => by
        rw [graphPoint_add_smul hΩ hu hη.1 s (hη.2.2 hx)]; rfl) (isClosed_tsupport η).measurableSet
  have hrest : IntegrableOn (fun x => L.value (LegendreHadamardData.graphPoint (u + s • η) x))
      (Ω \ tsupport η) :=
    (hE.mono_set sdiff_subset).congr_fun (fun x hx => by rw [heq x hx])
      (hΩ.measurableSet.diff (isClosed_tsupport η).measurableSet)
  have hunion : tsupport η ∪ (Ω \ tsupport η) = Ω := by
    ext x
    simp only [mem_union, Set.mem_sdiff]
    exact ⟨fun hx => hx.elim (fun h => hη.2.2 h) And.left, fun hx => by
      by_cases h : x ∈ tsupport η
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩⟩
  unfold energy
  nth_rw 1 [← hunion]
  rw [
    setIntegral_union disjoint_sdiff_right
      (hΩ.measurableSet.diff (isClosed_tsupport η).measurableSet) hK' hrest]
  congr 1
  · apply setIntegral_congr_fun (isClosed_tsupport η).measurableSet
    intro x hx
    change L.value (LegendreHadamardData.graphPoint (u + s • η) x) = _
    rw [graphPoint_add_smul hΩ hu hη.1 s (hη.2.2 hx)]
    rfl
  · apply setIntegral_congr_fun (hΩ.measurableSet.diff (isClosed_tsupport η).measurableSet)
    intro x hx
    change L.value (LegendreHadamardData.graphPoint (u + s • η) x) = _
    rw [heq x hx]


/-- A compactly supported smooth perturbation has finite energy whenever its
integrand is integrable on the support and the original field has finite energy. -/
theorem finiteEnergy_add_smul {d m : ℕ} {Ω : Set (State d)} (hΩ : IsOpen Ω)
    (L : FieldLagrangian d m) {u η : State d → State m}
    (hu : ContDiffOn ℝ 1 u Ω) (hη : smoothTest Ω η) (hE : finiteEnergy L Ω u)
    (s : ℝ)
    (hK : IntegrableOn
      (fun x => L.value (x, (u x, fderiv ℝ u x) + s • (η x, fderiv ℝ η x)))
      (tsupport η)) : finiteEnergy L Ω (u + s • η) := by
  have heq : ∀ x ∈ Ω \ tsupport η,
      LegendreHadamardData.graphPoint (u + s • η) x = LegendreHadamardData.graphPoint u x := by
    intro x hx
    rw [graphPoint_add_smul hΩ hu hη.1 s hx.1]
    have hz := image_eq_zero_of_notMem_tsupport hx.2
    have hDz := fderiv_of_notMem_tsupport ℝ hx.2
    have hs0 : s • (0 : Gradient d m) = 0 := by ext; simp
    simp only [hz, hDz, hs0, smul_zero, add_zero, LegendreHadamardData.graphPoint]
  have hK' : IntegrableOn
      (fun x => L.value (LegendreHadamardData.graphPoint (u + s • η) x)) (tsupport η) :=
    hK.congr_fun (fun x hx => by
      rw [graphPoint_add_smul hΩ hu hη.1 s (hη.2.2 hx)]; rfl)
      (isClosed_tsupport η).measurableSet
  have hrest : IntegrableOn
      (fun x => L.value (LegendreHadamardData.graphPoint (u + s • η) x))
      (Ω \ tsupport η) :=
    (hE.mono_set sdiff_subset).congr_fun (fun x hx => by rw [heq x hx])
      (hΩ.measurableSet.diff (isClosed_tsupport η).measurableSet)
  have hunion : tsupport η ∪ (Ω \ tsupport η) = Ω := by
    ext x
    simp only [mem_union, Set.mem_sdiff]
    exact ⟨fun hx => hx.elim (fun h => hη.2.2 h) And.left, fun hx => by
      by_cases h : x ∈ tsupport η
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩⟩
  exact hunion ▸ hK'.union hrest

/-- Local graph regularity preserves finite energy along each sufficiently small
compactly supported smooth perturbation. -/
theorem eventually_finiteEnergy_add_smul {d m : ℕ} {Ω : Set (State d)}
    (hΩ : IsOpen Ω) (L : FieldLagrangian d m) {u η : State d → State m}
    (hu : ContDiffOn ℝ 1 u Ω) (hη : smoothTest Ω η)
    (hreg : LegendreHadamardData.regularNearGraph L Ω u) (hE : finiteEnergy L Ω u) :
    ∀ᶠ s : ℝ in 𝓝 0, finiteEnergy L Ω (u + s • η) := by
  obtain ⟨U, hU, hgraph, _, hL⟩ := hreg
  obtain ⟨r, hr, htube⟩ := exists_graph_tube hΩ hu hη hU hgraph
  let z : State d → StateGradient d m := fun x => (u x, fderiv ℝ u x)
  let w : State d → StateGradient d m := fun x => (η x, fderiv ℝ η x)
  have hz : ContinuousOn z (tsupport η) :=
    (hu.continuousOn.prodMk
      (hu.continuousOn_fderiv_of_isOpen hΩ (by norm_num))).mono hη.2.2
  have hw : Continuous w := hη.1.continuous.prodMk (hη.1.continuous_fderiv (by simp))
  filter_upwards [Ioo_mem_nhds (by linarith : -r < 0) hr] with s hs
  apply finiteEnergy_add_smul hΩ L hu hη hE s
  exact (hL.continuousOn.comp
    (continuousOn_id.prodMk (hz.add (hw.continuousOn.const_smul s)))
    (fun x hx => htube s (Ioo_subset_Icc_self hs) x (hη.2.2 hx)))
    |>.integrableOn_compact hη.2.1

/-- The original C¹ local-minimum hypothesis gives a genuine two-sided scalar
minimum in every smooth compactly supported direction. -/
theorem weakLocalMinimum_direction {d m : ℕ} {Ω : Set (State d)} (hΩ : IsOpen Ω)
    (L : FieldLagrangian d m) {u η : State d → State m}
    (hu : ContDiffOn ℝ 1 u Ω) (hη : smoothTest Ω η)
    (hreg : LegendreHadamardData.regularNearGraph L Ω u) (hE : finiteEnergy L Ω u)
    (hmin : LegendreHadamardData.weakLocalMinimum L Ω u) :
    IsLocalMin (fun s : ℝ => energy L Ω (u + s • η)) 0 := by
  obtain ⟨hadm, ε, hε, hmin⟩ := hmin
  have ha := eventually_graphAdmissible hΩ L hu hη hadm
  have hs := eventually_test_small hη hε
  have hfinite := eventually_finiteEnergy_add_smul hΩ L hu hη hreg hE
  filter_upwards [ha, hs, hfinite] with s has hsmall hfinite
  simpa only [zero_smul, add_zero] using hmin (s • η) (smoothTest_smul hη s) has hfinite hsmall


/-- Nonnegative second variation under precisely the original local regularity
and finite-energy assumptions. -/
theorem nonnegative_secondVariation {d m : ℕ} {Ω : Set (State d)} (hΩ : IsOpen Ω)
    (L : FieldLagrangian d m) {u η : State d → State m}
    (hu : ContDiffOn ℝ 1 u Ω) (hreg : LegendreHadamardData.regularNearGraph L Ω u)
    (hE : finiteEnergy L Ω u) (hmin : LegendreHadamardData.weakLocalMinimum L Ω u)
    (hη : smoothTest Ω η) :
    IntegrableOn (fun x => stateGradientHessian L u x
      (η x, fderiv ℝ η x) (η x, fderiv ℝ η x)) Ω ∧
    0 ≤ ∫ x in Ω, stateGradientHessian L u x
      (η x, fderiv ℝ η x) (η x, fderiv ℝ η x) := by
  obtain ⟨U, hU, hgraph, hUL, hL⟩ := hreg
  obtain ⟨r, hr, htube⟩ := exists_graph_tube hΩ hu hη hU hgraph
  let z : State d → StateGradient d m := fun x => (u x, fderiv ℝ u x)
  let w : State d → StateGradient d m := fun x => (η x, fderiv ℝ η x)
  let F : ℝ → ℝ := fun s => ∫ x in tsupport η, L.value (x, z x + s • w x)
  let Q : State d → ℝ := fun x => stateGradientHessian L u x (w x) (w x)
  have hzΩ : ContinuousOn z Ω :=
    hu.continuousOn.prodMk (hu.continuousOn_fderiv_of_isOpen hΩ (by norm_num))
  have hw : Continuous w := hη.1.continuous.prodMk (hη.1.continuous_fderiv (by simp))
  have hz : ContinuousOn z (tsupport η) := hzΩ.mono hη.2.2
  have hK (s : ℝ) (hs : s ∈ Icc (-r) r) :
      IntegrableOn (fun x => L.value (x, z x + s • w x)) (tsupport η) :=
    (hL.continuousOn.comp
      (continuousOn_id.prodMk (hz.add (hw.continuousOn.const_smul s)))
      (fun x hx => htube s hs x (hη.2.2 hx))).integrableOn_compact hη.2.1
  have heqE (s : ℝ) (hs : s ∈ Icc (-r) r) :
      energy L Ω (u + s • η) = F s +
        ∫ x in Ω \ tsupport η, L.value (LegendreHadamardData.graphPoint u x) :=
    energy_add_smul_eq hΩ L hu hη hE s (hK s hs)
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have hminF : IsLocalMin F 0 := by
    filter_upwards [weakLocalMinimum_direction hΩ L hu hη ⟨U, hU, hgraph, hUL, hL⟩ hE hmin,
      Ioo_mem_nhds (by linarith : -r < 0) hr] with s hs hsr
    rw [heqE 0 h0, heqE s (Ioo_subset_Icc_self hsr)] at hs
    exact (add_le_add_iff_right _).mp hs
  have hderiv := second_derivative_affine_integral hη.2.1 hU hL hz hw.continuousOn hr
    (fun s hs x hx => htube s hs x (hη.2.2 hx))
  have hQpos : 0 ≤ ∫ x in tsupport η, Q x := by
    have hnonneg := second_derivative_nonnegative hminF hderiv.1.continuousAt
    rw [hderiv.2] at hnonneg
    exact hnonneg
  have hQzero : ∀ x ∈ Ω \ tsupport η, Q x = 0 := by
    intro x hx
    have hzη := image_eq_zero_of_notMem_tsupport hx.2
    have hDη := fderiv_of_notMem_tsupport ℝ hx.2
    simp only [Q, w, hzη, hDη, Prod.mk_zero_zero, map_zero]
  have hQcont : ContinuousOn Q Ω :=
    ((stateGradientHessian_continuousOn hΩ L hu ⟨U, hU, hgraph, hUL, hL⟩).clm_apply
      hw.continuousOn).clm_apply hw.continuousOn
  have hQint := (hQcont.mono hη.2.2).integrableOn_compact (μ := volume) hη.2.1
  refine ⟨hQint.of_forall_sdiff_eq_zero hΩ.measurableSet hQzero, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hη.2.2 hQzero]
  exact hQpos




/-- Nonnegative testing against squares of smooth scalar test functions detects
pointwise positivity of a continuous coefficient on an open set. -/
theorem nonneg_of_integral_sq_mul_nonneg {d : ℕ} {Ω : Set (State d)}
    (hΩ : IsOpen Ω) {q : State d → ℝ} (hq : ContinuousOn q Ω)
    (htest : ∀ χ : State d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Ω → 0 ≤ ∫ x in Ω, (χ x) ^ 2 * q x) :
    ∀ x ∈ Ω, 0 ≤ q x := by
  intro x hx
  by_contra hneg
  have hxneg : q x < 0 := lt_of_not_ge hneg
  have hs : Ω ∩ q ⁻¹' Iio 0 ∈ 𝓝 x :=
    inter_mem (hΩ.mem_nhds hx)
      ((hq.continuousAt (hΩ.mem_nhds hx)).preimage_mem_nhds (Iio_mem_nhds hxneg))
  obtain ⟨χ, hχs, hχc, hχd, _, hχx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hs
  have hχΩ : tsupport χ ⊆ Ω := fun y hy => (hχs hy).1
  let f : State d → ℝ := fun y => χ y * χ y * (-q y)
  have hfs : tsupport f ⊆ tsupport χ :=
    (tsupport_mul_subset_left).trans (tsupport_mul_subset_left)
  have hfcOn : ContinuousOn f Ω :=
    (hχd.continuous.continuousOn.mul hχd.continuous.continuousOn).mul hq.neg
  have hfc : Continuous f :=
    hfcOn.continuous_of_tsupport_subset hΩ (hfs.trans hχΩ)
  have hfcomp : HasCompactSupport f :=
    (hχc.mul_right (f' := χ)).mul_right (f' := fun y => -q y)
  have hfnonneg : 0 ≤ f := by
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact mul_nonneg (mul_self_nonneg _) (neg_nonneg.mpr (le_of_lt (hχs hy).2))
    · simp [f, image_eq_zero_of_notMem_tsupport hy]
  have hfx : f x ≠ 0 := by
    simp [f, hχx, ne_of_lt hxneg]
  have hfpos : 0 < ∫ y, f y :=
    hfc.integral_pos_of_hasCompactSupport_nonneg_nonzero hfcomp hfnonneg hfx
  have hfeq : (∫ y in Ω, f y) = ∫ y, f y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy =>
      image_eq_zero_of_notMem_tsupport (fun h => hy ((hfs.trans hχΩ) h)))
  have htest' := htest χ hχd hχc hχΩ
  have hnegint : (∫ y in Ω, f y) = -(∫ y in Ω, (χ y)^2 * q y) := by
    simp only [f, pow_two, mul_neg, integral_neg]
  rw [hfeq] at hnegint
  linarith




theorem tendsto_integral_cos_inner {d : ℕ} {b : State d} (hb : b ≠ 0)
    {g : State d → ℝ} (hg : Integrable g) :
    Tendsto (fun k : ℝ => ∫ x, g x * Real.cos (2 * k * inner ℝ b x))
      atTop (𝓝 0) := by
  let v : State d := (-(Real.pi⁻¹)) • b
  have hv : v ≠ 0 := smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero Real.pi_ne_zero)) hb
  have hray : Tendsto (fun k : ℝ => k • v) atTop (cocompact (State d)) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : State d)
    simp only [dist_zero_right, norm_smul, Real.norm_eq_abs]
    exact tendsto_abs_atTop_atTop.atTop_mul_const (norm_pos_iff.mpr hv)
  have hf := (tendsto_integral_exp_inner_smul_cocompact
    (fun x : State d => (g x : ℂ))).comp hray
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hf
  simp only [Complex.zero_re] at hre
  convert hre using 1
  funext k
  dsimp only [Function.comp_def]
  change _ = RCLike.re (∫ x : State d, 𝐞 (-inner ℝ x (k • v)) • (g x : ℂ))
  rw [← integral_re ((Real.fourierIntegral_convergent_iff (k • v)).2 hg.ofReal)]
  apply integral_congr_ae
  filter_upwards [] with x
  change _ = (𝐞 (-inner ℝ x (k • v)) • (g x : ℂ) : ℂ).re
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  rw [mul_comm (g x)]
  congr 2
  simp only [v, real_inner_smul_right, real_inner_comm x b]
  field_simp

theorem tendsto_integral_cos_sq_inner {d : ℕ} {b : State d} (hb : b ≠ 0)
    {g : State d → ℝ} (hg : Integrable g) :
    Tendsto (fun k : ℝ => ∫ x, g x * Real.cos (k * inner ℝ b x) ^ 2)
      atTop (𝓝 ((1 / 2 : ℝ) * ∫ x, g x)) := by
  have hosc (k : ℝ) : Integrable (fun x => g x * Real.cos (2 * k * inner ℝ b x)) := by
    apply hg.mul_bdd (c := 1)
    · exact (by fun_prop : Continuous (fun x : State d => Real.cos (2 * k * inner ℝ b x))).aestronglyMeasurable
    · exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * k * inner ℝ b x))
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ) * ∫ x, g x)).add ((tendsto_integral_cos_inner hb hg).div_const 2)
  convert h using 1
  · funext k
    have hid : (fun x : State d => g x * Real.cos (k * inner ℝ b x) ^ 2) =
        (fun x => (1 / 2 : ℝ) * g x + (g x * Real.cos (2 * k * inner ℝ b x)) / 2) := by
      funext x
      rw [Real.cos_sq]
      ring_nf
    rw [hid, integral_add (hg.const_mul _) ((hosc k).div_const 2),
      integral_const_mul, integral_div]
  · simp

theorem tendsto_integral_cos_inner_nat {d : ℕ} {b : State d} (hb : b ≠ 0)
    {g : State d → ℝ} (hg : Integrable g) :
    Tendsto (fun n : ℕ => ∫ x, g x * Real.cos (2 * (n : ℝ) * inner ℝ b x))
      atTop (𝓝 0) := by
  exact (tendsto_integral_cos_inner hb hg).comp tendsto_natCast_atTop_atTop

theorem tendsto_integral_cos_sq_inner_nat {d : ℕ} {b : State d} (hb : b ≠ 0)
    {g : State d → ℝ} (hg : Integrable g) :
    Tendsto (fun n : ℕ => ∫ x, g x * Real.cos ((n : ℝ) * inner ℝ b x) ^ 2)
      atTop (𝓝 ((1 / 2 : ℝ) * ∫ x, g x)) := by
  exact (tendsto_integral_cos_sq_inner hb hg).comp tendsto_natCast_atTop_atTop




theorem quadratic_sub_norm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    ‖A v v - A w w‖ ≤ ‖A‖ * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  have heq : A v v - A w w = A (v - w) v + A w (v - w) := by
    simp only [map_sub, sub_apply]
    ring
  rw [heq]
  calc
    _ ≤ ‖A (v - w) v‖ + ‖A w (v - w)‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖v - w‖ * ‖v‖ + ‖A‖ * ‖w‖ * ‖v - w‖ :=
      add_le_add (A.le_opNorm₂ _ _) (A.le_opNorm₂ _ _)
    _ = _ := by ring

theorem tendsto_quadratic_integral_sub {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set (State d)} (hK : IsCompact K)
    {A : State d → V →L[ℝ] V →L[ℝ] ℝ} (hA : ContinuousOn A K)
    {v w : ℕ → State d → V}
    (hv : ∀ n, ContinuousOn (v n) K) (hw : ∀ n, ContinuousOn (w n) K)
    {C : ℝ} (hC : 0 ≤ C)
    (hvb : ∀ n x, x ∈ K → ‖v n x‖ ≤ C)
    (hwb : ∀ n x, x ∈ K → ‖w n x‖ ≤ C)
    (hlim : ∀ x ∈ K, Tendsto (fun n => v n x - w n x) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ x in K, A x (v n x) (v n x)) -
      ∫ x in K, A x (w n x) (w n x)) atTop (𝓝 0) := by
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn hA
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hAb x (hx : x ∈ K) : ‖A x‖ ≤ M := (hM₀ x hx).trans (le_max_left _ _)
  have hdiff n x (hx : x ∈ K) : ‖v n x - w n x‖ ≤ C + C :=
    (norm_sub_le _ _).trans (add_le_add (hvb n x hx) (hwb n x hx))
  have hbound n x (hx : x ∈ K) :
      ‖A x (v n x) (v n x) - A x (w n x) (w n x)‖ ≤
        M * (C + C) * ‖v n x - w n x‖ := by
    apply (quadratic_sub_norm_le _ _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (hAb x hx) (add_le_add (hvb n x hx) (hwb n x hx))
      (by positivity) hM
  have hcont n : ContinuousOn (fun x => A x (v n x) (v n x) - A x (w n x) (w n x)) K :=
    ((hA.clm_apply (hv n)).clm_apply (hv n)).sub ((hA.clm_apply (hw n)).clm_apply (hw n))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict K) (f := fun _ : State d => (0 : ℝ))
    (fun _ => M * (C + C) * (C + C))
    (fun n => ((hcont n).integrableOn_compact hK).aestronglyMeasurable)
    (integrableOn_const hK.measure_ne_top)
    (fun n => ?_) ?_
  · simpa only [integral_zero] using ht.congr' (Eventually.of_forall (fun n =>
      (integral_sub (((hA.clm_apply (hv n)).clm_apply (hv n)).integrableOn_compact hK)
        (((hA.clm_apply (hw n)).clm_apply (hw n)).integrableOn_compact hK))))
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (hbound n x hx).trans (mul_le_mul_of_nonneg_left (hdiff n x hx) (by positivity))
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    apply squeeze_zero_norm (fun n => hbound n x hx)
    simpa only [norm_zero, mul_zero] using
      (tendsto_const_nhds.mul ((hlim x hx).norm) :
        Tendsto (fun n => M * (C + C) * ‖v n x - w n x‖) atTop (𝓝 (M * (C + C) * ‖(0 : V)‖)))



/-- Smooth compactly supported oscillatory rank-one variation. -/
def oscillatoryTest {d m : ℕ} (χ : State d → ℝ) (e : State m) (b : State d)
    (k : ℝ) (x : State d) : State m :=
  (k⁻¹ * (χ x * Real.sin (k * inner ℝ b x))) • e

/-- The derivative of the cutoff term in the oscillatory variation. -/
def cutoffGradient {d m : ℕ} (χ : State d → ℝ) (e : State m) (x : State d) :
    Gradient d m := (fderiv ℝ χ x).smulRight e

theorem oscillatoryTest_tsupport_subset {d m : ℕ} (χ : State d → ℝ)
    (e : State m) (b : State d) (k : ℝ) :
    tsupport (oscillatoryTest χ e b k) ⊆ tsupport χ :=
  (tsupport_smul_subset_left _ _).trans
    (tsupport_mul_subset_right.trans tsupport_mul_subset_left)

theorem oscillatoryTest_smoothTest {d m : ℕ} {Ω : Set (State d)}
    {χ : State d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (e : State m) (b : State d) (k : ℝ) :
    smoothTest Ω (oscillatoryTest χ e b k) := by
  have hphase : ContDiff ℝ ∞ (fun x : State d => k * inner ℝ b x) :=
    contDiff_const.mul (innerSL ℝ b).contDiff
  have hsm : ContDiff ℝ ∞ (oscillatoryTest χ e b k) :=
    (contDiff_const.mul (hχ.mul hphase.sin)).smul contDiff_const
  have hsub := oscillatoryTest_tsupport_subset χ e b k
  refine ⟨hsm, ?_, hsub.trans hχΩ⟩
  exact hχK.of_isClosed_subset (isClosed_tsupport _) hsub

theorem oscillatoryTest_fderiv {d m : ℕ} {χ : State d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (e : State m) (b : State d) {k : ℝ} (hk : k ≠ 0)
    (x : State d) :
    fderiv ℝ (oscillatoryTest χ e b k) x =
      (χ x * Real.cos (k * inner ℝ b x)) • rankOne e b +
        (k⁻¹ * Real.sin (k * inner ℝ b x)) • cutoffGradient χ e x := by
  have hphase : HasFDerivAt (fun y : State d => k * inner ℝ b y)
      (k • innerSL ℝ b) x := (innerSL ℝ b).hasFDerivAt.const_mul k
  have h := (((hχ.differentiable (by simp)).differentiableAt.hasFDerivAt.mul
    hphase.sin).const_mul k⁻¹).smul_const e
  change HasFDerivAt (oscillatoryTest χ e b k) _ x at h
  rw [h.fderiv]
  ext v : 1
  simp only [ContinuousLinearMap.smulRight_apply, add_apply,
    smul_apply, rankOne, InnerProductSpace.rankOne_apply,
    cutoffGradient, smul_smul, smul_eq_mul, innerSL_apply_apply, ← add_smul]
  congr 1
  field_simp [hk]

/-- Full state–gradient jet of the oscillatory variation. -/
def oscillatoryJet {d m : ℕ} (χ : State d → ℝ) (e : State m) (b : State d)
    (k : ℝ) (x : State d) : StateGradient d m :=
  (oscillatoryTest χ e b k x, fderiv ℝ (oscillatoryTest χ e b k) x)

/-- Its leading, purely gradient, rank-one jet. -/
def oscillatoryPrincipalJet {d m : ℕ} (χ : State d → ℝ) (e : State m)
    (b : State d) (k : ℝ) (x : State d) : StateGradient d m :=
  (0, (χ x * Real.cos (k * inner ℝ b x)) • rankOne e b)

theorem oscillatoryJet_sub_principal {d m : ℕ} {χ : State d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (e : State m) (b : State d) {k : ℝ} (hk : k ≠ 0)
    (x : State d) :
    oscillatoryJet χ e b k x - oscillatoryPrincipalJet χ e b k x =
      (k⁻¹ * Real.sin (k * inner ℝ b x)) • (χ x • e, cutoffGradient χ e x) := by
  apply Prod.ext
  · change oscillatoryTest χ e b k x - 0 = _
    simp only [oscillatoryTest, sub_zero, Prod.smul_fst, smul_smul]
    congr 1
    ring
  · change fderiv ℝ (oscillatoryTest χ e b k) x - _ = _
    rw [oscillatoryTest_fderiv hχ e b hk x]
    change _ + _ - ((χ x * Real.cos (k * inner ℝ b x)) • rankOne e b) = _
    exact add_sub_cancel_left _ _

theorem oscillatoryJet_error_bound {d m : ℕ} {χ : State d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (e : State m) (b : State d) {k : ℝ} (hk : k ≠ 0)
    (x : State d) :
    ‖oscillatoryJet χ e b k x - oscillatoryPrincipalJet χ e b k x‖ ≤
      |k⁻¹| * ‖(χ x • e, cutoffGradient χ e x)‖ := by
  rw [oscillatoryJet_sub_principal hχ e b hk x, norm_smul, Real.norm_eq_abs,
    abs_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)) (norm_nonneg _)

theorem oscillatoryPrincipalJet_bound {d m : ℕ} (χ : State d → ℝ)
    (e : State m) (b : State d) (k : ℝ) (x : State d) :
    ‖oscillatoryPrincipalJet χ e b k x‖ ≤ ‖χ x‖ * ‖rankOne e b‖ := by
  simp only [oscillatoryPrincipalJet, Prod.norm_mk, norm_zero]
  rw [max_eq_right (norm_nonneg _), norm_smul, Real.norm_eq_abs, abs_mul]
  rw [Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)) (norm_nonneg _)

theorem oscillatoryJet_continuous {d m : ℕ} {χ : State d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (e : State m) (b : State d) (k : ℝ) :
    Continuous (oscillatoryJet χ e b k) := by
  have hphase : ContDiff ℝ ∞ (fun x : State d => k * inner ℝ b x) :=
    contDiff_const.mul (innerSL ℝ b).contDiff
  have hsm : ContDiff ℝ ∞ (oscillatoryTest χ e b k) :=
    (contDiff_const.mul (hχ.mul hphase.sin)).smul contDiff_const
  exact hsm.continuous.prodMk (hsm.continuous_fderiv (by simp))

theorem oscillatoryPrincipalJet_continuous {d m : ℕ} {χ : State d → ℝ}
    (hχ : Continuous χ) (e : State m) (b : State d) (k : ℝ) :
    Continuous (oscillatoryPrincipalJet χ e b k) := by
  exact continuous_const.prodMk
    ((hχ.mul (Real.continuous_cos.comp (continuous_const.mul (innerSL ℝ b).continuous))).smul continuous_const)

/-- Pointwise convergence of the error uses only the elementary sine bound. -/
theorem oscillatoryJet_error_tendsto {d m : ℕ} {χ : State d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (e : State m) (b : State d) (x : State d) :
    Filter.Tendsto (fun n : ℕ => oscillatoryJet χ e b ((n : ℝ) + 1) x -
      oscillatoryPrincipalJet χ e b ((n : ℝ) + 1) x) Filter.atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => oscillatoryJet_error_bound hχ e b
    (ne_of_gt (Nat.cast_add_one_pos n)) x)
  have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1))
  simpa only [abs_zero, zero_mul] using
    ht.abs.mul_const ‖(χ x • e, cutoffGradient χ e x)‖

/-- Both the full and principal jets admit a common bound on every compact set. -/
theorem oscillatoryJets_uniform_bound {d m : ℕ} {χ : State d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {K : Set (State d)} (hK : IsCompact K)
    (e : State m) (b : State d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : State d), x ∈ K →
      ‖oscillatoryJet χ e b ((n : ℝ) + 1) x‖ ≤ C ∧
      ‖oscillatoryPrincipalJet χ e b ((n : ℝ) + 1) x‖ ≤ C := by
  have hcut : Continuous (fun x : State d => (χ x • e, cutoffGradient χ e x)) := by
    refine (hχ.continuous.smul continuous_const).prodMk ?_
    exact (((ContinuousLinearMap.smulRightL ℝ (State d) (State m)).continuous.comp
      (hχ.continuous_fderiv (by simp))).clm_apply continuous_const)
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hcut.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hχ.continuous.continuousOn
  let A' := max 0 A
  let B' := max 0 B * ‖rankOne e b‖
  have hA' : 0 ≤ A' := le_max_left _ _
  have hB' : 0 ≤ B' := mul_nonneg (le_max_left _ _) (norm_nonneg _)
  refine ⟨A' + B', add_nonneg hA' hB', ?_⟩
  intro n x hx
  have hp : ‖oscillatoryPrincipalJet χ e b ((n : ℝ) + 1) x‖ ≤ B' :=
    (oscillatoryPrincipalJet_bound χ e b _ x).trans
      (mul_le_mul_of_nonneg_right ((hB x hx).trans (le_max_right _ _)) (norm_nonneg _))
  have hinv : |((n : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (Nat.cast_add_one_pos n))]
    exact inv_le_one_of_one_le₀ (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have he : ‖oscillatoryJet χ e b ((n : ℝ) + 1) x -
      oscillatoryPrincipalJet χ e b ((n : ℝ) + 1) x‖ ≤ A' :=
    (oscillatoryJet_error_bound hχ e b (ne_of_gt (Nat.cast_add_one_pos n)) x).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hinv).trans
        ((hA x hx).trans (le_max_right _ _)))
  constructor
  · calc
      ‖oscillatoryJet χ e b ((n : ℝ) + 1) x‖ =
          ‖(oscillatoryJet χ e b ((n : ℝ) + 1) x -
            oscillatoryPrincipalJet χ e b ((n : ℝ) + 1) x) +
            oscillatoryPrincipalJet χ e b ((n : ℝ) + 1) x‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hp)
  · exact hp.trans (le_add_of_nonneg_left hA')



/-- Oscillatory compact tests extract precisely the rank-one part of any
continuous nonnegative second-variation form. -/
theorem rankOne_nonneg_of_secondVariation {d m : ℕ} {Ω : Set (State d)}
    (hΩ : IsOpen Ω)
    {A : State d → StateGradient d m →L[ℝ] StateGradient d m →L[ℝ] ℝ}
    (hA : ContinuousOn A Ω)
    (hQ : ∀ η : State d → State m, smoothTest Ω η →
      0 ≤ ∫ x in Ω, A x (η x, fderiv ℝ η x) (η x, fderiv ℝ η x))
    (e : State m) {b : State d} (hb : b ≠ 0) :
    ∀ x ∈ Ω, 0 ≤ A x (0, rankOne e b) (0, rankOne e b) := by
  let R : StateGradient d m := (0, rankOne e b)
  have hq : ContinuousOn (fun x => A x R R) Ω :=
    (hA.clm_apply continuousOn_const).clm_apply continuousOn_const
  apply nonneg_of_integral_sq_mul_nonneg hΩ hq
  intro χ hχ hχK hχΩ
  let K := tsupport χ
  let k : ℕ → ℝ := fun n => (n : ℝ) + 1
  let v : ℕ → State d → StateGradient d m := fun n => oscillatoryJet χ e b (k n)
  let w : ℕ → State d → StateGradient d m := fun n => oscillatoryPrincipalJet χ e b (k n)
  let g : State d → ℝ := fun x => χ x * χ x * A x R R
  have hgs : tsupport g ⊆ K :=
    tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hgcOn : ContinuousOn g Ω :=
    (hχ.continuous.continuousOn.mul hχ.continuous.continuousOn).mul hq
  have hgc : Continuous g := hgcOn.continuous_of_tsupport_subset hΩ (hgs.trans hχΩ)
  have hgK : HasCompactSupport g := (hχK.mul_right (f' := χ)).mul_right
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgK
  have hwQ (n : ℕ) :
      (∫ x in K, A x (w n x) (w n x)) =
      ∫ x, g x * Real.cos (k n * inner ℝ b x)^2 := by
    have heq : (fun x => A x (w n x) (w n x)) =
        (fun x => g x * Real.cos (k n * inner ℝ b x)^2) := by
      funext x
      have hwR : w n x = (χ x * Real.cos (k n * inner ℝ b x)) • R := by
        apply Prod.ext
        · simp only [w, oscillatoryPrincipalJet, R, Prod.smul_fst, smul_zero]
        · rfl
      rw [hwR]
      simp only [map_smul, smul_apply, smul_eq_mul, g, pow_two]
      ring
    rw [heq]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [g, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hwlim : Tendsto (fun n => ∫ x in K, A x (w n x) (w n x)) atTop
      (𝓝 ((1 / 2 : ℝ) * ∫ x in Ω, (χ x)^2 * A x R R)) := by
    have ht := (tendsto_integral_cos_sq_inner hb hgi).comp
      (by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1))
    have hgΩ : (∫ x, g x) = ∫ x in Ω, (χ x)^2 * A x R R := by
      symm
      simp only [pow_two]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      change g x = 0
      exact image_eq_zero_of_notMem_tsupport (f := g) (fun hs => hx ((hgs.trans hχΩ) hs))
    rw [hgΩ] at ht
    exact ht.congr (fun n => (hwQ n).symm)
  have hvnonneg (n : ℕ) : 0 ≤ ∫ x in K, A x (v n x) (v n x) := by
    have hη := oscillatoryTest_smoothTest hχ hχK hχΩ e b (k n)
    have hηK := oscillatoryTest_smoothTest hχ hχK (subset_refl K) e b (k n)
    have hzero : ∀ x ∈ Ω \ K, A x (v n x) (v n x) = 0 := by
      intro x hx
      have hxη : x ∉ tsupport (oscillatoryTest χ e b (k n)) :=
        fun hs => hx.2 (hηK.2.2 hs)
      simp only [v, oscillatoryJet, image_eq_zero_of_notMem_tsupport hxη,
        fderiv_of_notMem_tsupport ℝ hxη, Prod.mk_zero_zero, map_zero]
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hχΩ hzero]
    exact hQ _ hη
  obtain ⟨C, hC, hbnd⟩ := oscillatoryJets_uniform_bound hχ hχK e b
  have herror := tendsto_quadratic_integral_sub hχK (hA.mono hχΩ)
    (fun n => (oscillatoryJet_continuous hχ e b (k n)).continuousOn)
    (fun n => (oscillatoryPrincipalJet_continuous hχ.continuous e b (k n)).continuousOn)
    hC (fun n x hx => (hbnd n x hx).1) (fun n x hx => (hbnd n x hx).2) (fun x hx => oscillatoryJet_error_tendsto hχ e b x)
  change Tendsto (fun n => (∫ x in K, A x (v n x) (v n x)) -
    ∫ x in K, A x (w n x) (w n x)) atTop (𝓝 0) at herror
  have hvlim := herror.add hwlim
  simp only [sub_add_cancel, zero_add] at hvlim
  have hpos := le_of_tendsto_of_tendsto tendsto_const_nhds hvlim
    (Eventually.of_forall hvnonneg)
  linarith

/-- Legendre–Hadamard necessity on an arbitrary open domain, with only local
C² integrand regularity and finite base energy. -/
theorem necessity : LegendreHadamardSpec.necessityType := by
  intro d m Ω hΩ L u hu hreg hE hmin x hx e b
  by_cases hb : b = 0
  · simp [hb]
  · exact rankOne_nonneg_of_secondVariation hΩ
      (stateGradientHessian_continuousOn hΩ L hu hreg)
      (fun η hη => (nonnegative_secondVariation hΩ L hu hreg hE hmin hη).2)
      e hb x hx

end VariationalNotes.Classical.LegendreHadamard
