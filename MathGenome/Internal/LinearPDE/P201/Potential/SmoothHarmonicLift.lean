import MathGenome.Internal.LinearPDE.P201Specs.Potential.SmoothHarmonicLift
import MathGenome.Internal.LinearPDE.P201.Elliptic.WeakDirichlet
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import MathGenome.Internal.LinearPDE.P201.Elliptic.GlobalH2
import MathGenome.Internal.LinearPDE.P201.Potential.Weyl
import MathGenome.Internal.LinearPDE.P201.Potential.WeakHarmonicBoundary
import MathGenome.Internal.LinearPDE.P201.Common.SobolevScalars

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise

namespace P201.SmoothHarmonicLift
open P201Specs.SmoothHarmonicLift

/-- The identity coefficient has the exact ellipticity constant one. -/
theorem identity_elliptic {n : ℕ} (Ω : Domain n) :
    P201Specs.Dirichlet.Elliptic Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) 1 := by
  filter_upwards [] with x ξ
  rw [EuclideanSpace.norm_sq_eq]
  simp [Matrix.one_apply, pow_two]


/-- Affine Lax–Milgram for the identity coefficient on any bounded open set.
This statement is independent of pointwise boundary regularity. -/
theorem weak_lift_of_h1 {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (G₀ : Space n → ℝ)
    (G : H ℝ Ω 1) (hG : (hUnderlying Ω 1 G : Space n → ℝ)
      =ᵐ[domainMeasure Ω] G₀) :
    ∃ u : H ℝ Ω 1, IsWeakLift Ω G₀ u ∧
      ∀ v : H ℝ Ω 1, IsWeakLift Ω G₀ v → v = u := by
  let A : P201Specs.Dirichlet.MatrixField n := fun _ => 1
  have hA : MemLp A ∞ (domainMeasure Ω) := memLp_top_const _
  obtain ⟨C, hC, _, hform⟩ := Dirichlet.form_bridge hn Ω hb
  obtain ⟨B, hB, hBound, hCoercive⟩ := hform A hA
  obtain ⟨z, hz, _, hUnique⟩ := Dirichlet.solve_affine_form Ω B C 1
    (C * P201Specs.Dirichlet.CoefficientNorm Ω A) hC (by norm_num)
    (mul_nonneg hC.le ENNReal.toReal_nonneg) hBound
    (hCoercive 1 (by norm_num) (identity_elliptic Ω)) 0 G
  have hAffine (y : H10 ℝ Ω) : InAffineClass Ω G₀ (G + y.val) := by
    refine ⟨y, ?_⟩
    filter_upwards [hG, Lp.coeFn_add (hUnderlying Ω 1 G) (hUnderlying Ω 1 y.val)]
      with x hx hadd
    change hUnderlying Ω 1 (G + y.val) x = G₀ x + hUnderlying Ω 1 y.val x
    rw [map_add, hadd, Pi.add_apply, hx]
  refine ⟨G + z.val, ⟨hAffine z, ?_⟩, ?_⟩
  · intro v
    exact (hB _ _).symm.trans (hz v)
  · intro v hv
    obtain ⟨y, hy⟩ := hv.1
    have hvG : v = G + y.val := by
      apply hilbertUnderlyingInjective Ω 1
      apply Lp.ext
      filter_upwards [hy, hG,
        Lp.coeFn_add (hUnderlying Ω 1 G) (hUnderlying Ω 1 y.val)] with x hxy hxG hadd
      change hUnderlying Ω 1 v x = hUnderlying Ω 1 (G + y.val) x
      rw [map_add, hadd, Pi.add_apply, hxG]
      exact hxy
    rw [hvG]
    congr 1
    apply congrArg Subtype.val
    apply hUnique y
    intro φ
    exact (hB _ _).trans (by simpa [A, ← hvG] using hv.2 φ)

/-- Continuous functions on the compact closure have an L² bulk class.
No regularity is required of their ambient values outside the closure. -/
theorem continuousOn_closure_memLp {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (hb : Bornology.IsBounded (Ω : Set (Space n)))
    {f : Space n → 𝕜} (hf : ContinuousOn f (closure (Ω : Set _))) :
    MemLp f 2 (domainMeasure Ω) := by
  have hc : IsCompact (closure (Ω : Set (Space n))) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hb.closure⟩
  letI : IsFiniteMeasure (domainMeasure Ω) :=
    ⟨by
      simpa [domainMeasure, P201Specs.domainMeasure] using
        (measure_mono (μ := volume) subset_closure).trans_lt hc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hc.bddAbove_image hf.norm
  apply MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet) C
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC ⟨x, subset_closure hx, rfl⟩

/-- A smooth lift near a bounded closure defines an actual Hᵏ class, for
all finite orders. The weak derivatives are the classical coordinate partials. -/
theorem smooth_hilbert_representative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (f : Space n → 𝕜) (hf : SmoothOnClosure Ω f) (k : ℕ) :
    ∃ u : H 𝕜 Ω k, (hUnderlying Ω k u : Space n → 𝕜) =ᵐ[domainMeasure Ω] f := by
  obtain ⟨U, hU, hsub, hdiff⟩ := hf
  have hΩU : (Ω : Set (Space n)) ⊆ U := subset_closure.trans hsub
  have h0 := continuousOn_closure_memLp Ω hb (hdiff.continuousOn.mono hsub)
  have hα (α : MultiIndex n) : MemLp (multiPartial f α) 2 (domainMeasure Ω) := by
    have hfinite : ContDiffOn ℝ (α.card : ℕ) f U := hdiff.of_le (by simp)
    have hd : ContDiffOn ℝ (0 : ℕ) (multiPartial f α) U :=
      P102.U4.partialWord_contDiffOn ⟨U, hU⟩
        hfinite
        (α.sort (· ≤ ·)) 0 (by simp)
    exact continuousOn_closure_memLp Ω hb (hd.continuousOn.mono hsub)
  have heq (g : Space n → 𝕜) (hg : MemLp g 2 (domainMeasure Ω)) :
      regularDistribution Ω (hg.toLp g) = regularDistribution Ω g := by
    apply (P102.U4.regular_injectivity n 𝕜 Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _) (locallyIntegrableOn_of_locallyIntegrable_restrict
        (hg.locallyIntegrable (by norm_num)))).mpr
    exact hg.coeFn_toLp
  have hder : P102.U4.HasSobolevDerivatives Ω k 2 (h0.toLp f) := by
    intro α hcard
    refine ⟨(hα α).toLp (multiPartial f α), ?_⟩
    change distributionDerivative α (regularDistribution Ω (h0.toLp f)) =
      regularDistribution Ω ((hα α).toLp (multiPartial f α))
    rw [heq f h0, heq (multiPartial f α) (hα α)]
    apply P102.U4.derivative_classicalCompatibility n 𝕜 Ω α f
    exact (hdiff.of_le (by simp)).mono hΩU
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range Ω k 2) (h0.toLp f)).mpr hder
  refine ⟨(hToW 𝕜 Ω k).symm w, ?_⟩
  have hh : hUnderlying Ω k ((hToW 𝕜 Ω k).symm w) = h0.toLp f := by
    change P102.U4.sobolevUnderlying ((hToW 𝕜 Ω k) ((hToW 𝕜 Ω k).symm w)) = _
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  rw [hh]
  exact h0.coeFn_toLp

/-- The real affine weak solution exists for the source's smooth data,
without assuming a Sobolev representative as an extra hypothesis. -/
theorem weak_lift_of_smooth {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (G₀ : Space n → ℝ)
    (hG : SmoothOnClosure Ω G₀) :
    ∃ u : H ℝ Ω 1, IsWeakLift Ω G₀ u ∧
      ∀ v : H ℝ Ω 1, IsWeakLift Ω G₀ v → v = u := by
  obtain ⟨G, hG⟩ := smooth_hilbert_representative Ω hb G₀ hG 1
  exact weak_lift_of_h1 hn Ω hb G₀ G hG

open P102.Sobolev.Geometry P102.U4.GraphPieces in
/-- Shrinking a graph chart preserves its actual one-sided domain geometry. -/
def shrinkBoundaryChart {m : ℕ} {S : Set (P102.U4.GraphPieces.Ambient m)}
    (C : P102.Sobolev.Geometry.BoundaryChart S) (r : ℝ)
    (hr : 0 < r) (hrr : r ≤ C.radius) : P102.Sobolev.Geometry.BoundaryChart S where
  frame := C.frame
  center := C.center
  radius := r
  height := C.height
  radius_pos := hr
  height_pos := C.height_pos
  graphFunction := C.graphFunction
  constant := C.constant
  graph_lipschitz := C.graph_lipschitz.mono (ball_subset_ball hrr)
  side := by
    have hi : Function.Injective (shear C.graphFunction) :=
      fun x y h => by
        have := congrArg (unshear C.graphFunction) h
        simpa only [P102.Sobolev.Geometry.unshear_shear] using this
    ext x
    constructor
    · rintro ⟨hx, y, ⟨v, hv, rfl⟩, rfl⟩
      have hlarge : C.frame (shear C.graphFunction v) ∈
          chartImage C.frame C.graphFunction C.center C.radius C.height :=
        ⟨_, ⟨v, ⟨(ball_subset_ball hrr) hv.1, hv.2⟩, rfl⟩, rfl⟩
      have hm := C.side.subset ⟨hx, hlarge⟩
      obtain ⟨w, ⟨z, hz, hzw⟩, hw⟩ := hm
      have hzv : z = v := hi (hzw.trans (C.frame.injective hw))
      subst z
      exact ⟨_, ⟨v, ⟨hv.1, hz.2⟩, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      have hm : C.frame (shear C.graphFunction v) ∈
          C.frame '' (shear C.graphFunction '' upperCylinder C.center C.radius C.height) :=
        ⟨_, ⟨v, ⟨(ball_subset_ball hrr) hv.1, hv.2⟩, rfl⟩, rfl⟩
      refine ⟨(C.side.symm.subset hm).1, ?_⟩
      exact ⟨_, ⟨v, ⟨hv.1, ⟨lt_trans (neg_neg_of_pos C.height_pos) hv.2.1, hv.2.2⟩⟩,
        rfl⟩, rfl⟩
  boundary := by
    ext x
    constructor
    · rintro ⟨hx, y, ⟨v, hv, rfl⟩, rfl⟩
      have hlarge : C.frame (shear C.graphFunction v) ∈
          chartImage C.frame C.graphFunction C.center C.radius C.height :=
        ⟨_, ⟨v, ⟨(ball_subset_ball hrr) hv.1, hv.2⟩, rfl⟩, rfl⟩
      obtain ⟨w, ⟨z, hz, hzw⟩, hw⟩ := C.boundary.subset ⟨hx, hlarge⟩
      have hzv : z = v.ofLp.1 := by
        have he := hzw.trans (C.frame.injective hw)
        exact congrArg (fun q : P102.U4.GraphPieces.Ambient m => q.ofLp.1) he
      exact ⟨w, ⟨z, hzv.symm ▸ hv.1, hzw⟩, hw⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      have hm : C.frame (graph C.graphFunction z) ∈
          C.frame '' (graph C.graphFunction '' ball C.center C.radius) :=
        ⟨_, ⟨z, (ball_subset_ball hrr) hz, rfl⟩, rfl⟩
      refine ⟨(C.boundary.symm.subset hm).1, ?_⟩
      refine ⟨_, ⟨WithLp.toLp 2 (z, (0 : ℝ)), ?_, ?_⟩, rfl⟩
      · exact ⟨hz, ⟨neg_neg_of_pos C.height_pos, C.height_pos⟩⟩
      · simp [shear, graph]

/-- Every C² boundary is C¹,¹ in the exact shared chart representation.
The first derivative is locally Lipschitz, so the original chart is shrunk. -/
theorem c2_boundary_is_c11 {m : ℕ} (Ω : Domain (m + 1))
    (hc : HasCkBoundary Ω 2) : HasC11Boundary Ω := by
  intro p hp
  obtain ⟨C, hCp, hC⟩ := hc p hp
  have hcenter : C.center ∈ ball C.center C.radius := mem_ball_self C.radius_pos
  have hd := hC.contDiffAt (isOpen_ball.mem_nhds hcenter)
  obtain ⟨L, V, hV, hL⟩ :=
    (hd.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  let r := min C.radius δ
  have hr : 0 < r := lt_min C.radius_pos hδ
  refine ⟨shrinkBoundaryChart C r hr (min_le_left _ _), hCp, ?_, L, ?_⟩
  · exact (hC.of_le (by norm_num)).mono (ball_subset_ball (min_le_left _ _))
  · exact hL.mono ((ball_subset_ball (min_le_right _ _)).trans hδV)

/-- Agreement of the identity-matrix energy with the Euclidean weak-gradient
pairing, for actual Sobolev classes. -/
theorem identity_energy {n : ℕ} (Ω : Domain n) (u v : H ℝ Ω 1) :
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u v =
      ∫ x in Ω, inner ℝ (hGradient u x) (hGradient v x) := by
  change (∫ x in Ω, ∑ i, ∑ j,
    (1 : Matrix (Fin n) (Fin n) ℝ) i j * hFirstDerivative u j x *
      star (hFirstDerivative v i x)) = _
  apply integral_congr_ae
  filter_upwards [Dirichlet.gradient_ae Ω u, Dirichlet.gradient_ae Ω v] with x hu hv
  rw [hu, hv]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- The variational harmonic equation tests every compact smooth function,
with the same identity operator used by the H² theorem. -/
theorem weak_harmonic_equation {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (hu : WeakHarmonic Ω u) :
    P201Specs.InteriorH2.WeakEquation Ω
      (fun _ => ContinuousLinearMap.id ℝ (Space n)) u (0 : Lp ℝ Ω 2) := by
  intro φ
  obtain ⟨v, hv⟩ := InteriorTesting.exists_test_class Ω φ
  have hg := InteriorTesting.smooth_gradient_ae Ω v.val φ hv
  have he : (∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x)) = 0 := by
    calc
      _ = ∫ x in Ω, inner ℝ (hGradient u x) (hGradient v.val x) :=
        integral_congr_ae (hg.mono fun x hx =>
          congrArg (fun q : Space n => inner ℝ (hGradient u x) q) hx.symm)
      _ = ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) u v.val :=
        (identity_energy Ω u v.val).symm
      _ = 0 := hu v
  change (∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x)) = _
  rw [he]
  symm
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with x hx
  simpa only [Pi.zero_apply, zero_mul] using congrArg (fun t : ℝ => t * φ x) hx

/-- The weak lift is H² on a bounded C² open set. This is a bulk regularity
statement; continuity at the boundary is a separate conclusion. -/
theorem weak_lift_h2 {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1)))) (hc : HasCkBoundary Ω 2)
    (G₀ : Space (m + 1) → ℝ) (hG : SmoothOnClosure Ω G₀)
    (u : H ℝ Ω 1) (hu : IsWeakLift Ω G₀ u) :
    ∃ w : H ℝ Ω 2, hUnderlying Ω 2 w = hUnderlying Ω 1 u := by
  obtain ⟨G, hG⟩ := smooth_hilbert_representative Ω hb G₀ hG 2
  obtain ⟨z, hz⟩ := hu.1
  have hzero : hZeroUnderlying Ω z = hUnderlying Ω 1 u - hUnderlying Ω 2 G := by
    apply Lp.ext
    filter_upwards [hz, hG,
      Lp.coeFn_sub (hUnderlying Ω 1 u) (hUnderlying Ω 2 G)] with x hzx hGx hsub
    rw [hsub, Pi.sub_apply, hGx, hzx]
    simp
  let A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1) :=
    fun _ => ContinuousLinearMap.id ℝ _
  have hA : P201Specs.InteriorH2.CoefficientBounds Ω A 1 0 1 := by
    refine ⟨fun _ _ => ContinuousLinearMap.norm_id_le, (LipschitzWith.const _).lipschitzOnWith, ?_⟩
    intro x hx ξ
    simp [A]
  have hSym : P201Specs.BoundaryH2.SymmetricOn Ω A := by
    intro x hx ξ ζ
    rfl
  obtain ⟨C, hC, hreg⟩ := GlobalH2.liftedEstimate Ω hb (c2_boundary_is_c11 Ω hc)
    1 0 1 (by norm_num)
  obtain ⟨w, hw, _⟩ := hreg A hA hSym u G 0 ⟨z, hzero⟩ (weak_harmonic_equation Ω u hu.2)
  exact ⟨w, hw⟩

/-- Real smooth data admit a unique affine weak lift with an H² bulk class. -/
theorem weak_lift_of_smooth_h2 {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1)))) (hc : HasCkBoundary Ω 2)
    (G₀ : Space (m + 1) → ℝ) (hG : SmoothOnClosure Ω G₀) :
    ∃ u : H ℝ Ω 1, IsWeakLift Ω G₀ u ∧
      (∃ w : H ℝ Ω 2, hUnderlying Ω 2 w = hUnderlying Ω 1 u) ∧
      ∀ v : H ℝ Ω 1, IsWeakLift Ω G₀ v → v = u := by
  obtain ⟨u, hu, huniq⟩ := weak_lift_of_smooth (by omega) Ω hb G₀ hG
  exact ⟨u, hu, weak_lift_h2 Ω hb hc G₀ hG u hu, huniq⟩

/-- Weak harmonicity annihilates the distributional Laplacian of the bulk
class. This justifies applying Weyl's lemma to a variational solution. -/
theorem weak_harmonic_distribution {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1)
    (hu : WeakHarmonic Ω u) :
    distributionLaplacian (regularDistribution Ω (hUnderlying Ω 1 u)) = 0 := by
  have heq := weak_harmonic_equation Ω u hu
  have hdiv : negativeDivergenceDistribution Ω (hGradient u) = 0 := by
    ext φ
    rw [InteriorTesting.negativeDivergenceDistribution_pairing]
    have hφ := heq φ
    change (∫ x in Ω, inner ℝ (hGradient u x) (gradient φ x)) = _ at hφ ⊢
    rw [hφ]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with x hx
    simpa only [Pi.zero_apply, zero_mul] using congrArg (fun t : ℝ => t * φ x) hx
  have hg (i : Fin n) : regularDistribution Ω (fun x => hGradient u x i) =
      regularDistribution Ω (hFirstDerivative u i) := by
    apply (P102.U4.regular_injectivity n ℝ Ω _ _
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        (((Lp.memLp (hGradient u)).eval_piLp i).locallyIntegrable (by norm_num)))
      (P102.U4.domainLp_locallyIntegrable Ω 2 _)).mpr
    exact (Dirichlet.gradient_ae Ω u).mono fun x hx => congrArg (fun v : Space n => v i) hx
  have hid : negativeDivergenceDistribution Ω (hGradient u) =
      -distributionLaplacian (regularDistribution Ω (hUnderlying Ω 1 u)) := by
    change -(∑ i : Fin n, distributionDerivative {i}
      (regularDistribution Ω (fun x => hGradient u x i))) =
        -(∑ i : Fin n, distributionDerivative {i, i} (regularDistribution Ω (hUnderlying Ω 1 u)))
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hg]
    have hd : distributionDerivative {i} (regularDistribution Ω (hUnderlying Ω 1 u)) =
        regularDistribution Ω (hFirstDerivative u i) :=
      hilbertDerivativeDistribution Ω 1 u ⟨{i}, by simp⟩
    rw [← hd]
    change P102.U4.distributionPartial {i} (P102.U4.distributionPartial {i} _) = _
    rw [← P102.U4.derivative_add n ℝ Ω]
    rfl
  rw [hid] at hdiv
  exact neg_eq_zero.mp hdiv

/-- Every real weak harmonic class has a smooth harmonic interior
representative equal to its actual L² values almost everywhere. -/
theorem weak_harmonic_representative {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u : H ℝ Ω 1) (hu : WeakHarmonic Ω u) :
    ∃ h : Space n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h Ω ∧
      P201Specs.MeanValues.IsHarmonic Ω h ∧
      (hUnderlying Ω 1 u : Space n → ℝ) =ᵐ[domainMeasure Ω] h := by
  obtain ⟨h, hs, hh, hreg, _⟩ := Weyl.weyl hn Ω
    (regularDistribution Ω (hUnderlying Ω 1 u)) (weak_harmonic_distribution Ω u hu)
  refine ⟨h, hs, hh, ?_⟩
  exact ((P102.U4.regular_injectivity n ℝ Ω _ _
    (hs.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    (P102.U4.domainLp_locallyIntegrable Ω 2 _)).mp hreg).symm

/-- Replace a smooth neighborhood lift by a globally smooth compactly
supported function with exactly the same values on the closed domain.
This permits use of the canonical physical trace's smooth-agreement theorem. -/
theorem smooth_compact_extension {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (f : Space n → 𝕜) (hf : SmoothOnClosure Ω f) :
    ∃ F : Space n → 𝕜, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      EqOn F f (closure (Ω : Set (Space n))) := by
  obtain ⟨U, hU, hsub, hdiff⟩ := hf
  have hc : IsCompact (closure (Ω : Set (Space n))) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hb.closure⟩
  obtain ⟨V, hV, hKV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure hc hU hsub
  obtain ⟨χ, hχ, _, hsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hKV
  have hcompact : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hsupp]
    exact hcV
  have hsχ : tsupport χ ⊆ U := by
    change closure (Function.support χ) ⊆ U
    rwa [hsupp]
  refine ⟨fun x => χ x • f x, ?_, hcompact.smul_right, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hdiff.contDiffAt (hU.mem_nhds hx))
    · have hzero : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsχ h))
      apply contDiffAt_const.congr_of_eventuallyEq
      exact hzero.mono fun y hy => by
        change χ y • f y = (0 : 𝕜)
        change χ y = (0 : ℝ) at hy
        rw [hy, zero_smul]
  · intro x hx
    change χ x • f x = f x
    rw [(hχone x).mp hx, one_smul]

/-- The real continuous extension is the variational solution, with its actual
H² class. Boundary identification uses weak comparison rather than embedding. -/
theorem real_smooth_lift {m : ℕ} (hm : 1 ≤ m) (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1)))) (hc : HasCkBoundary Ω 2)
    (g : C(frontier (Ω : Set (Space (m + 1))), ℝ))
    (h : Space (m + 1) → ℝ) (hh : P201Specs.ContinuousHarmonicLift.IsExtension Ω g h)
    (G₀ : Space (m + 1) → ℝ) (hG : SmoothOnClosure Ω G₀)
    (hGg : ∀ z : frontier (Ω : Set (Space (m + 1))), G₀ z = g z) :
    ∃ u : H ℝ Ω 1, IsWeakLift Ω G₀ u ∧
      (hUnderlying Ω 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] h ∧
      (∃ w : H ℝ Ω 2,
        (hUnderlying Ω 2 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] h) ∧
      ∀ v : H ℝ Ω 1, IsWeakLift Ω G₀ v → v = u := by
  obtain ⟨u, hu, ⟨w, hw⟩, huniq⟩ := weak_lift_of_smooth_h2 Ω hb hc G₀ hG
  have he := WeakHarmonicBoundary.boundary_identification hm Ω hb hc g G₀ hG hGg
    u hu.1 hu.2 h hh
  refine ⟨u, hu, he, ⟨w, ?_⟩, huniq⟩
  rw [hw]
  exact he

theorem smoothOnClosure_comp_CLM {n : ℕ} {𝕜 𝕝 : Type} [RCLike 𝕜] [RCLike 𝕝]
    (Ω : P201.Domain n) (G : P201.Space n → 𝕜) (F : 𝕜 →L[ℝ] 𝕝)
    (hG : SmoothOnClosure Ω G) : SmoothOnClosure Ω (fun x => F (G x)) := by
  obtain ⟨U, hU, hcl, hdiff⟩ := hG
  exact ⟨U, hU, hcl, F.contDiff.comp_contDiffOn hdiff⟩


def realBoundaryData {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (g : C(frontier (Ω : Set (Space n)), 𝕜)) :
    C(frontier (Ω : Set (Space n)), ℝ) :=
  ⟨fun z => RCLike.re (g z), RCLike.continuous_re.comp g.continuous⟩

def imagBoundaryData {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (g : C(frontier (Ω : Set (Space n)), 𝕜)) :
    C(frontier (Ω : Set (Space n)), ℝ) :=
  ⟨fun z => RCLike.im (g z), RCLike.continuous_im.comp g.continuous⟩

theorem extension_re
    {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (g : C(frontier (Ω : Set (Space n)), 𝕜))
    (h : Space n → 𝕜) (hh : P201Specs.ContinuousHarmonicLift.IsExtension Ω g h) :
    P201Specs.ContinuousHarmonicLift.IsExtension Ω (realBoundaryData Ω g)
      (fun x => RCLike.re (h x)) := by
  refine ⟨?_, RCLike.continuous_re.comp_continuousOn hh.2.1, ?_⟩
  · exact (P201.MeanValues.harmonic_bridge Ω _).mpr
      (((P201.MeanValues.harmonic_bridge Ω h).mp hh.1).comp_CLM RCLike.reCLM)
  · intro z
    exact congrArg RCLike.re (hh.2.2 z)

theorem extension_im
    {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (g : C(frontier (Ω : Set (Space n)), 𝕜))
    (h : Space n → 𝕜) (hh : P201Specs.ContinuousHarmonicLift.IsExtension Ω g h) :
    P201Specs.ContinuousHarmonicLift.IsExtension Ω (imagBoundaryData Ω g)
      (fun x => RCLike.im (h x)) := by
  refine ⟨?_, RCLike.continuous_im.comp_continuousOn hh.2.1, ?_⟩
  · exact (P201.MeanValues.harmonic_bridge Ω _).mpr
      (((P201.MeanValues.harmonic_bridge Ω h).mp hh.1).comp_CLM RCLike.imCLM)
  · intro z
    exact congrArg RCLike.im (hh.2.2 z)


section ScalarAssembly
variable {n : ℕ} {K : Type} [RCLike K] {Ω : Domain n}

lemma scalar_synthesis_underlying
    (T : P201Specs.SobolevScalars.ScalarTransport Ω K) (k : ℕ)
    (a b : H ℝ Ω k) :
    (hUnderlying Ω k (T.ofRealMap k a + (RCLike.I : K) • T.ofRealMap k b) :
      Space n → K) =ᵐ[domainMeasure Ω]
      fun x => (hUnderlying Ω k a x : K) +
        (RCLike.I : K) * (hUnderlying Ω k b x : K) := by
  rw [map_add, map_smul]
  filter_upwards [Lp.coeFn_add (hUnderlying Ω k (T.ofRealMap k a))
      ((RCLike.I : K) • hUnderlying Ω k (T.ofRealMap k b)),
    Lp.coeFn_smul (RCLike.I : K) (hUnderlying Ω k (T.ofRealMap k b)),
    T.ofReal_underlying k a, T.ofReal_underlying k b] with x hadd hsmul ha hb
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, ha, hb]
  rfl

lemma scalar_synthesis_representative
    (T : P201Specs.SobolevScalars.ScalarTransport Ω K) (k : ℕ)
    (a b : H ℝ Ω k) (h : Space n → K)
    (ha : (hUnderlying Ω k a : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => RCLike.re (h x))
    (hb : (hUnderlying Ω k b : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => RCLike.im (h x)) :
    (hUnderlying Ω k (T.ofRealMap k a + (RCLike.I : K) • T.ofRealMap k b) :
      Space n → K) =ᵐ[domainMeasure Ω] h := by
  filter_upwards [scalar_synthesis_underlying T k a b, ha, hb] with x hx hax hbx
  rw [hx, hax, hbx, mul_comm RCLike.I]
  exact RCLike.re_add_im (h x)

lemma affine_scalar_detection
    (T : P201Specs.SobolevScalars.ScalarTransport Ω K)
    (G : Space n → K) (u : H K Ω 1) (hu : InAffineClass Ω G u) :
    InAffineClass Ω (fun x => RCLike.re (G x)) (T.reMap 1 u) ∧
      InAffineClass Ω (fun x => RCLike.im (G x)) (T.imMap 1 u) := by
  obtain ⟨z, hz⟩ := hu
  constructor
  · refine ⟨T.reZero z, ?_⟩
    change (hUnderlying Ω 1 (T.reMap 1 u) : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => RCLike.re (G x) + hUnderlying Ω 1 (T.reZero z).val x
    rw [T.reZero_inclusion]
    filter_upwards [hz, T.re_underlying 1 u, T.re_underlying 1 z.val] with x hx hru hrz
    rw [hru, hx]
    change RCLike.re (G x + hUnderlying Ω 1 z.val x) = _
    rw [map_add, ← hrz]
  · refine ⟨T.imZero z, ?_⟩
    change (hUnderlying Ω 1 (T.imMap 1 u) : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => RCLike.im (G x) + hUnderlying Ω 1 (T.imZero z).val x
    rw [T.imZero_inclusion]
    filter_upwards [hz, T.im_underlying 1 u, T.im_underlying 1 z.val] with x hx hiu hiz
    rw [hiu, hx]
    change RCLike.im (G x + hUnderlying Ω 1 z.val x) = _
    rw [map_add, ← hiz]

lemma affine_scalar_synthesis
    (T : P201Specs.SobolevScalars.ScalarTransport Ω K)
    (G : Space n → K) (a b : H ℝ Ω 1)
    (ha : InAffineClass Ω (fun x => RCLike.re (G x)) a)
    (hb : InAffineClass Ω (fun x => RCLike.im (G x)) b) :
    InAffineClass Ω G (T.ofRealMap 1 a + (RCLike.I : K) • T.ofRealMap 1 b) := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  let z : H10 K Ω := T.ofRealZero za + (RCLike.I : K) • T.ofRealZero zb
  have hzval : z.val = T.ofRealMap 1 za.val + (RCLike.I : K) • T.ofRealMap 1 zb.val := by
    change (T.ofRealZero za).val + (RCLike.I : K) • (T.ofRealZero zb).val = _
    rw [T.ofRealZero_inclusion, T.ofRealZero_inclusion]
  have hz : (hZeroUnderlying Ω z : Space n → K) =ᵐ[domainMeasure Ω]
      fun x => (hZeroUnderlying Ω za x : K) + (RCLike.I : K) * (hZeroUnderlying Ω zb x : K) := by
    change (hUnderlying Ω 1 z.val : Space n → K) =ᵐ[domainMeasure Ω] _
    rw [hzval]
    exact scalar_synthesis_underlying T 1 za.val zb.val
  refine ⟨z, ?_⟩
  filter_upwards [scalar_synthesis_underlying T 1 a b, hz, hza, hzb] with x hx hzx hax hbx
  rw [hx, hzx, hax, hbx]
  have hG : G x = (RCLike.re (G x) : K) + (RCLike.I : K) * (RCLike.im (G x) : K) := by
    simpa only [mul_comm RCLike.I] using (RCLike.re_add_im (G x)).symm
  rw [RCLike.ofReal_add, RCLike.ofReal_add]
  linear_combination -hG

lemma weak_lift_scalar_detection
    (T : P201Specs.SobolevScalars.ScalarTransport Ω K)
    (G : Space n → K) (u : H K Ω 1) (hu : IsWeakLift Ω G u) :
    IsWeakLift Ω (fun x => RCLike.re (G x)) (T.reMap 1 u) ∧
      IsWeakLift Ω (fun x => RCLike.im (G x)) (T.imMap 1 u) := by
  have ha := affine_scalar_detection T G u hu.1
  have hh := T.harmonic_detection u hu.2
  exact ⟨⟨ha.1, hh.1⟩, ⟨ha.2, hh.2⟩⟩

lemma weak_lift_scalar_synthesis
    (T : P201Specs.SobolevScalars.ScalarTransport Ω K)
    (G : Space n → K) (a b : H ℝ Ω 1)
    (ha : IsWeakLift Ω (fun x => RCLike.re (G x)) a)
    (hb : IsWeakLift Ω (fun x => RCLike.im (G x)) b) :
    IsWeakLift Ω G (T.ofRealMap 1 a + (RCLike.I : K) • T.ofRealMap 1 b) := by
  exact ⟨affine_scalar_synthesis T G a b ha.1 hb.1,
    T.harmonic_synthesis a b ha.2 hb.2⟩

lemma weak_lift_scalar_unique
    (T : P201Specs.SobolevScalars.ScalarTransport Ω K)
    (G : Space n → K) (a b : H ℝ Ω 1)
    (ha : ∀ v : H ℝ Ω 1, IsWeakLift Ω (fun x => RCLike.re (G x)) v → v = a)
    (hb : ∀ v : H ℝ Ω 1, IsWeakLift Ω (fun x => RCLike.im (G x)) v → v = b)
    (v : H K Ω 1) (hv : IsWeakLift Ω G v) :
    v = T.ofRealMap 1 a + (RCLike.I : K) • T.ofRealMap 1 b := by
  obtain ⟨hvr, hvi⟩ := weak_lift_scalar_detection T G v hv
  rw [T.reconstruction 1 v, ha _ hvr, hb _ hvi]

end ScalarAssembly

/-- Full harmonic lifting for continuous data, including identification with
and uniqueness of the affine weak lift and its H² bulk regularity. -/
theorem harmonic_lift : P201Specs.SmoothHarmonicLift.HarmonicLiftStatement := by
  intro m hm K _ Ω hb hc g
  obtain ⟨h, hh, huniq⟩ := ContinuousHarmonicLift.harmonic_lift hm Ω hb hc g
  refine ⟨h, hh, huniq, ?_⟩
  intro G₀ hG hGg
  obtain ⟨T⟩ := SobolevScalars.scalar_transport Ω K
  have hGr : SmoothOnClosure Ω (fun x => RCLike.re (G₀ x)) :=
    smoothOnClosure_comp_CLM Ω G₀ (RCLike.reCLM : K →L[ℝ] ℝ) hG
  have hGi : SmoothOnClosure Ω (fun x => RCLike.im (G₀ x)) :=
    smoothOnClosure_comp_CLM Ω G₀ (RCLike.imCLM : K →L[ℝ] ℝ) hG
  have hGgr : ∀ z : frontier (Ω : Set (Space (m + 1))),
      RCLike.re (G₀ z) = realBoundaryData Ω g z :=
    fun z => congrArg RCLike.re (hGg z)
  have hGgi : ∀ z : frontier (Ω : Set (Space (m + 1))),
      RCLike.im (G₀ z) = imagBoundaryData Ω g z :=
    fun z => congrArg RCLike.im (hGg z)
  obtain ⟨a, ha, hah, ⟨a₂, ha₂⟩, hauniq⟩ := real_smooth_lift hm Ω hb hc
    (realBoundaryData Ω g) (fun x => RCLike.re (h x)) (extension_re Ω g h hh)
    (fun x => RCLike.re (G₀ x)) hGr hGgr
  obtain ⟨b, hbweak, hbh, ⟨b₂, hb₂⟩, hbuniq⟩ := real_smooth_lift hm Ω hb hc
    (imagBoundaryData Ω g) (fun x => RCLike.im (h x)) (extension_im Ω g h hh)
    (fun x => RCLike.im (G₀ x)) hGi hGgi
  refine ⟨T.ofRealMap 1 a + (RCLike.I : K) • T.ofRealMap 1 b,
    weak_lift_scalar_synthesis T G₀ a b ha hbweak,
    scalar_synthesis_representative T 1 a b h hah hbh,
    ⟨T.ofRealMap 2 a₂ + (RCLike.I : K) • T.ofRealMap 2 b₂,
      scalar_synthesis_representative T 2 a₂ b₂ h ha₂ hb₂⟩,
    weak_lift_scalar_unique T G₀ a b hauniq hbuniq⟩

end P201.SmoothHarmonicLift
