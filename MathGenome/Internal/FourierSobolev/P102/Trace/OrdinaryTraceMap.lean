import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.OrdinaryTraceMap
import MathGenome.Internal.FourierSobolev.P102.U4.ACL
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.U4.GraphAreaPieces
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import MathGenome.Internal.FourierSobolev.P102.U4.MeyersSerrin
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatTrace
import MathGenome.Internal.FourierSobolev.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace P102.Trace.Ordinary
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open P102.Sobolev.Extension

/-- Surface data are supported on the actual frontier. -/
theorem boundaryMeasure_ae_frontier {m : ℕ} (Ω : Opens (Space (m + 1))) :
    ∀ᵐ x ∂boundaryMeasure Ω, x ∈ frontier (Ω : Set (Space (m + 1))) :=
  ae_restrict_mem isClosed_frontier.measurableSet

/-- Equality of continuous bulk representatives determines their boundary
values, using positivity of Euclidean volume on open sets. -/
theorem continuous_boundary_eq_of_ae {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space (m + 1))) (f g : Space (m + 1) → 𝕜)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] g) :
    f =ᵐ[boundaryMeasure Ω] g := by
  have heq := Measure.eqOn_open_of_ae_eq hfg Ω.isOpen hf.continuousOn hg.continuousOn
  have hclosure := heq.closure hf hg
  filter_upwards [boundaryMeasure_ae_frontier Ω] with x hx
  exact hclosure (frontier_subset_closure hx)

/-- Globally smooth restrictions form a scalar submodule of the shared weak
derivative graph. This is not an assumed trace or density certificate. -/
def smoothRestrictionSubmodule {m : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space (m + 1))) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule 𝕜 (Sobolev 𝕜 Ω 1 p) where
  carrier := {u | ∃ f : Space (m + 1) → 𝕜,
    ContDiff ℝ ∞ f ∧ sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f}
  zero_mem' := ⟨0, contDiff_const, Lp.coeFn_zero 𝕜 p _⟩
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    refine ⟨f + g, hf.add hg, ?_⟩
    have hsum : sobolevUnderlying (u + v) = sobolevUnderlying u + sobolevUnderlying v :=
      (sobolevUnderlyingCLM Ω 1 p).map_add u v
    rw [hsum]
    filter_upwards [Lp.coeFn_add (sobolevUnderlying u) (sobolevUnderlying v), hu, hv]
      with x hx hux hvx
    exact hx.trans (congrArg₂ (· + ·) hux hvx)
  smul_mem' := by
    rintro c u ⟨f, hf, hu⟩
    refine ⟨c • f, contDiff_const.smul hf, ?_⟩
    have hsmul : sobolevUnderlying (c • u) = c • sobolevUnderlying u :=
      (sobolevUnderlyingCLM Ω 1 p).map_smul c u
    rw [hsmul]
    filter_upwards [Lp.coeFn_smul c (sobolevUnderlying u), hu] with x hx hux
    exact hx.trans (congrArg (c • ·) hux)

/-- The full frozen density premise implies density of the smooth submodule.
Only its zero-order coordinate is needed to identify representatives. -/
theorem smooth_restrictions_dense
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense (smoothRestrictionSubmodule 𝕜 Ω p : Set (Sobolev 𝕜 Ω 1 p)) := by
  intro u
  obtain ⟨φ, v, hv, hlim⟩ := hDensity m e Ω hΩ 𝕜 p hp u
  apply mem_closure_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  refine ⟨φ n, (φ n).contDiff, ?_⟩
  simpa only [sobolevUnderlying, zeroSobolevIndex, multiPartial,
    Multiset.sort_zero, partialWord] using hv n (zeroSobolevIndex (m + 1) 1)

/-- Conditional canonicity with exactly the prescribed premises, in order.
The extension premise is retained even though density suffices for uniqueness. -/
theorem trace_uniqueness_conditional
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (_hExtension : P102.Sobolev.Extension.Expected.Extension) :
    Expected.TraceUniqueness := by
  intro m e Ω hΩ 𝕜 _ p _ hp T S hT hS
  have hd := smooth_restrictions_dense hDensity e Ω hΩ 𝕜 p hp
  have heq : EqOn T S (smoothRestrictionSubmodule 𝕜 Ω p) := by
    rintro u ⟨f, hf, hu⟩
    exact Lp.ext ((hT u f hf hu).trans (hS u f hf hu).symm)
  apply ContinuousLinearMap.ext
  intro u
  exact heq.closure T.continuous S.continuous (hd u)

/-- The one-dimensional surface normalization is genuinely counting measure
on the frontier, without a positive-dimensional normalization factor. -/
theorem boundaryMeasure_one_dimension (Ω : Opens (Space 1)) :
    boundaryMeasure Ω = Measure.count.restrict (frontier (Ω : Set (Space 1))) := by
  rw [boundaryMeasure, normalized_zero_eq_count]

/-- A finite graph cover gives finite normalized Hausdorff measure of the
frontier. This is purely geometric, including in dimension one. -/
theorem hausdorff_frontier_lt_top {m : ℕ} {G : Set (Ambient m)}
    (hG : IsLipschitzOpen G) : (μHE[m] : Measure (Ambient m)) (frontier G) < ⊤ := by
  obtain ⟨n, C, hC⟩ := finite_boundary_cover hG
  let S : Fin n → Set (Ambient m) := fun i =>
    (C i).frame '' (graph (C i).graphFunction '' Metric.ball (C i).center (C i).radius)
  have hcover : frontier G ⊆ ⋃ i, S i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hC hx)
    have hfull := chartImage_mono (C i).frame (C i).graphFunction (C i).center
      (show (C i).radius / 2 ≤ (C i).radius by linarith [(C i).radius_pos])
      (show (C i).height / 2 ≤ (C i).height by linarith [(C i).height_pos]) hi
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change x ∈ (C i).frame '' (graph (C i).graphFunction ''
      Metric.ball (C i).center (C i).radius)
    rw [← (C i).boundary]
    exact ⟨hx, hfull⟩
  apply lt_of_le_of_lt (measure_mono hcover)
  apply lt_of_le_of_lt (measure_iUnion_fintype_le _ S)
  apply ENNReal.sum_lt_top.mpr
  intro i _
  have harea := (graph_geometry_in_frame m (Metric.ball (C i).center (C i).radius)
    (C i).graphFunction (C i).constant (C i).graph_lipschitz (C i).frame).2.2
    (Metric.ball (C i).center (C i).radius) Subset.rfl
  change (μHE[m] : Measure (Ambient m)) (S i) < ⊤
  apply lt_of_le_of_lt (show (μHE[m] : Measure (Ambient m)) (S i) ≤
      (graphConstant (C i).constant : ℝ≥0∞) ^ m *
        volume (Metric.ball (C i).center (C i).radius) by
    simpa only [S, Set.image_comp] using harea.2)
  exact ENNReal.mul_lt_top (by finiteness) measure_ball_lt_top

/-- Transfer the geometric measure statement through the actual ambient
isometry. The normalizing constant is unchanged by this transfer. -/
theorem boundaryMeasure_univ_lt_top {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) :
    boundaryMeasure Ω univ < ⊤ := by
  have hfrontier : e '' frontier (geometricOpen e Ω : Set (Ambient m)) =
      frontier (Ω : Set (Space (m + 1))) := by
    calc
      _ = frontier (e '' (geometricOpen e Ω : Set (Ambient m))) :=
        e.toHomeomorph.image_frontier _
      _ = _ := congrArg frontier (e.image_preimage _)
  rw [boundaryMeasure, Measure.restrict_apply_univ, ← hfrontier,
    e.isometry.euclideanHausdorffMeasure_image]
  exact hausdorff_frontier_lt_top hΩ

/-- Every ambient continuous function is Lp on the compact Lipschitz boundary.
Only geometric finiteness and compactness enter here. -/
theorem continuous_boundary_memLp {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) (f : Space (m + 1) → 𝕜) (hf : Continuous f) :
    MemLp f p (boundaryMeasure Ω) := by
  let : IsFiniteMeasure (boundaryMeasure Ω) := ⟨boundaryMeasure_univ_lt_top e Ω hΩ⟩
  have hcompact : IsCompact (frontier (Ω : Set (Space (m + 1)))) := by
    have hg := hΩ.2.1.isCompact_closure.of_isClosed_subset isClosed_frontier
      frontier_subset_closure
    have ht := hg.image e.continuous
    have he : e '' frontier (geometricOpen e Ω : Set (Ambient m)) =
        frontier (Ω : Set (Space (m + 1))) := by
      calc
        _ = frontier (e '' (geometricOpen e Ω : Set (Ambient m))) :=
          e.toHomeomorph.image_frontier _
        _ = _ := congrArg frontier (e.image_preimage _)
    rwa [he] at ht
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [boundaryMeasure_ae_frontier Ω] with x hx
  exact hC x hx

section SmoothBoundaryRestriction
variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
  (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
  (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A chosen ambient smooth representative is used only on the smooth
submodule; a.e. invariance below removes this choice from the boundary map. -/
def smoothBoundaryRepresentative (u : smoothRestrictionSubmodule 𝕜 Ω p) :
    Space (m + 1) → 𝕜 := Classical.choose u.property

theorem smoothBoundaryRepresentative_contDiff (u : smoothRestrictionSubmodule 𝕜 Ω p) :
    ContDiff ℝ ∞ (smoothBoundaryRepresentative Ω p u) :=
  (Classical.choose_spec u.property).1

theorem smoothBoundaryRepresentative_ae (u : smoothRestrictionSubmodule 𝕜 Ω p) :
    sobolevUnderlying u.val =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
      smoothBoundaryRepresentative Ω p u :=
  (Classical.choose_spec u.property).2

/-- Actual restriction of a smooth representative to boundary Lp. This
definition uses only the proved finite measure of a Lipschitz boundary. -/
def smoothBoundaryRestriction (u : smoothRestrictionSubmodule 𝕜 Ω p) : BoundaryLp 𝕜 Ω p :=
  (continuous_boundary_memLp e Ω hΩ p (smoothBoundaryRepresentative Ω p u)
    (smoothBoundaryRepresentative_contDiff Ω p u).continuous).toLp _

theorem smoothBoundaryRestriction_coe (u : smoothRestrictionSubmodule 𝕜 Ω p)
    (f : Space (m + 1) → 𝕜) (hf : ContDiff ℝ ∞ f)
    (hu : sobolevUnderlying u.val =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    (smoothBoundaryRestriction e Ω hΩ p u : Space (m + 1) → 𝕜) =ᵐ[boundaryMeasure Ω] f := by
  apply (continuous_boundary_memLp e Ω hΩ p (smoothBoundaryRepresentative Ω p u)
    (smoothBoundaryRepresentative_contDiff Ω p u).continuous).coeFn_toLp.trans
  exact continuous_boundary_eq_of_ae Ω _ _
    (smoothBoundaryRepresentative_contDiff Ω p u).continuous hf.continuous
    ((smoothBoundaryRepresentative_ae Ω p u).symm.trans hu)

/-- Boundary restriction on smooth bulk classes is well-defined and linear
before any analytic trace norm inequality has been supplied. -/
def smoothBoundaryRestrictionLM :
    smoothRestrictionSubmodule 𝕜 Ω p →ₗ[𝕜] BoundaryLp 𝕜 Ω p where
  toFun := smoothBoundaryRestriction e Ω hΩ p
  map_add' u v := by
    let f := smoothBoundaryRepresentative Ω p u
    let g := smoothBoundaryRepresentative Ω p v
    have hf := smoothBoundaryRepresentative_contDiff Ω p u
    have hg := smoothBoundaryRepresentative_contDiff Ω p v
    have hu := smoothBoundaryRepresentative_ae Ω p u
    have hv := smoothBoundaryRepresentative_ae Ω p v
    have huv : sobolevUnderlying (u + v).val =ᵐ[
        volume.restrict (Ω : Set (Space (m + 1)))] f + g := by
      filter_upwards [Lp.coeFn_add (sobolevUnderlying u.val) (sobolevUnderlying v.val),
        hu, hv] with x hx hux hvx
      change (sobolevUnderlying u.val + sobolevUnderlying v.val : DomainLp 𝕜 Ω p) x = _
      rw [hx]
      exact congrArg₂ (· + ·) hux hvx
    apply Lp.ext
    filter_upwards [smoothBoundaryRestriction_coe e Ω hΩ p (u + v) (f + g) (hf.add hg) huv,
      Lp.coeFn_add (smoothBoundaryRestriction e Ω hΩ p u) (smoothBoundaryRestriction e Ω hΩ p v),
      smoothBoundaryRestriction_coe e Ω hΩ p u f hf hu,
      smoothBoundaryRestriction_coe e Ω hΩ p v g hg hv] with x hx hadd hux hvx
    rw [hx, hadd]
    exact congrArg₂ (· + ·) hux.symm hvx.symm
  map_smul' c u := by
    let f := smoothBoundaryRepresentative Ω p u
    have hf := smoothBoundaryRepresentative_contDiff Ω p u
    have hu := smoothBoundaryRepresentative_ae Ω p u
    have hcu : sobolevUnderlying (c • u).val =ᵐ[
        volume.restrict (Ω : Set (Space (m + 1)))] c • f := by
      filter_upwards [Lp.coeFn_smul c (sobolevUnderlying u.val), hu] with x hx hux
      change (c • sobolevUnderlying u.val : DomainLp 𝕜 Ω p) x = _
      rw [hx]
      exact congrArg (c • ·) hux
    apply Lp.ext
    filter_upwards [smoothBoundaryRestriction_coe e Ω hΩ p (c • u) (c • f)
        (contDiff_const.smul hf) hcu,
      Lp.coeFn_smul c (smoothBoundaryRestriction e Ω hΩ p u),
      smoothBoundaryRestriction_coe e Ω hΩ p u f hf hu] with x hx hsmul hux
    change _ = (c • smoothBoundaryRestriction e Ω hΩ p u : BoundaryLp 𝕜 Ω p) x
    rw [hx, hsmul]
    exact congrArg (c • ·) hux.symm

include e hΩ in
/-- Reduction of trace existence to the ordinary smooth-function boundary
inequality. The inequality is an explicit hypothesis of this *reduction*,
not an upstream assumption or a completed conditional target. -/
theorem exists_trace_of_smooth_bound
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (hp : p ≠ ⊤) (C : ℝ)
    (hbound : ∀ (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜),
      ContDiff ℝ ∞ f →
      sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f →
      (eLpNorm f p (boundaryMeasure Ω)).toReal ≤ C * ‖u‖) :
    ∃ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p,
      IsTrace T ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) := by
  let L := smoothBoundaryRestrictionLM e Ω hΩ p (𝕜 := 𝕜)
  let ι := (smoothRestrictionSubmodule 𝕜 Ω p).subtype
  have hd : DenseRange ι := by
    change Dense (Set.range ((↑) : smoothRestrictionSubmodule 𝕜 Ω p → Sobolev 𝕜 Ω 1 p))
    rw [Subtype.range_coe_subtype]
    exact smooth_restrictions_dense hDensity e Ω hΩ 𝕜 p hp
  have hnorm (u : smoothRestrictionSubmodule 𝕜 Ω p) : ‖L u‖ ≤ C * ‖ι u‖ := by
    change ‖smoothBoundaryRestriction e Ω hΩ p u‖ ≤ C * ‖u.val‖
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae (smoothBoundaryRestriction_coe e Ω hΩ p u
      (smoothBoundaryRepresentative Ω p u) (smoothBoundaryRepresentative_contDiff Ω p u)
      (smoothBoundaryRepresentative_ae Ω p u))]
    exact hbound u.val _ (smoothBoundaryRepresentative_contDiff Ω p u)
      (smoothBoundaryRepresentative_ae Ω p u)
  let T := L.extendOfNorm ι
  refine ⟨T, ?_, fun u => LinearMap.norm_extendOfNorm_apply_le hd C hnorm u⟩
  intro u f hf hu
  have he : T u = L ⟨u, ⟨f, hf, hu⟩⟩ :=
    LinearMap.extendOfNorm_eq hd ⟨C, hnorm⟩ ⟨u, ⟨f, hf, hu⟩⟩
  rw [he]
  exact smoothBoundaryRestriction_coe e Ω hΩ p ⟨u, ⟨f, hf, hu⟩⟩ f hf hu

end SmoothBoundaryRestriction

section LpMultiplication
variable {X : Type} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
  (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (χ : X → ℝ) (hχ : AEStronglyMeasurable χ μ) (C : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C)

omit [Fact (1 ≤ p)] in
include hχ hC in
private theorem cutoffLp_memLp (u : Lp 𝕜 p μ) : MemLp (fun x => χ x • u x) p μ := by
  apply (Lp.memLp u).of_le_mul (c := C) (hχ.smul (Lp.aestronglyMeasurable u))
  exact Eventually.of_forall fun x => by
    change ‖χ x • u x‖ ≤ C * ‖u x‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Multiplication by a bounded real coefficient on any scalar Lp space. -/
def cutoffLp : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun u := (cutoffLp_memLp μ p χ hχ C hC u).toLp _
      map_add' u v := by
        apply Lp.ext
        filter_upwards [(cutoffLp_memLp μ p χ hχ C hC (u + v)).coeFn_toLp,
          (cutoffLp_memLp μ p χ hχ C hC u).coeFn_toLp,
          (cutoffLp_memLp μ p χ hχ C hC v).coeFn_toLp,
          Lp.coeFn_add u v,
          Lp.coeFn_add ((cutoffLp_memLp μ p χ hχ C hC u).toLp _)
            ((cutoffLp_memLp μ p χ hχ C hC v).toLp _)] with x huv hu hv hs ht
        simp only [huv, ht, Pi.add_apply, hu, hv, hs, smul_add]
      map_smul' c u := by
        apply Lp.ext
        filter_upwards [(cutoffLp_memLp μ p χ hχ C hC (c • u)).coeFn_toLp,
          (cutoffLp_memLp μ p χ hχ C hC u).coeFn_toLp,
          Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((cutoffLp_memLp μ p χ hχ C hC u).toLp _)]
          with x hcu hu hs ht
        simp only [hcu, ht, RingHom.id_apply, Pi.smul_apply, hu, hs]
        exact smul_comm (χ x) c (u x) }
    C (fun u => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(cutoffLp_memLp μ p χ hχ C hC u).coeFn_toLp] with x hx
      change ‖((cutoffLp_memLp μ p χ hχ C hC u).toLp _ : Lp 𝕜 p μ) x‖ ≤ C * ‖u x‖
      rw [hx, norm_smul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

theorem cutoffLp_ae (u : Lp 𝕜 p μ) :
    (cutoffLp μ p χ hχ C hC u : X → 𝕜) =ᵐ[μ] (fun x => χ x • u x) :=
  (cutoffLp_memLp μ p χ hχ C hC u).coeFn_toLp

end LpMultiplication

/-- The frozen extension premise supplies existence of a Sobolev cutoff
product. Its weak derivatives come from whole-space test multiplication,
followed by restriction. No boundary trace is used. -/
theorem exists_cutoff_product
    (hExtension : P102.Sobolev.Extension.Expected.Extension)
    {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (χ : Space (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (u : Sobolev 𝕜 Ω 1 p) :
    ∃ v : Sobolev 𝕜 Ω 1 p,
      sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
        (fun x => χ x • sobolevUnderlying u x) := by
  obtain ⟨D, K, A, B, hD, hE⟩ := hExtension m e Ω hΩ
  obtain ⟨E, hraw, hres, hsupport, hnorm, hzero⟩ := hE 𝕜 p
  let a : WholeTests (m + 1) 𝕜 :=
    ⟨fun x => χ x • (1 : 𝕜), hχ.smul contDiff_const, hc.smul_right, subset_univ _⟩
  obtain ⟨w, hw⟩ := sobolev_testMul 1 p (E u) a
  refine ⟨sobolevRestrict Ω w, ?_⟩
  have hwa : (sobolevUnderlying w : Space (m + 1) → 𝕜) =ᵐ[volume]
      (fun x => a x * sobolevUnderlying (E u) x) := by
    rw [hw]
    exact testMulLp_ae a _
  have hwr := ae_restrict_of_ae (s := (Ω : Set (Space (m + 1)))) hwa
  filter_upwards [P102.U4.domainLpRestrict_ae Ω (sobolevUnderlying w), hwr, hres u]
    with x hx hax hux
  change P102.U4.domainLpRestrict Ω (sobolevUnderlying w) x = _
  rw [hx, hax, hux]
  change (χ x • (1 : 𝕜)) * sobolevUnderlying u x = _
  simp only [smul_mul_assoc, one_mul]

/-- Existence and injectivity determine a linear cutoff operator. The closed
graph theorem proves boundedness from boundedness of the underlying Lp
multiplier, without requiring a new derivative estimate. -/
theorem exists_sobolev_cutoffCLM
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (χ : Space d → ℝ)
    (hχ : AEStronglyMeasurable χ (volume.restrict (Ω : Set (Space d))))
    (C : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C)
    (hex : ∀ u : Sobolev 𝕜 Ω 1 p, ∃ v : Sobolev 𝕜 Ω 1 p,
      sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => χ x • sobolevUnderlying u x)) :
    ∃ M : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 Ω 1 p,
      ∀ u, sobolevUnderlying (M u) =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => χ x • sobolevUnderlying u x) := by
  let U := sobolevUnderlyingCLM (𝕜 := 𝕜) Ω 1 p
  let B := cutoffLp (𝕜 := 𝕜) (volume.restrict (Ω : Set (Space d))) p χ hχ C hC
  choose M hM using hex
  have hMB (u) : U (M u) = B (U u) :=
    Lp.ext ((hM u).trans (cutoffLp_ae _ p χ hχ C hC (U u)).symm)
  have hU := sobolevUnderlying_injective (𝕜 := 𝕜) Ω 1 p
  let L : Sobolev 𝕜 Ω 1 p →ₗ[𝕜] Sobolev 𝕜 Ω 1 p :=
    { toFun := M
      map_add' u v := hU (by
        change U (M (u + v)) = U (M u + M v)
        rw [hMB, map_add, map_add, map_add, hMB, hMB])
      map_smul' c u := hU (by
        change U (M (c • u)) = U (c • M u)
        rw [hMB, map_smul, map_smul, map_smul, hMB]) }
  have hclosed : IsClosed (L.graph : Set (Sobolev 𝕜 Ω 1 p × Sobolev 𝕜 Ω 1 p)) := by
    have he : (L.graph : Set (Sobolev 𝕜 Ω 1 p × Sobolev 𝕜 Ω 1 p)) =
        {z | U z.2 = B (U z.1)} := by
      ext z
      change z.2 = L z.1 ↔ U z.2 = B (U z.1)
      constructor
      · intro hz
        rw [hz]
        exact hMB z.1
      · intro hz
        exact hU (hz.trans (hMB z.1).symm)
    rw [he]
    exact isClosed_eq (U.continuous.comp continuous_snd)
      (B.continuous.comp (U.continuous.comp continuous_fst))
  exact ⟨ContinuousLinearMap.ofIsClosedGraph hclosed, hM⟩

/-- Trace commutes with smooth ambient cutoffs by density and the bounded
bulk and boundary multipliers. Both frozen premises appear in order. -/
theorem cutoff_compatibility_conditional
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (hExtension : P102.Sobolev.Extension.Expected.Extension) :
    Expected.CutoffCompatibility := by
  intro m e Ω hΩ 𝕜 _ p _ hp T hT χ hχ hc
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
  have hex := exists_cutoff_product hExtension e Ω hΩ 𝕜 p χ hχ hc
  obtain ⟨M, hM⟩ := exists_sobolev_cutoffCLM Ω p χ hχ.continuous.aestronglyMeasurable C hC hex
  let B := cutoffLp (𝕜 := 𝕜) (boundaryMeasure Ω) p χ hχ.continuous.aestronglyMeasurable C hC
  have heq : T.comp M = B.comp T := by
    have hd := smooth_restrictions_dense hDensity e Ω hΩ 𝕜 p hp
    have hon : EqOn (T.comp M) (B.comp T) (smoothRestrictionSubmodule 𝕜 Ω p) := by
      rintro u ⟨f, hf, hu⟩
      have hprod : sobolevUnderlying (M u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
          (fun x => χ x • f x) := by
        filter_upwards [hM u, hu] with x hx hux
        exact hx.trans (congrArg (χ x • ·) hux)
      apply Lp.ext
      filter_upwards [hT (M u) _ (hχ.smul hf) hprod, hT u f hf hu,
        cutoffLp_ae (boundaryMeasure Ω) p χ hχ.continuous.aestronglyMeasurable C hC (T u)]
        with x hleft hright hb
      exact hleft.trans ((congrArg (χ x • ·) hright.symm).trans hb.symm)
    apply ContinuousLinearMap.ext
    intro u
    exact hon.closure (T.comp M).continuous (B.comp T).continuous (hd u)
  intro u
  refine ⟨hex u, fun v hv => ?_⟩
  have hvM : v = M u := sobolevUnderlying_injective Ω 1 p (Lp.ext (hv.trans (hM u).symm))
  have hTM : T (M u) = B (T u) := congrArg (fun L : _ →L[𝕜] _ => L u) heq
  rw [hvM, hTM]
  exact cutoffLp_ae (boundaryMeasure Ω) p χ hχ.continuous.aestronglyMeasurable C hC (T u)

/-- AC representatives have unique values on every closed component,
including both endpoints. This uses the actual real-coordinate domain. -/
theorem endpoint_representative_unique {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {n : ℕ} (a b : Fin n → ℝ) (hab : ∀ i, a i < b i)
    (hsub : ∀ i, Ioo (a i) (b i) ⊆ linePoint ⁻¹' (Ω : Set (Space 1)))
    {u : Sobolev 𝕜 Ω 1 p} {f g : ℝ → 𝕜}
    (hf : IsEndpointRepresentative a b u f) (hg : IsEndpointRepresentative a b u g) :
    ∀ i, EqOn f g (Icc (a i) (b i)) := by
  intro i
  have hfc : ContinuousOn f (Icc (a i) (b i)) := by
    simpa only [uIcc_of_le (hab i).le] using (hf.2.1 i).continuousOn
  have hgc : ContinuousOn g (Icc (a i) (b i)) := by
    simpa only [uIcc_of_le (hab i).le] using (hg.2.1 i).continuousOn
  have hfg : f =ᵐ[volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1)))] g := by
    filter_upwards [hf.1, hg.1] with t hft hgt
    exact hft.symm.trans hgt
  have heq := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset (hsub i) hfg) isOpen_Ioo
    (hfc.mono Ioo_subset_Icc_self) (hgc.mono Ioo_subset_Icc_self)
  exact heq.of_subset_closure hfc hgc Ioo_subset_Icc_self (by
    rw [closure_Ioo (hab i).ne])

/-- In dimension one a boundary a.e. equality determines each endpoint value,
because every frontier singleton has counting mass one. -/
theorem boundary_ae_eq_at_one_dimension {Y : Type} (Ω : Opens (Space 1))
    {f g : Space 1 → Y} (hfg : f =ᵐ[boundaryMeasure Ω] g)
    {x : Space 1} (hx : x ∈ frontier (Ω : Set (Space 1))) : f x = g x := by
  have hmass : boundaryMeasure Ω {x} = 1 := by
    rw [boundaryMeasure_one_dimension, Measure.restrict_apply (measurableSet_singleton x),
      inter_eq_left.mpr (singleton_subset_iff.mpr hx)]
    simp
  by_contra hne
  have hle := measure_mono (μ := boundaryMeasure Ω)
    (singleton_subset_iff.mpr hne : {x} ⊆ {y | f y ≠ g y})
  have hzero : boundaryMeasure Ω {y | f y ≠ g y} = 0 := ae_iff.mp hfg
  rw [hmass, hzero] at hle
  exact (by simp : ¬ (1 : ℝ≥0∞) ≤ 0) hle

/-- Physical dimension-one coordinates, with their Euclidean length. -/
def lineIsometry : ℝ ≃ₗᵢ[ℝ] Space 1 where
  toFun := linePoint
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    ext i
    exact congrArg x (Subsingleton.elim _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' t := by
    change ‖linePoint t‖ = ‖t‖
    simp [linePoint, PiLp.norm_eq_of_L2, Real.sqrt_sq_eq_abs]

@[simp] theorem lineIsometry_apply (t : ℝ) : lineIsometry t = linePoint t := rfl

@[simp] theorem acl_line_one (t : ℝ) : ACL.line (0 : Fin 1) 0 t = linePoint t := by
  ext i
  simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, linePoint,
    show i = (0 : Fin 1) from Subsingleton.elim _ _]

/-- A.e. bulk identities pull back to the ordinary real coordinate. -/
theorem linePoint_ae_restrict {Ω : Opens (Space 1)} {P : Space 1 → Prop}
    (hP : ∀ᵐ x ∂volume.restrict (Ω : Set (Space 1)), P x) :
    ∀ᵐ t ∂volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1))), P (linePoint t) := by
  let : IsEmpty {j : Fin 1 // j ≠ (0 : Fin 1)} :=
    ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  have h := ACL.ae_on_fibers (0 : Fin 1) hP
  simp only [Measure.volume_pi_eq_dirac (0 : ACL.Transverse (0 : Fin 1)),
    ae_dirac_eq, Filter.eventually_pure] at h
  have hline : ACL.line (0 : Fin 1) 0 = linePoint := funext acl_line_one
  simpa only [ACL.fiber, hline] using h

/-- Every whole-line Sobolev class has one representative absolutely continuous
on every compact interval, whose derivative is its actual weak derivative. -/
theorem whole_line_ac_representative {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p) :
    ∃ f : ℝ → 𝕜,
      (∀ᵐ t ∂volume, sobolevUnderlying u (linePoint t) = f t) ∧
      (∀ a b, AbsolutelyContinuousOnInterval f a b) ∧
      ∀ᵐ t ∂volume, HasDerivAt f (firstWeakDerivative u 0 (linePoint t)) t := by
  obtain ⟨g, hg, hac, hd⟩ := (acl_dimensionOne 𝕜 ⊤
    (sobolevUnderlying u) (firstWeakDerivative u 0)
    (domainLp_locallyIntegrable ⊤ p _) (domainLp_locallyIntegrable ⊤ p _)).mp
    (sobolev_derivative_distribution ⊤ 1 p u (firstSobolevIndex 0))
  refine ⟨fun t => g (linePoint t), ?_, ?_, ?_⟩
  · simpa only [Opens.coe_top, preimage_univ, Measure.restrict_univ] using
      linePoint_ae_restrict hg
  · intro a b
    simpa only [acl_line_one] using hac a b (subset_univ _)
  · simpa only [ACL.fiber, acl_line_one, Opens.coe_top, preimage_univ,
      Measure.restrict_univ] using hd

/-- Extension across the boundary supplies AC representatives through all
endpoints at once. No trace value or endpoint estimate is assumed. -/
theorem exists_endpoint_representative
    (hExtension : P102.Sobolev.Extension.Expected.Extension)
    (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)))
    {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {n : ℕ} (a b : Fin n → ℝ) (u : Sobolev 𝕜 Ω 1 p) :
    ∃ f : ℝ → 𝕜, IsEndpointRepresentative a b u f := by
  obtain ⟨D, K, C, B, hD, hE⟩ := hExtension 0 e Ω hΩ
  obtain ⟨E, hraw, hres, hsupp, hnorm, hzero⟩ := hE 𝕜 p
  obtain ⟨f, hf, hac, hd⟩ := whole_line_ac_representative (E u)
  have hrestrict : sobolevRestrict Ω (E u) = u := by
    apply sobolevUnderlying_injective Ω 1 p
    apply Lp.ext
    exact (P102.U4.domainLpRestrict_ae Ω _).trans (hres u)
  have hder : firstWeakDerivative (E u) 0 =ᵐ[
      volume.restrict (Ω : Set (Space 1))] firstWeakDerivative u 0 := by
    have h := P102.U4.domainLpRestrict_ae Ω (firstWeakDerivative (E u) 0)
    have he : P102.U4.domainLpRestrict Ω (firstWeakDerivative (E u) 0) =
        firstWeakDerivative u 0 := by
      change firstWeakDerivative (sobolevRestrict Ω (E u)) 0 = _
      rw [hrestrict]
    rw [he] at h
    exact h.symm
  refine ⟨f, ?_, fun i => hac (a i) (b i), ?_⟩
  · filter_upwards [linePoint_ae_restrict (hres u),
      ae_restrict_of_ae (s := linePoint ⁻¹' (Ω : Set (Space 1))) hf] with t ht hft
    exact ht.symm.trans hft
  · filter_upwards [linePoint_ae_restrict hder,
      ae_restrict_of_ae (s := linePoint ⁻¹' (Ω : Set (Space 1))) hd] with t ht hdt
    rwa [ht] at hdt

/-- The one-sided Lipschitz graph condition is invariant under physical
rigid motions. The charts are transported, with their graph functions unchanged. -/
theorem lipschitzOpen_image {m : ℕ} {G : Set (Ambient m)}
    (hG : IsLipschitzOpen G) (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) :
    IsLipschitzOpen (F '' G) := by
  refine ⟨F.toHomeomorph.isOpenMap G hG.1,
    F.isometry.lipschitzWith.isBounded_image hG.2.1, ?_⟩
  intro x hx
  change x ∈ frontier (F.toHomeomorph '' G) at hx
  rw [← F.toHomeomorph.image_frontier] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨C, hC⟩ := hG.2.2 y hy
  let C' : BoundaryChart (F '' G) :=
    { frame := C.frame.trans F
      center := C.center
      radius := C.radius
      height := C.height
      radius_pos := C.radius_pos
      height_pos := C.height_pos
      graphFunction := C.graphFunction
      constant := C.constant
      graph_lipschitz := C.graph_lipschitz
      side := by
        change F '' G ∩ (F ∘ C.frame) '' _ = (F ∘ C.frame) '' _
        rw [Set.image_comp, Set.image_comp, ← image_inter F.injective]
        exact congrArg (F '' ·) C.side
      boundary := by
        change frontier (F.toHomeomorph '' G) ∩ _ = _
        rw [← F.toHomeomorph.image_frontier]
        change F '' frontier G ∩ (F ∘ C.frame) '' _ = (F ∘ C.frame) '' _
        rw [Set.image_comp, Set.image_comp, ← image_inter F.injective]
        exact congrArg (F '' ·) C.boundary }
  exact ⟨C', congrArg F hC⟩

/-- A finite interval decomposition in the physical real coordinate. This
includes either orientation of the arbitrary graph-coordinate isometry e. -/
theorem physical_interval_decomposition
    (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0))) :
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧ Function.Injective (Sum.elim a b) ∧
      Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      (Ω : Set (Space 1)) = ⋃ i, linePoint '' Ioo (a i) (b i) ∧
      frontier (Ω : Set (Space 1)) = ⋃ i, {linePoint (a i), linePoint (b i)} := by
  let q : Ambient 0 ≃ₗᵢ[ℝ] Space 1 := verticalLine.trans lineIsometry
  let F : Ambient 0 ≃ₗᵢ[ℝ] Ambient 0 := e.trans q.symm
  have hG : IsLipschitzOpen (q ⁻¹' (Ω : Set (Space 1))) := by
    have h := lipschitzOpen_image hΩ F.toAffineIsometryEquiv
    have he : F '' (geometricOpen e Ω : Set (Ambient 0)) =
        q ⁻¹' (Ω : Set (Space 1)) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        change q (q.symm (e w)) ∈ (Ω : Set (Space 1))
        simpa only [q.apply_symm_apply] using (show e w ∈ (Ω : Set (Space 1)) from hw)
      · intro hz
        refine ⟨e.symm (q z), ?_, ?_⟩
        · change e (e.symm (q z)) ∈ (Ω : Set (Space 1))
          simpa using hz
        · simp [F]
    change IsLipschitzOpen (F '' (geometricOpen e Ω : Set (Ambient 0))) at h
    rwa [he] at h
  obtain ⟨n, a, b, hab, hinj, hdis, hcover, hfront⟩ := one_dimension_forward hG
  refine ⟨n, a, b, hab, hinj, hdis, ?_, ?_⟩
  · calc
      (Ω : Set (Space 1)) = q '' (q ⁻¹' (Ω : Set (Space 1))) :=
        (q.image_preimage _).symm
      _ = _ := by
        rw [hcover, image_iUnion]
        apply iUnion_congr
        intro i
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z.ofLp.2, hz, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨verticalLine.symm t, ht, rfl⟩
  · have h := q.toHomeomorph.image_frontier (q ⁻¹' (Ω : Set (Space 1)))
    change q '' frontier (q ⁻¹' (Ω : Set (Space 1))) =
      frontier (q '' (q ⁻¹' (Ω : Set (Space 1)))) at h
    have hqp : q '' (q ⁻¹' (Ω : Set (Space 1))) = (Ω : Set (Space 1)) :=
      q.image_preimage _
    rw [hqp] at h
    rw [← h, hfront, image_iUnion]
    apply iUnion_congr
    intro i
    simp only [image_pair]
    rfl

/-- Averaging the fundamental theorem on a unit interval bounds point
values by the full first-order Lp norm, also at p=1. -/
theorem ac_value_norm_le {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f h : ℝ → 𝕜}
    (hf : MemLp f p volume) (hh : MemLp h p volume)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t ∂volume, HasDerivAt f (h t) t) (x : ℝ) :
    ‖f x‖ ≤ (eLpNorm f p volume).toReal + (eLpNorm h p volume).toReal := by
  let A := Ioc x (x + 1)
  let ν : Measure ℝ := volume.restrict A
  have hν : ν univ = 1 := by simp [ν, A, Real.volume_Ioc]
  let : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.one_lt_top⟩
  have hfA : MemLp f p ν := hf.mono_measure Measure.restrict_le_self
  have hhA : MemLp h p ν := hh.mono_measure Measure.restrict_le_self
  have hiF : Integrable f ν := hfA.integrable Fact.out
  have hiH : Integrable h ν := hhA.integrable Fact.out
  have hint (g : ℝ → 𝕜) (hg : MemLp g p volume) (hgA : MemLp g p ν) :
      (∫ t, ‖g t‖ ∂ν) ≤ (eLpNorm g p volume).toReal := by
    have hi := ExpandedFA.Sobolev.OneDimensional.integral_norm_le_lp hgA
    rw [hν] at hi
    simp only [ENNReal.toReal_one, Real.one_rpow, mul_one] at hi
    exact hi.trans (ENNReal.toReal_mono hg.eLpNorm_ne_top
      (eLpNorm_mono_measure g Measure.restrict_le_self))
  have hosc (y : ℝ) (hy : y ∈ A) : ‖f x - f y‖ ≤ ∫ t, ‖h t‖ ∂ν := by
    have he := ExpandedFA.Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
      (hac x y) (hh.locallyIntegrable Fact.out) (hd.mono fun _ ht _ => ht)
    rw [norm_sub_rev, ← he]
    calc
      _ ≤ ∫ t in Ioc x y, ‖h t‖ := by
        simpa only [intervalIntegral.integral_of_le hy.1.le] using
          intervalIntegral.norm_integral_le_integral_norm hy.1.le (f := h)
      _ ≤ ∫ t, ‖h t‖ ∂ν :=
        setIntegral_mono_set hiH.norm (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall fun _ ht => ⟨ht.1, ht.2.trans hy.2⟩)
  have hpoint : ∀ᵐ y ∂ν, ‖f x‖ ≤ ‖f y‖ + ∫ t, ‖h t‖ ∂ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    calc
      ‖f x‖ = ‖(f x - f y) + f y‖ := by congr 1; abel
      _ ≤ ‖f x - f y‖ + ‖f y‖ := norm_add_le _ _
      _ ≤ _ := by linarith [hosc y hy]
  have hi := integral_mono_ae (integrable_const ‖f x‖)
    (hiF.norm.add (integrable_const (∫ t, ‖h t‖ ∂ν))) hpoint
  have hmass : ν.real univ = 1 := by simp [Measure.real, hν]
  change (∫ _ : ℝ, ‖f x‖ ∂ν) ≤ (∫ y, ‖f y‖ + (∫ t, ‖h t‖ ∂ν) ∂ν) at hi
  rw [integral_add hiF.norm (integrable_const _)] at hi
  simp only [integral_const, hmass, smul_eq_mul, one_mul] at hi
  exact hi.trans (add_le_add (hint f hf hfA) (hint h hh hhA))

/-- Chosen whole-line representative; its uniqueness makes all ensuing
point evaluations independent of the choice. -/
def wholeLineRepresentative {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p) : ℝ → 𝕜 :=
  Classical.choose (whole_line_ac_representative u)

theorem wholeLineRepresentative_spec {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p) :
    (∀ᵐ t ∂volume, sobolevUnderlying u (linePoint t) = wholeLineRepresentative u t) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (wholeLineRepresentative u) a b) ∧
    ∀ᵐ t ∂volume, HasDerivAt (wholeLineRepresentative u)
      (firstWeakDerivative u 0 (linePoint t)) t :=
  Classical.choose_spec (whole_line_ac_representative u)

theorem wholeLineRepresentative_continuous {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p) :
    Continuous (wholeLineRepresentative u) := by
  apply continuousOn_univ.mp
  apply ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn _ isOpen_univ
  exact fun a b _ => (wholeLineRepresentative_spec u).2.1 a b

/-- Continuous representatives of a whole-line class agree everywhere. -/
theorem wholeLineRepresentative_eq {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p)
    (f : ℝ → 𝕜) (hf : Continuous f)
    (hu : ∀ᵐ t ∂volume, sobolevUnderlying u (linePoint t) = f t) :
    wholeLineRepresentative u = f := by
  have he : wholeLineRepresentative u =ᵐ[volume] f := by
    filter_upwards [(wholeLineRepresentative_spec u).1, hu] with t ht hft
    exact ht.symm.trans hft
  apply funext
  intro t
  exact Measure.eqOn_open_of_ae_eq
    (by simpa only [Measure.restrict_univ] using he)
    isOpen_univ (wholeLineRepresentative_continuous u).continuousOn hf.continuousOn
    (mem_univ t)

theorem wholeLineRepresentative_memLp {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p) :
    MemLp (wholeLineRepresentative u) p volume := by
  have hu := Lp.memLp (sobolevUnderlying u)
  simp only [Opens.coe_top, Measure.restrict_univ] at hu
  exact MemLp.ae_eq (wholeLineRepresentative_spec u).1
    (by simpa only [Function.comp_def, lineIsometry_apply] using
      hu.comp_measurePreserving lineIsometry.measurePreserving)

theorem wholeLineRepresentative_norm_le {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p) (t : ℝ) :
    ‖wholeLineRepresentative u t‖ ≤ 2 * ‖u‖ := by
  have h₀ := Lp.memLp (sobolevUnderlying u)
  have h₁ := Lp.memLp (firstWeakDerivative u 0)
  simp only [Opens.coe_top, Measure.restrict_univ] at h₀ h₁
  have h := ac_value_norm_le (wholeLineRepresentative_memLp u)
    (h₁.comp_measurePreserving lineIsometry.measurePreserving)
    (wholeLineRepresentative_spec u).2.1 (wholeLineRepresentative_spec u).2.2 t
  have he₀ : eLpNorm (wholeLineRepresentative u) p volume =
      eLpNorm (sobolevUnderlying u) p (volume.restrict (⊤ : Opens (Space 1))) := by
    rw [← eLpNorm_congr_ae (wholeLineRepresentative_spec u).1]
    simpa only [Opens.coe_top, Measure.restrict_univ, Function.comp_def, lineIsometry_apply] using
      eLpNorm_comp_measurePreserving h₀.aestronglyMeasurable lineIsometry.measurePreserving
  have he₁ : eLpNorm (fun s => firstWeakDerivative u 0 (linePoint s)) p volume =
      eLpNorm (firstWeakDerivative u 0) p (volume.restrict (⊤ : Opens (Space 1))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ, Function.comp_def, lineIsometry_apply] using
      eLpNorm_comp_measurePreserving h₁.aestronglyMeasurable lineIsometry.measurePreserving
  simp only [Function.comp_def, lineIsometry_apply] at h
  rw [he₀, he₁, ← Lp.norm_def, ← Lp.norm_def] at h
  have hbase : ‖sobolevUnderlying u‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val _
  have hder : ‖firstWeakDerivative u 0‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val _
  linarith

/-- Evaluation of the unique continuous whole-line representative is bounded
and scalar-linear, proved from a.e. linearity and the unit-interval estimate. -/
def wholeLineEvaluation {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (t : ℝ) :
    Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun u := wholeLineRepresentative u t
      map_add' u v := by
        have he := wholeLineRepresentative_eq (u + v)
          (fun s => wholeLineRepresentative u s + wholeLineRepresentative v s)
          ((wholeLineRepresentative_continuous u).add (wholeLineRepresentative_continuous v))
          (by
            have hsum := linePoint_ae_restrict
              (Ω := (⊤ : Opens (Space 1)))
              (Lp.coeFn_add (sobolevUnderlying u) (sobolevUnderlying v))
            simp only [Opens.coe_top, preimage_univ, Measure.restrict_univ] at hsum
            filter_upwards [hsum, (wholeLineRepresentative_spec u).1,
              (wholeLineRepresentative_spec v).1] with s hs hu hv
            change (sobolevUnderlying u + sobolevUnderlying v : DomainLp 𝕜 ⊤ p)
              (linePoint s) = _
            rw [hs, Pi.add_apply, hu, hv])
        exact congrFun he t
      map_smul' c u := by
        have he := wholeLineRepresentative_eq (c • u)
          (fun s => c • wholeLineRepresentative u s)
          ((wholeLineRepresentative_continuous u).const_smul c)
          (by
            have hsmul := linePoint_ae_restrict
              (Ω := (⊤ : Opens (Space 1))) (Lp.coeFn_smul c (sobolevUnderlying u))
            simp only [Opens.coe_top, preimage_univ, Measure.restrict_univ] at hsmul
            filter_upwards [hsmul, (wholeLineRepresentative_spec u).1] with s hs hu
            change (c • sobolevUnderlying u : DomainLp 𝕜 ⊤ p) (linePoint s) = _
            rw [hs, Pi.smul_apply, hu])
        exact congrFun he t }
    2 (fun u => wholeLineRepresentative_norm_le u t)

/-- Boundary point evaluation in dimension one is bounded because each
frontier point is a counting atom of mass one. -/
theorem boundary_value_norm_le {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (g : BoundaryLp 𝕜 Ω p) {x : Space 1} (hx : x ∈ frontier (Ω : Set (Space 1))) :
    ‖g x‖ ≤ ‖g‖ := by
  have hmass : boundaryMeasure Ω {x} = 1 := by
    rw [boundaryMeasure_one_dimension, Measure.restrict_apply (measurableSet_singleton x),
      inter_eq_left.mpr (singleton_subset_iff.mpr hx)]
    simp
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hi := le_eLpNorm_of_bddBelow' (μ := boundaryMeasure Ω)
    (f := (g : Space 1 → 𝕜)) hp0 hp ‖g x‖ₑ
    (s := {x}) (Eventually.of_forall fun y hy => by
      simpa only [mem_singleton_iff.mp hy] using (le_rfl : ‖g x‖ₑ ≤ ‖g x‖ₑ))
  rw [hmass, ENNReal.one_rpow, mul_one] at hi
  have h := ENNReal.toReal_mono (Lp.memLp g).eLpNorm_ne_top hi
  simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm, Lp.norm_def] using h

/-- The physical boundary Lp evaluation, defined using the actual quotient
representative and justified by positive singleton mass. -/
def boundaryEvaluation {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (x : Space 1) (hx : x ∈ frontier (Ω : Set (Space 1))) : BoundaryLp 𝕜 Ω p →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun g := g x
      map_add' g h := boundary_ae_eq_at_one_dimension Ω (Lp.coeFn_add g h) hx
      map_smul' c g := boundary_ae_eq_at_one_dimension Ω (Lp.coeFn_smul c g) hx }
    1 (fun g => by
      change ‖g x‖ ≤ 1 * ‖g‖
      simpa only [one_mul] using boundary_value_norm_le hp g hx)


/-- Continuous real-coordinate representatives of the same bulk class agree
on the closure of each component interval. -/
theorem line_representative_eqOn {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : Sobolev 𝕜 Ω 1 p} {f g : ℝ → 𝕜} {a b : ℝ} (hab : a < b)
    (hsub : Ioo a b ⊆ linePoint ⁻¹' (Ω : Set (Space 1)))
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (huf : ∀ᵐ t ∂volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1))),
      sobolevUnderlying u (linePoint t) = f t)
    (hug : ∀ᵐ t ∂volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1))),
      sobolevUnderlying u (linePoint t) = g t) :
    EqOn f g (Icc a b) := by
  have hfg : f =ᵐ[volume.restrict (linePoint ⁻¹' (Ω : Set (Space 1)))] g := by
    filter_upwards [huf, hug] with t hft hgt
    exact hft.symm.trans hgt
  have heq := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset hsub hfg) isOpen_Ioo
    (hf.mono Ioo_subset_Icc_self) (hg.mono Ioo_subset_Icc_self)
  exact heq.of_subset_closure hf hg Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])

/-- The endpoint values of any bounded trace agreeing on smooth restrictions
are the values of the continuous representative of a bounded extension. -/
theorem trace_extension_endpoint_eq
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)))
    {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (E : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p)
    (hE : ∀ u, sobolevUnderlying (E u) =ᵐ[volume.restrict (Ω : Set (Space 1))]
      sobolevUnderlying u)
    {a b t : ℝ} (hab : a < b)
    (hsub : Ioo a b ⊆ linePoint ⁻¹' (Ω : Set (Space 1)))
    (ht : t ∈ Icc a b) (hfront : linePoint t ∈ frontier (Ω : Set (Space 1)))
    (u : Sobolev 𝕜 Ω 1 p) :
    T u (linePoint t) = wholeLineRepresentative (E u) t := by
  let L := (boundaryEvaluation hp (linePoint t) hfront).comp T
  let R := (wholeLineEvaluation t).comp E
  have hon : EqOn L R (smoothRestrictionSubmodule 𝕜 Ω p) := by
    rintro v ⟨f, hf, hv⟩
    have he : EqOn (wholeLineRepresentative (E v)) (fun s => f (linePoint s)) (Icc a b) :=
      line_representative_eqOn hab hsub
        (wholeLineRepresentative_continuous (E v)).continuousOn
        (hf.continuous.comp lineIsometry.continuous).continuousOn
        (by
          filter_upwards [linePoint_ae_restrict (hE v),
            ae_restrict_of_ae (s := linePoint ⁻¹' (Ω : Set (Space 1)))
              (wholeLineRepresentative_spec (E v)).1] with s hs hs'
          exact hs.symm.trans hs')
        (linePoint_ae_restrict hv)
    change T v (linePoint t) = wholeLineRepresentative (E v) t
    exact (boundary_ae_eq_at_one_dimension Ω (hT v f hf hv) hfront).trans (he ht).symm
  exact hon.closure L.continuous R.continuous
    (smooth_restrictions_dense hDensity e Ω hΩ 𝕜 p hp u)

/-- Dimension-one trace values are precisely the endpoint values of every
absolutely continuous representative on the finitely many component closures.
The additional premises are the full frozen interfaces, in their given order. -/
theorem endpoint_identification_conditional
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (hExtension : P102.Sobolev.Extension.Expected.Extension) :
    Expected.EndpointIdentification := by
  intro e Ω hΩ 𝕜 _ p _ hp T hT
  refine ⟨boundaryMeasure_one_dimension Ω, ?_⟩
  obtain ⟨n, a, b, hab, hinj, hdis, hcover, hfront⟩ := physical_interval_decomposition e Ω hΩ
  have hsub : ∀ i, Ioo (a i) (b i) ⊆ linePoint ⁻¹' (Ω : Set (Space 1)) := by
    intro i t ht
    change linePoint t ∈ (Ω : Set (Space 1))
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
  refine ⟨n, a, b, hab, hinj, hdis, hcover, hfront,
    ⟨‖T‖, norm_nonneg T, fun u => T.le_opNorm u⟩,
    fun u => exists_endpoint_representative hExtension e Ω hΩ a b u, ?_⟩
  obtain ⟨D, K, C, B, hD, hE⟩ := hExtension 0 e Ω hΩ
  obtain ⟨E, hraw, hres, hsupp, hnorm, hzero⟩ := hE 𝕜 p
  intro u f hf i
  have he : EqOn (wholeLineRepresentative (E u)) f (Icc (a i) (b i)) :=
    line_representative_eqOn (hab i) (hsub i)
      (wholeLineRepresentative_continuous (E u)).continuousOn
      (by simpa only [uIcc_of_le (hab i).le] using (hf.2.1 i).continuousOn)
      (by
        filter_upwards [linePoint_ae_restrict (hres u),
          ae_restrict_of_ae (s := linePoint ⁻¹' (Ω : Set (Space 1)))
            (wholeLineRepresentative_spec (E u)).1] with t ht ht'
        exact ht.symm.trans ht') hf.1
  have hleft : linePoint (a i) ∈ frontier (Ω : Set (Space 1)) := by
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, by simp⟩
  have hright : linePoint (b i) ∈ frontier (Ω : Set (Space 1)) := by
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, by simp⟩
  constructor
  · exact (trace_extension_endpoint_eq hDensity e Ω hΩ hp T hT E hres
      (hab i) (hsub i) ⟨le_rfl, (hab i).le⟩ hleft u).trans (he ⟨le_rfl, (hab i).le⟩)
  · exact (trace_extension_endpoint_eq hDensity e Ω hΩ hp T hT E hres
      (hab i) (hsub i) ⟨(hab i).le, le_rfl⟩ hright u).trans (he ⟨(hab i).le, le_rfl⟩)


/-- The continuous representative of a whole-line Sobolev class also represents
that class in the physical one-dimensional Euclidean coordinates. -/
theorem wholeLineRepresentative_ae_physical {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space 1)) 1 p) :
    (sobolevUnderlying u : Space 1 → 𝕜) =ᵐ[volume]
      (fun x => wholeLineRepresentative u (lineIsometry.symm x)) := by
  have h := lineIsometry.symm.measurePreserving.quasiMeasurePreserving.ae
    (wholeLineRepresentative_spec u).1
  filter_upwards [h] with x hx
  simpa only [← lineIsometry_apply, lineIsometry.apply_symm_apply] using hx

/-- A numerical smooth trace bound in physical dimension one. This includes
the empty open set and any finite number of component intervals. -/
theorem exists_one_dimension_smooth_trace_bound
    (hExtension : P102.Sobolev.Extension.Expected.Extension)
    (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Sobolev 𝕜 Ω 1 p) (f : Space 1 → 𝕜), ContDiff ℝ ∞ f →
      sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space 1))] f →
      (eLpNorm f p (boundaryMeasure Ω)).toReal ≤ C * ‖u‖ := by
  obtain ⟨D, K, A, B, hD, hE⟩ := hExtension 0 e Ω hΩ
  obtain ⟨E, hraw, hres, hsupp, hnorm, hzero⟩ := hE 𝕜 p
  let q : ℝ≥0∞ := boundaryMeasure Ω univ ^ p.toReal⁻¹
  have hq : q ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by positivity)
    (boundaryMeasure_univ_lt_top e Ω hΩ).ne).ne
  refine ⟨q.toReal * (2 * ‖E‖), by positivity, ?_⟩
  intro u f hf hu
  let g : Space 1 → 𝕜 := fun x => wholeLineRepresentative (E u) (lineIsometry.symm x)
  have hg : Continuous g := (wholeLineRepresentative_continuous (E u)).comp
    lineIsometry.symm.continuous
  have hgu : g =ᵐ[volume.restrict (Ω : Set (Space 1))] f := by
    filter_upwards [ae_restrict_of_ae (s := (Ω : Set (Space 1)))
      (wholeLineRepresentative_ae_physical (E u)), hres u, hu] with x hgx hex hux
    exact hgx.symm.trans (hex.trans hux)
  have hgf := continuous_boundary_eq_of_ae Ω g f hg hf.continuous hgu
  have hle : eLpNorm f p (boundaryMeasure Ω) ≤ q * ENNReal.ofReal (2 * ‖E‖ * ‖u‖) := by
    apply eLpNorm_le_of_ae_bound hf.continuous.aestronglyMeasurable
    filter_upwards [hgf] with x hx
    rw [← hx]
    change ‖wholeLineRepresentative (E u) (lineIsometry.symm x)‖ ≤ _
    exact (wholeLineRepresentative_norm_le (E u) (lineIsometry.symm x)).trans
      (by nlinarith [E.le_opNorm u])
  have hn : q * ENNReal.ofReal (2 * ‖E‖ * ‖u‖) ≠ ⊤ :=
    ENNReal.mul_ne_top hq ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hn hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  simpa only [mul_assoc] using h

/-- The full trace conclusion, including canonicity, in dimension one. -/
theorem trace_exists_one_dimension_conditional
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (hExtension : P102.Sobolev.Extension.Expected.Extension)
    (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∃ T : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p,
      IsTrace T ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ S : Sobolev 𝕜 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace S → S = T := by
  obtain ⟨C, hC, hb⟩ := exists_one_dimension_smooth_trace_bound hExtension e Ω hΩ 𝕜 p
  obtain ⟨T, hT, hbound⟩ := exists_trace_of_smooth_bound e Ω hΩ p hDensity hp C hb
  exact ⟨C, hC, T, hT, hbound, fun S hS =>
    trace_uniqueness_conditional hDensity hExtension 0 e Ω hΩ 𝕜 p hp S T hS hT⟩

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary.MeasureTransport

theorem restrict_image_le_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Y) (ν : Measure X) (B : Set X) (hB : MeasurableSet B)
    (b : X → Y) (hb : AEMeasurable b (ν.restrict B)) (c : ℝ≥0∞)
    (hdom : ∀ S : Set X, S ⊆ B → μ (b '' S) ≤ c * ν S) :
    μ.restrict (b '' B) ≤ c • Measure.map b (ν.restrict B) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply,
    Measure.map_apply_of_aemeasurable hb hS, Measure.restrict_apply' hB]
  have he : S ∩ b '' B = b '' (b ⁻¹' S ∩ B) := by
    ext y
    constructor
    · rintro ⟨hyS, x, hxB, rfl⟩
      exact ⟨x, ⟨hyS, hxB⟩, rfl⟩
    · rintro ⟨x, ⟨hxS, hxB⟩, rfl⟩
      exact ⟨hxS, x, hxB, rfl⟩
  rw [he]
  exact hdom _ inter_subset_right

theorem eLpNorm_le_of_restrict_image_domination
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E]
    (μ : Measure Y) (ν : Measure X) (B : Set X) (hB : MeasurableSet B)
    (b : X → Y) (hb : AEMeasurable b (ν.restrict B)) (c : ℝ≥0∞)
    (hdom : ∀ S : Set X, S ⊆ B → μ (b '' S) ≤ c * ν S)
    (p : ℝ≥0∞) (f : Y → E)
    (hf : AEStronglyMeasurable f (Measure.map b (ν.restrict B))) :
    eLpNorm f p (μ.restrict (b '' B)) ≤
      c ^ (1 / p).toReal * eLpNorm (f ∘ b) p (ν.restrict B) := by
  calc
    _ ≤ eLpNorm f p (c • Measure.map b (ν.restrict B)) :=
      eLpNorm_mono_measure f (restrict_image_le_map μ ν B hB b hb c hdom)
    _ ≤ c ^ (1 / p).toReal * eLpNorm f p (Measure.map b (ν.restrict B)) :=
      eLpNorm_smul_measure_le c f p _
    _ = _ := by rw [eLpNorm_map_measure hf hb]

theorem eLpNorm_restrict_le_of_ae_zero
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (S T : Set X) (hT : MeasurableSet T)
    (p : ℝ≥0∞) (f : X → E)
    (hzero : ∀ᵐ x ∂μ.restrict S, x ∉ T → f x = 0) :
    eLpNorm f p (μ.restrict S) ≤ eLpNorm f p (μ.restrict T) := by
  classical
  have he : f =ᵐ[μ.restrict S] T.indicator f := by
    filter_upwards [hzero] with x hx
    by_cases ht : x ∈ T
    · exact (indicator_of_mem ht f).symm
    · rw [indicator_of_notMem ht f, hx ht]
  rw [eLpNorm_congr_ae he]
  exact (eLpNorm_restrict_le _ p μ S).trans_eq
    (eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet)

end P102.Trace.Ordinary.MeasureTransport

namespace P102.Trace.Ordinary
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry

/-- Physical graph surface measure is dominated by a finite multiple of base volume. -/
theorem physical_graph_measure_le_map
    {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (B : Set (Space m)) (hB : MeasurableSet B)
    (γ : Space m → ℝ) (L : ℝ≥0) (hL : LipschitzOnWith L γ B) :
    (μHE[m] : Measure (Space (m + 1))).restrict ((e ∘ F ∘ graph γ) '' B) ≤
      ((graphConstant L : ℝ≥0∞) ^ m) •
        Measure.map (e ∘ F ∘ graph γ) (volume.restrict B) := by
  have hgeom := graph_geometry_in_frame m B γ L hL F
  have hb : AEMeasurable (e ∘ F ∘ graph γ) (volume.restrict B) :=
    (e.continuous.comp_continuousOn hgeom.1.continuousOn).aemeasurable hB
  apply MeasureTransport.restrict_image_le_map _ volume B hB _ hb
  intro S hS
  rw [Set.image_comp, e.isometry.euclideanHausdorffMeasure_image]
  exact (hgeom.2.2 S hS).2

/-- Lp upper transport from a physical Lipschitz graph to its base. -/
theorem physical_graph_eLpNorm_le
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (B : Set (Space m)) (hB : MeasurableSet B)
    (γ : Space m → ℝ) (L : ℝ≥0) (hL : LipschitzOnWith L γ B)
    (p : ℝ≥0∞) (f : Space (m + 1) → 𝕜) (hf : Continuous f) :
    eLpNorm f p ((μHE[m] : Measure (Space (m + 1))).restrict
        ((e ∘ F ∘ graph γ) '' B)) ≤
      ((graphConstant L : ℝ≥0∞) ^ m) ^ (1 / p).toReal *
        eLpNorm (f ∘ e ∘ F ∘ graph γ) p (volume.restrict B) := by
  have hgeom := graph_geometry_in_frame m B γ L hL F
  have hb : AEMeasurable (e ∘ F ∘ graph γ) (volume.restrict B) :=
    (e.continuous.comp_continuousOn hgeom.1.continuousOn).aemeasurable hB
  calc
    _ ≤ eLpNorm f p (((graphConstant L : ℝ≥0∞) ^ m) •
        Measure.map (e ∘ F ∘ graph γ) (volume.restrict B)) :=
      eLpNorm_mono_measure f (physical_graph_measure_le_map e F B hB γ L hL)
    _ ≤ ((graphConstant L : ℝ≥0∞) ^ m) ^ (1 / p).toReal *
        eLpNorm f p (Measure.map (e ∘ F ∘ graph γ) (volume.restrict B)) :=
      eLpNorm_smul_measure_le _ f p _
    _ = _ := by rw [eLpNorm_map_measure hf.aestronglyMeasurable hb]

open P102.Sobolev.Extension

/-- The physical graph patch is exactly the boundary inside the full chart. -/
theorem physical_graph_image_eq
    {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : TopologicalSpace.Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) :
    (e ∘ C.frame ∘ graph C.graphFunction) '' Metric.ball C.center C.radius =
      frontier (Ω : Set (Space (m + 1))) ∩
        e '' chartImage C.frame C.graphFunction C.center C.radius C.height := by
  have hfrontier : e '' frontier (geometricOpen e Ω : Set (Ambient m)) =
      frontier (Ω : Set (Space (m + 1))) := by
    calc
      _ = frontier (e '' (geometricOpen e Ω : Set (Ambient m))) :=
        e.toHomeomorph.image_frontier _
      _ = _ := congrArg frontier (e.image_preimage _)
  rw [Set.image_comp, Set.image_comp, ← C.boundary, image_inter e.injective, hfrontier]

/-- A cutoff supported in a boundary chart has its entire boundary norm on
that chart's graph patch. Only the topological support inclusion is needed. -/
theorem cutoff_boundary_eLpNorm_le_graph
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : TopologicalSpace.Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (χ : Space (m + 1) → ℝ)
    (hχ : tsupport χ ⊆
      e '' chartImage C.frame C.graphFunction C.center C.radius C.height)
    (p : ℝ≥0∞) (f : Space (m + 1) → 𝕜) :
    eLpNorm (fun x => χ x • f x) p (boundaryMeasure Ω) ≤
      eLpNorm (fun x => χ x • f x) p
        ((μHE[m] : Measure (Space (m + 1))).restrict
          ((e ∘ C.frame ∘ graph C.graphFunction) '' Metric.ball C.center C.radius)) := by
  have hP : MeasurableSet
      ((e ∘ C.frame ∘ graph C.graphFunction) '' Metric.ball C.center C.radius) := by
    rw [physical_graph_image_eq e Ω C]
    exact isClosed_frontier.measurableSet.inter
      (e.toHomeomorph.isOpenMap _ (chartImage_open C.frame C.graph_lipschitz)).measurableSet
  apply MeasureTransport.eLpNorm_restrict_le_of_ae_zero _ _ _ hP
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx hnot
  have hz : χ x = 0 := by
    by_contra hne
    apply hnot
    rw [physical_graph_image_eq e Ω C]
    exact ⟨hx, hχ (subset_tsupport χ hne)⟩
  rw [hz, zero_smul]

/-- The localized physical boundary norm is bounded by its parametrized
base norm, with the correct Euclidean surface distortion. -/
theorem cutoff_boundary_eLpNorm_le_base
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : TopologicalSpace.Opens (Space (m + 1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (χ : Space (m + 1) → ℝ) (hc : Continuous χ)
    (hχ : tsupport χ ⊆
      e '' chartImage C.frame C.graphFunction C.center C.radius C.height)
    (p : ℝ≥0∞) (f : Space (m + 1) → 𝕜) (hf : Continuous f) :
    eLpNorm (fun x => χ x • f x) p (boundaryMeasure Ω) ≤
      ((graphConstant C.constant : ℝ≥0∞) ^ m) ^ (1 / p).toReal *
        eLpNorm ((fun x => χ x • f x) ∘ e ∘ C.frame ∘ graph C.graphFunction)
          p (volume.restrict (Metric.ball C.center C.radius)) :=
  (cutoff_boundary_eLpNorm_le_graph e Ω C χ hχ p f).trans
    (physical_graph_eLpNorm_le e C.frame _ Metric.isOpen_ball.measurableSet
      C.graphFunction C.constant C.graph_lipschitz p _ (hc.smul hf))

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry P102.Sobolev.Extension

/-- Summing finitely many localized smooth trace bounds gives the physical
boundary estimate. The only partition identity needed is on the frontier. -/
theorem smooth_trace_bound_of_local_bounds
    {m n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (χ : Fin n → Space (m + 1) → ℝ) (hχ : ∀ i, Continuous (χ i))
    (hpart : ∀ x ∈ frontier (Ω : Set (Space (m + 1))), ∑ i, χ i x = 1)
    (C : Fin n → ℝ)
    (hbound : ∀ i (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜),
      ContDiff ℝ ∞ f →
      sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f →
      (eLpNorm (fun x => χ i x • f x) p (boundaryMeasure Ω)).toReal ≤ C i * ‖u‖) :
    ∀ (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜), ContDiff ℝ ∞ f →
      sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f →
      (eLpNorm f p (boundaryMeasure Ω)).toReal ≤ (∑ i, C i) * ‖u‖ := by
  classical
  intro u f hf hu
  let hF := continuous_boundary_memLp e Ω hΩ p f hf.continuous
  let hG (i : Fin n) := continuous_boundary_memLp e Ω hΩ p
    (fun x => χ i x • f x) ((hχ i).smul hf.continuous)
  let F : BoundaryLp 𝕜 Ω p := hF.toLp f
  let G (i : Fin n) : BoundaryLp 𝕜 Ω p := (hG i).toLp _
  have hsum : F = ∑ i, G i := by
    apply Lp.ext
    have hGs : ∀ᵐ x ∂boundaryMeasure Ω, ∀ i, G i x = χ i x • f x :=
      ae_all_iff.mpr (fun i => (hG i).coeFn_toLp)
    filter_upwards [hF.coeFn_toLp, Lp.coeFn_fun_finsetSum Finset.univ G, hGs,
      boundaryMeasure_ae_frontier Ω] with x hx hsumx hGx hfront
    rw [hx, hsumx]
    simp_rw [hGx]
    rw [← Finset.sum_smul, hpart x hfront, one_smul]
  rw [← Lp.norm_toLp f hF]
  change ‖F‖ ≤ _
  rw [hsum]
  calc
    ‖∑ i, G i‖ ≤ ∑ i, ‖G i‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [Lp.norm_toLp]
      exact hbound i u f hf hu
    _ = _ := (Finset.sum_mul _ _ _).symm


/-- A finite physical-coordinate smooth partition on the boundary. Its interior
member vanishes there, and every other support stays inside its actual chart. -/
theorem physical_boundary_localization {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) :
    ∃ (n : ℕ) (C : Fin n → BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
      (χ : Fin (n + 1) → Space (m + 1) → ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧ ∀ x, 0 ≤ χ i x) ∧
      (∀ x ∈ frontier (Ω : Set (Space (m + 1))), χ 0 x = 0) ∧
      (∀ x ∈ frontier (Ω : Set (Space (m + 1))), ∑ i : Fin n, χ i.succ x = 1) ∧
      ∀ i : Fin n, tsupport (χ i.succ) ⊆
        e '' chartImage (C i).frame (C i).graphFunction (C i).center (C i).radius (C i).height := by
  obtain ⟨n, C, r, a, hra, hcover, V, ψ, hVo, hΩV, hψ, hsum, hint, hsep, hsupp⟩ :=
    finite_localization m (geometricOpen e Ω : Set (Ambient m)) hΩ
  have hfront (x : Space (m + 1)) (hx : x ∈ frontier (Ω : Set (Space (m + 1)))) :
      e.symm x ∈ frontier (geometricOpen e Ω : Set (Ambient m)) := by
    change e.symm x ∈ frontier (e.toHomeomorph ⁻¹' (Ω : Set (Space (m + 1))))
    rw [← e.toHomeomorph.preimage_frontier]
    change e (e.symm x) ∈ frontier (Ω : Set (Space (m + 1)))
    simpa only [e.apply_symm_apply] using hx
  have hzero (x : Space (m + 1)) (hx : x ∈ frontier (Ω : Set (Space (m + 1)))) :
      ψ 0 (e.symm x) = 0 := by
    have hb := hfront x hx
    rw [hΩ.1.frontier_eq] at hb
    by_contra hn
    exact hb.2 (hint (subset_tsupport _ (show e.symm x ∈ Function.support (ψ 0) from hn)))
  refine ⟨n, C, (fun i => ψ i ∘ e.symm), ?_, hzero, ?_, ?_⟩
  · intro i
    exact ⟨(hψ i).1.comp e.symm.contDiff,
      (hψ i).2.1.comp_homeomorph e.symm.toHomeomorph, fun x => (hψ i).2.2 _⟩
  · intro x hx
    have hs := hsum (e.symm x) (hΩV (frontier_subset_closure (hfront x hx)))
    rw [Fin.sum_univ_succ, hzero x hx, zero_add] at hs
    exact hs
  · intro i x hx
    change x ∈ tsupport (ψ i.succ ∘ e.symm.toHomeomorph) at hx
    rw [tsupport_comp_eq_preimage _ e.symm.toHomeomorph] at hx
    have hy := chartImage_mono (C i).frame (C i).graphFunction (C i).center
      (hra i).2.1.le (hra i).2.2.2.le (hsupp i hx)
    exact ⟨e.symm x, hy, e.apply_symm_apply x⟩

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry P102.Sobolev.Extension


/-- Smooth compactly supported physical cutoffs act by bounded scalar-linear
operators on whole-space Sobolev classes. -/
theorem exists_whole_space_cutoffCLM {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (χ : Space d → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ N : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
      ∀ u, sobolevUnderlying (N u) =ᵐ[volume]
        (fun x => χ x • sobolevUnderlying u x) := by
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
  have hex (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
      ∃ v : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
        sobolevUnderlying v =ᵐ[volume.restrict (⊤ : Opens (Space d))]
          (fun x => χ x • sobolevUnderlying u x) := by
    let a : WholeTests d 𝕜 :=
      ⟨fun x => χ x • (1 : 𝕜), hχ.smul contDiff_const, hc.smul_right, subset_univ _⟩
    obtain ⟨v, hv⟩ := sobolev_testMul 1 p u a
    refine ⟨v, ?_⟩
    simp only [Opens.coe_top, Measure.restrict_univ]
    rw [hv]
    filter_upwards [testMulLp_ae a (sobolevUnderlying u)] with x hx
    exact hx.trans (by
      change (χ x • (1 : 𝕜)) * sobolevUnderlying u x = _
      simp only [smul_mul_assoc, one_mul])
  obtain ⟨N, hN⟩ := exists_sobolev_cutoffCLM (⊤ : Opens (Space d)) p χ
    hχ.continuous.aestronglyMeasurable C hC hex
  exact ⟨N, by simpa only [Opens.coe_top, Measure.restrict_univ] using hN⟩

/-- Assembly of trace existence from actual localized chart inequalities. -/
theorem trace_exists_of_chart_bounds
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (hExtension : P102.Sobolev.Extension.Expected.Extension)
    (hChart : ∀ {m : ℕ}, 1 ≤ m →
      ∀ (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
        (_hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
        (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
      ∀ (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
        (χ : Space (m + 1) → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ e '' chartImage C.frame C.graphFunction C.center C.radius C.height →
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜), ContDiff ℝ ∞ f →
        sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f →
        (eLpNorm (fun x => χ x • f x) p (boundaryMeasure Ω)).toReal ≤ A * ‖u‖) :
    Expected.TraceExists := by
  intro m e Ω hΩ 𝕜 _ p _ hp
  cases m with
  | zero => exact trace_exists_one_dimension_conditional hDensity hExtension e Ω hΩ 𝕜 p hp
  | succ m =>
    obtain ⟨n, C, χ, hχ, hinterior, hpart, hsupp⟩ := physical_boundary_localization e Ω hΩ
    have hloc (i : Fin n) := hChart (Nat.succ_le_succ (Nat.zero_le m)) e Ω hΩ 𝕜 p hp
      (C i) (χ i.succ) (hχ i.succ).1 (hχ i.succ).2.1 (hsupp i)
    choose A hA hbound using hloc
    have hb := smooth_trace_bound_of_local_bounds e Ω hΩ p (fun i => χ i.succ)
      (fun i => (hχ i.succ).1.continuous) hpart A hbound
    obtain ⟨T, hT, hnorm⟩ := exists_trace_of_smooth_bound e Ω hΩ p hDensity hp (∑ i, A i) hb
    exact ⟨∑ i, A i, Finset.sum_nonneg (fun i _ => hA i), T, hT, hnorm,
      fun S hS => trace_uniqueness_conditional hDensity hExtension _ e Ω hΩ 𝕜 p hp S T hS hT⟩

end P102.Trace.Ordinary

open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry

namespace P102.Trace.Ordinary

def alignedCoordinates (m : ℕ) : Space (m+1) ≃L[ℝ] Ambient m :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (Space m)).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))) |>.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Space m) ℝ).symm

theorem alignedCoordinates_horizontal (m : ℕ) (x : Space (m+1)) (i : Fin m) :
    (alignedCoordinates m x).ofLp.1 i = x i.castSucc := by
  simp [alignedCoordinates, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, ContinuousLinearEquiv.trans_apply,
    PiLp.sumPiLpEquivProdLpPiLp, LinearIsometryEquiv.piLpCongrLeft,
    LinearEquiv.sumPiEquivProdPi]
  rfl

theorem alignedCoordinates_height (m : ℕ) (x : Space (m+1)) :
    (alignedCoordinates m x).ofLp.2 = x (Fin.last m) := by
  simp [alignedCoordinates, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, ContinuousLinearEquiv.trans_apply,
    PiLp.sumPiLpEquivProdLpPiLp, LinearIsometryEquiv.piLpCongrLeft,
    LinearEquiv.sumPiEquivProdPi]
  rfl


/-- A global flattening from aligned Euclidean coordinates to the physical space. -/
def globalGraphChart {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (frame : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ) (L : ℝ≥0)
    (hγ : LipschitzWith L γ) :
    BiLipschitzChart (⊤ : Opens (Space (m+1))) ⊤
      (shearConstant L * ‖(alignedCoordinates m).toContinuousLinearMap‖₊)
      (‖(alignedCoordinates m).symm.toContinuousLinearMap‖₊ * shearConstant L) where
  toFun x := e (frame (shear γ (alignedCoordinates m x)))
  invFun y := (alignedCoordinates m).symm (unshear γ (frame.symm (e.symm y)))
  mapsTo := fun _ _ => mem_univ _
  inv_mapsTo := fun _ _ => mem_univ _
  left_inv x _ := by simp
  right_inv y _ := by simp
  lipschitz := by
    have h := e.lipschitzWith.comp
      (frame.isometry.lipschitzWith.comp
        ((shear_lipschitzWith hγ).comp (alignedCoordinates m).toContinuousLinearMap.lipschitzWith))
    apply LipschitzOnWith.of_dist_le_mul
    intro x _ y _
    simpa only [one_mul, Function.comp_def, ContinuousLinearEquiv.coe_coe] using h.dist_le_mul x y
  inv_lipschitz := by
    have hU : LipschitzWith (shearConstant L) (unshear γ) := by
      rw [unshear_eq_shear_neg]
      exact shear_lipschitzWith hγ.neg
    have h := (alignedCoordinates m).symm.toContinuousLinearMap.lipschitzWith.comp
      (hU.comp (frame.symm.isometry.lipschitzWith.comp e.symm.lipschitzWith))
    apply LipschitzOnWith.of_dist_le_mul
    intro x _ y _
    simpa only [one_mul, mul_one, Function.comp_def, ContinuousLinearEquiv.coe_coe] using h.dist_le_mul x y

/-- Inside a boundary chart, positive flattened height is precisely the domain side. -/
theorem globalGraphChart_positive {m : ℕ} {G : Set (Ambient m)}
    (C : BoundaryChart G) (γ : Space m → ℝ)
    (hγ : EqOn γ C.graphFunction (Metric.ball C.center C.radius))
    (z : Ambient m)
    (hz : C.frame (shear γ z) ∈ chartImage C.frame C.graphFunction C.center C.radius C.height)
    (hpos : 0 < z.ofLp.2) : C.frame (shear γ z) ∈ G := by
  rw [chartImage_eq_of_eqOn C.frame hγ.symm] at hz
  obtain ⟨w, ⟨v, hv, rfl⟩, he⟩ := hz
  have hvz : v = z := (shearEquiv γ).injective (C.frame.injective he)
  subst v
  have hs : shear γ z = shear C.graphFunction z := by
    simp only [shear, hγ hv.1]
  have hmem : C.frame (shear γ z) ∈ G ∩
      chartImage C.frame C.graphFunction C.center C.radius C.height := by
    rw [C.side]
    refine ⟨shear C.graphFunction z, ⟨z, ?_, rfl⟩, ?_⟩
    · exact ⟨hv.1, hpos, hv.2.2⟩
    · rw [hs]
  exact hmem.1

/-- The horizontal transverse coordinates, now with the shared Euclidean norm. -/
def boundaryBase (m : ℕ) (z : P102.Trace.Boundary m) : Space m :=
  WithLp.toLp 2 (fun i => z (finSuccAboveEquiv (Fin.last m) i))

theorem alignedCoordinates_point (m : ℕ) (z : P102.Trace.Boundary m) (t : ℝ) :
    alignedCoordinates m (P102.Trace.point m z t) = WithLp.toLp 2 (boundaryBase m z, t) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change (alignedCoordinates m (P102.Trace.point m z t)).ofLp.1 i = boundaryBase m z i
    rw [alignedCoordinates_horizontal]
    simp [boundaryBase, P102.Trace.point, ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine,
      finSuccAboveEquiv_apply]
  · change (alignedCoordinates m (P102.Trace.point m z t)).ofLp.2 = t
    rw [alignedCoordinates_height]
    simp [P102.Trace.point, ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine]

/-- Localized pullback after extension has the expected continuous representative
on the positive half-space; support localization is the only geometric input. -/
theorem localized_pullback_agreement
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Ω : Opens (Space (m+1))) {L M : ℝ≥0}
    (g : BiLipschitzChart (⊤ : Opens (Space (m+1))) ⊤ L M)
    (E : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p)
    (hE : ∀ u, sobolevUnderlying (E u) =ᵐ[volume.restrict (Ω : Set (Space (m+1)))]
      sobolevUnderlying u)
    (χ : Space (m+1) → ℝ)
    (N : Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p)
    (hN : ∀ u, sobolevUnderlying (N u) =ᵐ[volume]
      (fun x => χ x • sobolevUnderlying u x))
    (P : Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p)
    (hP : ∀ u, sobolevUnderlying (P u) =ᵐ[volume]
      (fun x => sobolevUnderlying u (g.toFun x)))
    (hside : ∀ x ∈ (P102.Trace.halfSpace m : Set (Space (m+1))),
      χ (g.toFun x) ≠ 0 → g.toFun x ∈ (Ω : Set (Space (m+1))))
    (u : Sobolev 𝕜 Ω 1 p) (f : Space (m+1) → 𝕜)
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m+1)))] f) :
    sobolevUnderlying (sobolevRestrict (P102.Trace.halfSpace m) (P (N (E u))))
      =ᵐ[volume.restrict (P102.Trace.halfSpace m : Set (Space (m+1)))]
      (fun x => χ (g.toFun x) • f (g.toFun x)) := by
  have hEglobal : ∀ᵐ y ∂volume, y ∈ (Ω : Set (Space (m+1))) →
      sobolevUnderlying (E u) y = f y :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).mp ((hE u).trans hu)
  have hEg : ∀ᵐ x ∂volume, g.toFun x ∈ (Ω : Set (Space (m+1))) →
      sobolevUnderlying (E u) (g.toFun x) = f (g.toFun x) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      g.ae_comp (by simpa only [Opens.coe_top, Measure.restrict_univ] using hEglobal)
  have hNg : ∀ᵐ x ∂volume, sobolevUnderlying (N (E u)) (g.toFun x) =
      χ (g.toFun x) • sobolevUnderlying (E u) (g.toFun x) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      g.ae_comp (by simpa only [Opens.coe_top, Measure.restrict_univ] using (show ∀ᵐ y ∂volume, sobolevUnderlying (N (E u)) y = χ y • sobolevUnderlying (E u) y from hN (E u)))
  filter_upwards [P102.U4.domainLpRestrict_ae (P102.Trace.halfSpace m)
      (sobolevUnderlying (P (N (E u)))),
    ae_restrict_of_ae (hP (N (E u))), ae_restrict_of_ae hNg,
    ae_restrict_of_ae hEg, ae_restrict_mem (P102.Trace.halfSpace m).isOpen.measurableSet]
    with x hx hpx hnx hex hxH
  change P102.U4.domainLpRestrict (P102.Trace.halfSpace m) (sobolevUnderlying (P (N (E u)))) x = _
  rw [hx, hpx, hnx]
  by_cases hχ : χ (g.toFun x) = 0
  · simp [hχ]
  · rw [hex (hside x hxH hχ)]

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary
open MeasureTheory

/-- The actual transverse-to-Euclidean base identification preserves Lebesgue measure. -/
theorem boundaryBase_measurePreserving (m : ℕ) :
    MeasurePreserving (boundaryBase m) volume volume := by
  have h := (PiLp.volume_preserving_toLp (Fin m)).comp
    ((P102.Trace.boundaryCoordinates_measurePreserving m).symm
      (P102.Trace.boundaryCoordinates m))
  exact h

/-- Restricting the graph base costs no flat-boundary Lp norm. The agreement
is needed only over the base set, so a local graph extension is sufficient. -/
theorem eLpNorm_base_restrict_le_boundary
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (B : Set (Space m)) (hB : MeasurableSet B)
    (p : ℝ≥0∞) (h : Space m → 𝕜)
    (hh : AEStronglyMeasurable h (volume.restrict B))
    (v : P102.Trace.Boundary m → 𝕜)
    (hv : ∀ z, boundaryBase m z ∈ B → h (boundaryBase m z) = v z) :
    eLpNorm h p (volume.restrict B) ≤ eLpNorm v p volume := by
  have hmp := (boundaryBase_measurePreserving m).restrict_preimage hB
  rw [← eLpNorm_comp_measurePreserving hh hmp]
  have he : (h ∘ boundaryBase m) =ᵐ[
      volume.restrict (boundaryBase m ⁻¹' B)] v := by
    filter_upwards [ae_restrict_mem ((boundaryBase_measurePreserving m).measurable hB)] with z hz
    exact hv z hz
  rw [eLpNorm_congr_ae he]
  exact eLpNorm_restrict_le v p volume _

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary
open P102.Sobolev.Extension

set_option maxHeartbeats 600000 in
theorem exists_chart_smooth_trace_bound_of_multiplier
    (hExtension : P102.Sobolev.Extension.Expected.Extension)
    {m : ℕ} (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (Ω : Opens (Space (m+1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (χ : Space (m+1) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (_hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ e '' chartImage C.frame C.graphFunction C.center C.radius C.height)
    (N : Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p)
    (hN : ∀ u, sobolevUnderlying (N u) =ᵐ[volume]
      (fun x => χ x • sobolevUnderlying u x))
    (hside : ∀ (γ : Space m → ℝ) (hγ : LipschitzWith C.constant γ),
      EqOn γ C.graphFunction (Metric.ball C.center C.radius) →
      ∀ x ∈ (P102.Trace.halfSpace m : Set (Space (m+1))),
        χ ((globalGraphChart e C.frame γ C.constant hγ).toFun x) ≠ 0 →
        (globalGraphChart e C.frame γ C.constant hγ).toFun x ∈ (Ω : Set (Space (m+1)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : Sobolev 𝕜 Ω 1 p) (f : Space (m+1) → 𝕜),
      ContDiff ℝ ∞ f →
      sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m+1)))] f →
      (eLpNorm (fun x => χ x • f x) p (boundaryMeasure Ω)).toReal ≤ B * ‖u‖ := by
  obtain ⟨γ, hγ, heq⟩ := C.graph_lipschitz.extend_real
  let g := globalGraphChart e C.frame γ C.constant hγ
  obtain ⟨D, K, CE, BE, hraw, hex⟩ := hExtension m e Ω hΩ
  obtain ⟨E, hEraw, hE, hEsupport, hEnorm, hElp⟩ := hex 𝕜 p
  obtain ⟨P, hP, hPderiv, hPnorm⟩ :=
    bilipschitz_sobolevPullback (m+1) (by omega) 𝕜 ⊤ ⊤ _ _ g p
  simp only [Opens.coe_top, Measure.restrict_univ, Function.comp_def] at hP
  obtain ⟨CT, hCT, T, hTnorm, hTrep, hTcompat⟩ :=
    P102.Trace.flat_trace_exists m hm 𝕜 p hp
  let R : Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p →L[𝕜]
      P102.Trace.HalfSobolev m 𝕜 p := sobolevRestrictCLM (P102.Trace.halfSpace m)
  let A : Sobolev 𝕜 Ω 1 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p :=
    T.comp (R.comp (P.comp (N.comp E)))
  let J : ℝ≥0∞ := ((graphConstant C.constant : ℝ≥0∞) ^ m) ^ (1 / p).toReal
  refine ⟨J.toReal * ‖A‖, mul_nonneg ENNReal.toReal_nonneg (ContinuousLinearMap.opNorm_nonneg _), ?_⟩
  intro u f hf hu
  let r : Space (m+1) → 𝕜 := fun x => χ (g.toFun x) • f (g.toFun x)
  have hgcont : Continuous g.toFun := continuousOn_univ.mp g.lipschitz.continuousOn
  have hr : Continuous r := (hχ.continuous.comp hgcont).smul (hf.continuous.comp hgcont)
  have hrep : sobolevUnderlying (R (P (N (E u)))) =ᵐ[
      volume.restrict (P102.Trace.halfSpace m : Set (Space (m+1)))] r := by
    exact localized_pullback_agreement Ω g E hE χ N hN P hP
      (hside γ hγ heq.symm) u f hu
  have htr := hTcompat (R (P (N (E u)))) r hr.continuousOn hrep
  let v : P102.Trace.Boundary m → 𝕜 :=
    fun z => χ (e (C.frame (graph γ (boundaryBase m z)))) •
      f (e (C.frame (graph γ (boundaryBase m z))))
  have htr' : (A u : P102.Trace.Boundary m → 𝕜) =ᵐ[volume] v := by
    simpa [A, ContinuousLinearMap.comp_apply, r, g, v, globalGraphChart,
      alignedCoordinates_point, shear, graph] using htr
  let H : Space m → 𝕜 := (fun x => χ x • f x) ∘ e ∘ C.frame ∘ graph C.graphFunction
  have hH : AEStronglyMeasurable H (volume.restrict (Metric.ball C.center C.radius)) := by
    have hg := (P102.U4.GraphArea.graph_lipschitzOn C.graph_lipschitz).continuousOn
    exact (((hχ.continuous.smul hf.continuous).comp e.continuous).comp
      C.frame.continuous).comp_continuousOn hg |>.aestronglyMeasurable
        Metric.isOpen_ball.measurableSet
  have hbase : eLpNorm H p (volume.restrict (Metric.ball C.center C.radius)) ≤
      eLpNorm v p volume := by
    apply eLpNorm_base_restrict_le_boundary _ Metric.isOpen_ball.measurableSet p H hH v
    intro z hz
    dsimp [H, v, Function.comp_def]
    simp only [graph, heq hz]
  have hbound : eLpNorm (fun x => χ x • f x) p (boundaryMeasure Ω) ≤
      J * eLpNorm (A u) p volume := by
    calc
      _ ≤ J * eLpNorm H p (volume.restrict (Metric.ball C.center C.radius)) :=
        cutoff_boundary_eLpNorm_le_base e Ω C χ hχ.continuous hsupp p f hf.continuous
      _ ≤ J * eLpNorm v p volume := mul_le_mul_right hbase J
      _ = _ := by rw [eLpNorm_congr_ae htr']
  have hJ : J ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (by simp)
  have hfinite : J * eLpNorm (A u) p volume ≠ ⊤ :=
    ENNReal.mul_ne_top hJ (Lp.memLp (A u)).ne
  have hreal := ENNReal.toReal_mono hfinite hbound
  rw [ENNReal.toReal_mul, ← Lp.norm_def] at hreal
  calc
    _ ≤ J.toReal * ‖A u‖ := hreal
    _ ≤ J.toReal * (‖A‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm u) ENNReal.toReal_nonneg
    _ = _ := (mul_assoc _ _ _).symm

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary
open P102.Sobolev.Extension

/-- The localized global pullback sees the domain on every positive-height
point where the physical cutoff is nonzero. -/
theorem localized_globalGraphChart_side
    {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (Ω : Opens (Space (m+1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (γ : Space m → ℝ) (L : ℝ≥0) (hγ : LipschitzWith L γ)
    (hγEq : EqOn γ C.graphFunction (Metric.ball C.center C.radius))
    (χ : Space (m+1) → ℝ)
    (hsupp : tsupport χ ⊆
      e '' chartImage C.frame C.graphFunction C.center C.radius C.height) :
    ∀ x ∈ (P102.Trace.halfSpace m : Set (Space (m+1))),
      χ ((globalGraphChart e C.frame γ L hγ).toFun x) ≠ 0 →
        (globalGraphChart e C.frame γ L hγ).toFun x ∈ (Ω : Set (Space (m+1))) := by
  intro x hx hχ
  have hsupport := hsupp (subset_tsupport χ hχ)
  change e (C.frame (shear γ (alignedCoordinates m x))) ∈
    e '' chartImage C.frame C.graphFunction C.center C.radius C.height at hsupport
  obtain ⟨w, hw, hew⟩ := hsupport
  have hew' : w = C.frame (shear γ (alignedCoordinates m x)) := e.injective hew
  rw [hew'] at hw
  have hpos : 0 < (alignedCoordinates m x).ofLp.2 := by
    rw [alignedCoordinates_height]
    exact hx
  exact globalGraphChart_positive C γ hγEq _ hw hpos

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary
open P102.Sobolev.Extension

theorem exists_chart_smooth_trace_bound
    (hExtension : P102.Sobolev.Extension.Expected.Extension)
    {m : ℕ} (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (Ω : Opens (Space (m+1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (χ : Space (m+1) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ e '' chartImage C.frame C.graphFunction C.center C.radius C.height) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : Sobolev 𝕜 Ω 1 p) (f : Space (m+1) → 𝕜),
      ContDiff ℝ ∞ f →
      sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m+1)))] f →
      (eLpNorm (fun x => χ x • f x) p (boundaryMeasure Ω)).toReal ≤ B * ‖u‖ := by
  obtain ⟨N, hN⟩ := exists_whole_space_cutoffCLM (𝕜 := 𝕜) p χ hχ hc
  apply exists_chart_smooth_trace_bound_of_multiplier hExtension hm e Ω hΩ 𝕜 p hp C χ hχ hc hsupp N hN
  intro γ hγ heq
  exact localized_globalGraphChart_side e Ω C γ C.constant hγ heq χ hsupp

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary

/-- Conditional construction of the ordinary trace with exactly the two frozen
premises, in their prescribed order. -/
theorem trace_exists_conditional
    (hDensity : P102.Sobolev.Extension.Expected.Density)
    (hExtension : P102.Sobolev.Extension.Expected.Extension) :
    Expected.TraceExists :=
  trace_exists_of_chart_bounds hDensity hExtension
    (exists_chart_smooth_trace_bound hExtension)

end P102.Trace.Ordinary

namespace P102.Trace.Ordinary

theorem cutoff_compatibility : Expected.CutoffCompatibility :=
  cutoff_compatibility_conditional
    P102.Sobolev.Extension.lipschitz_ambient_density
    P102.Sobolev.Extension.lipschitz_extension

theorem endpoint_identification : Expected.EndpointIdentification :=
  endpoint_identification_conditional
    P102.Sobolev.Extension.lipschitz_ambient_density
    P102.Sobolev.Extension.lipschitz_extension

theorem trace_exists : Expected.TraceExists :=
  trace_exists_conditional
    P102.Sobolev.Extension.lipschitz_ambient_density
    P102.Sobolev.Extension.lipschitz_extension

theorem trace_uniqueness : Expected.TraceUniqueness :=
  trace_uniqueness_conditional
    P102.Sobolev.Extension.lipschitz_ambient_density
    P102.Sobolev.Extension.lipschitz_extension

end P102.Trace.Ordinary
