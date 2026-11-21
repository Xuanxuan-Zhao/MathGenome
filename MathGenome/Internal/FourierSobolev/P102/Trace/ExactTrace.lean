import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.ExactTrace
import MathGenome.Internal.FourierSobolev.P102.Trace.BoundaryFractionalSpace
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatExactTrace
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension

import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
noncomputable section
open Set TopologicalSpace MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace P102.Trace.Exact
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry P102.Sobolev.Extension
open Ordinary MeasuredFractional

variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
variable {Ω : Opens (Space (m + 1))} {s : ℝ} {p : ℝ≥0∞}

/-- Restrict the Hausdorff-measure isometry to the actual physical boundary. -/
theorem boundary_measurePreserving (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) :
    MeasurePreserving e
      (BoundaryFractional.surfaceMeasure (geometricOpen e Ω : Set (Ambient m)))
      (Ordinary.boundaryMeasure Ω) := by
  have h := (e.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure m).restrict_preimage
    (isClosed_frontier (s := (Ω : Set (Space (m + 1))))).measurableSet
  have hfront :
      frontier (geometricOpen e Ω : Set (Ambient m)) =
        e ⁻¹' frontier (Ω : Set (Space (m + 1))) :=
    (e.toHomeomorph.preimage_frontier (Ω : Set (Space (m + 1)))).symm
  simpa only [BoundaryFractional.surfaceMeasure, Ordinary.boundaryMeasure, hfront,
    LinearIsometryEquiv.coe_toIsometryEquiv] using h

/-- Boundary a.e. classes pull back without choosing point values on null sets. -/
def boundaryPullback (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Ordinary.BoundaryLp 𝕜 Ω p →ₗᵢ[𝕜]
      Lp 𝕜 p (BoundaryFractional.surfaceMeasure (geometricOpen e Ω : Set (Ambient m))) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 e (boundary_measurePreserving e)

theorem boundaryPullback_ae (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    [Fact (1 ≤ p)] (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    boundaryPullback e p g =ᵐ[BoundaryFractional.surfaceMeasure
      (geometricOpen e Ω : Set (Ambient m))] fun x => g (e x) := by
  exact Lp.coeFn_compMeasurePreserving g (boundary_measurePreserving e)

/-- The singular integral is unchanged by the ambient Euclidean isometry.
This uses the transport identity for arbitrary representatives, not an
assumption that the chosen Lp representative is everywhere continuous. -/
theorem energy_pullback (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (g : Space (m + 1) → 𝕜) :
    BoundaryFractional.energy (geometricOpen e Ω : Set (Ambient m)) s p (g ∘ e) =
      metricEnergy m (Ordinary.boundaryMeasure Ω) s p g := by
  rw [← (boundary_measurePreserving e).map_eq]
  have he : MeasurableEmbedding (fun x => e x) := by
    simpa only [LinearIsometryEquiv.coe_toHomeomorph] using e.toHomeomorph.measurableEmbedding
  rw [metricEnergy_map he]
  simp only [BoundaryFractional.energy, Function.comp_apply, e.isometry.dist_eq,
    dist_eq_norm]

theorem seminorm_pullback (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    [Fact (1 ≤ p)] (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    BoundaryFractional.seminorm (geometricOpen e Ω : Set (Ambient m)) s p
        (boundaryPullback e p g : Ambient m → 𝕜) =
      metricSeminorm m (Ordinary.boundaryMeasure Ω) s p
        (g : Space (m + 1) → 𝕜) := by
  rw [BoundaryFractional.seminorm_congr (boundaryPullback_ae e g)]
  unfold BoundaryFractional.seminorm metricSeminorm
  exact congrArg (fun t : ℝ≥0∞ => t ^ (1 / p.toReal)) (energy_pullback e g)

theorem intrinsicNorm_pullback (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    [Fact (1 ≤ p)] (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    BoundaryFractional.intrinsicNorm (geometricOpen e Ω : Set (Ambient m)) s p
        (boundaryPullback e p g : Ambient m → 𝕜) =
      metricNorm m (Ordinary.boundaryMeasure Ω) s p
        (g : Space (m + 1) → 𝕜) := by
  rw [BoundaryFractional.intrinsicNorm, metricNorm, seminorm_pullback,
    eLpNorm_congr_ae (boundaryPullback_ae e g)]
  congr 1
  simpa only [Function.comp_def] using
    eLpNorm_comp_measurePreserving (Lp.memLp g).aestronglyMeasurable
      (boundary_measurePreserving e)

/-- An exact identification of the physical data with the previously
constructed intrinsic space in graph coordinates. -/
def dataPullback (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    [Fact (1 ≤ p)] (g : BoundaryData 𝕜 Ω s p) :
    BoundaryFractional.space 𝕜 (geometricOpen e Ω : Set (Ambient m)) s p :=
  ⟨boundaryPullback e p g.val, by
    change BoundaryFractional.seminorm _ s p _ < ⊤
    rw [seminorm_pullback]
    exact g.property⟩

theorem dataPullback_norm (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    [Fact (1 ≤ p)] (g : BoundaryData 𝕜 Ω s p) :
    BoundaryFractional.spaceNorm (dataPullback e g) = dataNorm g := by
  simp only [BoundaryFractional.spaceNorm, dataPullback, dataNorm,
    (boundaryPullback e p).norm_map, seminorm_pullback]

theorem dataNorm_nonneg [Fact (1 ≤ p)] (g : BoundaryData 𝕜 Ω s p) : 0 ≤ dataNorm g :=
  add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg

theorem dataNorm_formula [Fact (1 ≤ p)] (g : BoundaryData 𝕜 Ω s p) :
    ENNReal.ofReal (dataNorm g) = metricNorm m (Ordinary.boundaryMeasure Ω) s p
      (g.val : Space (m + 1) → 𝕜) := by
  rw [dataNorm, ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg,
    Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
    ENNReal.ofReal_toReal g.property.ne]
  rfl

/-- Every admissible atlas recognizes exactly these same physical classes. -/
theorem data_iff_chartFinite (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    metricSeminorm m (Ordinary.boundaryMeasure Ω) s p
        (g : Space (m + 1) → 𝕜) < ⊤ ↔
      BoundaryFractional.chartNorm A s p (boundaryPullback e p g : Ambient m → 𝕜) < ⊤ := by
  rw [← seminorm_pullback e g]
  change boundaryPullback e p g ∈ BoundaryFractional.space 𝕜 _ s p ↔
    boundaryPullback e p g ∈ BoundaryFractional.chartSpace 𝕜 A s p
  rw [BoundaryFractional.common_underlying_classes m hm _ hΩ A s hs hs1 p hp 𝕜]

/-- Both quantitative chart comparisons hold on the original physical
surface quotient. The constants are fixed before the datum. -/
theorem physical_norm_comparison (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∃ C D : ℝ≥0, 0 < C ∧ 0 < D ∧
      ∀ g : Ordinary.BoundaryLp 𝕜 Ω p,
        BoundaryFractional.chartNorm A s p (boundaryPullback e p g : Ambient m → 𝕜) ≤
          (C : ℝ≥0∞) * metricNorm m (Ordinary.boundaryMeasure Ω) s p g ∧
        metricNorm m (Ordinary.boundaryMeasure Ω) s p g ≤
          (D : ℝ≥0∞) *
            BoundaryFractional.chartNorm A s p (boundaryPullback e p g : Ambient m → 𝕜) := by
  obtain ⟨C, D, hC, hD, hbound⟩ :=
    BoundaryFractional.norm_comparison m hm _ hΩ A s hs hs1 p hp
  refine ⟨C, D, hC, hD, fun g => ?_⟩
  simpa only [intrinsicNorm_pullback] using
    hbound (boundaryPullback e p g : Ambient m → 𝕜) (Lp.memLp _)

/-- Each fixed localized datum belongs to Lp on the entire tangential space.
The zero extension across the artificial edge is part of the formula. -/
theorem chart_input_memLp (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (i : Fin A.count) (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    MemLp (BoundaryFractional.localizedPullback A i
      (boundaryPullback e p g : Ambient m → 𝕜)) p volume := by
  obtain ⟨K, _, hK⟩ := BoundaryChartLocalization.localized_estimate m hm _ hΩ
    (A.chart i) (A.radius i) (A.height i) (A.smaller i).1 (A.smaller i).2.1
    (A.smaller i).2.2.1 (A.smaller i).2.2.2 (A.cutoff i)
    (A.smooth i) (A.compact i) (A.support_subset i) s hs hs1 p
    (Fact.out : 1 ≤ p) (lt_top_iff_ne_top.mpr hp)
  exact (hK 𝕜 _ (Lp.memLp (boundaryPullback e p g))).1

theorem chart_input_seminorm_finite (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (i : Fin A.count) (g : BoundaryData 𝕜 Ω s p) :
    P102.Fractional.seminorm Set.univ s p (BoundaryFractional.localizedPullback A i
      (boundaryPullback e p g.val : Ambient m → 𝕜)) < ⊤ := by
  have hfinite := (data_iff_chartFinite hm e hΩ A hs hs1 hp g.val).mp g.property
  let t : Fin A.count → ℝ≥0∞ := fun j =>
    eLpNorm (BoundaryFractional.localizedPullback A j
      (boundaryPullback e p g.val : Ambient m → 𝕜)) p volume +
    P102.Fractional.seminorm Set.univ s p (BoundaryFractional.localizedPullback A j
      (boundaryPullback e p g.val : Ambient m → 𝕜))
  have hle : t i ≤ ∑ j, t j := Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0∞) ≤ t j from bot_le)) (Finset.mem_univ i)
  exact (show _ ≤ t i from le_add_left le_rfl).trans_lt (hle.trans_lt hfinite)

/-- Whole-space tangential coordinates, preserving their Euclidean measure. -/
def baseCoordinates (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p (volume : Measure (Space m)) →ₗᵢ[𝕜]
      Lp 𝕜 p (volume : Measure (Fin m → ℝ)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (WithLp.toLp 2) (PiLp.volume_preserving_toLp (Fin m))

theorem baseCoordinates_reverse [Fact (1 ≤ p)]
    (g : Lp 𝕜 p (volume : Measure (Space m))) :
    (fun x => baseCoordinates m p g (ACL.coordinates m x)) =ᵐ[volume] g := by
  have h := (CoordinateBridge.coordinates_measurePreserving (d := m)).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving g (PiLp.volume_preserving_toLp (Fin m)))
  change (fun x => baseCoordinates m p g (ACL.coordinates m x)) =ᵐ[volume]
    (fun x => g ((ACL.coordinates m).symm (ACL.coordinates m x))) at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

namespace ChartInput

variable (hm : 1 ≤ m) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
  (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
  (hs : 0 < s) (hs1 : s < 1) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (i : Fin A.count)

/-- The fixed cutoff/pullback on boundary classes. -/
def lp (g : Ordinary.BoundaryLp 𝕜 Ω p) : Lp 𝕜 p (volume : Measure (Space m)) :=
  (chart_input_memLp hm e hΩ A hs hs1 hp i g).toLp _

theorem lp_ae (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    lp hm e hΩ A hs hs1 hp i g =ᵐ[volume]
      BoundaryFractional.localizedPullback A i
        (boundaryPullback e p g : Ambient m → 𝕜) :=
  (chart_input_memLp hm e hΩ A hs hs1 hp i g).coeFn_toLp

theorem lp_add (g h : Ordinary.BoundaryLp 𝕜 Ω p) :
    lp hm e hΩ A hs hs1 hp i (g + h) =
      lp hm e hΩ A hs hs1 hp i g + lp hm e hΩ A hs hs1 hp i h := by
  have hadd := BoundaryFractional.localizedPullback_congr A i
    (Lp.coeFn_add (boundaryPullback e p g) (boundaryPullback e p h))
  apply Lp.ext
  filter_upwards [lp_ae hm e hΩ A hs hs1 hp i (g + h),
    lp_ae hm e hΩ A hs hs1 hp i g, lp_ae hm e hΩ A hs hs1 hp i h,
    Lp.coeFn_add (lp hm e hΩ A hs hs1 hp i g) (lp hm e hΩ A hs hs1 hp i h),
    hadd] with x hx hg hh hxadd hlocal
  rw [hx, hxadd, Pi.add_apply, hg, hh]
  simp only [map_add]
  rw [hlocal]
  classical
  simp only [BoundaryFractional.localizedPullback, Pi.add_apply]
  split_ifs <;> simp [smul_add]

theorem lp_smul (c : 𝕜) (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    lp hm e hΩ A hs hs1 hp i (c • g) = c • lp hm e hΩ A hs hs1 hp i g := by
  have hsmul := BoundaryFractional.localizedPullback_congr A i
    (Lp.coeFn_smul c (boundaryPullback e p g))
  apply Lp.ext
  filter_upwards [lp_ae hm e hΩ A hs hs1 hp i (c • g),
    lp_ae hm e hΩ A hs hs1 hp i g,
    Lp.coeFn_smul c (lp hm e hΩ A hs hs1 hp i g), hsmul] with x hx hg hxc hlocal
  rw [hx, hxc, Pi.smul_apply, hg]
  simp only [map_smul]
  rw [hlocal]
  classical
  simp only [BoundaryFractional.localizedPullback, Pi.smul_apply]
  split_ifs <;> simp

def linear : Ordinary.BoundaryLp 𝕜 Ω p →ₗ[𝕜] Lp 𝕜 p (volume : Measure (Space m)) where
  toFun := lp hm e hΩ A hs hs1 hp i
  map_add' := lp_add hm e hΩ A hs hs1 hp i
  map_smul' := lp_smul hm e hΩ A hs hs1 hp i

/-- The localization is bounded already on the physical Lp space. This
estimate does not assume finite fractional energy. -/
theorem lp_bound : ∃ M : ℝ≥0, ∀ g : Ordinary.BoundaryLp 𝕜 Ω p,
    ‖lp hm e hΩ A hs hs1 hp i g‖ ≤ M * ‖g‖ := by
  obtain ⟨M, J, hJ, hM⟩ := BoundaryChartLocalization.cutoff_bounds
    (A.chart i) (A.cutoff i) (A.smooth i) (A.compact i)
  refine ⟨M, fun g => ?_⟩
  let b := boundaryPullback e p g
  have hb := (Lp.memLp b).mono_measure
    (BoundaryChartLocalization.graphMeasure_le_surfaceMeasure (A.chart i))
  have hbase := (GraphFractionalTransport.graph_memLp_iff Metric.isOpen_ball
    (A.chart i).graph_lipschitz (A.chart i).frame p
    (b : Ambient m → 𝕜)).mp hb
  let φ : Space m → 𝕜 := fun x => (A.cutoff i (BoundaryFractional.graphMap (A.chart i) x) : 𝕜)
  have hφ : LipschitzOnWith J φ (Metric.ball (A.chart i).center (A.chart i).radius) :=
    by simpa only [one_mul, φ, BoundaryFractional.graphMap, BoundaryChartLocalization.chartGraph, GraphFractionalTransport.graphMap, Function.comp_def] using RCLike.lipschitzWith_ofReal.comp_lipschitzOnWith hJ
  have hφM : ∀ x ∈ Metric.ball (A.chart i).center (A.chart i).radius, ‖φ x‖ ≤ M := by
    intro x hx
    simpa only [φ, BoundaryFractional.graphMap, BoundaryChartLocalization.chartGraph, GraphFractionalTransport.graphMap, RCLike.norm_ofReal, Real.norm_eq_abs, Function.comp_def] using hM x hx
  have hmul := P102.Fractional.LocalizationMultiplier.eLpNorm_mul_le
    Metric.isOpen_ball hφ hφM hbase
  have hgraph := (GraphFractionalTransport.graph_eLpNorm_comparison Metric.isOpen_ball
    (A.chart i).graph_lipschitz (A.chart i).frame p (b : Ambient m → 𝕜)).1
  have hraw : eLpNorm (BoundaryFractional.localizedPullback A i b) p volume ≤
      (M : ℝ≥0∞) * eLpNorm (g : Space (m + 1) → 𝕜) p (Ordinary.boundaryMeasure Ω) := by
    have hfun : BoundaryFractional.localizedPullback A i (b : Ambient m → 𝕜) =
        (Metric.ball (A.chart i).center (A.chart i).radius).indicator
          (fun x => φ x * b (BoundaryFractional.graphMap (A.chart i) x)) := by
      funext x
      classical
      simp only [BoundaryFractional.localizedPullback, Set.indicator, φ,
        RCLike.real_smul_eq_coe_mul]
    rw [hfun, eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet]
    apply hmul.trans
    apply mul_le_mul_right
    calc
      _ ≤ eLpNorm b p (GraphFractionalTransport.graphMeasure (A.chart i).frame
          (A.chart i).graphFunction (Metric.ball (A.chart i).center (A.chart i).radius)) := hgraph
      _ ≤ eLpNorm b p (BoundaryFractional.surfaceMeasure (geometricOpen e Ω : Set (Ambient m))) :=
        eLpNorm_mono_measure _ (BoundaryChartLocalization.graphMeasure_le_surfaceMeasure (A.chart i))
      _ = eLpNorm (g : Space (m + 1) → 𝕜) p (Ordinary.boundaryMeasure Ω) := by
        rw [← Lp.enorm_def, ← Lp.enorm_def]
        exact (boundaryPullback e p).enorm_map g
  rw [Lp.norm_def, eLpNorm_congr_ae (lp_ae hm e hΩ A hs hs1 hp i g)]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top g)) hraw
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← Lp.norm_def] using ht

/-- The actual continuous localization used to pass trace identities from
dense ambient smooth restrictions to arbitrary bulk Sobolev classes. -/
def continuousLinear : Ordinary.BoundaryLp 𝕜 Ω p →L[𝕜] Lp 𝕜 p (volume : Measure (Space m)) :=
  (linear hm e hΩ A hs hs1 hp i).mkContinuous
    (lp_bound hm e hΩ A hs hs1 hp i).choose
    (lp_bound hm e hΩ A hs hs1 hp i).choose_spec

theorem lp_seminorm (g : BoundaryData 𝕜 Ω s p) :
    P102.Fractional.seminorm Set.univ s p
      (lp hm e hΩ A hs hs1 hp i g.val : Space m → 𝕜) < ⊤ := by
  rw [P102.Fractional.seminorm_congr (by
    simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using
      lp_ae hm e hΩ A hs hs1 hp i g.val)]
  exact chart_input_seminorm_finite hm e hΩ A hs hs1 hp i g

/-- The local datum in the precise fractional space used by the existing
flat lift. This is an actual finite-energy element, not a lifting premise. -/
def fractional (g : BoundaryData 𝕜 Ω s p) :
    ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 m s p := by
  let v := lp hm e hΩ A hs hs1 hp i g.val
  refine ⟨baseCoordinates m p v, ?_⟩
  rw [CoordinateBridge.fractional_energy_coordinates]
  rw [P102.Fractional.energy_congr (by
    simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using
      baseCoordinates_reverse v)]
  have hpr : 0 < 1 / p.toReal := one_div_pos.mpr
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp)
  exact (ENNReal.rpow_lt_top_iff_of_pos hpr).mp (lp_seminorm hm e hΩ A hs hs1 hp i g)

theorem fractional_norm (g : BoundaryData 𝕜 Ω s p) :
    ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
      (fractional hm e hΩ A hs hs1 hp i g) =
        ‖lp hm e hΩ A hs hs1 hp i g.val‖ +
          (P102.Fractional.seminorm Set.univ s p
            (lp hm e hΩ A hs hs1 hp i g.val : Space m → 𝕜)).toReal := by
  rw [CoordinateBridge.fractional_full_norm_coordinates]
  change ‖baseCoordinates m p _‖ + _ = _
  rw [(baseCoordinates m p).norm_map]
  simp only [fractional]
  congr 1
  congr 1
  apply P102.Fractional.seminorm_congr
  simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using
    baseCoordinates_reverse (lp hm e hΩ A hs hs1 hp i g.val)

theorem fractional_norm_le_chartNorm (g : BoundaryData 𝕜 Ω s p) :
    ENNReal.ofReal (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
      (fractional hm e hΩ A hs hs1 hp i g)) ≤
        BoundaryFractional.chartNorm A s p
          (boundaryPullback e p g.val : Ambient m → 𝕜) := by
  rw [fractional_norm, ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg,
    Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
    ENNReal.ofReal_toReal (lp_seminorm hm e hΩ A hs hs1 hp i g).ne]
  rw [eLpNorm_congr_ae (lp_ae hm e hΩ A hs hs1 hp i g.val),
    P102.Fractional.seminorm_congr (by
      simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using
        lp_ae hm e hΩ A hs hs1 hp i g.val)]
  exact Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0∞) ≤
    eLpNorm (BoundaryFractional.localizedPullback A j
      (boundaryPullback e p g.val : Ambient m → 𝕜)) p volume +
    P102.Fractional.seminorm Set.univ s p (BoundaryFractional.localizedPullback A j
      (boundaryPullback e p g.val : Ambient m → 𝕜)) from bot_le)) (Finset.mem_univ i)

/-- One domain/atlas constant controls every fixed localization into the
flat fractional space. The operation is quantitative on the intrinsic norm. -/
theorem fractional_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin A.count) (g : BoundaryData 𝕜 Ω s p),
      ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p
        (fractional hm e hΩ A hs hs1 hp j g) ≤ C * dataNorm g := by
  obtain ⟨C, D, hC, hD, hb⟩ := physical_norm_comparison (𝕜 := 𝕜) hm e hΩ A hs hs1 hp
  refine ⟨C, C.coe_nonneg, fun j g => ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg C.coe_nonneg (dataNorm_nonneg g))).mp
  rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, dataNorm_formula]
  exact (fractional_norm_le_chartNorm hm e hΩ A hs hs1 hp j g).trans (hb g.val).1

theorem fractional_add [Fact (p ≠ ⊤)]
    (g h k : BoundaryData 𝕜 Ω s p) (hk : k.val = g.val + h.val) :
    fractional hm e hΩ A hs hs1 hp i k =
      fractional hm e hΩ A hs hs1 hp i g + fractional hm e hΩ A hs hs1 hp i h := by
  apply Subtype.ext
  change baseCoordinates m p (lp hm e hΩ A hs hs1 hp i k.val) = _
  rw [hk, lp_add, map_add]
  rfl

theorem fractional_smul [Fact (p ≠ ⊤)] (c : 𝕜) (g h : BoundaryData 𝕜 Ω s p)
    (hh : h.val = c • g.val) :
    fractional hm e hΩ A hs hs1 hp i h = c • fractional hm e hΩ A hs hs1 hp i g := by
  apply Subtype.ext
  change baseCoordinates m p (lp hm e hΩ A hs hs1 hp i h.val) = _
  rw [hh, lp_smul, map_smul]
  rfl

end ChartInput

theorem trace_order_range [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    0 < 1 - 1 / p.toReal ∧ 1 - 1 / p.toReal < 1 := by
  have hpr : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  constructor
  · exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hpr)).mpr hpr)
  · exact sub_lt_self _ (one_div_pos.mpr (zero_lt_one.trans hpr))

/-- Localize each physical fractional datum by the fixed boundary partition,
then apply the existing bounded scalar-linear flat lift. All local maps and
their common bound are constructed, rather than supplied as certificates.
The identity here is at the flat face; returning through charts is separate. -/
theorem localized_flat_lifts (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ (C : ℝ) (T : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p)
      (L : Fin A.count → BoundaryData 𝕜 Ω (1 - 1 / p.toReal) p → HalfSobolev m 𝕜 p),
      0 ≤ C ∧ IsFlatTrace T ∧
      (∀ i g h k, k.val = g.val + h.val → L i k = L i g + L i h) ∧
      (∀ i (c : 𝕜) g h, h.val = c • g.val → L i h = c • L i g) ∧
      (∀ i g, ‖L i g‖ ≤ C * dataNorm g) ∧
      ∀ i g, ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p
        (T (L i g)) =
          baseCoordinates m p
            (ChartInput.lp hm e hΩ A (trace_order_range hp1 hp).1
              (trace_order_range hp1 hp).2 hp i g.val) := by
  have : Fact (p ≠ ⊤) := ⟨hp⟩
  obtain ⟨Ct, hCt, hflat⟩ := exact_flat_trace m hm p hp1 hp
  obtain ⟨⟨T, hT⟩, hbound⟩ := hflat 𝕜
  obtain ⟨E, hEbound, hEtrace⟩ := (hbound T hT).2
  have hs := trace_order_range hp1 hp
  obtain ⟨Ca, hCa, hlocal⟩ := ChartInput.fractional_bound (𝕜 := 𝕜) hm e hΩ A hs.1 hs.2 hp
  let L := fun i g => E (ChartInput.fractional hm e hΩ A hs.1 hs.2 hp i g)
  refine ⟨Ct * Ca, T, L, mul_nonneg hCt hCa, hT, ?_, ?_, ?_, ?_⟩
  · intro i g h k hk
    dsimp [L]
    rw [ChartInput.fractional_add hm e hΩ A hs.1 hs.2 hp i g h k hk, map_add]
  · intro i c g h hh
    dsimp [L]
    rw [ChartInput.fractional_smul hm e hΩ A hs.1 hs.2 hp i c g h hh, map_smul]
  · intro i g
    exact (hEbound _).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hlocal i g) hCt)
  · intro i g
    exact hEtrace (ChartInput.fractional hm e hΩ A hs.1 hs.2 hp i g)

/-- Purely geometric choices for returning a flat lift. The cutoff is one
on the support of the boundary datum and compactly supported inside the full
chart. Neither the exponent nor the input datum occurs in these choices. -/
structure LiftCollar {G : Set (Ambient m)} (C : BoundaryChart G) (K : Set (Ambient m)) where
  graphExtension : Space m → ℝ
  extension_lipschitz : LipschitzWith C.constant graphExtension
  extension_agrees : EqOn C.graphFunction graphExtension (Metric.ball C.center C.radius)
  cutoff : Ambient m → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff
  compact : HasCompactSupport cutoff
  equal_one : ∀ x ∈ K, cutoff x = 1
  support_subset : tsupport cutoff ⊆
    chartImage C.frame C.graphFunction C.center C.radius C.height

theorem liftCollar_exists {G : Set (Ambient m)} (C : BoundaryChart G)
    (K : Set (Ambient m)) (hK : IsCompact K)
    (hKC : K ⊆ chartImage C.frame C.graphFunction C.center C.radius C.height) :
    Nonempty (LiftCollar C K) := by
  obtain ⟨γ, hγ, heq⟩ := C.graph_lipschitz.extend_real
  let U : Fin 1 → Set (Ambient m) := fun _ =>
    chartImage C.frame C.graphFunction C.center C.radius C.height
  obtain ⟨V, χ, hVo, hKV, hχ, hsum, hsupp⟩ := finite_smooth_partition hK U
    (fun _ => chartImage_open C.frame C.graph_lipschitz)
    (fun _ => chartImage_bounded C.frame C.graph_lipschitz)
    (fun _ hx => mem_iUnion.mpr ⟨0, hKC hx⟩)
  refine ⟨⟨γ, hγ, heq, χ 0, (hχ 0).1, (hχ 0).2.1, ?_, hsupp 0⟩⟩
  intro x hx
  simpa only [Fin.sum_univ_one] using hsum x (hKV hx)

/-- Every partition support admits a fixed collar. -/
theorem atlas_liftCollar_exists (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (i : Fin A.count) :
    Nonempty (LiftCollar (A.chart i) (tsupport (A.cutoff i))) :=
  liftCollar_exists _ _ (A.compact i) (fun _ hx =>
    chartImage_mono (A.chart i).frame (A.chart i).graphFunction
      (A.chart i).center (A.smaller i).2.1.le (A.smaller i).2.2.2.le (A.support_subset i hx))

namespace LiftCollar
variable (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  {K : Set (Ambient m)} (D : LiftCollar C K)

def physicalTest : WholeTests (m + 1) ℝ :=
  ⟨fun x => D.cutoff (e.symm x), D.smooth.comp e.symm.contDiff,
    D.compact.comp_homeomorph e.symm.toHomeomorph, subset_univ _⟩

theorem physicalTest_support :
    tsupport (D.physicalTest e C) ⊆ e '' tsupport D.cutoff := by
  apply closure_minimal
  · intro x hx
    exact ⟨e.symm x, subset_tsupport _ hx, e.apply_symm_apply x⟩
  · exact e.toHomeomorph.isClosedMap _ (isClosed_tsupport _)

/-- The local one-sided graph identity gives the precise collar needed
by relative zero extension after the inverse coordinate change. -/
theorem support_side :
    tsupport (scalarTest 𝕜 (D.physicalTest e C)) ∩ (Ω : Set (Space (m + 1))) ⊆
      globalGraphOpen e C.frame D.extension_lipschitz := by
  rintro x ⟨hxK, hxΩ⟩
  have hxreal : x ∈ tsupport (D.physicalTest e C) :=
    (tsupport_comp_subset (map_zero (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜))
      (D.physicalTest e C)) hxK
  obtain ⟨z, hz, rfl⟩ := D.physicalTest_support e C hxreal
  apply (globalGraphOpen_side e C D.extension_lipschitz D.extension_agrees
    (D.support_subset hz)).mpr
  change e z ∈ Ω
  exact hxΩ

/-- A genuine bounded Sobolev return operator, with zero values across the
artificial chart edges. No smoothness of the bi-Lipschitz pushforward is used. -/
def returnOperator (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HalfSobolev m 𝕜 p →L[𝕜] Sobolev 𝕜 Ω 1 p :=
  (relativeCutoffSobolev (globalGraphOpen e C.frame D.extension_lipschitz) Ω p
    (scalarTest 𝕜 (D.physicalTest e C)) (D.support_side e C)).comp
      (sobolevChartPullback (Nat.succ_pos m)
        (graphChart e C.frame D.extension_lipschitz).symm 𝕜 p)

theorem returnOperator_ae [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) :
    sobolevUnderlying (D.returnOperator e C 𝕜 p u) =ᵐ[
      volume.restrict (Ω : Set (Space (m + 1)))]
      fun x => D.cutoff (e.symm x) •
        sobolevUnderlying u ((flattenEquiv e C.frame D.graphExtension).symm x) := by
  let U := globalGraphOpen e C.frame D.extension_lipschitz
  let a := scalarTest 𝕜 (D.physicalTest e C)
  let P := sobolevChartPullback (Nat.succ_pos m)
    (graphChart e C.frame D.extension_lipschitz).symm 𝕜 p
  have hP := sobolevChartPullback_ae (Nat.succ_pos m)
    (graphChart e C.frame D.extension_lipschitz).symm 𝕜 p u
  have hP' := (ae_restrict_iff' U.isOpen.measurableSet).mp hP
  have hR := relativeCutoffSobolev_underlying_ae U Ω p a (D.support_side e C) (P u)
  filter_upwards [hR, ae_restrict_of_ae hP', self_mem_ae_restrict Ω.isOpen.measurableSet]
    with x hx hpx hxΩ
  change sobolevUnderlying (relativeCutoffSobolev U Ω p a (D.support_side e C) (P u)) x = _
  rw [hx, RCLike.real_smul_eq_coe_mul]
  change a x * sobolevUnderlying (P u) x = a x * _
  by_cases hxU : x ∈ U
  · rw [hpx hxU]
    rfl
  · have hxa : x ∉ tsupport a := fun hxK => hxU (D.support_side e C ⟨hxK, hxΩ⟩)
    rw [image_eq_zero_of_notMem_tsupport hxa, zero_mul, zero_mul]

/-- The reverse side of the chart collar permits localization from Ω to
the entire graph epigraph before flattening. -/
theorem flatten_support :
    tsupport (scalarTest 𝕜 (D.physicalTest e C)) ∩
      (globalGraphOpen e C.frame D.extension_lipschitz : Set (Space (m + 1))) ⊆ Ω := by
  rintro x ⟨hxK, hxU⟩
  have hxreal : x ∈ tsupport (D.physicalTest e C) :=
    (tsupport_comp_subset (map_zero (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜))
      (D.physicalTest e C)) hxK
  exact physicalSupport_inter_graph e Ω C D.extension_lipschitz D.extension_agrees
    D.cutoff D.compact D.support_subset ⟨D.physicalTest_support e C hxreal, hxU⟩

/-- Fixed-cutoff localization and flattening is an actual continuous
scalar-linear map on the full bulk Sobolev space. -/
def flattenOperator (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 Ω 1 p →L[𝕜] HalfSobolev m 𝕜 p :=
  (sobolevChartPullback (Nat.succ_pos m)
    (graphChart e C.frame D.extension_lipschitz) 𝕜 p).comp
      (relativeCutoffSobolev Ω (globalGraphOpen e C.frame D.extension_lipschitz) p
        (scalarTest 𝕜 (D.physicalTest e C)) (D.flatten_support e C))

/-- On an ambient smooth restriction, the flattened representative is
continuous through the face even when the graph is only Lipschitz. -/
theorem flattenOperator_smooth_ae [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜)
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    sobolevUnderlying (D.flattenOperator e C 𝕜 p u) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))]
      fun x => D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension x)) •
        f (flattenEquiv e C.frame D.graphExtension x) := by
  let U := globalGraphOpen e C.frame D.extension_lipschitz
  let a := scalarTest 𝕜 (D.physicalTest e C)
  let R := relativeCutoffSobolev Ω U p a (D.flatten_support e C)
  have hR := relativeCutoffSobolev_underlying_ae Ω U p a (D.flatten_support e C) u
  have hu' := ae_restrict_of_ae ((ae_restrict_iff' Ω.isOpen.measurableSet).mp hu)
      (s := (U : Set (Space (m + 1))))
  have hrep : sobolevUnderlying (R u) =ᵐ[volume.restrict (U : Set (Space (m + 1)))]
      fun x => D.cutoff (e.symm x) • f x := by
    filter_upwards [hR, hu', self_mem_ae_restrict U.isOpen.measurableSet] with x hx hux hxU
    rw [hx, RCLike.real_smul_eq_coe_mul]
    change a x * sobolevUnderlying u x = a x * f x
    by_cases hxΩ : x ∈ Ω
    · rw [hux hxΩ]
    · have hxa : x ∉ tsupport a := fun h => hxΩ (D.flatten_support e C ⟨h, hxU⟩)
      rw [image_eq_zero_of_notMem_tsupport hxa, zero_mul, zero_mul]
  exact (sobolevChartPullback_ae (Nat.succ_pos m)
    (graphChart e C.frame D.extension_lipschitz) 𝕜 p (R u)).trans
      ((graphChart e C.frame D.extension_lipschitz).ae_comp hrep)

/-- Flat trace on these localized representatives equals their continuous
boundary values. No differentiability of the Lipschitz graph is required. -/
theorem flattenOperator_smooth_trace (hm : 1 ≤ m) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (S : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p) (hS : IsFlatTrace S)
    (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜) (hf : Continuous f)
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    (S (D.flattenOperator e C 𝕜 p u) : Boundary m → 𝕜) =ᵐ[volume]
      fun z => D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension (point m z 0))) •
        f (flattenEquiv e C.frame D.graphExtension (point m z 0)) := by
  apply flatTrace_compatibility flat_trace_exists slice_unique hm hp S hS
    (D.flattenOperator e C 𝕜 p u)
    (fun x => D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension x)) •
      f (flattenEquiv e C.frame D.graphExtension x))
  · exact (((D.smooth.continuous.comp e.symm.continuous).comp
      (flattenEquiv_lipschitz e C.frame D.extension_lipschitz).continuous).smul
        (hf.comp (flattenEquiv_lipschitz e C.frame D.extension_lipschitz).continuous)).continuousOn
  · exact D.flattenOperator_smooth_ae e C u f hu

end LiftCollar

/-- Construct the finite sum of the fixed-cutoff returned flat lifts, with
the full scalar linearity laws and an intrinsic-norm bound. Its physical ordinary trace is identified with the input datum below,
after establishing compatibility with the chart maps. -/
theorem lift_construction (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ (B : ℝ) (T : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p)
      (F : Fin A.count → BoundaryData 𝕜 Ω (1 - 1 / p.toReal) p → HalfSobolev m 𝕜 p)
      (D : ∀ i, LiftCollar (A.chart i) (tsupport (A.cutoff i))),
      IsFlatTrace T ∧
      (∀ i g, ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p
        (T (F i g)) = baseCoordinates m p
          (ChartInput.lp hm e hΩ A (trace_order_range hp1 hp).1
            (trace_order_range hp1 hp).2 hp i g.val)) ∧
      let L := fun g => ∑ i, (D i).returnOperator e (A.chart i) 𝕜 p (F i g)
      0 ≤ B ∧
      (∀ g h k, k.val = g.val + h.val → L k = L g + L h) ∧
      (∀ (c : 𝕜) g h, h.val = c • g.val → L h = c • L g) ∧
      ∀ g, ‖L g‖ ≤ B * dataNorm g := by
  classical
  obtain ⟨Cf, T, F, hCf, hT, hadd, hsmul, hnorm, htrace⟩ :=
    localized_flat_lifts (𝕜 := 𝕜) hm e hΩ A hp1 hp
  let D := fun i => Classical.choice (atlas_liftCollar_exists e A i)
  let R := fun i => (D i).returnOperator e (A.chart i) 𝕜 p
  let B := (∑ i, ‖R i‖) * Cf
  refine ⟨B, T, F, D, hT, htrace, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg (R i)) hCf
  · intro g h k hk
    dsimp only
    simp_rw [hadd _ g h k hk, map_add]
    exact Finset.sum_add_distrib
  · intro c g h hh
    dsimp only
    simp_rw [hsmul _ c g h hh, map_smul]
    exact (Finset.smul_sum ..).symm
  · intro g
    change ‖∑ i, R i (F i g)‖ ≤ B * dataNorm g
    calc
      _ ≤ ∑ i, ‖R i (F i g)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖R i‖ * (Cf * dataNorm g) := by
        apply Finset.sum_le_sum
        intro i _
        exact ((R i).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hnorm i g) (norm_nonneg (R i)))
      _ = B * dataNorm g := by
        simp only [B, Finset.sum_mul, mul_assoc]

/-- The complete original ordinary theorem is an explicit premise. -/
theorem trace_existence_conditional (hordinary : Ordinary.Expected.OrdinaryTrace) :
    Expected.TraceExistence := by
  intro m _ e Ω hΩ 𝕜 _ p _ _ hp
  obtain ⟨_, _, T, hT, _⟩ := hordinary.1 m e Ω hΩ 𝕜 p hp
  exact ⟨T, hT⟩

theorem kernel_conditional (hordinary : Ordinary.Expected.OrdinaryTrace) :
    Expected.Kernel := by
  intro m _ e Ω hΩ 𝕜 _ p _ _ hp T hT
  exact hordinary.2.1 m e Ω hΩ 𝕜 p hp T hT

/-- Once the fixed linear lifting is constructed, surjectivity needs no
independent selection of preimages. -/
theorem onto_of_rightInverse (hlift : Expected.RightInverse) : Expected.Onto := by
  intro m hm e Ω hΩ 𝕜 _ p _ hp1 hp T hT g
  obtain ⟨C, L, _, _, _, _, hL⟩ := hlift m hm e Ω hΩ 𝕜 p hp1 hp
  exact ⟨L g, hL T hT g⟩

/-- A fixed smooth compact multiplier acts on Lp for any measure, in particular
on the physical surface quotient. -/
def testMultiplier {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d 𝕜) :
    Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ := by
  let hm (f : Lp 𝕜 p μ) : MemLp (fun x => a x * f x) p μ :=
    (memLp_top_of_bound a.continuous.aestronglyMeasurable (testBound a)
      (ae_of_all _ (norm_le_testBound a))).mul
      (Lp.memLp f)
  let F : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 p μ := {
    toFun := fun f => (hm f).toLp _
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hm (f + g)).coeFn_toLp, (hm f).coeFn_toLp,
        (hm g).coeFn_toLp, Lp.coeFn_add f g,
        Lp.coeFn_add ((hm f).toLp _) ((hm g).toLp _)] with x hfg hf hg hs ht
      simp only [Pi.add_apply] at *
      rw [hfg, hs, ht, hf, hg, mul_add]
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(hm (c • f)).coeFn_toLp, (hm f).coeFn_toLp,
        Lp.coeFn_smul c f, Lp.coeFn_smul c ((hm f).toLp _)] with x hcf hf hs ht
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
      rw [hcf, hs, ht, hf]
      ring }
  apply F.mkContinuous (testBound a)
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(hm f).coeFn_toLp] with x hx
  change ‖(hm f).toLp _ x‖ ≤ _
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_testBound a x) (norm_nonneg _)

theorem testMultiplier_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d 𝕜)
    (f : Lp 𝕜 p μ) :
    testMultiplier μ p a f =ᵐ[μ] fun x => a x * f x :=
  ((memLp_top_of_bound a.continuous.aestronglyMeasurable (testBound a)
      (ae_of_all _ (norm_le_testBound a))).mul
    (Lp.memLp f) : MemLp _ p _).coeFn_toLp

/-- Ordinary trace commutes with fixed ambient test multiplication. -/
theorem trace_testMultiplier {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space (m + 1))} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) (hp : p ≠ ⊤)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (a : WholeTests (m + 1) 𝕜) (u : Sobolev 𝕜 Ω 1 p) :
    T (domainTestMulSobolev Ω p a u) = testMultiplier (Ordinary.boundaryMeasure Ω) p a (T u) := by
  obtain ⟨φ, v, hv, hlim⟩ := lipschitz_ambient_density m e Ω hΩ 𝕜 p hp u
  have hident (n : ℕ) :
      T (domainTestMulSobolev Ω p a (v n)) =
        testMultiplier (Ordinary.boundaryMeasure Ω) p a (T (v n)) := by
    have hv0 : sobolevUnderlying (v n) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] φ n := by
      simpa only [sobolevUnderlying, zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] using
        hv n (zeroSobolevIndex (m + 1) 1)
    have hprod : sobolevUnderlying (domainTestMulSobolev Ω p a (v n)) =ᵐ[
        volume.restrict (Ω : Set (Space (m + 1)))] fun x => a x * φ n x := by
      rw [domainTestMulSobolev_underlying]
      filter_upwards [domainTestMul_ae Ω p a (sobolevUnderlying (v n)), hv0]
        with x hx hvx
      rw [hx, hvx]
    apply Lp.ext
    filter_upwards [hT _ _ (a.contDiff.mul (φ n).contDiff) hprod,
      testMultiplier_ae (Ordinary.boundaryMeasure Ω) p a (T (v n)),
      hT _ _ (φ n).contDiff hv0] with x hx hy hz
    rw [hx, hy, hz]
  have hl := ((T.comp (domainTestMulSobolev Ω p a)).continuous.tendsto u).comp hlim
  have hr := (((testMultiplier (Ordinary.boundaryMeasure Ω) p a).comp T).continuous.tendsto u).comp hlim
  exact tendsto_nhds_unique hl (hr.congr (fun n => (hident n).symm))

/-- A chart pullback determines a boundary class supported inside that chart. -/
theorem supported_pullback_injective {m : ℕ} {G : Set (Ambient m)}
    (C : BoundaryChart G) {K : Set (Ambient m)}
    (hKU : K ⊆ chartImage C.frame C.graphFunction C.center C.radius C.height)
    {E : Type*} [NormedAddCommGroup E] {q r : Ambient m → E}
    (hq : ∀ᵐ x ∂BoundaryPatchExtension.surfaceMeasure G, x ∉ K → q x = 0)
    (hr : ∀ᵐ x ∂BoundaryPatchExtension.surfaceMeasure G, x ∉ K → r x = 0)
    (hpull : BoundaryPatchExtension.pullback C q =ᵐ[volume]
      BoundaryPatchExtension.pullback C r) :
    q =ᵐ[BoundaryPatchExtension.surfaceMeasure G] r := by
  have hb : q ∘ GraphFractionalTransport.graphMap C.frame C.graphFunction =ᵐ[
      volume.restrict (ball C.center C.radius)]
      r ∘ GraphFractionalTransport.graphMap C.frame C.graphFunction := by
    filter_upwards [ae_restrict_of_ae hpull,
      ae_restrict_mem isOpen_ball.measurableSet] with x hx hxB
    simpa only [BoundaryPatchExtension.pullback, indicator_of_mem hxB] using hx
  have hpatch := ((GraphFractionalTransport.representative_transport m C.center C.radius
    C.radius_pos C.graphFunction C.constant C.graph_lipschitz C.frame E q r).1).mpr hb
  rw [BoundaryPatchExtension.graphMeasure_eq C] at hpatch
  apply ae_of_ae_restrict_of_ae_restrict_compl (BoundaryPatchExtension.patch C) hpatch
  filter_upwards [BoundaryPatchExtension.supported_zero_off_patch C hKU hq,
    BoundaryPatchExtension.supported_zero_off_patch C hKU hr] with x hqx hrx
  exact hqx.trans hrx.symm


/-- Enlarge the cutoff collar without changing the chosen global graph. -/
theorem LiftCollar.outer_exists
    {G : Set (Ambient m)} (C : BoundaryChart G) {K : Set (Ambient m)}
    (D : LiftCollar C K) :
    ∃ E : LiftCollar C (tsupport D.cutoff), E.graphExtension = D.graphExtension := by
  obtain ⟨E⟩ := liftCollar_exists C (tsupport D.cutoff) D.compact D.support_subset
  exact ⟨{ E with
    graphExtension := D.graphExtension
    extension_lipschitz := D.extension_lipschitz
    extension_agrees := D.extension_agrees }, rfl⟩

/-- The returned chart piece is unchanged by a collar which is one on
its entire physical support. -/
theorem LiftCollar.returnOperator_fixed_by_outer
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {K : Set (Ambient m)} (D : LiftCollar C K)
    (E : LiftCollar C (tsupport D.cutoff)) [Fact (1 ≤ p)]
    (u : HalfSobolev m 𝕜 p) :
    domainTestMulSobolev Ω p (scalarTest 𝕜 (E.physicalTest e C))
      (D.returnOperator e C 𝕜 p u) = D.returnOperator e C 𝕜 p u := by
  apply sobolevUnderlying_injective Ω 1 p
  rw [domainTestMulSobolev_underlying]
  apply Lp.ext
  filter_upwards [domainTestMul_ae Ω p (scalarTest 𝕜 (E.physicalTest e C))
      (sobolevUnderlying (D.returnOperator e C 𝕜 p u)),
    D.returnOperator_ae e C u] with x hmul hw
  rw [hmul, hw]
  change (E.cutoff (e.symm x) : 𝕜) *
    (D.cutoff (e.symm x) • sobolevUnderlying u
      ((flattenEquiv e C.frame D.graphExtension).symm x)) = _
  by_cases hx : e.symm x ∈ tsupport D.cutoff
  · rw [E.equal_one _ hx, RCLike.ofReal_one, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, mul_zero]


/-- Bounded measurable coefficients act continuously on any Lp quotient. -/
def boundedLpMul {X : Type*} [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (a : X → 𝕜) (ha : AEStronglyMeasurable a μ)
    (M : ℝ) (hM : ∀ x, ‖a x‖ ≤ M) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ := by
  let hm (f : Lp 𝕜 p μ) : MemLp (fun x => a x * f x) p μ :=
    (memLp_top_of_bound ha M (ae_of_all _ hM)).mul (Lp.memLp f)
  let F : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 p μ := {
    toFun := fun f => (hm f).toLp _
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hm (f + g)).coeFn_toLp, (hm f).coeFn_toLp,
        (hm g).coeFn_toLp, Lp.coeFn_add f g,
        Lp.coeFn_add ((hm f).toLp _) ((hm g).toLp _)] with x hfg hf hg hs ht
      simp only [Pi.add_apply] at *
      rw [hfg, hs, ht, hf, hg, mul_add]
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(hm (c • f)).coeFn_toLp, (hm f).coeFn_toLp,
        Lp.coeFn_smul c f, Lp.coeFn_smul c ((hm f).toLp _)] with x hcf hf hs ht
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
      rw [hcf, hs, ht, hf]
      ring
  }
  apply F.mkContinuous M
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(hm f).coeFn_toLp] with x hx
  change ‖(hm f).toLp _ x‖ ≤ _
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

theorem boundedLpMul_ae {X : Type*} [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (a : X → 𝕜) (ha : AEStronglyMeasurable a μ)
    (M : ℝ) (hM : ∀ x, ‖a x‖ ≤ M) (f : Lp 𝕜 p μ) :
    boundedLpMul μ p a ha M hM f =ᵐ[μ] fun x => a x * f x :=
  ((memLp_top_of_bound ha M (ae_of_all _ hM)).mul (Lp.memLp f) : MemLp _ p μ).coeFn_toLp

/-- Ambient smooth restrictions are dense in the half-space Sobolev space. -/
theorem half_ambient_density [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : HalfSobolev m 𝕜 p) :
    ∃ (φ : ℕ → WholeTests (m + 1) 𝕜) (v : ℕ → HalfSobolev m 𝕜 p),
      (∀ n, RepresentsOn (φ n) (v n)) ∧ Tendsto v atTop (𝓝 u) := by
  exact ambient_approximation_of_extension (halfSpace m) 1 p hp u
    (upperReflectionSobolev (Fin.last m) p u)
    (upperReflectionSobolev_restrict (Fin.last m) p u)

/-- Any bounded Sobolev multiplier with continuous coefficient commutes with
flat trace. The coefficient may be merely Lipschitz in physical coordinates. -/
theorem flatTrace_mul_of_operator (hm : 1 ≤ m) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (S : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p) (hS : IsFlatTrace S)
    (Q : HalfSobolev m 𝕜 p →L[𝕜] HalfSobolev m 𝕜 p)
    (a : Space (m + 1) → 𝕜) (ha : Continuous a) (M : ℝ)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hQ : ∀ u, sobolevUnderlying (Q u) =ᵐ[volume.restrict
      (halfSpace m : Set (Space (m + 1)))] fun x => a x * sobolevUnderlying u x)
    (u : HalfSobolev m 𝕜 p) :
    (S (Q u) : Boundary m → 𝕜) =ᵐ[volume]
      fun z => a (point m z 0) * S u z := by
  have hpoint : Continuous (fun z : Boundary m => point m z 0) := by
    unfold point ACL.line
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)).comp
    apply continuous_pi
    intro j
    by_cases h : j = Fin.last m
    · simpa only [ExpandedFA.Sobolev.Lines.coordinateLine, dite_eq_left h] using
        (continuous_const : Continuous (fun _ : Boundary m => (0 : ℝ)))
    · simpa only [ExpandedFA.Sobolev.Lines.coordinateLine, dite_eq_right h] using
        (continuous_apply (⟨j, h⟩ : {k : Fin (m + 1) // k ≠ Fin.last m}))
  let b : Boundary m → 𝕜 := fun z => a (point m z 0)
  have hb : Continuous b := ha.comp hpoint
  let B := boundedLpMul (volume : Measure (Boundary m)) p b hb.aestronglyMeasurable M
    (fun z => hM (point m z 0))
  obtain ⟨φ, v, hv, hlim⟩ := half_ambient_density hp u
  have heq (n : ℕ) : S (Q (v n)) = B (S (v n)) := by
    have hn : sobolevUnderlying (v n) =ᵐ[volume.restrict
        (halfSpace m : Set (Space (m + 1)))] (φ n : Space (m + 1) → 𝕜) := by
      simpa only [sobolevUnderlying, zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] using hv n (zeroSobolevIndex (m + 1) 1)
    have hqrep : sobolevUnderlying (Q (v n)) =ᵐ[volume.restrict
        (halfSpace m : Set (Space (m + 1)))] fun x => a x * φ n x := by
      filter_upwards [hQ (v n), hn] with x hqx hvx
      rw [hqx, hvx]
    have hs := flatTrace_compatibility flat_trace_exists slice_unique hm hp S hS
      (v n) (φ n) (φ n).continuous.continuousOn hn
    have hsq := flatTrace_compatibility flat_trace_exists slice_unique hm hp S hS
      (Q (v n)) (fun x => a x * φ n x) (ha.mul (φ n).continuous).continuousOn hqrep
    apply Lp.ext
    filter_upwards [hsq, hs, boundedLpMul_ae (volume : Measure (Boundary m)) p b
      hb.aestronglyMeasurable M (fun z => hM (point m z 0)) (S (v n))] with z hqz hsz hbz
    rw [hqz, hbz, hsz]
  have hleft := ((S.comp Q).continuous.tendsto u).comp hlim
  have hright := ((B.comp S).continuous.tendsto u).comp hlim
  have hresult : S (Q u) = B (S u) := tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun n => (heq n).symm))
  rw [hresult]
  exact boundedLpMul_ae _ _ _ _ _ _ _

namespace LiftCollar
variable {Ω : Opens (Space (m + 1))}
  (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  {K : Set (Ambient m)} (D : LiftCollar C K)

/-- Returning through one collar and flattening through a larger collar
with the same global graph multiplies by the product of the two cutoffs. -/
theorem flatten_return_ae_of_graph [Fact (1 ≤ p)]
    {K' : Set (Ambient m)} (E : LiftCollar C K')
    (hgraph : E.graphExtension = D.graphExtension) (u : HalfSobolev m 𝕜 p) :
    sobolevUnderlying (E.flattenOperator e C 𝕜 p (D.returnOperator e C 𝕜 p u)) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))]
      fun x => (E.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension x)) : 𝕜) *
        (D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension x)) : 𝕜) *
          sobolevUnderlying u x := by
  have h := E.flattenOperator_smooth_ae e C
    (D.returnOperator e C 𝕜 p u) _ (D.returnOperator_ae e C u)
  filter_upwards [h] with x hx
  rw [hx]
  simp only [hgraph, Equiv.symm_apply_apply, RCLike.real_smul_eq_coe_mul]
  ring

/-- A collar equal to one on the first cutoff's support removes the extra
factor introduced by the reverse localization. -/
theorem flatten_return_ae_larger [Fact (1 ≤ p)]
    (E : LiftCollar C (tsupport D.cutoff))
    (hgraph : E.graphExtension = D.graphExtension) (u : HalfSobolev m 𝕜 p) :
    sobolevUnderlying (E.flattenOperator e C 𝕜 p (D.returnOperator e C 𝕜 p u)) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))]
      fun x => (D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension x)) : 𝕜) *
        sobolevUnderlying u x := by
  filter_upwards [D.flatten_return_ae_of_graph e C E hgraph u] with x hx
  rw [hx]
  by_cases hd : D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension x)) = 0
  · simp only [hd, RCLike.ofReal_zero, mul_zero, zero_mul]
  · rw [E.equal_one _ (subset_tsupport _ hd)]
    simp only [RCLike.ofReal_one, one_mul]

/-- The flat trace after returning and reflattening through a larger collar
is the original flat trace multiplied by the first collar cutoff at the face. -/
theorem flatten_return_trace_larger (hm : 1 ≤ m) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (S : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p) (hS : IsFlatTrace S)
    (E : LiftCollar C (tsupport D.cutoff))
    (hgraph : E.graphExtension = D.graphExtension) (u : HalfSobolev m 𝕜 p) :
    (S (E.flattenOperator e C 𝕜 p (D.returnOperator e C 𝕜 p u)) : Boundary m → 𝕜) =ᵐ[volume]
      fun z => (D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension
        (point m z 0))) : 𝕜) * S u z := by
  let a : Space (m + 1) → 𝕜 := fun x =>
    (D.cutoff (e.symm (flattenEquiv e C.frame D.graphExtension x)) : 𝕜)
  have ha : Continuous a :=
    RCLike.continuous_ofReal.comp ((D.smooth.continuous.comp e.symm.continuous).comp
      (flattenEquiv_lipschitz e C.frame D.extension_lipschitz).continuous)
  let M := (testBound (scalarTest 𝕜 (D.physicalTest e C)) : ℝ)
  have hM : ∀ x, ‖a x‖ ≤ M := fun x =>
    norm_le_testBound (scalarTest 𝕜 (D.physicalTest e C))
      (flattenEquiv e C.frame D.graphExtension x)
  exact flatTrace_mul_of_operator hm hp S hS
    ((E.flattenOperator e C 𝕜 p).comp (D.returnOperator e C 𝕜 p)) a ha M hM
    (D.flatten_return_ae_larger e C E hgraph) u

end LiftCollar


/-- Ordinary trace of a returned local piece vanishes outside a fixed
compact collar, as a physical surface class. -/
theorem LiftCollar.returnOperator_trace_support
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space (m + 1))} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) (hp : p ≠ ⊤)
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {K : Set (Ambient m)} (D : LiftCollar C K)
    (E : LiftCollar C (tsupport D.cutoff))
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : HalfSobolev m 𝕜 p) :
    ∀ᵐ x ∂BoundaryFractional.surfaceMeasure (geometricOpen e Ω : Set (Ambient m)),
      x ∉ tsupport E.cutoff →
        boundaryPullback e p (T (D.returnOperator e C 𝕜 p u)) x = 0 := by
  let w := D.returnOperator e C 𝕜 p u
  let a := scalarTest 𝕜 (E.physicalTest e C)
  have hfix : T w = testMultiplier (Ordinary.boundaryMeasure Ω) p a (T w) := by
    have h := trace_testMultiplier e hΩ hp T hT a w
    rw [D.returnOperator_fixed_by_outer e C E u] at h
    exact h
  have hf : (T w : Space (m + 1) → 𝕜) =ᵐ[Ordinary.boundaryMeasure Ω]
      fun x => a x * T w x := by
    nth_rw 1 [hfix]
    exact testMultiplier_ae (Ordinary.boundaryMeasure Ω) p a (T w)
  have hf' := (boundary_measurePreserving e).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [boundaryPullback_ae e (T w), hf'] with x hx hfx hxK
  simp only [Function.comp_apply] at hfx
  rw [hx, hfx]
  change (E.cutoff (e.symm (e x)) : 𝕜) * T w (e x) = 0
  rw [e.symm_apply_apply, image_eq_zero_of_notMem_tsupport hxK,
    RCLike.ofReal_zero, zero_mul]


/-- The support on which a collar is one lies in the cutoff support. -/
theorem LiftCollar.datum_subset_tsupport
    {G : Set (Ambient m)} (C : BoundaryChart G) {K : Set (Ambient m)}
    (D : LiftCollar C K) : K ⊆ tsupport D.cutoff := by
  intro x hx
  apply subset_tsupport
  change D.cutoff x ≠ 0
  rw [D.equal_one x hx]
  exact one_ne_zero

/-- The partition datum vanishes outside any larger lifting collar. -/
theorem localized_representative_support
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (i : Fin A.count) (D : LiftCollar (A.chart i) (tsupport (A.cutoff i)))
    (E : LiftCollar (A.chart i) (tsupport D.cutoff)) (g : Ambient m → 𝕜) :
    ∀ x, x ∉ tsupport E.cutoff → A.cutoff i x • g x = 0 := by
  intro x hx
  have hxφ : x ∉ tsupport (A.cutoff i) := by
    intro hxφ
    exact hx (E.datum_subset_tsupport _ (D.datum_subset_tsupport _ hxφ))
  rw [image_eq_zero_of_notMem_tsupport hxφ, zero_smul]

/-- Convert the sharp theorem's reindexed flat boundary equality into
our whole Euclidean tangent-space representative formula. -/
theorem flat_trace_chart_input_ae (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (i : Fin A.count) (g : Ordinary.BoundaryLp 𝕜 Ω p)
    (v : P102.Trace.BoundaryLp m 𝕜 p)
    (hv : ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p v =
      baseCoordinates m p (ChartInput.lp hm e hΩ A hs hs1 hp i g)) :
    (fun x : Space m => v (boundaryCoordinates m (ACL.coordinates m x))) =ᵐ[volume]
      BoundaryFractional.localizedPullback A i
        (boundaryPullback e p g : Ambient m → 𝕜) := by
  have h := (CoordinateBridge.coordinates_measurePreserving (d := m)).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving v
      (ExpandedFA.PartIV.SharpTraceBound.boundaryCoordinates_measurePreserving (Fin.last m)))
  change (fun x => ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p v
      (ACL.coordinates m x)) =ᵐ[volume]
    (fun x => v (boundaryCoordinates m (ACL.coordinates m x))) at h
  rw [hv] at h
  exact h.symm.trans ((baseCoordinates_reverse
    (ChartInput.lp hm e hΩ A hs hs1 hp i g)).trans
      (ChartInput.lp_ae hm e hΩ A hs hs1 hp i g))

/-- The fixed lifting cutoff absorbs localized tangential data pointwise. -/
theorem localizedPullback_collar_mul
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (i : Fin A.count) (D : LiftCollar (A.chart i) (tsupport (A.cutoff i)))
    (g : Ambient m → 𝕜) (x : Space m) :
    (D.cutoff (BoundaryFractional.graphMap (A.chart i) x) : 𝕜) *
      BoundaryFractional.localizedPullback A i g x =
        BoundaryFractional.localizedPullback A i g x := by
  classical
  unfold BoundaryFractional.localizedPullback
  by_cases hx : x ∈ Metric.ball (A.chart i).center (A.chart i).radius
  · simp only [ite_eq_left hx]
    by_cases hφ : A.cutoff i (BoundaryFractional.graphMap (A.chart i) x) = 0
    · simp only [hφ, zero_smul, mul_zero]
    · rw [D.equal_one _ (subset_tsupport _ hφ), RCLike.ofReal_one, one_mul]
  · simp only [ite_eq_right hx, mul_zero]


section
variable [Fact (1 ≤ p)]

/-- Sum the genuine localized fractional estimates in the whole-space chart norm. -/
theorem chartNorm_bound_of_local (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) (hp : p ≠ ⊤)
    (M : Fin A.count → ℝ) (hM : ∀ i, 0 ≤ M i)
    (g : Ordinary.BoundaryLp 𝕜 Ω p) (r : ℝ)
    (hlocal : ∀ i, ∃ h : P102.Fractional.seminorm Set.univ s p
        (ChartInput.lp hm e hΩ A hs hs1 hp i g : Space m → 𝕜) < ⊤,
      ‖ChartInput.lp hm e hΩ A hs hs1 hp i g‖ +
        (P102.Fractional.seminorm Set.univ s p
          (ChartInput.lp hm e hΩ A hs hs1 hp i g : Space m → 𝕜)).toReal ≤ M i * r) :
    BoundaryFractional.chartNorm A s p (boundaryPullback e p g : Ambient m → 𝕜) ≤
      ENNReal.ofReal (∑ i, M i) * ENNReal.ofReal r := by
  have hterm (i : Fin A.count) :
      eLpNorm (BoundaryFractional.localizedPullback A i
        (boundaryPullback e p g : Ambient m → 𝕜)) p volume +
      P102.Fractional.seminorm Set.univ s p
        (BoundaryFractional.localizedPullback A i (boundaryPullback e p g : Ambient m → 𝕜)) ≤
      ENNReal.ofReal (M i) * ENNReal.ofReal r := by
    obtain ⟨h, hb⟩ := hlocal i
    have heq := ChartInput.lp_ae hm e hΩ A hs hs1 hp i g
    have heq' := (show (ChartInput.lp hm e hΩ A hs hs1 hp i g : Space m → 𝕜) =ᵐ[
      P102.Fractional.domainMeasure Set.univ] _ from by
        simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using heq)
    rw [← eLpNorm_congr_ae heq, ← P102.Fractional.seminorm_congr heq']
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def,
      ← ENNReal.ofReal_toReal h.ne,
      ← ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg]
    rw [← ENNReal.ofReal_mul (hM i)]
    exact ENNReal.ofReal_le_ofReal hb
  calc
    _ ≤ ∑ i, ENNReal.ofReal (M i) * ENNReal.ofReal r := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by
      rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => hM i)]

/-- The quantitative reverse chart comparison converts a bound on chart
norms into the sharp intrinsic norm bound on the physical boundary. -/
theorem intrinsic_bound_of_chart (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) (hp : p ≠ ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hchart : ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p,
      IsTrace T → ∀ u,
      BoundaryFractional.chartNorm A s p (boundaryPullback e p (T u) : Ambient m → 𝕜) ≤
        ENNReal.ofReal C * ENNReal.ofReal ‖u‖) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p, IsTrace T →
      ∀ u, ∃ h : metricSeminorm m (Ordinary.boundaryMeasure Ω) s p
          (T u : Space (m + 1) → 𝕜) < ⊤,
        dataNorm ⟨T u, h⟩ ≤ B * ‖u‖ := by
  obtain ⟨_, D, _, _, hb⟩ := physical_norm_comparison (𝕜 := 𝕜) hm e hΩ A hs hs1 hp
  refine ⟨D * C, mul_nonneg D.coe_nonneg hC, fun T hT u => ?_⟩
  have hbound : metricNorm m (Ordinary.boundaryMeasure Ω) s p
      (T u : Space (m + 1) → 𝕜) ≤ ENNReal.ofReal (D * C * ‖u‖) := by
    calc
      _ ≤ (D : ℝ≥0∞) * BoundaryFractional.chartNorm A s p
          (boundaryPullback e p (T u) : Ambient m → 𝕜) := (hb (T u)).2
      _ ≤ (D : ℝ≥0∞) * (ENNReal.ofReal C * ENNReal.ofReal ‖u‖) :=
        mul_le_mul_right (hchart T hT u) _
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg D.coe_nonneg hC),
          ENNReal.ofReal_mul D.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
  have hnorm : metricNorm m (Ordinary.boundaryMeasure Ω) s p
      (T u : Space (m + 1) → 𝕜) < ⊤ := hbound.trans_lt ENNReal.ofReal_lt_top
  have hsemi : metricSeminorm m (Ordinary.boundaryMeasure Ω) s p
      (T u : Space (m + 1) → 𝕜) < ⊤ :=
    (show _ ≤ metricNorm m (Ordinary.boundaryMeasure Ω) s p
      (T u : Space (m + 1) → 𝕜) from le_add_left le_rfl).trans_lt hnorm
  refine ⟨hsemi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg D.coe_nonneg hC) (norm_nonneg u))).mp
  exact (dataNorm_formula (⟨T u, hsemi⟩ : BoundaryData 𝕜 Ω s p)).le.trans hbound

end

/-- The unweighted patch pullback respects arbitrary surface representatives. -/
theorem patch_pullback_congr {m : ℕ} {G : Set (Ambient m)}
    (C : BoundaryChart G) {E : Type*} [NormedAddCommGroup E]
    {q r : Ambient m → E}
    (h : q =ᵐ[BoundaryPatchExtension.surfaceMeasure G] r) :
    BoundaryPatchExtension.pullback C q =ᵐ[volume]
      BoundaryPatchExtension.pullback C r := by
  have hp := ae_restrict_of_ae h (s := BoundaryPatchExtension.patch C)
  rw [← BoundaryPatchExtension.graphMeasure_eq C] at hp
  have hb := ((GraphFractionalTransport.representative_transport m C.center C.radius
    C.radius_pos C.graphFunction C.constant C.graph_lipschitz C.frame E q r).1).mp hp
  have hb' := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hb
  filter_upwards [hb'] with x hx
  classical
  by_cases hxB : x ∈ Metric.ball C.center C.radius
  · simp only [BoundaryPatchExtension.pullback, indicator_of_mem hxB]
    exact hx hxB
  · simp only [BoundaryPatchExtension.pullback, indicator_of_notMem hxB]

/-- A surface multiplier which fixes the class can be inserted into its
zero-extended patch pullback. -/
theorem patch_pullback_eq_localized_of_fixed
    {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    {𝕜 : Type} [RCLike 𝕜] (χ : Ambient m → ℝ) (q : Ambient m → 𝕜)
    (h : q =ᵐ[BoundaryPatchExtension.surfaceMeasure G] fun x => χ x • q x) :
    BoundaryPatchExtension.pullback C q =ᵐ[volume]
      BoundaryChartLocalization.localizedPullback C χ q := by
  have hp := patch_pullback_congr C h
  filter_upwards [hp] with x hx
  classical
  by_cases hxB : x ∈ Metric.ball C.center C.radius
  · simpa only [BoundaryPatchExtension.pullback, indicator_of_mem hxB,
      Function.comp_apply, BoundaryChartLocalization.localizedPullback,
      ite_eq_left hxB, BoundaryChartLocalization.chartGraph] using hx
  · simp only [BoundaryPatchExtension.pullback, indicator_of_notMem hxB,
      BoundaryChartLocalization.localizedPullback, ite_eq_right hxB]

/-- The outer collar fixes the returned trace as a surface representative. -/
theorem LiftCollar.returnOperator_trace_fixed
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space (m + 1))} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) (hp : p ≠ ⊤)
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {K : Set (Ambient m)} (D : LiftCollar C K)
    (E : LiftCollar C (tsupport D.cutoff))
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : HalfSobolev m 𝕜 p) :
    (boundaryPullback e p (T (D.returnOperator e C 𝕜 p u)) : Ambient m → 𝕜) =ᵐ[
      BoundaryFractional.surfaceMeasure (geometricOpen e Ω : Set (Ambient m))]
      fun x => E.cutoff x • boundaryPullback e p (T (D.returnOperator e C 𝕜 p u)) x := by
  let w := D.returnOperator e C 𝕜 p u
  let a := scalarTest 𝕜 (E.physicalTest e C)
  have hfix : T w = testMultiplier (Ordinary.boundaryMeasure Ω) p a (T w) := by
    have h := trace_testMultiplier e hΩ hp T hT a w
    rw [D.returnOperator_fixed_by_outer e C E u] at h
    exact h
  have hf : (T w : Space (m + 1) → 𝕜) =ᵐ[Ordinary.boundaryMeasure Ω]
      fun x => a x * T w x := by
    nth_rw 1 [hfix]
    exact testMultiplier_ae (Ordinary.boundaryMeasure Ω) p a (T w)
  have hf' := (boundary_measurePreserving e).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [boundaryPullback_ae e (T w), hf'] with x hx hfx
  simp only [Function.comp_apply] at hfx
  rw [hx]
  rw [RCLike.real_smul_eq_coe_mul]
  change T w (e x) = (E.cutoff (e.symm (e x)) : 𝕜) * T w (e x) at hfx
  simpa only [e.symm_apply_apply] using hfx


section
variable [Fact (1 ≤ p)]

namespace GraphInput
variable (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  (χ : Ambient m → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)

def raw (g : Ordinary.BoundaryLp 𝕜 Ω p) : Space m → 𝕜 :=
  BoundaryChartLocalization.localizedPullback C χ (boundaryPullback e p g)

include hχ hc

theorem bound : ∃ M : ℝ≥0, ∀ g : Ordinary.BoundaryLp 𝕜 Ω p,
    eLpNorm (raw e C χ g) p volume ≤ (M : ℝ≥0∞) * eLpNorm g p (Ordinary.boundaryMeasure Ω) := by
  obtain ⟨M, J, hJ, hM⟩ := BoundaryChartLocalization.cutoff_bounds C χ hχ hc
  refine ⟨M, fun g => ?_⟩
  let b := boundaryPullback e p g
  have hb := (Lp.memLp b).mono_measure
    (BoundaryChartLocalization.graphMeasure_le_surfaceMeasure C)
  have hbase := (GraphFractionalTransport.graph_memLp_iff Metric.isOpen_ball
    C.graph_lipschitz C.frame p (b : Ambient m → 𝕜)).mp hb
  let φ : Space m → 𝕜 := fun x => (χ (BoundaryFractional.graphMap C x) : 𝕜)
  have hφ : LipschitzOnWith J φ (Metric.ball C.center C.radius) := by
    simpa only [φ, BoundaryFractional.graphMap, BoundaryChartLocalization.chartGraph,
      GraphFractionalTransport.graphMap, Function.comp_def, one_mul] using RCLike.lipschitzWith_ofReal.comp_lipschitzOnWith hJ
  have hφM : ∀ x ∈ Metric.ball C.center C.radius, ‖φ x‖ ≤ M := by
    intro x hx
    simpa only [φ, BoundaryFractional.graphMap, BoundaryChartLocalization.chartGraph,
      GraphFractionalTransport.graphMap, Function.comp_def, RCLike.norm_ofReal, Real.norm_eq_abs] using hM x hx
  have hmul := P102.Fractional.LocalizationMultiplier.eLpNorm_mul_le
    Metric.isOpen_ball hφ hφM hbase
  have hgraph := (GraphFractionalTransport.graph_eLpNorm_comparison Metric.isOpen_ball
    C.graph_lipschitz C.frame p (b : Ambient m → 𝕜)).1
  have hfun : raw e C χ g = (Metric.ball C.center C.radius).indicator
      (fun x => φ x * b (BoundaryFractional.graphMap C x)) := by
    funext x
    classical
    simp only [raw, BoundaryChartLocalization.localizedPullback, Set.indicator, φ,
      BoundaryChartLocalization.chartGraph, BoundaryFractional.graphMap,
      GraphFractionalTransport.graphMap, Function.comp_def, b, RCLike.real_smul_eq_coe_mul]
  rw [hfun, eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet]
  apply hmul.trans
  apply mul_le_mul_right
  calc
    _ ≤ eLpNorm b p (GraphFractionalTransport.graphMeasure C.frame
        C.graphFunction (Metric.ball C.center C.radius)) := hgraph
    _ ≤ eLpNorm b p (BoundaryFractional.surfaceMeasure (geometricOpen e Ω : Set (Ambient m))) :=
      eLpNorm_mono_measure _ (BoundaryChartLocalization.graphMeasure_le_surfaceMeasure C)
    _ = eLpNorm (g : Space (m + 1) → 𝕜) p (Ordinary.boundaryMeasure Ω) := by
      rw [← Lp.enorm_def, ← Lp.enorm_def]
      exact (boundaryPullback e p).enorm_map g

theorem memLp (g : Ordinary.BoundaryLp 𝕜 Ω p) : MemLp (raw e C χ g) p volume :=
  ((bound (𝕜 := 𝕜) (p := p) e C χ hχ hc).choose_spec g).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (Lp.memLp g))

def lp (g : Ordinary.BoundaryLp 𝕜 Ω p) : Lp 𝕜 p (volume : Measure (Space m)) :=
  (memLp e C χ hχ hc g).toLp _

theorem lp_ae (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    lp e C χ hχ hc g =ᵐ[volume] raw e C χ g :=
  (memLp e C χ hχ hc g).coeFn_toLp

theorem lp_add (g h : Ordinary.BoundaryLp 𝕜 Ω p) :
    lp e C χ hχ hc (g + h) = lp e C χ hχ hc g + lp e C χ hχ hc h := by
  have hlocal := BoundaryChartLocalization.representative_independence m _ C χ 𝕜
    _ _ (Lp.coeFn_add (boundaryPullback e p g) (boundaryPullback e p h))
  apply Lp.ext
  filter_upwards [lp_ae e C χ hχ hc (g + h), lp_ae e C χ hχ hc g,
    lp_ae e C χ hχ hc h, Lp.coeFn_add (lp e C χ hχ hc g) (lp e C χ hχ hc h), hlocal]
    with x hx hg hh hxadd hl
  rw [hx, hxadd, Pi.add_apply, hg, hh]
  simp only [raw, map_add]
  rw [hl]
  classical
  simp only [BoundaryChartLocalization.localizedPullback, Pi.add_apply]
  split_ifs <;> simp [smul_add]

theorem lp_smul (c : 𝕜) (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    lp e C χ hχ hc (c • g) = c • lp e C χ hχ hc g := by
  have hlocal := BoundaryChartLocalization.representative_independence m _ C χ 𝕜
    _ _ (Lp.coeFn_smul c (boundaryPullback e p g))
  apply Lp.ext
  filter_upwards [lp_ae e C χ hχ hc (c • g), lp_ae e C χ hχ hc g,
    Lp.coeFn_smul c (lp e C χ hχ hc g), hlocal] with x hx hg hxsmul hl
  rw [hx, hxsmul, Pi.smul_apply, hg]
  simp only [raw, map_smul]
  rw [hl]
  classical
  simp only [BoundaryChartLocalization.localizedPullback, Pi.smul_apply]
  split_ifs <;> simp [smul_comm]

def linear : Ordinary.BoundaryLp 𝕜 Ω p →ₗ[𝕜] Lp 𝕜 p (volume : Measure (Space m)) where
  toFun := lp e C χ hχ hc
  map_add' := lp_add e C χ hχ hc
  map_smul' := lp_smul e C χ hχ hc

theorem lp_bound : ∃ M : ℝ≥0, ∀ g : Ordinary.BoundaryLp 𝕜 Ω p,
    ‖lp e C χ hχ hc g‖ ≤ M * ‖g‖ := by
  obtain ⟨M, hM⟩ := bound (𝕜 := 𝕜) (p := p) e C χ hχ hc
  refine ⟨M, fun g => ?_⟩
  rw [Lp.norm_def, eLpNorm_congr_ae (lp_ae e C χ hχ hc g)]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top g)) (hM g)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← Lp.norm_def] using ht

set_option maxHeartbeats 1000000 in
def continuousLinear : Ordinary.BoundaryLp 𝕜 Ω p →L[𝕜] Lp 𝕜 p (volume : Measure (Space m)) :=
  (linear e C χ hχ hc).mkContinuous (lp_bound (𝕜 := 𝕜) (p := p) e C χ hχ hc).choose
    (lp_bound (𝕜 := 𝕜) (p := p) e C χ hχ hc).choose_spec

end GraphInput

theorem flat_point_coordinates (x : Fin m → ℝ) :
    point m (ExpandedFA.PartIV.SharpTraceBound.boundaryCoordinates (Fin.last m) x) 0 =
      splitCoordinates m (WithLp.toLp 2 (WithLp.toLp 2 x, (0 : ℝ))) := by
  change WithLp.toLp 2 (ExpandedFA.Sobolev.Lines.coordinateLine _ _ _) = _
  rw [show ExpandedFA.PartIV.SharpTraceBound.boundaryCoordinates (Fin.last m) =
      ExpandedFA.Sobolev.Trace.transverseFinEquiv (Fin.last m) from rfl,
    ExpandedFA.Sobolev.Trace.coordinateLine_transverseFinEquiv]
  rw [Fin.insertNth_last']
  rfl

theorem flatten_at_face (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (γ : Space m → ℝ) (x : Fin m → ℝ) :
    flattenEquiv e C.frame γ
      (point m (ExpandedFA.PartIV.SharpTraceBound.boundaryCoordinates (Fin.last m) x) 0) =
      e (C.frame (graph γ (WithLp.toLp 2 x))) := by
  rw [flat_point_coordinates, flattenEquiv_apply, LinearIsometryEquiv.symm_apply_apply]
  congr 2
  simp only [shear, graph, WithLp.ofLp_toLp, add_zero]

namespace LiftCollar
variable (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
  (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
  {K : Set (Ambient m)} (D : LiftCollar C K)

theorem cutoff_extended_graph_zero {x : Space m}
    (hx : x ∉ Metric.ball C.center C.radius) :
    D.cutoff (C.frame (graph D.graphExtension x)) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hsupport
  obtain ⟨_, ⟨w, hw, hweq⟩, heq⟩ := D.support_subset hsupport
  have hcoord := C.frame.injective heq
  rw [← hweq] at hcoord
  have hfirst := congrArg (fun z : Ambient m => z.ofLp.1) hcoord
  have hwx : w.ofLp.1 = x := by simpa only [shear, graph, WithLp.ofLp_toLp] using hfirst
  exact hx (hwx ▸ hw.1)

theorem localized_boundary_formula (f : Space (m + 1) → 𝕜) (x : Space m) :
    BoundaryChartLocalization.localizedPullback C D.cutoff (f ∘ e) x =
      D.cutoff (C.frame (graph D.graphExtension x)) •
        f (e (C.frame (graph D.graphExtension x))) := by
  classical
  by_cases hx : x ∈ Metric.ball C.center C.radius
  · rw [BoundaryChartLocalization.localizedPullback, ite_eq_left hx]
    have hγ := D.extension_agrees hx
    simp only [BoundaryChartLocalization.chartGraph, GraphFractionalTransport.graphMap,
      Function.comp_apply, graph, hγ]
  · rw [BoundaryChartLocalization.localizedPullback, ite_eq_right hx,
      D.cutoff_extended_graph_zero e C hx, zero_smul]

 theorem flattenOperator_smooth_commutes (hm : 1 ≤ m) (hp : p ≠ ⊤)
    (S : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p) (hS : IsFlatTrace S)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : Sobolev 𝕜 Ω 1 p) (f : Space (m + 1) → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p
      (S (D.flattenOperator e C 𝕜 p u)) =
        baseCoordinates m p (GraphInput.lp e C D.cutoff D.smooth D.compact (T u)) := by
  have hphysical := hT u f hf hu
  have hpull := (boundaryPullback_ae e (T u)).trans
    ((boundary_measurePreserving e).quasiMeasurePreserving.ae_eq_comp hphysical)
  have hlocal := BoundaryChartLocalization.representative_independence m _ C D.cutoff 𝕜 _ _ hpull
  have hflat := (ExpandedFA.PartIV.SharpTraceBound.boundaryCoordinates_measurePreserving
    (Fin.last m)).quasiMeasurePreserving.ae_eq_comp
      (D.flattenOperator_smooth_trace e C hm hp S hS u f hf.continuous hu)
  have hlocfin := (PiLp.volume_preserving_toLp (Fin m)).quasiMeasurePreserving.ae_eq_comp
    ((GraphInput.lp_ae e C D.cutoff D.smooth D.compact (T u)).trans hlocal)
  apply Lp.ext
  filter_upwards [hflat, hlocfin,
    Lp.coeFn_compMeasurePreserving (S (D.flattenOperator e C 𝕜 p u))
      (ExpandedFA.PartIV.SharpTraceBound.boundaryCoordinates_measurePreserving (Fin.last m)),
    Lp.coeFn_compMeasurePreserving (GraphInput.lp e C D.cutoff D.smooth D.compact (T u))
      (PiLp.volume_preserving_toLp (Fin m))] with x hx hloc hleft hright
  change (Lp.compMeasurePreserving _ _ (S (D.flattenOperator e C 𝕜 p u))) x =
    (Lp.compMeasurePreserving _ _ (GraphInput.lp e C D.cutoff D.smooth D.compact (T u))) x
  rw [hleft, hright, hx, hloc]
  simp only [Function.comp_apply, D.localized_boundary_formula e C, flatten_at_face]
  simp only [LinearIsometryEquiv.symm_apply_apply]

 theorem flattenOperator_commutes (hm : 1 ≤ m)
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) (hp : p ≠ ⊤)
    (S : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p) (hS : IsFlatTrace S)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : Sobolev 𝕜 Ω 1 p) :
    ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p
      (S (D.flattenOperator e C 𝕜 p u)) =
        baseCoordinates m p (GraphInput.lp e C D.cutoff D.smooth D.compact (T u)) := by
  obtain ⟨φ, v, hv, hvlim⟩ := lipschitz_ambient_density m e Ω hΩ 𝕜 p hp u
  have hvrep (n : ℕ) : sobolevUnderlying (v n) =ᵐ[
      volume.restrict (Ω : Set (Space (m + 1)))] φ n := by
    simpa only [sobolevUnderlying, zeroSobolevIndex, multiPartial, Multiset.sort_zero,
      partialWord] using hv n (zeroSobolevIndex (m + 1) 1)
  have heq (n : ℕ) := D.flattenOperator_smooth_commutes e C hm hp S hS T hT
    (v n) (φ n) (φ n).contDiff (hvrep n)
  have hl := ((ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p).continuous.tendsto
    (S (D.flattenOperator e C 𝕜 p u))).comp
      (S.continuous.tendsto _ |>.comp ((D.flattenOperator e C 𝕜 p).continuous.tendsto _ |>.comp hvlim))
  have hr := ((baseCoordinates m p).continuous.tendsto
    (GraphInput.lp e C D.cutoff D.smooth D.compact (T u))).comp
      ((GraphInput.continuousLinear e C D.cutoff D.smooth D.compact).continuous.tendsto _ |>.comp
        (T.continuous.tendsto _ |>.comp hvlim))
  exact tendsto_nhds_unique hl (hr.congr (fun n => (heq n).symm))

end LiftCollar
/-- Use the atlas factor itself as a bulk cutoff; the empty marked set imposes no unit constraint. -/
def atlasFlattenCollar (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m))) (i : Fin A.count) :
    LiftCollar (A.chart i) ∅ where
  graphExtension := (Classical.choice (atlas_liftCollar_exists e A i)).graphExtension
  extension_lipschitz := (Classical.choice (atlas_liftCollar_exists e A i)).extension_lipschitz
  extension_agrees := (Classical.choice (atlas_liftCollar_exists e A i)).extension_agrees
  cutoff := A.cutoff i
  smooth := A.smooth i
  compact := A.compact i
  equal_one := fun _ hx => False.elim hx
  support_subset := fun _ hx => chartImage_mono (A.chart i).frame (A.chart i).graphFunction
    (A.chart i).center (A.smaller i).2.1.le (A.smaller i).2.2.2.le (A.support_subset i hx)

theorem graphInput_atlas (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp : p ≠ ⊤)
    (i : Fin A.count) (g : Ordinary.BoundaryLp 𝕜 Ω p) :
    GraphInput.lp e (A.chart i) (A.cutoff i) (A.smooth i) (A.compact i) g =
      ChartInput.lp hm e hΩ A hs hs1 hp i g := by
  apply Lp.ext
  refine (GraphInput.lp_ae e (A.chart i) (A.cutoff i) (A.smooth i) (A.compact i) g).trans ?_
  exact (ChartInput.lp_ae hm e hΩ A hs hs1 hp i g).symm

theorem fractional_base_norm {s : ℝ}
    (v : Lp 𝕜 p (volume : Measure (Space m)))
    (h : ExpandedFA.PartIV.FractionalSobolev.differenceEnergy s p (baseCoordinates m p v) < ⊤) :
    ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p ⟨baseCoordinates m p v, h⟩ =
      ‖v‖ + (P102.Fractional.seminorm Set.univ s p (v : Space m → 𝕜)).toReal := by
  rw [CoordinateBridge.fractional_full_norm_coordinates]
  change ‖baseCoordinates m p v‖ + _ = _
  rw [(baseCoordinates m p).norm_map]
  congr 1
  congr 1
  apply P102.Fractional.seminorm_congr
  simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using baseCoordinates_reverse v

theorem fractional_base_finite {s : ℝ} (hp : p ≠ ⊤)
    (v : Lp 𝕜 p (volume : Measure (Space m)))
    (h : ExpandedFA.PartIV.FractionalSobolev.differenceEnergy s p (baseCoordinates m p v) < ⊤) :
    P102.Fractional.seminorm Set.univ s p (v : Space m → 𝕜) < ⊤ := by
  rw [CoordinateBridge.fractional_energy_coordinates,
    P102.Fractional.energy_congr (by
      simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using baseCoordinates_reverse v)] at h
  exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr ENNReal.toReal_nonneg) h.ne

theorem localized_flat_bound (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ (Cf : ℝ) (Q : Fin A.count → Sobolev 𝕜 Ω 1 p →L[𝕜] HalfSobolev m 𝕜 p),
      0 ≤ Cf ∧
      ∀ T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p, IsTrace T →
      ∀ (u : Sobolev 𝕜 Ω 1 p) (i : Fin A.count),
        P102.Fractional.seminorm Set.univ (1 - 1 / p.toReal) p
          (ChartInput.lp hm e hΩ A (trace_order_range hp1 hp).1
            (trace_order_range hp1 hp).2 hp i (T u) : Space m → 𝕜) < ⊤ ∧
        ‖ChartInput.lp hm e hΩ A (trace_order_range hp1 hp).1
          (trace_order_range hp1 hp).2 hp i (T u)‖ +
          (P102.Fractional.seminorm Set.univ (1 - 1 / p.toReal) p
            (ChartInput.lp hm e hΩ A (trace_order_range hp1 hp).1
              (trace_order_range hp1 hp).2 hp i (T u) : Space m → 𝕜)).toReal ≤
            Cf * ‖Q i‖ * ‖u‖ := by
  letI : Fact (p ≠ ⊤) := ⟨hp⟩
  obtain ⟨Cf, hCf, hflat⟩ := exact_flat_trace m hm p hp1 hp
  obtain ⟨⟨S, hS⟩, hall⟩ := hflat 𝕜
  have hsharp := (hall S hS).1
  let Q := fun i => (atlasFlattenCollar e A i).flattenOperator e (A.chart i) 𝕜 p
  refine ⟨Cf, Q, hCf, ?_⟩
  intro T hT u i
  have hcomm := (atlasFlattenCollar e A i).flattenOperator_commutes e (A.chart i)
    hm hΩ hp S hS T hT u
  change ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p (S (Q i u)) =
    baseCoordinates m p (GraphInput.lp e (A.chart i) (A.cutoff i) (A.smooth i) (A.compact i) (T u)) at hcomm
  rw [graphInput_atlas hm e hΩ A (trace_order_range hp1 hp).1
    (trace_order_range hp1 hp).2 hp] at hcomm
  obtain ⟨henergy, hbound⟩ := hsharp (Q i u)
  have henergy2 := henergy
  rw [hcomm] at henergy2
  have hbound2 : ExpandedFA.PartIV.FractionalSobolev.fractionalNorm (1 - 1 / p.toReal) p
      ⟨baseCoordinates m p (ChartInput.lp hm e hΩ A (trace_order_range hp1 hp).1
        (trace_order_range hp1 hp).2 hp i (T u)), henergy2⟩ ≤ Cf * ‖Q i u‖ := by
    simpa only [hcomm] using hbound
  refine ⟨fractional_base_finite hp _ henergy2, ?_⟩
  rw [fractional_base_norm] at hbound2
  exact hbound2.trans ((mul_le_mul_of_nonneg_left ((Q i).le_opNorm u) hCf).trans_eq (mul_assoc _ _ _).symm)


end

/-- The sharp bound is for every realization of the ordinary physical trace. -/
theorem sharp_bound : Expected.SharpBound := by
  intro m hm e Ω hΩ 𝕜 _ p _ hp1 hp
  obtain ⟨A⟩ := BoundaryFractional.atlas_exists m _ hΩ
  have hs := trace_order_range hp1 hp
  obtain ⟨Cf, Q, hCf, hlocal⟩ := localized_flat_bound (𝕜 := 𝕜) hm e hΩ A hp1 hp
  let M : Fin A.count → ℝ := fun i => Cf * ‖Q i‖
  have hM : ∀ i, 0 ≤ M i := fun i => mul_nonneg hCf (norm_nonneg (Q i))
  apply intrinsic_bound_of_chart hm e hΩ A hs.1 hs.2 hp (∑ i, M i)
    (Finset.sum_nonneg fun i _ => hM i)
  intro T hT u
  apply chartNorm_bound_of_local hm e hΩ A hs.1 hs.2 hp M hM (T u) ‖u‖
  intro i
  exact ⟨(hlocal T hT u i).1, (hlocal T hT u i).2⟩

/-- The explicit reindexing used by the flat theorem, now in Euclidean base coordinates. -/
def faceCoordinates (m : ℕ) (x : Space m) : Boundary m :=
  P102.Trace.boundaryCoordinates m (ACL.coordinates m x)

theorem faceCoordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (faceCoordinates m) volume volume :=
  (P102.Trace.boundaryCoordinates_measurePreserving m).comp
    (CoordinateBridge.coordinates_measurePreserving (d := m))

theorem flatBoundaryPullback_reverse [Fact (1 ≤ p)]
    (q : P102.Trace.BoundaryLp m 𝕜 p) :
    (fun x => ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p q
      (ACL.coordinates m x)) =ᵐ[volume] fun x => q (faceCoordinates m x) := by
  exact (CoordinateBridge.coordinates_measurePreserving (d := m)).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving q
      (ExpandedFA.PartIV.SharpTraceBound.boundaryCoordinates_measurePreserving (Fin.last m)))


/-- The fixed local lifts recover precisely the localized physical boundary
classes under every ordinary trace. -/
theorem returned_local_trace (hm : 1 ≤ m)
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (A : BoundaryFractional.Atlas (geometricOpen e Ω : Set (Ambient m)))
    (hs : 0 < s) (hs1 : s < 1) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (i : Fin A.count) (D : LiftCollar (A.chart i) (tsupport (A.cutoff i)))
    (S : HalfSobolev m 𝕜 p →L[𝕜] P102.Trace.BoundaryLp m 𝕜 p) (hS : IsFlatTrace S)
    (T : Sobolev 𝕜 Ω 1 p →L[𝕜] Ordinary.BoundaryLp 𝕜 Ω p) (hT : Ordinary.IsTrace T)
    (u : HalfSobolev m 𝕜 p) (g : Ordinary.BoundaryLp 𝕜 Ω p)
    (hu : ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p (S u) =
      baseCoordinates m p (ChartInput.lp hm e hΩ A hs hs1 hp i g)) :
    boundaryPullback e p (T (D.returnOperator e (A.chart i) 𝕜 p u)) =ᵐ[
      BoundaryFractional.surfaceMeasure (geometricOpen e Ω : Set (Ambient m))]
      fun x => A.cutoff i x • boundaryPullback e p g x := by
  obtain ⟨E, hgraph⟩ := D.outer_exists (A.chart i)
  let w := D.returnOperator e (A.chart i) 𝕜 p u
  let q := boundaryPullback e p (T w)
  let r : Ambient m → 𝕜 := fun x => A.cutoff i x • boundaryPullback e p g x
  have hqfix := D.returnOperator_trace_fixed e hΩ hp (A.chart i) E T hT u
  have hq := D.returnOperator_trace_support e hΩ hp (A.chart i) E T hT u
  have hr : ∀ᵐ x ∂BoundaryFractional.surfaceMeasure
      (geometricOpen e Ω : Set (Ambient m)), x ∉ tsupport E.cutoff → r x = 0 :=
    ae_of_all _ (localized_representative_support e A i D E
      (boundaryPullback e p g : Ambient m → 𝕜))
  apply supported_pullback_injective (A.chart i) E.support_subset hq hr
  -- The following chain identifies both full-base pullbacks.
  have hcomm := E.flattenOperator_commutes e (A.chart i) hm hΩ hp S hS T hT w
  have hflat := D.flatten_return_trace_larger e (A.chart i) hm hp S hS E hgraph u
  have hin := flat_trace_chart_input_ae hm e hΩ A hs hs1 hp i g (S u) hu
  have hflatbase := (faceCoordinates_measurePreserving m).quasiMeasurePreserving.ae_eq_comp hflat
  have hQ := flatBoundaryPullback_reverse (S (E.flattenOperator e (A.chart i) 𝕜 p w))
  rw [hcomm] at hQ
  have hbase := (hQ.symm.trans (baseCoordinates_reverse
    (GraphInput.lp e (A.chart i) E.cutoff E.smooth E.compact (T w)))).symm
  have hloc := GraphInput.lp_ae e (A.chart i) E.cutoff E.smooth E.compact (T w)
  have hqpull := patch_pullback_eq_localized_of_fixed (A.chart i) E.cutoff q hqfix
  filter_upwards [hbase, hloc, hflatbase, hin, hqpull] with x hx hl hf hi hqp
  change GraphInput.lp e (A.chart i) E.cutoff E.smooth E.compact (T w) x =
    BoundaryChartLocalization.localizedPullback (A.chart i) E.cutoff (q : Ambient m → 𝕜) x at hl
  change S (E.flattenOperator e (A.chart i) 𝕜 p w) (faceCoordinates m x) =
    (D.cutoff (e.symm (flattenEquiv e (A.chart i).frame D.graphExtension
      (point m (faceCoordinates m x) 0))) : 𝕜) * S u (faceCoordinates m x) at hf
  change S u (faceCoordinates m x) = _ at hi
  rw [hqp, ← hl, hx, hf, hi]
  -- pointwise boundary cutoff absorption and graph agreement finish the equality
  by_cases hxb : x ∈ Metric.ball (A.chart i).center (A.chart i).radius
  · have hγ := D.extension_agrees hxb
    have hface := flatten_at_face e (A.chart i) D.graphExtension (ACL.coordinates m x)
    change flattenEquiv e (A.chart i).frame D.graphExtension (point m (faceCoordinates m x) 0) =
      e ((A.chart i).frame (graph D.graphExtension x)) at hface
    rw [hface, LinearIsometryEquiv.symm_apply_apply]
    simp only [graph, ← hγ]
    change (D.cutoff (BoundaryFractional.graphMap (A.chart i) x) : 𝕜) * _ = _
    rw [localizedPullback_collar_mul e A i D (boundaryPullback e p g : Ambient m → 𝕜) x]
    rfl
  · simp only [BoundaryFractional.localizedPullback, ite_eq_right hxb, mul_zero,
      BoundaryPatchExtension.pullback, indicator_of_notMem hxb]

/-- The finite fixed-cutoff construction is the desired bounded linear right inverse. -/
theorem right_inverse : Expected.RightInverse := by
  intro m hm e Ω hΩ 𝕜 _ p _ hp1 hp
  obtain ⟨A⟩ := BoundaryFractional.atlas_exists m (geometricOpen e Ω : Set (Ambient m)) hΩ
  obtain ⟨B, S, F, D, hS, hflat, hB, hadd, hsmul, hnorm⟩ :=
    lift_construction (𝕜 := 𝕜) hm e hΩ A hp1 hp
  let L := fun g : BoundaryData 𝕜 Ω (1 - 1 / p.toReal) p =>
    ∑ i, (D i).returnOperator e (A.chart i) 𝕜 p (F i g)
  refine ⟨B, L, hB, hadd, hsmul, hnorm, ?_⟩
  intro T hT g
  apply (boundaryPullback e p).injective
  rw [show T (L g) = ∑ i, T ((D i).returnOperator e (A.chart i) 𝕜 p (F i g)) from
    map_sum T _ _, map_sum]
  apply Lp.ext
  have hlocal := fun i => returned_local_trace hm e hΩ A
    (trace_order_range hp1 hp).1 (trace_order_range hp1 hp).2 hp i (D i)
    S hS T hT (F i g) g.val (hflat i g)
  have hall := ae_all_iff.mpr hlocal
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => boundaryPullback e p (T ((D i).returnOperator e (A.chart i) 𝕜 p (F i g)))),
    hall, ae_restrict_mem isClosed_frontier.measurableSet] with x hsum hx hxfront
  rw [hsum]
  simp only [Finset.sum_apply]
  simp_rw [hx]
  exact BoundaryFractional.partition_reconstruction A _ hxfront


/-- Conditional derivation of the complete original exact-trace theorem.
The sole premise is the full, unmodified ordinary trace theorem. The original
closed target is deliberately reserved for the owner after dependency closure. -/
theorem exact_trace_conditional (hordinary : Ordinary.Expected.OrdinaryTrace) :
    Expected.ExactTrace :=
  ⟨trace_existence_conditional hordinary, sharp_bound, right_inverse,
    onto_of_rightInverse right_inverse, kernel_conditional hordinary⟩

end P102.Trace.Exact

theorem _root_.«P102».«Trace».«Exact».«exact_trace» : _root_.«P102».«Trace».«Exact».«Expected».«ExactTrace» :=
  @_root_.«P102».«Trace».«Exact».«exact_trace_conditional» (@_root_.«P102».«Trace».«Ordinary».«ordinary_trace»)
