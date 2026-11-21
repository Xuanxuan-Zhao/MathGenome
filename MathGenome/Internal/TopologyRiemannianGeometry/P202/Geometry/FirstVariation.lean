import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.FirstVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthLaws
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! First variation on smooth and finite-piecewise compact segments.
The proofs use actual one-sided tangent velocities, smooth coordinate germs,
metric compatibility, and symmetry of the Levi–Civita coefficients. Compactness
justifies differentiation under the integral and supplies a positive-speed strip
for length. Endpoint and corner terms retain their original tangent fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.CurveData
open Set Filter MeasureTheory
universe u

/-- The integral of the centered square, without any positivity requirement on f. -/
theorem integral_centered_square {a b : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) (v : ℝ) :
    (∫ t in a..b, (f t - v) ^ 2) =
      (∫ t in a..b, f t ^ 2) - 2 * v * (∫ t in a..b, f t) + (b - a) * v ^ 2 := by
  have h : (fun t => (f t - v)^2) =
      (fun t => f t^2 - (2*v) * f t + v^2) := by funext t; ring
  rw [h, intervalIntegral.integral_add (hf2.sub (hf.const_mul _))
    intervalIntegrable_const, intervalIntegral.integral_sub hf2 (hf.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [smul_eq_mul]

/-- Cauchy–Schwarz on a finite interval via the nonnegative centered square. -/
theorem integral_sq_le {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t)^2 ≤ (b-a) * (∫ t in a..b, f t^2) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let v := (∫ t in a..b, f t) / (b-a)
  have hv : v * (b-a) = ∫ t in a..b, f t := div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
  have h := intervalIntegral.integral_nonneg (μ := volume) hab.le (fun t _ => sq_nonneg (f t-v))
  rw [integral_centered_square hf hf2 v] at h
  have hmul := mul_nonneg (sub_nonneg.mpr hab.le) h
  nlinarith [sq_nonneg (v * (b-a) - ∫ t in a..b, f t)]

/-- Equality for a speed that is constant almost everywhere. -/
theorem integral_sq_eq_of_ae_const {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} {v : ℝ} (h : f =ᵐ[volume.restrict (Ioc a b)] fun _ => v) :
    (∫ t in a..b, f t)^2 = (b-a) * (∫ t in a..b, f t^2) := by
  have hi : (∫ t in a..b, f t) = (b-a)*v := by
    rw [intervalIntegral.integral_of_le hab]
    rw [MeasureTheory.integral_congr_ae h]
    simp [Real.volume_real_Ioc_of_le hab]
  have hi2 : (∫ t in a..b, f t^2) = (b-a)*v^2 := by
    rw [intervalIntegral.integral_of_le hab]
    have h2 : (fun t => f t^2) =ᵐ[volume.restrict (Ioc a b)] fun _ => v^2 :=
      h.fun_comp (fun x : ℝ => x^2)
    rw [MeasureTheory.integral_congr_ae h2]
    simp [Real.volume_real_Ioc_of_le hab]
  rw [hi, hi2]
  ring

/-- The equality case of Cauchy–Schwarz for a continuous real speed. -/
theorem integral_sq_eq_iff_constant {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    (∫ t in a..b, f t)^2 = (b-a) * (∫ t in a..b, f t^2) ↔
      ∃ v : ℝ, ∀ t ∈ Icc a b, f t = v := by
  constructor
  · intro heq
    let v := (∫ t in a..b, f t) / (b-a)
    have hv : v * (b-a) = ∫ t in a..b, f t := div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
    have hfi := hf.intervalIntegrable_of_Icc (μ := volume) hab.le
    have hf2 := (hf.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
    have hvar : (∫ t in a..b, (f t-v)^2) = 0 := by
      rw [integral_centered_square hfi hf2 v]
      apply (mul_left_cancel₀ (sub_ne_zero.mpr hab.ne'))
      nlinarith [sq_nonneg (v * (b-a) - ∫ t in a..b, f t)]
    have hvcont : ContinuousOn (fun t => (f t-v)^2) (Icc a b) :=
      (hf.sub continuousOn_const).pow 2
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Eventually.of_forall (fun t => sq_nonneg (f t-v)))
      (hvcont.intervalIntegrable_of_Icc hab.le)).mp hvar
    have hfv : f =ᵐ[volume.restrict (Ioc a b)] fun _ => v := by
      filter_upwards [hae] with t ht
      have ht' : (f t-v)^2 = 0 := ht
      nlinarith [sq_nonneg (f t-v)]
    have hfv' : f =ᵐ[volume.restrict (Icc a b)] fun _ => v := by
      rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hfv
    exact ⟨v, Measure.eqOn_Icc_of_ae_eq volume hab.ne hfv' hf continuousOn_const⟩
  · rintro ⟨v, hv⟩
    apply integral_sq_eq_of_ae_const hab.le
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hv t ⟨ht.1.le, ht.2⟩


/-- Differentiation under the integral on a compact rectangle. Joint continuity
of the derivative supplies the uniform bound; no such bound is an extra
geometric assumption on a variation. -/
theorem hasDerivAt_integral_on_rectangle {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {H G : ℝ × ℝ → ℝ}
    (hH : ContinuousOn H (Icc (-δ) δ ×ˢ Icc a b))
    (hG : ContinuousOn G (Icc (-δ) δ ×ˢ Icc a b))
    (hder : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => H (r,t)) (G (s,t)) s) :
    HasDerivAt (fun s => ∫ t in a..b, H (s,t)) (∫ t in a..b, G (0,t)) 0 := by
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hHslice : ∀ s ∈ Icc (-δ) δ, ContinuousOn (fun t => H (s,t)) (Icc a b) := by
    intro s hs
    exact hH.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hs, ht⟩)
  have hGslice : ContinuousOn (fun t => G (0,t)) (Icc a b) :=
    hG.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨h0, ht⟩)
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  let μ := volume.restrict (Ioc a b)
  have hmem : ∀ᵐ t ∂μ, t ∈ Icc a b :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => ⟨ht.1.le, ht.2⟩)
  have hint : Integrable (fun t => H (0,t)) μ :=
    ((hHslice 0 h0).intervalIntegrable_of_Icc hab).1
  have hmeas : ∀ᶠ s in nhds 0, AEStronglyMeasurable (fun t => H (s,t)) μ := by
    filter_upwards [Ioo_mem_nhds (show -δ < (0 : ℝ) by linarith) hδ] with s hs
    exact ((hHslice s ⟨hs.1.le, hs.2.le⟩).intervalIntegrable_of_Icc hab).1.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun t => G (0,t)) μ :=
    (hGslice.intervalIntegrable_of_Icc hab).1.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ Ioo (-δ) δ, ‖G (s,t)‖ ≤ K := by
    filter_upwards [hmem] with t ht s hs
    exact hK (s,t) ⟨⟨hs.1.le, hs.2.le⟩, ht⟩
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ Ioo (-δ) δ,
      HasDerivAt (fun r => H (r,t)) (G (s,t)) s := by
    filter_upwards [hmem] with t ht s hs
    exact hder s hs t ht
  have hKi : Integrable (fun _ : ℝ => K) μ :=
    (intervalIntegrable_const (a := a) (b := b) (μ := volume)).1
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s t => H (s,t)) (F' := fun s t => G (s,t))
    (Ioo_mem_nhds (show -δ < (0 : ℝ) by linarith) hδ)
    hmeas hint hgm hbound hKi hdiff).2
  simpa only [intervalIntegral.integral_of_le hab] using hd

/-- Scalar integration by parts for a differentiated metric pairing.
The geometric product rule is an explicit hypothesis of this analytic helper;
it remains to be proved for the fields of an arbitrary smooth variation. -/
theorem integral_pairing_by_parts {a b : ℝ} (hab : a ≤ b)
    {B A I : ℝ → ℝ} (hB : ContinuousOn B (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt B (A t + I t) t)
    (hA : IntervalIntegrable A volume a b) (hI : IntervalIntegrable I volume a b) :
    (∫ t in a..b, A t) = B b - B a - ∫ t in a..b, I t := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hB hder (hA.add hI)
  rw [intervalIntegral.integral_add hA hI] at hFTC
  linarith

/-- The two analytic steps in the energy and positive-speed length arguments. -/
theorem firstVariation_of_pairing_derivative {a b : ℝ} (hab : a ≤ b)
    {E B A I : ℝ → ℝ} (hE : HasDerivAt E (∫ t in a..b, A t) 0)
    (hB : ContinuousOn B (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt B (A t + I t) t)
    (hA : IntervalIntegrable A volume a b) (hI : IntervalIntegrable I volume a b) :
    HasDerivAt E (B b - B a - ∫ t in a..b, I t) 0 := by
  rwa [integral_pairing_by_parts hab hB hder hA hI] at hE


/-- The algebra of the moving endpoints and all internal jumps. -/
theorem sum_segment_boundary {k : ℕ} (node : Fin (k+2) → ℝ)
    (B : Fin (k+1) → ℝ → ℝ) :
    (∑ i : Fin (k+1), (B i (node i.succ) - B i (node i.castSucc))) =
      B (Fin.last k) (node (Fin.last (k+1))) - B 0 (node 0) +
      (∑ j : Fin k, (B j.castSucc (node j.succ.castSucc) - B j.succ (node j.succ.castSucc))) := by
  rw [Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun i : Fin (k+1) => B i (node i.succ))]
  rw [Fin.sum_univ_succ (fun i : Fin (k+1) => B i (node i.castSucc))]
  simp only [Fin.succ_castSucc, Fin.castSucc_zero, Fin.succ_last]
  rw [Finset.sum_sub_distrib]
  ring

open P202.FirstVariationData P202.ConnectionData

/-- The corner term is literally pairing with the difference of velocities,
not an independently chosen number at a join. -/
theorem energy_boundary_sum
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) :
    (∑ i : Fin (k+1),
      (variationPairing g F (segmentVelocity S F (node i.castSucc) (node i.succ)) (node i.succ) -
      variationPairing g F (segmentVelocity S F (node i.castSucc) (node i.succ)) (node i.castSucc))) =
      variationPairing g F
        (segmentVelocity S F (node (Fin.last k).castSucc) (node (Fin.last k).succ))
        (node (Fin.last (k+1))) -
      variationPairing g F (segmentVelocity S F (node 0) (node (Fin.succ 0))) (node 0) +
      (∑ j : Fin k, energyCorner g F node j) := by
  rw [sum_segment_boundary]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [energyCorner, variationPairing]
  exact ((pairing g (F (0, node j.succ.castSucc))
    (variationField S F (node j.succ.castSucc))).map_sub
      (M := SmoothManifolds.TangentData.TangentSpace S (F (0, node j.succ.castSucc)))
      (M₂ := ℝ) _ _).symm

/-- The same endpoint algebra for normalized velocities. -/
theorem length_boundary_sum
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (F : ℝ × ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) :
    (∑ i : Fin (k+1),
      (variationPairing g F (unitVelocity g F (node i.castSucc) (node i.succ)) (node i.succ) -
      variationPairing g F (unitVelocity g F (node i.castSucc) (node i.succ)) (node i.castSucc))) =
      variationPairing g F
        (unitVelocity g F (node (Fin.last k).castSucc) (node (Fin.last k).succ))
        (node (Fin.last (k+1))) -
      variationPairing g F (unitVelocity g F (node 0) (node (Fin.succ 0))) (node 0) +
      (∑ j : Fin k, lengthCorner g F node j) := by
  rw [sum_segment_boundary]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [lengthCorner, variationPairing]
  exact ((pairing g (F (0, node j.succ.castSucc))
    (variationField S F (node j.succ.castSucc))).map_sub
      (M := SmoothManifolds.TangentData.TangentSpace S (F (0, node j.succ.castSucc)))
      (M₂ := ℝ) _ _).symm

/-- Both variation formulas on a singleton interval, with no speed condition. -/
theorem first_variations_degenerate
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M) (a : ℝ) :
    HasDerivAt (variedEnergy g F a a) (energyFirstVariation g C F a a) 0 ∧
      HasDerivAt (variedLength g F a a) (lengthFirstVariation g C F a a) 0 := by
  have hE : variedEnergy g F a a = fun _ => 0 := by funext s; simp [variedEnergy]
  have hL : variedLength g F a a = fun _ => 0 := by funext s; simp [variedLength]
  simp only [hE, hL, energyFirstVariation, lengthFirstVariation,
    intervalIntegral.integral_same, sub_self]
  exact ⟨hasDerivAt_const _ _, hasDerivAt_const _ _⟩


open scoped Topology

/-- A coordinate-smooth variation has C¹ slices up to both endpoints. -/
theorem variation_coordinateC1On_slice
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b s : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hs : s ∈ Ioo (-ε) ε) :
    CoordinateC1On S (fun r => F (s,r)) (Icc a b) := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hF.2 (s,t) ⟨hs, ht⟩
  refine ⟨e, he, hp, (fun r => x (s,r)), ?_, hxt, ?_⟩
  · exact (hx.comp t (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  · have hi : Tendsto (fun r : ℝ => (s,r)) (𝓝[Icc a b] t)
        (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (s,t)) :=
      ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
        (fun _ hr => ⟨hs, hr⟩)
    exact heq.comp_tendsto hi

/-- The corresponding slice is continuous on the whole closed segment. -/
theorem variation_continuousOn_slice
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b s : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hs : s ∈ Ioo (-ε) ε) :
    ContinuousOn (fun r => F (s,r)) (Icc a b) :=
  hF.1.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hr => ⟨hs, hr⟩)


/-- The chosen one-sided segment velocity satisfies its actual coordinate
within-derivative relation, rather than carrying a derivative certificate. -/
theorem segmentVelocity_spec
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (ht : t ∈ Icc a b) :
    P202.CurveConnectionData.HasVelocityWithinAt S (fun r => F (0,r)) (Icc a b) t
      (segmentVelocity S F a b t) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hex : ∃ v, P202.CurveConnectionData.HasVelocityWithinAt S
      (fun r => F (0,r)) (Icc a b) t v :=
    PiecewiseCurves.CoordinateC1On.exists_withinVelocity
      (variation_coordinateC1On_slice hF h0) (variation_continuousOn_slice hF h0) ht
  classical
  simp only [segmentVelocity, dite_eq_left hex]
  exact Classical.choose_spec hex

/-- In every genuine tangent chart, the endpoint velocity has the expected
one-sided coordinate derivative. -/
theorem segmentVelocity_coordinates
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (ht : t ∈ Icc a b) (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hp : F (0,t) ∈ e.source) :
    (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (segmentVelocity S F a b t) = derivWithin (fun r => (e (F (0,r))).val) (Icc a b) t :=
  ((PiecewiseCurves.hasVelocityWithinAt_coordinates
    (segmentVelocity_spec hF hε ht) ht e he hp).derivWithin (uniqueDiffOn_Icc hab t ht)).symm


/-- A smooth slice represented in the canonical compact-curve interface. -/
def variationSlice
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b s : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hs : s ∈ Ioo (-ε) ε) (hab : a ≤ b) :
    PiecewiseC1Curve S a b where
  ordered := hab
  toFun := fun t => F (s,t)
  continuousOn := variation_continuousOn_slice hF hs
  pieces := 1
  node := ![a,b]
  monotone_node := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  first_node := rfl
  last_node := rfl
  regular := by
    intro i
    fin_cases i
    exact variation_coordinateC1On_slice hF hs

/-- The variation functionals agree with the original energy and length. -/
theorem varied_functionals_eq
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b s : ℝ}
    (g : RiemannianMetric S) (hF : SmoothVariationOn S F ε a b)
    (hs : s ∈ Ioo (-ε) ε) (hab : a ≤ b) :
    variedEnergy g F a b s = energy g (variationSlice hF hs hab) ∧
      variedLength g F a b s = length g (variationSlice hF hs hab) := ⟨rfl,rfl⟩

open private sum_integrals from MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthLaws

/-- Finite subdivision of both functionals for the actual variation map. -/
theorem varied_functionals_subdivision
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) {F : ℝ × ℝ → M} {ε s : ℝ}
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : Monotone node)
    (hF : ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ))
    (hs : s ∈ Ioo (-ε) ε) :
    variedEnergy g F (node 0) (node (Fin.last (k+1))) s =
      ∑ i : Fin (k+1), variedEnergy g F (node i.castSucc) (node i.succ) s ∧
    variedLength g F (node 0) (node (Fin.last (k+1))) s =
      ∑ i : Fin (k+1), variedLength g F (node i.castSucc) (node i.succ) s := by
  have hE : ∀ i : Fin (k+1), IntervalIntegrable
      (fun t => speed g (fun r => F (s,r)) t^2) volume (node i.castSucc) (node i.succ) := by
    intro i
    exact PiecewiseCurves.squared_speed_integrable g
      (variationSlice (hF i) hs (hnode (Fin.castSucc_le_succ i)))
  have hL : ∀ i : Fin (k+1), IntervalIntegrable
      (speed g (fun r => F (s,r))) volume (node i.castSucc) (node i.succ) := by
    intro i
    exact PiecewiseCurves.speed_integrable g
      (variationSlice (hF i) hs (hnode (Fin.castSucc_le_succ i)))
  constructor
  · dsimp only [variedEnergy]
    rw [← sum_integrals node hE, Finset.mul_sum]
  · exact (sum_integrals node hL).symm

/-- Once the smooth energy formula is established, the piecewise formula follows
by finite differentiation, subdivision, and the proved velocity-jump algebra. -/
theorem piecewise_energy_from_smooth_formula
    (h : P202Specs.Geometry.FirstVariation.first_variation_energyType.{u}) :
    P202Specs.Geometry.FirstVariation.piecewise_energyType.{u} := by
  intro n kind M inst S g C hLC F ε hε k node hnode hF
  have hd : HasDerivAt
      (fun s => ∑ i : Fin (k+1), variedEnergy g F (node i.castSucc) (node i.succ) s)
      (∑ i : Fin (k+1), energyFirstVariation g C F (node i.castSucc) (node i.succ)) 0 :=
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h g C hLC F ε _ _ hε
          (hnode.monotone (Fin.castSucc_le_succ i)) (hF i)))
  have heq : (fun s => variedEnergy g F (node 0) (node (Fin.last (k+1))) s) =ᶠ[𝓝 0]
      (fun s => ∑ i : Fin (k+1), variedEnergy g F (node i.castSucc) (node i.succ) s) := by
    filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    exact (varied_functionals_subdivision g node hnode.monotone hF hs).1
  have hd' := hd.congr_of_eventuallyEq heq
  have hsum := energy_boundary_sum g F node
  simp only [Finset.sum_sub_distrib] at hsum
  simp only [energyFirstVariation, Finset.sum_sub_distrib] at hd'
  rw [hsum] at hd'
  exact hd'

/-- The analogous reduction for regular piecewise length variations. -/
theorem piecewise_length_from_smooth_formula
    (h : P202Specs.Geometry.FirstVariation.first_variation_lengthType.{u}) :
    P202Specs.Geometry.FirstVariation.piecewise_lengthType.{u} := by
  intro n kind M inst S g C hLC F ε hε k node hnode hF hpos
  have hd : HasDerivAt
      (fun s => ∑ i : Fin (k+1), variedLength g F (node i.castSucc) (node i.succ) s)
      (∑ i : Fin (k+1), lengthFirstVariation g C F (node i.castSucc) (node i.succ)) 0 :=
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h g C hLC F ε _ _ hε
          (hnode.monotone (Fin.castSucc_le_succ i)) (hF i) (hpos i)))
  have heq : (fun s => variedLength g F (node 0) (node (Fin.last (k+1))) s) =ᶠ[𝓝 0]
      (fun s => ∑ i : Fin (k+1), variedLength g F (node i.castSucc) (node i.succ) s) := by
    filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    exact (varied_functionals_subdivision g node hnode.monotone hF hs).2
  have hd' := hd.congr_of_eventuallyEq heq
  have hsum := length_boundary_sum g F node
  simp only [Finset.sum_sub_distrib] at hsum
  simp only [lengthFirstVariation, Finset.sum_sub_distrib] at hd'
  rw [hsum] at hd'
  exact hd'


/-- The variation field is an actual derivative in the s direction, even at
an endpoint of the t interval. Only the s parameter must be two-sided. -/
theorem variationField_spec
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (ht : t ∈ Icc a b) :
    HasVelocityAt S (fun s => F (s,t)) 0 (variationField S F t) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hi : Tendsto (fun s : ℝ => (s,t)) (𝓝 0) (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
    exact ⟨hs, ht⟩
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hF.2 (0,t) ⟨h0, ht⟩
  have hcont : ContinuousAt (fun s => F (s,t)) 0 := Filter.Tendsto.comp (hF.1 (0,t) ⟨h0,ht⟩) hi
  let L := (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
  have hx' : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => x (s,t)) 0 :=
    hx.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hv : HasVelocityAt S (fun s => F (s,t)) 0
      (L.symm (deriv (fun s : ℝ => x (s,t)) 0)) := by
    refine ⟨hcont, e, he, hp, ?_⟩
    change HasDerivAt _ (L (L.symm _)) 0
    rw [LinearEquiv.apply_symm_apply]
    exact (hx'.differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq (heq.comp_tendsto hi)
  change HasVelocityAt S (fun s => F (s,t)) 0 (velocity S (fun s => F (s,t)) 0)
  rw [PiecewiseCurves.velocity_eq hv]
  exact hv

/-- The coordinate description of the variation field in any chart. -/
theorem variationField_coordinates
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (ht : t ∈ Icc a b)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val) (hp : F (0,t) ∈ e.source) :
    (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp (variationField S F t) =
      deriv (fun s => (e (F (s,t))).val) 0 :=
  (PiecewiseCurves.hasVelocityAt_coordinates (variationField_spec hF hε ht) e he hp).deriv.symm

/-- On the open segment, the one-sided velocity equals the original ambient
velocity used by the energy and length integrands. -/
theorem segmentVelocity_eq_velocity
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (ht : t ∈ Ioo a b) :
    segmentVelocity S F a b t = velocity S (fun r => F (0,r)) t := by
  have hv := segmentVelocity_spec hF hε (Ioo_subset_Icc_self ht)
  have hv' : HasVelocityAt S (fun r => F (0,r)) t (segmentVelocity S F a b t) := by
    obtain ⟨hc, e, he, hp, hd⟩ := hv
    exact ⟨hc.continuousAt (Icc_mem_nhds ht.1 ht.2), e, he, hp,
      hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  exact (PiecewiseCurves.velocity_eq hv').symm

open SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FrameData P202.CurveConnectionData

/-- Coefficients in the canonical tangent frame are the original tangent
coordinates. This bridges the curve-field regularity interface to the metric
bundle realization. -/
theorem tangentFrame_coordinates
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (e : ModelChart n kind M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source)
    (v : TangentSpace S p) :
    let i : TangentIndex S := ⟨e, he⟩
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
    (b.basis ⟨p, (tangentRealization S).baseSet i ▸ hp⟩).equivFun v =
      (tangentStructure S).fiberCoordinates.equiv e he p hp v := by
  dsimp only
  rw [LeviCivita.trivializationFrame_coordinates,
    SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply]
  exact (tangentRealization S).coordinates ⟨e, he⟩ p hp v

/-- The one-sided velocity field of a smooth segment is C¹ up to its
endpoints, in the actual tangent bundle used by the connection. -/
theorem segmentVelocity_c1
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b) :
    C1FieldOn (B := tangentBundle S) (fun r => F (0,r))
      (segmentVelocity S F a b) (Icc a b) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hF.2 (0,t) ⟨h0, ht⟩
  let i : TangentIndex S := ⟨e, he⟩
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  have hi : F (0,t) ∈ (tangentBundle S).baseSet i :=
    (tangentRealization S).baseSet i ▸ hp
  have hU : IsOpen ((tangentBundle S).baseSet i) :=
    (tangentBundle S).trivialization_baseSet i ▸
      ((tangentBundle S).trivialization i).open_baseSet
  have hx1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => x (0,r)) t :=
    hx.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have hxc1 : ContDiffAt ℝ 1 (deriv (fun r : ℝ => x (0,r))) t :=
    hx1.derivWithin (by simp)
  have hi' : Tendsto (fun r : ℝ => (0,r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨h0, hr⟩)
  have heq' := heq.comp_tendsto hi'
  have hx1c : ContDiffAt ℝ 1 (fun r : ℝ => x (0,r)) t := hx1.of_le (by simp)
  have hcoeff : coefficientsAlong b' (fun r => F (0,r)) (segmentVelocity S F a b)
      =ᶠ[𝓝[Icc a b] t] deriv (fun r : ℝ => x (0,r)) := by
    filter_upwards [heq'.derivWithin,
      (hx1c.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
      (variation_continuousOn_slice hF h0 t ht).eventually (e.open_source.mem_nhds hp),
      self_mem_nhdsWithin] with r hr hxr hpr hrJ
    have hir : F (0,r) ∈ (tangentBundle S).baseSet i :=
      (tangentRealization S).baseSet i ▸ hpr
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hir]
    rw [tangentFrame_coordinates e he (F (0,r)) hpr]
    rw [segmentVelocity_coordinates hF hε hab hrJ e he hpr]
    change derivWithin (fun r => (e (F (0,r))).val) (Icc a b) r =
      derivWithin (fun r => x (0,r)) (Icc a b) r at hr
    rw [hr]
    exact (hxr.differentiableAt (by simp)).derivWithin (uniqueDiffOn_Icc hab r hrJ)
  exact ⟨_, hU, b', hi, _, hxc1, hcoeff.self_of_nhdsWithin ht, hcoeff⟩

/-- The variation field is C¹ along the closed base segment. In particular
its values at endpoints are the limits of its values in the segment. -/
theorem variationField_c1
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) :
    C1FieldOn (B := tangentBundle S) (fun r => F (0,r))
      (variationField S F) (Icc a b) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hF.2 (0,t) ⟨h0, ht⟩
  let i : TangentIndex S := ⟨e, he⟩
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  have hi : F (0,t) ∈ (tangentBundle S).baseSet i :=
    (tangentRealization S).baseSet i ▸ hp
  have hU : IsOpen ((tangentBundle S).baseSet i) :=
    (tangentBundle S).trivialization_baseSet i ▸
      ((tangentBundle S).trivialization i).open_baseSet
  let v : ℝ → Euclidean n := fun r => fderiv ℝ x (0,r) (1,0)
  have hv : ContDiffAt ℝ 1 v t :=
    ((hx.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).comp t
      (contDiffAt_const.prodMk contDiffAt_id)
  have hi' : Tendsto (fun r : ℝ => (0,r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨h0, hr⟩)
  have heqNear : ∀ᶠ r in 𝓝[Icc a b] t,
      (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,r)] x :=
    hi'.eventually (eventually_eventually_nhdsWithin.mpr heq)
  have hxc : ContDiffAt ℝ 1 x (0,t) := hx.of_le (by simp)
  have hxNear : ∀ᶠ r in 𝓝[Icc a b] t, ContDiffAt ℝ 1 x (0,r) :=
    hi'.eventually ((hxc.eventually (by simp)).filter_mono nhdsWithin_le_nhds)
  have hcoeff : coefficientsAlong b' (fun r => F (0,r)) (variationField S F)
      =ᶠ[𝓝[Icc a b] t] v := by
    filter_upwards [heqNear, hxNear,
      (variation_continuousOn_slice hF h0 t ht).eventually (e.open_source.mem_nhds hp),
      self_mem_nhdsWithin] with r hr hxr hpr hrJ
    have hsr : Tendsto (fun s : ℝ => (s,r)) (𝓝 0)
        (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,r)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
      filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
      exact ⟨hs, hrJ⟩
    have hd : HasDerivAt (fun s : ℝ => (e (F (s,r))).val) (v r) 0 := by
      apply ((hxr.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
        ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 r))).congr_of_eventuallyEq
      exact hr.comp_tendsto hsr
    have hir : F (0,r) ∈ (tangentBundle S).baseSet i :=
      (tangentRealization S).baseSet i ▸ hpr
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hir]
    rw [tangentFrame_coordinates e he (F (0,r)) hpr]
    rw [variationField_coordinates hF hε hrJ e he hpr]
    exact hd.deriv
  exact ⟨_, hU, b', hi, v, hv, hcoeff.self_of_nhdsWithin ht, hcoeff⟩

theorem length_sq_le_energy :
    P202Specs.Geometry.FirstVariation.length_sq_le_energyType.{u} := by
  intro n kind M inst S g a b c
  have h := integral_sq_le c.ordered
    (PiecewiseCurves.speed_integrable g c) (PiecewiseCurves.squared_speed_integrable g c)
  dsimp only [length, energy]
  nlinarith

theorem constant_speed_equality :
    P202Specs.Geometry.FirstVariation.constant_speed_equalityType.{u} := by
  intro n kind M inst S g a b c v h
  have heq := integral_sq_eq_of_ae_const c.ordered h
  dsimp only [length, energy]
  nlinarith

theorem equality_iff_constant_speed :
    P202Specs.Geometry.FirstVariation.equality_iff_constant_speedType.{u} := by
  intro n kind M inst S g a b c hab hc
  dsimp only [length, energy]
  have hr : 2 * (b-a) * ((1/2 : ℝ) * ∫ t in a..b, speed g c t^2) =
      (b-a) * ∫ t in a..b, speed g c t^2 := by ring
  rw [hr]
  exact integral_sq_eq_iff_constant hab hc

theorem degenerate :
    P202Specs.Geometry.FirstVariation.degenerateType.{u} := by
  intro n kind M inst S g a c
  simp [length, energy]

end P202.Geometry.FirstVariation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem metricMatrix_swap (g : RiemannianMetric S) (c : TangentIndex S)
    (i j : Fin n) :
    (fun q => metricMatrix g c q i j) = (fun q => metricMatrix g c q j i) := by
  funext q
  exact g.symmetric q _ _

theorem christoffel_symm (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : TangentIndex S) (p : (tangentBundle S).baseSet c) (k i j : Fin n) :
    christoffel C c p k i j = christoffel C c p k j i := by
  classical
  rw [P202.Geometry.LeviCivita.christoffel_formula g C hC c p k i j,
    P202.Geometry.LeviCivita.christoffel_formula g C hC c p k j i,
    metricMatrix_swap g c i j]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem connectionForm_expansion (C : Connection (tangentBundle S))
    (c : TangentIndex S) (p : (tangentBundle S).baseSet c)
    (V : TangentSpace S p.val) (k j : Fin n) :
    connectionForm C (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) c) p k j V =
        ∑ i : Fin n, ((tangentBundle S).fiberCoordinates c p.val p.property V) i *
          christoffel C c p k i j := by
  classical
  have h := congrArg
    (connectionForm C (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) c) p k j)
    (P202.Geometry.LeviCivita.coordinate_expansion c p.val p.property V)
  simpa only [map_sum, map_smul, smul_eq_mul, christoffel] using h.symm

theorem connectionMatrix_mulVec_symm (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : TangentIndex S) (p : (tangentBundle S).baseSet c)
    (V W : TangentSpace S p.val) :
    (connectionMatrix C (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) c) p V).mulVec
        ((tangentBundle S).fiberCoordinates c p.val p.property W) =
    (connectionMatrix C (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) c) p W).mulVec
        ((tangentBundle S).fiberCoordinates c p.val p.property V) := by
  classical
  funext k
  simp only [Matrix.mulVec, dotProduct, connectionMatrix,
    connectionForm_expansion C c p, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [christoffel_symm g C hC c p k j i]
  ring

end P202.Geometry.FirstVariation


set_option autoImplicit false
set_option maxHeartbeats 800000
namespace P202.Geometry.FirstVariation
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixed_partial_eq {x : ℝ × ℝ → E} {s t : ℝ}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x (s,t)) :
    deriv (fun r : ℝ => fderiv ℝ x (r,t) (0,1)) s =
      deriv (fun r : ℝ => fderiv ℝ x (s,r) (1,0)) t := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ x) (s,t) :=
    (hx.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hs : HasDerivAt (fun r : ℝ => fderiv ℝ x (r,t))
      (fderiv ℝ (fderiv ℝ x) (s,t) (1,0)) s :=
    hfd.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  have ht : HasDerivAt (fun r : ℝ => fderiv ℝ x (s,r))
      (fderiv ℝ (fderiv ℝ x) (s,t) (0,1)) t :=
    hfd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  have hs' := (hs.clm_apply (hasDerivAt_const s ((0,1) : ℝ × ℝ))).deriv
  have ht' := (ht.clm_apply (hasDerivAt_const t ((1,0) : ℝ × ℝ))).deriv
  simp only [map_zero, add_zero] at hs' ht'
  rw [hs', ht']
  exact (hx.isSymmSndFDerivAt (by simp)).eq (1,0) (0,1)

theorem hasDerivAt_mixed_partial {x : ℝ × ℝ → E} {s t : ℝ}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x (s,t)) :
    HasDerivAt (fun r : ℝ => fderiv ℝ x (r,t) (0,1))
      (deriv (fun r : ℝ => fderiv ℝ x (s,r) (1,0)) t) s := by
  have hT : ContDiffAt ℝ 1 (fun r : ℝ => fderiv ℝ x (r,t) (0,1)) s :=
    ((hx.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).comp s
      (contDiffAt_id.prodMk contDiffAt_const)
  exact (hT.differentiableAt (by simp)).hasDerivAt.congr_deriv (mixed_partial_eq hx)

end P202.Geometry.FirstVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

theorem variationPairing_hasDerivWithinAt
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    {W : (t : ℝ) → TangentSpace S (F (0,t))}
    (hW : C1FieldOn (B := tangentBundle S) (fun r => F (0,r)) W (Icc a b))
    (ht : t ∈ Icc a b) :
    HasDerivWithinAt (variationPairing g F W)
      (pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (W t) + variationPairing g F
          (covariantDerivativeWithin C (fun r => F (0,r)) W (Icc a b)) t) (Icc a b) t := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  exact TorsionAndMetric.metric_curve_product_c1 (tangentBundle S) g C hC ht
    (uniqueDiffOn_Icc hab t ht) (variation_coordinateC1On_slice hF h0)
    (variation_continuousOn_slice hF h0) (variationField_c1 hF hε) hW

theorem variationPairing_continuousOn
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    {W : (t : ℝ) → TangentSpace S (F (0,t))}
    (hW : C1FieldOn (B := tangentBundle S) (fun r => F (0,r)) W (Icc a b)) :
    ContinuousOn (variationPairing g F W) (Icc a b) := by
  intro t ht
  exact (variationPairing_hasDerivWithinAt g C hC hF hε hab hW ht).continuousWithinAt

theorem variationPairing_hasDerivAt
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε)
    {W : (t : ℝ) → TangentSpace S (F (0,t))}
    (hW : C1FieldOn (B := tangentBundle S) (fun r => F (0,r)) W (Icc a b))
    (ht : t ∈ Ioo a b) :
    HasDerivAt (variationPairing g F W)
      (pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (W t) + variationPairing g F
          (covariantDerivativeWithin C (fun r => F (0,r)) W (Icc a b)) t) t :=
  (variationPairing_hasDerivWithinAt g C hC hF hε (ht.1.trans ht.2) hW
    (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u v w

theorem scalar_c1_extension
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hc : CoordinateC1On S c J) (hc' : ContinuousOn c J) (ht : t ∈ J)
    {f : M → ℝ} (hf : VectorSmoothAt S.smoothStructure.val f (c t)) :
    ∃ y : ℝ → ℝ, ContDiffAt ℝ 1 y t ∧ (f ∘ c) =ᶠ[𝓝[J] t] y := by
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hc t ht
  obtain ⟨U, hU, hu, G, hG, heqG⟩ := hf.2 e he hp
  refine ⟨G ∘ x, ?_, ?_⟩
  · have hGc : ContDiffAt ℝ 1 G (x t) := by
      rw [hxt]
      exact (hG.contDiffAt (hU.mem_nhds hu)).of_le (by simp)
    exact hGc.comp t hx
  · filter_upwards [heq, heqG.comp_tendsto (hc' t ht)] with s hs hsG
    simpa only [Function.comp_apply, ← hs] using hsG.symm

theorem metric_pairing_c1_extension
    {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E)
    (g : SmoothManifolds.BundleMetricData.SmoothFiberMetric B)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    {f h : (s : ℝ) → E (c s)}
    (hc : CoordinateC1On S c J) (hc' : ContinuousOn c J) (ht : t ∈ J)
    (hf : C1FieldOn (B := B) c f J) (hh : C1FieldOn (B := B) c h J) :
    ∃ y : ℝ → ℝ, ContDiffAt ℝ 1 y t ∧
      (fun s => g.form (c s) (f s) (h s)) =ᶠ[𝓝[J] t] y := by
  classical
  obtain ⟨U, hU, bf, hpU, vf, hvf, _, hef⟩ := hf t ht
  obtain ⟨V, hV, bh, hpV, vh, hvh, _, heh⟩ := hh t ht
  obtain ⟨ef, hef'⟩ := ConnectionForms.local_frame_representative B bf ⟨c t, hpU⟩
  obtain ⟨eh, heh'⟩ := ConnectionForms.local_frame_representative B bh ⟨c t, hpV⟩
  have hgram : ∀ i j : Fin r, ∃ y : ℝ → ℝ, ContDiffAt ℝ 1 y t ∧
      (fun s => g.form (c s) ((ef i).val (c s)) ((eh j).val (c s))) =ᶠ[𝓝[J] t] y := by
    intro i j
    exact scalar_c1_extension hc hc' ht
      (TorsionAndMetric.metricPairing_smooth B g (ef i) (eh j) (c t))
  choose gram hg hegram using hgram
  refine ⟨fun s => ∑ i : Fin r, ∑ j : Fin r, vf s i * (vh s j * gram i j s), ?_, ?_⟩
  · apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (contDiffAt_pi.mp hvf i).mul ((contDiffAt_pi.mp hvh j).mul (hg i j))
  · have hefNear : ∀ᶠ s in 𝓝[J] t, ∀ i : Fin r,
        (ef i).val (c s) = SmoothManifolds.SectionExtension.totalSection (bf.section_ i) (c s) :=
      Filter.Tendsto.eventually (hc' t ht) (Filter.eventually_all.mpr hef')
    have hehNear : ∀ᶠ s in 𝓝[J] t, ∀ j : Fin r,
        (eh j).val (c s) = SmoothManifolds.SectionExtension.totalSection (bh.section_ j) (c s) :=
      Filter.Tendsto.eventually (hc' t ht) (Filter.eventually_all.mpr heh')
    have hegram' : ∀ᶠ s in 𝓝[J] t, ∀ i j : Fin r,
        g.form (c s) ((ef i).val (c s)) ((eh j).val (c s)) = gram i j s :=
      Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hegram i))
    filter_upwards [hef, heh, hefNear, hehNear, hegram',
      (hc' t ht).eventually (hU.mem_nhds hpU),
      (hc' t ht).eventually (hV.mem_nhds hpV)] with s hfs hhs hefS hehS hgS hsU hsV
    have hfexp : f s = ∑ i : Fin r, vf s i • (ef i).val (c s) := by
      have hb := (bf.basis ⟨c s, hsU⟩).sum_equivFun (f s)
      rw [← hfs, CurveCovariantDerivative.coefficientsAlong_of_mem bf c f s hsU]
      convert hb.symm using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hefS i, SmoothManifolds.SectionExtension.totalSection_of_mem _ _ hsU,
        ← bf.basis_eq]
    have hhexp : h s = ∑ j : Fin r, vh s j • (eh j).val (c s) := by
      have hb := (bh.basis ⟨c s, hsV⟩).sum_equivFun (h s)
      rw [← hhs, CurveCovariantDerivative.coefficientsAlong_of_mem bh c h s hsV]
      convert hb.symm using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hehS j, SmoothManifolds.SectionExtension.totalSection_of_mem _ _ hsV,
        ← bh.basis_eq]
    rw [hfexp, hhexp]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hgS i j]
    ring

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

theorem derivWithin_continuousOn_of_local_c1
    {J : Set ℝ} {f : ℝ → ℝ} (hJ : UniqueDiffOn ℝ J)
    (hf : ∀ t ∈ J, ∃ y : ℝ → ℝ, ContDiffAt ℝ 1 y t ∧ f =ᶠ[𝓝[J] t] y) :
    ContinuousOn (derivWithin f J) J := by
  intro t ht
  obtain ⟨y, hy, heq⟩ := hf t ht
  have hdy : ContDiffAt ℝ 0 (deriv y) t := hy.derivWithin (by norm_num)
  refine hdy.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [heq.derivWithin, (hy.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hys hsJ
  exact hs.trans ((hys.differentiableAt (by simp)).derivWithin (hJ s hsJ))

theorem variationPairing_derivWithin_continuousOn
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    {W : (t : ℝ) → TangentSpace S (F (0,t))}
    (hW : C1FieldOn (B := tangentBundle S) (fun r => F (0,r)) W (Icc a b)) :
    ContinuousOn (derivWithin (variationPairing g F W) (Icc a b)) (Icc a b) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  apply derivWithin_continuousOn_of_local_c1 (uniqueDiffOn_Icc hab)
  intro t ht
  exact metric_pairing_c1_extension (tangentBundle S) g
    (variation_coordinateC1On_slice hF h0) (variation_continuousOn_slice hF h0) ht
    (variationField_c1 hF hε) hW

theorem variationPairing_covariant_continuousOn
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    {W : (t : ℝ) → TangentSpace S (F (0,t))}
    (hW : C1FieldOn (B := tangentBundle S) (fun r => F (0,r)) W (Icc a b))
    (hA : ContinuousOn (fun t => pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (W t)) (Icc a b)) :
    ContinuousOn (variationPairing g F
      (covariantDerivativeWithin C (fun r => F (0,r)) W (Icc a b))) (Icc a b) := by
  have hc := (variationPairing_derivWithin_continuousOn g hF hε hab hW).sub hA
  apply hc.congr
  intro t ht
  have hd := (variationPairing_hasDerivWithinAt g C hC hF hε hab hW ht).derivWithin
    (uniqueDiffOn_Icc hab t ht)
  simp only [Pi.sub_apply]
  linarith

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u v w

theorem c1Field_smul_of_local_c1
    {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} {c : ℝ → M} {J : Set ℝ}
    {f : (s : ℝ) → E (c s)} {k : ℝ → ℝ}
    (hf : C1FieldOn (B := B) c f J)
    (hk : ∀ t ∈ J, ∃ y : ℝ → ℝ, ContDiffAt ℝ 1 y t ∧ k =ᶠ[𝓝[J] t] y) :
    C1FieldOn (B := B) c (fun t => k t • f t) J := by
  intro t ht
  obtain ⟨U, hU, b, hp, v, hv, _, heq⟩ := hf t ht
  obtain ⟨y, hy, heqy⟩ := hk t ht
  have heq' : coefficientsAlong b c (fun t => k t • f t) =ᶠ[𝓝[J] t]
      fun t => y t • v t := by
    filter_upwards [heq, heqy] with s hs hys
    simp only [CurveCovariantDerivative.coefficients_smul, hs, hys]
  exact ⟨U, hU, b, hp, _, hy.smul hv, heq'.self_of_nhdsWithin ht, heq'⟩

theorem unitVelocity_c1
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b,
      0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) :
    C1FieldOn (B := tangentBundle S) (fun r => F (0,r))
      (unitVelocity g F a b) (Icc a b) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hf := segmentVelocity_c1 hF hε hab
  apply c1Field_smul_of_local_c1 hf
  intro t ht
  obtain ⟨y, hy, heq⟩ := metric_pairing_c1_extension (tangentBundle S) g
    (variation_coordinateC1On_slice hF h0) (variation_continuousOn_slice hF h0) ht hf hf
  have hyt : Real.sqrt (y t) ≠ 0 := by
    rw [← heq.self_of_nhdsWithin ht]
    exact ne_of_gt (hpos t ht)
  have hyt' : y t ≠ 0 := by
    intro hz
    exact hyt (by simp [hz])
  refine ⟨fun s => (Real.sqrt (y s))⁻¹, (hy.sqrt hyt').inv hyt, ?_⟩
  filter_upwards [heq] with s hs
  simp only [tangentNorm, pairing, hs]

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
universe u

theorem firstVariation_of_c1_field
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    {W : (t : ℝ) → TangentSpace S (F (0,t))}
    (hW : C1FieldOn (B := tangentBundle S) (fun r => F (0,r)) W (Icc a b))
    (hA : ContinuousOn (fun t => pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (W t)) (Icc a b))
    {E : ℝ → ℝ}
    (hE : HasDerivAt E (∫ t in a..b, pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (W t)) 0) :
    HasDerivAt E (variationPairing g F W b - variationPairing g F W a -
      ∫ t in a..b, variationPairing g F
        (covariantDerivativeWithin C (fun r => F (0,r)) W (Icc a b)) t) 0 := by
  exact firstVariation_of_pairing_derivative hab.le hE
    (variationPairing_continuousOn g C hC hF hε hab hW)
    (fun t ht => variationPairing_hasDerivAt g C hC hF hε hW ht)
    (hA.intervalIntegrable_of_Icc hab.le)
    ((variationPairing_covariant_continuousOn g C hC hF hε hab hW hA).intervalIntegrable_of_Icc hab.le)

end P202.Geometry.FirstVariation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.FirstVariationData P202.CurveConnectionData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b : ℝ}

/-- The intrinsic one-sided velocity on every slice of a variation. -/
noncomputable def sliceVelocity (S : SmoothManifold n kind M) (F : ℝ × ℝ → M)
    (a b : ℝ) (s t : ℝ) : TangentSpace S (F (s,t)) :=
  PiecewiseCurves.withinVelocity S (fun r => F (s,r)) (Icc a b) t

@[simp] theorem sliceVelocity_zero (t : ℝ) :
    sliceVelocity S F a b 0 t = segmentVelocity S F a b t := rfl

/-- A smooth scalar on the manifold pulls back to an actual smooth Euclidean
extension germ along the parameter strip, even at its two closed edges. -/
theorem variation_scalar_extension
    (hF : SmoothVariationOn S F ε a b) {z : ℝ × ℝ}
    (hz : z ∈ Ioo (-ε) ε ×ˢ Icc a b) (f : M → ℝ)
    (hf : VectorSmoothAt S.smoothStructure.val f (F z)) :
    ∃ H : ℝ × ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) H z ∧
      (fun w => f (F w)) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] H := by
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hF.2 z hz
  obtain ⟨U, hU, hpU, g, hg, hrep⟩ := hf.2 e he hp
  refine ⟨fun w => g (x w), ?_, ?_⟩
  · exact (hg.contDiffAt (hU.mem_nhds (by simpa only [hxt] using hpU))).comp z hx
  · filter_upwards [hrep.comp_tendsto (hF.1 z hz), heq] with w hw hwx
    simpa only [Function.comp_def, ← hwx] using hw.symm

/-- Joint tangent coordinates of the slice velocity are the t partial of any
local smooth coordinate representative. -/
theorem sliceVelocity_coordinate_germ
    (hF : SmoothVariationOn S F ε a b) (hab : a < b)
    {z : ℝ × ℝ} (hz : z ∈ Ioo (-ε) ε ×ˢ Icc a b)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hp : F z ∈ e.source) (x : ℝ × ℝ → Euclidean n)
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x z)
    (heq : (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] x) :
    ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z,
      ∃ hw : F w ∈ e.source,
        (tangentStructure S).fiberCoordinates.equiv e he (F w) hw
          (sliceVelocity S F a b w.1 w.2) = fderiv ℝ x w (0,1) := by
  have hxc : ContDiffAt ℝ 1 x z := hx.of_le (by simp)
  have hxNear := (hxc.eventually (by simp)).filter_mono
    (nhdsWithin_le_nhds (s := Ioo (-ε) ε ×ˢ Icc a b))
  have heqNear : ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z,
      (fun u => (e (F u)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] w] x :=
    eventually_eventually_nhdsWithin.mpr heq
  filter_upwards [hxNear, heqNear, self_mem_nhdsWithin,
    (hF.1 z hz).eventually (e.open_source.mem_nhds hp)] with w hxs hweq hwD hw
  refine ⟨hw, ?_⟩
  have hi : Tendsto (fun r : ℝ => (w.1,r)) (𝓝[Icc a b] w.2)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] w) := by
    exact ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin (fun _ hr => ⟨hwD.1, hr⟩)
  have hd : HasDerivWithinAt (fun r => (e (F (w.1,r))).val)
      (fderiv ℝ x w (0,1)) (Icc a b) w.2 := by
    apply ((hxs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.2
      ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2))).hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem (hweq.comp_tendsto hi) hwD.2
  exact (uniqueDiffOn_Icc hab w.2 hwD.2).eq_deriv _
    (PiecewiseCurves.hasVelocityWithinAt_coordinates
      (PiecewiseCurves.withinVelocity_spec (variation_coordinateC1On_slice hF hwD.1)
        (variation_continuousOn_slice hF hwD.1) hwD.2) hwD.2 e he hw) hd


/-- A smooth extension germ of the squared norm of the actual slice velocity. -/
theorem sliceSquaredSpeed_extension
    (g : RiemannianMetric S) (hF : SmoothVariationOn S F ε a b) (hab : a < b)
    {z : ℝ × ℝ} (hz : z ∈ Ioo (-ε) ε ×ˢ Icc a b) :
    ∃ Q : ℝ × ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) Q z ∧
      (fun w => pairing g (F w) (sliceVelocity S F a b w.1 w.2)
        (sliceVelocity S F a b w.1 w.2)) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] Q := by
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hF.2 z hz
  let i : TangentIndex S := ⟨e, he⟩
  let B := tangentBundle S
  let gram : Fin n → Fin n → M → ℝ := fun j k p =>
    g.form p ((B.trivialization i).symm p (Pi.single j 1))
      ((B.trivialization i).symm p (Pi.single k 1))
  have hi : F z ∈ B.baseSet i := (tangentRealization S).baseSet i ▸ hp
  have hgram : ∀ j k : Fin n, ∃ G : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) G z ∧
        (fun w => gram j k (F w)) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] G := by
    intro j k
    exact variation_scalar_extension hF hz (gram j k) (g.smooth i j k (F z) hi)
  choose G hGc hGe using hgram
  let v : ℝ × ℝ → Euclidean n := fun w => fderiv ℝ x w (0,1)
  have hv : ContDiffAt ℝ (⊤ : ℕ∞) v z :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  refine ⟨fun w => ∑ j : Fin n, ∑ k : Fin n, v w j * (v w k * G j k w), ?_, ?_⟩
  · apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.sum
    intro k _
    exact ((contDiffAt_pi.mp hv) j).mul (((contDiffAt_pi.mp hv) k).mul (hGc j k))
  · have hGall : ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z,
        ∀ j k, gram j k (F w) = G j k w := by
      exact Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr (hGe j)
    filter_upwards [sliceVelocity_coordinate_germ hF hab hz e he hp x hx heq, hGall] with w hw hGw
    obtain ⟨hpw, hw⟩ := hw
    have hiw : F w ∈ B.baseSet i := (tangentRealization S).baseSet i ▸ hpw
    have hcoord : B.fiberCoordinates i (F w) hiw (sliceVelocity S F a b w.1 w.2) = v w := by
      rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
        (tangentRealization S).coordinates i (F w) hpw]
      exact hw
    have hbil := SmoothMetrics.bilinear_coordinates (B.fiberCoordinates i (F w) hiw)
      (g.form (F w)) (sliceVelocity S F a b w.1 w.2) (sliceVelocity S F a b w.1 w.2)
    simp only [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply,
      hcoord] at hbil
    change pairing g (F w) (sliceVelocity S F a b w.1 w.2)
      (sliceVelocity S F a b w.1 w.2) =
        ∑ j : Fin n, ∑ k : Fin n, v w j * (v w k * gram j k (F w)) at hbil
    exact hbil.trans (by simp only [hGw])

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open Set Filter
open scoped Topology
/-- Local smooth ambient extensions on a strip with open first coordinate give
joint continuity of the actual partial derivative in that coordinate. -/
theorem scalar_germs_on_strip
    {I J : Set ℝ} (hI : IsOpen I) {H : ℝ × ℝ → ℝ}
    (hH : ∀ z ∈ I ×ˢ J, ∃ y : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) y z ∧ H =ᶠ[𝓝[I ×ˢ J] z] y) :
    ContinuousOn H (I ×ˢ J) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv (fun s => H (s,z.2)) z.1) (I ×ˢ J) ∧
      ∀ z ∈ I ×ˢ J, HasDerivAt (fun s => H (s,z.2))
        (deriv (fun s => H (s,z.2)) z.1) z.1 := by
  have hline (w : ℝ × ℝ) (hw : w ∈ I ×ˢ J) :
      Tendsto (fun s : ℝ => (s,w.2)) (𝓝 w.1) (𝓝[I ×ˢ J] w) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
    filter_upwards [hI.mem_nhds hw.1] with s hs
    exact ⟨hs, hw.2⟩
  have hder_eq {z : ℝ × ℝ} (hz : z ∈ I ×ˢ J) {y : ℝ × ℝ → ℝ}
      (hy : ContDiffAt ℝ (⊤ : ℕ∞) y z) (he : H =ᶠ[𝓝[I ×ˢ J] z] y) :
      HasDerivAt (fun s => H (s,z.2)) (fderiv ℝ y z (1,0)) z.1 := by
    have hd := (hy.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
    exact hd.congr_of_eventuallyEq (he.comp_tendsto (hline z hz))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, he⟩ := hH z hz
    exact hy.continuousAt.continuousWithinAt.congr_of_eventuallyEq he
      (he.self_of_nhdsWithin hz)
  · intro z hz
    obtain ⟨y, hy, he⟩ := hH z hz
    have hc : ContinuousAt (fun w => fderiv ℝ y w (1,0)) z :=
      ((hy.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).continuousAt
    have he' : (fun w : ℝ × ℝ => deriv (fun s => H (s,w.2)) w.1)
        =ᶠ[𝓝[I ×ˢ J] z] (fun w => fderiv ℝ y w (1,0)) := by
      have hnear := eventually_eventually_nhdsWithin.mpr he
      have hy1 : ContDiffAt ℝ 1 y z := hy.of_le (by simp)
      have hynear : ∀ᶠ w in 𝓝[I ×ˢ J] z, ContDiffAt ℝ 1 y w :=
        (hy1.eventually (by simp)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hnear, hynear, self_mem_nhdsWithin] with w hw hyw hwD
      have hdy := (hyw.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1
        ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))
      have hw' : H =ᶠ[𝓝[I ×ˢ J] w] y := hw
      exact (hdy.congr_of_eventuallyEq (hw'.comp_tendsto (hline w hwD))).deriv
    exact hc.continuousWithinAt.congr_of_eventuallyEq he'
      ((hder_eq hz hy he).deriv)
  · intro z hz
    obtain ⟨y, hy, he⟩ := hH z hz
    have hd := hder_eq hz hy he
    rwa [← hd.deriv] at hd


end P202.Geometry.FirstVariation


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleData
  P202.MetricData P202.CurveData P202.FirstVariationData P202.CurveConnectionData
  P202.ConnectionData P202.LeviCivitaData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b t : ℝ}

/-- In a fixed tangent chart, the variation-field coefficients have the
s partial of a local coordinate representative as a within germ. -/
theorem variationField_coefficient_germ
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (ht : t ∈ Icc a b)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hp : F (0,t) ∈ e.source) (x : ℝ × ℝ → Euclidean n)
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x (0,t))
    (heq : (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] x) :
    coefficientsAlong (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) (⟨e, he⟩ : TangentIndex S))
      (fun r => F (0,r)) (variationField S F)
      =ᶠ[𝓝[Icc a b] t] (fun r => fderiv ℝ x (0,r) (1,0)) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  let i : TangentIndex S := ⟨e, he⟩
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  let v : ℝ → Euclidean n := fun r => fderiv ℝ x (0,r) (1,0)
  have hi' : Tendsto (fun r : ℝ => (0,r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨h0, hr⟩)
  have heqNear : ∀ᶠ r in 𝓝[Icc a b] t,
      (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,r)] x :=
    hi'.eventually (eventually_eventually_nhdsWithin.mpr heq)
  have hx1 : ContDiffAt ℝ 1 x (0,t) := hx.of_le (by simp)
  have hxNear : ∀ᶠ r in 𝓝[Icc a b] t, ContDiffAt ℝ 1 x (0,r) :=
    hi'.eventually ((hx1.eventually (by simp)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [heqNear, hxNear,
    (variation_continuousOn_slice hF h0 t ht).eventually (e.open_source.mem_nhds hp),
    self_mem_nhdsWithin] with r hr hxr hpr hrJ
  have hsr : Tendsto (fun s : ℝ => (s,r)) (𝓝 0)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,r)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
    exact ⟨hs, hrJ⟩
  have hd : HasDerivAt (fun s : ℝ => (e (F (s,r))).val) (v r) 0 := by
    apply ((hxr.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 r))).congr_of_eventuallyEq
    exact hr.comp_tendsto hsr
  have hir : F (0,r) ∈ (tangentBundle S).baseSet i :=
    (tangentRealization S).baseSet i ▸ hpr
  rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hir]
  rw [tangentFrame_coordinates e he (F (0,r)) hpr]
  rw [variationField_coordinates hF hε hrJ e he hpr]
  exact hd.deriv

/-- The actual mixed covariant derivatives agree on the full closed base
segment. This uses local coordinate extensions and makes no rank assumption. -/
theorem sliceVelocity_mixed_covariantDerivative
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) (hab : a < b) (ht : t ∈ Icc a b) :
    HasCovariantDerivativeWithinAt C (fun s => F (s,t))
      (fun s => sliceVelocity S F a b s t) (Ioo (-ε) ε) 0
      (covariantDerivativeWithin C (fun r => F (0,r))
        (variationField S F) (Icc a b) t) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hF.2 (0,t) ⟨h0, ht⟩
  let i : TangentIndex S := ⟨e, he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  have hi : F (0,t) ∈ B.baseSet i := (tangentRealization S).baseSet i ▸ hp
  have hU : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  let v : ℝ → Euclidean n := fun r => fderiv ℝ x (0,r) (1,0)
  have hv : ContDiffAt ℝ 1 v t :=
    ((hx.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).comp t
      (contDiffAt_const.prodMk contDiffAt_id)
  have hVcoeff : coefficientsAlong b' (fun r => F (0,r)) (variationField S F)
      =ᶠ[𝓝[Icc a b] t] v :=
    variationField_coefficient_germ hF hε ht e he hp x hx heq
  have hVder : HasDerivWithinAt
      (coefficientsAlong b' (fun r => F (0,r)) (variationField S F))
      (deriv v t) (Icc a b) t :=
    (hv.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem hVcoeff ht
  have hiS : Tendsto (fun s : ℝ => (s,t)) (𝓝[Ioo (-ε) ε] 0)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_id.prodMk continuous_const).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hs => ⟨hs, ht⟩)
  have hTcoeff : coefficientsAlong b' (fun s => F (s,t))
      (fun s => sliceVelocity S F a b s t)
      =ᶠ[𝓝[Ioo (-ε) ε] 0] (fun s => fderiv ℝ x (s,t) (0,1)) := by
    filter_upwards [hiS.eventually
      (sliceVelocity_coordinate_germ hF hab ⟨h0,ht⟩ e he hp x hx heq)] with s hs
    obtain ⟨hps, hcs⟩ := hs
    have his : F (s,t) ∈ B.baseSet i := (tangentRealization S).baseSet i ▸ hps
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ his]
    rw [tangentFrame_coordinates e he (F (s,t)) hps]
    exact hcs
  have hTder : HasDerivWithinAt
      (coefficientsAlong b' (fun s => F (s,t)) (fun s => sliceVelocity S F a b s t))
      (deriv v t) (Ioo (-ε) ε) 0 :=
    (hasDerivAt_mixed_partial hx).hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem hTcoeff h0
  have hVs : HasVelocityWithinAt S (fun s => F (s,t)) (Ioo (-ε) ε) 0
      (variationField S F t) := by
    obtain ⟨hc, d, hd, hpd, hder⟩ := variationField_spec hF hε ht
    exact ⟨hc.continuousWithinAt, d, hd, hpd, hder.hasDerivWithinAt⟩
  have hTt := segmentVelocity_spec hF hε ht
  have hDt : covariantDerivativeWithin C (fun r => F (0,r))
      (variationField S F) (Icc a b) t =
      frameDerivative C b' (fun r => F (0,r)) (variationField S F) t hi
        (segmentVelocity S F a b t) (deriv v t) :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C ht (uniqueDiffOn_Icc hab t ht)
      ⟨_, hTt, _, hU, b', hi, _, hVder, rfl⟩
  refine ⟨_, hVs, _, hU, b', hi, _, hTder, ?_⟩
  rw [hDt]
  unfold frameDerivative
  rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hi,
    CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hi]
  rw [LeviCivita.trivializationFrame_coordinates,
    LeviCivita.trivializationFrame_coordinates]
  change (b'.basis ⟨F (0,t), hi⟩).equivFun.symm
      (deriv v t + (connectionMatrix C b' ⟨F (0,t), hi⟩
        (segmentVelocity S F a b t)).mulVec
        (B.fiberCoordinates i (F (0,t)) hi (variationField S F t))) =
    (b'.basis ⟨F (0,t), hi⟩).equivFun.symm
      (deriv v t + (connectionMatrix C b' ⟨F (0,t), hi⟩
        (variationField S F t)).mulVec
        (B.fiberCoordinates i (F (0,t)) hi (segmentVelocity S F a b t)))
  rw [connectionMatrix_mulVec_symm g C hC i ⟨F (0,t),hi⟩]

/-- The energy-density derivative at the base is the actual covariant
pairing, including the endpoints in the integration parameter. -/
theorem sliceEnergyDensity_hasDerivAt
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) (hab : a < b) (ht : t ∈ Icc a b) :
    HasDerivAt (fun s => (1/2 : ℝ) *
      pairing g (F (s,t)) (sliceVelocity S F a b s t) (sliceVelocity S F a b s t))
      (pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (segmentVelocity S F a b t)) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hm := sliceVelocity_mixed_covariantDerivative g C hC hF hε hab ht
  have hd := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2
    h0 (uniqueDiffWithinAt_Ioo h0) hm hm
  have hd' := (hd.hasDerivAt (Ioo_mem_nhds h0.1 h0.2)).const_mul (1/2 : ℝ)
  convert hd' using 1
  · rfl
  · simp only [sliceVelocity_zero, pairing]
    rw [g.symmetric (F (0,t))]
    ring

end P202.Geometry.FirstVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b : ℝ}

noncomputable def squaredVariationSpeed (g : RiemannianMetric S)
    (F : ℝ × ℝ → M) (a b : ℝ) (z : ℝ × ℝ) : ℝ :=
  pairing g (F z) (sliceVelocity S F a b z.1 z.2) (sliceVelocity S F a b z.1 z.2)

theorem squaredVariationSpeed_calculus
    (g : RiemannianMetric S) (hF : SmoothVariationOn S F ε a b) (hab : a < b) :
    ContinuousOn (squaredVariationSpeed g F a b) (Ioo (-ε) ε ×ˢ Icc a b) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv
        (fun s => squaredVariationSpeed g F a b (s,z.2)) z.1) (Ioo (-ε) ε ×ˢ Icc a b) ∧
      ∀ z ∈ Ioo (-ε) ε ×ˢ Icc a b,
        HasDerivAt (fun s => squaredVariationSpeed g F a b (s,z.2))
          (deriv (fun s => squaredVariationSpeed g F a b (s,z.2)) z.1) z.1 :=
  scalar_germs_on_strip isOpen_Ioo (fun z hz => sliceSquaredSpeed_extension g hF hab hz)

theorem squaredVariationSpeed_derivative
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsMetricCompatible g C) (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc a b)
    (hmix : HasCovariantDerivativeWithinAt C (fun s => F (s,t))
      (fun s => sliceVelocity S F a b s t) (Ioo (-ε) ε) 0
      (covariantDerivativeWithin C (fun r => F (0,r))
        (variationField S F) (Icc a b) t)) :
    HasDerivAt (fun s => squaredVariationSpeed g F a b (s,t))
      (2 * pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r))
          (variationField S F) (Icc a b) t) (segmentVelocity S F a b t)) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hd := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC h0
    (uniqueDiffWithinAt_Ioo h0) hmix hmix
  have hsym := g.symmetric (F (0,t)) (segmentVelocity S F a b t)
    (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
  have hd' := hd.hasDerivAt (isOpen_Ioo.mem_nhds h0)
  change HasDerivAt (fun s => squaredVariationSpeed g F a b (s,t)) _ 0 at hd'
  convert hd' using 1
  dsimp only [pairing] at hsym ⊢
  simp only [sliceVelocity_zero, hsym]
  ring

/-- Continuous density and compactness justify differentiating the squared
speed integral. The only geometric input here is the explicit mixed derivative
certificate for the actual slice fields. -/
theorem energy_density_calculus
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsMetricCompatible g C) (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) (hab : a < b)
    (hmix : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun s => F (s,t))
      (fun s => sliceVelocity S F a b s t) (Ioo (-ε) ε) 0
      (covariantDerivativeWithin C (fun r => F (0,r))
        (variationField S F) (Icc a b) t)) :
    let A : ℝ → ℝ := fun t => pairing g (F (0,t))
      (covariantDerivativeWithin C (fun r => F (0,r))
        (variationField S F) (Icc a b) t) (segmentVelocity S F a b t)
    ContinuousOn A (Icc a b) ∧
      HasDerivAt (fun s => (1/2 : ℝ) * ∫ t in a..b,
        squaredVariationSpeed g F a b (s,t)) (∫ t in a..b, A t) 0 := by
  dsimp only
  let H := squaredVariationSpeed g F a b
  let G : ℝ × ℝ → ℝ := fun z => deriv (fun s => H (s,z.2)) z.1
  let A : ℝ → ℝ := fun t => pairing g (F (0,t))
    (covariantDerivativeWithin C (fun r => F (0,r))
      (variationField S F) (Icc a b) t) (segmentVelocity S F a b t)
  obtain ⟨hH, hG, hder⟩ := squaredVariationSpeed_calculus g hF hab
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hG0 (t : ℝ) (ht : t ∈ Icc a b) : G (0,t) = 2 * A t :=
    (squaredVariationSpeed_derivative g C hC hε ht (hmix t ht)).deriv
  have hAc : ContinuousOn A (Icc a b) := by
    have hc := (hG.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨h0, ht⟩)).const_mul (1/2 : ℝ)
    apply hc.congr
    intro t ht
    change A t = (1/2 : ℝ) * G (0,t)
    rw [hG0 t ht]
    ring
  refine ⟨hAc, ?_⟩
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsub : Icc (-δ) δ ×ˢ Icc a b ⊆ Ioo (-ε) ε ×ˢ Icc a b := by
    intro z hz
    exact ⟨⟨by dsimp [δ] at hz; linarith [hz.1.1],
      by dsimp [δ] at hz; linarith [hz.1.2]⟩, hz.2⟩
  have hd := hasDerivAt_integral_on_rectangle hab.le hδ (hH.mono hsub) (hG.mono hsub)
    (fun s hs t ht => hder (s,t) (hsub ⟨⟨hs.1.le, hs.2.le⟩,ht⟩))
  have heq : (∫ t in a..b, G (0,t)) = 2 * ∫ t in a..b, A t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro t ht
    exact hG0 t (Ioo_subset_Icc_self ht)
  have hd' := hd.const_mul (1/2 : ℝ)
  change HasDerivAt (fun s => (1/2 : ℝ) * ∫ t in a..b, H (s,t))
    ((1/2 : ℝ) * ∫ t in a..b, G (0,t)) 0 at hd'
  rw [heq] at hd'
  convert hd' using 1 <;> ring

end P202.Geometry.FirstVariation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b : ℝ}

theorem sliceVelocity_eq_velocity
    (hF : SmoothVariationOn S F ε a b) {s t : ℝ}
    (hs : s ∈ Ioo (-ε) ε) (ht : t ∈ Ioo a b) :
    sliceVelocity S F a b s t = velocity S (fun r => F (s,r)) t := by
  have hv := PiecewiseCurves.withinVelocity_spec (variation_coordinateC1On_slice hF hs)
    (variation_continuousOn_slice hF hs) (Ioo_subset_Icc_self ht)
  have hv' : HasVelocityAt S (fun r => F (s,r)) t (sliceVelocity S F a b s t) := by
    obtain ⟨hc, e, he, hp, hd⟩ := hv
    exact ⟨hc.continuousAt (Icc_mem_nhds ht.1 ht.2), e, he, hp,
      hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  exact (PiecewiseCurves.velocity_eq hv').symm

theorem variedEnergy_eq_within_integral (g : RiemannianMetric S)
    (hF : SmoothVariationOn S F ε a b) (hab : a ≤ b) {s : ℝ}
    (hs : s ∈ Ioo (-ε) ε) :
    variedEnergy g F a b s = (1 / 2 : ℝ) * ∫ t in a..b,
      pairing g (F (s,t)) (sliceVelocity S F a b s t) (sliceVelocity S F a b s t) := by
  unfold variedEnergy
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  dsimp only
  rw [sliceVelocity_eq_velocity hF hs ht]
  exact SmoothMetrics.tangentNorm_sq g (F (s,t)) _

theorem variedLength_eq_within_integral (g : RiemannianMetric S)
    (hF : SmoothVariationOn S F ε a b) (hab : a ≤ b) {s : ℝ}
    (hs : s ∈ Ioo (-ε) ε) :
    variedLength g F a b s = ∫ t in a..b,
      Real.sqrt (pairing g (F (s,t)) (sliceVelocity S F a b s t) (sliceVelocity S F a b s t)) := by
  unfold variedLength
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  dsimp only
  rw [sliceVelocity_eq_velocity hF hs ht]
  rfl

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b : ℝ}

theorem energy_firstVariation_of_density
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsMetricCompatible g C)
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hA : ContinuousOn (fun t => pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (segmentVelocity S F a b t)) (Icc a b))
    (hE : HasDerivAt (fun s => ∫ t in a..b,
        pairing g (F (s,t)) (sliceVelocity S F a b s t) (sliceVelocity S F a b s t))
      (2 * ∫ t in a..b, pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (segmentVelocity S F a b t)) 0) :
    HasDerivAt (variedEnergy g F a b) (energyFirstVariation g C F a b) 0 := by
  have hE' := hE.const_mul (1/2 : ℝ)
  have hEE : (fun s => variedEnergy g F a b s) =ᶠ[𝓝 0]
      (fun s => (1/2 : ℝ) * ∫ t in a..b,
        pairing g (F (s,t)) (sliceVelocity S F a b s t) (sliceVelocity S F a b s t)) := by
    filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    exact variedEnergy_eq_within_integral g hF hab.le hs
  have hE'' : HasDerivAt (variedEnergy g F a b)
      (∫ t in a..b, pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (segmentVelocity S F a b t)) 0 := by
    convert hE'.congr_of_eventuallyEq hEE using 1
    ring
  exact firstVariation_of_c1_field g C hC hF hε hab (segmentVelocity_c1 hF hε hab) hA hE''

theorem length_firstVariation_of_density
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsMetricCompatible g C)
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b,
      0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t))
    (hA : ContinuousOn (fun t => pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (unitVelocity g F a b t)) (Icc a b))
    (hL : HasDerivAt (fun s => ∫ t in a..b,
        Real.sqrt (pairing g (F (s,t)) (sliceVelocity S F a b s t) (sliceVelocity S F a b s t)))
      (∫ t in a..b, pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (unitVelocity g F a b t)) 0) :
    HasDerivAt (variedLength g F a b) (lengthFirstVariation g C F a b) 0 := by
  have hLL : (fun s => variedLength g F a b s) =ᶠ[𝓝 0]
      (fun s => ∫ t in a..b,
        Real.sqrt (pairing g (F (s,t)) (sliceVelocity S F a b s t) (sliceVelocity S F a b s t))) := by
    filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    exact variedLength_eq_within_integral g hF hab.le hs
  exact firstVariation_of_c1_field g C hC hF hε hab (unitVelocity_c1 g hF hε hab hpos)
    hA (hL.congr_of_eventuallyEq hLL)

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

/-- First variation of energy, with moving endpoints and no speed assumption. -/
theorem first_variation_energy :
    P202Specs.Geometry.FirstVariation.first_variation_energyType.{u} := by
  intro n kind M inst S g C hC F ε a b hε hab hF
  rcases hab.eq_or_lt with heq | hab
  · subst b
    exact (first_variations_degenerate g C F a).1
  obtain ⟨hA, hd⟩ := energy_density_calculus g C hC.2 hF hε hab
    (fun t ht => sliceVelocity_mixed_covariantDerivative g C hC hF hε hab ht)
  have heq : variedEnergy g F a b =ᶠ[𝓝 0]
      (fun s => (1/2 : ℝ) * ∫ t in a..b, squaredVariationSpeed g F a b (s,t)) := by
    filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    exact variedEnergy_eq_within_integral g hF hab.le hs
  exact firstVariation_of_c1_field g C hC.2 hF hε hab
    (segmentVelocity_c1 hF hε hab) hA (hd.congr_of_eventuallyEq heq)

/-- Finite-piecewise energy variation with every full-velocity corner term. -/
theorem piecewise_energy :
    P202Specs.Geometry.FirstVariation.piecewise_energyType.{u} :=
  piecewise_energy_from_smooth_formula first_variation_energy

end P202.Geometry.FirstVariation

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace P202.Geometry.FirstVariation

/-- Strict positivity on the compact central slice persists on a closed
uniform strip. No differentiability or nonnegative assumption is needed. -/
theorem exists_positive_closed_strip
    {ε a b : ℝ} (hε : 0 < ε) {H : ℝ × ℝ → ℝ}
    (hH : ContinuousOn H (Ioo (-ε) ε ×ˢ Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < H (0,t)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      ∀ z ∈ Icc (-δ) δ ×ˢ Icc a b, 0 < H z := by
  let K : Set (ℝ × Icc a b) := Ioo (-ε) ε ×ˢ univ
  let H' : ℝ × Icc a b → ℝ := fun z => H (z.1,z.2.val)
  have hK : IsOpen K := isOpen_Ioo.prod isOpen_univ
  have hH' : ContinuousOn H' K := by
    exact hH.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun z hz => ⟨hz.1, z.2.property⟩)
  let O := K ∩ H' ⁻¹' Ioi 0
  have hO : IsOpen O := hH'.isOpen_inter_preimage hK isOpen_Ioi
  have hKO : ({(0 : ℝ)} : Set ℝ) ×ˢ (univ : Set (Icc a b)) ⊆ O := by
    rintro ⟨s,t⟩ ⟨hs, _⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨⟨⟨by linarith, hε⟩, mem_univ _⟩, hpos t.val t.property⟩
  obtain ⟨U, V, hU, _, h0U, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hO hKO
  obtain ⟨d, hd, hdu⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  let δ := min (ε / 2) (d / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδd : δ < d := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, hδε, ?_⟩
  intro z hz
  have hzU : z.1 ∈ U := by
    apply hdu
    change dist z.1 0 < d
    rw [Real.dist_eq, sub_zero]
    exact (abs_le.mpr hz.1).trans_lt hδd
  have hvz := hUV (show (z.1, (⟨z.2,hz.2⟩ : Icc a b)) ∈ U ×ˢ V from
    ⟨hzU, hV (mem_univ _)⟩)
  exact hvz.2


/-- A positive compact central slice admits a smaller closed strip on which
sqrt(H) and its actual first partial derivative are jointly continuous. -/
theorem sqrt_on_positive_closed_strip
    {ε a b : ℝ} (hε : 0 < ε) {H : ℝ × ℝ → ℝ}
    (hH : ∀ z ∈ Ioo (-ε) ε ×ˢ Icc a b, ∃ y : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) y z ∧
        H =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] y)
    (hpos : ∀ t ∈ Icc a b, 0 < H (0,t)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      (∀ z ∈ Icc (-δ) δ ×ˢ Icc a b, 0 < H z) ∧
      ContinuousOn (fun z => Real.sqrt (H z)) (Icc (-δ) δ ×ˢ Icc a b) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv (fun s => Real.sqrt (H (s,z.2))) z.1)
        (Icc (-δ) δ ×ˢ Icc a b) ∧
      ∀ z ∈ Icc (-δ) δ ×ˢ Icc a b,
        HasDerivAt (fun s => Real.sqrt (H (s,z.2)))
          (deriv (fun s => Real.sqrt (H (s,z.2))) z.1) z.1 := by
  have hCont := (scalar_germs_on_strip isOpen_Ioo hH).1
  obtain ⟨η, hη, hηε, hηpos⟩ := exists_positive_closed_strip hε hCont hpos
  have hηsub : Ioo (-η) η ×ˢ Icc a b ⊆ Ioo (-ε) ε ×ˢ Icc a b := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], hz.1.2.trans hηε⟩, hz.2⟩
  have hsqrt : ∀ z ∈ Ioo (-η) η ×ˢ Icc a b, ∃ y : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) y z ∧
        (fun z => Real.sqrt (H z)) =ᶠ[𝓝[Ioo (-η) η ×ˢ Icc a b] z] y := by
    intro z hz
    obtain ⟨y, hy, he⟩ := hH z (hηsub hz)
    have hzy : 0 < y z := by
      rw [← he.self_of_nhdsWithin (hηsub hz)]
      exact hηpos z ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩
    refine ⟨fun z => Real.sqrt (y z), hy.sqrt hzy.ne', ?_⟩
    exact (he.filter_mono (nhdsWithin_mono z hηsub)).fun_comp Real.sqrt
  obtain ⟨hsqrtCont, hsqrtDerivCont, hsqrtDeriv⟩ := scalar_germs_on_strip isOpen_Ioo hsqrt
  let δ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδη : δ < η := by dsimp [δ]; linarith
  have hsub : Icc (-δ) δ ×ˢ Icc a b ⊆ Ioo (-η) η ×ˢ Icc a b := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], lt_of_le_of_lt hz.1.2 hδη⟩, hz.2⟩
  refine ⟨δ, hδ, hδη.trans hηε, ?_, hsqrtCont.mono hsub,
    hsqrtDerivCont.mono hsub, fun z hz => hsqrtDeriv z (hsub hz)⟩
  intro z hz
  have hz' := hsub hz
  exact hηpos z ⟨⟨hz'.1.1.le, hz'.1.2.le⟩, hz'.2⟩

end P202.Geometry.FirstVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {F : ℝ × ℝ → M} {ε a b : ℝ}

/-- Positive speed on the compact base segment permits differentiation of the
actual norm density on a common strip. -/
theorem length_density_calculus
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsMetricCompatible g C) (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t))
    (hmix : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun s => F (s,t))
      (fun s => sliceVelocity S F a b s t) (Ioo (-ε) ε) 0
      (covariantDerivativeWithin C (fun r => F (0,r))
        (variationField S F) (Icc a b) t)) :
    let A : ℝ → ℝ := fun t => pairing g (F (0,t))
      (covariantDerivativeWithin C (fun r => F (0,r))
        (variationField S F) (Icc a b) t) (unitVelocity g F a b t)
    ContinuousOn A (Icc a b) ∧
      HasDerivAt (fun s => ∫ t in a..b,
        Real.sqrt (squaredVariationSpeed g F a b (s,t))) (∫ t in a..b, A t) 0 := by
  dsimp only
  let H := squaredVariationSpeed g F a b
  let G : ℝ × ℝ → ℝ := fun z => deriv (fun s => Real.sqrt (H (s,z.2))) z.1
  let A : ℝ → ℝ := fun t => pairing g (F (0,t))
    (covariantDerivativeWithin C (fun r => F (0,r))
      (variationField S F) (Icc a b) t) (unitVelocity g F a b t)
  have hH0 (t : ℝ) : H (0,t) =
      tangentNorm g (F (0,t)) (segmentVelocity S F a b t) ^ 2 := by
    rw [SmoothMetrics.tangentNorm_sq]
    simp only [H, squaredVariationSpeed, sliceVelocity_zero]
  have hsqrt0 (t : ℝ) : Real.sqrt (H (0,t)) =
      tangentNorm g (F (0,t)) (segmentVelocity S F a b t) := by
    simp only [H, squaredVariationSpeed, sliceVelocity_zero, tangentNorm]
  have hHp (t : ℝ) (ht : t ∈ Icc a b) : 0 < H (0,t) := by
    rw [hH0]
    exact sq_pos_of_pos (hpos t ht)
  obtain ⟨δ, hδ, _, hHpos, hH, hG, hder⟩ := sqrt_on_positive_closed_strip hε
    (fun z hz => sliceSquaredSpeed_extension g hF hab hz) hHp
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hG0 (t : ℝ) (ht : t ∈ Icc a b) : G (0,t) = A t := by
    have hd := (squaredVariationSpeed_derivative g C hC hε ht (hmix t ht)).sqrt
      (hHp t ht).ne'
    change deriv (fun s => Real.sqrt (squaredVariationSpeed g F a b (s,t))) 0 = A t
    rw [hd.deriv, hsqrt0]
    simp only [A, unitVelocity, pairing, map_smul, smul_eq_mul]
    field_simp
  have hAc : ContinuousOn A (Icc a b) := by
    have hc := hG.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨h0, ht⟩)
    apply hc.congr
    intro t ht
    exact (hG0 t ht).symm
  refine ⟨hAc, ?_⟩
  have hd := hasDerivAt_integral_on_rectangle hab.le hδ hH hG
    (fun s hs t ht => hder (s,t) ⟨⟨hs.1.le, hs.2.le⟩,ht⟩)
  have heq : (∫ t in a..b, G (0,t)) = ∫ t in a..b, A t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro t ht
    exact hG0 t (Ioo_subset_Icc_self ht)
  change HasDerivAt (fun s => ∫ t in a..b, Real.sqrt (H (s,t)))
    (∫ t in a..b, G (0,t)) 0 at hd
  rwa [heq] at hd

end P202.Geometry.FirstVariation

namespace P202.Geometry.FirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

/-- First variation of length, with moving endpoints and positive base speed. -/
theorem first_variation_length :
    P202Specs.Geometry.FirstVariation.first_variation_lengthType.{u} := by
  intro n kind M inst S g C hC F ε a b hε hab hF hpos
  rcases hab.eq_or_lt with heq | hab
  · subst b
    exact (first_variations_degenerate g C F a).2
  obtain ⟨hA, hd⟩ := length_density_calculus g C hC.2 hF hε hab hpos
    (fun t ht => sliceVelocity_mixed_covariantDerivative g C hC hF hε hab ht)
  exact length_firstVariation_of_density g C hC.2 hF hε hab hpos hA hd

/-- Finite-piecewise length variation with every unit-velocity corner term. -/
theorem piecewise_length :
    P202Specs.Geometry.FirstVariation.piecewise_lengthType.{u} :=
  piecewise_length_from_smooth_formula first_variation_length

end P202.Geometry.FirstVariation
