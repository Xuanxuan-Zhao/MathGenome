import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LengthLaws
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PiecewiseCurves
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
namespace P202.Geometry.LengthLaws
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData
open Set Filter
open scoped Topology
universe u

private theorem sum_integrals {k : ℕ} (node : Fin (k + 1) → ℝ) {f : ℝ → ℝ}
    (h : ∀ i : Fin k, IntervalIntegrable f MeasureTheory.volume
      (node i.castSucc) (node i.succ)) :
    (∑ i : Fin k, ∫ t in node i.castSucc..node i.succ, f t) =
      ∫ t in node 0..node (Fin.last k), f t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have hp := fun i : Fin k => h i.castSucc
    have hpre := PiecewiseCurves.intervalIntegrable_of_partition
      (fun i : Fin (k + 1) => node i.castSucc) hp
    rw [show (∑ i : Fin k, ∫ t in node i.castSucc.castSucc..node i.castSucc.succ, f t) =
      ∫ t in node 0..node (Fin.last k).castSucc, f t from
        by simpa only [Fin.succ_castSucc, Fin.castSucc_zero] using ih (fun i => node i.castSucc) hp]
    exact intervalIntegral.integral_add_adjacent_intervals hpre (h (Fin.last k))

variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- Agreement on a closed curve interval suffices for integrals of speed,
even when the other total map has no regularity outside this interval. -/
theorem integral_speed_eq_of_eqOn (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) {d : ℝ → M} (heq : EqOn c d (Icc a b)) :
    (∫ t in a..b, speed g c t) = ∫ t in a..b, speed g d t := by
  apply PiecewiseCurves.integral_eq_of_eqOn_off_finite (breakpoints c)
  intro t ht hcorner
  rw [uIoc_of_le c.ordered] at ht
  exact PiecewiseCurves.speed_eq_of_eqOn g c heq ⟨ht.1.le, ht.2⟩ hcorner

theorem speed_integrable_of_eqOn (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) {d : ℝ → M} (heq : EqOn c d (Icc a b)) :
    IntervalIntegrable (speed g d) MeasureTheory.volume a b := by
  apply (PiecewiseCurves.intervalIntegrable_iff_of_eqOn_off_finite
    (breakpoints c) (fun t ht hcorner => ?_)).mp (PiecewiseCurves.speed_integrable g c)
  rw [uIoc_of_le c.ordered] at ht
  exact PiecewiseCurves.speed_eq_of_eqOn g c heq ⟨ht.1.le, ht.2⟩ hcorner

/-- A smooth metric-preserving differential preserves length; neither global
injectivity nor surjectivity of the map is required. -/
theorem metricPreserving_length
    {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N}
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, SmoothManifolds.DifferentialData.IsDifferential S T f p (L p))
    (hmetric : IsMetricPreserving g h f L)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) :
    length h (PiecewiseCurves.postcompose f hf c) = length g c := by
  unfold length
  apply PiecewiseCurves.integral_eq_of_eqOn_off_finite (breakpoints c)
  intro t ht hcorner
  rw [uIoc_of_le c.ordered] at ht
  change tangentNorm h (f (c t))
    (velocity T (PiecewiseCurves.postcompose f hf c) t) = _
  rw [PiecewiseCurves.velocity_postcompose f hf c ⟨ht.1.le, ht.2⟩ hcorner (L (c t)) (hL (c t))]
  exact SmoothMetrics.metricPreserving_norm g h f L hmetric _ _

/-- Scalar regularity on a closed piece gives the ordinary derivative at
all its interior points. Endpoint derivatives are deliberately unnecessary. -/
private theorem regular_deriv {φ : ℝ → ℝ} {l r t : ℝ}
    (h : RegularRealC1On φ (Icc l r)) (ht : t ∈ Ioo l r) :
    HasDerivAt φ (deriv φ t) t ∧ 0 < deriv φ t := by
  obtain ⟨ψ, hψ, _, heq, hpos⟩ := h t (Ioo_subset_Icc_self ht)
  have heq' : φ =ᶠ[𝓝 t] ψ := by
    simpa only [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht.1 ht.2)] using heq
  have hd := (hψ.differentiableAt (by simp)).hasDerivAt
  have hder : deriv φ t = deriv ψ t := heq'.deriv_eq
  constructor
  · rw [hder]
    exact hd.congr_of_eventuallyEq heq'
  · rwa [hder]

private theorem parameter_piece_deriv {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (i : Fin φ.pieces)
    {t : ℝ} (ht : t ∈ Ioo (min (φ.node i.castSucc) (φ.node i.succ))
      (max (φ.node i.castSucc) (φ.node i.succ))) :
    HasDerivAt φ (deriv φ t) t ∧ 0 < deriv φ t := by
  have hle := φ.monotone_node (Fin.castSucc_le_succ i)
  rw [min_eq_left hle, max_eq_right hle] at ht
  exact regular_deriv (φ.regular i) ht

/-- Substitution across every piece of a regular increasing parameter change.
The integrand need only be interval integrable, so it may have corners. -/
theorem parameter_integral_substitution {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ t in l..r, f (φ t) * deriv φ t) = ∫ t in a..b, f t := by
  have hi (i : Fin φ.pieces) : IntervalIntegrable f MeasureTheory.volume
      (φ (φ.node i.castSucc)) (φ (φ.node i.succ)) := by
    apply hf.mono_set
    rw [uIcc_of_le φ.target_ordered]
    exact uIcc_subset_Icc
      (PiecewiseCurves.parameter_mapsTo φ (PiecewiseCurves.parameter_node_mem φ i.castSucc))
      (PiecewiseCurves.parameter_mapsTo φ (PiecewiseCurves.parameter_node_mem φ i.succ))
  have hj (i : Fin φ.pieces) :
      IntervalIntegrable (fun t => f (φ t) * deriv φ t) MeasureTheory.volume
        (φ.node i.castSucc) (φ.node i.succ) :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (PiecewiseCurves.parameter_continuous φ).continuousOn
      (fun t ht => (parameter_piece_deriv φ i ht).1)
      (fun t ht => (parameter_piece_deriv φ i ht).2.le)).mpr (hi i)
  have heq (i : Fin φ.pieces) :
      (∫ t in φ.node i.castSucc..φ.node i.succ, f (φ t) * deriv φ t) =
        ∫ t in φ (φ.node i.castSucc)..φ (φ.node i.succ), f t :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (PiecewiseCurves.parameter_continuous φ).continuousOn
      (fun t ht => (parameter_piece_deriv φ i ht).1)
      (fun t ht => (parameter_piece_deriv φ i ht).2.le)
  calc
    _ = ∑ i : Fin φ.pieces,
        ∫ t in φ.node i.castSucc..φ.node i.succ, f (φ t) * deriv φ t := by
      simpa only [φ.first_node, φ.last_node] using (sum_integrals φ.node hj).symm
    _ = ∑ i : Fin φ.pieces,
        ∫ t in φ (φ.node i.castSucc)..φ (φ.node i.succ), f t := Finset.sum_congr rfl (fun i _ => heq i)
    _ = _ := by
      simpa only [φ.first_node, φ.last_node, PiecewiseCurves.parameter_first,
        PiecewiseCurves.parameter_last] using sum_integrals (fun i => φ (φ.node i)) hi

theorem isometricImmersion_length :
    P202Specs.Geometry.LengthLaws.isometricImmersion_lengthType.{u} := by
  intro n kind M _ S m targetKind N _ T g h f hi a b c d heq
  obtain ⟨i, hmetric⟩ := hi
  calc
    length h d = length h (PiecewiseCurves.postcompose f i.smooth c) :=
      PiecewiseCurves.length_eq_of_eqOn h d _ heq
    _ = length g c := metricPreserving_length g h f i.smooth
      i.differential i.isDifferential hmetric c

theorem localIsometry_length :
    P202Specs.Geometry.LengthLaws.localIsometry_lengthType.{u} := by
  intro n kind M _ S m targetKind N _ T g h f hi a b c d heq
  exact isometricImmersion_length g h f
    (SmoothMetrics.localIsometry_isIsometricImmersion g h f hi) c d heq

theorem localIsometry_length_exists :
    P202Specs.Geometry.LengthLaws.localIsometry_length_existsType.{u} := by
  intro n kind M _ S m targetKind N _ T g h f hi a b c
  refine ⟨PiecewiseCurves.postcompose f hi.1.1 c, fun _ => rfl, ?_⟩
  exact localIsometry_length g h f hi c _ (fun _ _ => rfl)

theorem subdivision_length :
    P202Specs.Geometry.LengthLaws.subdivision_lengthType.{u} := by
  intro n kind M _ S g a b c k node hnode hfirst hlast pieces heq
  have hint (i : Fin k) := speed_integrable_of_eqOn g (pieces i) (heq i)
  have heqint (i : Fin k) := integral_speed_eq_of_eqOn g (pieces i) (heq i)
  calc
    length g c = ∑ i : Fin k, ∫ t in node i.castSucc..node i.succ, speed g c t := by
      simpa only [hfirst, hlast, length] using (sum_integrals node hint).symm
    _ = _ := Finset.sum_congr rfl (fun i _ => (heqint i).symm)

theorem subdivision_length_exists :
    P202Specs.Geometry.LengthLaws.subdivision_length_existsType.{u} := by
  intro n kind M _ S g a b c k node hnode hfirst hlast
  have hleft (i : Fin k) : a ≤ node i.castSucc := by
    rw [← hfirst]
    exact hnode (Fin.zero_le _)
  have hright (i : Fin k) : node i.succ ≤ b := by
    rw [← hlast]
    exact hnode (Fin.le_last _)
  let pieces := fun i : Fin k => PiecewiseCurves.restrict c
    (node i.castSucc) (node i.succ) (hleft i)
    (hnode (Fin.castSucc_le_succ i)) (hright i)
  exact ⟨pieces, fun _ _ => rfl,
    subdivision_length g c node hnode hfirst hlast pieces (fun _ _ _ => rfl)⟩

theorem finiteConcatenation_length :
    P202Specs.Geometry.LengthLaws.finiteConcatenation_lengthType.{u} := by
  intro n kind M _ S g k node p curves hstart hend
  obtain ⟨c, hc0, hck, hpieces⟩ :=
    PiecewiseCurves.finiteConcatenation_exists node p curves hstart hend
  have hnode : Monotone node :=
    Fin.monotone_iff_le_succ.mpr (fun i => (curves i).ordered)
  refine ⟨c, hc0, hck, fun i t ht => hpieces i t ht, ?_⟩
  exact subdivision_length g c node hnode rfl rfl curves
    (fun i t ht => (hpieces i t ht).symm)

theorem concatenation_length :
    P202Specs.Geometry.LengthLaws.concatenation_lengthType.{u} := by
  intro n kind M _ S g a b z c d hmatch
  let e := PiecewiseCurves.concatenate c d hmatch
  have hleft : EqOn c e (Icc a b) := fun t ht =>
    (PiecewiseCurves.concatenate_eq_left c d hmatch ht).symm
  have hright : EqOn d e (Icc b z) := fun t ht =>
    (PiecewiseCurves.concatenate_eq_right c d hmatch ht).symm
  refine ⟨e, hleft.symm, hright.symm, ?_⟩
  change (∫ t in a..z, speed g e t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (speed_integrable_of_eqOn g c hleft) (speed_integrable_of_eqOn g d hright),
    ← integral_speed_eq_of_eqOn g c hleft, ← integral_speed_eq_of_eqOn g d hright]
  rfl

private theorem length_reverse (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) : length g (PiecewiseCurves.reverse c) = length g c := by
  classical
  let K := (breakpoints c).image (fun s => a + b - s)
  have heq : (∫ t in a..b, speed g (PiecewiseCurves.reverse c) t) =
      ∫ t in a..b, speed g c (a + b - t) := by
    apply PiecewiseCurves.integral_eq_of_eqOn_off_finite K
    intro t ht hbad
    rw [uIoc_of_le c.ordered] at ht
    have hmem : a + b - t ∈ Icc a b := by
      constructor <;> linarith [ht.1, ht.2]
    have hcorner : a + b - t ∉ breakpoints c := by
      intro h
      exact hbad (Finset.mem_image.mpr ⟨a + b - t, h, by ring⟩)
    change tangentNorm g (c (a + b - t))
      (velocity S (PiecewiseCurves.reverse c) t) = _
    rw [PiecewiseCurves.velocity_reverse c hmem hcorner, SmoothMetrics.tangentNorm_neg]
    rfl
  calc
    length g (PiecewiseCurves.reverse c) =
        ∫ t in a..b, speed g c (a + b - t) := heq
    _ = length g c := by
      simpa only [add_sub_cancel_right, add_sub_cancel_left, length] using
        intervalIntegral.integral_comp_sub_left (speed g c) (a + b) (a := a) (b := b)

theorem reversal_length :
    P202Specs.Geometry.LengthLaws.reversal_lengthType.{u} := by
  intro n kind M _ S g a b c d heq
  exact (PiecewiseCurves.length_eq_of_eqOn g d (PiecewiseCurves.reverse c) heq).trans
    (length_reverse g c)

theorem reversal_length_exists :
    P202Specs.Geometry.LengthLaws.reversal_length_existsType.{u} := by
  intro n kind M _ S g a b c
  exact ⟨PiecewiseCurves.reverse c, fun _ => rfl, length_reverse g c⟩

private theorem length_reparametrize (g : RiemannianMetric S) {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) :
    length g (PiecewiseCurves.reparametrize c φ) = length g c := by
  obtain ⟨K, hK⟩ := PiecewiseCurves.reparametrization_velocity_finite_exceptions c φ
  calc
    length g (PiecewiseCurves.reparametrize c φ) =
        ∫ t in l..r, speed g c (φ t) * deriv φ t := by
      apply PiecewiseCurves.integral_eq_of_eqOn_off_finite K
      intro t ht hbad
      rw [uIoc_of_le φ.source_ordered] at ht
      obtain ⟨_, hpos, hvel⟩ := hK t ⟨ht.1.le, ht.2⟩ hbad
      change tangentNorm g (c (φ t)) (velocity S (c ∘ φ) t) = _
      rw [hvel, SmoothMetrics.tangentNorm_smul, abs_of_pos hpos]
      exact mul_comm _ _
    _ = length g c := parameter_integral_substitution φ (PiecewiseCurves.speed_integrable g c)

theorem reparametrization_length :
    P202Specs.Geometry.LengthLaws.reparametrization_lengthType.{u} := by
  intro n kind M _ S g a b l r c φ q heq
  exact (PiecewiseCurves.length_eq_of_eqOn g q (PiecewiseCurves.reparametrize c φ) heq).trans
    (length_reparametrize g c φ)

theorem reparametrization_length_exists :
    P202Specs.Geometry.LengthLaws.reparametrization_length_existsType.{u} := by
  intro n kind M _ S g a b l r c φ
  exact ⟨PiecewiseCurves.reparametrize c φ, fun _ => rfl, length_reparametrize g c φ⟩

end P202.Geometry.LengthLaws
