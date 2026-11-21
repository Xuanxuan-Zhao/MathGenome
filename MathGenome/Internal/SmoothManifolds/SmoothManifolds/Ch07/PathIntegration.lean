import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.PathIntegration
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Covectors
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Intrinsic integration along paths. See the independent specification for
its full scope. The lemmas below also isolate the purely one-dimensional
integral algebra from the local smoothness arguments. -/
set_option autoImplicit false

namespace SmoothManifolds.PathIntegration
open ModelData AtlasData MapData PartitionData TangentData CovectorData
  BundleOperationsData PathIntegrationData Set Filter
open scoped Topology
universe u

section Curves
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n k M)

theorem velocity_spec (γ : ℝ → M) (side : TangentData.CurveSide) (t : ℝ)
    (h : TangentData.CurveSmoothAt S (γ t) side (fun h => γ (t + h))) :
    TangentData.CurveRepresentsDerivation S (γ t) side (fun h => γ (t + h))
      (velocity S γ side t) := by
  classical
  have hex : ∃ v, TangentData.CurveRepresentsDerivation S (γ t) side
      (fun h => γ (t + h)) v :=
    (smooth_curve_defines_derivation S (γ t) side (fun h => γ (t + h)) h).exists
  simpa only [velocity, dite_eq_left hex] using hex.choose_spec

/-- Endpoint choices affect only two points, so the one-sided piece formula
agrees with the canonical integrand without any analytic assumption. -/
theorem pieceIntegral_eq (α : CovectorField S) (γ : ℝ → M) {a b : ℝ}
    (hab : a ≤ b) :
    pieceIntegral S α γ a b = pathIntegral S α γ a b := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  have hta : t ≠ a := ne_of_gt ht.1
  have htb : t ≠ b := ne_of_lt ht.2
  simp only [sideAt, ite_eq_right hta, ite_eq_right htb, coefficient]

@[simp] theorem pathIntegral_same (α : CovectorField S) (γ : ℝ → M) (a : ℝ) :
    pathIntegral S α γ a a = 0 := by
  exact intervalIntegral.integral_same

@[simp] theorem pieceIntegral_same (α : CovectorField S) (γ : ℝ → M) (a : ℝ) :
    pieceIntegral S α γ a a = 0 := by
  exact intervalIntegral.integral_same

/-- Interval-integral additivity already handles the zero-length case. -/
theorem pathIntegral_add_adjacent (α : CovectorField S) (γ : ℝ → M) (a b c : ℝ)
    (hab : IntervalIntegrable (coefficient S α γ) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (coefficient S α γ) MeasureTheory.volume b c) :
    pathIntegral S α γ a b + pathIntegral S α γ b c =
      pathIntegral S α γ a c :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- The canonical integrand satisfies FTC on any interval where its genuine
scalar derivatives exist and it is integrable. Smoothness will discharge these
analytic hypotheses for exact one-forms on the smooth path pieces. -/
theorem integral_dFunction_of_hasDeriv (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn (u ∘ γ) (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt (u ∘ γ)
      (coefficient S (dFunction S u hu) γ t) t)
    (hi : IntervalIntegrable (coefficient S (dFunction S u hu) γ)
      MeasureTheory.volume a b) :
    pathIntegral S (dFunction S u hu) γ a b = u (γ b) - u (γ a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd hi

/-- Read the intrinsic velocity on any scalar germ, at the original time. -/
theorem represented_hasDerivAt (γ : ℝ → M) (t : ℝ)
    (v : TangentData.TangentSpace S (γ t))
    (hv : TangentData.CurveRepresentsDerivation S (γ t) .twoSided
      (fun h => γ (t+h)) v)
    (g : TangentData.SmoothGerm S (γ t)) (f : M → ℝ)
    (hf : Germ.ofFun f = g.val) : HasDerivAt (f ∘ γ) (v.val g) t := by
  have hd := hv.2 g f hf
  change HasDerivWithinAt (fun h => f (γ (t+h))) (v.val g) univ 0 at hd
  have hd0 := hd.hasDerivAt (by simp)
  have ht : HasDerivAt (fun h => f (γ (t+h))) (v.val g) (t-t) := by simpa using hd0
  simpa only [sub_self, add_sub_cancel, Function.comp_def] using ht.comp_sub_const t t

/-- Chain rule for du, with no coordinate choice and no cotangent realization. -/
theorem coefficient_dFunction_hasDerivAt (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) (t : ℝ)
    (hγ : TangentData.CurveSmoothAt S (γ t) .twoSided (fun h => γ (t+h))) :
    HasDerivAt (u ∘ γ) (coefficient S (dFunction S u hu) γ t) t := by
  exact represented_hasDerivAt S γ t (velocity S γ .twoSided t)
    (velocity_spec S γ .twoSided t hγ) (functionGerm S u hu (γ t)) u rfl

/-- Every interior point of a smooth piece has its ordinary two-sided velocity. -/
theorem smoothOnInterval_interior (γ : ℝ → M) {a b t : ℝ}
    (hγ : SmoothOnInterval S γ a b) (ht : t ∈ Ioo a b) :
    TangentData.CurveSmoothAt S (γ t) .twoSided (fun h => γ (t+h)) := by
  have hs := hγ.2.2 t ⟨ht.1.le, ht.2.le⟩ (ht.1.trans ht.2)
  simpa only [sideAt, ite_eq_right (ne_of_gt ht.1), ite_eq_right (ne_of_lt ht.2)] using hs

/-- On smooth pieces, the derivative part of FTC is automatic from the path
hypothesis. Integrability remains the separate analytic obligation. -/
theorem integral_dFunction_smoothPiece_of_integrable (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) {a b : ℝ}
    (hγ : SmoothOnInterval S γ a b)
    (hi : IntervalIntegrable (coefficient S (dFunction S u hu) γ)
      MeasureTheory.volume a b) :
    pathIntegral S (dFunction S u hu) γ a b = u (γ b) - u (γ a) := by
  apply integral_dFunction_of_hasDeriv S u hu γ hγ.1 _ _ hi
  · have hc : Continuous u := continuous_iff_continuousAt.mpr (fun p => (continuous_apply (0 : Fin 1)).continuousAt.comp (hu p).1)
    exact hc.comp_continuousOn hγ.2.1
  · intro t ht
    exact coefficient_dFunction_hasDerivAt S u hu γ t (smoothOnInterval_interior S γ hγ ht)

/-- The intrinsic chain rule for velocities at ordinary smooth points. In
particular the velocity of a paused reparameterization is zero. -/
theorem velocity_comp (γ : ℝ → M) (φ : ℝ → ℝ) (t r : ℝ)
    (hγ : TangentData.CurveSmoothAt S (γ (φ t)) .twoSided
      (fun h => γ (φ t + h)))
    (hcomp : TangentData.CurveSmoothAt S ((γ ∘ φ) t) .twoSided
      (fun h => (γ ∘ φ) (t+h)))
    (hφ : HasDerivAt φ r t) :
    velocity S (γ ∘ φ) .twoSided t = r • velocity S γ .twoSided (φ t) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  obtain ⟨f, _, hfg⟩ := (mem_smoothGermAlgebra_iff S (γ (φ t)) g.val).mp g.property
  have ho := represented_hasDerivAt S γ (φ t) (velocity S γ .twoSided (φ t))
    (velocity_spec S γ .twoSided (φ t) hγ) g f hfg.symm
  have hc := represented_hasDerivAt S (γ ∘ φ) t (velocity S (γ ∘ φ) .twoSided t)
    (velocity_spec S (γ ∘ φ) .twoSided t hcomp) g f hfg.symm
  have hd := hc.unique (ho.comp t hφ)
  change (velocity S (γ ∘ φ) .twoSided t).val g =
    r * (velocity S γ .twoSided (φ t)).val g
  exact hd.trans (mul_comm _ _)

theorem coefficient_comp (α : CovectorField S) (γ : ℝ → M)
    (φ : ℝ → ℝ) (t r : ℝ)
    (hγ : TangentData.CurveSmoothAt S (γ (φ t)) .twoSided
      (fun h => γ (φ t + h)))
    (hcomp : TangentData.CurveSmoothAt S ((γ ∘ φ) t) .twoSided
      (fun h => (γ ∘ φ) (t+h))) (hφ : HasDerivAt φ r t) :
    coefficient S α (γ ∘ φ) t = r * coefficient S α γ (φ t) := by
  unfold coefficient
  rw [velocity_comp S γ φ t r hγ hcomp hφ, map_smul]
  rfl

end Curves

namespace Subdivision

variable {a b : ℝ} (s : PathIntegrationData.Subdivision a b)

theorem point_le_point {i j : ℕ} (hi : i ≤ s.count) (hj : j ≤ s.count) (hij : i ≤ j) :
    s.point i ≤ s.point j :=
  s.increasing.monotoneOn ⟨Nat.zero_le i, hi⟩ ⟨Nat.zero_le j, hj⟩ hij

theorem point_mem {i : ℕ} (hi : i ≤ s.count) : s.point i ∈ Icc a b := by
  constructor
  · simpa only [s.first] using point_le_point s (Nat.zero_le _) hi (Nat.zero_le _)
  · simpa only [s.last] using point_le_point s hi le_rfl hi

theorem start_lt_end {i : ℕ} (hi : i < s.count) : s.point i < s.point (i + 1) :=
  s.increasing ⟨Nat.zero_le _, hi.le⟩ ⟨Nat.zero_le _, hi⟩ (Nat.lt_succ_self i)

include s in
 theorem le : a ≤ b := by
  simpa only [s.first, s.last] using point_le_point s (Nat.zero_le _) le_rfl (Nat.zero_le _)

theorem integral_eq_sum {f : ℝ → ℝ}
    (hi : ∀ i < s.count, IntervalIntegrable f MeasureTheory.volume (s.point i) (s.point (i+1))) :
    (∫ t in a..b, f t) = ∑ i ∈ Finset.range s.count, ∫ t in s.point i..s.point (i+1), f t := by
  simpa only [s.first, s.last] using
    (intervalIntegral.sum_integral_adjacent_intervals hi).symm

end Subdivision

section SubdivisionIntegrals
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n k M) (α : CovectorField S) (γ : ℝ → M)

theorem integral_eq_sum_of_integrable {a b : ℝ} (s : PathIntegrationData.Subdivision a b)
    (hi : ∀ i < s.count, IntervalIntegrable (coefficient S α γ)
      MeasureTheory.volume (s.point i) (s.point (i+1))) :
    pathIntegral S α γ a b = subdivisionIntegral S α γ s := by
  rw [pathIntegral, Subdivision.integral_eq_sum s hi]
  apply Finset.sum_congr rfl
  intro i hi
  exact (pieceIntegral_eq S α γ (Subdivision.start_lt_end s (Finset.mem_range.mp hi)).le).symm

theorem subdivision_independent_of_integrable {a b : ℝ}
    (s r : PathIntegrationData.Subdivision a b)
    (hs : ∀ i < s.count, IntervalIntegrable (coefficient S α γ)
      MeasureTheory.volume (s.point i) (s.point (i+1)))
    (hr : ∀ i < r.count, IntervalIntegrable (coefficient S α γ)
      MeasureTheory.volume (r.point i) (r.point (i+1))) :
    subdivisionIntegral S α γ s = subdivisionIntegral S α γ r :=
  (integral_eq_sum_of_integrable S α γ s hs).symm.trans
    (integral_eq_sum_of_integrable S α γ r hr)

end SubdivisionIntegrals
section ExactForms
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

theorem curve_scalar_contDiffWithinAt (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (p : M) (side : TangentData.CurveSide)
    (c : ℝ → M) (hc : TangentData.CurveSmoothAt S p side c) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞) (u ∘ c) (curveParameterSet side) 0 := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, G, hG, hGu⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp (hu p)).2 e he hp
  obtain ⟨V, hV, h0V, H, hH, heH⟩ := hc.2.2 e he hp
  have h0 : (0 : ℝ) ∈ curveParameterSet side := by
    cases side <;> simp [curveParameterSet, TangentData.curveParameterSet]
  have hH0 : H 0 = (e p).val := by
    have hh := heH.self_of_nhdsWithin h0
    simpa only [hc.1] using hh.symm
  have hGH : ContDiffAt ℝ (⊤ : ℕ∞) (G ∘ H) 0 :=
    (hG.contDiffAt (by rw [hH0]; exact hU.mem_nhds hpU)).comp 0
      (hH.contDiffAt (hV.mem_nhds h0V))
  apply hGH.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ h0
  have hct : Tendsto c (𝓝[curveParameterSet side] 0) (𝓝 p) := by
    simpa only [ContinuousWithinAt, hc.1] using hc.2.1
  have hucomp := hGu.comp_tendsto hct
  filter_upwards [hucomp, heH] with t hut het
  change u (c t) = G (H t)
  change G (e (c t)).val = u (c t) at hut
  exact hut.symm.trans (congrArg G het)

/-- Subtracting t maps the whole parameter interval to its appropriate side. -/
theorem sub_mapsTo_side {a b t : ℝ} (ht : t ∈ Icc a b) :
    MapsTo (fun s : ℝ => s-t) (Icc a b) (curveParameterSet (sideAt a b t)) := by
  intro s hs
  classical
  by_cases hta : t = a
  · simp only [sideAt, ite_eq_left hta, curveParameterSet, TangentData.curveParameterSet,
      mem_Ici]
    linarith [hs.1]
  · by_cases htb : t = b
    · simp only [sideAt, ite_eq_right hta, ite_eq_left htb, curveParameterSet,
        TangentData.curveParameterSet, mem_Iic]
      linarith [hs.2]
    · simp [sideAt, hta, htb, curveParameterSet, TangentData.curveParameterSet]

theorem scalar_comp_contDiffOn (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) {a b : ℝ}
    (hab : a < b) (hγ : SmoothOnInterval S γ a b) :
    ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ γ) (Icc a b) := by
  intro t ht
  have hs := curve_scalar_contDiffWithinAt S u hu (γ t) (sideAt a b t)
    (fun h => γ (t+h)) (hγ.2.2 t ht hab)
  have hs' : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun h => u (γ (t+h)))
      (curveParameterSet (sideAt a b t)) (t-t) := by simpa only [Function.comp_def, sub_self] using hs
  have hsub : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s-t) (Icc a b) t :=
    (contDiff_id.sub contDiff_const).contDiffWithinAt
  have hc := ContDiffWithinAt.comp (f := fun s : ℝ => s-t) t hs' hsub (sub_mapsTo_side ht)
  simpa only [Function.comp_def, add_sub_cancel] using hc

theorem exactCoefficient_integrable_smoothPiece (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) {a b : ℝ}
    (hγ : SmoothOnInterval S γ a b) :
    IntervalIntegrable (coefficient S (dFunction S u hu) γ) MeasureTheory.volume a b := by
  by_cases hab : a = b
  · subst b
    exact IntervalIntegrable.refl
  have hlt : a < b := lt_of_le_of_ne hγ.1 hab
  have hdiff := scalar_comp_contDiffOn S u hu γ hlt hγ
  have hcont := hdiff.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by simp)
  have hi : IntervalIntegrable (derivWithin (u ∘ γ) (Icc a b)) MeasureTheory.volume a b :=
    hcont.intervalIntegrable_of_Icc hγ.1
  apply hi.congr_uIoo
  rw [uIoo_of_le hγ.1]
  intro t ht
  have hd := PathIntegration.coefficient_dFunction_hasDerivAt S u hu γ t
    (PathIntegration.smoothOnInterval_interior S γ hγ ht)
  exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hlt t ⟨ht.1.le, ht.2.le⟩)

theorem integral_dFunction_smoothPiece (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) {a b : ℝ}
    (hγ : SmoothOnInterval S γ a b) :
    pathIntegral S (dFunction S u hu) γ a b = u (γ b) - u (γ a) :=
  PathIntegration.integral_dFunction_smoothPiece_of_integrable S u hu γ hγ
    (exactCoefficient_integrable_smoothPiece S u hu γ hγ)

theorem integral_dFunction (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (γ : ℝ → M) (a b : ℝ)
    (hγ : PiecewiseSmoothOn S γ a b) :
    pathIntegral S (dFunction S u hu) γ a b = u (γ b) - u (γ a) := by
  obtain ⟨s, hs⟩ := hγ.2.2
  have hi (i : ℕ) (hi : i < s.count) := exactCoefficient_integrable_smoothPiece S u hu γ (hs i hi)
  rw [PathIntegration.integral_eq_sum_of_integrable S (dFunction S u hu) γ s hi]
  change ∑ i ∈ Finset.range s.count, pieceIntegral S (dFunction S u hu) γ
    (s.point i) (s.point (i+1)) = _
  calc
    _ = ∑ i ∈ Finset.range s.count, (u (γ (s.point (i+1))) - u (γ (s.point i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [PathIntegration.pieceIntegral_eq S _ γ (hs i (Finset.mem_range.mp hi)).1]
      exact integral_dFunction_smoothPiece S u hu γ (hs i (Finset.mem_range.mp hi))
    _ = u (γ b) - u (γ a) := by
      simpa only [s.first, s.last] using Finset.sum_range_sub (fun i => u (γ (s.point i))) s.count


end ExactForms

section GeneralForms
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

/-- Evaluation of a one-sided intrinsic velocity differentiates scalar germs
within the whole closed parameter interval. -/
theorem represented_hasDerivWithinAt (γ : ℝ → M) {a b t : ℝ}
    (ht : t ∈ Icc a b) (v : TangentSpace S (γ t))
    (hv : CurveRepresentsDerivation S (γ t) (sideAt a b t)
      (fun h => γ (t+h)) v)
    (g : SmoothGerm S (γ t)) (f : M → ℝ) (hf : Germ.ofFun f = g.val) :
    HasDerivWithinAt (f ∘ γ) (v.val g) (Icc a b) t := by
  have hd := hv.2 g f hf
  have hd' : HasDerivWithinAt (fun h => f (γ (t+h))) (v.val g)
      (curveParameterSet (sideAt a b t)) (t-t) := by
    change HasDerivWithinAt (fun h => f (γ (t+h))) (v.val g)
      (curveParameterSet (sideAt a b t)) 0 at hd
    simpa only [sub_self] using hd
  have hsub : HasDerivWithinAt (fun s : ℝ => s-t) 1 (Icc a b) t := by
    simpa using (hasDerivAt_id t).sub_const t |>.hasDerivWithinAt (s := Icc a b)
  simpa only [Function.comp_def, add_sub_cancel, mul_one] using
    HasDerivWithinAt.comp (h := fun s : ℝ => s-t) t hd' hsub (sub_mapsTo_side ht)

/-- Coordinate derivatives within a smooth piece agree with the intrinsic
one-sided velocity, including at its two ends. -/
theorem velocity_coordinates_within (γ : ℝ → M) {a b t : ℝ}
    (hab : a < b) (hγ : SmoothOnInterval S γ a b) (ht : t ∈ Icc a b)
    (K : TangentBundleData.FiberCoordinates S)
    (e : ModelChart n k M) (he : e ∈ S.smoothStructure.val) (hp : γ t ∈ e.source)
    (j : Fin n) :
    K.equiv e he (γ t) hp (velocity S γ (sideAt a b t) t) j =
      derivWithin (fun y => (e (γ y)).val j) (Icc a b) t := by
  obtain ⟨xs, hxs, hx⟩ := K.isCoordinates e he (γ t) hp
  rw [hx]
  exact (represented_hasDerivWithinAt S γ ht _
    (velocity_spec S γ _ t (hγ.2.2 t ht hab)) (xs j) _ (hxs j).symm).derivWithin
      (uniqueDiffOn_Icc hab t ht) |>.symm

/-- In a chart valid at the point, the coordinate path is smooth within the
closed parameter interval. No extension into the manifold is used. -/
theorem curve_coordinates_contDiffWithinAt (γ : ℝ → M) {a b t : ℝ}
    (hab : a < b) (hγ : SmoothOnInterval S γ a b) (ht : t ∈ Icc a b)
    (e : ModelChart n k M) (he : e ∈ S.smoothStructure.val) (hp : γ t ∈ e.source) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun y => (e (γ y)).val) (Icc a b) t := by
  obtain ⟨U, hU, h0U, H, hH, heH⟩ := (hγ.2.2 t ht hab).2.2 e he hp
  have h0 : (0 : ℝ) ∈ curveParameterSet (sideAt a b t) := by
    cases sideAt a b t <;> simp [curveParameterSet, TangentData.curveParameterSet]
  have hs : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun h => (e (γ (t+h))).val)
      (curveParameterSet (sideAt a b t)) 0 :=
    (hH.contDiffAt (hU.mem_nhds h0U)).contDiffWithinAt.congr_of_eventuallyEq_of_mem heH h0
  have hs' : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun h => (e (γ (t+h))).val)
      (curveParameterSet (sideAt a b t)) (t-t) := by simpa using hs
  have hsub : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s-t) (Icc a b) t :=
    (contDiff_id.sub contDiff_const).contDiffWithinAt
  simpa only [Function.comp_def, add_sub_cancel] using ContDiffWithinAt.comp (f := fun s : ℝ => s-t) t hs' hsub (sub_mapsTo_side ht)

/-- The coefficient formed with one-sided endpoint velocities is continuous
on a smooth piece. -/
theorem pieceCoefficient_continuousOn (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) {a b : ℝ} (hab : a < b) (hγ : SmoothOnInterval S γ a b) :
    ContinuousOn (fun t => α.field (γ t) (velocity S γ (sideAt a b t) t)) (Icc a b) := by
  classical
  letI := (cotangentSpace C).topology
  intro t ht
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (γ t)
  let ac : M → Euclidean n := fun p =>
    (((cotangentSpace C).bundle.trivialization ⟨e, he⟩) ⟨p, α.field p⟩).2
  have hac : ContinuousAt ac (γ t) :=
    (Frames.trivializationCoordinates_smoothAt (cotangentSpace C).bundle ⟨e, he⟩
      ⟨γ t, α.field (γ t)⟩ (by rw [Covectors.cotangent_baseSet]; exact hp)).1.comp (f := fun p => (⟨p, α.field p⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))
      (α.smooth (γ t)).1
  have hc := hac.comp_continuousWithinAt (hγ.2.1 t ht)
  have hd (j : Fin n) : ContinuousWithinAt
      (derivWithin (fun y => (e (γ y)).val j) (Icc a b)) (Icc a b) t :=
    ((contDiffWithinAt_pi.mp (curve_coordinates_contDiffWithinAt S γ hab hγ ht e he hp) j).derivWithin
      (uniqueDiffOn_Icc hab) (m := 0) (by simp) ht).continuousWithinAt
  have hsum : ContinuousWithinAt (fun y => ∑ j, ac (γ y) j *
      derivWithin (fun z => (e (γ z)).val j) (Icc a b) y) (Icc a b) t := by
    apply tendsto_finsetSum
    intro j _
    exact ((continuous_apply j).continuousAt.comp_continuousWithinAt hc).mul (hd j)
  apply hsum.congr_of_eventuallyEq_of_mem _ ht
  have hchart : ∀ᶠ y in 𝓝[Icc a b] t, γ y ∈ e.source :=
    (hγ.2.1 t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp)
  filter_upwards [hchart, self_mem_nhdsWithin] with y hy hyt
  have hexpand := congrArg
    (fun lam : CotangentFiber S (γ y) => lam (velocity S γ (sideAt a b y) y))
    (Covectors.covector_expansion C.tangent.fiberCoordinates e he (γ y) hy (α.field (γ y)))
  rw [hexpand]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show ac (γ y) j = α.field (γ y)
    (coordinateVector C.tangent.fiberCoordinates e he (γ y) hy j) from
      Covectors.cotangent_coordinates C e he (γ y) hy _ j]
  rw [← velocity_coordinates_within S γ hab hγ hyt C.tangent.fiberCoordinates e he hy j]
  rfl

/-- A general smooth one-form has an integrable coefficient on every smooth
piece, even when only one-sided coordinate extensions exist at the ends. -/
theorem coefficient_integrable_smoothPiece (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) {a b : ℝ} (hγ : SmoothOnInterval S γ a b) :
    IntervalIntegrable (coefficient S α.field γ) MeasureTheory.volume a b := by
  by_cases hab : a = b
  · subst b
    exact IntervalIntegrable.refl
  have hlt : a < b := lt_of_le_of_ne hγ.1 hab
  apply (pieceCoefficient_continuousOn S C α γ hlt hγ).intervalIntegrable_of_Icc hγ.1 |>.congr_uIoo
  rw [uIoo_of_le hγ.1]
  intro t ht
  simp only [sideAt, ite_eq_right (ne_of_gt ht.1), ite_eq_right (ne_of_lt ht.2), coefficient]

theorem coefficient_integrable (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) (a b : ℝ) (hγ : PiecewiseSmoothOn S γ a b) :
    IntervalIntegrable (coefficient S α.field γ) MeasureTheory.volume a b := by
  obtain ⟨s, hs⟩ := hγ.2.2
  have hi (i : ℕ) (hi : i < s.count) := coefficient_integrable_smoothPiece S C α γ (hs i hi)
  simpa only [s.first, s.last] using IntervalIntegrable.trans_iterate hi

theorem integral_eq_sum (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) {a b : ℝ} (s : PathIntegrationData.Subdivision a b)
    (hs : ∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i+1))) :
    pathIntegral S α.field γ a b = subdivisionIntegral S α.field γ s :=
  integral_eq_sum_of_integrable S α.field γ s
    (fun i hi => coefficient_integrable_smoothPiece S C α γ (hs i hi))

theorem subdivision_independent (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) {a b : ℝ} (s r : PathIntegrationData.Subdivision a b)
    (hs : ∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i+1)))
    (hr : ∀ i < r.count, SmoothOnInterval S γ (r.point i) (r.point (i+1))) :
    subdivisionIntegral S α.field γ s = subdivisionIntegral S α.field γ r :=
  (integral_eq_sum S C α γ s hs).symm.trans (integral_eq_sum S C α γ r hr)

end GeneralForms

section PathOperations
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

/-- Changing a curve away from its parameter germ changes neither smoothness
nor its representation of an intrinsic tangent vector. -/
theorem curveSmoothAt_congr (p : M) (side : CurveSide) (c d : ℝ → M)
    (hc : CurveSmoothAt S p side c)
    (he : d =ᶠ[𝓝[curveParameterSet side] 0] c) (h0 : d 0 = c 0) :
    CurveSmoothAt S p side d := by
  refine ⟨h0.trans hc.1, hc.2.1.congr_of_eventuallyEq he h0, ?_⟩
  intro e he' hp
  obtain ⟨U, hU, h0U, F, hF, heF⟩ := hc.2.2 e he' hp
  exact ⟨U, hU, h0U, F, hF, (he.fun_comp (fun y => (e y).val)).trans heF⟩

theorem curveRepresents_congr (p : M) (side : CurveSide) (c d : ℝ → M)
    (he : d =ᶠ[𝓝[curveParameterSet side] 0] c) (h0 : d 0 = c 0)
    (v : TangentSpace S p) :
    CurveRepresentsDerivation S p side c v ↔ CurveRepresentsDerivation S p side d v := by
  suffices ∀ (c d : ℝ → M), d =ᶠ[𝓝[curveParameterSet side] 0] c → d 0 = c 0 →
      CurveRepresentsDerivation S p side c v → CurveRepresentsDerivation S p side d v by
    exact ⟨this c d he h0, this d c he.symm h0.symm⟩
  intro c d he h0 hc
  refine ⟨curveSmoothAt_congr S p side c d hc.1 he h0, ?_⟩
  intro g f hf
  exact (hc.2 g f hf).congr_of_eventuallyEq
    (he.fun_comp f) (congrArg f h0)

theorem coefficient_congr_of_eventuallyEq (α : CovectorField S)
    (γ η : ℝ → M) (t : ℝ) (he : γ =ᶠ[𝓝 t] η) :
    coefficient S α γ t = coefficient S α η t := by
  classical
  have hp : γ t = η t := he.self_of_nhds
  have ht : Tendsto (fun h : ℝ => t+h) (𝓝 (0 : ℝ)) (𝓝 t) := by
    convert (continuous_const.add continuous_id : Continuous (fun h : ℝ => t+h)).tendsto (0 : ℝ) using 1 <;> simp
  have hcurve : (fun h => η (t+h)) =ᶠ[𝓝[curveParameterSet CurveSide.twoSided] 0]
      (fun h => γ (t+h)) := by
    simpa only [curveParameterSet, TangentData.curveParameterSet, nhdsWithin_univ, Function.comp_def] using
      he.symm.comp_tendsto ht
  have hpred : (fun v : TangentSpace S (η t) => CurveRepresentsDerivation S (η t)
      .twoSided (fun h => γ (t+h)) v) =
      (fun v => CurveRepresentsDerivation S (η t) .twoSided (fun h => η (t+h)) v) := by
    funext v
    exact propext (curveRepresents_congr S (η t) .twoSided _ _ hcurve (by simpa using hp.symm) v)
  unfold coefficient velocity
  rw [hp]
  change α (η t) (if h : ∃ v, (fun v : TangentSpace S (η t) =>
    CurveRepresentsDerivation S (η t) .twoSided (fun h => γ (t+h)) v) v
    then h.choose else 0) = _
  rw [hpred]

/-- The translated parameter approaches the original closed interval from
exactly the selected side. -/
theorem add_tendsto_interval {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    Tendsto (fun h : ℝ => t+h) (𝓝[curveParameterSet (sideAt a b t)] 0) (𝓝[Icc a b] t) := by
  have hc : Tendsto (fun h : ℝ => t+h) (𝓝[curveParameterSet (sideAt a b t)] 0) (𝓝 t) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    convert (continuous_const.add continuous_id : Continuous (fun h : ℝ => t+h)).tendsto (0 : ℝ) using 1 <;> simp
  refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
  classical
  by_cases hta : t = a
  · subst t
    simp only [sideAt, ite_true, curveParameterSet, TangentData.curveParameterSet]
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (Iio_mem_nhds (show (0 : ℝ) < b-a by linarith))] with h hh hh'
    exact ⟨by simp only [mem_Ici] at hh; linarith, by simp only [mem_Iio] at hh'; linarith⟩
  · by_cases htb : t = b
    · subst t
      simp only [sideAt, ite_eq_right hta, ite_true, curveParameterSet, TangentData.curveParameterSet]
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
        (Ioi_mem_nhds (show a-b < (0 : ℝ) by linarith))] with h hh hh'
      exact ⟨by simp only [mem_Ioi] at hh'; linarith, by simp only [mem_Iic] at hh; linarith⟩
    · simp only [sideAt, ite_eq_right hta, ite_eq_right htb, curveParameterSet,
        TangentData.curveParameterSet, nhdsWithin_univ]
      filter_upwards [Ioo_mem_nhds (show a-t < 0 by have := lt_of_le_of_ne ht.1 (Ne.symm hta); linarith)
        (show (0 : ℝ) < b-t by have := lt_of_le_of_ne ht.2 htb; linarith)] with h hh
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem smoothOnInterval_congr (γ η : ℝ → M) {a b : ℝ}
    (hγ : SmoothOnInterval S γ a b) (he : EqOn η γ (Icc a b)) :
    SmoothOnInterval S η a b := by
  refine ⟨hγ.1, hγ.2.1.congr he, ?_⟩
  intro t ht hab
  have hpoint := he ht
  rw [hpoint]
  apply curveSmoothAt_congr S (γ t) (sideAt a b t) _ _ (hγ.2.2 t ht hab)
  · exact (he.eventuallyEq_nhdsWithin).comp_tendsto (add_tendsto_interval hab ht)
  · simpa using hpoint

end PathOperations

namespace Subdivision
variable {a b c : ℝ}

/-- Append subdivisions without repeating their common endpoint. -/
noncomputable def append (s : PathIntegrationData.Subdivision a b)
    (r : PathIntegrationData.Subdivision b c) : PathIntegrationData.Subdivision a c where
  count := s.count + r.count
  point i := if i ≤ s.count then s.point i else r.point (i-s.count)
  first := by simp [s.first]
  last := by
    by_cases hr : r.count = 0
    · simp [hr, s.last, ← r.last, r.first]
    · simp [show ¬s.count + r.count ≤ s.count by omega, r.last]
  increasing := by
    intro i hi j hj hij
    simp only [mem_Icc] at hi hj
    dsimp
    split_ifs with his hjs hjs
    · exact s.increasing ⟨Nat.zero_le _, his⟩ ⟨Nat.zero_le _, hjs⟩ hij
    · have hs := point_mem s his
      have hr : r.point 0 < r.point (j-s.count) :=
        r.increasing ⟨Nat.zero_le _, Nat.zero_le _⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
      rw [r.first] at hr
      exact hs.2.trans_lt hr
    · omega
    · exact r.increasing ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)

@[simp] theorem append_point_left (s : PathIntegrationData.Subdivision a b)
    (r : PathIntegrationData.Subdivision b c) {i : ℕ} (hi : i ≤ s.count) :
    (append s r).point i = s.point i := by simp [append, hi]

@[simp] theorem append_point_right (s : PathIntegrationData.Subdivision a b)
    (r : PathIntegrationData.Subdivision b c) {i : ℕ} (hi : s.count ≤ i) :
    (append s r).point i = r.point (i-s.count) := by
  by_cases h : i = s.count
  · subst i
    simp [append, s.last, r.first]
  · simp [append, show ¬i ≤ s.count by omega]

end Subdivision

section Concatenation
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

theorem continuousOn_of_smoothPieces (γ : ℝ → M) {a b : ℝ}
    (s : PathIntegrationData.Subdivision a b)
    (hs : ∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i+1))) :
    ContinuousOn γ (Icc a b) := by
  have hcont (m : ℕ) (hm : m ≤ s.count) :
      ContinuousOn γ (Icc (s.point 0) (s.point m)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hm' : m < s.count := by omega
      have hu := (ih hm'.le).union_of_isClosed (hs m hm').2.1 isClosed_Icc isClosed_Icc
      rwa [Icc_union_Icc_eq_Icc
        (Subdivision.point_le_point s (Nat.zero_le _) hm'.le (Nat.zero_le _))
        (Subdivision.start_lt_end s hm').le] at hu
  simpa only [s.first, s.last] using hcont s.count le_rfl

theorem piecewiseSmoothOn_of_smoothPieces (γ : ℝ → M) {a b : ℝ}
    (s : PathIntegrationData.Subdivision a b)
    (hs : ∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i+1))) :
    PiecewiseSmoothOn S γ a b :=
  ⟨Subdivision.le s, continuousOn_of_smoothPieces S γ s hs, s, hs⟩

theorem concatenate_eq_left (γ η : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    EqOn (concatenate γ η b) γ (Icc a b) := by
  intro t ht
  simp only [concatenate, if_pos ht.2]

theorem concatenate_eq_right (γ η : ℝ → M) {b c : ℝ} (hjoin : γ b = η b) :
    EqOn (concatenate γ η b) η (Icc b c) := by
  intro t ht
  by_cases h : t = b
  · subst t
    simpa only [concatenate, if_pos le_rfl] using hjoin
  · simp only [concatenate, if_neg (show ¬ t ≤ b by have := ht.1; order)]

theorem concatenate_piecewiseSmoothOn (γ η : ℝ → M) {a b c : ℝ}
    (hγ : PiecewiseSmoothOn S γ a b) (hη : PiecewiseSmoothOn S η b c)
    (hjoin : γ b = η b) : PiecewiseSmoothOn S (concatenate γ η b) a c := by
  obtain ⟨s, hs⟩ := hγ.2.2
  obtain ⟨r, hr⟩ := hη.2.2
  apply piecewiseSmoothOn_of_smoothPieces S _ (Subdivision.append s r)
  intro i hi
  change i < s.count + r.count at hi
  by_cases his : i < s.count
  · rw [Subdivision.append_point_left s r (i := i) his.le,
      Subdivision.append_point_left s r (i := i+1) his]
    apply smoothOnInterval_congr S γ _ (hs i his)
    apply (concatenate_eq_left γ η hγ.1).mono
    exact Icc_subset_Icc (Subdivision.point_mem s his.le).1
      (Subdivision.point_mem s his).2
  · have hir : i-s.count < r.count := by omega
    rw [Subdivision.append_point_right s r (i := i) (by omega),
      Subdivision.append_point_right s r (i := i+1) (by omega)]
    rw [show i+1-s.count = (i-s.count)+1 by omega]
    apply smoothOnInterval_congr S η _ (hr (i-s.count) hir)
    apply (concatenate_eq_right γ η hjoin).mono
    exact Icc_subset_Icc (Subdivision.point_mem r hir.le).1
      (Subdivision.point_mem r hir).2

theorem pathIntegral_congr (α : CovectorField S) (γ η : ℝ → M) {a b : ℝ}
    (hab : a ≤ b) (he : EqOn γ η (Icc a b)) :
    pathIntegral S α γ a b = pathIntegral S α η a b := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  apply coefficient_congr_of_eventuallyEq S α γ η t
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
  exact he ⟨hy.1.le, hy.2.le⟩

theorem concatenation (C : CotangentBundle S) (α : OneForm C)
    (γ η : ℝ → M) (a b c : ℝ)
    (hγ : PiecewiseSmoothOn S γ a b) (hη : PiecewiseSmoothOn S η b c)
    (hjoin : γ b = η b) :
    PiecewiseSmoothOn S (concatenate γ η b) a c ∧
      pathIntegral S α.field (concatenate γ η b) a c =
        pathIntegral S α.field γ a b + pathIntegral S α.field η b c := by
  have hc := concatenate_piecewiseSmoothOn S γ η hγ hη hjoin
  refine ⟨hc, ?_⟩
  have hi := coefficient_integrable S C α (concatenate γ η b) a c hc
  have hsplit := pathIntegral_add_adjacent S α.field (concatenate γ η b) a b c
    (hi.mono_set (uIcc_subset_uIcc (show a ∈ uIcc a c by simp)
      (by rw [uIcc_of_le hc.1]; exact ⟨hγ.1, hη.1⟩)))
    (hi.mono_set (uIcc_subset_uIcc
      (by rw [uIcc_of_le hc.1]; exact ⟨hγ.1, hη.1⟩) (by simp)))
  rw [← hsplit, pathIntegral_congr S α.field _ γ hγ.1 (concatenate_eq_left γ η hγ.1),
    pathIntegral_congr S α.field _ η hη.1 (concatenate_eq_right γ η hjoin)]

end Concatenation

/-- Exchange forward and backward parameter sides. -/
def oppositeSide : CurveSide → CurveSide
  | .twoSided => .twoSided
  | .forward => .backward
  | .backward => .forward

section Reflection
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

theorem curveSmoothAt_neg (p : M) (side : CurveSide) (c : ℝ → M)
    (hc : CurveSmoothAt S p (oppositeSide side) c) :
    CurveSmoothAt S p side (fun h => c (-h)) := by
  have hmap : MapsTo (fun h : ℝ => -h) (curveParameterSet side)
      (curveParameterSet (oppositeSide side)) := by
    cases side <;> simp [oppositeSide, curveParameterSet, TangentData.curveParameterSet, MapsTo]
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[curveParameterSet side] 0)
      (𝓝[curveParameterSet (oppositeSide side)] 0) := by
    simpa only [neg_zero] using (continuous_neg.continuousWithinAt (x := (0 : ℝ))).tendsto_nhdsWithin hmap
  refine ⟨by simpa only [neg_zero] using hc.1, ?_, ?_⟩
  · change Tendsto (fun h => c (-h)) _ (𝓝 (c (-0)))
    simpa only [neg_zero, hc.1, Function.comp_def] using hc.2.1.tendsto.comp hneg
  · intro e he hp
    obtain ⟨U, hU, h0U, F, hF, heF⟩ := hc.2.2 e he hp
    refine ⟨(fun h : ℝ => -h) ⁻¹' U, hU.preimage continuous_neg,
      by simpa only [mem_preimage, neg_zero] using h0U,
      fun h => F (-h), hF.comp contDiff_neg.contDiffOn (mapsTo_preimage _ _), ?_⟩
    exact heF.comp_tendsto hneg

theorem smoothOnInterval_reflect (γ : ℝ → M) {a b : ℝ}
    (hγ : SmoothOnInterval S γ a b) (q : ℝ) :
    SmoothOnInterval S (fun t => γ (q-t)) (q-b) (q-a) := by
  have hmap : MapsTo (fun t : ℝ => q-t) (Icc (q-b) (q-a)) (Icc a b) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨by linarith [hγ.1],
    hγ.2.1.comp (continuous_const.sub continuous_id).continuousOn hmap, ?_⟩
  intro t ht hab
  have hlt : a < b := by linarith
  have hside : oppositeSide (sideAt (q-b) (q-a) t) = sideAt a b (q-t) := by
    classical
    by_cases htb : t = q-b
    · have hne : q-t ≠ a := by linarith
      simp [sideAt, htb, oppositeSide, hne, ne_of_gt hlt, show q-(q-b) = b by ring]
    · by_cases hta : t = q-a
      · simp [sideAt, htb, hta, oppositeSide, ne_of_lt hlt, show q-(q-a) = a by ring]
      · have hne₁ : q-t ≠ a := by intro h; apply hta; linarith
        have hne₂ : q-t ≠ b := by intro h; apply htb; linarith
        simp [sideAt, htb, hta, hne₁, hne₂, oppositeSide]
  have hc := hγ.2.2 (q-t) (hmap ht) hlt
  rw [← hside] at hc
  have hn := curveSmoothAt_neg S (γ (q-t)) (sideAt (q-b) (q-a) t)
    (fun h => γ (q-t+h)) hc
  convert hn using 1 <;> congr 1 <;> funext h <;> congr 1 <;> ring

theorem pathIntegral_reflect_smoothPiece (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) {a b : ℝ} (hγ : SmoothOnInterval S γ a b) (q : ℝ) :
    pathIntegral S α.field (fun t => γ (q-t)) (q-b) (q-a) =
      -pathIntegral S α.field γ a b := by
  by_cases hab : a = b
  · subst b
    simp
  have hlt : a < b := lt_of_le_of_ne hγ.1 hab
  have hr := smoothOnInterval_reflect S γ hγ q
  change (∫ t in (q-b)..(q-a), coefficient S α.field (fun t => γ (q-t)) t) = _
  calc
    _ = ∫ t in (q-b)..(q-a), -coefficient S α.field γ (q-t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hr.1
      intro t ht
      have ho := smoothOnInterval_interior S γ hγ
        (show q-t ∈ Ioo a b from ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      have hc := smoothOnInterval_interior S (fun t => γ (q-t)) hr ht
      have hd : HasDerivAt (fun t : ℝ => q-t) (-1) t := by
        convert (hasDerivAt_const t q).sub (hasDerivAt_id t) using 1 <;> first | rfl | norm_num
      simpa only [neg_one_mul, Function.comp_def] using coefficient_comp S α.field γ (fun t => q-t) t (-1) ho hc hd
    _ = -(∫ t in (q-b)..(q-a), coefficient S α.field γ (q-t)) := intervalIntegral.integral_neg
    _ = -pathIntegral S α.field γ a b := by
      rw [intervalIntegral.integral_comp_sub_left]
      congr 1 <;> congr 1 <;> ring

end Reflection

namespace Subdivision
variable {a b : ℝ}

/-- Reflect a subdivision, listing its points in the opposite order. -/
noncomputable def reflect (s : PathIntegrationData.Subdivision a b) (q : ℝ) :
    PathIntegrationData.Subdivision (q-b) (q-a) where
  count := s.count
  point i := q - s.point (s.count-i)
  first := by simp [s.last]
  last := by simp [s.first]
  increasing := by
    intro i hi j hj hij
    have h := s.increasing
      (show s.count-j ∈ Icc 0 s.count from ⟨Nat.zero_le _, Nat.sub_le _ _⟩)
      (show s.count-i ∈ Icc 0 s.count from ⟨Nat.zero_le _, Nat.sub_le _ _⟩)
      (show s.count-j < s.count-i by have := hj.2; omega)
    dsimp
    linarith

end Subdivision

section Reversal
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

theorem reflect_smoothPieces (γ : ℝ → M) {a b : ℝ}
    (s : PathIntegrationData.Subdivision a b)
    (hs : ∀ i < s.count, SmoothOnInterval S γ (s.point i) (s.point (i+1))) (q : ℝ) :
    ∀ i < (Subdivision.reflect s q).count,
      SmoothOnInterval S (fun t => γ (q-t))
        ((Subdivision.reflect s q).point i) ((Subdivision.reflect s q).point (i+1)) := by
  intro i hi
  change i < s.count at hi
  have hj : s.count-(i+1) < s.count := by omega
  have h := smoothOnInterval_reflect S γ (hs _ hj) q
  simpa only [Subdivision.reflect, show s.count-(i+1)+1 = s.count-i by omega] using h

theorem reversal (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) (a b : ℝ) (hγ : PiecewiseSmoothOn S γ a b) :
    PiecewiseSmoothOn S (reverse γ a b) a b ∧
      pathIntegral S α.field (reverse γ a b) a b = -pathIntegral S α.field γ a b := by
  obtain ⟨s, hs⟩ := hγ.2.2
  have ha : a+b-b = a := by ring
  have hb : a+b-a = b := by ring
  have hr := reflect_smoothPieces S γ s hs (a+b)
  have hc := piecewiseSmoothOn_of_smoothPieces S _ _ hr
  refine ⟨?_, ?_⟩
  · change PiecewiseSmoothOn S (fun t => γ (a+b-t)) a b
    simpa only [ha, hb] using hc
  have hsum := integral_eq_sum S C α (fun t => γ (a+b-t)) (Subdivision.reflect s (a+b)) hr
  conv_lhs at hsum => rw [ha, hb]
  change pathIntegral S α.field (fun t => γ (a+b-t)) a b = _
  rw [hsum, integral_eq_sum S C α γ s hs]
  change (∑ i ∈ Finset.range s.count, pieceIntegral S α.field (fun t => γ (a+b-t))
    ((Subdivision.reflect s (a+b)).point i) ((Subdivision.reflect s (a+b)).point (i+1))) = _
  calc
    _ = ∑ i ∈ Finset.range s.count, -pieceIntegral S α.field γ
        (s.point (s.count-(i+1))) (s.point (s.count-(i+1)+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hj : s.count-(i+1) < s.count := by omega
      rw [pieceIntegral_eq S _ _ (hr i hi').1,
        pieceIntegral_eq S _ _ (hs _ hj).1]
      have hh := pathIntegral_reflect_smoothPiece S C α γ (hs _ hj) (a+b)
      simpa only [Subdivision.reflect, show s.count-(i+1)+1 = s.count-i by omega] using hh
    _ = -subdivisionIntegral S α.field γ s := by
      change _ = -(∑ i ∈ Finset.range s.count, pieceIntegral S α.field γ (s.point i) (s.point (i+1)))
      rw [Finset.sum_neg_distrib]
      apply congrArg Neg.neg
      simpa only [Nat.sub_sub, Nat.add_comm 1] using
        Finset.sum_range_reflect (fun i => pieceIntegral S α.field γ (s.point i) (s.point (i+1))) s.count

end Reversal

namespace Subdivision
variable {a b : ℝ}

/-- If a nontrivial interval contains no subdivision point in its interior,
it lies in a single subdivision piece. -/
theorem exists_piece_containing (s : PathIntegrationData.Subdivision a b)
    {x y : ℝ} (hxy : x < y) (hx : a ≤ x) (hy : y ≤ b)
    (havoid : ∀ j ≤ s.count, s.point j ∉ Ioo x y) :
    ∃ j < s.count, s.point j ≤ x ∧ y ≤ s.point (j+1) := by
  have hex : ∃ j : ℕ, x < s.point j := ⟨s.count, by rw [s.last]; linarith⟩
  let j := Nat.find hex
  have hj : x < s.point j := Nat.find_spec hex
  have hjle : j ≤ s.count := Nat.find_min' hex (by rw [s.last]; linarith)
  have hjpos : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz, s.first] at hj
    linarith
  have hprev : s.point (j-1) ≤ x := le_of_not_gt (Nat.find_min hex (by omega))
  have hyj : y ≤ s.point j := le_of_not_gt (fun hh => havoid j hjle ⟨hj, hh⟩)
  exact ⟨j-1, by omega, hprev, by simpa only [Nat.sub_add_cancel hjpos] using hyj⟩

noncomputable def ofFinset (F : Finset ℝ) (ha : a ∈ F) (hb : b ∈ F)
    (hF : ∀ x ∈ F, x ∈ Icc a b) : PathIntegrationData.Subdivision a b := by
  classical
  have hpos : 0 < F.card := Finset.card_pos.mpr ⟨a, ha⟩
  let e : Fin F.card ↪o ℝ := F.orderEmbOfFin rfl
  have hemem (i : Fin F.card) : e i ∈ F := F.orderEmbOfFin_mem rfl i
  have hesurj (x : ℝ) (hx : x ∈ F) : ∃ i, e i = x := by
    change x ∈ (F : Set ℝ) at hx
    rw [← F.range_orderEmbOfFin rfl] at hx
    exact hx
  refine ⟨F.card-1, fun i => if hi : i < F.card then e ⟨i, hi⟩ else b, ?_, ?_, ?_⟩
  · simp only [hpos, dite_true]
    apply le_antisymm
    · obtain ⟨i, hi⟩ := hesurj a ha
      rw [← hi]
      exact e.monotone (show (⟨0, hpos⟩ : Fin F.card) ≤ i from Nat.zero_le _)
    · exact (hF _ (hemem _)).1
  · simp only [Nat.sub_lt hpos (by omega : 0 < 1), dite_true]
    apply le_antisymm
    · exact (hF _ (hemem _)).2
    · obtain ⟨i, hi⟩ := hesurj b hb
      rw [← hi]
      exact e.monotone (show i ≤ (⟨F.card-1, by omega⟩ : Fin F.card) from Nat.le_sub_one_of_lt i.isLt)
  · intro i hi j hj hij
    have hi' : i < F.card := by have := hi.2; omega
    have hj' : j < F.card := by have := hj.2; omega
    simp only [hi', hj', dite_true]
    exact e.strictMono hij

theorem ofFinset_point (F : Finset ℝ) (ha : a ∈ F) (hb : b ∈ F)
    (hF : ∀ x ∈ F, x ∈ Icc a b) {i : ℕ} (hi : i ≤ (ofFinset F ha hb hF).count) :
    (ofFinset F ha hb hF).point i = F.orderEmbOfFin rfl ⟨i, by
      have hpos : 0 < F.card := Finset.card_pos.mpr ⟨a, ha⟩
      change i ≤ F.card-1 at hi
      omega⟩ := by
  dsimp [ofFinset]
  rw [dif_pos]

theorem ofFinset_avoids (F : Finset ℝ) (ha : a ∈ F) (hb : b ∈ F)
    (hF : ∀ x ∈ F, x ∈ Icc a b) {i : ℕ} (hi : i < (ofFinset F ha hb hF).count) :
    ∀ z ∈ F, z ∉ Ioo ((ofFinset F ha hb hF).point i)
      ((ofFinset F ha hb hF).point (i+1)) := by
  intro z hz hzint
  rw [ofFinset_point _ _ _ _ hi.le, ofFinset_point _ _ _ _ hi] at hzint
  change z ∈ (F : Set ℝ) at hz
  rw [← F.range_orderEmbOfFin rfl] at hz
  obtain ⟨j, rfl⟩ := hz
  have h₁ := (F.orderEmbOfFin rfl).lt_iff_lt.mp hzint.1
  have h₂ := (F.orderEmbOfFin rfl).lt_iff_lt.mp hzint.2
  have := j.isLt
  change i < j.val at h₁
  change j.val < i+1 at h₂
  omega

/-- A common refinement, with every refined closed piece contained in a
closed piece of either original subdivision. -/
theorem common_refinement (s r : PathIntegrationData.Subdivision a b) :
    ∃ t : PathIntegrationData.Subdivision a b,
      ∀ i < t.count,
        (∃ j < s.count, s.point j ≤ t.point i ∧ t.point (i+1) ≤ s.point (j+1)) ∧
        (∃ j < r.count, r.point j ≤ t.point i ∧ t.point (i+1) ≤ r.point (j+1)) := by
  classical
  let F := (Finset.range (s.count+1)).image s.point ∪
    (Finset.range (r.count+1)).image r.point
  have hsmem {i : ℕ} (hi : i ≤ s.count) : s.point i ∈ F :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
  have hrmem {i : ℕ} (hi : i ≤ r.count) : r.point i ∈ F :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
  have ha : a ∈ F := s.first ▸ hsmem (Nat.zero_le _)
  have hb : b ∈ F := s.last ▸ hsmem le_rfl
  have hF : ∀ x ∈ F, x ∈ Icc a b := by
    intro x hx
    rcases Finset.mem_union.mp hx with hs | hr
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      exact point_mem s (by have := Finset.mem_range.mp hi; omega)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
      exact point_mem r (by have := Finset.mem_range.mp hi; omega)
  let t := ofFinset F ha hb hF
  refine ⟨t, ?_⟩
  intro i hi
  have hxy := start_lt_end t hi
  have hx := (point_mem t hi.le).1
  have hy := (point_mem t hi).2
  have hav := ofFinset_avoids F ha hb hF hi
  exact ⟨exists_piece_containing s hxy hx hy (fun j hj => hav _ (hsmem hj)),
    exists_piece_containing r hxy hx hy (fun j hj => hav _ (hrmem hj))⟩

end Subdivision

section Composition
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

theorem scalarSmoothOnInterval_contDiffOn (φ : ℝ → ℝ) {a b : ℝ}
    (hφ : ScalarSmoothOnInterval φ a b) : ContDiffOn ℝ (⊤ : ℕ∞) φ (Icc a b) := by
  intro t ht
  obtain ⟨U, hU, htU, F, hF, heF⟩ := hφ.2 t ht
  apply (hF.contDiffAt (hU.mem_nhds htU)).contDiffWithinAt.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds htU), self_mem_nhdsWithin] with y hy hy'
  exact (heF ⟨hy, hy'⟩).symm

theorem scalarSmoothOnInterval_mono (φ : ℝ → ℝ) {a b c d : ℝ}
    (hφ : ScalarSmoothOnInterval φ a b) (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b) :
    ScalarSmoothOnInterval φ c d := by
  refine ⟨hcd, ?_⟩
  intro t ht
  obtain ⟨U, hU, htU, F, hF, heF⟩ := hφ.2 t (hsub ht)
  exact ⟨U, hU, htU, F, hF, heF.mono (inter_subset_inter_right U hsub)⟩

theorem smoothOnInterval_const (p : M) {a b : ℝ} (hab : a ≤ b) :
    SmoothOnInterval S (fun _ => p) a b := by
  refine ⟨hab, continuous_const.continuousOn, ?_⟩
  intro t ht _
  exact ⟨rfl, continuous_const.continuousWithinAt,
    fun e _ _ => ⟨univ, isOpen_univ, mem_univ _, fun _ => (e p).val,
      contDiffOn_const, Filter.EventuallyEq.rfl⟩⟩

/-- Composition of closed smooth pieces needs only a map of their intervals.
The ambient coordinate extensions can leave the model across an endpoint. -/
theorem smoothOnInterval_comp (γ : ℝ → M) (φ : ℝ → ℝ) {a b c d : ℝ}
    (hγ : SmoothOnInterval S γ a b) (hφ : ScalarSmoothOnInterval φ c d)
    (hmap : MapsTo φ (Icc c d) (Icc a b)) :
    SmoothOnInterval S (γ ∘ φ) c d := by
  by_cases hab : a = b
  · subst b
    apply smoothOnInterval_congr S (fun _ => γ a) (γ ∘ φ) (smoothOnInterval_const S _ hφ.1)
    intro t ht
    have hh : φ t = a := le_antisymm (hmap ht).2 (hmap ht).1
    simp only [Function.comp_apply, hh]
  have hlt : a < b := lt_of_le_of_ne hγ.1 hab
  have hφc := (scalarSmoothOnInterval_contDiffOn φ hφ).continuousOn
  refine ⟨hφ.1, hγ.2.1.comp hφc hmap, ?_⟩
  intro t ht hcd
  have htrans := add_tendsto_interval hcd ht
  have hδ : Tendsto (fun h => φ (t+h) - φ t)
      (𝓝[curveParameterSet (sideAt c d t)] 0)
      (𝓝[curveParameterSet (sideAt a b (φ t))] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh := ((hφc t ht).tendsto.comp htrans).sub (tendsto_const_nhds (x := φ t))
      simpa only [sub_self, Function.comp_def] using hh
    · filter_upwards [htrans.eventually self_mem_nhdsWithin] with h hh
      exact sub_mapsTo_side (hmap ht) (hmap hh)
  have hgc := hγ.2.2 (φ t) (hmap ht) hlt
  refine ⟨by simp, ?_, ?_⟩
  · have hh := hgc.2.1.tendsto.comp hδ
    simp only [ContinuousWithinAt, Function.comp_def, add_zero]
    convert hh using 1 <;> simp [Function.comp_def]
  · intro e he hp
    obtain ⟨U, hU, htU, F, hF, heF⟩ := hφ.2 t ht
    obtain ⟨V, hV, h0V, G, hG, heG⟩ := hgc.2.2 e he hp
    let A : Set ℝ := (fun h : ℝ => t+h) ⁻¹' U
    let P : ℝ → ℝ := fun h => F (t+h) - φ t
    have hA : IsOpen A := hU.preimage (continuous_const.add continuous_id)
    have h0A : (0 : ℝ) ∈ A := by simpa only [A, mem_preimage, add_zero] using htU
    have hP : ContDiffOn ℝ (⊤ : ℕ∞) P A :=
      (hF.comp (contDiff_const.add contDiff_id).contDiffOn (mapsTo_preimage _ _)).sub contDiffOn_const
    have hP0 : P 0 = 0 := by
      dsimp [P]
      rw [add_zero, heF ⟨htU, ht⟩, sub_self]
    let W : Set ℝ := A ∩ P ⁻¹' V
    have hW : IsOpen W := hP.continuousOn.isOpen_inter_preimage hA hV
    have h0W : (0 : ℝ) ∈ W := ⟨h0A, by rw [mem_preimage, hP0]; exact h0V⟩
    refine ⟨W, hW, h0W, fun h => G (P h),
      hG.comp (hP.mono inter_subset_left) (fun h hh => hh.2), ?_⟩
    have hEq : ∀ᶠ h in 𝓝[curveParameterSet (sideAt c d t)] 0,
        F (t+h) = φ (t+h) := by
      filter_upwards [htrans.eventually self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hA.mem_nhds h0A)] with h hh hh'
      exact heF ⟨hh', hh⟩
    filter_upwards [heG.comp_tendsto hδ, hEq] with h hg hf
    change (e (γ (φ (t+h)))).val = G (F (t+h)-φ t)
    rw [hf]
    simpa [Function.comp_def] using hg

end Composition

section ReparametrizationIntervals

 theorem reparametrization_endpoints (φ : ℝ → ℝ) {a b c d : ℝ}
    (hφ : IsReparametrization φ c d a b) :
    φ c = a ∧ φ d = b := by
  have hcd := hφ.2.1.1
  have hmap : MapsTo φ (Icc c d) (Icc a b) := by
    intro t ht
    rw [← hφ.2.2.2]
    exact ⟨t, ht, rfl⟩
  have hsurj (y : ℝ) (hy : y ∈ Icc a b) : ∃ t ∈ Icc c d, φ t = y := by
    rw [← hφ.2.2.2] at hy
    exact hy
  obtain ⟨x, hx, hxa⟩ := hsurj a ⟨le_rfl, hφ.1⟩
  obtain ⟨y, hy, hyb⟩ := hsurj b ⟨hφ.1, le_rfl⟩
  constructor
  · apply le_antisymm _ (hmap ⟨le_rfl, hcd⟩).1
    rw [← hxa]
    exact hφ.2.2.1 ⟨le_rfl, hcd⟩ hx hx.1
  · apply le_antisymm (hmap ⟨hcd, le_rfl⟩).2
    rw [← hyb]
    exact hφ.2.2.1 hy ⟨hcd, le_rfl⟩ hy.2

/-- Choose ordered preimages of the path's subdivision points. Monotonicity,
not injectivity, makes preimages of distinct values strictly ordered. -/
theorem preimage_subdivision (φ : ℝ → ℝ) {a b c d : ℝ}
    (hφ : IsReparametrization φ c d a b) (hab : a < b)
    (s : PathIntegrationData.Subdivision a b) :
    ∃ r : PathIntegrationData.Subdivision c d, r.count = s.count ∧
      ∀ i ≤ s.count, φ (r.point i) = s.point i := by
  classical
  have hcd := hφ.2.1.1
  obtain ⟨hstart, hend⟩ := reparametrization_endpoints φ hφ
  have hcount : 0 < s.count := by
    by_contra h
    have hs : s.count = 0 := by omega
    have := s.last
    rw [hs, s.first] at this
    linarith
  have hex (i : ℕ) (hi : i ≤ s.count) : ∃ t ∈ Icc c d, φ t = s.point i := by
    have hmem := Subdivision.point_mem s hi
    rw [← hφ.2.2.2] at hmem
    exact hmem
  let p (i : ℕ) : ℝ := if i = 0 then c else if i = s.count then d
    else if hi : i ≤ s.count then (hex i hi).choose else c
  have hp (i : ℕ) (hi : i ≤ s.count) : p i ∈ Icc c d ∧ φ (p i) = s.point i := by
    dsimp [p]
    split_ifs with h0 hn
    · subst i
      exact ⟨⟨le_rfl, hcd⟩, hstart.trans s.first.symm⟩
    · subst i
      exact ⟨⟨hcd, le_rfl⟩, hend.trans s.last.symm⟩
    · exact (hex i hi).choose_spec
  have hmono : StrictMonoOn p (Icc 0 s.count) := by
    intro i hi j hj hij
    by_contra h
    have hle := hφ.2.2.1 (hp j hj.2).1 (hp i hi.2).1 (le_of_not_gt h)
    rw [(hp j hj.2).2, (hp i hi.2).2] at hle
    exact (not_le_of_gt (s.increasing hi hj hij)) hle
  refine ⟨⟨s.count, p, by simp [p], by simp [p, Nat.ne_of_gt hcount], hmono⟩, rfl, ?_⟩
  exact fun i hi => (hp i hi).2

end ReparametrizationIntervals

section ReparametrizationPieces
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

/-- A finite subdivision on which the scalar map and the target path are
simultaneously represented by single smooth pieces. -/
theorem reparametrization_pieces (γ : ℝ → M) (φ : ℝ → ℝ) {a b c d : ℝ}
    (hγ : PiecewiseSmoothOn S γ a b) (hφ : IsReparametrization φ c d a b) (hab : a < b) :
    ∃ t : PathIntegrationData.Subdivision c d, ∀ i < t.count,
      ∃ x y : ℝ, SmoothOnInterval S γ x y ∧
        ScalarSmoothOnInterval φ (t.point i) (t.point (i+1)) ∧
        MapsTo φ (Icc (t.point i) (t.point (i+1))) (Icc x y) := by
  obtain ⟨s, hs⟩ := hγ.2.2
  obtain ⟨r, hr, hrφ⟩ := preimage_subdivision φ hφ hab s
  obtain ⟨v, hv⟩ := hφ.2.1.2.2
  obtain ⟨t, ht⟩ := Subdivision.common_refinement r v
  refine ⟨t, ?_⟩
  intro i hi
  obtain ⟨⟨j, hj, hjx, hjy⟩, ⟨l, hl, hlx, hly⟩⟩ := ht i hi
  have hjs : j < s.count := by omega
  refine ⟨s.point j, s.point (j+1), hs j hjs,
    scalarSmoothOnInterval_mono φ (hv l hl) (Subdivision.start_lt_end t hi).le
      (Icc_subset_Icc hlx hly), ?_⟩
  intro z hz
  have hzt : z ∈ Icc c d :=
    Icc_subset_Icc (Subdivision.point_mem t hi.le).1 (Subdivision.point_mem t hi).2 hz
  have hleft := hφ.2.2.1 (Subdivision.point_mem r hj.le) hzt (hjx.trans hz.1)
  have hright := hφ.2.2.1 hzt (Subdivision.point_mem r hj) (hz.2.trans hjy)
  rw [hrφ j hjs.le] at hleft
  rw [hrφ (j+1) hjs] at hright
  exact ⟨hleft, hright⟩

end ReparametrizationPieces

section Substitution
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

@[simp] theorem velocity_const (p : M) (t : ℝ) :
    velocity S (fun _ => p) .twoSided t = 0 := by
  have hc : CurveSmoothAt S p .twoSided (fun _ => p) :=
    smoothOnInterval_interior S (fun _ => p) (t := (0 : ℝ))
      (smoothOnInterval_const S p (show (-1 : ℝ) ≤ 1 by norm_num)) (by norm_num)
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  obtain ⟨f, _, hfg⟩ := (mem_smoothGermAlgebra_iff S p g.val).mp g.property
  have hd := represented_hasDerivAt S (fun _ => p) t _ (velocity_spec S (fun _ => p) .twoSided t hc) g f hfg.symm
  exact hd.unique (hasDerivAt_const t (f p))

@[simp] theorem pathIntegral_const (α : CovectorField S) (p : M) (a b : ℝ) :
    pathIntegral S α (fun _ => p) a b = 0 := by
  simp only [pathIntegral, coefficient, velocity_const, map_zero, intervalIntegral.integral_zero]

/-- The chain rule through one-sided target endpoints. It includes a scalar
map which is constant on a whole subinterval. -/
theorem velocity_comp_within (γ : ℝ → M) (φ : ℝ → ℝ) {a b c d t r : ℝ}
    (hab : a < b) (hγ : SmoothOnInterval S γ a b)
    (hφ : ScalarSmoothOnInterval φ c d) (hmap : MapsTo φ (Icc c d) (Icc a b))
    (ht : t ∈ Ioo c d) (hdφ : HasDerivWithinAt φ r (Icc c d) t) :
    velocity S (γ ∘ φ) .twoSided t = r • velocity S γ (sideAt a b (φ t)) (φ t) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  obtain ⟨f, _, hfg⟩ := (mem_smoothGermAlgebra_iff S (γ (φ t)) g.val).mp g.property
  have ho := represented_hasDerivWithinAt S γ (hmap ⟨ht.1.le, ht.2.le⟩) _
    (velocity_spec S γ _ (φ t) (hγ.2.2 (φ t) (hmap ⟨ht.1.le, ht.2.le⟩) hab)) g f hfg.symm
  have hcomp := smoothOnInterval_comp S γ φ hγ hφ hmap
  have hc := represented_hasDerivAt S (γ ∘ φ) t _
    (velocity_spec S (γ ∘ φ) .twoSided t (smoothOnInterval_interior S _ hcomp ht)) g f hfg.symm
  have hout := (ho.comp t hdφ hmap).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hh := hc.unique hout
  change (velocity S (γ ∘ φ) .twoSided t).val g =
    r * (velocity S γ (sideAt a b (φ t)) (φ t)).val g
  exact hh.trans (mul_comm _ _)

/-- One-dimensional substitution on one pair of smooth pieces, without a
strict monotonicity or positive-derivative hypothesis. -/
theorem pathIntegral_substitution_smoothPieces (α : CovectorField S)
    (γ : ℝ → M) (φ : ℝ → ℝ) {a b c d : ℝ}
    (hγ : SmoothOnInterval S γ a b) (hφ : ScalarSmoothOnInterval φ c d)
    (hmap : MapsTo φ (Icc c d) (Icc a b)) (hmono : MonotoneOn φ (Icc c d)) :
    pathIntegral S α (γ ∘ φ) c d = pathIntegral S α γ (φ c) (φ d) := by
  have hcd := hφ.1
  have hends : φ c ≤ φ d := hmono ⟨le_rfl, hcd⟩ ⟨hcd, le_rfl⟩ hcd
  have hφdiff := scalarSmoothOnInterval_contDiffOn φ hφ
  have hdφ (t : ℝ) (ht : t ∈ Ioo c d) :
      HasDerivAt φ (derivWithin φ (Icc c d) t) t :=
    (hφdiff.differentiableOn (by simp) t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  by_cases hab : a = b
  · subst b
    have heq : EqOn (γ ∘ φ) (fun _ => γ a) (Icc c d) := by
      intro t ht
      simp only [Function.comp_apply, le_antisymm (hmap ht).2 (hmap ht).1]
    have hec := le_antisymm (hmap ⟨le_rfl, hcd⟩).2 (hmap ⟨le_rfl, hcd⟩).1
    have hed := le_antisymm (hmap ⟨hcd, le_rfl⟩).2 (hmap ⟨hcd, le_rfl⟩).1
    rw [pathIntegral_congr S α _ _ hcd heq, pathIntegral_const, hec, hed, pathIntegral_same]
  have hlt : a < b := lt_of_le_of_ne hγ.1 hab
  let f : ℝ → ℝ := fun u => α (γ u) (velocity S γ (sideAt a b u) u)
  have heq : pathIntegral S α (γ ∘ φ) c d =
      ∫ t in c..d, f (φ t) * derivWithin φ (Icc c d) t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hcd
    intro t ht
    unfold coefficient
    rw [velocity_comp_within S γ φ hlt hγ hφ hmap ht (hdφ t ht).hasDerivWithinAt, map_smul]
    exact mul_comm _ _
  rw [heq]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := φ) (f' := derivWithin φ (Icc c d)) (g := f)
    (by rw [uIcc_of_le hcd]; exact hφdiff.continuousOn)
    (by simpa only [min_eq_left hcd, max_eq_right hcd] using hdφ)
    (fun _ _ => hmono.derivWithin_nonneg)
  simp only [Function.comp_apply] at hsub
  rw [hsub]
  apply intervalIntegral.integral_congr_Ioo_of_le hends
  intro t ht
  have hta : t ≠ a := by have := (hmap ⟨le_rfl, hcd⟩).1; linarith [ht.1]
  have htb : t ≠ b := by have := (hmap ⟨hcd, le_rfl⟩).2; linarith [ht.2]
  simp only [f, coefficient, sideAt, ite_eq_right hta, ite_eq_right htb]

end Substitution

section Reparametrization
variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M)

theorem reparametrization (C : CotangentBundle S) (α : OneForm C)
    (γ : ℝ → M) (φ : ℝ → ℝ) (a b c d : ℝ)
    (hγ : PiecewiseSmoothOn S γ a b) (hφ : IsReparametrization φ c d a b) :
    PiecewiseSmoothOn S (γ ∘ φ) c d ∧
      pathIntegral S α.field (γ ∘ φ) c d = pathIntegral S α.field γ a b := by
  have hcd := hφ.2.1.1
  have hmap : MapsTo φ (Icc c d) (Icc a b) := by
    intro t ht
    rw [← hφ.2.2.2]
    exact ⟨t, ht, rfl⟩
  by_cases hab : a = b
  · subst b
    have heq : EqOn (γ ∘ φ) (fun _ => γ a) (Icc c d) := by
      intro t ht
      simp only [Function.comp_apply, le_antisymm (hmap ht).2 (hmap ht).1]
    obtain ⟨s, _⟩ := hφ.2.1.2.2
    refine ⟨piecewiseSmoothOn_of_smoothPieces S _ s (fun i hi => ?_), ?_⟩
    · apply smoothOnInterval_congr S (fun _ => γ a) _
        (smoothOnInterval_const S _ (Subdivision.start_lt_end s hi).le)
      exact heq.mono (Icc_subset_Icc (Subdivision.point_mem s hi.le).1 (Subdivision.point_mem s hi).2)
    · rw [pathIntegral_congr S α.field _ _ hcd heq, pathIntegral_const, pathIntegral_same]
  have hlt : a < b := lt_of_le_of_ne hγ.1 hab
  obtain ⟨s, hs⟩ := reparametrization_pieces S γ φ hγ hφ hlt
  have hscomp : ∀ i < s.count, SmoothOnInterval S (γ ∘ φ) (s.point i) (s.point (i+1)) := by
    intro i hi
    obtain ⟨x, y, hxy, hφ', hmap'⟩ := hs i hi
    exact smoothOnInterval_comp S γ φ hxy hφ' hmap'
  refine ⟨piecewiseSmoothOn_of_smoothPieces S _ s hscomp, ?_⟩
  rw [integral_eq_sum S C α (γ ∘ φ) s hscomp]
  change ∑ i ∈ Finset.range s.count, pieceIntegral S α.field (γ ∘ φ) (s.point i) (s.point (i+1)) = _
  have hsum : (∑ i ∈ Finset.range s.count, pathIntegral S α.field γ (φ (s.point i)) (φ (s.point (i+1)))) =
      pathIntegral S α.field γ (φ c) (φ d) := by
    have hi := coefficient_integrable S C α γ a b hγ
    have hi' (i : ℕ) (hi' : i < s.count) : IntervalIntegrable (coefficient S α.field γ)
        MeasureTheory.volume (φ (s.point i)) (φ (s.point (i+1))) := by
      apply hi.mono_set
      rw [uIcc_of_le hγ.1]
      exact uIcc_subset_Icc (hmap (Subdivision.point_mem s hi'.le)) (hmap (Subdivision.point_mem s hi'))
    simpa only [pathIntegral, s.first, s.last] using intervalIntegral.sum_integral_adjacent_intervals hi'
  calc
    _ = ∑ i ∈ Finset.range s.count, pathIntegral S α.field γ (φ (s.point i)) (φ (s.point (i+1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      obtain ⟨x, y, hxy, hφ', hmap'⟩ := hs i hi'
      rw [pieceIntegral_eq S _ _ (hscomp i hi').1]
      exact pathIntegral_substitution_smoothPieces S α.field γ φ hxy hφ' hmap'
        (hφ.2.2.1.mono (Icc_subset_Icc (Subdivision.point_mem s hi'.le).1 (Subdivision.point_mem s hi').2))
    _ = pathIntegral S α.field γ (φ c) (φ d) := hsum
    _ = pathIntegral S α.field γ a b := by
      rw [(reparametrization_endpoints φ hφ).1, (reparametrization_endpoints φ hφ).2]

end Reparametrization

noncomputable section
abbrev Subdivision := @PathIntegrationData.Subdivision
abbrev sideAt := @PathIntegrationData.sideAt
abbrev SmoothOnInterval := @PathIntegrationData.SmoothOnInterval
abbrev PiecewiseSmoothOn := @PathIntegrationData.PiecewiseSmoothOn
abbrev velocity := @PathIntegrationData.velocity
abbrev coefficient := @PathIntegrationData.coefficient
abbrev pathIntegral := @PathIntegrationData.pathIntegral
abbrev pieceIntegral := @PathIntegrationData.pieceIntegral
abbrev subdivisionIntegral := @PathIntegrationData.subdivisionIntegral
abbrev reverse := @PathIntegrationData.reverse
abbrev concatenate := @PathIntegrationData.concatenate
abbrev ScalarSmoothOnInterval := @PathIntegrationData.ScalarSmoothOnInterval
abbrev ScalarPiecewiseSmoothOn := @PathIntegrationData.ScalarPiecewiseSmoothOn
abbrev IsReparametrization := @PathIntegrationData.IsReparametrization


end
end SmoothManifolds.PathIntegration
