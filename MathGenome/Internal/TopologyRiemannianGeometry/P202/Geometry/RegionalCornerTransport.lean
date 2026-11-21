import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RegionalCornerTransport
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetLocalization
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
/-! Corner metric and occupied-ray transport for the canonical regional objects.
Includes arbitrary presentation invariance, genuine atlas changes at seams,
and first-order domain/cone stability with exactly the corner boundary rays excluded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open Set
open scoped BigOperators
namespace P202.GlobalGaussBonnet.CornerTransport
open P202Specs.RegionalCornerTransport
open SmoothManifolds (ModelKind)
universe u
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.GlobalGaussBonnet

section PresentationEndpoints
open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning

/-- An endpoint is indexed in (0,1], so the cyclic period join is counted once. -/
lemma arcPresentation_endTime_mem {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count) : A.time j.succ ∈ Ioc 0 1 := by
  have hl := A.strictMono (show (0 : Fin (A.count + 1)) < j.succ from by
    change 0 < j.val + 1
    omega)
  have hu := A.strictMono.monotone (Fin.le_last j.succ)
  rw [A.first] at hl
  rw [A.last] at hu
  exact ⟨hl, hu⟩

lemma arcPresentation_endpoint_eq {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count) :
    A.arc j 1 = q.parametrization (A.time j.succ : ParameterCircle) := by
  simpa only [realLift, mul_one, add_sub_cancel] using A.agrees j 1 (by simp)

/-- Presentation endpoints of one genuine Jordan curve are distinct, even
when the last endpoint represents zero on the parameter circle. -/
theorem arcPresentation_endpoint_injective {q : RegularJordanCurve}
    (A : ArcPresentation q) : Function.Injective (fun j => A.arc j 1) := by
  intro i j hij
  have hp : (A.time i.succ : ParameterCircle) = (A.time j.succ : ParameterCircle) := by
    apply q.injective
    rwa [← arcPresentation_endpoint_eq, ← arcPresentation_endpoint_eq]
  have ht : A.time i.succ = A.time j.succ := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := (1 : ℝ)) (a := 0) (by simpa using arcPresentation_endTime_mem A i)
      (by simpa using arcPresentation_endTime_mem A j)).mp hp
  exact Fin.succ_injective _ (A.strictMono.injective ht)

lemma arcPresentation_endpoint_mem_trace {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count) : A.arc j 1 ∈ q.trace := by
  exact ⟨(A.time j.succ : ParameterCircle), (arcPresentation_endpoint_eq A j).symm⟩

/-- Every presentation corner of a region has a unique boundary-component
and arc index. This uses actual disjoint Jordan traces, not an incidence premise. -/
theorem regionalPresentation_endpoint_injective (R : PlanarRegion)
    (A : ∀ i, ArcPresentation (R.curve i)) :
    Function.Injective (fun p : Σ i, Fin (A i).count => (A p.1).arc p.2 1) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  change (A i).arc j 1 = (A k).arc l 1 at h
  have hik : i = k := by
    by_contra hn
    have hi := arcPresentation_endpoint_mem_trace (A i) j
    have hk := arcPresentation_endpoint_mem_trace (A k) l
    rw [← h] at hk
    exact (Set.disjoint_left.mp (R.disjoint_curves hn)) hi hk
  subst k
  have hjl : j = l := arcPresentation_endpoint_injective (A i) h
  subst l
  rfl
end PresentationEndpoints
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.MetricBoundaryTurning P202Specs.PlaneTurning
/-! Presentation invariance includes joins listed in only one presentation. -/
section PresentationInvariance
open Filter
open scoped _root_.Topology
open P202Specs.PlaneTurning
/-- Put an actual smooth presentation arc back into the original real parameter. -/
def parameterArc {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count)
    (t : ℝ) : Plane :=
  A.arc j ((t - A.time j.castSucc) / (A.time j.succ - A.time j.castSucc))

lemma parameterArc_agrees {q : RegularJordanCurve} (A : ArcPresentation q)
    (j : Fin A.count) :
    EqOn (parameterArc A j) (realLift q.parametrization)
      (Icc (A.time j.castSucc) (A.time j.succ)) := by
  intro t ht
  have hw : 0 < A.time j.succ - A.time j.castSucc :=
    sub_pos.mpr (A.strictMono (by simp))
  have hslot : (t - A.time j.castSucc) / (A.time j.succ - A.time j.castSucc) ∈
      Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hw.le
    · exact (div_le_one hw).mpr (by linarith [ht.2])
  rw [parameterArc, A.agrees j _ hslot]
  congr 1
  field_simp
  ring

lemma parameterArc_hasDerivAt {q : RegularJordanCurve} (A : ArcPresentation q)
    (j : Fin A.count) {t : ℝ} (ht : t ∈ Icc (A.time j.castSucc) (A.time j.succ)) :
    HasDerivAt (parameterArc A j)
      ((A.time j.succ - A.time j.castSucc)⁻¹ •
        velocity A j ((t - A.time j.castSucc) / (A.time j.succ - A.time j.castSucc))) t := by
  have hw : 0 < A.time j.succ - A.time j.castSucc :=
    sub_pos.mpr (A.strictMono (by simp))
  have hslot : (t - A.time j.castSucc) / (A.time j.succ - A.time j.castSucc) ∈
      Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hw.le
    · exact (div_le_one hw).mpr (by linarith [ht.2])
  have hd := (differentiableAt_of_deriv_ne_zero (A.regular j _ hslot)).hasDerivAt
  convert hd.scomp t (((hasDerivAt_id t).sub_const _).div_const
    (A.time j.succ - A.time j.castSucc)) using 1 <;> simp [parameterArc, velocity]
  rfl

lemma arcPresentation_velocity_end_eq {q : RegularJordanCurve}
    (A B : ArcPresentation q) (j : Fin A.count) (k : Fin B.count)
    (ht : A.time j.succ = B.time k.succ) :
    velocity B k 1 =
      ((B.time k.succ - B.time k.castSucc) /
        (A.time j.succ - A.time j.castSucc)) • velocity A j 1 := by
  have ha := A.strictMono (Fin.castSucc_lt_succ (i := j))
  have hb := B.strictMono (Fin.castSucc_lt_succ (i := k))
  have hdA := parameterArc_hasDerivAt A j (t := A.time j.succ) ⟨ha.le, le_rfl⟩
  have hdB := parameterArc_hasDerivAt B k (t := B.time k.succ) ⟨hb.le, le_rfl⟩
  simp only [div_self (sub_pos.mpr ha).ne', div_self (sub_pos.mpr hb).ne'] at hdA hdB
  have he : parameterArc A j =ᶠ[𝓝[≤] (A.time j.succ)] parameterArc B k := by
    have hA := (parameterArc_agrees A j).eventuallyEq_of_mem (Icc_mem_nhdsLE ha)
    have hB := (parameterArc_agrees B k).eventuallyEq_of_mem (Icc_mem_nhdsLE hb)
    rw [← ht] at hB
    exact hA.trans hB.symm
  have hdB' : HasDerivAt (parameterArc B k)
      ((B.time k.succ - B.time k.castSucc)⁻¹ • velocity B k 1) (A.time j.succ) := by
    simpa only [ht] using hdB
  have heq := P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_le
    hdA.differentiableAt hdB'.differentiableAt he
  rw [hdA.deriv, hdB'.deriv] at heq
  have hh := congrArg (fun v : Plane => (B.time k.succ - B.time k.castSucc) • v) heq
  simpa only [smul_smul, mul_inv_cancel₀ (sub_pos.mpr hb).ne', one_smul, div_eq_mul_inv]
    using hh.symm

lemma arcPresentation_velocity_start_eq {q : RegularJordanCurve}
    (A B : ArcPresentation q) (j : Fin A.count) (k : Fin B.count)
    (ht : A.time j.castSucc = B.time k.castSucc) :
    velocity B k 0 =
      ((B.time k.succ - B.time k.castSucc) /
        (A.time j.succ - A.time j.castSucc)) • velocity A j 0 := by
  have ha := A.strictMono (Fin.castSucc_lt_succ (i := j))
  have hb := B.strictMono (Fin.castSucc_lt_succ (i := k))
  have hdA := parameterArc_hasDerivAt A j (t := A.time j.castSucc) ⟨le_rfl, ha.le⟩
  have hdB := parameterArc_hasDerivAt B k (t := B.time k.castSucc) ⟨le_rfl, hb.le⟩
  simp only [sub_self, zero_div] at hdA hdB
  have he : parameterArc A j =ᶠ[𝓝[≥] (A.time j.castSucc)] parameterArc B k := by
    have hA := (parameterArc_agrees A j).eventuallyEq_of_mem (Icc_mem_nhdsGE ha)
    have hB := (parameterArc_agrees B k).eventuallyEq_of_mem (Icc_mem_nhdsGE hb)
    rw [← ht] at hB
    exact hA.trans hB.symm
  have hdB' : HasDerivAt (parameterArc B k)
      ((B.time k.succ - B.time k.castSucc)⁻¹ • velocity B k 0) (A.time j.castSucc) := by
    simpa only [ht] using hdB
  have heq := P202.PlanarRegionTopology.deriv_eq_of_eventuallyEq_ge
    hdA.differentiableAt hdB'.differentiableAt he
  rw [hdA.deriv, hdB'.deriv] at heq
  have hh := congrArg (fun v : Plane => (B.time k.succ - B.time k.castSucc) • v) heq
  simpa only [smul_smul, mul_inv_cancel₀ (sub_pos.mpr hb).ne', one_smul, div_eq_mul_inv]
    using hh.symm

lemma arcPresentation_next_start {q : RegularJordanCurve}
    (A : ArcPresentation q) (j : Fin A.count) :
    A.time (finRotate A.count j).castSucc =
      if A.time j.succ = 1 then 0 else A.time j.succ := by
  letI : NeZero A.count := ⟨A.positive.ne'⟩
  by_cases hj : j.val + 1 < A.count
  · let k : Fin A.count := ⟨j.val + 1, hj⟩
    have hrot : finRotate A.count j = k := by
      rw [finRotate_apply]
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      exact Nat.mod_eq_of_lt hj
    have ht : A.time j.succ < 1 := by
      rw [← A.last]
      apply A.strictMono
      exact hj
    rw [hrot, ite_eq_right ht.ne]
    congr 1
  · have hlast : j.succ = Fin.last A.count := by
      apply Fin.ext
      change j.val + 1 = A.count
      omega
    have hrot : finRotate A.count j = ⟨0, A.positive⟩ := by
      rw [finRotate_apply]
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      change (j.val + 1) % A.count = 0
      have he : j.val + 1 = A.count := by omega
      rw [he, Nat.mod_self]
    rw [hrot]
    change A.time 0 = _
    rw [A.first, hlast, A.last, ite_eq_left rfl]

/-- Every unlisted parameter lies in the interior of one smooth arc. -/
lemma arcPresentation_open_slot {q : RegularJordanCurve} (A : ArcPresentation q)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hne : ∀ j : Fin A.count, t ≠ A.time j.succ) :
    ∃ j : Fin A.count, t ∈ Ioo (A.time j.castSucc) (A.time j.succ) := by
  classical
  have hex : ∃ j : Fin A.count, t < A.time j.succ := by
    refine ⟨⟨A.count - 1, by have := A.positive; omega⟩, ?_⟩
    have he : (⟨A.count - 1, by have := A.positive; omega⟩ : Fin A.count).succ =
        Fin.last A.count := by apply Fin.ext; have := A.positive; simp; omega
    rw [he, A.last]
    exact ht.2
  let j := Fin.find (fun j : Fin A.count => t < A.time j.succ) hex
  refine ⟨j, ?_, Fin.find_spec hex⟩
  by_cases hz : j.val = 0
  · have hj : j.castSucc = 0 := Fin.ext hz
    simpa only [hj, A.first] using ht.1
  · let k : Fin A.count := ⟨j.val - 1, by omega⟩
    have hkj : k < j := by change j.val - 1 < j.val; omega
    have hn := Fin.find_min hex hkj
    have he : k.succ = j.castSucc := by apply Fin.ext; change j.val - 1 + 1 = j.val; omega
    have hle : A.time j.castSucc ≤ t := by
      rw [he] at hn
      exact le_of_not_gt hn
    apply hle.lt_of_ne
    have hneq := hne k
    rw [he] at hneq
    exact Ne.symm hneq

/-- Omitted presentation endpoints are smooth parameters of the original curve. -/
lemma arcPresentation_differentiable_at_unlisted {q : RegularJordanCurve}
    (A : ArcPresentation q) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (hne : ∀ j : Fin A.count, t ≠ A.time j.succ) :
    DifferentiableAt ℝ (realLift q.parametrization) t := by
  have ht1 : t < 1 := by
    apply ht.2.lt_of_ne
    intro he
    have hj := hne ⟨A.count - 1, by have := A.positive; omega⟩
    have hi : (⟨A.count - 1, by have := A.positive; omega⟩ : Fin A.count).succ =
        Fin.last A.count := by apply Fin.ext; have := A.positive; simp; omega
    exact hj (he.trans (hi ▸ A.last).symm)
  obtain ⟨j, hj⟩ := arcPresentation_open_slot A ⟨ht.1, ht1⟩ hne
  exact (parameterArc_hasDerivAt A j ⟨hj.1.le, hj.2.le⟩).differentiableAt.congr_of_eventuallyEq
    ((parameterArc_agrees A j).eventuallyEq_of_mem (Icc_mem_nhds hj.1 hj.2)).symm

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202.MetricData
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

/-- The literal principal metric corner is independent of the chosen smooth
arc extensions and of the speeds of the two adjacent presentation arcs. -/
theorem metricCornerAngle_eq_at_common_endpoint {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A B : ArcPresentation q) (j : Fin A.count) (k : Fin B.count)
    (hp : A.arc j 1 = B.arc k 1) :
    P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j =
      P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc B k := by
  have hcircle : (A.time j.succ : ParameterCircle) = (B.time k.succ : ParameterCircle) := by
    apply q.injective
    rwa [← arcPresentation_endpoint_eq, ← arcPresentation_endpoint_eq]
  have ht : A.time j.succ = B.time k.succ :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := (1 : ℝ)) (a := 0) (by simpa using arcPresentation_endTime_mem A j)
      (by simpa using arcPresentation_endTime_mem B k)).mp hcircle
  have hnext : A.time (finRotate A.count j).castSucc =
      B.time (finRotate B.count k).castSucc := by
    rw [arcPresentation_next_start, arcPresentation_next_start, ht]
  have ha (i : Fin A.count) : 0 < A.time i.succ - A.time i.castSucc :=
    sub_pos.mpr (A.strictMono (Fin.castSucc_lt_succ (i := i)))
  have hb (i : Fin B.count) : 0 < B.time i.succ - B.time i.castSucc :=
    sub_pos.mpr (B.strictMono (Fin.castSucc_lt_succ (i := i)))
  exact (P202.GlobalGaussBonnet.metricCornerAngle_eq_of_pos_smul_velocities g o c hc
    A B j k hp.symm (div_pos (hb k) (ha j))
    (div_pos (hb (finRotate B.count k)) (ha (finRotate A.count j)))
    (arcPresentation_velocity_end_eq A B j k ht)
    (arcPresentation_velocity_start_eq A B _ _ hnext)).symm

/-- A join omitted from any other presentation contributes zero, even when
it belongs to the original optional list of joins. -/
theorem metricCornerAngle_eq_zero_of_endpoint_unlisted {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A B : ArcPresentation q) (j : Fin A.count)
    (hne : ∀ k : Fin B.count, A.arc j 1 ≠ B.arc k 1) :
    P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j = 0 := by
  apply P202.GlobalGaussBonnet.metricCornerAngle_eq_zero_at_smooth_join g o c hc A j
  apply arcPresentation_differentiable_at_unlisted B (arcPresentation_endTime_mem A j)
  intro k hk
  apply hne k
  rw [arcPresentation_endpoint_eq, arcPresentation_endpoint_eq, hk]

/-- Every corner carrying nonzero metric turn is present in every actual
smooth presentation of the same parametrized Jordan curve. -/
lemma exists_endpoint_of_metricCornerAngle_ne_zero {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A B : ArcPresentation q) (j : Fin A.count)
    (hne : P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j ≠ 0) :
    ∃ k : Fin B.count, A.arc j 1 = B.arc k 1 := by
  by_contra hn
  exact hne (metricCornerAngle_eq_zero_of_endpoint_unlisted g o c hc A B j
    (by simpa only [not_exists] using hn))

/-- The total literal metric corner turn is invariant under every finite
smooth presentation, including arbitrary added or omitted smooth joins. -/
theorem sum_metricCornerAngle_eq {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A B : ArcPresentation q) :
    (∑ j, P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j) =
      ∑ k, P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc B k := by
  classical
  let fA := P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A
  let fB := P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc B
  have hmatch (j : Fin A.count) (hj : fA j ≠ 0) :
      ∃ k : Fin B.count, A.arc j 1 = B.arc k 1 :=
    exists_endpoint_of_metricCornerAngle_ne_zero g o c hc A B j hj
  let matchIndex (j : Fin A.count) (hj : fA j ≠ 0) : Fin B.count :=
    (hmatch j hj).choose
  have hpoint (j : Fin A.count) (hj : fA j ≠ 0) :
      A.arc j 1 = B.arc (matchIndex j hj) 1 := (hmatch j hj).choose_spec
  refine Finset.sum_bij_ne_zero (fun j _ hj => matchIndex j hj) (by simp) ?_ ?_ ?_
  · intro j₁ _ hj₁ j₂ _ hj₂ he
    apply arcPresentation_endpoint_injective A
    exact (hpoint j₁ hj₁).trans ((congrArg (fun k => B.arc k 1) he).trans
      (hpoint j₂ hj₂).symm)
  · intro k _ hk
    obtain ⟨j, hj⟩ := exists_endpoint_of_metricCornerAngle_ne_zero g o c hc B A k hk
    have hv : fA j = fB k := metricCornerAngle_eq_at_common_endpoint g o c hc A B j k hj.symm
    have hn : fA j ≠ 0 := by rwa [hv]
    refine ⟨j, Finset.mem_univ _, hn, ?_⟩
    exact arcPresentation_endpoint_injective B ((hpoint j hn).symm.trans hj.symm)
  · intro j _ hj
    exact metricCornerAngle_eq_at_common_endpoint g o c hc A B j _ (hpoint j hj)

/-- Arbitrary finite smooth refinements preserve the actual regional
exterior-angle sum. This needs no extra hypothesis on induced signs. -/
theorem exteriorAngleSum_eq_of_presentations
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (A B : ∀ i, ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) :
    P202Specs.LocalGaussBonnet.exteriorAngleSum g o c hc R A s =
      P202Specs.LocalGaussBonnet.exteriorAngleSum g o c hc R B s := by
  unfold P202Specs.LocalGaussBonnet.exteriorAngleSum P202Specs.LocalGaussBonnet.interiorAngle
  simp only [sub_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_metricCornerAngle_eq g o c hc (A i) (B i)]


/-- A genuinely smooth inserted join has no literal exterior-angle term. -/
theorem smoothJoin_exterior_contribution_zero {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : ArcPresentation q) (s : ℝ) (j : Fin A.count)
    (hd : DifferentiableAt ℝ (realLift q.parametrization) (A.time j.succ)) :
    Real.pi - P202Specs.LocalGaussBonnet.interiorAngle g o c hc A s j = 0 := by
  have hzero := P202.GlobalGaussBonnet.metricCornerAngle_eq_zero_at_smooth_join
    g o c hc A j hd
  simp only [P202Specs.LocalGaussBonnet.interiorAngle, hzero, mul_zero, sub_zero, sub_self]

end PresentationInvariance

section AngleTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [Fact (Module.finrank ℝ E = 2)] [Fact (Module.finrank ℝ F = 2)]
lemma orientation_eq_of_areaForm_pos (o₁ o₂ : Orientation ℝ E (Fin 2))
    (u v : E) (h₁ : 0 < o₁.areaForm u v) (h₂ : 0 < o₂.areaForm u v) : o₁ = o₂ := by
  rcases o₁.eq_or_eq_neg o₂ (by rw [Fintype.card_fin, (Fact.out : Module.finrank ℝ E = 2)]) with h | h
  · exact h
  · rw [h, Orientation.areaForm_neg_orientation] at h₁
    change 0 < -o₂.areaForm u v at h₁
    linarith

lemma areaForm_pos_of_basis_orientation (b : Module.Basis (Fin 2) ℝ E) :
    0 < b.orientation.areaForm (b 0) (b 1) := by
  let o := b.orientation
  let B := o.finOrthonormalBasis (by decide : 0 < 2) (Fact.out : Module.finrank ℝ E = 2)
  have hB : B.toBasis.orientation = b.orientation :=
    o.finOrthonormalBasis_orientation (by decide) Fact.out
  have hp : 0 < B.toBasis.det b := (B.toBasis.orientation_eq_iff_det_pos b).mp hB
  rw [Orientation.areaForm_to_volumeForm, o.volumeForm_robust B hB]
  convert hp using 2
  funext j
  fin_cases j <;> rfl

lemma oangle_eq_of_isometry_positive_pair
    (L : E ≃ₗ[ℝ] F) (hm : ∀ u v, inner ℝ (L u) (L v) = inner ℝ u v)
    (oE : Orientation ℝ E (Fin 2)) (oF : Orientation ℝ F (Fin 2))
    (a b : E) (hE : 0 < oE.areaForm a b) (hF : 0 < oF.areaForm (L a) (L b))
    (u v : E) : oF.oangle (L u) (L v) = oE.oangle u v := by
  let I : E ≃ₗᵢ[ℝ] F :=
    { L with norm_map' := fun x => by rw [norm_eq_sqrt_real_inner, hm, ← norm_eq_sqrt_real_inner] }
  have ho : Orientation.map (Fin 2) I.toLinearEquiv oE = oF := by
    apply orientation_eq_of_areaForm_pos _ _ (I a) (I b) _ hF
    rw [Orientation.areaForm_map, I.symm_apply_apply, I.symm_apply_apply]
    exact hE
  change oF.oangle (I u) (I v) = _
  rw [← ho, Orientation.oangle_map, I.symm_apply_apply, I.symm_apply_apply]
lemma oangle_isometry_eq_or_rev
    (L : E ≃ₗ[ℝ] F) (hm : ∀ u v, inner ℝ (L u) (L v) = inner ℝ u v)
    (oE : Orientation ℝ E (Fin 2)) (oF : Orientation ℝ F (Fin 2)) :
    (∀ u v, oF.oangle (L u) (L v) = oE.oangle u v) ∨
    (∀ u v, oF.oangle (L u) (L v) = oE.oangle v u) := by
  let I : E ≃ₗᵢ[ℝ] F :=
    { L with norm_map' := fun x => by rw [norm_eq_sqrt_real_inner, hm, ← norm_eq_sqrt_real_inner] }
  rcases oF.eq_or_eq_neg (Orientation.map (Fin 2) I.toLinearEquiv oE)
      (by rw [Fintype.card_fin, (Fact.out : Module.finrank ℝ F = 2)]) with ho | ho
  · left
    intro u v
    change oF.oangle (I u) (I v) = _
    rw [ho, Orientation.oangle_map, I.symm_apply_apply, I.symm_apply_apply]
  · right
    intro u v
    change oF.oangle (I u) (I v) = _
    rw [ho, Orientation.oangle_neg_orientation_eq_neg,
      Orientation.oangle_map, I.symm_apply_apply, I.symm_apply_apply, oE.oangle_rev, neg_neg]


/-- The sign of the actual image of a positive pair selects the uniform
ray order. It is computed from the metric area form, not supplied as an
angle-transport certificate. -/
theorem oangle_isometry_order_selection
    (L : E ≃ₗ[ℝ] F) (hm : ∀ u v, inner ℝ (L u) (L v) = inner ℝ u v)
    (oE : Orientation ℝ E (Fin 2)) (oF : Orientation ℝ F (Fin 2))
    (a b : E) (hE : 0 < oE.areaForm a b) :
    (0 < oF.areaForm (L a) (L b) ∨ oF.areaForm (L a) (L b) < 0) ∧
    (0 < oF.areaForm (L a) (L b) →
      ∀ u v, oF.oangle (L u) (L v) = oE.oangle u v) ∧
    (oF.areaForm (L a) (L b) < 0 →
      ∀ u v, oF.oangle (L u) (L v) = oE.oangle v u) := by
  let I : E ≃ₗᵢ[ℝ] F :=
    { L with norm_map' := fun x => by rw [norm_eq_sqrt_real_inner, hm, ← norm_eq_sqrt_real_inner] }
  have hsign : 0 < oF.areaForm (L a) (L b) ∨ oF.areaForm (L a) (L b) < 0 := by
    rcases oF.eq_or_eq_neg (Orientation.map (Fin 2) I.toLinearEquiv oE)
        (by rw [Fintype.card_fin, (Fact.out : Module.finrank ℝ F = 2)]) with h | h
    · left
      change 0 < oF.areaForm (I a) (I b)
      rw [h, Orientation.areaForm_map, I.symm_apply_apply, I.symm_apply_apply]
      exact hE
    · right
      change oF.areaForm (I a) (I b) < 0
      rw [h, Orientation.areaForm_neg_orientation]
      change -(Orientation.map (Fin 2) I.toLinearEquiv oE).areaForm (I a) (I b) < 0
      rw [Orientation.areaForm_map, I.symm_apply_apply, I.symm_apply_apply]
      linarith
  refine ⟨hsign, fun h => oangle_eq_of_isometry_positive_pair L hm oE oF a b hE h, ?_⟩
  intro h u v
  have hneg : 0 < (-oF).areaForm (L a) (L b) := by
    rw [Orientation.areaForm_neg_orientation]
    change 0 < -oF.areaForm (L a) (L b)
    linarith
  have hh := oangle_eq_of_isometry_positive_pair L hm oE (-oF) a b hE hneg v u
  rw [Orientation.oangle_neg_orientation_eq_neg, oF.oangle_rev, neg_neg] at hh
  exact hh

end AngleTransport

section RegionalPairing
open Filter
open scoped _root_.Topology
open SmoothManifolds.DifferentialData SmoothManifolds.MapData
open SmoothManifolds.TangentBundleData
theorem regionalChartGeometry_pairing_coordinateVectors
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood) (v w : Euclidean 2) :
    pairing G.metric (G.map p)
      (((tangentStructure G.ambientSurface).fiberCoordinates.equiv
        G.ambientChart G.ambientChart_mem (G.map p)
        (by rw [G.ambientChart_source]; trivial)).symm v)
      (((tangentStructure G.ambientSurface).fiberCoordinates.equiv
        G.ambientChart G.ambientChart_mem (G.map p)
        (by rw [G.ambientChart_source]; trivial)).symm w) =
    pairing g p.val
      (((tangentStructure S).fiberCoordinates.equiv
        (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)).symm v)
      (((tangentStructure S).fiberCoordinates.equiv
        (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)).symm w) := by
  let E := (tangentStructure G.restriction).fiberCoordinates.equiv
    G.restrictedChart G.restrictedChart_mem p
    (by rw [G.restrictedChart_source]; trivial)
  let F := (tangentStructure G.ambientSurface).fiberCoordinates.equiv
    G.ambientChart G.ambientChart_mem (G.map p)
    (by rw [G.ambientChart_source]; trivial)
  let K := (tangentStructure S).fiberCoordinates.equiv
    (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
  have hF (v : Euclidean 2) : G.immersion.differential p (E.symm v) = F.symm v := by
    apply F.injective
    have h := P202.GlobalGaussBonnet.differential_matching_coordinates G.map G.immersion.smooth p
      (G.immersion.differential p) (G.immersion.isDifferential p)
      G.restrictedChart G.ambientChart G.restrictedChart_mem G.ambientChart_mem
      (by rw [G.restrictedChart_source]; trivial)
      (by rw [G.ambientChart_source]; trivial)
      (Filter.Eventually.of_forall G.matching_coordinates)
      (tangentStructure G.restriction).fiberCoordinates
      (tangentStructure G.ambientSurface).fiberCoordinates (E.symm v)
    simpa only [E, F, LinearEquiv.apply_symm_apply] using h
  have hK (v : Euclidean 2) : G.inclusion.differential p (E.symm v) = K.symm v := by
    apply K.injective
    have h := P202.GlobalGaussBonnet.differential_matching_coordinates Subtype.val G.inclusion.smooth p
      (G.inclusion.differential p) (G.inclusion.isDifferential p)
      G.restrictedChart (D.chart r) G.restrictedChart_mem (D.chart_mem r)
      (by rw [G.restrictedChart_source]; trivial) (G.source_subset p.property)
      (Filter.Eventually.of_forall (fun q => congrArg Subtype.val (G.restrictedChart_eq q)))
      (tangentStructure G.restriction).fiberCoordinates
      (tangentStructure S).fiberCoordinates (E.symm v)
    simpa only [E, K, LinearEquiv.apply_symm_apply] using h
  change pairing G.metric (G.map p) (F.symm v) (F.symm w) =
    pairing g p.val (K.symm v) (K.symm w)
  rw [← hF, ← hF, G.metric_preserving, hK, hK]

open P202.SurfaceBoundaryData


theorem regionalChartGeometry_angle_transport
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2)) :
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let F := (tangentStructure G.ambientSurface).fiberCoordinates.equiv
      G.ambientChart G.ambientChart_mem (G.map p)
      (by rw [G.ambientChart_source]; trivial)
    (∀ u v : Euclidean 2,
      tangentAngle G.metric (G.map p) (planeOrientation G.metric G.orientation (G.map p))
        (F.symm u) (F.symm v) = tangentAngle g p.val o (K.symm u) (K.symm v)) ∨
    (∀ u v : Euclidean 2,
      tangentAngle G.metric (G.map p) (planeOrientation G.metric G.orientation (G.map p))
        (F.symm u) (F.symm v) = tangentAngle g p.val o (K.symm v) (K.symm u)) := by
  let K := (tangentStructure S).fiberCoordinates.equiv
    (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
  let F := (tangentStructure G.ambientSurface).fiberCoordinates.equiv
    G.ambientChart G.ambientChart_mem (G.map p)
    (by rw [G.ambientChart_source]; trivial)
  letI := (metricCore g p.val).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p.val).toCore
  letI := (SmoothManifolds.tangent_dimension S p.val).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p.val) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p.val).2⟩
  letI := (metricCore G.metric (G.map p)).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore G.metric (G.map p)).toCore
  letI := (SmoothManifolds.tangent_dimension G.ambientSurface (G.map p)).1
  letI : Fact (Module.finrank ℝ (TangentSpace G.ambientSurface (G.map p)) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension G.ambientSurface (G.map p)).2⟩
  let L := K.trans F.symm
  have hm (u v : TangentSpace S p.val) : inner ℝ (L u) (L v) = inner ℝ u v := by
    change pairing G.metric (G.map p) (F.symm (K u)) (F.symm (K v)) = pairing g p.val u v
    rw [regionalChartGeometry_pairing_coordinateVectors, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  rcases oangle_isometry_eq_or_rev L hm o (planeOrientation G.metric G.orientation (G.map p))
      with h | h
  · left
    intro u v
    simpa only [L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, tangentAngle] using
      h (K.symm u) (K.symm v)
  · right
    intro u v
    simpa only [L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, tangentAngle] using
      h (K.symm u) (K.symm v)


open P202Specs.MetricBoundaryTurning P202Specs.PlanarRegionTopology

lemma positiveMetricAngle_eq_tangentAngle
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) (x u v : Plane) :
    positiveMetricAngle g o c hc x u v = positiveAngle
      (tangentAngle g (chartPoint c x) (planeOrientation g o (chartPoint c x))
        (chartVector c hc x u) (chartVector c hc x v)) := rfl

lemma regionalChartGeometry_modelPoint
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood) :
    P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p.val) =
      G.ambientChart (G.map p) := by
  apply Subtype.ext
  simp only [P202Specs.ChartRegionStokes.modelPoint, coordinates, toPlane]
  exact (congrArg Subtype.val (G.restrictedChart_eq p)).symm.trans
    (G.matching_coordinates p)

lemma regionalChartGeometry_chartPoint
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood) :
    chartPoint G.ambientChart (coordinates (D.chart r) p.val) = G.map p := by
  unfold chartPoint
  rw [regionalChartGeometry_modelPoint]
  exact G.ambientChart.left_inv (by rw [G.ambientChart_source]; trivial)

lemma chartVector_heq_coordinateVector
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x v : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target)
    (p : M) (hp : p ∈ c.source) (he : chartPoint c x = p) :
    HEq (chartVector c hc x v) (((tangentStructure S).fiberCoordinates.equiv
      c hc p hp).symm (EuclideanSpace.equiv (Fin 2) ℝ v)) := by
  cases he
  simp only [chartVector, dite_eq_left hx]
  rfl

lemma regionalChartGeometry_chartVector
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood) (v : Plane) :
    HEq (chartVector G.ambientChart G.ambientChart_mem (coordinates (D.chart r) p.val) v)
      (((tangentStructure G.ambientSurface).fiberCoordinates.equiv
        G.ambientChart G.ambientChart_mem (G.map p)
        (by rw [G.ambientChart_source]; trivial)).symm (EuclideanSpace.equiv (Fin 2) ℝ v)) := by
  have hs : G.map p ∈ G.ambientChart.source := by rw [G.ambientChart_source]; trivial
  have hx : P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p.val) ∈ G.ambientChart.target := by
    rw [regionalChartGeometry_modelPoint]
    exact G.ambientChart.map_source hs
  exact chartVector_heq_coordinateVector G.ambientChart G.ambientChart_mem _ v hx _ hs
    (regionalChartGeometry_chartPoint g D r G p)

lemma positiveMetricAngle_eq_coordinateTangentAngle
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u v : Plane) (hx : P202Specs.ChartRegionStokes.modelPoint x ∈ c.target)
    (p : M) (hp : p ∈ c.source) (he : chartPoint c x = p) :
    positiveMetricAngle g o c hc x u v = positiveAngle
      (tangentAngle g p (planeOrientation g o p)
        (((tangentStructure S).fiberCoordinates.equiv c hc p hp).symm
          (EuclideanSpace.equiv (Fin 2) ℝ u))
        (((tangentStructure S).fiberCoordinates.equiv c hc p hp).symm
          (EuclideanSpace.equiv (Fin 2) ℝ v))) := by
  cases he
  simp only [positiveMetricAngle_eq_tangentAngle, chartVector, dite_eq_left hx]

theorem regionalChartGeometry_positiveMetricAngle_transport
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2)) :
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    (∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v)))) ∨
    (∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u)))) := by
  have hs : G.map p ∈ G.ambientChart.source := by rw [G.ambientChart_source]; trivial
  have hx : P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p.val) ∈ G.ambientChart.target := by
    rw [regionalChartGeometry_modelPoint]
    exact G.ambientChart.map_source hs
  have he := regionalChartGeometry_chartPoint g D r G p
  rcases regionalChartGeometry_angle_transport g D r G p o with h | h
  · left
    intro u v
    rw [positiveMetricAngle_eq_coordinateTangentAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem _ u v hx (G.map p) hs he]
    exact congrArg positiveAngle (h _ _)
  · right
    intro u v
    rw [positiveMetricAngle_eq_coordinateTangentAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem _ u v hx (G.map p) hs he]
    exact congrArg positiveAngle (h _ _)



open P202Specs.PlaneTurning

lemma metricCornerAngle_eq_coordinateTangentAngle
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    {q : RegularJordanCurve} (A : ArcPresentation q) (j : Fin A.count)
    (hx : P202Specs.ChartRegionStokes.modelPoint (A.arc j 1) ∈ c.target)
    (p : M) (hp : p ∈ c.source) (he : chartPoint c (A.arc j 1) = p) :
    P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j =
      (tangentAngle g p (planeOrientation g o p)
        (((tangentStructure S).fiberCoordinates.equiv c hc p hp).symm
          (EuclideanSpace.equiv (Fin 2) ℝ (velocity A j 1)))
        (((tangentStructure S).fiberCoordinates.equiv c hc p hp).symm
          (EuclideanSpace.equiv (Fin 2) ℝ (velocity A (finRotate A.count j) 0)))).toReal := by
  cases he
  simp only [P202Specs.LocalGaussBonnet.metricCornerAngle,
    P202Specs.LocalGaussBonnet.chartVector, dite_eq_left hx, tangentAngle]
  rfl

/-- One orientation choice at the original point transports every actual
principal presentation corner there. The quantifier over presentations lies
inside each branch, so the order cannot vary between corners. -/
theorem regionalChartGeometry_metricCornerAngle_transport
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2)) :
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    (∀ (q : RegularJordanCurve) (A : ArcPresentation q) (j : Fin A.count),
      A.arc j 1 = coordinates (D.chart r) p.val →
      P202Specs.LocalGaussBonnet.metricCornerAngle G.metric G.orientation
        G.ambientChart G.ambientChart_mem A j =
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ (velocity A j 1)))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ
              (velocity A (finRotate A.count j) 0)))).toReal) ∨
    (∀ (q : RegularJordanCurve) (A : ArcPresentation q) (j : Fin A.count),
      A.arc j 1 = coordinates (D.chart r) p.val →
      P202Specs.LocalGaussBonnet.metricCornerAngle G.metric G.orientation
        G.ambientChart G.ambientChart_mem A j =
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ
              (velocity A (finRotate A.count j) 0)))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ (velocity A j 1)))).toReal) := by
  have hs : G.map p ∈ G.ambientChart.source := by rw [G.ambientChart_source]; trivial
  have hx : P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p.val) ∈
      G.ambientChart.target := by
    rw [regionalChartGeometry_modelPoint]
    exact G.ambientChart.map_source hs
  have he := regionalChartGeometry_chartPoint g D r G p
  rcases regionalChartGeometry_angle_transport g D r G p o with h | h
  · left
    intro q A j hj
    rw [metricCornerAngle_eq_coordinateTangentAngle G.metric G.orientation G.ambientChart
      G.ambientChart_mem A j (by simpa only [hj] using hx) (G.map p) hs (by simpa only [hj] using he)]
    exact congrArg Real.Angle.toReal (h _ _)
  · right
    intro q A j hj
    rw [metricCornerAngle_eq_coordinateTangentAngle G.metric G.orientation G.ambientChart
      G.ambientChart_mem A j (by simpa only [hj] using hx) (G.map p) hs (by simpa only [hj] using he)]
    exact congrArg Real.Angle.toReal (h _ _)


/-- Transport the literal occupied-sector predicate, deriving it from the
upstream local boundary theorem rather than assuming a corner correspondence. -/
theorem regionalChartGeometry_occupiedSectorAngle_transport
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount) (j : Fin (A i).count)
    (hj : (A i).arc j 1 = coordinates (D.chart r) p.val) :
    ∃ reversed : Bool,
      originalOccupiedSectorAngle g D r p.val (G.source_subset p.property) o i (A i) (s i) j
        (P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
          G.ambientChart G.ambientChart_mem (A i) (s i) j) reversed := by
  have hlocal := (P202.LocalGaussBonnet.localGaussBonnet G.ambientSurface G.metric
    G.connection G.connection_LC G.curvature G.curvature_represents G.orientation
    G.ambientChart G.ambientChart_mem G.orientation_positive (D.region r)
    (P202.GlobalGaussBonnet.regionalChartGeometry_carrier_subset G)).2 A s hs
  have hoccupied := hlocal.2.2.2.1 i j
  have hdomain (v : Plane) :
      (∀ᶠ t : ℝ in 𝓝[>] 0, ∃ q ∈ regionInterior D r,
        coordinates (D.chart r) q = (A i).arc j 1 + t • v) ↔
      (∀ᶠ t : ℝ in 𝓝[>] 0, (A i).arc j 1 + t • v ∈ (D.region r).domain) := by
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall (fun t => by rw [← D.domain_coordinates r]; rfl)
  rcases regionalChartGeometry_positiveMetricAngle_transport g D r G p o with h | h
  · refine ⟨false, hoccupied.1, hoccupied.2.1, ?_⟩
    intro v hv hvo hvi
    change _ ↔ positiveAngle (tangentAngle g p.val o _ _) < _
    rw [hdomain]
    have hangle := h (outgoingRay (A i) (s i) j) v
    rw [← hj] at hangle
    rw [← hangle]
    exact hoccupied.2.2 v hv hvo hvi
  · refine ⟨true, hoccupied.1, hoccupied.2.1, ?_⟩
    intro v hv hvo hvi
    change _ ↔ positiveAngle (tangentAngle g p.val o _ _) < _
    rw [hdomain]
    have hangle := h (outgoingRay (A i) (s i) j) v
    rw [← hj] at hangle
    rw [← hangle]
    exact hoccupied.2.2 v hv hvo hvi


/-- Compute the uniform direct/reversed choice from the actual image area
of any positively oriented original tangent pair. Neither sign is assumed. -/
theorem regionalChartGeometry_order_selection
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (a b : TangentSpace S p.val) (hpos : 0 < tangentArea g p.val o a b) :
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let F := (tangentStructure G.ambientSurface).fiberCoordinates.equiv
      G.ambientChart G.ambientChart_mem (G.map p)
      (by rw [G.ambientChart_source]; trivial)
    let delta := tangentArea G.metric (G.map p)
      (planeOrientation G.metric G.orientation (G.map p)) (F.symm (K a)) (F.symm (K b))
    (0 < delta ∨ delta < 0) ∧
    (0 < delta → ∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v)))) ∧
    (delta < 0 → ∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u)))) := by
  let K := (tangentStructure S).fiberCoordinates.equiv
    (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
  let F := (tangentStructure G.ambientSurface).fiberCoordinates.equiv
    G.ambientChart G.ambientChart_mem (G.map p)
    (by rw [G.ambientChart_source]; trivial)
  letI := (metricCore g p.val).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p.val).toCore
  letI := (SmoothManifolds.tangent_dimension S p.val).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p.val) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p.val).2⟩
  letI := (metricCore G.metric (G.map p)).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore G.metric (G.map p)).toCore
  letI := (SmoothManifolds.tangent_dimension G.ambientSurface (G.map p)).1
  letI : Fact (Module.finrank ℝ (TangentSpace G.ambientSurface (G.map p)) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension G.ambientSurface (G.map p)).2⟩
  let L := K.trans F.symm
  have hm (u v : TangentSpace S p.val) : inner ℝ (L u) (L v) = inner ℝ u v := by
    change pairing G.metric (G.map p) (F.symm (K u)) (F.symm (K v)) = pairing g p.val u v
    rw [regionalChartGeometry_pairing_coordinateVectors, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  have hdata := oangle_isometry_order_selection L hm o
    (planeOrientation G.metric G.orientation (G.map p)) a b hpos
  have hs : G.map p ∈ G.ambientChart.source := by rw [G.ambientChart_source]; trivial
  have hx : P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p.val) ∈
      G.ambientChart.target := by
    rw [regionalChartGeometry_modelPoint]
    exact G.ambientChart.map_source hs
  have he := regionalChartGeometry_chartPoint g D r G p
  refine ⟨hdata.1, ?_, ?_⟩
  · intro hd u v
    rw [positiveMetricAngle_eq_coordinateTangentAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem _ u v hx (G.map p) hs he]
    apply congrArg positiveAngle
    simpa only [L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, tangentAngle] using
      hdata.2.1 hd (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))
        (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v))
  · intro hd u v
    rw [positiveMetricAngle_eq_coordinateTangentAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem _ u v hx (G.map p) hs he]
    apply congrArg positiveAngle
    simpa only [L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, tangentAngle] using
      hdata.2.2 hd (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))
        (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v))

end RegionalPairing

section AtlasTransitions
open Filter
open scoped _root_.Topology
open SmoothManifolds.TangentBundleData

/-- An actual atlas transition has a smooth ambient extension with its true
intrinsic Jacobian, even when the overlap meets the half-space seam. -/
theorem exists_atlas_transition_extension
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (K : FiberCoordinates S)
    (e d : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    ∃ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      F (e p).val = (d p).val ∧
      HasFDerivAt F (fderiv ℝ F (e p).val) (e p).val ∧
      (∀ q (hq : q ∈ e.source) (hqd : q ∈ d.source), (e q).val ∈ U →
        F (e q).val = (d q).val) ∧
      (∀ v, fderiv ℝ F (e p).val v =
        K.equiv d hd p hpd ((K.equiv e he p hp).symm v)) := by
  have hpt : e p ∈ (e.symm.trans d).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    exact ⟨e.map_source hp, by simpa only [e.left_inv hp] using hpd⟩
  obtain ⟨U, hU, hpU, F, hF, heq⟩ :=
    (S.smoothStructure.property.1.2 e he d hd).1 (e p) hpt
  have hmatch (q : M) (hq : q ∈ e.source) (hqd : q ∈ d.source)
      (hqU : (e q).val ∈ U) : F (e q).val = (d q).val := by
    have hqt : e q ∈ (e.symm.trans d).source := by
      simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
      exact ⟨e.map_source hq, by simpa only [e.left_inv hq] using hqd⟩
    simpa only [OpenPartialHomeomorph.trans_apply, e.left_inv hq] using heq (e q) hqt hqU
  have hrep : (fun q => F (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val) := by
    filter_upwards [e.open_source.mem_nhds hp, d.open_source.mem_nhds hpd,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
        (hU.mem_nhds hpU)] with q hqe hqd hqU
    exact hmatch q hqe hqd hqU
  refine ⟨U, F, hU, hpU, hF, hmatch p hp hpd hpU,
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp) |>.hasFDerivAt,
    hmatch, ?_⟩
  intro v
  have h := SmoothManifolds.TangentBundle.transition_jacobian S K e d he hd p hp hpd
    U F hU hpU hF hrep ((K.equiv e he p hp).symm v)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- A first-order approximation carries a straight source ray to a curve
with the actual derivative direction. It is not asserted to remain straight. -/
theorem hasDerivAt_transition_ray
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E →L[ℝ] F} {x : E} (hf : HasFDerivAt f L x) (v : E) :
    HasDerivAt (fun t : ℝ => f (x + t • v) - f x) (L v) 0 := by
  have hray : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f L (x + (0 : ℝ) • v) := by simpa using hf
  simpa [Function.comp_def] using (hf'.comp_hasDerivAt 0 hray).sub_const (f x)


/-- Genuine atlas changes extend to ambient local diffeomorphisms. Both
forward and inverse germs agree with the original charts, including seams,
and both derivatives are the canonical inverse fiber-coordinate maps. -/
theorem exists_atlas_transition_localDiffeomorph
    {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (e d : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    let L := ((K.equiv e he p hp).symm.trans (K.equiv d hd p hpd)).toContinuousLinearEquiv
    ∃ H : OpenPartialHomeomorph (Euclidean n) (Euclidean n),
      (e p).val ∈ H.source ∧ H (e p).val = (d p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H (e p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H.symm (d p).val ∧
      HasFDerivAt H (L : Euclidean n →L[ℝ] Euclidean n) (e p).val ∧
      HasFDerivAt H.symm (L.symm : Euclidean n →L[ℝ] Euclidean n) (d p).val ∧
      ((fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val)) ∧
      ((fun q => H.symm (d q).val) =ᶠ[𝓝 p] (fun q => (e q).val)) := by
  let L := ((K.equiv e he p hp).symm.trans (K.equiv d hd p hpd)).toContinuousLinearEquiv
  obtain ⟨U, F, hU, hpU, hF, hbase, hder, hmatch, hJ⟩ :=
    exists_atlas_transition_extension S K e d he hd p hp hpd
  have hder' : HasFDerivAt F (L : Euclidean n →L[ℝ] Euclidean n) (e p).val := by
    convert hder using 1
    apply ContinuousLinearMap.ext
    intro v
    exact (hJ v).symm
  have hsm := hF.contDiffAt (hU.mem_nhds hpU)
  have hs := hsm.hasStrictFDerivAt' hder' (by simp)
  let H := hs.toOpenPartialHomeomorph F
  have hHs : (e p).val ∈ H.source := hs.mem_toOpenPartialHomeomorph_source
  have hH : (H : Euclidean n → Euclidean n) = F := rfl
  have hrep : (fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val) := by
    filter_upwards [e.open_source.mem_nhds hp, d.open_source.mem_nhds hpd,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
        (hU.mem_nhds hpU)] with q hqe hqd hqU
    exact hmatch q hqe hqd hqU
  refine ⟨H, hHs, hbase, hsm, ?_, hder', ?_, hrep, ?_⟩
  · rw [← hbase]
    exact hsm.to_localInverse hder' (by simp)
  · rw [← hbase]
    exact hs.to_localInverse.hasFDerivAt
  · filter_upwards [hrep,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
        (H.open_source.mem_nhds hHs)] with q hq hqH
    rw [← hq]
    exact H.left_inv (show (e q).val ∈ H.source from hqH)

end AtlasTransitions

section ConeStability
open Complex Filter
open scoped Real _root_.Topology
namespace AngularSector
/-- A nonboundary limiting direction determines eventual cone membership of
an actual differentiable curve, not merely of the exact limiting ray. -/
theorem eventually_sector_iff_of_hasDerivAt
    {F : ℝ → ℂ} {v : ℂ} {r a b : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hv : v ∈ Complex.slitPlane) (ha : arg v ≠ a) (hb : arg v ≠ b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ sector r a b ↔ arg v ∈ Ioo a b) := by
  have hs : Tendsto (fun t : ℝ => t⁻¹ • F t) (𝓝[>] 0) (𝓝 v) := by
    simpa only [zero_add, h0, sub_zero] using hF.tendsto_slope_zero_right
  have harg := (Complex.continuousAt_arg hv).tendsto.comp hs
  have hcut (c : ℝ) (hc : arg v ≠ c) :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (c < arg (t⁻¹ • F t) ↔ c < arg v) ∧
        (arg (t⁻¹ • F t) < c ↔ arg v < c) := by
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · filter_upwards [harg.eventually (gt_mem_nhds hlt)] with t ht
      exact ⟨iff_of_false (not_lt_of_gt ht) (not_lt_of_gt hlt), iff_of_true ht hlt⟩
    · filter_upwards [harg.eventually (lt_mem_nhds hgt)] with t ht
      exact ⟨iff_of_true ht hgt, iff_of_false (not_lt_of_gt ht) (not_lt_of_gt hgt)⟩
  have hne : ∀ᶠ t : ℝ in 𝓝[>] 0, t⁻¹ • F t ≠ 0 :=
    hs.eventually (isOpen_compl_singleton.mem_nhds (Complex.slitPlane_ne_zero hv))
  have hnorm : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖F t‖ < r := by
    have hn : Tendsto (fun t => ‖F t‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [h0, norm_zero] using hF.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds
    exact hn.eventually (gt_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hne, hnorm, hcut a ha, hcut b hb]
    with t ht hn hnr hca hcb
  have ht' : 0 < t := ht
  have hFt : F t ≠ 0 := by intro hz; exact hn (by rw [hz, smul_zero])
  have hangle : arg (t⁻¹ • F t) = arg (F t) := by
    exact Complex.arg_real_mul _ (inv_pos.mpr ht')
  simp only [hangle] at hca hcb
  exact ⟨fun h => ⟨hca.1.mp h.2.2.1, hcb.2.mp h.2.2.2⟩,
    fun h => ⟨hFt, hnr, hca.1.mpr h.1, hcb.2.mpr h.2⟩⟩
/-- A regular curve and its actual derivative ray eventually lie in exactly
the same angular side, provided the direction is not a limiting boundary. -/
theorem eventually_sector_iff_derivative_ray
    {F : ℝ → ℂ} {v : ℂ} {r a b : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hv : v ∈ Complex.slitPlane) (ha : arg v ≠ a) (hb : arg v ≠ b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ sector r a b ↔ t • v ∈ sector r a b) := by
  have hlin : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const v using 1 <;> simp
  filter_upwards [eventually_sector_iff_of_hasDerivAt hF h0 hr hv ha hb,
    eventually_sector_iff_of_hasDerivAt hlin (zero_smul ℝ v) hr hv ha hb] with t ht hlin
  exact ht.trans hlin.symm

end AngularSector
open AngularSector

/-- The image of an exact ray under any differentiable coordinate map has
its derivative's cone side. The map can have any invertible Jacobian; no
conformality is required, and the image curve need not be straight. -/
theorem eventually_cone_iff_of_hasFDerivAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E →L[ℝ] F} {x : E} (hf : HasFDerivAt f L x)
    (v : E) (C : F →L[ℝ] ℂ) {r a b : ℝ} (hr : 0 < r)
    (hv : C (L v) ∈ Complex.slitPlane)
    (ha : Complex.arg (C (L v)) ≠ a) (hb : Complex.arg (C (L v)) ≠ b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (C (f (x + t • v) - f x) ∈ sector r a b ↔
        t • C (L v) ∈ sector r a b) := by
  have hd : HasDerivAt (fun t : ℝ => C (f (x + t • v) - f x)) (C (L v)) 0 := by
    simpa only [Function.comp_def] using
      C.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_transition_ray hf v)
  exact AngularSector.eventually_sector_iff_derivative_ray hd (by simp) hr hv ha hb


/-- Cone stability for extensions constructed from the genuine original atlas.
The limiting direction is the actual intrinsic fiber-coordinate transition.
The same statement applies on half-space seams; both sides are evaluated in
the ambient plane and no conformal or sector-angle certificate is required. -/
theorem exists_atlas_transition_extension_with_cones
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (e d : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    ∃ (U : Set (Euclidean 2)) (F : Euclidean 2 → Euclidean 2),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      F (e p).val = (d p).val ∧
      (∀ q (hq : q ∈ e.source) (hqd : q ∈ d.source), (e q).val ∈ U →
        F (e q).val = (d q).val) ∧
      (∀ v, fderiv ℝ F (e p).val v =
        K.equiv d hd p hpd ((K.equiv e he p hp).symm v)) ∧
      (∀ (v : Euclidean 2) (C : Euclidean 2 →L[ℝ] ℂ) (r a b : ℝ),
        let w := K.equiv d hd p hpd ((K.equiv e he p hp).symm v)
        0 < r → C w ∈ Complex.slitPlane →
        Complex.arg (C w) ≠ a → Complex.arg (C w) ≠ b →
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          (C (F ((e p).val + t • v) - (d p).val) ∈ sector r a b ↔
            t • C w ∈ sector r a b)) := by
  obtain ⟨U, F, hU, hpU, hF, hbase, hder, hmatch, hJ⟩ :=
    exists_atlas_transition_extension S K e d he hd p hp hpd
  refine ⟨U, F, hU, hpU, hF, hbase, hmatch, hJ, ?_⟩
  intro v C r a b
  dsimp only
  intro hr hv ha hb
  have hv' : C (fderiv ℝ F (e p).val v) ∈ Complex.slitPlane := by rwa [hJ]
  have ha' : Complex.arg (C (fderiv ℝ F (e p).val v)) ≠ a := by rwa [hJ]
  have hb' : Complex.arg (C (fderiv ℝ F (e p).val v)) ≠ b := by rwa [hJ]
  simpa only [hbase, hJ] using
    eventually_cone_iff_of_hasFDerivAt hder v C hr hv' ha' hb'


/-- Membership in the actual image of an explicit cone is detected by the
inverse derivative for every direction off the limiting boundary rays. -/
theorem eventually_image_cone_iff_inverse_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : OpenPartialHomeomorph E F) (x : E) (hx : x ∈ H.source)
    {L : F →L[ℝ] E} (hder : HasFDerivAt H.symm L (H x))
    (v : F) (C : E →L[ℝ] ℂ) {r a b : ℝ} (hr : 0 < r)
    (hv : C (L v) ∈ Complex.slitPlane)
    (ha : Complex.arg (C (L v)) ≠ a) (hb : Complex.arg (C (L v)) ≠ b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (H x + t • v ∈ H '' (H.source ∩ (fun z => C (z - x)) ⁻¹' sector r a b) ↔
        t • C (L v) ∈ sector r a b) := by
  have hcone := eventually_cone_iff_of_hasFDerivAt hder v C hr hv ha hb
  have hray : ContinuousAt (fun t : ℝ => H x + t • v) 0 := by fun_prop
  have htarget : ∀ᶠ t : ℝ in 𝓝[>] 0, H x + t • v ∈ H.target := by
    apply (hray.tendsto.mono_left nhdsWithin_le_nhds).eventually
    simpa using H.open_target.mem_nhds (H.map_source hx)
  filter_upwards [hcone, htarget] with t ht hyt
  rw [H.left_inv hx] at ht
  rw [← ht]
  constructor
  · rintro ⟨z, ⟨hz, hcz⟩, he⟩
    have hz' : H.symm (H x + t • v) = z := by rw [← he, H.left_inv hz]
    change C (z - x) ∈ sector r a b at hcz
    rw [hz']
    exact hcz
  · intro ht
    exact ⟨H.symm (H x + t • v), ⟨H.map_target hyt, ht⟩, H.right_inv hyt⟩


/-- Actual atlas transitions, with cone-image ray tests controlled by the
true inverse intrinsic Jacobian. This supplies the domain-ray test used by
occupied sectors without assuming any region/corner correspondence. -/
theorem exists_atlas_transition_with_cone_images
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (e d : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    let L := ((K.equiv e he p hp).symm.trans (K.equiv d hd p hpd)).toContinuousLinearEquiv
    ∃ H : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2),
      (e p).val ∈ H.source ∧ H (e p).val = (d p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H (e p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H.symm (d p).val ∧
      ((fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val)) ∧
      ((fun q => H.symm (d q).val) =ᶠ[𝓝 p] (fun q => (e q).val)) ∧
      (∀ (v : Euclidean 2) (C : Euclidean 2 →L[ℝ] ℂ) (r a b : ℝ),
        0 < r → C (L.symm v) ∈ Complex.slitPlane →
        Complex.arg (C (L.symm v)) ≠ a → Complex.arg (C (L.symm v)) ≠ b →
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          ((d p).val + t • v ∈
            H '' (H.source ∩ (fun z => C (z - (e p).val)) ⁻¹' sector r a b) ↔
            t • C (L.symm v) ∈ sector r a b)) := by
  dsimp only
  obtain ⟨H, hx, hbase, hsm, hsmi, hder, hderi, hrep, hrepi⟩ :=
    exists_atlas_transition_localDiffeomorph S K e d he hd p hp hpd
  refine ⟨H, hx, hbase, hsm, hsmi, hrep, hrepi, ?_⟩
  intro v C r a b hr hv ha hb
  have hderi' := hderi
  rw [← hbase] at hderi'
  have hh := eventually_image_cone_iff_inverse_derivative H (e p).val hx hderi' v C hr hv ha hb
  rw [hbase] at hh
  convert! hh using 1

end ConeStability
section BoundaryRayCones
open Complex Filter
open scoped Real _root_.Topology
lemma branchCoordinate_ne_zero {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    branchCoordinate u v ≠ 0 := by
  exact mul_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hu)) hv

lemma branchCoordinate_self (u : ℂ) : branchCoordinate u u = -((‖u‖ ^ 2 : ℝ) : ℂ) := by
  unfold branchCoordinate
  rw [neg_mul]
  congr 1
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.conj_mul' u

lemma branchCoordinate_self_arg {u : ℂ} (hu : u ≠ 0) :
    arg (branchCoordinate u u) = Real.pi := by
  rw [branchCoordinate_self, ← Complex.ofReal_neg]
  exact Complex.arg_ofReal_of_neg (neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hu)))

lemma branchCoordinate_arg_ne_iff {u v w : ℂ} (hu : u ≠ 0)
    (hv : v ≠ 0) (hw : w ≠ 0) :
    arg (branchCoordinate u v) ≠ arg (branchCoordinate u w) ↔ ¬SameRay ℝ v w := by
  let c : ℂ := -star u
  have hc : c ≠ 0 := neg_ne_zero.mpr (star_ne_zero.mpr hu)
  let L : ℂ ≃ₗ[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℂ ℂ c hc).restrictScalars ℝ
  have h : SameRay ℝ (branchCoordinate u v) (branchCoordinate u w) ↔ SameRay ℝ v w :=
    SameRay.sameRay_map_iff L
  rw [Complex.sameRay_iff, or_iff_right (branchCoordinate_ne_zero hu hv),
    or_iff_right (branchCoordinate_ne_zero hu hw)] at h
  exact h.not

lemma branchCoordinate_mem_slitPlane {u v : ℂ} (hu : u ≠ 0)
    (hv : v ≠ 0) (hvu : ¬SameRay ℝ v u) : branchCoordinate u v ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨?_, branchCoordinate_ne_zero hu hv⟩
  rw [← branchCoordinate_self_arg hu]
  exact (branchCoordinate_arg_ne_iff hu hv hu).2 hvu


theorem eventually_raySector_iff_of_hasDerivAt
    {F : ℝ → ℂ} {v u w : ℂ} {r : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hvu : ¬SameRay ℝ v u) (hvw : ¬SameRay ℝ v w) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (F t ∈ raySector r u w ↔
        arg (branchCoordinate u v) ∈ Ioo (-Real.pi) (arg (branchCoordinate u w))) := by
  have hrot : HasDerivAt (fun t => branchCoordinate u (F t)) (branchCoordinate u v) 0 :=
    hF.const_mul (-star u)
  exact AngularSector.eventually_sector_iff_of_hasDerivAt hrot (by simp [branchCoordinate, h0]) hr
    (branchCoordinate_mem_slitPlane hu hv hvu)
    (ne_of_gt (Complex.neg_pi_lt_arg _)) ((branchCoordinate_arg_ne_iff hu hv hw).2 hvw)

theorem eventually_raySector_iff_derivative_ray
    {F : ℝ → ℂ} {v u w : ℂ} {r : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hvu : ¬SameRay ℝ v u) (hvw : ¬SameRay ℝ v w) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ raySector r u w ↔ t • v ∈ raySector r u w) := by
  have hlin : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const v using 1 <;> simp
  filter_upwards [eventually_raySector_iff_of_hasDerivAt hF h0 hr hu hw hv hvu hvw,
    eventually_raySector_iff_of_hasDerivAt hlin (zero_smul ℝ v) hr hu hw hv hvu hvw]
    with t ht hlin
  exact ht.trans hlin.symm


lemma not_sameRay_iff_normalize_ne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    ¬SameRay ℝ u v ↔ NormedSpace.normalize u ≠ NormedSpace.normalize v := by
  exact (sameRay_iff_inv_norm_smul_eq_of_ne hu hv).not

theorem eventually_rayCone_iff_of_hasFDerivAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E →L[ℝ] F} {x : E} (hf : HasFDerivAt f L x)
    (v : E) (C : F →L[ℝ] ℂ) {r : ℝ} {u w : ℂ} (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : C (L v) ≠ 0)
    (hvu : ¬SameRay ℝ (C (L v)) u) (hvw : ¬SameRay ℝ (C (L v)) w) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (C (f (x + t • v) - f x) ∈ raySector r u w ↔
        t • C (L v) ∈ raySector r u w) := by
  have hd : HasDerivAt (fun t : ℝ => C (f (x + t • v) - f x)) (C (L v)) 0 := by
    simpa only [Function.comp_def] using
      C.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_transition_ray hf v)
  exact eventually_raySector_iff_derivative_ray hd (by simp) hr hu hw hv hvu hvw

theorem eventually_image_rayCone_iff_inverse_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : OpenPartialHomeomorph E F) (x : E) (hx : x ∈ H.source)
    {L : F →L[ℝ] E} (hder : HasFDerivAt H.symm L (H x))
    (v : F) (C : E →L[ℝ] ℂ) {r : ℝ} {u w : ℂ} (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : C (L v) ≠ 0)
    (hvu : ¬SameRay ℝ (C (L v)) u) (hvw : ¬SameRay ℝ (C (L v)) w) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (H x + t • v ∈ H '' (H.source ∩ (fun z => C (z - x)) ⁻¹' raySector r u w) ↔
        t • C (L v) ∈ raySector r u w) := by
  have hcone := eventually_rayCone_iff_of_hasFDerivAt hder v C hr hu hw hv hvu hvw
  have hray : ContinuousAt (fun t : ℝ => H x + t • v) 0 := by fun_prop
  have htarget : ∀ᶠ t : ℝ in 𝓝[>] 0, H x + t • v ∈ H.target := by
    apply (hray.tendsto.mono_left nhdsWithin_le_nhds).eventually
    simpa using H.open_target.mem_nhds (H.map_source hx)
  filter_upwards [hcone, htarget] with t ht hyt
  rw [H.left_inv hx] at ht
  rw [← ht]
  constructor
  · rintro ⟨z, ⟨hz, hcz⟩, he⟩
    have hz' : H.symm (H x + t • v) = z := by rw [← he, H.left_inv hz]
    change C (z - x) ∈ raySector r u w at hcz
    rw [hz']
    exact hcz
  · intro ht
    exact ⟨H.symm (H x + t • v), ⟨H.map_target hyt, ht⟩, H.right_inv hyt⟩


end BoundaryRayCones

section CoordinateDomainGerms
open Filter
open scoped _root_.Topology
/-- Cutting a set by a neighborhood of a source point does not change the
ambient coordinate germ of its image. This also holds for half-space charts. -/
theorem coordinateImage_inter_nhds
    {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (d : ModelChart n kind M) (p : M) (hp : p ∈ d.source)
    (W : Set M) (hW : IsOpen W) (hpW : p ∈ W)
    (A : Set M) (hA : A ⊆ d.source) :
    ∀ᶠ y : Euclidean n in 𝓝 (d p).val,
      (y ∈ (fun q => (d q).val) '' A ↔
        y ∈ (fun q => (d q).val) '' (A ∩ W)) := by
  have hO : IsOpen (d.target ∩ d.symm ⁻¹' W) :=
    d.continuousOn_symm.isOpen_inter_preimage d.open_target hW
  obtain ⟨V, hV, heq⟩ := (Topology.IsInducing.subtypeVal).isOpen_iff.mp hO
  have hpV : (d p).val ∈ V := by
    change d p ∈ Subtype.val ⁻¹' V
    rw [heq]
    exact ⟨d.map_source hp, by simpa only [mem_preimage, d.left_inv hp] using hpW⟩
  filter_upwards [hV.mem_nhds hpV] with y hy
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqw : q ∈ W := by
      have hh : d q ∈ d.target ∩ d.symm ⁻¹' W := by
        rw [← heq]
        exact hy
      simpa only [mem_preimage, d.left_inv (hA hq)] using hh.2
    exact ⟨q, ⟨hq, hqw⟩, rfl⟩
  · rintro ⟨q, ⟨hq, _⟩, rfl⟩
    exact ⟨q, hq, rfl⟩

/-- Genuine coordinate agreement gives an ambient germ identity for images
of every subset. No regularity or cone shape of that subset is assumed. -/
theorem exists_coordinateImage_germ
    {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (e d : ModelChart n kind M) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (H : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hx : (e p).val ∈ H.source)
    (hrep : (fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val)) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ e.source ∩ d.source ∧
      (∀ q ∈ W, (e q).val ∈ H.source) ∧
      ∀ A : Set M, A ⊆ d.source → ∀ᶠ y : Euclidean n in 𝓝 (d p).val,
        (y ∈ (fun q => (d q).val) '' A ↔
          y ∈ H '' ((fun q => (e q).val) '' (A ∩ W))) := by
  have hg : ∀ᶠ q in 𝓝 p, q ∈ e.source ∧ q ∈ d.source ∧
      (e q).val ∈ H.source ∧ H (e q).val = (d q).val := by
    filter_upwards [e.open_source.mem_nhds hp, d.open_source.mem_nhds hpd,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
        (H.open_source.mem_nhds hx), hrep] with q hqe hqd hqH hqrep
    exact ⟨hqe, hqd, hqH, hqrep⟩
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hg
  refine ⟨W, hW, hpW, fun q hq => ⟨(hWsub hq).1, (hWsub hq).2.1⟩,
    fun q hq => (hWsub hq).2.2.1, ?_⟩
  intro A hA
  have heq : (fun q => (d q).val) '' (A ∩ W) =
      H '' ((fun q => (e q).val) '' (A ∩ W)) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(e q).val, ⟨q, hq, rfl⟩, (hWsub hq.2).2.2.2⟩
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (hWsub hq.2).2.2.2.symm⟩
  simpa only [heq] using coordinateImage_inter_nhds d p hpd W hW hpW A hA

end CoordinateDomainGerms

section ComponentGerms
open Filter
open scoped _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In an open positive cone, a curve and its tangent ray occupy the same
actual connected component; an extra convex model restriction is allowed. -/
theorem eventually_connectedComponentIn_eq_of_tangent
    {F : ℝ → E} {v : E} {A K : Set E}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0)
    (hA : IsOpen A) (hv : v ∈ A)
    (hcone : ∀ t : ℝ, 0 < t → ∀ z ∈ A, t • z ∈ A)
    (hK : Convex ℝ K)
    (hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ K ∧ t • v ∈ K) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      F t ∈ A ∩ K ∧ t • v ∈ A ∩ K ∧
      connectedComponentIn (A ∩ K) (F t) =
        connectedComponentIn (A ∩ K) (t • v) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA v hv
  have hs : Tendsto (fun t : ℝ => t⁻¹ • F t) (𝓝[>] 0) (𝓝 v) := by
    simpa only [zero_add, h0, sub_zero] using hF.tendsto_slope_zero_right
  have hsmall := hs.eventually (Metric.ball_mem_nhds v hε)
  filter_upwards [self_mem_nhdsWithin, hsmall, hmodel] with t ht hsmall hmodel
  have ht : 0 < t := ht
  let B : Set E := (fun z : E => t • z) '' Metric.ball v ε ∩ K
  have hconv : Convex ℝ B :=
    ((convex_ball v ε).linear_image (LinearMap.lsmul ℝ E t)).inter hK
  have hsub : B ⊆ A ∩ K := by
    rintro z ⟨⟨w, hw, rfl⟩, hKz⟩
    exact ⟨hcone t ht w (hball hw), hKz⟩
  have hFt : F t ∈ B := by
    refine ⟨⟨t⁻¹ • F t, hsmall, ?_⟩, hmodel.1⟩
    simp [smul_smul, ht.ne']
  have htv : t • v ∈ B := by
    exact ⟨⟨v, Metric.mem_ball_self hε, rfl⟩, hmodel.2⟩
  exact ⟨hsub hFt, hsub htv,
    connectedComponentIn_eq (hconv.isPreconnected.subset_connectedComponentIn hFt hsub htv)⟩


lemma isClosed_closedRays {n : ℕ} (d : Fin n → E) :
    IsClosed (closedRays d) := by
  exact isClosed_singleton.union (isClosed_iUnion_of_finite fun i =>
    isClosedMap_smul_left (d i) _ isClosed_Ici)

lemma closedRays_compl_smul {n : ℕ} (d : Fin n → E)
    (t : ℝ) (ht : 0 < t) (z : E) (hz : z ∈ (closedRays d)ᶜ) :
    t • z ∈ (closedRays d)ᶜ := by
  intro hmem
  apply hz
  rcases hmem with hzero | hmem
  · left
    have hzero' : t • z = 0 := hzero
    simpa only [smul_eq_zero, ht.ne', false_or, mem_singleton_iff] using hzero'
  · right
    obtain ⟨i, r, hr, he⟩ := mem_iUnion.mp hmem
    change r • d i = _ at he
    apply mem_iUnion.mpr
    refine ⟨i, r / t, div_nonneg hr ht.le, ?_⟩
    calc
      (r / t) • d i = t⁻¹ • (r • d i) := by
        rw [smul_smul, div_eq_inv_mul]
      _ = t⁻¹ • (t • z) := by rw [he]
      _ = z := by simp [smul_smul, ht.ne']

lemma not_mem_closedRays_of_normalize {n : ℕ} (d : Fin n → E) {v : E}
    (hv : v ≠ 0) (hdir : ∀ i, NormedSpace.normalize v ≠ NormedSpace.normalize (d i)) :
    v ∈ (closedRays d)ᶜ := by
  intro hmem
  rcases hmem with hzero | hmem
  · exact hv hzero
  · obtain ⟨i, r, hr, he⟩ := mem_iUnion.mp hmem
    change r • d i = _ at he
    have hr0 : r ≠ 0 := by
      intro hr0
      apply hv
      rw [← he, hr0, zero_smul]
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    apply hdir i
    rw [← he, NormedSpace.normalize_smul_of_pos hrpos]

/-- Finite exact graph rays control the component of any curve with the
same nonboundary tangent. No angular-sector/region correspondence is assumed.
The convex set K may be the translated half-space model. -/
theorem eventually_connectedComponentIn_eq_off_finite_rays
    {n : ℕ} (d : Fin n → E) {F : ℝ → E} {v : E} {K : Set E}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hv : v ≠ 0)
    (hdir : ∀ i, NormedSpace.normalize v ≠ NormedSpace.normalize (d i))
    (hK : Convex ℝ K)
    (hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ K ∧ t • v ∈ K) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      F t ∈ (closedRays d)ᶜ ∩ K ∧ t • v ∈ (closedRays d)ᶜ ∩ K ∧
      connectedComponentIn ((closedRays d)ᶜ ∩ K) (F t) =
        connectedComponentIn ((closedRays d)ᶜ ∩ K) (t • v) :=
  eventually_connectedComponentIn_eq_of_tangent hF h0
    (isClosed_closedRays d).isOpen_compl
    (not_mem_closedRays_of_normalize d hv hdir)
    (closedRays_compl_smul d) hK hmodel


/-- The same result inside a prescribed local ball, as required for a
finite graph star neighborhood. -/
theorem eventually_connectedComponentIn_eq_off_finite_rays_ball
    {n : ℕ} (d : Fin n → E) {F : ℝ → E} {v : E} {K : Set E} {R : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hv : v ≠ 0)
    (hdir : ∀ i, NormedSpace.normalize v ≠ NormedSpace.normalize (d i))
    (hK : Convex ℝ K) (hR : 0 < R)
    (hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ K ∧ t • v ∈ K) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      F t ∈ (closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R) ∧
      t • v ∈ (closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R) ∧
      connectedComponentIn ((closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R)) (F t) =
        connectedComponentIn ((closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R)) (t • v) := by
  have hFb : ∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ Metric.ball 0 R := by
    apply hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.eventually
    change Metric.ball 0 R ∈ 𝓝 (F 0)
    rw [h0]
    exact Metric.ball_mem_nhds (0 : E) hR
  have hvb : ∀ᶠ t : ℝ in 𝓝[>] 0, t • v ∈ Metric.ball 0 R := by
    have hcont : ContinuousAt (fun t : ℝ => t • v) 0 := by fun_prop
    apply hcont.tendsto.mono_left nhdsWithin_le_nhds |>.eventually
    change Metric.ball 0 R ∈ 𝓝 ((0 : ℝ) • v)
    rw [zero_smul]
    exact Metric.ball_mem_nhds (0 : E) hR
  apply eventually_connectedComponentIn_eq_off_finite_rays d hF h0 hv hdir
    (hK.inter (convex_ball 0 R))
  filter_upwards [hmodel, hFb, hvb] with t hm hF hv
  exact ⟨⟨hm.1, hF⟩, hm.2, hv⟩

lemma connectedComponents_mk_eq_of_componentIn_eq {U : Set E} {x y : E}
    (hx : x ∈ U) (hy : y ∈ U)
    (heq : connectedComponentIn U x = connectedComponentIn U y) :
    ConnectedComponents.mk (⟨x, hx⟩ : U) = ConnectedComponents.mk (⟨y, hy⟩ : U) := by
  apply ConnectedComponents.coe_eq_coe.mpr
  rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy] at heq
  exact Subtype.val_injective.image_injective heq


end ComponentGerms

section MetricSectorCones
open Complex Filter
open scoped Real _root_.Topology
lemma positiveAngle_coe_of_pos_of_le_two_pi {theta : ℝ}
    (hpos : 0 < theta) (hle : theta ≤ 2 * Real.pi) :
    positiveAngle (theta : Real.Angle) = theta := by
  unfold positiveAngle
  by_cases hpi : theta ≤ Real.pi
  · have he : (theta : Real.Angle).toReal = theta :=
      Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], hpi⟩
    rw [he, if_pos hpos]
  · have he : (theta : Real.Angle).toReal = theta - 2 * Real.pi :=
      Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr
        ⟨lt_of_not_ge hpi, by linarith [Real.pi_pos]⟩
    rw [he, if_neg (by linarith)]
    ring

lemma branchCoordinate_angle {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    ((arg (branchCoordinate u v) + Real.pi : ℝ) : Real.Angle) =
      (arg v : Real.Angle) - arg u := by
  rw [Real.Angle.coe_add]
  unfold branchCoordinate
  rw [Complex.arg_mul_coe_angle (neg_ne_zero.mpr (star_ne_zero.mpr hu)) hv,
    Complex.arg_neg_coe_angle (star_ne_zero.mpr hu)]
  have hstar : (arg (star u) : Real.Angle) = -(arg u : Real.Angle) := by
    simpa only [starRingEnd_apply] using Complex.arg_conj_coe_angle u
  rw [hstar]
  have hpi : (Real.pi : Real.Angle) + (Real.pi : Real.Angle) = 0 := by
    rw [← Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi]
  calc
    -(arg u : Real.Angle) + (Real.pi : Real.Angle) + arg v + (Real.pi : Real.Angle) =
        (arg v : Real.Angle) - arg u + ((Real.pi : Real.Angle) + (Real.pi : Real.Angle)) := by abel
    _ = _ := by rw [hpi, add_zero]

lemma positiveAngle_arg_sub {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    :
    positiveAngle ((arg v : Real.Angle) - arg u) = arg (branchCoordinate u v) + Real.pi := by
  rw [← branchCoordinate_angle hu hv]
  exact positiveAngle_coe_of_pos_of_le_two_pi
    (by linarith [Complex.neg_pi_lt_arg (branchCoordinate u v)])
    (by linarith [Complex.arg_le_pi (branchCoordinate u v)])

lemma raySector_iff_positiveAngle_lt {u v w : ℂ} {r : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    :
    v ∈ raySector r u w ↔
      ‖branchCoordinate u v‖ < r ∧
        positiveAngle ((arg v : Real.Angle) - arg u) <
          positiveAngle ((arg w : Real.Angle) - arg u) := by
  rw [positiveAngle_arg_sub hu hv, positiveAngle_arg_sub hu hw]
  change (branchCoordinate u v ≠ 0 ∧ ‖branchCoordinate u v‖ < r ∧
    -Real.pi < arg (branchCoordinate u v) ∧
    arg (branchCoordinate u v) < arg (branchCoordinate u w)) ↔ _
  constructor
  · intro h
    exact ⟨h.2.1, by linarith [h.2.2.2]⟩
  · intro h
    refine ⟨branchCoordinate_ne_zero hu hv, h.1, Complex.neg_pi_lt_arg _, ?_⟩
    exact lt_of_add_lt_add_right h.2


attribute [local instance] Complex.finrank_real_complex_fact

lemma positiveAngle_complex_oangle {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    positiveAngle (Complex.orientation.oangle u v) = arg (branchCoordinate u v) + Real.pi := by
  have hu' : (starRingEnd ℂ) u ≠ 0 := by
    simpa only [starRingEnd_apply] using star_ne_zero.mpr hu
  rw [Complex.oangle, Complex.arg_mul_coe_angle hu' hv,
    Complex.arg_conj_coe_angle]
  convert positiveAngle_arg_sub hu hv using 2 <;> abel

lemma raySector_iff_positive_oangle_lt {u v w : ℂ} {r : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    v ∈ raySector r u w ↔
      ‖branchCoordinate u v‖ < r ∧
        positiveAngle (Complex.orientation.oangle u v) <
          positiveAngle (Complex.orientation.oangle u w) := by
  rw [positiveAngle_complex_oangle hu hv, positiveAngle_complex_oangle hu hw]
  rw [raySector_iff_positiveAngle_lt hu hv hw,
    positiveAngle_arg_sub hu hv, positiveAngle_arg_sub hu hw]

lemma positiveAngle_oangle_map_complex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (C : E ≃ₗᵢ[ℝ] ℂ)
    (hC : Orientation.map (Fin 2) C.toLinearEquiv o = Complex.orientation)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    positiveAngle (o.oangle u v) = arg (branchCoordinate (C u) (C v)) + Real.pi := by
  rw [o.oangle_map_complex C hC, ← Complex.oangle]
  have huC : C u ≠ 0 := C.map_ne_zero_iff.mpr hu
  have hvC : C v ≠ 0 := C.map_ne_zero_iff.mpr hv
  exact positiveAngle_complex_oangle huC hvC

lemma raySector_iff_oangle_map_complex_lt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (C : E ≃ₗᵢ[ℝ] ℂ)
    (hC : Orientation.map (Fin 2) C.toLinearEquiv o = Complex.orientation)
    {u v w : E} {r : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    C v ∈ raySector r (C u) (C w) ↔
      ‖branchCoordinate (C u) (C v)‖ < r ∧
        positiveAngle (o.oangle u v) < positiveAngle (o.oangle u w) := by
  rw [positiveAngle_oangle_map_complex o C hC hu hv,
    positiveAngle_oangle_map_complex o C hC hu hw]
  have huC : C u ≠ 0 := C.map_ne_zero_iff.mpr hu
  have hvC : C v ≠ 0 := C.map_ne_zero_iff.mpr hv
  have hwC : C w ≠ 0 := C.map_ne_zero_iff.mpr hw
  rw [raySector_iff_positiveAngle_lt huC hvC hwC,
    positiveAngle_arg_sub huC hvC, positiveAngle_arg_sub huC hwC]


lemma exists_oriented_complex_isometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)) :
    ∃ C : E ≃ₗᵢ[ℝ] ℂ,
      Orientation.map (Fin 2) C.toLinearEquiv o = Complex.orientation := by
  let b := o.finOrthonormalBasis (by decide : 0 < 2) Fact.out
  let C := b.equiv Complex.orthonormalBasisOneI (Equiv.refl (Fin 2))
  refine ⟨C, ?_⟩
  have hb : b.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  have hmap : b.toBasis.map C.toLinearEquiv = Complex.orthonormalBasisOneI.toBasis := by
    ext i
    exact b.equiv_apply_basis Complex.orthonormalBasisOneI (Equiv.refl (Fin 2)) i
  rw [← hb, ← Module.Basis.orientation_map, hmap]
  rfl


lemma eventually_raySector_iff_positive_oangle
    {F : ℝ → ℂ} {v u w : ℂ} {r : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hvu : ¬SameRay ℝ v u) (hvw : ¬SameRay ℝ v w) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (F t ∈ raySector r u w ↔
        positiveAngle (Complex.orientation.oangle u v) <
          positiveAngle (Complex.orientation.oangle u w)) := by
  filter_upwards [eventually_raySector_iff_of_hasDerivAt hF h0 hr hu hw hv hvu hvw]
    with t ht
  rw [positiveAngle_complex_oangle hu hv, positiveAngle_complex_oangle hu hw]
  exact ht.trans ⟨fun h => by linarith [h.2],
    fun h => ⟨Complex.neg_pi_lt_arg _, by linarith⟩⟩

lemma eventually_raySector_mem_iff_positive_oangle
    {F : ℝ → ℂ} {v u w : ℂ} {r : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hvu : ¬SameRay ℝ v u) (hvw : ¬SameRay ℝ v w) :
    (∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ raySector r u w) ↔
      positiveAngle (Complex.orientation.oangle u v) <
        positiveAngle (Complex.orientation.oangle u w) := by
  have hh := eventually_raySector_iff_positive_oangle hF h0 hr hu hw hv hvu hvw
  exact (Filter.eventually_congr hh).trans (eventually_const)


open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.TangentBundleData
open P202.MetricData P202.SurfaceBoundaryData

lemma exists_original_tangent_sector_coordinates
    {kind : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (c : ModelChart 2 kind M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)) :
    let K := (tangentStructure S).fiberCoordinates.equiv c hc p hp
    ∃ C : Euclidean 2 →L[ℝ] ℂ, Function.Injective C ∧
      ∀ u v : Euclidean 2, u ≠ 0 → v ≠ 0 →
        P202Specs.RegionalCornerTransport.positiveAngle
          (P202Specs.RegionalCornerTransport.tangentAngle g p o (K.symm u) (K.symm v)) =
            arg (branchCoordinate (C u) (C v)) + Real.pi := by
  let K := (tangentStructure S).fiberCoordinates.equiv c hc p hp
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  obtain ⟨I, hI⟩ := exists_oriented_complex_isometry o
  let C := K.symm.toContinuousLinearEquiv.trans I.toContinuousLinearEquiv
  refine ⟨C.toContinuousLinearMap, C.injective, ?_⟩
  intro u v hu hv
  have huK : K.symm u ≠ 0 := K.symm.map_ne_zero_iff.mpr hu
  have hvK : K.symm v ≠ 0 := K.symm.map_ne_zero_iff.mpr hv
  exact positiveAngle_oangle_map_complex o I hI huK hvK

end MetricSectorCones

section RegionalDomainGerms
open Filter
open scoped _root_.Topology
open SmoothManifolds.TangentBundleData
/-- The original regional domain is the literal ambient image of the original
complementary component, after the fixed Euclidean-to-plane conversion. -/
theorem regionalDomain_coordinateImage_mem
    {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (D : RegionDecomposition S)
    (r : Fin D.regionCount) (y : Euclidean 2) :
    toPlane y ∈ (D.region r).domain ↔
      y ∈ (fun q => ((D.chart r) q).val) '' regionInterior D r := by
  rw [← D.domain_coordinates r]
  constructor
  · rintro ⟨q, hq, hqy⟩
    refine ⟨q, hq, toPlane.injective ?_⟩
    exact hqy
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩

/-- The coordinate-image germ may be represented inside any prescribed
neighborhood. This lets an actual graph-star neighborhood be chosen later. -/
theorem exists_coordinateImage_germ_within
    {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (e d : ModelChart n kind M) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (H : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hx : (e p).val ∈ H.source)
    (hrep : (fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val))
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧ W ⊆ e.source ∩ d.source ∧
      (∀ q ∈ W, (e q).val ∈ H.source) ∧
      ∀ A : Set M, A ⊆ d.source → ∀ᶠ y : Euclidean n in 𝓝 (d p).val,
        (y ∈ (fun q => (d q).val) '' A ↔
          y ∈ H '' ((fun q => (e q).val) '' (A ∩ W))) := by
  obtain ⟨W, hW, hpW, hWsub, hWH, _⟩ :=
    exists_coordinateImage_germ e d p hp hpd H hx hrep
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hrep
  let W' := (W ∩ O) ∩ V
  have hW' : IsOpen W' := (hW.inter hO).inter hV
  have hpW' : p ∈ W' := ⟨⟨hpW, hpO⟩, hpV⟩
  refine ⟨W', hW', hpW', fun q hq => hq.1.2,
    fun q hq => hWsub hq.1.1, fun q hq => hWH q hq.1.1, ?_⟩
  intro A hA
  have heq : (fun q => (d q).val) '' (A ∩ W') =
      H '' ((fun q => (e q).val) '' (A ∩ W')) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(e q).val, ⟨q, hq, rfl⟩, hVsub hq.2.2⟩
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (hVsub hq.2.2).symm⟩
  simpa only [heq] using coordinateImage_inter_nhds d p hpd W' hW' hpW' A hA

/-- For any genuine star chart and original region chart, the ambient germ of
the actual planar domain is the image under their actual ambient transition
of the actual regional component in the star chart. This is a statement about
every subset, specialized here to the actual regional domain, and does not
assume that a corner corresponds to any particular sector. -/
theorem exists_regionalDomain_atlas_germ
    {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : FiberCoordinates S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hpd : p ∈ (D.chart r).source)
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    let L := ((K.equiv e he p hp).symm.trans
      (K.equiv (D.chart r) (D.chart_mem r) p hpd)).toContinuousLinearEquiv
    ∃ (H : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2)) (W : Set M),
      (e p).val ∈ H.source ∧ H (e p).val = ((D.chart r) p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H (e p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H.symm ((D.chart r) p).val ∧
      HasFDerivAt H (L : Euclidean 2 →L[ℝ] Euclidean 2) (e p).val ∧
      HasFDerivAt H.symm (L.symm : Euclidean 2 →L[ℝ] Euclidean 2)
        ((D.chart r) p).val ∧
      ((fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => ((D.chart r) q).val)) ∧
      ((fun q => H.symm ((D.chart r) q).val) =ᶠ[𝓝 p] (fun q => (e q).val)) ∧
      IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧ W ⊆ e.source ∩ (D.chart r).source ∧
      (∀ q ∈ W, (e q).val ∈ H.source) ∧
      (∀ᶠ y : Euclidean 2 in 𝓝 ((D.chart r) p).val,
        (toPlane y ∈ (D.region r).domain ↔
          y ∈ H '' ((fun q => (e q).val) '' (regionInterior D r ∩ W)))) ∧
      (∀ v : Plane, ∀ᶠ t : ℝ in 𝓝[>] 0,
        (coordinates (D.chart r) p + t • v ∈ (D.region r).domain ↔
          toPlane.symm (coordinates (D.chart r) p + t • v) ∈
            H '' ((fun q => (e q).val) '' (regionInterior D r ∩ W)))) := by
  dsimp only
  obtain ⟨H, hx, hbase, hsm, hsmi, hder, hderi, hrep, hrepi⟩ :=
    exists_atlas_transition_localDiffeomorph S K e (D.chart r) he (D.chart_mem r) p hp hpd
  obtain ⟨W, hW, hpW, hWO, hWsub, hWH, himage⟩ :=
    exists_coordinateImage_germ_within e (D.chart r) p hp hpd H hx hrep O hO hpO
  have hA : regionInterior D r ⊆ (D.chart r).source := by
    intro q hq
    exact D.closure_in_chart r (subset_closure hq)
  have hdomain : ∀ᶠ y : Euclidean 2 in 𝓝 ((D.chart r) p).val,
      (toPlane y ∈ (D.region r).domain ↔
        y ∈ H '' ((fun q => (e q).val) '' (regionInterior D r ∩ W))) := by
    filter_upwards [himage (regionInterior D r) hA] with y hy
    exact (regionalDomain_coordinateImage_mem D r y).trans hy
  refine ⟨H, W, hx, hbase, hsm, hsmi, hder, hderi, hrep, hrepi,
    hW, hpW, hWO, hWsub, hWH, hdomain, ?_⟩
  intro v
  have hc : ContinuousAt (fun t : ℝ =>
      toPlane.symm (coordinates (D.chart r) p + t • v)) 0 := by fun_prop
  have ht : Tendsto (fun t : ℝ =>
      toPlane.symm (coordinates (D.chart r) p + t • v))
      (𝓝[>] 0) (𝓝 ((D.chart r) p).val) := by
    simpa [coordinates] using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using ht.eventually hdomain

end RegionalDomainGerms

section ModelRays
open Filter
open scoped _root_.Topology
/-- A tangent to a curve in the actual model has a forward ray in the model,
including at the half-space face. -/
theorem eventually_tangent_ray_in_model
    {kind : SmoothManifolds.ModelKind} (p : ModelSpace 2 kind)
    {F : ℝ → Plane} {v : Plane} (hF : HasDerivAt F v 0) (h0 : F 0 = 0)
    (hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0,
      toPlane.symm (toPlane p.val + F t) ∈ modelSet 2 kind) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      toPlane.symm (toPlane p.val + t • v) ∈ modelSet 2 kind := by
  cases kind with
  | euclidean => exact Eventually.of_forall (fun t => trivial)
  | halfSpace =>
    have hp : 0 ≤ p.val 1 := p.property
    by_cases ha : p.val 1 = 0
    · have hs : Tendsto (fun t : ℝ => (t⁻¹ • F t) 1) (𝓝[>] 0) (𝓝 (v 1)) := by
        have ht : Tendsto (fun t : ℝ => t⁻¹ • F t) (𝓝[>] 0) (𝓝 v) := by
          simpa only [zero_add, h0, sub_zero] using hF.tendsto_slope_zero_right
        have hc : Continuous (fun z : Plane => z 1) := by fun_prop
        exact hc.continuousAt.tendsto.comp ht
      have hv : 0 ≤ v 1 := by
        apply isClosed_Ici.mem_of_tendsto hs
        filter_upwards [self_mem_nhdsWithin, hmodel] with t ht hm
        have ht : 0 < t := ht
        have hm' : 0 ≤ (toPlane.symm (toPlane p.val + F t)) 1 := hm
        have hft : 0 ≤ F t 1 := by simpa [toPlane, ha] using hm'
        exact mul_nonneg (inv_nonneg.mpr ht.le) hft
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : 0 < t := ht
      change 0 ≤ (toPlane.symm (toPlane p.val + t • v)) 1
      simpa [toPlane, ha] using mul_nonneg ht.le hv
    · have hpos : 0 < p.val 1 := lt_of_le_of_ne hp (Ne.symm ha)
      have hcont : ContinuousAt (fun t : ℝ => (toPlane.symm (toPlane p.val + t • v)) 1) 0 := by
        fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < (toPlane.symm (toPlane p.val + t • v)) 1 :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds |>.eventually
        (lt_mem_nhds (show 0 < (toPlane.symm (toPlane p.val + (0 : ℝ) • v)) 1 from by
          simpa only [zero_smul, add_zero, toPlane.symm_apply_apply] using hpos))
      filter_upwards [he] with t ht
      exact ht.le
end ModelRays
section GraphStars
open Filter
open scoped _root_.Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202Specs.SurfaceRegionConstruction P202Specs.PlanarRegionTopology

variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}

lemma convex_centeredModel (g : GraphStar G p) : Convex ℝ (centeredModel g) := by
  exact ((SmoothManifolds.convex_modelSet 2 kind).linear_preimage toPlane.symm.toLinearMap).translate_preimage_right
    (coordinates g.chart p)

/-- Literal equality between the coordinate image of an actual graph-star
complement and the model ball with its exact finite positive rays deleted. -/
theorem graphStar_centered_coordinates_image (g : GraphStar G p) :
    (fun q => coordinates g.chart q - coordinates g.chart p) ''
      (g.neighborhood \ G.carrier) =
      (closedRays g.direction)ᶜ ∩ (centeredModel g ∩ Metric.ball 0 g.radius) := by
  ext z
  constructor
  · rintro ⟨q, ⟨⟨hqs, hqb⟩, hqG⟩, rfl⟩
    have hball : ‖coordinates g.chart q - coordinates g.chart p‖ < g.radius := by
      change coordinates g.chart q ∈ Metric.ball (coordinates g.chart p) g.radius at hqb
      simpa only [Metric.mem_ball, dist_eq_norm] using hqb
    refine ⟨?_, ?_, by simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hball⟩
    · intro hmem
      apply hqG
      apply (g.graph_eq q hqs hqb).mpr
      rcases hmem with hzero | hmem
      · left
        apply g.chart.injOn hqs g.mem_source
        apply Subtype.ext
        apply toPlane.injective
        exact sub_eq_zero.mp hzero
      · obtain ⟨i, r, hr, he⟩ := mem_iUnion.mp hmem
        change r • g.direction i = coordinates g.chart q - coordinates g.chart p at he
        by_cases hr0 : r = 0
        · left
          apply g.chart.injOn hqs g.mem_source
          apply Subtype.ext
          apply toPlane.injective
          have hzero : coordinates g.chart q - coordinates g.chart p = 0 := by
            simpa only [hr0, zero_smul] using he.symm
          exact sub_eq_zero.mp hzero
        · right
          have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
          have hrr : r < g.radius := by
            rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, g.direction_unit i, mul_one]
              at hball
            exact hball
          exact ⟨i, r, hrpos, hrr, by rw [he]; abel⟩
    · change toPlane.symm (coordinates g.chart p +
        (coordinates g.chart q - coordinates g.chart p)) ∈ modelSet 2 kind
      simpa only [add_sub_cancel, coordinates, toPlane.symm_apply_apply] using (g.chart q).property
  · rintro ⟨hzr, hzmodel, hzball⟩
    let m : ModelSpace 2 kind :=
      ⟨toPlane.symm (coordinates g.chart p + z), hzmodel⟩
    have hmb : toPlane m.val ∈ Metric.ball (coordinates g.chart p) g.radius := by
      simpa only [m, toPlane.apply_symm_apply, Metric.mem_ball, dist_eq_norm,
        add_sub_cancel_left, sub_zero] using hzball
    have hmt : m ∈ g.chart.target := g.ball_in_target m hmb
    let q := g.chart.symm m
    have hqs : q ∈ g.chart.source := g.chart.map_target hmt
    have hcoord : coordinates g.chart q = coordinates g.chart p + z := by
      unfold coordinates
      rw [show g.chart q = m from g.chart.right_inv hmt]
      exact toPlane.apply_symm_apply _
    have hqb : coordinates g.chart q ∈ Metric.ball (coordinates g.chart p) g.radius := by
      simpa only [hcoord, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hzball
    refine ⟨q, ⟨⟨hqs, hqb⟩, ?_⟩, by dsimp only; rw [hcoord]; abel⟩
    intro hqG
    apply hzr
    rcases (g.graph_eq q hqs hqb).mp hqG with hqp | ⟨i, t, ht, htr, he⟩
    · left
      change z = 0
      have heq := hcoord
      rw [hqp] at heq
      exact (add_eq_left.mp heq.symm)
    · right
      apply mem_iUnion.mpr
      refine ⟨i, t, ht.le, ?_⟩
      change t • g.direction i = z
      rw [hcoord] at he
      exact (add_left_cancel he).symm

/-- An asymptotically tangent curve and the exact derivative ray belong to
one actual component of the star's coordinate complement, including seams. -/
theorem graphStar_eventually_same_coordinate_component (g : GraphStar G p)
    {F : ℝ → Plane} {v : Plane} (hF : HasDerivAt F v 0) (h0 : F 0 = 0)
    (hv : v ≠ 0)
    (hdir : ∀ i, NormedSpace.normalize v ≠ g.direction i)
    (hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ centeredModel g ∧ t • v ∈ centeredModel g) :
    let U := (fun q => coordinates g.chart q - coordinates g.chart p) ''
      (g.neighborhood \ G.carrier)
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      F t ∈ U ∧ t • v ∈ U ∧
      connectedComponentIn U (F t) = connectedComponentIn U (t • v) := by
  dsimp only
  rw [graphStar_centered_coordinates_image]
  apply eventually_connectedComponentIn_eq_off_finite_rays_ball g.direction hF h0 hv
    ?_ (convex_centeredModel g) g.radius_pos hmodel
  intro i
  simpa only [NormedSpace.normalize_eq_self_of_norm_eq_one (g.direction_unit i)]
    using hdir i


/-- Equality of coordinate components implies equality of actual components
inside an arbitrary subset of an actual chart source. -/
theorem coordinate_component_eq_implies_component_eq
    (e : ModelChart 2 kind M) (c : Plane) (V : Set M) (hV : V ⊆ e.source)
    {x y : M} (hx : x ∈ V) (hy : y ∈ V)
    (heq : connectedComponentIn ((fun q => coordinates e q - c) '' V)
      (coordinates e x - c) = connectedComponentIn ((fun q => coordinates e q - c) '' V)
      (coordinates e y - c)) :
    ConnectedComponents.mk (⟨x, hx⟩ : V) = ConnectedComponents.mk (⟨y, hy⟩ : V) := by
  let U := (fun q => coordinates e q - c) '' V
  let f : U → ModelSpace 2 kind := fun z =>
    ⟨toPlane.symm (c + z.val), by
      obtain ⟨q, hq, hqz⟩ := z.property
      have heq : c + z.val = coordinates e q := by rw [← hqz]; dsimp only; abel
      rw [heq]
      simpa only [coordinates, toPlane.symm_apply_apply] using (e q).property⟩
  have hf : Continuous f :=
    (toPlane.symm.continuous.comp (continuous_const.add continuous_subtype_val)).subtype_mk _
  have hfp : ∀ (q : M) (hq : q ∈ V),
      f ⟨coordinates e q-c, q, hq, rfl⟩ = e q := by
    intro q hq
    apply Subtype.ext
    dsimp only [f]
    rw [add_sub_cancel]
    exact toPlane.symm_apply_apply _
  have hft : ∀ z : U, f z ∈ e.target := by
    intro z
    obtain ⟨q, hq, he⟩ := z.property
    have hz : z = ⟨coordinates e q-c, q, hq, rfl⟩ := by
      exact Subtype.ext he.symm
    rw [hz, hfp q hq]
    exact e.map_source (hV hq)
  have hin : ∀ z : U, e.symm (f z) ∈ V := by
    intro z
    obtain ⟨q, hq, he⟩ := z.property
    have hz : z = ⟨coordinates e q-c, q, hq, rfl⟩ := by
      exact Subtype.ext he.symm
    rw [hz, hfp q hq, e.left_inv (hV hq)]
    exact hq
  let inv : U → V := fun z => ⟨e.symm (f z), hin z⟩
  have hi : Continuous inv :=
    (e.symm.continuousOn.comp_continuous hf hft).subtype_mk _
  let xU : U := ⟨coordinates e x-c, x, hx, rfl⟩
  let yU : U := ⟨coordinates e y-c, y, hy, rfl⟩
  have hmk : ConnectedComponents.mk xU = ConnectedComponents.mk yU :=
    connectedComponents_mk_eq_of_componentIn_eq xU.property yU.property heq
  have hmapped : ConnectedComponents.mk (inv xU) = ConnectedComponents.mk (inv yU) :=
    ConnectedComponents.coe_eq_coe'.mpr (hi.mapsTo_connectedComponent yU
      (ConnectedComponents.coe_eq_coe'.mp hmk))
  have hix : inv xU = ⟨x, hx⟩ := by
    apply Subtype.ext
    dsimp only [inv, xU]
    rw [hfp x hx, e.left_inv (hV hx)]
  have hiy : inv yU = ⟨y, hy⟩ := by
    apply Subtype.ext
    dsimp only [inv, yU]
    rw [hfp y hy, e.left_inv (hV hy)]
  rwa [hix, hiy] at hmapped

/-- Coordinate component equality for an actual star yields equality of the
actual graph-complement components in M. -/
theorem graphStar_component_eq_of_coordinate_component_eq (g : GraphStar G p)
    {x y : M} (hx : x ∈ g.neighborhood \ G.carrier)
    (hy : y ∈ g.neighborhood \ G.carrier)
    (heq : connectedComponentIn ((fun q => coordinates g.chart q - coordinates g.chart p) ''
      (g.neighborhood \ G.carrier)) (coordinates g.chart x - coordinates g.chart p) =
      connectedComponentIn ((fun q => coordinates g.chart q - coordinates g.chart p) ''
      (g.neighborhood \ G.carrier)) (coordinates g.chart y - coordinates g.chart p)) :
    ConnectedComponents.mk (⟨x, hx.2⟩ : ↥(G.carrierᶜ : Set M)) =
      ConnectedComponents.mk (⟨y, hy.2⟩ : ↥(G.carrierᶜ : Set M)) := by
  have hlocal := coordinate_component_eq_implies_component_eq g.chart (coordinates g.chart p)
    (g.neighborhood \ G.carrier) (fun _ h => h.1.1) hx hy heq
  let inc : ↥(g.neighborhood \ G.carrier : Set M) → ↥(G.carrierᶜ : Set M) := fun z => ⟨z.val, z.property.2⟩
  have hi : Continuous inc := continuous_subtype_val.subtype_mk _
  exact ConnectedComponents.coe_eq_coe'.mpr (hi.mapsTo_connectedComponent ⟨y, hy⟩
    (ConnectedComponents.coe_eq_coe'.mp hlocal))

/-- Consequently the two points have identical membership in every original
global component, without a sector/region correspondence assumption. -/
theorem graphStar_region_mem_iff_of_coordinate_component_eq
    (D : RegionDecomposition S) (g : GraphStar D.graph p)
    {x y : M} (hx : x ∈ g.neighborhood \ D.graph.carrier)
    (hy : y ∈ g.neighborhood \ D.graph.carrier)
    (heq : connectedComponentIn ((fun q => coordinates g.chart q - coordinates g.chart p) ''
      (g.neighborhood \ D.graph.carrier)) (coordinates g.chart x - coordinates g.chart p) =
      connectedComponentIn ((fun q => coordinates g.chart q - coordinates g.chart p) ''
      (g.neighborhood \ D.graph.carrier)) (coordinates g.chart y - coordinates g.chart p))
    (r : Fin D.regionCount) :
    x ∈ componentSet D.graph.carrierᶜ (D.component r) ↔
      y ∈ componentSet D.graph.carrierᶜ (D.component r) := by
  have hmk := graphStar_component_eq_of_coordinate_component_eq g hx hy heq
  constructor
  · rintro ⟨x', hx', he⟩
    have heq : x' = ⟨x, hx.2⟩ := Subtype.ext he
    rw [heq] at hx'
    exact ⟨⟨y, hy.2⟩, hmk.symm.trans hx', rfl⟩
  · rintro ⟨y', hy', he⟩
    have heq : y' = ⟨y, hy.2⟩ := Subtype.ext he
    rw [heq] at hy'
    exact ⟨⟨x, hx.2⟩, hmk.trans hy', rfl⟩


/-- Domain-ray stability for every actual global region. The curve is only
required to have the specified derivative in a genuine star chart; the second
actual curve is the literal derivative ray in that chart. -/
theorem graphStar_eventually_region_mem_iff (D : RegionDecomposition S)
    (g : GraphStar D.graph p) (q r : ℝ → M) (v : Plane)
    (hF : HasDerivAt (fun t => coordinates g.chart (q t) - coordinates g.chart p) v 0)
    (h0 : coordinates g.chart (q 0) = coordinates g.chart p)
    (hv : v ≠ 0) (hdir : ∀ i, NormedSpace.normalize v ≠ g.direction i)
    (hqs : ∀ᶠ t : ℝ in 𝓝[>] 0, q t ∈ g.chart.source)
    (hrs : ∀ᶠ t : ℝ in 𝓝[>] 0, r t ∈ g.chart.source)
    (hray : ∀ᶠ t : ℝ in 𝓝[>] 0,
      coordinates g.chart (r t) = coordinates g.chart p + t • v) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      q t ∈ g.neighborhood \ D.graph.carrier ∧
      r t ∈ g.neighborhood \ D.graph.carrier ∧
      ∀ j : Fin D.regionCount,
        (q t ∈ componentSet D.graph.carrierᶜ (D.component j) ↔
          r t ∈ componentSet D.graph.carrierᶜ (D.component j)) := by
  let F := fun t => coordinates g.chart (q t) - coordinates g.chart p
  have hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0,
      F t ∈ centeredModel g ∧ t • v ∈ centeredModel g := by
    filter_upwards [hray] with t hrt
    constructor
    · change toPlane.symm (coordinates g.chart p +
        (coordinates g.chart (q t) - coordinates g.chart p)) ∈ modelSet 2 kind
      simpa only [add_sub_cancel, coordinates, toPlane.symm_apply_apply] using (g.chart (q t)).property
    · change toPlane.symm (coordinates g.chart p + t • v) ∈ modelSet 2 kind
      rw [← hrt]
      simpa only [coordinates, toPlane.symm_apply_apply] using (g.chart (r t)).property
  have hzero : F 0 = 0 := by dsimp only [F]; rw [h0, sub_self]
  have hc := graphStar_eventually_same_coordinate_component g hF hzero hv hdir hmodel
  filter_upwards [hc, hqs, hrs, hray] with t ht hqt hrt hrayt
  let U := (fun a => coordinates g.chart a - coordinates g.chart p) ''
    (g.neighborhood \ D.graph.carrier)
  have hmem_of_coord : ∀ (a : M), a ∈ g.chart.source →
      coordinates g.chart a - coordinates g.chart p ∈ U →
      a ∈ g.neighborhood \ D.graph.carrier := by
    intro a ha ham
    obtain ⟨b, hb, he⟩ := ham
    have hcoords : coordinates g.chart b = coordinates g.chart a :=
      sub_left_inj.mp he
    have hba : b = a := g.chart.injOn hb.1.1 ha (Subtype.ext (toPlane.injective hcoords))
    simpa only [hba] using hb
  have hqU : q t ∈ g.neighborhood \ D.graph.carrier := hmem_of_coord _ hqt ht.1
  have hrU : r t ∈ g.neighborhood \ D.graph.carrier := by
    apply hmem_of_coord _ hrt
    rw [hrayt, add_sub_cancel_left]
    exact ht.2.1
  refine ⟨hqU, hrU, ?_⟩
  intro j
  apply graphStar_region_mem_iff_of_coordinate_component_eq D g hqU hrU
  rw [hrayt, add_sub_cancel_left]
  exact ht.2.2

end GraphStars
section PlanarDomainCurveGerms
open Filter
open scoped _root_.Topology
open P202Specs.BoundaryGraphDirections P202Specs.PlaneTurning
open SmoothManifolds.TangentBundleData
open P202.BoundaryGraphDirections
open P202.MetricBoundaryTurning
open P202.MetricBoundaryTurning.BoundarySectorGraph
open P202.MetricBoundaryTurning.PresentationTangents
set_option maxHeartbeats 1200000
lemma eventually_sign_of_right_derivative {f : ℝ → ℝ} {D : ℝ}
    (hf : HasDerivWithinAt f D (Ioi 0) 0) (hzero : f 0 = 0) (hD : D ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (0 < f t ↔ 0 < D) := by
  have hs : Tendsto (fun t : ℝ => t⁻¹ * f t) (𝓝[>] 0) (𝓝 D) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hf
    convert h using 1
    funext t
    simp [slope_def_field, hzero, div_eq_mul_inv, mul_comm]
  rcases lt_or_gt_of_ne hD with hD | hD
  · filter_upwards [hs.eventually (eventually_lt_nhds hD), self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    have hneg : f t < 0 := (mul_neg_iff.mp ht).resolve_right
      (fun h => (not_lt_of_ge (inv_pos.mpr htpos').le) h.1) |>.2
    exact iff_of_false (not_lt_of_ge hneg.le) (not_lt_of_ge hD.le)
  · filter_upwards [hs.eventually (eventually_gt_nhds hD), self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    exact ⟨fun _ => hD, fun _ => (mul_pos_iff_of_pos_left (inv_pos.mpr htpos')).mp ht⟩

/-- A curve with nonzero horizontal derivative eventually stays on the
corresponding side of a graph join, so its height composition has the relevant
one-sided derivative. -/
lemma one_sided_height_comp
    {f X : ℝ → ℝ} {a mL mR x : ℝ}
    (hL : HasDerivWithinAt f mL (Iic a) a)
    (hR : HasDerivWithinAt f mR (Ici a) a)
    (hX : HasDerivAt X x 0) (hX0 : X 0 = a) (hx : x ≠ 0) :
    HasDerivWithinAt (fun t => f (X t)) ((if 0 < x then mR else mL) * x) (Ioi 0) 0 := by
  have hsign := eventually_sign_of_right_derivative
    (hX.sub_const a).hasDerivWithinAt (by simp [hX0]) hx
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hside : ∀ᶠ t : ℝ in 𝓝[>] 0, X t ≤ a := by
      filter_upwards [hsign] with t ht
      have hh : ¬0 < X t - a := by rw [ht]; exact not_lt_of_gt hneg
      linarith
    have hd := hL.comp_of_eq 0
      (hX.hasDerivWithinAt.mono (inter_subset_left : Ioi 0 ∩ X ⁻¹' Iic a ⊆ Ioi 0))
      (fun _ h => h.2) hX0.symm
    have hmem : Ioi 0 ∩ X ⁻¹' Iic a ∈ 𝓝[>] (0 : ℝ) :=
      Filter.inter_mem self_mem_nhdsWithin hside
    simpa only [not_lt_of_gt hneg, ↓reduceIte, Function.comp_def] using hd.mono_of_mem_nhdsWithin hmem
  · have hside : ∀ᶠ t : ℝ in 𝓝[>] 0, a ≤ X t := by
      filter_upwards [hsign] with t ht
      have hh : 0 < X t - a := ht.mpr hpos
      linarith
    have hd := hR.comp_of_eq 0
      (hX.hasDerivWithinAt.mono (inter_subset_left : Ioi 0 ∩ X ⁻¹' Ici a ⊆ Ioi 0))
      (fun _ h => h.2) hX0.symm
    have hmem : Ioi 0 ∩ X ⁻¹' Ici a ∈ 𝓝[>] (0 : ℝ) :=
      Filter.inter_mem self_mem_nhdsWithin hside
    simpa only [hpos, ↓reduceIte, Function.comp_def] using hd.mono_of_mem_nhdsWithin hmem

/-- Actual curved epigraph membership has precisely its tangent-ray test,
using only genuine one-sided height derivatives and transversality. -/
theorem eventually_epigraph_iff_tangent
    {f X Y : ℝ → ℝ} {a mL mR x y : ℝ}
    (hL : HasDerivWithinAt f mL (Iic a) a)
    (hR : HasDerivWithinAt f mR (Ici a) a)
    (hX : HasDerivAt X x 0) (hY : HasDerivAt Y y 0)
    (hX0 : X 0 = a) (hY0 : Y 0 = f a) (hx : x ≠ 0)
    (htrans : y - (if 0 < x then mR else mL) * x ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (f (X t) < Y t ↔ 0 < y - (if 0 < x then mR else mL) * x) := by
  have hd := hY.hasDerivWithinAt.sub (one_sided_height_comp hL hR hX hX0 hx)
  have hzero : Y 0 - f (X 0) = 0 := by rw [hX0, hY0, sub_self]
  simpa only [Pi.sub_apply, sub_pos] using eventually_sign_of_right_derivative hd hzero htrans


open P202Specs.PlanarRegionTopology P202Specs.BoundaryGraphDirections

lemma exists_nonzero_projection (axes : Fin 2 → Plane)
    (haxes : LinearIndependent ℝ axes) {v : Plane} (hv : v ≠ 0) :
    ∃ k, inner ℝ (axes k) v ≠ 0 := by
  by_contra h
  have hz : ∀ k, inner ℝ (axes k) v = 0 := by simpa only [not_exists, not_not] using h
  let b := basisOfLinearIndependentOfCardEqFinrank haxes (by simp [Plane])
  apply hv
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ v v = inner ℝ (∑ k, b.repr v k • b k) v := by rw [b.sum_repr]
    _ = 0 := by
      simp only [sum_inner, real_inner_smul_left]
      apply Finset.sum_eq_zero
      intro k hk
      have hb : b k = axes k := by
        simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
      rw [hb, hz k, mul_zero]


/-- Any actual local epigraph domain has the same eventual membership along
an asymptotically tangent curve as its derivative's explicit side test. -/
theorem eventually_domain_curve_iff_tangent
    {U O : Set Plane} {F : ℝ → Plane} {p v e : Plane} {f : ℝ → ℝ} {mL mR : ℝ}
    (hO : IsOpen O) (hp : p ∈ O)
    (hdom : ∀ z ∈ O, z ∈ U ↔ f (inner ℝ e z) < inner ℝ (quarterTurn e) z)
    (hbase : inner ℝ (quarterTurn e) p = f (inner ℝ e p))
    (hL : HasDerivWithinAt f mL (Iic (inner ℝ e p)) (inner ℝ e p))
    (hR : HasDerivWithinAt f mR (Ici (inner ℝ e p)) (inner ℝ e p))
    (hF : HasDerivAt F v 0) (hF0 : F 0 = p)
    (hproj : inner ℝ e v ≠ 0)
    (htrans : inner ℝ (quarterTurn e) v -
      (if 0 < inner ℝ e v then mR else mL) * inner ℝ e v ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (F t ∈ U ↔ 0 < inner ℝ (quarterTurn e) v -
        (if 0 < inner ℝ e v then mR else mL) * inner ℝ e v) := by
  have hX : HasDerivAt (fun t => inner ℝ e (F t)) (inner ℝ e v) 0 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const (0 : ℝ) e).inner ℝ hF
  have hY : HasDerivAt (fun t => inner ℝ (quarterTurn e) (F t))
      (inner ℝ (quarterTurn e) v) 0 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const (0 : ℝ) (quarterTurn e)).inner ℝ hF
  have htest := eventually_epigraph_iff_tangent hL hR hX hY
    (by rw [hF0]) (by rw [hF0, hbase]) hproj htrans
  have hFO : ∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ O := by
    apply (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
    rw [hF0]
    exact hO.mem_nhds hp
  filter_upwards [htest, hFO] with t ht hFt
  exact (hdom (F t) hFt).trans ht

/-- Curved-domain membership and the exact derivative ray agree pointwise
for all sufficiently small positive parameters. -/
theorem eventually_domain_curve_iff_ray
    {U O : Set Plane} {F : ℝ → Plane} {p v e : Plane} {f : ℝ → ℝ} {mL mR : ℝ}
    (hO : IsOpen O) (hp : p ∈ O)
    (hdom : ∀ z ∈ O, z ∈ U ↔ f (inner ℝ e z) < inner ℝ (quarterTurn e) z)
    (hbase : inner ℝ (quarterTurn e) p = f (inner ℝ e p))
    (hL : HasDerivWithinAt f mL (Iic (inner ℝ e p)) (inner ℝ e p))
    (hR : HasDerivWithinAt f mR (Ici (inner ℝ e p)) (inner ℝ e p))
    (hF : HasDerivAt F v 0) (hF0 : F 0 = p)
    (hproj : inner ℝ e v ≠ 0)
    (htrans : inner ℝ (quarterTurn e) v -
      (if 0 < inner ℝ e v then mR else mL) * inner ℝ e v ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ U ↔ p + t • v ∈ U) := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p using 1 <;> simp
  filter_upwards [eventually_domain_curve_iff_tangent hO hp hdom hbase hL hR hF hF0 hproj htrans,
    eventually_domain_curve_iff_tangent hO hp hdom hbase hL hR hline
      (by simp) hproj htrans] with t ht ht'
  exact ht.trans ht'.symm

lemma local_graph_eventually_curve_iff_ray
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hO : IsOpen O)
    (hpO : realLift (R.curve i).parametrization t ∈ O)
    {mL mR : ℝ} {F : ℝ → Plane} {v : Plane}
    (hL : HasDerivWithinAt G.height mL
      (Iic (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t))
    (hR : HasDerivWithinAt G.height mR
      (Ici (arcProjection (R.curve i) G.arc.axis t))
      (arcProjection (R.curve i) G.arc.axis t))
    (hF : HasDerivAt F v 0) (hF0 : F 0 = realLift (R.curve i).parametrization t)
    (hproj : inner ℝ G.arc.axis v ≠ 0)
    (htrans : inner ℝ (quarterTurn G.arc.axis) v -
      (if 0 < inner ℝ G.arc.axis v then mR else mL) * inner ℝ G.arc.axis v ≠ 0) :
    ∀ᶠ u : ℝ in 𝓝[>] 0,
      (F u ∈ R.domain ↔ realLift (R.curve i).parametrization t + u • v ∈ R.domain) := by
  let p := realLift (R.curve i).parametrization t
  let e := G.arc.axis
  have hbase : inner ℝ (quarterTurn e) p = G.height (inner ℝ e p) := by
    have hh := congrArg (fun z => inner ℝ (quarterTurn e) z)
      (G.arc_identity t ⟨by linarith [G.arc.radius_pos], by linarith [G.arc.radius_pos]⟩)
    simpa only [p, e, arcProjection, frame_vertical G.arc.unit_axis G.frame,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] using hh
  have hdom : ∀ z ∈ O, z ∈ R.domain ↔ G.height (inner ℝ e z) < inner ℝ (quarterTurn e) z := by
    intro z hz
    have hh := congrArg (fun A : Set Plane => z ∈ A) G.domain_eq
    have hi : (z ∈ R.domain) ↔ z ∈ G.frame.map '' {w : Plane | G.height (w 0) < w 1} := by
      simpa only [mem_inter_iff, hz, and_true] using (Iff.of_eq hh)
    exact hi.trans (frame_epigraph_iff G.arc.unit_axis G.frame G.height z)
  exact eventually_domain_curve_iff_ray hO hpO hdom hbase hL hR hF hF0 hproj htrans

/-- Every actual curve with a nonboundary limiting direction has the same
literal PlanarRegion-domain membership germ as its derivative ray. Only the
two outward boundary rays are excluded, exactly as in IsOccupiedSectorAngle. -/
theorem eventually_planarRegion_domain_iff_derivative_ray
    (R : PlanarRegion) (s : Fin R.boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) (j : Fin A.count)
    {F : ℝ → Plane} {v : Plane} (hF : HasDerivAt F v 0) (hF0 : F 0 = A.arc j 1)
    (hv : v ≠ 0)
    (hvo : NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay A (s i) j))
    (hvi : NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay A (s i) j)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ R.domain ↔ A.arc j 1 + t • v ∈ R.domain) := by
  obtain ⟨arcs, haxes⟩ := twoDirectedProjectionArcs (R.curve i) (s i) (A.time j.succ) (hs i).1
  obtain ⟨k, hk⟩ := exists_nonzero_projection (fun k => (arcs k).axis) haxes hv
  have hσ : s i ≠ 0 := by
    rcases (hs i).1 with h | h <;> simp only [h, ne_eq, one_ne_zero, neg_eq_zero, not_false_eq_true]
  obtain ⟨O, G, hO, hpO, hGA⟩ :=
    localDirectedBoundaryGraph_of_arc R s i (A.time j.succ) hσ (hs i).2 (arcs k)
  have hproj : inner ℝ G.arc.axis v ≠ 0 := by rwa [hGA]
  have hp : A.arc j 1 = realLift (R.curve i).parametrization (A.time j.succ) :=
    arc_finish_eq_original A j
  have hleft := directedProjectionArc_left_deriv A j (s i) G.arc
  have hright := directedProjectionArc_right_deriv A j (s i) G.arc
  have hkL : 0 < (A.time j.succ - A.time j.castSucc)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (A.strictMono j.castSucc_lt_succ))
  have hkR : 0 < (A.time (finRotate A.count j).succ - A.time (finRotate A.count j).castSucc)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (A.strictMono (finRotate A.count j).castSucc_lt_succ))
  have hF0' := hF0.trans hp
  rw [hp]
  rcases (hs i).1 with hsign | hsign
  · obtain ⟨hU, hW, _⟩ := ray_test_with_forward_tangents G hO hpO hsign hkL hkR hleft hright
    obtain ⟨hL, hR⟩ := height_one_sided_derivatives G hsign
    rw [hleft, projection_slope_smul hkL.ne'] at hL
    rw [hright, projection_slope_smul hkR.ne'] at hR
    have hvo' : NormedSpace.normalize v ≠ NormedSpace.normalize (velocity A (finRotate A.count j) 0) := by
      simpa only [outgoingRay, hsign, ↓reduceIte] using hvo
    have hvi' : NormedSpace.normalize v ≠ NormedSpace.normalize (-velocity A j 1) := by
      simpa only [incomingRay, hsign, ↓reduceIte] using hvi
    exact local_graph_eventually_curve_iff_ray G hO hpO hL hR hF hF0' hproj
      (graph_ray_transverse G.arc.unit_axis hU hW hv hvo' hvi')
  · obtain ⟨hU, hW, _⟩ := ray_test_with_reverse_tangents G hO hpO hsign hkL hkR hleft hright
    obtain ⟨hL, hR⟩ := height_one_sided_derivatives_reverse G hsign
    rw [hright, projection_slope_smul hkR.ne'] at hL
    rw [hleft, projection_slope_smul hkL.ne'] at hR
    have hL' : HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (-velocity A (finRotate A.count j) 0) /
        inner ℝ G.arc.axis (-velocity A (finRotate A.count j) 0))
      (Iic (arcProjection (R.curve i) G.arc.axis (A.time j.succ)))
      (arcProjection (R.curve i) G.arc.axis (A.time j.succ)) := by
      simpa only [inner_neg_right, neg_div_neg_eq] using hL
    have hR' : HasDerivWithinAt G.height
      (inner ℝ (quarterTurn G.arc.axis) (-velocity A j 1) /
        inner ℝ G.arc.axis (-velocity A j 1))
      (Ici (arcProjection (R.curve i) G.arc.axis (A.time j.succ)))
      (arcProjection (R.curve i) G.arc.axis (A.time j.succ)) := by
      simpa only [inner_neg_right, neg_div_neg_eq] using hR
    have hsone : s i ≠ 1 := by rw [hsign]; norm_num
    have hvo' : NormedSpace.normalize v ≠ NormedSpace.normalize (-velocity A j 1) := by
      simpa only [outgoingRay, hsone, ↓reduceIte] using hvo
    have hvi' : NormedSpace.normalize v ≠ NormedSpace.normalize (velocity A (finRotate A.count j) 0) := by
      simpa only [incomingRay, hsone, ↓reduceIte] using hvi
    apply local_graph_eventually_curve_iff_ray G hO hpO hL' hR' hF hF0' hproj
    exact graph_ray_transverse G.arc.unit_axis hU hW hv hvo'
      (by simpa only [neg_neg] using hvi')


/-- The literal occupied-sector predicate also tests every actual curve with
the same nonboundary derivative, which is the chart-transition use case. -/
theorem occupiedSectorAngle_curved_test
    {M : Type*} [TopologicalSpace M]
    {S : SmoothManifolds.AtlasData.SmoothManifold 2 .euclidean M}
    (g : P202.MetricData.RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : SmoothManifolds.ModelData.ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (s : Fin R.boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) (j : Fin A.count)
    (alpha : ℝ) (hocc : IsOccupiedSectorAngle g o c hc R i A (s i) j alpha)
    {F : ℝ → Plane} {v : Plane} (hF : HasDerivAt F v 0) (hF0 : F 0 = A.arc j 1)
    (hv : v ≠ 0)
    (hvo : NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay A (s i) j))
    (hvi : NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay A (s i) j)) :
    (∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ R.domain) ↔
      positiveMetricAngle g o c hc (A.arc j 1) (outgoingRay A (s i) j) v < alpha := by
  have he := eventually_planarRegion_domain_iff_derivative_ray R s hs i A j hF hF0 hv hvo hvi
  exact (eventually_congr he).trans (hocc.2.2 v hv hvo hvi)

/-- Actual regional domain-ray transport through genuine original charts,
with the true intrinsic Jacobian and exactly the two corner boundary exclusions. -/
theorem regionalDomain_changed_chart_ray_transport
    {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : FiberCoordinates S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hpd : p ∈ (D.chart r).source)
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (j : Fin A.count)
    (hj : A.arc j 1 = coordinates (D.chart r) p) :
    let L := ((K.equiv e he p hp).symm.trans
      (K.equiv (D.chart r) (D.chart_mem r) p hpd)).toContinuousLinearEquiv
    ∀ (u : Euclidean 2), u ≠ 0 →
      NormedSpace.normalize (toPlane (L u)) ≠ NormedSpace.normalize (outgoingRay A (s i) j) →
      NormedSpace.normalize (toPlane (L u)) ≠ NormedSpace.normalize (incomingRay A (s i) j) →
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (((e p).val + t • u ∈
            (fun q => (e q).val) '' (regionInterior D r ∩ e.source)) ↔
          coordinates (D.chart r) p + t • toPlane (L u) ∈ (D.region r).domain) := by
  dsimp only
  intro u hu hvo hvi
  let L := ((K.equiv e he p hp).symm.trans
    (K.equiv (D.chart r) (D.chart_mem r) p hpd)).toContinuousLinearEquiv
  obtain ⟨H, W, hx, hbase, _, _, hder, _, _, _, hW, hpW, _, hWsub, hWH, hdomain, _⟩ :=
    exists_regionalDomain_atlas_germ S K D r e he p hp hpd univ isOpen_univ (mem_univ p)
  have hray : HasDerivAt (fun t : ℝ => (e p).val + t • u) u 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (e p).val using 1 <;> simp
  have hder0 : HasFDerivAt H (L : Euclidean 2 →L[ℝ] Euclidean 2)
      ((e p).val + (0 : ℝ) • u) := by simpa only [zero_smul, add_zero] using hder
  have hHd : HasDerivAt (fun t : ℝ => H ((e p).val + t • u)) (L u) 0 := by
    convert! hder0.comp_hasDerivAt 0 hray using 1
  have hF : HasDerivAt (fun t : ℝ => toPlane (H ((e p).val + t • u)))
      (toPlane (L u)) 0 :=
    toPlane.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hHd
  have hF0 : toPlane (H ((e p).val + (0 : ℝ) • u)) = A.arc j 1 := by
    simp only [zero_smul, add_zero, hbase, hj, coordinates]
  have htv : toPlane (L u) ≠ 0 :=
    toPlane.map_ne_zero_iff.mpr (L.map_ne_zero_iff.mpr hu)
  have htest := eventually_planarRegion_domain_iff_derivative_ray (D.region r) s hs i A j hF hF0 htv hvo hvi
  let U := regionInterior D r ∩ e.source
  have hU : U ⊆ e.source := inter_subset_right
  have hgerm := coordinateImage_inter_nhds e p hp W hW hpW U hU
  have hsets : U ∩ W = regionInterior D r ∩ W := by
    ext q
    constructor
    · rintro ⟨⟨hq, _⟩, hqw⟩
      exact ⟨hq, hqw⟩
    · rintro ⟨hq, hqw⟩
      exact ⟨⟨hq, (hWsub hqw).1⟩, hqw⟩
  rw [hsets] at hgerm
  have hsource : Tendsto (fun t : ℝ => (e p).val + t • u)
      (𝓝[>] 0) (𝓝 (e p).val) := by
    simpa only [zero_smul, add_zero] using
      hray.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htarget : Tendsto (fun t : ℝ => H ((e p).val + t • u))
      (𝓝[>] 0) (𝓝 ((D.chart r) p).val) := by
    simpa only [zero_smul, add_zero, hbase] using
      hHd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsrcH : ∀ᶠ t : ℝ in 𝓝[>] 0, (e p).val + t • u ∈ H.source :=
    hsource.eventually (H.open_source.mem_nhds hx)
  filter_upwards [htest, hsource.eventually hgerm, htarget.eventually hdomain, hsrcH]
    with t ht hg hd hHs
  have hpull : H ((e p).val + t • u) ∈
      H '' ((fun q => (e q).val) '' (regionInterior D r ∩ W)) ↔
      (e p).val + t • u ∈ (fun q => (e q).val) '' (regionInterior D r ∩ W) := by
    constructor
    · rintro ⟨z, hz, hez⟩
      have hzH : z ∈ H.source := by
        obtain ⟨q, hq, rfl⟩ := hz
        exact hWH q hq.2
      have hzy : z = (e p).val + t • u := H.injOn hzH hHs hez
      rwa [hzy] at hz
    · exact fun h => ⟨(e p).val + t • u, h, rfl⟩
  exact hg.trans (hpull.symm.trans (hd.symm.trans (by simpa only [hj] using ht)))

/-- A single orientation choice transports the literal occupied-sector test
for every differentiable domain curve at the actual original point. -/
theorem regionalChartGeometry_occupiedSectorCurve_transport
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount) (j : Fin (A i).count)
    (hj : (A i).arc j 1 = coordinates (D.chart r) p.val) :
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let V := fun v : Plane => K.symm (EuclideanSpace.equiv (Fin 2) ℝ v)
    let alpha := P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem (A i) (s i) j
    ∃ reversed : Bool, 0 < alpha ∧ alpha < 2 * Real.pi ∧
      ∀ {F : ℝ → Plane} {v : Plane}, HasDerivAt F v 0 → F 0 = (A i).arc j 1 →
        v ≠ 0 →
        NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay (A i) (s i) j) →
        NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay (A i) (s i) j) →
        ((∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ (D.region r).domain) ↔
          (if reversed then positiveAngle (tangentAngle g p.val o (V v) (V (outgoingRay (A i) (s i) j)))
           else positiveAngle (tangentAngle g p.val o (V (outgoingRay (A i) (s i) j)) (V v))) < alpha) := by
  obtain ⟨reversed, hocc⟩ :=
    regionalChartGeometry_occupiedSectorAngle_transport g D r G p o A s hs i j hj
  refine ⟨reversed, hocc.1, hocc.2.1, ?_⟩
  intro F v hF hF0 hv hvo hvi
  have hcurve := eventually_planarRegion_domain_iff_derivative_ray
    (D.region r) s hs i (A i) j hF hF0 hv hvo hvi
  have hdomain :
      (∀ᶠ t : ℝ in 𝓝[>] 0, ∃ q ∈ regionInterior D r,
        coordinates (D.chart r) q = (A i).arc j 1 + t • v) ↔
      (∀ᶠ t : ℝ in 𝓝[>] 0, (A i).arc j 1 + t • v ∈ (D.region r).domain) := by
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall (fun t => by rw [← D.domain_coordinates r]; rfl)
  exact (eventually_congr hcurve).trans
    (hdomain.symm.trans (hocc.2.2 v hv hvo hvi))

end PlanarDomainCurveGerms

section ChangedChartOccupiedSectors
open Filter
open scoped _root_.Topology
open SmoothManifolds.TangentBundleData
/-- The actual occupied-sector test, transported through an arbitrary genuine
original chart change into the original metric tangent fiber. The orientation
choice is uniform over all source directions and no sign certificate is assumed. -/
theorem regionalChartGeometry_changed_chart_occupiedSectorAngle_transport
    {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount) (j : Fin (A i).count)
    (hj : (A i).arc j 1 = coordinates (D.chart r) p.val)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source) :
    let Ke := (tangentStructure S).fiberCoordinates.equiv e he p.val hp
    let Kd := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let L := (Ke.symm.trans Kd).toContinuousLinearEquiv
    let alpha := P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem (A i) (s i) j
    ∃ reversed : Bool, 0 < alpha ∧ alpha < 2 * Real.pi ∧
      ∀ (u : Euclidean 2), u ≠ 0 →
        NormedSpace.normalize (toPlane (L u)) ≠
          NormedSpace.normalize (outgoingRay (A i) (s i) j) →
        NormedSpace.normalize (toPlane (L u)) ≠
          NormedSpace.normalize (incomingRay (A i) (s i) j) →
        ((∀ᶠ t : ℝ in 𝓝[>] 0, (e p.val).val + t • u ∈
            (fun q => (e q).val) '' (regionInterior D r ∩ e.source)) ↔
          (if reversed then positiveAngle (tangentAngle g p.val o
            (Ke.symm u)
            (Kd.symm (EuclideanSpace.equiv (Fin 2) ℝ (outgoingRay (A i) (s i) j))))
          else positiveAngle (tangentAngle g p.val o
            (Kd.symm (EuclideanSpace.equiv (Fin 2) ℝ (outgoingRay (A i) (s i) j)))
            (Ke.symm u))) < alpha) := by
  dsimp only
  let Ke := (tangentStructure S).fiberCoordinates.equiv e he p.val hp
  let Kd := (tangentStructure S).fiberCoordinates.equiv
    (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
  let L := (Ke.symm.trans Kd).toContinuousLinearEquiv
  let alpha := P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
    G.ambientChart G.ambientChart_mem (A i) (s i) j
  obtain ⟨reversed, hsector⟩ := regionalChartGeometry_occupiedSectorAngle_transport g D r G p o A s hs i j hj
  dsimp only [originalOccupiedSectorAngle] at hsector
  refine ⟨reversed, hsector.1, hsector.2.1, ?_⟩
  intro u hu hvo hvi
  have hv : toPlane (L u) ≠ 0 :=
    toPlane.map_ne_zero_iff.mpr (L.map_ne_zero_iff.mpr hu)
  have htest := hsector.2.2 (toPlane (L u)) hv hvo hvi
  have hdomain :
      (∀ᶠ t : ℝ in 𝓝[>] 0, ∃ q ∈ regionInterior D r,
        coordinates (D.chart r) q = (A i).arc j 1 + t • toPlane (L u)) ↔
      (∀ᶠ t : ℝ in 𝓝[>] 0, (A i).arc j 1 + t • toPlane (L u) ∈
        (D.region r).domain) := by
    apply Filter.eventually_congr
    exact Filter.Eventually.of_forall (fun t => by rw [← D.domain_coordinates r]; rfl)
  rw [hdomain] at htest
  have hray := regionalDomain_changed_chart_ray_transport S (tangentStructure S).fiberCoordinates D r e he p.val hp
    (G.source_subset p.property) s hs i (A i) j hj u hu hvo hvi
  rw [← hj] at hray
  have hsrc := (Filter.eventually_congr hray).trans htest
  have hmap : Kd.symm (EuclideanSpace.equiv (Fin 2) ℝ (toPlane (L u))) = Ke.symm u := by
    change Kd.symm (toPlane.symm (toPlane (L u))) = Ke.symm u
    rw [toPlane.symm_apply_apply]
    exact Kd.symm_apply_apply _
  dsimp only [Kd, Ke] at hmap
  simpa only [hmap] using hsrc


end ChangedChartOccupiedSectors

end P202.GlobalGaussBonnet.CornerTransport
