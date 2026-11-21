import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.BoundaryCones
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Isomorphisms

namespace SmoothManifolds
open Set Filter
open scoped Topology BoundaryConeData
open DifferentialData
universe u

abbrev VelocitySign := BoundaryConeData.VelocitySign
abbrev IsBoundaryStructure := @BoundaryConeData.IsBoundaryStructure

/-- Coordinate realizations specified by germs agree with the upstream one. -/
theorem chartCoordinates_eq {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (hE : IsChartCoordinates S p e E)
    (v : TangentSpace S p) : E v = coordinateDerivationEquiv S p e he hp v := by
  obtain ⟨xs, hxs, hE⟩ := hE
  ext i
  rw [hE]
  exact congrArg v.val (Subtype.ext (hxs i))

theorem coordinateDerivationEquiv_isChartCoordinates {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    IsChartCoordinates S p e (coordinateDerivationEquiv S p e he hp) :=
  ⟨coordinateGerm S p e he hp, fun _ => rfl, fun _ _ => rfl⟩

/-- A right derivative of a nonnegative function vanishing at zero is nonnegative. -/
private theorem right_derivative_nonneg {f : ℝ → ℝ} {r : ℝ}
    (hf : ∀ t, 0 ≤ f t) (h0 : f 0 = 0) (hd : HasDerivWithinAt f r (Ici 0) 0) :
    0 ≤ r := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ Ici 0 \ {0} from
      fun t ht => ⟨mem_Ici.mpr (le_of_lt (mem_Ioi.mp ht)),
        by simpa only [mem_singleton_iff] using ne_of_gt (mem_Ioi.mp ht)⟩))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_def_field, h0, sub_zero]
  exact div_nonneg (hf t) (le_of_lt ht)

private theorem left_derivative_nonpos {f : ℝ → ℝ} {r : ℝ}
    (hf : ∀ t, 0 ≤ f t) (h0 : f 0 = 0) (hd : HasDerivWithinAt f r (Iic 0) 0) :
    r ≤ 0 := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Iio (0 : ℝ) ⊆ Iic 0 \ {0} from
      fun t ht => ⟨mem_Iic.mpr (le_of_lt (mem_Iio.mp ht)),
        by simpa only [mem_singleton_iff] using ne_of_lt (mem_Iio.mp ht)⟩))
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_def_field, h0, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hf t) (le_of_lt ht)

/-- Unlike an arbitrary tangent vector, a velocity on a prescribed side has a sign. -/
theorem boundary_curve_velocity_sign {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (p : intrinsicBoundary S)
    (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source) (side : CurveSide) (c : ℝ → M)
    (v : TangentSpace S p.val) (hv : CurveRepresentsDerivation S p.val side c v) :
    VelocitySign side (coordinateDerivationEquiv S p.val e he hp v (Fin.last n)) := by
  let f : ℝ → ℝ := fun t => (e (c t)).val (Fin.last n)
  have hf (t : ℝ) : 0 ≤ f t := (e (c t)).property
  have h0 : f 0 = 0 := by
    change (e (c 0)).val (Fin.last n) = 0
    rw [hv.1.1]
    exact (intrinsicBoundary_iff_chart S e he p.val hp).mp p.property
  have hd := hv.2 (coordinateGerm S p.val e he hp (Fin.last n))
    (fun y => (e y).val (Fin.last n)) rfl
  cases side with
  | forward => exact right_derivative_nonneg hf h0 hd
  | backward => exact left_derivative_nonpos hf h0 hd
  | twoSided =>
    have hd' : HasDerivAt f (v.val (coordinateGerm S p.val e he hp (Fin.last n))) 0 :=
      (hasDerivWithinAt_univ.mp hd)
    exact le_antisymm (left_derivative_nonpos hf h0 hd'.hasDerivWithinAt)
      (right_derivative_nonneg hf h0 hd'.hasDerivWithinAt)

/-- A straight chart curve on a prescribed parameter side, whenever that line
stays in the model. Its smoothness is checked in every compatible chart. -/
theorem exists_curve_on_side {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (side : CurveSide) (v : Euclidean n)
    (hline : ∀ t ∈ curveParameterSet side, (e p).val + t • v ∈ modelSet n a) :
    ∃ c : ℝ → M, CurveSmoothAt S p side c ∧
      HasDerivWithinAt (fun t => (e (c t)).val) v (curveParameterSet side) 0 := by
  classical
  let J := curveParameterSet side
  have h0J : 0 ∈ J := by cases side <;> simp [J, TangentData.curveParameterSet]
  let A : ℝ → Euclidean n := fun t => (e p).val + t • v
  have hA0 : A 0 = (e p).val := by simp [A]
  have hAc : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  have hAs : ContDiff ℝ (⊤ : ℕ∞) A := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hAd : HasDerivAt A v 0 := by
    simpa [A] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (e p).val
  let q : ℝ → ModelSpace n a := fun t =>
    if h : A t ∈ modelSet n a then ⟨A t, h⟩ else e p
  have hqval (t : ℝ) (ht : t ∈ J) : (q t).val = A t := by
    have h : A t ∈ modelSet n a := hline t ht
    simp only [q, dite_eq_left h]
  have hq0 : q 0 = e p := Subtype.ext ((hqval 0 h0J).trans hA0)
  have hqval_ev : (fun t => (q t).val) =ᶠ[𝓝[J] 0] A := by
    filter_upwards [self_mem_nhdsWithin] with t ht using hqval t ht
  have hqc : ContinuousWithinAt q J 0 := by
    apply tendsto_subtype_rng.mpr
    exact hAc.continuousAt.continuousWithinAt.congr_of_eventuallyEq hqval_ev (hqval 0 h0J)
  let c : ℝ → M := fun t => e.symm (q t)
  have hc0 : c 0 = p := by
    change e.symm (q 0) = p
    rw [hq0, e.left_inv hp]
  have hcc : ContinuousWithinAt c J 0 :=
    (e.symm.continuousAt (by rw [hq0]; exact e.map_source hp)).comp_continuousWithinAt hqc
  have hct : Tendsto c (𝓝[J] 0) (𝓝 p) := by
    simpa only [ContinuousWithinAt, hc0] using hcc
  have hec : (fun t => (e (c t)).val) =ᶠ[𝓝[J] 0] A := by
    have hqt : ∀ᶠ t in 𝓝[J] 0, q t ∈ e.target :=
      (show Tendsto q (𝓝[J] 0) (𝓝 (q 0)) from hqc).eventually
        (e.open_target.mem_nhds (by rw [hq0]; exact e.map_source hp))
    filter_upwards [hqt, hqval_ev] with t ht hval
    change (e (e.symm (q t))).val = A t
    rw [e.right_inv ht, hval]
  refine ⟨c, ⟨hc0, hcc, ?_⟩, hAd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hec h0J⟩
  intro d hd hpd
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hp hpd
  refine ⟨A ⁻¹' U, hU.preimage hAc, ?_, F ∘ A,
    hF.comp hAs.contDiffOn (fun _ ht => ht), ?_⟩
  · change A 0 ∈ U
    rwa [hA0]
  · exact (heF.comp_tendsto hct).symm.trans (hec.fun_comp F)

theorem boundary_curve_cones :
    Specs.SmoothManifolds.Tangent.BoundaryCones.boundary_curve_conesType.{u} := by
  intro n M _ S p e he hp E hE side v
  have hcoords := chartCoordinates_eq S p.val e he hp E hE
  constructor
  · rintro ⟨c, hc⟩
    rw [hcoords v]
    exact boundary_curve_velocity_sign S p e he hp side c v hc
  · intro hsign
    have hface : (e p.val).val (Fin.last n) = 0 :=
      (intrinsicBoundary_iff_chart S e he p.val hp).mp p.property
    have hline (t : ℝ) (ht : t ∈ curveParameterSet side) :
        (e p.val).val + t • E v ∈ modelSet (n + 1) .halfSpace := by
      change 0 ≤ (e p.val).val (Fin.last n) + t * E v (Fin.last n)
      rw [hface, zero_add]
      cases side with
      | forward => exact mul_nonneg ht hsign
      | backward => exact mul_nonneg_of_nonpos_of_nonpos ht hsign
      | twoSided => change E v (Fin.last n) = 0 at hsign; simp [hsign]
    obtain ⟨c, hc, hd⟩ := exists_curve_on_side S p.val e he hp side (E v) hline
    obtain ⟨w, hw, _⟩ := exists_curve_derivation_of_chart S p.val e he hp side c hc (E v) hd
    have heq : w = v := by
      apply E.injective
      rw [hcoords w]
      exact funext (curve_coordinate_values S p.val e he hp side c w hw (E v) hd)
    exact ⟨c, heq ▸ hw⟩

/-- In a restricted face chart, the inclusion differential inserts a final zero. -/
theorem boundary_inclusion_coordinates {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (p : intrinsicBoundary S) (e : ModelChart (n + 1) .halfSpace M)
    (he : e ∈ S.smoothStructure.val) (hp : p.val ∈ e.source)
    (b : ModelChart n .euclidean (intrinsicBoundary S))
    (hb : b ∈ B.smoothStructure.val) (hface : IsFaceRestriction S e b)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential B S Subtype.val p L)
    (E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n + 1))
    (hE : IsChartCoordinates S p.val e E) (v : TangentSpace B p) :
    E (L v) = Fin.snoc (coordinateDerivationEquiv B p b hb
      (by rw [hface.1]; exact hp) v) 0 := by
  have hpb : p ∈ b.source := by rw [hface.1]; exact hp
  rw [chartCoordinates_eq S p.val e he hp E hE]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    change (L v).val (coordinateGerm S p.val e he hp (Fin.last n)) = 0
    have hk : Germ.ofFun ((fun y => (e y).val (Fin.last n)) ∘ Subtype.val) =
        (0 : SmoothGerm B p).val := by
      apply Germ.coe_eq.mpr
      filter_upwards [(isOpen_induced e.open_source).mem_nhds hp] with q hq
      exact (intrinsicBoundary_iff_chart S e he q.val hq).mp q.property
    rw [hL v _ 0 _ rfl hk, map_zero]
  · simp only [Fin.snoc_castSucc]
    change (L v).val (coordinateGerm S p.val e he hp j.castSucc) =
      v.val (coordinateGerm B p b hb hpb j)
    apply hL v _ _ (fun y => (e y).val j.castSucc) rfl
    apply Germ.coe_eq.mpr
    filter_upwards [b.open_source.mem_nhds hpb] with q hq
    exact (hface.2.2 q hq j).symm

/-- Local identification for any boundary structure with the natural face charts. -/
theorem boundary_inclusion_image {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (hB : IsBoundaryStructure S B)
    (p : intrinsicBoundary S) (e : ModelChart (n + 1) .halfSpace M)
    (he : e ∈ S.smoothStructure.val) (hp : p.val ∈ e.source)
    (L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential B S Subtype.val p L)
    (E : TangentSpace S p.val ≃ₗ[ℝ] Euclidean (n + 1))
    (hE : IsChartCoordinates S p.val e E) :
    Function.Injective L ∧ ∀ v, v ∈ LinearMap.range L ↔ E v (Fin.last n) = 0 := by
  obtain ⟨b, hb, hface⟩ := hB.2 e he ⟨⟨p, hp⟩⟩
  have hpb : p ∈ b.source := by rw [hface.1]; exact hp
  let F := coordinateDerivationEquiv B p b hb hpb
  have hcoords (v) : E (L v) = Fin.snoc (F v) 0 :=
    boundary_inclusion_coordinates S B p e he hp b hb hface L hL E hE v
  constructor
  · intro v w hvw
    apply F.injective
    ext i
    have h := congrArg (fun z => E z i.castSucc) hvw
    simpa only [hcoords, Fin.snoc_castSucc] using h
  · intro v
    constructor
    · rintro ⟨w, rfl⟩
      simp only [hcoords, Fin.snoc_last]
    · intro hv
      refine ⟨F.symm (Fin.init (E v)), ?_⟩
      apply E.injective
      rw [hcoords, F.apply_symm_apply, ← hv, Fin.snoc_init_self]

theorem boundary_tangent_identification :
    Specs.SmoothManifolds.Tangent.BoundaryCones.boundary_tangent_identificationType.{u} := by
  intro n M _ S
  obtain ⟨B, hBsmooth, hBcharts⟩ := exists_boundary_smoothManifold S
  have hB : IsBoundaryStructure S B := ⟨hBsmooth, hBcharts⟩
  refine ⟨B, hB, ?_⟩
  intro p e he hp E hE
  obtain ⟨L, hL, _⟩ := differential_exists B S Subtype.val hBsmooth p
  exact ⟨L, hL, boundary_inclusion_image S B hB p e he hp L hL E hE⟩

/-- Equality of the realizable cones forces positive proportionality of the two
normal functionals. This avoids choosing an ambient extension of a transition. -/
theorem boundary_transition_positive :
    Specs.SmoothManifolds.Tangent.BoundaryCones.boundary_transition_positiveType.{u} := by
  intro n M _ S p e d he hd hp hpd E F hE hF
  have hzero (v : TangentSpace S p.val) :
      E v (Fin.last n) = 0 ↔ F v (Fin.last n) = 0 :=
    (boundary_curve_cones S p e he hp E hE .twoSided v).symm.trans
      (boundary_curve_cones S p d hd hpd F hF .twoSided v)
  let u := E.symm (Pi.single (Fin.last n) (1 : ℝ))
  have hEu : E u (Fin.last n) = 1 := by simp [u]
  have hr0 : 0 ≤ F u (Fin.last n) :=
    (boundary_curve_cones S p d hd hpd F hF .forward u).mp
      ((boundary_curve_cones S p e he hp E hE .forward u).mpr (by
        change 0 ≤ E u (Fin.last n); rw [hEu]; exact zero_le_one))
  have hrne : F u (Fin.last n) ≠ 0 := fun h =>
    one_ne_zero (hEu.symm.trans ((hzero u).mpr h))
  refine ⟨F u (Fin.last n), lt_of_le_of_ne hr0 (Ne.symm hrne), ?_⟩
  intro v
  let z := E.symm (E v - E v (Fin.last n) • Pi.single (Fin.last n) (1 : ℝ))
  have hz : E z (Fin.last n) = 0 := by simp [z]
  have hFz : F z (Fin.last n) = 0 := (hzero z).mp hz
  have hv : v = z + E v (Fin.last n) • u := by
    apply E.injective
    simp only [map_add, map_smul, z, u, E.apply_symm_apply]
    exact (sub_add_cancel _ _).symm
  calc
    F v (Fin.last n) = F (z + E v (Fin.last n) • u) (Fin.last n) :=
      congrArg (fun w => F w (Fin.last n)) hv
    _ = F u (Fin.last n) * E v (Fin.last n) := by
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, hFz, zero_add,
        smul_eq_mul, mul_comm]

theorem boundary_full_tangent_dimension :
    Specs.SmoothManifolds.Tangent.BoundaryCones.boundary_full_tangent_dimensionType.{u} := by
  intro n M _ S p
  exact tangent_dimension S p.val

/-- Positive normal rescaling also holds for every ambient transition Jacobian. -/
theorem boundary_transition_jacobian :
    Specs.SmoothManifolds.Tangent.BoundaryCones.boundary_transition_jacobianType.{u} := by
  intro n M _ S p e d he hd hp hpd U H hU hpU hH hHeq
  let E := coordinateDerivationEquiv S p.val e he hp
  let F := coordinateDerivationEquiv S p.val d hd hpd
  have hE := coordinateDerivationEquiv_isChartCoordinates S p.val e he hp
  have hF := coordinateDerivationEquiv_isChartCoordinates S p.val d hd hpd
  obtain ⟨r, hr, hEF⟩ := boundary_transition_positive S p e d he hd hp hpd E F hE hF
  have hid : IsSmoothMap S S id :=
    manifoldContDiff_id _ _ S.smoothStructure.property.1
  have hj (v : TangentSpace S p.val) : F v = fderiv ℝ H (e p.val).val (E v) :=
    differential_jacobian S S id hid p.val LinearMap.id (differential_id S p.val)
      e d he hd hp hpd E F hE hF U H hU hpU hH hHeq v
  refine ⟨r, hr, ?_⟩
  intro v
  have h := hEF (E.symm v)
  rw [hj, E.apply_symm_apply] at h
  exact h

/-- The actual normal quotient, with both strict rays and their chart comparison. -/
theorem boundary_normal_quotient :
    Specs.SmoothManifolds.Tangent.BoundaryCones.boundary_normal_quotientType.{u} := by
  intro n M _ S B hB p L hL e he hp E hE
  let N : TangentSpace S p.val →ₗ[ℝ] ℝ :=
    (LinearMap.proj (Fin.last n)).comp E.toLinearMap
  have hsurj : Function.Surjective N := by
    intro r
    refine ⟨E.symm (Pi.single (Fin.last n) r), ?_⟩
    simp [N]
  have hker : LinearMap.range L = LinearMap.ker N := by
    ext v
    exact (boundary_inclusion_image S B hB p e he hp L hL E hE).2 v
  let Q : (TangentSpace S p.val ⧸ LinearMap.range L) ≃ₗ[ℝ] ℝ :=
    (Submodule.quotEquivOfEq _ _ hker).trans (N.quotKerEquivOfSurjective hsurj)
  have hQ (v) : Q (Submodule.Quotient.mk v) = E v (Fin.last n) := by
    simp [Q, N]
  refine ⟨Q, hQ, ?_, ?_, ?_, ?_⟩
  · simpa using Q.finrank_eq
  · ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa only [mem_ofPred_eq, hQ] using hv
    · intro hq
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range L) q
      exact ⟨v, by simpa only [mem_ofPred_eq, hQ] using hq, rfl⟩
  · ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa only [mem_ofPred_eq, hQ] using hv
    · intro hq
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range L) q
      exact ⟨v, by simpa only [mem_ofPred_eq, hQ] using hq, rfl⟩
  · intro d hd hpd F hF
    obtain ⟨r, hr, hEF⟩ := boundary_transition_positive S p e d he hd hp hpd E F hE hF
    exact ⟨r, hr, fun v => (hEF v).trans (by rw [hQ])⟩

end SmoothManifolds
