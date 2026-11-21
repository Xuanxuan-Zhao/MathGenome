import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurveCovariantDerivative
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PiecewiseCurves

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace P202.Geometry.CurveCovariantDerivative
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.MapData SmoothManifolds.FrameData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
open Set Filter
open scoped Topology
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothVectorBundle S r ι E}

/-- This uses exactly the same within tangent model as the accepted curve calculus. -/
theorem hasVelocityWithinAt_iff {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    {V : TangentSpace S (c t)} :
    HasVelocityWithinAt S c J t V ↔ PiecewiseCurves.HasVelocityWithinAt S c J t V := Iff.rfl

theorem velocity_coordinates {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V) (ht : t ∈ J)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : c t ∈ e.source) :
    HasDerivWithinAt (fun s => (e (c s)).val)
      ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp V) J t :=
  PiecewiseCurves.hasVelocityWithinAt_coordinates hV ht e he hp

theorem velocity_unique {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {V W : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    (hW : HasVelocityWithinAt S c J t W) : V = W := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c t)
  apply ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp).injective
  exact hJ.eq_deriv J (velocity_coordinates hV ht e he hp) (velocity_coordinates hW ht e he hp)

/-- Smooth scalar germs differentiate along C¹ curves by their actual intrinsic
linear differential. The curve itself needs no smooth manifold-valued extension. -/
theorem scalar_chain {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    (f : M → ℝ) (hf : VectorSmoothAt S.smoothStructure.val f (c t)) :
    HasDerivWithinAt (f ∘ c) (scalarDerivative S f (c t) V) J t := by
  classical
  obtain ⟨hc, e, he, hp, hd⟩ := hV
  have hs := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hf
  have hg : (scalarGerm S f (c t)).val = Germ.ofFun f := by
    simp only [scalarGerm, dite_eq_left hs]
  obtain ⟨F, hF⟩ := SmoothManifolds.exists_germChartExtension S (c t) e he hp
    (scalarGerm S f (c t))
  obtain ⟨U, hU, hpU, hFU⟩ := hF.1
  have hrep : (fun p => F (e p).val) =ᶠ[𝓝 (c t)] f := Germ.coe_eq.mp (hF.2.trans hg)
  have hdif : scalarDerivative S f (c t) V =
      fderiv ℝ F (e (c t)).val
        ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp V) :=
    SmoothManifolds.VectorFields.tangent_action_coordinates S
      (tangentStructure S).fiberCoordinates (c t) e he hp V (scalarGerm S f (c t)) F hF
  rw [hdif]
  exact ((hFU.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivWithinAt t hd
    |>.congr_of_eventuallyEq (hrep.comp_tendsto hc).symm hrep.eq_of_nhds.symm

@[simp] theorem coefficientsAlong_of_mem {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (c : ℝ → M) (f : (t : ℝ) → E (c t))
    (t : ℝ) (hp : c t ∈ U) :
    coefficientsAlong b c f t = (b.basis ⟨c t, hp⟩).equivFun (f t) := by
  classical
  simp only [coefficientsAlong, dite_eq_left hp]

/-- Chain rule for each entry of the actual transition matrix. -/
theorem transition_chain {U : Set M} {hU : IsOpen U}
    (b d : LocalFrame B U hU) {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c J t V) (i j : Fin r) :
    HasDerivWithinAt
      ((totalize (fun p : U => localTransition b d p i j)) ∘ c)
      (localTransitionDerivative b d ⟨c t, hp⟩ V i j) J t :=
  scalar_chain hV _ (VectorSmoothAt.totalize hU
    (ConnectionForms.localTransition_smooth B b d i j ⟨c t, hp⟩))

/-- The coefficient column in one frame is A times the column in the other. -/
theorem coefficients_change {U : Set M} {hU : IsOpen U}
    (b d : LocalFrame B U hU) (c : ℝ → M) (f : (t : ℝ) → E (c t))
    (t : ℝ) (hp : c t ∈ U) :
    coefficientsAlong b c f t =
      (localTransition b d ⟨c t, hp⟩).mulVec (coefficientsAlong d c f t) := by
  rw [coefficientsAlong_of_mem b c f t hp, coefficientsAlong_of_mem d c f t hp]
  ext i
  exact ConnectionForms.local_coefficient_change B b d ⟨c t, hp⟩ (f t) i

/-- Differentiating the actual change of coefficients needs only C¹ data on the
parameter domain. This is the product rule (Av)' = dA(γ')v + Av'. -/
theorem coefficients_change_deriv {U : Set M} {hU : IsOpen U}
    (b d : LocalFrame B U hU) {c : ℝ → M} {f : (t : ℝ) → E (c t)}
    {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    {w' : Euclidean r} (hw : HasDerivWithinAt (coefficientsAlong d c f) w' J t) :
    HasDerivWithinAt (coefficientsAlong b c f)
      ((localTransitionDerivative b d ⟨c t, hp⟩ V).mulVec (coefficientsAlong d c f t) +
        (localTransition b d ⟨c t, hp⟩).mulVec w') J t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  have hd := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
    (transition_chain b d hp hV i j).mul (hasDerivWithinAt_pi.mp hw j))
  simp only [Function.comp_apply, totalize_of_mem _ (c t) hp,
    Finset.sum_add_distrib] at hd
  change HasDerivWithinAt _
    ((∑ j, localTransitionDerivative b d ⟨c t, hp⟩ V i j * coefficientsAlong d c f t j) +
      (∑ j, localTransition b d ⟨c t, hp⟩ i j * w' j)) J t
  apply hd.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [hV.1.eventually (hU.mem_nhds hp)] with s hs
  rw [coefficients_change b d c f s hs]
  simp only [Matrix.mulVec, dotProduct, Pi.mul_apply, Function.comp_apply, totalize_of_mem _ (c s) hs]

/-- The gauge law proves equality of the two actual fiber elements. -/
theorem frameDerivative_change {U : Set M} {hU : IsOpen U}
    (C : Connection B) (b d : LocalFrame B U hU)
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) (hp : c t ∈ U)
    (V : TangentSpace S (c t)) (v' w' : Euclidean r)
    (hder : v' = (localTransitionDerivative b d ⟨c t, hp⟩ V).mulVec
      (coefficientsAlong d c f t) + (localTransition b d ⟨c t, hp⟩).mulVec w') :
    frameDerivative C b c f t hp V v' = frameDerivative C d c f t hp V w' := by
  apply (b.basis ⟨c t, hp⟩).equivFun.injective
  have heq : (b.basis ⟨c t, hp⟩).equivFun (frameDerivative C d c f t hp V w') =
      (localTransition b d ⟨c t, hp⟩).mulVec
        ((d.basis ⟨c t, hp⟩).equivFun (frameDerivative C d c f t hp V w')) := by
    ext i
    exact ConnectionForms.local_coefficient_change B b d ⟨c t, hp⟩ _ i
  rw [heq]
  simp only [frameDerivative, LinearEquiv.apply_symm_apply]
  rw [hder, coefficients_change b d c f t hp]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  rw [ConnectionForms.local_frame_transformation_product B C b d ⟨c t, hp⟩ V,
    Matrix.add_mulVec]
  abel

/-- Independence of frames on a common domain, including one-sided derivatives. -/
theorem frameDerivative_independent_same_domain {U : Set M} {hU : IsOpen U}
    (C : Connection B) (b d : LocalFrame B U hU)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    {v' w' : Euclidean r}
    (hv : HasDerivWithinAt (coefficientsAlong b c f) v' J t)
    (hw : HasDerivWithinAt (coefficientsAlong d c f) w' J t) :
    frameDerivative C b c f t hp V v' = frameDerivative C d c f t hp V w' :=
  frameDerivative_change C b d c f t hp V v' w'
    (hJ.eq_deriv J hv (coefficients_change_deriv b d ht hp hV hw))

/-- Restriction changes neither the coefficient values nor their parameter germs. -/
theorem coefficients_restrict {U W : Set M} {hU : IsOpen U} {hW : IsOpen W}
    (b : LocalFrame B U hU) (hWU : W ⊆ U) (c : ℝ → M)
    (f : (t : ℝ) → E (c t)) (t : ℝ) (hp : c t ∈ W) :
    coefficientsAlong (restrictFrame (hU := hW) b hWU) c f t =
      coefficientsAlong b c f t := by
  rw [coefficientsAlong_of_mem _ c f t hp,
    coefficientsAlong_of_mem b c f t (hWU hp)]
  rfl

theorem coefficients_restrict_germ {U W : Set M} {hU : IsOpen U} {hW : IsOpen W}
    (b : LocalFrame B U hU) (hWU : W ⊆ U) {c : ℝ → M}
    (f : (t : ℝ) → E (c t)) {J : Set ℝ} {t : ℝ}
    (hc : ContinuousWithinAt c J t) (hp : c t ∈ W) :
    coefficientsAlong (restrictFrame (hU := hW) b hWU) c f =ᶠ[𝓝[J] t]
      coefficientsAlong b c f := by
  filter_upwards [hc.eventually (hW.mem_nhds hp)] with s hs
  exact coefficients_restrict b hWU c f s hs

theorem frameDerivative_restrict {U W : Set M} {hU : IsOpen U} {hW : IsOpen W}
    (C : Connection B) (b : LocalFrame B U hU) (hWU : W ⊆ U)
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) (hp : c t ∈ W)
    (V : TangentSpace S (c t)) (v' : Euclidean r) :
    frameDerivative C (restrictFrame (hU := hW) b hWU) c f t hp V v' =
      frameDerivative C b c f t (hWU hp) V v' := by
  have hmat : connectionMatrix C (restrictFrame (hU := hW) b hWU) ⟨c t, hp⟩ V =
      connectionMatrix C b ⟨c t, hWU hp⟩ V := by
    ext i j
    exact congrArg (fun L => L V)
      (ConnectionForms.connectionForm_restriction B C hWU b ⟨c t, hp⟩ i j)
  simp only [frameDerivative, hmat, coefficients_restrict b hWU c f t hp]
  rfl

/-- Arbitrary overlapping local frames give the same derivative in the original
fiber. Restriction to the open intersection reduces to the proved gauge law. -/
theorem frameDerivative_independent {U W : Set M} {hU : IsOpen U} {hW : IsOpen W}
    (C : Connection B) (b : LocalFrame B U hU) (d : LocalFrame B W hW)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) (hp : c t ∈ U) (hq : c t ∈ W)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    {v' w' : Euclidean r}
    (hv : HasDerivWithinAt (coefficientsAlong b c f) v' J t)
    (hw : HasDerivWithinAt (coefficientsAlong d c f) w' J t) :
    frameDerivative C b c f t hp V v' = frameDerivative C d c f t hq V w' := by
  let hO := hU.inter hW
  let hOU : U ∩ W ⊆ U := inter_subset_left
  let hOW : U ∩ W ⊆ W := inter_subset_right
  let b' := restrictFrame (hU := hO) b hOU
  let d' := restrictFrame (hU := hO) d hOW
  have hv' : HasDerivWithinAt (coefficientsAlong b' c f) v' J t :=
    hv.congr_of_eventuallyEq_of_mem (coefficients_restrict_germ b hOU f hV.1 ⟨hp, hq⟩) ht
  have hw' : HasDerivWithinAt (coefficientsAlong d' c f) w' J t :=
    hw.congr_of_eventuallyEq_of_mem (coefficients_restrict_germ d hOW f hV.1 ⟨hp, hq⟩) ht
  have h := frameDerivative_independent_same_domain C b' d' ht hJ ⟨hp, hq⟩ hV hv' hw'
  exact (frameDerivative_restrict C b hOU c f t ⟨hp, hq⟩ V v').symm.trans
    (h.trans (frameDerivative_restrict C d hOW c f t ⟨hp, hq⟩ V w'))

/-- Uniqueness follows from coordinate and frame independence, not from data
stored in the definition of a derivative. -/
theorem covariantDerivative_unique (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D F : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    (hF : HasCovariantDerivativeWithinAt C c f J t F) : D = F := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, rfl⟩ := hD
  obtain ⟨W, hW, O, hO, d, hq, w', hw, rfl⟩ := hF
  have heq := velocity_unique ht hJ hV hW
  subst W
  exact frameDerivative_independent C b d ht hJ hp hq hV hv hw

/-- A field differentiable in one frame is differentiable in every other local
frame. The proof differentiates transition matrices on their actual overlap. -/
theorem exists_coefficients_deriv (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (hp : c t ∈ U) :
    ∃ v', HasDerivWithinAt (coefficientsAlong b c f) v' J t := by
  obtain ⟨V, hV, W, hW, d, hq, w', hw, _⟩ := hD
  let hO := hU.inter hW
  let hOU : U ∩ W ⊆ U := inter_subset_left
  let hOW : U ∩ W ⊆ W := inter_subset_right
  let b' := restrictFrame (hU := hO) b hOU
  let d' := restrictFrame (hU := hO) d hOW
  have hw' : HasDerivWithinAt (coefficientsAlong d' c f) w' J t :=
    hw.congr_of_eventuallyEq_of_mem (coefficients_restrict_germ d hOW f hV.1 ⟨hp, hq⟩) ht
  have hv' := coefficients_change_deriv b' d' ht ⟨hp, hq⟩ hV hw'
  exact ⟨_, hv'.congr_of_eventuallyEq_of_mem
    (coefficients_restrict_germ b hOU f hV.1 ⟨hp, hq⟩).symm ht⟩

/-- The local formula for the derivative in every smooth frame. -/
theorem local_formula (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    {v' : Euclidean r} (hv : HasDerivWithinAt (coefficientsAlong b c f) v' J t) :
    D = frameDerivative C b c f t hp V v' :=
  covariantDerivative_unique C ht hJ hD ⟨V, hV, U, hU, b, hp, v', hv, rfl⟩

/-- C¹ coefficient extensions give existence, even when the curve has only a
one-sided germ and has no smooth extension into the manifold. -/
theorem exists_covariantDerivative (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hc : P202.CurveData.CoordinateC1On S c J) (hc' : ContinuousOn c J)
    (hf : C1FieldOn (B := B) c f J) :
    ∃ D, HasCovariantDerivativeWithinAt C c f J t D := by
  obtain ⟨V, hV⟩ := PiecewiseCurves.CoordinateC1On.exists_withinVelocity hc hc' ht
  obtain ⟨U, hU, b, hp, v, hv, hval, heq⟩ := hf t ht
  have hd := (hv.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
    |>.congr_of_eventuallyEq heq hval
  exact ⟨_, V, hV, U, hU, b, hp, deriv v t, hd, rfl⟩

/-- The choice defining the actual derivative field satisfies its local relation. -/
theorem covariantDerivativeWithin_spec (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (hex : ∃ D, HasCovariantDerivativeWithinAt C c f J t D) :
    HasCovariantDerivativeWithinAt C c f J t (covariantDerivativeWithin C c f J t) := by
  classical
  simp only [covariantDerivativeWithin, dite_eq_left hex]
  exact Classical.choose_spec hex

theorem covariantDerivativeWithin_eq (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D) :
    covariantDerivativeWithin C c f J t = D :=
  covariantDerivative_unique C ht hJ (covariantDerivativeWithin_spec C ⟨D, hD⟩) hD

/-- In particular, the closed nontrivial segment includes both one-sided
endpoints. Constant curves, zero velocities and rank zero are allowed. -/
theorem segment_derivative (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {l q : ℝ} (hlq : l < q)
    (hc : P202.CurveData.CoordinateC1On S c (Icc l q)) (hc' : ContinuousOn c (Icc l q))
    (hf : C1FieldOn (B := B) c f (Icc l q)) {t : ℝ} (ht : t ∈ Icc l q) :
    HasCovariantDerivativeWithinAt C c f (Icc l q) t
      (covariantDerivativeWithin C c f (Icc l q) t) ∧
    ∀ D, HasCovariantDerivativeWithinAt C c f (Icc l q) t D →
      D = covariantDerivativeWithin C c f (Icc l q) t := by
  have h := covariantDerivativeWithin_spec C (exists_covariantDerivative C ht hc hc' hf)
  exact ⟨h, fun _ hD => covariantDerivative_unique C ht (uniqueDiffOn_Icc hlq t ht) hD h⟩

@[simp] theorem coefficients_add {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (c : ℝ → M) (f g : (t : ℝ) → E (c t)) :
    coefficientsAlong b c (fun t => f t + g t) =
      fun t => coefficientsAlong b c f t + coefficientsAlong b c g t := by
  classical
  funext t
  by_cases hp : c t ∈ U
  · simp only [coefficientsAlong, dite_eq_left hp, map_add]
  · simp only [coefficientsAlong, dite_eq_right hp, add_zero]

@[simp] theorem coefficients_smul {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (c : ℝ → M) (f : (t : ℝ) → E (c t)) (k : ℝ → ℝ) :
    coefficientsAlong b c (fun t => k t • f t) =
      fun t => k t • coefficientsAlong b c f t := by
  classical
  funext t
  by_cases hp : c t ∈ U
  · simp only [coefficientsAlong, dite_eq_left hp, map_smul]
  · simp only [coefficientsAlong, dite_eq_right hp, smul_zero]

/-- Additivity in the field, proved using coefficients in one common frame. -/
theorem derivative_add (C : Connection B) {c : ℝ → M}
    {f g : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D F : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    (hF : HasCovariantDerivativeWithinAt C c g J t F) :
    HasCovariantDerivativeWithinAt C c (fun t => f t + g t) J t (D + F) := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, hDeq⟩ := hD
  obtain ⟨w', hw⟩ := exists_coefficients_deriv C ht hF b hp
  have hFeq := local_formula C ht hJ hF b hp hV hw
  refine ⟨V, hV, U, hU, b, hp, v' + w', ?_, ?_⟩
  · rw [coefficients_add]
    apply hasDerivWithinAt_pi.mpr
    intro i
    exact (hasDerivWithinAt_pi.mp hv i).add (hasDerivWithinAt_pi.mp hw i)
  · rw [hDeq, hFeq]
    simp only [frameDerivative, coefficients_add, Matrix.mulVec_add]
    rw [← map_add]
    congr 1
    abel

/-- The scalar product rule holds for arbitrary C¹ scalar functions of the
parameter, including at one-sided endpoints. -/
theorem derivative_smul (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {k : ℝ → ℝ} {k' : ℝ} (hk : HasDerivWithinAt k k' J t) :
    HasCovariantDerivativeWithinAt C c (fun t => k t • f t) J t
      (k' • f t + k t • D) := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, rfl⟩ := hD
  refine ⟨V, hV, U, hU, b, hp,
    k' • coefficientsAlong b c f t + k t • v', ?_, ?_⟩
  · rw [coefficients_smul]
    apply hasDerivWithinAt_pi.mpr
    intro i
    convert hk.fun_mul (hasDerivWithinAt_pi.mp hv i) using 1
  · apply (b.basis ⟨c t, hp⟩).equivFun.injective
    simp only [map_add, map_smul, frameDerivative, LinearEquiv.apply_symm_apply,
      coefficients_smul, Matrix.mulVec_smul,
      ← coefficientsAlong_of_mem b c f t hp, smul_add]
    abel

/-- Within velocities obey the chain rule for arbitrary C¹ parameter maps.
No sign or nonvanishing condition occurs. -/
theorem velocity_reparam {c : ℝ → M} {φ : ℝ → ℝ} {I J : Set ℝ} {s : ℝ} {k : ℝ}
    {V : TangentSpace S (c (φ s))} (hV : HasVelocityWithinAt S c J (φ s) V)
    (hφ : HasDerivWithinAt φ k I s) (hmaps : MapsTo φ I J) :
    HasVelocityWithinAt S (c ∘ φ) I s (k • V) := by
  obtain ⟨hc, e, he, hp, hd⟩ := hV
  refine ⟨hc.comp hφ.continuousWithinAt hmaps, e, he, hp, ?_⟩
  simpa only [Function.comp_def, map_smul] using hd.scomp s hφ hmaps

@[simp] theorem connectionMatrix_smul (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (p : U)
    (k : ℝ) (V : TangentSpace S p.val) :
    connectionMatrix C b p (k • V) = k • connectionMatrix C b p V := by
  ext i j
  exact (connectionForm C b p i j).map_smul k V

/-- The local derivative scales in the actual new tangent direction. -/
theorem frameDerivative_reparam (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (φ : ℝ → ℝ) (s : ℝ)
    (hp : c (φ s) ∈ U) (k : ℝ) (V : TangentSpace S (c (φ s))) (v' : Euclidean r) :
    frameDerivative C b (c ∘ φ) (fun s => f (φ s)) s hp (k • V) (k • v') =
      k • frameDerivative C b c f (φ s) hp V v' := by
  unfold frameDerivative
  have hcoeff : coefficientsAlong b (c ∘ φ) (fun s => f (φ s)) s =
      coefficientsAlong b c f (φ s) := rfl
  rw [hcoeff]
  dsimp only [Function.comp_apply]
  have hmat := connectionMatrix_smul C b ⟨c (φ s), hp⟩ k V
  rw [hmat, Matrix.smul_mulVec, ← smul_add, map_smul]

/-- The reparametrization rule on arbitrary one-sided domains, including
constant maps, zero t', and orientation reversing maps whenever they map the
stated source parameter domain into the target parameter domain. -/
theorem derivative_reparam (C : Connection B)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ}
    {I J : Set ℝ} {s : ℝ} {k : ℝ} {D : E (c (φ s))}
    (hD : HasCovariantDerivativeWithinAt C c f J (φ s) D)
    (hφ : HasDerivWithinAt φ k I s) (hmaps : MapsTo φ I J) :
    HasCovariantDerivativeWithinAt C (c ∘ φ) (fun s => f (φ s)) I s (k • D) := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, rfl⟩ := hD
  refine ⟨k • V, velocity_reparam hV hφ hmaps, U, hU, b, hp, k • v', ?_, ?_⟩
  · exact hv.scomp s hφ hmaps
  · exact (frameDerivative_reparam C b c f φ s hp k V v').symm

/-- Reparametrization for the constructed derivative field itself. -/
theorem covariantDerivativeWithin_reparam (C : Connection B)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ}
    {I J : Set ℝ} {s : ℝ} {k : ℝ}
    (hs : s ∈ I) (hI : UniqueDiffWithinAt ℝ I s)
    (ht : φ s ∈ J) (hJ : UniqueDiffWithinAt ℝ J (φ s))
    {D : E (c (φ s))} (hD : HasCovariantDerivativeWithinAt C c f J (φ s) D)
    (hφ : HasDerivWithinAt φ k I s) (hmaps : MapsTo φ I J) :
    covariantDerivativeWithin C (c ∘ φ) (fun s => f (φ s)) I s =
      k • covariantDerivativeWithin C c f J (φ s) := by
  rw [covariantDerivativeWithin_eq C hs hI (derivative_reparam C hD hφ hmaps),
    covariantDerivativeWithin_eq C ht hJ hD]

/-- Ordinary differentiation is the specialization to the full parameter germ. -/
theorem ordinary_velocity_iff {c : ℝ → M} {t : ℝ} {V : TangentSpace S (c t)} :
    HasVelocityWithinAt S c univ t V ↔ P202.CurveData.HasVelocityAt S c t V := by
  simp only [HasVelocityWithinAt, P202.CurveData.HasVelocityAt,
    continuousWithinAt_univ, hasDerivWithinAt_univ]

theorem ordinary_reparam (C : Connection B)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ}
    {s k : ℝ} {D : E (c (φ s))}
    (hD : HasCovariantDerivativeAt C c f (φ s) D) (hφ : HasDerivAt φ k s) :
    HasCovariantDerivativeAt C (c ∘ φ) (fun s => f (φ s)) s (k • D) :=
  derivative_reparam C hD hφ.hasDerivWithinAt (mapsTo_univ _ _)

/-- A pulled-back smooth local section differentiates in the actual intrinsic
velocity direction. This holds even for C¹, rather than smooth, curves. -/
theorem derivative_local_section (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (z : LocalSection B U hU)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V) :
    HasCovariantDerivativeWithinAt C c
      (fun s => SmoothManifolds.SectionExtension.totalSection z.val (c s)) J t
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection z.val) (c t) V) := by
  let f := fun s => SmoothManifolds.SectionExtension.totalSection z.val (c s)
  let g (i : Fin r) := totalize
    (fun p : U => SmoothManifolds.FrameData.coefficients b z.val p i)
  let v' : Euclidean r := fun i => scalarDerivative S (g i) (c t) V
  have hd : HasDerivWithinAt (coefficientsAlong b c f) v' J t := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    have hg : VectorSmoothAt S.smoothStructure.val (g i) (c t) :=
      VectorSmoothAt.totalize hU
        ((SmoothManifolds.Frames.smooth_section_iff_coefficients B U hU b z.val).mp z.property i
          ⟨c t, hp⟩)
    apply (scalar_chain hV (g i) hg).congr_of_eventuallyEq_of_mem _ ht
    filter_upwards [hV.1.eventually (hU.mem_nhds hp)] with s hs
    simp only [f, g, Function.comp_apply, coefficientsAlong_of_mem b c _ s hs,
      totalize_of_mem _ (c s) hs, SmoothManifolds.FrameData.coefficients,
      SmoothManifolds.SectionExtension.totalSection_of_mem _ (c s) hs]
  refine ⟨V, hV, U, hU, b, hp, v', hd, ?_⟩
  apply (b.basis ⟨c t, hp⟩).equivFun.injective
  simp only [frameDerivative, LinearEquiv.apply_symm_apply]
  ext i
  rw [ConnectionForms.local_frame_formula B C b z ⟨c t, hp⟩ V i]
  simp only [v', g, Pi.add_apply, Matrix.mulVec, dotProduct,
    coefficientsAlong_of_mem b c f t hp, f,
    SmoothManifolds.SectionExtension.totalSection_of_mem _ (c t) hp,
    connectionMatrix]
  rfl

/-- For a global smooth section the local derivative is precisely the original
connection in direction γ'(t). No metric or torsion condition is involved. -/
theorem derivative_section (C : Connection B) (z : Section B)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V) :
    HasCovariantDerivativeWithinAt C c (fun s => z.val (c s)) J t
      (pointDerivative C z.val (c t) V) := by
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B (c t)
  let z' := restrictGlobalSection z U hU
  let f := SmoothManifolds.SectionExtension.totalSection z'.val
  have hfg : ∀ᶠ p in 𝓝 (c t), f p = z.val p := by
    filter_upwards [hU.mem_nhds hp] with p hpu
    simp only [f, z', SmoothManifolds.SectionExtension.totalSection_of_mem _ p hpu]
    rfl
  have h := derivative_local_section C b z' ht hp hV
  have hpoint : pointDerivative C f (c t) = pointDerivative C z.val (c t) :=
    ConnectionForms.pointDerivative_congr B C f z.val (c t)
      (ConnectionForms.exists_section_representative B U hU f
        (SmoothManifolds.SectionExtension.totalSection_smooth B hU z'.val z'.property) (c t) hp)
      hfg
  obtain ⟨V', hV', W, hW, d, hq, v', hv, hEq⟩ := h
  have hcoeff : coefficientsAlong d c (fun s => z.val (c s)) =ᶠ[𝓝[J] t]
      coefficientsAlong d c (fun s => f (c s)) := by
    filter_upwards [hV.1 hfg] with s hs
    change f (c s) = z.val (c s) at hs
    simp only [coefficientsAlong, hs]
  have hd : HasDerivWithinAt (coefficientsAlong d c (fun s => z.val (c s))) v' J t :=
    hv.congr_of_eventuallyEq_of_mem hcoeff ht
  refine ⟨V', hV', W, hW, d, hq, v', hd, ?_⟩
  change pointDerivative C f (c t) V = _ at hEq
  rw [hpoint] at hEq
  rw [hEq]
  unfold frameDerivative
  rw [hcoeff.eq_of_nhdsWithin ht]

/-- Evaluation of the original connection on a smooth vector field agrees with
our C¹ construction whenever its value is the actual curve velocity. -/
theorem derivative_section_field (C : Connection B) (z : Section B) (X : Field S)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hV : HasVelocityWithinAt S c J t (X.val (c t))) :
    HasCovariantDerivativeWithinAt C c (fun s => z.val (c s)) J t
      ((C.cov X z).val (c t)) := by
  rw [← ConnectionForms.pointDerivative_global B C z (c t) X]
  exact derivative_section C z ht hV

/-- The displayed curve formula for an actual row-frame expansion e(γ)v. -/
theorem derivative_frame_expansion (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {v : ℝ → Euclidean r} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c J t V) {v' : Euclidean r}
    (hv : HasDerivWithinAt v v' J t) :
    HasCovariantDerivativeWithinAt C c (frameFieldAlong b c v) J t
      ((b.basis ⟨c t, hp⟩).equivFun.symm
        (v' + (connectionMatrix C b ⟨c t, hp⟩ V).mulVec (v t))) := by
  classical
  have heq : coefficientsAlong b c (frameFieldAlong b c v) =ᶠ[𝓝[J] t] v := by
    filter_upwards [hV.1.eventually (hU.mem_nhds hp)] with s hs
    rw [coefficientsAlong_of_mem b c _ s hs]
    unfold frameFieldAlong
    split_ifs with h
    · exact LinearEquiv.apply_symm_apply _ _
    · exact (h hs).elim
  refine ⟨V, hV, U, hU, b, hp, v', hv.congr_of_eventuallyEq_of_mem heq ht, ?_⟩
  simp only [frameDerivative, heq.eq_of_nhdsWithin ht]

/-- Real scalar linearity as a special case of the parameter scalar product rule. -/
theorem derivative_const_smul (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ} {D : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D) (k : ℝ) :
    HasCovariantDerivativeWithinAt C c (fun t => k • f t) J t (k • D) := by
  simpa only [zero_smul, zero_add] using
    derivative_smul C hD (hasDerivWithinAt_const t J k)

/-- The constructed derivative field is additive on differentiable fields. -/
theorem covariantDerivativeWithin_add (C : Connection B) {c : ℝ → M}
    {f g : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D F : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    (hF : HasCovariantDerivativeWithinAt C c g J t F) :
    covariantDerivativeWithin C c (fun t => f t + g t) J t =
      covariantDerivativeWithin C c f J t + covariantDerivativeWithin C c g J t := by
  rw [covariantDerivativeWithin_eq C ht hJ (derivative_add C ht hJ hD hF),
    covariantDerivativeWithin_eq C ht hJ hD, covariantDerivativeWithin_eq C ht hJ hF]

/-- The constructed derivative field satisfies the scalar product rule. -/
theorem covariantDerivativeWithin_smul (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {k : ℝ → ℝ} {k' : ℝ} (hk : HasDerivWithinAt k k' J t) :
    covariantDerivativeWithin C c (fun t => k t • f t) J t =
      k' • f t + k t • covariantDerivativeWithin C c f J t := by
  rw [covariantDerivativeWithin_eq C ht hJ (derivative_smul C hD hk),
    covariantDerivativeWithin_eq C ht hJ hD]


/-! Public aliases of the independent canonical objects. -/
noncomputable abbrev HasVelocityWithinAt := @P202.CurveConnectionData.HasVelocityWithinAt
noncomputable abbrev coefficientsAlong := @P202.CurveConnectionData.coefficientsAlong
noncomputable abbrev frameFieldAlong := @P202.CurveConnectionData.frameFieldAlong
noncomputable abbrev frameDerivative := @P202.CurveConnectionData.frameDerivative
noncomputable abbrev C1FieldOn := @P202.CurveConnectionData.C1FieldOn
noncomputable abbrev HasCovariantDerivativeWithinAt := @P202.CurveConnectionData.HasCovariantDerivativeWithinAt
noncomputable abbrev covariantDerivativeWithin := @P202.CurveConnectionData.covariantDerivativeWithin
noncomputable abbrev HasCovariantDerivativeAt := @P202.CurveConnectionData.HasCovariantDerivativeAt
noncomputable abbrev covariantDerivative := @P202.CurveConnectionData.covariantDerivative

end P202.Geometry.CurveCovariantDerivative
