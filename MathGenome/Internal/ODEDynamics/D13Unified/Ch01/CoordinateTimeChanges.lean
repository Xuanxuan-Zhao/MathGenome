import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.CoordinateTimeChanges
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
open Set Function
open Specs.D13Unified.Ch01.SolutionConcepts

namespace D13Unified
universe u v
variable {E : Type u} {G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace C1Change

def symm (H : C1Change E G) : C1Change G E where
  source := H.target
  target := H.source
  open_source := H.open_target
  open_target := H.open_source
  forward := H.inverse
  inverse := H.forward
  map_source := H.map_target
  map_target := H.map_source
  left_inv := H.right_inv
  right_inv := H.left_inv
  forward_c1 := H.inverse_c1
  inverse_c1 := H.forward_c1

theorem differentiable_forward (H : C1Change E G) {x : E} (hx : x ∈ H.source) :
    DifferentiableAt ℝ H.forward x :=
  H.forward_c1.differentiableOn_one.differentiableAt (H.open_source.mem_nhds hx)

theorem differentiable_inverse (H : C1Change E G) {z : G} (hz : z ∈ H.target) :
    DifferentiableAt ℝ H.inverse z :=
  H.inverse_c1.differentiableOn_one.differentiableAt (H.open_target.mem_nhds hz)

/-- The inverse derivative identity is proved from the local inverse law. -/
theorem inverse_derivative (H : C1Change E G) {x : E} (hx : x ∈ H.source) (v : E) :
    fderiv ℝ H.inverse (H.forward x) (fderiv ℝ H.forward x v) = v := by
  have hd := (H.differentiable_inverse (H.map_source hx)).hasFDerivAt.comp x
    (H.differentiable_forward hx).hasFDerivAt
  have he : (H.inverse ∘ H.forward) =ᶠ[nhds x] id :=
    Filter.Eventually.mono (H.open_source.mem_nhds hx) (fun y hy => H.left_inv y hy)
  have hi := hd.congr_of_eventuallyEq he.symm
  have hh := hi.unique (hasFDerivAt_id x)
  exact congrArg (fun A : E →L[ℝ] E => A v) hh

theorem inverse_time_derivative (θ : C1Change ℝ ℝ) {r : ℝ} (hr : r ∈ θ.source) :
    deriv θ.inverse (θ.forward r) * deriv θ.forward r = 1 := by
  have hd := (θ.differentiable_inverse (θ.map_source hr)).hasDerivAt.comp r
    (θ.differentiable_forward hr).hasDerivAt
  have he : (θ.inverse ∘ θ.forward) =ᶠ[nhds r] id :=
    Filter.Eventually.mono (θ.open_source.mem_nhds hr) (fun y hy => θ.left_inv y hy)
  exact (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id r)

end C1Change

namespace ODE

theorem inCoordinates_eval (F : ODE E) (H : C1Change E G) {t : ℝ} {z : G}
    (hz : (t,z) ∈ (F.inCoordinates H).domain) :
    (F.inCoordinates H).eval t z =
      fderiv ℝ H.forward (H.inverse z) (F.eval t (H.inverse z)) := by
  rw [(F.inCoordinates H).eval_of_mem hz, F.eval_of_mem hz.2]
  rfl

theorem inTime_eval (F : ODE E) (θ : C1Change ℝ ℝ) {r : ℝ} {x : E}
    (hx : (r,x) ∈ (F.inTime θ).domain) :
    (F.inTime θ).eval r x = deriv θ.forward r • F.eval (θ.forward r) x := by
  rw [(F.inTime θ).eval_of_mem hx, F.eval_of_mem hx.2]
  rfl

end ODE

/-- Equality on the actual open interval suffices for the classical predicate. -/
theorem classicalSolutionOn_congr (F : ODE E) (I : OpenTimeInterval) (x y : ℝ → E)
    (hxy : EqOn x y I.carrier) : IsClassicalSolutionOn F I x ↔ IsClassicalSolutionOn F I y := by
  exact (classical_iff_solutionOn F I x).trans
    ((solutionOn_congr F I.toTimeInterval x y hxy).trans
      (classical_iff_solutionOn F I y).symm)

theorem coordinate_forward (F : ODE E) (H : C1Change E G) (I : OpenTimeInterval)
    {x : ℝ → E} (hx : IsClassicalSolutionOn F I x) (hs : MapsTo x I.carrier H.source) :
    IsClassicalSolutionOn (F.inCoordinates H) I (H.forward ∘ x) := by
  have hg : ∀ t ∈ I.carrier, (t, (H.forward ∘ x) t) ∈ (F.inCoordinates H).domain := by
    intro t ht
    exact ⟨H.map_source (hs ht), by simpa only [comp_apply, H.left_inv _ (hs ht)]
      using (hx.2.1 t ht)⟩
  refine ⟨H.forward_c1.comp hx.1 hs, hg, ?_⟩
  intro t ht
  rw [F.inCoordinates_eval H (hg t ht)]
  simpa only [comp_apply, H.left_inv _ (hs ht)] using
    (H.differentiable_forward (hs ht)).hasFDerivAt.comp_hasDerivAt t (hx.2.2 t ht)

theorem coordinate_backward (F : ODE E) (H : C1Change E G) (I : OpenTimeInterval)
    {z : ℝ → G} (hz : IsClassicalSolutionOn (F.inCoordinates H) I z) :
    IsClassicalSolutionOn F I (H.inverse ∘ z) ∧
      MapsTo (H.inverse ∘ z) I.carrier H.source ∧
      EqOn (H.forward ∘ H.inverse ∘ z) z I.carrier := by
  have hs : MapsTo z I.carrier H.target := fun t ht => (hz.2.1 t ht).1
  refine ⟨⟨H.inverse_c1.comp hz.1 hs, fun t ht => (hz.2.1 t ht).2, ?_⟩,
    fun t ht => H.map_target (hs ht), fun t ht => H.right_inv _ (hs ht)⟩
  intro t ht
  have hd := (H.differentiable_inverse (hs ht)).hasFDerivAt.comp_hasDerivAt t
    (hz.2.2 t ht)
  rw [F.inCoordinates_eval H (hz.2.1 t ht)] at hd
  have hi := H.inverse_derivative (H.map_target (hs ht)) (F.eval t (H.inverse (z t)))
  rw [H.right_inv _ (hs ht)] at hi
  simpa only [comp_apply, hi] using hd

/-- Pullback of a solution by a change of time. -/
theorem time_forward (F : ODE E) (θ : C1Change ℝ ℝ) (J I : OpenTimeInterval)
    (hJ : θ.source = J.carrier) (hI : θ.target = I.carrier)
    {x : ℝ → E} (hx : IsClassicalSolutionOn F I x) :
    IsClassicalSolutionOn (F.inTime θ) J (x ∘ θ.forward) := by
  have hs : MapsTo θ.forward J.carrier I.carrier := by
    simpa only [hJ, hI] using θ.map_source
  have hg : ∀ r ∈ J.carrier, (r, (x ∘ θ.forward) r) ∈ (F.inTime θ).domain :=
    fun r hr => ⟨hJ.symm ▸ hr, hx.2.1 _ (hs hr)⟩
  refine ⟨hx.1.comp (hJ ▸ θ.forward_c1) hs, hg, ?_⟩
  intro r hr
  rw [F.inTime_eval θ (hg r hr)]
  exact (hx.2.2 _ (hs hr)).scomp r
    (θ.differentiable_forward (hJ.symm ▸ hr)).hasDerivAt

/-- The inverse time correspondence, with its exact inverse law on J. -/
theorem time_backward (F : ODE E) (θ : C1Change ℝ ℝ) (J I : OpenTimeInterval)
    (hJ : θ.source = J.carrier) (hI : θ.target = I.carrier)
    {y : ℝ → E} (hy : IsClassicalSolutionOn (F.inTime θ) J y) :
    IsClassicalSolutionOn F I (y ∘ θ.inverse) ∧
      EqOn (y ∘ θ.inverse ∘ θ.forward) y J.carrier := by
  have hs : MapsTo θ.inverse I.carrier J.carrier := by
    simpa only [hJ, hI] using θ.map_target
  refine ⟨⟨hy.1.comp (hI ▸ θ.inverse_c1) hs, ?_, ?_⟩, ?_⟩
  · intro t ht
    have hg := (hy.2.1 _ (hs ht)).2
    simpa only [comp_apply, θ.right_inv _ (hI.symm ▸ ht)] using hg
  · intro t ht
    have hd := (hy.2.2 _ (hs ht)).scomp t
      (θ.differentiable_inverse (hI.symm ▸ ht)).hasDerivAt
    rw [F.inTime_eval θ (hy.2.1 _ (hs ht))] at hd
    have hi := θ.symm.inverse_time_derivative (hI.symm ▸ ht)
    change deriv θ.forward (θ.inverse t) * deriv θ.inverse t = 1 at hi
    rw [smul_smul, mul_comm, hi, one_smul, θ.right_inv _ (hI.symm ▸ ht)] at hd
    exact hd
  · intro r hr
    simp only [comp_apply, θ.left_inv _ (hJ.symm ▸ hr)]

theorem coordinate_iff (F : ODE E) (H : C1Change E G) (I : OpenTimeInterval)
    (x : ℝ → E) (hs : MapsTo x I.carrier H.source) :
    IsClassicalSolutionOn (F.inCoordinates H) I (H.forward ∘ x) ↔
      IsClassicalSolutionOn F I x := by
  constructor
  · intro h
    exact (classicalSolutionOn_congr F I _ x
      (fun t ht => H.left_inv _ (hs ht))).mp (coordinate_backward F H I h).1
  · exact fun h => coordinate_forward F H I h hs

theorem coordinate_bijOn (F : ODE E) (H : C1Change E G) (I : OpenTimeInterval) :
    BijOn (fun v : I.carrier → E => H.forward ∘ v)
      {v | v ∈ SolutionValues F I ∧ ∀ t, v t ∈ H.source}
      (SolutionValues (F.inCoordinates H) I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, he⟩ := hv.1
    refine ⟨H.forward ∘ x, coordinate_forward F H I hx ?_, ?_⟩
    · intro t ht
      simpa only [he ⟨t, ht⟩] using hv.2 ⟨t, ht⟩
    · intro t
      exact congrArg H.forward (he t)
  · intro v hv w hw he
    funext t
    have h := congrArg H.inverse (congrFun he t)
    simpa only [comp_apply, H.left_inv _ (hv.2 t), H.left_inv _ (hw.2 t)] using h
  · rintro v ⟨z, hz, he⟩
    have hb := coordinate_backward F H I hz
    refine ⟨fun t => H.inverse (z t), ⟨⟨H.inverse ∘ z, hb.1, fun _ => rfl⟩,
      fun t => hb.2.1 t.property⟩, ?_⟩
    funext t
    exact (H.right_inv _ (hz.2.1 t t.property).1).trans (he t)

/-- Coordinate change is a bijection on actual-domain solution curves, and
transports every admissible initial datum. -/
theorem coordinate_change :
    Specs.D13Unified.Ch01.CoordinateTimeChanges.coordinateChangeExpected.{u,v} := by
  intro E G _ _ _ _ F H I
  refine ⟨fun _ hx hs => coordinate_forward F H I hx hs,
    fun _ hz => coordinate_backward F H I hz, coordinate_bijOn F H I, ?_⟩
  intro x s ξ hs hξ
  change (_ ∧ s ∈ I.carrier ∧ H.forward (x s) = H.forward ξ) ↔
    (_ ∧ s ∈ I.carrier ∧ x s = ξ)
  constructor
  · rintro ⟨hx, ht, he⟩
    refine ⟨(coordinate_iff F H I x hs).mp hx, ht, ?_⟩
    have hi := congrArg H.inverse he
    simpa only [H.left_inv _ (hs ht), H.left_inv _ hξ] using hi
  · rintro ⟨hx, ht, he⟩
    exact ⟨(coordinate_iff F H I x hs).mpr hx, ht, congrArg H.forward he⟩

theorem time_iff (F : ODE E) (θ : C1Change ℝ ℝ) (J I : OpenTimeInterval)
    (hJ : θ.source = J.carrier) (hI : θ.target = I.carrier) (x : ℝ → E) :
    IsClassicalSolutionOn (F.inTime θ) J (x ∘ θ.forward) ↔
      IsClassicalSolutionOn F I x := by
  constructor
  · intro h
    exact (classicalSolutionOn_congr F I _ x
      (fun t ht => congrArg x (θ.right_inv t (hI.symm ▸ ht)))).mp
        (time_backward F θ J I hJ hI h).1
  · exact fun h => time_forward F θ J I hJ hI h

/-- A clock change as a map between the actual time domains. -/
def C1Change.onIntervals (θ : C1Change ℝ ℝ) (J I : OpenTimeInterval)
    (hJ : θ.source = J.carrier) (hI : θ.target = I.carrier) : J.carrier → I.carrier :=
  fun r => ⟨θ.forward r, by rw [← hI]; exact θ.map_source (hJ.symm ▸ r.property)⟩

theorem time_bijOn (F : ODE E) (θ : C1Change ℝ ℝ) (J I : OpenTimeInterval)
    (hJ : θ.source = J.carrier) (hI : θ.target = I.carrier) :
    BijOn (fun v : I.carrier → E => v ∘ θ.onIntervals J I hJ hI)
      (SolutionValues F I) (SolutionValues (F.inTime θ) J) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro v ⟨x, hx, he⟩
    exact ⟨x ∘ θ.forward, time_forward F θ J I hJ hI hx,
      fun r => he (θ.onIntervals J I hJ hI r)⟩
  · intro v hv w hw he
    funext t
    let r : J.carrier := ⟨θ.inverse t, by rw [← hJ]; exact θ.map_target (hI.symm ▸ t.property)⟩
    have ht : θ.onIntervals J I hJ hI r = t := by
      apply Subtype.ext
      exact θ.right_inv t (hI.symm ▸ t.property)
    have h := congrFun he r
    change v (θ.onIntervals J I hJ hI r) = w (θ.onIntervals J I hJ hI r) at h
    simpa only [ht] using h
  · rintro v ⟨y, hy, he⟩
    have hb := time_backward F θ J I hJ hI hy
    refine ⟨fun t => y (θ.inverse t), ⟨y ∘ θ.inverse, hb.1, fun _ => rfl⟩, ?_⟩
    funext r
    change y (θ.inverse (θ.forward r)) = v r
    rw [θ.left_inv _ (hJ.symm ▸ r.property)]
    exact he r

/-- Both directions preserve exactly the indicated intervals, and composition
with the inverse clock is the inverse solution correspondence. -/
theorem time_change :
    Specs.D13Unified.Ch01.CoordinateTimeChanges.timeChangeExpected.{u} := by
  intro E _ _ F θ J I hJ hI
  refine ⟨?_, fun _ hx => time_forward F θ J I hJ hI hx,
    fun _ hy => time_backward F θ J I hJ hI hy, time_bijOn F θ J I hJ hI, ?_⟩
  · intro r hr hzero
    have h := θ.inverse_time_derivative (hJ.symm ▸ hr)
    rw [hzero, mul_zero] at h
    exact zero_ne_one h
  · intro x r ξ hr
    change (_ ∧ r ∈ J.carrier ∧ x (θ.forward r) = ξ) ↔
      (_ ∧ θ.forward r ∈ I.carrier ∧ x (θ.forward r) = ξ)
    have ht : θ.forward r ∈ I.carrier := hI ▸ θ.map_source (hJ.symm ▸ hr)
    exact ⟨fun h => ⟨(time_iff F θ J I hJ hI x).mp h.1, ht, h.2.2⟩,
      fun h => ⟨(time_iff F θ J I hJ hI x).mpr h.1, hr, h.2.2⟩⟩

theorem time_reversal :
    Specs.D13Unified.Ch01.CoordinateTimeChanges.timeReversalExpected.{u} := by
  intro E _ _ F I
  refine ⟨fun _ _ => Iff.rfl, ?_, fun x => time_iff F (timeReflection I) I.reflected I rfl rfl x, ?_⟩
  · intro r x hx
    rw [F.inTime_eval (timeReflection I) hx]
    simp only [timeReflection, deriv_neg'', neg_one_smul]
  · intro x s ξ
    change (_ ∧ -s ∈ I.reflected.carrier ∧ x (- -s) = ξ) ↔
      (_ ∧ s ∈ I.carrier ∧ x s = ξ)
    simp only [OpenTimeInterval.reflected, mem_preimage, neg_neg]
    exact and_congr_left fun _ => time_iff F (timeReflection I) I.reflected I rfl rfl x

/-- The state chain rule also applies to within derivatives at endpoints. -/
theorem coordinate_interval_forward (F : ODE E) (H : C1Change E G) (I : TimeInterval)
    {x : ℝ → E} (hx : IsSolutionOn F I x) (hs : MapsTo x I.carrier H.source) :
    IsSolutionOn (F.inCoordinates H) I (H.forward ∘ x) := by
  have hg : ∀ t ∈ I.carrier, (t, (H.forward ∘ x) t) ∈ (F.inCoordinates H).domain := by
    intro t ht
    exact ⟨H.map_source (hs ht), by simpa only [comp_apply, H.left_inv _ (hs ht)]
      using (hx.2.1 t ht)⟩
  refine ⟨H.forward_c1.continuousOn.comp hx.1 hs, hg, ?_⟩
  intro t ht
  rw [F.inCoordinates_eval H (hg t ht)]
  simpa only [comp_apply, H.left_inv _ (hs ht)] using
    (H.differentiable_forward (hs ht)).hasFDerivAt.comp_hasDerivWithinAt t (hx.2.2 t ht)

theorem coordinate_interval_backward (F : ODE E) (H : C1Change E G) (I : TimeInterval)
    {z : ℝ → G} (hz : IsSolutionOn (F.inCoordinates H) I z) :
    IsSolutionOn F I (H.inverse ∘ z) ∧
      MapsTo (H.inverse ∘ z) I.carrier H.source ∧
      EqOn (H.forward ∘ H.inverse ∘ z) z I.carrier := by
  have hs : MapsTo z I.carrier H.target := fun t ht => (hz.2.1 t ht).1
  refine ⟨⟨H.inverse_c1.continuousOn.comp hz.1 hs,
    fun t ht => (hz.2.1 t ht).2, ?_⟩,
    fun t ht => H.map_target (hs ht), fun t ht => H.right_inv _ (hs ht)⟩
  intro t ht
  have hd := (H.differentiable_inverse (hs ht)).hasFDerivAt.comp_hasDerivWithinAt t
    (hz.2.2 t ht)
  rw [F.inCoordinates_eval H (hz.2.1 t ht)] at hd
  have hi := H.inverse_derivative (H.map_target (hs ht)) (F.eval t (H.inverse (z t)))
  rw [H.right_inv _ (hs ht)] at hi
  simpa only [comp_apply, hi] using hd

theorem coordinate_interval_iff (F : ODE E) (H : C1Change E G) (I : TimeInterval)
    (x : ℝ → E) (hs : MapsTo x I.carrier H.source) :
    IsSolutionOn (F.inCoordinates H) I (H.forward ∘ x) ↔ IsSolutionOn F I x := by
  constructor
  · intro h
    exact (solutionOn_congr F I _ x
      (fun t ht => H.left_inv _ (hs ht))).mp (coordinate_interval_backward F H I h).1
  · exact fun h => coordinate_interval_forward F H I h hs

theorem coordinate_interval_change :
    Specs.D13Unified.Ch01.CoordinateTimeChanges.intervalCoordinateChangeExpected.{u,v} := by
  intro E G _ _ _ _ F H I
  refine ⟨fun x hs => coordinate_interval_iff F H I x hs,
    fun _ hz => coordinate_interval_backward F H I hz, ?_⟩
  intro x s ξ hs hξ
  change (_ ∧ s ∈ I.carrier ∧ H.forward (x s) = H.forward ξ) ↔
    (_ ∧ s ∈ I.carrier ∧ x s = ξ)
  constructor
  · rintro ⟨hx, ht, he⟩
    refine ⟨(coordinate_interval_iff F H I x hs).mp hx, ht, ?_⟩
    have hi := congrArg H.inverse he
    simpa only [H.left_inv _ (hs ht), H.left_inv _ hξ] using hi
  · rintro ⟨hx, ht, he⟩
    exact ⟨(coordinate_interval_iff F H I x hs).mpr hx, ht, congrArg H.forward he⟩

theorem time_interval_forward (F : ODE E) (θ : C1Change ℝ ℝ) (J I : TimeInterval)
    (hJ : J.carrier ⊆ θ.source) (hm : MapsTo θ.forward J.carrier I.carrier)
    {x : ℝ → E} (hx : IsSolutionOn F I x) :
    IsSolutionOn (F.inTime θ) J (x ∘ θ.forward) := by
  have hg : ∀ r ∈ J.carrier, (r, (x ∘ θ.forward) r) ∈ (F.inTime θ).domain :=
    fun r hr => ⟨hJ hr, hx.2.1 _ (hm hr)⟩
  refine ⟨hx.1.comp (θ.forward_c1.continuousOn.mono hJ) hm, hg, ?_⟩
  intro r hr
  rw [F.inTime_eval θ (hg r hr)]
  exact (hx.2.2 _ (hm hr)).scomp r
    (θ.differentiable_forward (hJ hr)).hasDerivAt.hasDerivWithinAt hm

theorem time_interval_backward (F : ODE E) (θ : C1Change ℝ ℝ) (J I : TimeInterval)
    (hJ : J.carrier ⊆ θ.source) (hI : I.carrier ⊆ θ.target)
    (hm : MapsTo θ.inverse I.carrier J.carrier)
    {y : ℝ → E} (hy : IsSolutionOn (F.inTime θ) J y) :
    IsSolutionOn F I (y ∘ θ.inverse) ∧
      EqOn (y ∘ θ.inverse ∘ θ.forward) y J.carrier := by
  refine ⟨⟨hy.1.comp (θ.inverse_c1.continuousOn.mono hI) hm, ?_, ?_⟩, ?_⟩
  · intro t ht
    have hg := (hy.2.1 _ (hm ht)).2
    simpa only [comp_apply, θ.right_inv _ (hI ht)] using hg
  · intro t ht
    have hd := (hy.2.2 _ (hm ht)).scomp t
      (θ.differentiable_inverse (hI ht)).hasDerivAt.hasDerivWithinAt hm
    rw [F.inTime_eval θ (hy.2.1 _ (hm ht))] at hd
    have hi := θ.symm.inverse_time_derivative (hI ht)
    change deriv θ.forward (θ.inverse t) * deriv θ.inverse t = 1 at hi
    rw [smul_smul, mul_comm, hi, one_smul, θ.right_inv _ (hI ht)] at hd
    exact hd
  · intro r hr
    simp only [comp_apply, θ.left_inv _ (hJ hr)]

theorem time_interval_iff (F : ODE E) (θ : C1Change ℝ ℝ) (J I : TimeInterval)
    (hJ : J.carrier ⊆ θ.source) (hI : I.carrier ⊆ θ.target)
    (hf : MapsTo θ.forward J.carrier I.carrier) (hi : MapsTo θ.inverse I.carrier J.carrier)
    (x : ℝ → E) :
    IsSolutionOn (F.inTime θ) J (x ∘ θ.forward) ↔ IsSolutionOn F I x := by
  constructor
  · intro h
    exact (solutionOn_congr F I _ x
      (fun t ht => congrArg x (θ.right_inv t (hI ht)))).mp
        (time_interval_backward F θ J I hJ hI hi h).1
  · exact fun h => time_interval_forward F θ J I hJ hf h

theorem time_interval_change :
    Specs.D13Unified.Ch01.CoordinateTimeChanges.intervalTimeChangeExpected.{u} := by
  intro E _ _ F θ J I hJ hI hf hi
  refine ⟨fun x => time_interval_iff F θ J I hJ hI hf hi x,
    fun _ hy => time_interval_backward F θ J I hJ hI hi hy, ?_⟩
  intro x r ξ hr
  change (_ ∧ r ∈ J.carrier ∧ x (θ.forward r) = ξ) ↔
    (_ ∧ θ.forward r ∈ I.carrier ∧ x (θ.forward r) = ξ)
  exact ⟨fun h => ⟨(time_interval_iff F θ J I hJ hI hf hi x).mp h.1, hf hr, h.2.2⟩,
    fun h => ⟨(time_interval_iff F θ J I hJ hI hf hi x).mpr h.1, hr, h.2.2⟩⟩

/-- A non-singleton real interval has unique within derivatives even at
included endpoints. The singleton case is treated separately below. -/
theorem TimeInterval.uniqueDiffOn_of_not_subsingleton (I : TimeInterval)
    (h : ¬ I.carrier.Subsingleton) : UniqueDiffOn ℝ I.carrier := by
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp h
  apply uniqueDiffOn_convex I.ordConnected.convex
  have hs : Icc (min a b) (max a b) ⊆ I.carrier := I.ordConnected.uIcc_subset ha hb
  refine (nonempty_Ioo.mpr (min_lt_max.mpr hab)).mono ?_
  intro r hr
  exact interior_mono hs (by simpa only [interior_Icc] using hr)

/-- The chain rule on the two actual intervals. -/
theorem intrinsic_time_forward (F : ODE E) (J I : TimeInterval) (θ : IntervalClock J I)
    {x : ℝ → E} (hx : IsSolutionOn F I x) :
    IsTimeChangedSolutionOn F θ (x ∘ θ.forward) := by
  refine ⟨hx.1.comp θ.continuous_forward θ.map_source,
    fun r hr => hx.2.1 _ (θ.map_source hr), ?_⟩
  intro r hr
  exact (hx.2.2 _ (θ.map_source hr)).scomp r (θ.hasDeriv_forward r hr) θ.map_source

/-- The inverse derivative product is derived on nondegenerate intervals;
no such identity is needed for a singleton interval. -/
theorem IntervalClock.derivative_product {J I : TimeInterval} (θ : IntervalClock J I)
    (hI : ¬ I.carrier.Subsingleton) {t : ℝ} (ht : t ∈ I.carrier) :
    θ.velocity (θ.inverse t) * θ.inverseVelocity t = 1 := by
  have hd := (θ.hasDeriv_forward _ (θ.map_target ht)).comp t
    (θ.hasDeriv_inverse t ht) θ.map_target
  have he : EqOn id (θ.forward ∘ θ.inverse) I.carrier :=
    fun r hr => (θ.right_inv r hr).symm
  have hi := hd.congr_of_mem he ht
  exact (I.uniqueDiffOn_of_not_subsingleton hI t ht).eq_deriv I.carrier hi
    (hasDerivWithinAt_id t I.carrier)

/-- Composition with the inverse clock recovers the original equation.
The singleton case uses exactly the shared vacuous within derivative. -/
theorem intrinsic_time_backward (F : ODE E) (J I : TimeInterval) (θ : IntervalClock J I)
    {y : ℝ → E} (hy : IsTimeChangedSolutionOn F θ y) :
    IsSolutionOn F I (y ∘ θ.inverse) ∧
      EqOn (y ∘ θ.inverse ∘ θ.forward) y J.carrier := by
  refine ⟨⟨hy.1.comp θ.continuous_inverse θ.map_target, ?_, ?_⟩,
    fun r hr => congrArg y (θ.left_inv r hr)⟩
  · intro t ht
    simpa only [comp_apply, θ.right_inv _ ht] using hy.2.1 _ (θ.map_target ht)
  · intro t ht
    by_cases hI : I.carrier.Subsingleton
    · change HasFDerivWithinAt (y ∘ θ.inverse) _ I.carrier t
      exact HasFDerivWithinAt.of_subsingleton hI
    · have hd := (hy.2.2 _ (θ.map_target ht)).scomp t
        (θ.hasDeriv_inverse t ht) θ.map_target
      rw [smul_smul, mul_comm, θ.derivative_product hI ht, one_smul,
        θ.right_inv _ ht] at hd
      exact hd

theorem intrinsic_time_iff (F : ODE E) (J I : TimeInterval) (θ : IntervalClock J I)
    (x : ℝ → E) :
    IsTimeChangedSolutionOn F θ (x ∘ θ.forward) ↔ IsSolutionOn F I x := by
  constructor
  · intro h
    exact (solutionOn_congr F I _ x
      (fun t ht => congrArg x (θ.right_inv t ht))).mp
        (intrinsic_time_backward F J I θ h).1
  · exact fun h => intrinsic_time_forward F J I θ h

theorem intrinsic_time_bijOn (F : ODE E) (J I : TimeInterval) (θ : IntervalClock J I) :
    BijOn (fun v : I.carrier → E => fun r : J.carrier =>
      v ⟨θ.forward r, θ.map_source r.property⟩)
      (IntervalSolutionValues F I) (TimeChangedSolutionValues F θ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro v ⟨x, hx, he⟩
    exact ⟨x ∘ θ.forward, intrinsic_time_forward F J I θ hx,
      fun r => he ⟨θ.forward r, θ.map_source r.property⟩⟩
  · intro v hv w hw he
    funext t
    let r : J.carrier := ⟨θ.inverse t, θ.map_target t.property⟩
    have ht : (⟨θ.forward r, θ.map_source r.property⟩ : I.carrier) = t := by
      apply Subtype.ext
      exact θ.right_inv t t.property
    have h := congrFun he r
    change v ⟨θ.forward r, θ.map_source r.property⟩ =
      w ⟨θ.forward r, θ.map_source r.property⟩ at h
    simpa only [ht] using h
  · rintro v ⟨y, hy, he⟩
    have hb := intrinsic_time_backward F J I θ hy
    refine ⟨fun t => y (θ.inverse t), ⟨y ∘ θ.inverse, hb.1, fun _ => rfl⟩, ?_⟩
    funext r
    change y (θ.inverse (θ.forward r)) = v r
    rw [θ.left_inv _ r.property]
    exact he r

theorem intrinsic_time_change :
    Specs.D13Unified.Ch01.CoordinateTimeChanges.intrinsicTimeChangeExpected.{u} := by
  intro E _ _ F J I θ
  refine ⟨intrinsic_time_iff F J I θ,
    fun _ hy => intrinsic_time_backward F J I θ hy, intrinsic_time_bijOn F J I θ, ?_⟩
  intro x r ξ hr
  exact ⟨fun h => ⟨(intrinsic_time_iff F J I θ x).mp h.1, θ.map_source hr, h.2⟩,
    fun h => ⟨(intrinsic_time_iff F J I θ x).mpr h.1, h.2.2⟩⟩

/-- Compatibility with the canonical continuous ODE on its open domain. -/
theorem interval_time_compatibility :
    Specs.D13Unified.Ch01.CoordinateTimeChanges.intervalTimeCompatibilityExpected.{u} := by
  intro E _ _ F θ J I hJ hI hf hi y
  constructor
  · rintro ⟨hc, hg, hd⟩
    have hgraph : ∀ r ∈ J.carrier, (r, y r) ∈ (F.inTime θ).domain :=
      fun r hr => ⟨hJ hr, hg r hr⟩
    refine ⟨hc, hgraph, ?_⟩
    intro r hr
    rw [F.inTime_eval θ (hgraph r hr)]
    exact hd r hr
  · rintro ⟨hc, hg, hd⟩
    refine ⟨hc, fun r hr => (hg r hr).2, ?_⟩
    intro r hr
    change HasDerivWithinAt y (deriv θ.forward r • F.eval (θ.forward r) (y r)) J.carrier r
    simpa only [F.inTime_eval θ (hg r hr)] using hd r hr

end D13Unified
