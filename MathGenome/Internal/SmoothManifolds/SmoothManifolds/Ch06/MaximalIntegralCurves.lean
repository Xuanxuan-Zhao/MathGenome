import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalIntegralCurves
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalExistenceUniqueness
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import Mathlib.Analysis.Calculus.ContDiff.Deriv

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.VectorFieldDerivations
namespace SmoothManifolds.IntegralCurves
open ModelData AtlasData MapData TangentData TangentBundleData VectorFieldData
  IntegralCurveData Set Filter
open scoped Topology ContDiff
universe u

/-- Smoothness in time follows by bootstrapping the actual autonomous equation. -/
theorem smooth_of_autonomous {n : ℕ} {I : Set ℝ} (hI : IsOpen I)
    {U : Set (Euclidean n)} {F : Euclidean n → Euclidean n}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) {x : ℝ → Euclidean n}
    (hx : ContinuousOn x I) (hrange : MapsTo x I U)
    (hd : ∀ t ∈ I, HasDerivAt x (F (x t)) t) :
    ContDiffOn ℝ (⊤ : ℕ∞) x I := by
  apply contDiffOn_infty.mpr
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr hx
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp]
    apply (contDiffOn_succ_iff_deriv_of_isOpen hI).mpr
    refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact ((hF.of_le (by simp)).comp ih hrange).congr
      (fun t ht => (hd t ht).deriv)

/-- Integral-curve predicates are local in the ambient time variable. -/
theorem integral_congr {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {I : Set ℝ} (hI : IsOpen I) {γ η : ℝ → M}
    (hγ : IsIntegralCurveOn X I γ) (heq : EqOn η γ I) :
    IsIntegralCurveOn X I η := by
  refine ⟨hγ.1.congr (fun t ht => heq ht), ?_⟩
  intro t ht e he hη
  have hev : η =ᶠ[𝓝 t] γ := mem_of_superset (hI.mem_nhds ht) (fun s hs => heq hs)
  have hγt : γ t ∈ e.source := by rwa [← heq ht]
  have h := hγ.2 t ht e he hγt
  refine ⟨h.1.congr_of_eventuallyEq (hev.fun_comp (fun q => (e q).val)), ?_⟩
  have hd := h.2.congr_of_eventuallyEq (hev.fun_comp (fun q => (e q).val))
  have hv := congrArg (fun q => TangentBundle.chartFiber B e he ⟨q, X.val q⟩) (heq ht)
  rw [TangentBundle.chartFiber_eq S B e he _ hη,
    TangentBundle.chartFiber_eq S B e he _ hγt] at hv
  exact hv.symm ▸ hd

theorem integral_mono {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {X : SmoothField B} {I J : Set ℝ} {γ : ℝ → M}
    (hγ : IsIntegralCurveOn X I γ) (hJI : J ⊆ I) : IsIntegralCurveOn X J γ :=
  ⟨hγ.1.mono hJI, fun t ht => hγ.2 t (hJI ht)⟩

/-- Maximality as a universal extension property forces uniqueness of both the
interval and the curve, with no assertion about unused representative values. -/
theorem maximal_unique_proof :
    Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_uniqueType.{u} := by
  intro n M _ S B X p I J γ η hγ hη
  have hJI := hγ.2.2.2 J η hη.1 hη.2.1 hη.2.2.1
  have hIJ := hη.2.2.2 I γ hγ.1 hγ.2.1 hγ.2.2.1
  exact ⟨Subset.antisymm hIJ.1 hJI.1, fun t ht => (hIJ.2 ht).symm⟩

/-- The actual open time-state domain is ℝ × U. Evaluation outside it is only
D13's zero-extension convention and is never used as an ODE hypothesis. -/
def coordinateODE {n : ℕ} (U : Set (Euclidean n)) (hU : IsOpen U)
    (F : Euclidean n → Euclidean n) (hc : ContinuousOn F U) :
    D13Unified.ODE (Euclidean n) where
  domain := Prod.snd ⁻¹' U
  isOpen_domain := hU.preimage continuous_snd
  field := fun q => F q.val.2
  continuous_field := hc.comp_continuous
    (continuous_snd.comp continuous_subtype_val) (fun q => q.property)

theorem coordinateODE_eval {n : ℕ} {U : Set (Euclidean n)} {hU : IsOpen U}
    {F : Euclidean n → Euclidean n} {hc : ContinuousOn F U}
    (t : ℝ) (z : Euclidean n) (hz : z ∈ U) :
    (coordinateODE U hU F hc).eval t z = F z := by
  simp [D13Unified.ODE.eval, coordinateODE, hz]

theorem coordinateODE_lipschitz {n : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    {F : Euclidean n → Euclidean n} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    (coordinateODE U hU F hF.continuousOn).LocallyLipschitzInState := by
  apply D13Unified.ODE.locallyLipschitzInState_of_contDiffOn
  have hh : ContDiffOn ℝ 1 (fun z : ℝ × Euclidean n => F z.2) (Prod.snd ⁻¹' U) :=
    (hF.of_le (by simp)).comp contDiffOn_snd (fun _ hz => hz)
  exact hh.congr (fun z hz => coordinateODE_eval (hU := hU) (hc := hF.continuousOn) z.1 z.2 hz)

section Charts
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
  (X : SmoothField B)

/-- Any chart description of an integral curve gives all chart descriptions.
The velocity transformation is the actual Jacobian of a smooth transition. -/
theorem integral_of_chart {I : Set ℝ} (hI : IsOpen I) {γ : ℝ → M}
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hc : ContinuousOn γ I) (hr : MapsTo γ I e.source)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => (e (γ t)).val) I)
    (hd : ∀ t (ht : t ∈ I), HasDerivAt (fun s => (e (γ s)).val)
      (B.fiberCoordinates.equiv e he (γ t) (hr ht) (X.val (γ t))) t) :
    IsIntegralCurveOn X I γ := by
  refine ⟨hc, ?_⟩
  intro t ht d hdm hdt
  have hp := hr ht
  have hcompat := S.smoothStructure.property.1.2 e he d hdm
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ :=
    chartContDiffAt_of_compatible hcompat hp hdt
  have hct := hc.continuousAt (hI.mem_nhds ht)
  have heq := hrep.comp_tendsto hct
  have hst := hs.contDiffAt (hI.mem_nhds ht)
  have hsF := (hF.contDiffAt (hU.mem_nhds hpU)).comp t hst
  have hdF := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hvel := TangentBundle.transition_jacobian S B.fiberCoordinates e d he hdm
    (γ t) hp hdt U F hU hpU hF hrep (X.val (γ t))
  exact ⟨hsF.congr_of_eventuallyEq heq.symm,
    hvel ▸ hdF.congr_of_eventuallyEq heq.symm⟩

/-- Euclidean models carry no state constraint. -/
def modelPoint (z : Euclidean n) : ModelSpace n .euclidean := ⟨z, mem_univ _⟩

theorem modelPoint_continuous : Continuous (modelPoint (n := n)) :=
  continuous_id.subtype_mk _

/-- Around every point the actual smooth section has an ambient smooth
coefficient map on an open coordinate domain contained in the chart target. -/
theorem coefficient_extension (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    ∃ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      ∀ z ∈ U, modelPoint z ∈ e.target ∧
        F z = TangentBundle.chartFiber B e he
          ⟨e.symm (modelPoint z), X.val (e.symm (modelPoint z))⟩ := by
  let H : M → Euclidean n := fun q =>
    TangentBundle.chartFiber B e he ⟨q, X.val q⟩
  have hH := TangentBundle.chartFiber_smoothAt S B S
    (fun q => ⟨q, X.val q⟩) p e he hp (X.smooth p)
  obtain ⟨W, hW, hpW, F, hF, hEq⟩ := hH.2 e he hp
  obtain ⟨V, hVEq, hV, hpV⟩ := eventually_nhds_iff.mp hEq
  let T := e.target ∩ e.symm ⁻¹' V
  have hT : IsOpen T := e.symm.continuousOn.isOpen_inter_preimage e.open_target hV
  let U := W ∩ modelPoint ⁻¹' T
  refine ⟨U, F, hW.inter (hT.preimage modelPoint_continuous), ?_, hF.mono inter_subset_left, ?_⟩
  · exact ⟨hpW, e.map_source hp, by simpa [modelPoint, e.left_inv hp] using hpV⟩
  · intro z hz
    refine ⟨hz.2.1, ?_⟩
    have hh := hVEq _ hz.2.2
    change F (e (e.symm (modelPoint z))).val = _ at hh
    rw [e.right_inv hz.2.1] at hh
    exact hh

/-- Local existence is invoked only after constructing the actual open
coordinate ODE and proving its state Lipschitz hypothesis. -/
theorem local_solution (p : M) :
    ∃ (I : D13Unified.OpenTimeInterval) (γ : ℝ → M),
      0 ∈ I.carrier ∧ γ 0 = p ∧ IsIntegralCurveOn X I.carrier γ := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, F, hU, hpU, hF, hcoeff⟩ := coefficient_extension X e he p hp
  let A := coordinateODE U hU F hF.continuousOn
  obtain ⟨I, x, hx, _⟩ :=
    D13Unified.Ch03.LocalExistenceUniqueness.local_existence_uniqueness
      A (coordinateODE_lipschitz hU hF) 0 (e p).val hpU
  have hrange : MapsTo x I.carrier U := hx.1.2.1
  have hxd (t : ℝ) (ht : t ∈ I.carrier) : HasDerivAt x (F (x t)) t := by
    have hd := hx.1.2.2 t ht
    rwa [coordinateODE_eval (hU := hU) (hc := hF.continuousOn) t (x t) (hrange ht)] at hd
  have hxs := smooth_of_autonomous I.isOpen hF hx.1.1.continuousOn hrange hxd
  let γ : ℝ → M := fun t => e.symm (modelPoint (x t))
  have htarget (t : ℝ) (ht : t ∈ I.carrier) : modelPoint (x t) ∈ e.target :=
    (hcoeff _ (hrange ht)).1
  have hsource : MapsTo γ I.carrier e.source := fun t ht => e.map_target (htarget t ht)
  have hcoords (t : ℝ) (ht : t ∈ I.carrier) : (e (γ t)).val = x t := by
    change (e (e.symm (modelPoint (x t)))).val = x t
    rw [e.right_inv (htarget t ht)]
    rfl
  have hγc : ContinuousOn γ I.carrier :=
    e.symm.continuousOn.comp
      (modelPoint_continuous.comp_continuousOn hx.1.1.continuousOn) htarget
  refine ⟨I, γ, hx.2.1, ?_, integral_of_chart X I.isOpen e he hγc hsource
    (hxs.congr hcoords) ?_⟩
  · change e.symm (modelPoint (x 0)) = p
    rw [hx.2.2]
    exact e.left_inv hp
  · intro t ht
    have hev : (fun s => (e (γ s)).val) =ᶠ[𝓝 t] x :=
      mem_of_superset (I.isOpen.mem_nhds ht) (fun s hs => hcoords s hs)
    have hv := (hcoeff (x t) (hrange ht)).2
    rw [TangentBundle.chartFiber_eq S B e he _ (hsource ht)] at hv
    exact hv ▸ (hxd t ht).congr_of_eventuallyEq hev

/-- Restricting an intrinsic integral curve to a coordinate neighborhood gives
an actual D13 classical solution with the original open coordinate state domain. -/
theorem chart_classical_solution {I : Set ℝ} {γ : ℝ → M}
    (hγ : IsIntegralCurveOn X I γ)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    {U : Set (Euclidean n)} (hU : IsOpen U) {F : Euclidean n → Euclidean n}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hcoeff : ∀ z ∈ U, modelPoint z ∈ e.target ∧
      F z = TangentBundle.chartFiber B e he
        ⟨e.symm (modelPoint z), X.val (e.symm (modelPoint z))⟩)
    (K : D13Unified.OpenTimeInterval) (hKI : K.carrier ⊆ I)
    (hr : ∀ t ∈ K.carrier, γ t ∈ e.source ∧ (e (γ t)).val ∈ U) :
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
      (coordinateODE U hU F hF.continuousOn) K (fun t => (e (γ t)).val) := by
  refine ⟨fun t ht => ((hγ.2 t (hKI ht) e he (hr t ht).1).1.of_le
    (by simp)).contDiffWithinAt,
    fun t ht => (hr t ht).2, ?_⟩
  intro t ht
  rw [coordinateODE_eval _ _ (hr t ht).2]
  have hv := (hcoeff (e (γ t)).val (hr t ht).2).2
  rw [show modelPoint (e (γ t)).val = e (γ t) from rfl,
    e.left_inv (hr t ht).1,
    TangentBundle.chartFiber_eq S B e he _ (hr t ht).1] at hv
  exact hv.symm ▸ (hγ.2 t (hKI ht) e he (hr t ht).1).2

/-- Euclidean uniqueness implies equality near any meeting time of two
manifold integral curves. The common chart is chosen at the meeting point. -/
theorem local_unique (I J : D13Unified.OpenTimeInterval) (γ η : ℝ → M)
    (hγ : IsIntegralCurveOn X I.carrier γ) (hη : IsIntegralCurveOn X J.carrier η)
    (s : ℝ) (hs : s ∈ I.carrier ∩ J.carrier) (hmeet : γ s = η s) :
    γ =ᶠ[𝓝 s] η := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (γ s)
  obtain ⟨U, F, hU, hpU, hF, hcoeff⟩ := coefficient_extension X e he (γ s) hp
  let V := e.source ∩ (fun q => (e q).val) ⁻¹' U
  have hV : IsOpen V :=
    (continuous_subtype_val.comp_continuousOn e.continuousOn).isOpen_inter_preimage
      e.open_source hU
  have hpV : γ s ∈ V := ⟨hp, hpU⟩
  have hηV : η s ∈ V := hmeet ▸ hpV
  have hnear : ∀ᶠ t in 𝓝 s,
      (t ∈ I.carrier ∩ J.carrier) ∧ γ t ∈ V ∧ η t ∈ V :=
    by
      filter_upwards [I.isOpen.mem_nhds hs.1, J.isOpen.mem_nhds hs.2,
        (hγ.1.continuousAt (I.isOpen.mem_nhds hs.1)).eventually (hV.mem_nhds hpV),
        (hη.1.continuousAt (J.isOpen.mem_nhds hs.2)).eventually (hV.mem_nhds hηV)]
        with t hIt hJt hγt hηt
      exact ⟨⟨hIt, hJt⟩, hγt, hηt⟩
  obtain ⟨l, r, hls, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let K := D13Unified.OpenTimeInterval.bounded l r (hls.1.trans hls.2)
  have hKγ := chart_classical_solution X hγ e he hU hF hcoeff K
    (fun t ht => (hsub ht).1.1) (fun t ht => (hsub ht).2.1)
  have hKη := chart_classical_solution X hη e he hU hF hcoeff K
    (fun t ht => (hsub ht).1.2) (fun t ht => (hsub ht).2.2)
  have heq := D13Unified.Ch03.LocalExistenceUniqueness.no_crossing
    (coordinateODE U hU F hF.continuousOn) (coordinateODE_lipschitz hU hF)
    K K (fun t => (e (γ t)).val) (fun t => (e (η t)).val) s hKγ hKη
    ⟨hls, hls⟩ (congrArg (fun q => (e q).val) hmeet)
  filter_upwards [isOpen_Ioo.mem_nhds hls] with t ht
  apply e.injOn (hsub ht).2.1.1 (hsub ht).2.2.1
  exact Subtype.ext (heq ⟨ht, ht⟩)

end Charts

/-- The coincidence set is closed by Hausdorffness and open by local ODE
uniqueness. Connectedness of the common time interval gives global equality. -/
theorem overlap_unique_proof :
    Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.overlap_uniqueType.{u} := by
  intro n M _ S B X I J γ η hγ hη s hs hmeet
  letI : T2Space M := S.topologicalManifold.hausdorff
  let A := I.carrier ∩ J.carrier
  letI : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp
    (I.ordConnected.inter J.ordConnected).isPreconnected
  have hclosed : IsClosed {t : A | γ t = η t} :=
    isClosed_eq (hγ.1.mono inter_subset_left).domRestrict
      (hη.1.mono inter_subset_right).domRestrict
  have hopen : IsOpen {t : A | γ t = η t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact (local_unique X I J γ η hγ hη t t.property ht).comp_tendsto
      (continuous_subtype_val.tendsto t)
  have hall : {t : A | γ t = η t} = univ :=
    (show IsClopen {t : A | γ t = η t} from ⟨hclosed, hopen⟩).eq_univ
      ⟨⟨s, hs⟩, hmeet⟩
  intro t ht
  exact (show (⟨t, ht⟩ : A) ∈ {t : A | γ t = η t} from hall ▸ mem_univ _)


/-- Glue all solutions through the initial point. Their domains have a common
point, so their open union is still an interval, even for an unbounded lifespan. -/
theorem maximal_exists_proof :
    Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_existsType.{u} := by
  intro n M _ S B X p
  classical
  let A := {a : D13Unified.OpenTimeInterval × (ℝ → M) //
    0 ∈ a.1.carrier ∧ a.2 0 = p ∧ IsIntegralCurveOn X a.1.carrier a.2}
  obtain ⟨I₀, γ₀, hI₀, hγ₀, hsol₀⟩ := local_solution X p
  let a₀ : A := ⟨(I₀, γ₀), hI₀, hγ₀, hsol₀⟩
  let D : Set ℝ := ⋃ a : A, a.val.1.carrier
  have hD0 : 0 ∈ D := mem_iUnion.mpr ⟨a₀, hI₀⟩
  have hDo : IsOpen D := isOpen_iUnion (fun a : A => a.val.1.isOpen)
  have hDc : OrdConnected D := by
    constructor
    intro a ha b hb t ht
    obtain ⟨x, hx⟩ := mem_iUnion.mp ha
    obtain ⟨y, hy⟩ := mem_iUnion.mp hb
    by_cases ht0 : t ≤ 0
    · exact mem_iUnion.mpr ⟨x, x.val.1.ordConnected.out hx x.property.1 ⟨ht.1, ht0⟩⟩
    · exact mem_iUnion.mpr ⟨y, y.val.1.ordConnected.out y.property.1 hy
        ⟨(le_of_not_ge ht0), ht.2⟩⟩
  let I : D13Unified.OpenTimeInterval := ⟨⟨D, ⟨0, hD0⟩, hDc⟩, hDo⟩
  let z : ℝ → M := fun t =>
    if h : ∃ a : A, t ∈ a.val.1.carrier then
      (Classical.choose h).val.2 t else p
  have hz (a : A) : EqOn z a.val.2 a.val.1.carrier := by
    intro t ht
    have hex : ∃ b : A, t ∈ b.val.1.carrier := ⟨a, ht⟩
    dsimp only [z]
    rw [dite_eq_left hex]
    exact overlap_unique_proof S B X (Classical.choose hex).val.1 a.val.1
      (Classical.choose hex).val.2 a.val.2
      (Classical.choose hex).property.2.2 a.property.2.2 0
      ⟨(Classical.choose hex).property.1, a.property.1⟩
      ((Classical.choose hex).property.2.1.trans a.property.2.1.symm)
      ⟨Classical.choose_spec hex, ht⟩
  have hlocal (a : A) : IsIntegralCurveOn X a.val.1.carrier z :=
    integral_congr a.val.1.isOpen a.property.2.2 (hz a)
  have hsol : IsIntegralCurveOn X D z := by
    constructor
    · intro t ht
      obtain ⟨a, ha⟩ := mem_iUnion.mp ht
      exact ((hlocal a).1.continuousAt (a.val.1.isOpen.mem_nhds ha)).continuousWithinAt
    · intro t ht e he hpt
      obtain ⟨a, ha⟩ := mem_iUnion.mp ht
      exact (hlocal a).2 t ha e he hpt
  refine ⟨I, z, hD0, (hz a₀ hI₀).trans hγ₀, hsol, ?_⟩
  intro J η hJ hη hηsol
  let a : A := ⟨(J, η), hJ, hη, hηsol⟩
  exact ⟨fun t ht => mem_iUnion.mpr ⟨a, ht⟩, hz a⟩

/-- Equilibria have a global constant maximal curve. In particular this covers
zero fields without dividing by a field norm or a positive dimension. -/
theorem equilibrium_maximal {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) (p : M) (hXp : X.val p = 0) :
    IsMaximalThrough X p D13Unified.OpenTimeInterval.whole (fun _ => p) := by
  have hc : IsIntegralCurveOn X univ (fun _ => p) := by
    refine ⟨continuous_const.continuousOn, ?_⟩
    intro t ht e he hp
    refine ⟨contDiffAt_const, ?_⟩
    simpa only [hXp, map_zero] using hasDerivAt_const t (e p).val
  refine ⟨mem_univ _, rfl, hc, ?_⟩
  intro J η hJ hη hsol
  refine ⟨subset_univ _, ?_⟩
  intro t ht
  exact overlap_unique_proof S B X D13Unified.OpenTimeInterval.whole J
    (fun _ => p) η hc hsol 0 ⟨mem_univ _, hJ⟩ hη.symm ⟨mem_univ _, ht⟩

/-- Every field in dimension zero is an equilibrium field. Empty manifolds
require no initial point and are already covered by the quantified statements. -/
theorem zero_dimension_maximal {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) (p : M) :
    IsMaximalThrough X p D13Unified.OpenTimeInterval.whole (fun _ => p) := by
  letI := tangent_zero S p
  exact equilibrium_maximal X p (Subsingleton.elim _ _)

end SmoothManifolds.IntegralCurves

namespace SmoothManifolds.IntegralCurves
universe u

theorem maximal_exists_conditional
    (_h1 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (_h2 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_h3 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_h4 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_h5 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_h6 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_h7 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u})
    : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_existsType.{u} :=
  maximal_exists_proof

end SmoothManifolds.IntegralCurves

namespace SmoothManifolds.IntegralCurves
universe u

theorem overlap_unique_conditional
    (_h1 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (_h2 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_h3 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_h4 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_h5 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_h6 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_h7 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u})
    : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.overlap_uniqueType.{u} :=
  overlap_unique_proof

end SmoothManifolds.IntegralCurves

namespace SmoothManifolds.IntegralCurves
universe u

theorem maximal_unique_conditional
    (_h1 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (_h2 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_h3 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_h4 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_h5 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_h6 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_h7 : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u})
    : Specs.SmoothManifolds.Ch06.MaximalIntegralCurves.maximal_uniqueType.{u} :=
  maximal_unique_proof

end SmoothManifolds.IntegralCurves

universe v8_closure_5209c091577e4c9f_u0
theorem _root_.«SmoothManifolds».«IntegralCurves».«maximal_exists» : _root_.«Specs».«SmoothManifolds».«Ch06».«MaximalIntegralCurves».«maximal_existsType».{v8_closure_5209c091577e4c9f_u0} :=
  @_root_.«SmoothManifolds».«IntegralCurves».«maximal_exists_conditional».{v8_closure_5209c091577e4c9f_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_5209c091577e4c9f_u0})
theorem _root_.«SmoothManifolds».«IntegralCurves».«maximal_unique» : _root_.«Specs».«SmoothManifolds».«Ch06».«MaximalIntegralCurves».«maximal_uniqueType».{v8_closure_5209c091577e4c9f_u0} :=
  @_root_.«SmoothManifolds».«IntegralCurves».«maximal_unique_conditional».{v8_closure_5209c091577e4c9f_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_5209c091577e4c9f_u0})
theorem _root_.«SmoothManifolds».«IntegralCurves».«overlap_unique» : _root_.«Specs».«SmoothManifolds».«Ch06».«MaximalIntegralCurves».«overlap_uniqueType».{v8_closure_5209c091577e4c9f_u0} :=
  @_root_.«SmoothManifolds».«IntegralCurves».«overlap_unique_conditional».{v8_closure_5209c091577e4c9f_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_5209c091577e4c9f_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_5209c091577e4c9f_u0})
