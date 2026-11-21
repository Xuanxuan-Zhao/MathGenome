import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.BoundaryTangentFlow
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalIntegralCurves
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.RegularConstraints
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence

namespace SmoothManifolds.BoundaryTangentFlow
open ModelData AtlasData MapData TangentData TangentBundleData VectorFieldData
  BoundaryData BoundaryFlowData Set Filter
open MaximalFlowData (CurveFamily flowDomain flow timeDomain)
open scoped Topology ContDiff
universe u

section Curves
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S} {X : SmoothField B}

/-- Integral-curve equations are local in the open time domain, on either model. -/
theorem integral_congr {I : Set ℝ} (hI : IsOpen I) {γ η : ℝ → M}
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

theorem integral_mono {I J : Set ℝ} {γ : ℝ → M}
    (hγ : IsIntegralCurveOn X I γ) (hJI : J ⊆ I) : IsIntegralCurveOn X J γ :=
  ⟨hγ.1.mono hJI, fun t ht => hγ.2 t (hJI ht)⟩

/-- Universal maximality determines the actual interval and all on-domain values. -/
theorem maximal_unique {p : M} {I J : D13Unified.OpenTimeInterval} {γ η : ℝ → M}
    (hγ : IsMaximalThrough X p I γ) (hη : IsMaximalThrough X p J η) :
    I.carrier = J.carrier ∧ EqOn γ η I.carrier := by
  have hJI := hγ.2.2.2 J η hη.1 hη.2.1 hη.2.2.1
  have hIJ := hη.2.2.2 I γ hγ.1 hγ.2.1 hγ.2.2.1
  exact ⟨Subset.antisymm hIJ.1 hJI.1, fun t ht => (hIJ.2 ht).symm⟩

/-- Translation of the time variable preserves the intrinsic equation. -/
theorem integral_translate {I : Set ℝ} {γ : ℝ → M}
    (hγ : IsIntegralCurveOn X I γ) (s : ℝ) :
    IsIntegralCurveOn X {t | s + t ∈ I} (fun t => γ (s + t)) := by
  refine ⟨hγ.1.comp (continuous_const.add continuous_id).continuousOn (fun t ht => ht), ?_⟩
  intro t ht e he hpt
  have h := hγ.2 (s + t) ht e he hpt
  refine ⟨h.1.comp t (contDiffAt_const.add contDiffAt_id), ?_⟩
  have hg : HasDerivAt (fun r : ℝ => s + r) 1 t := by
    simpa using (hasDerivAt_id t).const_add s
  convert! h.2.scomp t hg using 1 <;> simp [Function.comp_def]

end Curves

/-- The exact translated interval, with no boundedness assumption. -/
def translatedInterval (I : D13Unified.OpenTimeInterval) (s : ℝ) (hs : s ∈ I.carrier) :
    D13Unified.OpenTimeInterval where
  carrier := {t | s + t ∈ I.carrier}
  nonempty := ⟨0, by simpa using hs⟩
  ordConnected := I.ordConnected.preimage_mono (by intro x y h; linarith)
  isOpen := I.isOpen.preimage (continuous_const.add continuous_id)

section Coordinates
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S} (X : SmoothField B)

/-- An actual smooth ambient coefficient extension. Only its restriction to the
model is required to coincide with the field or lie in the chart target. -/
theorem coefficient_extension (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    ∃ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      ∀ z : ModelSpace n a, z.val ∈ U → z ∈ e.target ∧
        F z.val = TangentBundle.chartFiber B e he ⟨e.symm z, X.val (e.symm z)⟩ := by
  have hH := TangentBundle.chartFiber_smoothAt S B S
    (fun q => ⟨q, X.val q⟩) p e he hp (X.smooth p)
  obtain ⟨W, hW, hpW, F, hF, hEq⟩ := hH.2 e he hp
  obtain ⟨V, hVEq, hV, hpV⟩ := eventually_nhds_iff.mp hEq
  let T := e.target ∩ e.symm ⁻¹' V
  have hT : IsOpen T := e.symm.continuousOn.isOpen_inter_preimage e.open_target hV
  obtain ⟨O, hO, hOT⟩ := isOpen_induced_iff.mp hT
  refine ⟨W ∩ O, F, hW.inter hO, ⟨hpW, ?_⟩, hF.mono inter_subset_left, ?_⟩
  · have hpt : e p ∈ T := ⟨e.map_source hp, by simpa only [mem_preimage, e.left_inv hp] using hpV⟩
    rw [← hOT] at hpt
    exact hpt
  · intro z hz
    have hzT : z ∈ T := by rw [← hOT]; exact hz.2
    refine ⟨hzT.1, ?_⟩
    have hh := hVEq _ hzT.2
    change F (e (e.symm z)).val = _ at hh
    rwa [e.right_inv hzT.1] at hh

/-- Any chart description of a curve gives all its chart descriptions, also at
boundary states. The derivative transition is the intrinsic bundle Jacobian. -/
theorem integral_of_chart {I : Set ℝ} (hI : IsOpen I) {γ : ℝ → M}
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hc : ContinuousOn γ I) (hr : MapsTo γ I e.source)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => (e (γ t)).val) I)
    (hd : ∀ t (ht : t ∈ I), HasDerivAt (fun s => (e (γ s)).val)
      (B.fiberCoordinates.equiv e he (γ t) (hr ht) (X.val (γ t))) t) :
    IsIntegralCurveOn X I γ := by
  refine ⟨hc, ?_⟩
  intro t ht d hdm hdt
  have hp := hr ht
  have hcompat := S.smoothStructure.property.1.2 e he d hdm
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := chartContDiffAt_of_compatible hcompat hp hdt
  have hct := hc.continuousAt (hI.mem_nhds ht)
  have heq := hrep.comp_tendsto hct
  have hst := hs.contDiffAt (hI.mem_nhds ht)
  have hsF := (hF.contDiffAt (hU.mem_nhds hpU)).comp t hst
  have hdF := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hvel := TangentBundle.transition_jacobian S B.fiberCoordinates e d he hdm
    (γ t) hp hdt U F hU hpU hF hrep (X.val (γ t))
  exact ⟨hsF.congr_of_eventuallyEq heq.symm,
    hvel ▸ hdF.congr_of_eventuallyEq heq.symm⟩

/-- A curve in a chart is a classical solution for the actual ambient extension
ODE on its open state domain; no half-space is falsely declared open. -/
theorem chart_classical_solution {I : Set ℝ} {γ : ℝ → M}
    (hγ : IsIntegralCurveOn X I γ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    {U : Set (Euclidean n)} (hU : IsOpen U) {F : Euclidean n → Euclidean n}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hcoeff : ∀ z : ModelSpace n a, z.val ∈ U → z ∈ e.target ∧
      F z.val = TangentBundle.chartFiber B e he ⟨e.symm z, X.val (e.symm z)⟩)
    (K : D13Unified.OpenTimeInterval) (hKI : K.carrier ⊆ I)
    (hr : ∀ t ∈ K.carrier, γ t ∈ e.source ∧ (e (γ t)).val ∈ U) :
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
      (IntegralCurves.coordinateODE U hU F hF.continuousOn) K
      (fun t => (e (γ t)).val) := by
  refine ⟨fun t ht => ((hγ.2 t (hKI ht) e he (hr t ht).1).1.of_le
    (by simp)).contDiffWithinAt,
    fun t ht => (hr t ht).2, ?_⟩
  intro t ht
  rw [IntegralCurves.coordinateODE_eval _ _ (hr t ht).2]
  have hv := (hcoeff (e (γ t)) (hr t ht).2).2
  rw [e.left_inv (hr t ht).1,
    TangentBundle.chartFiber_eq S B e he _ (hr t ht).1] at hv
  exact hv.symm ▸ (hγ.2 t (hKI ht) e he (hr t ht).1).2

/-- Local uniqueness requires no tangency assumption: it compares only curves
that already remain in the model. -/
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
      (t ∈ I.carrier ∩ J.carrier) ∧ γ t ∈ V ∧ η t ∈ V := by
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
    (IntegralCurves.coordinateODE U hU F hF.continuousOn)
    (IntegralCurves.coordinateODE_lipschitz hU hF)
    K K (fun t => (e (γ t)).val) (fun t => (e (η t)).val) s hKγ hKη
    ⟨hls, hls⟩ (congrArg (fun q => (e q).val) hmeet)
  filter_upwards [isOpen_Ioo.mem_nhds hls] with t ht
  apply e.injOn (hsub ht).2.1.1 (hsub ht).2.2.1
  exact Subtype.ext (heq ⟨ht, ht⟩)

/-- Propagation from one meeting time across the whole common interval. -/
theorem overlap_unique (I J : D13Unified.OpenTimeInterval) (γ η : ℝ → M)
    (hγ : IsIntegralCurveOn X I.carrier γ) (hη : IsIntegralCurveOn X J.carrier η)
    (s : ℝ) (hs : s ∈ I.carrier ∩ J.carrier) (hmeet : γ s = η s) :
    EqOn γ η (I.carrier ∩ J.carrier) := by
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

end Coordinates

section HalfSpace

/-- The field extension is an autonomous ODE on exactly its ambient open set. -/
def ambientODE {n : ℕ} (U : Set (Euclidean n)) (hU : IsOpen U)
    (F : Euclidean n → Euclidean n) (hc : ContinuousOn F U) :
    D13Unified.AutonomousODE (Euclidean n) where
  domain := U
  isOpen_domain := hU
  field := fun z => F z.val
  continuous_field := hc.domRestrict

theorem ambientODE_eval {n : ℕ} {U : Set (Euclidean n)} {hU : IsOpen U}
    {F : Euclidean n → Euclidean n} {hc : ContinuousOn F U}
    {z : Euclidean n} (hz : z ∈ U) :
    (ambientODE U hU F hc).eval z = F z := by
  simp [D13Unified.AutonomousODE.eval,
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue, ambientODE, hz]

/-- Tangency gives vanishing of the ambient extension's normal component on
the whole local hyperplane, which is the hypothesis needed by ODE invariance. -/
theorem extension_normal_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n + 1) .halfSpace M} {B : TangentBundleStructure S}
    (X : SmoothField B) (hX : IsTangentToBoundary X)
    (e : ModelChart (n + 1) .halfSpace M) (he : e ∈ S.smoothStructure.val)
    {U : Set (Euclidean (n + 1))} {F : Euclidean (n + 1) → Euclidean (n + 1)}
    (hcoeff : ∀ z : ModelSpace (n + 1) .halfSpace, z.val ∈ U → z ∈ e.target ∧
      F z.val = TangentBundle.chartFiber B e he ⟨e.symm z, X.val (e.symm z)⟩) :
    ∀ z ∈ U, z (Fin.last n) = 0 → F z (Fin.last n) = 0 := by
  intro z hz hz0
  let y : ModelSpace (n + 1) .halfSpace := ⟨z, by
    change 0 ≤ z (Fin.last n)
    exact le_of_eq hz0.symm⟩
  obtain ⟨hy, hFy⟩ := hcoeff y hz
  have hp := e.map_target hy
  have hb : e.symm y ∈ intrinsicBoundary S := by
    apply (intrinsicBoundary_iff_chart S e he (e.symm y) hp).mpr
    rw [e.right_inv hy]
    exact hz0
  have htan := hX (e.symm y) hb e he hp
  change B.fiberCoordinates.equiv e he (e.symm y) hp (X.val (e.symm y)) (Fin.last n) = 0 at htan
  rw [TangentBundle.chartFiber_eq S B e he _ hp] at hFy
  change F y.val (Fin.last n) = 0
  rw [hFy]
  exact htan

/-- A smooth ambient ODE tangent to the coordinate hyperplane preserves its
zero set in both time directions, on every actual open solution interval. -/
theorem normal_zero_iff {n : ℕ} (A : D13Unified.AutonomousODE (Euclidean (n + 1)))
    (hA : ContDiffOn ℝ 1 A.eval A.domain)
    (htan : ∀ z ∈ A.domain, z (Fin.last n) = 0 → A.eval z (Fin.last n) = 0)
    (I : D13Unified.OpenTimeInterval) (x : ℝ → Euclidean (n + 1))
    (hx : D13Unified.IsClassicalAutonomousSolutionOn A I x)
    (s : ℝ) (hs : s ∈ I.carrier) (t : ℝ) (ht : t ∈ I.carrier) :
    x t (Fin.last n) = 0 ↔ x s (Fin.last n) = 0 := by
  let P : Euclidean (n + 1) →L[ℝ] ℝ := ContinuousLinearMap.proj (Fin.last n)
  have hrank (z : Euclidean (n + 1)) : Function.Surjective (fderiv ℝ P z) := by
    rw [P.hasFDerivAt.fderiv]
    intro r
    exact ⟨fun _ => r, rfl⟩
  have hz (r : ℝ) (hr : r ∈ I.carrier) (hxr : P (x r) = 0) :
      ∀ t ∈ I.carrier, P (x t) = 0 := by
    apply D13Unified.Ch11.RegularConstraints.constraint_on_solution A hA P
      P.contDiff.contDiffOn 0 (fun z _ _ => hrank z) ?_ I x hx r hr hxr
    intro z hz hz0
    rw [P.hasFDerivAt.fderiv]
    exact htan z hz hz0
  exact ⟨fun h => hz t ht h s hs, fun h => hz s hs h t ht⟩

/-- No crossing of the boundary hyperplane, including when the initial point
is on it. No positive-time or compactness restriction is used. -/
theorem halfspace_on_solution {n : ℕ}
    (A : D13Unified.AutonomousODE (Euclidean (n + 1)))
    (hA : ContDiffOn ℝ 1 A.eval A.domain)
    (htan : ∀ z ∈ A.domain, z (Fin.last n) = 0 → A.eval z (Fin.last n) = 0)
    (I : D13Unified.OpenTimeInterval) (x : ℝ → Euclidean (n + 1))
    (hx : D13Unified.IsClassicalAutonomousSolutionOn A I x)
    (s : ℝ) (hs : s ∈ I.carrier) (hxs : 0 ≤ x s (Fin.last n)) :
    ∀ t ∈ I.carrier, 0 ≤ x t (Fin.last n) := by
  intro t ht
  by_contra hn
  have hneg : x t (Fin.last n) < 0 := lt_of_not_ge hn
  have hpos : 0 < x s (Fin.last n) := by
    apply lt_of_le_of_ne hxs
    intro heq
    have hz := (normal_zero_iff A hA htan I x hx s hs t ht).mpr heq.symm
    linarith
  have hc : ContinuousOn (fun r => x r (Fin.last n)) I.carrier :=
    (continuous_apply (Fin.last n)).comp_continuousOn hx.1.continuousOn
  obtain ⟨r, hr, hr0⟩ := I.ordConnected.isPreconnected.intermediate_value ht hs hc
    (show (0 : ℝ) ∈ Icc (x t (Fin.last n)) (x s (Fin.last n)) from
      ⟨hneg.le, hpos.le⟩)
  have hz := (normal_zero_iff A hA htan I x hx s hs r hr).mp hr0
  linarith

end HalfSpace

section Existence
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S} (X : SmoothField B)

/-- Transfer a model-valued ambient solution back to the manifold. Values
outside the recorded interval are filled with the initial point. -/
theorem curve_of_ambient_solution (p : M) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    {U : Set (Euclidean n)} (hU : IsOpen U) {F : Euclidean n → Euclidean n}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hcoeff : ∀ z : ModelSpace n a, z.val ∈ U → z ∈ e.target ∧
      F z.val = TangentBundle.chartFiber B e he ⟨e.symm z, X.val (e.symm z)⟩)
    (I : D13Unified.OpenTimeInterval) (x : ℝ → Euclidean n)
    (hx : D13Unified.IsClassicalAutonomousIVPOn
      (ambientODE U hU F hF.continuousOn) I x 0 (e p).val)
    (hmodel : ∀ t ∈ I.carrier, x t ∈ modelSet n a) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsIntegralCurveOn X I.carrier γ ∧
      ∀ t ∈ I.carrier, γ t ∈ e.source ∧ (e (γ t)).val = x t := by
  classical
  let y : ℝ → ModelSpace n a := fun t =>
    if ht : t ∈ I.carrier then ⟨x t, hmodel t ht⟩ else e p
  have hyval (t : ℝ) (ht : t ∈ I.carrier) : (y t).val = x t := by simp [y, ht]
  have hyc : ContinuousOn y I.carrier := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun t : I.carrier => (y t).val) :=
      hx.1.1.continuousOn.domRestrict.congr (fun t => (hyval t t.property).symm)
    exact hc.subtype_mk _
  have htarget (t : ℝ) (ht : t ∈ I.carrier) : y t ∈ e.target :=
    (hcoeff (y t) (by rw [hyval t ht]; exact hx.1.2.1 t ht)).1
  let γ : ℝ → M := fun t => e.symm (y t)
  have hsource : MapsTo γ I.carrier e.source := fun t ht => e.map_target (htarget t ht)
  have hcoords (t : ℝ) (ht : t ∈ I.carrier) : (e (γ t)).val = x t := by
    change (e (e.symm (y t))).val = x t
    rw [e.right_inv (htarget t ht), hyval t ht]
  have hxd (t : ℝ) (ht : t ∈ I.carrier) : HasDerivAt x (F (x t)) t := by
    have hd := hx.1.2.2 t ht
    change HasDerivAt x ((ambientODE U hU F hF.continuousOn).eval (x t)) t at hd
    rwa [ambientODE_eval (hU := hU) (F := F) (hc := hF.continuousOn) (hx.1.2.1 t ht)] at hd
  have hxs := IntegralCurves.smooth_of_autonomous I.isOpen hF hx.1.1.continuousOn
    hx.1.2.1 hxd
  refine ⟨γ, ?_, integral_of_chart X I.isOpen e he
    (e.symm.continuousOn.comp hyc htarget) hsource (hxs.congr hcoords) ?_,
    fun t ht => ⟨hsource ht, hcoords t ht⟩⟩
  · change e.symm (y 0) = p
    have hy0 : y 0 = e p := Subtype.ext ((hyval 0 hx.2.1).trans hx.2.2)
    rw [hy0, e.left_inv hp]
  · intro t ht
    have hev : (fun s => (e (γ s)).val) =ᶠ[𝓝 t] x :=
      mem_of_superset (I.isOpen.mem_nhds ht) (fun s hs => hcoords s hs)
    have hv := (hcoeff (y t) (by rw [hyval t ht]; exact hx.1.2.1 t ht)).2
    rw [hyval t ht, TangentBundle.chartFiber_eq S B e he _ (hsource ht)] at hv
    exact hv ▸ (hxd t ht).congr_of_eventuallyEq hev

/-- Tangency suffices for an actual two-sided local integral curve. The open
ambient ODE stays in the half-space by regular-level invariance and no crossing. -/
theorem local_solution (hX : IsTangentToBoundary X) (p : M) :
    ∃ (I : D13Unified.OpenTimeInterval) (γ : ℝ → M),
      0 ∈ I.carrier ∧ γ 0 = p ∧ IsIntegralCurveOn X I.carrier γ := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, F, hU, hpU, hF, hcoeff⟩ := coefficient_extension X e he p hp
  let A := ambientODE U hU F hF.continuousOn
  have hA : ContDiffOn ℝ 1 A.eval A.domain :=
    (hF.of_le (by simp)).congr (fun z hz => ambientODE_eval hz)
  obtain ⟨I, x, hx, _⟩ :=
    D13Unified.Ch03.LocalExistenceUniqueness.local_existence_uniqueness
      A.toODE (A.locallyLipschitzInState_of_contDiffOn hA) 0 (e p).val hpU
  have hx' : D13Unified.IsClassicalAutonomousIVPOn A I x 0 (e p).val := hx
  have hmodel : ∀ t ∈ I.carrier, x t ∈ modelSet n a := by
    cases a with
    | euclidean => exact fun _ _ => mem_univ _
    | halfSpace =>
      cases n with
      | zero => exact fun _ _ => mem_univ _
      | succ k =>
        have htan : ∀ z ∈ A.domain, z (Fin.last k) = 0 → A.eval z (Fin.last k) = 0 := by
          intro z hz hz0
          change (ambientODE U hU F hF.continuousOn).eval z (Fin.last k) = 0
          rw [ambientODE_eval (hU := hU) (F := F) (hc := hF.continuousOn) hz]
          exact extension_normal_zero X hX e he hcoeff z hz hz0
        exact halfspace_on_solution A hA htan I x hx'.1 0 hx'.2.1
          (by rw [hx'.2.2]; exact (e p).property)
  obtain ⟨γ, hγ0, hγ, _⟩ := curve_of_ambient_solution X p e he hp hU hF hcoeff I x hx' hmodel
  exact ⟨I, γ, hx'.2.1, hγ0, hγ⟩

/-- Union of all solutions through p. Local uniqueness makes the selected values
agree, and the common zero time makes the union an interval. -/
theorem maximal_through_exists (hX : IsTangentToBoundary X) (p : M) :
    ∃ (I : D13Unified.OpenTimeInterval) (γ : ℝ → M), IsMaximalThrough X p I γ := by
  classical
  let Solutions := {z : D13Unified.OpenTimeInterval × (ℝ → M) //
    0 ∈ z.1.carrier ∧ z.2 0 = p ∧ IsIntegralCurveOn X z.1.carrier z.2}
  obtain ⟨I₀, γ₀, hI₀, hγ₀, hsol₀⟩ := local_solution X hX p
  let seed : Solutions := ⟨(I₀, γ₀), hI₀, hγ₀, hsol₀⟩
  let D : Set ℝ := ⋃ z : Solutions, z.val.1.carrier
  have hzero : 0 ∈ D := mem_iUnion.mpr ⟨seed, hI₀⟩
  have hopen : IsOpen D := isOpen_iUnion (fun z : Solutions => z.val.1.isOpen)
  have hinterval : OrdConnected D := by
    constructor
    intro l hl r hr t ht
    obtain ⟨leftSol, hleft⟩ := mem_iUnion.mp hl
    obtain ⟨rightSol, hright⟩ := mem_iUnion.mp hr
    by_cases hsign : t ≤ 0
    · exact mem_iUnion.mpr ⟨leftSol,
        leftSol.val.1.ordConnected.out hleft leftSol.property.1 ⟨ht.1, hsign⟩⟩
    · exact mem_iUnion.mpr ⟨rightSol,
        rightSol.val.1.ordConnected.out rightSol.property.1 hright
          ⟨le_of_not_ge hsign, ht.2⟩⟩
  let I : D13Unified.OpenTimeInterval := ⟨⟨D, ⟨0, hzero⟩, hinterval⟩, hopen⟩
  let γ : ℝ → M := fun t =>
    if h : ∃ z : Solutions, t ∈ z.val.1.carrier then
      (Classical.choose h).val.2 t else p
  have hagree (z : Solutions) : EqOn γ z.val.2 z.val.1.carrier := by
    intro t ht
    have hex : ∃ w : Solutions, t ∈ w.val.1.carrier := ⟨z, ht⟩
    dsimp only [γ]
    rw [dite_eq_left hex]
    exact overlap_unique X (Classical.choose hex).val.1 z.val.1
      (Classical.choose hex).val.2 z.val.2
      (Classical.choose hex).property.2.2 z.property.2.2 0
      ⟨(Classical.choose hex).property.1, z.property.1⟩
      ((Classical.choose hex).property.2.1.trans z.property.2.1.symm)
      ⟨Classical.choose_spec hex, ht⟩
  have hlocal (z : Solutions) : IsIntegralCurveOn X z.val.1.carrier γ :=
    integral_congr z.val.1.isOpen z.property.2.2 (hagree z)
  have hsol : IsIntegralCurveOn X D γ := by
    constructor
    · intro t ht
      obtain ⟨z, hz⟩ := mem_iUnion.mp ht
      exact ((hlocal z).1.continuousAt (z.val.1.isOpen.mem_nhds hz)).continuousWithinAt
    · intro t ht e he hpt
      obtain ⟨z, hz⟩ := mem_iUnion.mp ht
      exact (hlocal z).2 t hz e he hpt
  refine ⟨I, γ, hzero, (hagree seed hI₀).trans hγ₀, hsol, ?_⟩
  intro J η hJ hη hηsol
  let z : Solutions := ⟨(J, η), hJ, hη, hηsol⟩
  exact ⟨fun t ht => mem_iUnion.mpr ⟨z, ht⟩, hagree z⟩

end Existence

section Preservation
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S} (X : SmoothField B)

/-- A curve meeting the boundary stays on it near that time. The extension's
constraint theorem is used on a genuine open coordinate state domain. -/
theorem boundary_local_invariance (hX : IsTangentToBoundary X)
    (I : D13Unified.OpenTimeInterval) (γ : ℝ → M)
    (hγ : IsIntegralCurveOn X I.carrier γ) (s : ℝ) (hs : s ∈ I.carrier)
    (hb : γ s ∈ intrinsicBoundary S) :
    ∀ᶠ t in 𝓝 s, γ t ∈ intrinsicBoundary S := by
  cases a with
  | euclidean => simpa only [intrinsicBoundary_euclidean S, mem_empty_iff_false] using hb
  | halfSpace =>
    cases n with
    | zero => simpa only [intrinsicBoundary_zero S, mem_empty_iff_false] using hb
    | succ k =>
      obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (γ s)
      obtain ⟨U, F, hU, hpU, hF, hcoeff⟩ := coefficient_extension X e he (γ s) hp
      let V := e.source ∩ (fun q => (e q).val) ⁻¹' U
      have hV : IsOpen V :=
        (continuous_subtype_val.comp_continuousOn e.continuousOn).isOpen_inter_preimage
          e.open_source hU
      have hnear : ∀ᶠ t in 𝓝 s, t ∈ I.carrier ∧ γ t ∈ V :=
        Filter.Eventually.and (I.isOpen.mem_nhds hs)
          ((hγ.1.continuousAt (I.isOpen.mem_nhds hs)).eventually (hV.mem_nhds ⟨hp, hpU⟩))
      obtain ⟨l, r, hls, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
      let K := D13Unified.OpenTimeInterval.bounded l r (hls.1.trans hls.2)
      let A := ambientODE U hU F hF.continuousOn
      have hA : ContDiffOn ℝ 1 A.eval A.domain :=
        (hF.of_le (by simp)).congr (fun z hz => ambientODE_eval hz)
      have htan : ∀ z ∈ A.domain, z (Fin.last k) = 0 → A.eval z (Fin.last k) = 0 := by
        intro z hz hz0
        change (ambientODE U hU F hF.continuousOn).eval z (Fin.last k) = 0
        rw [ambientODE_eval (hU := hU) (F := F) (hc := hF.continuousOn) hz]
        exact extension_normal_zero X hX e he hcoeff z hz hz0
      have hclass := chart_classical_solution X hγ e he hU hF hcoeff K
        (fun t ht => (hsub ht).1) (fun t ht => (hsub ht).2)
      have hsol : D13Unified.IsClassicalAutonomousSolutionOn A K
          (fun t => (e (γ t)).val) := hclass
      have hs0 : (e (γ s)).val (Fin.last k) = 0 :=
        (intrinsicBoundary_iff_chart S e he (γ s) hp).mp hb
      filter_upwards [isOpen_Ioo.mem_nhds hls] with t ht
      apply (intrinsicBoundary_iff_chart S e he (γ t) (hsub ht).2.1).mpr
      exact (normal_zero_iff A hA htan K (fun t => (e (γ t)).val) hsol s hls t ht).mpr hs0

/-- Closedness of the intrinsic boundary and local invariance propagate it over
the whole connected solution interval, starting at any meeting time. -/
theorem boundary_on_curve (hX : IsTangentToBoundary X)
    (I : D13Unified.OpenTimeInterval) (γ : ℝ → M)
    (hγ : IsIntegralCurveOn X I.carrier γ) (s : ℝ) (hs : s ∈ I.carrier)
    (hb : γ s ∈ intrinsicBoundary S) :
    ∀ t ∈ I.carrier, γ t ∈ intrinsicBoundary S := by
  let T : Set I.carrier := {t | γ t ∈ intrinsicBoundary S}
  have hc : IsClosed T := (isClosed_intrinsicBoundary S).preimage hγ.1.domRestrict
  have ho : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact (continuous_subtype_val.tendsto t).eventually
      (boundary_local_invariance X hX I γ hγ t t.property ht)
  letI : PreconnectedSpace I.carrier :=
    isPreconnected_iff_preconnectedSpace.mp I.ordConnected.isPreconnected
  have hT : T = univ := IsClopen.eq_univ ⟨hc, ho⟩ ⟨⟨s, hs⟩, hb⟩
  intro t ht
  exact (show (⟨t, ht⟩ : I.carrier) ∈ T from hT ▸ mem_univ _)

theorem boundary_iff_on_curve (hX : IsTangentToBoundary X)
    (I : D13Unified.OpenTimeInterval) (γ : ℝ → M)
    (hγ : IsIntegralCurveOn X I.carrier γ) (s : ℝ) (hs : s ∈ I.carrier)
    (t : ℝ) (ht : t ∈ I.carrier) :
    γ t ∈ intrinsicBoundary S ↔ γ s ∈ intrinsicBoundary S :=
  ⟨fun hb => boundary_on_curve X hX I γ hγ t ht hb s hs,
    fun hb => boundary_on_curve X hX I γ hγ s hs hb t ht⟩

end Preservation

/-- The coordinate tangency predicate is exactly membership in the tangent
image of the natural boundary inclusion, for every valid inclusion differential. -/
theorem tangent_iff_boundary_range {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (B : TangentBundleStructure S)
    (T : SmoothManifold n .euclidean (intrinsicBoundary S))
    (hT : BoundaryConeData.IsBoundaryStructure S T)
    (L : ∀ p : intrinsicBoundary S, TangentSpace T p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, DifferentialData.IsDifferential T S Subtype.val p (L p))
    (X : SmoothField B) :
    IsTangentToBoundary X ↔ ∀ p : intrinsicBoundary S, X.val p.val ∈ LinearMap.range (L p) := by
  constructor
  · intro hX p
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p.val
    exact (boundary_inclusion_image S T hT p e he hp (L p) (hL p)
      (B.fiberCoordinates.equiv e he p.val hp) (B.fiberCoordinates.isCoordinates e he p.val hp)).2
      (X.val p.val) |>.mpr (hX p.val p.property e he hp)
  · intro hX p hpb e he hp
    let q : intrinsicBoundary S := ⟨p, hpb⟩
    exact (boundary_inclusion_image S T hT q e he hp (L q) (hL q)
      (B.fiberCoordinates.equiv e he p hp) (B.fiberCoordinates.isCoordinates e he p hp)).2
      (X.val p) |>.mp (hX q)

section Laws
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S} {X : SmoothField B}

/-- Applying universal maximality first after time s, and then after time -s,
gives both inclusions of the exact lifespan, without any endpoint assumptions. -/
theorem lifespan_flow_law_proof (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (s : ℝ) (hs : s ∈ (F.interval p).carrier) :
    (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t : ℝ, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t) := by
  let K := translatedInterval (F.interval p) s hs
  have hK0 : 0 ∈ K.carrier := by simpa [K, translatedInterval] using hs
  have hKs : IsIntegralCurveOn X K.carrier (fun t => F.curve p (s + t)) :=
    integral_translate (hF p).2.2.1 s
  have hq := (hF (F.curve p s)).2.2.2 K (fun t => F.curve p (s + t))
    hK0 (by simp) hKs
  have hKneg : -s ∈ K.carrier := by
    change s + -s ∈ (F.interval p).carrier
    simpa using (hF p).1
  have hneg := hq.1 hKneg
  have hback : F.curve (F.curve p s) (-s) = p := by
    simpa only [add_neg_cancel, (hF p).2.1] using hq.2 hKneg
  let L := translatedInterval (F.interval (F.curve p s)) (-s) hneg
  have hL0 : 0 ∈ L.carrier := by simpa [L, translatedInterval] using hneg
  have hLs : IsIntegralCurveOn X L.carrier
      (fun t => F.curve (F.curve p s) (-s + t)) :=
    integral_translate (hF (F.curve p s)).2.2.1 (-s)
  have hp := (hF p).2.2.2 L (fun t => F.curve (F.curve p s) (-s + t))
    hL0 (by simpa only [add_zero] using hback) hLs
  refine ⟨Subset.antisymm ?_ hq.1, fun t ht => hq.2 ht⟩
  intro t ht
  have hLt : s + t ∈ L.carrier := by
    change -s + (s + t) ∈ (F.interval (F.curve p s)).carrier
    simpa only [neg_add_cancel_left] using ht
  exact hp.1 hLt

end Laws

section JointRegularity
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S} {X : SmoothField B}

/-- A chart together with a genuine ambient extension of the given field.
The domain is Euclidean-open; the coefficient identity is required only on the model. -/
structure FlowChart (X : SmoothField B) where
  chart : ModelChart n a M
  chart_mem : chart ∈ S.smoothStructure.val
  domain : Set (Euclidean n)
  open_domain : IsOpen domain
  field : Euclidean n → Euclidean n
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) field domain
  coefficients : ∀ z : ModelSpace n a, z.val ∈ domain → z ∈ chart.target ∧
    field z.val = TangentBundle.chartFiber B chart chart_mem ⟨chart.symm z, X.val (chart.symm z)⟩

namespace FlowChart

theorem exists_at (X : SmoothField B) (p : M) :
    ∃ C : FlowChart X, p ∈ C.chart.source ∧ (C.chart p).val ∈ C.domain := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, f, hU, hpU, hf, hcoeff⟩ := coefficient_extension X e he p hp
  exact ⟨⟨e, he, U, hU, f, hf, hcoeff⟩, hp, hpU⟩

def ode (C : FlowChart X) : D13Unified.AutonomousODE (Euclidean n) :=
  ambientODE C.domain C.open_domain C.field C.smooth.continuousOn

theorem smooth_eval (C : FlowChart X) :
    ContDiffOn ℝ (⊤ : ℕ∞) C.ode.eval C.ode.domain :=
  C.smooth.congr (fun _ hz => ambientODE_eval hz)

theorem regular (C : FlowChart X) :
    IsOpen (D13Unified.Ch06.StateDerivative.flowDomain C.ode) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : ℝ × Euclidean n => D13Unified.Ch06.StateDerivative.flow C.ode v.1 v.2)
      (D13Unified.Ch06.StateDerivative.flowDomain C.ode) := by
  have hC1 : ContDiffOn ℝ 1 C.ode.eval C.ode.domain := C.smooth_eval.of_le (by simp)
  refine ⟨D13Unified.Ch06.C1Dependence.isOpen_flowDomain _ hC1, ?_⟩
  rw [contDiffOn_infty]
  intro k
  by_cases hk : k = 0
  · subst k
    exact (D13Unified.Ch06.CkDependence.autonomous_joint_ck 1 le_rfl _ hC1).of_le (by simp)
  · exact D13Unified.Ch06.CkDependence.autonomous_joint_ck k
      (Nat.one_le_iff_ne_zero.mpr hk) _ (C.smooth_eval.of_le (by simp))

/-- Every canonical ambient trajectory starting in the model stays there.
Tangency supplies hyperplane invariance in positive half-space dimension. -/
theorem solution_model (C : FlowChart X) (hX : IsTangentToBoundary X)
    {y : Euclidean n} (hy : y ∈ C.domain) (hym : y ∈ modelSet n a) :
    ∀ t ∈ (D13Unified.Ch06.StateDerivative.flowInterval C.ode y).carrier,
      D13Unified.Ch06.StateDerivative.flow C.ode t y ∈ modelSet n a := by
  have hC1 : ContDiffOn ℝ 1 C.ode.eval C.ode.domain := C.smooth_eval.of_le (by simp)
  have hx := D13Unified.Ch06.StateDerivative.flow_ivp C.ode hC1 hy
  cases a with
  | euclidean => exact fun _ _ => mem_univ _
  | halfSpace =>
    cases n with
    | zero => exact fun _ _ => mem_univ _
    | succ k =>
      have htan : ∀ z ∈ C.ode.domain, z (Fin.last k) = 0 → C.ode.eval z (Fin.last k) = 0 := by
        intro z hz hz0
        rw [show C.ode.eval z = C.field z from ambientODE_eval hz]
        exact extension_normal_zero X hX C.chart C.chart_mem C.coefficients z hz hz0
      exact halfspace_on_solution C.ode hC1 htan _ _ hx.1 0 hx.2.1
        (by
          have hzero : D13Unified.Ch06.StateDerivative.flow C.ode 0 y = y := hx.2.2
          rw [hzero]; exact hym)

/-- Universal maximality identifies the ambient trajectory with the manifold
trajectory on its full ambient interval, with explicit output coordinates. -/
theorem agrees (C : FlowChart X) (hX : IsTangentToBoundary X)
    (F : CurveFamily M) (hF : IsMaximalFamily X F) (z : ℝ × M)
    (hp : z.2 ∈ C.chart.source)
    (hz : (z.1, (C.chart z.2).val) ∈ D13Unified.Ch06.StateDerivative.flowDomain C.ode) :
    z ∈ flowDomain F ∧ flow F z ∈ C.chart.source ∧
      (C.chart (flow F z)).val = D13Unified.Ch06.StateDerivative.flow C.ode z.1 (C.chart z.2).val := by
  have hC1 : ContDiffOn ℝ 1 C.ode.eval C.ode.domain := C.smooth_eval.of_le (by simp)
  have hx := D13Unified.Ch06.StateDerivative.flow_ivp C.ode hC1 hz.1
  obtain ⟨γ, hγ0, hγ, hcoord⟩ := curve_of_ambient_solution X z.2 C.chart C.chart_mem hp
    C.open_domain C.smooth C.coefficients _ _ hx (C.solution_model hX hz.1 (C.chart z.2).property)
  have hmax := (hF z.2).2.2.2 _ γ hx.2.1 hγ0 hγ
  have heq : flow F z = γ z.1 := hmax.2 hz.2
  exact ⟨hmax.1 hz.2, heq ▸ (hcoord z.1 hz.2).1, heq ▸ (hcoord z.1 hz.2).2⟩

end FlowChart

/-- Recover continuity from one output chart, whose source contains all nearby
values. This uses the actual subtype topology of the relative chart model. -/
theorem continuousAt_of_output_coordinates {Z : Type*} [TopologicalSpace Z]
    {f : Z → M} {z : Z} (e : ModelChart n a M)
    (hsource : ∀ᶠ w in 𝓝 z, f w ∈ e.source)
    (hc : ContinuousAt (fun w => (e (f w)).val) z) : ContinuousAt f z := by
  have hmodel : ContinuousAt (fun w => e (f w)) z := tendsto_subtype_rng.mpr hc
  have hlift := (e.continuousAt_symm (e.map_source hsource.self_of_nhds)).comp
    (f := fun w => e (f w)) hmodel
  exact hlift.congr (hsource.mono (fun w hw => e.left_inv hw))

/-- A regular pair has an actual domain neighborhood and joint ambient smoothness. -/
def FlowRegularAt (S : SmoothManifold n a M) (F : CurveFamily M) (z : ℝ × M) : Prop :=
  flowDomain F ∈ 𝓝 z ∧ FlowSmoothAt S F z

/-- The ambient chart flow gives a uniform neighborhood of each zero-time pair,
including half-space states. All other output charts follow by transition extensions. -/
theorem flowRegularAt_zero (hX : IsTangentToBoundary X)
    (F : CurveFamily M) (hF : IsMaximalFamily X F) (p : M) :
    FlowRegularAt S F (0, p) := by
  obtain ⟨C, hp, hpU⟩ := FlowChart.exists_at X p
  let A : ℝ × M → ℝ × Euclidean n := fun w => (w.1, (C.chart w.2).val)
  let Ψ : ℝ × Euclidean n → Euclidean n :=
    fun v => D13Unified.Ch06.StateDerivative.flow C.ode v.1 v.2
  have hC1 : ContDiffOn ℝ 1 C.ode.eval C.ode.domain := C.smooth_eval.of_le (by simp)
  have hx := D13Unified.Ch06.StateDerivative.flow_ivp C.ode hC1 hpU
  have hMem : A (0, p) ∈ D13Unified.Ch06.StateDerivative.flowDomain C.ode := ⟨hpU, hx.2.1⟩
  have hA : ContinuousAt A (0, p) := continuousAt_fst.prodMk
    (continuous_subtype_val.continuousAt.comp ((C.chart.continuousAt hp).comp continuousAt_snd))
  have hNear : ∀ᶠ w in 𝓝 (0, p), w ∈ flowDomain F ∧ flow F w ∈ C.chart.source ∧
      (C.chart (flow F w)).val = Ψ (A w) := by
    filter_upwards [hA.preimage_mem_nhds (C.regular.1.mem_nhds hMem),
      (C.chart.open_source.preimage continuous_snd).mem_nhds hp] with w hw hwp
    exact C.agrees hX F hF w hwp hw
  have hCoord : (fun w => (C.chart (flow F w)).val) =ᶠ[𝓝 (0, p)] Ψ ∘ A :=
    hNear.mono (fun _ h => h.2.2)
  have hc : ContinuousAt (flow F) (0, p) := continuousAt_of_output_coordinates C.chart
    (hNear.mono (fun _ h => h.2.1))
    (((C.regular.2.continuousOn.continuousAt (C.regular.1.mem_nhds hMem)).comp hA).congr hCoord.symm)
  refine ⟨hNear.mono (fun _ h => h.1), hc, ?_⟩
  intro e he d hd hpe hpd
  have hzero : flow F (0, p) = p := (hF p).2.1
  rw [hzero] at hpd
  obtain ⟨V, hV, hpV, K, hK, hKrep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he C.chart C.chart_mem) hpe hp
  obtain ⟨T, hT, hpT, L, hL, hLrep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 C.chart C.chart_mem d hd) hp hpd
  let H : ℝ × Euclidean n → ℝ × Euclidean n := fun v => (v.1, K v.2)
  let W₀ := (Prod.snd ⁻¹' V) ∩ H ⁻¹' D13Unified.Ch06.StateDerivative.flowDomain C.ode
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H (Prod.snd ⁻¹' V) :=
    contDiffOn_fst.prodMk (hK.comp contDiffOn_snd (fun _ h => h))
  have hW₀ : IsOpen W₀ := hH.continuousOn.isOpen_inter_preimage
    (hV.preimage continuous_snd) C.regular.1
  have hΨH : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ H) W₀ :=
    C.regular.2.comp (hH.mono inter_subset_left) (fun _ h => h.2)
  let W := W₀ ∩ (Ψ ∘ H) ⁻¹' T
  have hW : IsOpen W := hΨH.continuousOn.isOpen_inter_preimage hW₀ hT
  have hHv : H (0, (e p).val) = A (0, p) := Prod.ext rfl hKrep.eq_of_nhds
  have hcenter : (0, (e p).val) ∈ W := by
    refine ⟨⟨hpV, ?_⟩, ?_⟩
    · change H (0, (e p).val) ∈ D13Unified.Ch06.StateDerivative.flowDomain C.ode
      rw [hHv]; exact hMem
    · change Ψ (H (0, (e p).val)) ∈ T
      rw [hHv]
      change D13Unified.Ch06.StateDerivative.flow C.ode 0 (C.chart p).val ∈ T
      have hzero : D13Unified.Ch06.StateDerivative.flow C.ode 0 (C.chart p).val = (C.chart p).val := hx.2.2
      rw [hzero]; exact hpT
  refine ⟨W, hW, hcenter, L ∘ (Ψ ∘ H),
    hL.comp (hΨH.mono inter_subset_left) (fun _ h => h.2), ?_⟩
  have hKrep' := hKrep.comp_tendsto (continuousAt_snd : ContinuousAt (Prod.snd : ℝ × M → M) (0, p))
  have hLrep' := hLrep.comp_tendsto (show Tendsto (flow F) (𝓝 (0, p)) (𝓝 p) by
    simpa only [ContinuousAt, hzero] using hc)
  filter_upwards [hKrep', hCoord, hLrep'] with w hwK hwCoord hwL
  change L (Ψ (H (w.1, (e w.2).val))) = (d (flow F w)).val
  have hHw : H (w.1, (e w.2).val) = A w := Prod.ext rfl hwK
  change (C.chart (flow F w)).val = Ψ (A w) at hwCoord
  rw [hHw, ← hwCoord]
  exact hwL

/-- Restart a regular manifold flow using a canonical ambient chart flow.
The exact lifespan law justifies the entire neighborhood, not just its center. -/
theorem flowRegularAt_restart (hX : IsTangentToBoundary X)
    (F : CurveFamily M) (hF : IsMaximalFamily X F) (p : M) (s t : ℝ)
    (hs : FlowRegularAt S F (s, p)) (C : FlowChart X)
    (hp : F.curve p s ∈ C.chart.source)
    (ht : (t - s, (C.chart (F.curve p s)).val) ∈
      D13Unified.Ch06.StateDerivative.flowDomain C.ode) :
    FlowRegularAt S F (t, p) := by
  let Q : ℝ × M → M := fun w => F.curve w.2 s
  let A : ℝ × M → ℝ × Euclidean n := fun w => (w.1 - s, (C.chart (Q w)).val)
  let Ψ : ℝ × Euclidean n → Euclidean n :=
    fun v => D13Unified.Ch06.StateDerivative.flow C.ode v.1 v.2
  let D := D13Unified.Ch06.StateDerivative.flowDomain C.ode
  have hi : ContinuousAt (fun w : ℝ × M => (s, w.2)) (t, p) :=
    continuousAt_const.prodMk continuousAt_snd
  have hQ : ContinuousAt Q (t, p) :=
    ContinuousAt.comp (f := fun w : ℝ × M => (s, w.2)) (x := (t, p)) hs.2.1 hi
  have hA : ContinuousAt A (t, p) :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      (continuous_subtype_val.continuousAt.comp ((C.chart.continuousAt hp).comp (f := Q) hQ))
  have hNear : ∀ᶠ w in 𝓝 (t, p), w ∈ flowDomain F ∧ flow F w ∈ C.chart.source ∧
      (C.chart (flow F w)).val = Ψ (A w) := by
    filter_upwards [hi.preimage_mem_nhds hs.1,
      hA.preimage_mem_nhds (C.regular.1.mem_nhds ht),
      hQ.preimage_mem_nhds (C.chart.open_source.mem_nhds hp)] with w hw hwA hwQ
    have hLaw := lifespan_flow_law_proof F hF w.2 s hw
    have hChart := C.agrees hX F hF (w.1 - s, Q w) hwQ hwA
    have hsum : s + (w.1 - s) = w.1 := by ring
    have hDom : w ∈ flowDomain F := by
      have hh := hChart.1
      change w.1 - s ∈ (F.interval (F.curve w.2 s)).carrier at hh
      rw [hLaw.1] at hh
      simpa only [mem_ofPred_eq, flowDomain, hsum] using hh
    have hVal := hLaw.2 (w.1 - s) (by simpa only [flowDomain, mem_ofPred_eq, hsum] using hDom)
    have heq : flow F w = flow F (w.1 - s, Q w) := by
      simpa only [flow, Q, hsum] using hVal.symm
    exact ⟨hDom, heq ▸ hChart.2.1, heq ▸ hChart.2.2⟩
  have hCoord : (fun w => (C.chart (flow F w)).val) =ᶠ[𝓝 (t, p)] Ψ ∘ A :=
    hNear.mono (fun _ h => h.2.2)
  have hc : ContinuousAt (flow F) (t, p) := continuousAt_of_output_coordinates C.chart
    (hNear.mono (fun _ h => h.2.1))
    (((C.regular.2.continuousOn.continuousAt (C.regular.1.mem_nhds ht)).comp (f := A) hA).congr hCoord.symm)
  have hpOut : flow F (t, p) ∈ C.chart.source := hNear.self_of_nhds.2.1
  refine ⟨hNear.mono (fun _ h => h.1), hc, ?_⟩
  intro e he d hd hpa hpd
  obtain ⟨V, hV, hpV, K, hK, hKrep⟩ := hs.2.2 e he C.chart C.chart_mem hpa hp
  obtain ⟨T, hT, hpT, L, hL, hLrep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 C.chart C.chart_mem d hd) hpOut hpd
  let J : ℝ × Euclidean n → ℝ × Euclidean n := fun v => (s, v.2)
  let H : ℝ × Euclidean n → ℝ × Euclidean n := fun v => (v.1 - s, K (J v))
  let W₀ := J ⁻¹' V
  have hW₀ : IsOpen W₀ := hV.preimage (continuous_const.prodMk continuous_snd)
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H W₀ :=
    (contDiff_fst.sub contDiff_const).contDiffOn.prodMk
      (hK.comp (contDiff_const.prodMk contDiff_snd).contDiffOn (fun _ h => h))
  let W₁ := W₀ ∩ H ⁻¹' D
  have hW₁ : IsOpen W₁ := hH.continuousOn.isOpen_inter_preimage hW₀ C.regular.1
  have hΨH : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ H) W₁ :=
    C.regular.2.comp (hH.mono inter_subset_left) (fun _ h => h.2)
  let W := W₁ ∩ (Ψ ∘ H) ⁻¹' T
  have hW : IsOpen W := hΨH.continuousOn.isOpen_inter_preimage hW₁ hT
  have hHval : H (t, (e p).val) = A (t, p) := Prod.ext rfl hKrep.eq_of_nhds
  have hCenter : (t, (e p).val) ∈ W := by
    refine ⟨⟨hpV, ?_⟩, ?_⟩
    · change H (t, (e p).val) ∈ D
      rw [hHval]; exact ht
    · change Ψ (H (t, (e p).val)) ∈ T
      have hval : (C.chart (flow F (t, p))).val = Ψ (A (t, p)) := hCoord.eq_of_nhds
      rw [hHval, ← hval]
      exact hpT
  refine ⟨W, hW, hCenter, L ∘ (Ψ ∘ H),
    hL.comp (hΨH.mono inter_subset_left) (fun _ h => h.2), ?_⟩
  have hKrep' := hKrep.comp_tendsto hi
  have hLrep' := hLrep.comp_tendsto hc
  filter_upwards [hKrep', hCoord, hLrep'] with w hwK hwCoord hwL
  change L (Ψ (H (w.1, (e w.2).val))) = (d (flow F w)).val
  have hHw : H (w.1, (e w.2).val) = A w := Prod.ext rfl hwK
  change (C.chart (flow F w)).val = Ψ (A w) at hwCoord
  rw [hHw, ← hwCoord]
  exact hwL

/-- Regular times form a nonempty clopen subset of the connected lifespan.
For closedness a fixed ambient patch at the limiting state restarts any nearby
regular time, using only continuity of the original single trajectory. -/
theorem flowRegularAt_of_mem (hX : IsTangentToBoundary X)
    (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (p : M) (t : ℝ) (ht : t ∈ (F.interval p).carrier) : FlowRegularAt S F (t, p) := by
  let I := (F.interval p).carrier
  let T : Set I := {r | FlowRegularAt S F (r.val, p)}
  letI : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp
    (F.interval p).ordConnected.isPreconnected
  have hStart (C : FlowChart X) {q : M} (hq : (C.chart q).val ∈ C.domain) :
      (0, (C.chart q).val) ∈ D13Unified.Ch06.StateDerivative.flowDomain C.ode :=
    ⟨hq, (D13Unified.Ch06.StateDerivative.flow_ivp C.ode
      (C.smooth_eval.of_le (by simp)) hq).2.1⟩
  have hOpen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro r hr
    obtain ⟨C, hp, hpU⟩ := FlowChart.exists_at X (F.curve p r.val)
    have hA : ContinuousAt (fun b : I => (b.val - r.val, (C.chart (F.curve p r.val)).val)) r :=
      (continuousAt_subtype_val.sub continuousAt_const).prodMk continuousAt_const
    have hNear := hA.preimage_mem_nhds
      (C.regular.1.mem_nhds (by simpa using hStart C hpU))
    filter_upwards [hNear] with b hb
    exact flowRegularAt_restart hX F hF p r.val b.val hr C hp hb
  have hClosed : IsClosed T := by
    apply isClosed_of_closure_subset
    intro r hr
    obtain ⟨C, hp, hpU⟩ := FlowChart.exists_at X (F.curve p r.val)
    have hγ : Continuous (fun b : I => F.curve p b.val) := (hF p).2.2.1.1.domRestrict
    have hE : ContinuousAt (fun b : I => (C.chart (F.curve p b.val)).val) r :=
      continuous_subtype_val.continuousAt.comp
        ((C.chart.continuousAt hp).comp (f := fun b : I => F.curve p b.val) hγ.continuousAt)
    have hA : ContinuousAt (fun b : I => (r.val - b.val, (C.chart (F.curve p b.val)).val)) r :=
      (continuousAt_const.sub continuousAt_subtype_val).prodMk hE
    have hNear := hA.preimage_mem_nhds
      (C.regular.1.mem_nhds (by simpa using hStart C hpU))
    have hSource := hγ.continuousAt.preimage_mem_nhds (C.chart.open_source.mem_nhds hp)
    obtain ⟨b, ⟨hb, hbp⟩, hbT⟩ := mem_closure_iff_nhds.mp hr _ (inter_mem hNear hSource)
    exact flowRegularAt_restart hX F hF p b.val r.val hbT C hbp hb
  have hAll : T = univ :=
    (show IsClopen T from ⟨hClosed, hOpen⟩).eq_univ
      ⟨⟨0, (hF p).1⟩, flowRegularAt_zero hX F hF p⟩
  exact (show (⟨t, ht⟩ : I) ∈ T from hAll ▸ mem_univ _)

end JointRegularity

section TimeMaps
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S} {X : SmoothField B}

/-- Restrict the time variable in an actual product-coordinate extension. -/
theorem time_map_smooth_at (F : CurveFamily M) (s : ℝ) (p : M)
    (h : FlowSmoothAt S F (s, p)) :
    ManifoldSmoothAt S.smoothStructure.val S.smoothStructure.val
      (fun q => F.curve q s) p := by
  have hi : Continuous (fun q : M => (s, q)) := continuous_const.prodMk continuous_id
  refine ⟨h.1.comp hi.continuousAt, ?_⟩
  intro e he d hd hp hfp
  obtain ⟨U, hU, hzU, G, hG, heq⟩ := h.2 e he d hd hp hfp
  let i : Euclidean n → ℝ × Euclidean n := fun x => (s, x)
  refine ⟨i ⁻¹' U, hU.preimage (continuous_const.prodMk continuous_id), hzU,
    fun x => G (i x), hG.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => hx), ?_⟩
  exact heq.comp_tendsto hi.continuousAt

/-- A smooth map with values in an open subset is smooth as a map into that
subset's actual restricted atlas. -/
theorem smoothAt_codRestrict {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    {A : Set (ModelChart n a M)} {C : Set (ModelChart m b N)}
    {f : M → N} {V : Set N} (hV : IsOpen V) (hmap : ∀ p, f p ∈ V)
    (p : M) (hf : ManifoldSmoothAt A C f p) :
    ManifoldSmoothAt A (openSubsetAtlas C V hV) (fun q => (⟨f q, hmap q⟩ : V)) p := by
  refine ⟨hf.1.codRestrict hmap, ?_⟩
  rintro e he _ ⟨hne, d, hd, rfl⟩ hp hfp
  have hfd : f p ∈ d.source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hfp
  change ChartContDiffAt (⊤ : ℕ∞) e d f p
  exact hf.2 e he d hd hp hfd

/-- Once joint openness and smoothness have been established, the exact flow
law supplies diffeomorphisms of the actual open time domains. This lemma records
the remaining dependence explicitly; it does not assert joint regularity. -/
theorem time_diffeomorph_of_smooth (F : CurveFamily M) (hF : IsMaximalFamily X F)
    (hregular : IsOpen (flowDomain F) ∧ ∀ z ∈ flowDomain F, FlowSmoothAt S F z)
    (s : ℝ) :
    ∃ (hs : IsOpen (timeDomain F s)) (hneg : IsOpen (timeDomain F (-s))),
      ∃ h : Diffeomorph
        (openSubsetAtlas S.smoothStructure.val (timeDomain F s) hs)
        (openSubsetAtlas S.smoothStructure.val (timeDomain F (-s)) hneg),
        (∀ p : timeDomain F s, (h.toEquiv p).val = F.curve p.val s) ∧
        (∀ q : timeDomain F (-s), (h.toEquiv.symm q).val = F.curve q.val (-s)) := by
  have hopen (r : ℝ) : IsOpen (timeDomain F r) :=
    hregular.1.preimage (continuous_const.prodMk continuous_id)
  have hinv (r : ℝ) (p : M) (hp : r ∈ (F.interval p).carrier) :
      -r ∈ (F.interval (F.curve p r)).carrier ∧ F.curve (F.curve p r) (-r) = p := by
    have h := lifespan_flow_law_proof F hF p r hp
    have hz : r + -r ∈ (F.interval p).carrier := by simpa using (hF p).1
    refine ⟨?_, ?_⟩
    · rw [h.1]; exact hz
    · simpa only [add_neg_cancel, (hF p).2.1] using h.2 (-r) hz
  let f : timeDomain F s → timeDomain F (-s) :=
    fun p => ⟨F.curve p.val s, (hinv s p.val p.property).1⟩
  let g : timeDomain F (-s) → timeDomain F s :=
    fun q => ⟨F.curve q.val (-s), by
      change s ∈ (F.interval (F.curve q.val (-s))).carrier
      simpa only [neg_neg] using (hinv (-s) q.val q.property).1⟩
  have hleft : Function.LeftInverse g f := by
    intro p
    exact Subtype.ext (hinv s p.val p.property).2
  have hright : Function.RightInverse g f := by
    intro q
    apply Subtype.ext
    simpa using (hinv (-s) q.val q.property).2
  have hsm (r : ℝ) :
      ManifoldSmooth (openSubsetAtlas S.smoothStructure.val (timeDomain F r) (hopen r))
        S.smoothStructure.val (fun p : timeDomain F r => F.curve p.val r) := by
    apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.val
      (fun p => F.curve p r) (timeDomain F r) (hopen r)).mp
    intro p hp
    exact time_map_smooth_at F r p (hregular.2 (r, p) hp)
  have hf : ManifoldSmooth
      (openSubsetAtlas S.smoothStructure.val (timeDomain F s) (hopen s))
      (openSubsetAtlas S.smoothStructure.val (timeDomain F (-s)) (hopen (-s))) f := by
    intro p
    exact smoothAt_codRestrict (f := fun q : timeDomain F s => F.curve q.val s)
      (hopen (-s)) (fun q => (hinv s q.val q.property).1) p (hsm s p)
  have hg : ManifoldSmooth
      (openSubsetAtlas S.smoothStructure.val (timeDomain F (-s)) (hopen (-s)))
      (openSubsetAtlas S.smoothStructure.val (timeDomain F s) (hopen s)) g := by
    intro q
    exact smoothAt_codRestrict (f := fun p : timeDomain F (-s) => F.curve p.val (-s))
      (hopen s) (fun p => by
        change s ∈ (F.interval (F.curve p.val (-s))).carrier
        simpa only [neg_neg] using (hinv (-s) p.val p.property).1) q (hsm (-s) q)
  exact ⟨hopen s, hopen (-s), ⟨⟨f, g, hleft, hright⟩, hf, hg⟩,
    fun _ => rfl, fun _ => rfl⟩

end TimeMaps

/-- Universal maximality determines the lifespan and every on-domain value. -/
theorem maximal_family_unique :
    Specs.SmoothManifolds.Ch06.BoundaryTangentFlow.maximal_uniqueType.{u} := by
  intro n a M _ S B X _ F G hF hG p
  exact maximal_unique (hF p) (hG p)

theorem lifespan_flow_law :
    Specs.SmoothManifolds.Ch06.BoundaryTangentFlow.lifespan_flow_lawType.{u} := by
  intro n a M _ S B X _ F hF p s hs
  exact lifespan_flow_law_proof F hF p s hs

theorem maximal_family_exists :
    Specs.SmoothManifolds.Ch06.BoundaryTangentFlow.maximal_family_existsType.{u} := by
  intro n a M _ S B X hX
  classical
  choose I γ h using maximal_through_exists X hX
  exact ⟨⟨I, γ⟩, h⟩

theorem preserves_boundary_interior :
    Specs.SmoothManifolds.Ch06.BoundaryTangentFlow.preserves_boundary_interiorType.{u} := by
  intro n a M _ S B X hX F hF p t ht
  have hb := boundary_iff_on_curve X hX (F.interval p) (F.curve p)
    (hF p).2.2.1 0 (hF p).1 t ht
  rw [(hF p).2.1] at hb
  refine ⟨hb, ?_⟩
  simpa only [← compl_intrinsicBoundary S, mem_compl_iff] using not_congr hb

/-- Joint regularity holds on the entire maximal domain, including boundary
states. Neighborhood membership gives relative openness in `ℝ × M`. -/
theorem domain_open_smooth :
    Specs.SmoothManifolds.Ch06.BoundaryTangentFlow.domain_open_smoothType.{u} := by
  intro n a M _ S B X hX F hF
  have hReg : ∀ z ∈ flowDomain F, FlowRegularAt S F z := by
    rintro ⟨t, p⟩ ht
    exact flowRegularAt_of_mem hX F hF p t ht
  exact ⟨isOpen_iff_mem_nhds.mpr (fun z hz => (hReg z hz).1),
    fun z hz => (hReg z hz).2⟩

/-- Each time map is a diffeomorphism of the actual open time domains,
with the negative-time map as its inverse. -/
theorem time_diffeomorph :
    Specs.SmoothManifolds.Ch06.BoundaryTangentFlow.time_diffeomorphType.{u} := by
  intro n a M _ S B X hX F hF s
  exact time_diffeomorph_of_smooth F hF (domain_open_smooth S B X hX F hF) s

end SmoothManifolds.BoundaryTangentFlow
