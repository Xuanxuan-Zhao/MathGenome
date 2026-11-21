import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.Evolution
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalFlow
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence

/-! M06.08 via smooth nonautonomous chart ODEs. Local solutions glue to a
unique maximal family. Joint regularity continues along each connected lifespan;
exact restart intervals then give the inverse smooth time maps. -/
noncomputable section
namespace SmoothManifolds.Evolution
open ModelData AtlasData MapData TangentData TangentBundleData EvolutionData Set Filter
open scoped Topology ContDiff
universe u

section Elementary
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
  {Ω : Set (ℝ × M)} {X : SmoothTimeDependentField B Ω}

omit [TopologicalSpace M] in
@[simp] theorem evolution_apply (F : EvolutionFamily Ω) (z : Ω) (t : ℝ) :
    evolution F (t, z.val) = F.curve z t := by
  simp only [evolution, dite_eq_left z.property]

omit [TopologicalSpace M] in
@[simp] theorem mem_evolutionDomain (F : EvolutionFamily Ω) (z : Ω) (t : ℝ) :
    (t, z.val) ∈ evolutionDomain F ↔ t ∈ (F.interval z).carrier := by
  constructor
  · rintro ⟨h, ht⟩
    exact ht
  · intro ht
    exact ⟨z.property, ht⟩

/-- The initial diagonal belongs to the actual domain, and the initial value is
the prescribed state. -/
theorem initial_value {F : EvolutionFamily Ω} (hF : IsMaximalFamily X F) (z : Ω) :
    (z.val.1, z.val) ∈ evolutionDomain F ∧ evolution F (z.val.1, z.val) = z.val.2 := by
  exact ⟨⟨z.property, (hF z).1⟩, (evolution_apply F z _).trans (hF z).2.1⟩

/-- A comparison in each direction proves equality of actual maximal domains. -/
theorem maximalThrough_unique {z : Ω} {I K : D13Unified.OpenTimeInterval}
    {γ η : ℝ → M} (hγ : IsMaximalThrough X z I γ)
    (hη : IsMaximalThrough X z K η) :
    I.carrier = K.carrier ∧ EqOn γ η I.carrier := by
  have hKI := hγ.2.2.2 K η hη.1 hη.2.1 hη.2.2.1
  have hIK := hη.2.2.2 I γ hγ.1 hγ.2.1 hγ.2.2.1
  exact ⟨Subset.antisymm hIK.1 hKI.1, fun t ht => (hIK.2 ht).symm⟩

/-- Graph membership is part of the differential equation, including at every
restart time. -/
theorem graph_mem {F : EvolutionFamily Ω} (hF : IsMaximalFamily X F)
    (z : Ω) {t : ℝ} (ht : t ∈ (F.interval z).carrier) : (t, F.curve z t) ∈ Ω :=
  ((hF z).2.2.1.2 t ht).choose

/-- Universal maximality through every point proves restart directly. First the
new maximal curve absorbs the old curve; then it passes through the old initial
point, so the old maximal curve absorbs it. No autonomous action law is used. -/
theorem restart_at {F : EvolutionFamily Ω} (hF : IsMaximalFamily X F)
    (z : Ω) {u : ℝ} (hu : u ∈ (F.interval z).carrier) :
    let w : Ω := ⟨(u, F.curve z u), graph_mem hF z hu⟩
    (F.interval w).carrier = (F.interval z).carrier ∧
      EqOn (F.curve w) (F.curve z) (F.interval z).carrier := by
  let w : Ω := ⟨(u, F.curve z u), graph_mem hF z hu⟩
  have hOldNew := (hF w).2.2.2 (F.interval z) (F.curve z) hu rfl (hF z).2.2.1
  have hs : z.val.1 ∈ (F.interval w).carrier := hOldNew.1 (hF z).1
  have hv : F.curve w z.val.1 = z.val.2 := (hOldNew.2 (hF z).1).trans (hF z).2.1
  have hNewOld := (hF z).2.2.2 (F.interval w) (F.curve w) hs hv (hF w).2.2.1
  exact ⟨Subset.antisymm hNewOld.1 hOldNew.1, hOldNew.2⟩

end Elementary

theorem maximal_unique : Specs.SmoothManifolds.Ch06.Evolution.maximal_uniqueType.{u} := by
  intro n M _ S B Ω X F G hF hG z
  exact maximalThrough_unique (hF z) (hG z)

theorem restart : Specs.SmoothManifolds.Ch06.Evolution.restartType.{u} := by
  intro n M _ S B Ω X F hF z u hu
  refine ⟨graph_mem hF z hu, ?_⟩
  obtain ⟨hI, hEq⟩ := restart_at hF z hu
  refine ⟨hI, ?_, fun t ht => hEq ht⟩
  ext τ
  change u + τ ∈ (F.interval _).carrier ↔ z.val.1 + ((u - z.val.1) + τ) ∈ (F.interval z).carrier
  rw [hI]
  rw [show z.val.1 + ((u - z.val.1) + τ) = u + τ by ring]

/-- The actual triple domain and the solution on it are independent of the
choice of maximal representatives. -/
theorem evolution_unique {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {Ω : Set (ℝ × M)} {X : SmoothTimeDependentField B Ω}
    {F G : EvolutionFamily Ω} (hF : IsMaximalFamily X F) (hG : IsMaximalFamily X G) :
    evolutionDomain F = evolutionDomain G ∧ EqOn (evolution F) (evolution G) (evolutionDomain F) := by
  have h := maximal_unique S B Ω X F G hF hG
  constructor
  · ext q
    constructor <;> rintro ⟨hq, ht⟩
    · exact ⟨hq, (h ⟨q.2, hq⟩).1 ▸ ht⟩
    · exact ⟨hq, (h ⟨q.2, hq⟩).1.symm ▸ ht⟩
  · rintro ⟨t, s, p⟩ ⟨hq, ht⟩
    rw [evolution_apply F ⟨(s,p),hq⟩, evolution_apply G ⟨(s,p),hq⟩]
    exact (h ⟨(s,p),hq⟩).2 ht

/-- Every fixed pair of times gives an open state domain whenever the joint
triple domain is open. -/
theorem timeDomain_isOpen {M : Type u} [TopologicalSpace M]
    {Ω : Set (ℝ × M)} (F : EvolutionFamily Ω)
    (hD : IsOpen (evolutionDomain F)) (s t : ℝ) : IsOpen (timeDomain F s t) :=
  hD.preimage (continuous_const.prodMk (continuous_const.prodMk continuous_id))

/-- Restricting joint smoothness in all three variables to the two fixed times
gives smoothness between any open restrictions of the state manifold. -/
theorem timeMap_smooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) {Ω : Set (ℝ × M)}
    (F : EvolutionFamily Ω) (s t : ℝ) {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V) (g : U → V)
    (hg : ∀ p, (g p).val = evolution F (t, s, p.val))
    (hSmooth : ∀ p ∈ U, EvolutionSmoothAt S F (t, s, p)) :
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (openSubsetAtlas S.smoothStructure.val V hV) g := by
  intro p
  have hi : ContinuousAt (fun q : U => (t, s, q.val)) p :=
    continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_subtype_val)
  have hc : ContinuousAt (fun q : U => evolution F (t, s, q.val)) p :=
    ContinuousAt.comp (f := fun q : U => (t, s, q.val)) (hSmooth p.val p.property).1 hi
  have hcg : ContinuousAt (fun q : U => (g q).val) p :=
    hc.congr (Eventually.of_forall (fun q => (hg q).symm))
  refine ⟨tendsto_subtype_rng.mpr hcg, ?_⟩
  rintro _ ⟨hne, e, he, rfl⟩ _ ⟨hne', d, hd, rfl⟩ hp hgp
  have hpe : p.val ∈ e.source := by simpa using hp
  have hpd : evolution F (t, s, p.val) ∈ d.source := by simpa [← hg p] using hgp
  obtain ⟨W, hW, hpW, G, hG, hEq⟩ := (hSmooth p.val p.property).2 e he d hd hpe hpd
  refine ⟨(fun x : Euclidean n => (t, s, x)) ⁻¹' W,
    hW.preimage (continuous_const.prodMk (continuous_const.prodMk continuous_id)), hpW,
    (fun x => G (t, s, x)), ?_, ?_⟩
  · exact hG.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn (fun _ h => h)
  · have hEq' := hEq.comp_tendsto hi
    filter_upwards [hEq'] with q hq
    change G (t, s, (e q.val).val) = (d (g q).val).val
    rw [hg q]
    exact hq

/-- Forward evolution lies in the domain of the reverse evolution, which
recovers precisely the original state. -/
theorem timeMap_inverse {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {Ω : Set (ℝ × M)} {X : SmoothTimeDependentField B Ω}
    {F : EvolutionFamily Ω} (hF : IsMaximalFamily X F)
    {s t : ℝ} {p : M} (hp : p ∈ timeDomain F s t) :
    evolution F (t, s, p) ∈ timeDomain F t s ∧
      evolution F (s, t, evolution F (t, s, p)) = p := by
  obtain ⟨hz, ht⟩ := hp
  let z : Ω := ⟨(s, p), hz⟩
  have hv : evolution F (t, s, p) = F.curve z t := evolution_apply F z t
  rw [hv]
  have hw := graph_mem hF z ht
  obtain ⟨hI, hEq⟩ := restart_at hF z ht
  have hs : s ∈ (F.interval ⟨(t, F.curve z t), hw⟩).carrier := by
    rw [hI]
    exact (hF z).1
  refine ⟨⟨hw, hs⟩, ?_⟩
  rw [evolution_apply F ⟨(t, F.curve z t), hw⟩]
  exact (hEq (hF z).1).trans (hF z).2.1

/-- This equivalence uses the actual opposite pair of times, rather than the
negative of one time as would be appropriate only for an autonomous field. -/
def timeEquiv {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {Ω : Set (ℝ × M)} {X : SmoothTimeDependentField B Ω}
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F) (s t : ℝ) :
    timeDomain F s t ≃ timeDomain F t s where
  toFun p := ⟨evolution F (t, s, p.val), (timeMap_inverse hF p.property).1⟩
  invFun p := ⟨evolution F (s, t, p.val), (timeMap_inverse hF p.property).1⟩
  left_inv p := Subtype.ext (timeMap_inverse hF p.property).2
  right_inv p := Subtype.ext (timeMap_inverse hF p.property).2

/-- Joint openness and smoothness give diffeomorphisms between the actual
opposite-time state domains. -/
theorem time_diffeomorph_of_open_smooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    {Ω : Set (ℝ × M)} (X : SmoothTimeDependentField B Ω)
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F)
    (hD : IsOpen (evolutionDomain F))
    (hSmooth : ∀ q ∈ evolutionDomain F, EvolutionSmoothAt S F q) :
    HasTimeDiffeomorphs S F := by
  intro s t
  have hU := timeDomain_isOpen F hD s t
  have hV := timeDomain_isOpen F hD t s
  let E := timeEquiv F hF s t
  refine ⟨hU, hV, ⟨E, ?_, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · exact timeMap_smooth S F s t hU hV E (fun _ => rfl)
      (fun p hp => hSmooth (t,s,p) hp)
  · exact timeMap_smooth S F t s hV hU E.symm (fun _ => rfl)
      (fun p hp => hSmooth (s,t,p) hp)

/-- Assembly of the complete source conclusion from maximal existence and
joint regularity, proved below. -/
theorem evolution_exists_conditional
    (hExists : Specs.SmoothManifolds.Ch06.Evolution.maximal_family_existsType.{u})
    (hJoint : Specs.SmoothManifolds.Ch06.Evolution.domain_open_smoothType.{u}) :
    Specs.SmoothManifolds.Ch06.Evolution.evolution_existsType.{u} := by
  intro n M _ S B J hJ hiJ Ω hΩ hΩJ X
  obtain ⟨F, hF⟩ := hExists S B J hJ hiJ Ω hΩ hΩJ X
  obtain ⟨hD, hdiag, hSmooth⟩ := hJoint S B Ω hΩ X F hF
  refine ⟨F, hF, hD, hdiag, hSmooth, restart S B Ω X F hF,
    time_diffeomorph_of_open_smooth S B X F hF hD hSmooth, ?_⟩
  intro G hG
  have h := evolution_unique hF hG
  exact ⟨h.1.symm, fun q hq => (h.2 hq).symm⟩

section Coordinates
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
  {Ω : Set (ℝ × M)}

/-- The original open time–state domain restricted to a chart. -/
def chartDomain (Ω : Set (ℝ × M)) (e : ModelChart n .euclidean M) : Set (ℝ × Euclidean n) :=
  {q | MaximalFlow.euclideanModelPoint q.2 ∈ e.target ∧
    (q.1, e.symm (MaximalFlow.euclideanModelPoint q.2)) ∈ Ω}

theorem chartDomain_isOpen (hΩ : IsOpen Ω) (e : ModelChart n .euclidean M) :
    IsOpen (chartDomain Ω e) := by
  let U := (fun q : ℝ × Euclidean n => MaximalFlow.euclideanModelPoint q.2) ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage
    ((MaximalFlow.continuous_euclideanModelPoint n).comp continuous_snd)
  have hi : ContinuousOn (fun q : ℝ × Euclidean n =>
      (q.1, e.symm (MaximalFlow.euclideanModelPoint q.2))) U :=
    continuousOn_fst.prodMk (e.symm.continuousOn.comp
      ((MaximalFlow.continuous_euclideanModelPoint n).comp continuous_snd).continuousOn
      (fun _ h => h))
  exact hi.isOpen_inter_preimage hU hΩ

/-- On the true chart domain the field is transported by the intrinsic tangent
coordinate equivalence. The value zero outside it has no regularity meaning. -/
def chartField (X : SmoothTimeDependentField B Ω) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (q : ℝ × Euclidean n) : Euclidean n := by
  classical
  exact if h : q ∈ chartDomain Ω e then
    B.fiberCoordinates.equiv e he _ (e.map_target h.1) (X.val ⟨_,h.2⟩) else 0

/-- Pulling the local ambient extensions back along the inverse chart proves
joint C-infinity regularity on the actual time–state coordinate domain. -/
theorem chartField_contDiffOn (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartField X e he) (chartDomain Ω e) := by
  intro q hq
  let z : Ω := ⟨(q.1, e.symm (MaximalFlow.euclideanModelPoint q.2)), hq.2⟩
  have hp : z.val.2 ∈ e.source := e.map_target hq.1
  obtain ⟨U, hU, hzU, G, hG, hEq⟩ := X.smooth z e he hp
  have hcoords : (z.val.1, (e z.val.2).val) = q := by
    simp only [z, e.right_inv hq.1]
    rfl
  have hqU : q ∈ U := hcoords ▸ hzU
  let D := chartDomain Ω e
  have hD : IsOpen D := chartDomain_isOpen hΩ e
  let lift : D → Ω := fun r => ⟨(r.val.1, e.symm (MaximalFlow.euclideanModelPoint r.val.2)),r.property.2⟩
  have hLift : Continuous lift := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (e.symm.continuousOn.comp_continuous
        ((MaximalFlow.continuous_euclideanModelPoint n).comp
          (continuous_snd.comp continuous_subtype_val)) (fun r => r.property.1))
  have hEq' := hEq.comp_tendsto (hLift.tendsto ⟨q,hq⟩)
  have hNear : ∀ᶠ r in 𝓝 q, r ∈ D ∧ chartField X e he r = G r := by
    have hWithin : ∀ᶠ r in 𝓝 (⟨q,hq⟩ : D), chartField X e he r.val = G r.val := by
      filter_upwards [hEq'] with r hr
      change G (r.val.1, (e (e.symm (MaximalFlow.euclideanModelPoint r.val.2))).val) =
        fieldCoefficients B X.val e he (lift r) at hr
      rw [e.right_inv r.property.1] at hr
      unfold fieldCoefficients at hr
      dsimp only [lift] at hr
      rw [dite_eq_left (e.map_target r.property.1)] at hr
      unfold chartField
      rw [dite_eq_left r.property]
      exact hr.symm
    have hMap : ∀ᶠ r in map (Subtype.val : D → ℝ × Euclidean n) (𝓝 ⟨q,hq⟩),
        chartField X e he r = G r := hWithin
    rw [hD.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨q,hq⟩] at hMap
    filter_upwards [hD.mem_nhds hq, hMap] with r hr hval
    exact ⟨hr,hval⟩
  have hEqG : chartField X e he =ᶠ[𝓝 q] G := hNear.mono (fun _ h => h.2)
  exact ((hG.contDiffAt (hU.mem_nhds hqU)).congr_of_eventuallyEq hEqG).contDiffWithinAt

/-- A genuine D13 nonautonomous ODE, whose domain includes the time restriction. -/
def chartODE (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    D13Unified.ODE (Euclidean n) where
  domain := chartDomain Ω e
  isOpen_domain := chartDomain_isOpen hΩ e
  field := fun q => chartField X e he q.val
  continuous_field := (chartField_contDiffOn hΩ X e he).continuousOn.domRestrict

@[simp] theorem chartODE_eval (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    {q : ℝ × Euclidean n} (hq : q ∈ chartDomain Ω e) :
    (chartODE hΩ X e he).eval q.1 q.2 = chartField X e he q := by
  simp [D13Unified.ODE.eval, chartODE, hq]

theorem chartODE_locallyLipschitz (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    (chartODE hΩ X e he).LocallyLipschitzInState := by
  apply D13Unified.ODE.locallyLipschitzInState_of_contDiffOn
  exact ((chartField_contDiffOn hΩ X e he).of_le (by simp)).congr
    (fun q hq => chartODE_eval hΩ X e he hq)

/-- Bootstrapping the nonautonomous equation preserves the true time–state
domain. No assumption that a state path stays in a time-independent domain. -/
theorem smooth_of_nonautonomous {I : Set ℝ} (hI : IsOpen I)
    {U : Set (ℝ × Euclidean n)} {G : ℝ × Euclidean n → Euclidean n}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) {x : ℝ → Euclidean n}
    (hx : ContinuousOn x I) (hrange : ∀ t ∈ I, (t,x t) ∈ U)
    (hd : ∀ t ∈ I, HasDerivAt x (G (t,x t)) t) :
    ContDiffOn ℝ (⊤ : ℕ∞) x I := by
  apply contDiffOn_infty.mpr
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr hx
  | succ k ih =>
    rw [show ((k+1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp]
    apply (contDiffOn_succ_iff_deriv_of_isOpen hI).mpr
    refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact ((hG.of_le (by simp)).comp (contDiffOn_id.prodMk ih) hrange).congr
      (fun t ht => (hd t ht).deriv)

/-- Recovering coefficients at an actual time–state point removes only the
irrelevant off-chart evaluation convention. -/
theorem chartField_apply (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (z : Ω) (hp : z.val.2 ∈ e.source) :
    chartField X e he (z.val.1, (e z.val.2).val) =
      B.fiberCoordinates.equiv e he z.val.2 hp (X.val z) := by
  have hi : e.symm (MaximalFlow.euclideanModelPoint (e z.val.2).val) = z.val.2 := e.left_inv hp
  have hq : (z.val.1, (e z.val.2).val) ∈ chartDomain Ω e := by
    refine ⟨e.map_source hp, ?_⟩
    change (z.val.1, e.symm (MaximalFlow.euclideanModelPoint (e z.val.2).val)) ∈ Ω
    rw [hi]
    exact z.property
  let w : Ω := ⟨(z.val.1, e.symm (MaximalFlow.euclideanModelPoint (e z.val.2).val)),hq.2⟩
  have hw : w = z := Subtype.ext (Prod.ext rfl hi)
  have hcw : chartField X e he (z.val.1,(e z.val.2).val) = fieldCoefficients B X.val e he w := by
    unfold chartField fieldCoefficients
    rw [dite_eq_left hq, dite_eq_left (e.map_target hq.1)]
  rw [hcw, hw]
  simp only [fieldCoefficients, dite_eq_left hp]

/-- The actual intrinsic equation in a single chart implies the equation in
all charts by the tangent transition Jacobian. -/
theorem integralCurve_of_chart (X : SmoothTimeDependentField B Ω)
    {I : Set ℝ} (hI : IsOpen I) {γ : ℝ → M}
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hc : ContinuousOn γ I) (hr : MapsTo γ I e.source)
    (hgraph : ∀ t ∈ I, (t,γ t) ∈ Ω)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => (e (γ t)).val) I)
    (hd : ∀ t (ht : t ∈ I), HasDerivAt (fun r => (e (γ r)).val)
      (B.fiberCoordinates.equiv e he (γ t) (hr ht) (X.val ⟨(t,γ t),hgraph t ht⟩)) t) :
    EvolutionData.IsIntegralCurveOn X I γ := by
  refine ⟨hc, fun t ht => ⟨hgraph t ht, ?_⟩⟩
  intro d hdm hdt
  have hp := hr ht
  obtain ⟨U,hU,hpU,G,hG,hrep⟩ :=
    chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hdm) hp hdt
  have heq := hrep.comp_tendsto (hc.continuousAt (hI.mem_nhds ht))
  have hcoords := hs.contDiffAt (hI.mem_nhds ht)
  have hGt := hG.contDiffAt (hU.mem_nhds hpU)
  have hvel := TangentBundle.transition_jacobian S B.fiberCoordinates e d he hdm
    (γ t) hp hdt U G hU hpU hG hrep (X.val ⟨(t,γ t),hgraph t ht⟩)
  refine ⟨(hGt.comp t hcoords).congr_of_eventuallyEq heq.symm, ?_⟩
  rw [hvel]
  exact ((hGt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (hd t ht)).congr_of_eventuallyEq heq.symm

/-- Local existence for the original field, at any allowed initial absolute
time, follows after checking the actual chart ODE's smoothness and Lipschitz
hypotheses. -/
theorem local_solution (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω) (z : Ω) :
    ∃ (I : D13Unified.OpenTimeInterval) (γ : ℝ → M),
      z.val.1 ∈ I.carrier ∧ γ z.val.1 = z.val.2 ∧ EvolutionData.IsIntegralCurveOn X I.carrier γ := by
  obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 z.val.2
  have hcoords : (z.val.1, (e z.val.2).val) ∈ chartDomain Ω e := by
    refine ⟨e.map_source hp, ?_⟩
    simpa only [show MaximalFlow.euclideanModelPoint (e z.val.2).val = e z.val.2 from rfl,
      e.left_inv hp] using z.property
  let A := chartODE hΩ X e he
  obtain ⟨I,x,hx,_⟩ := D13Unified.Ch03.LocalExistenceUniqueness.local_existence_uniqueness
    A (chartODE_locallyLipschitz hΩ X e he) z.val.1 (e z.val.2).val hcoords
  have hRange : ∀ t ∈ I.carrier, (t,x t) ∈ chartDomain Ω e := hx.1.2.1
  have hxd : ∀ t ∈ I.carrier, HasDerivAt x (chartField X e he (t,x t)) t := by
    intro t ht
    simpa only [A, chartODE_eval hΩ X e he (hRange t ht)] using hx.1.2.2 t ht
  have hxs := smooth_of_nonautonomous I.isOpen (chartField_contDiffOn hΩ X e he)
    hx.1.1.continuousOn hRange hxd
  let γ : ℝ → M := fun t => e.symm (MaximalFlow.euclideanModelPoint (x t))
  have hsource : MapsTo γ I.carrier e.source := fun t ht => e.map_target (hRange t ht).1
  have hgraph : ∀ t ∈ I.carrier, (t,γ t) ∈ Ω := fun t ht => (hRange t ht).2
  have hγcoords : EqOn (fun t => (e (γ t)).val) x I.carrier := by
    intro t ht
    exact congrArg Subtype.val (e.right_inv (hRange t ht).1)
  have hγc : ContinuousOn γ I.carrier := e.symm.continuousOn.comp
    ((MaximalFlow.continuous_euclideanModelPoint n).comp_continuousOn hx.1.1.continuousOn)
    (fun t ht => (hRange t ht).1)
  refine ⟨I,γ,hx.2.1,?_,integralCurve_of_chart X I.isOpen e he hγc hsource hgraph
    (hxs.congr hγcoords) ?_⟩
  · change e.symm (MaximalFlow.euclideanModelPoint (x z.val.1)) = z.val.2
    have hx0 : x z.val.1 = (e z.val.2).val := hx.2.2
    rw [hx0]
    exact e.left_inv hp
  · intro t ht
    have hev : (fun r => (e (γ r)).val) =ᶠ[𝓝 t] x :=
      mem_of_superset (I.isOpen.mem_nhds ht) (fun r hr => hγcoords hr)
    have hvel := chartField_apply X e he ⟨(t,γ t),hgraph t ht⟩ (hsource ht)
    change chartField X e he (t,(e (γ t)).val) = _ at hvel
    have hvel' := (congrArg (fun v => chartField X e he (t,v)) (hγcoords ht)).symm.trans hvel
    exact hvel' ▸ (hxd t ht).congr_of_eventuallyEq hev

/-- Restricting an intrinsic solution to a coordinate neighborhood gives a
classical solution of the actual nonautonomous chart ODE. -/
theorem chartCurve_solution (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    {I : Set ℝ} {γ : ℝ → M} (hγ : EvolutionData.IsIntegralCurveOn X I γ)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (K : D13Unified.OpenTimeInterval) (hKI : K.carrier ⊆ I)
    (hr : ∀ t ∈ K.carrier, γ t ∈ e.source) :
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
      (chartODE hΩ X e he) K (fun t => (e (γ t)).val) := by
  have hdom : ∀ t ∈ K.carrier, (t,(e (γ t)).val) ∈ chartDomain Ω e := by
    intro t ht
    refine ⟨e.map_source (hr t ht), ?_⟩
    simpa only [show MaximalFlow.euclideanModelPoint (e (γ t)).val = e (γ t) from rfl,
      e.left_inv (hr t ht)] using (hγ.2 t (hKI ht)).choose
  refine ⟨?_,hdom,?_⟩
  · intro t ht
    exact (((hγ.2 t (hKI ht)).choose_spec e he (hr t ht)).1.of_le (by simp)).contDiffWithinAt
  · intro t ht
    rw [chartODE_eval hΩ X e he (hdom t ht),
      chartField_apply X e he ⟨(t,γ t),(hγ.2 t (hKI ht)).choose⟩ (hr t ht)]
    exact ((hγ.2 t (hKI ht)).choose_spec e he (hr t ht)).2

/-- Local Euclidean uniqueness applies at any common absolute time. -/
theorem local_unique (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (I K : D13Unified.OpenTimeInterval) (γ η : ℝ → M)
    (hγ : EvolutionData.IsIntegralCurveOn X I.carrier γ)
    (hη : EvolutionData.IsIntegralCurveOn X K.carrier η)
    (s : ℝ) (hs : s ∈ I.carrier ∩ K.carrier) (hmeet : γ s = η s) :
    γ =ᶠ[𝓝 s] η := by
  obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 (γ s)
  have hpη : η s ∈ e.source := hmeet ▸ hp
  have hnear : ∀ᶠ r in 𝓝 s,
      r ∈ I.carrier ∩ K.carrier ∧ γ r ∈ e.source ∧ η r ∈ e.source := by
    filter_upwards [I.isOpen.mem_nhds hs.1, K.isOpen.mem_nhds hs.2,
      (hγ.1.continuousAt (I.isOpen.mem_nhds hs.1)).eventually (e.open_source.mem_nhds hp),
      (hη.1.continuousAt (K.isOpen.mem_nhds hs.2)).eventually (e.open_source.mem_nhds hpη)]
      with r hI hK hrγ hrη
    exact ⟨⟨hI,hK⟩,hrγ,hrη⟩
  obtain ⟨l,r,hsJ,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let J := D13Unified.OpenTimeInterval.bounded l r (hsJ.1.trans hsJ.2)
  have hJγ := chartCurve_solution hΩ X hγ e he J
    (fun t ht => (hsub ht).1.1) (fun t ht => (hsub ht).2.1)
  have hJη := chartCurve_solution hΩ X hη e he J
    (fun t ht => (hsub ht).1.2) (fun t ht => (hsub ht).2.2)
  have hEq := D13Unified.Ch03.LocalExistenceUniqueness.no_crossing
    (chartODE hΩ X e he) (chartODE_locallyLipschitz hΩ X e he) J J
    (fun t => (e (γ t)).val) (fun t => (e (η t)).val) s hJγ hJη
    ⟨hsJ,hsJ⟩ (congrArg (fun p => (e p).val) hmeet)
  filter_upwards [isOpen_Ioo.mem_nhds hsJ] with t ht
  exact e.injOn (hsub ht).2.1 (hsub ht).2.2 (Subtype.ext (hEq ⟨ht,ht⟩))

/-- The coincidence set is open by local uniqueness and closed by
Hausdorffness, so equality holds on the complete intersection of lifespans. -/
theorem overlap_unique (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (I K : D13Unified.OpenTimeInterval) (γ η : ℝ → M)
    (hγ : EvolutionData.IsIntegralCurveOn X I.carrier γ)
    (hη : EvolutionData.IsIntegralCurveOn X K.carrier η)
    (s : ℝ) (hs : s ∈ I.carrier ∩ K.carrier) (hmeet : γ s = η s) :
    EqOn γ η (I.carrier ∩ K.carrier) := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let A := I.carrier ∩ K.carrier
  let : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp
    (I.ordConnected.inter K.ordConnected).isPreconnected
  have hc : IsClosed {t : A | γ t = η t} :=
    isClosed_eq (hγ.1.mono inter_subset_left).domRestrict
      (hη.1.mono inter_subset_right).domRestrict
  have ho : IsOpen {t : A | γ t = η t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact (local_unique hΩ X I K γ η hγ hη t t.property ht).comp_tendsto
      (continuous_subtype_val.tendsto t)
  have hall := (show IsClopen {t : A | γ t = η t} from ⟨hc,ho⟩).eq_univ ⟨⟨s,hs⟩,hmeet⟩
  intro t ht
  exact (show (⟨t,ht⟩ : A) ∈ {t : A | γ t = η t} from hall ▸ mem_univ _)

/-- Changing only off-domain representative values preserves the original
nonautonomous equation. -/
theorem integralCurve_congr (X : SmoothTimeDependentField B Ω)
    {I : Set ℝ} (hI : IsOpen I) {γ η : ℝ → M}
    (hγ : EvolutionData.IsIntegralCurveOn X I γ) (heq : EqOn η γ I) :
    EvolutionData.IsIntegralCurveOn X I η := by
  refine ⟨hγ.1.congr (fun t ht => heq ht), ?_⟩
  intro t ht
  have hAt := heq ht
  have hev : η =ᶠ[𝓝 t] γ := mem_of_superset (hI.mem_nhds ht) (fun r hr => heq hr)
  obtain ⟨hg,hcoord⟩ := hγ.2 t ht
  have hgη : (t,η t) ∈ Ω := by rw [hAt]; exact hg
  refine ⟨hgη, ?_⟩
  intro e he hp
  have hpγ : γ t ∈ e.source := hAt ▸ hp
  have hs := hcoord e he hpγ
  refine ⟨hs.1.congr_of_eventuallyEq (hev.fun_comp (fun p => (e p).val)), ?_⟩
  have hv := congrArg (fieldCoefficients B X.val e he)
    (show (⟨(t,η t),hgη⟩ : Ω) = ⟨(t,γ t),hg⟩ from Subtype.ext (Prod.ext rfl hAt))
  dsimp only [fieldCoefficients] at hv
  rw [dite_eq_left hp, dite_eq_left hpγ] at hv
  exact hv.symm ▸ hs.2.congr_of_eventuallyEq (hev.fun_comp (fun p => (e p).val))

/-- Gluing all solutions through a fixed allowed time–state point gives the
universal maximal solution, with no finite-endpoint or compactness assumption. -/
theorem maximal_through_exists (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω) (z : Ω) :
    ∃ (I : D13Unified.OpenTimeInterval) (γ : ℝ → M), IsMaximalThrough X z I γ := by
  classical
  let A := {a : D13Unified.OpenTimeInterval × (ℝ → M) //
    z.val.1 ∈ a.1.carrier ∧ a.2 z.val.1 = z.val.2 ∧
      EvolutionData.IsIntegralCurveOn X a.1.carrier a.2}
  obtain ⟨I₀,γ₀,hs₀,hv₀,hsol₀⟩ := local_solution hΩ X z
  let a₀ : A := ⟨(I₀,γ₀),hs₀,hv₀,hsol₀⟩
  let D : Set ℝ := ⋃ a : A, a.val.1.carrier
  have hsD : z.val.1 ∈ D := mem_iUnion.mpr ⟨a₀,hs₀⟩
  have hDo : IsOpen D := isOpen_iUnion (fun a : A => a.val.1.isOpen)
  have hDc : OrdConnected D := by
    constructor
    intro a ha b hb r hr
    obtain ⟨x,hx⟩ := mem_iUnion.mp ha
    obtain ⟨y,hy⟩ := mem_iUnion.mp hb
    by_cases hle : r ≤ z.val.1
    · exact mem_iUnion.mpr ⟨x,x.val.1.ordConnected.out hx x.property.1 ⟨hr.1,hle⟩⟩
    · exact mem_iUnion.mpr ⟨y,y.val.1.ordConnected.out y.property.1 hy ⟨le_of_not_ge hle,hr.2⟩⟩
  let I : D13Unified.OpenTimeInterval := ⟨⟨D,⟨z.val.1,hsD⟩,hDc⟩,hDo⟩
  let γ : ℝ → M := fun t => if h : ∃ a : A, t ∈ a.val.1.carrier then
    (Classical.choose h).val.2 t else z.val.2
  have hγa (a : A) : EqOn γ a.val.2 a.val.1.carrier := by
    intro t ht
    have hex : ∃ b : A, t ∈ b.val.1.carrier := ⟨a,ht⟩
    dsimp only [γ]
    rw [dite_eq_left hex]
    exact overlap_unique hΩ X (Classical.choose hex).val.1 a.val.1
      (Classical.choose hex).val.2 a.val.2 (Classical.choose hex).property.2.2 a.property.2.2
      z.val.1 ⟨(Classical.choose hex).property.1,a.property.1⟩
      ((Classical.choose hex).property.2.1.trans a.property.2.1.symm)
      ⟨Classical.choose_spec hex,ht⟩
  have hlocal (a : A) : EvolutionData.IsIntegralCurveOn X a.val.1.carrier γ :=
    integralCurve_congr X a.val.1.isOpen a.property.2.2 (hγa a)
  have hsol : EvolutionData.IsIntegralCurveOn X D γ := by
    constructor
    · intro t ht
      obtain ⟨a,ha⟩ := mem_iUnion.mp ht
      exact ((hlocal a).1.continuousAt (a.val.1.isOpen.mem_nhds ha)).continuousWithinAt
    · intro t ht
      obtain ⟨a,ha⟩ := mem_iUnion.mp ht
      exact (hlocal a).2 t ha
  refine ⟨I,γ,hsD,(hγa a₀ hs₀).trans hv₀,hsol,?_⟩
  intro K η hs hv hη
  let a : A := ⟨(K,η),hs,hv,hη⟩
  exact ⟨fun t ht => mem_iUnion.mpr ⟨a,ht⟩,hγa a⟩

open Specs.D13Unified.Ch04.MaximalSolutionMap
  Specs.D13Unified.Ch01.AutonomousParameters in
/-- Smooth dependence for an unparameterized nonautonomous ODE is the zero
parameter slice of D13's joint smooth-dependence theorem. -/
theorem chartSolution_regular (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) :
    IsOpen (solutionDomainValue (chartODE hΩ X e he)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × (ℝ × Euclidean n) => solutionValueValue (chartODE hΩ X e he) q.1 q.2.1 q.2.2)
        (solutionDomainValue (chartODE hΩ X e he)) := by
  let A := chartODE hΩ X e he
  let P : D13Unified.ParameterODE (Euclidean n) (Euclidean 0) := {
    domain := Prod.fst ⁻¹' A.domain
    isOpen_domain := A.isOpen_domain.preimage continuous_fst
    field := fun q => A.field ⟨q.val.1,q.property⟩
    continuous_field := A.continuous_field.comp
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _) }
  have hslice : ∀ p : Euclidean 0, atParameterValue P p = A := fun _ => rfl
  have hfield : D13Unified.Ch06.C1Dependence.field P =
      fun q : (ℝ × Euclidean n) × Euclidean 0 => A.eval q.1.1 q.1.2 := rfl
  have hC : ContDiffOn ℝ (⊤ : ℕ∞) (D13Unified.Ch06.C1Dependence.field P) P.domain := by
    rw [hfield]
    exact ((chartField_contDiffOn hΩ X e he).congr
      (fun q hq => chartODE_eval hΩ X e he hq)).comp contDiffOn_fst (fun _ h => h)
  obtain ⟨hD,hSmooth⟩ := D13Unified.Ch06.CkDependence.joint_smooth P hC
  let changeVars : ℝ × (ℝ × Euclidean n) → ℝ × ((ℝ × Euclidean n) × Euclidean 0) :=
    fun q => (q.1,(q.2,0))
  have hchange : ContDiff ℝ (⊤ : ℕ∞) changeVars :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  refine ⟨hD.preimage hchange.continuous, ?_⟩
  exact hSmooth.comp hchange.contDiffOn (fun _ h => h)

open Specs.D13Unified.Ch04.MaximalSolutionMap in
/-- The canonical coordinate solution, on its whole recorded interval, is an
intrinsic solution when lifted through the chart inverse. -/
theorem canonicalChartLift (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (z : Ω) (hp : z.val.2 ∈ e.source) :
    let A := chartODE hΩ X e he
    let I := maximalIntervalValue A z.val.1 (e z.val.2).val
    let γ := fun t => e.symm (MaximalFlow.euclideanModelPoint
      (solutionValueValue A t z.val.1 (e z.val.2).val))
    z.val.1 ∈ I.carrier ∧ γ z.val.1 = z.val.2 ∧ EvolutionData.IsIntegralCurveOn X I.carrier γ := by
  let A := chartODE hΩ X e he
  have hz : (z.val.1,(e z.val.2).val) ∈ A.domain := by
    refine ⟨e.map_source hp,?_⟩
    simpa only [show MaximalFlow.euclideanModelPoint (e z.val.2).val = e z.val.2 from rfl,
      e.left_inv hp] using z.property
  let I := maximalIntervalValue A z.val.1 (e z.val.2).val
  let x := fun t => solutionValueValue A t z.val.1 (e z.val.2).val
  have hx := D13Unified.ODE.solutionValue_ivp A (chartODE_locallyLipschitz hΩ X e he)
    z.val.1 (e z.val.2).val hz
  have hRange : ∀ t ∈ I.carrier, (t,x t) ∈ chartDomain Ω e := hx.1.2.1
  have hxd : ∀ t ∈ I.carrier, HasDerivAt x (chartField X e he (t,x t)) t := by
    intro t ht
    have hd : HasDerivAt x ((chartODE hΩ X e he).eval t (x t)) t := hx.1.2.2 t ht
    rw [chartODE_eval hΩ X e he (hRange t ht)] at hd
    exact hd
  have hxs := smooth_of_nonautonomous I.isOpen (chartField_contDiffOn hΩ X e he)
    hx.1.1.continuousOn hRange hxd
  let γ : ℝ → M := fun t => e.symm (MaximalFlow.euclideanModelPoint (x t))
  have hr : MapsTo γ I.carrier e.source := fun t ht => e.map_target (hRange t ht).1
  have hg : ∀ t ∈ I.carrier, (t,γ t) ∈ Ω := fun t ht => (hRange t ht).2
  have hv : EqOn (fun t => (e (γ t)).val) x I.carrier :=
    fun t ht => congrArg Subtype.val (e.right_inv (hRange t ht).1)
  have hc : ContinuousOn γ I.carrier := e.symm.continuousOn.comp
    ((MaximalFlow.continuous_euclideanModelPoint n).comp_continuousOn hx.1.1.continuousOn)
    (fun t ht => (hRange t ht).1)
  refine ⟨hx.2.1,?_,integralCurve_of_chart X I.isOpen e he hc hr hg (hxs.congr hv) ?_⟩
  · change e.symm (MaximalFlow.euclideanModelPoint (x z.val.1)) = z.val.2
    have hx0 : x z.val.1 = (e z.val.2).val := hx.2.2
    rw [hx0]
    exact e.left_inv hp
  · intro t ht
    have hev : (fun r => (e (γ r)).val) =ᶠ[𝓝 t] x :=
      mem_of_superset (I.isOpen.mem_nhds ht) (fun r hr => hv hr)
    have hvel := chartField_apply X e he ⟨(t,γ t),hg t ht⟩ (hr ht)
    have hvel' := (congrArg (fun v => chartField X e he (t,v)) (hv ht)).symm.trans hvel
    exact hvel' ▸ (hxd t ht).congr_of_eventuallyEq hev

open Specs.D13Unified.Ch04.MaximalSolutionMap in
/-- All canonical chart solutions agree with the maximal manifold solution on
their full actual coordinate lifespans. -/
theorem chartSolution_agrees (hΩ : IsOpen Ω) {X : SmoothTimeDependentField B Ω}
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (q : ℝ × (ℝ × M)) (hq : q.2 ∈ Ω) (hp : q.2.2 ∈ e.source)
    (ht : (q.1,q.2.1,(e q.2.2).val) ∈ solutionDomainValue (chartODE hΩ X e he)) :
    q ∈ evolutionDomain F ∧ evolution F q = e.symm (MaximalFlow.euclideanModelPoint
      (solutionValueValue (chartODE hΩ X e he) q.1 q.2.1 (e q.2.2).val)) := by
  have h := canonicalChartLift hΩ X e he ⟨q.2,hq⟩ hp
  have hsub := (hF ⟨q.2,hq⟩).2.2.2 _ _ h.1 h.2.1 h.2.2
  exact ⟨⟨hq,hsub.1 ht.2⟩,(evolution_apply F ⟨q.2,hq⟩ q.1).trans (hsub.2 ht.2)⟩

/-- A regular triple has a neighborhood in the actual domain and is jointly
smooth in both times and the initial state. -/
def EvolutionRegularAt (S : SmoothManifold n .euclidean M)
    (F : EvolutionFamily Ω) (q : ℝ × (ℝ × M)) : Prop :=
  evolutionDomain F ∈ 𝓝 q ∧ EvolutionSmoothAt S F q

open Specs.D13Unified.Ch04.MaximalSolutionMap in
/-- A canonical chart solution supplies a genuine domain neighborhood and
joint smoothness, for arbitrary starting and terminal times in its domain. -/
theorem regularAt_of_chartSolution (hΩ : IsOpen Ω) {X : SmoothTimeDependentField B Ω}
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (q : ℝ × (ℝ × M)) (hq : q.2 ∈ Ω) (hp : q.2.2 ∈ e.source)
    (ht : (q.1,q.2.1,(e q.2.2).val) ∈ solutionDomainValue (chartODE hΩ X e he)) :
    EvolutionRegularAt S F q := by
  let A : ℝ × (ℝ × M) → ℝ × (ℝ × Euclidean n) := fun w => (w.1,w.2.1,(e w.2.2).val)
  let Φ : ℝ × (ℝ × Euclidean n) → Euclidean n :=
    fun v => solutionValueValue (chartODE hΩ X e he) v.1 v.2.1 v.2.2
  let D := solutionDomainValue (chartODE hΩ X e he)
  have hReg := chartSolution_regular hΩ X e he
  have hA : ContinuousAt A q := continuousAt_fst.prodMk
    (continuousAt_snd.fst.prodMk (continuousAt_subtype_val.comp
      ((e.continuousAt hp).comp (f := fun w : ℝ × (ℝ × M) => w.2.2) continuousAt_snd.snd)))
  have hNear : ∀ᶠ w in 𝓝 q, w ∈ evolutionDomain F ∧
      evolution F w = e.symm (MaximalFlow.euclideanModelPoint (Φ (A w))) := by
    filter_upwards [(hΩ.preimage continuous_snd).mem_nhds hq,
      (e.open_source.preimage (continuous_snd.snd)).mem_nhds hp,
      hA.preimage_mem_nhds (hReg.1.mem_nhds ht)] with w hwΩ hwp hwD
    exact chartSolution_agrees hΩ F hF e he w hwΩ hwp hwD
  have hState : MaximalFlow.euclideanModelPoint (Φ (A q)) ∈ e.target :=
    (D13Unified.ODE.solutionValue_on_domain _ (chartODE_locallyLipschitz hΩ X e he)
      q.1 q.2.1 (e q.2.2).val ht).2.1
  have hΦ : ContinuousAt Φ (A q) := hReg.2.continuousOn.continuousAt (hReg.1.mem_nhds ht)
  have hLift : ContinuousAt (fun w => e.symm (MaximalFlow.euclideanModelPoint (Φ (A w)))) q :=
    (e.continuousAt_symm hState).comp
      (f := fun w => MaximalFlow.euclideanModelPoint (Φ (A w)))
      ((MaximalFlow.continuous_euclideanModelPoint n).continuousAt.comp
        (f := Φ ∘ A) (hΦ.comp hA))
  have hEq : evolution F =ᶠ[𝓝 q]
      (fun w => e.symm (MaximalFlow.euclideanModelPoint (Φ (A w)))) := hNear.mono (fun _ h => h.2)
  have hc : ContinuousAt (evolution F) q := hLift.congr hEq.symm
  have hCoord : (fun w => (e (evolution F w)).val) =ᶠ[𝓝 q] (Φ ∘ A) := by
    filter_upwards [hNear, hA.preimage_mem_nhds (hReg.1.mem_nhds ht)] with w hw hwD
    rw [hw.2]
    exact congrArg Subtype.val (e.right_inv
      (D13Unified.ODE.solutionValue_on_domain _ (chartODE_locallyLipschitz hΩ X e he)
        w.1 w.2.1 (e w.2.2).val hwD).2.1)
  have hpOut : evolution F q ∈ e.source := by
    rw [hEq.eq_of_nhds]
    exact e.map_target hState
  refine ⟨hNear.mono (fun _ h => h.1),hc,?_⟩
  intro a ha d hd hpa hpd
  obtain ⟨U,hU,hpU,K,hK,hKrep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 a ha e he) hpa hp
  obtain ⟨V,hV,hpV,L,hL,hLrep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hpOut hpd
  let H : ℝ × (ℝ × Euclidean n) → ℝ × (ℝ × Euclidean n) :=
    fun v => (v.1,v.2.1,K v.2.2)
  let W₀ := (fun v : ℝ × (ℝ × Euclidean n) => v.2.2) ⁻¹' U
  have hW₀ : IsOpen W₀ := hU.preimage continuous_snd.snd
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H W₀ := contDiffOn_fst.prodMk
    (contDiffOn_snd.fst.prodMk (hK.comp contDiffOn_snd.snd (fun _ h => h)))
  let W₁ := W₀ ∩ H ⁻¹' D
  have hW₁ : IsOpen W₁ := hH.continuousOn.isOpen_inter_preimage hW₀ hReg.1
  have hΦH : ContDiffOn ℝ (⊤ : ℕ∞) (Φ ∘ H) W₁ :=
    hReg.2.comp (hH.mono inter_subset_left) (fun _ h => h.2)
  let W := W₁ ∩ (Φ ∘ H) ⁻¹' V
  have hW : IsOpen W := hΦH.continuousOn.isOpen_inter_preimage hW₁ hV
  have hHq : H (q.1,q.2.1,(a q.2.2).val) = A q := by
    change (q.1,q.2.1,K (a q.2.2).val) = (q.1,q.2.1,(e q.2.2).val)
    exact congrArg (fun v => (q.1,q.2.1,v)) hKrep.eq_of_nhds
  have hCenter : (q.1,q.2.1,(a q.2.2).val) ∈ W := by
    refine ⟨⟨hpU,?_⟩,?_⟩
    · change H _ ∈ D
      rw [hHq]
      exact ht
    · change Φ (H _) ∈ V
      have hvq : (e (evolution F q)).val = Φ (A q) := hCoord.eq_of_nhds
      rw [hHq,← hvq]
      exact hpV
  refine ⟨W,hW,hCenter,L ∘ (Φ ∘ H),
    hL.comp (hΦH.mono inter_subset_left) (fun _ h => h.2),?_⟩
  have hKrep' := hKrep.comp_tendsto (continuousAt_snd.snd :
    ContinuousAt (fun w : ℝ × (ℝ × M) => w.2.2) q)
  have hLrep' := hLrep.comp_tendsto hc
  filter_upwards [hKrep',hCoord,hLrep'] with w hwK hwCoord hwL
  change L (Φ (H (w.1,w.2.1,(a w.2.2).val))) = (d (evolution F w)).val
  have hHw : H (w.1,w.2.1,(a w.2.2).val) = A w := by
    change (w.1,w.2.1,K (a w.2.2).val) = (w.1,w.2.1,(e w.2.2).val)
    exact congrArg (fun v => (w.1,w.2.1,v)) hwK
  change (e (evolution F w)).val = Φ (A w) at hwCoord
  rw [hHw,← hwCoord]
  exact hwL

/-- Domain-restricted composition follows from the already proved exact
restart intervals. Both initial data must belong to their actual domains. -/
theorem composition_mem_value {X : SmoothTimeDependentField B Ω}
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F) (t s u : ℝ) (p : M)
    (hu : (u,s,p) ∈ evolutionDomain F)
    (ht : (t,u,evolution F (u,s,p)) ∈ evolutionDomain F) :
    (t,s,p) ∈ evolutionDomain F ∧
      evolution F (t,s,p) = evolution F (t,u,evolution F (u,s,p)) := by
  obtain ⟨hz,hu⟩ := hu
  let z : Ω := ⟨(s,p),hz⟩
  have hv : evolution F (u,s,p) = F.curve z u := evolution_apply F z u
  obtain ⟨hw,hI,_hElapsed,hEq⟩ := restart S B Ω X F hF z u hu
  have htNew : t ∈ (F.interval ⟨(u,F.curve z u),hw⟩).carrier := by
    have ht' : (t,u,F.curve z u) ∈ evolutionDomain F := by rwa [hv] at ht
    exact (mem_evolutionDomain F ⟨(u,F.curve z u),hw⟩ t).mp ht'
  have htOld : t ∈ (F.interval z).carrier := hI ▸ htNew
  refine ⟨⟨hz,htOld⟩,?_⟩
  rw [hv,evolution_apply F z t,evolution_apply F ⟨(u,F.curve z u),hw⟩ t]
  exact (hEq t htOld).symm

/-- Composition of two regular evolution maps preserves regularity. The
starting time is kept as a variable throughout the local coordinate proof. -/
theorem regularAt_comp {X : SmoothTimeDependentField B Ω}
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F) (t s u : ℝ) (p : M)
    (hs : EvolutionRegularAt S F (u,s,p))
    (ht : EvolutionRegularAt S F (t,u,evolution F (u,s,p))) :
    EvolutionRegularAt S F (t,s,p) := by
  let Q : ℝ × (ℝ × M) → M := fun w => evolution F (u,w.2)
  let C : ℝ × (ℝ × M) → ℝ × (ℝ × M) := fun w => (w.1,u,Q w)
  have hi : ContinuousAt (fun w : ℝ × (ℝ × M) => (u,w.2)) (t,s,p) :=
    continuousAt_const.prodMk continuousAt_snd
  have hOldCont : ContinuousAt (evolution F) (u,s,p) := hs.2.1
  have hQ : ContinuousAt Q (t,s,p) :=
    ContinuousAt.comp (g := evolution F) (f := fun w : ℝ × (ℝ × M) => (u,w.2))
      (x := (t,s,p)) hOldCont hi
  have hC : ContinuousAt C (t,s,p) :=
    continuousAt_fst.prodMk (continuousAt_const.prodMk hQ)
  have hNear : ∀ᶠ w in 𝓝 (t,s,p), w ∈ evolutionDomain F ∧
      evolution F w = evolution F (C w) := by
    filter_upwards [hi.preimage_mem_nhds hs.1,hC.preimage_mem_nhds ht.1] with w hw₁ hw₂
    exact composition_mem_value F hF w.1 w.2.1 u w.2.2 hw₁ hw₂
  have hEq : evolution F =ᶠ[𝓝 (t,s,p)] (evolution F ∘ C) := hNear.mono (fun _ h => h.2)
  have hc : ContinuousAt (evolution F) (t,s,p) :=
    (ContinuousAt.comp (f := C) ht.2.1 hC).congr hEq.symm
  refine ⟨hNear.mono (fun _ h => h.1),hc,?_⟩
  intro a ha d hd hpa hpd
  obtain ⟨e,he,hpe⟩ := S.smoothStructure.property.1.1 (Q (t,s,p))
  obtain ⟨U,hU,hpU,K,hK,hKrep⟩ := hs.2.2 a ha e he hpa hpe
  have hval : evolution F (t,s,p) = evolution F (t,u,Q (t,s,p)) := hEq.eq_of_nhds
  have hpd' : evolution F (t,u,Q (t,s,p)) ∈ d.source := hval ▸ hpd
  obtain ⟨V,hV,hpV,L,hL,hLrep⟩ := ht.2.2 e he d hd hpe hpd'
  let J : ℝ × (ℝ × Euclidean n) → ℝ × (ℝ × Euclidean n) := fun v => (u,v.2)
  let H : ℝ × (ℝ × Euclidean n) → ℝ × (ℝ × Euclidean n) :=
    fun v => (v.1,u,K (J v))
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J := contDiff_const.prodMk contDiff_snd
  let W₀ := J ⁻¹' U
  have hW₀ : IsOpen W₀ := hU.preimage hJ.continuous
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H W₀ := contDiffOn_fst.prodMk
    (contDiffOn_const.prodMk (hK.comp hJ.contDiffOn (fun _ h => h)))
  let W := W₀ ∩ H ⁻¹' V
  have hW : IsOpen W := hH.continuousOn.isOpen_inter_preimage hW₀ hV
  have hHq : H (t,s,(a p).val) = (t,u,(e (Q (t,s,p))).val) := by
    change (t,u,K (u,s,(a p).val)) = (t,u,(e (Q (t,s,p))).val)
    rw [hKrep.eq_of_nhds]
  have hCenter : (t,s,(a p).val) ∈ W := by
    refine ⟨hpU,?_⟩
    change H _ ∈ V
    rw [hHq]
    exact hpV
  refine ⟨W,hW,hCenter,L ∘ H,hL.comp (hH.mono inter_subset_left) (fun _ h => h.2),?_⟩
  have hKrep' := hKrep.comp_tendsto hi
  have hLrep' := hLrep.comp_tendsto hC
  filter_upwards [hKrep',hLrep',hEq] with w hwK hwL hwEq
  have hHw : H (w.1,w.2.1,(a w.2.2).val) = (w.1,u,(e (Q w)).val) := by
    change (w.1,u,K (u,w.2.1,(a w.2.2).val)) = (w.1,u,(e (Q w)).val)
    exact congrArg (fun v => (w.1,u,v)) hwK
  change L (H (w.1,w.2.1,(a w.2.2).val)) = (d (evolution F w)).val
  rw [hHw]
  exact hwL.trans (congrArg (fun x => (d x).val) hwEq.symm)

open Specs.D13Unified.Ch04.MaximalSolutionMap in
/-- Each permitted initial point lies in the coordinate solution domain at its
initial time, with no uniform time width required. -/
theorem chartSolution_diagonal (hΩ : IsOpen Ω) (X : SmoothTimeDependentField B Ω)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (z : Ω) (hp : z.val.2 ∈ e.source) :
    (z.val.1,z.val.1,(e z.val.2).val) ∈ solutionDomainValue (chartODE hΩ X e he) := by
  refine ⟨⟨e.map_source hp,?_⟩,(canonicalChartLift hΩ X e he z hp).1⟩
  simpa only [show MaximalFlow.euclideanModelPoint (e z.val.2).val = e z.val.2 from rfl,
    e.left_inv hp] using z.property

/-- Regularity holds at every initial diagonal triple. -/
theorem regularAt_diagonal (hΩ : IsOpen Ω) {X : SmoothTimeDependentField B Ω}
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F) (z : Ω) :
    EvolutionRegularAt S F (z.val.1,z.val) := by
  obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 z.val.2
  exact regularAt_of_chartSolution hΩ F hF e he _ z.property hp
    (chartSolution_diagonal hΩ X e he z hp)

open Specs.D13Unified.Ch04.MaximalSolutionMap in
/-- The regular terminal times form a nonempty clopen subset of each actual
connected lifespan. Local chart maps supply continuation in both directions. -/
theorem regularAt_of_mem (hΩ : IsOpen Ω) {X : SmoothTimeDependentField B Ω}
    (F : EvolutionFamily Ω) (hF : IsMaximalFamily X F)
    (z : Ω) (t : ℝ) (ht : t ∈ (F.interval z).carrier) :
    EvolutionRegularAt S F (t,z.val) := by
  let I := (F.interval z).carrier
  let T : Set I := {a | EvolutionRegularAt S F (a.val,z.val)}
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp
    (F.interval z).ordConnected.isPreconnected
  have hStart (a : I) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (hp : F.curve z a.val ∈ e.source) :
      (a.val,a.val,(e (F.curve z a.val)).val) ∈ solutionDomainValue (chartODE hΩ X e he) :=
    chartSolution_diagonal hΩ X e he ⟨(a.val,F.curve z a.val),graph_mem hF z a.property⟩ hp
  have ho : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 (F.curve z a.val)
    have hReg := chartSolution_regular hΩ X e he
    have hA : ContinuousAt (fun b : I => (b.val,a.val,(e (F.curve z a.val)).val)) a :=
      continuousAt_subtype_val.prodMk (continuousAt_const.prodMk continuousAt_const)
    have hNear := hA.preimage_mem_nhds (hReg.1.mem_nhds (hStart a e he hp))
    filter_upwards [hNear] with b hb
    have hLocal := regularAt_of_chartSolution hΩ F hF e he (b.val,a.val,F.curve z a.val)
      (graph_mem hF z a.property) hp hb
    apply regularAt_comp F hF b.val z.val.1 a.val z.val.2 ha
    change EvolutionRegularAt S F (b.val,a.val,evolution F (a.val,z.val))
    rw [evolution_apply]
    exact hLocal
  have hc : IsClosed T := by
    apply isClosed_of_closure_subset
    intro a ha
    obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 (F.curve z a.val)
    have hReg := chartSolution_regular hΩ X e he
    have hγ : Continuous (fun b : I => F.curve z b.val) := (hF z).2.2.1.1.domRestrict
    have hE : ContinuousAt (fun b : I => (e (F.curve z b.val)).val) a :=
      continuousAt_subtype_val.comp ((e.continuousAt hp).comp
        (f := fun b : I => F.curve z b.val) hγ.continuousAt)
    have hA : ContinuousAt (fun b : I => (a.val,b.val,(e (F.curve z b.val)).val)) a :=
      continuousAt_const.prodMk (continuousAt_subtype_val.prodMk hE)
    have hNear := hA.preimage_mem_nhds (hReg.1.mem_nhds (hStart a e he hp))
    have hSource := hγ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hp)
    obtain ⟨b,⟨hb,hpb⟩,hbT⟩ := mem_closure_iff_nhds.mp ha _ (inter_mem hNear hSource)
    have hLocal := regularAt_of_chartSolution hΩ F hF e he (a.val,b.val,F.curve z b.val)
      (graph_mem hF z b.property) hpb hb
    apply regularAt_comp F hF a.val z.val.1 b.val z.val.2 hbT
    change EvolutionRegularAt S F (a.val,b.val,evolution F (b.val,z.val))
    rw [evolution_apply]
    exact hLocal
  have hAll : T = univ := (show IsClopen T from ⟨hc,ho⟩).eq_univ
    ⟨⟨z.val.1,(hF z).1⟩,regularAt_diagonal hΩ F hF z⟩
  exact (show (⟨t,ht⟩ : I) ∈ T from hAll ▸ mem_univ _)

end Coordinates

theorem maximal_family_exists : Specs.SmoothManifolds.Ch06.Evolution.maximal_family_existsType.{u} := by
  intro n M _ S B J _hJ _hconn Ω hΩ _hΩJ X
  choose I γ hγ using maximal_through_exists hΩ X
  exact ⟨⟨I,γ⟩,hγ⟩

/-- Openness and joint smoothness hold on the entire maximal triple domain. -/
theorem domain_open_smooth : Specs.SmoothManifolds.Ch06.Evolution.domain_open_smoothType.{u} := by
  intro n M _ S B Ω hΩ X F hF
  have hReg : ∀ q ∈ evolutionDomain F, EvolutionRegularAt S F q := by
    intro q hq
    obtain ⟨hz,ht⟩ := hq
    exact regularAt_of_mem hΩ F hF ⟨q.2,hz⟩ q.1 ht
  exact ⟨isOpen_iff_mem_nhds.mpr (fun q hq => (hReg q hq).1),
    fun z => (initial_value hF z).1,fun q hq => (hReg q hq).2⟩

theorem time_diffeomorph : Specs.SmoothManifolds.Ch06.Evolution.time_diffeomorphType.{u} := by
  intro n M _ S B Ω hΩ X F hF
  obtain ⟨hD,_hdiag,hSmooth⟩ := domain_open_smooth S B Ω hΩ X F hF
  exact time_diffeomorph_of_open_smooth S B X F hF hD hSmooth

/-- M06.08: unique maximal evolution, its full open smooth domain, exact restart
intervals and the two mutually inverse smooth time maps. -/
theorem evolution_exists : Specs.SmoothManifolds.Ch06.Evolution.evolution_existsType.{u} :=
  evolution_exists_conditional maximal_family_exists domain_open_smooth

end SmoothManifolds.Evolution
