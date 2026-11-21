import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Dulac
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.DomainInterior
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge

/-! Geometric preparation for Bendixson--Dulac on the actual maximal flow.
The Green flux contradiction is applied with the actual regular-domain and
outward-first oriented-boundary hypotheses. -/
noncomputable section
open Set Function Filter
open scoped Topology

namespace D13Unified.Ch13.Dulac
open Ch06.StateDerivative Ch11.Orbits
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan
open Specs.D13Unified.Ch21.DomainInterior

/-- Standard real Euclidean coordinates, preserving the norm and orientation. -/
def planeCoordinates : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv

/-- Divergence in the standard oriented orthonormal real basis (1,i). -/
def divergence (g : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ g z 1).re + (fderiv ℝ g z Complex.I).im


lemma complete_time (F : AutonomousODE ℂ) {x : ℂ} (hc : IsComplete F x) (t : ℝ) :
    t ∈ (flowInterval F x).carrier := by
  rw [show (flowInterval F x).carrier = univ from hc]
  trivial

/-- A self-intersection of a complete trajectory is exactly a time period,
including the zero difference. This is stronger than equality at one base time. -/
lemma flow_eq_iff_period (F : AutonomousODE ℂ)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : ℂ} (hx : x ∈ F.domain)
    (hc : IsComplete F x) (a b : ℝ) :
    flow F a x = flow F b x ↔ Periodic (fun t => flow F t x) (a-b) := by
  constructor
  · intro he
    by_cases hab : b = a
    · subst b
      simp only [sub_self]
      exact periodic_with_period_zero (fun t => flow F t x)
    · exact (Ch11.Orbits.self_intersection F hF x hx b (complete_time F hc b)
        a (complete_time F hc a) hab he.symm).2
  · intro hp
    simpa using hp b

/-- A nonconstant trajectory cannot pass through an equilibrium. -/
lemma field_ne_zero_on_complete_orbit (F : AutonomousODE ℂ)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : ℂ} (hx : x ∈ F.domain)
    (hn : ¬ IsConstant F x) (hc : IsComplete F x) (t : ℝ) :
    F.eval (flow F t x) ≠ 0 := by
  intro he
  have hX := flow_ivp F hF hx
  have ht := complete_time F hc t
  have hy := hX.1.2.1 t ht
  have hconst := (Ch11.Orbits.constant_equilibrium F hF hy he).2
  have htr := Ch11.Flow.flow_translation F hF x hx t ht
  have heq (s : ℝ) : flow F s x = flow F t x := by
    have hs : s-t ∈ (flowInterval F (flow F t x)).carrier := by
      rw [htr.1]
      simpa using complete_time F hc s
    have hh := hconst (s-t) hs
    rw [htr.2 (s-t) (by simpa using complete_time F hc s)] at hh
    simpa using hh
  apply hn
  intro s _
  exact (heq s).trans ((heq 0).symm.trans hX.2.2)

/-- Normalize the least positive period to one before taking the quotient.
The injectivity proof uses all integer periods, rather than injectivity of a
representative on an arbitrarily chosen interval. -/
theorem periodic_orbit_loop : Specs.D13Unified.Ch13.Dulac.PeriodicOrbitLoop := by
  intro F hF x hx hn hp
  obtain ⟨hc, T, hT, hperiod, _hleast, hperiods⟩ := hp
  let g : ℝ → ℂ := fun t => flow F (T*t) x
  have hgperiod : Periodic g 1 := by
    intro t
    change flow F (T*(t+1)) x = flow F (T*t) x
    rw [mul_add, mul_one]
    exact hperiod _
  let γ : Circle → ℂ := hgperiod.lift
  have hγlift (t : ℝ) : realLift γ t = g t := hgperiod.lift_coe t
  have hX := flow_ivp F hF hx
  have hcont : ContDiff ℝ 1 (fun t => flow F t x) := by
    apply contDiffOn_univ.mp
    simpa only [show (flowInterval F x).carrier = univ from hc] using hX.1.1
  have hgcont : ContDiff ℝ 1 g :=
    hcont.comp (contDiff_const.mul contDiff_id)
  have heq (t u : ℝ) : realLift γ t = realLift γ u ↔ ∃ k : ℤ, t-u = (k : ℝ) := by
    rw [hγlift, hγlift, flow_eq_iff_period F hF hx hc, hperiods]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hh : T * (t-u) = T * (k : ℝ) := by nlinarith [hk]
      exact mul_left_cancel₀ (ne_of_gt hT) hh
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; ring⟩
  have hd (t : ℝ) : HasDerivAt (realLift γ) (T • F.eval (realLift γ t)) t := by
    have hlin : HasDerivAt (fun s : ℝ => T*s) T t := by
      simpa using (hasDerivAt_id t).const_mul T
    have houter : HasDerivAt (fun s : ℝ => flow F s x)
        (F.eval (flow F (T*t) x)) (T*t) := hX.1.2.2 _ (complete_time F hc _)
    have hd := houter.scomp t hlin
    have heval : F.toODE.eval (T*t) (flow F (T*t) x) = F.eval (flow F (T*t) x) := rfl
    simpa only [heval, mul_one, show realLift γ = g from funext hγlift,
      g, Function.comp_def] using hd
  have hreg : RegularEmbeddedLoop γ := by
    apply (Ch21.Collar.regularity_bridge γ).mpr
    refine ⟨?_, heq, ?_⟩
    · simpa only [show realLift γ = g from funext hγlift] using hgcont
    · intro t
      rw [(hd t).deriv]
      apply smul_ne_zero (ne_of_gt hT)
      rw [hγlift]
      exact field_ne_zero_on_complete_orbit F hF hx hn hc (T*t)
  refine ⟨T, γ, hT, hreg, ?_, hγlift, hd⟩
  rw [← Ch21.Collar.lift_trace γ]
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨T*t, complete_time F hc _, hγlift t |>.symm⟩
  · rintro _ ⟨t, _, rfl⟩
    refine ⟨t/T, ?_⟩
    rw [hγlift]
    change flow F (T*(t/T)) x = flow F t x
    congr 1
    field_simp

/-- Separation and simply connected interior containment are both used;
compactness of the closure follows from boundedness in the actual plane. -/
theorem periodic_orbit_interior : Specs.D13Unified.Ch13.Dulac.PeriodicOrbitInterior := by
  intro F hF D hD hsc x hx hn hp htrace
  obtain ⟨T, γ, hT, hγ, hγtrace, hγlift, hγderiv⟩ := periodic_orbit_loop F hF x hx hn hp
  obtain ⟨V, E, hcomp, hVo, _hEo, _hVp, _hEp, hVb, _hEb, hVf, _hEf,
    hcl, hC1, _hiE, _hiV⟩ := Ch21.SmoothJordan.smooth_jordan γ hγ
  obtain ⟨p, hpV⟩ := hcomp.1
  have hpS : p ∈ (range γ)ᶜ := hcomp.2.2.2.1 ▸ Or.inl hpV
  have hbounded : BoundedInterior γ V := ⟨p, hpS, hcomp.2.2.2.2.1 p hpV, hVb⟩
  have hVD := (Ch21.DomainInterior.domain_interior D hD hsc γ hγ
    (hγtrace ▸ htrace) V hbounded).2
  exact ⟨T, γ, V, hT, hγ, hγtrace, hγlift, hγderiv, ⟨p, hpV⟩, hVo, hVb,
    hC1, hVf, hcl, hVb.isCompact_closure, hVD⟩

/-- A C¹ graph boundary supplies the library's actual regular-domain
structure after the fixed real coordinate change. -/
lemma regular_domain_of_graph_boundary (V : Set ℂ) (hVo : IsOpen V)
    (hVb : Bornology.IsBounded V) (hC1 : HasC1Boundary V) :
    Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain
      (planeCoordinates.symm ⁻¹' V) := by
  let W := planeCoordinates.symm ⁻¹' V
  have hwfront : frontier W = planeCoordinates.symm ⁻¹' frontier V :=
    (planeCoordinates.symm.toHomeomorph.preimage_frontier V).symm
  refine ⟨by norm_num, ?_, hVo.preimage planeCoordinates.symm.continuous, ?_⟩
  · apply (hVb.isCompact_closure.image planeCoordinates.continuous).isBounded.subset
    intro z hz
    exact ⟨planeCoordinates.symm z, subset_closure hz, planeCoordinates.apply_symm_apply z⟩
  · intro p hp
    have hpV : planeCoordinates.symm p ∈ frontier V := by
      have hh : p ∈ frontier W := hp
      rw [hwfront] at hh
      exact hh
    obtain ⟨L, b, c, hb, hc, f, hf, hf0, hfbound, hgraph⟩ := hC1 _ hpV
    let C : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ := planeCoordinates.symm.trans L
    let a : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun z => C (z-p)
    let U := a ⁻¹' (Ioo (-b) b ×ˢ Ioo (-c) c)
    let ρ : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => (a z).2 - f (a z).1
    have ha : ContDiff ℝ 1 a := C.contDiff.comp (contDiff_id.sub contDiff_const)
    have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).preimage ha.continuous
    have hpg : p ∈ U := by
      simp [U, a, hb, hc]
    have hrel (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ U) :
        (z ∈ frontier W ↔ (a z).2 = f (a z).1) ∧
        (z ∈ W ↔ (a z).2 < f (a z).1) := by
      have he : L (planeCoordinates.symm z - planeCoordinates.symm p) = a z := by
        simp [a, C, map_sub]
      have hh := hgraph (planeCoordinates.symm z) (by rwa [he])
      rw [he] at hh
      simpa only [hwfront, mem_preimage, W] using hh
    refine ⟨U, ρ, hpg, hU, ?_, ?_, ?_, ?_⟩
    · exact ha.contDiffOn.snd.sub (hf.comp ha.contDiffOn.fst (fun z hz => hz.1))
    · intro z hz
      exact (hrel z hz).2.trans (sub_neg : (a z).2 - f (a z).1 < 0 ↔ _).symm
    · intro z hz
      exact (hrel z hz).1.trans sub_eq_zero.symm
    · intro z hz _hz0 hzero
      have haf : HasFDerivAt a C.toContinuousLinearMap z := by
        simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, a] using
          C.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const p)
      have hff : DifferentiableAt ℝ f (a z).1 :=
        ((hf (a z).1 hz.1).contDiffAt (isOpen_Ioo.mem_nhds hz.1)).differentiableAt one_ne_zero
      have hr := haf.snd.sub (hff.hasFDerivAt.comp z haf.fst)
      have he := congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => A (C.symm (0,1)))
        (hr.fderiv.symm.trans hzero)
      have hv : C.toContinuousLinearMap (C.symm (0,1)) = (0,1) := C.apply_symm_apply _
      simp only [sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.fst, ContinuousLinearMap.snd, hv,
        map_zero, sub_zero, zero_apply] at he
      norm_num at he

namespace GreenFlux
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.GeneralizedStokes.Model

/-- A velocity of a curve lying on the boundary is orthogonal to the
actual outward normal. This uses a local defining function and the chain rule. -/
lemma normal_orthogonal_of_boundary_curve {V : Set (E 2)}
    (hV : IsClassicalRegularDomain V) (α : ℝ → E 2) (t : ℝ) (v : E 2)
    (hd : HasDerivAt α v t) (hα : ∀ s : ℝ, α s ∈ frontier V) :
    inner ℝ (outwardNormal hV ⟨α t, hα t⟩) v = 0 := by
  obtain ⟨U, ρ, hpU, hρ⟩ := hV.defining (α t) (hα t)
  have hρd := ((hρ.regular (α t) hpU).contDiffAt
    (hρ.isOpen.mem_nhds hpU)).differentiableAt one_ne_zero
  have hchain := hρd.hasFDerivAt.comp_hasDerivAt t hd
  have he : (ρ ∘ α) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hd.continuousAt.preimage_mem_nhds (hρ.isOpen.mem_nhds hpU)] with s hs
    exact (hρ.zero_level _ hs).mp (hα s)
  have hv : fderiv ℝ ρ (α t) v = 0 :=
    (hchain.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const t (0 : ℝ))
  have hnormal := D04.ClassicalRegularDomains.outwardNormal_formula hV ⟨α t, hα t⟩ hρ hpU
  change outwardNormal hV ⟨α t, hα t⟩ =
    Specs.D04.C12.ClassicalRegularDomains.Model.normalFromDefining ρ (α t) at hnormal
  rw [hnormal]
  exact (D04.ClassicalRegularDomains.normal_properties hρ hpU (hα t)).2.1 v hv

/-- Strict positivity on a nonempty open set gives a strictly positive actual
Darboux region integral. The proof uses its proved Lebesgue integral bridge. -/
lemma regionIntegral_pos {V : Set (E 2)} (hV : IsOpen V) (hne : V.Nonempty)
    (f : E 2 → ℝ) (hi : RegionIntegrable (fun x : V => f x))
    (hf : ∀ z ∈ V, 0 < f z) : 0 < regionIntegral (fun x : V => f x) := by
  obtain ⟨hfi, he⟩ := D04.MeasureBridge.region_bridge_ambient f hV.measurableSet hi
  change regionIntegral (fun x : V => f x) = _ at he
  rw [he]
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict V] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem hV.measurableSet] with z hz
    exact (hf z hz).le
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfi).mpr
  have hs : support f ∩ V = V := by
    apply inter_eq_right.mpr
    intro z hz
    exact ne_of_gt (hf z hz)
  rw [hs]
  exact hV.measure_pos MeasureTheory.volume hne

/-- The coordinate partials in the flux theorem equal the original real
Fréchet divergence in the standard complex-plane basis. -/
lemma divergence_coordinates (g : ℂ → ℂ) (z : E 2)
    (hg : DifferentiableAt ℝ g (planeCoordinates.symm z)) :
    divergenceDensity (fun w => (g (planeCoordinates.symm w)).re)
      (fun w => (g (planeCoordinates.symm w)).im) z =
      divergence g (planeCoordinates.symm z) := by
  have hdir (j : Fin 2) :
      HasDerivAt (fun t : ℝ => planeCoordinates.symm (z + t • standardBasis 2 j))
        (planeCoordinates.symm (standardBasis 2 j)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => z + t • standardBasis 2 j) (standardBasis 2 j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (standardBasis 2 j)).const_add z
    simpa [Function.comp_def] using planeCoordinates.symm.hasFDerivAt.comp_hasDerivAt 0 hl
  have hgd (j : Fin 2) := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hdir j) (by simp)
  have hp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hgd 0)
  have hq := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (hgd 1)
  have h0 : planeCoordinates.symm (standardBasis 2 0) = 1 := by
    simp [planeCoordinates, standardBasis, Complex.orthonormalBasisOneI_repr_symm_apply]
  have h1 : planeCoordinates.symm (standardBasis 2 1) = Complex.I := by
    simp [planeCoordinates, standardBasis, Complex.orthonormalBasisOneI_repr_symm_apply]
  change deriv (fun t : ℝ => (g (planeCoordinates.symm (z + t • standardBasis 2 0))).re) 0 +
      deriv (fun t : ℝ => (g (planeCoordinates.symm (z + t • standardBasis 2 1))).im) 0 = _
  simpa only [Function.comp_def, h0, h1, Complex.reCLM_apply, Complex.imCLM_apply, divergence] using congrArg₂ (· + ·) hp.deriv hq.deriv

end GreenFlux

/-- Green's theorem with its real outward-first boundary orientation and
actual regular-domain hypotheses. The sign hypothesis is used only after the
boundary integral has been shown to vanish. -/
theorem regular_domain_flux_contradiction :
    Specs.D13Unified.Ch13.Dulac.RegularDomainFluxContradiction := by
  intro V hV hne U P Q hU hVU hP hQ ht hsign
  obtain ⟨hb, o, bO, ho, hout, _hc, hi, _hcirculation, _hflux, hnormal⟩ :=
    D04.Green.green hV U P Q hU hVU hP hQ
  have hz : Specs.D04.C12.GreenCirculationAndFlux.Model.normalFluxField hV hb bO P Q = 0 := by
    funext p
    change (_ + _) • _ = 0
    rw [ht ⟨p, hb ▸ p.property⟩, zero_smul]
  rw [hz] at hnormal
  have hi0 := D04Stokes.positive_integral_unique bO 0 hnormal
    (D04Stokes.positive_integral_zero bO)
  rcases hsign with hp | hn
  · have hpos := GreenFlux.regionIntegral_pos hV.isOpen hne _ hi
      (fun z hz => hp z (hVU (subset_closure hz)))
    linarith
  · have hfi := D04.MeasureBridge.region_bridge_ambient
      (Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q)
      hV.isOpen.measurableSet hi
    have hp : 0 < ∫ z in V,
        -Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q z := by
      have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict V]
          (fun z => -Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q z) := by
        filter_upwards [MeasureTheory.ae_restrict_mem hV.isOpen.measurableSet] with z hz
        exact (neg_pos.mpr (hn z (hVU (subset_closure hz)))).le
      apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfi.1.neg).mpr
      have hs : support (fun z => -Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q z) ∩ V = V := by
        apply inter_eq_right.mpr
        intro z hz
        exact ne_of_gt (neg_pos.mpr (hn z (hVU (subset_closure hz))))
      rw [hs]
      exact hV.isOpen.measure_pos MeasureTheory.volume hne
    have hi0' : D04.JordanRegions.regionIntegral (fun x : V =>
        Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q x) = 0 := hi0
    rw [MeasureTheory.integral_neg, ← hfi.2, hi0', neg_zero] at hp
    exact (lt_irrefl 0) hp

/-- Bendixson--Dulac exclusion. All geometric, regularity, orientation and
integral hypotheses are established before applying the flux obstruction. -/
theorem bendixson_dulac : Specs.D13Unified.Ch13.Dulac.BendixsonDulac := by
  intro F hF D hD hsc hDF B hB hsign x hx htrace hn hp
  obtain ⟨T, γ, V, hT, hγ, hγtrace, hγlift, hγderiv, hVne, hVo, hVb,
    hVC1, hVf, hVcl, hVcompact, hVD⟩ :=
    periodic_orbit_interior F hF D hD hsc x hx hn hp htrace
  let E := EuclideanSpace ℝ (Fin 2)
  let W : Set E := planeCoordinates.symm ⁻¹' V
  let U : Set E := planeCoordinates.symm ⁻¹' D
  let g : ℂ → ℂ := fun z => B z • F.eval z
  let P : E → ℝ := fun z => (g (planeCoordinates.symm z)).re
  let Q : E → ℝ := fun z => (g (planeCoordinates.symm z)).im
  have hW := regular_domain_of_graph_boundary V hVo hVb hVC1
  have hUne : IsOpen U := hD.preimage planeCoordinates.symm.continuous
  have hWne : W.Nonempty := by
    obtain ⟨y, hy⟩ := hVne
    exact ⟨planeCoordinates y, by simpa [W] using hy⟩
  have hWcl : closure W = planeCoordinates.symm ⁻¹' closure V :=
    (planeCoordinates.symm.toHomeomorph.preimage_closure V).symm
  have hWf : frontier W = planeCoordinates.symm ⁻¹' frontier V :=
    (planeCoordinates.symm.toHomeomorph.preimage_frontier V).symm
  have hWU : closure W ⊆ U := by
    intro z hz
    rw [hWcl] at hz
    exact hVD hz
  have hg : ContDiffOn ℝ 1 g D := hB.smul (hF.mono hDF)
  have hgc : ContDiffOn ℝ 1 (fun z : E => g (planeCoordinates.symm z)) U :=
    hg.comp planeCoordinates.symm.contDiff.contDiffOn (fun _ hz => hz)
  have hP : Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1 U P :=
    (D04.crOn_iff_contDiffOn 1 U P hUne).mpr
      (Complex.reCLM.contDiff.comp_contDiffOn hgc)
  have hQ : Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1 U Q :=
    (D04.crOn_iff_contDiffOn 1 U Q hUne).mpr
      (Complex.imCLM.contDiff.comp_contDiffOn hgc)
  have ht : ∀ p : frontier W,
      P p * Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hW p 0 +
      Q p * Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hW p 1 = 0 := by
    intro p
    have hpV : planeCoordinates.symm p ∈ frontier V := by
      exact (Set.ext_iff.mp hWf p.val).mp p.property
    rw [hVf] at hpV
    obtain ⟨s, hs⟩ := hpV
    obtain ⟨t, ht⟩ := Ch15.CircleLift.quotientMap_surjective s
    have hγt : realLift γ t = planeCoordinates.symm p := by
      change γ (q t) = _
      have ht' : q t = s := ht
      exact (congrArg γ ht').trans hs
    let α : ℝ → E := fun r => planeCoordinates (realLift γ r)
    have hα : ∀ r, α r ∈ frontier W := by
      intro r
      rw [hWf]
      change planeCoordinates.symm (planeCoordinates (realLift γ r)) ∈ frontier V
      rw [planeCoordinates.symm_apply_apply, hVf]
      exact ⟨q r, rfl⟩
    have hαt : α t = p := by simp [α, hγt]
    have hαd : HasDerivAt α (T • planeCoordinates (F.eval (realLift γ t))) t := by
      have hh := planeCoordinates.hasFDerivAt.comp_hasDerivAt t (hγderiv t)
      change HasDerivAt α (planeCoordinates (T • F.eval (realLift γ t))) t at hh
      rwa [map_smul] at hh
    have ho := GreenFlux.normal_orthogonal_of_boundary_curve hW α t _ hαd hα
    have hpeq : (⟨α t, hα t⟩ : frontier W) = p := Subtype.ext hαt
    rw [hpeq, hγt, real_inner_smul_right] at ho
    have ho0 : inner ℝ
        (Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hW p)
        (planeCoordinates (F.eval (planeCoordinates.symm p))) = 0 :=
      (mul_eq_zero.mp ho).resolve_left (ne_of_gt hT)
    have hoB : inner ℝ
        (Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hW p)
        (planeCoordinates (g (planeCoordinates.symm p))) = 0 := by
      simp only [g, map_smul, real_inner_smul_right, ho0, mul_zero]
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      planeCoordinates, Complex.orthonormalBasisOneI_repr_apply, P, Q, mul_comm] using hoB
  have hdiv (z : E) (hz : z ∈ U) :
      Specs.D04.C12.GreenCirculationAndFlux.Model.divergenceDensity P Q z =
        divergence g (planeCoordinates.symm z) :=
    GreenFlux.divergence_coordinates g z
      (((hg _ hz).contDiffAt (hD.mem_nhds hz)).differentiableAt one_ne_zero)
  apply regular_domain_flux_contradiction W hW hWne U P Q hUne hWU hP hQ ht
  rcases hsign with hpos | hneg
  · exact Or.inl (fun z hz => (hdiv z hz).symm ▸ hpos _ hz)
  · exact Or.inr (fun z hz => (hdiv z hz).symm ▸ hneg _ hz)

/-- Nonconstant allowed trajectories have no self-intersections, even when
their actual maximal interval is not known to be complete. -/
theorem dulac_orbit_injective : Specs.D13Unified.Ch13.Dulac.DulacOrbitInjective := by
  intro F hF D hD hsc hDF B hB hsign x hx htrace hn a ha b hb he
  by_contra hab
  exact bendixson_dulac F hF D hD hsc hDF B hB hsign x hx htrace hn
    (Ch11.Orbits.self_intersection_least_period F hF x hx hn a ha b hb hab he)

/-- The choice B=1 yields Bendixson's criterion. -/
theorem bendixson : Specs.D13Unified.Ch13.Dulac.Bendixson := by
  intro F hF D hD hsc hDF hsign x hx htrace hn
  apply bendixson_dulac F hF D hD hsc hDF (fun _ => 1) contDiffOn_const
    (by simpa only [one_smul] using hsign) x hx htrace hn

end D13Unified.Ch13.Dulac
