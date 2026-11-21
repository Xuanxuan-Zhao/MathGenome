import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts

/-! Shared solution concepts for the real ODE theory. See the independent Specs
for canonical interval, domain, field, and solution data types. -/

noncomputable section

open Set

namespace D13Unified

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Specs.D13Unified.Ch01.SolutionConcepts

/-- A solution with derivatives relative to its actual interval, including any
included endpoints. -/
def IsSolutionOn : solutionOnType (E := E) := solutionOnValue

/-- A C¹ solution on a specified nonempty open interval. -/
def IsClassicalSolutionOn : classicalSolutionOnType (E := E) := classicalSolutionOnValue

/-- The differential solution and its initial time and value. -/
def IsIVPOn : ivpOnType (E := E) := ivpOnValue

def IsClassicalIVPOn : classicalIVPOnType (E := E) := classicalIVPOnValue

def IsCompactSolutionOn : compactSolutionOnType (E := E) := compactSolutionOnValue

/-- `Extends x y` means that `y` is an extension of `x`. -/
def Extends {F : ODE E} : extensionType F := extensionValue

def IsMaximal {F : ODE E} : maximalType F := maximalValue

def IsGlobal {F : ODE E} : globalType F := globalValue

def Solution.restrict {F : ODE E} : restrictType F := restrictValue

def IntervalSolution.restrict {F : ODE E} : intervalRestrictType F := intervalRestrictValue

namespace TimeInterval

/-- The closed interval `[a,b]`, with nonemptiness explicitly justified. -/
def closed (a b : ℝ) (hab : a ≤ b) : TimeInterval :=
  ⟨Icc a b, ⟨a, le_rfl, hab⟩, ordConnected_Icc⟩

end TimeInterval

namespace OpenTimeInterval

def whole : OpenTimeInterval :=
  ⟨⟨univ, Set.univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩

def bounded (a b : ℝ) (hab : a < b) : OpenTimeInterval :=
  ⟨⟨Ioo a b, nonempty_Ioo.mpr hab, ordConnected_Ioo⟩, isOpen_Ioo⟩

def rightRay (a : ℝ) : OpenTimeInterval :=
  ⟨⟨Ioi a, nonempty_Ioi, ordConnected_Ioi⟩, isOpen_Ioi⟩

def leftRay (b : ℝ) : OpenTimeInterval :=
  ⟨⟨Iio b, nonempty_Iio, ordConnected_Iio⟩, isOpen_Iio⟩

end OpenTimeInterval

namespace ODE

variable (F : ODE E)

@[simp] theorem eval_of_mem {t : ℝ} {x : E} (h : (t, x) ∈ F.domain) :
    F.eval t x = F.field ⟨(t, x), h⟩ := by
  classical
  exact dite_eq_left h

/-- The evaluation convention preserves exactly the given continuity on `U`. -/
theorem continuousOn_eval : ContinuousOn (fun p : ℝ × E => F.eval p.1 p.2) F.domain := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert F.continuous_field using 1
  funext p
  exact F.eval_of_mem p.property

end ODE

/-- Initial data really belong to the prescribed time-state domain. -/
theorem IsIVPOn.initial_mem {F : ODE E} {I : TimeInterval} {x : ℝ → E}
    {s : ℝ} {ξ : E} (h : IsIVPOn F I x s ξ) : (s, ξ) ∈ F.domain := by
  have hgraph := h.1.2.1 s h.2.1
  simpa only [h.2.2] using hgraph

theorem IsClassicalIVPOn.initial_mem {F : ODE E} {I : OpenTimeInterval} {x : ℝ → E}
    {s : ℝ} {ξ : E} (h : IsClassicalIVPOn F I x s ξ) : (s, ξ) ∈ F.domain := by
  have hgraph := h.1.2.1 s h.2.1
  simpa only [h.2.2] using hgraph

/-- Compact solutions are an instance of the common interval predicate. -/
theorem compactSolutionOn_iff {F : ODE E} {a b : ℝ} (hab : a ≤ b) (x : ℝ → E) :
    IsCompactSolutionOn F a b x ↔ IsSolutionOn F (TimeInterval.closed a b hab) x := by
  exact ⟨fun h => h.2, fun h => ⟨hab, h⟩⟩

theorem compact_endpoint_derivatives : compactEndpointDerivatives (E := E) := by
  intro F a b hab x h
  constructor
  · simpa only [HasDerivWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] using
      h.2.2.2 a ⟨le_rfl, hab.le⟩
  · simpa only [HasDerivWithinAt, nhdsWithin_Icc_eq_nhdsLE hab] using
      h.2.2.2 b ⟨hab.le, le_rfl⟩

theorem solutionOn_congr : representativeIndependence (E := E) := by
  intro F I x y hxy
  have forward : ∀ (x y : ℝ → E), EqOn x y I.carrier →
      solutionOnValue F I x → solutionOnValue F I y := by
    intro x y hxy h
    refine ⟨h.1.congr hxy.symm, ?_, ?_⟩
    · intro t ht
      simpa only [← hxy ht] using h.2.1 t ht
    · intro t ht
      have hd := (h.2.2 t ht).congr_of_mem hxy.symm ht
      simpa only [hxy ht] using hd
  exact ⟨forward x y hxy, forward y x hxy.symm⟩

theorem classical_iff_solutionOn : classicalIffSolutionOn (E := E) := by
  intro F I x
  constructor
  · intro h
    exact ⟨h.1.continuousOn, h.2.1, fun t ht => (h.2.2 t ht).hasDerivWithinAt⟩
  · intro h
    have hd : ∀ t ∈ I.carrier, HasDerivAt x (F.eval t (x t)) t :=
      fun t ht => (h.2.2 t ht).hasDerivAt (I.isOpen.mem_nhds ht)
    refine ⟨?_, h.2.1, hd⟩
    rw [contDiffOn_one_iff_derivWithin I.isOpen.uniqueDiffOn]
    refine ⟨fun t ht => (h.2.2 t ht).differentiableWithinAt, ?_⟩
    have hv : ContinuousOn (fun t => F.eval t (x t)) I.carrier :=
      F.continuousOn_eval.comp (continuousOn_id.prodMk h.1) h.2.1
    apply hv.congr
    intro t ht
    exact (h.2.2 t ht).derivWithin (I.isOpen.uniqueDiffOn t ht)

/-- Restricting does not change any value in the smaller actual domain. -/
theorem Solution.restrict_value {F : ODE E} (x : Solution F) (J : OpenTimeInterval)
    (hJ : J.carrier ⊆ x.interval.carrier) (t : J.carrier) :
    (x.restrict J hJ).value t = x.value ⟨t, hJ t.property⟩ := rfl

theorem Solution.restrict_extends {F : ODE E} (x : Solution F) (J : OpenTimeInterval)
    (hJ : J.carrier ⊆ x.interval.carrier) : Extends (x.restrict J hJ) x :=
  ⟨hJ, fun _ _ => rfl⟩

theorem global_isMaximal {F : ODE E} (x : Solution F) (h : IsGlobal x) : IsMaximal x := by
  rintro ⟨y, _, hstrict⟩
  exact hstrict.2 (by rw [h]; exact subset_univ _)

theorem norm_independence : normIndependence.{u, v} (E := E) := by
  intro G _ _ _ _ e I x v
  let L := e.toContinuousLinearEquiv
  have hc : ContinuousOn (fun t => e (x t)) I ↔ ContinuousOn x I := by
    constructor
    · intro h
      simpa [L, Function.comp_def] using L.symm.continuous.comp_continuousOn h
    · intro h
      exact L.continuous.comp_continuousOn h
  have hC : ContDiffOn ℝ 1 (fun t => e (x t)) I ↔ ContDiffOn ℝ 1 x I := by
    constructor
    · intro h
      simpa [L, Function.comp_def] using h.continuousLinearMap_comp L.symm.toContinuousLinearMap
    · intro h
      exact h.continuousLinearMap_comp L.toContinuousLinearMap
  refine ⟨hc, hC, ?_, ?_⟩
  · constructor
    · intro h t ht
      simpa [L, Function.comp_def] using L.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (h t ht)
    · intro h t ht
      exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (h t ht)
  · constructor
    · intro h t ht
      simpa [L, Function.comp_def] using L.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (h t ht)
    · intro h t ht
      exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (h t ht)

namespace ODE

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]

@[simp] theorem transport_eval (F : ODE E) (e : E ≃L[ℝ] G) (t : ℝ) (x : E) :
    (F.transport e).eval t (e x) = e (F.eval t x) := by
  classical
  by_cases h : (t, x) ∈ F.domain
  · simp [ODE.eval, ODE.transport, h]
  · simp [ODE.eval, ODE.transport, h]

end ODE

/-- The endpoint-aware differential predicate is unchanged by a change of
finite-dimensional normed realization. This also transports graph membership. -/
theorem solutionOn_transport_iff {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    (e : E ≃ₗ[ℝ] G) (F : ODE E) (I : TimeInterval) (x : ℝ → E) :
    IsSolutionOn (F.transport e.toContinuousLinearEquiv) I (fun t => e (x t)) ↔
      IsSolutionOn F I x := by
  have h := norm_independence e I.carrier x (fun t => F.eval t (x t))
  have heval (t : ℝ) : (F.transport e.toContinuousLinearEquiv).eval t (e (x t)) =
      e (F.eval t (x t)) := F.transport_eval e.toContinuousLinearEquiv t (x t)
  constructor
  · rintro ⟨hc, hg, hd⟩
    refine ⟨h.1.mp hc, ?_, h.2.2.1.mp ?_⟩
    · intro t ht
      simpa [ODE.transport] using hg t ht
    · simpa only [heval] using hd
  · rintro ⟨hc, hg, hd⟩
    refine ⟨h.1.mpr hc, ?_, ?_⟩
    · intro t ht
      simpa [ODE.transport] using hg t ht
    · simpa only [heval] using h.2.2.1.mpr hd

theorem classicalSolutionOn_transport_iff
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    (e : E ≃ₗ[ℝ] G) (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E) :
    IsClassicalSolutionOn (F.transport e.toContinuousLinearEquiv) I (fun t => e (x t)) ↔
      IsClassicalSolutionOn F I x := by
  exact (classical_iff_solutionOn _ _ _).trans
    ((solutionOn_transport_iff e F I.toTimeInterval x).trans
      (classical_iff_solutionOn _ _ _).symm)

theorem norm_independent_solutions : normIndependentSolutions.{u, v} (E := E) := by
  intro G _ _ _ _ e F I s ξ
  have h : ∀ x : ℝ → E,
      classicalIVPOnValue (F.transport e.toContinuousLinearEquiv) I
        (fun t => e (x t)) s (e ξ) ↔ classicalIVPOnValue F I x s ξ := by
    intro x
    change (_ ∧ s ∈ I.carrier ∧ e (x s) = e ξ) ↔
      (_ ∧ s ∈ I.carrier ∧ x s = ξ)
    rw [e.injective.eq_iff]
    exact and_congr_left fun _ => classicalSolutionOn_transport_iff e F I x
  refine ⟨h, ?_⟩
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun t => e.symm (y t), (h _).mp ?_⟩
    simpa only [e.apply_symm_apply] using hy
  · rintro ⟨x, hx⟩
    exact ⟨fun t => e (x t), (h x).mpr hx⟩

end D13Unified
