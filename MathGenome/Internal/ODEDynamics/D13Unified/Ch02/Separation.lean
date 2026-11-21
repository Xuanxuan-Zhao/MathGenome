import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.Separation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D13Unified.Separation

lemma hasDerivAt_primitive (d : Data) {u : ℝ} (hu : u ∈ d.J.carrier) :
    HasDerivAt (primitive d) (d.g u)⁻¹ u := by
  exact (hasDerivWithinAt_integral_on_interval d.J.ordConnected
    (d.continuous_g.inv₀ d.nonzero_g) d.mem_ξ hu).hasDerivAt (d.J.isOpen.mem_nhds hu)

lemma contDiffOn_primitive (d : Data) : ContDiffOn ℝ 1 (primitive d) d.J.carrier := by
  rw [contDiffOn_one_iff_derivWithin d.J.isOpen.uniqueDiffOn]
  refine ⟨fun u hu => (hasDerivAt_primitive d hu).differentiableAt.differentiableWithinAt, ?_⟩
  apply (d.continuous_g.inv₀ d.nonzero_g).congr
  intro u hu
  exact (hasDerivAt_primitive d hu).hasDerivWithinAt.derivWithin
    (d.J.isOpen.uniqueDiffOn u hu)

lemma sign_g (d : Data) :
    (∀ u ∈ d.J.carrier, 0 < d.g u) ∨ (∀ u ∈ d.J.carrier, d.g u < 0) := by
  have hconn := d.J.ordConnected.isPreconnected
  rcases lt_or_gt_of_ne (d.nonzero_g d.ξ d.mem_ξ) with hξ | hξ
  · right
    intro u hu
    by_contra hn
    obtain ⟨v, hv, hz⟩ := hconn.intermediate_value d.mem_ξ hu d.continuous_g
      (show (0 : ℝ) ∈ Icc (d.g d.ξ) (d.g u) from ⟨hξ.le, le_of_not_gt hn⟩)
    exact d.nonzero_g v hv hz
  · left
    intro u hu
    by_contra hn
    obtain ⟨v, hv, hz⟩ := hconn.intermediate_value hu d.mem_ξ d.continuous_g
      (show (0 : ℝ) ∈ Icc (d.g u) (d.g d.ξ) from ⟨le_of_not_gt hn, hξ.le⟩)
    exact d.nonzero_g v hv hz

lemma strictMonotone_primitive (d : Data) :
    StrictMonoOn (primitive d) d.J.carrier ∨ StrictAntiOn (primitive d) d.J.carrier := by
  rcases sign_g d with hp | hn
  · left
    apply strictMonoOn_of_deriv_pos d.J.ordConnected.convex (contDiffOn_primitive d).continuousOn
    intro u hu
    rw [(hasDerivAt_primitive d (interior_subset hu)).deriv]
    exact inv_pos.mpr (hp u (interior_subset hu))
  · right
    apply strictAntiOn_of_deriv_neg d.J.ordConnected.convex (contDiffOn_primitive d).continuousOn
    intro u hu
    rw [(hasDerivAt_primitive d (interior_subset hu)).deriv]
    exact inv_lt_zero.mpr (hn u (interior_subset hu))

lemma injOn_primitive (d : Data) : InjOn (primitive d) d.J.carrier :=
  (strictMonotone_primitive d).elim StrictMonoOn.injOn StrictAntiOn.injOn

lemma hasStrictDerivAt_primitive (d : Data) {u : ℝ} (hu : u ∈ d.J.carrier) :
    HasStrictDerivAt (primitive d) (d.g u)⁻¹ u :=
  ((contDiffOn_primitive d).contDiffAt (d.J.isOpen.mem_nhds hu)).hasStrictDerivAt'
    (hasDerivAt_primitive d hu) one_ne_zero

lemma isOpen_image (d : Data) : IsOpen (image d) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨u, hu, rfl⟩
  rw [← (hasStrictDerivAt_primitive d hu).map_nhds_eq (inv_ne_zero (d.nonzero_g u hu))]
  exact Filter.image_mem_map (d.J.isOpen.mem_nhds hu)

lemma inverse_left (d : Data) : LeftInvOn (inverse d) (primitive d) d.J.carrier :=
  (injOn_primitive d).leftInvOn_invFunOn

lemma inverse_right (d : Data) : RightInvOn (inverse d) (primitive d) (image d) :=
  (surjOn_image (primitive d) d.J.carrier).rightInvOn_invFunOn

lemma inverse_mem (d : Data) : MapsTo (inverse d) (image d) d.J.carrier :=
  (surjOn_image (primitive d) d.J.carrier).mapsTo_invFunOn

lemma hasDerivAt_inverse (d : Data) {z : ℝ} (hz : z ∈ image d) :
    HasDerivAt (inverse d) (d.g (inverse d z)) z := by
  obtain ⟨u, hu, rfl⟩ := hz
  have h := (hasStrictDerivAt_primitive d hu).to_local_left_inverse
    (inv_ne_zero (d.nonzero_g u hu))
    (Filter.eventually_of_mem (d.J.isOpen.mem_nhds hu) (fun v hv => inverse_left d hv))
  simpa only [inv_inv, inverse_left d hu] using h.hasDerivAt

lemma contDiffOn_inverse (d : Data) : ContDiffOn ℝ 1 (inverse d) (image d) := by
  have hc : ContinuousOn (inverse d) (image d) :=
    fun z hz => (hasDerivAt_inverse d hz).continuousAt.continuousWithinAt
  rw [contDiffOn_one_iff_derivWithin (isOpen_image d).uniqueDiffOn]
  refine ⟨fun z hz => (hasDerivAt_inverse d hz).differentiableAt.differentiableWithinAt, ?_⟩
  apply (d.continuous_g.comp hc (inverse_mem d)).congr
  intro z hz
  exact (hasDerivAt_inverse d hz).hasDerivWithinAt.derivWithin
    ((isOpen_image d).uniqueDiffOn z hz)

/-- The complete primitive and inverse assertion, with both monotonicity signs. -/
theorem primitive_properties : Specs.D13Unified.Ch02.Separation.primitiveExpected := by
  intro d
  exact ⟨contDiffOn_primitive d, fun _ => hasDerivAt_primitive d,
    strictMonotone_primitive d, isOpen_image d, inverse_mem d, inverse_left d,
    inverse_right d, contDiffOn_inverse d, fun _ => hasDerivAt_inverse d⟩

lemma hasDerivAt_timePrimitive (d : Data) {t : ℝ} (ht : t ∈ d.I.carrier) :
    HasDerivAt (timePrimitive d) (d.a t) t :=
  (hasDerivWithinAt_integral_on_interval d.I.ordConnected d.continuous_a d.mem_s ht).hasDerivAt
    (d.I.isOpen.mem_nhds ht)

lemma contDiffOn_timePrimitive (d : Data) :
    ContDiffOn ℝ 1 (timePrimitive d) d.I.carrier := by
  rw [contDiffOn_one_iff_derivWithin d.I.isOpen.uniqueDiffOn]
  refine ⟨fun t ht => (hasDerivAt_timePrimitive d ht).differentiableAt.differentiableWithinAt, ?_⟩
  apply d.continuous_a.congr
  intro t ht
  exact (hasDerivAt_timePrimitive d ht).hasDerivWithinAt.derivWithin
    (d.I.isOpen.uniqueDiffOn t ht)

@[simp] lemma primitive_initial (d : Data) : primitive d d.ξ = 0 := by
  simp [primitive]

@[simp] lemma timePrimitive_initial (d : Data) : timePrimitive d d.s = 0 := by
  simp [timePrimitive]

lemma isOpen_admissibleTimes (d : Data) : IsOpen (admissibleTimes d) :=
  (contDiffOn_timePrimitive d).continuousOn.isOpen_inter_preimage d.I.isOpen (isOpen_image d)

lemma mem_admissibleTimes (d : Data) : d.s ∈ admissibleTimes d := by
  refine ⟨d.mem_s, ?_⟩
  exact ⟨d.ξ, d.mem_ξ, by simp⟩

lemma mem_branch (d : Data) : d.s ∈ branch d :=
  mem_connectedComponentIn (mem_admissibleTimes d)

lemma branch_subset (d : Data) : branch d ⊆ admissibleTimes d :=
  connectedComponentIn_subset _ _

lemma isOpen_branch (d : Data) : IsOpen (branch d) :=
  (isOpen_admissibleTimes d).connectedComponentIn

/-- The formula's actual connected time domain. -/
def branchInterval (d : Data) : OpenTimeInterval where
  carrier := branch d
  nonempty := ⟨d.s, mem_branch d⟩
  ordConnected := isPreconnected_connectedComponentIn.ordConnected
  isOpen := isOpen_branch d

lemma formula_graph (d : Data) {t : ℝ} (ht : t ∈ branch d) :
    (t, formula d t) ∈ d.ode.domain :=
  ⟨(branch_subset d ht).1, inverse_mem d (branch_subset d ht).2⟩

lemma eval_ode (d : Data) {t u : ℝ} (ht : t ∈ d.I.carrier) (hu : u ∈ d.J.carrier) :
    d.ode.eval t u = d.a t * d.g u := by
  exact d.ode.eval_of_mem ⟨ht, hu⟩

lemma contDiffOn_formula (d : Data) : ContDiffOn ℝ 1 (formula d) (branch d) :=
  (contDiffOn_inverse d).comp
    ((contDiffOn_timePrimitive d).mono fun _ ht => (branch_subset d ht).1)
    (fun _ ht => (branch_subset d ht).2)

lemma hasDerivAt_formula (d : Data) {t : ℝ} (ht : t ∈ branch d) :
    HasDerivAt (formula d) (d.ode.eval t (formula d t)) t := by
  have h := (hasDerivAt_inverse d (branch_subset d ht).2).comp t
    (hasDerivAt_timePrimitive d (branch_subset d ht).1)
  rw [eval_ode d (branch_subset d ht).1 (formula_graph d ht).2]
  convert h using 1
  · rfl
  · exact mul_comm _ _

lemma formula_initial (d : Data) : formula d d.s = d.ξ := by
  have h := inverse_left d d.mem_ξ
  simpa only [formula, primitive_initial, timePrimitive_initial] using h

/-- This construction has no existence or uniqueness certificate as an input. -/
def branchSolution (d : Data) : Solution d.ode where
  interval := branchInterval d
  representative := formula d
  isSolution := ⟨contDiffOn_formula d, fun _ => formula_graph d, fun _ => hasDerivAt_formula d⟩

/-- Necessity of the separated integral identity for every solution through
these data; this uses only continuity of the coefficients. -/
lemma primitive_solution (d : Data) (y : Solution d.ode)
    (hs : d.s ∈ y.interval.carrier) (hξ : y.representative d.s = d.ξ)
    {t : ℝ} (ht : t ∈ y.interval.carrier) :
    primitive d (y.representative t) = timePrimitive d t := by
  have hI : y.interval.carrier ⊆ d.I.carrier := fun r hr => (y.isSolution.2.1 r hr).1
  have hJ : MapsTo y.representative y.interval.carrier d.J.carrier :=
    fun r hr => (y.isSolution.2.1 r hr).2
  have hd : ∀ r ∈ y.interval.carrier,
      HasDerivAt (fun u => primitive d (y.representative u)) (d.a r) r := by
    intro r hr
    have h := (hasDerivAt_primitive d (hJ hr)).comp r (y.isSolution.2.2 r hr)
    rw [eval_ode d (hI hr) (hJ hr)] at h
    convert h using 1
    · rfl
    · field_simp [d.nonzero_g _ (hJ hr)]
  have hi := integral_eq_sub_on_interval y.interval.ordConnected
    ((contDiffOn_primitive d).continuousOn.comp y.isSolution.1.continuousOn hJ)
    (d.continuous_a.mono hI) (fun r hr => (hd r hr).hasDerivWithinAt) hs ht
  simpa only [Function.comp_def, hξ, primitive_initial, sub_zero, timePrimitive] using hi.symm

lemma solution_subset_branch (d : Data) (y : Solution d.ode)
    (hs : d.s ∈ y.interval.carrier) (hξ : y.representative d.s = d.ξ) :
    y.interval.carrier ⊆ branch d := by
  apply y.interval.ordConnected.isPreconnected.subset_connectedComponentIn hs
  intro t ht
  refine ⟨(y.isSolution.2.1 t ht).1, y.representative t, (y.isSolution.2.1 t ht).2, ?_⟩
  exact primitive_solution d y hs hξ ht

lemma solution_eq_formula (d : Data) (y : Solution d.ode)
    (hs : d.s ∈ y.interval.carrier) (hξ : y.representative d.s = d.ξ) :
    EqOn (formula d) y.representative y.interval.carrier := by
  intro t ht
  change inverse d (timePrimitive d t) = y.representative t
  rw [← primitive_solution d y hs hξ ht]
  exact inverse_left d (y.isSolution.2.1 t ht).2

lemma branchSolution_extends (d : Data) (y : Solution d.ode)
    (hs : d.s ∈ y.interval.carrier) (hξ : y.representative d.s = d.ξ) :
    Extends y (branchSolution d) :=
  ⟨solution_subset_branch d y hs hξ, solution_eq_formula d y hs hξ⟩

lemma branchSolution_maximal (d : Data) : IsMaximal (branchSolution d) := by
  rintro ⟨y, hy, hstrict⟩
  have hs : d.s ∈ y.interval.carrier := hy.1 (mem_branch d)
  have hξ : y.representative d.s = d.ξ := (hy.2 (mem_branch d)).trans (formula_initial d)
  exact hstrict.not_subset (solution_subset_branch d y hs hξ)

/-- Full existence, restriction, and maximality assertion in the original rectangle. -/
theorem separation : Specs.D13Unified.Ch02.Separation.branchExpected := by
  intro d
  exact ⟨branchSolution d, rfl, fun _ _ => rfl, mem_branch d, formula_initial d,
    fun y hs hξ => branchSolution_extends d y hs hξ, branchSolution_maximal d⟩

/-- Zeros excluded by division still give the original constant IVP. -/
theorem equilibrium : Specs.D13Unified.Ch02.Separation.equilibriumExpected := by
  intro d c hc
  refine ⟨fun hmem => d.nonzero_g c hmem hc, ?_⟩
  intro F hgraph heval
  refine ⟨⟨contDiffOn_const, hgraph, ?_⟩, d.mem_s, rfl⟩
  intro t ht
  simpa only [heval t ht, hc, mul_zero] using hasDerivAt_const t c

end D13Unified.Separation
