import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.IntermediateValues
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ClosedPreimage
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.IntervalImages
import Mathlib.Topology.Order.IntermediateValue

/-!
# Intervals and connectedness

K03.03.interval_images, paper.tex:555–570. A separation uses open subsets
of the induced domain subtype. In the manuscript convention the empty set
is connected; we bridge this definition to Mathlib's `IsPreconnected`.
Mathlib's real order-topology theorem then identifies it with the
between-points property. Its proof uses completeness for closed segments
and unions of those segments; continuous images use open preimages.
The continuity hypotheses below are the upstream epsilon–delta definition,
tested only on the stated domain, including any included endpoints.
-/
namespace SingleVariableAnalysis

universe u v

/-- Absence of a separation into two nonempty relatively open pieces. -/
def RelativeConnected {X : Type u} [MetricSpace X] (E : Set X) : Prop :=
  ¬ ∃ U V : Set E,
    IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint U V ∧ U ∪ V = Set.univ

/-- Every point between two members belongs to the real set. -/
def RealInterval (I : Set ℝ) : Prop :=
  ∀ ⦃a : ℝ⦄, a ∈ I → ∀ ⦃b : ℝ⦄, b ∈ I →
    ∀ ⦃x : ℝ⦄, a ≤ x → x ≤ b → x ∈ I

theorem relativeConnected_iff_isPreconnected
    {X : Type u} [MetricSpace X] (E : Set X) :
    RelativeConnected E ↔ IsPreconnected E := by
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_univ]
  constructor
  · intro h U V hU hV hcover hUne hVne
    by_contra hdis
    apply h
    refine ⟨U, V, hU, hV, ?_, ?_, ?_, ?_⟩
    · exact hUne.mono Set.inter_subset_right
    · exact hVne.mono Set.inter_subset_right
    · exact Set.disjoint_left.mpr (fun x hxU hxV => hdis ⟨x, Set.mem_univ x, hxU, hxV⟩)
    · exact Set.eq_univ_of_forall (fun x => hcover (Set.mem_univ x))
  · rintro h ⟨U, V, hU, hV, ⟨x, hx⟩, ⟨y, hy⟩, hdis, hcover⟩
    obtain ⟨z, _, hzU, hzV⟩ := h U V hU hV
      (by rw [hcover]) ⟨x, Set.mem_univ x, hx⟩ ⟨y, Set.mem_univ y, hy⟩
    exact Set.disjoint_left.mp hdis hzU hzV

theorem realInterval_iff_ordConnected (I : Set ℝ) :
    RealInterval I ↔ Set.OrdConnected I := by
  constructor
  · exact fun h => ⟨fun _ ha _ hb _ hx => h ha hb hx.1 hx.2⟩
  · exact fun h _ ha _ hb _ hax hxb => h.out ha hb ⟨hax, hxb⟩

/-- A real set is connected exactly when it is an interval, including ∅. -/
theorem real_connected_iff_interval (I : Set ℝ) :
    RelativeConnected I ↔ RealInterval I := by
  rw [relativeConnected_iff_isPreconnected, realInterval_iff_ordConnected]
  exact isPreconnected_iff_ordConnected

/-- Only continuity on E is needed for its image to remain connected. -/
theorem relativeConnected_image
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (hE : RelativeConnected E)
    (hf : RelativeContinuous f E) : RelativeConnected (f '' E) := by
  apply (relativeConnected_iff_isPreconnected _).mpr
  exact ((relativeConnected_iff_isPreconnected E).mp hE).image f
    (fun x hx => (relativeContinuousAt_within_iff f E x).mp (hf x hx))

/-- Continuous images of whole connected metric spaces are connected. -/
theorem connectedSpace_range
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hX : RelativeConnected (Set.univ : Set X))
    (hf : RelativeContinuous f Set.univ) : RelativeConnected (Set.range f) := by
  simpa only [Set.image_univ] using relativeConnected_image f Set.univ hX hf

theorem continuous_real_interval_image (f : ℝ → ℝ) (I : Set ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I) : RealInterval (f '' I) :=
  (real_connected_iff_interval _).mp
    (relativeConnected_image f I ((real_connected_iff_interval I).mpr hI) hf)

/-- Intrinsic functions on an interval need no choice of values outside it. -/
theorem continuous_real_interval_range (I : Set ℝ) (f : I → ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f Set.univ) :
    RealInterval (Set.range f) := by
  have hp : IsPreconnected I :=
    (relativeConnected_iff_isPreconnected I).mp ((real_connected_iff_interval I).mpr hI)
  have hu : RelativeConnected (Set.univ : Set I) :=
    (relativeConnected_iff_isPreconnected _).mpr
      ((preconnectedSpace_iff_univ).mp (isPreconnected_iff_preconnectedSpace.mp hp))
  exact (real_connected_iff_interval _).mp (connectedSpace_range f hu hf)

theorem relativeConnected_empty {X : Type u} [MetricSpace X] :
    RelativeConnected (∅ : Set X) :=
  (relativeConnected_iff_isPreconnected _).mpr isPreconnected_empty

theorem relativeConnected_singleton {X : Type u} [MetricSpace X] (x : X) :
    RelativeConnected ({x} : Set X) :=
  (relativeConnected_iff_isPreconnected _).mpr isPreconnected_singleton

theorem realInterval_empty : RealInterval ∅ :=
  (real_connected_iff_interval _).mp relativeConnected_empty

theorem realInterval_singleton (x : ℝ) : RealInterval {x} :=
  (real_connected_iff_interval _).mp (relativeConnected_singleton x)

end SingleVariableAnalysis
