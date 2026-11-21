import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.AttractorDefinition
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions

/-! Stable attractors and their basins, as in Definition d13:18:attractor-definition. -/
namespace D13Unified.Ch18.AttractorDefinition

universe u
open Filter Set
open scoped Topology
open D13Unified.Ch15.DiscreteDefinitions

/-- Forward iterates approach a set in distance. -/
abbrev ApproachesSet : Specs.D13Unified.Ch18.AttractorDefinition.ApproachesSetType.{u} :=
  Specs.D13Unified.Ch18.AttractorDefinition.ApproachesSet

/-- Lyapunov stability using neighborhoods of the whole set. -/
abbrev SetLyapunovStable :
    Specs.D13Unified.Ch18.AttractorDefinition.SetLyapunovStableType.{u} :=
  Specs.D13Unified.Ch18.AttractorDefinition.SetLyapunovStable

/-- Every initial point in one neighborhood approaches the set. -/
abbrev AttractsSetNeighborhood :
    Specs.D13Unified.Ch18.AttractorDefinition.AttractsSetNeighborhoodType.{u} :=
  Specs.D13Unified.Ch18.AttractorDefinition.AttractsSetNeighborhood

/-- The basin consists of all points approaching the set under forward iteration. -/
abbrev basin : Specs.D13Unified.Ch18.AttractorDefinition.basinType.{u} :=
  Specs.D13Unified.Ch18.AttractorDefinition.basin

/-- A nonempty compact invariant stable set attracting a neighborhood,
for a continuous self-map of a metric space. -/
abbrev StableAttractor : Specs.D13Unified.Ch18.AttractorDefinition.StableAttractorType.{u} :=
  Specs.D13Unified.Ch18.AttractorDefinition.StableAttractor

theorem approachesSet_iff_dist :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X) (hA : A.Nonempty) (x : X),
      ApproachesSet F A x ↔
        Tendsto (fun n : ℕ => Metric.infDist (F^[n] x) A) atTop (𝓝 0) := by
  intro X _ F A hA x
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n : ℕ => Metric.infEDist_ne_top (x := F^[n] x) hA)).symm

theorem setLyapunovStable_iff_open_neighborhoods :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X),
      SetLyapunovStable F A ↔
        ∀ V : Set X, IsOpen V → A ⊆ V →
          ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ ∀ x ∈ U, ∀ n : ℕ, F^[n] x ∈ V := by
  intro X _ F A
  constructor
  · intro h V hV hAV
    obtain ⟨U, hU, horbit⟩ := h V (hV.mem_nhdsSet.mpr hAV)
    obtain ⟨W, hW, hAW, hWU⟩ := mem_nhdsSet_iff_exists.mp hU
    exact ⟨W, hW, hAW, fun x hx n => horbit x (hWU hx) n⟩
  · intro h V hV
    obtain ⟨W, hW, hAW, hWV⟩ := mem_nhdsSet_iff_exists.mp hV
    obtain ⟨U, hU, hAU, horbit⟩ := h W hW hAW
    exact ⟨U, hU.mem_nhdsSet.mpr hAU, fun x hx n => hWV (horbit x hx n)⟩

theorem attractsSetNeighborhood_iff_open_dist :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X) (hA : A.Nonempty),
      AttractsSetNeighborhood F A ↔
        ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ ∀ x ∈ U,
          Tendsto (fun n : ℕ => Metric.infDist (F^[n] x) A) atTop (𝓝 0) := by
  intro X _ F A hA
  constructor
  · rintro ⟨U, hU, horbit⟩
    obtain ⟨W, hW, hAW, hWU⟩ := mem_nhdsSet_iff_exists.mp hU
    exact ⟨W, hW, hAW, fun x hx => (approachesSet_iff_dist F A hA x).mp
      (horbit x (hWU hx))⟩
  · rintro ⟨U, hU, hAU, horbit⟩
    exact ⟨U, hU.mem_nhdsSet.mpr hAU, fun x hx =>
      (approachesSet_iff_dist F A hA x).mpr (horbit x hx)⟩

theorem mem_basin_iff_dist :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X) (hA : A.Nonempty) (x : X),
      x ∈ basin F A ↔
        Tendsto (fun n : ℕ => Metric.infDist (F^[n] x) A) atTop (𝓝 0) := by
  intro X _ F A hA x
  exact approachesSet_iff_dist F A hA x

theorem stableAttractor_iff :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X),
      StableAttractor F A ↔
        Continuous F ∧ A.Nonempty ∧ IsCompact A ∧ F '' A = A ∧
          SetLyapunovStable F A ∧ AttractsSetNeighborhood F A := by
  intro X _ F A
  rfl

theorem basin_mem_nhdsSet :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (A : Set X),
      StableAttractor F A → basin F A ∈ 𝓝ˢ A := by
  intro X _ F A h
  obtain ⟨U, hU, horbit⟩ := h.2.2.2.2.2
  exact Filter.mem_of_superset hU horbit

end D13Unified.Ch18.AttractorDefinition
