import MathGenome.Internal.MultivariableAnalysis.D04.C01.Compactness
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.CompactContinuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact

/-! Continuous maps on compact Euclidean sets. We use the shared bridges
from the ambient-open-cover and epsilon-delta definitions to the topology
and uniformity on the actual subtype domain. -/

namespace D04

theorem compact_image {n m : ℕ} (K : Set (E n)) (f : K → E m)
    (hK : Compact K) (hf : RelativeContinuous K f) : Compact (Set.range f) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp ((compact_iff_isCompact K).mp hK)
  exact (compact_iff_isCompact _).mpr
    (isCompact_range ((relativeContinuous_iff K f).mp hf))

theorem bounded_of_compact {n m : ℕ} (K : Set (E n)) (f : K → E m)
    (hK : Compact K) (hf : RelativeContinuous K f) :
    ∃ B : ℝ, ∀ x : K, ‖f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := ((compact_iff_closed_bounded _).mp (compact_image K f hK hf)).2
  exact ⟨B, fun x => hB (f x) ⟨x, rfl⟩⟩

theorem uniformContinuous_of_compact {n m : ℕ} (K : Set (E n)) (f : K → E m)
    (hK : Compact K) (hf : RelativeContinuous K f) : RelativeUniformContinuous K f := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp ((compact_iff_isCompact K).mp hK)
  exact (relativeUniformContinuous_iff K f).mpr
    (CompactSpace.uniformContinuous_of_continuous ((relativeContinuous_iff K f).mp hf))

theorem exists_min_max_of_compact {n : ℕ} (K : Set (E n)) (f : K → E 1)
    (hK : Compact K) (hf : RelativeContinuous K f) (hne : K.Nonempty) :
    ∃ x_min x_max : K, ∀ x : K,
      f x_min 0 ≤ f x 0 ∧ f x 0 ≤ f x_max 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp ((compact_iff_isCompact K).mp hK)
  have hc : Continuous (fun x : K => f x 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      ((relativeContinuous_iff K f).mp hf)
  obtain ⟨a, ha⟩ := hne
  have hu : (Set.univ : Set K).Nonempty := ⟨⟨a, ha⟩, Set.mem_univ _⟩
  obtain ⟨x_min, _, hmin⟩ := isCompact_univ.exists_isMinOn hu hc.continuousOn
  obtain ⟨x_max, _, hmax⟩ := isCompact_univ.exists_isMaxOn hu hc.continuousOn
  exact ⟨x_min, x_max, fun x => ⟨hmin (Set.mem_univ x), hmax (Set.mem_univ x)⟩⟩

end D04
