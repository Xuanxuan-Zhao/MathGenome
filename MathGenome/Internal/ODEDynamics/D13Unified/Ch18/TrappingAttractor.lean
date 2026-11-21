import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.TrappingLimit
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.AttractorDefinition
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.TrappingAttractor

/-! The compact trapping construction, including stability separately from
uniform attraction and the open preimage union in the basin. -/
namespace D13Unified.Ch18.TrappingAttractor

universe u
open Set Filter
open scoped Topology
open D13Unified.Ch15.DiscreteDefinitions
open D13Unified.Ch18.TrappingLimit
open D13Unified.Ch18.AttractorDefinition

variable {X : Type u} [MetricSpace X] {F : X → X} {K A : Set X}

/-- Uniform eventual inclusion in every set neighborhood implies distance
convergence for each orbit starting in K. -/
lemma approachesSet_of_uniform_images (hA : A.Nonempty)
    (htail : ∀ V ∈ 𝓝ˢ A, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → iterate F n '' K ⊆ V)
    {x : X} (hx : x ∈ K) : ApproachesSet F A x := by
  apply (approachesSet_iff_dist F A hA x).mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let V : Set X := {y | Metric.infDist y A < ε}
  have hV : IsOpen V := isOpen_lt (Metric.continuous_infDist_pt A) continuous_const
  have hAV : A ⊆ V := by
    intro y hy
    change Metric.infDist y A < ε
    simpa only [Metric.infDist_zero_of_mem hy] using hε
  obtain ⟨N, hN⟩ := htail V (hV.mem_nhdsSet.mpr hAV)
  refine ⟨N, fun n hn => ?_⟩
  have hdist : Metric.infDist (F^[n] x) A < ε := hN n hn ⟨x, hx, rfl⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] using hdist

/-- The initial finite segment is controlled by continuity; the uniform
image tail then controls all later times. -/
lemma setLyapunovStable_of_uniform_images (hF : Continuous F)
    (hAK : A ⊆ interior K) (hFA : MapsTo F A A)
    (htail : ∀ V ∈ 𝓝ˢ A, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → iterate F n '' K ⊆ V) :
    SetLyapunovStable F A := by
  intro V hV
  obtain ⟨W, hW, hAW, hWV⟩ := mem_nhdsSet_iff_exists.mp hV
  obtain ⟨N, hN⟩ := htail V hV
  let U : Set X := interior K ∩ ⋂ j : Fin N, (iterate F j.val) ⁻¹' W
  have hU : IsOpen U := isOpen_interior.inter
    (isOpen_iInter_of_finite (fun j => hW.preimage (hF.iterate j.val)))
  have hAU : A ⊆ U := by
    intro x hx
    exact ⟨hAK hx, mem_iInter.mpr (fun j => hAW (hFA.iterate j.val hx))⟩
  refine ⟨U, hU.mem_nhdsSet.mpr hAU, ?_⟩
  intro x hx n
  by_cases hn : n < N
  · exact hWV (mem_iInter.mp hx.2 ⟨n, hn⟩)
  · exact hN n (Nat.le_of_not_gt hn) ⟨x, interior_subset hx.1, rfl⟩

theorem compact_trapping_attractor :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (K : Set X),
      Continuous F → IsCompact K → K.Nonempty → F '' K ⊆ interior K →
      StableAttractor F (trappingLimit F K) ∧
        (∀ V ∈ 𝓝ˢ (trappingLimit F K),
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n → iterate F n '' K ⊆ V) ∧
        IsOpen (⋃ n : ℕ, (iterate F n) ⁻¹' interior K) ∧
        (⋃ n : ℕ, (iterate F n) ⁻¹' interior K) ⊆ basin F (trappingLimit F K) := by
  intro X _ F K hF hK hne htrap
  obtain ⟨hAne, hAc, hAi, htail⟩ := compact_trapping_limit F K hF hK hne htrap
  have hAK : trappingLimit F K ⊆ interior K := by
    intro x hx
    apply htrap
    have hx1 := mem_iInter.mp hx 1
    simpa only [iterate, Specs.D13Unified.Ch15.DiscreteDefinitions.iterate,
      Function.iterate_one] using hx1
  have hFA : MapsTo F (trappingLimit F K) (trappingLimit F K) := by
    intro x hx
    rw [← hAi]
    exact ⟨x, hx, rfl⟩
  have hstable := setLyapunovStable_of_uniform_images hF hAK hFA htail
  have hattract : AttractsSetNeighborhood F (trappingLimit F K) :=
    ⟨interior K, isOpen_interior.mem_nhdsSet.mpr hAK,
      fun x hx => approachesSet_of_uniform_images hAne htail (interior_subset hx)⟩
  refine ⟨⟨hF, hAne, hAc, hAi, hstable, hattract⟩, htail,
    isOpen_iUnion (fun n => isOpen_interior.preimage (hF.iterate n)), ?_⟩
  intro x hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  have hconv := approachesSet_of_uniform_images hAne htail (interior_subset hm)
  change Tendsto (fun n : ℕ => Metric.infEDist (F^[n] (F^[m] x)) (trappingLimit F K))
    atTop (𝓝 0) at hconv
  change ApproachesSet F (trappingLimit F K) x
  change Tendsto (fun n : ℕ => Metric.infEDist (F^[n] x) (trappingLimit F K))
    atTop (𝓝 0)
  apply (tendsto_add_atTop_iff_nat m).mp
  simpa only [Function.iterate_add_apply] using hconv

end D13Unified.Ch18.TrappingAttractor
