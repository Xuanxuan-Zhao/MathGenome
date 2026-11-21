import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.TrappingLimit

/-! The nested compact-set argument for the Chapter 18 trapping construction.
For the reverse image inclusion we intersect compact fibers of F. This does
not require that F be injective, or that X be compact or complete. -/
namespace D13Unified.Ch18.TrappingLimit

universe u
open Set Filter
open scoped Topology
open D13Unified.Ch15.DiscreteDefinitions

/-- The intersection of all forward images, including time zero. -/
abbrev trappingLimit : Specs.D13Unified.Ch18.TrappingLimit.trappingLimitType.{u} :=
  Specs.D13Unified.Ch18.TrappingLimit.trappingLimit

variable {X : Type u} {F : X → X} {K : Set X}

private lemma image_iterate_succ (n : ℕ) :
    iterate F (n + 1) '' K = F '' (iterate F n '' K) := by
  rw [iterate_succ, Set.image_comp]

private lemma iterate_images_antitone (hK : F '' K ⊆ K) :
    Antitone (fun n : ℕ => iterate F n '' K) := by
  apply antitone_nat_of_succ_le
  intro n
  change F^[n + 1] '' K ⊆ F^[n] '' K
  rw [Function.iterate_succ, Set.image_comp]
  exact Set.image_mono hK

private lemma iterate_images_compact [MetricSpace X] (hF : Continuous F) (hK : IsCompact K) (n : ℕ) :
    IsCompact (iterate F n '' K) :=
  hK.image (hF.iterate n)

/-- The compact trapping limit is nonempty, compact, invariant in both
image directions, and uniformly approached by all forward images of K. -/
theorem compact_trapping_limit :
    ∀ {X : Type u} [MetricSpace X] (F : X → X) (K : Set X),
      Continuous F → IsCompact K → K.Nonempty → F '' K ⊆ interior K →
      (trappingLimit F K).Nonempty ∧ IsCompact (trappingLimit F K) ∧
        Invariant F (trappingLimit F K) ∧
        ∀ V ∈ 𝓝ˢ (trappingLimit F K),
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n → iterate F n '' K ⊆ V := by
  intro X _ F K hF hK hne htrap
  have hFK : F '' K ⊆ K := htrap.trans interior_subset
  have hanti := iterate_images_antitone hFK
  have hcp := iterate_images_compact hF hK
  have hclosed : ∀ n : ℕ, IsClosed (iterate F n '' K) := fun n => (hcp n).isClosed
  have hstep : ∀ n : ℕ, iterate F (n + 1) '' K ⊆ iterate F n '' K :=
    fun n => hanti (Nat.le_succ n)
  have hnonempty : (trappingLimit F K).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hstep
      (fun n => hne.image (iterate F n)) (hcp 0) hclosed
  have hcompact : IsCompact (trappingLimit F K) := by
    apply (hcp 0).of_isClosed_subset (isClosed_iInter hclosed)
    exact iInter_subset _ 0
  have hinvariant : Invariant F (trappingLimit F K) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      apply mem_iInter.mpr
      intro n
      apply hstep n
      rw [image_iterate_succ]
      exact ⟨x, mem_iInter.mp hx n, rfl⟩
    · intro y hy
      -- Every level has a preimage of y, but the preimages may differ.
      -- Compactness supplies a single preimage lying in every level.
      let C : ℕ → Set X := fun n => (iterate F n '' K) ∩ F ⁻¹' {y}
      have hCclosed : ∀ n : ℕ, IsClosed (C n) :=
        fun n => (hclosed n).inter (isClosed_singleton.preimage hF)
      have hCstep : ∀ n : ℕ, C (n + 1) ⊆ C n :=
        fun n x hx => ⟨hstep n hx.1, hx.2⟩
      have hCne : ∀ n : ℕ, (C n).Nonempty := by
        intro n
        have hyn : y ∈ F '' (iterate F n '' K) := by
          rw [← image_iterate_succ]
          exact mem_iInter.mp hy (n + 1)
        rcases hyn with ⟨x, hx, hxy⟩
        exact ⟨x, hx, hxy⟩
      obtain ⟨x, hx⟩ :=
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCstep hCne
          ((hcp 0).inter_right (isClosed_singleton.preimage hF)) hCclosed
      refine ⟨x, mem_iInter.mpr (fun n => (mem_iInter.mp hx n).1), ?_⟩
      exact (mem_iInter.mp hx 0).2
  refine ⟨hnonempty, hcompact, hinvariant, ?_⟩
  intro V hV
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact hanti.directed_ge hcp hV
  exact ⟨N, fun n hn => (hanti hn).trans hN⟩

end D13Unified.Ch18.TrappingLimit
