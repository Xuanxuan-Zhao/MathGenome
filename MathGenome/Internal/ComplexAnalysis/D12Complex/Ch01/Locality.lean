import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Locality

/-!
Restriction and compatible gluing for weakly holomorphic functions.
Only pointwise differentiability and equality on open neighborhoods are used.
-/

open scoped Topology

namespace D12Complex

theorem holomorphicOn_restrict (Ω U : Set ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (hU : IsOpen U) (hsub : U ⊆ Ω) :
    HolomorphicOn U f :=
  ⟨hU, fun a ha => hf.2 a (hsub ha)⟩

/-- Glue an arbitrary compatible open cover, with uniqueness on the covered set. -/
theorem holomorphicOn_glue {ι : Type u} (Ω : Set ℂ) (U : ι → Set ℂ)
    (f : ι → ℂ → ℂ) (hcover : (⋃ i, U i) = Ω)
    (hf : ∀ i, HolomorphicOn (U i) (f i))
    (hcompat : ∀ i j, Set.EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ F : ℂ → ℂ, HolomorphicOn Ω F ∧
      (∀ i, Set.EqOn F (f i) (U i)) ∧
      ∀ G : ℂ → ℂ, (∀ i, Set.EqOn G (f i) (U i)) → Set.EqOn G F Ω := by
  classical
  let F : ℂ → ℂ := fun z =>
    if hz : ∃ i, z ∈ U i then f (Classical.choose hz) z else 0
  have hF : ∀ i, Set.EqOn F (f i) (U i) := by
    intro i z hz
    have hex : ∃ j, z ∈ U j := ⟨i, hz⟩
    dsimp only [F]
    rw [dite_eq_left hex]
    exact hcompat (Classical.choose hex) i ⟨Classical.choose_spec hex, hz⟩
  have hΩ : IsOpen Ω := by
    rw [← hcover]
    exact isOpen_iUnion fun i => (hf i).1
  refine ⟨F, ⟨hΩ, ?_⟩, hF, ?_⟩
  · intro a ha
    have ha' : a ∈ ⋃ i, U i := hcover.symm ▸ ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha'
    apply ((hf i).2 a hi).congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem ((hf i).1.mem_nhds hi) (hF i)
  · intro G hG z hz
    have hz' : z ∈ ⋃ i, U i := hcover.symm ▸ hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz'
    exact (hG i hi).trans (hF i hi).symm

end D12Complex
