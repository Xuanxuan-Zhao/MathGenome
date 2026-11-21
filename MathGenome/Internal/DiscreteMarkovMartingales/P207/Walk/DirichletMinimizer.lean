import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.DirichletMinimizer
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.BoundaryHarmonic

open scoped BigOperators
universe u
namespace P207.Markov
noncomputable section

namespace WeightedSpace
variable {S : Type u} [Fintype S] (π : ProbabilityLaw S) (hπ : ∀ x, 0 < π x)
  (P : StochasticMatrix S)

/-- Reversibility makes the bilinear energy symmetric. -/
theorem dirichlet_symm (hb : DetailedBalance P π) (f g : WeightedSpace π hπ) :
    dirichletForm π hπ P f g = dirichletForm π hπ P g f := by
  rw [dirichlet_identity π hπ P hb, dirichlet_identity π hπ P hb]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- A perturbation vanishing on the boundary is orthogonal to a harmonic function. -/
theorem dirichlet_boundary_orthogonal (B : Set S) (g : B → ℝ)
    (h w : WeightedSpace π hπ) (hh : IsBoundaryHarmonic P B g h)
    (hw : ∀ x ∈ B, w x = 0) : dirichletForm π hπ P w h = 0 := by
  change (∑ x, (π x).toReal * w x * (h x - ∑ y, realMatrix P x y * h y)) = 0
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hxB : x ∈ B
  · rw [hw x hxB]
    simp
  · rw [hh.2 x hxB, sub_self, mul_zero]

/-- The energy expansion at a boundary-harmonic function has no cross term. -/
theorem dirichlet_boundary_expansion (hb : DetailedBalance P π)
    (B : Set S) (g : B → ℝ) (h f : WeightedSpace π hπ)
    (hh : IsBoundaryHarmonic P B g h) (hf : ∀ x : B, f x = g x) :
    dirichletForm π hπ P f f = dirichletForm π hπ P h h +
      dirichletForm π hπ P (f - h) (f - h) := by
  let w := f - h
  have hw : ∀ x ∈ B, w x = 0 := by
    intro x hx
    change f x - h x = 0
    rw [hf ⟨x, hx⟩, hh.1 ⟨x, hx⟩, sub_self]
  have hwh := dirichlet_boundary_orthogonal π hπ P B g h w hh hw
  have hhw : dirichletForm π hπ P h w = 0 :=
    (dirichlet_symm π hπ P hb h w).trans hwh
  have hexpand : dirichletForm π hπ P (h + w) (h + w) =
      dirichletForm π hπ P h h + dirichletForm π hπ P h w +
      dirichletForm π hπ P w h + dirichletForm π hπ P w w := by
    unfold dirichletForm
    rw [map_add, add_sub_add_comm]
    simp only [inner_add_left, inner_add_right]
    ring
  have he : h + w = f := by
    funext x
    change h x + (f x - h x) = f x
    ring
  rw [he, hwh, hhw, add_zero, add_zero] at hexpand
  exact hexpand

end WeightedSpace

/-- Dirichlet's principle, with the canonical hitting representation and the
complete equality characterization of the minimizing inequality. -/
theorem dirichlet_principle : DirichletMinimizerSpec.dirichlet_principle.{u} := by
  intro S _ _ _ _ P π hπ hi hr B hB g
  obtain ⟨hh, hu⟩ := boundary_harmonic_unique P π hπ hi hr B hB g
  refine ⟨hh, hu, boundary_representation P hi B hB g, ?_⟩
  intro f hf
  have hb := (reversible_iff_detailedBalance P π).mp hr
  let h : WeightedSpace π hπ := boundaryHarmonic P B g
  let w : WeightedSpace π hπ := fun x => f x - h x
  have hexpand := WeightedSpace.dirichlet_boundary_expansion π hπ P hb B g h f hh hf
  change WeightedSpace.dirichletForm π hπ P f f =
    WeightedSpace.dirichletForm π hπ P h h +
      WeightedSpace.dirichletForm π hπ P w w at hexpand
  have hn := WeightedSpace.dirichlet_nonneg π hπ P hb w
  refine ⟨?_, ?_⟩
  · change WeightedSpace.dirichletForm π hπ P h h ≤ _
    linarith
  · constructor
    · intro heq
      have hz : WeightedSpace.dirichletForm π hπ P w w = 0 := by
        change WeightedSpace.dirichletForm π hπ P f f =
          WeightedSpace.dirichletForm π hπ P h h at heq
        linarith
      obtain ⟨b, hbB⟩ := hB
      funext x
      obtain ⟨n, hn⟩ := (hi x b).1
      have he := WeightedSpace.equal_of_power_positive π hπ P w
        (WeightedSpace.equal_on_edge_of_dirichlet_zero π hπ P hb w hz) n x b hn
      have hwB : w b = 0 := by
        change f b - boundaryHarmonic P B g b = 0
        rw [hf ⟨b, hbB⟩, hh.1 ⟨b, hbB⟩, sub_self]
      exact sub_eq_zero.mp (he.trans hwB)
    · intro heq
      rw [heq]

end
end P207.Markov
