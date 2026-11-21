import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.CoordinateExtensions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.RealTietze
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products

/-!
Coordinate extension, paper.tex `d10:07:finite-coordinate-extension`.
The real power is a finite product with its canonical product topology.
For intervals we use Mathlib's interval-preserving real Tietze theorem,
which also permits unbounded intervals and empty closed domains. Choosing
one extension per coordinate and using continuity into a product proves
the arbitrary product assertion. Choice is allowed by foundation F1.
-/

open Set
universe u v

namespace D10Topology.Ch07

/-- Continuous maps on a closed subspace of a normal space extend to every
finite real power. This includes the zero-factor singleton. -/
theorem finite_coordinate_extension {X : Type u} [TopologicalSpace X]
    (hN : NormalSpace X) (A : Set X) (hA : IsClosed A)
    (n : ℕ) (f : A → (Fin n → ℝ)) (hf : Continuous f) :
    ∃ F : X → (Fin n → ℝ), Continuous F ∧ ∀ x : A, F x = f x := by
  classical
  have hcoord : ∀ i : Fin n, ∃ g : X → ℝ,
      Continuous g ∧ ∀ x : A, g x = f x i := by
    intro i
    exact tietze_real hN A hA (fun x => f x i) ((continuous_apply i).comp hf)
  choose g hg hgf using hcoord
  exact ⟨fun x i => g i x, continuous_pi hg, fun x => funext fun i => hgf i x⟩

/-- Continuous maps extend into the same product of nonempty closed real
intervals, with arbitrary index type and possibly empty closed domain. -/
theorem closed_interval_product_extension {X : Type u} [TopologicalSpace X]
    (hN : NormalSpace X) (A : Set X) (hA : IsClosed A)
    {I : Type v} (J : I → Set ℝ) (_hclosed : ∀ i, IsClosed (J i))
    (hinterval : ∀ i, OrdConnected (J i)) (hne : ∀ i, (J i).Nonempty)
    (f : A → (∀ i, J i)) (hf : Continuous f) :
    ∃ F : X → (∀ i, J i), Continuous F ∧ ∀ x : A, F x = f x := by
  classical
  let : NormalSpace X := hN
  have hcoord : ∀ i, ∃ g : X → J i,
      Continuous g ∧ ∀ x : A, g x = f x i := by
    intro i
    let : OrdConnected (J i) := hinterval i
    let fi : C(A, ℝ) := ⟨fun x => (f x i).val,
      continuous_subtype_val.comp ((continuous_apply i).comp hf)⟩
    obtain ⟨g, hmem, heq⟩ := fi.exists_restrict_eq_forall_mem_of_closed
      (fun x => (f x i).property) (hne i) hA
    refine ⟨fun x => ⟨g x, hmem x⟩, g.continuous.subtype_mk hmem, ?_⟩
    intro x
    apply Subtype.ext
    exact congrArg (fun h : C(A, ℝ) => h x) heq
  choose g hg hgf using hcoord
  exact ⟨fun x i => g i x, continuous_pi hg, fun x => funext fun i => hgf i x⟩

end D10Topology.Ch07
