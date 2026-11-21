import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.BaireOne
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.CategoryInterface
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set Filter
open scoped Topology
universe u v

namespace D10Topology.Ch14

namespace BaireOne

/-- Points at which the entire tail has pairwise distance at most `ε`. -/
private def tailSet {X : Type u} {Y : Type v} [MetricSpace Y]
    (g : ℕ → X → Y) (ε : ℝ) (N : ℕ) : Set X :=
  {x | ∀ n ≥ N, ∀ m ≥ N, dist (g n x) (g m x) ≤ ε}

private theorem tailSet_closed {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] (g : ℕ → X → Y)
    (hg : ∀ n, Continuous (g n)) (ε : ℝ) (N : ℕ) :
    IsClosed (tailSet g ε N) := by
  simp only [tailSet, ofPred_forall]
  exact isClosed_iInter fun n => isClosed_iInter fun _ =>
    isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_le ((hg n).dist (hg m)) continuous_const

private theorem tailSet_cover {X : Type u} {Y : Type v}
    [MetricSpace Y] (g : ℕ → X → Y) (f : X → Y)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    (ε : ℝ) (hε : 0 < ε) : (⋃ N, tailSet g ε N) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hlim x).cauchySeq ε hε
  exact mem_iUnion.mpr ⟨N, fun n hn m hm => (hN n hn m hm).le⟩

private theorem tailSet_limit_bound {X : Type u} {Y : Type v}
    [MetricSpace Y] (g : ℕ → X → Y) (f : X → Y)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    {ε : ℝ} {N : ℕ} {x : X} (hx : x ∈ tailSet g ε N) :
    dist (g N x) (f x) ≤ ε := by
  apply le_of_tendsto (tendsto_const_nhds.dist (hlim x))
  filter_upwards [eventually_ge_atTop N] with m hm
  exact hx N le_rfl m hm

end BaireOne

/-- A metric-valued pointwise limit of continuous maps on a Baire space has
an entire continuity set which is dense, Gδ, and residual. -/
theorem baire_one_continuity_set {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] (hX : BaireIn X)
    (g : ℕ → X → Y) (f : X → Y) (hg : ∀ n, Continuous (g n))
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) :
    Dense {x | ContinuousAt f x} ∧ IsGδ {x | ContinuousAt f x} ∧
      ResidualIn {x | ContinuousAt f x} := by
  let : BaireSpace X := (baire_iff_library X).mp hX
  let ε : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  have hε : ∀ k, 0 < ε k := fun k => by dsimp [ε]; positivity
  let U : ℕ → Set X := fun k => ⋃ N, interior (BaireOne.tailSet g (ε k) N)
  have hUo : ∀ k, IsOpen (U k) := fun k => isOpen_iUnion fun N => isOpen_interior
  have hUd : ∀ k, Dense (U k) := fun k =>
    dense_iUnion_interior_of_closed (BaireOne.tailSet_closed g hg (ε k))
      (BaireOne.tailSet_cover g f hlim (ε k) (hε k))
  have hsub : (⋂ k, U k) ⊆ {x | ContinuousAt f x} := by
    intro x hx
    apply Metric.continuousAt_iff'.mpr
    intro η hη
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < η / 3 by linarith)
    have hk' : ε k < η / 3 := hk
    obtain ⟨N, hxN⟩ := mem_iUnion.mp (mem_iInter.mp hx k)
    have hW : interior (BaireOne.tailSet g (ε k) N) ∈ 𝓝 x :=
      isOpen_interior.mem_nhds hxN
    have hNg : ∀ᶠ y in 𝓝 x, dist (g N y) (g N x) < η / 3 :=
      (Metric.continuousAt_iff'.mp (hg N).continuousAt) (η / 3) (by linarith)
    filter_upwards [hW, hNg] with y hy hny
    have hyb := BaireOne.tailSet_limit_bound g f hlim (interior_subset hy)
    have hxb := BaireOne.tailSet_limit_bound g f hlim (interior_subset hxN)
    calc
      dist (f y) (f x) ≤ dist (f y) (g N y) + dist (g N y) (g N x) +
          dist (g N x) (f x) := dist_triangle4 _ _ _ _
      _ < η := by rw [dist_comm (f y) (g N y)]; linarith
  have hd : Dense {x | ContinuousAt f x} :=
    (dense_iInter_of_isOpen hUo hUd).mono hsub
  have hG : IsGδ {x | ContinuousAt f x} := IsGδ.setOfPred_continuousAt f
  exact ⟨hd, hG, contains_dense_gdelta_residual _ _ (Subset.refl _) hG hd⟩

end D10Topology.Ch14
