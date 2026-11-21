import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainSubdivision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.AffineSubdivisionMesh
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section
open Convexity P202Specs.SingularChains P202Specs.SingularSubdivision
namespace P202.SmallChainSubdivision
universe u v w

/-- The finite coordinate metric, with the existing standard simplex topology. -/
abbrev simplexMetric (n : ℕ) : MetricSpace (Delta n) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).comapMetricSpace
    (fun t : Delta n => (t.weights : Fin (n+1) → ℝ))

local instance (n : ℕ) : MetricSpace (Delta n) := simplexMetric n

def coordinates (n : ℕ) : ConvexSpace.AffineMap ℝ (Delta n) (Fin (n+1) → ℝ) :=
  ⟨fun t => t.weights,
    (IsAffineMap.linearMap (Finsupp.lcoeFun : (Fin (n+1) →₀ ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ))).comp
      (StdSimplex.isAffineMap_weights ℝ (Fin (n+1)))⟩

lemma simplex_dist (n : ℕ) (x y : Delta n) :
    dist x y = dist (coordinates n x) (coordinates n y) := rfl

local instance (n : ℕ) : IsConvexDist (Delta n) where
  dist_iConvexComb_fst_snd_le f := by
    simp only [simplex_dist, (coordinates n).isAffineMap.map_iConvexComb]
    exact dist_iConvexComb_le f (fun p => coordinates n p.1) (fun p => coordinates n p.2)

variable (R : Type u) [CommRing R]

/-- Evaluation intertwines all iterates, including level zero. -/
theorem iterate_evaluate {X : TopCat.{v}} {k : ℕ} (s : Simplex X k)
    (n m : ℕ) (c : AffineChains R (Delta k) (n+1)) :
    ((subdivision R X n)^m) (evaluate R s n c) =
      evaluate R s n (((affineSubdivision R (Delta k) (n+1))^m) c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [ih, P202.SingularSubdivision.subdivision_evaluate]

/-- All barycentric coordinates lie in `[0,1]`, so the coordinate
sup metric gives a unit bound on the original simplex. -/
lemma simplex_dist_le_one (n : ℕ) (x y : Delta n) : dist x y ≤ 1 := by
  rw [simplex_dist]
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have hx : (0 : ℝ) ≤ x.weights i := x.nonneg i
    have hy := y.weights_apply_le_one i
    change -(1 : ℝ) ≤ x.weights i - y.weights i
    linarith
  · have hx := x.weights_apply_le_one i
    have hy : (0 : ℝ) ≤ y.weights i := y.nonneg i
    change x.weights i - y.weights i ≤ (1 : ℝ)
    linarith

/-- Convexity extends the vertex bound to the entire affine simplex. -/
lemma affineSimplexMap_dist_vertex {k n : ℕ} (q : Fin (n+1) → Delta k)
    (r : ℝ) (hq : ∀ i j, dist (q i) (q j) ≤ r) (x : Delta n) (j : Fin (n+1)) :
    dist (affineSimplexMap q x) (q j) ≤ r := by
  change dist (x.iConvexComb q) (q j) ≤ r
  exact (dist_iConvexComb_left_le x q (q j)).trans
    (P202.Topology.real_iConvexComb_le x _ r (fun i _ => hq i j))

/-- Eventual smallness for a single generator, with the raw indexed cover. -/
theorem eventualSmall_generator (X : TopCat.{v}) {ι : Type w} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (n : ℕ) (s : Simplex X n) :
    ∃ m : ℕ, IsSmall U (((subdivision R X n)^m) (Finsupp.single s 1)) := by
  classical
  let V : ι → Set (Delta n) := fun i => (simplexEquiv X n s) ⁻¹' U i
  have hV : ∀ i, IsOpen (V i) := fun i =>
    (hU i).preimage (simplexEquiv X n s).continuous
  have hVc : (Set.univ : Set (Delta n)) ⊆ ⋃ i, V i := by
    intro x _
    obtain ⟨i, hi⟩ := hcover (simplexEquiv X n s x)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hVc
  obtain ⟨m, hm⟩ := P202.Topology.subdivision_contraction_eventually_lt (n+1)
    (Nat.succ_pos n) δ hδ
  refine ⟨m, ?_⟩
  rw [← P202.SingularSubdivision.evaluate_vertices R s, iterate_evaluate]
  intro σ hσ
  change σ ∈ (Finsupp.mapDomain _ _).support at hσ
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
  have hvertices := P202.AffineSubdivisionMesh.iterated_contraction R n m
    (StdSimplex.single : Fin (n+1) → Delta n) 1 (by norm_num)
    (fun i j => simplex_dist_le_one n _ _) q hq
  have hvertices' : ∀ i j, dist (q i) (q j) ≤ (1 - 1 / ((n+1 : ℕ) : ℝ))^m := by
    simpa only [mul_one] using hvertices
  obtain ⟨i, hi⟩ := hball (q 0) (Set.mem_univ _)
  refine ⟨i, ?_⟩
  rintro y ⟨x, rfl⟩
  change simplexEquiv X n s (affineSimplexMap q x) ∈ U i
  apply hi
  exact (affineSimplexMap_dist_vertex q _ hvertices' x 0).trans_lt (hm m le_rfl)

end P202.SmallChainSubdivision

namespace P202.Topology
universe u v w
/-- Each individual simplex eventually becomes small under the fixed
barycentric subdivision, for every indexed open cover. -/
theorem smallChainEventualSubdivision : P202Specs.SmallChainSubdivision.eventualSmall.{u,v,w} := by
  intro R _ X ι U hU hc n s
  exact P202.SmallChainSubdivision.eventualSmall_generator R X U hU hc n s
end P202.Topology
