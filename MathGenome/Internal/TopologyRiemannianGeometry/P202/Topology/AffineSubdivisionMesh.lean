import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.AffineSubdivisionMesh
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularSubdivision

noncomputable section
open Convexity P202Specs.SingularSubdivision
namespace P202.AffineSubdivisionMesh
universe u v
variable (R : Type u) [CommRing R]

/-- Every surviving output term of a linear map comes from a surviving input
term; this only asserts inclusion, so permits coefficient cancellation. -/
theorem linearMap_support {I J : Type*} (L : (I →₀ R) →ₗ[R] (J →₀ R))
    (c : I →₀ R) (q : J) (hq : q ∈ (L c).support) :
    ∃ t ∈ c.support, q ∈ (L (Finsupp.single t 1)).support := by
  classical
  have he : L c = c.sum (fun t a => a • L (Finsupp.single t 1)) := by
    conv_lhs => rw [← c.sum_single]
    rw [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← Finsupp.smul_single_one t (c t), map_smul]
  rw [he, Finsupp.sum] at hq
  obtain ⟨t, ht, hqt⟩ := Finsupp.mem_support_finsetSum q hq
  exact ⟨t, ht, Finsupp.support_smul hqt⟩

theorem cone_support {Y : Type v} (b : Y) (n : ℕ)
    (c : AffineChains R Y n) (q : Fin (n+1) → Y)
    (hq : q ∈ (cone R b n c).support) :
    ∃ t ∈ c.support, Fin.cons b t = q := by
  classical
  exact Finset.mem_image.mp (Finsupp.mapDomain_support hq)

theorem boundary_support {Y : Type v} (n : ℕ) (t : Fin (n+1) → Y)
    (q : Fin n → Y) (hq : q ∈ (affineBoundary R Y n (Finsupp.single t 1)).support) :
    ∃ i : Fin (n+1), t ∘ i.succAbove = q := by
  classical
  rw [P202.SingularSubdivision.affineBoundary_single] at hq
  obtain ⟨i, _, hi⟩ := Finsupp.mem_support_finsetSum q hq
  have hi := Finsupp.support_smul hi
  exact ⟨i, (Finset.mem_singleton.mp (Finsupp.support_single_subset hi)).symm⟩

/-- Subdivision preserves every closed metric ball on the vertices. -/
theorem vertex_ball {Y : Type v} [ConvexSpace ℝ Y] [MetricSpace Y]
    [IsConvexDist Y] (n : ℕ) (t : Fin n → Y) (b : Y) (d : ℝ)
    (ht : ∀ i, dist (t i) b ≤ d) (q : Fin n → Y)
    (hq : q ∈ (affineSubdivision R Y n (Finsupp.single t 1)).support) :
    ∀ i, dist (q i) b ≤ d := by
  classical
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    rw [P202.SingularSubdivision.affineSubdivision_single] at hq
    obtain ⟨p, hp, rfl⟩ := cone_support R _ _ _ q hq
    obtain ⟨s, hs, hps⟩ := linearMap_support R (affineSubdivision R Y n) _ p hp
    obtain ⟨j, rfl⟩ := boundary_support R n t s hs
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero]
      apply (dist_iConvexComb_left_le _ t b).trans
      exact P202.Topology.real_iConvexComb_le _ _ d (fun i _ => ht i)
    · simp only [Fin.cons_succ]
      exact ih (t ∘ j.succAbove) (fun k => ht _) p hps k



/-- Each original vertex lies in the ball about the barycenter with the
sharp dimension-dependent radius. -/
theorem vertex_to_barycenter {Y : Type v} [ConvexSpace ℝ Y] [MetricSpace Y]
    [IsConvexDist Y] (n : ℕ) (t : Fin (n+1) → Y) (r : ℝ) (hr : 0 ≤ r)
    (ht : ∀ i j, dist (t i) (t j) ≤ r) (i : Fin (n+1)) :
    dist (t i) ((StdSimplex.barycenter : StdSimplex ℝ (Fin (n+1))).iConvexComb t) ≤
      (1 - 1 / ((n+1 : ℕ) : ℝ)) * r := by
  classical
  have h := P202.Topology.nested_barycenter_dist_le
    ({i} : Finset (Fin (n+1))) Finset.univ (by simp)
    (Finset.subset_univ _) t r hr (fun a _ b _ => ht a b)
  simpa only [StdSimplex.subBarycenter_singleton, iConvexComb_single,
    Finset.card_singleton, Nat.cast_one, Finset.card_univ, Fintype.card_fin] using h

/-- One subdivision contracts vertex diameter for the exact recursive operator. -/
theorem one_step {Y : Type v} [ConvexSpace ℝ Y] [MetricSpace Y]
    [IsConvexDist Y] (n : ℕ) (t : Fin (n+1) → Y) (r : ℝ) (hr : 0 ≤ r)
    (ht : ∀ i j, dist (t i) (t j) ≤ r) (q : Fin (n+1) → Y)
    (hq : q ∈ (affineSubdivision R Y (n+1) (Finsupp.single t 1)).support) :
    ∀ i j, dist (q i) (q j) ≤ (1 - 1 / ((n+1 : ℕ) : ℝ)) * r := by
  classical
  induction n with
  | zero =>
    intro i j
    have hij : i = j := by omega
    simp [hij]
  | succ n ih =>
    rw [P202.SingularSubdivision.affineSubdivision_single] at hq
    obtain ⟨p, hp, rfl⟩ := cone_support R _ _ _ q hq
    obtain ⟨s, hs, hps⟩ := linearMap_support R (affineSubdivision R Y (n+1)) _ p hp
    obtain ⟨k, rfl⟩ := boundary_support R (n+1) t s hs
    have hball : ∀ i, dist (p i)
        ((StdSimplex.barycenter : StdSimplex ℝ (Fin (n+1+1))).iConvexComb t) ≤
        (1 - 1 / ((n+1+1 : ℕ) : ℝ)) * r :=
      vertex_ball R (n+1) (t ∘ k.succAbove) _ _
        (fun i => vertex_to_barycenter (n+1) t r hr ht _) p hps
    have htail := ih (t ∘ k.succAbove) (fun i j => ht _ _) p hps
    have hfactor := P202.Topology.barycenter_contraction_factor_le 1 (n+1)
      (by omega) (by omega) (n+1+1) (by omega) r hr
    intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · simpa using mul_nonneg (show 0 ≤ 1 - 1 / ((n+1+1 : ℕ) : ℝ) by
          have hN : (1 : ℝ) ≤ ((n+1+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n+1+1)
          have hdiv : 1 / ((n+1+1 : ℕ) : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hN
          linarith) hr
      · simpa only [Fin.cons_zero, Fin.cons_succ, dist_comm] using hball b
    · refine Fin.cases ?_ (fun b => ?_) j
      · simpa only [Fin.cons_zero, Fin.cons_succ] using hball a
      · simpa only [Fin.cons_succ] using (htail a b).trans (by simpa using hfactor)



/-- The quantitative estimate after any number of subdivisions, uniformly over
all surviving affine tuples. -/
theorem iterated_contraction {Y : Type v} [ConvexSpace ℝ Y] [MetricSpace Y]
    [IsConvexDist Y] (n m : ℕ) (t : Fin (n+1) → Y) (r : ℝ) (hr : 0 ≤ r)
    (ht : ∀ i j, dist (t i) (t j) ≤ r) :
    ∀ q ∈ (((affineSubdivision R Y (n+1)) ^ m) (Finsupp.single t 1)).support,
      ∀ i j, dist (q i) (q j) ≤ (1 - 1 / ((n+1 : ℕ) : ℝ)) ^ m * r := by
  classical
  have hc : 0 ≤ 1 - 1 / ((n+1 : ℕ) : ℝ) := by
    have hN : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n+1)
    have hdiv : 1 / ((n+1 : ℕ) : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hN
    linarith
  induction m with
  | zero =>
    intro q hq
    have hqt : q = t := Finset.mem_singleton.mp (Finsupp.support_single_subset hq)
    subst q
    simpa using ht
  | succ m ih =>
    intro q hq i j
    rw [pow_succ', Module.End.mul_apply] at hq
    obtain ⟨p, hp, hqp⟩ := linearMap_support R (affineSubdivision R Y (n+1)) _ q hq
    have h := one_step R n p _ (mul_nonneg (pow_nonneg hc m) hr) (ih p hp) q hqp i j
    simpa only [pow_succ', mul_assoc] using h

end P202.AffineSubdivisionMesh

namespace P202.Topology
universe u v
/-- Shrinking vertex diameter for the concrete affine-chain subdivision. -/
theorem affineSubdivisionMesh : P202Specs.AffineSubdivisionMesh.shrinkingVertexDiameter.{u,v} := by
  intro R _ Y _ _ _ n m t r hr ht
  exact P202.AffineSubdivisionMesh.iterated_contraction R n m t r hr ht
end P202.Topology
