import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.MinimumCostFlow
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualCycleOptimality
import MathGenome.Internal.ExtremalOptimization.P205.Networks.NegativeCyclePotentials
import MathGenome.Internal.ExtremalOptimization.P205.Networks.BoundedFlowIntegrality

open scoped BigOperators
open Matrix
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Forgetting the endpoint indices gives precisely the list-walk convention. -/
theorem walk_isWalk {G : Digraph V A} {x y : V} (p : Walk G x y) :
    IsWalk G.tail G.head x p.arcs y := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change G.tail a.val = _ ∧ IsWalk G.tail G.head (G.head a.val) _ _
    rw [a.property.2]
    exact ⟨a.property.1, ih⟩

/-- Recover an indexed walk without changing any labelled arc. -/
theorem exists_walk_of_isWalk (G : Digraph V A) {x y : V} {es : List A}
    (h : IsWalk G.tail G.head x es y) : ∃ p : Walk G x y, p.arcs = es := by
  induction es generalizing x with
  | nil =>
    have hxy : x = y := h
    subst y
    exact ⟨.nil x, rfl⟩
  | cons e es ih =>
    change G.tail e = x ∧ IsWalk G.tail G.head (G.head e) es y at h
    obtain ⟨p, hp⟩ := ih h.2
    refine ⟨Walk.cons (⟨e, h.1, rfl⟩ : Arc G x (G.head e)) p, ?_⟩
    change e :: p.arcs = e :: es
    rw [hp]

/-- The two upstream cycle predicates use the same simple directed cycles,
including one-arc loops. -/
theorem noNegativeCycles_iff_list (G : Digraph V A) (lo hi f w : A → ℝ) :
    CycleSpec.NoNegativeCycles G lo hi f w ↔
    NoNegativeSimpleCycles (BoundedSpec.graph G lo hi f).tail
      (BoundedSpec.graph G lo hi f).head (fun r => BoundedSpec.cost w r.val) := by
  constructor
  · intro h x es hs
    obtain ⟨p, hp⟩ := exists_walk_of_isWalk _ hs.1
    have hc : p.IsCycle := by
      change 0 < p.arcs.length ∧ p.vertices.dropLast.Nodup
      rw [← walk_tails, hp]
      exact ⟨List.length_pos_iff.mpr hs.2.1, hs.2.2⟩
    simpa only [CycleSpec.walkCost, walkCost, hp] using h x p hc
  · intro h x p hp
    apply h x p.arcs
    refine ⟨walk_isWalk p, ?_, ?_⟩
    · exact List.length_pos_iff.mp hp.1
    · rw [walk_tails]
      exact hp.2

/-- All three original certificates, for every feasible bounded flow. -/
theorem minimum_cost_flow_certificates : MinimumCostFlowSpecs.certificates.{u,v} := by
  intro V A _ _ G lo hi b w f hf
  refine ⟨residual_cycle_optimality G lo hi b w f hf, ?_⟩
  exact (noNegativeCycles_iff_list G lo hi f w).trans
    (negative_cycles_iff_potential V (BoundedSpec.ResidualArc lo hi f)
      (BoundedSpec.graph G lo hi f).tail (BoundedSpec.graph G lo hi f).head
      (fun r => BoundedSpec.cost w r.val))

/-- Matrix multiplication by the signed incidence matrix is net outflow,
including the zero column contributed by a loop. -/
theorem incidence_mulVec_eq_divergence (G : Digraph V A) (f : A → ℝ) :
    (Specs.P205.Networks.directedIncidence G.tail G.head).map (Int.cast : ℤ → ℝ) *ᵥ f =
      G.divergence f := by
  classical
  ext x
  rw [divergence_eq_incidence_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp [Specs.P205.Networks.directedIncidence, eq_comm]

/-- The common fixed-divergence feasible set agrees with the TU interface. -/
theorem feasible_iff_mem_boundedFlowSet (G : Digraph V A)
    (lo hi : A → ℤ) (b : V → ℤ) (f : A → ℝ) :
    BoundedSpec.Feasible G (fun a => (lo a : ℝ)) (fun a => (hi a : ℝ))
      (fun x => (b x : ℝ)) f ↔
    f ∈ Specs.P205.Networks.boundedFlowSet G.tail G.head b lo hi := by
  unfold Specs.P205.Networks.boundedFlowSet
  rw [Set.mem_ofPred_eq, incidence_mulVec_eq_divergence]
  exact ⟨fun h => ⟨funext h.2, h.1⟩, fun h => ⟨h.2, congrFun h.1⟩⟩

/-- Integral data admit an integral minimizing flow for arbitrary real costs. -/
theorem integral_minimum_cost_flow : MinimumCostFlowSpecs.integral_minimum.{u,v} := by
  intro V A _ _ G lo hi b w hne
  obtain ⟨f₀, hf₀⟩ := hne
  obtain ⟨f, hf, hint, hopt⟩ := BoundedFlowIntegrality.integral_minimizer
    G.tail G.head b lo hi w
    ⟨f₀, (feasible_iff_mem_boundedFlowSet G lo hi b f₀).mp hf₀⟩
  refine ⟨f, (feasible_iff_mem_boundedFlowSet G lo hi b f).mpr hf.1, hint, ?_⟩
  intro g hg
  exact hopt g ((feasible_iff_mem_boundedFlowSet G lo hi b g).mp hg)

end P205.Networks
