import MathGenome.Internal.Specs.D05.M13.NormalReducing.Graph
import MathGenome.Internal.D05.M13.NormalReducing.Subspace

/-! The graph proof of the commutant consequence of normal reduction. -/

noncomputable section
namespace D05.M13.NormalReducing.Graph

open Specs.D05.M13.NormalReducing.Graph (SumSpace diagonalMap graphSubspace)

universe u v
variable {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V]

theorem external_sum_components :
    Specs.D05.M13.NormalReducing.Graph.external_sum_components := by
  intro F V _ _ _ z
  rfl

theorem direct_sum_inner : Specs.D05.M13.NormalReducing.Graph.direct_sum_inner := by
  intro F V _ _ _ x y
  rfl

theorem diagonal_apply : Specs.D05.M13.NormalReducing.Graph.diagonal_apply := by
  intro F V _ _ _ T x y
  rfl

theorem mem_graph : Specs.D05.M13.NormalReducing.Graph.mem_graph := by
  intro F V _ _ _ S z
  rfl

theorem diagonal_adjoint : Specs.D05.M13.NormalReducing.Graph.diagonal_adjoint := by
  intro F V _ _ _ _ T
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner F (T.adjoint (WithLp.ofLp x).1) (WithLp.ofLp y).1 +
      inner F (T.adjoint (WithLp.ofLp x).2) (WithLp.ofLp y).2 =
    inner F (WithLp.ofLp x).1 (T (WithLp.ofLp y).1) +
      inner F (WithLp.ofLp x).2 (T (WithLp.ofLp y).2)
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]

theorem diagonal_normal : Specs.D05.M13.NormalReducing.Graph.diagonal_normal := by
  intro F V _ _ _ _ T hT
  unfold _root_.D05.normalOperator
  rw [diagonal_adjoint]
  apply LinearMap.ext
  intro z
  apply (WithLp.linearEquiv 2 F (V × V)).injective
  apply Prod.ext
  · exact DFunLike.congr_fun hT (WithLp.ofLp z).1
  · exact DFunLike.congr_fun hT (WithLp.ofLp z).2

theorem graph_invariant : Specs.D05.M13.NormalReducing.Graph.graph_invariant := by
  intro F V _ _ _ T S hST z hz
  rw [mem_graph] at hz ⊢
  change T (WithLp.ofLp z).2 = S (T (WithLp.ofLp z).1)
  rw [hz]
  exact (DFunLike.congr_fun hST (WithLp.ofLp z).1).symm

/-- Invoke finite-dimensional normal reduction on the L² product, with
normality of its diagonal proved above. -/
theorem graph_adjoint_invariant :
    Specs.D05.M13.NormalReducing.Graph.graph_adjoint_invariant := by
  intro F V _ _ _ _ T S hT hST
  exact D05.M13.NormalReducing.Subspace.adjoint_invariant
    (diagonalMap T) (graphSubspace S) (diagonal_normal T hT) (graph_invariant T S hST)

/-- Membership of (T†x,T†Sx) in the graph says exactly T†Sx = ST†x. -/
theorem commutes_adjoint : Specs.D05.M13.NormalReducing.Graph.commutes_adjoint := by
  intro F V _ _ _ _ T S hT hST
  apply LinearMap.ext
  intro x
  have hx : WithLp.toLp 2 (x, S x) ∈ graphSubspace S := (mem_graph S _).mpr rfl
  have ha := graph_adjoint_invariant T S hT hST _ hx
  rw [diagonal_adjoint, diagonal_apply, mem_graph] at ha
  exact ha.symm

end D05.M13.NormalReducing.Graph
