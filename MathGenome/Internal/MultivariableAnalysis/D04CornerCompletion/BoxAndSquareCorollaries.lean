import MathGenome.Internal.MultivariableAnalysis.D04CornerCompletion.NoVertexChart
import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.BoxAndSquareCorollaries

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open scoped ContDiff

namespace D04CornerCompletion

/-- The centered chart required at the lower vertex contradicts the vertex
obstruction. -/
theorem box_not_isEmbeddedManifold
    {n : ℕ} (hn : 2 ≤ n) (a b : E n)
    (hab : ∀ i : Fin n, a i < b i) :
    ¬ IsEmbeddedManifold (1 : ℕ∞ω) n (box a b) := by
  intro hM
  have ha : a ∈ box a b := fun i => ⟨le_rfl, (hab i).le⟩
  have hv : IsBoxVertex a b a := fun _ => Or.inl rfl
  exact no_centered_vertex_chart hn a b hab a hv (hM.2.2 a ha)

/-- The coordinatewise square has no centered C¹ embedded chart at the origin. -/
theorem square_no_centered_origin_chart :
    ¬ ∃ (c : EmbeddedChart (1 : ℕ∞ω) 2 2
        {x : E 2 | ∀ i : Fin 2, (0 : ℝ) ≤ x i ∧ x i ≤ 1}) (u : E 2),
      CenteredAt c u ∧ c.toFun u = (0 : E 2) := by
  change ¬ ∃ (c : EmbeddedChart (1 : ℕ∞ω) 2 2
      (box (0 : E 2) (WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ))))) (u : E 2),
    CenteredAt c u ∧ c.toFun u = (0 : E 2)
  exact no_centered_vertex_chart (by decide) _ _ (by intro i; norm_num)
    (0 : E 2) (fun _ => Or.inl rfl)

/-- The coordinatewise square is not a C¹ embedded two-manifold with smooth
boundary in its Euclidean ambient space. -/
theorem square_not_isEmbeddedManifold :
    ¬ IsEmbeddedManifold (1 : ℕ∞ω) 2
      {x : E 2 | ∀ i : Fin 2, (0 : ℝ) ≤ x i ∧ x i ≤ 1} := by
  change ¬ IsEmbeddedManifold (1 : ℕ∞ω) 2
    (box (0 : E 2) (WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ))))
  exact box_not_isEmbeddedManifold (by decide) _ _ (by intro i; norm_num)

end D04CornerCompletion
