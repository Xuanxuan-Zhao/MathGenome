import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Statements for Theorem 1.1 of the manuscript (paper.tex:67–118).
No countability or nontriviality is imposed on the Hilbert space or index type.
`HasSum` denotes convergence of the net over all finite subsets. -/
noncomputable section
open scoped lp ComplexConjugate Topology
open Filter

namespace P102.Hilbert

/-- The manuscript's inner product is linear in its first argument. -/
def paperInner {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (x y : H) : 𝕜 := inner 𝕜 y x

/-- The closed linear span of the specified family. -/
def closedSpan {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (u : I → H) : Submodule 𝕜 H :=
  (Submodule.span 𝕜 (Set.range u)).topologicalClosure

namespace Specs

/-- The nonnegative sum is the supremum of its finite subsums, and obeys Bessel. -/
def Bessel : Prop :=
  ∀ {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
  ∀ (u : I → H), Orthonormal 𝕜 u → ∀ x : H,
    Summable (fun i => ‖paperInner (𝕜 := 𝕜) x (u i)‖ ^ 2) ∧
    IsLUB (Set.range (fun F : Finset I => ∑ i ∈ F, ‖paperInner (𝕜 := 𝕜) x (u i)‖ ^ 2))
      (∑' i, ‖paperInner (𝕜 := 𝕜) x (u i)‖ ^ 2) ∧
    (∑' i, ‖paperInner (𝕜 := 𝕜) x (u i)‖ ^ 2) ≤ ‖x‖ ^ 2

/-- The synthesis isomorphism onto precisely the closed span, specified by its net sum. -/
def Synthesis : Prop :=
  ∀ {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
  ∀ (u : I → H), Orthonormal 𝕜 u →
    ∃ S : ℓ²(I, 𝕜) ≃ₗᵢ[𝕜] closedSpan (𝕜 := 𝕜) u,
      ∀ a, HasSum (fun i => a i • u i) (S a : H)

/-- In the total case the inverse consists of inner products, with reconstruction,
absolute cross-Parseval and Parseval. -/
def CompleteExpansion : Prop :=
  ∀ {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
  ∀ (u : I → H), Orthonormal 𝕜 u → closedSpan (𝕜 := 𝕜) u = ⊤ →
    ∃ S : ℓ²(I, 𝕜) ≃ₗᵢ[𝕜] H,
      (∀ a, HasSum (fun i => a i • u i) (S a)) ∧
      (∀ x i, S.symm x i = paperInner (𝕜 := 𝕜) x (u i)) ∧
      (∀ x, HasSum (fun i => paperInner (𝕜 := 𝕜) x (u i) • u i) x) ∧
      (∀ x y, HasSum
        (fun i => paperInner (𝕜 := 𝕜) x (u i) * conj (paperInner (𝕜 := 𝕜) y (u i))) (paperInner (𝕜 := 𝕜) x y)) ∧
      (∀ x y, Summable
        (fun i => ‖paperInner (𝕜 := 𝕜) x (u i) * conj (paperInner (𝕜 := 𝕜) y (u i))‖)) ∧
      (∀ x, HasSum (fun i => ‖paperInner (𝕜 := 𝕜) x (u i)‖ ^ 2) (‖x‖ ^ 2))

/-- Every square-summable coefficient vector has countable support. For any
convergent synthesis net, every enumeration of its infinite support gives the
ordinary norm-convergent series; finite support gives the finite sum. -/
def CountableSeries : Prop :=
  ∀ {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
  ∀ a : ℓ²(I, 𝕜), (Function.support a).Countable ∧
    ∀ (u : I → H) (z : H), HasSum (fun i => a i • u i) z →
      (∀ e : ℕ ≃ Function.support a,
        Tendsto (fun n => ∑ k ∈ Finset.range n, a (e k) • u (e k)) atTop (𝓝 z)) ∧
      (∀ F : Finset I, Function.support a ⊆ (F : Set I) →
        ∑ i ∈ F, a i • u i = z)

end Specs
end P102.Hilbert
