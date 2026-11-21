import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DoubleAnnihilatorDual
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
Double annihilation for a subspace of the continuous scalar-linear dual.
We work with the native weak-star topology, which is definitionally the
shared pairing topology after removing the induced identity map.

Separation of a point outside the closed subspace gives a weak-star continuous
linear functional. Weak representation writes it as evaluation at x ∈ E.
Its real part is bounded above on N; scaling any nonzero value would violate
that bound. Thus x preannihilates N and excludes the given point from the
double annihilator. In the other direction, evaluation kernels are closed.
-/

namespace ExpandedFA.P1.DoubleAnnihilatorDual

universe u v
open Topology

theorem double_annihilator_dual : Spec.DoubleAnnihilatorClosure.{u, v} := by
  intro 𝕜 E _ _ _ N
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 (WeakDual 𝕜 E) :=
    inferInstanceAs (IsScalarTower ℝ 𝕜 (E →L[𝕜] 𝕜))
  let : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing 𝕜 E)))
  let M : Submodule 𝕜 (WeakDual 𝕜 E) := N
  change {f : WeakDual 𝕜 E | ∀ x, (∀ g ∈ N, g x = 0) → f x = 0} =
    @closure (WeakDual 𝕜 E)
      (TopologicalSpace.induced id inferInstance) (M : Set (WeakDual 𝕜 E))
  rw [induced_id]
  ext f
  change (∀ x, (∀ g ∈ N, g x = 0) → f x = 0) ↔
    f ∈ closure (M : Set (WeakDual 𝕜 E))
  constructor
  · intro hf
    by_contra hcl
    obtain ⟨l, c, hl, hlf⟩ := RCLike.geometric_hahn_banach_closed_point
      (𝕜 := 𝕜) (M.topologicalClosure.restrictScalars ℝ).convex
      isClosed_closure hcl
    obtain ⟨x, hx⟩ := LinearMap.dualEmbedding_surjective (topDualPairing 𝕜 E) l
    have heval (g : WeakDual 𝕜 E) : l g = g x := by
      exact congrArg (fun L : StrongDual 𝕜 (WeakDual 𝕜 E) => L g) hx.symm
    have hc : 0 < c := by simpa using hl 0 (subset_closure M.zero_mem)
    have hxN : ∀ g ∈ N, g x = 0 := by
      intro g hg
      by_contra hne
      let a : 𝕜 := (c + 1 : ℝ) / g x
      have ha : a • StrongDual.toWeakDual g ∈ M :=
        M.smul_mem a hg
      have hb := hl _ (subset_closure ha)
      rw [heval] at hb
      have hav : (a • StrongDual.toWeakDual g) x = (c + 1 : ℝ) := by
        change ((c + 1 : ℝ) : 𝕜) / g x * g x = _
        exact div_mul_cancel₀ _ hne
      rw [hav] at hb
      simp only [RCLike.ofReal_re] at hb
      linarith
    have hzero := hf x hxN
    rw [heval, hzero, map_zero] at hlf
    linarith
  · intro hf x hx
    have hclosed : IsClosed {g : WeakDual 𝕜 E | g x = 0} :=
      isClosed_eq (WeakDual.eval_continuous x) continuous_const
    apply closure_minimal (t := {g : WeakDual 𝕜 E | g x = 0}) ?_ hclosed hf
    intro g hg
    exact hx g hg

end ExpandedFA.P1.DoubleAnnihilatorDual
