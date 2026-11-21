import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.BoundedTietze
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.Linarith

/-!
Bounded Tietze extension and the separately stated approximate-extension lemma
from paper.tex, Chapter 7. The interval-preserving Mathlib theorem uses only
normality and closedness. Applying it before scaling gives an alternative
proof of the approximate lemma, independent of the source's residual series.
-/

open Set
universe u

namespace D10Topology.Ch07

/-- Bounded Tietze, with the codomain equal to the prescribed real interval.
The proof also covers a = b and empty closed subspaces and ambient spaces. -/
theorem tietze_bounded {X : Type u} [TopologicalSpace X] (hN : NormalSpace X)
    (A : Set X) (hA : IsClosed A) (a b : ℝ) (hab : a ≤ b)
    (f : A → Icc a b) (hf : Continuous f) :
    ∃ F : X → Icc a b, Continuous F ∧ ∀ x : A, F x = f x := by
  let : NormalSpace X := hN
  let fReal : C(A, ℝ) := ⟨fun x => (f x : ℝ), continuous_subtype_val.comp hf⟩
  obtain ⟨F, hF, hFf⟩ := fReal.exists_restrict_eq_forall_mem_of_closed
    (fun x => (f x).property) (nonempty_Icc.mpr hab) hA
  refine ⟨fun x => ⟨F x, hF x⟩, F.continuous.subtype_mk _, ?_⟩
  intro x
  apply Subtype.ext
  exact congrArg (fun k : C(A, ℝ) => k x) hFf

/-- Approximate extension with range [-a/3,a/3] and error at most 2a/3. -/
theorem approximate_extension {X : Type u} [TopologicalSpace X] (hN : NormalSpace X)
    (A : Set X) (hA : IsClosed A) (a : ℝ) (ha : 0 < a)
    (h : A → Icc (-a) a) (hh : Continuous h) :
    ∃ g : X → Icc (-(a / 3)) (a / 3), Continuous g ∧
      ∀ x : A, |(h x : ℝ) - (g x : ℝ)| ≤ 2 * a / 3 := by
  obtain ⟨H, hH, hHh⟩ := tietze_bounded hN A hA (-a) a (by linarith) h hh
  have hbound (x : X) : (H x : ℝ) / 3 ∈ Icc (-(a / 3)) (a / 3) := by
    obtain ⟨hl, hu⟩ := (H x).property
    constructor <;> linarith
  refine ⟨fun x => ⟨(H x : ℝ) / 3, hbound x⟩,
    ((continuous_subtype_val.comp hH).div_const 3).subtype_mk _, ?_⟩
  intro x
  change |(h x : ℝ) - (H x : ℝ) / 3| ≤ 2 * a / 3
  rw [hHh x]
  obtain ⟨hl, hu⟩ := (h x).property
  rw [abs_le]
  constructor <;> linarith

end D10Topology.Ch07
