import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.Peano
import MathGenome.Internal.PointSetTopology.D10Topology.Ch18.CantorSurjection
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.CoordinateExtensions
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
Space-filling curves, paper.tex `d10:18:peano`.
Transport the upstream Cantor-space surjection along the proved ternary
Cantor homeomorphism. Extend from that closed subset of ℝ into the same
product of intervals, then restrict the extension to [0,1]. Since the
Cantor subset lies in [0,1], the restricted extension is still surjective.
-/

open Set

namespace D10Topology.Ch18

/-- Every positive finite cube is a continuous image of the real unit interval. -/
theorem peano_cube (m : ℕ) (_hm : 1 ≤ m) :
    ∃ f : Icc (0 : ℝ) 1 → (Fin m → Icc (0 : ℝ) 1),
      Continuous f ∧ Function.Surjective f := by
  obtain ⟨f, hf, honto⟩ := cantor_surjection (Fin m → Icc (0 : ℝ) 1)
  obtain ⟨h, _⟩ := cantor_homeomorph
  let g : cantorSet → (Fin m → Icc (0 : ℝ) 1) := f ∘ h.symm
  have hg : Continuous g := hf.comp h.symm.continuous
  obtain ⟨F, hF, hext⟩ := Ch07.closed_interval_product_extension
    (inferInstance : NormalSpace ℝ) cantorSet isClosed_cantorSet
    (fun _ : Fin m => Icc (0 : ℝ) 1) (fun _ => isClosed_Icc)
    (fun _ => ordConnected_Icc) (fun _ => nonempty_Icc.mpr zero_le_one) g hg
  refine ⟨fun x => F x.val, hF.comp continuous_subtype_val, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := honto y
  refine ⟨⟨(h a).val, cantorSet_subset_unitInterval (h a).property⟩, ?_⟩
  change F (h a).val = y
  rw [hext (h a)]
  simpa [g] using ha

/-- The square-filling case, with the square represented as a pair of intervals. -/
theorem peano_square :
    ∃ f : Icc (0 : ℝ) 1 → (Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1),
      Continuous f ∧ Function.Surjective f := by
  obtain ⟨f, hf, honto⟩ := peano_cube 2 (by decide)
  refine ⟨fun x => (f x 0, f x 1),
    ((continuous_apply 0).comp hf).prodMk ((continuous_apply 1).comp hf), ?_⟩
  rintro ⟨y₀, y₁⟩
  obtain ⟨x, hx⟩ := honto ![y₀, y₁]
  exact ⟨x, by simp [hx]⟩

end D10Topology.Ch18
