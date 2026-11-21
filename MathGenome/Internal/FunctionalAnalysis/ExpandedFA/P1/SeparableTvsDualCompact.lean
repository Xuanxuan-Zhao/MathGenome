import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SeparableTvsDualCompact
import Mathlib.Topology.DenseEmbedding

/-!
Compact dual sets over a separable TVS are metrizable. Evaluations on a dense
sequence separate continuous functionals, giving a continuous injection into
a countable product of scalar spaces. Compactness makes this an embedding.
-/

namespace ExpandedFA.P1

open TopologicalSpace Topology

/-- The corollary applies to arbitrary separable TVSs, without a norm or
local convexity hypothesis. -/
theorem separable_tvs_dual_compact_metrizable :
    SeparableTvsDualCompactSpec.CompactDualMetrizable := by
  intro 𝕜 E _ _ _ _ _ _ _hTVS K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨d, hd⟩ := exists_dense_seq E
  let Φ : K → ℕ → 𝕜 := fun f n => f.val (d n)
  have hcont : Continuous Φ := continuous_pi fun n =>
    (WeakDual.eval_continuous (d n)).comp continuous_subtype_val
  have hinj : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    have heq : (f.val : E → 𝕜) = (g.val : E → 𝕜) :=
      hd.equalizer (map_continuous f.val) (map_continuous g.val)
        (funext fun n => congrFun hfg n)
    exact congrFun heq x
  exact (hcont.isClosedEmbedding hinj).isEmbedding.metrizableSpace

end ExpandedFA.P1
