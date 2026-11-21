import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.TowerMaps
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.SeparableComparison
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler

/-! The general separable comparison of KD-22. Mathlib's formal étaleness
theorem for separable field extensions includes infinite extensions: its
proof glues the unique lifts on finite simple subextensions. The comparison
for formally étale algebras uses exactly `KaehlerDifferential.mapBaseChange`,
so it identifies the canonical map, for an arbitrary commutative base A. -/
namespace AdvCommAlg.Differentials

universe u v w
open scoped TensorProduct

theorem separable_comparison_bijective :
    Specs.AdvCommAlg.Differentials.separableComparisonBijective.{u,v,w} := by
  intro A K L _ _ _ _ _ _ _ _
  letI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A K L).bijective

theorem separable_comparison :
    Specs.AdvCommAlg.Differentials.separableComparison.{u,v,w} := by
  intro A K L _ _ _ _ _ _ _ _
  letI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  refine ⟨KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A K L, rfl, ?_⟩
  intro k
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]

theorem separable_vanishing :
    Specs.AdvCommAlg.Differentials.separableVanishing.{v,w} := by
  intro K L _ _ _ _
  letI : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  infer_instance

end AdvCommAlg.Differentials
