import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Naturality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TowerMaps

/-! KD-08: canonical C-linear maps in every compatible tower A → B → C. -/
namespace AdvCommAlg.Differentials

universe u v w
noncomputable section

/-- The scalar extension of the differential map for B → C over A. -/
def towerMapU : Specs.AdvCommAlg.Differentials.towerMapUType.{u,v,w} :=
  fun A B C _ _ _ _ _ _ _ => KaehlerDifferential.mapBaseChange A B C

/-- Change the base from A to B, leaving the target C unchanged. -/
def towerMapV : Specs.AdvCommAlg.Differentials.towerMapVType.{u,v,w} :=
  fun A B C _ _ _ _ _ _ _ => KaehlerDifferential.map A B C C

theorem towerMapU_apply : Specs.AdvCommAlg.Differentials.towerMapUApply.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ c b
  change KaehlerDifferential.mapBaseChange A B C _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

theorem towerMapV_apply : Specs.AdvCommAlg.Differentials.towerMapVApply.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ c
  exact KaehlerDifferential.map_D A B C C c

end
end AdvCommAlg.Differentials
