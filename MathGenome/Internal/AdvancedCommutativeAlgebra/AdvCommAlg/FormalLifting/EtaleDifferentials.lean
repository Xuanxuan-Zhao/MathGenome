import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.TowerMaps
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.EtaleDifferentials
import Mathlib.RingTheory.Etale.Kaehler

/-! FL-11: a formally étale intermediate map preserves absolute
differentials after extending scalars. No finiteness, flatness, or
nontriviality hypothesis is required. -/
namespace AdvCommAlg.FormalLifting

universe u v w
open scoped TensorProduct

/-- The canonical map D ⊗[B] Ω_{B/A} → Ω_{D/A} is an isomorphism
when B → D is formally étale, with its prescribed value on differentials. -/
theorem etale_differentials :
    Specs.AdvCommAlg.FormalLifting.etaleDifferentials.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ h
  let : Algebra.FormallyEtale B D := (formallyEtale_iff B D).mp h
  refine ⟨KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B D, rfl, ?_⟩
  intro b
  change KaehlerDifferential.mapBaseChange A B D _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]

end AdvCommAlg.FormalLifting
