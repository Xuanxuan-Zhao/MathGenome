import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Type

/-! CM-18 (paper.tex:3911–3950). Type uses Ext in the depth degree.
The closed fiber has its quotient-ring action; its residue field is the
residue field of S/mS, whereas the base type is measured over R/m. -/
universe u
open scoped TensorProduct
namespace AdvCommAlg.CohenMacaulay.Specs

noncomputable def flatLocal_tensor_typeType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N],
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := closedFiberLocalRing R S
  AdvCommAlg.Depth.Specs.moduleTypeValue S (ModuleCat.of S (M ⊗[R] N)) =
    AdvCommAlg.Depth.Specs.moduleTypeValue R (ModuleCat.of R M) *
    AdvCommAlg.Depth.Specs.moduleTypeValue (S ⧸ J)
      (ModuleCat.of (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))

end AdvCommAlg.CohenMacaulay.Specs
