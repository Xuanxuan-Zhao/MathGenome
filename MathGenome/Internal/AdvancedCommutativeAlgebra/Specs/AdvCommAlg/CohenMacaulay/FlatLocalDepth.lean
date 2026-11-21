import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.BaseChange

/-! The depth clause of CM-10, paper.tex:3504–3515 and 3579–3592.
Only the module N is required to be flat over the base. Depth is the
regular-sequence depth of chapter 6. -/
universe u
open scoped TensorProduct
namespace AdvCommAlg.CohenMacaulay.Specs

/-- The actual closed fiber ring is local, since the original map is local. -/
@[instance_reducible] def closedFiberLocalRing (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] :
    IsLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  letI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

noncomputable def flatLocal_tensor_depthType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N],
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := closedFiberLocalRing R S
  AdvCommAlg.Depth.Specs.depthValue S (M ⊗[R] N) =
    AdvCommAlg.Depth.Specs.depthValue R M +
    AdvCommAlg.Depth.Specs.depthValue (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N)))

end AdvCommAlg.CohenMacaulay.Specs
