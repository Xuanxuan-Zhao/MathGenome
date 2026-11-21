import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.BaseChange
import Mathlib.RingTheory.LocalRing.Module

/-! Independent statements for the support and dimension clauses of CM-10,
`paper.tex:3504–3512, 3523–3560`. The closed fiber is the quotient by the
extension of the maximal ideal, with its canonical quotient-ring action.
The tensor product uses the existing right-factor action from RK-02.
Only N, and not S, is assumed flat over R. -/

universe u
open scoped TensorProduct
namespace AdvCommAlg.CohenMacaulay.Specs

/-- Nonvanishing of N/mN; this clause does not need flatness. -/
def closedFiber_nontrivialType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (N : Type u) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N] [Nontrivial N],
  Nontrivial (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
    (⊤ : Submodule S N)))

/-- The tensor product is nonzero under the original CM-10 hypotheses. -/
def flatLocal_tensor_nontrivialType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N], Nontrivial (M ⊗[R] N)

/-- The exact support formula with contraction along the structural map. -/
def flatLocal_tensor_supportType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N],
  Module.support S (M ⊗[R] N) = Module.support S N ∩
    (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' Module.support R M

/-- The full dimension equality over the closed fiber ring S/mS. -/
noncomputable def flatLocal_tensor_dimensionType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N],
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  Module.supportDim S (M ⊗[R] N) = Module.supportDim R M +
    Module.supportDim (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N)))

end AdvCommAlg.CohenMacaulay.Specs
