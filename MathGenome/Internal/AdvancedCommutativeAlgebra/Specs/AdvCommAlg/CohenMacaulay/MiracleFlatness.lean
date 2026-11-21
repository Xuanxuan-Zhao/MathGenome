import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Torsion.Basic

/-! CM-13, paper.tex:3702–3728. The closed fiber is S/mS and its module
is N/(mS)N with the canonical quotient action. Finiteness is over S only. -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

noncomputable def miracleFlatnessType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (N : Type u) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [Nontrivial N],
    LocalCohenMacaulayValue S N →
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    dimensionValue S N = ringKrullDim R +
      Module.supportDim (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) →
    Module.Flat R N

noncomputable def miracleFlatnessRingType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)],
    LocalCohenMacaulayValue S S →
    ringKrullDim S = ringKrullDim R +
      ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) →
    Module.Flat R S

end AdvCommAlg.CohenMacaulay.Specs
