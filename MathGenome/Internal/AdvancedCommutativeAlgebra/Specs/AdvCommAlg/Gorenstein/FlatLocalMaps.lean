import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalDepth
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! GC-08, paper.tex:4622–4640, flat local equivalence.
The closed fiber is the actual quotient by the extended maximal ideal.
`IsLocalRing` includes nonzeroness; no Cohen–Macaulay assumption is made.
Completion and étale consequences are allocated separately.
-/

universe u
namespace AdvCommAlg.Gorenstein.FlatLocalMapsSpecs

noncomputable def flatLocal_gorensteinType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S],
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := CohenMacaulay.Specs.closedFiberLocalRing R S
  Specs.LocalGorensteinValue S ↔
    Specs.LocalGorensteinValue R ∧ Specs.LocalGorensteinValue (S ⧸ J)

end AdvCommAlg.Gorenstein.FlatLocalMapsSpecs
