import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Trapping
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.PoincareBendixson
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Invariant

/-! The trapping corollary of Poincaré–Bendixson (paper.tex, d13:13:trapping).
Compact continuation first supplies forward completeness. Closedness keeps
the positive orbit closure, and hence its omega-limit set, in the trapping
set. Poincaré–Bendixson supplies the contained complete periodic orbit. -/
noncomputable section
open Set

namespace D13Unified.Ch13.Trapping
open Ch13.Nullclines Ch06.StateDerivative Ch11.Orbits
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch11.OmegaTopology

/-- A compact positively invariant planar set without equilibria contains
a complete nonconstant periodic classical solution. -/
theorem trapping : Specs.D13Unified.Ch13.Trapping.Trapping := by
  intro F hF K hne hK hInv hregular
  have hforward := Ch11.Invariant.compact_forward_complete F hF K hK hInv
  refine ⟨hforward, ?_⟩
  obtain ⟨x, hx⟩ := hne
  have hpos : positiveOrbit F x ⊆ K := by
    rintro _ ⟨t, ⟨_, ht⟩, rfl⟩
    exact (hforward x hx).2 t ht
  have hcl : closure (positiveOrbit F x) ⊆ K := closure_minimal hpos hK.isClosed
  have hcompact : IsCompact (closure (positiveOrbit F x)) :=
    hK.of_isClosed_subset isClosed_closure hcl
  have homega : omegaValue F x ⊆ K := by
    intro p hp
    exact hcl (mem_iInter.mp (mem_iInter.mp hp 0) (le_refl 0))
  obtain ⟨p, hp, hnonconstant, hperiod, heq⟩ :=
    Ch13.PoincareBendixson.poincare_bendixson F hF x (hInv.1 hx)
      hcompact (hcl.trans hInv.1) (fun p hp => hregular p (homega hp))
  have hpK : p ∈ K := homega hp
  have horbit : orbit F p ⊆ K := by rw [← heq]; exact homega
  have hsol := flow_ivp F hF (hInv.1 hpK)
  have hcomplete : (flowInterval F p).carrier = univ := hperiod.1
  refine ⟨p, hpK, hnonconstant, hperiod, horbit, ?_, ?_, hsol.2.2⟩
  · exact contDiffOn_univ.mp (hcomplete ▸ hsol.1.1)
  · intro t
    exact hsol.1.2.2 t (hcomplete.symm ▸ mem_univ t)

end D13Unified.Ch13.Trapping
