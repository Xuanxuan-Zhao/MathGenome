import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.ContractionConsequences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.Banach
import Mathlib.Tactic.Linarith

/-! Consequences of Banach's theorem from paper.tex, Chapter 14.
For an iterate contraction, uniqueness for the iterate forces T p = p;
this uses only commutation of a map with its iterates. For perturbations,
the triangle inequality yields (1-q) d(pS,pT) ≤ δ. -/
universe u
namespace D10Topology.Ch14

theorem iterate_contraction :
    Specs.D10Topology.Ch14.ContractionConsequences.iterate_contraction.{u} := by
  intro X d hnonempty hcomplete T m q _hm hq₀ hq₁ hcontract
  obtain ⟨p, hp, huniq, _⟩ :=
    banach_contraction d hnonempty hcomplete (T^[m]) q hq₀ hq₁ hcontract
  have hTp : T p = p := by
    apply huniq
    calc
      T^[m] (T p) = T^[m.succ] p := (Function.iterate_succ_apply T m p).symm
      _ = T (T^[m] p) := Function.iterate_succ_apply' T m p
      _ = T p := congrArg T hp
  refine ⟨p, hTp, ?_⟩
  intro x hx
  apply huniq
  exact Function.IsFixedPt.iterate hx m

theorem fixed_point_stability :
    Specs.D10Topology.Ch14.ContractionConsequences.fixed_point_stability.{u} := by
  intro X d hnonempty hcomplete S T q δ hq₀ hq₁ hS hT hperturb
  obtain ⟨pS, hpS, huniqS, _⟩ :=
    banach_contraction d hnonempty hcomplete S q hq₀ hq₁ hS
  obtain ⟨pT, hpT, huniqT, _⟩ :=
    banach_contraction d hnonempty hcomplete T q hq₀ hq₁ hT
  refine ⟨pS, pT, hpS, hpT, huniqS, huniqT, ?_⟩
  let := d
  change dist pS pT ≤ δ / (1 - q)
  apply (le_div_iff₀ (sub_pos.mpr hq₁)).mpr
  have hdist : dist pS pT ≤ δ + q * dist pS pT := by
    calc
      dist pS pT = dist (S pS) (T pT) := by rw [hpS, hpT]
      _ ≤ dist (S pS) (T pS) + dist (T pS) (T pT) := dist_triangle _ _ _
      _ ≤ δ + q * dist pS pT := add_le_add (hperturb pS) (hT pS pT)
  linarith

end D10Topology.Ch14
