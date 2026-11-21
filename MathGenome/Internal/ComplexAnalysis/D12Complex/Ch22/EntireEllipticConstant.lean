import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.EntireEllipticConstant
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.Liouville
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Group.Bounded

/-! Entire lattice-periodic functions are bounded, hence constant by Liouville.
Mathlib's compact-range lemma reduces every point to a closed fundamental
parallelepiped; its only analytic hypothesis is continuity. -/

noncomputable section

namespace D12Complex.Ch22.EntireEllipticConstant

open D12Complex.Ch22.LatticeGeometry
open private lattice_eq_span_basis from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry

/-- The first assertion of d12:22-02, with no derivative-continuity assumption. -/
theorem entire_elliptic_constant :
    Specs.D12Complex.Ch22.EntireEllipticConstant.entire_elliptic_constant_type := by
  intro ω₁ ω₂ h₁ h₂ f hf hperiod
  let :=  discrete ω₁ ω₂ h₁ h₂
  let : IsZLattice ℝ (lattice ω₁ ω₂) := ⟨by
    rw [lattice_eq_span_basis h₁ h₂]
    exact ZSpan.span_top _⟩
  have hdiff : Differentiable ℂ f := fun z => hf.2 z (Set.mem_univ z)
  have hcont : Continuous f := hdiff.continuous
  have hcompact : IsCompact (Set.range f) :=
    IsZLattice.isCompact_range_of_periodic (lattice ω₁ ω₂) f hcont hperiod
  obtain ⟨M, hM⟩ := hcompact.isBounded.exists_norm_le
  exact D12Complex.Liouville.bounded_entire_constant f (max M 0) hf
    (le_max_right _ _) (fun z => (hM (f z) (Set.mem_range_self z)).trans (le_max_left _ _))

end D12Complex.Ch22.EntireEllipticConstant
