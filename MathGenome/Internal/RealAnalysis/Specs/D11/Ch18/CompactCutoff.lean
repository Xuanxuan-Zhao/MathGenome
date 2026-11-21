import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero

/-!
Independent statement of paper.tex:5346, `d11:18:compact-cutoff`.
The witness uses the canonical native Cc space fixed by the Chapter 19
definition interface. Support is written literally as the closure of the
nonzero set. No countability or nonemptiness is assumed.
-/

namespace Specs.D11.Ch18.CompactCutoff

universe u

/-- A compact set in an open set of an LCH space admits a real compactly
supported cutoff, with its entire closed support contained in that open set. -/
def compact_cutoff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (K U : Set X), IsCompact K → IsOpen U → K ⊆ U →
    ∃ φ : CompactlySupportedContinuousMap X ℝ,
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ K, φ x = 1) ∧
      IsCompact (closure {x | φ x ≠ 0}) ∧
      closure {x | φ x ≠ 0} ⊆ U

end Specs.D11.Ch18.CompactCutoff
