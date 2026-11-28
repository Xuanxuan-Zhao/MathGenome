import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

namespace RepTheorySurvey.Geometric.LatticeWindowInclusionCoordinateSpecs

open LatticeModelSpecs

/-- In nested lattice windows, the larger quotient of a lattice in the smaller
window is the smaller quotient together with the full lower summand and a zero
upper component. -/
def WindowInclusionCoordinates : Prop :=
  ∀ (r : ℕ) (a b : ℤ) (m k : ℕ), b ≤ a → a + (m : ℤ) ≤ b + (k : ℤ) →
    let α := (a - b).toNat
    let β := (b + (k : ℤ) - (a + (m : ℤ))).toNat
    ∃ e : Window r b k ≃ₗ[ℂ] Window r a m ×
        ((Fin r × Fin β → ℂ) × (Fin r × Fin α → ℂ)),
      (∀ (L : Lattice r), (scalarLattice r (a + (m : ℤ))).val ≤ L.val →
        L.val ≤ (scalarLattice r a).val → ∀ w : Window r b k,
          w ∈ latticeSubspace b k L ↔ (e w).1 ∈ latticeSubspace a m L ∧ (e w).2.2 = 0) ∧
      Module.finrank ℂ (Fin r × Fin β → ℂ) = r * β ∧
      Module.finrank ℂ (Fin r × Fin α → ℂ) = r * α

end RepTheorySurvey.Geometric.LatticeWindowInclusionCoordinateSpecs
