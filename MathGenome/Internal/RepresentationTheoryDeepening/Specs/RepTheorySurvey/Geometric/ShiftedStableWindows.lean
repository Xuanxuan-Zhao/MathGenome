import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.BoundedLattices

namespace RepTheorySurvey.Geometric.ShiftedStableWindowsSpecs

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points)
open LatticeModelSpecs BoundedLatticeSpecs

noncomputable section

set_option autoImplicit false

/-- Scalar multiplication by (t^a) on lattices in (K^2). -/
def translate (a : ℤ) (L : GL2Lattice) : GL2Lattice :=
  mapLattice (diagonalEquiv (fun _ : Fin 2 ↦ a)) L

/-- The linear equivalence that keeps the jet coefficients in the translated window. -/
def shiftWindow (a b : ℤ) (m : ℕ) : Window 2 b m ≃ₗ[ℂ] Window 2 (b + a) m :=
  windowCoordinates 2 b m ≪≫ₗ (windowCoordinates 2 (b + a) m).symm

/-- Scalar translation realizes the shift on the reduced stable schemes and gives
a closed immersion into every symmetric window containing the translated interval. -/
def WindowTranslation : Prop :=
  ∀ (a b : ℤ) (m : ℕ),
    (∀ L : WindowLattice 2 b m,
      ((scalarLattice 2 (b + a + (m : ℤ))).val ≤ (translate a L.val).val ∧
        (translate a L.val).val ≤ (scalarLattice 2 (b + a)).val) ∧
      latticeSubspace (b + a) m (translate a L.val) =
        (latticeSubspace b m L.val).map (shiftWindow a b m).toLinearMap) ∧
    (∀ x : Window 2 b m,
      shiftWindow a b m (windowOperator 2 b m x) =
        windowOperator 2 (b + a) m (shiftWindow a b m x)) ∧
    ∀ d : WindowDimension 2 b m,
      ∃ d' : WindowDimension 2 (b + a) m, d'.val = d.val ∧
        ∃ e : windowStableScheme 2 b m d ≅ windowStableScheme 2 (b + a) m d',
          (∀ q : Points (windowStableScheme 2 b m d) complexAlgebra,
            windowSchemeSubspace (q ≫ e.hom) =
              (windowSchemeSubspace q).map (shiftWindow a b m).toLinearMap) ∧
          ∀ (M : ℕ), -(M : ℤ) ≤ b + a → b + a + (m : ℤ) ≤ (M : ℤ) →
            ∃ (d'' : WindowDimension 2 (-(M : ℤ)) (2 * M))
              (j : windowStableScheme 2 b m d ⟶ windowStableScheme 2 (-(M : ℤ)) (2 * M) d''),
              (d''.val : ℤ) = (d.val : ℤ) + 2 * ((M : ℤ) - (b + a + (m : ℤ))) ∧
              IsClosedImmersion j.left ∧
              ∀ (q : Points (windowStableScheme 2 b m d) complexAlgebra)
                (L : WindowLattice 2 b m),
                windowSchemeSubspace q = latticeSubspace b m L.val →
                  windowSchemeSubspace (q ≫ j) =
                    latticeSubspace (-(M : ℤ)) (2 * M) (translate a L.val)

end

end RepTheorySurvey.Geometric.ShiftedStableWindowsSpecs
