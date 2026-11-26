import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusCentralizer
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Notation

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace LinearAlgebraicGroups.Specs.RealTori

open GeometricRadicals (IsMaximalTorus IsSplitTorus IsTorus baseChangedSubgroup)
open GeometricBorelConjugacy (ConjugatesSubgroups)

noncomputable section

abbrev SL₂Points := StandardGroups.specialLinearPoints ℝ (Fin 2)

def diagonalMatrix {R : Type} [CommRing R] (t : Rˣ) : Matrix (Fin 2) (Fin 2) R :=
  !![(t : R), 0; 0, (↑t⁻¹ : R)]

def rotationMatrix {R : Type} [CommRing R] (a b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, -b; b, a]

def GeometricallyMaximal {G : GroupScheme ℝ} (T : ClosedSubgroup G) : Prop :=
  ∃ h : IsClosedImmersion
      ((groupBaseChange ℝ (AlgebraicClosure ℝ)).map T.inclusion).hom.hom.left,
    IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure ℝ) T h)

/-- The inclusion evaluated as a determinant-one matrix on a test algebra. -/
abbrev matrixPoint {G : GroupScheme ℝ} (e : (groupPointsFunctor ℝ).obj G ≅ SL₂Points)
    (T : ClosedSubgroup G) (R : TestAlgebra ℝ) (p : Points T.group.X R) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  e.hom.app R (((groupPointsFunctor ℝ).map T.inclusion).app R p)

/-- A complex test point of the real group, evaluated in the standard representation. -/
abbrev complexMatrixPoint {G : GroupScheme ℝ}
    (e : (groupPointsFunctor ℝ).obj G ≅ SL₂Points) (T : ClosedSubgroup G)
    (R : TestAlgebra ℂ) (p : Points ((groupBaseChange ℝ ℂ).obj T.group).X R) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  matrixPoint e T ((restrictTestAlgebra ℝ ℂ).obj R) (baseChangePoint ℝ ℂ T.group.X R p)

abbrev RankOneTorus (k : Type) [Field k] :=
  (StandardGroups.multiplicativePowerGroup k (ULift (Fin 1))).val

abbrev characterValue {V : GroupScheme ℂ}
    (u : (groupPointsFunctor ℂ).obj (RankOneTorus ℂ) ≅ StandardGroups.multiplicativePoints ℂ)
    (chi : V ⟶ RankOneTorus ℂ) (R : TestAlgebra ℂ) (p : Points V.X R) : Rˣ :=
  u.hom.app R (((groupPointsFunctor ℂ).map chi).app R p)

/-- The eigencharacters on the two displayed eigenvectors and their exchange under
complex conjugation. Semilinearity in the last clause expresses the exchange on
all complex algebras. -/
def RotationCharacters {G : GroupScheme ℝ}
    (e : (groupPointsFunctor ℝ).obj G ≅ SL₂Points) (T : ClosedSubgroup G) : Prop :=
  let V := (groupBaseChange ℝ ℂ).obj T.group
  ∃ (u : (groupPointsFunctor ℂ).obj (RankOneTorus ℂ) ≅ StandardGroups.multiplicativePoints ℂ)
    (chiPlus : V ≅ RankOneTorus ℂ) (chiMinus : V ⟶ RankOneTorus ℂ),
    chiPlus.hom ≠ chiMinus ∧
    (∀ (R : TestAlgebra ℂ) (p : Points V.X R),
      let M := complexMatrixPoint e T R p
      let i := algebraMap ℂ R Complex.I
      let zPlus := characterValue u chiPlus.hom R p
      let zMinus := characterValue u chiMinus R p
      (zPlus : R) = M 0 0 + i * M 1 0 ∧
      (zMinus : R) = M 0 0 - i * M 1 0 ∧ zPlus * zMinus = 1 ∧
      M.val *ᵥ ![1, -i] = (zPlus : R) • (![1, -i] : Fin 2 → R) ∧
      M.val *ᵥ ![1, i] = (zMinus : R) • (![1, i] : Fin 2 → R)) ∧
    (∀ (R S : TestAlgebra ℂ)
      (f : (restrictTestAlgebra ℝ ℂ).obj R ⟶ (restrictTestAlgebra ℝ ℂ).obj S)
      (_ : ∀ z : ℂ, f.hom (algebraMap ℂ R z) = algebraMap ℂ S (star z))
      (p : Points V.X R) (q : Points V.X S),
      baseChangePoint ℝ ℂ T.group.X S q = mapPoints f (baseChangePoint ℝ ℂ T.group.X R p) →
      f.hom (characterValue u chiPlus.hom R p : R) = (characterValue u chiMinus S q : S) ∧
      f.hom (characterValue u chiMinus R p : R) = (characterValue u chiPlus.hom S q : S))

/-- The diagonal and rotation tori in the standard real determinant-one group.
The two complex characters are realized by homomorphisms of group schemes,
with the indicated eigenvectors on every complex test algebra. -/
def RealMaximalTori : Prop :=
  ∃ (G : AffineAlgebraicGroup ℝ) (e : (groupPointsFunctor ℝ).obj G.val ≅ SL₂Points)
    (D T : ClosedSubgroup G.val),
    (∀ (R : TestAlgebra ℝ) (g : Matrix.SpecialLinearGroup (Fin 2) R),
      (∃ p : Points D.group.X R, matrixPoint e D R p = g) ↔
        ∃ t : Rˣ, g.val = diagonalMatrix t) ∧
    (∀ (R : TestAlgebra ℝ) (g : Matrix.SpecialLinearGroup (Fin 2) R),
      (∃ p : Points T.group.X R, matrixPoint e T R p = g) ↔
        ∃ a b : R, a ^ 2 + b ^ 2 = 1 ∧ g.val = rotationMatrix a b) ∧
    Nonempty (D.group ≅ (StandardGroups.multiplicativePowerGroup ℝ (ULift (Fin 1))).val) ∧
    IsTorus T.group ∧
    GeometricallyMaximal D ∧ GeometricallyMaximal T ∧
    RotationCharacters e T ∧
    ¬ IsSplitTorus T.group ∧
    ¬ ∃ g, ConjugatesSubgroups g D T

end

end LinearAlgebraicGroups.Specs.RealTori
