import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Relative.GenericCocharacterMinimalParabolic

open CharacterDescent (Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition unitPoint)
open MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)

/-- A cocharacter of a maximal split torus defines a minimal rational parabolic
if every absolute root of pairing zero restricts trivially to that split torus. -/
def GenericCocharacterMinimality : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    (G : AffineAlgebraicGroup F), IsReductive G →
    ∀ (S : ClosedSubgroup G.val), IsMaximalSplitTorus S →
    ∀ (c : Cocharacter S.group) (J : LimitDecomposition (c ≫ S.inclusion))
      (G₀ : AffineAlgebraicGroup K), IsReductive G₀ →
    ∀ (T : ClosedSubgroup G₀.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    let B := groupBaseChange F K
    ∀ (f : G₀.val ≅ B.obj G.val) (s : B.obj S.group ⟶ T.group),
      s ≫ T.inclusion ≫ f.hom = B.map S.inclusion →
    ∀ (e : specGroup (groupAlgebra K IntegerCharacters) ≅
        B.obj (specGroup (groupAlgebra F IntegerCharacters))),
      (∀ (R : TestAlgebra K) (t : Rˣ),
        baseChangePoint F K (specGroup (groupAlgebra F IntegerCharacters)).X R
          (unitPoint R t ≫ e.hom.hom.hom) =
        unitPoint ((restrictTestAlgebra F K).obj R) t) →
      (∀ χ ∈ absoluteRoots T, pairing T.group χ (e.hom ≫ B.map c ≫ s) = 0 →
        s ≫ χ = 1) →
      IsMinimalParabolic G J.parabolic

end LinearAlgebraicGroups.Specs.Relative.GenericCocharacterMinimalParabolic
