import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.LocalField.Basic

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Matrix TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingQuadraticSpinRankOne

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open IsotropicSpinGeneration (HyperbolicPair)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification
  (ScalarClifford vectors IsSpinPointRepresentation)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport (pointTopology)
open _root_.LinearAlgebraicGroups.CocharacterDynamics
  (HasLimit cocharacterPoint oppositeCocharacter)

noncomputable section

variable {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]

/-- The upper transvection in the matrix model of `SL₂`. -/
def upper {R : Type u} [CommRing R] (x : R) :
    Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R :=
  Matrix.SpecialLinearGroup.transvection (i := ⟨0⟩) (j := ⟨1⟩) (by decide) x

/-- The lower transvection in the matrix model of `SL₂`. -/
def lower {R : Type u} [CommRing R] (x : R) :
    Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R :=
  Matrix.SpecialLinearGroup.transvection (i := ⟨1⟩) (j := ⟨0⟩) (by decide) x

/-- The matrix-unit map associated to a hyperbolic pair and a nonisotropic
vector in its perpendicular space. -/
def cliffordMatrix (q : QuadraticForm F V) (h : HyperbolicPair q) (w : h.perpendicular)
    (R : TestAlgebra F) (M : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) R) :
    ScalarClifford q R :=
  let e := vectors q R (1 ⊗ₜ[F] h.e)
  let f := vectors q R (1 ⊗ₜ[F] h.f)
  let z := vectors q R (1 ⊗ₜ[F] w.val)
  M ⟨0⟩ ⟨0⟩ • (e * f) + M ⟨0⟩ ⟨1⟩ • (e * z) +
    M ⟨1⟩ ⟨0⟩ • (-(algebraMap F R ((q w.val)⁻¹)) • (f * z)) +
    M ⟨1⟩ ⟨1⟩ • (f * e)

/-- The embedded determinant-one subgroup supplies a whole transvection line
contracted by the inverse of the input cocharacter. Its own diagonal yields
the two opposite contracting subgroups that generate densely. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G →
    ∀ (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (q : QuadraticForm F V)
      (ρ : ∀ R : TestAlgebra F, GroupPoints G.val R →* (ScalarClifford q R)ˣ),
      5 ≤ Module.finrank F V → IsotropicSpinGeneration.IsRegular q →
      IsotropicSpinGeneration.IsIsotropic q → IsSpinPointRepresentation q G.val ρ →
      ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      ∀ c : Cocharacter S.group, Relative.RelativeChambers.IsRegular S c →
      ∃ (h : HyperbolicPair q) (w : h.perpendicular), q w.val ≠ 0 ∧
      ∃ (A : AffineAlgebraicGroup F) (j : A.val ⟶ G.val),
        IsClosedImmersion j.hom.hom.left ∧
      ∃ (e : (groupPointsFunctor F).obj A.val ≅
          StandardGroups.specialLinearPoints F (ULift.{u} (Fin 2)))
        (b : Cocharacter A.val),
        let d : Cocharacter G.val := b ≫ j
        let K := CommAlgCat.of F F
        let includePoint (R : TestAlgebra F)
            (M : Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R) : GroupPoints G.val R :=
          ((groupPointsFunctor F).map j).app R (e.inv.app R M)
        let u (R : TestAlgebra F) (x : R) := includePoint R (upper x)
        let v (R : TestAlgebra F) (x : R) := includePoint R (lower x)
        (∀ (R : TestAlgebra F) (M : Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R),
          (ρ R (includePoint R M)).val = cliffordMatrix q h w R M.val) ∧
        (∀ (R : TestAlgebra F) (t : Rˣ),
          (show Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) R from
            e.hom.app R (cocharacterPoint b R t)).val =
            Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm !![(t : R), 0; 0, (↑t⁻¹ : R)]) ∧
        (∀ (R : TestAlgebra F) (x : R),
          HasLimit d (u R x) 1 ∧ HasLimit (oppositeCocharacter d) (v R x) 1) ∧
        ((∀ x : F, HasLimit (oppositeCocharacter (c ≫ S.inclusion)) (u K x) 1) ∨
         (∀ x : F, HasLimit (oppositeCocharacter (c ≫ S.inclusion)) (v K x) 1)) ∧
        (letI : TopologicalSpace (GroupPoints G.val K) := pointTopology G.val.X
         Dense (Subgroup.closure
           ({g : GroupPoints G.val K | HasLimit d g 1} ∪
            {g : GroupPoints G.val K | HasLimit (oppositeCocharacter d) g 1}) :
              Set (GroupPoints G.val K)))

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingQuadraticSpinRankOne
