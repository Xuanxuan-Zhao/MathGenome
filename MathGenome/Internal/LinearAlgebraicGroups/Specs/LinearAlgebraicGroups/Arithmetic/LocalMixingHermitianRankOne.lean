import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeALocalModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import Mathlib.NumberTheory.LocalField.Basic

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingHermitianRankOne

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (IsRegular)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open OuterTypeALocalModels (RepresentsHermitian)
open UnitaryRankOne (quadraticConjugation)
open LinearAlgebraicGroups.CocharacterDynamics (HasLimit cocharacterPoint oppositeCocharacter)
open LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport (pointTopology)

noncomputable section

variable {F : Type u} [Field F]

abbrev RankOneIndex := ULift.{u} (Fin 2)

/-- The image of an elementary matrix under the marked rank-one inclusion. -/
def transvectionPoint {A G : AffineAlgebraicGroup F} (j : A.val ⟶ G.val)
    (e : (groupPointsFunctor F).obj A.val ≅ StandardGroups.specialLinearPoints F RankOneIndex)
    (R : TestAlgebra F) {i k : RankOneIndex.{u}} (hik : i ≠ k) (x : R) :
    GroupPoints G.val R :=
  ((groupPointsFunctor F).map j).app R
    (e.inv.app R (Matrix.SpecialLinearGroup.transvection hik x))

/-- A hyperbolic plane supplies a split rank-one subgroup whose diagonal lies
in the given maximal split torus and whose two opposite limit radicals
generate densely in the original local points. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple G →
    ∀ (E : Type u) [Field E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
      {n : ℕ} (H : (Matrix (Fin n) (Fin n) E)ˣ),
      let σ := quadraticConjugation F E
      (H.val.map σ).transpose = H.val →
      (∃ x : Fin n → E, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.val.mulVec x) = 0) →
      RepresentsHermitian σ H.val G →
      ∀ (S : ClosedSubgroup G.val), IsMaximalSplitTorus S →
        ∀ (c : Cocharacter S.group), IsRegular S c →
          ∃ (A : AffineAlgebraicGroup F) (j : A.val ⟶ G.val)
            (e : (groupPointsFunctor F).obj A.val ≅
              StandardGroups.specialLinearPoints F RankOneIndex)
            (b : Cocharacter A.val),
            IsClosedImmersion j.hom.hom.left ∧
            (∀ (R : TestAlgebra F) (t : Rˣ),
              (show Matrix.SpecialLinearGroup RankOneIndex.{u} R from
                e.hom.app R (cocharacterPoint b R t)).val =
                Matrix.diagonal (fun i : RankOneIndex.{u} =>
                  if i.down = 0 then (t : R) else (↑t⁻¹ : R))) ∧
            let d : Cocharacter G.val := b ≫ j
            (∃ s : Cocharacter S.group, s ≫ S.inclusion = d) ∧
            let upper (R : TestAlgebra F) (x : R) :=
              transvectionPoint j e R (i := ⟨0⟩) (k := ⟨1⟩) (by decide) x
            let lower (R : TestAlgebra F) (x : R) :=
              transvectionPoint j e R (i := ⟨1⟩) (k := ⟨0⟩) (by decide) x
            let R₀ := CommAlgCat.of F F
            (∀ (R : TestAlgebra F) (x : R),
              HasLimit d (upper R x) 1 ∧
                HasLimit (oppositeCocharacter d) (lower R x) 1) ∧
            ((∀ x : F, HasLimit (oppositeCocharacter (c ≫ S.inclusion)) (upper R₀ x) 1) ∨
              (∀ x : F, HasLimit (oppositeCocharacter (c ≫ S.inclusion)) (lower R₀ x) 1)) ∧
            @Dense (GroupPoints G.val R₀) (pointTopology G.val.X) (Subgroup.closure
              ({g : GroupPoints G.val R₀ | HasLimit d g 1} ∪
                {g : GroupPoints G.val R₀ | HasLimit (oppositeCocharacter d) g 1}) :
                  Set (GroupPoints G.val R₀))

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingHermitianRankOne
