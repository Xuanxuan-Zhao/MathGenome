import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianFixedRootSL2

open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open GeneralLinearStructure (SpecialMatrixPoints)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (IsSemisimple baseChangedSubgroup)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (AttachedDatum Pinning SimpleRoot)
open QuasiSplitFixedWeyl (IsLargestSplitSubtorus)
open QuasiSplitOrbitDerivedRoots (diagramRoot)
open QuasiSplitOrbitLevis (IsAmbientPinnedAction MultiplicativeComparison PreservesUnits SplitPairOver)
open QuasiSplitPinnedPairModel (BorelPair)
open RankOneFlag (SameSubgroup)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open RootGroups (AdditiveLine rootPoint)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (Index)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

/-- A split determinant-one rank-one subgroup with its elementary subgroups
and diagonal inside the given ambient group and split torus. -/
structure RankOne (S : ClosedSubgroup G.val) where
  group : AffineAlgebraicGroup F
  matrix : SpecialMatrixPoints group 2
  embedding : group.val ⟶ G.val
  closedEmbedding : IsClosedImmersion embedding.hom.hom.left
  trivialKernel : IsPullback (η[group.val.X]) (𝟙 _) embedding.hom.hom (η[G.val.X])
  positive : ClosedSubgroup G.val
  negative : ClosedSubgroup G.val
  additive : AdditiveLine F
  upper : additive.group ≅ positive.group
  lower : additive.group ≅ negative.group
  cochar : Cocharacter S.group
  upperFormula : ∀ (R : TestAlgebra F) (x : R),
    (((matrix.inv.app R) (Matrix.SpecialLinearGroup.transvection
      (i := (⟨0⟩ : Index.{u} 2)) (j := (⟨1⟩ : Index.{u} 2)) (by decide) x)) :
        GroupPoints group.val R) ≫ embedding.hom.hom =
      rootPoint (upper.hom ≫ positive.inclusion) R x
  lowerFormula : ∀ (R : TestAlgebra F) (x : R),
    (((matrix.inv.app R) (Matrix.SpecialLinearGroup.transvection
      (i := (⟨1⟩ : Index.{u} 2)) (j := (⟨0⟩ : Index.{u} 2)) (by decide) x)) :
        GroupPoints group.val R) ≫ embedding.hom.hom =
      rootPoint (lower.hom ≫ negative.inclusion) R x
  diagonalFormula : ∀ (R : TestAlgebra F) (v : Rˣ), ∃ x : GroupPoints group.val R,
    x ≫ embedding.hom.hom = cocharacterPoint (cochar ≫ S.inclusion) R v ∧
    (matrix.hom.app R x).val = Matrix.diagonal (fun i : Index.{u} 2 ↦
      if i.down = 0 then (v : R) else (↑v⁻¹ : R))

/-- The fixed simple root descends with its prescribed pin and with primitive
absolute coroot. All point formulas use the full functors on test algebras. -/
def Statement : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (G : AffineAlgebraicGroup F), IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (M : BorelPair G) (S : ClosedSubgroup M.torus.group),
      IsLargestSplitSubtorus S → IsMaximalSplitTorus (subgroupOfSubgroup M.torus S) →
      ∀ (P : SplitPairOver (K := K) G M.torus M.positive) (D : AttachedDatum P.pair)
        (A₀ : AdditiveLine F) (A : AdditiveLine K)
        (U : RootSubgroupFamily P.pair.T) (p : Pinning A P.pair U)
        (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
        (m : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased),
        PreservesUnits m → IsAmbientPinnedAction D p a m ω →
        (∀ (R : TestAlgebra K) (x : R),
          baseChangePoint F K A₀.group.X R (rootPoint a.inv R x) =
            rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) x) →
        ∀ α : SimpleRoot P.pair, (∀ σ, diagramRoot ω σ α.val = α.val) →
          letI := D.comm
          ∃ (β : Root P.pair.T) (H : RankOne (subgroupOfSubgroup M.torus S)),
            β.val = α.val.val⁻¹ ∧
            (∃ hp hn,
              SameSubgroup (baseChangedSubgroup K H.positive hp) (U α.val).val ∧
              SameSubgroup (baseChangedSubgroup K H.negative hn) (U β).val) ∧
            (∀ (R : TestAlgebra K) (x : R),
              baseChangePoint F K G.val.X R
                (rootPoint ((p α).val.hom ≫ (U α.val).val.inclusion) R x) =
                rootPoint (H.upper.hom ≫ H.positive.inclusion)
                  ((restrictTestAlgebra F K).obj R) x) ∧
            Additive.ofMul (m.hom ≫ (groupBaseChange F K).map (H.cochar ≫ S.inclusion)) =
              D.datum.rootDatum.coroot α.val ∧
            ∃ f : Additive (Cocharacter P.pair.T.group) →ₗ[ℤ] ℤ,
              f (D.datum.rootDatum.coroot α.val) = 1

end

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianFixedRootSL2
