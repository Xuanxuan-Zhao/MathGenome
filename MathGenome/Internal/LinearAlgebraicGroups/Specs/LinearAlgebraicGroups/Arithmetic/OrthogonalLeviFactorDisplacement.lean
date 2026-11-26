import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.OrthogonalLeviFactorDisplacement

open AutomorphismSequence (AdjointQuotient SplitSequence RelativeAut)
open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open GeneralLinearStructure (SpecialMatrixPoints)
open GeometricRadicals (IsReductive)
open Pinning (AttachedDatum PinnedGroup)
open QuasiSplitInnerForms (outerHom)
open RelativeFormComparison (IsInduced fieldTest)
open RootGroups (AdditiveLine)
open SchemeDerivedGroup (IsDerivedSubgroup)
open Unipotent (Index closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open StandardParabolicLevi (HasFace)

noncomputable section

variable {F : Type u} [Field F]

/-- The labelled projection identifies the specified root subgroup with the
upper transvections under the chosen matrix comparison on every test algebra. -/
def IsUpperRootProjection {U : GroupScheme F} {S : AffineAlgebraicGroup F}
    (s : SpecialMatrixPoints S 2) (f : U ⟶ S.val) : Prop :=
  ∀ R : TestAlgebra F,
    Function.Injective (((groupPointsFunctor F).map f).app R) ∧
      Set.range (fun x : Points U.X R =>
        s.hom.app R (((groupPointsFunctor F).map f).app R x)) =
      Set.range (fun t : R =>
        Matrix.SpecialLinearGroup.transvection
          (show (⟨0⟩ : Index.{u} 2) ≠ ⟨1⟩ by decide) t)

/-- The restriction of the displacement to the actual derived subgroup
transports its split rank-one projections by the outer permutation. -/
def FactorDisplacement : Prop :=
  ∀ (F K I : Type u) [Field F] [Field K] [Algebra F K] [Finite I] [Nonempty I]
    {A : AdditiveLine F} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (seq : SplitSequence P D l Q) (r : I ↪ D.toBased.I),
    Set.range r ⊆ D.toBased.base.support →
    ∀ (c : Cocharacter P.pair.T.group) (M₀ : LimitDecomposition (c ≫ P.pair.T.inclusion)),
      (letI := D.comm; HasFace D.base (Set.range r) c) →
      IsParabolic P.pair.G M₀.parabolic →
      IsReductive (closedSubgroupAlgebraicGroup M₀.centralizer) →
      ∀ (H₀ : ClosedSubgroup M₀.centralizer.group), IsDerivedSubgroup H₀ →
        let B := groupBaseChange F K
        ∀ (a : B.obj P.pair.G.val ≅ B.obj P.pair.G.val)
          (α : RelativeAut P.pair.G.val (fieldTest F K)),
          IsInduced F K a α.asIso →
          ∀ (p : B.obj M₀.parabolic.group ≅ B.obj M₀.parabolic.group)
            (b : B.obj M₀.centralizer.group ≅ B.obj M₀.centralizer.group)
            (δ : B.obj H₀.group ≅ B.obj H₀.group),
            B.map M₀.parabolic.inclusion ≫ a.hom = p.hom ≫ B.map M₀.parabolic.inclusion →
            B.map M₀.centralizer.inclusion ≫ a.hom = b.hom ≫ B.map M₀.centralizer.inclusion →
            B.map H₀.inclusion ≫ b.hom = δ.hom ≫ B.map H₀.inclusion →
            ∀ (τ : I ≃ I),
              (∀ i, (outerHom seq α).asIso.hom.val.indexEquiv (r i) = r (τ i)) →
              ∀ (S : AffineAlgebraicGroup F) (s : SpecialMatrixPoints S 2)
                (π : I → (H₀.group ⟶ S.val)),
                Nonempty (IsLimit (Fan.mk H₀.group π)) →
                ∀ (uᵣ : ∀ i, (P.roots (r i)).val.group ⟶ H₀.group),
                  (∀ i, uᵣ i ≫ H₀.inclusion ≫ M₀.centralizer.inclusion =
                    (P.roots (r i)).val.inclusion) →
                  (∀ i j, j ≠ i → uᵣ i ≫ π j = 0) →
                  (∀ i, IsUpperRootProjection s (uᵣ i ≫ π i)) →
                  ∀ i, ∃ eᵢ : B.obj S.val ≅ B.obj S.val,
                    δ.hom ≫ B.map (π (τ i)) = B.map (π i) ≫ eᵢ.hom

end

end LinearAlgebraicGroups.Specs.Arithmetic.OrthogonalLeviFactorDisplacement
