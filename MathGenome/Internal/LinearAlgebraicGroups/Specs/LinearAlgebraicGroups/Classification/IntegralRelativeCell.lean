import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.IntegralRelativeCell

open IntegralCentralQuotient
open Pinning (AttachedDatum BasedIso BasedRootDatum RootCoordinate SplitBorelPair)
open OrderedRootProducts (Enumerates RootSubgroupFamily)
open RootGroups (AdditiveLine)
open DiagonalizableGroups (IntegerCharacters integerGenerator)
open CharacterDescent (Character)

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The root-line coordinate after extending scalars to the geometric field. -/
def extendCoordinate (K : Type u) [Field K] [Algebra R K]
    (x : A →ₐ[R] Polynomial R) : K ⊗[R] A →ₐ[K] Polynomial K :=
  AlgHom.liftEquiv R K A (Polynomial K) ((Polynomial.aeval (Polynomial.X : Polynomial K)).comp x)

/-- A calibrated identification of a geometric fibre with the indicated based datum. -/
structure FibreDatum (D : BasedRootDatum.{u})
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (K : Type u) [Field K] [Algebra R K] where
  pair : SplitBorelPair K
  groupIso : HopfSpectrum K (K ⊗[R] A) ≅ pair.G.val
  torusIso : HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X)) ≅ pair.T.group
  attached : AttachedDatum pair
  based : BasedIso D attached.toBased
  torus_comm :
    spectrumOfHopfHom (Bialgebra.TensorProduct.map (BialgHom.id K K) t) ≫ groupIso.hom =
      torusIso.hom ≫ pair.T.inclusion
  character_eq : ∀ χ : D.X,
    let c : Character (HopfSpectrum K (K ⊗[R] MonoidAlgebra R (Multiplicative D.X))) :=
      torusIso.hom ≫ Additive.toMul (based.val.weightEquiv χ)
    let f := ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage c.hom.hom).unop
    f.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator) =
      (1 : K) ⊗ₜ[R] MonoidAlgebra.of R (Multiplicative D.X) (Multiplicative.ofAdd χ)

/-- The parametrizations on a calibrated fibre are the equivariant coordinates of
the actual root subgroups, with the labels transported by the based identification. -/
def FibreCoordinates {D : BasedRootDatum.{u}}
    {t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X)}
    {K : Type u} [Field K] [Algebra R K] (F : FibreDatum D t K)
    (x : D.I → A →ₐ[R] Polynomial R) : Prop :=
  ∃ (L : AdditiveLine K) (U : RootSubgroupFamily F.pair.T),
    ∀ i : D.I,
      let α := F.based.val.indexEquiv i
      ∃ y : RootCoordinate L F.pair.T (U α).val α.val,
        spectrumOfAlgHom (extendCoordinate K (x i)) ≫ F.groupIso.hom.hom.hom =
          y.val.hom.hom.hom ≫ (U α).val.inclusion.hom.hom

/-- A surjective pullback of the coordinate of a closed additive root line. -/
def ClosedAdditiveCoordinate (x : A →ₐ[R] Polynomial R) : Prop :=
  Function.Surjective x ∧
    ∀ (S : CommAlgCat.{u} R) (a b : S),
      toConv ((Polynomial.aeval (a + b)).comp x) =
        toConv ((Polynomial.aeval a).comp x) * toConv ((Polynomial.aeval b).comp x)

/-- The relative difference map on a product of two copies of a cell. -/
def cellDivision {S : Scheme.{u}} (G : Grp (Over S)) {W : Over S} (i : W ⟶ G.X) :
    W ⊗ W ⟶ G.X :=
  (fst W W ≫ i) * (snd W W ≫ i)⁻¹

/-- An affine presentation of the full two-cell cover and its faithfully flat coordinate map. -/
def FaithfullyFlatCellCover {W : OverBase R} (i : W ⟶ (HopfSpectrum R A).X) : Prop :=
  ∃ (C : CommAlgCat.{u} R)
    (e : (algSpec (CommRingCat.of R)).obj (op C) ≅ W ⊗ W) (f : A →ₐ[R] C),
    spectrumOfAlgHom f = e.hom ≫ cellDivision (HopfSpectrum R A) i ∧
      f.toRingHom.FaithfullyFlat

/-- The integral open cell and smooth faithfully flat two-cell cover for any two orders. -/
def Statement : Prop :=
  let R := IntegralRing.{u}
  ∀ (D : BasedRootDatum.{u}) {A : Type u} [CommRing A] [HopfAlgebra R A]
    (t : A →ₐc[R] MonoidAlgebra R (Multiplicative D.X))
    (x : D.I → A →ₐ[R] Polynomial R),
    Algebra.FinitePresentation R A → Smooth (HopfSpectrum R A).X.hom →
    Function.Surjective t → (∀ i, ClosedAdditiveCoordinate (x i)) →
    (∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      ∃ F : FibreDatum D t K, FibreCoordinates F x) →
    ∀ (negative positive : List D.I),
      Enumerates negative {i | ¬ D.base.IsPos i} →
      Enumerates positive {i | D.base.IsPos i} →
      let i := cellMap t x negative positive
      IsAffine (lineProduct R negative ⊗ ((HopfSpectrum R (MonoidAlgebra R (Multiplicative D.X))).X ⊗
        lineProduct R positive)).left ∧ IsOpenImmersion i.left ∧
        Smooth (cellDivision (HopfSpectrum R A) i).left ∧
        Surjective (cellDivision (HopfSpectrum R A) i).left ∧ FaithfullyFlatCellCover i

end

end LinearAlgebraicGroups.Specs.IntegralRelativeCell
