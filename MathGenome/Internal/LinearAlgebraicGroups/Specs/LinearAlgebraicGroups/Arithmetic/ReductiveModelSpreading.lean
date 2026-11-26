import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ReductiveModelSpreading

open GeometricRadicals (IsReductive IsSemisimple)
open IntegralSemisimpleModel (Integers Model fibre)
open IntegralCentralQuotient (OverBase)

noncomputable section

/-- Scalar extension of group schemes by pullback along the spectrum map. -/
abbrev scalarExtension (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Grp (OverBase R) ⥤ Grp (OverBase S) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp

/-- A split pinned integral model with semisimple field fibres. -/
structure SplitModel where
  datum : Pinning.BasedRootDatum.{u}
  model : Model datum
  semisimple : ∀ (F : Type u) [Field F],
    ∃ H : AffineAlgebraicGroup F, IsSemisimple H ∧ Nonempty ((fibre F).obj model.group ≅ H.val)

attribute [local instance] IntegralSemisimpleModel.integerAlgebra

/-- A model and a splitting comparison over a finite faithfully flat étale algebra. -/
structure ReductiveModel {K R : Type u} [Field K] [CommRing R] [Algebra R K]
    (G : AffineAlgebraicGroup K) where
  group : Grp (OverBase R)
  affine : IsAffine group.X.left
  finitePresentation : LocallyOfFinitePresentation group.X.hom
  quasiCompact : QuasiCompact group.X.hom
  smooth : Smooth group.X.hom
  generic : (scalarExtension R K).obj group ≅ G.val
  reductive : ∀ (F : Type u) [Field F] [Algebra R F],
    ∃ H : AffineAlgebraicGroup F, IsReductive H ∧
      Nonempty ((scalarExtension R F).obj group ≅ H.val)
  split : SplitModel.{u}
  cover : Type u
  [coverRing : CommRing cover]
  [coverAlgebra : Algebra R cover]
  coverFinite : Module.Finite R cover
  coverFaithfullyFlat : Module.FaithfullyFlat R cover
  coverEtale : Algebra.Etale R cover
  splitting : (scalarExtension R cover).obj group ≅
    (scalarExtension Integers.{u} cover).obj split.model.group

/-- The group has a model over a principal open of the actual ring of integers. -/
def Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (G : AffineAlgebraicGroup K),
    IsSemisimple G →
    ∃ d : NumberField.RingOfIntegers K, d ≠ 0 ∧
      ∃ a : Algebra (Localization.Away d) K,
        letI := a
        IsScalarTower (NumberField.RingOfIntegers K) (Localization.Away d) K ∧
        Nonempty (ReductiveModel G (R := Localization.Away d))

/-- The actual split integral comparison before spreading denominators. -/
def GenericSplitting : Prop :=
  ∀ (K : Type u) [Field K] (G : AffineAlgebraicGroup K), IsSemisimple G →
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (_ : IsGalois K E) (M : SplitModel.{u}),
      Nonempty ((scalarExtension K E).obj G.val ≅ (fibre E).obj M.model.group)

/-- At every good finite place the model and its étale splitting comparison
pull back to the completed valuation ring. Its generic fibre is the original
group extended to the actual completion of the number field. -/
def CompletedBaseChange : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (G : AffineAlgebraicGroup K)
    (d : NumberField.RingOfIntegers K) [Algebra (Localization.Away d) K]
    [IsScalarTower (NumberField.RingOfIntegers K) (Localization.Away d) K],
    ∀ (M : ReductiveModel G (R := Localization.Away d)) (v : Arithmetic.NumberFinitePlace K),
      let O := v.adicCompletionIntegers K
      let L := v.adicCompletion K
      let R := Localization.Away d
      IsUnit (algebraMap (NumberField.RingOfIntegers K) O d) →
      ∃ a : Algebra R O,
        letI := a
        letI := M.coverRing
        letI := M.coverAlgebra
        let T := O ⊗[R] M.cover
        IsScalarTower (NumberField.RingOfIntegers K) R O ∧
          Nonempty ((scalarExtension O L).obj ((scalarExtension R O).obj M.group) ≅
            (scalarExtension K L).obj G.val) ∧
          Module.Finite O T ∧ Module.FaithfullyFlat O T ∧ Algebra.Etale O T ∧
          Nonempty ((scalarExtension O T).obj ((scalarExtension R O).obj M.group) ≅
            (scalarExtension Integers.{u} T).obj M.split.model.group)

end

end LinearAlgebraicGroups.Specs.ReductiveModelSpreading
