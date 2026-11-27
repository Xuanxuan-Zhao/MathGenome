import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Cofibrations
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ZeroObject

universe u

namespace DerivedFormalization.Specs.ComplexPushoutProductGenerators

open Model.Complexes ComplexGenerators ComplexCellFactorization ComplexProjective
open _root_.Specs.DerivedFormalization.CochainModels (tensorComplexValue tensorMapValue)

variable {A : Type u} [CommRing A]

/-- The two sides of the span defining the pushout product. -/
noncomputable abbrev leftLeg {X Y U V : Cochains A} (a : X ⟶ Y) (_b : U ⟶ V) :=
  tensorMapValue a (𝟙 U)

noncomputable abbrev rightLeg {X Y U V : Cochains A} (_a : X ⟶ Y) (b : U ⟶ V) :=
  tensorMapValue (𝟙 X) b

noncomputable abbrev source {X Y U V : Cochains A} (a : X ⟶ Y) (b : U ⟶ V) :=
  pushout (leftLeg a b) (rightLeg a b)

def pushoutProductType :=
  ∀ {A : Type u} [CommRing A] {X Y U V : Cochains A}
    (a : X ⟶ Y) (b : U ⟶ V), source a b ⟶ tensorComplexValue Y V

noncomputable def pushoutProductValue : pushoutProductType.{u} := by
  intro A _ X Y U V a b
  refine pushout.desc (tensorMapValue (𝟙 Y) b) (tensorMapValue a (𝟙 V)) ?_
  change
    HomologicalComplex.tensorHom a (𝟙 U) ≫
      HomologicalComplex.tensorHom (𝟙 Y) b =
    HomologicalComplex.tensorHom (𝟙 X) b ≫ HomologicalComplex.tensorHom a (𝟙 V)
  let F := (MonoidalCategory.curriedTensor (ModuleCat A)).map₂CochainComplex
  exact (F.map a).naturality b |>.symm

/-- The homogeneous pure tensor in the direct-sum total complex. -/
noncomputable abbrev homogeneousTensor {X Y : Cochains A} {i j k : ℤ} (h : i + j = k)
    (x : X.X i) (y : Y.X j) : (tensorComplexValue X Y).X k :=
  ιTensorObj X Y i j k h (x ⊗ₜ[A] y)

/-- The source of the attaching map contains the two terms of the signed differential. -/
noncomputable def attachmentBoundary (A : Type u) [CommRing A] (n m : ℤ) :
    (source (iGeneratorValue A n) (iGeneratorValue A m)).X (n + m + 1) :=
  let a := iGeneratorValue A n
  let b := iGeneratorValue A m
  (pushout.inr (leftLeg a b) (rightLeg a b)).f _
    (homogeneousTensor (by omega : n + 1 + m = n + m + 1)
      (sphereGenerator A (n + 1)) (diskGenerator A m)) +
  n.negOnePow • (pushout.inl (leftLeg a b) (rightLeg a b)).f _
    (homogeneousTensor (by omega : n + (m + 1) = n + m + 1)
      (diskGenerator A n) (sphereGenerator A (m + 1)))


/-- The tensor of the lower generators freely supplies the one new cell. -/
def pushoutProductIIType : Prop :=
  ∀ (A : Type u) [CommRing A] (n m : ℤ),
    ∃ (s : sphereValue A (n + m + 1) ⟶ source (iGeneratorValue A n) (iGeneratorValue A m))
      (e : diskValue A (n + m) ⟶ tensorComplexValue (diskValue A n) (diskValue A m)),
      IsPushout (iGeneratorValue A (n + m)) s e
        (pushoutProductValue (iGeneratorValue A n) (iGeneratorValue A m)) ∧
      e.f _ (diskGenerator A (n + m)) = homogeneousTensor rfl (diskGenerator A n) (diskGenerator A m) ∧
      s.f _ (sphereGenerator A (n + m + 1)) = attachmentBoundary A n m

/-- The mixed pushout product has a degreewise splitting and quotient disk.
The quotient is identified by the lower generator and the signed upper generator. -/
def pushoutProductIJType : Prop :=
  ∀ (A : Type u) [CommRing A] (n m : ℤ),
    let f := pushoutProductValue (iGeneratorValue A n) (jGeneratorValue A m)
    (∀ k, IsSplitMono (f.f k)) ∧
      (∃ e : cokernel f ≅ diskValue A (n + m),
        (cokernel.π f ≫ e.hom).f (n + m)
          (homogeneousTensor rfl (diskGenerator A n) (diskGenerator A m)) =
            diskGenerator A (n + m) ∧
        (cokernel.π f ≫ e.hom).f (n + m + 1)
          (homogeneousTensor (by omega : n + (m + 1) = n + m + 1)
            (diskGenerator A n) ((diskValue A m).d m (m + 1) (diskGenerator A m))) =
          n.negOnePow • (diskValue A (n + m)).d (n + m) (n + m + 1)
            (diskGenerator A (n + m))) ∧
      cofibrationsValue A f ∧ QuasiIso f

/-- The swapped mixed pushout product has the same splitting, quotient and lifting property. -/
def pushoutProductJIType : Prop :=
  ∀ (A : Type u) [CommRing A] (n m : ℤ),
    let f := pushoutProductValue (jGeneratorValue A m) (iGeneratorValue A n)
    (∀ k, IsSplitMono (f.f k)) ∧
      Nonempty (cokernel f ≅ diskValue A (n + m)) ∧
      cofibrationsValue A f ∧ QuasiIso f

end DerivedFormalization.Specs.ComplexPushoutProductGenerators
