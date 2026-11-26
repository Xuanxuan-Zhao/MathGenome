import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AlbertFrames
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.PeirceFrames
import Mathlib.FieldTheory.RatFunc.Basic

/-!
The weighted Hermitian presentation of a framed Albert algebra and its splitting
over a nonarchimedean local field, a finite completion, or a global function field.
The group conclusion uses the split Chevalley model identified by the Albert
automorphism scheme.
-/

namespace LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalFormsSpecification

open AlbertFramesSpecification
open LinearAlgebraicGroups.Albert
open SplitSpecification IntrinsicCubicSpecification
open HermitianSpecification (Coordinates)
open CubicSpecification (cubicUnit cubicNorm blockWeight)
open FrameSpecification (frameAxis)
open LinearAlgebraicGroups.Composition
open Composition.Specification (OctonionNormConditions)
open Composition.PeirceSpecification (ZornIsomorphism)
open CategoryTheory
open scoped RatFunc TensorProduct

universe u v

section Coordinates

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
  (J : ParaQuadratic k M) (F : Coefficients k M)
  (e : Fin 3 → Ground k M)

/-- The Peirce projector opposite the diagonal index `i`. -/
def blockProjector (i : Fin 3) : Module.End k (Ground k M) :=
  let j := HermitianSpecification.cyclicNext i
  let l := HermitianSpecification.cyclicPrev i
  U J (e j + e l) - U J (e j) - U J (e l)

abbrev Block (i : Fin 3) := LinearMap.range (blockProjector J e i)

variable {C : Type (max u v)} [NonAssocRing C] [Module k C]
  [IsScalarTower k C C] [SMulCommClass k C C]

/-- A comparison with the weighted Hermitian model carries the entire pointed
Jordan law, and identifies the scalar norm and the marked frame. -/
structure FrameModel (n : QuadraticForm k C) where
  composition : OctonionNormConditions n
  weights : Fin 3 → kˣ
  model : ParaQuadratic k (Coordinates k C)
  reduced : IsReducedModel composition weights model
  coordinates : M ≃ₗ[k] Coordinates k C
  operator : J.IsIso model coordinates
  frame : ∀ i, coordinates (TensorProduct.lid k M (e i)) = frameAxis i
  norm : ∀ x : Ground k M,
    AlbertFramesSpecification.norm F x = cubicNorm n weights (coordinates (TensorProduct.lid k M x))
  blocks : ∀ i, ∃ q : QuadraticForm k (Block J e i),
    Module.finrank k (Block J e i) = 8 ∧ (∀ x, (∀ y, QuadraticMap.polar q x y = 0) → x = 0) ∧
    (∀ x, q x = -trace F (sharp J F x.val)) ∧
    ∃ b : Block J e i ≃ₗ[k] C,
      (∀ x, coordinates (TensorProduct.lid k M x.val) = (0, Pi.single i (b x))) ∧
      ∀ x, q x = blockWeight weights i * n (b x)
  cross : ∀ (x : Block J e 0) (y : Block J e 1),
    sharp J F (x.val + y.val) - sharp J F x.val - sharp J F y.val ∈ Block J e 2
  triple : ∀ (x : Block J e 0) (y : Block J e 1) (z : Block J e 2),
    AlbertFramesSpecification.norm F (x.val + y.val + z.val) =
      pairing F k (sharp J F (x.val + y.val) - sharp J F x.val - sharp J F y.val) z.val

end Coordinates

/-- A full frame in any Albert algebra over a field gives a reduced model. -/
def FrameCoordinatization : Prop :=
  ∀ {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M) (F : Coefficients k M), IsAlbert J → IsCharacteristic J F →
    ∀ e : Fin 3 → Ground k M, IsFrame J F e →
      ∃ (C : Type (max u v)) (_ : NonAssocRing C) (_ : Module k C)
        (_ : IsScalarTower k C C) (_ : SMulCommClass k C C) (n : QuadraticForm k C),
        Nonempty (FrameModel J F e n)

/-- For split octonions the specified block scaling compares a weighted
Hermitian law with the untwisted model over the original field. -/
def SplitFrameModel : Prop :=
  ∀ {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M) (F : Coefficients k M) (e : Fin 3 → Ground k M)
    {C : Type (max u v)} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C}
    (A : FrameModel J F e n) (z : ZornIsomorphism n),
    let g : Coordinates k C ≃ₗ[k] SplitRank.octonion.Model k :=
      (LinearEquiv.refl k _).prodCongr
        (LinearEquiv.piCongrRight fun _ => z.toLinearEquiv.symm)
    let f := A.coordinates.trans (g.trans (RemoveParametersSpecification.removeZornWeights A.weights))
    f J.unit = cubicUnit ∧
      (∀ x : Ground k M, AlbertFramesSpecification.norm F x =
        cubicNorm (SplitRank.norm k .octonion) (LowerRankSpecification.untwisted k)
          (f (TensorProduct.lid k M x))) ∧
      ∃ (h : OctonionNormConditions (SplitRank.norm k .octonion))
        (K : ParaQuadratic k (SplitRank.octonion.Model k)),
        IsReducedModel h (LowerRankSpecification.untwisted k) K ∧ J.IsIso K f

/-- Every Albert algebra over the indicated field is already split there. -/
def AlbertSplits (k : Type u) [Field k] : Prop :=
  ∀ {M : Type v} [AddCommGroup M] [Module k M] (J : ParaQuadratic k M),
    IsAlbert J → IsSplitModel J .octonion

open AutomorphismTypeSpecification
open LinearAlgebraicGroups.Specs
open GeometricRadicals (GeometricGroup IsSemisimple)
open Pinning (AttachedDatum BasedRootDatum SplitBorelPair)

/-- The Cartan pairing on the simple roots and coroots of the full datum. -/
def HasF4Cartan (D : BasedRootDatum.{u}) : Prop :=
  ∃ e : Fin 4 ≃ D.base.support,
    ∀ i j, D.datum.pairing (e i).val (e j).val = cartanMatrix i j

/-- Absolute type F₄ for a semisimple group, read from its geometric Borel pair. -/
def IsAbsoluteF4 {k : Type u} [Field k] (H : AffineAlgebraicGroup k) : Prop :=
  IsSemisimple H ∧ ∃ P : SplitBorelPair (AlgebraicClosure k),
    P.G = GeometricGroup H ∧ ∃ D : AttachedDatum P, HasF4Cartan D.toBased

/-- The geometric type identifies the separable scalar extension with the
Chevalley model from the integral split Albert calculation. -/
def AbsoluteF4IsForm : Prop :=
  ∀ (S : IntegralSplitIdentification) {k K : Type} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] (H : AffineAlgebraicGroup k), IsAbsoluteF4 H →
    Nonempty (((groupChange k K).obj H.val) ≅ (chevalleyChange K).obj S.chevalley.group)

/-- Every form that becomes isomorphic to the specified split group over a
separable closure is already isomorphic over the ground field. -/
def FormsSplit (S : IntegralSplitIdentification) (k : Type) [Field k] : Prop :=
  ∀ {K : Type} [Field K] [Algebra k K] [IsSepClosure k K] (H : AffineAlgebraicGroup k),
    Nonempty (((groupChange k K).obj H.val) ≅ (chevalleyChange K).obj S.chevalley.group) →
    Nonempty (H.val ≅ (chevalleyChange k).obj S.chevalley.group)

def LocalAlbertSplitting : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], AlbertSplits.{u, v} k

def FunctionFieldAlbertSplitting : Prop :=
  ∀ {k : Type u} [Field k] {F : Type v} [Field F] [Finite F]
    [Algebra F⟮X⟯ k] [FiniteDimensional F⟮X⟯ k], AlbertSplits.{u, v} k

def FiniteCompletionAlbertSplitting : Prop :=
  ∀ {k : Type u} [Field k] (D : GlobalFieldData.{u,v} k) (w : D.FinitePlace),
    AlbertSplits.{u,v} (D.FiniteCompletion w)

/-- The Chevalley group is chosen once for both field classes and all completions. -/
def GroupSplitting : Prop :=
  ∃ S : IntegralSplitIdentification,
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k], FormsSplit S k) ∧
    (∀ {k F : Type} [Field k] [Field F] [Finite F]
      [Algebra F⟮X⟯ k] [FiniteDimensional F⟮X⟯ k], FormsSplit S k) ∧
    (∀ {k : Type} [Field k] (D : GlobalFieldData.{0,0} k) (w : D.FinitePlace),
      FormsSplit S (D.FiniteCompletion w))

/-- Every group of absolute type F₄ is isomorphic to the specified split model
over this field. -/
def AbsoluteGroupsSplit (S : IntegralSplitIdentification) (k : Type) [Field k] : Prop :=
  ∀ H : AffineAlgebraicGroup k, IsAbsoluteF4 H →
    Nonempty (H.val ≅ (chevalleyChange k).obj S.chevalley.group)

/-- The absolute-type splitting over local fields, global function fields, and
finite completions uses a single integral Chevalley model. -/
def AbsoluteGroupSplitting : Prop :=
  ∃ S : IntegralSplitIdentification,
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k], AbsoluteGroupsSplit S k) ∧
    (∀ {k F : Type} [Field k] [Field F] [Finite F]
      [Algebra F⟮X⟯ k] [FiniteDimensional F⟮X⟯ k], AbsoluteGroupsSplit S k) ∧
    (∀ {k : Type} [Field k] (D : GlobalFieldData.{0,0} k) (w : D.FinitePlace),
      AbsoluteGroupsSplit S (D.FiniteCompletion w))

end LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalFormsSpecification
