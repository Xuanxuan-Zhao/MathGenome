import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace

/-! Statements of Proposition 6.7, including the coordinate formulas for the splitting. -/

universe u w

namespace CommutativeAlgebraNotes.SchlessingerSplitCorrectionsSpec

open LocalArtinAlgebra SchlessingerConditionsSpec SchlessingerTangentVectorSpaceSpec
open scoped TensorProduct

variable {k : Type u} [Field k]

abbrev ExtensionKernel {B A : LocalArtinAlgebra.{u,u} k} (g : Hom B A) :=
  RingHom.ker g.val.toRingHom

theorem extensionKernelFinite {B A : LocalArtinAlgebra.{u,u} k} (g : Hom B A) :
    Module.Finite k (ExtensionKernel g) := by
  let := moduleFinite B
  exact Module.Finite.of_injective ((ExtensionKernel g).subtype.restrictScalars k)
    Subtype.val_injective

attribute [local instance] extensionKernelFinite

abbrev SplitPullback (A₁ : LocalArtinAlgebra.{u,u} k) {B A : LocalArtinAlgebra.{u,u} k}
    (g : Hom B A) :=
  pullbackModel (residueHomModel A₁) (residueHomModel (splitModel k (ExtensionKernel g)))

abbrev splitFst (A₁ : LocalArtinAlgebra.{u,u} k) {B A : LocalArtinAlgebra.{u,u} k}
    (g : Hom B A) : Hom (SplitPullback A₁ g) A₁ :=
  pullbackFstModel (residueHomModel A₁) (residueHomModel (splitModel k (ExtensionKernel g)))

abbrev splitSnd (A₁ : LocalArtinAlgebra.{u,u} k) {B A : LocalArtinAlgebra.{u,u} k}
    (g : Hom B A) : Hom (SplitPullback A₁ g) (splitModel k (ExtensionKernel g)) :=
  pullbackSndModel (residueHomModel A₁) (residueHomModel (splitModel k (ExtensionKernel g)))

def SplitFormula {A₁ B A : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom B A)
    (h : Hom A₁ B) (e : pullbackModel f g ≃ₐ[k] SplitPullback A₁ g) : Prop :=
  (∀ p : pullbackModel f g,
    (splitFst A₁ g).val (e p) = (pullbackFstModel f g).val p ∧
    ((splitSnd A₁ g).val (e p)).fst = A₁.residue ((pullbackFstModel f g).val p) ∧
    (((splitSnd A₁ g).val (e p)).snd : B) = (pullbackSndModel f g).val p - h ((pullbackFstModel f g).val p)) ∧
  (∀ q : SplitPullback A₁ g,
    (pullbackFstModel f g).val (e.symm q) = (splitFst A₁ g).val q ∧
    (pullbackSndModel f g).val (e.symm q) = h ((splitFst A₁ g).val q) + (((splitSnd A₁ g).val q).snd : B))

def SplitPullbackStatement : Prop :=
  ∀ {k : Type u} [Field k] {A₁ B A : LocalArtinAlgebra.{u,u} k}
    (f : Hom A₁ A) (g : Hom B A), SmallExtensionModel g →
    ∀ (h : Hom A₁ B), g.comp h = f →
      ∃ e : pullbackModel f g ≃ₐ[k] SplitPullback A₁ g, SplitFormula f g h e

/-- An algebra equivalence of the bundled rings gives a morphism of local Artin algebras. -/
def equivHom {C D : LocalArtinAlgebra.{u,u} k} (e : C ≃ₐ[k] D) : Hom C D :=
  ⟨e.toAlgHom, ⟨fun x hx => by
    have h := hx.map e.symm.toAlgHom
    change IsUnit (e.symm (e x)) at h
    simpa only [e.symm_apply_apply] using h⟩⟩

/-- The two coordinates of an element on the original pullback, after splitting
and applying the tangent tensor comparison to the square-zero coordinate. -/
def correctionCoordinates {A₁ B A : LocalArtinAlgebra.{u,u} k}
    {f : Hom A₁ A} {g : Hom B A} (F : ArtinFunctorModel.{u,w} k)
    (laws : VectorLaws F) (c : SplitTensorComparison F laws (ExtensionKernel g))
    (e : pullbackModel f g ≃ₐ[k] SplitPullback A₁ g) :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    F.toFunctor.obj (pullbackModel f g) →
      F.toFunctor.obj A₁ × (TangentModel F ⊗[k] ExtensionKernel g) :=
  fun p =>
    let q := onHom F (equivHom e) p
    (onHom F (splitFst A₁ g) q, c.equiv (onHom F (splitSnd A₁ g) q))

def CorrectionCoordinatesStatement : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k), H2Model F →
    ∀ {A₁ B A : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom B A),
      SmallExtensionModel g →
    ∀ (laws : VectorLaws F) (c : SplitTensorComparison F laws (ExtensionKernel g))
      (e : pullbackModel f g ≃ₐ[k] SplitPullback A₁ g),
      Function.Bijective (correctionCoordinates F laws c e)

/-- A correction determines a unique pullback element with the prescribed first
coordinate and the prescribed image over the extension. -/
def HasSplitCorrection {A₁ B A : LocalArtinAlgebra.{u,u} k}
    {f : Hom A₁ A} {g : Hom B A} (F : ArtinFunctorModel.{u,w} k)
    (laws : VectorLaws F) (c : SplitTensorComparison F laws (ExtensionKernel g))
    (e : pullbackModel f g ≃ₐ[k] SplitPullback A₁ g)
    (x : F.toFunctor.obj A₁) (y : F.toFunctor.obj B) : Prop :=
  letI := tangentAddCommGroupModel F laws
  letI := tangentModuleModel F laws
  ∃ θ : TangentModel F ⊗[k] ExtensionKernel g,
    ∃! p : F.toFunctor.obj (pullbackModel f g),
      correctionCoordinates F laws c e p = (x, θ) ∧ onHom F (pullbackSndModel f g) p = y

def SplitCorrectionsStatement : Prop :=
  ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k), H1Model F → H2Model F →
    ∀ {A₁ B A : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom B A),
      SmallExtensionModel g →
    ∀ (h : Hom A₁ B), g.comp h = f →
      ∃ (e : pullbackModel f g ≃ₐ[k] SplitPullback A₁ g) (_ : SplitFormula f g h e)
        (laws : VectorLaws F) (c : SplitTensorComparison F laws (ExtensionKernel g)),
        Function.Bijective (correctionCoordinates F laws c e) ∧
          ∀ (x : F.toFunctor.obj A₁) (y : F.toFunctor.obj B), onHom F f x = onHom F g y →
            HasSplitCorrection F laws c e x y

/-- The full tangent assertion, using the upstream statements for the canonical
operations, the tensor comparison, and its naturality. -/
def TangentFunctorStatement : Prop :=
  VectorLawsStatement.{u,w} ∧ SplitTensorStatement.{u,w} ∧ TensorPureFormula.{u,w} ∧
    TensorNaturalityInIdeal.{u,w} ∧ TangentMapStatement.{u,w} ∧ TensorNaturalityInFunctor.{u,w}

end CommutativeAlgebraNotes.SchlessingerSplitCorrectionsSpec
