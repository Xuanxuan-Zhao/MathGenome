import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.CommutativeRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.SelfAdjointSpectrumNormalRadius
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Approximation.StoneWeierstrass

/-! The Gelfand representation on the original algebraic character space.
Star preservation follows from real self-adjoint character values. Surjectivity
uses self-conjugate Stone–Weierstrass on the actual closed transform range. -/

noncomputable section
namespace ExpandedFA.CStar.CommutativeRepresentation

open Specs.ExpandedFA.BanachAlgebra.Characters
open Specs.ExpandedFA.BanachAlgebra.GelfandTransform
universe u

local instance characterTop (A : Type u) [CommCStarAlgebra A] :
    TopologicalSpace (Character A) := CharacterTopologyValue A

local instance characterCompact (A : Type u) [CommCStarAlgebra A] :
    CompactSpace (Character A) :=
  (BanachAlgebra.Characters.characterHomeomorph A).symm.compactSpace

local instance characterT2 (A : Type u) [CommCStarAlgebra A] : T2Space (Character A) :=
  (BanachAlgebra.Characters.characterHomeomorph A).isEmbedding.t2Space

theorem character_real : Spec.CharacterReal.{u} := by
  intro A _ _ χ a ha
  apply SelfAdjointSpectrumNormalRadius.unital_selfAdjoint_spectrum A a ha
  change χ.val a ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue ℂ A a
  rw [BanachAlgebra.Characters.spectrum_characters A a]
  exact ⟨χ, rfl⟩

theorem character_star : Spec.CharacterStar.{u} := by
  intro A _ _ χ a
  have hsa : ∀ s : selfAdjoint A, star (χ.val s) = χ.val s := by
    intro s
    apply Complex.ext <;> simp [character_real A χ s s.property]
  open scoped ComplexStarModule in
    rw [← realPart_add_I_smul_imaginaryPart a]
    simp only [star_add, star_smul, selfAdjoint.star_val_eq,
      map_add, map_smul, hsa]

theorem transform_star : Spec.TransformStar.{u} := by
  intro A _ _ a
  ext χ
  exact character_star A χ a

theorem transform_norm : Spec.TransformNorm.{u} := by
  intro A _ _ a
  rw [BanachAlgebra.GelfandTransform.norm_eq_spectralRadius A a]
  exact SelfAdjointSpectrumNormalRadius.unital_normal_radius A a inferInstance

theorem transform_isometry : Spec.TransformIsometry.{u} := by
  intro A _ _
  exact AddMonoidHomClass.isometry_of_norm (TransformValue A) (transform_norm A)

theorem transform_surjective : Spec.TransformSurjective.{u} := by
  intro A _ _
  let R := (TransformValue A).range
  have hsep : R.SeparatesPoints := by
    intro χ ψ hne
    contrapose! hne
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact hne (TransformValue A a) ⟨TransformValue A a, ⟨a, rfl⟩, rfl⟩
  have hconj : ∀ f ∈ R, star f ∈ R := by
    rintro _ ⟨a, rfl⟩
    exact ⟨star a, transform_star A a⟩
  have hdense := Approximation.StoneWeierstrass.complex_dense (Character A) R hsep hconj
  have hclosed : IsClosed (R : Set C(Character A, ℂ)) :=
    (transform_isometry A).isClosedEmbedding.isClosed_range
  intro f
  have hf := hdense f
  rw [hclosed.closure_eq] at hf
  exact hf

theorem representation : Spec.Representation.{u} := by
  intro A _ _
  let f : A →⋆ₐ[ℂ] C(Character A, ℂ) :=
    { TransformValue A with map_star' := transform_star A }
  let e := StarAlgEquiv.ofBijective f
    ⟨(transform_isometry A).injective, transform_surjective A⟩
  exact ⟨e, fun _ => rfl, transform_isometry A⟩

theorem zero_representation : Spec.ZeroRepresentation.{u} := by
  intro A _ _
  have he : IsEmpty (Character A) := ⟨fun χ => by
    have h := BanachAlgebra.Characters.character_map_one χ
    have hzero : (1 : A) = 0 := Subsingleton.elim _ _
    rw [hzero, map_zero] at h
    exact zero_ne_one h⟩
  let := he
  let f : A →⋆ₐ[ℂ] C(Character A, ℂ) :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _
      commutes' := fun _ => Subsingleton.elim _ _
      map_star' := fun _ => Subsingleton.elim _ _ }
  let e := StarAlgEquiv.ofBijective f
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun g => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨he, e, fun _ χ => isEmptyElim χ, ?_⟩
  exact fun a b => by simp [Subsingleton.elim a b]

end ExpandedFA.CStar.CommutativeRepresentation
