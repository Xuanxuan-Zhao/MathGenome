import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Characters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
The character stage of the manuscript's Gelfand theorem. The algebraic
characters and their topology are retained, and a homeomorphism to the native
weak-star character space supplies the compactness theorem. The imported
GelfandDuality results used here are from its `ComplexBanachAlgebra` section:
no star operation, C⋆ identity, or semisimplicity is assumed.
-/

noncomputable section

namespace ExpandedFA.BanachAlgebra.Characters

open Specs.ExpandedFA.BanachAlgebra.Characters
universe u

section Algebraic
variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A]

/-- A nonzero multiplicative linear functional preserves the unit. -/
theorem character_map_one (χ : Character ℂ A) : χ.val 1 = 1 := by
  have hmul := χ.property.2 (1 : A) 1
  rw [one_mul] at hmul
  have h : χ.val 1 = 0 ∨ χ.val 1 = 1 := by
    have hz : χ.val 1 * (χ.val 1 - 1) = 0 := by
      rw [mul_sub, mul_one, ← hmul, sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  rcases h with h | h
  · exfalso
    apply χ.property.1
    apply LinearMap.ext
    intro a
    have ha := χ.property.2 a 1
    simpa only [mul_one, h, mul_zero, LinearMap.zero_apply] using ha
  · exact h

/-- Algebraic packaging; no continuity assumption is introduced. -/
def characterAlgHom (χ : Character ℂ A) : A →ₐ[ℂ] ℂ where
  toFun := χ.val
  map_zero' := χ.val.map_zero
  map_add' := χ.val.map_add
  map_one' := character_map_one χ
  map_mul' := χ.property.2
  commutes' z := by
    change χ.val (algebraMap ℂ A z) = z
    rw [Algebra.algebraMap_eq_smul_one, χ.val.map_smul, character_map_one,
      smul_eq_mul, mul_one]

@[simp] theorem characterAlgHom_apply (χ : Character ℂ A) (a : A) :
    characterAlgHom χ a = χ.val a := rfl

/-- Forgetting continuity retains precisely the manuscript's characters. -/
def algebraicCharacter (χ : WeakDual.characterSpace ℂ A) : Character ℂ A :=
  ⟨(WeakDual.CharacterSpace.toAlgHom χ).toLinearMap, by
    refine ⟨?_, fun a b => map_mul χ a b⟩
    intro h
    have hh := LinearMap.congr_fun h (1 : A)
    simp at hh⟩

@[simp] theorem algebraicCharacter_apply (χ : WeakDual.characterSpace ℂ A) (a : A) :
    (algebraicCharacter χ).val a = χ a := rfl

end Algebraic

section Banach
variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Automatic continuity promotes every algebraic character to the weak dual. -/
def characterEquiv : Character ℂ A ≃ WeakDual.characterSpace ℂ A where
  toFun χ := WeakDual.CharacterSpace.equivAlgHom.symm (characterAlgHom χ)
  invFun := algebraicCharacter
  left_inv χ := by apply Subtype.ext; rfl
  right_inv χ := by apply WeakDual.CharacterSpace.ext; intro a; rfl

@[simp] theorem characterEquiv_apply (χ : Character ℂ A) (a : A) :
    characterEquiv χ a = χ.val a := rfl

end Banach

abbrev characterTopology : CharacterTopologyType.{u} := CharacterTopologyValue

theorem maximal_closed : MaximalClosed.{u} := by
  intro A _ _ _ _ _ I hI
  let := hI
  exact Ideal.IsMaximal.isClosed

theorem automatic_boundedness : AutomaticBoundedness.{u} := by
  intro A _ _ _ _ _ χ
  refine ⟨(characterAlgHom χ).toContinuousLinearMap, rfl,
    AlgHom.toContinuousLinearMap_norm _, ?_⟩
  intro a
  exact AlgHom.norm_apply_le_self (characterAlgHom χ) a

theorem maximal_quotient : MaximalQuotient.{u} := by
  intro A _ _ _ _ _ I hI
  let := hI
  let e : (A ⧸ I) ≃ₐ[ℂ] ℂ :=
    (NormedRing.algEquivComplexOfComplete
      (letI := Ideal.Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm
  refine ⟨e, algebraicCharacter I.toCharacterSpace, ?_, ?_⟩
  · intro a
    rfl
  · intro a
    change e (Ideal.Quotient.mk I a) = 0 ↔ a ∈ I
    rw [← map_zero e, e.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem character_quotient : CharacterQuotient.{u} := by
  intro A _ _ _ _ _ χ
  let f := characterAlgHom χ
  have hsurj : Function.Surjective f := fun z =>
    ⟨algebraMap ℂ A z, f.commutes z⟩
  refine ⟨RingHom.ker f, RingHom.ker_isMaximal_of_surjective f hsurj,
    Ideal.quotientKerAlgEquivOfSurjective hsurj, ?_, ?_⟩
  · intro a
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk hsurj a).symm
  · intro a
    rfl

theorem maximal_correspondence : MaximalCorrespondence.{u} := by
  intro A _ _ _ _ _ I
  constructor
  · intro hI
    obtain ⟨e, χ, _, hχ⟩ := maximal_quotient A I hI
    refine ⟨χ, hχ, ?_⟩
    intro ψ hψ
    apply characterEquiv.injective
    apply WeakDual.CharacterSpace.ext_ker
    ext a
    exact (hψ a).trans (hχ a).symm
  · rintro ⟨χ, hχ, _⟩
    have hker : RingHom.ker (characterAlgHom χ) = I := by
      ext a
      exact hχ a
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective (characterAlgHom χ)
      (fun z => ⟨algebraMap ℂ A z, (characterAlgHom χ).commutes z⟩)

section Topology
variable (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

local instance : TopologicalSpace (Character ℂ A) := characterTopology A

/-- The algebraic character carrier with evaluation topology is the native
weak-star character space, with precisely the same evaluations. -/
def characterHomeomorph : Character ℂ A ≃ₜ WeakDual.characterSpace ℂ A :=
  characterEquiv.toHomeomorphOfIsInducing ⟨by
    change TopologicalSpace.induced (fun χ a => χ.val a) Pi.topologicalSpace =
      TopologicalSpace.induced characterEquiv
        (TopologicalSpace.induced Subtype.val
          (TopologicalSpace.induced (fun (f : WeakDual ℂ A) a => f a) Pi.topologicalSpace))
    rw [induced_compose, induced_compose]
    rfl⟩

end Topology

theorem weakStar_identification : NativeWeakStarIdentification.{u} := by
  intro A _ _ _
  exact ⟨characterHomeomorph A, fun _ _ => rfl⟩

theorem compact_hausdorff : CompactHausdorff.{u} := by
  intro A _ _ _ _ _
  let : TopologicalSpace (Character ℂ A) := characterTopology A
  have e := characterHomeomorph A
  exact ⟨e.symm.compactSpace, e.isEmbedding.t2Space⟩

theorem spectrum_characters : SpectrumCharacters.{u} := by
  intro A _ _ _ _ _ a
  ext z
  change z ∈ spectrum ℂ a ↔ ∃ χ : Character ℂ A, χ.val a = z
  rw [WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨algebraicCharacter χ, hχ⟩
  · rintro ⟨χ, hχ⟩
    exact ⟨characterEquiv χ, hχ⟩

end ExpandedFA.BanachAlgebra.Characters
