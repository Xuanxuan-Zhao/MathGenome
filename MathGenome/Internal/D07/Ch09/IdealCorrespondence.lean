import MathGenome.Internal.Specs.D07.Ch09.IdealCorrespondence
import MathGenome.Internal.D07.Ch08.KernelImage
import MathGenome.Internal.D07.Ch09.QuotientProjection
import Mathlib.Data.Rat.Lemmas

/-! K07.09.ideal_correspondence (paper.tex:1610–1633).
Restrict the ideal correspondence to two-sided ideals. Surjectivity
identifies Mathlib's generated image with the actual image and ensures
right absorption. The quotient case uses the accepted projection kernel.
-/

universe u v

namespace D07.Ch09.IdealCorrespondence

open Specs.D07.Ch09.IdealCorrespondence

theorem preimage_properties : PreimageProperties.{u, v} := by
  intro R S _ _ f H _
  refine ⟨inferInstance, ?_, rfl⟩
  intro x hx
  change f x ∈ H
  rw [RingHom.mem_ker.mp hx]
  exact H.zero_mem

theorem image_properties : ImageProperties.{u, v} := by
  intro R S _ _ f hf J _
  let _ : RingHomSurjective f := ⟨hf⟩
  exact ⟨inferInstance, Ideal.map_eq_image_of_surjective f hf⟩

theorem ideal_correspondence : SurjectiveCorrespondence.{u, v} := by
  intro R S _ _ f hf
  let _ : RingHomSurjective f := ⟨hf⟩
  let e : {H : Ideal S // H.IsTwoSided} ≃o
      {J : Ideal R // J.IsTwoSided ∧ RingHom.ker f ≤ J} := {
    toFun := fun H => by
      letI := H.property
      exact ⟨H.val.comap f, (preimage_properties R S f H.val).1,
        (preimage_properties R S f H.val).2.1⟩
    invFun := fun J => by
      letI := J.property.1
      exact ⟨J.val.map f, (image_properties R S f hf J.val).1⟩
    left_inv := fun H => Subtype.ext (Ideal.map_comap_of_surjective f hf H.val)
    right_inv := fun J => by
      apply Subtype.ext
      change (J.val.map f).comap f = J.val
      rw [Ideal.comap_map_of_surjective f hf]
      exact sup_eq_left.mpr J.property.2
    map_rel_iff' := by
      intro H K
      exact Ideal.comap_le_comap_iff_of_surjective f hf H.val K.val }
  exact ⟨e, fun _ => rfl, fun J => Ideal.map_eq_image_of_surjective f hf⟩

theorem quotient_correspondence : QuotientCorrespondence.{u} := by
  intro R _ I _
  let f := Ideal.Quotient.mk I
  have hf := D07.Ch09.QuotientProjection.projection_surjective R I
  have hk := D07.Ch09.QuotientProjection.projection_kernel R I
  have hk' : RingHom.ker f = I := hk
  have h := ideal_correspondence R (R ⧸ I) f hf
  rw [hk'] at h
  exact h

private theorem half_not_integer_range :
    (1 / 2 : ℚ) ∉ Set.range (Int.castRingHom ℚ) := by
  rintro ⟨n, hn⟩
  have hden := congrArg Rat.den hn
  have hhalfden : (1 / 2 : ℚ).den ≠ 1 := by
    change ¬ (((1 : ℕ) : ℚ) / ((2 : ℕ) : ℚ)).den = 1
    rw [Rat.den_div_natCast_eq_one_iff 1 2 (by decide)]
    decide
  exact hhalfden (by simpa using hden.symm)

theorem integer_rational_image_not_ideal : IntegerRationalImageNotIdeal := by
  refine ⟨Int.cast_injective, ?_⟩
  rintro ⟨H, hH⟩
  have h1 : (1 : ℚ) ∈ H := by
    apply (Set.ext_iff.mp hH 1).mpr
    exact ⟨1, map_one (Int.castRingHom ℚ)⟩
  have hhalf : (1 / 2 : ℚ) ∈ H := by
    simpa using H.mul_mem_left (1 / 2) h1
  exact half_not_integer_range ((Set.ext_iff.mp hH _).mp hhalf)

theorem generated_image_differs : GeneratedImageDiffers := by
  have himage : (Int.castRingHom ℚ) '' (↑(⊤ : Ideal ℤ) : Set ℤ) =
      Set.range (Int.castRingHom ℚ) := by
    ext q
    simp
  refine ⟨himage, Ideal.map_top _, ?_⟩
  intro h
  apply integer_rational_image_not_ideal.2
  exact ⟨(⊤ : Ideal ℤ).map (Int.castRingHom ℚ), h.trans himage⟩

end D07.Ch09.IdealCorrespondence
