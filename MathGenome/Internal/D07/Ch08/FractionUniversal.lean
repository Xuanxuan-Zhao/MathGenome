import MathGenome.Internal.Specs.D07.Ch08.FractionUniversal
import MathGenome.Internal.D07.Ch08.FractionField
import MathGenome.Internal.D07.Ch08.FieldEmbedding

/-! The universal property of fractions, including arbitrary commutative
ring targets and uniqueness for models given by embeddings and fractions. -/

universe u v w

namespace D07.Ch08.FractionUniversal

open Specs.D07.Ch08.FractionUniversal

theorem ringExtensionUnique : RingExtensionUnique.{u, v} := by
  intro R S _ _ _ f g h hg hh
  exact IsLocalization.ringHom_ext (nonZeroDivisors R) (hg.trans hh.symm)

theorem fieldExtensionUnique : FieldExtensionUnique.{u, v} := by
  intro R K _ _ _ f hf
  let g : FractionRing R →+* K := IsFractionRing.lift hf
  have hg : g.comp (algebraMap R (FractionRing R)) = f := by
    ext a
    exact IsFractionRing.lift_algebraMap hf a
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact ringExtensionUnique R K f h g hh hg

theorem fieldExtensionInjective : FieldExtensionInjective.{u, v} := by
  intro R K _ _ _ f _ g _
  exact FieldEmbedding.unital_injective (FractionRing R) K g

theorem fieldFractionFormula : FieldFractionFormula.{u, v} := by
  intro R K _ _ _ f _ g hg a b _
  rw [map_div₀]
  change (g.comp (algebraMap R (FractionRing R))) a /
    (g.comp (algebraMap R (FractionRing R))) b = f a / f b
  rw [hg]

theorem modelsUniqueIso : ModelsUniqueIso.{u, v, w} := by
  intro R K L _ _ _ _ i j hi hj hK hL
  let : Algebra R K := i.toAlgebra
  let : Algebra R L := j.toAlgebra
  let : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr hi
  let : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hj
  let : IsFractionRing R K := IsFractionRing.of_field R K (fun x => by
    obtain ⟨a, b, _, hab⟩ := hK x
    exact ⟨a, b, hab⟩)
  let : IsFractionRing R L := IsFractionRing.of_field R L (fun x => by
    obtain ⟨a, b, _, hab⟩ := hL x
    exact ⟨a, b, hab⟩)
  let e : K ≃+* L := IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl R)
  have he : ∀ a : R, e (i a) = j a := by
    intro a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingEquiv.refl R) a
  refine ⟨e, he, ?_⟩
  intro e' he'
  ext x
  obtain ⟨a, b, _, rfl⟩ := hK x
  rw [map_div₀, map_div₀, he' a, he' b, he a, he b]

theorem ringExtensionCriterion : RingExtensionCriterion.{u, v} := by
  intro R S _ _ _ f
  constructor
  · rintro ⟨g, hg⟩ b hb
    have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb
    have hu := (isUnit_iff_ne_zero.mpr hb').map g
    change IsUnit ((g.comp (algebraMap R (FractionRing R))) b) at hu
    rwa [hg] at hu
  · intro hf
    have hunits : ∀ b : nonZeroDivisors R, IsUnit (f b) :=
      fun b => hf b (mem_nonZeroDivisors_iff_ne_zero.mp b.2)
    exact ⟨IsLocalization.lift hunits, IsLocalization.lift_comp hunits⟩

theorem ringFractionFormula : RingFractionFormula.{u, v} := by
  intro R S _ _ _ f g hg a b hb s hs
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb
  have hbase (r : R) : g (algebraMap R (FractionRing R) r) = f r :=
    RingHom.congr_fun hg r
  have hmul :
      g (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) *
        f b = f a := by
    rw [← hbase b, ← map_mul, div_mul_cancel₀ _ hb', hbase a]
  calc
    g (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) =
        (g (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) *
          (s : S)) * ↑(s⁻¹) := by simp [mul_assoc]
    _ = f a * ↑(s⁻¹) := by rw [hs, hmul]

end D07.Ch08.FractionUniversal
