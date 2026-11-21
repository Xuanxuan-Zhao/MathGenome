import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Conormal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.SplitQuotient

/-! The split conormal sequence, with the retraction specified by KD-14. -/
namespace AdvCommAlg.Differentials

universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
open TensorProduct
open Specs.AdvCommAlg.Differentials (conormalExtension Conormal)

section Construction
variable (A : Type u) (P : Type v) (B : Type w)
variable [CommRing A] [CommRing P] [CommRing B]
variable [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
variable (h : Function.Surjective (algebraMap P B))
variable (s : B →ₐ[A] P) (hs : Function.RightInverse s (algebraMap P B))

/-- The endomorphism s composed with the quotient map, over B. -/
private def sectionEndomorphism :
    (conormalExtension A P B h).Hom (conormalExtension A P B h) where
  toRingHom := (s.comp (IsScalarTower.toAlgHom A P B)).toRingHom
  toRingHom_algebraMap a := by
    change s (algebraMap P B (algebraMap A P a)) = algebraMap A P (algebraMap A A a)
    rw [← IsScalarTower.algebraMap_apply, s.commutes]
    rfl
  algebraMap_toRingHom p := by
    change algebraMap P B (s (algebraMap P B p)) = algebraMap B B (algebraMap P B p)
    exact hs _

/-- The difference of id and s composed with the quotient factors through
universal differentials and extension of scalars. -/
private def splitRetraction :
    B ⊗[P] KaehlerDifferential A P →ₗ[B] Conormal A P B h :=
  (Algebra.Extension.Hom.id (conormalExtension A P B h)).sub
    (sectionEndomorphism A P B h s hs)

private theorem splitRetraction_one_tmul (p : P) :
    splitRetraction A P B h s hs (1 ⊗ₜ[P] KaehlerDifferential.D A P p) =
      Algebra.Extension.Cotangent.mk
        ⟨p - s (algebraMap P B p), by
          change algebraMap P B (p - s (algebraMap P B p)) = 0
          rw [map_sub, hs, sub_self]⟩ := by
  have H := Algebra.Extension.Hom.sub_one_tmul
    (Algebra.Extension.Hom.id (conormalExtension A P B h))
    (sectionEndomorphism A P B h s hs) p
  exact H

private theorem splitRetraction_leftInverse :
    Function.LeftInverse (splitRetraction A P B h s hs) (conormalMap A P B h) := by
  intro x
  obtain ⟨f, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  change splitRetraction A P B h s hs
    ((conormalExtension A P B h).cotangentComplex (Algebra.Extension.Cotangent.mk f)) = _
  rw [Algebra.Extension.cotangentComplex_mk]
  change splitRetraction A P B h s hs
    (1 ⊗ₜ[P] KaehlerDifferential.D A P f.val) = _
  rw [splitRetraction_one_tmul]
  congr 1
  apply Subtype.ext
  have hf : algebraMap P B f.val = 0 := f.property
  simp [hf]

end Construction

/-- The conormal sequence of an algebra quotient with an algebra section is
split short exact, with the stated difference derivation as left splitting. -/
theorem split_quotient : Specs.AdvCommAlg.Differentials.splitQuotient.{u,v,w} := by
  intro A P B _ _ _ _ _ _ _ h s hs
  let r := splitRetraction A P B h s hs
  let L : KaehlerDifferential A P →ₗ[P] Conormal A P B h :=
    (r.restrictScalars P).comp (TensorProduct.mk P B (KaehlerDifferential A P) 1)
  let D : Derivation A P (Conormal A P B h) := L.compDer (KaehlerDifferential.D A P)
  have hD (p : P) : D p = r (1 ⊗ₜ[P] KaehlerDifferential.D A P p) := rfl
  refine ⟨D, ?_, r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hD]
    exact splitRetraction_one_tmul A P B h s hs p
  · apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      rw [LinearMap.liftBaseChange_tmul]
      change r (b ⊗ₜ[P] x) = b • D.liftKaehlerDifferential x
      have hL : D.liftKaehlerDifferential = L := by
        apply Derivation.liftKaehlerDifferential_unique
        exact D.liftKaehlerDifferential_comp
      rw [hL]
      change r (b ⊗ₜ[P] x) = b • r (1 ⊗ₜ[P] x)
      rw [← map_smul, smul_tmul', smul_eq_mul, mul_one]
  · exact splitRetraction_leftInverse A P B h s hs
  · exact (splitRetraction_leftInverse A P B h s hs).injective
  · exact (conormal_exact A P B h).1
  · exact (conormal_exact A P B h).2
  · have hex := (conormal_exact A P B h).1
    have hsurj := (conormal_exact A P B h).2
    have hcomp : r.comp (conormalMap A P B h) = LinearMap.id := by
      ext x
      exact splitRetraction_leftInverse A P B h s hs x
    have he : Function.Surjective (conormalProjection A P B) ∧
        ∃ l : B ⊗[P] KaehlerDifferential A P →ₗ[B] Conormal A P B h,
          l.comp (conormalMap A P B h) = LinearMap.id := ⟨hsurj, r, hcomp⟩
    obtain ⟨_, t, ht⟩ := ((hex.split_tfae').out 2 1 rfl rfl).mp he
    exact ⟨t, fun x => LinearMap.congr_fun ht x⟩

end
end AdvCommAlg.Differentials
