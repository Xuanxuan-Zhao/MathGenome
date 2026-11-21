import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.SimpleRootAndStandardPermanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.RealizeResidueFieldExtension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Localization.Integral

namespace AdvCommAlg.Etale

universe u v
noncomputable section
open Polynomial
open Specs.AdvCommAlg.Etale.StandardAndPointwise
open Specs.AdvCommAlg.Etale.SimpleRoot
open scoped nonZeroDivisors

/-- Clear denominators in κ(p) and then lift the numerator from A/p to A.
No surjectivity of A → κ(p) is used. -/
lemma exists_residue_polynomial_multiple {A : Type u} [CommRing A]
    (p : Ideal A) [p.IsPrime] (f : p.ResidueField[X]) :
    ∃ (g : A[X]) (s : A), s ∉ p ∧
      g.map (algebraMap A p.ResidueField) = (algebraMap A p.ResidueField s) • f := by
  obtain ⟨g, hg⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
    (IsLocalization.integerNormalization (A ⧸ p)⁰ f)
  obtain ⟨b, hb, hbf⟩ := IsLocalization.integerNormalization_spec (A ⧸ p)⁰ f
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨g, s, ?_, ?_⟩
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using hb
  · simpa [← hg, Polynomial.map_map, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq, algebraMap_smul] using hbf

/-- A map to a field containing a primitive element induces the full residue
field extension at its kernel. -/
lemma residue_equiv_of_primitive_image {A : Type u} [CommRing A]
    (p : Ideal A) [p.IsPrime] (L : Type v) [Field L]
    [Algebra p.ResidueField L] [Algebra A L] [IsScalarTower A p.ResidueField L]
    (α : L) (hα : IntermediateField.adjoin p.ResidueField {α} = ⊤)
    (B : Type u) [CommRing B] [Algebra A B]
    (φ : B →ₐ[A] L) (x : B) (hx : φ x = α) :
    ∃ (q : Ideal B) (_ : q.IsPrime) (_ : q.LiesOver p),
      let : Algebra p.ResidueField q.ResidueField :=
        (Ideal.ResidueField.map p q (algebraMap A B) (q.over_def p)).toAlgebra
      Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L) := by
  let q : Ideal B := RingHom.ker φ.toRingHom
  have : q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  have : q.LiesOver p := by
    constructor
    ext a
    simp [q, Ideal.mem_comap, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply A p.ResidueField L]
  refine ⟨q, inferInstance, inferInstance, ?_⟩
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap A B) (q.over_def p)).toAlgebra
  let ψ : q.ResidueField →+* L := Ideal.ResidueField.lift q φ.toRingHom le_rfl (by
    intro b hb
    exact isUnit_iff_ne_zero.mpr hb)
  have hcomm : ψ.comp (algebraMap p.ResidueField q.ResidueField) =
      algebraMap p.ResidueField L := by
    apply Ideal.ResidueField.ringHom_ext
    ext a
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
      Ideal.ResidueField.map_algebraMap]
    simp [ψ, IsScalarTower.algebraMap_apply A p.ResidueField L]
  let ψₐ : q.ResidueField →ₐ[p.ResidueField] L :=
    { ψ with commutes' := fun a => congrArg (fun f : p.ResidueField →+* L => f a) hcomm }
  have hαrange : α ∈ ψₐ.fieldRange := by
    refine ⟨algebraMap B q.ResidueField x, ?_⟩
    change ψ (algebraMap B q.ResidueField x) = α
    simpa [ψ] using hx
  have htop : ψₐ.fieldRange = ⊤ := by
    apply top_unique
    rw [← hα]
    exact IntermediateField.adjoin_simple_le_iff.mpr hαrange
  refine ⟨AlgEquiv.ofBijective ψₐ ⟨ψₐ.injective, ?_⟩⟩
  intro y
  have hy : y ∈ ψₐ.fieldRange := by rw [htop]; trivial
  exact hy

/-- Every finite separable extension of κ(p) occurs as the residue extension
at a prime of an étale A-algebra. -/
theorem realize_residue_field_extension :
    Specs.AdvCommAlg.Etale.ResidueExtension.realization.{u,v} := by
  intro A _ p _ L _ _ _ _
  let : Algebra A L :=
    ((algebraMap p.ResidueField L).comp (algebraMap A p.ResidueField)).toAlgebra
  let : IsScalarTower A p.ResidueField L := .of_algebraMap_eq' rfl
  obtain ⟨α, hα⟩ := Field.exists_primitive_element p.ResidueField L
  obtain ⟨f, s, hs, hf⟩ :=
    exists_residue_polynomial_multiple p (minpoly p.ResidueField α)
  have hroot : aeval α f = 0 := by
    rw [← aeval_map_algebraMap p.ResidueField α, hf, map_smul, minpoly.aeval, smul_zero]
  have hdf : f.derivative.map (algebraMap A p.ResidueField) =
      (algebraMap A p.ResidueField s) • (minpoly p.ResidueField α).derivative := by
    rw [← Polynomial.derivative_map, hf, Polynomial.derivative_smul]
  have hder : aeval α f.derivative ≠ 0 := by
    rw [← aeval_map_algebraMap p.ResidueField α, hdf, map_smul, Algebra.smul_def]
    apply mul_ne_zero
    · have hs' : algebraMap A p.ResidueField s ≠ 0 := by simpa using hs
      exact (_root_.map_ne_zero (algebraMap p.ResidueField L)).mpr hs'
    · exact (Algebra.IsSeparable.isSeparable p.ResidueField α).aeval_derivative_ne_zero
        (minpoly.aeval _ _)
  let B := LocalizedQuotient f f.derivative
  have hB : Etale A B :=
    simple_root_etale A f f.derivative (IsLocalization.Away.algebraMap_isUnit _)
  let φ : B →ₐ[A] L := localized_root_lift f f.derivative α hroot
    (isUnit_iff_ne_zero.mpr hder)
  obtain ⟨q, hq, hlies, e⟩ := residue_equiv_of_primitive_image p L α hα B φ
    (rootImage f f.derivative) (localized_root_lift_root _ _ _ _ _)
  exact ⟨B, inferInstance, inferInstance, hB, q, hq, hlies, e⟩

end
end AdvCommAlg.Etale
