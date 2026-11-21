import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.InfiniteGalois
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.Conjugation
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.StableIntermediateFields
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.OpenFiniteFields
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.Normality

/-! Normality in the infinite Galois correspondence (FT-C08). -/

universe u v

namespace AdvancedFieldTheory

open scoped Pointwise

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- A fixing subgroup is normal exactly when the intermediate field is Galois.
Conjugation of fixing subgroups corresponds to taking automorphic images;
field recovery makes this correspondence injective. -/
theorem fixingSubgroup_normal_iff_isGalois (M : IntermediateField K L) :
    (fixingSubgroup M).Normal ↔ IsGalois K M := by
  constructor
  · intro hN
    let : (fixingSubgroup M).Normal := hN
    apply (isGalois_iff_stable M).mpr
    intro g
    have heq : fixingSubgroup (M.map g.toAlgHom) = fixingSubgroup M := by
      rw [fixingSubgroup_image, Subgroup.Normal.conj_smul_eq_self]
    calc
      M.map g.toAlgHom = fixedField (fixingSubgroup (M.map g.toAlgHom)) :=
        (fixedField_fixingSubgroup K L _).symm
      _ = fixedField (fixingSubgroup M) := congrArg fixedField heq
      _ = M := fixedField_fixingSubgroup K L M
  · intro hM
    apply Subgroup.Normal.of_conjugate_fixed
    intro g
    rw [← fixingSubgroup_image, (isGalois_iff_stable M).mp hM g]

/-- For a Krull-closed subgroup, normality is equivalent to its fixed field
being Galois over the original base, including infinite fixed fields. -/
theorem closed_normal_iff_fixedField_isGalois
    (H : Subgroup (GaloisGroup K L))
    (hH : IsClosed (H : Set (GaloisGroup K L))) :
    H.Normal ↔ IsGalois K (fixedField H) := by
  have hrecover : fixingSubgroup (fixedField H) = H := by
    rw [fixingSubgroup_fixedField_eq_topologicalClosure]
    apply SetLike.ext'
    exact hH.closure_eq
  rw [← fixingSubgroup_normal_iff_isGalois, hrecover]

/-- The open normal subgroups correspond precisely to finite Galois
intermediate extensions under the canonical fixing-subgroup map. -/
theorem isOpen_and_normal_iff_exists_finite_galois
    (H : Subgroup (GaloisGroup K L)) :
    (IsOpen (H : Set (GaloisGroup K L)) ∧ H.Normal) ↔
      ∃ M : IntermediateField K L,
        FiniteDimensional K M ∧ IsGalois K M ∧ fixingSubgroup M = H := by
  constructor
  · rintro ⟨hOpen, hNormal⟩
    have hClosed := H.isClosed_of_isOpen hOpen
    have hrecover : fixingSubgroup (fixedField H) = H := by
      rw [fixingSubgroup_fixedField_eq_topologicalClosure]
      apply SetLike.ext'
      exact hClosed.closure_eq
    refine ⟨fixedField H, ?_, ?_, hrecover⟩
    · apply (fixingSubgroup_isOpen_iff_finiteDimensional K L _).mp
      simpa only [hrecover] using hOpen
    · exact (closed_normal_iff_fixedField_isGalois H hClosed).mp hNormal
  · rintro ⟨M, hFinite, hGalois, rfl⟩
    exact ⟨(fixingSubgroup_isOpen_iff_finiteDimensional K L M).mpr hFinite,
      (fixingSubgroup_normal_iff_isGalois M).mpr hGalois⟩

end AdvancedFieldTheory
