import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Homological.ExtProjectivityTest
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v

namespace AdvCommAlg

variable {R : Type u} [CommRing R] [Small.{v} R]

theorem projective_of_ext_one_vanishes (T : ModuleCat.{v} R)
    (h : ∀ V : ModuleCat.{v} R, Subsingleton (Ext T V 1)) : Module.Projective R T := by
  have : Projective T := projective_iff_subsingleton_ext_one.mpr h
  infer_instance

theorem projectiveDimension_le_of_ext_vanishes (M : ModuleCat.{v} R) (b : ℕ)
    (h : ∀ V : ModuleCat.{v} R, Subsingleton (Ext M V (b + 1))) :
    projectiveDimension M ≤ (b : WithBot ℕ∞) := by
  exact (projectiveDimension_le_iff M b).mpr
    (hasProjectiveDimensionLT_of_enoughInjectives M (b + 1) h)

variable {M : ModuleCat.{v} R} (P : ProjectiveResolution M)

/-- The augmentation identifies the zeroth syzygy with M. -/
noncomputable def resolutionSyzygyZeroIso : resolutionSyzygy P 0 ≅ M :=
  P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

noncomputable def syzygyShortComplex (b : ℕ) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (P.complex.fromOpcycles (b + 1) b) (P.complex.pOpcycles b) (by
    rw [← cancel_epi (P.complex.pOpcycles (b + 1)),
      HomologicalComplex.p_fromOpcycles_assoc, HomologicalComplex.d_pOpcycles,
      comp_zero])

lemma syzygyShortComplex_shortExact (b : ℕ) : (syzygyShortComplex P b).ShortExact := by
  have hm : Mono (P.complex.fromOpcycles (b + 1) b) := by
    let e := P.complex.opcyclesIsoSc' (b + 2) (b + 1) b (by simp) (by simp)
    have : Mono (e.inv ≫ P.complex.fromOpcycles (b + 1) b) := by
      dsimp [e]
      rw [HomologicalComplex.opcyclesIsoSc'_inv_fromOpcycles]
      exact (P.exact_succ b).mono_fromOpcycles
    have heq : P.complex.fromOpcycles (b + 1) b =
        e.hom ≫ (e.inv ≫ P.complex.fromOpcycles (b + 1) b) := by simp
    rw [heq]
    infer_instance
  have : Mono (syzygyShortComplex P b).f := hm
  have : Epi (syzygyShortComplex P b).g := by
    dsimp [syzygyShortComplex]; infer_instance
  refine { exact := ?_ }
  let S := ShortComplex.mk (P.complex.d (b + 1) b) (P.complex.pOpcycles b)
    (P.complex.d_pOpcycles (b + 1) b)
  have hs : S.Exact := S.exact_of_g_is_cokernel (P.complex.opcyclesIsCokernel (b + 1) b (by simp))
  let φ : S ⟶ syzygyShortComplex P b :=
    { τ₁ := P.complex.pOpcycles (b + 1)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, syzygyShortComplex]
      comm₂₃ := by simp [S, syzygyShortComplex] }
  have : Epi φ.τ₁ := by
    change Epi (P.complex.pOpcycles (b + 1))
    infer_instance
  have : IsIso φ.τ₂ := by
    change IsIso (𝟙 (P.complex.X b))
    infer_instance
  have : Mono φ.τ₃ := by
    change Mono (𝟙 (P.complex.opcycles b))
    infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hs

lemma syzygy_hasProjectiveDimensionLE (b n : ℕ)
    (h : HasProjectiveDimensionLE M (b + n)) :
    HasProjectiveDimensionLE (resolutionSyzygy P b) n := by
  induction b generalizing n with
  | zero =>
    have : HasProjectiveDimensionLE M n := by simpa using h
    exact hasProjectiveDimensionLT_of_iso (resolutionSyzygyZeroIso P).symm (n + 1)
  | succ b ih =>
    have h' : HasProjectiveDimensionLE (resolutionSyzygy P b) (n + 1) :=
      ih (n + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
    exact (syzygyShortComplex_shortExact P b).hasProjectiveDimensionLT_X₁ (n + 1)
      (by dsimp [syzygyShortComplex]; infer_instance) h'

theorem syzygy_projective_of_ext_vanishes (M : ModuleCat.{v} R) (b : ℕ)
    (P : ProjectiveResolution M)
    (h : ∀ V : ModuleCat.{v} R, Subsingleton (Ext M V (b + 1))) :
    Module.Projective R (resolutionSyzygy P b) := by
  have hp : HasProjectiveDimensionLE M (b + 0) :=
    hasProjectiveDimensionLT_of_enoughInjectives M (b + 1) h
  have : HasProjectiveDimensionLE (resolutionSyzygy P b) 0 :=
    syzygy_hasProjectiveDimensionLE P b 0 hp
  have : Projective (resolutionSyzygy P b) :=
    (projective_iff_hasProjectiveDimensionLE_zero _).mpr this
  infer_instance

end AdvCommAlg
