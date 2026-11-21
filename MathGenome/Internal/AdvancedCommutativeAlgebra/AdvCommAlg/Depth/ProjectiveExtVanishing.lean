import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.ExtProjectivityTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ProjectiveExtVanishing
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! The general-ring projective-dimension bounds of paper.tex, DP-11. -/

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Pointwise

namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R]

/-- Ext into a finite free module vanishes whenever Ext into R vanishes. -/
lemma ext_finite_free_subsingleton (E : ModuleCat.{u} R) (n i : ℕ)
    [Subsingleton (Ext E (ModuleCat.of R R) i)] :
    Subsingleton (Ext E (ModuleCat.of R (Fin n → R)) i) := by
  let F : Fin n → ModuleCat.{u} R := fun _ => ModuleCat.of R R
  have h : Subsingleton (Ext E (⨁ F) i) :=
    (Ext.addEquivBiproduct E (biproduct.isBilimit F) i).injective.subsingleton
  exact ((extFunctorObj.{u} E i).mapIso
    (ModuleCat.biproductIsoPi F)).addCommGroupIsoToAddEquiv.subsingleton_congr.mp h

/-- A finite projective is a retract of a finite free module. -/
lemma ext_finite_projective_subsingleton (E P : ModuleCat.{u} R)
    [Module.Finite R P] [Module.Projective R P] (i : ℕ)
    [Subsingleton (Ext E (ModuleCat.of R R) i)] : Subsingleton (Ext E P i) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  have hz : Subsingleton ((extFunctorObj.{u} E i).obj
      (ModuleCat.of R (Fin n → R))) := ext_finite_free_subsingleton E n i
  let h : Retract P (ModuleCat.of R (Fin n → R)) :=
    { i := ModuleCat.ofHom g
      r := ModuleCat.ofHom f
      retract := by ext x; exact DFunLike.congr_fun hfg x }
  let h' := h.map (extFunctorObj.{u} E i)
  exact ((AddCommGrpCat.mono_iff_injective h'.i).mp inferInstance).subsingleton

variable [IsNoetherianRing R]

/-- Induction on a finite projective-dimension bound, using finite free covers. -/
lemma ext_vanishes_of_add_lt_grade (E : ModuleCat.{u} R) [Module.Finite R E]
    (ℓ : ℕ) (N : ModuleCat.{u} R) [Module.Finite R N]
    [HasProjectiveDimensionLE N ℓ] (i : ℕ)
    (hi : ((i + ℓ : ℕ) : ℕ∞) < grade (Module.annihilator R E) R) :
    Subsingleton (Ext E N i) := by
  induction ℓ generalizing N i with
  | zero =>
    have : Projective N := (projective_iff_hasProjectiveDimensionLE_zero N).mpr inferInstance
    have : Module.Projective R N := inferInstance
    have hbase : Subsingleton (Ext E (ModuleCat.of R R) i) := by
      apply ModuleCat.subsingleton_ext_of_lt_depth
      rw [← grade_eq_extDepth]
      simpa using hi
    exact ext_finite_projective_subsingleton E N i
  | succ ℓ ih =>
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hpd : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) ℓ :=
      hS.hasProjectiveDimensionLT_X₁ (ℓ + 1) (by infer_instance) inferInstance
    have hU : Subsingleton (Ext E (ModuleCat.of R (LinearMap.ker f)) (i + 1)) :=
      ih _ (i + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi)
    have hbase : Subsingleton (Ext E (ModuleCat.of R R) i) := by
      apply ModuleCat.subsingleton_ext_of_lt_depth
      rw [← grade_eq_extDepth]
      exact lt_of_le_of_lt (by exact_mod_cast Nat.le_add_right i (ℓ + 1)) hi
    have hF := ext_finite_free_subsingleton E n i
    exact AddCommGrpCat.subsingleton_of_isZero <|
      ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' E hS i (i + 1) rfl)
        ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr hF).eq_zero_of_src _)
        ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr hU).eq_zero_of_tgt _)

theorem ext_vanishes_below_grade_sub_projectiveDimension
    (E N : ModuleCat.{u} R) [Module.Finite R E] [Module.Finite R N]
    (ℓ : ℕ) [HasProjectiveDimensionLE N ℓ] (i : ℕ)
    (hi : (i : ℕ∞) < grade (Module.annihilator R E) R - (ℓ : ℕ∞)) :
    Subsingleton (Ext E N i) := by
  apply ext_vanishes_of_add_lt_grade E ℓ N i
  simpa using (lt_tsub_iff_right.mp hi)

/-- The finite first nonzero Ext degree cannot exceed projective dimension.
This argument also handles infinite projective dimension without a case split. -/
theorem grade_annihilator_le_projectiveDimension
    (E : ModuleCat.{u} R) [Module.Finite R E] [Nontrivial E] :
    (grade (Module.annihilator R E) R : WithBot ℕ∞) ≤ projectiveDimension E := by
  have : Nontrivial R := Module.nontrivial R E
  have hproper : Module.annihilator R E ≠ ⊤ := by
    intro h
    have : Subsingleton E := Module.annihilator_eq_top_iff.mp h
    exact not_subsingleton E this
  have hI : Module.annihilator R E • (⊤ : Submodule R R) ≠ ⊤ := by
    change Module.annihilator R E * ⊤ ≠ ⊤
    simpa using hproper
  obtain ⟨xs, hxs⟩ := exists_maximalRegular_extension (Module.annihilator R E) R hI []
    (RingTheory.Sequence.IsRegular.nil R R) (by simp)
  have hgrade : grade (Module.annihilator R E) R = (xs.length : ℕ∞) := by
    simpa using (maximalRegular_length_eq_grade (Module.annihilator R E) R hI
      ([] ++ xs) hxs).symm
  have hnt : Nontrivial (Ext E (ModuleCat.of R R) xs.length) :=
    ((grade_eq_nat_iff E (ModuleCat.of R R) xs.length).mp hgrade).1
  rw [hgrade]
  apply le_of_not_gt
  intro hlt
  have : HasProjectiveDimensionLT E xs.length := projectiveDimension_lt_iff.mp hlt
  have hz := HasProjectiveDimensionLT.subsingleton E xs.length xs.length le_rfl
    (ModuleCat.of R R)
  exact not_nontrivial (Ext E (ModuleCat.of R R) xs.length) hnt

end AdvCommAlg.Depth
