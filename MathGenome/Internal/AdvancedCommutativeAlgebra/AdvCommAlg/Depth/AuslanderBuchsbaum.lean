import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.AuslanderBuchsbaum
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExactSequence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.MinimalFreeResolution
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Auslander–Buchsbaum for the source regular-length depth (DP-13).
The induction uses a minimal first syzygy. At projective dimension one,
minimality kills the map on residue Ext; injectivity on Hom excludes depth
zero, and the connecting map gives the drop by one. In higher dimension
the strict case of the depth lemma supplies the same drop. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct Pointwise
universe u
namespace AdvCommAlg.Depth
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
lemma depth_free (F : ModuleCat.{u} R) [Module.Finite R F] [Module.Free R F]
    [Nontrivial F] : depth R F = depth R R := by
  classical
  have hF : IsLocalRing.maximalIdeal R • (⊤ : Submodule R F) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R F))).symm
  have hR : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R R))).symm
  rw [depth_eq_grade, depth_eq_grade, grade_of_smul_ne_top _ _ hF,
    grade_of_smul_ne_top _ _ hR]
  congr 1
  ext n
  constructor <;> rintro ⟨xs, hxs, hm, rfl⟩
  · refine ⟨xs, ?_, hm, rfl⟩
    apply (RegularSequence.regular_rTensor_iff R F xs).mp
    exact ((TensorProduct.lid R F).isRegular_congr xs).mpr hxs
  · refine ⟨xs, ?_, hm, rfl⟩
    apply ((TensorProduct.lid R F).isRegular_congr xs).mp
    exact (RegularSequence.regular_rTensor_iff R F xs).mpr hxs

omit [IsNoetherianRing R] in
/-- A minimal map with finite free source induces zero on residue-field Ext.
The proof expands the source in a basis and uses m-torsion of residue Ext. -/
lemma residueExt_map_zero {U F : ModuleCat.{u} R} [Module.Finite R U]
    [Module.Free R U] (f : U ⟶ F)
    (hf : LinearMap.range f.hom ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F))
    (n : ℕ) (x : Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) U n) :
    x.comp (Ext.mk₀ f) (add_zero n) = 0 := by
  classical
  let k := ModuleCat.of R (IsLocalRing.ResidueField R)
  let L : (U ⟶ F) →ₗ[R] Ext k F n :=
    { toFun g := x.comp (Ext.mk₀ g) (add_zero n)
      map_add' g h := by simp [Ext.mk₀_add, Ext.comp_add]
      map_smul' a g := by simp [Ext.mk₀_smul] }
  have hz (c : U →ₗ[R] R) (z : F)
      (hz : z ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F)) :
      L (ModuleCat.ofHom (c.smulRight z)) = 0 := by
    let T : F →ₗ[R] (U ⟶ F) :=
      { toFun z := ModuleCat.ofHom (c.smulRight z)
        map_add' z w := by ext; simp [LinearMap.smulRight_apply, smul_add]
        map_smul' a z := by ext; simp [LinearMap.smulRight_apply, smul_smul, mul_comm] }
    change (L.comp T) z = 0
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha z _
      rw [map_smul]
      apply ExtScalarActions.annihilator_smul_eq_zero R k _ a _ n
      change a ∈ Module.annihilator R (R ⧸ IsLocalRing.maximalIdeal R)
      rwa [Ideal.annihilator_quotient]
    · intro z w hz hw
      rw [map_add, hz, hw, add_zero]
  let b := Module.Free.chooseBasis R U
  let : Fintype (Module.Free.ChooseBasisIndex R U) :=
    Fintype.ofFinite (Module.Free.ChooseBasisIndex R U)
  have heq : f = ∑ i, ModuleCat.ofHom ((b.coord i).smulRight (f.hom (b i))) := by
    apply ModuleCat.hom_ext
    ext z
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_ofHom,
      LinearMap.smulRight_apply]
    simpa only [map_sum, map_smul, Module.Basis.coord_apply] using
      (congrArg f.hom (b.sum_repr z)).symm
  change L f = 0
  rw [heq, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hz (b.coord i) _ (hf ⟨b i, rfl⟩))

lemma depth_eq_residueDepth (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth R M = (ModuleCat.of R (IsLocalRing.ResidueField R)).depth M := by
  have h := grade_eq_extDepth
    (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) M
  rw [Ideal.annihilator_quotient] at h
  exact h

lemma exists_depth_eq_nat (M : ModuleCat.{u} R) [Module.Finite R M]
    [Nontrivial M] : ∃ n : ℕ, depth R M = n := by
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  obtain ⟨xs, hxs⟩ := exists_maximalRegular_extension
    (IsLocalRing.maximalIdeal R) M hI []
    ((RegularSequence.regular_nil_iff M).mpr inferInstance) (by simp)
  exact ⟨xs.length, (maximalRegular_length_eq_grade _ M hI _ hxs).symm⟩

/-- Equal free depths drop by one at a minimal nonsplit first step.
Injectivity on Hom rules out degree zero before invoking the connecting map. -/
lemma depth_right_add_one_of_minimal_free (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    [Module.Free R S.X₁] [Nontrivial S.X₁]
    (hS : S.ShortExact)
    (hmin : LinearMap.range S.f.hom ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R S.X₂))
    (heq : depth R S.X₁ = depth R S.X₂) :
    depth R S.X₃ + 1 = depth R S.X₁ := by
  have := hS.mono_f
  let k := ModuleCat.of R (IsLocalRing.ResidueField R)
  obtain ⟨d, hd⟩ := exists_depth_eq_nat S.X₁
  have hU : k.depth S.X₁ = d := by rw [← depth_eq_residueDepth, hd]
  have hnt := ((ModuleCat.depth_eq_iff k S.X₁ d).mp hU).1
  have hz := residueExt_map_zero S.f hmin d
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    subst d
    have hinj := Ext.postcomp_mk₀_injective_of_mono k S.f
    have hzero : Subsingleton (Ext k S.X₁ 0) :=
      ⟨fun x y => hinj ((hz x).trans (hz y).symm)⟩
    exact not_subsingleton_iff_nontrivial.mpr hnt hzero
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  have hntM : Nontrivial (Ext k S.X₃ q) := by
    have hsurj : Function.Surjective (fun x : Ext k S.X₃ q =>
        x.comp hS.extClass (show q + 1 = q + 1 from rfl)) := by
      intro x
      exact Ext.covariant_sequence_exact₁ k hS x (hz x) rfl
    exact Function.Surjective.nontrivial hsurj
  have hlower := depth_min_sub_one_le_right S hS
  rw [← heq, hd] at hlower
  have hqle : (q : ℕ∞) ≤ depth R S.X₃ := by simpa using hlower
  have hvan : ∀ i < q, Subsingleton (Ext k S.X₃ i) := by
    intro i hi
    apply ModuleCat.subsingleton_ext_of_lt_depth
    rw [← depth_eq_residueDepth]
    exact (by exact_mod_cast hi : (i : ℕ∞) < q).trans_le hqle
  have hdM : depth R S.X₃ = q := by
    rw [depth_eq_residueDepth]
    exact (ModuleCat.depth_eq_iff k S.X₃ q).mpr ⟨hntM, hvan⟩
  rw [hdM, hd]
  simp

lemma depth_eq_of_iso {M N : ModuleCat.{u} R} [Module.Finite R M]
    [Module.Finite R N] (e : M ≅ N) : depth R M = depth R N := by
  rw [depth_eq_libraryDepth, depth_eq_libraryDepth]
  exact IsLocalRing.depth_eq_of_iso e

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma nontrivial_of_projectiveDimension_eq_nat (M : ModuleCat.{u} R)
    (n : ℕ) (hn : projectiveDimension M = (n : WithBot ℕ∞)) : Nontrivial M := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  have hz := (projectiveDimension_eq_bot_iff M).mpr
    (ModuleCat.isZero_iff_subsingleton.mpr hs)
  rw [hn] at hz
  simp at hz

/-- Auslander–Buchsbaum, including the projective and depth-zero boundaries. -/
theorem auslanderBuchsbaum (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (e : ℕ) (he : projectiveDimension M = (e : WithBot ℕ∞)) :
    (e : ℕ∞) + depth R M = depth R R := by
  induction e generalizing M with
  | zero =>
    have hp : Projective M := (projectiveDimension_eq_zero_iff M).mp he |>.1
    have : Module.Projective R M := inferInstance
    have : Module.Free R M := finite_projective_free M
    simpa using depth_free M
  | succ n ih =>
    obtain ⟨P, hP⟩ := exists_minimalFreeResolution M
    let S := syzygyShortComplex P 0
    have hS : S.ShortExact := syzygyShortComplex_shortExact P 0
    have := hS.mono_f
    have : Module.Finite R S.X₁ := minimalFreeResolution_syzygy_finite M P hP 1
    have : Module.Finite R S.X₂ := hP.finite 0
    have : Module.Free R S.X₂ := hP.free 0
    have : Module.Finite R S.X₃ := minimalFreeResolution_syzygy_finite M P hP 0
    have hp₃ : projectiveDimension S.X₃ = ((n + 1 : ℕ) : WithBot ℕ∞) :=
      (projectiveDimension_eq_of_iso (resolutionSyzygyZeroIso P)).trans he
    have hnp : ¬ Projective S.X₃ := by
      intro hp
      have hh := hp.projectiveDimension_le_zero
      rw [hp₃] at hh
      norm_cast at hh
    have hsucc := hS.projectiveDimension_X₃_eq_succ_of_not_projective
      (inferInstance : Projective S.X₂) hnp
    have hp₁ : projectiveDimension S.X₁ = (n : WithBot ℕ∞) := by
      apply ENat.WithBot.add_one_cancel.mp
      rw [← hsucc, hp₃]
      simp
    have : Nontrivial S.X₁ := nontrivial_of_projectiveDimension_eq_nat S.X₁ n hp₁
    have : Nontrivial S.X₂ := Function.Injective.nontrivial
      ((ModuleCat.mono_iff_injective S.f).mp inferInstance)
    have hUF := ih S.X₁ hp₁
    have hdF : depth R S.X₂ = depth R R := depth_free S.X₂
    have hdM : depth R S.X₃ = depth R M := depth_eq_of_iso (resolutionSyzygyZeroIso P)
    have hmin : LinearMap.range S.f.hom ≤
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R S.X₂) :=
      minimalFreeResolution_syzygy_inclusion M P hP 0
    obtain ⟨t, ht⟩ := exists_depth_eq_nat S.X₁
    obtain ⟨d, hd⟩ := exists_depth_eq_nat (ModuleCat.of R R)
    have hntd : n + t = d := by
      rw [ht, hd, ← Nat.cast_add] at hUF
      exact_mod_cast hUF
    have hstep : depth R S.X₃ + 1 = depth R S.X₁ := by
      by_cases hn : n = 0
      · have hp : Projective S.X₁ := (projectiveDimension_eq_zero_iff S.X₁).mp
          (by simpa [hn] using hp₁) |>.1
        have : Module.Projective R S.X₁ := inferInstance
        have : Module.Free R S.X₁ := finite_projective_free S.X₁
        apply depth_right_add_one_of_minimal_free S hS hmin
        rw [depth_free S.X₁, hdF]
      · have hlt : depth R S.X₁ < depth R S.X₂ := by
          rw [ht, hdF, hd]
          exact_mod_cast (show t < d by omega)
        obtain ⟨hpos, heq⟩ := depth_right_eq_sub_one_of_left_lt_middle S hS hlt
        rw [heq]
        exact tsub_add_cancel_of_le hpos
    rw [hdM, ht] at hstep
    calc
      ((n + 1 : ℕ) : ℕ∞) + depth R M = (n : ℕ∞) + (depth R M + 1) := by
        simp [Nat.cast_add, add_assoc, add_comm]
      _ = (n : ℕ∞) + depth R S.X₁ := by rw [hstep, ht]
      _ = depth R R := hUF

end AdvCommAlg.Depth
