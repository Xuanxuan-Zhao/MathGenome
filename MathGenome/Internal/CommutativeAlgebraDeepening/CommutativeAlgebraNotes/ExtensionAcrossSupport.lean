import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExtensionAcrossSupport
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyOfComplement
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GradeFromLocalCohomology

open CategoryTheory
open Specs.CommutativeAlgebraNotes.LocalCohomologyOfComplement (complementRestriction)

namespace CommutativeAlgebraNotes

universe u

private theorem grade_ge_two_iff (R : CommRingCat.{u}) [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    2 ≤ AdvCommAlg.Depth.grade I M ↔
      Subsingleton ((localCohomology I 0).obj M) ∧
      Subsingleton ((localCohomology I 1).obj M) := by
  have hgrade := grade_eq_inf_localCohomology (R := R) I M
  change AdvCommAlg.Depth.grade I M =
    ⨅ q : {q : ℕ // Nontrivial ((localCohomology I (q : ℤ)).obj M)}, (q.val : ℕ∞)
    at hgrade
  rw [hgrade, le_iInf_iff]
  constructor
  · intro h
    refine ⟨not_nontrivial_iff_subsingleton.mp ?_, not_nontrivial_iff_subsingleton.mp ?_⟩
    · intro h₀
      have hle := h ⟨0, h₀⟩
      norm_num at hle
    · intro h₁
      have hle := h ⟨1, h₁⟩
      norm_num at hle
  · rintro ⟨h₀, h₁⟩ ⟨q, hq⟩
    change (2 : ℕ∞) ≤ (q : ℕ∞)
    suffices 2 ≤ q by exact_mod_cast this
    cases q with
    | zero => exact (not_nontrivial_iff_subsingleton.mpr h₀ hq).elim
    | succ q =>
      cases q with
      | zero => exact (not_nontrivial_iff_subsingleton.mpr h₁ hq).elim
      | succ q => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le q))

/-- Extension across the support, Corollary 2.8. -/
theorem complementRestriction_isIso_iff_grade :
    Specs.CommutativeAlgebraNotes.ExtensionAcrossSupport.restrictionIsIsoIffGradeType.{u} := by
  intro R _ I M _
  rw [← complementRestriction_app, grade_ge_two_iff]
  obtain ⟨e, δ, _, hexact⟩ := localCohomologyComplement_exact R I
  obtain ⟨ha, hab, hbδ, hδ⟩ := hexact M
  let a := (e.inv ≫ Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsionInclusion I).app M
  let b := (complementRestriction R I).app M
  change IsIso b ↔ _
  rw [ConcreteCategory.isIso_iff_bijective]
  have hinj : Function.Injective b ↔ a.hom = 0 :=
    LinearMap.injective_iff_eq_zero_of_exact hab
  have hsurj : Function.Surjective b ↔ (δ.app M).hom = 0 :=
    LinearMap.surjective_iff_eq_zero_of_exact hbδ
  constructor
  · intro hb
    have ha₀ := hinj.mp hb.1
    have hδ₀ := hsurj.mp hb.2
    constructor
    · refine ⟨fun x y => ha ?_⟩
      change a.hom x = a.hom y
      simp [ha₀]
    · refine ⟨fun x y => ?_⟩
      obtain ⟨x', rfl⟩ := hδ x
      obtain ⟨y', rfl⟩ := hδ y
      change (δ.app M).hom x' = (δ.app M).hom y'
      simp [hδ₀]
  · rintro ⟨h₀, h₁⟩
    exact ⟨hinj.mpr (Subsingleton.elim _ _), hsurj.mpr (Subsingleton.elim _ _)⟩

end CommutativeAlgebraNotes
