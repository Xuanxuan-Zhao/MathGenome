import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.FiniteExtDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.InjectiveDimensionTest

/-! GC-02: testing the actual injective dimension at the residue field.
Finite-module Ext detection supplies vanishing on every cyclic quotient.
The all-ideal Baer criterion, including dimension shifting, supplies the
injective-dimension bound. For the top-degree assertion, DP-04 supplies
some nonzero residue-field Ext of every nonzero finite module. This treats
injective dimension zero as well as the positive dimensions.
-/

universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

namespace AdvCommAlg.Gorenstein.InjectiveDimensionTest

variable (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]

/-- The bound includes the zero coefficient module, whose dimension is `⊥`. -/
theorem injectiveDimension_le_iff_residue_ext
    (N : ModuleCat.{u} R) [Module.Finite R N] (n : ℕ) :
    injectiveDimension N ≤ (n : WithBot ℕ∞) ↔
      ∀ i : ℕ, n < i →
        Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i) := by
  constructor
  · intro h i hi
    have := (injectiveDimension_le_iff N n).mp h
    exact HasInjectiveDimensionLT.subsingleton N (n + 1) i (by omega) _
  · intro h
    apply (injectiveDimension_le_iff N n).mpr
    apply ModuleCat.hasInjectiveDimensionLE_of_quotients N n
    intro I
    apply FiniteExtDetection.finite_ext_vanishing R N n _
      (ModuleCat.of R (Shrink.{u} (R ⧸ I))) (n + 1) (by omega)
    intro i hi
    have := h i hi
    exact FiniteExtDetection.subsingleton_ext_of_linearEquiv
      (B := ModuleCat.of R (IsLocalRing.ResidueField R))
      (Shrink.linearEquiv R (R ⧸ IsLocalRing.maximalIdeal R)) i

/-- A nonzero finite module has a nonzero residue-field Ext in some degree.
Choose a maximal regular list using DP-04, then apply its grade criterion. -/
lemma exists_nontrivial_residue_ext (N : ModuleCat.{u} R)
    [Module.Finite R N] [Nontrivial N] :
    ∃ i : ℕ, Nontrivial (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i) := by
  have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R N))).symm
  obtain ⟨xs, hxs⟩ := Depth.exists_maximalRegular_extension
    (IsLocalRing.maximalIdeal R) N hproper []
    (RingTheory.Sequence.IsRegular.nil R N) (by simp)
  have hd := Depth.maximalRegular_length_eq_grade
    (IsLocalRing.maximalIdeal R) N hproper ([] ++ xs) hxs
  have hg : Depth.grade
      (Module.annihilator R (ModuleCat.of R (IsLocalRing.ResidueField R))) N = xs.length := by
    change Depth.grade (Module.annihilator R (R ⧸ IsLocalRing.maximalIdeal R)) N = _
    rw [Ideal.annihilator_quotient]
    simpa only [List.nil_append] using hd.symm
  exact ⟨xs.length, ((Depth.grade_eq_nat_iff
    (ModuleCat.of R (IsLocalRing.ResidueField R)) N xs.length).mp hg).1⟩

/-- Equality detects the top nonvanishing degree, including degree zero. -/
theorem injectiveDimension_eq_iff_residue_ext
    (N : ModuleCat.{u} R) [Module.Finite R N] [Nontrivial N] (n : ℕ) :
    injectiveDimension N = (n : WithBot ℕ∞) ↔
      Nontrivial (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N n) ∧
      ∀ i : ℕ, n < i →
        Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i) := by
  classical
  constructor
  · intro hd
    have hvan := (injectiveDimension_le_iff_residue_ext R N n).mp hd.le
    refine ⟨?_, hvan⟩
    by_contra hn
    have hz := not_nontrivial_iff_subsingleton.mp hn
    cases n with
    | zero =>
      obtain ⟨i, hi⟩ := exists_nontrivial_residue_ext R N
      have : Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i) := by
        cases i with
        | zero => exact hz
        | succ i => exact hvan (i + 1) (by omega)
      exact not_nontrivial _ hi
    | succ n =>
      have hsmall : injectiveDimension N ≤ (n : WithBot ℕ∞) :=
        (injectiveDimension_le_iff_residue_ext R N n).mpr (by
          intro i hi
          by_cases he : i = n + 1
          · subst i
            exact hz
          · exact hvan i (by omega))
      rw [hd] at hsmall
      have : n + 1 ≤ n := by exact_mod_cast hsmall
      omega
  · rintro ⟨hnt, hvan⟩
    apply le_antisymm ((injectiveDimension_le_iff_residue_ext R N n).mpr hvan)
    apply (injectiveDimension_ge_iff N n).mpr
    intro hlt
    have := HasInjectiveDimensionLT.subsingleton N n n le_rfl
      (ModuleCat.of R (IsLocalRing.ResidueField R))
    exact not_nontrivial _ hnt

theorem injectiveDimension_eq_iff_isGreatest_residue_ext
    (N : ModuleCat.{u} R) [Module.Finite R N] [Nontrivial N] (n : ℕ) :
    injectiveDimension N = (n : WithBot ℕ∞) ↔
      IsGreatest {i : ℕ | Nontrivial
        (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i)} n := by
  rw [injectiveDimension_eq_iff_residue_ext R N n]
  constructor
  · rintro ⟨hn, hv⟩
    refine ⟨hn, ?_⟩
    intro i hi
    by_contra hle
    have := hv i (lt_of_not_ge hle)
    exact not_nontrivial _ hi
  · rintro ⟨hn, hmax⟩
    refine ⟨hn, ?_⟩
    intro i hi
    exact not_nontrivial_iff_subsingleton.mp (fun h => (not_le_of_gt hi) (hmax h))

/-- Finite injective dimension is the greatest nonvanishing Ext degree.
The nonzero hypothesis rules out the library's value `⊥`. -/
theorem finite_injectiveDimension_eq_greatest
    (N : ModuleCat.{u} R) [Module.Finite R N] [Nontrivial N]
    (hfinite : injectiveDimension N ≠ ⊤) :
    ∃ n : ℕ, injectiveDimension N = (n : WithBot ℕ∞) ∧
      IsGreatest {i : ℕ | Nontrivial
        (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i)} n := by
  have hbot : injectiveDimension N ≠ ⊥ := by
    intro h
    have := ModuleCat.isZero_iff_subsingleton.mp ((injectiveDimension_eq_bot_iff N).mp h)
    exact not_nontrivial N inferInstance
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hdt : d ≠ ⊤ := by
    intro h
    exact hfinite (by simpa [h] using hd.symm)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hdt
  have heq : injectiveDimension N = (n : WithBot ℕ∞) := by
    rw [← hd, ← hn]
    rfl
  exact ⟨n, heq, (injectiveDimension_eq_iff_isGreatest_residue_ext R N n).mp heq⟩

end AdvCommAlg.Gorenstein.InjectiveDimensionTest
