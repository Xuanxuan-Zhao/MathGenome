import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ZeroTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtScalarActions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExtCharacterization

/-! DP-04: the regular-length grade equals the first nonvanishing Ext degree.
The proper-ideal case uses Mathlib's Rees theorem, with exactly the same
regular-list predicate. If IM=M, the determinant form of Nakayama supplies
an element of I acting as the identity on M; it acts both as zero and as
the identity on Ext when I annihilates N. This includes both zero modules. -/

universe u
open scoped Pointwise
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

lemma ext_subsingleton_of_annihilator_smul_eq_top
    (N M : ModuleCat.{u} R) [Module.Finite R M]
    (hI : Module.annihilator R N • (⊤ : Submodule R M) = ⊤) (i : ℕ) :
    Subsingleton (Ext N M i) := by
  obtain ⟨a, ha, haM⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    (Module.annihilator R N) (⊤ : Submodule R M) (Module.Finite.fg_top)
    (le_of_eq hI.symm)
  have hid : a • 𝟙 M = 𝟙 M := by
    ext m
    exact haM m Submodule.mem_top
  have hz (x : Ext N M i) : x = 0 := by
    have hact := ExtScalarActions.annihilator_smul_eq_zero R N M a ha i x
    rw [ExtScalarActions.scalar_eq_postcomposition R N M a i x, hid] at hact
    simpa using hact
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem grade_eq_extDepth (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] :
    grade (Module.annihilator R N) M = N.depth M := by
  by_cases hI : Module.annihilator R N • (⊤ : Submodule R M) = ⊤
  · rw [grade_of_smul_eq_top _ _ hI]
    exact ((ModuleCat.depth_eq_top_iff N M).mpr
      (ext_subsingleton_of_annihilator_smul_eq_top N M hI)).symm
  · have : Nontrivial N := by
      by_contra hn
      have : Subsingleton N := not_nontrivial_iff_subsingleton.mp hn
      have ha : Module.annihilator R N = ⊤ := Module.annihilator_eq_top_iff.mpr inferInstance
      exact hI (by simp [ha])
    rw [grade_of_smul_ne_top _ _ hI]
    exact (ModuleCat.depth_eq_sSup_length_isRegular (Module.annihilator R N) N M
      (lt_top_iff_ne_top.mpr hI) (Module.support_eq_zeroLocus (R := R) (M := N))).symm

/-- Explicit conversion from Mathlib's vanishing-threshold convention to infimum. -/
lemma extDepth_eq_iInf (N M : ModuleCat.{u} R) :
    N.depth M = ⨅ (i : ℕ) (_ : Nontrivial (Ext N M i)), (i : ℕ∞) := by
  classical
  by_cases he : ∃ i : ℕ, Nontrivial (Ext N M i)
  · let n := Nat.find he
    have hnt : Nontrivial (Ext N M n) := Nat.find_spec he
    have hd : N.depth M = n := (ModuleCat.depth_eq_iff N M n).mpr
      ⟨hnt, fun i hi => not_nontrivial_iff_subsingleton.mp (Nat.find_min he hi)⟩
    rw [hd]
    apply le_antisymm
    · apply le_iInf
      intro i
      apply le_iInf
      intro hi
      exact_mod_cast Nat.find_min' he hi
    · exact iInf_le_of_le n (iInf_le_of_le hnt le_rfl)
  · rw [(ModuleCat.depth_eq_top_iff N M).mpr (fun i =>
      not_nontrivial_iff_subsingleton.mp (fun hi => he ⟨i, hi⟩))]
    apply le_antisymm ?_ le_top
    apply le_iInf
    intro i
    apply le_iInf
    intro hi
    exact False.elim (he ⟨i, hi⟩)

theorem grade_eq_iInf_ext (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] :
    grade (Module.annihilator R N) M =
      ⨅ (i : ℕ) (_ : Nontrivial (Ext N M i)), (i : ℕ∞) := by
  rw [grade_eq_extDepth, extDepth_eq_iInf]

theorem grade_eq_idealDepth (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    grade I M = I.depth M := by
  by_cases hI : I • (⊤ : Submodule R M) = ⊤
  · have h := grade_eq_extDepth (ModuleCat.of R (R ⧸ I)) M
    rw [Ideal.annihilator_quotient] at h
    rw [h]
    exact ModuleCat.depth_eq_of_linearEquiv
      (Shrink.linearEquiv R (R ⧸ I)).symm (LinearEquiv.refl R M)
  · rw [grade_of_smul_ne_top _ _ hI]
    exact (Ideal.depth_eq_sSup_length_isRegular I M (lt_top_iff_ne_top.mpr hI)).symm

theorem grade_eq_quotient_ext (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    grade I M =
      ⨅ (i : ℕ) (_ : Nontrivial (Ext (ModuleCat.of R (R ⧸ I)) M i)), (i : ℕ∞) := by
  simpa only [Ideal.annihilator_quotient] using
    grade_eq_iInf_ext (ModuleCat.of R (R ⧸ I)) M

theorem depth_eq_libraryDepth [IsLocalRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] : depth R M = IsLocalRing.depth M :=
  grade_eq_idealDepth _ M

theorem depth_eq_residue_ext [IsLocalRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] : depth R M =
      ⨅ (i : ℕ) (_ : Nontrivial (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) M i)),
        (i : ℕ∞) :=
  grade_eq_quotient_ext _ M

theorem grade_eq_nat_iff (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] (n : ℕ) :
    grade (Module.annihilator R N) M = n ↔
      Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  rw [grade_eq_extDepth, ModuleCat.depth_eq_iff]

theorem grade_eq_top_iff_ext_zero (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] :
    grade (Module.annihilator R N) M = ⊤ ↔ ∀ i : ℕ, Subsingleton (Ext N M i) := by
  rw [grade_eq_extDepth, ModuleCat.depth_eq_top_iff]

lemma ideal_smul_quotSMulTop_ne_top (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] (a : R) (ha : a ∈ I)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    I • (⊤ : Submodule R (QuotSMulTop a M)) ≠ ⊤ := by
  intro he
  apply hI
  have h := congrArg (Submodule.comap (Submodule.mkQ (a • (⊤ : Submodule R M)))) he
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr ha),
    ← Submodule.ideal_span_singleton_smul] using h

/-- In a maximal regular list the terminal quotient has grade zero. Induction
backwards uses vanishing below the list length and injectivity of the connecting
map to obtain nonvanishing at that length. -/
theorem maximalRegular_length_eq_grade (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (xs : List R)
    (hmax : MaximalRegular I M xs) : (xs.length : ℕ∞) = grade I M := by
  induction xs generalizing M with
  | nil =>
    apply Eq.symm
    apply (grade_zero_iff_no_regular I M hI).mpr
    intro a ha hreg
    apply hmax.2.2 a ha
    refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff M a).mpr hreg, ?_⟩
    exact (ne_top_of_le_ne_top hI (Submodule.smul_mono_left
      (Ideal.span_le.mpr (by simpa using ha)))).symm
  | cons a xs ih =>
    have hreg := (RingTheory.Sequence.isRegular_cons_iff M a xs).mp hmax.1
    have ha : a ∈ I := hmax.2.1 a (by simp)
    have hmem : ∀ b ∈ xs, b ∈ I := fun b hb => hmax.2.1 b (by simp [hb])
    have hqI := ideal_smul_quotSMulTop_ne_top I M a ha hI
    have htail : MaximalRegular I (QuotSMulTop a M) xs := by
      refine ⟨hreg.2, hmem, ?_⟩
      intro b hb hbad
      exact hmax.2.2 b hb
        ((RingTheory.Sequence.isRegular_cons_iff M a (xs ++ [b])).mpr ⟨hreg.1, hbad⟩)
    have hlen := ih (QuotSMulTop a M) hqI htail
    let N := ModuleCat.of R (R ⧸ I)
    let U := ModuleCat.of R M
    let V := ModuleCat.of R (QuotSMulTop a M)
    have hvan : ∀ i < (a :: xs).length, Subsingleton (Ext N U i) :=
      ModuleCat.subsingleton_ext_of_exists_isRegular I N
        (by rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]) U
        (lt_top_iff_ne_top.mpr hI) (a :: xs) hmax.2.1 hmax.1
    have hdV : N.depth V = xs.length := by
      rw [← grade_eq_extDepth, Ideal.annihilator_quotient]
      exact hlen.symm
    have hntV := ((ModuleCat.depth_eq_iff N V xs.length).mp hdV).1
    letI : Nontrivial (Ext N V xs.length) := hntV
    have hzU := hvan xs.length (by simp)
    have hmono := (Ext.covariant_sequence_exact₃' N
      (IsSMulRegular.smulShortComplex_shortExact (M := U) (r := a) hreg.1)
      xs.length (xs.length + 1) rfl).mono_g
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr hzU).eq_zero_of_src _)
    have hinj := (AddCommGrpCat.mono_iff_injective _).mp hmono
    have hntU : Nontrivial (Ext N U (xs.length + 1)) :=
      @Function.Injective.nontrivial (Ext N V xs.length) (Ext N U (xs.length + 1))
        hntV _ hinj
    have hdU := (ModuleCat.depth_eq_iff N U (xs.length + 1)).mpr
      ⟨hntU, by simpa only [List.length_cons] using hvan⟩
    rw [← grade_eq_extDepth, Ideal.annihilator_quotient] at hdU
    exact hdU.symm

/-- The uniform finite bound from DP-02 lets us choose an extension of greatest
length. Any further regular element would contradict its greatest length. -/
theorem exists_maximalRegular_extension (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (xs : List R)
    (hreg : RingTheory.Sequence.IsRegular M xs) (hmem : ∀ a ∈ xs, a ∈ I) :
    ∃ ys : List R, MaximalRegular I M (xs ++ ys) := by
  classical
  obtain ⟨n, hn⟩ := regular_lengths_bounded M I hI
  let P : ℕ → Prop := fun k => ∃ ys : List R,
    RingTheory.Sequence.IsRegular M (xs ++ ys) ∧
      (∀ a ∈ xs ++ ys, a ∈ I) ∧ (xs ++ ys).length = k
  have hP : P xs.length := ⟨[], by simpa using hreg, by simpa using hmem, by simp⟩
  obtain ⟨ys, hys, hysI, hlen⟩ := Nat.findGreatest_spec (hn xs hreg hmem) hP
  refine ⟨ys, hys, hysI, ?_⟩
  intro a ha hbad
  have hbadI : ∀ b ∈ (xs ++ ys) ++ [a], b ∈ I := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hysI b hb
    · simpa using (List.mem_singleton.mp hb) ▸ ha
  have hPk : P ((xs ++ ys) ++ [a]).length :=
    ⟨ys ++ [a], by simpa only [List.append_assoc] using hbad,
      by simpa only [List.append_assoc] using hbadI, by simp⟩
  have hle := Nat.le_findGreatest (hn _ hbad hbadI) hPk
  simp only [List.length_append, List.length_singleton] at hle hlen
  omega

end AdvCommAlg.Depth
