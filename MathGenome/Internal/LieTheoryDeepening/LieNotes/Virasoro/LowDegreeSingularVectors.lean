import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.VermaModules
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.LowDegreeSingularVectors
import Mathlib.Tactic.LinearCombination

/-! The first two singular degrees of the Virasoro Verma module. -/

noncomputable section

namespace LieNotes.Virasoro.Singular

open VermaSpec SingularSpec

local notation "Lᵥ" => VirasoroSpec.mode
local notation "C" => VirasoroSpec.central

private def firstWord : Word := Shared.Lie.PBW.singletonWord 0
private def secondWord : Word := Shared.Lie.PBW.singletonWord 1
private def squareWord : Word := ⟨[0, 0], by simp⟩

private theorem word_of_degree_one (w : Word) (hw : (wordDegree w : ℤ) = 1) :
    w.val = [0] := by
  obtain ⟨l, _⟩ := w
  cases l with
  | nil => simp [wordDegree] at hw
  | cons i l =>
    cases l with
    | nil =>
      have hi : i = 0 := by
        simp [wordDegree] at hw
        omega
      simp [hi]
    | cons j l =>
      simp only [wordDegree, List.map_cons, List.sum_cons, Nat.cast_add] at hw
      omega

private theorem word_of_degree_two (w : Word) (hw : (wordDegree w : ℤ) = 2) :
    w.val = [1] ∨ w.val = [0, 0] := by
  obtain ⟨l, _⟩ := w
  cases l with
  | nil => simp [wordDegree] at hw
  | cons i l =>
    cases l with
    | nil =>
      have hi : i = 1 := by
        simp [wordDegree] at hw
        omega
      exact Or.inl (by simp [hi])
    | cons j l =>
      cases l with
      | nil =>
        have hij : i = 0 ∧ j = 0 := by
          simp [wordDegree] at hw
          omega
        exact Or.inr (by simp [hij.1, hij.2])
      | cons k l =>
        simp only [wordDegree, List.map_cons, List.sum_cons, Nat.cast_add] at hw
        omega

section Models

variable [r : LieRing V] [a : LieAlgebra ℂ V]
variable {D : InducingData} (P : ModelProperties.{0} D)
variable (c h : ℂ)
include P

private theorem degree_one_span : D.degree c h 1 = Submodule.span ℂ {first D c h} := by
  rw [P.degree_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact Set.mem_singleton_iff.mpr (congrArg (D.applyWord c h) (word_of_degree_one w hw))
  · intro hx
    exact ⟨firstWord, rfl, Set.mem_singleton_iff.mp hx⟩

private theorem degree_two_span :
    D.degree c h 2 = Submodule.span ℂ {second D c h, square D c h} := by
  rw [P.degree_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases word_of_degree_two w hw with hw | hw
    · exact Or.inl (congrArg (D.applyWord c h) hw)
    · exact Or.inr (Set.mem_singleton_iff.mpr (congrArg (D.applyWord c h) hw))
  · rintro (hx | hx)
    · exact ⟨secondWord, rfl, hx⟩
    · exact ⟨squareWord, rfl, Set.mem_singleton_iff.mp hx⟩

private theorem first_ne_zero : first D c h ≠ 0 := by
  obtain ⟨b, hb⟩ := P.orderedBasis c h
  rw [← show b firstWord = first D c h from hb firstWord]
  exact b.ne_zero _

private theorem degree_two_independent (a b : ℂ)
    (hz : a • second D c h + b • square D c h = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨B, hB⟩ := P.orderedBasis c h
  have hne : secondWord ≠ squareWord := by decide
  rw [← show B secondWord = second D c h from hB secondWord,
      ← show B squareWord = square D c h from hB squareWord] at hz
  constructor
  · have he := congrArg (B.coord secondWord) hz
    simpa [Module.Basis.coord_apply, hne, hne.symm] using he
  · have he := congrArg (B.coord squareWord) hz
    simpa [Module.Basis.coord_apply, hne, hne.symm] using he

private theorem first_weight : ⁅Lᵥ 0, first D c h⁆ = (h + 1) • first D c h := by
  have hw := P.word_weight c h firstWord
  have he := Module.End.mem_eigenspace_iff.mp hw
  change ⁅Lᵥ 0, first D c h⁆ = (h + ((1 : ℤ) : ℂ)) • first D c h at he
  simpa only [Int.cast_one] using he

private theorem action_rows (bracket : ModeBracket) : ActionRows D c h := by
  let _ : AddCommGroup V := r.toAddCommGroup
  let _ : Module ℂ V := a.toModule
  obtain ⟨hc, hzero, hpos⟩ := P.highestWeight c h
  have b11 : ⁅Lᵥ 1, Lᵥ (-1)⁆ = (2 : ℂ) • Lᵥ 0 := by
    have hb := bracket 1 (-1)
    norm_num [VirasoroSpec.centralCoefficient] at hb ⊢
    exact hb
  have b12 : ⁅Lᵥ 1, Lᵥ (-2)⁆ = (3 : ℂ) • Lᵥ (-1) := by
    have hb := bracket 1 (-2)
    norm_num [VirasoroSpec.centralCoefficient] at hb ⊢
    exact hb
  have b21 : ⁅Lᵥ 2, Lᵥ (-1)⁆ = (3 : ℂ) • Lᵥ 1 := by
    have hb := bracket 2 (-1)
    norm_num [VirasoroSpec.centralCoefficient] at hb ⊢
    exact hb
  have b22 : ⁅Lᵥ 2, Lᵥ (-2)⁆ = (4 : ℂ) • Lᵥ 0 + (1 / 2 : ℂ) • C := by
    have hb := bracket 2 (-2)
    norm_num [VirasoroSpec.centralCoefficient] at hb ⊢
    exact hb
  have first_one : ⁅Lᵥ 1, first D c h⁆ = (2 * h) • D.top c h := by
    change ⁅Lᵥ 1, ⁅Lᵥ (-1), D.top c h⁆⁆ = _
    rw [leibniz_lie, b11, smul_lie, hzero, hpos 1 (by decide), lie_zero, add_zero, smul_smul]
  refine ⟨first_one, ?_, ?_, ?_, ?_⟩
  · change ⁅Lᵥ 1, ⁅Lᵥ (-2), D.top c h⁆⁆ = _
    rw [leibniz_lie, b12, smul_lie, hpos 1 (by decide), lie_zero, add_zero]
    rfl
  · change ⁅Lᵥ 1, ⁅Lᵥ (-1), first D c h⁆⁆ = _
    rw [leibniz_lie, b11, smul_lie, first_weight P c h, first_one, lie_smul, smul_smul]
    change (2 * (h + 1)) • first D c h + (2 * h) • first D c h = _
    rw [← add_smul]
    congr 1
    ring
  · change ⁅Lᵥ 2, ⁅Lᵥ (-2), D.top c h⁆⁆ = _
    rw [leibniz_lie, b22, add_lie, smul_lie, smul_lie, hzero, hc, hpos 2 (by decide),
      lie_zero, add_zero, smul_smul, smul_smul, ← add_smul]
    congr 1
    ring
  · have first_two : ⁅Lᵥ 2, first D c h⁆ = 0 := by
      exact P.kills_below c h 2 1 _ (P.word_weight c h firstWord) (by decide)
    change ⁅Lᵥ 2, ⁅Lᵥ (-1), first D c h⁆⁆ = _
    rw [leibniz_lie, b21, smul_lie, first_one, first_two, lie_zero, add_zero, smul_smul]
    congr 1
    ring

private theorem first_singular (rows : ActionRows D c h) (hh : h = 0) :
    first D c h ∈ singularSpace D c h 1 := by
  have hw : first D c h ∈ D.degree c h 1 := P.word_weight c h firstWord
  refine ⟨hw, fun j hj => ?_⟩
  by_cases hj1 : j = 1
  · subst j
    rw [rows.first_one, hh, mul_zero, zero_smul]
  · exact P.kills_below c h j 1 _ hw (by omega)

private theorem degree_one_exists (rows : ActionRows D c h) :
    (∃ x ∈ singularSpace D c h 1, x ≠ 0) ↔ h = 0 := by
  constructor
  · rintro ⟨x, hx, hn⟩
    have hw : x ∈ Submodule.span ℂ {first D c h} := (degree_one_span P c h) ▸ hx.1
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have ha : a ≠ 0 := by
      rintro rfl
      exact hn (zero_smul _ _)
    have hz := hx.2 1 (by decide)
    rw [lie_smul, rows.first_one, smul_smul] at hz
    have hz' := (smul_eq_zero.mp hz).resolve_right (P.top_ne_zero c h)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left ha)).resolve_left (by norm_num)
  · intro hh
    exact ⟨_, first_singular P c h rows hh, first_ne_zero P c h⟩

private theorem degree_one_line (rows : ActionRows D c h) (hh : h = 0) :
    singularSpace D c h 1 = Submodule.span ℂ {first D c h} := by
  apply le_antisymm
  · intro x hx
    exact (degree_one_span P c h) ▸ hx.1
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (first_singular P c h rows hh))

omit P in
private theorem generator_rows (rows : ActionRows D c h) :
    ⁅Lᵥ 1, degreeTwoGenerator D c h⁆ = 0 ∧
      ⁅Lᵥ 2, degreeTwoGenerator D c h⁆ = determinant c h • D.top c h := by
  constructor
  · simp only [degreeTwoGenerator, lie_sub,
      lie_smul, rows.square_one,
      rows.second_one, smul_smul, mul_comm (3 : ℂ), sub_self]
  · simp only [degreeTwoGenerator, lie_sub,
      lie_smul, rows.square_two,
      rows.second_two, smul_smul, ← sub_smul, determinant]
    congr 1
    ring

private theorem degree_two_generator_ne_zero : degreeTwoGenerator D c h ≠ 0 := by
  intro hz
  have he : (-(4 * h + 2)) • second D c h + (3 : ℂ) • square D c h = 0 := by
    simpa only [degreeTwoGenerator, sub_eq_add_neg, neg_smul, add_comm] using hz
  exact (by norm_num : (3 : ℂ) ≠ 0) (degree_two_independent P c h _ _ he).2

private theorem generator_singular (rows : ActionRows D c h) (hdet : determinant c h = 0) :
    degreeTwoGenerator D c h ∈ singularSpace D c h 2 := by
  have hw : degreeTwoGenerator D c h ∈ D.degree c h 2 :=
    (D.degree c h 2).sub_mem
      ((D.degree c h 2).smul_mem _ (P.word_weight c h squareWord))
      ((D.degree c h 2).smul_mem _ (P.word_weight c h secondWord))
  refine ⟨hw, fun j hj => ?_⟩
  obtain hj1 | hj2 | hj3 : j = 1 ∨ j = 2 ∨ 2 < j := by omega
  · subst j
    exact (generator_rows c h rows).1
  · subst j
    rw [(generator_rows c h rows).2, hdet, zero_smul]
  · exact P.kills_below c h j 2 _ hw (by omega)

-- The first row has a constant nonzero pivot, including when its second entry vanishes.
private theorem mem_line_of_singular_two (rows : ActionRows D c h)
    {x : D.Verma c h} (hx : x ∈ singularSpace D c h 2) :
    x ∈ Submodule.span ℂ {degreeTwoGenerator D c h} := by
  have hw : x ∈ Submodule.span ℂ {second D c h, square D c h} := (degree_two_span P c h) ▸ hx.1
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
  have hz := hx.2 1 (by decide)
  simp only [lie_add,
    lie_smul, rows.second_one,
    rows.square_one, smul_smul, ← add_smul] at hz
  have hab : a * 3 + b * (4 * h + 2) = 0 := (smul_eq_zero.mp hz).resolve_right (first_ne_zero P c h)
  refine Submodule.mem_span_singleton.mpr ⟨b / 3, ?_⟩
  have ha : -(b / 3 * (4 * h + 2)) = a := by
    linear_combination (- (1 / 3 : ℂ)) * hab
  have hb : b / 3 * 3 = b := by ring
  rw [degreeTwoGenerator, smul_sub, smul_smul, smul_smul, hb, sub_eq_add_neg, ← neg_smul, ha, add_comm]

private theorem degree_two_exists (rows : ActionRows D c h) :
    (∃ x ∈ singularSpace D c h 2, x ≠ 0) ↔ determinant c h = 0 := by
  constructor
  · rintro ⟨x, hx, hn⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (mem_line_of_singular_two P c h rows hx)
    have ha : a ≠ 0 := by
      rintro rfl
      exact hn (zero_smul _ _)
    have hz := hx.2 2 (by decide)
    rw [lie_smul, (generator_rows c h rows).2, smul_smul] at hz
    exact (mul_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (P.top_ne_zero c h))).resolve_left ha
  · intro hdet
    exact ⟨_, generator_singular P c h rows hdet, degree_two_generator_ne_zero P c h⟩

private theorem degree_two_line (rows : ActionRows D c h) (hdet : determinant c h = 0) :
    singularSpace D c h 2 = Submodule.span ℂ {degreeTwoGenerator D c h} := by
  apply le_antisymm
  · exact fun _ hx => mem_line_of_singular_two P c h rows hx
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (generator_singular P c h rows hdet))

private theorem generated_degrees (d : ℤ) (x : D.Verma c h) (hx : x ∈ singularSpace D c h d) :
    (LieSubmodule.lieSpan ℂ V {x}).toSubmodule ≤ ⨆ n : ℕ, D.degree c h (d + n) := by
  have hw : IsHighestWeight c (h + (d : ℂ)) x :=
    ⟨P.central_action c h x, Module.End.mem_eigenspace_iff.mp hx.1, hx.2⟩
  -- The image of the Verma module with highest weight h+d contains the generated submodule.
  obtain ⟨f, hf, _⟩ := P.universal c (h + (d : ℂ)) x hw
  have hspan : LieSubmodule.lieSpan ℂ V {x} ≤ f.range :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr ((f.mem_range x).mpr ⟨_, hf⟩))
  obtain ⟨b, hb⟩ := P.orderedBasis c (h + (d : ℂ))
  let S := ⨆ n : ℕ, D.degree c h (d + n)
  have hword (w : Word) : f (b w) ∈ S := by
    have he := Module.End.mem_eigenspace_iff.mp (P.word_weight c (h + (d : ℂ)) w)
    have hef := congrArg f he
    have hm : f (b w) ∈ D.degree c h (d + (wordDegree w : ℤ)) := by
      rw [hb]
      apply Module.End.mem_eigenspace_iff.mpr
      change ⁅Lᵥ 0, f (D.applyWord c (h + (d : ℂ)) w.val)⁆ =
        (h + ((d + (wordDegree w : ℤ) : ℤ) : ℂ)) • f (D.applyWord c (h + (d : ℂ)) w.val)
      rw [Int.cast_add, ← add_assoc]
      change f ⁅Lᵥ 0, D.applyWord c (h + (d : ℂ)) w.val⁆ =
        f ((h + (d : ℂ) + ((wordDegree w : ℤ) : ℂ)) • D.applyWord c (h + (d : ℂ)) w.val) at hef
      simpa only [LieModuleHom.map_lie, map_smul] using hef
    exact le_iSup (fun n : ℕ => D.degree c h (d + n)) (wordDegree w) hm
  intro y hy
  obtain ⟨z, rfl⟩ := (f.mem_range y).mp (hspan hy)
  have hle : Submodule.span ℂ (Set.range b) ≤ S.comap (f : _ →ₗ[ℂ] _) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact hword w
  exact hle (b.mem_span z)

private theorem generated_proper (d : ℤ) (x : D.Verma c h) (hd : 0 < d)
    (hx : x ∈ singularSpace D c h d) :
    D.top c h ∉ LieSubmodule.lieSpan ℂ V {x} ∧ LieSubmodule.lieSpan ℂ V {x} ≠ ⊤ := by
  obtain ⟨b, hb⟩ := P.orderedBasis c h
  let e := Shared.Lie.PBW.emptyWord ℕ
  have hker : (⨆ n : ℕ, D.degree c h (d + n)) ≤ LinearMap.ker (b.coord e) := by
    apply iSup_le
    intro n
    rw [P.degree_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hdw, rfl⟩
    have hn : w ≠ e := by
      intro he
      subst w
      change (0 : ℤ) = d + n at hdw
      omega
    change D.applyWord c h w.val ∈ LinearMap.ker (b.coord e)
    rw [← hb w, LinearMap.mem_ker, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hn.symm]
  have htop : D.top c h ∉ LieSubmodule.lieSpan ℂ V {x} := by
    intro ht
    have hz : D.top c h ∈ LinearMap.ker (b.coord e) := hker (generated_degrees P c h d x hx ht)
    rw [← show b e = D.top c h from hb e, LinearMap.mem_ker, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same] at hz
    exact one_ne_zero hz
  exact ⟨htop, fun he => htop (he ▸ LieSubmodule.mem_top (D.top c h))⟩

end Models

theorem resultsOnModels : ResultsOnModels := by
  intro r a bracket D P
  have rows := fun c h => action_rows P c h bracket
  have example_det : determinant 1 (1 / 4) = 0 := by
    norm_num [determinant]
  refine
    { degree_one_span := degree_one_span P
      first_ne_zero := first_ne_zero P
      degree_two_span := degree_two_span P
      degree_two_independent := degree_two_independent P
      action_rows := rows
      higher_modes := fun c h d j x hx hj => P.kills_below c h j d x hx (by omega)
      degree_one_exists := fun c h => degree_one_exists P c h (rows c h)
      degree_one_line := fun c h => degree_one_line P c h (rows c h)
      degree_two_exists := fun c h => degree_two_exists P c h (rows c h)
      degree_two_line := fun c h => degree_two_line P c h (rows c h)
      generated_degrees := generated_degrees P
      generated_proper := generated_proper P
      first_positive_example := ?_
      example_line := ?_ }
  · refine ⟨⟨by decide, (degree_two_exists P 1 (1 / 4) (rows 1 (1 / 4))).mpr example_det⟩, ?_⟩
    rintro d ⟨hd, hex⟩
    by_contra! hlt
    have he : d = 1 := by omega
    subst d
    have hbad := (degree_one_exists P 1 (1 / 4) (rows 1 (1 / 4))).mp hex
    norm_num at hbad
  · rw [degree_two_line P 1 (1 / 4) (rows 1 (1 / 4)) example_det]
    have he : degreeTwoGenerator D 1 (1 / 4) = (3 : ℂ) • (square D 1 (1 / 4) - second D 1 (1 / 4)) := by
      unfold degreeTwoGenerator
      rw [smul_sub, show (4 : ℂ) * (1 / 4) + 2 = 3 by norm_num]
    rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num : (3 : ℂ) ≠ 0))]

/-- The conclusions on the canonical induced Verma module. -/
theorem canonical : Results Verma.inducingData :=
  resultsOnModels Vir.lie_L Verma.inducingData Verma.modelProperties

theorem canonicalResult : CanonicalResult :=
  ⟨inferInstanceAs (LieRing Vir), inferInstanceAs (LieAlgebra ℂ Vir),
    rfl, HEq.rfl, fun _ _ => rfl, Verma.inducingData, Verma.modelProperties, canonical⟩

end LieNotes.Virasoro.Singular
