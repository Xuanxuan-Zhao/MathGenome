import MathGenome.Internal.D07.Ch17.IrreducibleDefinitionFiniteSemisimpleDecomposition
import MathGenome.Internal.Specs.D07.Ch17.IrreducibleDefinition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace D07.Ch17.IrreducibleDefinition
universe u v w
noncomputable section
open Specs.D07.Ch17.IrreducibleDefinition

abbrev IsIrreducible : PredicateType.{u,v,w} := irreducibleValue
abbrev IsSemisimple : PredicateType.{u,v,w} := semisimpleValue
abbrev IsIndecomposable : PredicateType.{u,v,w} := indecomposableValue
abbrev rotation := rotationValue

variable {K : Type u} {G : Type v} {V : Type w}
  [Field K] [Group G] [AddCommGroup V] [Module K V]

lemma irreducible_nontrivial {ρ : Representation K G V} (h : Representation.IsIrreducible ρ) :
    Nontrivial V := by
  classical
  by_contra hn
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
  have := h
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)

lemma irreducible_iff_subrepresentations (ρ : Representation K G V) :
    Representation.IsIrreducible ρ ↔ Nontrivial V ∧
      ∀ U : Subrepresentation ρ, U = ⊥ ∨ U = ⊤ := by
  constructor
  · intro h
    have := h
    exact ⟨irreducible_nontrivial h, fun U => eq_bot_or_eq_top U⟩
  · rintro ⟨h, hU⟩
    have := h
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
    exact ⟨hU⟩

theorem irreducibility_characterization : IrreducibilityCharacterization.{u,v,w} := by
  intro K G V _ _ _ _ ρ
  rw [irreducibleValue, irreducible_iff_subrepresentations]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun U hU => ?_⟩
    exact (h ⟨U, fun g _ hx => hU g _ hx⟩).imp
      (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun U => ?_⟩
    rcases h U.toSubmodule (fun g _ hx => U.apply_mem_toSubmodule g hx) with he | he
    · left
      apply Subrepresentation.toSubmodule_injective
      exact he
    · right
      apply Subrepresentation.toSubmodule_injective
      exact he

theorem semisimplicity_characterization : SemisimplicityCharacterization.{u,v,w} := by
  intro K G V _ _ _ _ ρ
  constructor
  · intro h U hU
    obtain ⟨W, hW⟩ := h ⟨U, fun g _ hx => hU g _ hx⟩
    exact ⟨W.toSubmodule, fun g _ hx => W.apply_mem_toSubmodule g hx, hW⟩
  · intro h U
    obtain ⟨W, hi, hc⟩ := h U.toSubmodule (fun g _ hx => U.apply_mem_toSubmodule g hx)
    exact ⟨⟨W, fun g _ hx => hi g _ hx⟩, hc⟩

theorem zero_space : ZeroSpace.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ
  refine ⟨(IrreducibleDefinitionFiniteSemisimpleDecomposition.zero_space K G V ρ).1, ?_⟩
  intro h
  have := irreducible_nontrivial h
  exact not_nontrivial V inferInstance

theorem irreducible_indecomposable : IrreducibleIndecomposable.{u,v,w} := by
  intro K G V _ _ _ _ ρ h
  obtain ⟨hne, hU⟩ := (irreducible_iff_subrepresentations ρ).mp h
  refine ⟨hne, fun U W hc => ?_⟩
  rcases hU U with h0 | htop
  · exact Or.inl h0
  · right
    apply Subrepresentation.toSubmodule_injective
    change W.toSubmodule = ⊥
    have ht : U.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule htop
    have := hc.inf_eq_bot
    simpa [ht] using this

theorem reducibility_criterion : ReducibilityCriterion.{u,v,w} := by
  classical
  intro K G V _ _ _ _ _ ρ
  rw [irreducibleValue, irreducible_iff_subrepresentations]
  simp only [true_and, show Nontrivial V from inferInstance]
  push Not
  rfl

theorem indecomposable_semisimple : IndecomposableSemisimple.{u,v,w} := by
  intro K G V _ _ _ _ ρ
  constructor
  · intro h
    refine ⟨irreducible_indecomposable K G V ρ h, fun U => ?_⟩
    rcases (irreducible_iff_subrepresentations ρ).mp h |>.2 U with he | he
    · exact ⟨⊤, he ▸ isCompl_bot_top⟩
    · exact ⟨⊥, he ▸ isCompl_top_bot⟩
  · rintro ⟨hi, hs⟩
    apply (irreducible_iff_subrepresentations ρ).mpr
    refine ⟨hi.1, fun U => ?_⟩
    obtain ⟨W, hW⟩ := hs U
    rcases hi.2 U W hW with he | he
    · exact Or.inl he
    · right
      apply Subrepresentation.toSubmodule_injective
      change U.toSubmodule = ⊤
      have h0 : W.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule he
      simpa [h0] using hW.sup_eq_top

theorem unique_proper_invariant_subspace : UniqueProperInvariantSubspace.{u,v,w} := by
  classical
  intro K G V _ _ _ _ ρ U hU0 hUt hunique
  have hU : U.toSubmodule ≠ ⊥ := fun h => hU0 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨p, _, hp⟩ := U.toSubmodule.ne_bot_iff.mp hU
  have hn : Nontrivial V := ⟨⟨p, 0, hp⟩⟩
  refine ⟨⟨hn, fun A B hAB => ?_⟩, ?_⟩
  · by_cases hA0 : A = ⊥
    · exact Or.inl hA0
    by_cases hB0 : B = ⊥
    · exact Or.inr hB0
    have hAt : A ≠ ⊤ := by
      intro he
      apply hB0
      apply Subrepresentation.toSubmodule_injective
      change B.toSubmodule = ⊥
      have ht : A.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule he
      simpa [ht] using hAB.inf_eq_bot
    have hBt : B ≠ ⊤ := by
      intro he
      apply hA0
      apply Subrepresentation.toSubmodule_injective
      change A.toSubmodule = ⊥
      have ht : B.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule he
      simpa [ht] using hAB.inf_eq_bot
    have hAU := hunique A hA0 hAt
    have hBU := hunique B hB0 hBt
    have he : U.toSubmodule = ⊥ := by simpa [hAU, hBU] using hAB.inf_eq_bot
    exact (hU he).elim
  · intro h
    rcases (irreducible_iff_subrepresentations ρ).mp h |>.2 U with he | he
    · exact hU0 he
    · exact hUt he

theorem finite_semisimple_decomposition : FiniteSemisimpleDecomposition.{u,v,w} :=
  IrreducibleDefinitionFiniteSemisimpleDecomposition.finite_semisimple_decomposition

lemma rotation_generator (K : Type*) [Field K] :
    rotation K (Multiplicative.ofAdd (1 : ZMod 4)) = quarterTurn K := by
  change quarterTurn K ^ (1 : ZMod 4).val = quarterTurn K
  rw [ZMod.val_one_eq_one_mod]
  norm_num

lemma quarterTurn_square (K : Type*) [Field K] : quarterTurn K ^ 2 = -1 := by
  apply LinearMap.ext
  intro p
  apply Prod.ext <;> simp [pow_two, Module.End.mul_apply, quarterTurn]

theorem rotation_laws : RotationLaws := by
  intro K _
  exact ⟨rotation_generator K, fun _ => rfl, quarterTurn_square K, quarterTurn_four K⟩

/-- A nonzero vector and its quarter turn span the real plane. -/
lemma real_invariant_eq_top (U : Submodule ℝ (ℝ × ℝ))
    (hi : Specs.D07.Ch17.DirectSums.Invariant (rotation ℝ) U)
    {p : ℝ × ℝ} (hp : p ∈ U) (hp0 : p ≠ 0) : U = ⊤ := by
  have hj : quarterTurn ℝ p ∈ U := by
    rw [← rotation_generator ℝ]
    exact hi _ p hp
  have hd : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by
    intro h
    have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.2]
    have h2 : p.2 = 0 := by nlinarith [sq_nonneg p.1]
    exact hp0 (Prod.ext h1 h2)
  apply top_unique
  intro q _
  have heq : q = ((p.1 * q.1 + p.2 * q.2) / (p.1^2 + p.2^2)) • p +
      ((p.1 * q.2 - p.2 * q.1) / (p.1^2 + p.2^2)) • quarterTurn ℝ p := by
    apply Prod.ext <;> dsimp [quarterTurn] <;> field_simp <;> ring
  rw [heq]
  exact U.add_mem (U.smul_mem _ hp) (U.smul_mem _ hj)

theorem real_rotation_irreducible : RealRotationIrreducible := by
  apply (irreducibility_characterization ℝ C4 (ℝ × ℝ) (rotation ℝ)).mpr
  refine ⟨inferInstance, fun U hi => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · obtain ⟨p, hp, hp0⟩ := U.ne_bot_iff.mp hU
    exact Or.inr (real_invariant_eq_top U hi hp hp0)

lemma real_eigenvector_zero (a : ℝ) (p : ℝ × ℝ)
    (hp : quarterTurn ℝ p = a • p) : p = 0 := by
  have hj2 : (-1 : ℝ) • p = (a * a) • p := by
    calc
      (-1 : ℝ) • p = quarterTurn ℝ (quarterTurn ℝ p) := by
        apply Prod.ext <;> simp [quarterTurn]
      _ = a • (a • p) := by rw [hp, map_smul, hp]
      _ = (a * a) • p := (mul_smul a a p).symm
  have he : (a * a + 1) • p = 0 := by
    rw [add_smul, one_smul, ← hj2]
    simp
  exact (smul_eq_zero.mp he).resolve_left (by nlinarith [sq_nonneg a])

theorem real_rotation_no_line : RealRotationNoLine := by
  refine ⟨real_eigenvector_zero, fun U hdim hi => ?_⟩
  rcases ((irreducibility_characterization ℝ C4 (ℝ × ℝ) _).mp
    real_rotation_irreducible).2 U hi with h | h
  · subst U
    simp at hdim
  · subst U
    have hd : Module.finrank ℝ (⊤ : Submodule ℝ (ℝ × ℝ)) = 2 := by
      simp [Module.finrank_prod]
    omega

lemma rotation_invariant_span_of_eigen {K : Type*} [Field K]
    (v : K × K) (a : K) (hv : quarterTurn K v = a • v) :
    Specs.D07.Ch17.DirectSums.Invariant (rotation K) (Submodule.span K {v}) := by
  have stable : ∀ p ∈ Submodule.span K {v}, quarterTurn K p ∈ Submodule.span K {v} := by
    intro p hp
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
    rw [map_smul, hv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  intro g p hp
  change (quarterTurn K ^ g.toAdd.val) p ∈ _
  generalize g.toAdd.val = n
  induction n with
  | zero => simpa using hp
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply]
    exact stable _ hn

lemma complex_plus_eigen : quarterTurn ℂ (1, -Complex.I) = Complex.I • (1, -Complex.I) := by
  apply Prod.ext <;> simp [quarterTurn, Complex.I_mul_I]

lemma complex_minus_eigen : quarterTurn ℂ (1, Complex.I) = -Complex.I • (1, Complex.I) := by
  apply Prod.ext <;> simp [quarterTurn, Complex.I_mul_I]

lemma eigenlines_compl : IsCompl plusLine minusLine := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro p hp hq
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hp
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hq
    have hab := ha.trans hb.symm
    have h1 : a = b := by simpa using congrArg Prod.fst hab
    have h2 : a * -Complex.I = b * Complex.I := by
      simpa using congrArg Prod.snd hab
    have ha0 : a = 0 := by
      rw [← h1] at h2
      have hz : a * Complex.I = 0 := by linear_combination - (1 / 2 : ℂ) * h2
      exact (mul_eq_zero.mp hz).resolve_right Complex.I_ne_zero
    rw [← ha, ha0, zero_smul]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro p _
    apply Submodule.mem_sup.mpr
    refine ⟨((p.1 + Complex.I * p.2) / 2) • (1, -Complex.I),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      ((p.1 - Complex.I * p.2) / 2) • (1, Complex.I),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    apply Prod.ext
    · dsimp
      ring
    · dsimp
      linear_combination (-p.2) * Complex.I_mul_I

theorem complex_rotation_splitting : ComplexRotationSplitting := by
  have hiP := rotation_invariant_span_of_eigen _ _ complex_plus_eigen
  have hiM := rotation_invariant_span_of_eigen _ _ complex_minus_eigen
  refine ⟨complex_plus_eigen, complex_minus_eigen, hiP, hiM,
    finrank_span_singleton (by intro h; have := congrArg Prod.fst h; simp at this),
    finrank_span_singleton (by intro h; have := congrArg Prod.fst h; simp at this),
    eigenlines_compl, ?_⟩
  intro h
  rcases ((irreducibility_characterization ℂ C4 (ℂ × ℂ) _).mp h).2 plusLine hiP with h0 | ht
  · have hm : ((1 : ℂ), -Complex.I) ∈ plusLine := Submodule.mem_span_singleton_self _
    rw [h0] at hm
    have := congrArg Prod.fst ((Submodule.mem_bot ℂ).mp hm)
    simp at this
  · have hm : ((1 : ℂ), Complex.I) ∈ minusLine := Submodule.mem_span_singleton_self _
    have hz : ((1 : ℂ), Complex.I) = 0 :=
      Submodule.disjoint_def.mp eigenlines_compl.disjoint _ (ht ▸ Submodule.mem_top) hm
    have := congrArg Prod.fst hz
    simp at this

lemma rotation_complexifies (g : C4) (p : ℝ × ℝ) :
    rotation ℂ g ((p.1 : ℂ), (p.2 : ℂ)) =
      (((rotation ℝ g p).1 : ℂ), ((rotation ℝ g p).2 : ℂ)) := by
  change (quarterTurn ℂ ^ g.toAdd.val) ((p.1 : ℂ), (p.2 : ℂ)) =
    ((((quarterTurn ℝ ^ g.toAdd.val) p).1 : ℂ), (((quarterTurn ℝ ^ g.toAdd.val) p).2 : ℂ))
  generalize g.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hn]
    apply Prod.ext <;> simp [quarterTurn]

theorem scalar_extension : ScalarExtension := by
  refine ⟨rotation_complexifies, ?_, ?_⟩
  · intro g T hT
    apply LinearMap.prod_ext <;> apply LinearMap.ext_ring
    · simpa using (hT (1, 0)).trans (rotation_complexifies g (1, 0)).symm
    · simpa using (hT (0, 1)).trans (rotation_complexifies g (0, 1)).symm
  · apply top_unique
    intro p _
    have h1 : ((1 : ℂ), (0 : ℂ)) ∈ Submodule.span ℂ
        (Set.range (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ)))) :=
      Submodule.subset_span ⟨(1, 0), by simp⟩
    have h2 : ((0 : ℂ), (1 : ℂ)) ∈ Submodule.span ℂ
        (Set.range (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ)))) :=
      Submodule.subset_span ⟨(0, 1), by simp⟩
    have hp : p = p.1 • ((1 : ℂ), (0 : ℂ)) + p.2 • ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
    rw [hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

end
end D07.Ch17.IrreducibleDefinition
