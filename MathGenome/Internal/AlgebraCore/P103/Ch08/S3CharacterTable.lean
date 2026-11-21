import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.S3CharacterTable
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions
import MathGenome.Internal.AlgebraCore.P103.Ch08.UnitarityPairing
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

noncomputable section
universe u
namespace P103.Ch08.S3CharacterTable
open S3CharacterTableSpecs
open scoped MonoidAlgebra

/-- The trivial line, sign line, coordinate action, and its zero-sum plane. -/
def trivialRepresentation : trivialRepresentationType := trivialValue

def signRepresentation : signRepresentationType := signValue

def permutationRepresentation : permutationRepresentationType := permutationValue

def standardRepresentation : standardRepresentationType := standardValue

theorem class_data : classDataType := by
  unfold classDataType
  simp_rw [Equiv.Perm.isConj_iff_cycleType_eq]
  norm_num [Nat.card_eq_fintype_card]
  decide

/-- Trace in the coordinate basis is the number of fixed coordinates. -/
theorem fixed_point_trace (g : S3) : CharacterSpecs.characterValue permutationValue g =
    (Fintype.card {i : Fin 3 // g i = i} : ℂ) := by
  classical
  rw [CharacterSpecs.characterValue, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 3))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    permutationValue, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Pi.single_apply]
  have hi (i : Fin 3) : g⁻¹ i = i ↔ g i = i := by
    constructor
    · intro h
      have := congrArg g h
      simpa using this.symm
    · intro h
      apply g.injective
      simpa using h.symm
  simp_rw [hi]
  simp [Fintype.card_subtype]

private def mean (x : Coordinates) : ℂ := (∑ i, x i) / 3

private def splitEquiv : (ℂ × Plane) ≃ₗ[ℂ] Coordinates where
  toFun z i := z.1 + z.2.val i
  invFun x := (mean x, ⟨fun i => x i - mean x, by
    change ∑ i : Fin 3, (x i - mean x) = 0
    simp [Finset.sum_sub_distrib, mean]
    ring⟩)
  left_inv z := by
    have hz := z.2.property
    change ∑ i, z.2.val i = 0 at hz
    have hm : mean (fun i => z.1 + z.2.val i) = z.1 := by
      simp [mean, Finset.sum_add_distrib, hz]
    apply Prod.ext
    · exact hm
    · apply Subtype.ext
      funext i
      change z.1 + z.2.val i - mean (fun i => z.1 + z.2.val i) = z.2.val i
      rw [hm]; ring
  right_inv x := by funext i; dsimp; ring
  map_add' z w := by funext i; dsimp; ring
  map_smul' c z := by funext i; dsimp; ring

private def splitRepresentationEquiv :
    (trivialValue.prod standardValue).Equiv permutationValue :=
  Representation.Equiv.mk splitEquiv (by
    intro g
    apply LinearMap.ext
    intro z
    funext i
    rfl)

theorem decomposition : decompositionType :=
  ⟨splitRepresentationEquiv, fun _ _ _ => rfl⟩

theorem dimensions : dimensionsType := by
  have h := splitEquiv.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
    Fintype.card_fin] at h
  unfold dimensionsType
  omega

private theorem trivial_character (g : S3) : CharacterSpecs.characterValue trivialValue g = 1 := by
  change LinearMap.trace ℂ ℂ 1 = 1
  simp

private theorem sign_character (g : S3) :
    CharacterSpecs.characterValue signValue g = ((Equiv.Perm.sign g : ℤ) : ℂ) := by
  simp [CharacterSpecs.characterValue, signValue, map_smul]

theorem trivial_row : trivialRowType :=
  ⟨trivial_character _, trivial_character _, trivial_character _⟩

theorem sign_row : signRowType := by
  simp [signRowType, sign_character, transposition, threeCycle]

private theorem standard_character (g : S3) :
    CharacterSpecs.characterValue standardValue g = CharacterSpecs.characterValue permutationValue g - 1 := by
  have h := congrFun (RegularMultiplicity.character_of_equiv splitRepresentationEquiv) g
  have hh := character_directSum trivialValue standardValue g
  change CharacterSpecs.characterValue (trivialValue.prod standardValue) g = _ at hh
  rw [hh, trivial_character] at h
  linear_combination h

theorem standard_row : standardRowType := by
  have he : Fintype.card {i : Fin 3 // (1 : S3) i = i} = 3 := by decide
  have ht : Fintype.card {i : Fin 3 // transposition i = i} = 1 := by decide
  have hc : Fintype.card {i : Fin 3 // threeCycle i = i} = 0 := by decide
  norm_num [standardRowType, standard_character, fixed_point_trace, he, ht, hc]

private theorem univ_permutations : (Finset.univ : Finset S3) =
    {1, transposition, Equiv.swap 0 2, Equiv.swap 1 2, threeCycle, threeCycle⁻¹} := by
  decide

private theorem group_order : Fintype.card S3 = 6 := by decide

private theorem sum_permutations (f : S3 → ℂ) :
    ∑ g, f g = f 1 + f transposition + f (Equiv.swap 0 2) + f (Equiv.swap 1 2) +
      f threeCycle + f threeCycle⁻¹ := by
  rw [univ_permutations]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ring

theorem norm : normType := by
  have he : Fintype.card {i : Fin 3 // (1 : S3) i = i} = 3 := by decide
  have ht : Fintype.card {i : Fin 3 // transposition i = i} = 1 := by decide
  have h02 : Fintype.card {i : Fin 3 // Equiv.swap 0 2 i = i} = 1 := by decide
  have h12 : Fintype.card {i : Fin 3 // Equiv.swap 1 2 i = i} = 1 := by decide
  have hc : Fintype.card {i : Fin 3 // threeCycle i = i} = 0 := by decide
  have hci : Fintype.card {i : Fin 3 // threeCycle⁻¹ i = i} = 0 := by decide
  unfold normType UnitaritySpecs.functionPairingValue
  rw [group_order, sum_permutations]
  norm_num [standard_character, fixed_point_trace, he, ht, h02, h12, hc, hci]

private theorem one_dimensional_irreducible (ρ : Representation ℂ S3 ℂ) :
    Irreducible ℂ S3 ℂ ρ := by
  refine ⟨inferInstance, fun U => ?_⟩
  rcases eq_bot_or_eq_top U.toSubmodule with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact h

/-- In a semisimple representation, norm one forces every invariant
projection to be scalar, hence every invariant subspace is zero or the whole space. -/
private theorem irreducible_of_norm_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ S3 V)
    (hn : UnitaritySpecs.functionPairingValue (CharacterSpecs.characterValue ρ)
      (CharacterSpecs.characterValue ρ) = 1) : Irreducible ℂ S3 V ρ := by
  classical
  have hd : Module.finrank ℂ (Module.End ℂ[S3] ρ.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq]
    exact_mod_cast (character_pairing ρ ρ).1.symm.trans hn
  have : Nontrivial ρ.asModule := ρ.asModuleEquiv.toEquiv.nontrivial
  have hsem := Maschke.semisimple ρ (by norm_num [Nat.card_eq_fintype_card, group_order])
  have hs : IsSimpleModule ℂ[S3] ρ.asModule := by
    rw [isSimpleModule_iff]
    refine ⟨fun U => ?_⟩
    by_cases hu : U = ⊥
    · exact Or.inl hu
    · right
      obtain ⟨W, hW⟩ := exists_isCompl U
      let p := U.projection W hW
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
        (1 : Module.End ℂ[S3] ρ.asModule) one_ne_zero).mp hd p
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hu
      have hcv : c • v = v := by
        have hh := LinearMap.congr_fun hc v
        simpa [p, Submodule.projection_apply_of_mem_left hW hv] using hh
      have hc1 : c = 1 := by
        apply (smul_left_injective ℂ hv0)
        simpa using hcv
      have hp : p = 1 := by simpa [hc1] using hc.symm
      rw [← Submodule.range_projection hW]
      change LinearMap.range p = ⊤
      rw [hp]
      exact LinearMap.range_id
  have hr : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hs
  exact ⟨inferInstance, fun U => eq_bot_or_eq_top U⟩

theorem irreducibility : irreducibilityType := by
  have hd : Module.finrank ℂ Plane = 2 := dimensions
  have : Nontrivial Plane := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  exact ⟨one_dimensional_irreducible trivialValue, one_dimensional_irreducible signValue,
    irreducible_of_norm_one standardValue (norm.1.trans norm.2)⟩

theorem distinct : distinctType := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have h := congrFun (RegularMultiplicity.character_of_equiv e) transposition
    have ht := trivial_row.2.1
    have hs := sign_row.2.1
    rw [ht, hs] at h
    norm_num at h
  · rintro ⟨e⟩
    have h := e.toLinearEquiv.finrank_eq
    have hd : Module.finrank ℂ Plane = 2 := dimensions
    norm_num at h
    omega
  · rintro ⟨e⟩
    have h := e.toLinearEquiv.finrank_eq
    have hd : Module.finrank ℂ Plane = 2 := dimensions
    norm_num at h
    omega

theorem square_sum : squareSumType := by
  change (Module.finrank ℂ ℂ)^2 + (Module.finrank ℂ ℂ)^2 +
    (Module.finrank ℂ Plane)^2 = Fintype.card S3
  rw [show Module.finrank ℂ Plane = 2 from dimensions, group_order]
  norm_num

/-- The three known types use all six dimensions in the regular
representation. Every further simple type would contribute a positive square. -/
theorem exhaustive : exhaustiveType.{u} := by
  intro V _ _ ρ hρ
  classical
  obtain ⟨C, hC, hEx⟩ := RegularMultiplicity.finite_family.{0,0} (G := S3)
  obtain ⟨a, ⟨ea⟩⟩ := hEx trivialValue irreducibility.1
  obtain ⟨b, ⟨eb⟩⟩ := hEx signValue irreducibility.2.1
  obtain ⟨c, ⟨ec⟩⟩ := hEx standardValue irreducibility.2.2
  have hab : a ≠ b := by
    intro h; subst b
    exact distinct.1 ⟨ea.symm.trans eb⟩
  have hac : a ≠ c := by
    intro h; subst c
    exact distinct.2.1 ⟨ea.symm.trans ec⟩
  have hbc : b ≠ c := by
    intro h; subst c
    exact distinct.2.2 ⟨eb.symm.trans ec⟩
  have ha : Module.finrank ℂ (C.space a) = 1 := by
    simpa using ea.toLinearEquiv.finrank_eq
  have hb : Module.finrank ℂ (C.space b) = 1 := by
    simpa using eb.toLinearEquiv.finrank_eq
  have hc : Module.finrank ℂ (C.space c) = 2 :=
    ec.toLinearEquiv.finrank_eq.trans dimensions
  have hsum : ∑ j : Fin C.n, (Module.finrank ℂ (C.space j)) ^ 2 = 6 := by
    exact (RegularMultiplicity.regular_decomposition C hC hEx).2.symm.trans group_order
  have hall (j : Fin C.n) : j = a ∨ j = b ∨ j = c := by
    by_contra hj
    have hjt : j ∉ ({a, b, c} : Finset (Fin C.n)) := by simpa using hj
    have ht : ∑ i ∈ ({a, b, c} : Finset (Fin C.n)),
        (Module.finrank ℂ (C.space i)) ^ 2 = 6 := by
      simp [hab, hac, hbc, ha, hb, hc]
    have hle : (Module.finrank ℂ (C.space j)) ^ 2 + 6 ≤ 6 := by
      calc
        _ = ∑ i ∈ insert j ({a, b, c} : Finset (Fin C.n)),
            (Module.finrank ℂ (C.space i)) ^ 2 := by rw [Finset.sum_insert hjt, ht]
        _ ≤ ∑ i : Fin C.n, (Module.finrank ℂ (C.space i)) ^ 2 :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = 6 := hsum
    have : IsSimpleModule ℂ[S3] (C.space j) := hC.1 j
    have : Nontrivial (C.space j) := IsSimpleModule.nontrivial ℂ[S3] (C.space j)
    have hp : 0 < Module.finrank ℂ (C.space j) := Module.finrank_pos
    nlinarith
  obtain ⟨j, ⟨ej⟩⟩ := (RegularMultiplicity.exhaustive_from_regular C hEx) ρ hρ
  rcases hall j with rfl | rfl | rfl
  · exact Or.inl ⟨ea.symm.trans ej⟩
  · exact Or.inr (Or.inl ⟨eb.symm.trans ej⟩)
  · exact Or.inr (Or.inr ⟨ec.symm.trans ej⟩)

end P103.Ch08.S3CharacterTable
