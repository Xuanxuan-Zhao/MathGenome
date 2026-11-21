import MathGenome.Internal.D07.Ch02.ConjugacyCycleType
import MathGenome.Internal.D07.Ch17.CharacterDirectSum
import MathGenome.Internal.D07.Ch21.MultiplicityClassification
import MathGenome.Internal.Specs.D07.Ch21.S3Table
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace D07.Ch21.S3Table
noncomputable section
open Specs.D07.Ch21.S3Table
open scoped BigOperators

lemma plane_invariant (g : S3) (v : V3) (hv : v ∈ plane) :
    permRep g v ∈ plane := by
  change ∑ i, v (g⁻¹ i) = 0
  change ∑ i, v i = 0 at hv
  rw [Equiv.sum_comp g⁻¹ v]
  exact hv

def standard : Representation ℂ S3 plane :=
  (Subrepresentation.mk plane plane_invariant).toRepresentation

lemma standard_apply (g : S3) (v : plane) (i : Fin 3) :
    (standard g v : V3) i = (v : V3) (g⁻¹ i) := rfl

/-- Coordinates in the ordered basis e₁−e₃, e₂−e₃. -/
def planeCoordinates : plane ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![(v : V3) 0, (v : V3) 1]
  invFun z := ⟨![z 0, z 1, -z 0 - z 1], by
    change ∑ i : Fin 3, (![z 0, z 1, -z 0 - z 1] : V3) i = 0
    simp [Fin.sum_univ_succ]⟩
  left_inv v := by
    apply Subtype.ext
    have hv : (v : V3) 0 + (v : V3) 1 + (v : V3) 2 = 0 := by
      simpa [plane, coordinateSum, Fin.sum_univ_succ, add_assoc] using v.property
    ext i
    fin_cases i <;> simp
    linear_combination -hv
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> simp

def planeBasis : Module.Basis (Fin 2) ℂ plane :=
  (Pi.basisFun ℂ (Fin 2)).map planeCoordinates.symm

lemma planeBasis_zero : (planeBasis 0 : V3) = ![1, 0, -1] := by
  ext i; fin_cases i <;> simp [planeBasis, planeCoordinates, Pi.basisFun_apply]

lemma planeBasis_one : (planeBasis 1 : V3) = ![0, 1, -1] := by
  ext i; fin_cases i <;> simp [planeBasis, planeCoordinates, Pi.basisFun_apply]

lemma plane_dimension : Module.finrank ℂ plane = 2 := by
  exact (Module.finrank_eq_card_basis planeBasis).trans (Fintype.card_fin 2)

lemma matrix_s : LinearMap.toMatrix planeBasis planeBasis (standard s) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, planeBasis, Module.Basis.map_repr,
      planeCoordinates, standard, Subrepresentation.toRepresentation,
      permRep, s, Pi.basisFun_repr]

lemma matrix_a : LinearMap.toMatrix planeBasis planeBasis (standard a) = !![-1, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, planeBasis, Module.Basis.map_repr,
      planeCoordinates, standard, Subrepresentation.toRepresentation,
      permRep, a, Pi.basisFun_repr, Equiv.Perm.mul_def, Equiv.swap_apply_def]

lemma line_iff (v : V3) : v ∈ line ↔ ∃ c : ℂ, v = fun _ => c := by
  rw [line, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ext; simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ext; simp⟩

lemma mean_mem (v : V3) : (fun _ : Fin 3 => coordinateSum v / 3) ∈ line :=
  (line_iff _).mpr ⟨_, rfl⟩

lemma centered_mem (v : V3) : (v - fun _ : Fin 3 => coordinateSum v / 3) ∈ plane := by
  change ∑ i : Fin 3, (v i - coordinateSum v / 3) = 0
  simp [Finset.sum_sub_distrib, coordinateSum]
  ring

lemma line_fixed (g : S3) (v : V3) (hv : v ∈ line) : permRep g v = v := by
  obtain ⟨c, rfl⟩ := (line_iff v).mp hv
  rfl

lemma complement : IsCompl line plane := by
  apply isCompl_iff.mpr
  constructor
  · apply Submodule.disjoint_def.mpr
    intro v hvL hvW
    obtain ⟨c, rfl⟩ := (line_iff v).mp hvL
    have hc : (3 : ℂ) * c = 0 := by
      have hh : c + (c + c) = 0 := by
        simpa [plane, coordinateSum, Fin.sum_univ_succ] using hvW
      linear_combination hh
    have hz : c = 0 := (mul_eq_zero.mp hc).resolve_left (by norm_num)
    ext i
    simp [hz]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    exact Submodule.mem_sup.mpr ⟨_, mean_mem v, _, centered_mem v, add_sub_cancel _ _⟩

lemma group_card : Fintype.card S3 = 6 := by decide +kernel

lemma group_elements : (Finset.univ : Finset S3) =
    {1, s, Equiv.swap 0 2, Equiv.swap 1 2, a, a⁻¹} := by decide +kernel

lemma conjugacy (g h : S3) : IsConj g h ↔ g.cycleType = h.cycleType :=
  Equiv.Perm.isConj_iff_cycleType_eq

lemma classes : Classes := by
  refine ⟨group_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp_rw [conjugacy]
    decide +kernel
  · rw [conjugacy]; decide +kernel
  · rw [conjugacy]; decide +kernel
  · rw [conjugacy]; decide +kernel
  · have he : {g : S3 // IsConj g 1} ≃ {g : S3 // g.cycleType = (1 : S3).cycleType} :=
      Equiv.subtypeEquivRight (fun g => conjugacy g 1)
    rw [Nat.card_congr he, Nat.card_eq_fintype_card]
    decide +kernel
  · have he : {g : S3 // IsConj g s} ≃ {g : S3 // g.cycleType = s.cycleType} :=
      Equiv.subtypeEquivRight (fun g => conjugacy g s)
    rw [Nat.card_congr he, Nat.card_eq_fintype_card]
    decide +kernel
  · have he : {g : S3 // IsConj g a} ≃ {g : S3 // g.cycleType = a.cycleType} :=
      Equiv.subtypeEquivRight (fun g => conjugacy g a)
    rw [Nat.card_congr he, Nat.card_eq_fintype_card]
    decide +kernel

lemma permutation_character (g : S3) :
    χ permRep g = (Nat.card {i : Fin 3 // g i = i} : ℂ) := by
  classical
  change LinearMap.trace ℂ V3 (permRep g) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 3))]
  have hd (i : Fin 3) :
      LinearMap.toMatrix (Pi.basisFun ℂ (Fin 3)) (Pi.basisFun ℂ (Fin 3))
        (permRep g) i i = if g i = i then 1 else 0 := by
    rw [LinearMap.toMatrix_apply]
    by_cases h : g i = i
    · have hi : (Equiv.symm g) i = i := by
        calc
          (Equiv.symm g) i = (Equiv.symm g) (g i) := congrArg g.symm h.symm
          _ = i := g.symm_apply_apply i
      simp [permRep, Pi.basisFun_apply, hi, h]
    · have hi : (Equiv.symm g) i ≠ i := by
        intro hi
        apply h
        calc
          g i = g (g⁻¹ i) := congrArg g hi.symm
          _ = i := g.apply_symm_apply i
      simp [permRep, Pi.basisFun_apply, Pi.single_apply, hi, h]
  simp only [Matrix.trace, Matrix.diag_apply, hd]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma permutation_values : χ permRep 1 = 3 ∧ χ permRep s = 1 ∧ χ permRep a = 0 := by
  have hs : Fintype.card {i : Fin 3 // s i = i} = 1 := by decide +kernel
  have ha : Fintype.card {i : Fin 3 // a i = i} = 0 := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · rw [permutation_character]
    simp [Nat.card_eq_fintype_card]
  · rw [permutation_character, Nat.card_eq_fintype_card, hs]
    norm_num
  · rw [permutation_character, Nat.card_eq_fintype_card, ha]
    norm_num

lemma geometry : Geometry := by
  refine ⟨plane_invariant, line_fixed, complement, ?_, permutation_character, permutation_values⟩
  intro v
  exact ⟨mean_mem v, centered_mem v, Submodule.existsUnique_add_of_isCompl_prod complement v⟩

lemma trivial_character (g : S3) : χ triv g = 1 := by
  change LinearMap.trace ℂ ℂ 1 = 1
  simp [LinearMap.trace_one]

lemma sign_character (g : S3) : χ sign g = ((Specs.D07.Ch02.TranspositionsParity.signValue (Fin 3) g : ℤˣ) : ℤ) := by
  have h : sign g = (((Specs.D07.Ch02.TranspositionsParity.signValue (Fin 3) g : ℤˣ) : ℤ) : ℂ) • (1 : Module.End ℂ ℂ) := by
    apply LinearMap.ext
    intro z
    change Specs.D07.Ch17.Examples.signValue ℂ (Fin 3) g z = _
    rw [D07.Ch17.Examples.sign_action]
    simp
  change LinearMap.trace ℂ ℂ (sign g) = _
  rw [h, map_smul, LinearMap.trace_one]
  simp

lemma sign_values : χ sign 1 = 1 ∧ χ sign s = -1 ∧ χ sign a = 1 := by
  have hswap (x y : Fin 3) :
      @Equiv.swap (Fin 3) (fun a b => Classical.propDecidable (a = b)) x y =
        Equiv.swap x y := by
    ext i
    simp only [Equiv.swap_apply_def]
    split_ifs <;> rfl
  have h01 : Specs.D07.Ch02.TranspositionsParity.signValue (Fin 3) (Equiv.swap 0 1) = -1 :=
    by simpa only [hswap] using
      D07.Ch02.TranspositionsParity.transposition_sign (Fin 3) 0 1 (by decide)
  have h12 : Specs.D07.Ch02.TranspositionsParity.signValue (Fin 3) (Equiv.swap 1 2) = -1 :=
    by simpa only [hswap] using
      D07.Ch02.TranspositionsParity.transposition_sign (Fin 3) 1 2 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [sign_character, map_one]
    norm_num
  · rw [sign_character, h01]
    norm_num
  · rw [sign_character, map_mul, h01, h12]
    norm_num

lemma standard_values : χ standard 1 = 2 ∧ χ standard s = 0 ∧ χ standard a = -1 := by
  constructor
  · change LinearMap.trace ℂ plane (standard 1) = 2
    rw [map_one, LinearMap.trace_one, plane_dimension]
    norm_num
  constructor
  · change LinearMap.trace ℂ plane (standard s) = 0
    rw [LinearMap.trace_eq_matrix_trace ℂ planeBasis, matrix_s]
    norm_num [Matrix.trace, Fin.sum_univ_succ]
  · change LinearMap.trace ℂ plane (standard a) = -1
    rw [LinearMap.trace_eq_matrix_trace ℂ planeBasis, matrix_a]
    norm_num [Matrix.trace, Fin.sum_univ_succ]

lemma character_class {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ S3 V) {g h : S3}
    (hgh : IsConj g h) : χ τ g = χ τ h := by
  obtain ⟨b, rfl⟩ := isConj_iff.mp hgh
  exact (D07.Ch17.Characters.character_conjugate ℂ S3 V τ g b).symm

lemma class_sum (f : S3 → ℂ) (hf : ∀ {g h}, IsConj g h → f g = f h) :
    ∑ g, f g = f 1 + 3 * f s + 2 * f a := by
  have h02 : IsConj (Equiv.swap (0 : Fin 3) 2) s := by rw [conjugacy]; decide +kernel
  have h12 : IsConj (Equiv.swap (1 : Fin 3) 2) s := by rw [conjugacy]; decide +kernel
  have hai : IsConj a⁻¹ a := by rw [conjugacy]; decide +kernel
  rw [group_elements]
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  rw [hf h02, hf h12, hf hai]
  ring

lemma pairing_formula {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (τ : Representation ℂ S3 V) (σ : Representation ℂ S3 W) :
    Specs.D07.Ch21.HomPairing.pairingValue S3 (χ τ) (χ σ) =
      (χ τ 1 * starRingEnd ℂ (χ σ 1) +
        3 * (χ τ s * starRingEnd ℂ (χ σ s)) +
        2 * (χ τ a * starRingEnd ℂ (χ σ a))) / 6 := by
  unfold Specs.D07.Ch21.HomPairing.pairingValue
  rw [class_sum _ (fun h => by rw [character_class τ h, character_class σ h]), group_card]
  ring

lemma norm_criterion {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ S3 V) :
    Representation.IsIrreducible τ ↔
    Specs.D07.Ch21.HomPairing.pairingValue S3 (χ τ) (χ τ) = 1 := by
  classical
  obtain ⟨q, _, hi, hne, hc, _⟩ := RegularDecomposition.regular_theorem.{0,0} S3
  let α (i : q) := i.val.toRepresentation
  have hα (i : q) : Representation.IsIrreducible (α i) := hi i.val i.property
  have hneq (i j : q) (hij : i ≠ j) : ¬ Nonempty ((α i).Equiv (α j)) :=
    hne i.property j.property (fun h => hij (Subtype.ext h))
  haveI (i : q) : FiniteDimensional ℂ i.val.toSubmodule :=
    (RegularDecomposition.irreducible_finite S3 _ (α i) (hα i)).1
  exact MultiplicityClassification.irreducible_iff_norm_one α hα hneq hc τ

lemma standard_norm :
    Specs.D07.Ch21.HomPairing.pairingValue S3 (χ standard) (χ standard) = 1 := by
  rw [pairing_formula, standard_values.1, standard_values.2.1, standard_values.2.2]
  simp only [map_ofNat, map_neg, map_one, map_zero]
  norm_num

lemma irreducibles : Representation.IsIrreducible triv ∧
    Representation.IsIrreducible sign ∧ Representation.IsIrreducible standard := by
  refine ⟨(norm_criterion triv).mpr ?_, (norm_criterion sign).mpr ?_,
    (norm_criterion standard).mpr standard_norm⟩
  · rw [pairing_formula, trivial_character, trivial_character, trivial_character]
    norm_num
  · rw [pairing_formula, sign_values.1, sign_values.2.1, sign_values.2.2]
    norm_num

lemma pairwise_inequivalent : ¬ Nonempty (triv.Equiv sign) ∧
    ¬ Nonempty (triv.Equiv standard) ∧ ¬ Nonempty (sign.Equiv standard) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have h := congrFun (D07.Ch17.Characters.character_equivalence ℂ S3 ℂ ℂ triv sign he) s
    change χ triv s = χ sign s at h
    rw [trivial_character, sign_values.2.1] at h
    norm_num at h
  · intro he
    have h := congrFun (D07.Ch17.Characters.character_equivalence ℂ S3 ℂ plane triv standard he) 1
    change χ triv 1 = χ standard 1 at h
    rw [trivial_character, standard_values.1] at h
    norm_num at h
  · intro he
    have h := congrFun (D07.Ch17.Characters.character_equivalence ℂ S3 ℂ plane sign standard he) 1
    change χ sign 1 = χ standard 1 at h
    rw [sign_values.1, standard_values.1] at h
    norm_num at h

/-- Exhaustiveness does not assume finite dimension of the representation
being classified. Orthogonality against the three rows leaves zero as the
only possible character for a putative fourth irreducible. -/
lemma complete (V : Type*) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ S3 V) (hτ : Representation.IsIrreducible τ) :
    FiniteDimensional ℂ V ∧ (Nonempty (triv.Equiv τ) ∨
      Nonempty (sign.Equiv τ) ∨ Nonempty (standard.Equiv τ)) := by
  haveI hfd : FiniteDimensional ℂ V := (RegularDecomposition.irreducible_finite S3 V τ hτ).1
  refine ⟨hfd, ?_⟩
  classical
  by_contra! hn
  have ht := MatrixOrthogonality.character_orthogonality S3 ℂ V triv τ irreducibles.1 hτ
  have hs := MatrixOrthogonality.character_orthogonality S3 ℂ V sign τ irreducibles.2.1 hτ
  have hw := MatrixOrthogonality.character_orthogonality S3 plane V standard τ irreducibles.2.2 hτ
  rw [ite_eq_right (fun ⟨e⟩ => hn.1.false e), pairing_formula, trivial_character, trivial_character, trivial_character] at ht
  rw [ite_eq_right (fun ⟨e⟩ => hn.2.1.false e), pairing_formula, sign_values.1, sign_values.2.1, sign_values.2.2] at hs
  rw [ite_eq_right (fun ⟨e⟩ => hn.2.2.false e), pairing_formula, standard_values.1, standard_values.2.1, standard_values.2.2] at hw
  have hz : starRingEnd ℂ (χ τ 1) = 0 := by
    linear_combination 1 * ht + 1 * hs + 2 * hw
  have hz' : χ τ 1 = 0 := (map_eq_zero (starRingEnd ℂ)).mp hz
  haveI : Nontrivial V := D07.Ch17.IrreducibleDefinition.irreducible_nontrivial hτ
  have hp : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hd : (Module.finrank ℂ V : ℂ) = 0 := by
    simpa [Specs.D07.Ch17.Characters.characterValue, map_one, LinearMap.trace_one] using hz'
  have hnz : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  exact hnz hd

lemma character_decomposition (g : S3) : χ permRep g = χ triv g + χ standard g := by
  rcases classes.2.1 g with h | h | h <;>
    rw [character_class permRep h, character_class triv h, character_class standard h] <;>
    simp [trivial_character, permutation_values.1, permutation_values.2.1,
      permutation_values.2.2, standard_values.1, standard_values.2.1, standard_values.2.2] <;> norm_num

/-- All parts of the example refer to the same plane, action, and basis. -/
theorem s3_table : CompleteTable := by
  refine ⟨classes, geometry, standard, planeBasis, standard_apply,
    planeBasis_zero, planeBasis_one, matrix_s, matrix_a, plane_dimension,
    ⟨trivial_character 1, trivial_character s, trivial_character a⟩,
    sign_values, standard_values, character_decomposition, standard_norm, irreducibles.1, irreducibles.2.1,
    irreducibles.2.2, pairwise_inequivalent.1, pairwise_inequivalent.2.1,
    pairwise_inequivalent.2.2, ?_, complete⟩
  rw [plane_dimension, group_card, Module.finrank_self]
  norm_num

end
end D07.Ch21.S3Table
