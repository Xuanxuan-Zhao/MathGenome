import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeModules
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DecompositionMatrix
import Mathlib.Tactic.LinearCombination
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeDecompositionThree

namespace RepTheorySurvey.Modular.SymmetricThree

/-- The ordered modular simple labels at three. -/
noncomputable abbrev modularFamilyThree := DecompositionThreeSpec.modularFamilyValue

private theorem one_regular_at_three : IsPRegular 3 (1 : Group) := by
  unfold IsPRegular
  rw [orderOf_one]
  decide

private theorem transposition_regular_at_three : IsPRegular 3 transposition := by
  unfold IsPRegular
  rw [representative_orders.2.1]
  decide

theorem regular_classes_three : DecompositionThreeSpec.regularClassesType := by
  intro g
  change IsPRegular 3 g ↔ IsConj g 1 ∨ IsConj g transposition
  constructor
  · intro hg
    rcases class_data.1 g with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have hc := (isPRegular_iff_of_isConj (p := 3) h).mp hg
      unfold IsPRegular at hc
      rw [representative_orders.2.2] at hc
      have hnot : ¬ Nat.Coprime 3 3 := by decide
      exact (hnot hc).elim
  · rintro (h | h)
    · exact (isPRegular_iff_of_isConj h).mpr one_regular_at_three
    · exact (isPRegular_iff_of_isConj h).mpr transposition_regular_at_three

private def regularIdentityThree : PRegular Group 3 := ⟨1, one_regular_at_three⟩

private def regularTranspositionThree : PRegular Group 3 :=
  ⟨transposition, transposition_regular_at_three⟩

private theorem regular_class_count_three : Nat.card (PRegularConjClasses Group 3) = 2 := by
  classical
  let c₁ := pRegularConjClass regularIdentityThree
  let cₜ := pRegularConjClass regularTranspositionThree
  have hd : c₁ ≠ cₜ := by
    intro h
    have he : ConjClasses.mk (1 : Group) = ConjClasses.mk transposition :=
      congrArg Subtype.val h
    obtain ⟨a, ha⟩ := ConjClasses.mk_eq_mk_iff_isConj.mp he
    have ho := SemiconjBy.orderOf_eq (a : Group) ha
    rw [representative_orders.1, representative_orders.2.1] at ho
    contradiction
  let f : Fin 2 → PRegularConjClasses Group 3 := ![c₁, cₜ]
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hd h).elim
      · exact (hd h.symm).elim
      · rfl
    · intro c
      obtain ⟨g, rfl⟩ := pRegularConjClass_surjective c
      rcases (regular_classes_three g.val).mp g.property with h | h
      · exact ⟨0, Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm)⟩
      · exact ⟨1, Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h.symm)⟩
  simpa using (Nat.card_congr (Equiv.ofBijective f hf)).symm

open private one_dimensional_irreducible from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeModules

set_option backward.isDefEq.respectTransparency false

private theorem trivial_sign_not_isomorphic (F : Type*) [Field F] [CharP F 3]
    (e : (trivial F).asModule ≃ₗ[MonoidAlgebra F Group] (sign F).asModule) : False := by
  let f := (Representation.IntertwiningMap.equivLinearMapAsModule
    (trivial F) (sign F)).symm e.toLinearMap
  have hf : Function.Bijective f := e.bijective
  have h := congrFun (Representation.char_iso (f.ofBijective hf)) transposition
  rw [trivial_character F transposition, sign_character F transposition,
    sign_representatives.1] at h
  have htwo : (2 : F) ≠ 0 := by
    intro hzero
    exact (by decide : ¬ 3 ∣ 2) ((CharP.cast_eq_zero_iff F 3 2).mp hzero)
  apply htwo
  have h' : (1 : F) = ((-1 : ℤ) : F) := h
  rw [Int.cast_neg, Int.cast_one] at h'
  linear_combination h'

theorem modular_simple_family_three
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K] :
    DecompositionThreeSpec.simpleFamilyType (O := O) (K := K) := by
  classical
  intro system
  let k := IsLocalRing.ResidueField O
  let : CharP k 3 := system.residueChar
  let S := modularFamilyThree k
  have simple (i : Fin 2) : IsSimpleModule (MonoidAlgebra k Group) (S i) := by
    fin_cases i
    · exact (Representation.irreducible_iff_isSimpleModule_asModule (trivial k)).mp
        (one_dimensional_irreducible k (trivial k))
    · exact (Representation.irreducible_iff_isSimpleModule_asModule (sign k)).mp
        (one_dimensional_irreducible k (sign k))
  have eq_of_iso {i j : Fin 2} (e : S i ≃ₗ[MonoidAlgebra k Group] S j) : i = j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact (trivial_sign_not_isomorphic k e).elim
    · exact (trivial_sign_not_isomorphic k e.symm).elim
    · rfl
  refine ⟨simple, fun ⟨e⟩ => eq_of_iso e, ?_⟩
  obtain ⟨n, d, hd, e, hC⟩ := modular_columns_exist system.modularSplit
  let C := columnModule (modularColumnMap e)
  have hn : Nat.card (Fin n) = 2 :=
    (card_simple_representatives system C hC).2.trans regular_class_count_three
  choose a ha using fun i => hC.exhaustive (S i) (simple i)
  let iso (i : Fin 2) := (ha i).some
  have ha_inj : Function.Injective a := by
    intro i j hij
    have h : Nonempty (C (a i) ≃ₗ[MonoidAlgebra k Group] C (a j)) := by
      rw [hij]
      exact ⟨LinearEquiv.refl _ _⟩
    exact eq_of_iso ((iso i).trans (h.some.trans (iso j).symm))
  have ha_surj : Function.Surjective a :=
    (ha_inj.bijective_of_nat_card_le (by simpa using hn.le)).surjective
  intro M hM
  obtain ⟨j, ⟨f⟩⟩ := hC.exhaustive M hM
  obtain ⟨i, rfl⟩ := ha_surj j
  exact ⟨i, ⟨f.trans (iso i).symm⟩⟩


open private modularGroundFinite from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeDecompositionThree

section BrauerValues

open IsLocalRing (ResidueField)
open Polynomial

open private charpoly_ofModule_asModule from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.CharacterReduction

private theorem charpoly_scalar_field {F : Type*} [Field F] (a : F) :
    (a • (1 : Module.End F F)).charpoly = X - C a := by
  have h := LinearMap.charpoly_sub_smul (0 : Module.End F F) (-a)
  rw [LinearMap.charpoly_zero, Module.finrank_self, pow_one, X_comp, map_neg,
    ← sub_eq_add_neg] at h
  have he : (0 : Module.End F F) - (-a) • 1 = a • 1 := by
    apply LinearMap.ext
    intro x
    simp [LinearMap.smul_apply]
  rwa [he] at h

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K]

local notation "k" => ResidueField O
local notation "m" => primeToPart Group 3

private theorem brauer_character_of_scalar (system : SplittingSystem Group 3 O K)
    (ρ : Representation k Group k)
    (g : PRegular Group 3) (z : O) (hz : z ^ m = 1)
    (hρ : ρ g.val = IsLocalRing.residue O z • 1) :
    letI : Module.Finite k (RestrictScalars k (MonoidAlgebra k Group) ρ.asModule) :=
      Module.Finite.equiv (MR04Spec.asModuleScalarEquiv ρ).symm
    brauerCharacter system ρ.asModule g = z := by
  let : Module.Finite k (RestrictScalars k (MonoidAlgebra k Group) ρ.asModule) :=
    Module.Finite.equiv (MR04Spec.asModuleScalarEquiv ρ).symm
  classical
  let : NeZero m := ⟨(primeToPart_pos Group 3).ne'⟩
  let zO := rootsOfUnity.mkOfPowEq z hz
  let zk := residualRootsEquiv system zO
  have hres : zk.val.val = IsLocalRing.residue O z := by
    change IsLocalRing.residue O (zO.val.val) = IsLocalRing.residue O z
    rw [rootsOfUnity.coe_mkOfPowEq]
  have hlift : (residualRootLift system zk).val.val = z := by
    change ((residualRootsEquiv system).symm (residualRootsEquiv system zO)).val.val = z
    rw [MulEquiv.symm_apply_apply, rootsOfUnity.coe_mkOfPowEq]
  have hpoly : (moduleRepresentation k Group ρ.asModule g.val).charpoly = X - C zk.val.val := by
    rw [charpoly_ofModule_asModule, hρ, charpoly_scalar_field, hres]
  unfold brauerCharacter
  rw [hpoly, Finset.sum_eq_single zk]
  · rw [rootMultiplicity_X_sub_C_self, one_nsmul, hlift]
  · intro ξ _ hξ
    have hne : ξ.val.val ≠ zk.val.val := fun h => hξ (rootsOfUnity.coe_injective h)
    rw [rootMultiplicity_X_sub_C, ite_eq_right hne, zero_nsmul]
  · simp

theorem modular_brauer_values_three :
    DecompositionThreeSpec.brauerValuesType (O := O) (K := K) := by
  intro system i g
  let := modularGroundFinite (ResidueField O) i
  change (IsConj g.val 1 → brauerCharacter system (modularFamilyThree k i) g = 1) ∧
    (IsConj g.val transposition →
      brauerCharacter system (modularFamilyThree k i) g = (![1, -1] : Fin 2 → O) i)
  have ht (x : PRegular Group 3) : trivial k x.val = IsLocalRing.residue O 1 • 1 := by
    simp [trivial, Spec.trivialValue, Representation.trivial, Module.End.one_eq_id]
  constructor
  · intro h
    rw [brauerCharacter_eq_of_isConj system (modularFamilyThree k i)
      (h := regularIdentityThree) h]
    fin_cases i
    · exact brauer_character_of_scalar system (trivial k) regularIdentityThree
        1 (one_pow _) (ht _)
    · apply brauer_character_of_scalar system (sign k) regularIdentityThree 1 (one_pow _)
      change sign k 1 = _
      rw [map_one, map_one, one_smul]
  · intro h
    rw [brauerCharacter_eq_of_isConj system (modularFamilyThree k i)
      (h := regularTranspositionThree) h]
    fin_cases i
    · exact brauer_character_of_scalar system (trivial k) regularTranspositionThree
        1 (one_pow _) (ht _)
    · have hm : 2 ∣ m := by
        have hh := orderOf_dvd_primeToPart system.prime regularTranspositionThree
        rwa [show orderOf regularTranspositionThree.val = 2 from representative_orders.2.1] at hh
      have hpow : (-1 : O) ^ m = 1 := by
        obtain ⟨n, hn⟩ := hm
        rw [hn, pow_mul]
        simp
      apply brauer_character_of_scalar system (sign k) regularTranspositionThree (-1) hpow
      change ((Equiv.Perm.sign transposition : ℤ) : k) • (1 : Module.End k k) =
        IsLocalRing.residue O (-1) • 1
      rw [sign_representatives.1]
      change ((-1 : ℤ) : k) • (1 : Module.End k k) = IsLocalRing.residue O (-1) • 1
      rw [Int.cast_neg, Int.cast_one, map_neg, map_one]

end BrauerValues

private theorem ordinary_character_of_representation {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [Module.Finite F V] (ρ : Representation F Group V)
    [Module.Finite F (RestrictScalars F (MonoidAlgebra F Group) ρ.asModule)] (g : Group) :
    ordinaryCharacter (K := F) ρ.asModule g = ρ.character g := by
  let e := MR04Spec.asModuleScalarEquiv ρ
  let T := moduleRepresentation F Group ρ.asModule g
  have h : e.conj T = ρ g := by
    ext x
    change e (T (e.symm x)) = ρ g x
    have hact (y) : T y = e.symm (ρ g (e y)) := Representation.ofModule_asModule_act ρ g y
    rw [hact, e.apply_symm_apply, e.apply_symm_apply]
  change LinearMap.trace F _ T = LinearMap.trace F V (ρ g)
  rw [← h, LinearMap.trace_conj']

private theorem ordinary_character_values_three (F : Type*) [Field F] (i : Fin 3)
    [Module.Finite F (RestrictScalars F (MonoidAlgebra F Group) (ordinaryFamily F i))] :
    ordinaryCharacter (K := F) (ordinaryFamily F i) (1 : Group) = (![1, 1, 2] : Fin 3 → F) i ∧
      ordinaryCharacter (K := F) (ordinaryFamily F i) transposition = (![1, -1, 0] : Fin 3 → F) i := by
  fin_cases i
  · let : Module.Finite F (RestrictScalars F (MonoidAlgebra F Group) (trivial F).asModule) :=
      Module.Finite.equiv (MR04Spec.asModuleScalarEquiv (trivial F)).symm
    exact ⟨(ordinary_character_of_representation (trivial F) 1).trans (trivial_character F 1),
      (ordinary_character_of_representation (trivial F) transposition).trans (trivial_character F _)⟩
  · let : Module.Finite F (RestrictScalars F (MonoidAlgebra F Group) (sign F).asModule) :=
      Module.Finite.equiv (MR04Spec.asModuleScalarEquiv (sign F)).symm
    constructor
    · change ordinaryCharacter (K := F) (sign F).asModule (1 : Group) = 1
      rw [ordinary_character_of_representation, sign_character, map_one, Units.val_one, Int.cast_one]
    · change ordinaryCharacter (K := F) (sign F).asModule transposition = -1
      rw [ordinary_character_of_representation, sign_character, sign_representatives.1]
      change ((-1 : ℤ) : F) = -1
      rw [Int.cast_neg, Int.cast_one]
  · let : Module.Finite F (RestrictScalars F (MonoidAlgebra F Group) (standard F).asModule) :=
      Module.Finite.equiv (MR04Spec.asModuleScalarEquiv (standard F)).symm
    exact ⟨(ordinary_character_of_representation (standard F) 1).trans (standard_character F).1,
      (ordinary_character_of_representation (standard F) transposition).trans
        (standard_character F).2.1⟩

theorem decomposition_matrix_three
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K] :
    DecompositionThreeSpec.decompositionMatrixType (O := O) (K := K) := by
  intro system
  let k := IsLocalRing.ResidueField O
  let : CharZero K := system.charZero
  let D := decompositionMatrix system (ordinaryFamily K) (modularFamilyThree k)
  let E : Matrix (Fin 3) (Fin 2) ℕ := !![1, 0; 0, 1; 1, 1]
  change D = E
  ext i j
  have hV := ordinary_simple_family system
  have hS := modular_simple_family_three system
  let := hV.simple i
  let : Module.Finite K (RestrictScalars K (MonoidAlgebra K Group) (ordinaryFamily K i)) :=
    CompositionMultiplicity.groundFinite_of_simple (F := K) (G := Group) (S := ordinaryFamily K i)
  have hrow := decompositionMatrix_row_formula system (ordinaryFamily K) hV
    (modularFamilyThree k) hS i
  have h₁ := hrow regularIdentityThree
  have hₜ := hrow regularTranspositionThree
  have b₁₀ := (modular_brauer_values_three system 0 regularIdentityThree).1 (IsConj.refl 1)
  have b₁₁ := (modular_brauer_values_three system 1 regularIdentityThree).1 (IsConj.refl 1)
  have bₜ₀ := (modular_brauer_values_three system 0 regularTranspositionThree).2
    (IsConj.refl transposition)
  have bₜ₁ := (modular_brauer_values_three system 1 regularTranspositionThree).2
    (IsConj.refl transposition)
  let := modularGroundFinite k 0
  let := modularGroundFinite k 1
  change brauerCharacter system (modularFamilyThree k 0) regularIdentityThree = 1 at b₁₀
  change brauerCharacter system (modularFamilyThree k 1) regularIdentityThree = 1 at b₁₁
  change brauerCharacter system (modularFamilyThree k 0) regularTranspositionThree = 1 at bₜ₀
  change brauerCharacter system (modularFamilyThree k 1) regularTranspositionThree = -1 at bₜ₁
  simp only [Fin.sum_univ_two, b₁₀, b₁₁, map_one, mul_one] at h₁
  simp only [Fin.sum_univ_two, bₜ₀, bₜ₁, map_one, map_neg, mul_one, mul_neg,
    ← sub_eq_add_neg] at hₜ
  have hχ := ordinary_character_values_three K i
  have he₁ : (E i 0 : K) + (E i 1 : K) = (![1, 1, 2] : Fin 3 → K) i := by
    fin_cases i <;> norm_num [E]
  have heₜ : (E i 0 : K) - (E i 1 : K) = (![1, -1, 0] : Fin 3 → K) i := by
    fin_cases i <;> norm_num [E]
  have hadd : (D i 0 : K) + (D i 1 : K) = (E i 0 : K) + (E i 1 : K) :=
    h₁.symm.trans (hχ.1.trans he₁.symm)
  have hsub : (D i 0 : K) - (D i 1 : K) = (E i 0 : K) - (E i 1 : K) :=
    hₜ.symm.trans (hχ.2.trans heₜ.symm)
  have htwo (a b : ℕ) (h : (2 : K) * ((a : K) - (b : K)) = 0) : a = b :=
    Nat.cast_injective (R := K) (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num)))
  have hzero : D i 0 = E i 0 := htwo _ _ (by linear_combination hadd + hsub)
  have hone : D i 1 = E i 1 := htwo _ _ (by linear_combination hadd - hsub)
  fin_cases j
  · exact hzero
  · exact hone

end RepTheorySurvey.Modular.SymmetricThree
