import MathGenome.Internal.Specs.D07.Ch21.InductionExamples
import MathGenome.Internal.D07.Ch21.InducedCharacter
import MathGenome.Internal.D07.Ch21.S3Table
import MathGenome.Internal.D07.Ch18.NilpotenceExamplesSolvableNonnilpotent
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace D07.Ch21.InductionExamples
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
open Representation
open Specs.D07.Ch21.InductionExamples
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open D07.Ch21.InductionCosetModelInductionConventionBridge
open D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
open Specs.D07.Ch21.S3Table

universe u

/-- The canonical coordinates for induction of a trivial line. -/
def trivialCoordinates {G : Type u} [Group G] (H : Subgroup G) :
    NotesInd H (trivial ℂ H ℂ) ≃ₗ[ℂ] ((G ⧸ H) →₀ ℂ) :=
  (coordinateEquiv H (trivial ℂ H ℂ) Quotient.out QuotientGroup.out_eq').symm

@[simp] lemma trivialCoordinates_mk {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (c : ℂ) :
    trivialCoordinates H (notesMk H (trivial ℂ H ℂ) g c) =
      Finsupp.single (QuotientGroup.mk g) c := by
  exact coordinateEquiv_symm_mk H (trivial ℂ H ℂ) Quotient.out
    QuotientGroup.out_eq' g c

/-- Identify the quotient with the canonical permutation representation. -/
def trivialPermutationEquiv {G : Type u} [Group G] (H : Subgroup G) :
    (notesRep H (trivial ℂ H ℂ)).Equiv (ofMulAction ℂ G (G ⧸ H)) :=
  Representation.Equiv.mk
    ((trivialCoordinates H).trans (MonoidAlgebra.coeffLinearEquiv ℂ).symm) (by
      intro k
      apply notes_hom_ext
      intro g c
      change (MonoidAlgebra.coeffLinearEquiv ℂ).symm
        (trivialCoordinates H (notesRep H (trivial ℂ H ℂ) k
          (notesMk H (trivial ℂ H ℂ) g c))) =
        ofMulAction ℂ G (G ⧸ H) k ((MonoidAlgebra.coeffLinearEquiv ℂ).symm
          (trivialCoordinates H (notesMk H (trivial ℂ H ℂ) g c)))
      rw [notesRep_mk, trivialCoordinates_mk, trivialCoordinates_mk]
      change MonoidAlgebra.single (QuotientGroup.mk (k * g) : G ⧸ H) c =
        ofMulAction ℂ G (G ⧸ H) k (MonoidAlgebra.single (QuotientGroup.mk g) c)
      rw [ofMulAction_single]
      rfl)

theorem trivial_induction : TrivialInduction.{u} := by
  intro G _ _ H
  refine ⟨notesRep H (trivial ℂ H ℂ), trivialCoordinates H, notesRep_mk _ _,
    trivialCoordinates_mk H, ?_, ⟨trivialPermutationEquiv H⟩⟩
  intro k q c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← trivialCoordinates_mk H g c, LinearEquiv.symm_apply_apply,
    notesRep_mk, trivialCoordinates_mk]
  rfl


section Regular
variable {G : Type u} [Group G]

/-- The identity subgroup has one coset per group element. -/
def regularCoordinates :
    NotesInd (⊥ : Subgroup G) (trivial ℂ _ ℂ) ≃ₗ[ℂ] MonoidAlgebra ℂ G :=
  ((trivialCoordinates (⊥ : Subgroup G)).trans
    (Finsupp.domLCongr QuotientGroup.quotientBot.toEquiv)).trans
      (MonoidAlgebra.coeffLinearEquiv ℂ).symm

@[simp] lemma regularCoordinates_mk (g : G) (c : ℂ) :
    regularCoordinates (notesMk (⊥ : Subgroup G) (trivial ℂ _ ℂ) g c) =
      MonoidAlgebra.single g c := by
  simp only [regularCoordinates, LinearEquiv.trans_apply, trivialCoordinates_mk,
    Finsupp.domLCongr_single]
  rfl

def regularEquiv :
    (notesRep (⊥ : Subgroup G) (trivial ℂ _ ℂ)).Equiv (leftRegular ℂ G) :=
  Representation.Equiv.mk regularCoordinates (by
    intro k
    apply notes_hom_ext
    intro g c
    change regularCoordinates (notesRep ⊥ (trivial ℂ _ ℂ) k
      (notesMk ⊥ (trivial ℂ _ ℂ) g c)) =
      leftRegular ℂ G k (regularCoordinates (notesMk ⊥ (trivial ℂ _ ℂ) g c))
    simp [notesRep_mk])

/-- The regular identification imposes no nontriviality assumption. -/
theorem regular_induction : RegularInduction.{u} := by
  intro K _ _
  exact ⟨notesRep ⊥ (trivial ℂ _ ℂ), regularEquiv, notesRep_mk _ _, regularCoordinates_mk⟩

variable [Fintype G]

def regularSum : MonoidAlgebra ℂ G := ∑ g : G, MonoidAlgebra.single g 1

@[simp] lemma regularSum_coeff (g : G) : (regularSum (G := G)).coeff g = 1 := by
  simp [regularSum, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]

lemma regularSum_ne_zero : regularSum (G := G) ≠ 0 := by
  intro hz
  have := congrArg (fun x : MonoidAlgebra ℂ G => x.coeff 1) hz
  simpa using this

lemma regularSum_fixed (k : G) : leftRegular ℂ G k regularSum = regularSum := by
  simp only [regularSum, map_sum, ofMulAction_single, smul_eq_mul]
  exact Equiv.sum_comp (Equiv.mulLeft k) (fun g : G => MonoidAlgebra.single g (1 : ℂ))

lemma regularLine_proper (hG : 1 < Fintype.card G) :
    Submodule.span ℂ {regularSum (G := G)} ≠ ⊤ := by
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hG
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  intro htop
  obtain ⟨c, hc⟩ := (Submodule.span_singleton_eq_top_iff ℂ regularSum).mp htop
    (MonoidAlgebra.single (1 : G) 1)
  have h1 := congrArg (fun x : MonoidAlgebra ℂ G => x.coeff 1) hc
  have hg' := congrArg (fun x : MonoidAlgebra ℂ G => x.coeff g) hc
  have hc1 : c = 1 := by simpa using h1
  have hc0 : c = 0 := by simpa [hg, Ne.symm hg] using hg'
  exact one_ne_zero (hc1.symm.trans hc0)

lemma regularLine_invariant (k : G) (v : MonoidAlgebra ℂ G)
    (hv : v ∈ Submodule.span ℂ {regularSum (G := G)}) :
    leftRegular ℂ G k v ∈ Submodule.span ℂ {regularSum (G := G)} := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, regularSum_fixed]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

lemma regular_not_irreducible (hG : 1 < Fintype.card G) :
    ¬ Representation.IsIrreducible (leftRegular ℂ G) := by
  intro hirr
  have hh := (D07.Ch17.IrreducibleDefinition.irreducibility_characterization
    ℂ G (MonoidAlgebra ℂ G) (leftRegular ℂ G)).mp hirr
  rcases hh.2 _ regularLine_invariant with hb | ht
  · apply regularSum_ne_zero (G := G)
    have hz : regularSum (G := G) ∈ (⊥ : Submodule ℂ (MonoidAlgebra ℂ G)) :=
      hb ▸ Submodule.subset_span (Set.mem_singleton _)
    simpa using hz
  · exact regularLine_proper hG ht

end Regular

/-- Any action on a complex line is irreducible. -/
lemma line_irreducible {K : Type*} [Group K] (ρ : Representation ℂ K ℂ) :
    Representation.IsIrreducible ρ := by
  apply (D07.Ch17.IrreducibleDefinition.irreducibility_characterization ℂ K ℂ ρ).mpr
  exact ⟨inferInstance, fun U _ => eq_bot_or_eq_top U⟩

theorem regular_example : RegularExample.{u} := by
  intro G _ _ hG
  refine ⟨notesRep ⊥ (trivial ℂ _ ℂ), regularEquiv, notesRep_mk _ _,
    regularCoordinates_mk, regularSum_ne_zero, regularLine_proper hG,
    regularSum_fixed, line_irreducible _, ?_⟩
  intro h
  apply regular_not_irreducible hG
  exact MultiplicityClassification.irreducible_of_equiv regularEquiv.symm h


lemma h2_mem (g : S3) : g ∈ H2 ↔ g = 1 ∨ g = s := by
  have hh : ∀ g : S3, g ∈ Subgroup.zpowers s ↔ g = 1 ∨ g = s := by
    have hs : orderOf s = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    simp_rw [mem_zpowers_iff_mem_range_orderOf, hs]
    decide +kernel
  exact hh g

lemma h2_stabilizer : H2 = MulAction.stabilizer S3 (2 : Fin 3) := by
  ext g
  rw [h2_mem]
  change (g = 1 ∨ g = s) ↔ g 2 = 2
  have hh : ∀ g : S3, (g = 1 ∨ g = s) ↔ g 2 = 2 := by decide +kernel
  exact hh g

/-- Orbit-stabilizer with the specified base point and its full orbit. -/
def cosetPointEquiv : (S3 ⧸ H2) ≃ Fin 3 :=
  (Subgroup.quotientEquivOfEq h2_stabilizer).trans
    (Equiv.ofBijective (MulAction.ofQuotientStabilizer S3 (2 : Fin 3))
      ⟨MulAction.injective_ofQuotientStabilizer S3 2, by
        intro i
        exact ⟨QuotientGroup.mk (Equiv.swap 2 i), by
          simp only [MulAction.ofQuotientStabilizer_mk]
          exact Equiv.swap_apply_left 2 i⟩⟩)

@[simp] lemma cosetPointEquiv_mk (g : S3) :
    cosetPointEquiv (QuotientGroup.mk g) = g 2 := rfl

lemma cosetPointEquiv_action (k : S3) (q : S3 ⧸ H2) :
    cosetPointEquiv (k • q) = k (cosetPointEquiv q) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

theorem s3_cosets : S3Cosets :=
  ⟨h2_stabilizer, cosetPointEquiv, cosetPointEquiv_mk, cosetPointEquiv_action⟩


section H2Characters
open Specs.D07.Ch21.InducedCharacter
open Specs.D07.Ch17.Characters

lemma h2_card : Nat.card H2 = 2 := by
  let e : H2 ≃ {g : S3 // g = 1 ∨ g = s} :=
    Equiv.subtypeEquivRight h2_mem
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

/-- A line's trace is its scalar evaluated at 1. -/
lemma trace_line (f : Module.End ℂ ℂ) : LinearMap.trace ℂ ℂ f = f 1 := by
  have hf : f = f 1 • (1 : Module.End ℂ ℂ) := by
    ext z
    simpa [mul_comm] using f.map_smul z (1 : ℂ)
  rw [hf, map_smul, LinearMap.trace_one]
  simp

lemma trivial_line_character {K : Type*} [Group K] (h : K) :
    characterValue ℂ K ℂ (trivial ℂ K ℂ) h = 1 := by
  exact trace_line 1

lemma epsilon_character (h : H2) :
    characterValue ℂ H2 ℂ epsilon h = χ sign h := rfl

lemma sum_indicator {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (∑ i, if P i then (1 : ℂ) else 0) = (Fintype.card {i // P i} : ℂ) := by
  simp [Fintype.card_subtype]

lemma induced_h2_trivial_values :
    induceClassFunction H2 (fun _ => 1) 1 = 3 ∧
    induceClassFunction H2 (fun _ => 1) s = 1 ∧
    induceClassFunction H2 (fun _ => 1) a = 0 := by
  have h1 : Fintype.card {x : S3 // x⁻¹ * 1 * x = 1 ∨ x⁻¹ * 1 * x = s} = 6 := by decide +kernel
  have hs : Fintype.card {x : S3 // x⁻¹ * s * x = 1 ∨ x⁻¹ * s * x = s} = 2 := by decide +kernel
  have ha : Fintype.card {x : S3 // x⁻¹ * a * x = 1 ∨ x⁻¹ * a * x = s} = 0 := by decide +kernel
  unfold induceClassFunction
  rw [h2_card]
  simp only [extendByZero, dite_eq_ite, h2_mem]
  rw [sum_indicator, sum_indicator, sum_indicator, h1, hs, ha]
  norm_num

lemma induced_h2_sign (g : S3) :
    induceClassFunction H2 (characterValue ℂ H2 ℂ epsilon) g =
      χ sign g * induceClassFunction H2 (fun _ => 1) g := by
  unfold induceClassFunction
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hy : x⁻¹ * g * x ∈ H2
  · simp only [extendByZero, dite_eq_left hy, epsilon_character, mul_one]
    simpa using D07.Ch17.Characters.character_conjugate ℂ S3 ℂ sign g x⁻¹
  · simp [extendByZero, hy]

lemma h2_trivial_values :
    χ (notesRep H2 (trivial ℂ H2 ℂ)) 1 = 3 ∧
    χ (notesRep H2 (trivial ℂ H2 ℂ)) s = 1 ∧
    χ (notesRep H2 (trivial ℂ H2 ℂ)) a = 0 := by
  have hh (g : S3) : χ (notesRep H2 (trivial ℂ H2 ℂ)) g =
      induceClassFunction H2 (fun _ => 1) g := by
    exact (InducedCharacter.character_formulas S3 H2 ℂ (trivial ℂ H2 ℂ)
      (notesRep H2 _) (notesRep_mk _ _) Quotient.out QuotientGroup.out_eq' g).2.trans
      (by
        have he : characterValue ℂ H2 ℂ (trivial ℂ H2 ℂ) = fun _ => 1 :=
          funext trivial_line_character
        rw [he])
  simpa only [hh] using induced_h2_trivial_values

lemma h2_epsilon_values :
    χ (notesRep H2 epsilon) 1 = 3 ∧
    χ (notesRep H2 epsilon) s = -1 ∧
    χ (notesRep H2 epsilon) a = 0 := by
  have hh (g : S3) : χ (notesRep H2 epsilon) g =
      χ sign g * induceClassFunction H2 (fun _ => 1) g :=
    (InducedCharacter.character_formulas S3 H2 ℂ epsilon
      (notesRep H2 _) (notesRep_mk _ _) Quotient.out QuotientGroup.out_eq' g).2.trans
        (induced_h2_sign g)
  rw [hh, hh, hh, S3Table.sign_values.1, S3Table.sign_values.2.1,
    S3Table.sign_values.2.2, induced_h2_trivial_values.1,
    induced_h2_trivial_values.2.1, induced_h2_trivial_values.2.2]
  norm_num

end H2Characters


section Characters
variable {V W Z : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [FiniteDimensional ℂ Z]

lemma character_eq_of_values (ρ : Representation ℂ S3 V) (τ : Representation ℂ S3 W)
    (h1 : χ ρ 1 = χ τ 1) (hs : χ ρ s = χ τ s) (ha : χ ρ a = χ τ a) :
    χ ρ = χ τ := by
  funext g
  rcases S3Table.classes.2.1 g with h | h | h <;>
    rw [S3Table.character_class ρ h, S3Table.character_class τ h]
  · exact h1
  · exact hs
  · exact ha

lemma character_prod (ρ : Representation ℂ S3 V) (τ : Representation ℂ S3 W) (g : S3) :
    χ (ρ.prod τ) g = χ ρ g + χ τ g :=
  LinearMap.trace_prodMap' (ρ g) (τ g)

/-- Character classification is applied to actual finite dimensional actions. -/
lemma equiv_of_character (ρ : Representation ℂ S3 V) (τ : Representation ℂ S3 W)
    (hχ : χ ρ = χ τ) : Nonempty (ρ.Equiv τ) := by
  obtain ⟨q, _, hi, hne, hc, _⟩ := RegularDecomposition.regular_theorem.{0,0} S3
  let α (i : q) := i.val.toRepresentation
  have hα (i : q) : Representation.IsIrreducible (α i) := hi i.val i.property
  have hneq (i j : q) (hij : i ≠ j) : ¬ Nonempty ((α i).Equiv (α j)) :=
    hne i.property j.property (fun h => hij (Subtype.ext h))
  haveI (i : q) : FiniteDimensional ℂ i.val.toSubmodule :=
    (RegularDecomposition.irreducible_finite S3 _ (α i) (hα i)).1
  exact (MultiplicityClassification.equivalence_iff α hα hneq hc ρ τ).mpr hχ

end Characters

lemma h2_trivial_character :
    χ (notesRep H2 (trivial ℂ H2 ℂ)) = χ permRep :=
  character_eq_of_values _ _
    (h2_trivial_values.1.trans S3Table.permutation_values.1.symm)
    (h2_trivial_values.2.1.trans S3Table.permutation_values.2.1.symm)
    (h2_trivial_values.2.2.trans S3Table.permutation_values.2.2.symm)

lemma h2_epsilon_character :
    χ (notesRep H2 epsilon) = χ (sign.prod S3Table.standard) := by
  apply character_eq_of_values <;> rw [character_prod]
  · rw [h2_epsilon_values.1, S3Table.sign_values.1, S3Table.standard_values.1]; norm_num
  · rw [h2_epsilon_values.2.1, S3Table.sign_values.2.1, S3Table.standard_values.2.1]; norm_num
  · rw [h2_epsilon_values.2.2, S3Table.sign_values.2.2, S3Table.standard_values.2.2]; norm_num

theorem s3_order_two : S3OrderTwo := by
  refine ⟨S3Table.standard, S3Table.standard_apply, notesRep H2 (trivial ℂ H2 ℂ),
    notesRep H2 epsilon, notesRep_mk _ _, notesRep_mk _ _, ?_,
    h2_trivial_values, h2_epsilon_values, ?_, ?_,
    equiv_of_character _ _ h2_trivial_character, ?_,
    equiv_of_character _ _ h2_epsilon_character⟩
  · refine ⟨⟨s, (h2_mem s).mpr (Or.inr rfl)⟩, ?_⟩
    rw [← trace_line]
    exact S3Table.sign_values.2.1
  · intro g
    rw [congrFun h2_trivial_character g]
    exact S3Table.character_decomposition g
  · intro g
    rw [congrFun h2_epsilon_character g, character_prod]
  · apply equiv_of_character
    funext g
    rw [congrFun h2_trivial_character g, character_prod]
    exact S3Table.character_decomposition g


section H3

lemma h3_mem (g : S3) : g ∈ H3 ↔ g = 1 ∨ g = a ∨ g = a ^ 2 := by
  have hh : ∀ g : S3, g ∈ alternatingGroup (Fin 3) ↔ g = 1 ∨ g = a ∨ g = a ^ 2 := by
    simp_rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  exact hh g

lemma h3_zpowers : H3 = Subgroup.zpowers a := by
  have ha : orderOf a = 3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  ext g
  rw [h3_mem, mem_zpowers_iff_mem_range_orderOf, ha]
  have hh : ∀ g : S3, (g = 1 ∨ g = a ∨ g = a ^ 2) ↔
      g ∈ Finset.image (fun n => a ^ n) (Finset.range 3) := by decide +kernel
  exact hh g

abbrev a3 : H3 := ⟨a, (h3_mem a).mpr (Or.inr (Or.inl rfl))⟩

lemma a3_order : orderOf a3 = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have ha : a ≠ 1 := by decide +kernel
    exact ha (congrArg Subtype.val h)

lemma a3_powers (x : H3) : x ∈ Subgroup.zpowers a3 := by
  rcases (h3_mem x).mp x.property with h | h | h
  · exact Subgroup.mem_zpowers_iff.mpr ⟨0, by apply Subtype.ext; simpa using h.symm⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by apply Subtype.ext; simpa using h.symm⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨2, by apply Subtype.ext; simpa using h.symm⟩

/-- Construct the cyclic character by the universal property of a generator. -/
def cubicCharacter (ω : ℂ) (hω : IsPrimitiveRoot ω 3) : H3 →* ℂ :=
  (Units.coeHom ℂ).comp (monoidHomOfForallMemZpowers a3_powers
    (g' := Units.mk0 ω (hω.ne_zero (by decide))) (by
      rw [a3_order]
      exact orderOf_dvd_of_pow_eq_one (by apply Units.ext; exact hω.pow_eq_one)))

@[simp] lemma cubicCharacter_a (ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    cubicCharacter ω hω a3 = ω := by
  change (↑((monoidHomOfForallMemZpowers a3_powers
    (g' := Units.mk0 ω (hω.ne_zero (by decide))) _) a3) : ℂ) = ω
  rw [monoidHomOfForallMemZpowers_apply_gen]
  rfl

def conjugateCharacter (ψ : H3 →* ℂ) : H3 →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp ψ

lemma h3_card : Nat.card H3 = 3 := by
  let e : H3 ≃ {g : S3 // g = 1 ∨ g = a ∨ g = a ^ 2} :=
    Equiv.subtypeEquivRight h3_mem
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

lemma scalar_character (ψ : H3 →* ℂ) (h : H3) :
    Specs.D07.Ch17.Characters.characterValue ℂ H3 ℂ (scalarRep ψ) h = ψ h := by
  rw [Specs.D07.Ch17.Characters.characterValue, trace_line]
  change ψ h * 1 = ψ h
  exact mul_one _

lemma h3_extend (ψ : H3 →* ℂ) (g : S3) :
    Specs.D07.Ch21.InducedCharacter.extendByZero H3 (fun h => ψ h) g =
      if g = 1 then 1 else if g = a then ψ a3 else if g = a ^ 2 then ψ a3 ^ 2 else 0 := by
  by_cases hg1 : g = 1
  · subst g
    rw [Specs.D07.Ch21.InducedCharacter.extendByZero, dite_eq_left H3.one_mem, ite_eq_left rfl]
    exact map_one ψ
  by_cases hga : g = a
  · subst g
    rw [Specs.D07.Ch21.InducedCharacter.extendByZero, dite_eq_left a3.property,
      ite_eq_right hg1, ite_eq_left rfl]
  by_cases hga2 : g = a ^ 2
  · subst g
    rw [Specs.D07.Ch21.InducedCharacter.extendByZero,
      dite_eq_left (H3.pow_mem a3.property 2), ite_eq_right hg1, ite_eq_right hga, ite_eq_left rfl]
    exact map_pow ψ a3 2
  · have hg : g ∉ H3 := by
      intro hm
      rcases (h3_mem g).mp hm with h | h | h
      · exact hg1 h
      · exact hga h
      · exact hga2 h
    rw [Specs.D07.Ch21.InducedCharacter.extendByZero, dite_eq_right hg,
      ite_eq_right hg1, ite_eq_right hga, ite_eq_right hga2]


lemma sum_s3 (f : S3 → ℂ) : ∑ x, f x =
    f 1 + f s + f (Equiv.swap 0 2) + f (Equiv.swap 1 2) + f a + f a⁻¹ := by
  rw [S3Table.group_elements]
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  ring

lemma sum_h3_split (c d : ℂ) :
    (∑ x : S3, if x = 1 ∨ x = a ∨ x = a ^ 2 then c else d) = 3 * c + 3 * d := by
  rw [sum_s3]
  simp (discharger := decide +kernel) only [ite_eq_left, ite_eq_right]
  ring

lemma h3_function_values (ψ : H3 →* ℂ) :
    Specs.D07.Ch21.InducedCharacter.induceClassFunction H3 (fun h => ψ h) 1 = 2 ∧
    Specs.D07.Ch21.InducedCharacter.induceClassFunction H3 (fun h => ψ h) s = 0 ∧
    Specs.D07.Ch21.InducedCharacter.induceClassFunction H3 (fun h => ψ h) a =
      ψ a3 + ψ a3 ^ 2 := by
  have ha1 : a ≠ 1 := by decide +kernel
  have ha21 : a ^ 2 ≠ 1 := by decide +kernel
  have ha2a : a ^ 2 ≠ a := by decide +kernel
  have hc : ∀ x : S3, x⁻¹ * a * x =
      if x = 1 ∨ x = a ∨ x = a ^ 2 then a else a ^ 2 := by decide +kernel
  have hs : ∀ x : S3, x⁻¹ * s * x ≠ 1 ∧ x⁻¹ * s * x ≠ a ∧
      x⁻¹ * s * x ≠ a ^ 2 := by decide +kernel
  unfold Specs.D07.Ch21.InducedCharacter.induceClassFunction
  rw [h3_card]
  simp_rw [h3_extend]
  refine ⟨?_, ?_, ?_⟩
  · simp [S3Table.group_card]
    norm_num
  · simp only [ite_eq_right (hs _).1, ite_eq_right (hs _).2.1,
      ite_eq_right (hs _).2.2, Finset.sum_const_zero, mul_zero]
  · have he (x : S3) :
        (if x⁻¹ * a * x = 1 then 1 else if x⁻¹ * a * x = a then ψ a3
          else if x⁻¹ * a * x = a ^ 2 then ψ a3 ^ 2 else 0) =
        if x = 1 ∨ x = a ∨ x = a ^ 2 then ψ a3 else ψ a3 ^ 2 := by
      rw [hc]
      by_cases hx : x = 1 ∨ x = a ∨ x = a ^ 2
      · rw [ite_eq_left hx]
        simp [ha1, hx]
      · rw [ite_eq_right hx]
        simp [ha21, ha2a, hx]
    simp_rw [he]
    rw [sum_h3_split]
    ring

lemma h3_character_values (ψ : H3 →* ℂ) :
    χ (notesRep H3 (scalarRep ψ)) 1 = 2 ∧
    χ (notesRep H3 (scalarRep ψ)) s = 0 ∧
    χ (notesRep H3 (scalarRep ψ)) a = ψ a3 + ψ a3 ^ 2 := by
  have hh (g : S3) : χ (notesRep H3 (scalarRep ψ)) g =
      Specs.D07.Ch21.InducedCharacter.induceClassFunction H3 (fun h => ψ h) g := by
    have h := (InducedCharacter.character_formulas S3 H3 ℂ (scalarRep ψ)
      (notesRep H3 _) (notesRep_mk _ _) Quotient.out QuotientGroup.out_eq' g).2
    have he : Specs.D07.Ch17.Characters.characterValue ℂ H3 ℂ (scalarRep ψ) =
        fun h => ψ h := funext (scalar_character ψ)
    rwa [he] at h
  simpa only [hh] using h3_function_values ψ

lemma cubic_sum (ω : ℂ) (hω : IsPrimitiveRoot ω 3) : ω + ω ^ 2 = -1 := by
  have h := hω.geom_sum_eq_zero (by decide)
  have he : 1 + ω + ω ^ 2 = 0 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] using h
  linear_combination he

lemma cubic_induced_character (ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    χ (notesRep H3 (scalarRep (cubicCharacter ω hω))) = χ S3Table.standard := by
  apply character_eq_of_values
  · exact (h3_character_values _).1.trans S3Table.standard_values.1.symm
  · exact (h3_character_values _).2.1.trans S3Table.standard_values.2.1.symm
  · rw [(h3_character_values _).2.2, cubicCharacter_a, cubic_sum ω hω]
    exact S3Table.standard_values.2.2.symm

lemma conjugate_induced_character (ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    χ (notesRep H3 (scalarRep (conjugateCharacter (cubicCharacter ω hω)))) =
      χ S3Table.standard := by
  apply character_eq_of_values
  · exact (h3_character_values _).1.trans S3Table.standard_values.1.symm
  · exact (h3_character_values _).2.1.trans S3Table.standard_values.2.1.symm
  · rw [(h3_character_values _).2.2]
    change starRingEnd ℂ (cubicCharacter ω hω a3) +
      (starRingEnd ℂ (cubicCharacter ω hω a3)) ^ 2 = χ S3Table.standard a
    rw [cubicCharacter_a, ← map_pow, ← map_add, cubic_sum ω hω,
      map_neg, map_one, S3Table.standard_values.2.2]

lemma cubic_ne_conjugate (ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    ω ≠ starRingEnd ℂ ω := by
  intro h
  have hmul : ω * starRingEnd ℂ ω = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω.norm'_eq_one (by decide)]
    norm_num
  have hsq : ω ^ 2 = 1 := by simpa [← h, pow_two] using hmul
  have hthree := hω.pow_eq_one
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, hsq, one_mul, pow_one] at hthree
  exact hω.ne_one (by decide) hthree

lemma cubic_inputs_inequivalent (ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    ¬ Nonempty ((scalarRep (cubicCharacter ω hω)).Equiv
      (scalarRep (conjugateCharacter (cubicCharacter ω hω)))) := by
  intro he
  have h := congrFun (D07.Ch17.Characters.character_equivalence ℂ H3 ℂ ℂ _ _ he) a3
  rw [scalar_character, scalar_character, cubicCharacter_a] at h
  change ω = starRingEnd ℂ (cubicCharacter ω hω a3) at h
  rw [cubicCharacter_a] at h
  exact cubic_ne_conjugate ω hω h

lemma cubic_no_extension (ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    ¬ ∃ θ : S3 →* ℂ, θ.comp H3.subtype = cubicCharacter ω hω := by
  rintro ⟨θ, he⟩
  have hcomm : a ∈ commutator S3 := by
    rw [D07.Ch18.NilpotenceExamplesSolvableNonnilpotent.derived_subgroup]
    exact a3.property
  have hk := Abelianization.commutator_subset_ker θ.toHomUnits hcomm
  have hθ : θ a = 1 := congrArg (fun u : ℂˣ => (u : ℂ)) hk
  have hv : θ a = ω := (congrArg (fun f : H3 →* ℂ => f a3) he).trans
    (cubicCharacter_a ω hω)
  exact hω.ne_one (by decide) (hv.symm.trans hθ)



/-- The two representatives in the source are a transversal of A₃. -/
def cubicCosetEquiv : Fin 2 ≃ (S3 ⧸ H3) :=
  Equiv.ofBijective (fun i => QuotientGroup.mk (if i = 0 then 1 else s)) (by
    constructor
    · intro i j he
      fin_cases i <;> fin_cases j
      · rfl
      · have hs : s ∉ H3 := by rw [h3_mem]; decide +kernel
        exact (hs (by simpa using QuotientGroup.eq.mp he)).elim
      · have hs : s ∉ H3 := by rw [h3_mem]; decide +kernel
        exact (hs (by simpa using QuotientGroup.eq.mp he.symm)).elim
      · rfl
    · intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ H3 ∨ s⁻¹ * g ∈ H3 := by
        have hh : ∀ g : S3, (g = 1 ∨ g = a ∨ g = a ^ 2) ∨
            (s⁻¹ * g = 1 ∨ s⁻¹ * g = a ∨ s⁻¹ * g = a ^ 2) := by decide +kernel
        exact ((h3_mem g).symm.or (h3_mem (s⁻¹ * g)).symm).mp (hh g)
      rcases hg with hg | hg
      · refine ⟨0, QuotientGroup.eq.mpr ?_⟩
        simpa using hg
      · refine ⟨1, QuotientGroup.eq.mpr ?_⟩
        simpa using hg)

theorem cubic_preliminaries : CubicPreliminaries := by
  refine ⟨⟨Complex.exp (2 * Real.pi * Complex.I / 3),
    Complex.isPrimitiveRoot_exp 3 (by decide)⟩, ?_, cubicCosetEquiv, rfl, rfl⟩
  decide +kernel


theorem s3_order_three : S3OrderThree := by
  refine ⟨h3_zpowers, ?_⟩
  intro ω hω
  let ψ := cubicCharacter ω hω
  let ψbar := conjugateCharacter ψ
  have hχ := cubic_induced_character ω hω
  have hbχ := conjugate_induced_character ω hω
  have he := equiv_of_character _ _ hχ
  have hbe := equiv_of_character _ _ hbχ
  refine ⟨a3.property, ψ, ψbar, S3Table.standard, notesRep H3 (scalarRep ψ),
    notesRep H3 (scalarRep ψbar), cubicCharacter_a ω hω,
    fun _ => rfl, S3Table.standard_apply, notesRep_mk _ _, notesRep_mk _ _,
    ?_, congrFun hχ, congrFun hbχ, he, hbe,
    MultiplicityClassification.irreducible_of_equiv he.some S3Table.irreducibles.2.2,
    line_irreducible _, line_irreducible _, cubic_inputs_inequivalent ω hω, ⟨he.some.trans hbe.some.symm⟩,
    cubic_no_extension ω hω⟩
  refine ⟨(h3_character_values ψ).1, (h3_character_values ψ).2.1, ?_⟩
  rw [(h3_character_values ψ).2.2]
  exact (congrArg (fun z : ℂ => z + z ^ 2) (cubicCharacter_a ω hω)).trans (cubic_sum ω hω)


end H3

end
end D07.Ch21.InductionExamples
