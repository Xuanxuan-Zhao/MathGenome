import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterTableOrthogonality
import MathGenome.Internal.AlgebraCore.P103.Ch08.CentralIdempotents
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.Index

noncomputable section
universe u v
namespace P103.Ch08.CharacterTableOrthogonality
open FourierSpecs CharacterTableSpecs
open scoped Classical
open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur

@[simp] theorem character_mk {G : Type u} [Group G] (C : Family.{u,v} G)
    (i : Fin C.n) (g : G) :
    classCharacter C i (ConjClasses.mk g) = CharacterSpecs.characterValue (C.representation i) g := rfl

/-- Descent along the conjugacy quotient is equivalent to ordinary invariance. -/
theorem pullback : pullbackType.{u} := by
  intro G _ f
  constructor
  · intro hf
    let F : ClassFunction G := Quotient.lift f (by
      intro g h hgh
      obtain ⟨s, hs⟩ := isConj_iff.mp hgh
      rw [← hs]
      exact (hf g s).symm)
    refine ⟨F, fun _ => rfl, ?_⟩
    intro H hH
    funext D
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep D
    exact hH g
  · rintro ⟨F, hF, _⟩ g h
    rw [← hF, ← hF]
    congr 1
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact (isConj_iff.mpr ⟨h, rfl⟩).symm

/-- Schur orthogonality with the source's first-variable-linear pairing. -/
theorem row : rowType.{u,v} := by
  intro G _ _ C hC i j
  classical
  have := RegularMultiplicity.finite_dimensional (C.representation i) (hC.1 i)
  have := RegularMultiplicity.finite_dimensional (C.representation j) (hC.1 j)
  have := libraryIrreducible (C.representation i) (hC.1 i)
  have := libraryIrreducible (C.representation j) (hC.1 j)
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have ht := Representation.char_orthonormal (C.representation i) (C.representation j)
  have he : Nonempty ((C.representation j).Equiv (C.representation i)) ↔ i = j := by
    constructor
    · intro h; exact (hC.2 j i h).symm
    · rintro rfl; exact ⟨Representation.Equiv.refl _⟩
  unfold UnitaritySpecs.functionPairingValue
  simp_rw [← character_inverse_conjugate (C.representation j)]
  simpa only [Representation.character, CharacterSpecs.characterValue,
    Fintype.card_eq_nat_card, he] using ht

/-- Compare the two actual bases of the same group-algebra center. -/
theorem class_count : classCountType.{u,v} := by
  intro G _ _ C hC hEx
  classical
  obtain ⟨b, _⟩ := CentralIdempotents.idempotent_basis C hC hEx
  obtain ⟨c, _⟩ := CentralIdempotents.class_sum_basis (G := G)
  have h := (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis c)
  simpa [Nat.card_eq_fintype_card] using h

/-- Pair with a fixed character; this is complex-linear in the class function. -/
def pairWith {G : Type u} [Group G] [Fintype G] (C : Family.{u,v} G) (j : Fin C.n) :
    ClassFunction G →ₗ[ℂ] ℂ where
  toFun f := UnitaritySpecs.functionPairingValue (fun g => f (ConjClasses.mk g))
    (CharacterSpecs.characterValue (C.representation j))
  map_add' f h := by
    simp [UnitaritySpecs.functionPairingValue, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a f := by
    simp [UnitaritySpecs.functionPairingValue, Finset.mul_sum, mul_assoc, mul_left_comm]

@[simp] theorem pairWith_classCharacter {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (i j : Fin C.n) :
    pairWith C j (classCharacter C i) = if i = j then 1 else 0 := row C hC i j

theorem characters_linearIndependent {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) : LinearIndependent ℂ (classCharacter C) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have h := congrArg (pairWith C j) ha
  simpa only [map_sum, map_smul, pairWith_classCharacter C hC, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, map_zero] using h

/-- The orthogonal characters have exactly the dimension of the class functions. -/
theorem basis : basisType.{u,v} := by
  intro G _ _ C hC hEx
  classical
  let b := basisOfLinearIndependentOfCardEqFinrank' (classCharacter C)
    (characters_linearIndependent C hC) (by
      simpa using class_count C hC hEx)
  exact ⟨b, fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i⟩

/-- Orthonormal coordinates of an arbitrary class function. -/
theorem expansion {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C) (f : ClassFunction G) :
    ∑ i, pairWith C i f • classCharacter C i = f := by
  classical
  obtain ⟨b, hb⟩ := basis C hC hEx
  have hc (j) : b.repr f j = pairWith C j f := by
    have h := congrArg (pairWith C j) (b.sum_repr f)
    simpa only [map_sum, map_smul, hb, pairWith_classCharacter C hC, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using h
  simpa only [hc, hb] using b.sum_repr f

/-- Pairing a class indicator with a character gives the class-size weight. -/
theorem indicator_pairing {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (j : Fin C.n) (g : G) :
    pairWith C j (fun D => if D = ConjClasses.mk g then 1 else 0) =
      (Fintype.card G : ℂ)⁻¹ * (Nat.card (conjugatesOf g) : ℂ) *
        star (CharacterSpecs.characterValue (C.representation j) g) := by
  classical
  change (Fintype.card G : ℂ)⁻¹ * (∑ x : G,
    (if ConjClasses.mk x = ConjClasses.mk g then 1 else 0) *
      star (CharacterSpecs.characterValue (C.representation j) x)) = _
  have hs : (∑ x : G,
      (if ConjClasses.mk x = ConjClasses.mk g then 1 else 0) *
        star (CharacterSpecs.characterValue (C.representation j) x)) =
      (Nat.card (conjugatesOf g) : ℂ) *
        star (CharacterSpecs.characterValue (C.representation j) g) := by
    calc
      _ = ∑ x : G, if IsConj g x then
          star (CharacterSpecs.characterValue (C.representation j) g) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : IsConj g x
        · have he := ConjClasses.mk_eq_mk_iff_isConj.mpr hx.symm
          have hc := congrArg (classCharacter C j) he
          simp only [character_mk] at hc
          simp only [he, hx, ite_true, one_mul, hc]
        · have he : ConjClasses.mk x ≠ ConjClasses.mk g :=
            fun h => hx (ConjClasses.mk_eq_mk_iff_isConj.mp h).symm
          simp only [ite_eq_right he, ite_eq_right hx, zero_mul]
      _ = _ := by
        simp [Finset.sum_ite, Nat.card_eq_fintype_card,
          conjugatesOf]
  rw [hs]
  ring

/-- Orbit-stabilizer in precisely the form needed for the column normalization. -/
theorem classSize_mul_centralizer {G : Type u} [Group G] [Fintype G] (g : G) :
    Nat.card (conjugatesOf g) * Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Fintype.card G := by
  rw [Nat.card_coe_set_eq, ← Subgroup.index_centralizer_eq_ncard,
    Subgroup.index_mul_card, Nat.card_eq_fintype_card]

/-- Evaluate the expansion of a conjugacy-class indicator, then conjugate.
Orbit-stabilizer supplies the centralizer factor with the stated orientation. -/
theorem column : columnType.{u,v} := by
  intro G _ _ C hC hEx g h
  classical
  let d := Nat.card (conjugatesOf g)
  let n := Fintype.card G
  let S := ∑ i : Fin C.n, CharacterSpecs.characterValue (C.representation i) g *
    star (CharacterSpecs.characterValue (C.representation i) h)
  have hex := congrFun
    (expansion C hC hEx (fun D => if D = ConjClasses.mk g then 1 else 0))
    (ConjClasses.mk h)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    indicator_pairing, character_mk] at hex
  have hs : (n : ℂ)⁻¹ * (d : ℂ) * S =
      if ConjClasses.mk h = ConjClasses.mk g then 1 else 0 := by
    have hc := congrArg star hex
    simpa [S, n, d, star_sum, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      using hc
  have hn : (n : ℂ) ≠ 0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have hd : (d : ℂ) ≠ 0 := by
    have : Nonempty (conjugatesOf g) := ⟨⟨g, IsConj.refl g⟩⟩
    exact_mod_cast (Nat.card_pos (α := conjugatesOf g)).ne'
  have hsize : (d : ℂ) * (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) = n := by
    exact_mod_cast classSize_mul_centralizer g
  change S = _
  by_cases hgh : IsConj g h
  · have he := ConjClasses.mk_eq_mk_iff_isConj.mpr hgh.symm
    rw [ite_eq_left he] at hs
    rw [ite_eq_left hgh]
    apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hn) hd)
    rw [hs]
    calc
      1 = (n : ℂ)⁻¹ * n := (inv_mul_cancel₀ hn).symm
      _ = _ := by rw [← hsize]; ring
  · have he : ConjClasses.mk h ≠ ConjClasses.mk g :=
      fun he => hgh (ConjClasses.mk_eq_mk_iff_isConj.mp he).symm
    rw [ite_eq_right he] at hs
    rw [ite_eq_right hgh]
    exact (mul_eq_zero.mp hs).resolve_left (mul_ne_zero (inv_ne_zero hn) hd)

end P103.Ch08.CharacterTableOrthogonality
