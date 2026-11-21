import MathGenome.Internal.Specs.D07.Ch14.BiquadraticExample
import MathGenome.Internal.D07.Ch14.QuadraticExample
import MathGenome.Internal.D07.Ch14.FundamentalCorrespondence
import MathGenome.Internal.D07.Ch06.PrimeSquareClassification
import Mathlib.Data.Rat.Sqrt
import Mathlib.Data.Fintype.Powerset

namespace D07.Ch14.BiquadraticExample

open IntermediateField
open Specs.D07.Ch14.BiquadraticExample

/-- Two rational square roots cannot lie in the same quadratic field when
both the second radicand and the product of the radicands are nonsquares.
Conjugation fixes either the second root or the product of the two roots;
its fixed field is the rational field. -/
lemma root_not_mem_quadratic {T : Type*} [Field T] [Algebra ℚ T] (a : ℚˣ) (ha : ¬ IsSquare (a : ℚ))
    (b : ℚ) (hb : ¬ IsSquare b) (hab : ¬ IsSquare ((a : ℚ) * b))
    (x y : T) (hx : x ^ 2 = algebraMap ℚ T (a : ℚ))
    (hy : y ^ 2 = algebraMap ℚ T b) :
    y ∉ adjoin ℚ {x} := by
  intro hmem
  obtain ⟨hfin, _, hgal, _, _, σ, _, hσ, _, _, hall⟩ :=
    QuadraticExample.quadratic_extension ℚ T a (by norm_num) ha x hx
  let E := adjoin ℚ ({x} : Set T)
  let r : E := ⟨x, mem_adjoin_simple_self ℚ x⟩
  let s : E := ⟨y, hmem⟩
  let : FiniteDimensional ℚ E := hfin
  let : IsGalois ℚ E := hgal
  have hr : r ^ 2 = algebraMap ℚ E (a : ℚ) := by
    apply Subtype.ext
    exact hx
  have hs : s ^ 2 = algebraMap ℚ E b := by
    apply Subtype.ext
    exact hy
  have hfixed (z : E) (hz : σ z = z) : ∃ q : ℚ, algebraMap ℚ E q = z := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed z).mpr
    intro τ
    rcases hall τ with h | h
    · simp [h]
    · simpa [h] using hz
  have hsign : σ s = s ∨ σ s = -s := by
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    rw [← map_pow, hs, AlgEquiv.commutes]
  rcases hsign with h | h
  · obtain ⟨q, hq⟩ := hfixed s h
    apply hb
    refine ⟨q, ?_⟩
    apply (algebraMap ℚ E).injective
    rw [map_mul, hq]
    simpa [pow_two] using hs.symm
  · have hprod : σ (r * s) = r * s := by
      rw [map_mul, hσ, h, neg_mul_neg]
    obtain ⟨q, hq⟩ := hfixed (r * s) hprod
    apply hab
    refine ⟨q, ?_⟩
    apply (algebraMap ℚ E).injective
    rw [map_mul, map_mul, hq, ← pow_two, mul_pow, hr, hs]

lemma nonsquare_two : ¬ IsSquare (2 : ℚ) := by
  norm_num
  exact Nat.prime_two.not_isSquare
lemma nonsquare_three : ¬ IsSquare (3 : ℚ) := by
  norm_num
  exact (by decide : Nat.Prime 3).not_isSquare
unseal Nat.sqrt.iter in
lemma nonsquare_six : ¬ IsSquare (6 : ℚ) := by
  norm_num
  decide

lemma u_sq : u ^ 2 = (2 : L) := by
  apply Subtype.ext
  exact Real.sq_sqrt (by norm_num)

lemma v_sq : v ^ 2 = (3 : L) := by
  apply Subtype.ext
  exact Real.sq_sqrt (by norm_num)

lemma uv_sq : (u * v) ^ 2 = (6 : L) := by
  rw [mul_pow, u_sq, v_sq]
  norm_num

theorem product_root : ProductRoot := by
  change Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma quadratic_degrees :
    Module.finrank ℚ E2 = 2 ∧ Module.finrank ℚ E3 = 2 ∧ Module.finrank ℚ E6 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact QuadraticExample.quadratic_finrank (Units.mk0 2 (by norm_num))
      nonsquare_two u (by simpa using u_sq)
  · exact QuadraticExample.quadratic_finrank (Units.mk0 3 (by norm_num))
      nonsquare_three v (by simpa using v_sq)
  · exact QuadraticExample.quadratic_finrank (Units.mk0 6 (by norm_num))
      nonsquare_six (u * v) (by simpa using uv_sq)

lemma sqrt_three_not_mem : Real.sqrt 3 ∉ adjoin ℚ ({Real.sqrt 2} : Set ℝ) := by
  apply root_not_mem_quadratic (Units.mk0 2 (by norm_num)) nonsquare_two
    (3 : ℚ) nonsquare_three
  · simpa only [Units.val_mk0, show (2 : ℚ) * 3 = 6 by norm_num] using nonsquare_six
  · simp
  · simp

lemma L_eq_sup : L = adjoin ℚ ({Real.sqrt 2} : Set ℝ) ⊔
    adjoin ℚ ({Real.sqrt 3} : Set ℝ) := by
  rw [← adjoin_union]
  rfl

lemma degree_four : Module.finrank ℚ L = 4 := by
  let A := adjoin ℚ ({Real.sqrt 2} : Set ℝ)
  let B := adjoin ℚ ({Real.sqrt 3} : Set ℝ)
  have hA : Module.finrank ℚ A = 2 :=
    QuadraticExample.quadratic_finrank (Units.mk0 2 (by norm_num)) nonsquare_two
      (Real.sqrt 2) (by simp)
  have hB : Module.finrank ℚ B = 2 :=
    QuadraticExample.quadratic_finrank (Units.mk0 3 (by norm_num)) nonsquare_three
      (Real.sqrt 3) (by simp)
  let : FiniteDimensional ℚ A := Module.finite_of_finrank_pos (by omega)
  let : FiniteDimensional ℚ B := Module.finite_of_finrank_pos (by omega)
  have hsup : L = A ⊔ B := L_eq_sup
  have hfin : FiniteDimensional ℚ L := hsup ▸ inferInstance
  let := hfin
  have hle : A ≤ L := hsup ▸ le_sup_left
  have hd : 2 ∣ Module.finrank ℚ L := hA ▸ finrank_dvd_of_le_right hle
  have hu : Module.finrank ℚ L ≤ 4 := by
    rw [hsup]
    simpa [hA, hB] using (finrank_sup_le A B)
  have hl : 2 < Module.finrank ℚ L := by
    by_contra! hh
    have he : A = L := eq_of_le_of_finrank_le hle (by omega)
    apply sqrt_three_not_mem
    have hv : Real.sqrt 3 ∈ L := v.property
    change Real.sqrt 3 ∈ A
    rw [he]
    exact hv
  omega

theorem degree_and_galois : DegreeAndGalois := by
  have hdegree := degree_four
  let : FiniteDimensional ℚ L := Module.finite_of_finrank_pos (by omega)
  have hA : IsGalois ℚ (adjoin ℚ ({Real.sqrt 2} : Set ℝ)) :=
    QuadraticExample.quadratic_galois (Units.mk0 2 (by norm_num)) (by norm_num)
      nonsquare_two (Real.sqrt 2)
      (by simp)
  have hB : IsGalois ℚ (adjoin ℚ ({Real.sqrt 3} : Set ℝ)) :=
    QuadraticExample.quadratic_galois (Units.mk0 3 (by norm_num)) (by norm_num)
      nonsquare_three (Real.sqrt 3)
      (by simp)
  let := hA
  let := hB
  have hnormal : Normal ℚ L := L_eq_sup ▸ inferInstance
  let := hnormal
  exact ⟨inferInstance, hdegree, { to_isSeparable := inferInstance, to_normal := inferInstance }⟩

/-- Each automorphism acts by signs on the two generators, so has square one. -/
lemma aut_square (σ : L ≃ₐ[ℚ] L) : σ ^ 2 = 1 := by
  have hfix (r : L) (n : ℚ) (hr : r ^ 2 = algebraMap ℚ L n) : σ (σ r) = r := by
    have hh : (σ r) ^ 2 = r ^ 2 := by
      rw [← map_pow, hr, AlgEquiv.commutes]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h | h
    · rw [h, h]
    · rw [h, map_neg, h, neg_neg]
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext ℚ
  intro x hx
  rcases Set.mem_insert_iff.mp hx with h | h
  · subst x
    change σ (σ u) = u
    exact hfix u 2 (by simpa using u_sq)
  · have h := Set.mem_singleton_iff.mp h
    subst x
    change σ (σ v) = v
    exact hfix v 3 (by simpa using v_sq)

theorem galois_group : GaloisGroup := by
  let : FiniteDimensional ℚ L := degree_and_galois.1
  let : IsGalois ℚ L := degree_and_galois.2.2
  have hcard : Nat.card (L ≃ₐ[ℚ] L) = 2 ^ 2 :=
    (IsGalois.card_aut_eq_finrank ℚ L).trans degree_four
  rcases Ch06.PrimeSquareClassification.prime_square_models
    (L ≃ₐ[ℚ] L) 2 Nat.prime_two hcard with h | h
  · obtain ⟨e⟩ := h
    have hh := congrArg e (aut_square (e.symm (Multiplicative.ofAdd (1 : ZMod 4))))
    have he : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1 := by
      simpa only [map_pow, MulEquiv.apply_symm_apply, map_one] using hh
    exact False.elim ((by decide : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1) he)
  · exact h

unseal Nat.sqrt.iter in
lemma three_fields_distinct : E2 ≠ E3 ∧ E2 ≠ E6 ∧ E3 ≠ E6 := by
  have h32 : v ∉ E2 := by
    apply root_not_mem_quadratic (Units.mk0 2 (by norm_num)) nonsquare_two
      (3 : ℚ) nonsquare_three
    · simpa only [Units.val_mk0, show (2 : ℚ) * 3 = 6 by norm_num] using nonsquare_six
    · simpa using u_sq
    · simpa using v_sq
  have h62 : u * v ∉ E2 := by
    apply root_not_mem_quadratic (Units.mk0 2 (by norm_num)) nonsquare_two
      (6 : ℚ) nonsquare_six
    · norm_num
      decide
    · simpa using u_sq
    · simpa using uv_sq
  have h63 : u * v ∉ E3 := by
    apply root_not_mem_quadratic (Units.mk0 3 (by norm_num)) nonsquare_three
      (6 : ℚ) nonsquare_six
    · norm_num
      decide
    · simpa using v_sq
    · simpa using uv_sq
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply h32
    rw [h]
    exact mem_adjoin_simple_self ℚ v
  · intro h
    apply h62
    rw [h]
    exact mem_adjoin_simple_self ℚ (u * v)
  · intro h
    apply h63
    rw [h]
    exact mem_adjoin_simple_self ℚ (u * v)

/-- Counting closed subsets of the four-element group is a finite kernel computation. -/
private abbrev KleinModel := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private abbrev ClosedFinsets (G : Type*) [Group G] [Fintype G] [DecidableEq G] :=
  {s : Finset G // 1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ (∀ a ∈ s, a⁻¹ ∈ s)}

private noncomputable def subgroupFinsetEquiv (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Subgroup G ≃ ClosedFinsets G where
  toFun H := by
    classical
    refine ⟨(H : Set G).toFinset, ?_⟩
    simp only [Set.mem_toFinset]
    exact ⟨H.one_mem, fun a ha b hb => H.mul_mem ha hb, fun a ha => H.inv_mem ha⟩
  invFun s :=
    { carrier := s.val
      one_mem' := s.property.1
      mul_mem' := fun ha hb => s.property.2.1 _ ha _ hb
      inv_mem' := fun ha => s.property.2.2 _ ha }
  left_inv H := by
    classical
    ext x
    simp
  right_inv s := by
    classical
    apply Subtype.ext
    ext x
    simp

lemma klein_subgroup_card : Nat.card (Subgroup KleinModel) = 5 := by
  rw [Nat.card_congr (subgroupFinsetEquiv KleinModel)]
  let : DecidablePred (fun s : Finset KleinModel => 1 ∈ s ∧
      (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ (∀ a ∈ s, a⁻¹ ∈ s)) := by
    intro s
    change Decidable (1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ (∀ a ∈ s, a⁻¹ ∈ s))
    exact @instDecidableAnd _ _
      (inferInstance : Decidable (1 ∈ s))
      (@instDecidableAnd _ _
        (inferInstance : Decidable (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s))
        (inferInstance : Decidable (∀ a ∈ s, a⁻¹ ∈ s)))
  change Nat.card (ClosedFinsets KleinModel) = 5
  rw [Nat.card_eq_fintype_card]
  decide

lemma intermediate_field_card : Nat.card (IntermediateField ℚ L) = 5 := by
  let : FiniteDimensional ℚ L := degree_and_galois.1
  let : IsGalois ℚ L := degree_and_galois.2.2
  obtain ⟨e, _, _⟩ := FundamentalCorrespondence.fundamental_correspondence ℚ L
  obtain ⟨f⟩ := galois_group
  calc
    Nat.card (IntermediateField ℚ L) = Nat.card (Subgroup (L ≃ₐ[ℚ] L)) :=
      Nat.card_congr e.toEquiv
    _ = Nat.card (Subgroup KleinModel) := Nat.card_congr f.mapSubgroup.toEquiv
    _ = 5 := klein_subgroup_card

/-- The five distinct fields exhaust the lattice, by the Galois correspondence. -/
theorem intermediate_fields : IntermediateFields := by
  classical
  obtain ⟨hd2, hd3, hd6⟩ := quadratic_degrees
  obtain ⟨h23, h26, h36⟩ := three_fields_distinct
  have hbot (E : IntermediateField ℚ L) (hd : Module.finrank ℚ E = 2) : E ≠ ⊥ := by
    intro h
    subst E
    rw [IntermediateField.finrank_bot] at hd
    omega
  have htop (E : IntermediateField ℚ L) (hd : Module.finrank ℚ E = 2) : E ≠ ⊤ := by
    intro h
    subst E
    rw [IntermediateField.finrank_top', degree_four] at hd
    omega
  have hb2 := hbot E2 hd2
  have hb3 := hbot E3 hd3
  have hb6 := hbot E6 hd6
  have ht2 := htop E2 hd2
  have ht3 := htop E3 hd3
  have ht6 := htop E6 hd6
  have hbt : (⊥ : IntermediateField ℚ L) ≠ ⊤ := by
    intro h
    have hh := bot_eq_top_iff_finrank_eq_one.mp h
    rw [degree_four] at hh
    norm_num at hh
  let : Finite (IntermediateField ℚ L) :=
    Nat.finite_of_card_ne_zero (by rw [intermediate_field_card]; decide)
  let : Fintype (IntermediateField ℚ L) := Fintype.ofFinite _
  have huniv : ({⊥, ⊤, E2, E3, E6} : Finset (IntermediateField ℚ L)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, intermediate_field_card]
    simp [h23, h26, h36, hb2.symm, hb3.symm, hb6.symm,
      ht2.symm, ht3.symm, ht6.symm, hbt]
  refine ⟨hd2, hd3, hd6, h23, h26, h36, hb2, ht2, hb3, ht3, hb6, ht6, ?_⟩
  intro E
  constructor
  · rintro ⟨hEb, hEt⟩
    have hmem : E ∈ ({⊥, ⊤, E2, E3, E6} : Finset (IntermediateField ℚ L)) := by
      rw [huniv]
      exact Finset.mem_univ E
    simpa [hEb, hEt] using hmem
  · rintro (rfl | rfl | rfl)
    · exact ⟨hb2, ht2⟩
    · exact ⟨hb3, ht3⟩
    · exact ⟨hb6, ht6⟩

/-- Inclusion in the real ambient field identifies the internal quadratic fields. -/
theorem embedded_fields : EmbeddedFields := by
  refine ⟨?_, ?_, ?_⟩
  · change (adjoin ℚ {u}).map L.val = adjoin ℚ ({Real.sqrt 2} : Set ℝ)
    rw [adjoin_map, Set.image_singleton]
    rfl
  · change (adjoin ℚ {v}).map L.val = adjoin ℚ ({Real.sqrt 3} : Set ℝ)
    rw [adjoin_map, Set.image_singleton]
    rfl
  · change (adjoin ℚ {u * v}).map L.val = adjoin ℚ ({Real.sqrt 6} : Set ℝ)
    rw [adjoin_map, Set.image_singleton]
    change adjoin ℚ {((u * v : L) : ℝ)} = adjoin ℚ ({Real.sqrt 6} : Set ℝ)
    rw [product_root]

end D07.Ch14.BiquadraticExample
