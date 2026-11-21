import MathGenome.Internal.Specs.D07.Ch06.SmallOrderExamplesOrderSix
import MathGenome.Internal.D07.Ch01.Presentations
import MathGenome.Internal.D07.Ch04.SemidirectRecognition
import MathGenome.Internal.D07.Ch06.OrderPqCyclicCriterion
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group

noncomputable section
namespace D07.Ch06.SmallOrderExamplesOrderSix
open Specs.D07.Ch06.SmallOrderExamplesOrderSix
open Specs.D07.Ch04.SemidirectRecognition (C2 C3 threeCycle transposition)
open scoped Pointwise
universe u

lemma presentation_relations : a ^ 3 = 1 ∧ b ^ 2 = 1 ∧ b * a * b = a⁻¹ := by
  have h1 := D07.Ch01.Presentations.relators_vanish Bool relators
    (FreeGroup.of false ^ 3) (by simp [relators])
  have h2 := D07.Ch01.Presentations.relators_vanish Bool relators
    (FreeGroup.of true ^ 2) (by simp [relators])
  have h3 := D07.Ch01.Presentations.relators_vanish Bool relators
    (FreeGroup.of true * FreeGroup.of false * FreeGroup.of true * FreeGroup.of false)
    (by simp [relators])
  change a ^ 3 = 1 at h1
  change b ^ 2 = 1 at h2
  change b * a * b * a = 1 at h3
  exact ⟨h1, h2, (eq_inv_iff_mul_eq_one).mpr h3⟩

/-- Reduction of the six normal forms by left multiplication by either generator. -/
lemma normal_form_steps {G : Type*} [Group G] (x y : G)
    (hx : x ^ 3 = 1) (hy : y ^ 2 = 1) (hyx : y * x * y = x⁻¹) :
    (∀ z, (∃ (i : Fin 3) (j : Fin 2), z = x ^ i.val * y ^ j.val) →
      ∃ (i : Fin 3) (j : Fin 2), x * z = x ^ i.val * y ^ j.val) ∧
    (∀ z, (∃ (i : Fin 3) (j : Fin 2), z = x ^ i.val * y ^ j.val) →
      ∃ (i : Fin 3) (j : Fin 2), y * z = x ^ i.val * y ^ j.val) := by
  have hxinv : x⁻¹ = x ^ 2 := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    simpa [← pow_succ] using hx
  have hyinv : y⁻¹ = y := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hy
  have hmove : y * x = x ^ 2 * y := by
    calc
      y * x = (y * x * y) * y⁻¹ := by group
      _ = x ^ 2 * y := by rw [hyx, hxinv, hyinv]
  have hmove2 : y * x ^ 2 = x * y := by
    calc
      y * x ^ 2 = (y * x) * x := by simp [pow_two, mul_assoc]
      _ = (x ^ 2 * y) * x := by rw [hmove]
      _ = x ^ 2 * (y * x) := by group
      _ = x ^ 2 * (x ^ 2 * y) := by rw [hmove]
      _ = (x ^ 3 * x) * y := by group
      _ = x * y := by rw [hx, one_mul]
  constructor
  · rintro z ⟨i, j, rfl⟩
    fin_cases i
    · exact ⟨1, j, by simp⟩
    · exact ⟨2, j, by simp [pow_two, mul_assoc]⟩
    · exact ⟨0, j, by simp [← mul_assoc, ← pow_succ', hx]⟩
  · rintro z ⟨i, j, rfl⟩
    fin_cases i <;> fin_cases j
    · exact ⟨0, 1, by simp⟩
    · exact ⟨0, 0, by simpa [pow_two] using hy⟩
    · exact ⟨2, 1, by simpa using hmove⟩
    · refine ⟨2, 0, ?_⟩
      have h : y * (x * y) = x ^ 2 := by
        rw [← mul_assoc, hmove, mul_assoc, ← pow_two, hy, mul_one]
      simpa using h
    · exact ⟨1, 1, by simpa using hmove2⟩
    · refine ⟨1, 0, ?_⟩
      have h : y * (x ^ 2 * y) = x := by
        rw [← mul_assoc, hmove2, mul_assoc, ← pow_two, hy, mul_one]
      simpa using h

lemma presentation_normal_form (z : P) :
    ∃ (i : Fin 3) (j : Fin 2), z = a ^ i.val * b ^ j.val := by
  obtain ⟨ha, hb, hba⟩ := presentation_relations
  obtain ⟨stepa, stepb⟩ := normal_form_steps a b ha hb hba
  have ha_inv : a⁻¹ = a ^ 2 := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    simpa [← pow_succ] using ha
  have hb_inv : b⁻¹ = b := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hb
  have hz : z ∈ Subgroup.closure (Set.range (PresentedGroup.of (rels := relators))) := by
    rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top z
  apply Subgroup.closure_induction_left (p := fun z _ =>
    ∃ (i : Fin 3) (j : Fin 2), z = a ^ i.val * b ^ j.val) ?_ ?_ ?_ hz
  · exact ⟨0, 0, by simp; rfl⟩
  · rintro x ⟨s, rfl⟩ y _ hy
    cases s
    · exact stepa y hy
    · exact stepb y hy
  · rintro x ⟨s, rfl⟩ y _ hy
    cases s
    · change ∃ (i : Fin 3) (j : Fin 2), a⁻¹ * y = a ^ i.val * b ^ j.val
      rw [ha_inv, pow_two, mul_assoc]
      exact stepa _ (stepa y hy)
    · change ∃ (i : Fin 3) (j : Fin 2), b⁻¹ * y = a ^ i.val * b ^ j.val
      rw [hb_inv]
      exact stepb y hy

lemma powers_represent {G : Type*} [Group G] [Finite G] (x z : G) (n : ℕ)
    (hx : orderOf x = n) (hz : z ∈ Subgroup.zpowers x) :
    ∃ i : Fin n, z = x ^ i.val := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hz
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hz
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, he.symm⟩

lemma complement_normal_forms {G : Type*} [Group G] [Finite G] (x y : G)
    (hx : orderOf x = 3) (hy : orderOf y = 2)
    (hc : (Subgroup.zpowers x).IsComplement' (Subgroup.zpowers y)) (z : G) :
    ∃ (i : Fin 3) (j : Fin 2), z = x ^ i.val * y ^ j.val := by
  have hz : z ∈ (Subgroup.zpowers x : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [hc.mul_eq]; trivial
  obtain ⟨n, hn, h, hh, rfl⟩ := hz
  obtain ⟨i, rfl⟩ := powers_represent x n 3 hx hn
  obtain ⟨j, rfl⟩ := powers_represent y h 2 hy hh
  exact ⟨i, j, rfl⟩

lemma relators_evaluate {G : Type*} [Group G] (x y : G)
    (hx : x ^ 3 = 1) (hy : y ^ 2 = 1) (hxy : y * x * y = x⁻¹) :
    ∀ r ∈ relators, FreeGroup.lift (fun s : Bool => if s then y else x) r = 1 := by
  intro r hr
  simp only [relators, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using hx
  · simpa using hy
  · simp [hxy]

lemma presentation_map {G : Type*} [Group G] (x y : G)
    (hx : x ^ 3 = 1) (hy : y ^ 2 = 1) (hxy : y * x * y = x⁻¹) :
    ∃ f : P →* G, f a = x ∧ f b = y := by
  obtain ⟨f, hf⟩ := (D07.Ch01.Presentations.induced_hom_exists_iff Bool relators G
    (fun s : Bool => if s then y else x)).mpr (relators_evaluate x y hx hy hxy)
  exact ⟨f, hf false, hf true⟩

lemma map_surjective {G : Type*} [Group G] (x y : G)
    (hf : ∀ z : G, ∃ (i : Fin 3) (j : Fin 2), z = x ^ i.val * y ^ j.val)
    (f : P →* G) (hfa : f a = x) (hfb : f b = y) : Function.Surjective f := by
  intro z
  obtain ⟨i, j, rfl⟩ := hf z
  exact ⟨a ^ i.val * b ^ j.val, by simp [hfa, hfb]⟩

instance presentation_finite : Finite P :=
  Finite.of_surjective (fun ij : Fin 3 × Fin 2 => a ^ ij.1.val * b ^ ij.2.val)
    (fun z => by obtain ⟨i, j, h⟩ := presentation_normal_form z; exact ⟨(i,j), h.symm⟩)

lemma presentation_card_le : Nat.card P ≤ 6 := by
  have h := Nat.card_le_card_of_surjective
    (fun ij : Fin 3 × Fin 2 => a ^ ij.1.val * b ^ ij.2.val)
    (fun z => by obtain ⟨i,j,h⟩ := presentation_normal_form z; exact ⟨(i,j), h.symm⟩)
  simpa using h

lemma presentation_symmetric_equiv :
    ∃ e : P ≃* S3, e a = threeCycle ∧ e b = transposition := by
  have ha : threeCycle ^ 3 = 1 := by decide
  have hb : transposition ^ 2 = 1 := by decide
  have hba : transposition * threeCycle * transposition = threeCycle⁻¹ := by decide
  obtain ⟨f, hfa, hfb⟩ := presentation_map threeCycle transposition ha hb hba
  have hsurj : Function.Surjective f := map_surjective _ _
    (complement_normal_forms _ _ D07.Ch04.SemidirectRecognition.threeCycle_order
      D07.Ch04.SemidirectRecognition.transposition_order
      D07.Ch04.SemidirectRecognition.s3_complement) f hfa hfb
  have hcard : Nat.card P = Nat.card S3 := by
    apply Nat.le_antisymm
    · exact presentation_card_le.trans_eq D07.Ch04.SemidirectRecognition.s3_card.symm
    · exact Nat.card_le_card_of_surjective f hsurj
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hsurj, hcard⟩), hfa, hfb⟩

lemma presentation_card : Nat.card P = 6 := by
  obtain ⟨e, _, _⟩ := presentation_symmetric_equiv
  exact (Nat.card_congr e.toEquiv).trans D07.Ch04.SemidirectRecognition.s3_card

theorem presentation_identification : PresentationIdentification := by
  obtain ⟨h1,h2,h3⟩ := presentation_relations
  exact ⟨h1,h2,h3,presentation_normal_form,presentation_card,presentation_symmetric_equiv⟩

theorem presentation_semidirect : PresentationSemidirect := by
  obtain ⟨e, hea, heb⟩ := presentation_symmetric_equiv
  obtain ⟨φ, hinv, hne, E, hEa, hEb⟩ := D07.Ch04.SemidirectRecognition.symmetric_split
  refine ⟨φ, hinv, hne, e.trans E.symm, ?_, ?_⟩
  · apply E.injective
    simpa [hea] using hEa.symm
  · apply E.injective
    simpa [heb] using hEb.symm

lemma order_six_generators (G : Type u) [Group G] [Finite G] (hcard : Nat.card G = 6) :
    ∃ x y : G, orderOf x = 3 ∧ orderOf y = 2 ∧
      (Subgroup.zpowers x).Normal ∧
      (Subgroup.zpowers x).IsComplement' (Subgroup.zpowers y) := by
  obtain ⟨x, hx⟩ := Cauchy.exists_element_order_eq G 3 (by decide) (by rw [hcard]; decide)
  obtain ⟨y, hy⟩ := Cauchy.exists_element_order_eq G 2 (by decide) (by rw [hcard]; decide)
  have hN : Nat.card (Subgroup.zpowers x) = 3 := (Nat.card_zpowers x).trans hx
  have hH : Nat.card (Subgroup.zpowers y) = 2 := (Nat.card_zpowers y).trans hy
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [hN, hcard] at h
    omega
  refine ⟨x,y,hx,hy,Subgroup.normal_of_index_eq_two hindex, ?_⟩
  apply Subgroup.isComplement'_of_coprime
  · rw [hN, hH, hcard]
  · rw [hN, hH]; decide

theorem splitting : Splitting.{u} := by
  intro G _ _ hcard
  obtain ⟨x,y,hx,hy,hN,hc⟩ := order_six_generators G hcard
  let := hN
  exact ⟨x,y,hx,hy,hN,hc,
    D07.Ch04.SemidirectRecognition.recognition G _ _ hc.disjoint.eq_bot hc.mul_eq⟩

/-- On the cyclic subgroup of order three a conjugate generator is either
itself or its inverse. The identity is excluded by injectivity of conjugation. -/
lemma conjugation_dichotomy {G : Type*} [Group G] [Finite G] (x y : G)
    (hx : orderOf x = 3) (hy : orderOf y = 2) (hN : (Subgroup.zpowers x).Normal) :
    Commute x y ∨ y * x * y = x⁻¹ := by
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyinv : y⁻¹ = y := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hy2
  have hxinv : x ^ 2 = x⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa [← pow_succ] using hx3
  have hmem := hN.conj_mem x (Subgroup.mem_zpowers x) y
  obtain ⟨i, hi⟩ := powers_represent x (y * x * y⁻¹) 3 hx hmem
  fin_cases i
  · have hbad : x = 1 := by
      have hh : y * x * y⁻¹ = 1 := by simpa using hi
      have he := congrArg (fun z : G => y⁻¹ * z * y) hh
      simpa [mul_assoc] using he
    rw [hbad, orderOf_one] at hx
    contradiction
  · left
    have hh : y * x * y⁻¹ = x := by simpa using hi
    have he := congrArg (fun z : G => z * y) hh
    exact (by simpa [mul_assoc] using he : y * x = x * y).symm
  · right
    simpa [hyinv, hxinv] using hi

lemma cyclic_of_commuting_generators {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 6) (x y : G) (hx : orderOf x = 3) (hy : orderOf y = 2)
    (hc : Commute x y) : Nonempty (G ≃* C6) := by
  have ho : orderOf (x * y) = 6 := by
    rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx,hy]; decide), hx, hy]
  let : IsCyclic G := isCyclic_of_orderOf_eq_card (x * y) (ho.trans hcard.symm)
  have e := (zmodCyclicMulEquiv (G := G) inferInstance).symm
  rw [hcard] at e
  exact ⟨e⟩

lemma presentation_equiv_of_factors {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 6) (x y : G) (hx : orderOf x = 3) (hy : orderOf y = 2)
    (hc : (Subgroup.zpowers x).IsComplement' (Subgroup.zpowers y))
    (hxy : y * x * y = x⁻¹) : ∃ e : P ≃* G, e a = x ∧ e b = y := by
  obtain ⟨f,hfa,hfb⟩ := presentation_map x y (hx ▸ pow_orderOf_eq_one x)
    (hy ▸ pow_orderOf_eq_one y) hxy
  have hsurj := map_surjective x y (complement_normal_forms x y hx hy hc) f hfa hfb
  refine ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hsurj, presentation_card.trans hcard.symm⟩), hfa, hfb⟩

theorem classification : Classification.{u} := by
  intro G _ _ hcard
  obtain ⟨x,y,hx,hy,hN,hc⟩ := order_six_generators G hcard
  rcases conjugation_dichotomy x y hx hy hN with hcomm | hinv
  · exact Or.inl (cyclic_of_commuting_generators hcard x y hx hy hcomm)
  · obtain ⟨e,_,_⟩ := presentation_equiv_of_factors hcard x y hx hy hc hinv
    obtain ⟨E,_,_⟩ := presentation_symmetric_equiv
    exact Or.inr ⟨e.symm.trans E⟩

theorem models : Models := by
  refine ⟨by simp [C6], D07.Ch04.SemidirectRecognition.s3_card, ?_⟩
  rintro ⟨e⟩
  have h := congrArg e (mul_comm (e.symm threeCycle) (e.symm transposition))
  have hne : threeCycle * transposition ≠ transposition * threeCycle := by decide
  exact hne (by simpa only [map_mul, e.apply_symm_apply] using h)

theorem nonabelian_correspondence : NonabelianCorrespondence.{u} := by
  intro G _ _ hcard hnon
  obtain ⟨x,y,hx,hy,hN,hc⟩ := order_six_generators G hcard
  have hinv : y * x * y = x⁻¹ := by
    rcases conjugation_dichotomy x y hx hy hN with hcomm | hinv
    · obtain ⟨e⟩ := cyclic_of_commuting_generators hcard x y hx hy hcomm
      obtain ⟨v,w,hvw⟩ := hnon
      exact False.elim (hvw (e.injective (by simpa only [map_mul] using mul_comm (e v) (e w))))
    · exact hinv
  obtain ⟨e,hea,heb⟩ := presentation_equiv_of_factors hcard x y hx hy hc hinv
  obtain ⟨φ,hφ,hne,E,hEa,hEb⟩ := presentation_semidirect
  refine ⟨x,y,hx,hy,hinv,⟨e,hea,heb⟩,φ,hφ,hne,E.symm.trans e,?_,?_⟩
  · change e (E.symm _) = x
    rw [← hEa, E.symm_apply_apply, hea]
  · change e (E.symm _) = y
    rw [← hEb, E.symm_apply_apply, heb]

end D07.Ch06.SmallOrderExamplesOrderSix
