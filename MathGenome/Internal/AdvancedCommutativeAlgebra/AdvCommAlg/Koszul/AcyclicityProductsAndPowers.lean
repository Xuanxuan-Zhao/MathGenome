import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Cone
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Functoriality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.AcyclicityProductsAndPowers

/-! Products and positive powers in a fixed coordinate, RK-15.
The proof uses the accepted cone exact sequence and works degree by degree. -/
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The cone exact sequence characterizes vanishing by surjectivity and
injectivity on the two adjacent homology modules. -/
theorem append_homology_vanish_iff (x : List R) (a : R) (n : ℕ) :
    Subsingleton (homology M (x ++ [a]) (n+1)) ↔
      Function.Surjective (fun z : homology M x (n+1) => a • z) ∧
      Function.Injective (fun z : homology M x n => a • z) := by
  let S := koszulAppendConeSequence M x a
  constructor
  · intro h
    have : Subsingleton ((coefficientComplex M (x ++ [a])).homology (n+1)) := h
    constructor
    · intro z
      exact (S.exact_multiply_inclusion (n+1) z).mp (Subsingleton.elim _ _)
    · have hz : ∀ z : homology M x n, a • z = 0 → z = 0 := by
        intro z hz
        obtain ⟨w, hw⟩ := (S.exact_projection_multiply n z).mp hz
        rw [← hw, Subsingleton.elim w 0, map_zero]
      intro z w he
      exact sub_eq_zero.mp (hz (z-w) (by simp [smul_sub, he]))
  · rintro ⟨hs, hi⟩
    have hz : ∀ z : homology M (x ++ [a]) (n+1), z = 0 := by
      intro z
      have hp : (S.projection n).hom z = 0 := by
        apply hi
        have he := (S.exact_projection_multiply n ((S.projection n).hom z)).mpr ⟨z, rfl⟩
        change a • ((S.projection n).hom z) = 0 at he
        simpa only [smul_zero] using he
      obtain ⟨w, hw⟩ := (S.exact_inclusion_projection n z).mp hp
      obtain ⟨t, ht⟩ := hs w
      rw [← hw]
      exact (S.exact_multiply_inclusion (n+1) w).mpr ⟨t, ht⟩
    exact ⟨fun z w => (hz z).trans (hz w).symm⟩

/-- Multiplication of last coordinates preserves vanishing in any positive degree. -/
theorem append_homology_product (x : List R) (a b : R) (n : ℕ)
    (ha : Subsingleton (homology M (x ++ [a]) (n+1)))
    (hb : Subsingleton (homology M (x ++ [b]) (n+1))) :
    Subsingleton (homology M (x ++ [a*b]) (n+1)) := by
  obtain ⟨hsa, hia⟩ := (append_homology_vanish_iff M x a n).mp ha
  obtain ⟨hsb, hib⟩ := (append_homology_vanish_iff M x b n).mp hb
  apply (append_homology_vanish_iff M x (a*b) n).mpr
  simpa only [mul_smul, Function.comp_def] using And.intro (hsa.comp hsb) (hia.comp hib)


private def moveCoordinate (pre post : List R) (a : R) :
    Fin (pre ++ a :: post).length ≃ Fin ((pre ++ post) ++ [a]).length where
  toFun i := ⟨if i.val < pre.length then i.val else
    if i.val = pre.length then pre.length + post.length else i.val - 1, by
      have hi := i.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      split <;> (try split) <;> omega⟩
  invFun j := ⟨if j.val < pre.length then j.val else
    if j.val < pre.length + post.length then j.val + 1 else pre.length, by
      have hj := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      split <;> (try split) <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt
    simp only [List.length_append, List.length_cons] at hi
    dsimp
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    have hj := j.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    dsimp
    split_ifs <;> omega

omit [CommRing R] in
private theorem moveCoordinate_get (pre post : List R) (a : R)
    (i : Fin (pre ++ a :: post).length) :
    ((pre ++ post) ++ [a]).get (moveCoordinate pre post a i) =
      (pre ++ a :: post).get i := by
  have hi := i.isLt
  simp only [List.length_append, List.length_cons] at hi
  by_cases h₁ : i.val < pre.length
  · simp [moveCoordinate, h₁, List.get_eq_getElem]
  · by_cases h₂ : i.val = pre.length
    · simp [moveCoordinate, h₂, List.get_eq_getElem]
    · have h₃ : pre.length < i.val := by omega
      have h₄ : i.val - 1 < (pre ++ post).length := by simp; omega
      simp only [List.get_eq_getElem, moveCoordinate, Equiv.coe_fn_mk, h₁, ↓reduceIte,
        h₂, List.getElem_append_left h₄]
      rw [List.getElem_append_right (by omega : pre.length ≤ i.val - 1),
        List.getElem_append_right (by omega : pre.length ≤ i.val), List.getElem_cons]
      simp only [show i.val - pre.length ≠ 0 by omega, ↓reduceDIte]
      congr 1; omega

/-- Moving the selected coordinate past the suffix preserves its homology. -/
theorem coordinate_homology_vanish_iff (pre post : List R) (a : R) (q : ℕ) :
    Subsingleton (homology M (pre ++ a :: post) q) ↔
      Subsingleton (homology M ((pre ++ post) ++ [a]) q) := by
  obtain ⟨e⟩ := coefficient_permutation_iso M (pre ++ a :: post)
    ((pre ++ post) ++ [a]) (moveCoordinate pre post a) (moveCoordinate_get pre post a)
  exact (HomologicalComplex.homologyMapIso e q).toLinearEquiv.toEquiv.subsingleton_congr

/-- The product assertion in every positive degree and every position. -/
theorem homology_product : Specs.AdvCommAlg.Koszul.homologyProduct.{u,v} := by
  intro R _ M _ _ pre post a b n ha hb
  apply (coordinate_homology_vanish_iff M pre post (a*b) (n+1)).mpr
  exact append_homology_product M (pre ++ post) a b n
    ((coordinate_homology_vanish_iff M pre post a (n+1)).mp ha)
    ((coordinate_homology_vanish_iff M pre post b (n+1)).mp hb)

/-- Repeated multiplication gives arbitrary positive powers at one position. -/
theorem homology_power : Specs.AdvCommAlg.Koszul.homologyPower.{u,v} := by
  intro R _ M _ _ pre post a k n hk ha
  cases k with
  | zero => omega
  | succ k =>
    clear hk
    induction k with
    | zero => simpa only [Nat.zero_add, pow_one] using ha
    | succ k ih =>
      rw [pow_succ]
      exact homology_product M pre post (a^(k+1)) a n ih ha

/-- Power several positions, retaining an arbitrary initial part of the list. -/
theorem homology_powers_append (x : List R) (ks : List ℕ) (n : ℕ)
    (hlen : x.length = ks.length) (hpos : ∀ k ∈ ks, 0 < k)
    (pre : List R) (h : Subsingleton (homology M (pre ++ x) (n+1))) :
    Subsingleton (homology M (pre ++ List.zipWith (fun a k => a^k) x ks) (n+1)) := by
  induction x generalizing ks pre with
  | nil =>
    cases ks with
    | nil => simpa using h
    | cons k ks => simp at hlen
  | cons a x ih =>
    cases ks with
    | nil => simp at hlen
    | cons k ks =>
      have hk : 0 < k := hpos k (by simp)
      have ht : ∀ j ∈ ks, 0 < j := fun j hj => hpos j (by simp [hj])
      have hp := homology_power M pre x a k n hk h
      have hh := ih ks (by simpa using hlen) ht (pre ++ [a^k])
        (by simpa only [List.append_assoc, List.singleton_append] using hp)
      simpa only [List.zipWith_cons_cons, List.append_assoc, List.singleton_append] using hh

/-- Simultaneous, independently chosen positive powers. -/
theorem homology_powers : Specs.AdvCommAlg.Koszul.homologyPowers.{u,v} := by
  intro R _ M _ _ x ks n hlen hpos h
  simpa only [List.nil_append] using homology_powers_append M x ks n hlen hpos [] h


/-- Degree-one acyclicity is preserved by a product in one coordinate. -/
theorem degree_one_product : Specs.AdvCommAlg.Koszul.degreeOneProduct.{u,v} := by
  intro R _ M _ _ pre post a b
  exact homology_product M pre post a b 0

/-- Degree-one acyclicity is preserved by a positive power in one coordinate. -/
theorem degree_one_power : Specs.AdvCommAlg.Koszul.degreeOnePower.{u,v} := by
  intro R _ M _ _ pre post a k
  exact homology_power M pre post a k 0

/-- Degree-one acyclicity is preserved by independently powering any positions. -/
theorem degree_one_powers : Specs.AdvCommAlg.Koszul.degreeOnePowers.{u,v} := by
  intro R _ M _ _ x ks
  exact homology_powers M x ks 0

/-- Acyclicity in all positive degrees is preserved by products. -/
theorem positive_product : Specs.AdvCommAlg.Koszul.positiveProduct.{u,v} := by
  intro R _ M _ _ pre post a b ha hb q hq
  cases q with
  | zero => omega
  | succ n => exact homology_product M pre post a b n (ha _ hq) (hb _ hq)

/-- Acyclicity in all positive degrees is preserved by one positive power. -/
theorem positive_power : Specs.AdvCommAlg.Koszul.positivePower.{u,v} := by
  intro R _ M _ _ pre post a k hk ha q hq
  cases q with
  | zero => omega
  | succ n => exact homology_power M pre post a k n hk (ha _ hq)

/-- Acyclicity in all positive degrees is preserved by independently powering
several coordinates; exponents equal to one retain the remaining coordinates. -/
theorem positive_powers : Specs.AdvCommAlg.Koszul.positivePowers.{u,v} := by
  intro R _ M _ _ x ks hlen hpos ha q hq
  cases q with
  | zero => omega
  | succ n => exact homology_powers M x ks n hlen hpos (ha _ hq)

end AdvCommAlg.Koszul
