import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedAlcoveVertices
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedAlcoveVertices

open LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems
open scoped BigOperators Matrix

open private foldedDirectionTable foldedTable_mem foldedTable_surjective
  normalizedFoldedRoot_apply from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

universe u

private def direction (i : Fin 48) : FoldedRootDirection :=
  ⟨foldedDirectionTable i, foldedTable_mem i⟩

/-- The two long and then the two doubled short simple directions. -/
private def simpleDirection (i : Fin 4) : FoldedRootDirection :=
  direction (![28, 25, 24, 33] i)

/-- The negative of the highest normalized root, with doubled vector `(-2, 0, 0, 0)`. -/
private def highestOpposite : FoldedRootDirection := direction 3

private def highestCoefficients : Fin 4 → ℚ := ![2, 4, 3, 2]

private theorem highestCoefficients_pos (i : Fin 4) : 0 < highestCoefficients i := by
  fin_cases i <;> decide

/-- Coordinates dual to the four normalized finite simple roots. -/
private def simpleCoordinates : (Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun x := ![x 1 - x 2, x 2 - x 3, 2 * x 3, x 0 - x 1 - x 2 - x 3]
  invFun y := ![y 3 + y 0 + 2 * y 1 + 3 * y 2 / 2, y 0 + y 1 + y 2 / 2,
    y 1 + y 2 / 2, y 2 / 2]
  left_inv x := by
    funext j
    fin_cases j <;> simp
    ring
  right_inv y := by
    funext j
    fin_cases j <;> simp <;> ring
  map_add' x y := by
    funext j
    fin_cases j <;> simp <;> ring
  map_smul' c x := by
    funext j
    fin_cases j <;> simp [smul_eq_mul] <;> ring

private theorem simpleCoordinates_ray (c : ℚ) (i : Fin 4) (hc : 0 < c) :
    0 < simpleCoordinates (unfoldApartment (fun _ : Fin 6 => c)) i := by
  fin_cases i <;> simp [simpleCoordinates, unfoldApartment] <;> linarith

private def rootCoefficients (a : FoldedRootDirection) : Fin 4 → ℚ :=
  let v j := (normalizedFoldedNumerator a.val j : ℚ) / 2
  ![v 0 + v 1, 2 * v 0 + v 1 + v 2, (3 * v 0 + v 1 + v 2 + v 3) / 2, v 0]

private theorem rootCoordinates (a : FoldedRootDirection) (x : Fin 4 → ℚ) :
    normalizedFoldedRoot ℚ a x = ∑ i, rootCoefficients a i * simpleCoordinates x i := by
  rw [normalizedFoldedRoot_apply]
  simp [rootCoefficients, simpleCoordinates, Fin.sum_univ_succ]
  ring

private theorem simpleCoefficients :
    ∀ i, rootCoefficients (simpleDirection i) = Pi.single i 1 := by
  decide +kernel

private theorem oppositeCoefficients : rootCoefficients highestOpposite = -highestCoefficients := by
  decide +kernel

private theorem coefficientBounds (a : FoldedRootDirection) :
    (∀ i, -(highestCoefficients i) ≤ rootCoefficients a i) ∧
    ((∀ i, 0 ≤ rootCoefficients a i) ∨ (∀ i, rootCoefficients a i ≤ 0)) := by
  have table : ∀ k : Fin 48,
      (∀ i, -(highestCoefficients i) ≤ rootCoefficients (direction k) i) ∧
      ((∀ i, 0 ≤ rootCoefficients (direction k) i) ∨
        (∀ i, rootCoefficients (direction k) i ≤ 0)) := by
    decide +kernel
  obtain ⟨k, hk⟩ := foldedTable_surjective a
  exact (show direction k = a from Subtype.ext hk) ▸ table k

section Simplex

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]
variable {A : ApartmentRoots ℚ V J} {p : V}

/-- A simplex described by its barycentric coordinates has a unique
opposite vertex for each simple wall. -/
private theorem verticesOfBarycentricCoordinates {I : Type*} [Fintype I] [Nontrivial I]
    (facet : I → J × ℤ) (hFacet : Function.Injective facet)
    (hPos : ∀ i, A.positive p (facet i))
    (weight : I → ℚ) (hWeight : ∀ i, 0 < weight i)
    (coord : V → I → ℚ) (hCoord : Function.Injective coord)
    (hValue : ∀ x i, coord x i = weight i * A.wallValue (facet i) x)
    (hSum : ∀ x, ∑ i, coord x i = 1)
    (hRealize : ∀ v : I → ℚ, ∑ i, v i = 1 → ∃ x, coord x = v)
    (hCombination : ∀ b, A.positive p b →
      ∃ k : I → ℚ, (∀ i, 0 ≤ k i) ∧ (∃ i, 0 < k i) ∧
        (∀ i, (∀ j ≠ i, k j = 0) → b = facet i) ∧
        ∀ x, A.wallValue b x = ∑ i, k i * coord x i) :
    ∀ a : A.SimpleWall p, ∃! x : V,
      (∀ b, A.positive p b → 0 ≤ A.wallValue b x) ∧
      ∀ b : A.SimpleWall p, A.wallValue b.val x = 0 ↔ b ≠ a := by
  classical
  have hZero (x : V) (i : I) : A.wallValue (facet i) x = 0 ↔ coord x i = 0 := by
    rw [hValue, mul_eq_zero_iff_left (hWeight i).ne']
  have hClosed (x : V) :
      (∀ b, A.positive p b → 0 ≤ A.wallValue b x) ↔ ∀ i, 0 ≤ coord x i := by
    constructor
    · intro h i
      rw [hValue]
      exact mul_nonneg (hWeight i).le (h (facet i) (hPos i))
    · intro h b hb
      obtain ⟨k, hk, _, _, hEval⟩ := hCombination b hb
      rw [hEval]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hk i) (h i))
  have hSimple (i : I) : A.IsSimple p (facet i) := by
    let z : I → ℚ := fun j => if j = i then 0 else 1
    have hz (j : I) : 0 ≤ z j := by
      by_cases h : j = i <;> simp [z, h]
    obtain ⟨j, hj⟩ := exists_ne i
    have hSumPos : 0 < ∑ j, z j :=
      Finset.sum_pos' (fun j _ => hz j) ⟨j, Finset.mem_univ _, by simp [z, hj]⟩
    let v : I → ℚ := fun j => z j / ∑ k, z k
    obtain ⟨x, hx⟩ := hRealize v (by
      change (∑ j, z j / ∑ k, z k) = 1
      rw [← Finset.sum_div, div_self hSumPos.ne'])
    refine ⟨hPos i, x, (hZero x i).mpr (by simp [hx, v, z]), ?_⟩
    intro b hb hne
    obtain ⟨k, hk, _, hSupport, hEval⟩ := hCombination b hb
    have h : ∃ j, j ≠ i ∧ 0 < k j := by
      by_contra! hn
      exact hne (hSupport i fun j hj => le_antisymm (hn j hj) (hk j))
    obtain ⟨j, hj, hkj⟩ := h
    change 0 < A.wallValue b x
    rw [hEval, hx]
    exact Finset.sum_pos' (fun l _ => mul_nonneg (hk l) (div_nonneg (hz l) hSumPos.le))
      ⟨j, Finset.mem_univ _, mul_pos hkj (by simp [v, z, hj, hSumPos])⟩
  have hCovers (b : A.SimpleWall p) : ∃ i, facet i = b.val := by
    by_contra! hne
    obtain ⟨hb, x, hx, hPanel⟩ := b.property
    obtain ⟨k, hk, ⟨i, hi⟩, _, hEval⟩ := hCombination b.val hb
    have hCoordPos (j : I) : 0 < coord x j :=
      (hValue x j).symm ▸ mul_pos (hWeight j) (hPanel _ (hPos j) (hne j))
    change A.wallValue b.val x = 0 at hx
    rw [hEval] at hx
    exact (Finset.sum_pos' (fun j _ => mul_nonneg (hk j) (hCoordPos j).le)
      ⟨i, Finset.mem_univ _, mul_pos hi (hCoordPos i)⟩).ne' hx
  intro a
  obtain ⟨i, hi⟩ := hCovers a
  let v : I → ℚ := fun j => if j = i then 1 else 0
  obtain ⟨x, hx⟩ := hRealize v (by simp [v])
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · apply (hClosed x).mpr
    intro j
    rw [hx]
    by_cases h : j = i <;> simp [v, h]
  · intro b
    obtain ⟨j, hj⟩ := hCovers b
    rw [← hj, hZero, hx]
    have heq : j = i ↔ b = a := by
      rw [← hFacet.eq_iff, hj, hi, Subtype.coe_inj]
    by_cases h : j = i <;> simp [v, h, ← heq]
  · intro y hy
    have hOther (j : I) (hj : j ≠ i) : coord y j = 0 :=
      (hZero y j).mp ((hy.2 ⟨facet j, hSimple j⟩).mpr
        (fun h => hj (hFacet ((congrArg Subtype.val h).trans hi.symm))))
    have hOne : coord y i = 1 :=
      (Finset.sum_eq_single i (fun j _ hj => hOther j hj) (by simp)).symm.trans (hSum y)
    apply hCoord
    rw [hx]
    funext j
    by_cases hj : j = i
    · simp [v, hj, hOne]
    · simp [v, hj, hOther j hj]

end Simplex

private theorem simpleDirection_injective : Function.Injective simpleDirection := by
  change ∀ i j : Fin 4, simpleDirection i = simpleDirection j → i = j
  decide +kernel

/-- The normalized dual F₄ alcove has a unique vertex opposite each bounding wall. -/
theorem foldedAlcoveVertices : Specs.ExceptionalFoldedAlcoveVertices.Statement.{u} := by
  classical
  intro V _ _ A e hTransport hReduced c hc p hSmall
  let s := e.symm.trans simpleCoordinates
  let θ := highestCoefficients
  have hRoot (a : FoldedRootDirection) (x : V) :
      A.root a x = ∑ i, rootCoefficients a i * s x i := by
    simpa only [s, LinearEquiv.trans_apply, e.apply_symm_apply] using
      (hTransport a (e.symm x)).trans (rootCoordinates a (e.symm x))
  have hSimple (i : Fin 4) (x : V) : A.root (simpleDirection i) x = s x i := by
    rw [hRoot, simpleCoefficients]
    simp [Pi.single_apply, ite_mul]
  have hHighest (x : V) : A.root highestOpposite x = -∑ i, θ i * s x i := by
    rw [hRoot, oppositeCoefficients]
    simp [θ, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have hRay (i : Fin 4) : 0 < s p i := by
    simpa only [p, s, LinearEquiv.trans_apply, e.symm_apply_apply] using
      simpleCoordinates_ray c i hc
  let facet : Option (Fin 4) → FoldedRootDirection × ℤ :=
    fun i => i.rec (highestOpposite, 1) (fun j => (simpleDirection j, 0))
  have hFacet : Function.Injective facet := by
    intro i j h
    cases i <;> cases j <;> simp_all [facet, simpleDirection_injective.eq_iff]
  have hSome (x : V) (i : Fin 4) : A.wallValue (facet (some i)) x = s x i := by
    change A.root (simpleDirection i) x + ((0 : ℤ) : ℚ) = _
    simp [hSimple]
  have hNone (x : V) : A.wallValue (facet none) x = 1 - ∑ i, θ i * s x i := by
    change A.root highestOpposite x + ((1 : ℤ) : ℚ) = _
    simp [hHighest, sub_eq_add_neg, add_comm]
  have hPos (i : Option (Fin 4)) : A.positive p (facet i) := by
    change 0 < A.wallValue (facet i) p
    cases i with
    | none =>
      change 0 < A.root highestOpposite p + ((1 : ℤ) : ℚ)
      have h := (abs_lt.mp (hSmall highestOpposite)).1
      push_cast
      linarith
    | some i => rw [hSome]; exact hRay i
  let coord (x : V) (i : Option (Fin 4)) : ℚ :=
    i.rec (1 - ∑ j, θ j * s x j) (fun j => θ j * s x j)
  have hSum (x : V) : ∑ i, coord x i = 1 := by
    rw [Fintype.sum_option]
    change 1 - (∑ j, θ j * s x j) + (∑ j, θ j * s x j) = 1
    ring
  refine verticesOfBarycentricCoordinates facet hFacet hPos (fun i => i.rec 1 θ)
    (fun i => i.rec zero_lt_one highestCoefficients_pos) coord ?_ ?_ hSum ?_ ?_
  · intro x y h
    apply s.injective
    funext i
    exact mul_left_cancel₀ (highestCoefficients_pos i).ne' (congrFun h (some i))
  · intro x i
    cases i <;> simp [coord, hNone, hSome]
  · intro v hv
    obtain ⟨x, hx⟩ := s.surjective (fun i => v (some i) / θ i)
    have hSomeCoord (i : Fin 4) : coord x (some i) = v (some i) := by
      change θ i * s x i = _
      rw [congrFun hx i, mul_div_cancel₀ _ (highestCoefficients_pos i).ne']
    have h := (hSum x).trans hv.symm
    rw [Fintype.sum_option, Fintype.sum_option] at h
    simp_rw [hSomeCoord] at h
    exact ⟨x, funext fun i => i.rec (add_right_cancel h) hSomeCoord⟩
  · rintro ⟨a, m⟩ ha
    change 0 < A.root a p + (m : ℚ) at ha
    have hm : 0 ≤ m := by
      by_contra! h
      have hm' : (m : ℚ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      linarith only [ha, hm', (abs_lt.mp (hSmall a)).2]
    let r := rootCoefficients a
    have hLower : ∀ i, -θ i ≤ r i := (coefficientBounds a).1
    have hPositive (h : m = 0) (i : Fin 4) : 0 ≤ r i := by
      rcases (coefficientBounds a).2 with hNonneg | hNonpos
      · exact hNonneg i
      · rw [h, Int.cast_zero, add_zero, hRoot] at ha
        exact (ha.not_ge (Finset.sum_nonpos fun j _ =>
          mul_nonpos_of_nonpos_of_nonneg (hNonpos j) (hRay j).le)).elim
    let k : Option (Fin 4) → ℚ :=
      fun i => i.rec (m : ℚ) (fun j => (m : ℚ) + r j / θ j)
    have hNonneg (i : Option (Fin 4)) : 0 ≤ k i := by
      cases i with
      | none =>
        change (0 : ℚ) ≤ (m : ℚ)
        exact_mod_cast hm
      | some i =>
        change 0 ≤ (m : ℚ) + r i / θ i
        by_cases h : m = 0
        · simpa [h] using div_nonneg (hPositive h i) (highestCoefficients_pos i).le
        · have hm' : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
          have hr : -1 ≤ r i / θ i :=
            (le_div_iff₀ (highestCoefficients_pos i)).mpr (by simpa using hLower i)
          linarith
    have hEval (x : V) : A.wallValue (a, m) x = ∑ i, k i * coord x i := by
      rw [Fintype.sum_option]
      change A.root a x + (m : ℚ) = (m : ℚ) * (1 - ∑ i, θ i * s x i) +
        ∑ i, ((m : ℚ) + r i / θ i) * (θ i * s x i)
      rw [hRoot]
      simp only [add_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hTerm (i : Fin 4) : r i / θ i * (θ i * s x i) = r i * s x i := by
        rw [← mul_assoc, div_mul_cancel₀ _ (highestCoefficients_pos i).ne']
      simp_rw [hTerm]
      change (∑ i, r i * s x i) + (m : ℚ) = _
      ring
    have hStrict : ∃ i, 0 < k i := by
      apply Classical.byContradiction
      intro h
      have hz (i : Option (Fin 4)) : k i = 0 :=
        le_antisymm (not_lt.mp (fun hi => h ⟨i, hi⟩)) (hNonneg i)
      change 0 < A.wallValue (a, m) p at ha
      rw [hEval] at ha
      simp [hz] at ha
    refine ⟨k, hNonneg, hStrict, ?_, hEval⟩
    intro i hSupport
    cases i with
    | none =>
      have hmPos : 0 < m := by
        obtain ⟨i, hi⟩ := hStrict
        cases i with
        | none =>
          change (0 : ℚ) < (m : ℚ) at hi
          exact_mod_cast hi
        | some i =>
          rw [hSupport (some i) (by simp)] at hi
          exact (lt_irrefl _ hi).elim
      have hr (i : Fin 4) : r i = -(m : ℚ) * θ i := by
        have h := hSupport (some i) (by simp)
        change (m : ℚ) + r i / θ i = 0 at h
        apply (div_eq_iff (highestCoefficients_pos i).ne').mp
        linarith only [h]
      have hmOne : m = 1 := by
        have h := hLower 0
        rw [hr] at h
        have hle : (m : ℚ) ≤ 1 := by
          nlinarith only [h, highestCoefficients_pos 0]
        have hmLe : m ≤ 1 := by exact_mod_cast hle
        omega
      have he : a = highestOpposite := by
        apply hReduced.1
        ext x
        rw [hRoot, hHighest]
        change (∑ i, r i * s x i) = _
        simp [hr, hmOne, neg_mul, Finset.sum_neg_distrib]
      exact Prod.ext he hmOne
    | some i =>
      have hmZero : m = 0 := by
        have h := hSupport none (by simp)
        change (m : ℚ) = 0 at h
        exact_mod_cast h
      have hz (j : Fin 4) (hj : j ≠ i) : r j = 0 := by
        have h := hSupport (some j) (by simpa using hj)
        change (m : ℚ) + r j / θ j = 0 at h
        rw [hmZero, Int.cast_zero, zero_add] at h
        exact (div_eq_zero_iff.mp h).resolve_right (highestCoefficients_pos j).ne'
      have he : A.root a = r i • A.root (simpleDirection i) := by
        ext x
        rw [hRoot]
        change (∑ j, r j * s x j) = _
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [hz j hj, zero_mul]) (by simp)]
        simp [hSimple, smul_eq_mul]
      rcases hReduced.2 (simpleDirection i) a (r i) he with he | he
      · exact Prod.ext he.symm hmZero
      · rw [he, LinearMap.neg_apply, hSimple, hmZero, Int.cast_zero, add_zero] at ha
        linarith only [ha, hRay i]

end LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedAlcoveVertices
