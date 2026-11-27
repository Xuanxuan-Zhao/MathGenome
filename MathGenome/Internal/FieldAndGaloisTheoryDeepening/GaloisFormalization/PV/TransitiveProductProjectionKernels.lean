import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.TransitiveProductProjectionKernels

/-! Projection kernels of a stable subring of a transitive finite product. -/

open scoped BigOperators nonZeroDivisors

set_option backward.isDefEq.respectTransparency false

namespace GaloisFormalization.PV.ProjectionKernels

universe u v

variable {ι : Type u} {K : ι → Type v} [∀ i, Field (K i)]
variable {S₀ : Subring (∀ i, K i)}

private theorem ofCoordinate_surjective (S : Subring (∀ i, K i)) :
    Function.Surjective (ofCoordinate S) := by
  rintro ⟨P, i, rfl⟩
  exact ⟨i, rfl⟩

private theorem mem_ofCoordinate_iff (i : ι) (x : S₀) :
    x ∈ (ofCoordinate S₀ i).val ↔ coordinate S₀ i x = 0 :=
  RingHom.mem_ker

private theorem coordinate_ext {x y : S₀} (h : ∀ i, coordinate S₀ i x = coordinate S₀ i y) :
    x = y :=
  Subtype.ext (funext h)

section Permutation

variable [hfinite : Finite ι] [hnonempty : Nonempty ι]
variable (σ : (∀ i, K i) ≃+* (∀ i, K i)) (p : Equiv.Perm ι)
variable (hσ : PermutesFactors σ p) (hp : Transitive p)
variable (S : Operator.Subring (Operator.difference σ))

include hfinite hnonempty hσ hp

-- Keep the same finite nonempty ambient product hypotheses for the projection lemmas.
set_option linter.unusedSectionVars false in
/-- Transport of distinct projection kernels by the ambient permutation. -/
theorem permuted :
    ∃ q : Equiv.Perm (Index S.val), Transitive q ∧
      (∀ i, q (ofCoordinate S.val i) = ofCoordinate S.val (p i)) ∧
      ∀ P, (q P).val = P.val.map (restrict σ S).toRingHom := by
  let E := (restrict σ S).idealComapOrderIso.symm
  have hmap (i : ι) : E (kernel S.val i) = kernel S.val (p i) := by
    change (kernel S.val i).map (restrict σ S).toRingHom = _
    refine (Ideal.map_comap_of_equiv (restrict σ S)).trans ?_
    ext x
    change σ.symm x.val i = 0 ↔ x.val (p i) = 0
    simpa only [RingEquiv.apply_symm_apply] using (hσ (σ.symm x.val) i).symm
  let f (P : Index S.val) : Index S.val := ⟨E P.val, by
    obtain ⟨i, hi⟩ := P.property
    exact ⟨p i, (hmap i).symm.trans (congrArg E hi)⟩⟩
  have hf (i : ι) : f (ofCoordinate S.val i) = ofCoordinate S.val (p i) :=
    Subtype.ext (hmap i)
  have hf_inj : Function.Injective f := fun _ _ h =>
    Subtype.ext (E.injective (congrArg Subtype.val h))
  have hf_surj : Function.Surjective f := by
    intro P
    obtain ⟨i, rfl⟩ := ofCoordinate_surjective S.val P
    exact ⟨ofCoordinate S.val (p.symm i), by rw [hf, p.apply_symm_apply]⟩
  let q := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨q, ?_, hf, fun _ => rfl⟩
  intro P T
  obtain ⟨i, rfl⟩ := ofCoordinate_surjective S.val P
  obtain ⟨j, rfl⟩ := ofCoordinate_surjective S.val T
  obtain ⟨n, hn⟩ := hp i j
  have hsem : Function.Semiconj (ofCoordinate S.val) p q := fun i => (hf i).symm
  exact ⟨n, ((hsem.iterate_right n) i).symm.trans (congrArg (ofCoordinate S.val) hn)⟩

/-- No distinct kernels lie above one another. -/
theorem incomparable (P T : Index S.val) (hne : P ≠ T) : ¬ P.val ≤ T.val := by
  obtain ⟨q, hq, _, hmap⟩ := permuted σ p hσ hp S
  have hstep (A B : Index S.val) : q A ≤ q B ↔ A ≤ B := by
    change (q A).val ≤ (q B).val ↔ A.val ≤ B.val
    rw [hmap, hmap]
    exact (restrict σ S).idealComapOrderIso.symm.le_iff_le
  have hiter (n : ℕ) (A B : Index S.val) : (q^[n]) A ≤ (q^[n]) B ↔ A ≤ B := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, ih]
  obtain ⟨M, _, hM⟩ := Finite.exists_le_maximal (p := fun _ : Index S.val => True) (a := P) trivial
  obtain ⟨n, hn⟩ := hq M P
  obtain ⟨B, rfl⟩ := q.surjective.iterate n T
  intro h
  have hMB : M ≤ B := (hiter n M B).mp (hn ▸ h)
  have heq : M = B := le_antisymm hMB (hM.2 trivial hMB)
  exact hne (hn.symm.trans (congrArg (q^[n]) heq))

/-- One finite product separates a given projection kernel from all the others. -/
theorem exists_test (P : Index S.val) : ∃ t : S.val, IsTest P t := by
  classical
  have h (T : Index S.val) (hne : T ≠ P) : ∃ a : S.val, a ∈ T.val ∧ a ∉ P.val := by
    by_contra! hall
    exact incomparable σ p hσ hp S T P hne (fun _ ha => hall _ ha)
  choose a ha using h
  let b (T : Index S.val) : S.val := if h : T ≠ P then a T h else 1
  refine ⟨∏ T ∈ Finset.univ.erase P, b T, ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := ofCoordinate_surjective S.val P
    rw [mem_ofCoordinate_iff, map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro T hT
    have hne := Finset.ne_of_mem_erase hT
    rw [show b T = a T hne from dite_eq_left hne]
    exact fun hz => (ha T hne).2 ((mem_ofCoordinate_iff i _).mpr hz)
  · intro T hne
    have hb : b T ∈ T.val := by simpa only [b, dite_eq_left hne] using (ha T hne).1
    obtain ⟨i, rfl⟩ := ofCoordinate_surjective S.val T
    rw [mem_ofCoordinate_iff, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
      ((mem_ofCoordinate_iff _ _).mp hb)

/-- A regular element of the subring has no zero field coordinate. -/
theorem mem_nonZeroDivisors_iff_coordinates (x : S.val) :
    x ∈ (S.val : Type _)⁰ ↔ ∀ i, coordinate S.val i x ≠ 0 := by
  rw [mem_nonZeroDivisors_iff_left]
  constructor
  · intro hx i hi
    obtain ⟨t, ht, ht'⟩ := exists_test σ p hσ hp S (ofCoordinate S.val i)
    have hxt : x * t = 0 := by
      apply coordinate_ext
      intro j
      rw [map_mul, map_zero]
      by_cases hij : ofCoordinate S.val j = ofCoordinate S.val i
      · have hj : x ∈ (ofCoordinate S.val j).val :=
          hij.symm ▸ (mem_ofCoordinate_iff i x).mpr hi
        rw [(mem_ofCoordinate_iff j x).mp hj, zero_mul]
      · rw [(mem_ofCoordinate_iff j t).mp (ht' _ hij), mul_zero]
    exact ht (hx t hxt ▸ Ideal.zero_mem _)
  · intro hx y hxy
    apply coordinate_ext
    intro i
    have hi := congrArg (coordinate S.val i) hxy
    rw [map_mul, map_zero] at hi
    rw [map_zero]
    exact (mul_eq_zero.mp hi).resolve_left (hx i)

/-- Regularity in the subring is equivalent to invertibility in the ambient product. -/
theorem mem_nonZeroDivisors_iff_isUnit (x : S.val) :
    x ∈ (S.val : Type _)⁰ ↔ IsUnit x.val := by
  rw [mem_nonZeroDivisors_iff_coordinates σ p hσ hp S, Pi.isUnit_iff]
  simp only [isUnit_iff_ne_zero]
  rfl

open scoped Classical in
/-- Normalizing the separating elements by their sum gives the characteristic idempotents. -/
theorem exists_orthogonal_idempotents (hregular : RegularElementsAreUnits (S.val : Type _)) :
    ∃ (t : Index S.val → S.val) (s : (S.val : Type _)ˣ) (e : Index S.val → S.val),
      (∀ P, IsTest P (t P)) ∧
      (s : S.val) = ∑ P, t P ∧
      (∀ P, e P = t P * (↑s⁻¹ : S.val)) ∧
      (∀ P i, coordinate S.val i (e P) = if ofCoordinate S.val i = P then 1 else 0) ∧
      (∀ P, e P * e P = e P) ∧
      (∀ P T, P ≠ T → e P * e T = 0) ∧
      ∑ P, e P = 1 := by
  choose t ht using exists_test σ p hσ hp S
  have hsum (i : ι) :
      coordinate S.val i (∑ P, t P) = coordinate S.val i (t (ofCoordinate S.val i)) := by
    rw [map_sum, Finset.sum_eq_single (ofCoordinate S.val i)]
    · intro P _ hne
      exact (mem_ofCoordinate_iff i _).mp ((ht P).2 _ hne.symm)
    · simp
  obtain ⟨s, hs⟩ : IsUnit (∑ P, t P) :=
    hregular _ ((mem_nonZeroDivisors_iff_coordinates σ p hσ hp S _).mpr fun i => by
      rw [hsum]
      exact fun hz => (ht (ofCoordinate S.val i)).1 ((mem_ofCoordinate_iff i _).mpr hz))
  let e (P : Index S.val) : S.val := t P * ↑s⁻¹
  have he (P : Index S.val) (i : ι) :
      coordinate S.val i (e P) = if ofCoordinate S.val i = P then 1 else 0 := by
    change coordinate S.val i (t P * ↑s⁻¹) = _
    rw [map_mul]
    by_cases hi : ofCoordinate S.val i = P
    · rw [ite_eq_left hi, ← hi, ← hsum, ← hs, ← map_mul, Units.mul_inv, map_one]
    · rw [ite_eq_right hi, (mem_ofCoordinate_iff i _).mp ((ht P).2 _ hi), zero_mul]
  refine ⟨t, s, e, ht, hs, fun _ => rfl, he, ?_, ?_, ?_⟩
  · intro P
    apply coordinate_ext
    intro i
    rw [map_mul, he]
    split <;> simp
  · intro P T hne
    apply coordinate_ext
    intro i
    rw [map_mul, map_zero, he P, he T]
    by_cases hi : ofCoordinate S.val i = P
    · simp [hi, hne]
    · simp [hi]
  · change (∑ P, t P * (↑s⁻¹ : S.val)) = 1
    rw [← Finset.sum_mul, ← hs, Units.mul_inv]

/-- The quotient coordinates give the decomposition, and the operator transports them
by the ring equivalences induced on the quotients. -/
theorem decomposition (hregular : RegularElementsAreUnits (S.val : Type _)) :
    ∃ (q : Equiv.Perm (Index S.val)) (g : (S.val : Type _) ≃+* (∀ P : Index S.val, S.val ⧸ P.val))
      (τ : ∀ P : Index S.val, (S.val ⧸ P.val) ≃+* (S.val ⧸ (q P).val)),
      Transitive q ∧
      (∀ i, q (ofCoordinate S.val i) = ofCoordinate S.val (p i)) ∧
      (∀ P : Index S.val, IsField (S.val ⧸ P.val)) ∧
      (∀ (x : S.val) (P : Index S.val), g x P = Ideal.Quotient.mk P.val x) ∧
      ∀ (x : S.val) (P : Index S.val), g (restrict σ S x) (q P) = τ P (g x P) := by
  classical
  obtain ⟨_, _, e, _, _, _, he, _, _, _⟩ :=
    exists_orthogonal_idempotents σ p hσ hp S hregular
  have hquot (P T : Index S.val) :
      Ideal.Quotient.mk T.val (e P) = if T = P then 1 else 0 := by
    by_cases hTP : T = P
    · subst T
      rw [ite_eq_left rfl, ← map_one (Ideal.Quotient.mk P.val), Ideal.Quotient.eq]
      obtain ⟨i, rfl⟩ := ofCoordinate_surjective S.val P
      rw [mem_ofCoordinate_iff, map_sub, map_one, he, ite_eq_left rfl, sub_self]
    · rw [ite_eq_right hTP, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨i, rfl⟩ := ofCoordinate_surjective S.val T
      rw [mem_ofCoordinate_iff, he, ite_eq_right hTP]
  let f := RingHom.pi fun P : Index S.val => Ideal.Quotient.mk P.val
  have hf : Function.Bijective f := by
    constructor
    · refine (injective_iff_map_eq_zero f).mpr fun x hx => coordinate_ext fun i => ?_
      rw [map_zero]
      apply (mem_ofCoordinate_iff i x).mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact congrFun hx (ofCoordinate S.val i)
    · intro y
      choose x hx using fun P => Ideal.Quotient.mk_surjective (y P)
      refine ⟨∑ P, e P * x P, ?_⟩
      funext T
      change Ideal.Quotient.mk T.val (∑ P, e P * x P) = y T
      simp only [map_sum, map_mul, hquot]
      rw [Finset.sum_eq_single T]
      · simpa only [ite_true, one_mul] using hx T
      · intro P _ hne
        rw [ite_eq_right hne.symm, zero_mul]
      · simp
  have hfield (P : Index S.val) : IsField (S.val ⧸ P.val) := by
    refine ⟨⟨1, 0, ?_⟩, mul_comm, ?_⟩
    · intro hzero
      have hone : (1 : S.val) ∈ P.val :=
        Ideal.Quotient.eq_zero_iff_mem.mp ((map_one (Ideal.Quotient.mk P.val)).trans hzero)
      obtain ⟨i, rfl⟩ := ofCoordinate_surjective S.val P
      exact one_ne_zero ((map_one (coordinate S.val i)).symm.trans
        ((mem_ofCoordinate_iff i _).mp hone))
    · intro a ha
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      let y : S.val := x * e P + (1 - e P)
      have hu : IsUnit y := by
        apply hregular
        apply (mem_nonZeroDivisors_iff_coordinates σ p hσ hp S y).mpr
        intro i
        change coordinate S.val i (x * e P + (1 - e P)) ≠ 0
        simp only [map_add, map_sub, map_mul, map_one, he]
        by_cases hi : ofCoordinate S.val i = P
        · rw [ite_eq_left hi, mul_one, sub_self, add_zero]
          exact fun hz => ha (Ideal.Quotient.eq_zero_iff_mem.mpr
            (hi ▸ (mem_ofCoordinate_iff i x).mpr hz))
        · simp [hi]
      have hy : Ideal.Quotient.mk P.val y = Ideal.Quotient.mk P.val x := by
        change Ideal.Quotient.mk P.val (x * e P + (1 - e P)) = _
        simp only [map_add, map_sub, map_mul, map_one, hquot, ite_true,
          mul_one, sub_self, add_zero]
      obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
      refine ⟨Ideal.Quotient.mk P.val z, ?_⟩
      rw [← hy, ← map_mul, hz, map_one]
  obtain ⟨q, hq, hqp, hqmap⟩ := permuted σ p hσ hp S
  let τ (P : Index S.val) := Ideal.quotientEquiv P.val (q P).val (restrict σ S) (hqmap P)
  refine ⟨q, RingEquiv.ofBijective f hf, τ, hq, hqp, hfield, fun _ _ => rfl, ?_⟩
  intro x P
  exact (Ideal.quotientEquiv_mk P.val (q P).val (restrict σ S) (hqmap P) x).symm

end Permutation

/-- In a single field factor a unital subring with the regular-unit property is a field. -/
theorem subring_isField_of_regular_isUnit {L : Type v} [Field L] (S : Subring L)
    (h : RegularElementsAreUnits (S : Type v)) : IsField (S : Type v) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel ha := isUnit_iff_exists_inv.mp (h _ (mem_nonZeroDivisors_iff_ne_zero.mpr ha))

end GaloisFormalization.PV.ProjectionKernels
