import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Albert.SplitSpin

open Matrix SplitSpinSpecification
open scoped Matrix TensorProduct

noncomputable section

variable {m : ℕ} {R : Type*} [CommRing R]

private theorem dotProduct_left_add (x y z : Fin m → R) :
    (x + y) ⬝ᵥ z = x ⬝ᵥ z + y ⬝ᵥ z :=
  add_dotProduct _ _ _

theorem alternatingEntries : AlternatingEntriesType := by
  intro m R _ P
  let e : Fin m → Fin m → R := fun i => Pi.single i 1
  constructor
  · intro h
    have hd (i) : P i i = 0 := by
      simpa [e, single_dotProduct, mulVec_single_one] using h (e i)
    refine ⟨hd, fun i j => ?_⟩
    have hij := h (e i + e j)
    simp only [mulVec_add, dotProduct_add, dotProduct_left_add] at hij
    have hv : P j i + P i j = 0 := by
      simpa [e, single_dotProduct, mulVec_single_one, hd] using hij
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hv)
  · rintro ⟨hd, hs⟩ x
    classical
    have expand (s : Finset (Fin m)) :
        (∑ i ∈ s, (Pi.single i (x i) : Fin m → R)) ⬝ᵥ
          (P *ᵥ (∑ i ∈ s, (Pi.single i (x i) : Fin m → R))) = 0 := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, mulVec_add, dotProduct_add,
          dotProduct_left_add, dotProduct_left_add, ih, add_zero]
        have hh : Pᵀ = -P := by
          ext j k
          exact hs k j
        rw [← dotProduct_transpose_mulVec P (∑ j ∈ s, (Pi.single j (x j) : Fin m → R)),
          hh, neg_mulVec, dotProduct_neg]
        -- The term with two copies of the new coordinate is the diagonal entry.
        have hself : Pi.single i (x i) ⬝ᵥ (P *ᵥ Pi.single i (x i)) = 0 := by
          simp [single_dotProduct, mulVec_single, hd]
        change (Pi.single i (x i) ⬝ᵥ (P *ᵥ Pi.single i (x i)) + _) + _ = 0
        rw [hself, zero_add, add_neg_cancel]
    have hx : (∑ i : Fin m, (Pi.single i (x i) : Fin m → R)) = x := by
      ext i
      simp [Pi.single_apply]
    simpa only [hx] using expand Finset.univ

private theorem preserves_mul {g h : Matrix (PairIndex m) (PairIndex m) R}
    (hg : PreservesNorm g) (hh : PreservesNorm h) : PreservesNorm (g * h) := by
  intro v
  rw [← mulVec_mulVec, hg, hh]

@[simp] private theorem norm_elim (x y : Fin m → R) :
    hyperbolicNorm (Sum.elim x y) = x ⬝ᵥ y := rfl

private theorem block_norm (A B C D : Block m R) (x y : Fin m → R) :
    hyperbolicNorm (fromBlocks A B C D *ᵥ Sum.elim x y) =
      (A *ᵥ x + B *ᵥ y) ⬝ᵥ (C *ᵥ x + D *ᵥ y) := by
  rw [fromBlocks_mulVec]
  rfl

private theorem lower_preserves {P : Block m R} (hP : IsAlternating P) :
    PreservesNorm (lower P) := by
  intro v
  have hv : Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i
    cases i <;> rfl
  rw [← hv]
  rw [lower, block_norm, norm_elim]
  simp only [one_mulVec, zero_mulVec, add_zero, dotProduct_add]
  rw [hP, zero_add]

private theorem upper_preserves {Q : Block m R} (hQ : IsAlternating Q) :
    PreservesNorm (upper Q) := by
  intro v
  have hv : Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i
    cases i <;> rfl
  rw [← hv]
  rw [upper, block_norm, norm_elim]
  simp only [one_mulVec, zero_mulVec, zero_add, dotProduct_left_add]
  rw [dotProduct_comm (Q *ᵥ _), hQ, add_zero]

private theorem middle_pairing {A : Block m R} (hA : IsUnit A.det) (x y : Fin m → R) :
    (A *ᵥ x) ⬝ᵥ ((A⁻¹)ᵀ *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_transpose_mulVec, mulVec_mulVec, nonsing_inv_mul A hA, one_mulVec,
    dotProduct_comm]

private theorem middle_preserves {A : Block m R} (hA : IsUnit A.det) :
    PreservesNorm (middle A) := by
  intro v
  have hv : Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i
    cases i <;> rfl
  rw [← hv]
  rw [middle, block_norm, norm_elim]
  simp only [zero_mulVec, add_zero, zero_add, middle_pairing hA]

private theorem factor_blocks (A P Q : Block m R) :
    lower P * middle A * upper Q =
      fromBlocks A (A * Q) (P * A) (P * A * Q + (A⁻¹)ᵀ) := by
  simp [lower, middle, upper, fromBlocks_multiply]

private theorem lower_mul_lower (P P' : Block m R) :
    lower P * lower P' = lower (P + P') := by
  simp [lower, fromBlocks_multiply]

private theorem triangular_bottom {A B D : Block m R}
    (hA : IsUnit A.det) (h : PreservesNorm (fromBlocks A B 0 D)) :
    D = (A⁻¹)ᵀ := by
  have h₀ (y : Fin m → R) : (B *ᵥ y) ⬝ᵥ (D *ᵥ y) = 0 := by
    simpa [block_norm] using h (Sum.elim 0 y)
  have hpair (x y : Fin m → R) : (A *ᵥ x) ⬝ᵥ (D *ᵥ y) = x ⬝ᵥ y := by
    simpa [block_norm, dotProduct_left_add, h₀] using h (Sum.elim x y)
  apply mulVec_injective
  funext y i
  have hp := hpair (A⁻¹ *ᵥ Pi.single i 1) y
  rw [mulVec_mulVec, mul_nonsing_inv A hA, one_mulVec, single_dotProduct, one_mul] at hp
  exact hp.trans (by rw [dotProduct_comm (A⁻¹ *ᵥ _), ← dotProduct_transpose_mulVec, single_dotProduct, one_mul])

private theorem chart_fromBlocks {A B C D : Block m R} (hA : IsUnit A.det)
    (hg : PreservesNorm (fromBlocks A B C D)) :
    ∃! pq : Block m R × Block m R,
      IsAlternating pq.1 ∧ IsAlternating pq.2 ∧
        fromBlocks A B C D = lower pq.1 * middle A * upper pq.2 := by
  let P := C * A⁻¹
  let Q := A⁻¹ * B
  have hP : IsAlternating P := by
    intro x
    have h := hg (Sum.elim (A⁻¹ *ᵥ x) 0)
    rw [block_norm, norm_elim, mulVec_zero, mulVec_zero, add_zero, add_zero,
      mulVec_mulVec, mul_nonsing_inv A hA, one_mulVec, dotProduct_zero] at h
    simpa only [P, ← mulVec_mulVec] using h
  have hne : IsAlternating (-P) := by
    intro x
    rw [neg_mulVec, dotProduct_neg, hP, neg_zero]
  have hPA : P * A = C := by simp [P, Matrix.mul_assoc, nonsing_inv_mul A hA]
  have hAQ : A * Q = B := by simp [Q, ← Matrix.mul_assoc, mul_nonsing_inv A hA]
  have htri : lower (-P) * fromBlocks A B C D = fromBlocks A B 0 (-(P * B) + D) := by
    simp [lower, fromBlocks_multiply, neg_mul, hPA]
  have ht := preserves_mul (lower_preserves hne) hg
  rw [htri] at ht
  have hD := triangular_bottom hA ht
  have hfact : fromBlocks A B C D = lower P * middle A * upper Q := by
    rw [factor_blocks, fromBlocks_inj, hAQ, hPA]
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [← hD, ← hPA, Matrix.mul_assoc, hAQ]
    abel
  have hQ : IsAlternating Q := by
    intro y
    have h := ht (Sum.elim 0 y)
    rw [hD] at h
    have ht' : (B *ᵥ y) ⬝ᵥ ((A⁻¹)ᵀ *ᵥ y) = 0 := by
      simpa [block_norm] using h
    simpa only [← hAQ, ← mulVec_mulVec, middle_pairing hA, dotProduct_comm y] using ht'
  refine ⟨(P,Q), ⟨hP,hQ,hfact⟩, ?_⟩
  rintro ⟨P', Q'⟩ ⟨_, _, h⟩
  rw [factor_blocks, fromBlocks_inj] at h
  refine Prod.ext ?_ ?_
  · change P' = C * A⁻¹
    rw [h.2.2.1, mul_nonsing_inv_cancel_right A _ hA]
  · change Q' = A⁻¹ * B
    rw [h.2.1, nonsing_inv_mul_cancel_left A _ hA]

theorem orthogonalChart : OrthogonalChartType := by
  intro m R _ g hA
  generalize h : g.toBlocks₁₁ = A at hA ⊢
  constructor
  · intro hg
    have hblocks : fromBlocks A g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ = g := by
      rw [← h, fromBlocks_toBlocks]
    rw [← hblocks] at hg
    exact hblocks ▸ chart_fromBlocks hA hg
  · rintro ⟨⟨P, Q⟩, ⟨hP, hQ, rfl⟩, _⟩
    exact preserves_mul (preserves_mul (lower_preserves hP) (middle_preserves hA))
      (upper_preserves hQ)

private theorem scaleRow_det (i : Fin m) (t : R) (A : Block m R) :
    (scaleRow i t A).det = t * A.det := by
  simp [scaleRow, det_updateRow_smul]

private theorem scaleRow_scaleRow (i : Fin m) (s t : R) (A : Block m R) :
    scaleRow i s (scaleRow i t A) = scaleRow i (s * t) A := by
  ext j k
  by_cases h : j = i
  · subst j
    simp [scaleRow, smul_smul, mul_assoc]
  · simp [scaleRow, h]

theorem normalizeMiddle : NormalizeMiddleType := by
  intro m R _ i
  let inverse (p : {A : Block m R // A.det = 1} × Rˣ) : NormOneBlock m R :=
    ⟨(scaleRow i ((↑p.2⁻¹ : R) ^ 2) p.1.val, p.2), by
      simp only [scaleRow_det, p.1.property, mul_one, ← mul_pow, Units.mul_inv, one_pow]⟩
  let forward (p : NormOneBlock m R) : {A : Block m R // A.det = 1} × Rˣ :=
    (⟨scaleRow i ((p.val.2 : R) ^ 2) p.val.1, (scaleRow_det ..).trans p.property⟩, p.val.2)
  refine ⟨⟨forward, inverse, ?_, ?_⟩, fun p => ⟨rfl,rfl⟩⟩
  · intro p
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    change scaleRow i ((↑p.val.2⁻¹ : R) ^ 2)
      (scaleRow i ((p.val.2 : R) ^ 2) p.val.1) = p.val.1
    rw [scaleRow_scaleRow, ← mul_pow, Units.inv_mul, one_pow]
    simp [scaleRow]
  · intro p
    refine Prod.ext (Subtype.ext ?_) rfl
    change scaleRow i ((p.2 : R) ^ 2)
      (scaleRow i ((↑p.2⁻¹ : R) ^ 2) p.1.val) = p.1.val
    rw [scaleRow_scaleRow, ← mul_pow, Units.mul_inv, one_pow]
    simp [scaleRow]

theorem scalarKernel : ScalarKernelType := by
  intro m
  exact SpinFunctor.hyperbolicSchemeKernelSpecification (Pi.basisFun ℤ (Fin m))
    (hyperbolicBasis ℤ m)

open Polynomial in
theorem nonreducedMuTwo : NonreducedMuTwoType := by
  intro K _ h₂ h
  let p : K[X] := SpinSpecification.muTwoPolynomial K
  have hp : p.Monic := by
    exact (show (X ^ 2 - C (1 : K)).Monic from
      monic_X_pow_sub_C 1 (by decide : (2 : ℕ) ≠ 0))
  have hpdeg : p.natDegree = 2 := by
    dsimp [p]
    rw [SpinSpecification.muTwoPolynomial, ← C_1]
    exact natDegree_X_pow_sub_C
  have hn : AdjoinRoot.mk p (X - 1) ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt hp
    · rw [← C_1]
      exact X_sub_C_ne_zero 1
    · rw [← C_1, natDegree_X_sub_C, hpdeg]
      decide
  apply hn
  apply IsNilpotent.eq_zero
  use 2
  rw [← map_pow]
  have hpoly : (X - 1 : K[X]) ^ 2 = p := by
    change (X - 1 : K[X]) ^ 2 = X ^ 2 - 1
    have hc : (2 : K[X]) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg Polynomial.C h₂
    calc
      _ = (X ^ 2 - 2 * X + 1 : K[X]) := by ring
      _ = (X ^ 2 - 1 : K[X]) := by
        have hsum : (1 : K[X]) + 1 = 0 := by simpa only [one_add_one_eq_two] using hc
        rw [hc, zero_mul, sub_zero, eq_sub_iff_add_eq]
        rw [add_assoc, hsum, add_zero]
  rw [hpoly, AdjoinRoot.mk_self]

/-- The quadratic form induced by the dot product of the two coordinate blocks. -/
private def coordinateForm (S : Type*) [CommRing S] (m : ℕ) :
    QuadraticForm S (Lex (PairIndex m) → S) :=
  LinearMap.BilinMap.toQuadraticMap ((dotProductBilin S S : LinearMap.BilinForm S (Fin m → S)).compl₁₂
    (LinearMap.funLeft S S (fun i : Fin m => toLex (Sum.inl i : PairIndex m)))
    (LinearMap.funLeft S S (fun i : Fin m => toLex (Sum.inr i : PairIndex m))))

theorem vectorCoordinates : VectorCoordinatesType := by
  intro m S _ _ x
  let : Module ℤ S := Algebra.toModule
  let b := hyperbolicBasis ℤ m
  have h : (coordinateForm S m).comp (b.baseChange S).equivFun.toLinearMap =
      CliffordSpecification.coefficientForm S (integralForm m) b := by
    apply (CliffordModel.coefficient_form_unique S (integralForm m) b _).2
    intro v
    change hyperbolicNorm ((b.baseChange S).equivFun (1 ⊗ₜ[ℤ] v)) =
      algebraMap ℤ S (v.1 v.2)
    have hl (i : Fin m) : b.repr v (toLex (Sum.inl i)) = v.2 i := by
      change ((Pi.basisFun ℤ (Fin m)).dualBasis.prod (Pi.basisFun ℤ (Fin m))).repr
        v (Sum.inr i) = v.2 i
      simp
    have hr (i : Fin m) : b.repr v (toLex (Sum.inr i)) = v.1 (Pi.single i 1) := by
      change ((Pi.basisFun ℤ (Fin m)).dualBasis.prod (Pi.basisFun ℤ (Fin m))).repr
        v (Sum.inl i) = v.1 (Pi.single i 1)
      simp
    have hv : ∑ i : Fin m, v.2 i • (Pi.single i 1 : Fin m → ℤ) = v.2 := by
      simpa using (Pi.basisFun ℤ (Fin m)).sum_repr v.2
    change (∑ i : Fin m,
      (b.baseChange S).equivFun (1 ⊗ₜ[ℤ] v) (toLex (Sum.inl i : PairIndex m)) *
        (b.baseChange S).equivFun (1 ⊗ₜ[ℤ] v) (toLex (Sum.inr i : PairIndex m))) =
        algebraMap ℤ S (v.1 v.2)
    simp only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
    simp only [hl, hr, Algebra.smul_def, mul_one, ← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← hv]
    simp only [map_sum, map_smul, smul_eq_mul]
  exact (DFunLike.congr_fun h x).symm

private theorem switch_apply (J : Finset (Fin m)) (x y : Fin m → R) :
    signedSwitch m R J *ᵥ Sum.elim x y =
      Sum.elim (fun i => if i ∈ J then -y i else x i) (fun i => if i ∈ J then -x i else y i) := by
  rw [signedSwitch, fromBlocks_mulVec]
  funext i
  cases i with
  | inl i =>
    by_cases h : i ∈ J <;> simp [mulVec_diagonal, h]
  | inr i =>
    by_cases h : i ∈ J <;> simp [mulVec_diagonal, h]

theorem signedSwitchProperties : SignedSwitchType := by
  intro m R _ J
  have decompose (v : PairIndex m → R) :
      Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i
    cases i <;> rfl
  constructor
  · intro v
    rw [← decompose v, switch_apply, norm_elim, norm_elim]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i ∈ J <;> simp [h, mul_comm]
  · apply mulVec_injective
    funext v
    rw [← decompose v, ← mulVec_mulVec, switch_apply, switch_apply, one_mulVec]
    funext i
    cases i with
    | inl i =>
      by_cases h : i ∈ J <;> simp [h]
    | inr i =>
      by_cases h : i ∈ J <;> simp [h]

private def alternatingCoordinates (m : ℕ) (S : Type*) [CommRing S] :
    {P : Block m S // IsAlternating P} ≃ (AlternatingIndex m → S) where
  toFun P p := P.val p.val.1 p.val.2
  invFun f := ⟨of fun i j =>
    if h : i < j then f ⟨(i,j),h⟩ else if h' : j < i then -f ⟨(j,i),h'⟩ else 0,
    (alternatingEntries m S _).mpr ⟨by simp, by
      intro i j
      obtain h | rfl | h := lt_trichotomy i j
      · simp [h, not_lt_of_gt h]
      · simp
      · simp [h, not_lt_of_gt h]⟩⟩
  left_inv P := by
    apply Subtype.ext
    ext i j
    have hp := (alternatingEntries m S _).mp P.property
    obtain h | rfl | h := lt_trichotomy i j
    · simp [h]
    · simpa using (hp.1 i).symm
    · simpa [h, not_lt_of_gt h] using (hp.2 i j).symm
  right_inv f := by
    funext p
    simp [p.property]

theorem alternatingDimension : AlternatingDimensionType := by
  intro m
  have hc : Fintype.card (AlternatingIndex m) = m.choose 2 := by
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]
  refine ⟨hc, ?_⟩
  rw [hc]
  clear hc
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have hs : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    rw [Nat.succ_eq_add_one, hs]
    have h : m ≤ m ^ 2 := by
      cases m with
      | zero => simp
      | succ m => rw [pow_two, Nat.mul_succ]; omega
    change 2 * (m + m.choose 2) + (m ^ 2 + 2 * m + 1) =
      2 * (m ^ 2 + 2 * m + 1) - (m + 1)
    omega

theorem chartParameters : ChartParametersType := by
  intro m S _ i
  obtain ⟨e, he⟩ := normalizeMiddle m S i
  let E : ChartParameters m S ≃
      ({P : Block m S // IsAlternating P} × {Q : Block m S // IsAlternating Q} ×
        NormOneBlock m S) :=
    ⟨fun p => (⟨p.P,p.alternatingP⟩, ⟨p.Q,p.alternatingQ⟩, ⟨(p.A,p.u),p.normOne⟩),
     fun p => ⟨p.1.val, p.2.1.val, p.2.2.val.1, p.2.2.val.2,
       p.1.property, p.2.1.property, p.2.2.property⟩,
     fun _ => rfl, fun _ => rfl⟩
  refine ⟨E.trans (Equiv.prodCongr (alternatingCoordinates m S)
    (Equiv.prodCongr (alternatingCoordinates m S) e)), ?_⟩
  intro p
  exact ⟨fun _ => rfl, fun _ => rfl, he ⟨(p.A,p.u),p.normOne⟩⟩

theorem spinMatrix : SpinMatrixType := by
  intro m S _ _ a ha
  let q := integralForm m
  let b := hyperbolicBasis ℤ m
  let g := SpinFunctor.vectorAction q S b ⟨a, ha⟩
  have hg := SpinFunctor.vectorAction_characterization q S b ⟨a, ha⟩
  refine ⟨vectorMatrix m g, ⟨⟨g, hg, rfl⟩, ?_⟩, ?_⟩
  · intro v
    let d := (b.baseChange S).equivFun
    let x := d.symm (v : Lex (PairIndex m) → S)
    have hv : (d x : PairIndex m → S) = v := d.apply_symm_apply _
    have hmul : vectorMatrix m g *ᵥ (d x : PairIndex m → S) = d (g x) :=
      LinearMap.toMatrix_mulVec_repr _ _ _ _
    rw [← hv, hmul, ← vectorCoordinates, ← vectorCoordinates]
    exact SpinFunctor.vectorAction_preserves q S b ⟨a, ha⟩ x
  · rintro M ⟨⟨f, hf, rfl⟩, _⟩
    congr 1
    ext x
    have ⟨p, hp⟩ := CliffordModel.vector_summand q b
    have hproj : (p.baseChange S).comp (SpinSpecification.vectors q S) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hp, LinearMap.baseChange_id]
    have hvec : Function.Injective (SpinSpecification.vectors q S) :=
      Function.LeftInverse.injective (g := p.baseChange S)
        (fun x => LinearMap.congr_fun hproj x)
    exact hvec ((hf x).trans (hg x).symm)

theorem evenSwitchOverlap : EvenSwitchOverlapType := by
  intro m R _ J
  classical
  let I := J.val
  obtain ⟨k, hk⟩ := J.property
  let e : I ≃ Fin k ⊕ Fin k := Fintype.equivOfCardEq (by simpa [I, Fintype.card_coe] using hk)
  let p (i : I) : I := e.symm (Sum.swap (e i))
  let s (i : I) : R := Sum.elim (fun _ => 1) (fun _ => -1) (e i)
  have hp (i : I) : p (p i) = i := by simp [p]
  have hn (i : I) : p i ≠ i := by
    intro h
    have he : Sum.swap (e i) = e i := by simpa [p] using congrArg e h
    cases h' : e i <;> simp [h'] at he
  have hs (i : I) : s (p i) = -s i := by
    cases he : e i <;> simp [s, p, he]
  have hu (i : I) : IsUnit (s i) := by
    cases he : e i <;> simp [s, he]
  let t (i : Fin m) : Fin m := if h : i ∈ I then (p ⟨i,h⟩).val else i
  have ht_in (i : Fin m) (hi : i ∈ I) : t i ∈ I := by
    simp [t, hi]
  have ht : Function.Involutive t := by
    intro i
    by_cases h : i ∈ I
    · have h' : t i ∈ I := ht_in i h
      have heq : (⟨t i, h'⟩ : I) = p ⟨i,h⟩ := by
        apply Subtype.ext
        simp [t,h]
      conv_lhs => rw [show t (t i) = (p ⟨t i,h'⟩).val by simp only [t, h', dite_true]]
      rw [heq, hp]
    · simp [t,h]
  let τ := ht.toPerm t
  let P : Block m R := of fun i j =>
    if hi : i ∈ I then if j = t i then s ⟨i,hi⟩ else 0 else 0
  have hP : IsAlternating P := (alternatingEntries m R P).mpr ⟨by
    intro i
    by_cases h : i ∈ I
    · have hne : i ≠ t i := by
        intro h'
        apply hn (⟨i,h⟩ : I)
        apply Subtype.ext
        simpa [t,h] using h'.symm
      simp [P, h, hne]
    · simp [P, h], by
    intro i j
    by_cases hi : i ∈ I
    · by_cases hij : j = t i
      · subst j
        have heq : (⟨t i, ht_in i hi⟩ : I) = p ⟨i,hi⟩ := by
          apply Subtype.ext
          simp [t,hi]
        simp [P, hi, ht_in i hi, ht i, heq, hs]
      · have hji : i ≠ t j := fun h => hij (by rw [h, ht j])
        by_cases hj : j ∈ I <;> simp [P, hi, hj, hij, hji]
    · by_cases hj : j ∈ I
      · have hji : i ≠ t j := fun h => hi (h ▸ ht_in j hj)
        simp [P, hi, hj, hji]
      · simp [P, hi, hj]⟩
  refine ⟨P, hP, ?_⟩
  let w (i : Fin m) : R := if hi : i ∈ I then -s ⟨i,hi⟩ else 1
  have hB : (signedSwitch m R J.val * lower P).toBlocks₁₁ = diagonal w * τ.permMatrix R := by
    apply mulVec_injective
    funext v i
    rw [← mulVec_mulVec, permMatrix_mulVec, mulVec_diagonal]
    have h :=
      congrFun (show (signedSwitch m R J.val * lower P) *ᵥ Sum.elim v 0 =
          Sum.elim (fun i => if i ∈ I then -(P *ᵥ v) i else v i)
            (fun i => if i ∈ I then -v i else (P *ᵥ v) i) from by
          rw [← mulVec_mulVec, lower, fromBlocks_mulVec]
          simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, mulVec_zero, add_zero]
          exact switch_apply J.val v (P *ᵥ v)) (Sum.inl i)
    have hl :
        ((signedSwitch m R J.val * lower P) *ᵥ Sum.elim v 0) (Sum.inl i) =
          ((signedSwitch m R J.val * lower P).toBlocks₁₁ *ᵥ v) i := by
      generalize signedSwitch m R J.val * lower P = M
      conv_lhs => rw [← fromBlocks_toBlocks M, fromBlocks_mulVec]
      simp
    rw [hl] at h
    rw [h]
    change (if i ∈ I then -(P *ᵥ v) i else v i) = w i * v (t i)
    by_cases hi : i ∈ I
    · have hpv : (P *ᵥ v) i = s ⟨i,hi⟩ * v (t i) := by
        simp [mulVec_apply_eq_sum, P, hi, ite_mul]
      simp [hpv, w, hi]
    · simp [w, t, hi]
  rw [hB, det_mul, det_diagonal]
  refine IsUnit.mul
    (Finset.prod_induction w IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => ?_) ?_
  · by_cases hi : i ∈ I
    · simpa [w,hi] using (hu ⟨i,hi⟩).neg
    · simp [w,hi]
  · rw [det_permutation]
    exact (Equiv.Perm.sign τ).isUnit.map (Int.castRingHom R)

section CliffordShears

open CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The Clifford implementer of the elementary shear attached to an orthogonal
pair of isotropic vectors. All identities hold with arbitrary scalars. -/
theorem cliffordElementaryShear (q : QuadraticForm R V) (v w : V)
    (hv : q v = 0) (hw : q w = 0) (hvw : QuadraticMap.polar q v w = 0) (t : R) :
    let c := 1 + t • (ι q v * ι q w)
    c ∈ evenOdd q 0 ∧ reverse c * c = 1 ∧ c * reverse c = 1 ∧
    ∀ x, c * ι q x * reverse c =
      ι q (x + t • (QuadraticMap.polar q w x • v - QuadraticMap.polar q v x • w)) := by
  let e := ι q v
  let f := ι q w
  let L := e * f
  have he : e * e = 0 := by rw [ι_sq_scalar, hv, map_zero]
  have hf : f * f = 0 := by rw [ι_sq_scalar, hw, map_zero]
  have hswap : f * e = -L := by
    apply eq_neg_of_add_eq_zero_left
    change f * e + e * f = 0
    rw [add_comm, ι_mul_ι_add_swap, hvw, map_zero]
  have hLrev : reverse L = -L := by
    change reverse (e * f) = -L
    rw [reverse.map_mul, reverse_ι, reverse_ι, hswap]
  have hEL : e * L = 0 := by
    rw [show L = e * f by rfl, ← mul_assoc, he, zero_mul]
  have hFL : f * L = 0 := by
    rw [show L = e * f by rfl, ← mul_assoc, hswap, neg_mul,
      show L = e * f by rfl, mul_assoc, hf, mul_zero, neg_zero]
  have hLL : L * L = 0 := by
    calc
      L * L = e * (f * L) := mul_assoc e f L
      _ = 0 := by rw [hFL, mul_zero]
  change (1 + t • L) ∈ evenOdd q 0 ∧ _
  have hrev : reverse (1 + t • L) = 1 - t • L := by simp [hLrev, sub_eq_add_neg]
  have hn : (t • L) * (t • L) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, hLL, smul_zero, smul_zero]
  refine ⟨(evenOdd q 0).add_mem (SetLike.one_mem_graded _)
    ((evenOdd q 0).smul_mem t (ι_mul_ι_mem_evenOdd_zero q v w)), ?_, ?_, ?_⟩
  · rw [hrev, sub_mul, mul_add, one_mul, one_mul, mul_add, mul_one, hn, add_zero, add_sub_cancel_right]
  · rw [hrev, add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hn, sub_zero]
    abel
  · intro x
    let X := ι q x
    let a := QuadraticMap.polar q v x
    let b := QuadraticMap.polar q w x
    have hfx : f * X = algebraMap R _ b - X * f := ι_mul_ι_comm w x
    have hex : e * X = algebraMap R _ a - X * e := ι_mul_ι_comm v x
    have hcomm : L * X - X * L = b • e - a • f := by
      change (e * f) * X - X * (e * f) = _
      rw [mul_assoc, hfx, mul_sub, ← mul_assoc, hex, sub_mul,
        ← Algebra.commutes b e, ← Algebra.smul_def, ← Algebra.smul_def, mul_assoc]
      abel
    have hLX : (L * X) * L = 0 := by
      rw [show L * X = (L * X - X * L) + X * L by abel, hcomm, add_mul, sub_mul,
        smul_mul_assoc, smul_mul_assoc, hEL, hFL, mul_assoc X L L, hLL]
      simp only [smul_zero, sub_zero, mul_zero, add_zero]
    change (1 + t • L) * X * reverse (1 + t • L) = _
    rw [hrev]
    calc
      _ = X + t • (L * X - X * L) := by
        simp only [add_mul, mul_sub, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
          hLX, smul_zero, add_zero, smul_sub]
        abel
      _ = _ := by rw [hcomm]; simp [X, e, f, a, b]

end CliffordShears

section IsotropicProjection

variable {K : Type*} [Field K] {I : Type*} [DecidableEq I]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- A nonzero coordinate of an isotropic subspace can be chosen as a pivot.
On its kernel the complementary coordinate in the same pair can be omitted. -/
private theorem restrict_pairs (s : Finset I) (i : I) (hi : i ∉ s)
    (f g : I → W →ₗ[K] K) (v : W) (hv : f i v ≠ 0)
    (hq : ∀ x, ∑ j ∈ insert i s, f j x * g j x = 0)
    (hsep : ∀ x, (∀ j ∈ insert i s, f j x = 0 ∧ g j x = 0) → x = 0) :
    (∀ x : LinearMap.ker (f i), ∑ j ∈ s, f j x * g j x = 0) ∧
    (∀ x : LinearMap.ker (f i), (∀ j ∈ s, f j x = 0 ∧ g j x = 0) → x = 0) := by
  have hz (x : LinearMap.ker (f i)) : f i x = 0 := x.property
  constructor
  · intro x
    simpa only [Finset.sum_insert hi, hz x, zero_mul, zero_add] using hq (x : W)
  · intro x hx
    have hs : (∑ j ∈ s, f j (v + (x : W)) * g j (v + (x : W))) =
        ∑ j ∈ s, f j v * g j v := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [map_add, (hx j hj).1, (hx j hj).2]
    have h1 := hq (v + (x : W))
    rw [Finset.sum_insert hi, hs, map_add, map_add, hz x, add_zero, mul_add,
      add_right_comm] at h1
    have h2 := hq v
    rw [Finset.sum_insert hi] at h2
    rw [h2, zero_add] at h1
    have hg := (mul_eq_zero.mp h1).resolve_left hv
    apply Subtype.ext
    exact hsep x fun j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨hz x, hg⟩
      · exact hx j hj

/-- For an isotropic family of coordinate pairs separating the vectors of a
linear space, a choice of one coordinate per pair still separates vectors. -/
private theorem select_isotropic_coordinates (s : Finset I) :
    ∀ {W : Type*} [AddCommGroup W] [Module K W] (f g : I → W →ₗ[K] K),
    (∀ x, ∑ j ∈ s, f j x * g j x = 0) →
    (∀ x, (∀ j ∈ s, f j x = 0 ∧ g j x = 0) → x = 0) →
    ∃ J ⊆ s, ∀ x, (∀ j ∈ s, (if j ∈ J then g j x else f j x) = 0) → x = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro W _ _ f g _ hsep
    exact ⟨∅, Finset.Subset.rfl, fun x _ => hsep x (by simp)⟩
  | insert i s hi ih =>
    intro W _ _ f g hq hsep
    by_cases hf : ∃ v, f i v ≠ 0
    · obtain ⟨v, hv⟩ := hf
      have ⟨hr, hsep'⟩ := restrict_pairs s i hi f g v hv hq hsep
      obtain ⟨J, hJ, hp⟩ := ih
        (fun j => (f j).comp (LinearMap.ker (f i)).subtype)
        (fun j => (g j).comp (LinearMap.ker (f i)).subtype) hr hsep'
      refine ⟨J, hJ.trans (Finset.subset_insert i s), fun x hx => ?_⟩
      have hxi : f i x = 0 := by
        simpa [show i ∉ J from fun h => hi (hJ h)] using hx i (Finset.mem_insert_self i s)
      exact congrArg Subtype.val (hp ⟨x, hxi⟩
        fun j hj => hx j (Finset.mem_insert_of_mem hj))
    · push Not at hf
      by_cases hg : ∃ v, g i v ≠ 0
      · obtain ⟨v, hv⟩ := hg
        have hq' (x : W) : ∑ j ∈ insert i s, g j x * f j x = 0 := by
          simpa only [mul_comm] using hq x
        have ⟨hr, hsep'⟩ := restrict_pairs s i hi g f v hv hq'
          (fun x h => hsep x fun j hj => (h j hj).symm)
        obtain ⟨J, hJ, hp⟩ := ih
          (fun j => (g j).comp (LinearMap.ker (g i)).subtype)
          (fun j => (f j).comp (LinearMap.ker (g i)).subtype) hr hsep'
        refine ⟨insert i (s \ J), Finset.insert_subset_insert i Finset.sdiff_subset, fun x hx => ?_⟩
        have hxi : g i x = 0 := by simpa using hx i (Finset.mem_insert_self i s)
        apply congrArg Subtype.val (hp ⟨x, hxi⟩ ?_)
        intro j hj
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        by_cases h : j ∈ J <;>
          simpa [h, hj, hji] using hx j (Finset.mem_insert_of_mem hj)
      · push Not at hg
        have hq' (x : W) : ∑ j ∈ s, f j x * g j x = 0 := by
          simpa [Finset.sum_insert hi, hf x] using hq x
        obtain ⟨J, hJ, hp⟩ := ih f g hq' (fun x h => hsep x fun j hj => by
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact ⟨hf x, hg x⟩
          · exact h j hj)
        exact ⟨J, hJ.trans (Finset.subset_insert i s),
          fun x hx => hp x fun j hj => hx j (Finset.mem_insert_of_mem hj)⟩

end IsotropicProjection

/-- A norm-preserving invertible matrix can be moved into the block chart
by signed switches. This statement also applies to the odd component. -/
theorem exists_switch_invertible_block {K : Type*} [Field K]
    (g : Matrix (PairIndex m) (PairIndex m) K) (hg : PreservesNorm g)
    (hinj : Function.Injective g.mulVec) :
    ∃ J : Finset (Fin m), IsUnit (signedSwitch m K J * g).toBlocks₁₁.det := by
  let f (j : Fin m) : (Fin m → K) →ₗ[K] K :=
    (LinearMap.proj j).comp g.toBlocks₁₁.mulVecLin
  let h (j : Fin m) : (Fin m → K) →ₗ[K] K :=
    (LinearMap.proj j).comp g.toBlocks₂₁.mulVecLin
  have hblocks (x : Fin m → K) :
      g *ᵥ Sum.elim x 0 = Sum.elim (fun j => f j x) (fun j => h j x) := by
    conv_lhs => rw [← fromBlocks_toBlocks g, fromBlocks_mulVec]
    simp [f, h]
  have hq (x : Fin m → K) : ∑ j ∈ Finset.univ, f j x * h j x = 0 := by
    have hnorm := hg (Sum.elim x 0)
    rw [hblocks, norm_elim, norm_elim, dotProduct_zero] at hnorm
    exact hnorm
  have hsep (x : Fin m → K)
      (hx : ∀ j ∈ Finset.univ, f j x = 0 ∧ h j x = 0) : x = 0 := by
    have hz : g *ᵥ Sum.elim x 0 = g *ᵥ (0 : PairIndex m → K) := by
      rw [hblocks, mulVec_zero]
      funext j
      cases j with
      | inl j => exact (hx j (Finset.mem_univ _)).1
      | inr j => exact (hx j (Finset.mem_univ _)).2
    funext j
    exact congrFun (hinj hz) (Sum.inl j)
  obtain ⟨J, _, hJ⟩ := select_isotropic_coordinates Finset.univ f h hq hsep
  refine ⟨J, isUnit_iff_ne_zero.mpr ?_⟩
  intro hdet
  obtain ⟨x, hx, hzero⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  apply hx
  apply hJ x
  intro j _
  have hleft :
    ((signedSwitch m K J * g) *ᵥ Sum.elim x 0) (Sum.inl j) =
      ((signedSwitch m K J * g).toBlocks₁₁ *ᵥ x) j := by
    conv_lhs => rw [← fromBlocks_toBlocks (signedSwitch m K J * g), fromBlocks_mulVec]
    simp
  rw [← mulVec_mulVec, hblocks, switch_apply] at hleft
  have he := hleft.trans (congrFun hzero j)
  change (if j ∈ J then -h j x else f j x) = 0 at he
  by_cases hj : j ∈ J <;> simpa [hj] using he

section IntrinsicClifford

open CliffordAlgebra

variable {S : Type*} [CommRing S] [Algebra ℤ S]

private abbrev splitForm (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  SpinSpecification.ExtendedForm (integralForm m) S (hyperbolicBasis ℤ m)

private abbrev splitBasis (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  (hyperbolicBasis ℤ m).baseChange S

private abbrev splitCoordinates (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :
    ExtendedModule m S ≃ₗ[S] (PairIndex m → S) :=
  (splitBasis m S).equivFun

private theorem split_form_coordinates (x : ExtendedModule m S) :
    splitForm m S x = hyperbolicNorm (splitCoordinates m S x) :=
  vectorCoordinates m S x

omit [Algebra ℤ S] in
private theorem native_hyperbolic_coordinates (x : HyperbolicModule S m) :
    QuadraticForm.dualProd S _ x = hyperbolicNorm ((hyperbolicBasis S m).equivFun x) := by
  have hl (i : Fin m) : (hyperbolicBasis S m).repr x (toLex (Sum.inl i)) = x.2 i := by
    change ((Pi.basisFun S (Fin m)).dualBasis.prod (Pi.basisFun S (Fin m))).repr
      x (Sum.inr i) = x.2 i
    simp
  have hr (i : Fin m) :
      (hyperbolicBasis S m).repr x (toLex (Sum.inr i)) = x.1 (Pi.single i 1) := by
    change ((Pi.basisFun S (Fin m)).dualBasis.prod (Pi.basisFun S (Fin m))).repr
      x (Sum.inl i) = x.1 (Pi.single i 1)
    simp
  have hv : ∑ i : Fin m, x.2 i • (Pi.single i 1 : Fin m → S) = x.2 := by
    simpa using (Pi.basisFun S (Fin m)).sum_repr x.2
  change x.1 x.2 = ∑ i : Fin m, (hyperbolicBasis S m).repr x (toLex (Sum.inl i)) *
    (hyperbolicBasis S m).repr x (toLex (Sum.inr i))
  simp only [hl, hr]
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, smul_eq_mul]

private def splitIsometry (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :
    (splitForm m S).IsometryEquiv (QuadraticForm.dualProd S (FreeModule S m)) where
  toLinearEquiv := (splitCoordinates m S).trans (hyperbolicBasis S m).equivFun.symm
  map_app' x := by
    change QuadraticForm.dualProd S _ ((hyperbolicBasis S m).equivFun.symm
      (splitCoordinates m S x)) = splitForm m S x
    rw [native_hyperbolic_coordinates]
    exact (congrArg hyperbolicNorm ((hyperbolicBasis S m).equivFun.apply_symm_apply
      ((splitBasis m S).equivFun x))).trans (split_form_coordinates x).symm

private theorem split_scalar_centralizer (c : CliffordAlgebra (splitForm m S))
    (hc : ∀ x, Commute c (ι (splitForm m S) x)) :
    ∃ r : S, c = algebraMap S _ r := by
  let e := CliffordAlgebra.equivOfIsometry (splitIsometry m S)
  have hm (y : HyperbolicModule S m) :
      Commute (e c) (ι (QuadraticForm.dualProd S _) y) := by
    let a := splitIsometry m S
    have h := (hc (a.symm y)).map e
    change Commute (e c) (CliffordAlgebra.map a.toIsometry (ι (splitForm m S) (a.symm y))) at h
    simpa using h
  obtain ⟨r, hr⟩ := (CliffordModel.hyperbolic_scalar_centralizer
    (Pi.basisFun S (Fin m)) (e c)).mp hm
  exact ⟨r, e.injective (hr.trans (e.commutes r).symm)⟩

private def unitConj {A : Type*} [Monoid A] (a : Aˣ) (x : A) : A :=
  ↑a * x * ↑a⁻¹

private theorem unitConj_mul_units {A : Type*} [Monoid A] (a b : Aˣ) (x : A) :
    unitConj (a * b) x = unitConj a (unitConj b x) := by
  simp [unitConj, mul_assoc]

private theorem unitConj_cancel_left {A : Type*} [Monoid A] (a : Aˣ) (x : A) :
    unitConj a⁻¹ (unitConj a x) = x := by
  rw [← unitConj_mul_units, inv_mul_cancel]
  simp [unitConj]

private theorem unitConj_eq_self_iff {A : Type*} [Monoid A] (a : Aˣ) (x : A) :
    unitConj a x = x ↔ Commute (a : A) x := by
  constructor
  · intro h
    change (a : A) * x = x * (a : A)
    simpa [unitConj, mul_assoc] using congrArg (fun y => y * (a : A)) h
  · intro h
    rw [unitConj, h.eq, mul_assoc, Units.mul_inv, mul_one]

open private scalar_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private theorem split_scalar_injective :
    Function.Injective (algebraMap S (CliffordAlgebra (splitForm m S))) :=
  scalar_injective (splitForm m S) (splitBasis m S)

/-- Any unit in the full split Clifford algebra acting trivially on the
vectors is the image of a scalar unit, over every test algebra. -/
private theorem scalar_unit_of_trivial_action (a : (CliffordAlgebra (splitForm m S))ˣ)
    (ha : ∀ x, unitConj a (ι (splitForm m S) x) = ι (splitForm m S) x) :
    ∃ u : Sˣ, Units.map (algebraMap S (CliffordAlgebra (splitForm m S))) u = a := by
  have hc (x) := (unitConj_eq_self_iff a _).mp (ha x)
  obtain ⟨r, hr⟩ := split_scalar_centralizer (m := m) (S := S) a hc
  have hi (x) : Commute (↑a⁻¹ : CliffordAlgebra (splitForm m S)) (ι (splitForm m S) x) := by
    apply (unitConj_eq_self_iff a⁻¹ _).mp
    simpa only [ha x] using unitConj_cancel_left a (ι (splitForm m S) x)
  obtain ⟨s, hs⟩ := split_scalar_centralizer (m := m) (S := S) (↑a⁻¹) hi
  have hrs : r * s = 1 := split_scalar_injective (m := m) (by
    rw [map_mul, ← hr, ← hs, Units.mul_inv, map_one])
  refine ⟨⟨r, s, hrs, (mul_comm s r).trans hrs⟩, ?_⟩
  exact Units.ext hr.symm

/-- Two units implementing the same vector map differ by a unique invertible
scalar. No condition on their Clifford degree or reversion norm is needed. -/
theorem ratio_of_implementers (a b : (CliffordAlgebra (splitForm m S))ˣ)
    (h : ∀ x, unitConj a (ι (splitForm m S) x) = unitConj b (ι (splitForm m S) x)) :
    ∃! u : Sˣ, a = b * Units.map (algebraMap S (CliffordAlgebra (splitForm m S))) u := by
  have hb (x) : unitConj (b⁻¹ * a) (ι (splitForm m S) x) = ι (splitForm m S) x := by
    rw [unitConj_mul_units, h, unitConj_cancel_left]
  obtain ⟨u, hu⟩ := scalar_unit_of_trivial_action (m := m) (S := S) (b⁻¹ * a) hb
  have hu' : a = b * Units.map (algebraMap S (CliffordAlgebra (splitForm m S))) u := by
    rw [hu, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨u, hu', fun v hv => ?_⟩
  change a = b * Units.map (algebraMap S (CliffordAlgebra (splitForm m S))) v at hv
  have he := mul_left_cancel (hv.symm.trans hu')
  exact Units.ext (split_scalar_injective (m := m) (congrArg Units.val he))

private theorem split_polar (x y : ExtendedModule m S) :
    QuadraticMap.polar (splitForm m S) x y =
      ((fun i => splitCoordinates m S x (Sum.inl i)) ⬝ᵥ
        (fun i => splitCoordinates m S y (Sum.inr i))) +
      ((fun i => splitCoordinates m S y (Sum.inl i)) ⬝ᵥ
        (fun i => splitCoordinates m S x (Sum.inr i))) := by
  rw [QuadraticMap.polar, split_form_coordinates, split_form_coordinates, split_form_coordinates, map_add]
  change
    ((fun i => splitCoordinates m S x (Sum.inl i)) + (fun i => splitCoordinates m S y (Sum.inl i))) ⬝ᵥ
      ((fun i => splitCoordinates m S x (Sum.inr i)) + (fun i => splitCoordinates m S y (Sum.inr i))) -
      _ - _ = _
  simp only [add_dotProduct, dotProduct_add, hyperbolicNorm]
  abel

private abbrev splitE (i : Fin m) : ExtendedModule m S :=
  splitBasis m S (Sum.inl i)

private abbrev splitF (i : Fin m) : ExtendedModule m S :=
  splitBasis m S (Sum.inr i)

private theorem split_coordinates_e (i : Fin m) :
    (splitCoordinates m S (splitE (m := m) (S := S) i) : PairIndex m → S) =
      Sum.elim (Pi.single i 1) 0 := by
  funext j
  change (splitBasis m S).equivFun (splitBasis m S (toLex (Sum.inl i))) (toLex j) = _
  rw [Module.Basis.equivFun_self]
  cases j <;> simp [Pi.single_apply, eq_comm]

private theorem split_coordinates_f (i : Fin m) :
    (splitCoordinates m S (splitF (m := m) (S := S) i) : PairIndex m → S) =
      Sum.elim (0 : Fin m → S) (Pi.single i 1) := by
  funext j
  change (splitBasis m S).equivFun (splitBasis m S (toLex (Sum.inr i))) (toLex j) = _
  rw [Module.Basis.equivFun_self]
  cases j <;> simp [Pi.single_apply, eq_comm]

private def switchVector (i : Fin m) : ExtendedModule m S := splitE i + splitF i

private theorem switch_vector_norm (i : Fin m) :
    splitForm m S (switchVector (S := S) i) = 1 := by
  rw [split_form_coordinates, switchVector, map_add, split_coordinates_e, split_coordinates_f]
  change ((Pi.single i 1 + 0 : Fin m → S) ⬝ᵥ (0 + Pi.single i 1)) = 1
  simp

private def switchFactor (i : Fin m) : (CliffordAlgebra (splitForm m S))ˣ where
  val := ι (splitForm m S) (switchVector i)
  inv := ι (splitForm m S) (switchVector i)
  val_inv := by rw [ι_sq_scalar, switch_vector_norm, map_one]
  inv_val := by rw [ι_sq_scalar, switch_vector_norm, map_one]

private theorem switch_vector_polar (i : Fin m) (x : ExtendedModule m S) :
    QuadraticMap.polar (splitForm m S) (switchVector i) x =
      splitCoordinates m S x (Sum.inr i) + splitCoordinates m S x (Sum.inl i) := by
  rw [split_polar, switchVector, map_add, split_coordinates_e, split_coordinates_f]
  change ((Pi.single i 1 + 0 : Fin m → S) ⬝ᵥ _) +
      (_ ⬝ᵥ (0 + Pi.single i 1 : Fin m → S)) = _
  simp [single_dotProduct, dotProduct_single]

private theorem switch_coordinate_formula (i : Fin m) (x : ExtendedModule m S) :
    signedSwitch m S {i} *ᵥ (splitCoordinates m S x : PairIndex m → S) =
      splitCoordinates m S (x - QuadraticMap.polar (splitForm m S) (switchVector i) x •
        switchVector i) := by
  rw [switch_vector_polar, map_sub, map_smul, switchVector, map_add,
    split_coordinates_e, split_coordinates_f]
  let d : PairIndex m → S := splitCoordinates m S x
  change signedSwitch m S {i} *ᵥ d = _
  have hd : Sum.elim (d ∘ Sum.inl) (d ∘ Sum.inr) = d := by
    funext j
    cases j <;> rfl
  conv_lhs => rw [← hd, switch_apply]
  funext j
  cases j with
  | inl j =>
    change (if j ∈ ({i} : Finset (Fin m)) then -d (Sum.inr j) else d (Sum.inl j)) =
      d (Sum.inl j) - (d (Sum.inr i) + d (Sum.inl i)) * ((Pi.single i (1 : S) : Fin m → S) j + 0)
    by_cases h : j = i <;> simp [h, sub_eq_add_neg, add_comm]
  | inr j =>
    change (if j ∈ ({i} : Finset (Fin m)) then -d (Sum.inl j) else d (Sum.inr j)) =
      d (Sum.inr j) - (d (Sum.inr i) + d (Sum.inl i)) * (0 + (Pi.single i (1 : S) : Fin m → S) j)
    by_cases h : j = i <;> simp [h, sub_eq_add_neg, add_comm]

private theorem switch_factor_action (i : Fin m) (v : PairIndex m → S) :
    unitConj (switchFactor (S := S) i) (ι (splitForm m S) ((splitCoordinates m S).symm v)) =
      -ι (splitForm m S) ((splitCoordinates m S).symm (signedSwitch m S {i} *ᵥ v)) := by
  let q := splitForm m S
  let x := (splitCoordinates m S).symm v
  let w := switchVector (S := S) i
  have hv : (splitCoordinates m S x : PairIndex m → S) = v :=
    (splitCoordinates m S).apply_symm_apply v
  rw [← hv, switch_coordinate_formula]
  simp only [LinearEquiv.symm_apply_apply]
  change ι q w * ι q x * ι q w = -ι q (x - QuadraticMap.polar q w x • w)
  rw [ι_mul_ι_comm w x, sub_mul, mul_assoc (ι q x), ι_sq_scalar, switch_vector_norm,
    map_one, mul_one, ← Algebra.smul_def, map_sub, map_smul, neg_sub]

private theorem signed_switch_empty :
    signedSwitch m R ∅ = 1 := by
  simp [signedSwitch, fromBlocks_one]

private theorem signed_switch_insert (J : Finset (Fin m)) (i : Fin m) (hi : i ∉ J) :
    signedSwitch m R (insert i J) = signedSwitch m R {i} * signedSwitch m R J := by
  apply mulVec_injective
  funext v
  have hv : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
    funext j
    cases j <;> rfl
  rw [← hv, ← mulVec_mulVec, switch_apply, switch_apply, switch_apply]
  funext j
  cases j with
  | inl j =>
    by_cases h : j = i
    · subst j
      simp [hi]
    · simp [h]
  | inr j =>
    by_cases h : j = i
    · subst j
      simp [hi]
    · simp [h]

/-- Signed switches are implemented by products of the vectors (e_i+f_i).
The conjugation includes the global sign indexed by the Clifford degree. -/
private theorem intrinsic_switch_lift (J : Finset (Fin m)) :
    ∃ a : (CliffordAlgebra (splitForm m S))ˣ,
      (a : CliffordAlgebra _) ∈ evenOdd (splitForm m S) (J.card : ZMod 2) ∧
      reverse (a : CliffordAlgebra (splitForm m S)) * (a : CliffordAlgebra (splitForm m S)) = 1 ∧
      ∀ v : PairIndex m → S,
        unitConj a (ι (splitForm m S) ((splitCoordinates m S).symm v)) =
          (-1 : S) ^ J.card •
            ι (splitForm m S) ((splitCoordinates m S).symm (signedSwitch m S J *ᵥ v)) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    exact ⟨1, by simpa using SetLike.one_mem_graded (A := evenOdd (splitForm m S)),
      by simp, by simp [unitConj, signed_switch_empty]⟩
  | insert i J hi ih =>
    obtain ⟨a, ha, hnorm, haction⟩ := ih
    let b := switchFactor (S := S) i
    refine ⟨b * a, ?_, ?_, ?_⟩
    · rw [Units.val_mul, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, add_comm]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one (splitForm m S) (switchVector i)) ha
    · have h : reverse (b : CliffordAlgebra (splitForm m S)) * (b : CliffordAlgebra (splitForm m S)) = 1 := by
        change reverse (ι (splitForm m S) (switchVector i)) * ι _ (switchVector i) = 1
        rw [reverse_ι, ι_sq_scalar, switch_vector_norm, map_one]
      rw [Units.val_mul, reverse.map_mul]
      calc
        _ = reverse (a : CliffordAlgebra (splitForm m S)) *
            ((reverse (b : CliffordAlgebra (splitForm m S)) * (b : CliffordAlgebra (splitForm m S))) *
              (a : CliffordAlgebra (splitForm m S))) := by
          simp only [mul_assoc]
        _ = 1 := by rw [h, one_mul, hnorm]
    · intro v
      rw [unitConj_mul_units, haction, signed_switch_insert J i hi, ← mulVec_mulVec]
      rw [unitConj, mul_smul_comm, smul_mul_assoc]
      change (-1 : S) ^ J.card • unitConj b _ = _
      rw [switch_factor_action, Finset.card_insert_of_notMem hi, pow_succ, mul_smul, neg_one_smul]


open private cliffordEquiv cliffordEquiv_vector cliffordEquiv_even
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor
open private baseChangeEquiv_reverse from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CliffordModel

private abbrev integralCliffordEquiv (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  cliffordEquiv (integralForm m) S (hyperbolicBasis ℤ m)

set_option maxRecDepth 2000 in
private theorem intrinsic_implementer_to_action
    (a : (CliffordAlgebra (splitForm m S))ˣ) (M : Matrix (PairIndex m) (PairIndex m) S)
    (hM : IsUnit M.det)
    (h : ∀ v : PairIndex m → S, unitConj a (ι _ ((splitCoordinates m S).symm v)) =
      ι _ ((splitCoordinates m S).symm (M *ᵥ v))) :
    HasActionMatrix m (Units.map (integralCliffordEquiv m S).symm.toMonoidHom a) M := by
  let q := integralForm m
  let e := integralCliffordEquiv m S
  let d := splitCoordinates m S
  let b : Module.Basis (PairIndex m) S (ExtendedModule m S) := splitBasis m S
  let g := Matrix.toLinearEquiv b M hM
  have hcoords (x : ExtendedModule m S) :
      M *ᵥ (d x : PairIndex m → S) = d (g x) := by
    have he := LinearMap.toMatrix_mulVec_repr b b g.toLinearMap x
    rwa [show g.toLinearMap = Matrix.toLin b b M from rfl, LinearMap.toMatrix_toLin] at he
  refine ⟨g, fun x => e.injective ?_, ?_⟩
  · have hh := h (d x)
    rw [LinearEquiv.symm_apply_apply, hcoords, LinearEquiv.symm_apply_apply] at hh
    let a₀ := Units.map e.symm.toMonoidHom a
    change e (SpinSpecification.vectors q S (g x)) =
      e (SpinSpecification.conjugate q S a₀ (SpinSpecification.vectors q S x))
    have ha₀ : e (a₀ : ScalarClifford m S) = a := e.apply_symm_apply _
    have ha₀inv : e (↑a₀⁻¹ : ScalarClifford m S) = ↑a⁻¹ := by
      rw [show a₀⁻¹ = Units.map e.symm.toMonoidHom a⁻¹ from (map_inv _ _).symm]
      exact e.apply_symm_apply _
    rw [SpinSpecification.conjugate, map_mul, map_mul, ha₀, ha₀inv,
      show ∀ y, e (SpinSpecification.vectors q S y) = ι (splitForm m S) y from
        cliffordEquiv_vector q S (hyperbolicBasis ℤ m)]
    rw [show e (SpinSpecification.vectors q S x) = ι (splitForm m S) x from
      cliffordEquiv_vector q S (hyperbolicBasis ℤ m) x]
    exact hh.symm
  · exact (LinearMap.toMatrix_toLin b b M : _)

private theorem spin_of_intrinsic_implementer (a : (CliffordAlgebra (splitForm m S))ˣ)
    (ha : (a : CliffordAlgebra (splitForm m S)) ∈ evenOdd (splitForm m S) 0)
    (hnorm : reverse (a : CliffordAlgebra (splitForm m S)) * (a : CliffordAlgebra (splitForm m S)) = 1)
    (M : Matrix (PairIndex m) (PairIndex m) S)
    (hM : IsUnit M.det)
    (h : ∀ v : PairIndex m → S, unitConj a (ι _ ((splitCoordinates m S).symm v)) =
      ι _ ((splitCoordinates m S).symm (M *ᵥ v))) :
    let a₀ := Units.map (integralCliffordEquiv m S).symm.toMonoidHom a
    a₀ ∈ SpinSpecification.spinUnits (integralForm m) S ∧ HasActionMatrix m a₀ M := by
  let q := integralForm m
  let b := hyperbolicBasis ℤ m
  let e := integralCliffordEquiv m S
  let a₀ := Units.map e.symm.toMonoidHom a
  have ha₀ : e (a₀ : ScalarClifford m S) = a := e.apply_symm_apply _
  have hrev := baseChangeEquiv_reverse S q b (a₀ : ScalarClifford m S)
  obtain ⟨g, hg, hgm⟩ := intrinsic_implementer_to_action a M hM h
  refine ⟨⟨(cliffordEquiv_even q S b _).mp (ha₀.symm ▸ ha), e.injective ?_, ?_, ?_⟩,
    ⟨g, hg, hgm⟩⟩
  · change e (SpinSpecification.reversion q S a₀ * (a₀ : ScalarClifford m S)) = e 1
    rw [map_mul, map_one, show e (SpinSpecification.reversion q S a₀) = reverse (e a₀) from hrev,
      ha₀, hnorm]
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, hg x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨g.symm x, ?_⟩
    have heq := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at heq
    rw [heq]
    exact (unitConj_cancel_left a₀ _).symm

/-- Every even signed switch has a norm-one Clifford lift over any test
algebra, in particular over the integers. -/
theorem even_switch_spin_lift (J : EvenSwitches m) :
    ∃ a : (ScalarClifford m S)ˣ, a ∈ SpinSpecification.spinUnits (integralForm m) S ∧
      HasActionMatrix m a (signedSwitch m S J.val) := by
  obtain ⟨a, ha, hn, h⟩ := intrinsic_switch_lift (S := S) J.val
  rw [J.property.natCast_zmod_two] at ha
  have hs : (-1 : S) ^ J.val.card = 1 := J.property.neg_one_pow
  simp only [hs, one_smul] at h
  have hd := Matrix.isUnit_det_of_left_inverse (signedSwitchProperties m S J.val).2
  exact ⟨_, spin_of_intrinsic_implementer a ha hn _ hd h⟩


private def shearMatrix (upperShear : Bool) (P : Block m S) :
    Matrix (PairIndex m) (PairIndex m) S :=
  if upperShear then upper P else lower P

private def shearBasisVector (upperShear : Bool) (i : Fin m) : ExtendedModule m S :=
  if upperShear then splitE i else splitF i

private def elementaryAlternating (i j : Fin m) (t : S) : Block m S :=
  Matrix.single i j t - Matrix.single j i t

private theorem split_e_norm (i : Fin m) : splitForm m S (splitE i) = 0 := by
  rw [split_form_coordinates, split_coordinates_e, norm_elim, dotProduct_zero]

private theorem split_f_norm (i : Fin m) : splitForm m S (splitF i) = 0 := by
  rw [split_form_coordinates, split_coordinates_f, norm_elim, zero_dotProduct]

private theorem split_e_polar (i : Fin m) (x : ExtendedModule m S) :
    QuadraticMap.polar (splitForm m S) (splitE i) x = splitCoordinates m S x (Sum.inr i) := by
  rw [split_polar, split_coordinates_e]
  change (Pi.single i 1 ⬝ᵥ _) + (_ ⬝ᵥ (0 : Fin m → S)) = _
  simp [single_dotProduct]

private theorem split_f_polar (i : Fin m) (x : ExtendedModule m S) :
    QuadraticMap.polar (splitForm m S) (splitF i) x = splitCoordinates m S x (Sum.inl i) := by
  rw [split_polar, split_coordinates_f]
  change ((0 : Fin m → S) ⬝ᵥ _) + (_ ⬝ᵥ Pi.single i 1) = _
  simp [dotProduct_single]

private theorem elementary_shear_on_coordinates (upperShear : Bool) (i j : Fin m)
    (t : S) (x : ExtendedModule m S) :
    let v := shearBasisVector (S := S) upperShear i
    let w := shearBasisVector (S := S) upperShear j
    shearMatrix upperShear (elementaryAlternating i j t) *ᵥ splitCoordinates m S x =
      splitCoordinates m S (x + t •
        (QuadraticMap.polar (splitForm m S) w x • v - QuadraticMap.polar (splitForm m S) v x • w)) := by
  let b := splitCoordinates m S
  let u : Fin m → S := fun k => b x (Sum.inl k)
  let v : Fin m → S := fun k => b x (Sum.inr k)
  have hx : Sum.elim u v = b x := by
    funext k
    cases k <;> rfl
  have hmul (z : Fin m → S) :
      elementaryAlternating i j t *ᵥ z =
        t • (z j • (Pi.single i 1 : Fin m → S) - z i • (Pi.single j 1 : Fin m → S)) := by
    rw [elementaryAlternating, sub_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq,
      smul_sub, smul_smul, smul_smul]
  cases upperShear
  · simp only [shearMatrix, Bool.false_eq_true, ite_false, shearBasisVector, split_f_polar,
      map_add, map_smul, map_sub, split_coordinates_f]
    change lower (elementaryAlternating i j t) *ᵥ b x =
      b x + t • (u j • Sum.elim (0 : Fin m → S) (Pi.single i 1) -
        u i • Sum.elim (0 : Fin m → S) (Pi.single j 1))
    rw [← hx, lower, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, one_mulVec, hmul]
    funext k
    cases k <;> simp [Pi.single_apply, add_comm]
  · simp only [shearMatrix, ite_true, shearBasisVector, split_e_polar,
      map_add, map_smul, map_sub, split_coordinates_e]
    change upper (elementaryAlternating i j t) *ᵥ b x =
      b x + t • (v j • Sum.elim (Pi.single i 1) (0 : Fin m → S) -
        v i • Sum.elim (Pi.single j 1) (0 : Fin m → S))
    rw [← hx, upper, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, one_mulVec, hmul]
    funext k
    cases k <;> simp [Pi.single_apply]

private def IsCliffordLift (M : Matrix (PairIndex m) (PairIndex m) S)
    (a : (CliffordAlgebra (splitForm m S))ˣ) (k : ZMod 2) (r : S) : Prop :=
  (a : CliffordAlgebra (splitForm m S)) ∈ evenOdd (splitForm m S) k ∧
    reverse (a : CliffordAlgebra (splitForm m S)) * (a : CliffordAlgebra (splitForm m S)) =
      algebraMap S _ r ∧
    ∀ v : PairIndex m → S,
      unitConj a (ι (splitForm m S) ((splitCoordinates m S).symm v)) =
        ι (splitForm m S) ((splitCoordinates m S).symm (M *ᵥ v))

private theorem isCliffordLift_one :
    IsCliffordLift (1 : Matrix (PairIndex m) (PairIndex m) S) 1 0 1 := by
  exact ⟨SetLike.one_mem_graded _, by simp, by simp [unitConj]⟩

private theorem IsCliffordLift.mul
    {M N : Matrix (PairIndex m) (PairIndex m) S}
    {a b : (CliffordAlgebra (splitForm m S))ˣ} {k l : ZMod 2} {r s : S}
    (ha : IsCliffordLift M a k r) (hb : IsCliffordLift N b l s) :
    IsCliffordLift (M * N) (a * b) (k + l) (r * s) := by
  refine ⟨SetLike.mul_mem_graded ha.1 hb.1, ?_, fun v => ?_⟩
  · let a' : CliffordAlgebra (splitForm m S) := a
    let b' : CliffordAlgebra (splitForm m S) := b
    have ha' : reverse a' * a' = algebraMap S _ r := ha.2.1
    have hb' : reverse b' * b' = algebraMap S _ s := hb.2.1
    change reverse (a' * b') * (a' * b') = _
    rw [reverse.map_mul, mul_assoc, ← mul_assoc (reverse a'), ha',
      ← mul_assoc (reverse b'), ← Algebra.commutes r (reverse b'), mul_assoc, hb', ← map_mul]
  · rw [unitConj_mul_units, hb.2.2, ha.2.2, mulVec_mulVec]

private theorem elementary_shear_lift (upperShear : Bool) (i j : Fin m) (t : S) :
    ∃ a, IsCliffordLift (shearMatrix upperShear (elementaryAlternating i j t)) a 0 1 := by
  let q := splitForm m S
  let d := splitCoordinates m S
  let v := shearBasisVector (S := S) upperShear i
  let w := shearBasisVector (S := S) upperShear j
  have hn (k : Fin m) : q (shearBasisVector (S := S) upperShear k) = 0 := by
    cases upperShear
    · exact split_f_norm k
    · exact split_e_norm k
  have hp : QuadraticMap.polar q v w = 0 := by
    cases upperShear
    · change QuadraticMap.polar q (splitF i) (splitF j) = 0
      rw [split_f_polar, split_coordinates_f]
      rfl
    · change QuadraticMap.polar q (splitE i) (splitE j) = 0
      rw [split_e_polar, split_coordinates_e]
      rfl
  let c := 1 + t • (ι q v * ι q w)
  obtain ⟨he, hr, hl, hc⟩ := cliffordElementaryShear q v w (hn i) (hn j) hp t
  let a : (CliffordAlgebra q)ˣ := ⟨c, reverse c, hl, hr⟩
  refine ⟨a, he, by rw [map_one]; exact hr, fun x => ?_⟩
  have h := elementary_shear_on_coordinates upperShear i j t (d.symm x)
  simp only [d, LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply]
  exact hc (d.symm x)

omit [Algebra ℤ S] in
private theorem shear_matrix_zero (upperShear : Bool) :
    shearMatrix upperShear (0 : Block m S) = 1 := by
  cases upperShear <;> simp [shearMatrix, upper, lower]

omit [Algebra ℤ S] in
private theorem shear_matrix_add (upperShear : Bool) (P Q : Block m S) :
    shearMatrix upperShear (P + Q) = shearMatrix upperShear P * shearMatrix upperShear Q := by
  cases upperShear <;> simp [shearMatrix, lower, upper, fromBlocks_multiply, add_comm]

omit [Algebra ℤ S] in
private theorem alternating_expansion (P : Block m S) (hP : IsAlternating P) :
    (∑ ij : AlternatingIndex m, elementaryAlternating ij.val.1 ij.val.2 (P ij.val.1 ij.val.2)) =
      P := by
  classical
  obtain ⟨hd, hs⟩ := (alternatingEntries m S P).mp hP
  ext i j
  simp only [Matrix.sum_apply]
  obtain h | rfl | h := lt_trichotomy i j
  · rw [Finset.sum_eq_single (⟨(i,j),h⟩ : AlternatingIndex m)]
    · simp [elementaryAlternating, Matrix.single, h.ne, h.ne']
    · intro a _ ha
      obtain ⟨⟨a,b⟩,hab⟩ := a
      simp only [elementaryAlternating, Matrix.sub_apply, Matrix.single, Matrix.of_apply]
      split
      · rename_i he
        exact (ha (Subtype.ext (Prod.ext he.1 he.2))).elim
      · split
        · rename_i he
          exact (h.asymm (he.1 ▸ he.2 ▸ hab)).elim
        · simp
    · simp
  · rw [hd]
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨⟨a,b⟩,hab⟩ := a
    simp [elementaryAlternating, Matrix.single, and_comm]
  · rw [Finset.sum_eq_single (⟨(j,i),h⟩ : AlternatingIndex m)]
    · simpa [elementaryAlternating, Matrix.single, h.ne, h.ne'] using (hs i j).symm
    · intro a _ ha
      obtain ⟨⟨a,b⟩,hab⟩ := a
      simp only [elementaryAlternating, Matrix.sub_apply, Matrix.single, Matrix.of_apply]
      split
      · rename_i he
        exact (h.asymm (he.1 ▸ he.2 ▸ hab)).elim
      · split
        · rename_i he
          exact (ha (Subtype.ext (Prod.ext he.2 he.1))).elim
        · simp
    · simp

/-- Every alternating shear has a norm-one even Clifford implementer over the test algebra. -/
private theorem alternating_shear_lift (upperShear : Bool) (P : Block m S) (hP : IsAlternating P) :
    ∃ a, IsCliffordLift (shearMatrix upperShear P) a 0 1 := by
  classical
  let term (ij : AlternatingIndex m) := elementaryAlternating ij.val.1 ij.val.2 (P ij.val.1 ij.val.2)
  have liftSum (s : Finset (AlternatingIndex m)) :
      ∃ a, IsCliffordLift (shearMatrix upperShear (∑ i ∈ s, term i)) a 0 1 := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_⟩
      simpa only [Finset.sum_empty, shear_matrix_zero] using isCliffordLift_one (m := m) (S := S)
    | insert i s hi ih =>
      obtain ⟨a, ha⟩ := elementary_shear_lift upperShear i.val.1 i.val.2 (P i.val.1 i.val.2)
      obtain ⟨b, hb⟩ := ih
      rw [Finset.sum_insert hi, shear_matrix_add]
      exact ⟨a * b, by simpa only [add_zero, mul_one] using ha.mul hb⟩
  have hsum : (∑ i : AlternatingIndex m, term i) = P := alternating_expansion P hP
  rw [← hsum]
  exact liftSum Finset.univ


section ExteriorImplementation

open Module

private abbrev W (m : ℕ) (S : Type*) := Fin m → S
private abbrev Ext (m : ℕ) (S : Type*) [CommRing S] := ExteriorAlgebra S (W m S)
private abbrev N (m : ℕ) (S : Type*) [CommRing S] :=
  QuadraticForm.dualProd S (W m S)

omit [Algebra ℤ S] in
private theorem exterior_contract_map (f : W m S →ₗ[S] W m S)
    (d : Module.Dual S (W m S)) (x : Ext m S) :
    contractLeft (Q := (0 : QuadraticForm S (W m S))) d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (contractLeft (Q := (0 : QuadraticForm S (W m S))) (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    change contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι S v * x)) =
      ExteriorAlgebra.map f (contractLeft (d.comp f) (ExteriorAlgebra.ι S v * x))
    rw [map_mul, ExteriorAlgebra.map_apply_ι]
    change contractLeft d (ι (0 : QuadraticForm S (W m S)) (f v) * _) =
      ExteriorAlgebra.map f (contractLeft (d.comp f) (ι (0 : QuadraticForm S (W m S)) v * _))
    rw [contractLeft_ι_mul, contractLeft_ι_mul, map_sub, map_smul, map_mul, hx,
      ExteriorAlgebra.map_apply_ι, LinearMap.comp_apply]

omit [Algebra ℤ S] in
private theorem exterior_map_evenOdd (f : W m S →ₗ[S] W m S) (k : ZMod 2)
    (x : Ext m S) (hx : x ∈ evenOdd (0 : QuadraticForm S (W m S)) k) :
    ExteriorAlgebra.map f x ∈ evenOdd (0 : QuadraticForm S (W m S)) k := by
  have he : ExteriorAlgebra.map f =
      CliffordAlgebra.map (⟨f, fun _ => rfl⟩ :
        (0 : QuadraticForm S (W m S)) →qᵢ (0 : QuadraticForm S (W m S))) := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change ExteriorAlgebra.map f (ExteriorAlgebra.ι S v) = CliffordAlgebra.map _ (ι _ v)
    rw [ExteriorAlgebra.map_apply_ι, map_apply_ι]
    rfl
  have hm : (evenOdd (0 : QuadraticForm S (W m S)) k).map
      (ExteriorAlgebra.map f).toLinearMap ≤ evenOdd (0 : QuadraticForm S (W m S)) k := by
    simp only [he, evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_map]
    refine iSup_mono fun i => ?_
    gcongr
    rw [← LinearMap.range_comp]
    exact LinearMap.range_comp_le_range _ _
  exact hm (Submodule.mem_map_of_mem hx)

private abbrev exteriorRep (m : ℕ) (S : Type*) [CommRing S] :
    CliffordAlgebra (N m S) ≃ₐ[S] Module.End S (Ext m S) :=
  CliffordModel.hyperbolicEquiv (Pi.basisFun S (Fin m))

omit [Algebra ℤ S] in
private def exteriorUnit (f : W m S ≃ₗ[S] W m S) : (Module.End S (Ext m S))ˣ where
  val := (ExteriorAlgebra.map f.toLinearMap).toLinearMap
  inv := (ExteriorAlgebra.map f.symm.toLinearMap).toLinearMap
  val_inv := by
    apply LinearMap.ext
    intro x
    change (ExteriorAlgebra.map f.toLinearMap) ((ExteriorAlgebra.map f.symm.toLinearMap) x) = x
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    simp
  inv_val := by
    apply LinearMap.ext
    intro x
    change (ExteriorAlgebra.map f.symm.toLinearMap) ((ExteriorAlgebra.map f.toLinearMap) x) = x
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    simp

omit [Algebra ℤ S] in
private def exteriorImplementer (f : W m S ≃ₗ[S] W m S) : (CliffordAlgebra (N m S))ˣ :=
  Units.map (exteriorRep m S).symm.toMonoidHom (exteriorUnit f)

omit [Algebra ℤ S] in
private theorem exterior_implementer_action (f : W m S ≃ₗ[S] W m S)
    (d : Module.Dual S (W m S)) (v : W m S) :
    unitConj (exteriorImplementer f) (ι (N m S) (d, v)) =
      ι (N m S) (d.comp f.symm.toLinearMap, f v) := by
  let e := exteriorRep m S
  apply e.injective
  simp only [unitConj, map_mul]
  have h : e ((exteriorImplementer f : (CliffordAlgebra (N m S))ˣ) :
      CliffordAlgebra (N m S)) = exteriorUnit f := e.apply_symm_apply _
  have h' : e (↑(exteriorImplementer f)⁻¹ : CliffordAlgebra (N m S)) =
      ↑(exteriorUnit f)⁻¹ := by
    rw [exteriorImplementer, ← map_inv]
    exact e.apply_symm_apply _
  have hi (z : HyperbolicModule S m) : e (ι (N m S) z) =
      CliffordSpecification.hyperbolicOperator z := CliffordModel.hyperbolicEquiv_ι _ _
  rw [h, h', hi, hi]
  apply LinearMap.ext
  intro x
  let y := ExteriorAlgebra.map f.symm.toLinearMap x
  have hy : ExteriorAlgebra.map f.toLinearMap y = x :=
    congrArg (fun g : Module.End S (Ext m S) => g x) (exteriorUnit f).val_inv
  change ExteriorAlgebra.map f.toLinearMap
      (ExteriorAlgebra.ι S v * y + contractLeft (Q := (0 : QuadraticForm S (W m S))) d y) =
    ExteriorAlgebra.ι S (f v) * x +
      contractLeft (Q := (0 : QuadraticForm S (W m S))) (d.comp f.symm.toLinearMap) x
  rw [map_add, map_mul, ExteriorAlgebra.map_apply_ι, hy]
  have hd : (d.comp f.symm.toLinearMap).comp f.toLinearMap = d := by
    apply LinearMap.ext
    intro z
    exact congrArg d (f.symm_apply_apply z)
  have hc := exterior_contract_map f.toLinearMap (d.comp f.symm.toLinearMap) y
  rw [hy, hd] at hc
  rw [hc]
  rfl

omit [Algebra ℤ S] in
private theorem exterior_implementer_even (f : W m S ≃ₗ[S] W m S) :
    (exteriorImplementer f : CliffordAlgebra (N m S)) ∈ evenOdd (N m S) 0 := by
  apply (CliffordModel.hyperbolicEquiv_even (Pi.basisFun S (Fin m)) _).mpr
  intro k x hx
  change exteriorRep m S (exteriorImplementer f : CliffordAlgebra (N m S)) x ∈ _
  rw [show exteriorRep m S (exteriorImplementer f : CliffordAlgebra (N m S)) =
    ↑(exteriorUnit f) from (exteriorRep m S).apply_symm_apply _]
  exact exterior_map_evenOdd f.toLinearMap k x hx

omit [Algebra ℤ S] in
private theorem top_alternating (f : W m S →ₗ[S] W m S) (v : Fin m → W m S) :
    ExteriorAlgebra.map f (ExteriorAlgebra.ιMulti S m v) =
      LinearMap.det f • ExteriorAlgebra.ιMulti S m v := by
  let b := Pi.basisFun S (Fin m)
  have he : (ExteriorAlgebra.map f).toLinearMap.compAlternatingMap (ExteriorAlgebra.ιMulti S m) =
      (LinearMap.det f) • ExteriorAlgebra.ιMulti S m := by
    have hcomp : ExteriorAlgebra.ιMulti S m (f ∘ b) =
        LinearMap.det f • ExteriorAlgebra.ιMulti S m b := by
      let g : W m S [⋀^Fin m]→ₗ[S] Ext m S :=
        ((LinearMap.toSpanSingleton S _ (ExteriorAlgebra.ιMulti S m b))).compAlternatingMap b.det
      have hg : ExteriorAlgebra.ιMulti S m = g := by
        apply b.ext_alternating
        intro i hi
        let σ : Equiv.Perm (Fin m) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
        change ExteriorAlgebra.ιMulti S m (b ∘ σ) = b.det (b ∘ σ) • _
        rw [AlternatingMap.map_perm, AlternatingMap.map_perm, b.det_self]
        simp only [Units.smul_def, zsmul_eq_mul, mul_one]
        exact (Int.cast_smul_eq_zsmul (R := S) (σ.sign : ℤ) _).symm
      nth_rw 1 [hg]
      change b.det (f ∘ b) • ExteriorAlgebra.ιMulti S m b = _
      rw [b.det_comp, b.det_self, mul_one]
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change ExteriorAlgebra.map f (ExteriorAlgebra.ιMulti S m (b ∘ σ)) =
      LinearMap.det f • ExteriorAlgebra.ιMulti S m (b ∘ σ)
    rw [ExteriorAlgebra.map_apply_ιMulti, show f ∘ (b ∘ σ) = (f ∘ b) ∘ σ from rfl,
      AlternatingMap.map_perm, AlternatingMap.map_perm, hcomp, smul_comm]
  exact DFunLike.congr_fun he v

omit [Algebra ℤ S] in
private theorem exterior_map_reverse (f : W m S →ₗ[S] W m S) (x : Ext m S) :
    ExteriorAlgebra.map f (reverse (Q := (0 : QuadraticForm S (W m S))) x) =
      reverse (Q := (0 : QuadraticForm S (W m S))) (ExteriorAlgebra.map f x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [reverse.commutes]
  | ι x =>
    change ExteriorAlgebra.map f (reverse (ι (0 : QuadraticForm S (W m S)) x)) =
      reverse (ExteriorAlgebra.map f (ExteriorAlgebra.ι S x))
    rw [reverse_ι, ExteriorAlgebra.map_apply_ι]
    exact (reverse_ι _).symm
  | mul x y hx hy => rw [reverse.map_mul, map_mul, map_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Algebra ℤ S] in
private def exteriorCreation (m : ℕ) (S : Type*) [CommRing S] :
    Ext m S →ₐ[S] CliffordAlgebra (N m S) :=
  CliffordAlgebra.map (⟨(LinearMap.inr S (Module.Dual S (W m S)) (W m S)),
    fun x => show (0 : Module.Dual S (W m S)) x = 0 from rfl⟩ :
    (0 : QuadraticForm S (W m S)) →qᵢ N m S)

omit [Algebra ℤ S] in
private theorem exterior_creation_apply (x : Ext m S) :
    exteriorRep m S (exteriorCreation m S x) = Algebra.lmul S (Ext m S) x := by
  have h : (exteriorRep m S).toAlgHom.comp (exteriorCreation m S) = Algebra.lmul S (Ext m S) := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change exteriorRep m S (CliffordAlgebra.map _ (ι _ v)) =
      Algebra.lmul S (Ext m S) (ExteriorAlgebra.ι S v)
    rw [map_apply_ι, CliffordModel.hyperbolicEquiv_ι]
    apply LinearMap.ext
    intro y
    change ExteriorAlgebra.ι S v * y + contractLeft (Q := (0 : QuadraticForm S (W m S))) 0 y = _
    simp
  exact DFunLike.congr_fun h x

omit [Algebra ℤ S] in
private theorem exterior_creation_reverse (x : Ext m S) :
    reverse (exteriorCreation m S x) =
      exteriorCreation m S (reverse (Q := (0 : QuadraticForm S (W m S))) x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [reverse.commutes]
  | ι v => simp only [exteriorCreation, map_apply_ι, reverse_ι]
  | mul x y hx hy => rw [map_mul, reverse.map_mul, reverse.map_mul, map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Algebra ℤ S] in
private theorem top_mul_generator (v : Fin m → W m S)
    (h : ∀ i, ∃ j, v j = (Pi.basisFun S (Fin m)) i)
    (x : W m S) :
    ExteriorAlgebra.ιMulti S m v * ExteriorAlgebra.ι S x = 0 := by
  let L := (LinearMap.mulLeft S (ExteriorAlgebra.ιMulti S m v)).comp
    (ExteriorAlgebra.ι S : W m S →ₗ[S] Ext m S)
  suffices L = 0 from DFunLike.congr_fun this x
  apply (Pi.basisFun S (Fin m)).ext
  intro k
  obtain ⟨i, hi⟩ := h k
  change ExteriorAlgebra.ιMulti S m v * ExteriorAlgebra.ι S ((Pi.basisFun S (Fin m)) k) = 0
  rw [← hi]
  let w : Fin 1 → W m S := fun _ => v i
  have hw : ExteriorAlgebra.ιMulti S 1 w = ExteriorAlgebra.ι S (v i) := by simp [w]
  rw [← hw, ExteriorAlgebra.ιMulti_mul_ιMulti]
  apply (ExteriorAlgebra.ιMulti S (m + 1)).map_eq_zero_of_eq
    (i := Fin.castAdd 1 i) (j := Fin.natAdd m 0)
  · simp [w]
  · apply ne_of_lt
    change i.val < m + 0
    simp

omit [Algebra ℤ S] in
private theorem exterior_implementer_norm (f : W m S ≃ₗ[S] W m S) :
    reverse (exteriorImplementer f : CliffordAlgebra (N m S)) * exteriorImplementer f =
      algebraMap S _ (LinearMap.det f.toLinearMap) := by
  let a := exteriorImplementer f
  have hc (x : HyperbolicModule S m) :
      Commute (reverse (a : CliffordAlgebra (N m S)) * (a : CliffordAlgebra (N m S)))
        (ι (N m S) x) := by
    let y := ι (N m S) (x.1.comp f.symm.toLinearMap, f x.2)
    have h : (a : CliffordAlgebra (N m S)) * ι (N m S) x = y * (a : CliffordAlgebra (N m S)) := by
      have he := exterior_implementer_action f x.1 x.2
      simpa [unitConj, a, y, mul_assoc] using
        congrArg (fun z => z * (a : CliffordAlgebra (N m S))) he
    have hr : ι (N m S) x * reverse (a : CliffordAlgebra (N m S)) =
        reverse (a : CliffordAlgebra (N m S)) * y := by
      simpa only [y, reverse.map_mul, reverse_ι] using congrArg (reverse (Q := N m S)) h
    show (reverse (a : CliffordAlgebra (N m S)) * (a : CliffordAlgebra (N m S))) * _ =
      _ * (reverse (a : CliffordAlgebra (N m S)) * (a : CliffordAlgebra (N m S)))
    rw [mul_assoc, h, ← mul_assoc, ← hr, mul_assoc]
  obtain ⟨r, hr⟩ := (CliffordModel.hyperbolic_scalar_centralizer (Pi.basisFun S (Fin m)) _).mp hc
  rw [hr]
  let b := Pi.basisFun S (Fin m)
  let s : Set.powersetCard (Fin m) m := Set.powersetCard.ofCard (s := Finset.univ) (by simp)
  let v : Fin m → W m S := b ∘ Set.powersetCard.ofFinEmbEquiv.symm s
  let ω := ExteriorAlgebra.ιMulti S m v
  have hω : ω = b.ExteriorAlgebra Finset.univ := (ExteriorAlgebra.basis_apply_ofCard b (by simp)).symm
  have hv (i : Fin m) : ∃ j, v j = b i := by
    obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr
      (by change i ∈ Finset.univ; simp)
    exact ⟨j, congrArg b hj⟩
  let E := exteriorCreation m S ω
  let e := exteriorRep m S
  have hea : e (a : CliffordAlgebra (N m S)) = (ExteriorAlgebra.map f.toLinearMap).toLinearMap :=
    e.apply_symm_apply _
  -- Multiplication by the top wedge only sees the scalar term, which the exterior map fixes.
  have hE : E * (a : CliffordAlgebra (N m S)) = E := by
    apply e.injective
    rw [map_mul, exterior_creation_apply, hea]
    apply LinearMap.ext
    intro x
    change ω * ExteriorAlgebra.map f.toLinearMap x = ω * x
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r => simp
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | ι_mul x w hx =>
      rw [map_mul, ExteriorAlgebra.map_apply_ι, ← mul_assoc, ← mul_assoc,
        top_mul_generator v hv, top_mul_generator v hv, zero_mul, zero_mul]
  have hrev := congrArg (reverse (Q := N m S)) hE
  rw [reverse.map_mul] at hrev
  have hfix : e (reverse (a : CliffordAlgebra (N m S)))
      (reverse (Q := (0 : QuadraticForm S (W m S))) ω) =
      reverse (Q := (0 : QuadraticForm S (W m S))) ω := by
    have ht := congrArg (fun c => e c (1 : Ext m S)) hrev
    rw [map_mul, exterior_creation_reverse] at ht
    rw [exterior_creation_apply] at ht
    change e (reverse (a : CliffordAlgebra (N m S))) (reverse ω * 1) = reverse ω * 1 at ht
    simpa only [mul_one] using ht
  have hdet : e (a : CliffordAlgebra (N m S)) (reverse (Q := (0 : QuadraticForm S (W m S))) ω) =
      LinearMap.det f.toLinearMap • reverse (Q := (0 : QuadraticForm S (W m S))) ω := by
    rw [hea]
    change ExteriorAlgebra.map f.toLinearMap (reverse ω) = _
    rw [exterior_map_reverse, top_alternating, map_smul]
  have ht := congrArg (fun c => e c (reverse (Q := (0 : QuadraticForm S (W m S))) ω)) hr
  rw [map_mul, Module.End.mul_apply, hdet, map_smul, hfix, AlgEquiv.commutes] at ht
  have ht' : LinearMap.det f.toLinearMap • reverse (Q := (0 : QuadraticForm S (W m S))) ω =
      r • reverse (Q := (0 : QuadraticForm S (W m S))) ω := ht
  have ht'' := congrArg (reverse (Q := (0 : QuadraticForm S (W m S)))) ht'
  rw [map_smul, map_smul, reverse_reverse, hω] at ht''
  have hh := congrArg (b.ExteriorAlgebra.coord Finset.univ) ht''
  have hcoord : b.ExteriorAlgebra.coord Finset.univ (b.ExteriorAlgebra Finset.univ) = 1 := by
    simp [Basis.coord_apply]
  simp only [map_smul, hcoord, smul_eq_mul, mul_one] at hh
  rw [hh]

omit [Algebra ℤ S] in
private theorem map_isometry_reverse {V W : Type*} [AddCommGroup V] [Module S V]
    [AddCommGroup W] [Module S W] {q : QuadraticForm S V} {q' : QuadraticForm S W}
    (f : q →qᵢ q') (x : CliffordAlgebra q) :
    CliffordAlgebra.map f (reverse x) = reverse (CliffordAlgebra.map f x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [reverse.commutes]
  | ι x => simp only [reverse_ι, map_apply_ι]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => rw [reverse.map_mul, map_mul, map_mul, reverse.map_mul, hx, hy]

omit [Algebra ℤ S] in
private theorem map_isometry_evenOdd {V W : Type*} [AddCommGroup V] [Module S V]
    [AddCommGroup W] [Module S W] {q : QuadraticForm S V} {q' : QuadraticForm S W}
    (f : q →qᵢ q') {k : ZMod 2} {x : CliffordAlgebra q} (hx : x ∈ evenOdd q k) :
    CliffordAlgebra.map f x ∈ evenOdd q' k := by
  have hm : (evenOdd q k).map (CliffordAlgebra.map f).toLinearMap ≤ evenOdd q' k := by
    simp only [evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_map]
    refine iSup_mono fun i => ?_
    gcongr
    rw [← LinearMap.range_comp]
    exact LinearMap.range_comp_le_range _ _
  exact hm (Submodule.mem_map_of_mem hx)

omit [Algebra ℤ S] in
private theorem native_pair_coordinates (d : Module.Dual S (W m S)) (x : W m S) :
    (hyperbolicBasis S m).equivFun (d, x) = Sum.elim x (fun i => d (Pi.single i 1)) := by
  funext j
  change PairIndex m at j
  cases j with
  | inl i =>
    change ((Pi.basisFun S (Fin m)).dualBasis.prod (Pi.basisFun S (Fin m))).repr
      (d, x) (Sum.inr i) = x i
    simp
  | inr i =>
    change ((Pi.basisFun S (Fin m)).dualBasis.prod (Pi.basisFun S (Fin m))).repr
      (d, x) (Sum.inl i) = d (Pi.single i 1)
    simp

omit [Algebra ℤ S] in
private theorem dual_is_dotProduct (d : Module.Dual S (W m S)) (x : W m S) :
    d x = x ⬝ᵥ (fun i => d (Pi.single i 1)) := by
  have hx : ∑ i : Fin m, x i • (Pi.single i 1 : Fin m → S) = x := by
    simpa using (Pi.basisFun S (Fin m)).sum_repr x
  conv_lhs => rw [← hx]
  simp [dotProduct, smul_eq_mul]

omit [Algebra ℤ S] in
private theorem native_middle_coordinates (A : Block m S) (hA : IsUnit A.det)
    (x : HyperbolicModule S m) :
    let f := Matrix.toLinearEquiv (Pi.basisFun S (Fin m)) A hA
    (hyperbolicBasis S m).equivFun (x.1.comp f.symm.toLinearMap, f x.2) =
      middle A *ᵥ (hyperbolicBasis S m).equivFun x := by
  obtain ⟨d, x⟩ := x
  let f := Matrix.toLinearEquiv (Pi.basisFun S (Fin m)) A hA
  change (hyperbolicBasis S m).equivFun (d.comp f.symm.toLinearMap, f x) =
    middle A *ᵥ (hyperbolicBasis S m).equivFun (d, x)
  have h1 (v : W m S) : f v = A *ᵥ v := by
    change Matrix.toLin (Pi.basisFun S (Fin m)) (Pi.basisFun S (Fin m)) A v = _
    rw [Matrix.toLin_eq_toLin']
    rfl
  have h2 : (fun i => (d.comp f.symm.toLinearMap) (Pi.single i 1)) =
      (A⁻¹)ᵀ *ᵥ (fun i => d (Pi.single i 1)) := by
    let y : Fin m → S := fun i => d (Pi.single i 1)
    have h (v : W m S) : (d.comp f.symm.toLinearMap) v = v ⬝ᵥ ((A⁻¹)ᵀ *ᵥ y) := by
      obtain ⟨w, rfl⟩ := f.surjective v
      change d (f.symm (f w)) = _
      rw [f.symm_apply_apply, h1, middle_pairing hA]
      exact dual_is_dotProduct d w
    funext i
    rw [h, single_dotProduct]
    simp [y]
  rw [native_pair_coordinates, native_pair_coordinates, h1, h2, middle, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  rfl

set_option maxRecDepth 2000 in
private theorem middle_lift (A : Block m S) (hA : IsUnit A.det) :
    ∃ a, IsCliffordLift (middle A) a 0 A.det := by
  let f := Matrix.toLinearEquiv (Pi.basisFun S (Fin m)) A hA
  let iso := splitIsometry m S
  let e := CliffordAlgebra.equivOfIsometry iso
  let b := exteriorImplementer f
  let a := Units.map e.symm.toMonoidHom b
  have hdet : LinearMap.det f.toLinearMap = A.det := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun S (Fin m))]
    exact congrArg Matrix.det (LinearMap.toMatrix_toLin _ _ _)
  have he : e (a : CliffordAlgebra (splitForm m S)) = (b : CliffordAlgebra (N m S)) :=
    e.apply_symm_apply _
  have hinv : e (↑a⁻¹ : CliffordAlgebra (splitForm m S)) = (↑b⁻¹ : CliffordAlgebra (N m S)) := by
    change e (↑(Units.map e.symm.toMonoidHom b)⁻¹ : CliffordAlgebra (splitForm m S)) = _
    rw [← map_inv]
    exact e.apply_symm_apply _
  refine ⟨a, ?_, ?_, ?_⟩
  · exact map_isometry_evenOdd iso.symm.toIsometry (exterior_implementer_even f)
  · apply e.injective
    rw [map_mul, show e (reverse (a : CliffordAlgebra (splitForm m S))) =
      reverse (e a) from map_isometry_reverse iso.toIsometry _, he, e.commutes,
      exterior_implementer_norm, hdet]
  · intro v
    apply e.injective
    rw [unitConj, map_mul, map_mul, he, hinv]
    have hv (x : ExtendedModule m S) : e (ι (splitForm m S) x) =
        ι (N m S) (iso x) := CliffordAlgebra.map_apply_ι _ _
    rw [hv, hv]
    change unitConj b (ι (N m S) (iso ((splitCoordinates m S).symm v))) = _
    let x := iso ((splitCoordinates m S).symm v)
    change unitConj b (ι (N m S) (x.1, x.2)) = _
    rw [exterior_implementer_action]
    apply congrArg (ι (N m S))
    apply (hyperbolicBasis S m).equivFun.injective
    rw [native_middle_coordinates A hA x]
    have hc (z : PairIndex m → S) :
        (hyperbolicBasis S m).equivFun (iso ((splitCoordinates m S).symm z)) = z := by
      change (hyperbolicBasis S m).equivFun ((hyperbolicBasis S m).equivFun.symm
        ((splitCoordinates m S) ((splitCoordinates m S).symm z))) = z
      rw [LinearEquiv.apply_symm_apply (splitCoordinates m S)]
      exact (hyperbolicBasis S m).equivFun.apply_symm_apply (z : Lex (PairIndex m) → S)
    exact congrArg ((middle A).mulVec) (hc v) |>.trans (hc _).symm

end ExteriorImplementation

private abbrev splitVector (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  SpinSpecification.vectors (integralForm m) S

private def splitScalarUnit {m : ℕ} {S : Type*} [CommRing S] [Algebra ℤ S] (u : Sˣ) :
    (ScalarClifford m S)ˣ :=
  Units.map (algebraMap S (ScalarClifford m S)).toMonoidHom u

private theorem action_matrix_on_vectors {M : Matrix (PairIndex m) (PairIndex m) S}
    {a : (ScalarClifford m S)ˣ} (h : HasActionMatrix m a M) (x : ExtendedModule m S) :
    unitConj a (splitVector m S x) =
      splitVector m S ((splitCoordinates m S).symm (M *ᵥ splitCoordinates m S x)) := by
  obtain ⟨g, hg, rfl⟩ := h
  have hm : vectorMatrix m g *ᵥ (splitCoordinates m S x : PairIndex m → S) =
      splitCoordinates m S (g x) := LinearMap.toMatrix_mulVec_repr _ _ _ _
  rw [hm, LinearEquiv.symm_apply_apply]
  exact (hg x).symm

open private vectors_injective changeModule changeModule_basis changeModule_coord
  changeCoefficients_reverse changeCoefficients_even changeCoefficients_vector reversion_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private theorem action_matrix_unique {M N : Matrix (PairIndex m) (PairIndex m) S}
    {a : (ScalarClifford m S)ˣ} (hM : HasActionMatrix m a M) (hN : HasActionMatrix m a N) :
    M = N := by
  obtain ⟨g, hg, rfl⟩ := hM
  obtain ⟨h, hh, rfl⟩ := hN
  have he : g = h := LinearEquiv.ext fun x =>
    vectors_injective (integralForm m) S (hyperbolicBasis ℤ m) ((hg x).trans (hh x).symm)
  rw [he]

private theorem action_matrix_unit_det {M : Matrix (PairIndex m) (PairIndex m) S}
    {a : (ScalarClifford m S)ˣ} (h : HasActionMatrix m a M) : IsUnit M.det := by
  obtain ⟨g, _, rfl⟩ := h
  let b : Module.Basis (PairIndex m) S (ExtendedModule m S) := splitBasis m S
  change IsUnit (LinearMap.toMatrix b b g.toLinearMap).det
  exact LinearEquiv.isUnit_det g b b

private theorem action_matrix_mul {M N : Matrix (PairIndex m) (PairIndex m) S}
    {a b : (ScalarClifford m S)ˣ} (ha : HasActionMatrix m a M) (hb : HasActionMatrix m b N) :
    HasActionMatrix m (a * b) (M * N) := by
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨h, hh, rfl⟩ := hb
  refine ⟨h.trans g, fun x => ?_, ?_⟩
  · change splitVector m S (g (h x)) = unitConj (a * b) (splitVector m S x)
    rw [unitConj_mul_units]
    exact (hg (h x)).trans (congrArg (unitConj a) (hh x))
  · exact LinearMap.toMatrix_comp _ _ _ _ _

private theorem matrix_map_det {I B C : Type*} [Fintype I] [DecidableEq I]
    [CommRing B] [CommRing C] (f : B →+* C) (M : Matrix I I B) :
    (M.map f).det = f M.det := (f.map_det M).symm

set_option maxRecDepth 2000 in
set_option maxHeartbeats 600000 in
private theorem action_matrix_after_map {T : Type*} [CommRing T] [Algebra ℤ T] (f : S →ₐ[ℤ] T)
    {M : Matrix (PairIndex m) (PairIndex m) S} {a : (ScalarClifford m S)ˣ}
    (h : HasActionMatrix m a M) :
    HasActionMatrix m (Units.map
      (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom a) (M.map f) := by
  have hu : IsUnit (M.map f).det :=
    (matrix_map_det f.toRingHom M).symm ▸ (action_matrix_unit_det h).map f
  obtain ⟨g, hg, rfl⟩ := h
  let q := integralForm m
  let b := hyperbolicBasis ℤ m
  let e := SpinSpecification.coefficientMap q S f
  let a' := Units.map e.toMonoidHom a
  let M' := (vectorMatrix m g).map f
  let g' := Matrix.toLinearEquiv (b.baseChange T) M' hu
  have hmat : vectorMatrix m g' = M' := LinearMap.toMatrix_toLin _ _ _
  refine ⟨g', ?_, hmat⟩
  intro x
  let L := (splitVector m T).comp g'.toLinearMap
  let L' := ((LinearMap.mulRight T (↑a'⁻¹ : ScalarClifford m T)).comp
    (LinearMap.mulLeft T (a' : ScalarClifford m T))).comp (splitVector m T)
  suffices L = L' from DFunLike.congr_fun this x
  apply (b.baseChange T).ext
  intro j
  have hv : changeModule f (g (b.baseChange S j)) = g' (b.baseChange T j) := by
    apply (b.baseChange T).equivFun.injective
    funext i
    change (b.baseChange T).coord i (changeModule f (g (b.baseChange S j))) =
      (b.baseChange T).coord i (g' (b.baseChange T j))
    rw [changeModule_coord, Module.Basis.coord_apply, Module.Basis.coord_apply]
    have ht := LinearMap.toMatrix_apply (b.baseChange T) (b.baseChange T) g'.toLinearMap i j
    have hs := LinearMap.toMatrix_apply (b.baseChange S) (b.baseChange S) g.toLinearMap i j
    have hf := congrArg (fun N : Matrix (PairIndex m) (PairIndex m) T => N i j) hmat.symm
    exact (congrArg f hs).symm.trans (hf.trans ht)
  change splitVector m T (g' (b.baseChange T j)) =
    unitConj a' (splitVector m T (b.baseChange T j))
  rw [← hv, ← changeModule_basis b f j]
  rw [← changeCoefficients_vector, ← changeCoefficients_vector]
  change e (splitVector m S (g (b.baseChange S j))) =
    unitConj a' (e (splitVector m S (b.baseChange S j)))
  rw [hg]
  simp [SpinSpecification.conjugate, unitConj, a']

private theorem intrinsic_action_matrix {M : Matrix (PairIndex m) (PairIndex m) S}
    {a : (ScalarClifford m S)ˣ} (h : HasActionMatrix m a M) (v : PairIndex m → S) :
    unitConj (Units.map (integralCliffordEquiv m S).toMonoidHom a)
        (ι (splitForm m S) ((splitCoordinates m S).symm v)) =
      ι (splitForm m S) ((splitCoordinates m S).symm (M *ᵥ v)) := by
  have he (x : ExtendedModule m S) :
      (integralCliffordEquiv m S) (splitVector m S x) = ι (splitForm m S) x :=
    cliffordEquiv_vector (integralForm m) S (hyperbolicBasis ℤ m) x
  have hh := congrArg (integralCliffordEquiv m S)
    (action_matrix_on_vectors h ((splitCoordinates m S).symm v))
  simp only [unitConj, ← map_inv]
  change (integralCliffordEquiv m S) (a : ScalarClifford m S) * _ *
    (integralCliffordEquiv m S) (↑a⁻¹ : ScalarClifford m S) = _
  simpa only [LinearEquiv.apply_symm_apply, unitConj, map_mul, he] using hh

private def IsTensorLift (M : Matrix (PairIndex m) (PairIndex m) S)
    (a : (ScalarClifford m S)ˣ) (r : S) : Prop :=
  (a : ScalarClifford m S) ∈ SpinSpecification.evenPart (integralForm m) S ∧
    SpinSpecification.reversion (integralForm m) S a * (a : ScalarClifford m S) =
      algebraMap S _ r ∧ HasActionMatrix m a M

private theorem IsTensorLift.mem_spin {M : Matrix (PairIndex m) (PairIndex m) S}
    {a : (ScalarClifford m S)ˣ} (ha : IsTensorLift M a 1) :
    a ∈ SpinSpecification.spinUnits (integralForm m) S := by
  obtain ⟨g, hg, _⟩ := ha.2.2
  refine ⟨ha.1, ha.2.1.trans (map_one _), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, hg x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨g.symm x, ?_⟩
    have heq := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at heq
    rw [heq]
    exact (unitConj_cancel_left a _).symm

private theorem intrinsic_to_tensor_lift {M : Matrix (PairIndex m) (PairIndex m) S}
    (hM : IsUnit M.det) {a : (CliffordAlgebra (splitForm m S))ˣ} {r : S}
    (ha : IsCliffordLift M a 0 r) :
    IsTensorLift M (Units.map (integralCliffordEquiv m S).symm.toMonoidHom a) r := by
  let q := integralForm m
  let b := hyperbolicBasis ℤ m
  let e := integralCliffordEquiv m S
  let a₀ := Units.map e.symm.toMonoidHom a
  have h₀ : e (a₀ : ScalarClifford m S) = a := e.apply_symm_apply _
  refine ⟨(cliffordEquiv_even q S b _).mp (h₀.symm ▸ ha.1), e.injective ?_,
    intrinsic_implementer_to_action a M hM ha.2.2⟩
  rw [map_mul, show e (SpinSpecification.reversion q S a₀) = reverse (e a₀) from
    baseChangeEquiv_reverse S q b a₀, h₀, e.commutes]
  exact ha.2.1

private theorem IsTensorLift.map {T : Type*} [CommRing T] [Algebra ℤ T] (f : S →ₐ[ℤ] T)
    {M : Matrix (PairIndex m) (PairIndex m) S} {a : (ScalarClifford m S)ˣ} {r : S}
    (ha : IsTensorLift M a r) :
    IsTensorLift (M.map f)
      (Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom a) (f r) := by
  let q := integralForm m
  let e := SpinFunctor.changeCoefficients q f
  refine ⟨changeCoefficients_even q f ha.1, ?_, action_matrix_after_map f ha.2.2⟩
  change SpinSpecification.reversion q T (e a) * e a = algebraMap T _ (f r)
  rw [← changeCoefficients_reverse, ← map_mul, ha.2.1]
  simp [SpinFunctor.changeCoefficients, Algebra.TensorProduct.algebraMap_apply]

private theorem tensor_scalar_lift (u : Sˣ) :
    IsTensorLift (1 : Matrix (PairIndex m) (PairIndex m) S) (splitScalarUnit u) ((u : S) ^ 2) := by
  let q := integralForm m
  let b := hyperbolicBasis ℤ m
  let e := integralCliffordEquiv m S
  let a : (CliffordAlgebra (splitForm m S))ˣ :=
    Units.map (algebraMap S (CliffordAlgebra (splitForm m S))).toMonoidHom u
  have ha : IsCliffordLift (1 : Matrix (PairIndex m) (PairIndex m) S) a 0 ((u : S) ^ 2) := by
    refine ⟨?_, ?_, fun v => ?_⟩
    · change algebraMap S _ (u : S) ∈ evenOdd (splitForm m S) 0
      rw [Algebra.algebraMap_eq_smul_one]
      exact (evenOdd _ _).smul_mem _ (SetLike.one_mem_graded _)
    · change reverse (algebraMap S _ (u : S)) * algebraMap S _ (u : S) =
        algebraMap S _ ((u : S) ^ 2)
      rw [reverse.commutes, ← map_mul, pow_two]
    · rw [one_mulVec]
      exact (unitConj_eq_self_iff _ _).mpr (Algebra.commutes _ _)
  have h := intrinsic_to_tensor_lift (by simp : IsUnit
    (1 : Matrix (PairIndex m) (PairIndex m) S).det) ha
  convert h using 2
  apply Units.ext
  exact (e.symm.commutes (u : S)).symm

open private even_mul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private theorem IsTensorLift.mul {M N : Matrix (PairIndex m) (PairIndex m) S}
    {a b : (ScalarClifford m S)ˣ} {r s : S}
    (ha : IsTensorLift M a r) (hb : IsTensorLift N b s) :
    IsTensorLift (M * N) (a * b) (r * s) := by
  let q := integralForm m
  let d := hyperbolicBasis ℤ m
  refine ⟨even_mul q S d ha.1 hb.1, ?_, action_matrix_mul ha.2.2 hb.2.2⟩
  change SpinSpecification.reversion q S ((a : ScalarClifford m S) * b) * (a * b) = _
  rw [reversion_mul q S d, mul_assoc, ← mul_assoc (SpinSpecification.reversion q S a),
    ha.2.1, ← mul_assoc (SpinSpecification.reversion q S b),
    ← Algebra.commutes r (SpinSpecification.reversion q S b), mul_assoc, hb.2.1, ← map_mul]

private theorem raw_factor_lift (P Q A : Block m S) (hP : IsAlternating P) (hQ : IsAlternating Q)
    (hA : IsUnit A.det) :
    ∃ a, IsCliffordLift (lower P * middle A * upper Q) a 0 A.det := by
  obtain ⟨p, hp⟩ := alternating_shear_lift false P hP
  obtain ⟨q, hq⟩ := alternating_shear_lift true Q hQ
  obtain ⟨a, ha⟩ := middle_lift A hA
  exact ⟨p * a * q, by simpa only [shearMatrix, Bool.false_eq_true, ite_false, ite_true,
    add_zero, one_mul, mul_one] using (hp.mul ha).mul hq⟩

omit [Algebra ℤ S] in
private theorem factor_det (P Q A : Block m S) (hA : IsUnit A.det) :
    (lower P * middle A * upper Q).det = 1 := by
  simp only [det_mul, lower, upper, middle, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁,
    det_one, one_mul, mul_one, det_transpose]
  rw [← det_mul, mul_nonsing_inv _ hA, det_one]

private theorem raw_tensor_factor_lift (P Q A : Block m S) (hP : IsAlternating P)
    (hQ : IsAlternating Q) (hA : IsUnit A.det) :
    ∃ a, IsTensorLift (lower P * middle A * upper Q) a A.det := by
  obtain ⟨a, ha⟩ := raw_factor_lift P Q A hP hQ hA
  exact ⟨_, intrinsic_to_tensor_lift (by rw [factor_det P Q A hA]; exact isUnit_one) ha⟩


section UniversalLift

open MvPolynomial

private abbrev FactorIndex (m : ℕ) :=
  (AlternatingIndex m ⊕ AlternatingIndex m) ⊕ (Fin m × Fin m)

private abbrev FactorPolynomial (m : ℕ) := MvPolynomial (FactorIndex m) ℤ

private def factorVariables (P Q A : Block m S) : FactorIndex m → S
  | Sum.inl (Sum.inl i) => P i.val.1 i.val.2
  | Sum.inl (Sum.inr i) => Q i.val.1 i.val.2
  | Sum.inr ij => A ij.1 ij.2

private def genericBlock (m : ℕ) : Block m (FactorPolynomial m) :=
  Matrix.of fun i j => X (Sum.inr (i, j))

private abbrev FactorRing (m : ℕ) :=
  Localization.Away (genericBlock m).det

private def factorX (m : ℕ) (i : FactorIndex m) : FactorRing m :=
  algebraMap (FactorPolynomial m) (FactorRing m) (X i)

private def genericLower (m : ℕ) :=
  (alternatingCoordinates m (FactorRing m)).symm (fun i => factorX m (Sum.inl (Sum.inl i)))

private def genericUpper (m : ℕ) :=
  (alternatingCoordinates m (FactorRing m)).symm (fun i => factorX m (Sum.inl (Sum.inr i)))

private def genericMiddle (m : ℕ) : Block m (FactorRing m) :=
  (genericBlock m).map (algebraMap (FactorPolynomial m) (FactorRing m))

private theorem genericMiddle_det (m : ℕ) : IsUnit (genericMiddle m).det := by
  exact (matrix_map_det (algebraMap (FactorPolynomial m) (FactorRing m))
    (genericBlock m)).symm ▸ IsLocalization.Away.algebraMap_isUnit _

private def factorEval (P Q A : Block m S) (hA : IsUnit A.det) : FactorRing m →ₐ[ℤ] S :=
  IsLocalization.Away.liftAlgHom (genericBlock m).det
    (f := aeval (factorVariables P Q A)) (by
      let f := aeval (R := ℤ) (factorVariables P Q A)
      have he : (genericBlock m).map f = A := by
        ext i j
        exact aeval_X (factorVariables P Q A) (Sum.inr (i, j))
      have hu : IsUnit ((genericBlock m).map f).det := (congrArg Matrix.det he).symm ▸ hA
      exact (matrix_map_det f.toRingHom (genericBlock m)) ▸ hu)

private theorem factorEval_X (P Q A : Block m S) (hA : IsUnit A.det) (i : FactorIndex m) :
    factorEval P Q A hA (factorX m i) = factorVariables P Q A i := by
  rw [factorEval, factorX, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact aeval_X _ _

private theorem factorRing_hom_ext {f g : FactorRing m →ₐ[ℤ] S}
    (h : ∀ i, f (factorX m i) = g (factorX m i)) : f = g := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (genericBlock m).det)
  have he : f.comp (IsScalarTower.toAlgHom ℤ (FactorPolynomial m) (FactorRing m)) =
      g.comp (IsScalarTower.toAlgHom ℤ (FactorPolynomial m) (FactorRing m)) := by
    apply MvPolynomial.algHom_ext
    exact h
  exact congrArg AlgHom.toRingHom he

private theorem factorEval_middle (P Q A : Block m S) (hA : IsUnit A.det) :
    (genericMiddle m).map (factorEval P Q A hA) = A := by
  ext i j
  change factorEval P Q A hA (factorX m (Sum.inr (i,j))) = A i j
  exact factorEval_X P Q A hA _

omit [Algebra ℤ S] in
private theorem alternating_ofCoordinates_map {D : Type*} [CommRing D]
    (f : D →+* S) (x : AlternatingIndex m → D) :
    ((alternatingCoordinates m D).symm x).val.map f =
      ((alternatingCoordinates m S).symm (f ∘ x)).val := by
  ext i j
  simp only [alternatingCoordinates, Equiv.coe_fn_symm_mk, Matrix.map_apply, of_apply,
    Function.comp_apply]
  split
  · rfl
  · split <;> simp

private theorem factorEval_lower (P Q A : Block m S) (hP : IsAlternating P)
    (hA : IsUnit A.det) :
    (genericLower m).val.map (factorEval P Q A hA) = P := by
  change (genericLower m).val.map (factorEval P Q A hA).toRingHom = P
  rw [genericLower, alternating_ofCoordinates_map (factorEval P Q A hA).toRingHom]
  have hf : (factorEval P Q A hA).toRingHom ∘ (fun i => factorX m (Sum.inl (Sum.inl i))) =
      alternatingCoordinates m S ⟨P, hP⟩ := by
    funext i
    exact factorEval_X P Q A hA _
  rw [hf, Equiv.symm_apply_apply]

private theorem factorEval_upper (P Q A : Block m S) (hQ : IsAlternating Q)
    (hA : IsUnit A.det) :
    (genericUpper m).val.map (factorEval P Q A hA) = Q := by
  change (genericUpper m).val.map (factorEval P Q A hA).toRingHom = Q
  rw [genericUpper, alternating_ofCoordinates_map (factorEval P Q A hA).toRingHom]
  have hf : (factorEval P Q A hA).toRingHom ∘ (fun i => factorX m (Sum.inl (Sum.inr i))) =
      alternatingCoordinates m S ⟨Q, hQ⟩ := by
    funext i
    exact factorEval_X P Q A hA _
  rw [hf, Equiv.symm_apply_apply]

omit [Algebra ℤ S] in
private theorem map_split_blocks {D : Type*} [CommRing D] (f : D →+* S)
    (A B C D' : Block m D) :
    (fromBlocks A B C D').map f = fromBlocks (A.map f) (B.map f) (C.map f) (D'.map f) := by
  ext i j
  cases i <;> cases j <;> rfl

private theorem factor_map {D : Type*} [CommRing D] (f : D →+* S)
    (P Q A : Block m D) (hA : IsUnit A.det) :
    (lower P * middle A * upper Q).map f =
      lower (P.map f) * middle (A.map f) * upper (Q.map f) := by
  have hi : (A.map f)⁻¹ = A⁻¹.map f := by
    apply inv_eq_right_inv
    rw [← Matrix.map_mul, mul_nonsing_inv _ hA]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have htrans : (A⁻¹ᵀ).map f = (A⁻¹.map f)ᵀ := rfl
  simp only [Matrix.map_mul, lower, upper, middle, map_split_blocks, htrans, hi,
    Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f)]

-- Choose the unscaled lift once over the coefficient ring of the orthogonal chart.
private def genericFactor (m : ℕ) : (ScalarClifford m (FactorRing m))ˣ :=
  (raw_tensor_factor_lift (genericLower m).val (genericUpper m).val (genericMiddle m)
    (genericLower m).property (genericUpper m).property (genericMiddle_det m)).choose

private def factorUnit (P Q A : Block m S) (hA : IsUnit A.det) : (ScalarClifford m S)ˣ :=
  Units.map (SpinSpecification.coefficientMap (integralForm m) (FactorRing m)
    (factorEval P Q A hA)).toMonoidHom (genericFactor m)

private theorem factorUnit_congr {P Q A P' Q' A' : Block m S}
    {h : IsUnit A.det} {h' : IsUnit A'.det} (hP : P = P') (hQ : Q = Q') (hA : A = A') :
    factorUnit P Q A h = factorUnit P' Q' A' h' := by
  subst P'
  subst Q'
  subst A'
  rfl

private theorem factorUnit_lift (P Q A : Block m S) (hP : IsAlternating P) (hQ : IsAlternating Q)
    (hA : IsUnit A.det) :
    IsTensorLift (lower P * middle A * upper Q) (factorUnit P Q A hA) A.det := by
  have h := (raw_tensor_factor_lift (genericLower m).val (genericUpper m).val
    (genericMiddle m) (genericLower m).property (genericUpper m).property
    (genericMiddle_det m)).choose_spec
  let f := factorEval P Q A hA
  have hf := h.map f
  change IsTensorLift ((lower (genericLower m).val * middle (genericMiddle m) *
    upper (genericUpper m).val).map f.toRingHom) (factorUnit P Q A hA) _ at hf
  rw [factor_map f.toRingHom _ _ _ (genericMiddle_det m)] at hf
  have hd : f (genericMiddle m).det = A.det :=
    (matrix_map_det f.toRingHom _).symm.trans (congrArg Matrix.det (factorEval_middle P Q A hA))
  have hl : (genericLower m).val.map f.toRingHom = P := factorEval_lower P Q A hP hA
  have hu : (genericUpper m).val.map f.toRingHom = Q := factorEval_upper P Q A hQ hA
  have hm : (genericMiddle m).map f.toRingHom = A := factorEval_middle P Q A hA
  rw [hl, hu, hm, hd] at hf
  exact hf

private theorem coefficientMap_comp {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    [Algebra ℤ B] [Algebra ℤ C] [Algebra ℤ D] (f : B →ₐ[ℤ] C) (g : C →ₐ[ℤ] D)
    (a : (ScalarClifford m B)ˣ) :
    Units.map (SpinSpecification.coefficientMap (integralForm m) B (g.comp f)).toMonoidHom a =
    Units.map (SpinSpecification.coefficientMap (integralForm m) C g).toMonoidHom
      (Units.map (SpinSpecification.coefficientMap (integralForm m) B f).toMonoidHom a) := by
  apply Units.ext
  change SpinSpecification.coefficientMap (integralForm m) B (g.comp f) a.val =
    SpinSpecification.coefficientMap (integralForm m) C g
      (SpinSpecification.coefficientMap (integralForm m) B f a.val)
  generalize a.val = x
  induction x using TensorProduct.inductionOn with
  | tmul s c => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem factorUnit_natural {T : Type*} [CommRing T] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (P Q A : Block m S) (hA : IsUnit A.det) (h : IsUnit (A.map f).det) :
    factorUnit (P.map f) (Q.map f) (A.map f) h =
      Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom
        (factorUnit P Q A hA) := by
  have he : factorEval (P.map f) (Q.map f) (A.map f) h = f.comp (factorEval P Q A hA) := by
    apply factorRing_hom_ext
    intro i
    rw [AlgHom.comp_apply, factorEval_X, factorEval_X]
    rcases i with (i | i) | i <;> rfl
  unfold factorUnit
  rw [he, coefficientMap_comp]

private theorem splitScalarUnit_natural {T : Type*} [CommRing T] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (u : Sˣ) :
    Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom
        (splitScalarUnit u) = splitScalarUnit (Units.map f.toMonoidHom u) := by
  apply Units.ext
  change SpinSpecification.coefficientMap (integralForm m) S f (algebraMap S _ (u : S)) =
    algebraMap T _ (f (u : S))
  simp [SpinSpecification.coefficientMap, Algebra.TensorProduct.algebraMap_apply]

omit [Algebra ℤ S] in
private theorem normOneBlock_unit {x : S} {A : Block m S} (h : x ^ 2 * A.det = 1) :
    IsUnit A.det :=
  IsUnit.of_mul_eq_one_right _ h

omit [Algebra ℤ S] in
private theorem factor_topLeft (P Q A : Block m S) :
    (lower P * middle A * upper Q).toBlocks₁₁ = A := by
  rw [factor_blocks]
  rfl

private def chartPoint (p : ChartParameters m S) : SpinChart m S :=
  let hA := normOneBlock_unit p.normOne
  let a := splitScalarUnit p.u * factorUnit p.P p.Q p.A hA
  have h := (tensor_scalar_lift (m := m) p.u).mul
    (factorUnit_lift p.P p.Q p.A p.alternatingP p.alternatingQ hA)
  have h' : IsTensorLift (lower p.P * middle p.A * upper p.Q) a 1 := by
    simpa only [one_mul, p.normOne] using h
  ⟨a, h'.mem_spin, _, h'.2.2, by rwa [factor_topLeft]⟩

private theorem chartPoint_action (p : ChartParameters m S) :
    HasActionMatrix m (chartPoint p).val (lower p.P * middle p.A * upper p.Q) := by
  have h := (tensor_scalar_lift (m := m) p.u).mul
    (factorUnit_lift p.P p.Q p.A p.alternatingP p.alternatingQ (normOneBlock_unit p.normOne))
  simpa only [one_mul, chartPoint] using h.2.2

open private scalar_tensor_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private theorem splitScalarUnit_injective :
    Function.Injective (splitScalarUnit (m := m) (S := S)) := fun _ _ h =>
  Units.ext (scalar_tensor_injective (integralForm m) S (hyperbolicBasis ℤ m) (congrArg Units.val h))

private theorem tensor_ratio {a b : (ScalarClifford m S)ˣ}
    {M : Matrix (PairIndex m) (PairIndex m) S}
    (ha : HasActionMatrix m a M) (hb : HasActionMatrix m b M) :
    ∃ u : Sˣ, a = splitScalarUnit u * b := by
  let e := integralCliffordEquiv m S
  let F := Units.map e.toMonoidHom
  have hc (x : ExtendedModule m S) : unitConj (F a) (ι (splitForm m S) x) =
      unitConj (F b) (ι (splitForm m S) x) := by
    obtain ⟨v, rfl⟩ := (splitCoordinates m S).symm.surjective x
    exact (intrinsic_action_matrix ha v).trans (intrinsic_action_matrix hb v).symm
  obtain ⟨u, hu, _⟩ := ratio_of_implementers (F a) (F b) hc
  refine ⟨u, Units.ext (e.injective ?_)⟩
  have huv := congrArg Units.val hu
  change e (a : ScalarClifford m S) =
    e ((splitScalarUnit u : (ScalarClifford m S)ˣ) * b : (ScalarClifford m S)ˣ)
  rw [Units.val_mul, map_mul]
  change e (a : ScalarClifford m S) = e (algebraMap S _ (u : S)) * e (b : ScalarClifford m S)
  rw [e.commutes, Algebra.commutes]
  exact huv

private theorem chartPoint_injective (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :
    Function.Injective (chartPoint (m := m) (S := S)) := by
  intro p q h
  have hval := congrArg Subtype.val h
  have hp := chartPoint_action p
  have hq := chartPoint_action q
  have hmat := action_matrix_unique (hval ▸ hp) hq
  have hA : p.A = q.A := by simpa only [factor_topLeft] using congrArg toBlocks₁₁ hmat
  have hdet := normOneBlock_unit p.normOne
  let M := lower p.P * middle p.A * upper p.Q
  have hM : IsUnit M.toBlocks₁₁.det := by simpa only [M, factor_topLeft] using hdet
  have hpres : PreservesNorm M := preserves_mul
    (preserves_mul (lower_preserves p.alternatingP) (middle_preserves hdet)) (upper_preserves p.alternatingQ)
  obtain ⟨t, _, ht⟩ := (orthogonalChart m S M hM).mp hpres
  have hp' : (p.P, p.Q) = t := ht _ ⟨p.alternatingP, p.alternatingQ, by rw [show M.toBlocks₁₁ = p.A
    from factor_topLeft _ _ _]⟩
  have hq' : (q.P, q.Q) = t := ht _ ⟨q.alternatingP, q.alternatingQ, by
    rw [show M.toBlocks₁₁ = p.A from factor_topLeft _ _ _, hA]
    exact hmat⟩
  have hPQ := hp'.trans hq'.symm
  have hP := congrArg Prod.fst hPQ
  have hQ := congrArg Prod.snd hPQ
  have hu : p.u = q.u := by
    change splitScalarUnit p.u * factorUnit p.P p.Q p.A (normOneBlock_unit p.normOne) =
      splitScalarUnit q.u * factorUnit q.P q.Q q.A (normOneBlock_unit q.normOne) at hval
    apply splitScalarUnit_injective (m := m)
    rw [factorUnit_congr (h' := normOneBlock_unit q.normOne) hP hQ hA] at hval
    exact mul_right_cancel hval
  cases p
  cases q
  cases hP
  cases hQ
  cases hA
  cases hu
  rfl

private theorem chartPoint_surjective (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :
    Function.Surjective (chartPoint (m := m) (S := S)) := by
  rintro ⟨a, ha, M, hM, hdet⟩
  have hp : PreservesNorm M := by
    obtain ⟨N, ⟨hN, hNP⟩, _⟩ := spinMatrix m S a ha
    rwa [action_matrix_unique hM hN]
  obtain ⟨⟨P,Q⟩, ⟨hP, hQ, hfac⟩, _⟩ := (orthogonalChart m S M hdet).mp hp
  let b := factorUnit P Q M.toBlocks₁₁ hdet
  have hb := factorUnit_lift P Q M.toBlocks₁₁ hP hQ hdet
  have hMb : HasActionMatrix m b M := by rw [hfac]; exact hb.2.2
  obtain ⟨u, hu⟩ := tensor_ratio hM hMb
  have hlift := (tensor_scalar_lift (m := m) u).mul hb
  have hn := hlift.2.1
  rw [← hu] at hn
  have hn' : (u : S)^2 * M.toBlocks₁₁.det = 1 :=
    scalar_tensor_injective (integralForm m) S (hyperbolicBasis ℤ m)
      (hn.symm.trans (ha.2.1.trans (map_one _).symm))
  refine ⟨⟨P, Q, M.toBlocks₁₁, u, hP, hQ, hn'⟩, Subtype.ext ?_⟩
  exact hu.symm

/-- The split chart is the indicated parameter space, naturally in the test algebra. -/
theorem cliffordChart : CliffordChartType := by
  intro m _
  refine ⟨fun S _ _ => Equiv.ofBijective chartPoint
    ⟨chartPoint_injective m S, chartPoint_surjective m S⟩,
    fun S _ _ p => chartPoint_action p, ?_, ?_⟩
  · intro S T _ _ _ _ f p q hP hQ hA hu
    change splitScalarUnit q.u * factorUnit q.P q.Q q.A (normOneBlock_unit q.normOne) = _
    have hdet : IsUnit (p.A.map f).det := hA ▸ normOneBlock_unit q.normOne
    rw [factorUnit_congr (h' := hdet) hP hQ hA, hu, factorUnit_natural]
    change _ = Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom
      (splitScalarUnit p.u * factorUnit p.P p.Q p.A (normOneBlock_unit p.normOne))
    rw [map_mul, splitScalarUnit_natural]
  · intro S _ _ ζ p q hP hQ hA hu
    change splitScalarUnit q.u * factorUnit q.P q.Q q.A (normOneBlock_unit q.normOne) =
      splitScalarUnit ζ.val * (splitScalarUnit p.u * factorUnit p.P p.Q p.A (normOneBlock_unit p.normOne))
    rw [factorUnit_congr hP hQ hA, hu, show splitScalarUnit (m := m) (ζ.val * p.u) =
      splitScalarUnit ζ.val * splitScalarUnit p.u from map_mul _ _ _, mul_assoc]

end UniversalLift

omit [Algebra ℤ S] in
private theorem signedSwitch_map {T : Type*} [CommRing T] (f : S →+* T) (J : Finset (Fin m)) :
    (signedSwitch m S J).map f = signedSwitch m T J := by
  unfold signedSwitch
  rw [map_split_blocks]
  have hA : (diagonal (fun i => if i ∈ J then (0 : S) else 1)).map f =
      diagonal (fun i => if i ∈ J then (0 : T) else 1) := by
    ext i j
    by_cases h : i = j
    · subst j
      by_cases h' : i ∈ J <;> simp [Matrix.map_apply, h']
    · simp [Matrix.map_apply, h]
  have hB : (diagonal (fun i => if i ∈ J then (-1 : S) else 0)).map f =
      diagonal (fun i => if i ∈ J then (-1 : T) else 0) := by
    ext i j
    by_cases h : i = j
    · subst j
      by_cases h' : i ∈ J <;> simp [Matrix.map_apply, h']
    · simp [Matrix.map_apply, h]
  rw [hA, hB]

/-- The orthogonal pivot selection for a spin point can always be made with
an even number of switches. This works over every field. -/
theorem spin_even_switch_cover {K : Type*} [Field K] [Algebra ℤ K]
    (a : (ScalarClifford m K)ˣ) (ha : a ∈ SpinSpecification.spinUnits (integralForm m) K)
    {M : Matrix (PairIndex m) (PairIndex m) K} (hM : HasActionMatrix m a M) :
    ∃ J : EvenSwitches m, IsUnit (signedSwitch m K J.val * M).toBlocks₁₁.det := by
  have hpres : PreservesNorm M := by
    obtain ⟨N, ⟨hN, hn⟩, _⟩ := spinMatrix m K a ha
    rwa [action_matrix_unique hM hN]
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det M).mpr (action_matrix_unit_det hM))
  obtain ⟨J, hJ⟩ := exists_switch_invertible_block M hpres hinj
  by_cases hE : Even J.card
  · exact ⟨⟨J, hE⟩, hJ⟩
  have hO : Odd J.card := Nat.not_even_iff_odd.mp hE
  exfalso
  let q := splitForm m K
  let e := integralCliffordEquiv m K
  let a' := Units.map e.toMonoidHom a
  have ha' : (a' : CliffordAlgebra q) ∈ evenOdd q 0 :=
    (cliffordEquiv_even (integralForm m) K (hyperbolicBasis ℤ m) (a : ScalarClifford m K)).mpr ha.1
  obtain ⟨w, hw, _, hwAct⟩ := intrinsic_switch_lift (S := K) J
  have hw' : (w : CliffordAlgebra q) ∈ evenOdd q 1 := hO.natCast_zmod_two ▸ hw
  let N := -(signedSwitch m K J * M)
  have hdet : IsUnit N.toBlocks₁₁.det := by
    change IsUnit (-(signedSwitch m K J * M).toBlocks₁₁).det
    rw [det_neg]
    exact (isUnit_one.neg.pow _).mul hJ
  have hN : PreservesNorm N := by
    intro v
    change hyperbolicNorm ((-(signedSwitch m K J * M)) *ᵥ v) = _
    rw [neg_mulVec]
    have h (z : PairIndex m → K) : hyperbolicNorm (-z) = hyperbolicNorm z := by
      change (-(fun i => z (Sum.inl i))) ⬝ᵥ (-(fun i => z (Sum.inr i))) = _
      rw [dotProduct_neg, neg_dotProduct, neg_neg]
      rfl
    rw [h]
    exact preserves_mul (signedSwitchProperties m K J).1 hpres v
  obtain ⟨⟨P,Q⟩, ⟨hP,hQ,hfac⟩, _⟩ := (orthogonalChart m K N hdet).mp hN
  obtain ⟨b, hb⟩ := raw_factor_lift P Q N.toBlocks₁₁ hP hQ hdet
  have hAction (v : PairIndex m → K) :
      unitConj (w * a') (ι q ((splitCoordinates m K).symm v)) =
        ι q ((splitCoordinates m K).symm (N *ᵥ v)) := by
    rw [unitConj_mul_units, intrinsic_action_matrix hM, hwAct, hO.neg_one_pow, neg_one_smul]
    change -ι q ((splitCoordinates m K).symm (signedSwitch m K J *ᵥ (M *ᵥ v))) = _
    change _ = ι q ((splitCoordinates m K).symm ((-(signedSwitch m K J * M)) *ᵥ v))
    rw [neg_mulVec, ← mulVec_mulVec, map_neg, map_neg]
  obtain ⟨u, hu, _⟩ := ratio_of_implementers (w * a') b (fun x => by
    obtain ⟨v, rfl⟩ := (splitCoordinates m K).symm.surjective x
    have hB := hb.2.2 v
    rw [← hfac] at hB
    exact (hAction v).trans hB.symm)
  have ho : (↑(w * a') : CliffordAlgebra q) ∈ evenOdd q 1 := by
    change (w : CliffordAlgebra q) * (a' : CliffordAlgebra q) ∈ evenOdd q 1
    simpa only [add_zero] using SetLike.mul_mem_graded hw' ha'
  have he : (↑(w * a') : CliffordAlgebra q) ∈ evenOdd q 0 := by
    rw [hu, Units.val_mul]
    have hs : algebraMap K (CliffordAlgebra q) (u : K) ∈ evenOdd q 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (evenOdd q 0).smul_mem _ (SetLike.one_mem_graded _)
    change (b : CliffordAlgebra q) * algebraMap K _ (u : K) ∈ evenOdd q 0
    simpa only [add_zero] using SetLike.mul_mem_graded hb.1 hs
  have hz := Submodule.disjoint_def.mp (evenOdd_isCompl q).disjoint _ he ho
  have h01 : (0 : CliffordAlgebra q) = 1 := by simpa only [hz, zero_mul] using (w * a').val_inv
  exact zero_ne_one (split_scalar_injective (m := m) (S := K) (by rw [map_zero, map_one]; exact h01))


end IntrinsicClifford

section SchemeCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

variable {S : Type*} [CommRing S] [Algebra ℤ S]

private abbrev splitSpinScheme (m : ℕ) :=
  SpinFunctor.spinScheme (integralForm m) (hyperbolicBasis ℤ m)

private abbrev SpinRing (m : ℕ) :=
  SpinFunctor.CoordinateRing (integralForm m) (hyperbolicBasis ℤ m)

private abbrev specInt := algSpec (CommRingCat.of ℤ)

private abbrev testAlgebra (S : Type) [CommRing S] [Algebra ℤ S] := CommAlgCat.of ℤ S

private abbrev SplitSpinPoint (m : ℕ) (S : CommAlgCat ℤ) :=
  SpinSpecification.SchemePoints (splitSpinScheme m) S

open private spinUnitPoints spinUnitPoints_represents schemePoints_onSpec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinFunctor

private abbrev splitSpinPointValue (m : ℕ) (S : CommAlgCat ℤ) :=
  spinUnitPoints (integralForm m) (hyperbolicBasis ℤ m) S

private abbrev splitSpinPointEquiv (m : ℕ) (S : CommAlgCat ℤ) :=
  SpinFunctor.schemePoints (integralForm m) (hyperbolicBasis ℤ m) S

private abbrev spinFromAlg (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :=
  SpinFunctor.pointEquiv (integralForm m) (hyperbolicBasis ℤ m) S

private def actionMatrix (m : ℕ) (a : SpinFunctor.Spin (integralForm m) S (hyperbolicBasis ℤ m)) :
    Matrix (PairIndex m) (PairIndex m) S :=
  vectorMatrix m (SpinFunctor.vectorAction (integralForm m) S (hyperbolicBasis ℤ m) a)

private theorem actionMatrix_spec (m : ℕ)
    (a : SpinFunctor.Spin (integralForm m) S (hyperbolicBasis ℤ m)) :
    HasActionMatrix m a.val (actionMatrix m a) :=
  ⟨_, SpinFunctor.vectorAction_characterization (integralForm m) S (hyperbolicBasis ℤ m) a, rfl⟩

private theorem actionMatrix_change {T : Type*} [CommRing T] [Algebra ℤ T] (f : S →ₐ[ℤ] T)
    (a : SpinFunctor.Spin (integralForm m) S (hyperbolicBasis ℤ m)) :
    actionMatrix m (SpinFunctor.map (integralForm m) (hyperbolicBasis ℤ m) f a) =
      (actionMatrix m a).map f :=
  action_matrix_unique (actionMatrix_spec m _) (action_matrix_after_map f (actionMatrix_spec m a))

private def standardDet (m : ℕ) : SpinRing m :=
  (actionMatrix m (spinFromAlg m (SpinRing m) (AlgHom.id ℤ _))).toBlocks₁₁.det

private theorem standardDet_eval (m : ℕ) (f : SpinRing m →ₐ[ℤ] S) :
    (actionMatrix m (spinFromAlg m S f)).toBlocks₁₁.det = f (standardDet m) := by
  have h := SpinFunctor.pointEquiv_natural (integralForm m) (hyperbolicBasis ℤ m) f
    (AlgHom.id ℤ (SpinRing m))
  change spinFromAlg m S (f.comp (AlgHom.id ℤ _)) = _ at h
  rw [AlgHom.comp_id] at h
  unfold standardDet
  rw [h, actionMatrix_change]
  exact matrix_map_det f.toRingHom _

private def standardOpen (m : ℕ) : (splitSpinScheme m).X.left.Opens :=
  PrimeSpectrum.basicOpen (standardDet m)

private theorem spec_basicOpen_iff {B : Type} [CommRing B] (b : B) :
    (∀ x : Spec (CommRingCat.of B), x ∈ PrimeSpectrum.basicOpen b) ↔ IsUnit b := by
  have h : (⨆ _ : Unit, PrimeSpectrum.basicOpen b) = ⊤ ↔ IsUnit b := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    simp [Ideal.span_singleton_eq_top]
  rw [← h, iSup_const, eq_top_iff]
  exact ⟨fun h _ _ => h _, fun h x => h (show x ∈ (⊤ : (Spec (CommRingCat.of B)).Opens) from trivial)⟩

private theorem standardOpen_point (m : ℕ) (S : CommAlgCat ℤ) (a : SplitSpinPoint m S) :
    (∀ x, a.left x ∈ standardOpen m) ↔
    ∃ M, HasActionMatrix m (splitSpinPointValue m S a) M ∧ IsUnit M.toBlocks₁₁.det := by
  let F := specInt
  obtain ⟨p, rfl⟩ := (algSpec.fullyFaithful (R := CommRingCat.of ℤ)).map_surjective a
  let f : SpinRing m →ₐ[ℤ] S := p.unop.hom
  change (∀ x : Spec (CommRingCat.of S),
    Spec.map (CommRingCat.ofHom f.toRingHom) x ∈ PrimeSpectrum.basicOpen (standardDet m)) ↔ _
  change (∀ x : Spec (CommRingCat.of S), x ∈ PrimeSpectrum.basicOpen (f (standardDet m))) ↔ _
  rw [spec_basicOpen_iff, ← standardDet_eval m f]
  have hc : HasActionMatrix m (splitSpinPointValue m S (F.map p))
      (actionMatrix m (spinFromAlg m S f)) := by
    change HasActionMatrix m (splitSpinPointEquiv m S (F.map p)).val _
    rw [schemePoints_onSpec]
    exact actionMatrix_spec m _
  constructor
  · exact fun h => ⟨_, hc, h⟩
  · rintro ⟨M, hM, hunit⟩
    rwa [action_matrix_unique hc hM]

private def terminalOverInt (X : Over (Spec (CommRingCat.of ℤ))) :
    X ⟶ specInt.obj (op (testAlgebra ℤ)) :=
  Over.homMk X.hom (specZIsTerminal.hom_ext _ _)

private theorem comp_terminalOverInt {X Y : Over (Spec (CommRingCat.of ℤ))} (f : X ⟶ Y) :
    f ≫ terminalOverInt Y = terminalOverInt X := by
  apply Over.OverMorphism.ext
  exact specZIsTerminal.hom_ext _ _

private def translateSpin (m : ℕ) (s : SplitSpinPoint m (testAlgebra ℤ)) :
    (splitSpinScheme m).X ≅ (splitSpinScheme m).X where
  hom := (terminalOverInt _ ≫ s) * 𝟙 _
  inv := (terminalOverInt _ ≫ s⁻¹) * 𝟙 _
  hom_inv_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_terminalOverInt,
      GrpObj.comp_inv, inv_mul_cancel_left]
  inv_hom_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_terminalOverInt,
      GrpObj.comp_inv, mul_inv_cancel_left]

private theorem translateSpin_comp (m : ℕ) (s : SplitSpinPoint m (testAlgebra ℤ))
    (S : CommAlgCat ℤ) (a : SplitSpinPoint m S) :
    a ≫ (translateSpin m s).hom =
      (specInt.map (CommAlgCat.ofHom (Algebra.ofId ℤ S)).op ≫ s) * a := by
  change a ≫ ((terminalOverInt _ ≫ s) * 𝟙 _) = _
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_terminalOverInt]
  have h : terminalOverInt (specInt.obj (op S)) =
      specInt.map (CommAlgCat.ofHom (Algebra.ofId ℤ S)).op := by
    apply Over.OverMorphism.ext
    exact specZIsTerminal.hom_ext _ _
  rw [h]

private def integralSwitch (m : ℕ) (J : EvenSwitches m) : SplitSpinPoint m (testAlgebra ℤ) :=
  (splitSpinPointEquiv m _).symm
    ⟨(even_switch_spin_lift (S := ℤ) J).choose, (even_switch_spin_lift (S := ℤ) J).choose_spec.1⟩

private theorem integralSwitch_action (m : ℕ) (J : EvenSwitches m) :
    HasActionMatrix m (splitSpinPointValue m _ (integralSwitch m J)) (signedSwitch m ℤ J.val) := by
  change HasActionMatrix m (splitSpinPointEquiv m _ ((splitSpinPointEquiv m _).symm _)).val _
  rw [MulEquiv.apply_symm_apply]
  exact (even_switch_spin_lift (S := ℤ) J).choose_spec.2

private theorem integralSwitch_action_after_map (m : ℕ) (J : EvenSwitches m) (S : CommAlgCat ℤ) :
    HasActionMatrix m
      (splitSpinPointValue m S
        (specInt.map (CommAlgCat.ofHom (Algebra.ofId ℤ S)).op ≫ integralSwitch m J))
      (signedSwitch m S J.val) := by
  rw [(spinUnitPoints_represents (integralForm m) (hyperbolicBasis ℤ m)).2]
  have h := action_matrix_after_map (Algebra.ofId ℤ S) (integralSwitch_action m J)
  have hh : (signedSwitch m ℤ J.val).map (Algebra.ofId ℤ S) = signedSwitch m S J.val :=
    signedSwitch_map (Algebra.ofId ℤ S).toRingHom _
  rwa [hh] at h

private def switchOpen (m : ℕ) (J : EvenSwitches m) : (splitSpinScheme m).X.left.Opens :=
  (translateSpin m (integralSwitch m J)).hom.left ⁻¹ᵁ standardOpen m

private theorem switchOpen_point (m : ℕ) (J : EvenSwitches m) (S : CommAlgCat ℤ)
    (a : SplitSpinPoint m S) :
    let sS := specInt.map (CommAlgCat.ofHom (Algebra.ofId ℤ S)).op ≫ integralSwitch m J
    (∀ x, a.left x ∈ switchOpen m J) ↔
      ∃ M, HasActionMatrix m (splitSpinPointValue m S (sS * a)) M ∧ IsUnit M.toBlocks₁₁.det := by
  change (∀ x, (a ≫ (translateSpin m (integralSwitch m J)).hom).left x ∈ standardOpen m) ↔ _
  rw [translateSpin_comp]
  exact standardOpen_point m S _

private theorem switchOpen_cover (m : ℕ) : (⨆ J, switchOpen m J) = ⊤ := by
  apply top_unique
  intro x _
  let G := splitSpinScheme m
  let S := testAlgebra (G.X.left.residueField x)
  let a : SplitSpinPoint m S :=
    Over.homMk (G.X.left.fromSpecResidueField x) (specZIsTerminal.hom_ext _ _)
  let w := splitSpinPointEquiv m S a
  let M := actionMatrix m w
  have hM : HasActionMatrix m (splitSpinPointValue m S a) M := actionMatrix_spec m w
  obtain ⟨J, hdet⟩ := spin_even_switch_cover w.val w.property hM
  have h := (switchOpen_point m J S a).mpr
    ⟨_, by rw [map_mul]; exact action_matrix_mul (integralSwitch_action_after_map m J S) hM, hdet⟩
  let t : Spec (G.X.left.residueField x) := IsLocalRing.closedPoint _
  have hz : G.X.left.fromSpecResidueField x t ∈ switchOpen m J := h t
  exact (le_iSup (switchOpen m) J)
    (Scheme.fromSpecResidueField_apply x t ▸ hz)

private abbrev StandardRing (m : ℕ) := Localization.Away (standardDet m)

private def localizationPoints {B T : Type*} [CommRing B] [CommRing T] [Algebra ℤ B]
    [Algebra ℤ T] (d : B) :
    (Localization.Away d →ₐ[ℤ] T) ≃ {g : B →ₐ[ℤ] T // IsUnit (g d)} where
  toFun g := ⟨g.comp (IsScalarTower.toAlgHom ℤ B (Localization.Away d)),
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d).map g⟩
  invFun g := IsLocalization.Away.liftAlgHom d g.property
  left_inv g := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    apply RingHom.ext
    intro x
    let g₀ := g.comp (IsScalarTower.toAlgHom ℤ B (Localization.Away d))
    have h₀ : IsUnit (g₀ d) := (IsLocalization.Away.algebraMap_isUnit d).map g
    exact IsLocalization.Away.lift_eq d (g := g₀.toRingHom) h₀ x
  right_inv g := by
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact IsLocalization.Away.lift_eq d (g := g.val.toRingHom) g.property x

private def standardPointFromAlg (m : ℕ) (f : SpinRing m →ₐ[ℤ] S)
    (hf : IsUnit (f (standardDet m))) : SpinChart m S :=
  let a := spinFromAlg m S f
  ⟨a.val, a.property, _, actionMatrix_spec m a, (standardDet_eval m f).symm ▸ hf⟩

private def standardPointEquiv (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :
    (StandardRing m →ₐ[ℤ] S) ≃ SpinChart m S :=
  (localizationPoints (standardDet m)).trans
    { toFun := fun f => standardPointFromAlg m f.val f.property
      invFun := fun a =>
        let w : SpinFunctor.Spin (integralForm m) S (hyperbolicBasis ℤ m) :=
          ⟨a.val, a.property.1⟩
        let f := (spinFromAlg m S).symm w
        have h : IsUnit (actionMatrix m w).toBlocks₁₁.det := by
          obtain ⟨M, hM, hdet⟩ := a.property.2
          rwa [action_matrix_unique (actionMatrix_spec m w) hM]
        ⟨f, by
          rw [← standardDet_eval m f, Equiv.apply_symm_apply]
          exact h⟩
      left_inv := fun f => Subtype.ext ((spinFromAlg m S).symm_apply_apply f.val)
      right_inv := fun a => by
        apply Subtype.ext
        let w : SpinFunctor.Spin (integralForm m) S (hyperbolicBasis ℤ m) := ⟨a.val, a.property.1⟩
        exact congrArg (fun w : SpinFunctor.Spin (integralForm m) S (hyperbolicBasis ℤ m) => w.val)
          ((spinFromAlg m S).apply_symm_apply w) }

private def standardParameters (m : ℕ) (S : Type*) [CommRing S] [Algebra ℤ S] :
    (StandardRing m →ₐ[ℤ] S) ≃ ChartParameters m S :=
  (standardPointEquiv m S).trans
    (Equiv.ofBijective chartPoint ⟨chartPoint_injective m S, chartPoint_surjective m S⟩).symm

private theorem standardParameters_spec (m : ℕ) (f : StandardRing m →ₐ[ℤ] S) :
    chartPoint (standardParameters m S f) = standardPointEquiv m S f :=
  (Equiv.ofBijective chartPoint
    ⟨chartPoint_injective m S, chartPoint_surjective m S⟩).apply_symm_apply _

omit [Algebra ℤ S] in
private theorem chartParameters_ext {p q : ChartParameters m S}
    (hP : p.P = q.P) (hQ : p.Q = q.Q) (hA : p.A = q.A) (hu : p.u = q.u) : p = q := by
  cases p
  cases q
  cases hP
  cases hQ
  cases hA
  cases hu
  rfl

omit [Algebra ℤ S] in
private theorem map_alternating {T : Type*} [CommRing T] (f : S →+* T) (P : Block m S)
    (hP : IsAlternating P) : IsAlternating (P.map f) := by
  obtain ⟨hd, hs⟩ := (alternatingEntries m S P).mp hP
  exact (alternatingEntries m T _).mpr
    ⟨fun i => by simp [Matrix.map_apply, hd],
      fun i j => by simp only [Matrix.map_apply, hs i j, map_neg]⟩

private def parametersMap {T : Type*} [CommRing T] [Algebra ℤ T] (f : S →ₐ[ℤ] T)
    (p : ChartParameters m S) : ChartParameters m T where
  P := p.P.map f
  Q := p.Q.map f
  A := p.A.map f
  u := Units.map f.toMonoidHom p.u
  alternatingP := map_alternating f.toRingHom _ p.alternatingP
  alternatingQ := map_alternating f.toRingHom _ p.alternatingQ
  normOne := by
    change f (p.u : S) ^ 2 * (p.A.map f).det = 1
    have hd : (p.A.map f).det = f p.A.det := matrix_map_det f.toRingHom p.A
    rw [hd, ← map_pow, ← map_mul, p.normOne, map_one]

private theorem chartPoint_map {T : Type*} [CommRing T] [Algebra ℤ T] (f : S →ₐ[ℤ] T)
    (p : ChartParameters m S) :
    (chartPoint (parametersMap f p)).val =
      Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom (chartPoint p).val := by
  change splitScalarUnit (Units.map f.toMonoidHom p.u) *
    factorUnit (p.P.map f) (p.Q.map f) (p.A.map f) (normOneBlock_unit (parametersMap f p).normOne) =
    Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom
      (splitScalarUnit p.u * factorUnit p.P p.Q p.A (normOneBlock_unit p.normOne))
  rw [factorUnit_natural, map_mul, splitScalarUnit_natural]

private theorem standardParameters_map {T : Type*} [CommRing T] [Algebra ℤ T] (m : ℕ)
    (f : S →ₐ[ℤ] T) (g : StandardRing m →ₐ[ℤ] S) :
    standardParameters m T (f.comp g) = parametersMap f (standardParameters m S g) := by
  apply chartPoint_injective m T
  apply Subtype.ext
  rw [standardParameters_spec, chartPoint_map, standardParameters_spec]
  change (spinFromAlg m T (f.comp (g.comp
    (IsScalarTower.toAlgHom ℤ (SpinRing m) (StandardRing m))))).val =
      Units.map (SpinSpecification.coefficientMap (integralForm m) S f).toMonoidHom
        (spinFromAlg m S (g.comp (IsScalarTower.toAlgHom ℤ (SpinRing m) (StandardRing m)))).val
  exact congrArg Subtype.val (SpinFunctor.pointEquiv_natural (integralForm m)
    (hyperbolicBasis ℤ m) f (g.comp (IsScalarTower.toAlgHom ℤ (SpinRing m) (StandardRing m))))

private def universalStandardParameters (m : ℕ) : ChartParameters m (StandardRing m) :=
  standardParameters m _ (AlgHom.id ℤ _)

private theorem standardParameters_universal (m : ℕ) (f : StandardRing m →ₐ[ℤ] S) :
    standardParameters m S f = parametersMap f (universalStandardParameters m) := by
  unfold universalStandardParameters
  simpa only [AlgHom.comp_id] using standardParameters_map m f (AlgHom.id ℤ _)


open MvPolynomial

private abbrev ChartIndex (m : ℕ) := FactorIndex m ⊕ Unit

private abbrev unitVariable (m : ℕ) : ChartIndex m := Sum.inr ()

private abbrev entryVariable (i j : Fin m) : ChartIndex m := Sum.inl (Sum.inr (i, j))

private def chartValues (p : ChartParameters m S) : ChartIndex m → S :=
  Sum.elim (factorVariables p.P p.Q p.A) (fun _ => p.u)

private def blockOfValues (x : ChartIndex m → S) : Block m S :=
  Matrix.of fun i j => x (entryVariable i j)

private def lowerOfValues (x : ChartIndex m → S) :=
  (alternatingCoordinates m S).symm fun i => x (Sum.inl (Sum.inl (Sum.inl i)))

private def upperOfValues (x : ChartIndex m → S) :=
  (alternatingCoordinates m S).symm fun i => x (Sum.inl (Sum.inl (Sum.inr i)))

private def parametersOfValues (x : ChartIndex m → S) (u : Sˣ)
    (hu : (u : S) = x (unitVariable m)) (h : x (unitVariable m) ^ 2 * (blockOfValues x).det = 1) :
    ChartParameters m S :=
  ⟨(lowerOfValues x).val, (upperOfValues x).val, blockOfValues x, u,
    (lowerOfValues x).property, (upperOfValues x).property, hu.symm ▸ h⟩

omit [Algebra ℤ S] in
private theorem chartValues_parametersOfValues (x : ChartIndex m → S) (u : Sˣ)
    (hu : (u : S) = x (unitVariable m)) (h : x (unitVariable m) ^ 2 * (blockOfValues x).det = 1) :
    chartValues (parametersOfValues x u hu h) = x := by
  funext k
  rcases k with ((i | i) | ⟨i,j⟩) | ⟨⟩
  · exact congrFun ((alternatingCoordinates m S).apply_symm_apply
      (fun k => x (Sum.inl (Sum.inl (Sum.inl k))))) i
  · exact congrFun ((alternatingCoordinates m S).apply_symm_apply
      (fun k => x (Sum.inl (Sum.inl (Sum.inr k))))) i
  · rfl
  · exact hu

private theorem chartValues_injective :
    Function.Injective (chartValues (m := m) (S := S)) := by
  intro p q h
  apply chartParameters_ext
  · have he : alternatingCoordinates m S ⟨p.P, p.alternatingP⟩ =
        alternatingCoordinates m S ⟨q.P, q.alternatingP⟩ :=
      funext fun i => congrFun h (Sum.inl (Sum.inl (Sum.inl i)))
    exact congrArg Subtype.val ((alternatingCoordinates m S).injective he)
  · have he : alternatingCoordinates m S ⟨p.Q, p.alternatingQ⟩ =
        alternatingCoordinates m S ⟨q.Q, q.alternatingQ⟩ :=
      funext fun i => congrFun h (Sum.inl (Sum.inl (Sum.inr i)))
    exact congrArg Subtype.val ((alternatingCoordinates m S).injective he)
  · exact Matrix.ext fun i j => congrFun h (entryVariable i j)
  · exact Units.ext (congrFun h (unitVariable m))

private theorem chartValues_map {T : Type*} [CommRing T] [Algebra ℤ T]
    (f : S →ₐ[ℤ] T) (p : ChartParameters m S) :
    chartValues (parametersMap f p) = f ∘ chartValues p := by
  funext i
  rcases i with ((i | i) | i) | ⟨⟩ <;> rfl

private theorem map_cofactor {I B C : Type*} [Fintype I] [DecidableEq I]
    [CommRing B] [CommRing C] (f : B →+* C) (A : Matrix I I B) (i j : I) :
    (A.map f).adjugate j i = f (A.adjugate j i) :=
  congrArg (fun A : Matrix I I C => A j i) (f.map_adjugate A).symm

private def polynomialPoints {I : Type*} (d : MvPolynomial I ℤ) :
    (Localization.Away d →ₐ[ℤ] S) ≃ {x : I → S // IsUnit (aeval x d)} :=
  (localizationPoints d).trans
    ((Equiv.mk (fun f : MvPolynomial I ℤ →ₐ[ℤ] S => f ∘ X) aeval
      (fun f => (aeval_unique f).symm) (fun _ => funext (aeval_X _))).subtypeEquiv
      (fun f => by
        change IsUnit (f d) ↔ IsUnit (aeval (f ∘ X) d)
        rw [← aeval_unique f]))

private def algEquivFromPoints {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (e : ∀ (T : Type) [CommRing T] [Algebra ℤ T], (A →ₐ[ℤ] T) ≃ (B →ₐ[ℤ] T))
    (hnat : ∀ (T U : Type) [CommRing T] [CommRing U] [Algebra ℤ T] [Algebra ℤ U]
      (f : T →ₐ[ℤ] U) (g : A →ₐ[ℤ] T), e U (f.comp g) = f.comp (e T g)) :
    A ≃ₐ[ℤ] B := by
  let g := e A (AlgHom.id ℤ A)
  let f := (e B).symm (AlgHom.id ℤ B)
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · have h := hnat A B f (AlgHom.id ℤ A)
    rw [AlgHom.comp_id] at h
    exact h.symm.trans ((e B).apply_symm_apply _)
  · apply (e A).injective
    rw [hnat B A]
    change g.comp (e B ((e B).symm (AlgHom.id ℤ B))) = g
    rw [Equiv.apply_symm_apply, AlgHom.comp_id]


section CofactorCharts

private abbrev PivotIndex (i j : Fin m) := {k : ChartIndex m // k ≠ entryVariable i j}

private def pivotUnitVariable (i j : Fin m) : PivotIndex i j := ⟨unitVariable m, by simp⟩

private def completeValues {i j : Fin m} (x : PivotIndex i j → S) (a : S) (k : ChartIndex m) : S :=
  if h : k = entryVariable i j then a else x ⟨k,h⟩

omit [Algebra ℤ S] in
private theorem completeValues_updateRow {i j : Fin m} (x : PivotIndex i j → S) (a : S) :
    blockOfValues (completeValues x a) =
      (blockOfValues (completeValues x 0)).updateRow i
        ((blockOfValues (completeValues x 0)) i + a • Pi.single j 1) := by
  ext k l
  by_cases hk : k = i
  · subst k
    by_cases hl : l = j
    · subst l
      simp [blockOfValues, completeValues, Matrix.updateRow_apply]
    · simp [blockOfValues, completeValues, Matrix.updateRow_apply, hl]
  · simp [blockOfValues, completeValues, Matrix.updateRow_apply, hk]

private def pivotCofactor {i j : Fin m} (x : PivotIndex i j → S) : S :=
  (blockOfValues (completeValues x 0)).adjugate j i

private theorem completeValues_cofactor {i j : Fin m} (x : PivotIndex i j → S) (a : S) :
    (blockOfValues (completeValues x a)).adjugate j i = pivotCofactor x := by
  rw [completeValues_updateRow, pivotCofactor, Matrix.adjugate_apply, Matrix.adjugate_apply]
  congr 1
  ext k l
  by_cases hk : k = i <;> simp [Matrix.updateRow_apply, hk]

private theorem completeValues_det {i j : Fin m} (x : PivotIndex i j → S) (a : S) :
    (blockOfValues (completeValues x a)).det =
      (blockOfValues (completeValues x 0)).det + a * pivotCofactor x := by
  rw [completeValues_updateRow, det_updateRow_add, det_updateRow_smul, updateRow_eq_self,
    pivotCofactor, Matrix.adjugate_apply]

private def restrictedValues {i j : Fin m} (p : ChartParameters m S) (k : PivotIndex i j) : S :=
  chartValues p k.val

omit [Algebra ℤ S] in
private theorem complete_restricted {i j : Fin m} (p : ChartParameters m S) :
    completeValues (restrictedValues (i := i) (j := j) p) (p.A i j) = chartValues p := by
  funext k
  by_cases hk : k = entryVariable i j
  · subst k
    simp [completeValues, chartValues, factorVariables]
  · simp [completeValues, restrictedValues, hk]

-- On this cofactor open the determinant equation uniquely recovers the omitted entry.
private def pivotParameters (i j : Fin m) :
    {p : ChartParameters m S // IsUnit (p.A.adjugate j i)} ≃
      {x : PivotIndex i j → S // IsUnit (x (pivotUnitVariable i j) * pivotCofactor x)} := by
  let f (p : {p : ChartParameters m S // IsUnit (p.A.adjugate j i)}) :
      {x : PivotIndex i j → S // IsUnit (x (pivotUnitVariable i j) * pivotCofactor x)} := by
    refine ⟨restrictedValues p.val, p.val.u.isUnit.mul ?_⟩
    have h := completeValues_cofactor (restrictedValues (i := i) (j := j) p.val) (p.val.A i j)
    rw [complete_restricted] at h
    exact h ▸ p.property
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q h
    have hx := congrArg Subtype.val h
    have hq : restrictedValues (i := i) (j := j) p.val = restrictedValues q.val := hx
    have hu : (p.val.u : S) = q.val.u := congrFun hq (pivotUnitVariable i j)
    have hd : p.val.A.det = q.val.A.det := by
      apply (p.val.u.isUnit.pow 2).mul_left_cancel
      rw [p.val.normOne, hu, q.val.normOne]
    have hP := completeValues_det (restrictedValues (i := i) (j := j) p.val) (p.val.A i j)
    have hQ := completeValues_det (restrictedValues (i := i) (j := j) q.val) (q.val.A i j)
    rw [complete_restricted] at hP hQ
    change p.val.A.det = _ at hP
    change q.val.A.det = _ at hQ
    rw [hP, hQ, hq] at hd
    have hc : IsUnit (pivotCofactor (restrictedValues (i := i) (j := j) q.val)) := by
      have hh := completeValues_cofactor (restrictedValues (i := i) (j := j) q.val) (q.val.A i j)
      rw [complete_restricted] at hh
      exact hh ▸ q.property
    have ha := hc.mul_right_cancel (add_left_cancel hd)
    apply Subtype.ext
    apply chartValues_injective
    rw [← complete_restricted (i := i) (j := j) p.val, ← complete_restricted (i := i) (j := j) q.val, hq, ha]
  · rintro ⟨x, hx⟩
    have hu := isUnit_of_mul_isUnit_left hx
    have hc := isUnit_of_mul_isUnit_right hx
    let u := hu.unit
    let c := hc.unit
    let a := ((↑u⁻¹ : S)^2 - (blockOfValues (completeValues x 0)).det) * (↑c⁻¹ : S)
    have hco : pivotCofactor x = (c : S) := hc.unit_spec.symm
    have hd : (blockOfValues (completeValues x a)).det = (↑u⁻¹ : S)^2 := by
      rw [completeValues_det, hco]
      change _ + ((_ - _) * (↑c⁻¹ : S)) * (c : S) = _
      rw [mul_assoc, Units.inv_mul, mul_one]
      ring
    have huv : (u : S) = completeValues x a (unitVariable m) := by
      have h : completeValues x a (unitVariable m) = x (pivotUnitVariable i j) := by
        simp [completeValues, pivotUnitVariable]
      exact hu.unit_spec.trans h.symm
    have hn : completeValues x a (unitVariable m)^2 * (blockOfValues (completeValues x a)).det = 1 := by
      rw [← huv, hd, ← mul_pow, Units.mul_inv, one_pow]
    let p := parametersOfValues (completeValues x a) u huv hn
    have hp : IsUnit (p.A.adjugate j i) := by
      change IsUnit ((blockOfValues (completeValues x a)).adjugate j i)
      rwa [completeValues_cofactor]
    refine ⟨⟨p,hp⟩, Subtype.ext ?_⟩
    funext k
    change chartValues p k.val = x k
    rw [chartValues_parametersOfValues]
    simp [completeValues, k.property]

private def standardCofactor (i j : Fin m) : StandardRing m :=
  (universalStandardParameters m).A.adjugate j i

private def standardCofactorParameters (i j : Fin m) (S : Type*) [CommRing S] [Algebra ℤ S] :
    (Localization.Away (standardCofactor i j) →ₐ[ℤ] S) ≃
      {p : ChartParameters m S // IsUnit (p.A.adjugate j i)} :=
  (localizationPoints (standardCofactor i j)).trans
    ((standardParameters m S).subtypeEquiv fun g => by
      rw [standardParameters_universal]
      change IsUnit (g (standardCofactor i j)) ↔
        IsUnit (((universalStandardParameters m).A.map g).adjugate j i)
      exact Iff.rfl.trans (congrArg IsUnit
        (map_cofactor g.toRingHom (universalStandardParameters m).A i j).symm).to_iff)

private def pivotDenominator (i j : Fin m) : MvPolynomial (PivotIndex i j) ℤ :=
  X (pivotUnitVariable i j) * pivotCofactor (fun k : PivotIndex i j => X k)

private theorem eval_pivotDenominator (i j : Fin m) (x : PivotIndex i j → S) :
    aeval x (pivotDenominator i j) = x (pivotUnitVariable i j) * pivotCofactor x := by
  let f := aeval (R := ℤ) x
  let y : PivotIndex i j → MvPolynomial (PivotIndex i j) ℤ := X
  have h (k : ChartIndex m) : f (completeValues y 0 k) = completeValues x 0 k := by
    by_cases hk : k = entryVariable i j
    · simp [completeValues, hk]
    · simp [completeValues, hk, f, y]
  have he : ((blockOfValues (completeValues y 0)).map f) = blockOfValues (completeValues x 0) :=
    Matrix.ext fun i j => h _
  have hc := map_cofactor f.toRingHom (blockOfValues (completeValues y 0)) i j
  change (((blockOfValues (completeValues y 0)).map f).adjugate j i) = f (pivotCofactor y) at hc
  rw [he] at hc
  rw [pivotDenominator, map_mul, aeval_X]
  exact congrArg (fun z => x (pivotUnitVariable i j) * z) hc.symm

private abbrev pivotRing (i j : Fin m) := Localization.Away (pivotDenominator i j)

private def pivotRingPoints (i j : Fin m) (S : Type*) [CommRing S] [Algebra ℤ S] :
    (pivotRing i j →ₐ[ℤ] S) ≃
      {x : PivotIndex i j → S // IsUnit (x (pivotUnitVariable i j) * pivotCofactor x)} :=
  (polynomialPoints (pivotDenominator i j)).trans
    (Equiv.subtypeEquivRight fun x => by rw [eval_pivotDenominator])

private theorem localParameterValues (i j : Fin m) (g : Localization.Away (standardCofactor i j) →ₐ[ℤ] S)
    (k : PivotIndex i j) :
    (pivotParameters i j (standardCofactorParameters i j S g)).val k =
     g (algebraMap (StandardRing m) (Localization.Away (standardCofactor i j))
       (chartValues (universalStandardParameters m) k.val)) := by
  let h := g.comp (IsScalarTower.toAlgHom ℤ (StandardRing m) (Localization.Away (standardCofactor i j)))
  change chartValues (standardParameters m S h) k.val = _
  rw [standardParameters_universal, chartValues_map]
  rfl

private def cofactorRingEquiv (i j : Fin m) : Localization.Away (standardCofactor i j) ≃ₐ[ℤ] pivotRing i j :=
  algEquivFromPoints
    (fun S _ _ => (standardCofactorParameters i j S).trans
      ((pivotParameters i j).trans (pivotRingPoints i j S).symm))
    (by
      intro S T _ _ _ _ f g
      apply (pivotRingPoints i j T).injective
      apply Subtype.ext
      funext k
      have h (S : Type) [CommRing S] [Algebra ℤ S] (g : _ →ₐ[ℤ] S) :
          (pivotRingPoints i j S).symm
              (pivotParameters i j (standardCofactorParameters i j S g))
              (algebraMap (MvPolynomial (PivotIndex i j) ℤ) (pivotRing i j) (X k)) =
            (pivotParameters i j (standardCofactorParameters i j S g)).val k := by
        have h := (pivotRingPoints i j S).apply_symm_apply
          (pivotParameters i j (standardCofactorParameters i j S g))
        exact congrArg (fun x : {x : PivotIndex i j → S // _} => x.val k) h
      change (pivotRingPoints i j T
        ((pivotRingPoints i j T).symm
          (pivotParameters i j (standardCofactorParameters i j T (f.comp g))))).val k =
          f ((pivotRingPoints i j S).symm
            (pivotParameters i j (standardCofactorParameters i j S g))
            (algebraMap (MvPolynomial (PivotIndex i j) ℤ) (pivotRing i j) (X k)))
      rw [Equiv.apply_symm_apply, h, localParameterValues, localParameterValues]
      rfl)

private theorem pivotIndex_card (i j : Fin m) : Nat.card (PivotIndex i j) = 2 * m ^ 2 - m := by
  classical
  letI : Unique {k : ChartIndex m // k = entryVariable i j} :=
    ⟨⟨⟨entryVariable i j, rfl⟩⟩, fun k => Subtype.ext k.property⟩
  have h := Nat.card_congr (Equiv.sumCompl (fun k : ChartIndex m => k = entryVariable i j))
  change Nat.card ({k : ChartIndex m // k = entryVariable i j} ⊕ PivotIndex i j) =
    Nat.card (ChartIndex m) at h
  have h' : Nat.card (ChartIndex m) = (2 * m ^ 2 - m) + 1 := by
    change Nat.card (((AlternatingIndex m ⊕ AlternatingIndex m) ⊕ (Fin m × Fin m)) ⊕ Unit) = _
    simp only [Nat.card_sum, Nat.card_prod, Nat.card_fin, Nat.card_unique (α := Unit),
      Nat.card_eq_fintype_card (α := AlternatingIndex m), ← two_mul, ← pow_two,
      (alternatingDimension m).2]
  rw [Nat.card_sum, Nat.card_unique, h'] at h
  omega

private theorem standardCofactor_span (m : ℕ) (hm : 0 < m) :
    Ideal.span (Set.range (fun ij : Fin m × Fin m => standardCofactor ij.1 ij.2)) = ⊤ := by
  let I := Ideal.span (Set.range (fun ij : Fin m × Fin m => standardCofactor ij.1 ij.2))
  let p := universalStandardParameters m
  let i : Fin m := ⟨0,hm⟩
  have hd : p.A.det ∈ I := by
    rw [Matrix.det_eq_sum_mul_adjugate_row _ i]
    apply I.sum_mem
    intro j _
    exact I.mul_mem_left _ (Ideal.subset_span ⟨(i,j),rfl⟩)
  have h1 : (1 : StandardRing m) ∈ I := p.normOne ▸ I.mul_mem_left ((p.u : StandardRing m)^2) hd
  exact (Ideal.eq_top_iff_one I).mpr h1

private theorem standardRing_smooth (m : ℕ) (hm : 0 < m) :
    SmoothOfRelativeDimension (2 * m ^ 2 - m)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (StandardRing m)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (2 * m ^ 2 - m))).mpr
  refine ⟨Set.range (fun ij : Fin m × Fin m => standardCofactor ij.1 ij.2),
    standardCofactor_span m hm, ?_⟩
  rintro _ ⟨⟨i,j⟩,rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension (2 * m ^ 2 - m)
    ((algebraMap (StandardRing m) (Localization.Away (standardCofactor i j))).comp
      (algebraMap ℤ (StandardRing m)))
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let B := MvPolynomial (PivotIndex i j) ℤ
  let A := pivotRing i j
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (2 * m ^ 2 - m) ℤ B :=
    pivotIndex_card i j ▸ Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial ℤ (PivotIndex i j)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 B A :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (pivotDenominator i j)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (0 + (2 * m ^ 2 - m)) ℤ A :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans _ _ ℤ B A
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (2 * m ^ 2 - m) ℤ A := by
    simpa only [zero_add] using (inferInstance :
      Algebra.IsStandardSmoothOfRelativeDimension (0 + (2 * m ^ 2 - m)) ℤ A)
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv _ (cofactorRingEquiv i j).symm

end CofactorCharts

section ConnectedCharts

private def largeDenominator (m : ℕ) : MvPolynomial (ChartIndex m) ℤ :=
  X (unitVariable m) * (blockOfValues (X : ChartIndex m → MvPolynomial (ChartIndex m) ℤ)).det

private abbrev LargeRing (m : ℕ) := Localization.Away (largeDenominator m)

private abbrev IntTensor (A B : Type) [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] :=
  letI : Module ℤ A := Algebra.toModule
  letI : Module ℤ B := Algebra.toModule
  A ⊗[ℤ] B

private theorem eval_largeDenominator (x : ChartIndex m → S) :
    aeval x (largeDenominator m) = x (unitVariable m) * (blockOfValues x).det := by
  let f := aeval (R := ℤ) x
  have h : (blockOfValues (X : ChartIndex m → MvPolynomial (ChartIndex m) ℤ)).map f =
      blockOfValues x := Matrix.ext fun _ _ => aeval_X x _
  have hd := (matrix_map_det f.toRingHom _).symm.trans (congrArg Matrix.det h)
  rw [largeDenominator, map_mul, aeval_X]
  exact congrArg (fun t => x (unitVariable m) * t) hd

omit [Algebra ℤ S] in
private theorem scaleRow_map {T : Type*} [CommRing T] (f : S →+* T)
    (i : Fin m) (s : S) (A : Block m S) :
    (scaleRow i s A).map f = scaleRow i (f s) (A.map f) := by
  ext j k
  by_cases h : j = i
  · subst j
    simp [scaleRow, Matrix.map_apply, smul_eq_mul]
  · simp [scaleRow, Matrix.map_apply, h]

/-- The chart is a retract of the principal open parametrizing arbitrary
alternating coordinates, an invertible middle matrix and an invertible scalar. -/
private theorem standardRing_retract (i : Fin m) :
    ∃ (f : StandardRing m →ₐ[ℤ] LargeRing m) (g : LargeRing m →ₐ[ℤ] StandardRing m),
      g.comp f = AlgHom.id ℤ _ := by
  let p := universalStandardParameters m
  let E := polynomialPoints (largeDenominator m) (S := StandardRing m)
  have hp : IsUnit (aeval (chartValues p) (largeDenominator m)) := by
    rw [eval_largeDenominator]
    exact p.u.isUnit.mul (normOneBlock_unit p.normOne)
  let g := E.symm ⟨chartValues p, hp⟩
  let Z := polynomialPoints (largeDenominator m) (S := LargeRing m)
    (AlgHom.id ℤ (LargeRing m))
  let z := Z.val
  have hz (k : ChartIndex m) : g (z k) = chartValues p k := by
    have h := E.apply_symm_apply ⟨chartValues p, hp⟩
    exact congrArg (fun x : {x : ChartIndex m → StandardRing m // _} => x.val k) h
  have hunit : IsUnit (z (unitVariable m) * (blockOfValues z).det) := by
    rw [← eval_largeDenominator]
    exact Z.property
  have hu := isUnit_of_mul_isUnit_left hunit
  have hd := isUnit_of_mul_isUnit_right hunit
  let u := hu.unit
  let A := blockOfValues z
  have ht₀ : IsUnit (z (unitVariable m)^2 * A.det) := (hu.pow 2).mul hd
  let t : LargeRing m := ↑ht₀.unit⁻¹
  have ht : t * (z (unitVariable m)^2 * A.det) = 1 := by
    rw [← ht₀.unit_spec]
    exact Units.inv_mul ht₀.unit
  let q : ChartParameters m (LargeRing m) :=
    ⟨(lowerOfValues z).val, (upperOfValues z).val, scaleRow i t A, u,
      (lowerOfValues z).property, (upperOfValues z).property, by
        change (u : LargeRing m)^2 * (scaleRow i t A).det = 1
        rw [hu.unit_spec, scaleRow_det]
        calc
          _ = t * (z (unitVariable m)^2 * A.det) := by ring
          _ = 1 := ht⟩
  let f := (standardParameters m (LargeRing m)).symm q
  refine ⟨f, g, ?_⟩
  apply (standardParameters m (StandardRing m)).injective
  rw [standardParameters_map]
  change parametersMap g (standardParameters m (LargeRing m)
    ((standardParameters m (LargeRing m)).symm q)) = p
  rw [Equiv.apply_symm_apply]
  have hA : A.map g = p.A := Matrix.ext fun i j => hz (entryVariable i j)
  have hAz : g A.det = p.A.det :=
    (matrix_map_det g.toRingHom _).symm.trans (congrArg Matrix.det hA)
  have hU : g (z (unitVariable m)) = (p.u : StandardRing m) := hz (unitVariable m)
  have hT : g t = 1 := by
    have h := congrArg g ht
    rw [map_mul, map_mul, map_pow, hU, hAz, p.normOne, mul_one, map_one] at h
    exact h
  apply chartParameters_ext
  · change ((lowerOfValues z).val.map g.toRingHom) = p.P
    rw [lowerOfValues, alternating_ofCoordinates_map]
    have he : g.toRingHom ∘ (fun i => z (Sum.inl (Sum.inl (Sum.inl i)))) =
        alternatingCoordinates m (StandardRing m) ⟨p.P, p.alternatingP⟩ :=
      funext fun j => hz (Sum.inl (Sum.inl (Sum.inl j)))
    rw [he, Equiv.symm_apply_apply]
  · change ((upperOfValues z).val.map g.toRingHom) = p.Q
    rw [upperOfValues, alternating_ofCoordinates_map]
    have he : g.toRingHom ∘ (fun i => z (Sum.inl (Sum.inl (Sum.inr i)))) =
        alternatingCoordinates m (StandardRing m) ⟨p.Q, p.alternatingQ⟩ :=
      funext fun j => hz (Sum.inl (Sum.inl (Sum.inr j)))
    rw [he, Equiv.symm_apply_apply]
  · change (scaleRow i t A).map g.toRingHom = p.A
    have hAm : A.map g.toRingHom = p.A := hA
    have hTr : g.toRingHom t = 1 := hT
    rw [scaleRow_map, hTr, hAm]
    simp [scaleRow]
  · apply Units.ext
    change g (u : LargeRing m) = p.u.val
    rw [hu.unit_spec]
    exact hU

private theorem largeRing_baseChange_isDomain (m : ℕ) (K : Type) [Field K] :
    IsDomain (IntTensor K (LargeRing m)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := ChartIndex m) ℤ K
  letI : IsDomain (K ⊗[ℤ] MvPolynomial (ChartIndex m) ℤ) :=
    Function.Injective.isDomain e e.injective
  let t := IsLocalization.Away.tensorProductEquivTMulRight ℤ K (largeDenominator m) (LargeRing m)
  have hne : (1 : K) ⊗ₜ[ℤ] largeDenominator m ≠ 0 := by
    intro h
    let x : ChartIndex m → K :=
      Sum.elim (factorVariables (0 : Block m K) 0 1) (fun _ => 1)
    have hx : blockOfValues x = 1 := rfl
    have he := congrArg (fun z => aeval x (e z)) h
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, map_zero, map_zero] at he
    rw [MvPolynomial.aeval_map_algebraMap (R := ℤ) K, eval_largeDenominator, hx, det_one] at he
    simp [x] at he
  letI : IsDomain (Localization.Away ((1 : K) ⊗ₜ[ℤ] largeDenominator m)) :=
    IsLocalization.Away.isDomain _ hne
  exact Function.Injective.isDomain t t.injective

private theorem standardRing_baseChange_isDomain (m : ℕ) (hm : 0 < m) (K : Type)
    [Field K] : IsDomain (IntTensor K (StandardRing m)) := by
  obtain ⟨f, g, hg⟩ := standardRing_retract (⟨0,hm⟩ : Fin m)
  letI := largeRing_baseChange_isDomain m K
  let fK := Algebra.TensorProduct.map (AlgHom.id K K) f
  let gK := Algebra.TensorProduct.map (AlgHom.id K K) g
  have he : gK.comp fK = AlgHom.id K _ := by
    change (Algebra.TensorProduct.map (AlgHom.id K K) g).comp
      (Algebra.TensorProduct.map (AlgHom.id K K) f) = _
    rw [← Algebra.TensorProduct.map_id_comp, hg, Algebra.TensorProduct.map_id]
  exact Function.Injective.isDomain fK
    (Function.LeftInverse.injective (g := gK) fun x => DFunLike.congr_fun he x)

private theorem standardRing_connected (m : ℕ) (hm : 0 < m) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap ℤ (StandardRing m)))) := by
  constructor
  apply (geometrically_iff_of_isClosedUnderIsomorphisms (P := fun X : Scheme => ConnectedSpace X)).mpr
  intro K _ y
  letI := standardRing_baseChange_isDomain m hm K
  rw [show y = Spec.map (CommRingCat.ofHom (algebraMap ℤ K)) from specZIsTerminal.hom_ext _ _]
  let e := pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap ℤ (StandardRing m))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) ≪≫ pullbackSpecIso ℤ K (StandardRing m)
  exact e.hom.homeomorph.connectedSpace_iff.mpr (inferInstance : ConnectedSpace
    (Spec (CommRingCat.of (IntTensor K (StandardRing m)))))

end ConnectedCharts

private def standardOpenIso (m : ℕ) : (standardOpen m).toScheme ≅ Spec (CommRingCat.of (StandardRing m)) :=
  basicOpenIsoSpecAway (R := CommRingCat.of (SpinRing m)) (standardDet m)

private theorem property_of_iso_over_int (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Scheme.{0}} (e : X ≅ Y)
    {f : X ⟶ Spec (CommRingCat.of ℤ)} {g : Y ⟶ Spec (CommRingCat.of ℤ)} (hg : P g) : P f := by
  letI : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h : f = e.hom ≫ g := specZIsTerminal.hom_ext _ _
  rw [h, MorphismProperty.cancel_left_of_respectsIso P]
  exact hg

private theorem standardOpen_smooth (m : ℕ) (hm : 0 < m) :
    SmoothOfRelativeDimension (2 * m ^ 2 - m) ((standardOpen m).ι ≫ (splitSpinScheme m).X.hom) :=
  property_of_iso_over_int (@SmoothOfRelativeDimension (2 * m ^ 2 - m)) (standardOpenIso m)
    (standardRing_smooth m hm)

private theorem standardOpen_connected (m : ℕ) (hm : 0 < m) :
    GeometricallyConnected ((standardOpen m).ι ≫ (splitSpinScheme m).X.hom) :=
  property_of_iso_over_int @GeometricallyConnected (standardOpenIso m) (standardRing_connected m hm)

private def switchOpenIso (m : ℕ) (J : EvenSwitches m) :
    (switchOpen m J).toScheme ≅ (standardOpen m).toScheme := by
  let e := translateSpin m (integralSwitch m J)
  let f := (Over.forget _).mapIso e
  change ((f.hom ⁻¹ᵁ standardOpen m).toScheme) ≅ (standardOpen m).toScheme
  exact asIso (f.hom ∣_ standardOpen m)

private theorem switchOpen_smooth (m : ℕ) (hm : 0 < m) (J : EvenSwitches m) :
    SmoothOfRelativeDimension (2 * m ^ 2 - m) ((switchOpen m J).ι ≫ (splitSpinScheme m).X.hom) :=
  property_of_iso_over_int (@SmoothOfRelativeDimension (2 * m ^ 2 - m)) (switchOpenIso m J)
    (standardOpen_smooth m hm)

private theorem switchOpen_connected (m : ℕ) (hm : 0 < m) (J : EvenSwitches m) :
    GeometricallyConnected ((switchOpen m J).ι ≫ (splitSpinScheme m).X.hom) :=
  property_of_iso_over_int @GeometricallyConnected (switchOpenIso m J) (standardOpen_connected m hm)

private theorem fiberOpen_connected {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens)
    (h : GeometricallyConnected (U.ι ≫ f)) (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ Y) :
    _root_.IsConnected ((pullback.fst f y) ⁻¹ᵁ U).1 := by
  let pr := pullback.fst f y
  let V := pr ⁻¹ᵁ U
  have hp : IsPullback (pr ∣_ U) (V.ι ≫ pullback.snd f y) (U.ι ≫ f) y :=
    (isPullback_morphismRestrict pr U).paste_vert (IsPullback.of_hasPullback f y)
  exact isConnected_iff_connectedSpace.mpr (h.geometrically_connectedSpace _ _ _ hp)

private theorem switchOpen_fiber_overlap (m : ℕ) (J : EvenSwitches m)
    (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℤ)) :
    let pr := pullback.fst (splitSpinScheme m).X.hom y
    ((pr ⁻¹ᵁ standardOpen m).1 ∩ (pr ⁻¹ᵁ switchOpen m J).1).Nonempty := by
  intro pr
  obtain ⟨P, hP, hdet⟩ := evenSwitchOverlap m K J
  let p : ChartParameters m K := ⟨P, 0, 1, 1, hP, by intro x; simp, by simp⟩
  let a := (splitSpinPointEquiv m (testAlgebra K)).symm
    ⟨(chartPoint p).val, (chartPoint p).property.1⟩
  have hm : HasActionMatrix m (splitSpinPointValue m (testAlgebra K) a) (lower P) := by
    change HasActionMatrix m ((splitSpinPointEquiv m _) ((splitSpinPointEquiv m _).symm _)).val _
    rw [MulEquiv.apply_symm_apply]
    have hh := chartPoint_action p
    change HasActionMatrix m (chartPoint p).val (lower P * middle 1 * upper 0) at hh
    simpa [middle, upper] using hh
  let v : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let t := pullback.lift (f := (splitSpinScheme m).X.hom) (g := y)
    a.left (𝟙 (Spec (CommRingCat.of K))) (specZIsTerminal.hom_ext _ _)
  have ht : pr (t v) = a.left v := by
    have h : t ≫ pullback.fst (splitSpinScheme m).X.hom y = a.left :=
      pullback.lift_fst _ _ _
    exact congrArg (fun f : (specInt.obj (op (testAlgebra K))).left ⟶ (splitSpinScheme m).X.left => f v) h
  refine ⟨t v, ?_, ?_⟩
  · change pr (t v) ∈ standardOpen m
    rw [ht]
    exact (standardOpen_point m _ a).mpr ⟨_, hm, by simp [lower]⟩ v
  · change pr (t v) ∈ switchOpen m J
    rw [ht]
    refine (switchOpen_point m J _ a).mpr ⟨_, ?_, hdet⟩ v
    rw [map_mul]
    exact action_matrix_mul (integralSwitch_action_after_map m J _) hm

private theorem splitSpin_connected (m : ℕ) (hm : 0 < m) :
    GeometricallyConnected (splitSpinScheme m).X.hom := by
  constructor
  apply (geometrically_iff_of_isClosedUnderIsomorphisms (P := fun X : Scheme => ConnectedSpace X)).mpr
  intro K _ y
  let G := splitSpinScheme m
  let pr := pullback.fst G.X.hom y
  let C := (pr ⁻¹ᵁ standardOpen m).1
  let U (J : EvenSwitches m) := (pr ⁻¹ᵁ switchOpen m J).1
  have hc : _root_.IsConnected C := fiberOpen_connected _ _ (standardOpen_connected m hm) K y
  have hU (J) : _root_.IsConnected (U J) := fiberOpen_connected _ _ (switchOpen_connected m hm J) K y
  have hu : (⋃ J, C ∪ U J) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have h : pr x ∈ ⨆ J, switchOpen m J := by rw [switchOpen_cover]; exact trivial
    obtain ⟨J, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    exact Set.mem_iUnion.mpr ⟨J, Or.inr hj⟩
  obtain ⟨x, hx⟩ := hc.nonempty
  have hi : (⋂ J, C ∪ U J).Nonempty := ⟨x, Set.mem_iInter.mpr fun _ => Or.inl hx⟩
  rw [connectedSpace_iff_univ, ← hu]
  refine ⟨⟨x, ?_⟩, isPreconnected_iUnion hi fun J => ?_⟩
  · let J : EvenSwitches m := ⟨∅, by simp⟩
    exact Set.mem_iUnion.mpr ⟨J, Or.inl hx⟩
  · exact (hc.union (switchOpen_fiber_overlap m J K y) (hU J)).isPreconnected

/-- The split even Clifford spin scheme over the integers has the translated
alternating-shear charts, is smooth of the stated dimension, and has connected geometric fibers. -/
theorem spinGeometry : SpinGeometryType := by
  intro m hm
  refine ⟨splitSpinScheme m, splitSpinPointValue m, integralSwitch m, switchOpen m,
    spinUnitPoints_represents (integralForm m) (hyperbolicBasis ℤ m),
    integralSwitch_action m, switchOpen_point m, switchOpen_cover m,
    switchOpen_connected m hm, ?_, splitSpin_connected m hm⟩
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} (2 * m ^ 2 - m)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (2 * m ^ 2 - m)))
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (2 * m ^ 2 - m))
    (switchOpen m) (switchOpen_cover m) (switchOpen_smooth m hm)


end SchemeCharts

end

end LinearAlgebraicGroups.Albert.SplitSpin
