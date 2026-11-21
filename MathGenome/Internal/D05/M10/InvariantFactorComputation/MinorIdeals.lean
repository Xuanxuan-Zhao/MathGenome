import MathGenome.Internal.Specs.D05.M10.InvariantFactorComputation.MinorIdeals
import MathGenome.Internal.D05.Foundations.IdealsGcd
import MathGenome.Internal.D05.M05.DetDefinition
import MathGenome.Internal.D05.M05.DetUniqueness
import Lean.Elab.Tactic.Omega

noncomputable section
open scoped BigOperators
namespace D05.M10.InvariantFactorComputation.MinorIdeals

variable {R : Type*} [CommRing R] {m n k : ℕ}

theorem chain_iff_adjacent : D05.Specs.MinorIdeals.chain_iff_adjacent := by
  intro K _ d r
  constructor
  · rintro ⟨hm, hz, hc⟩
    exact ⟨hm, hz, fun i _ => hc i (i + 1) (Nat.le_succ i)⟩
  · rintro ⟨hm, hz, hc⟩
    refine ⟨hm, hz, ?_⟩
    intro i j hij
    by_cases hj : r ≤ j
    · rw [hz j hj]
      exact dvd_zero _
    · have H : ∀ j, i ≤ j → j < r → d i ∣ d j := by
        intro j
        induction j with
        | zero =>
          intro hi _
          have : i = 0 := Nat.eq_zero_of_le_zero hi
          subst i
          exact dvd_rfl
        | succ j ih =>
          intro hi hj
          by_cases he : i = j + 1
          · rw [he]
          · exact (ih (by omega) (by omega)).trans (hc j hj)
      exact H j hij (by omega)

lemma minor_mem (M : Matrix (Fin m) (Fin n) R)
    (ρ : Fin k → Fin m) (κ : Fin k → Fin n) :
    (M.submatrix ρ κ).det ∈ minorIdeal M k :=
  Ideal.subset_span ⟨ρ, κ, rfl⟩

lemma minor_zero_of_not_injective_row (M : Matrix (Fin m) (Fin n) R)
    (ρ : Fin k → Fin m) (κ : Fin k → Fin n) (h : ¬ Function.Injective ρ) :
    (M.submatrix ρ κ).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp h
  exact Matrix.det_zero_of_row_eq hne (by ext a; simp [hij])

lemma minor_zero_of_not_injective_col (M : Matrix (Fin m) (Fin n) R)
    (ρ : Fin k → Fin m) (κ : Fin k → Fin n) (h : ¬ Function.Injective κ) :
    (M.submatrix ρ κ).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp h
  exact Matrix.det_zero_of_column_eq hne (by intro a; simp [hij])

theorem injective_generators : D05.Specs.MinorIdeals.injective_generators := by
  intro R _ m n k M
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨ρ, κ, rfl⟩
    by_cases hr : Function.Injective ρ
    · by_cases hc : Function.Injective κ
      · exact Ideal.subset_span ⟨ρ, κ, hr, hc, rfl⟩
      · rw [minor_zero_of_not_injective_col M ρ κ hc]
        exact Ideal.zero_mem _
    · rw [minor_zero_of_not_injective_row M ρ κ hr]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro x ⟨ρ, κ, _, _, rfl⟩
    exact minor_mem M ρ κ

/-- Multilinear expansion in the rows, with no distinctness restriction on f. -/
lemma det_mul_rect (A : Matrix (Fin k) (Fin m) R)
    (B : Matrix (Fin m) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin m,
      (∏ i, A i (f i)) * (B.submatrix f id).det := by
  classical
  let F : MultilinearMap R (fun _ : Fin k => Fin k → R) R :=
    Matrix.detRowAlternating.toMultilinearMap
  have hexpand := F.map_sum (fun i j => A i j • B j)
  have heq : (fun i => ∑ j : Fin m, A i j • B j) = A * B := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq] at hexpand
  change (A * B).det = _ at hexpand
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro f _
  exact F.map_smul_univ (fun i => A i (f i)) (fun i => B (f i))

/-- Left multiplication only takes linear combinations of old minors. -/
lemma minorIdeal_mul_left_le (A : Matrix (Fin m) (Fin m) R)
    (M : Matrix (Fin m) (Fin n) R) (k : ℕ) :
    minorIdeal (A * M) k ≤ minorIdeal M k := by
  classical
  apply Ideal.span_le.mpr
  rintro x ⟨ρ, κ, rfl⟩
  have heq : (A * M).submatrix ρ κ =
      (A.submatrix ρ id) * (M.submatrix id κ) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [heq, det_mul_rect]
  apply (minorIdeal M k).sum_mem
  intro f _
  apply Ideal.mul_mem_left
  exact minor_mem M f κ

lemma minorIdeal_transpose (M : Matrix (Fin m) (Fin n) R) (k : ℕ) :
    minorIdeal M.transpose k = minorIdeal M k := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨ρ, κ, rfl⟩
    have h : (M.transpose.submatrix ρ κ).det = (M.submatrix κ ρ).det :=
      Matrix.det_transpose _
    rw [h]
    exact minor_mem M κ ρ
  · apply Ideal.span_le.mpr
    rintro x ⟨ρ, κ, rfl⟩
    have h : (M.submatrix ρ κ).det = (M.transpose.submatrix κ ρ).det :=
      (Matrix.det_transpose _).symm
    rw [h]
    exact minor_mem M.transpose κ ρ

lemma minorIdeal_mul_right_le (M : Matrix (Fin m) (Fin n) R)
    (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    minorIdeal (M * A) k ≤ minorIdeal M k := by
  rw [← minorIdeal_transpose (M * A), Matrix.transpose_mul,
    ← minorIdeal_transpose M]
  exact minorIdeal_mul_left_le A.transpose M.transpose k

theorem invertible_invariance : D05.Specs.MinorIdeals.invertible_invariance := by
  intro R _ m n k M U V
  apply le_antisymm
  · exact (minorIdeal_mul_right_le _ _ k).trans (minorIdeal_mul_left_le _ _ k)
  · let X : Matrix (Fin m) (Fin n) R :=
      (U : Matrix (Fin m) (Fin m) R) * M * (V : Matrix (Fin n) (Fin n) R)
    have h₁ : minorIdeal ((↑U⁻¹ : Matrix (Fin m) (Fin m) R) * X) k ≤
        minorIdeal X k := minorIdeal_mul_left_le _ _ k
    have h₂ : minorIdeal (((↑U⁻¹ : Matrix (Fin m) (Fin m) R) * X) *
        (↑V⁻¹ : Matrix (Fin n) (Fin n) R)) k ≤
        minorIdeal ((↑U⁻¹ : Matrix (Fin m) (Fin m) R) * X) k :=
      minorIdeal_mul_right_le _ _ k
    have heq : ((↑U⁻¹ : Matrix (Fin m) (Fin m) R) * X) *
        (↑V⁻¹ : Matrix (Fin n) (Fin n) R) = M := by
      simp [X, ← Matrix.mul_assoc]
    rw [heq] at h₂
    exact h₂.trans h₁

theorem zero_size : D05.Specs.MinorIdeals.zero_size := by
  intro R _ m n M
  apply Ideal.eq_top_of_isUnit_mem _ ?_ (isUnit_one)
  simpa using minor_mem M (Fin.elim0 : Fin 0 → Fin m) (Fin.elim0 : Fin 0 → Fin n)

theorem oversized : D05.Specs.MinorIdeals.oversized := by
  intro R _ m n k M h
  apply le_antisymm _ bot_le
  apply Ideal.span_le.mpr
  rintro x ⟨ρ, κ, rfl⟩
  change (M.submatrix ρ κ).det = 0
  rcases h with h | h
  · apply minor_zero_of_not_injective_row M ρ κ
    intro hi
    have := Fintype.card_le_of_injective ρ hi
    simp only [Fintype.card_fin] at this
    omega
  · apply minor_zero_of_not_injective_col M ρ κ
    intro hi
    have := Fintype.card_le_of_injective κ hi
    simp only [Fintype.card_fin] at this
    omega

/-- An increasing k-tuple of natural indices has its ith index at least i. -/
lemma strictMono_nat_bound (f : Fin k → ℕ) (hf : StrictMono f) (i : Fin k) :
    i.val ≤ f i := by
  have H : ∀ a (ha : a < k), a ≤ f ⟨a, ha⟩ := by
    intro a
    induction a with
    | zero => intro ha; exact Nat.zero_le _
    | succ a ih =>
      intro ha
      have hb : a < k := by omega
      have hlt := hf (show (⟨a, hb⟩ : Fin k) < ⟨a + 1, ha⟩ from Nat.lt_succ_self a)
      have hle := ih hb
      omega
  exact H i.val i.isLt

/-- Sort the selected indices, then use i ≤ index(i) and divisibility termwise. -/
lemma prefix_dvd_selected {A : Type*} [CommMonoid A] (d : ℕ → A)
    (hchain : ∀ i j, i ≤ j → d i ∣ d j) (ρ : Fin k → ℕ)
    (hρ : Function.Injective ρ) : prefixProduct d k ∣ ∏ i, d (ρ i) := by
  classical
  let S := Finset.univ.image ρ
  have hS : S.card = k := by
    simp [S, Finset.card_image_of_injective _ hρ]
  let e := S.orderEmbOfFin hS
  have hprod : (∏ i : Fin k, d (e i)) = ∏ i : Fin k, d (ρ i) := by
    calc
      _ = ∏ a ∈ Finset.univ.image e, d a :=
        (Finset.prod_image e.injective.injOn).symm
      _ = ∏ a ∈ S, d a := by rw [Finset.image_orderEmbOfFin_univ]
      _ = _ := Finset.prod_image hρ.injOn
  unfold prefixProduct
  rw [← Fin.prod_univ_eq_prod_range, ← hprod]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ =>
    hchain i.val (e i) (strictMono_nat_bound e e.strictMono i))

/-- The diagonal factor of each selected row factors out of its minor. -/
lemma diagonal_minor_dvd (d : ℕ → R) (hchain : ∀ i j, i ≤ j → d i ∣ d j)
    (ρ : Fin k → Fin m) (κ : Fin k → Fin n) :
    prefixProduct d k ∣ ((rectDiagonal m n d).submatrix ρ κ).det := by
  classical
  by_cases hr : Function.Injective ρ
  · let B : Matrix (Fin k) (Fin k) R :=
      fun i j => if (ρ i).val = (κ j).val then 1 else 0
    have hmatrix : (rectDiagonal m n d).submatrix ρ κ =
        Matrix.of (fun i j => d (ρ i).val * B i j) := by
      ext i j
      simp only [rectDiagonal, Matrix.submatrix_apply, Matrix.of_apply, B]
      split <;> simp_all
    rw [hmatrix, Matrix.det_mul_column]
    exact dvd_mul_of_dvd_left (prefix_dvd_selected d hchain
      (fun i => (ρ i).val) (fun _ _ h => hr (Fin.ext h))) _
  · rw [minor_zero_of_not_injective_row _ _ _ hr]
    exact dvd_zero _

/-- Leading k by k submatrix of a rectangular diagonal. -/
lemma leading_minor (d : ℕ → R) (hm : k ≤ m) (hn : k ≤ n) :
    ((rectDiagonal m n d).submatrix (Fin.castLE hm) (Fin.castLE hn)).det =
      prefixProduct d k := by
  have heq : (rectDiagonal m n d).submatrix (Fin.castLE hm) (Fin.castLE hn) =
      Matrix.diagonal (fun i : Fin k => d i.val) := by
    ext i j
    simp [rectDiagonal, Matrix.diagonal_apply, Fin.ext_iff]
  rw [heq, Matrix.det_diagonal, Fin.prod_univ_eq_prod_range, prefixProduct]

lemma diagonal_ideal_formula (d : ℕ → R)
    (hchain : ∀ i j, i ≤ j → d i ∣ d j) (hm : k ≤ m) (hn : k ≤ n) :
    minorIdeal (rectDiagonal m n d) k = Ideal.span {prefixProduct d k} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨ρ, κ, rfl⟩
    exact Ideal.mem_span_singleton.mpr (diagonal_minor_dvd d hchain ρ κ)
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [← leading_minor d hm hn]
    exact minor_mem _ _ _

section Polynomial
variable {K : Type*} [Field K]

lemma span_minorGcd (M : Matrix (Fin m) (Fin n) (Polynomial K)) (k : ℕ) :
    Ideal.span {minorGcd M k} = minorIdeal M k := by
  classical
  exact (D05.Foundations.IdealsGcd.span_normalize _).trans
    (Ideal.span_singleton_generator _)

lemma minorGcd_eq_zero_iff (M : Matrix (Fin m) (Fin n) (Polynomial K)) (k : ℕ) :
    minorGcd M k = 0 ↔ minorIdeal M k = ⊥ := by
  classical
  exact normalize_eq_zero.trans
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).symm

lemma minorGcd_monic (M : Matrix (Fin m) (Fin n) (Polynomial K)) (k : ℕ)
    (h : minorGcd M k ≠ 0) : (minorGcd M k).Monic := by
  classical
  apply Polynomial.monic_normalize
  exact fun hz => h (normalize_eq_zero.mpr hz)

lemma dvd_minorGcd_iff (M : Matrix (Fin m) (Fin n) (Polynomial K)) (k : ℕ)
    (p : Polynomial K) : p ∣ minorGcd M k ↔
      ∀ (ρ : Fin k → Fin m) (κ : Fin k → Fin n), p ∣ (M.submatrix ρ κ).det := by
  constructor
  · intro h ρ κ
    have hle : minorIdeal M k ≤ Ideal.span {p} := by
      rw [← span_minorGcd]
      exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr h)
    exact Ideal.mem_span_singleton.mp (hle (minor_mem M ρ κ))
  · intro h
    have hle : minorIdeal M k ≤ Ideal.span {p} := by
      apply Ideal.span_le.mpr
      rintro x ⟨ρ, κ, rfl⟩
      exact Ideal.mem_span_singleton.mpr (h ρ κ)
    apply Ideal.mem_span_singleton.mp
    apply hle
    rw [← span_minorGcd]
    exact Ideal.subset_span (Set.mem_singleton _)

end Polynomial

theorem gcd_properties : D05.Specs.MinorIdeals.gcd_properties := by
  intro K _ m n k M
  exact ⟨span_minorGcd M k, minorGcd_eq_zero_iff M k, minorGcd_monic M k,
    dvd_minorGcd_iff M k⟩

lemma prefixProduct_zero_of_rank {K : Type*} [Field K] (d : ℕ → Polynomial K)
    {r k : ℕ} (htail : ∀ i, r ≤ i → d i = 0) (hk : r < k) :
    prefixProduct d k = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hk) (htail r le_rfl)

theorem diagonal_ideals : D05.Specs.MinorIdeals.diagonal_ideals := by
  intro K _ m n r d hm hn hd
  refine ⟨fun k hk => diagonal_ideal_formula d hd.2.2 (hk.trans hm) (hk.trans hn),
    ?_, zero_size _ _ _ _⟩
  intro k hk
  by_cases hkm : k ≤ m
  · by_cases hkn : k ≤ n
    · rw [diagonal_ideal_formula d hd.2.2 hkm hkn,
        prefixProduct_zero_of_rank d hd.2.1 hk, Ideal.span_singleton_zero]
    · exact oversized _ _ _ _ _ (Or.inr (by omega))
  · exact oversized _ _ _ _ _ (Or.inl (by omega))

section Polynomial
variable {K : Type*} [Field K]

lemma prefixProduct_monic (d : ℕ → Polynomial K) {r k : ℕ}
    (hmonic : ∀ i, i < r → (d i).Monic) (hk : k ≤ r) :
    (prefixProduct d k).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i hi =>
    hmonic i ((Finset.mem_range.mp hi).trans_le hk))

lemma minorGcd_eq_monic_generator (M : Matrix (Fin m) (Fin n) (Polynomial K))
    (k : ℕ) (p : Polynomial K) (hp : p.Monic)
    (hI : minorIdeal M k = Ideal.span {p}) : minorGcd M k = p := by
  have hn : minorGcd M k ≠ 0 := by
    intro hz
    have hmem : p ∈ Ideal.span {minorGcd M k} := by
      rw [span_minorGcd, hI]
      exact Ideal.subset_span (Set.mem_singleton _)
    rw [hz, Ideal.span_singleton_zero] at hmem
    exact hp.ne_zero hmem
  exact D05.Foundations.IdealsGcd.monic_generators_eq
    (minorGcd_monic M k hn) hp ((span_minorGcd M k).trans hI)

lemma minorGcd_eq_of_ideal_eq {M N : Matrix (Fin m) (Fin n) (Polynomial K)}
    (k : ℕ) (h : minorIdeal M k = minorIdeal N k) : minorGcd M k = minorGcd N k := by
  classical
  let F (I : Ideal (Polynomial K)) : Polynomial K :=
    normalize (Submodule.IsPrincipal.generator I)
  exact congrArg F h

end Polynomial

theorem diagonal_gcd : D05.Specs.MinorIdeals.diagonal_gcd := by
  intro K _ m n r d hm hn hd
  obtain ⟨hsmall, hlarge, _⟩ := diagonal_ideals K m n r d hm hn hd
  have hdelta : ∀ k, k ≤ r → minorGcd (rectDiagonal m n d) k = prefixProduct d k := by
    intro k hk
    exact minorGcd_eq_monic_generator _ k _ (prefixProduct_monic d hd.1 hk) (hsmall k hk)
  refine ⟨hdelta, fun k hk => (minorGcd_eq_zero_iff _ _).mpr (hlarge k hk),
    ?_, ?_⟩
  · simpa [prefixProduct] using hdelta 0 (Nat.zero_le r)
  · intro i hi
    rw [hdelta (i + 1) (by omega), hdelta i (by omega)]
    unfold prefixProduct
    rw [Finset.prod_range_succ]
    exact (mul_div_cancel_left₀ (d i) (prefixProduct_monic d hd.1 (by omega)).ne_zero).symm

theorem transformed_gcd : D05.Specs.MinorIdeals.transformed_gcd := by
  intro K _ m n r d M U V hm hn hd hdiag
  have heq : ∀ k, minorGcd M k = minorGcd (rectDiagonal m n d) k := by
    intro k
    apply minorGcd_eq_of_ideal_eq
    rw [← hdiag]
    exact (invertible_invariance _ _ _ _ _ U V).symm
  obtain ⟨hsmall, hlarge, hzero, hquot⟩ := diagonal_gcd K m n r d hm hn hd
  refine ⟨fun k hk => (heq k).trans (hsmall k hk),
    fun k hk => (heq k).trans (hlarge k hk), (heq 0).trans hzero, ?_⟩
  intro i hi
  rw [heq, heq]
  exact hquot i hi

end D05.M10.InvariantFactorComputation.MinorIdeals
