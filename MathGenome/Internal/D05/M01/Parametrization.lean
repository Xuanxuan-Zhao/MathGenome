import MathGenome.Internal.Specs.D05.M01.Parametrization
import MathGenome.Internal.D05.M01.Echelon

namespace D05.M01.Parametrization
open scoped BigOperators Matrix
universe u
variable {K : Type u} [Field K] {m n : ℕ}

noncomputable def parametrize (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (t : FreeColumn R → K) : Fin n → K := formula R b t

/-- A pivot in a coefficient column remains a pivot after augmentation. -/
theorem leadingEntry_augmented (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    {i : Fin m} {p : Fin n} (hp : R.IsLeadingEntry i p) :
    (System.augmentedMatrix R b).IsLeadingEntry i p.castSucc := by
  refine ⟨?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro hj
      exact (not_lt_of_ge (Fin.le_last _) hj).elim
    · intro hj
      rw [System.augmentedMatrix_castSucc]
      exact hp.1 k (by simpa using hj)
  · simpa only [System.augmentedMatrix_castSucc] using hp.2

theorem coefficient_reduced : Specs.D05.M01.Parametrization.coefficient_reduced := by
  intro K _ m n R b h
  change (System.augmentedMatrix R b).IsReducedRowEchelon at h
  refine ⟨?_, ?_, ?_⟩
  · intro i k hik j hj
    have he := h.isRowEchelon hik (j₂ := j.castSucc)
    rw [← System.augmentedMatrix_castSucc R b k j]
    apply he
    intro c
    refine Fin.lastCases ?_ (fun d => ?_) c
    · intro hc
      exact (not_lt_of_ge (Fin.le_last _) hc).elim
    · intro hc
      rw [System.augmentedMatrix_castSucc]
      exact hj d (by simpa using hc)
  · intro i p hp
    simpa only [System.augmentedMatrix_castSucc] using
      h.eq_one (leadingEntry_augmented R b hp)
  · intro i k p hik hp
    simpa only [System.augmentedMatrix_castSucc] using
      h.eq_zero hik (leadingEntry_augmented R b hp)

theorem free_card : Specs.D05.M01.Parametrization.free_card := by
  intro K _ m n R
  simpa only [Fintype.card_fin, pivotCount] using
    (Fintype.card_subtype_compl (fun j => ∃ i, R.IsLeadingEntry i j))

theorem pivot_row_unique (R : Matrix (Fin m) (Fin n) K) (hR : R.IsReducedRowEchelon)
    {i k : Fin m} {p : Fin n} (hi : R.IsLeadingEntry i p)
    (hk : R.IsLeadingEntry k p) : i = k := by
  by_contra hne
  exact one_ne_zero ((hR.eq_one hi).symm.trans
    (hR.eq_zero_of_ne_of_isLeadingEntry hne hk))

theorem pivotCount_eq_nonzero_rows :
    Specs.D05.M01.Parametrization.pivotCount_eq_nonzero_rows := by
  intro K _ m n R hR
  classical
  let f : {i : Fin m // R i ≠ 0} → PivotColumn R := fun i =>
    ⟨(Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp i.property).choose,
      i, (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp i.property).choose_spec⟩
  have hf : ∀ i : {i : Fin m // R i ≠ 0}, R.IsLeadingEntry i (f i) :=
    fun i => (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp i.property).choose_spec
  have hbij : Function.Bijective f := by
    constructor
    · intro i k hik
      apply Subtype.ext
      exact pivot_row_unique R hR (hf i) (hik.symm ▸ hf k)
    · rintro ⟨p, i, hi⟩
      refine ⟨⟨i, hi.row_ne_zero⟩, Subtype.ext ?_⟩
      exact (hf ⟨i, hi.row_ne_zero⟩).unique hi
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (Equiv.ofBijective f hbij)).symm

theorem parametrize_free : Specs.D05.M01.Parametrization.parametrize_free := by
  intro K _ m n R b t j
  classical
  simp only [formula, dite_eq_right j.property]

theorem parametrize_pivot : Specs.D05.M01.Parametrization.parametrize_pivot := by
  intro K _ m n R b hR t i p hp
  classical
  have hex : ∃ k, R.IsLeadingEntry k p := ⟨i, hp⟩
  have hi : hex.choose = i := pivot_row_unique R hR hex.choose_spec hp
  simp only [formula, dite_eq_left hex, hi]

/-- The sum on the pivot columns is exactly the coordinate of this row's pivot. -/
theorem pivot_row_sum (R : Matrix (Fin m) (Fin n) K) (hR : R.IsReducedRowEchelon)
    {i : Fin m} {p : Fin n} (hp : R.IsLeadingEntry i p) (x : Fin n → K) :
    (∑ j : Fin n, R i j * x j) =
      x p + ∑ j : FreeColumn R, R i j * x j := by
  classical
  have hs : (∑ j : PivotColumn R, R i j * x j) = x p := by
    let c : PivotColumn R := ⟨p, i, hp⟩
    rw [Finset.sum_eq_single c]
    · simp only [c, hR.eq_one hp, one_mul]
    · intro j _ hj
      obtain ⟨k, hk⟩ := j.property
      have hki : i ≠ k := by
        intro he
        subst k
        exact hj (Subtype.ext (hk.unique hp))
      rw [hR.eq_zero_of_ne_of_isLeadingEntry hki hk, zero_mul]
    · simp
  calc
    _ = (∑ j : PivotColumn R, R i j * x j) +
        ∑ j : FreeColumn R, R i j * x j :=
      (Fintype.sum_subtype_add_sum_subtype (fun j => ∃ k, R.IsLeadingEntry k j)
        (fun j => R i j * x j)).symm
    _ = _ := by rw [hs]

/-- Consistency forces the right-hand side of every zero row to be zero. -/
theorem rhs_zero_of_zero_row (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (hc : ∃ x, System.IsSolution R b x) {i : Fin m} (hi : R i = 0) : b i = 0 := by
  obtain ⟨x, hx⟩ := hc
  have h := (System.solution_iff_rows R b x).mp hx i
  have hz : ∀ j, R i j = 0 := fun j => congrFun hi j
  simpa only [hz, zero_mul, Finset.sum_const_zero] using h.symm

/-- The algebraic row calculation also works with zero-row compatibility stated explicitly. -/
theorem solution_iff_pivot_equations_of_zero_rows
    (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (hR : R.IsReducedRowEchelon) (hb : ∀ i, R i = 0 → b i = 0) (x : Fin n → K) :
    System.IsSolution R b x ↔ ∀ i p, R.IsLeadingEntry i p →
      x p = b i - ∑ j : FreeColumn R, R i j * x j := by
  rw [System.solution_iff_rows]
  constructor
  · intro hx i p hp
    apply eq_sub_iff_add_eq.mpr
    rw [← pivot_row_sum R hR hp x]
    exact hx i
  · intro hx i
    by_cases hi : R i = 0
    · have hz : ∀ j, R i j = 0 := fun j => congrFun hi j
      simp only [hz, zero_mul, Finset.sum_const_zero, hb i hi]
    · obtain ⟨p, hp⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hi
      rw [pivot_row_sum R hR hp x]
      exact eq_sub_iff_add_eq.mp (hx i p hp)

theorem solution_iff_pivot_equations :
    Specs.D05.M01.Parametrization.solution_iff_pivot_equations := by
  intro K _ m n R b hAug hc x
  exact solution_iff_pivot_equations_of_zero_rows R b (coefficient_reduced R b hAug)
    (fun _ hi => rhs_zero_of_zero_row R b hc hi) x

theorem formula_solves_of_zero_rows (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (hR : R.IsReducedRowEchelon) (hb : ∀ i, R i = 0 → b i = 0)
    (t : FreeColumn R → K) : System.IsSolution R b (formula R b t) := by
  apply (solution_iff_pivot_equations_of_zero_rows R b hR hb _).mpr
  intro i p hp
  rw [parametrize_pivot R b hR t i p hp]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [parametrize_free R b t j]

theorem formula_solves : Specs.D05.M01.Parametrization.formula_solves := by
  intro K _ m n R b hAug hc t
  exact formula_solves_of_zero_rows R b (coefficient_reduced R b hAug)
    (fun _ hi => rhs_zero_of_zero_row R b hc hi) t

/-- Any solution equals the formula applied to its own free coordinates. -/
theorem solution_eq_formula (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (hR : R.IsReducedRowEchelon) {x : Fin n → K} (hx : System.IsSolution R b x) :
    x = formula R b (freeCoordinates R x) := by
  classical
  funext j
  by_cases hj : ∃ i, R.IsLeadingEntry i j
  · obtain ⟨i, hi⟩ := hj
    rw [parametrize_pivot R b hR _ i j hi]
    apply eq_sub_iff_add_eq.mpr
    change x j + ∑ k : FreeColumn R, R i k * x k = b i
    rw [← pivot_row_sum R hR hi x]
    exact (System.solution_iff_rows R b x).mp hx i
  · exact (parametrize_free R b (freeCoordinates R x) ⟨j, hj⟩).symm

theorem freeCoordinates_formula (R : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (t : FreeColumn R → K) : freeCoordinates R (formula R b t) = t := by
  funext j
  exact parametrize_free R b t j

theorem unique_solution : Specs.D05.M01.Parametrization.unique_solution := by
  intro K _ m n R b hAug hc t
  refine ⟨formula R b t, ⟨formula_solves R b hAug hc t,
    freeCoordinates_formula R b t⟩, ?_⟩
  rintro x ⟨hx, ht⟩
  rw [solution_eq_formula R b (coefficient_reduced R b hAug) hx, ht]

theorem solution_equiv : Specs.D05.M01.Parametrization.solution_equiv := by
  intro K _ m n R b hAug hc
  let e : (FreeColumn R → K) ≃ {x // System.IsSolution R b x} :=
    { toFun := fun t => ⟨formula R b t, formula_solves R b hAug hc t⟩
      invFun := fun x => freeCoordinates R x.val
      left_inv := freeCoordinates_formula R b
      right_inv := fun x => Subtype.ext
        (solution_eq_formula R b (coefficient_reduced R b hAug) x.property).symm }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

theorem solution_equiv_fin : Specs.D05.M01.Parametrization.solution_equiv_fin := by
  intro K _ m n R b hAug hc
  obtain ⟨e, _⟩ := solution_equiv R b hAug hc
  let c := Fintype.equivFinOfCardEq (free_card R)
  exact ⟨(Equiv.arrowCongr c.symm (Equiv.refl K)).trans e⟩

theorem homogeneous_linear_equiv : Specs.D05.M01.Parametrization.homogeneous_linear_equiv := by
  intro K _ m n R hR
  let f : homogeneousSpace R →ₗ[K] (FreeColumn R → K) :=
    { toFun := fun x => freeCoordinates R x.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      calc
        x.val = formula R 0 (f x) := solution_eq_formula R 0 hR x.property
        _ = formula R 0 (f y) := congrArg (formula R 0) hxy
        _ = y.val := (solution_eq_formula R 0 hR y.property).symm
    · intro t
      refine ⟨⟨formula R 0 t, formula_solves_of_zero_rows R 0 hR (fun _ _ => rfl) t⟩, ?_⟩
      exact freeCoordinates_formula R 0 t
  let e := (LinearEquiv.ofBijective f hf).symm
  refine ⟨e, ?_, fun _ => rfl⟩
  intro t
  have ht : freeCoordinates R (e t).val = t := e.symm_apply_apply t
  exact (solution_eq_formula R 0 hR (e t).property).trans (congrArg (formula R 0) ht)

theorem homogeneous_linear_equiv_fin :
    Specs.D05.M01.Parametrization.homogeneous_linear_equiv_fin := by
  intro K _ m n R hR
  obtain ⟨e, _⟩ := homogeneous_linear_equiv R hR
  exact ⟨(LinearEquiv.funCongrLeft K K (Fintype.equivFinOfCardEq (free_card R))).trans e⟩

theorem homogeneous_dimension : Specs.D05.M01.Parametrization.homogeneous_dimension := by
  intro K _ m n R hR
  obtain ⟨e, _⟩ := homogeneous_linear_equiv R hR
  rw [← e.finrank_eq, Module.finrank_pi, free_card R]

end D05.M01.Parametrization
