import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorActions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.PolynomialHomogeneousDecomposition
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open scoped BigOperators
open Module
universe u v
namespace AdvancedFiniteGroupRepresentations

abbrev matrixCoordinates := @Specs.AdvancedFiniteGroupRepresentations.matrixCoordinates
abbrev IsPolynomialRepresentation :=
  @Specs.AdvancedFiniteGroupRepresentations.IsPolynomialRepresentation
abbrev IsHomogeneousRepresentation :=
  @Specs.AdvancedFiniteGroupRepresentations.IsHomogeneousRepresentation
abbrev scalarElement := @Specs.AdvancedFiniteGroupRepresentations.scalarElement
abbrev weightSpace := @Specs.AdvancedFiniteGroupRepresentations.weightSpace
abbrev IsInvariant := @Specs.AdvancedFiniteGroupRepresentations.IsInvariant
abbrev restrictedRepresentation :=
  @Specs.AdvancedFiniteGroupRepresentations.restrictedRepresentation
abbrev HomogeneousDecomposition :=
  @Specs.AdvancedFiniteGroupRepresentations.HomogeneousDecomposition

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {d m : ℕ}

@[simp] theorem scalarElement_apply (t : ℂˣ) (v : V) :
    scalarElement V t v = (t : ℂ) • v := rfl

@[simp] theorem scalarElement_one : scalarElement V 1 = 1 := by
  ext x
  simp

theorem scalarElement_mul (t s : ℂˣ) :
    scalarElement V (t * s) = scalarElement V t * scalarElement V s := by
  ext x
  simp [smul_smul, mul_comm]

theorem scalarElement_central (t : ℂˣ) (g : LinearGroup V) :
    scalarElement V t * g = g * scalarElement V t := by
  ext x
  simp

theorem weightSpace_invariant (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ) :
    IsInvariant ρ (weightSpace ρ n) := by
  intro g w hw t
  change ρ (scalarElement V t) (ρ g w) = (t : ℂ) ^ n • ρ g w
  have hc := congrArg ρ (scalarElement_central t g)
  rw [map_mul, map_mul] at hc
  calc
    ρ (scalarElement V t) (ρ g w) = ρ g (ρ (scalarElement V t) w) :=
      DFunLike.congr_fun hc w
    _ = (t : ℂ) ^ n • ρ g w := by rw [hw t, map_smul]

theorem homogeneous_isPolynomial (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ)
    (h : IsHomogeneousRepresentation b c ρ n) : IsPolynomialRepresentation b c ρ := by
  intro i j
  obtain ⟨p, _, hp⟩ := h i j
  exact ⟨p, hp⟩

theorem zero_dimension_group_trivial (b : Basis (Fin 0) ℂ V) (g : LinearGroup V) :
    g = 1 := by
  have hv : ∀ x : V, x = 0 := by
    intro x
    apply b.repr.injective
    ext i
    exact Fin.elim0 i
  ext x
  exact (hv _).trans (hv _).symm

theorem zero_dimension_degree_zero (b : Basis (Fin 0) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) : IsHomogeneousRepresentation b c ρ 0 := by
  intro i j
  refine ⟨MvPolynomial.C ((1 : Matrix (Fin m) (Fin m) ℂ) i j),
    MvPolynomial.isHomogeneous_C _ _, ?_⟩
  intro g
  rw [zero_dimension_group_trivial b g, map_one]
  simp

theorem zero_dimension_no_positive_degree (b : Basis (Fin 0) ℂ V)
    (c : Basis (Fin m) ℂ W) (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ)
    (hn : 0 < n) (h : IsHomogeneousRepresentation b c ρ n) : Subsingleton W := by
  have hz : ∀ i j, LinearMap.toMatrix c c (1 : Module.End ℂ W) i j = 0 := by
    intro i j
    obtain ⟨p, hp, heval⟩ := h i j
    have hpz : p = 0 := by
      by_contra hpz
      have := (MvPolynomial.isHomogeneous_of_isEmpty _ _ p).inj_right hp hpz
      omega
    simpa [hpz] using (heval 1).symm
  have hzero : (1 : Module.End ℂ W) = 0 := by
    apply (LinearMap.toMatrix c c).injective
    ext i j
    simpa using hz i j
  exact ⟨fun x y => by
    have h : ∀ w : W, w = 0 := fun w => by
      simpa using DFunLike.congr_fun hzero w
    exact (h x).trans (h y).symm⟩

/-- Substitution of a scalar matrix into an entry polynomial. -/
def scalarPolynomial (p : MvPolynomial (Fin d × Fin d) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun ij => if ij.1 = ij.2 then Polynomial.X else 0) p

theorem eval_scalarPolynomial (p : MvPolynomial (Fin d × Fin d) ℂ) (t : ℂ) :
    (scalarPolynomial p).eval t =
      MvPolynomial.eval (fun ij => if ij.1 = ij.2 then t else 0) p := by
  unfold scalarPolynomial
  change (Polynomial.evalRingHom t) (MvPolynomial.eval₂ _ _ p) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext a
    simp
  rw [hC, MvPolynomial.eval₂_id]
  have hX : (⇑(Polynomial.evalRingHom t) ∘
      fun ij : Fin d × Fin d => if ij.1 = ij.2 then Polynomial.X else 0) =
      fun ij => if ij.1 = ij.2 then t else 0 := by
    funext ij
    simp only [Function.comp_apply]
    split_ifs <;> simp_all
  rw [hX]

theorem scalar_matrixCoordinates (b : Basis (Fin d) ℂ V) (t : ℂˣ) :
    matrixCoordinates b (scalarElement V t) =
      fun ij => if ij.1 = ij.2 then (t : ℂ) else 0 := by
  funext ij
  simp [matrixCoordinates, Specs.AdvancedFiniteGroupRepresentations.matrixCoordinates,
    LinearMap.toMatrix_apply, Finsupp.single_apply, eq_comm]

set_option backward.isDefEq.respectTransparency false in
theorem scalar_polynomial_expansion (b : Basis (Fin d) ℂ V)
    (c : Basis (Fin m) ℂ W) (ρ : LinearGroup V →* Module.End ℂ W)
    (h : IsPolynomialRepresentation b c ρ) :
    ∃ (N : ℕ) (P : ℕ → Module.End ℂ W),
      (∀ n, N < n → P n = 0) ∧
      ∀ t : ℂˣ, ρ (scalarElement V t) =
        ∑ n ∈ Finset.range (N + 1), (t : ℂ) ^ n • P n := by
  classical
  let p : Fin m → Fin m → MvPolynomial (Fin d × Fin d) ℂ :=
    fun i j => Classical.choose (h i j)
  have hp : ∀ i j g, MvPolynomial.eval (matrixCoordinates b g) (p i j) =
      LinearMap.toMatrix c c (ρ g) i j := fun i j => Classical.choose_spec (h i j)
  let q : Fin m → Fin m → Polynomial ℂ := fun i j => scalarPolynomial (p i j)
  let N := (Finset.univ : Finset (Fin m × Fin m)).sup
    (fun ij => (q ij.1 ij.2).natDegree)
  have hN : ∀ i j, (q i j).natDegree ≤ N := fun i j =>
    Finset.le_sup (b := (i,j)) (f := fun ij : Fin m × Fin m => (q ij.1 ij.2).natDegree)
      (Finset.mem_univ (i,j))
  let P : ℕ → Module.End ℂ W := fun n =>
    Matrix.toLin c c (fun i j => (q i j).coeff n)
  refine ⟨N, P, ?_, ?_⟩
  · intro n hn
    refine (LinearMap.toMatrix c c).injective ?_
    ext i j
    simp only [P, LinearMap.toMatrix_toLin, map_zero, Matrix.zero_apply]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hN i j).trans_lt hn)
  · intro t
    refine (LinearMap.toMatrix c c).injective ?_
    ext i j
    have heval : (q i j).eval (t : ℂ) =
        LinearMap.toMatrix c c (ρ (scalarElement V t)) i j := by
      rw [show q i j = scalarPolynomial (p i j) from rfl, eval_scalarPolynomial,
        ← scalar_matrixCoordinates b t]
      exact hp i j _
    rw [← heval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hN i j))]
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
      P, LinearMap.toMatrix_toLin, smul_eq_mul]
    exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)

theorem scalar_coefficients_sum (ρ : LinearGroup V →* Module.End ℂ W)
    (N : ℕ) (P : ℕ → Module.End ℂ W)
    (h : ∀ t : ℂˣ, ρ (scalarElement V t) =
      ∑ n ∈ Finset.range (N + 1), (t : ℂ) ^ n • P n) :
    ∑ n ∈ Finset.range (N + 1), P n = 1 := by
  simpa using (h 1).symm

/-- Polynomial matrix entries are preserved by fixed linear maps on either side. -/
theorem polynomial_entries_sandwich {U : Type*} [AddCommGroup U] [Module ℂ U]
    {k : ℕ} (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (r : Basis (Fin k) ℂ U) (ρ : LinearGroup V →* Module.End ℂ W)
    (h : IsPolynomialRepresentation b c ρ) (ι : U →ₗ[ℂ] W) (π : W →ₗ[ℂ] U) :
    ∀ i j, ∃ p : MvPolynomial (Fin d × Fin d) ℂ,
      ∀ g, MvPolynomial.eval (matrixCoordinates b g) p =
        LinearMap.toMatrix r r (π.comp ((ρ g).comp ι)) i j := by
  classical
  let p : Fin m → Fin m → MvPolynomial (Fin d × Fin d) ℂ :=
    fun a b => Classical.choose (h a b)
  have hp : ∀ a z g, MvPolynomial.eval (matrixCoordinates b g) (p a z) =
      LinearMap.toMatrix c c (ρ g) a z := fun a z => Classical.choose_spec (h a z)
  intro i j
  refine ⟨∑ a : Fin m, ∑ z : Fin m,
    MvPolynomial.C (LinearMap.toMatrix c r π i a) *
      (p a z * MvPolynomial.C (LinearMap.toMatrix r c ι z j)), ?_⟩
  intro g
  simp only [map_sum, map_mul, MvPolynomial.eval_C, hp,
    LinearMap.toMatrix_comp r c r, LinearMap.toMatrix_comp r c c,
    Matrix.mul_apply, Finset.mul_sum]

theorem invariant_subspace_isPolynomial (b : Basis (Fin d) ℂ V)
    (c : Basis (Fin m) ℂ W) (ρ : LinearGroup V →* Module.End ℂ W)
    (h : IsPolynomialRepresentation b c ρ) (U : Submodule ℂ W)
    (hU : IsInvariant ρ U) {k : ℕ} (r : Basis (Fin k) ℂ U) :
    IsPolynomialRepresentation b r (restrictedRepresentation ρ U hU) := by
  let π := U.subtype.leftInverse
  have hπ : ∀ x : U, π (x : W) = x :=
    LinearMap.leftInverse_apply_of_inj U.ker_subtype
  have heq : ∀ g, π.comp ((ρ g).comp U.subtype) = restrictedRepresentation ρ U hU g := by
    intro g
    ext x
    exact congrArg Subtype.val (hπ (restrictedRepresentation ρ U hU g x))
  intro i j
  obtain ⟨p, hp⟩ := polynomial_entries_sandwich b c r ρ h U.subtype π i j
  exact ⟨p, fun g => (hp g).trans (congrArg (fun f => LinearMap.toMatrix r r f i j) (heq g))⟩

/-- Polynomial identities may be checked on the nonzero complex numbers. -/
lemma polynomial_eq_of_units (p q : Polynomial ℂ)
    (h : ∀ t : ℂˣ, p.eval (t : ℂ) = q.eval (t : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_singleton (0 : ℂ)).infinite_compl.mono
  intro z hz
  exact h (Units.mk0 z hz)

/-- Finite polynomial expansions with coefficients in a complex vector space are unique. -/
lemma sum_coefficients_unique {E : Type*} [AddCommGroup E] [Module ℂ E]
    (N : ℕ) (A B : ℕ → E)
    (hA : ∀ n, N < n → A n = 0) (hB : ∀ n, N < n → B n = 0)
    (h : ∀ t : ℂˣ, ∑ k ∈ Finset.range (N+1), (t : ℂ)^k • A k =
      ∑ k ∈ Finset.range (N+1), (t : ℂ)^k • B k) : A = B := by
  classical
  let b := Basis.ofVectorSpace ℂ E
  funext n
  by_cases hn : n < N+1
  · apply b.repr.injective
    ext i
    have heq : (∑ k ∈ Finset.range (N+1), Polynomial.monomial k (b.repr (A k) i)) =
        ∑ k ∈ Finset.range (N+1), Polynomial.monomial k (b.repr (B k) i) := by
      apply polynomial_eq_of_units
      intro t
      have hh := congrArg (fun x => b.repr x i) (h t)
      simpa [Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm] using hh
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff n) heq
    simpa [Polynomial.coeff_monomial, Finset.mem_range.mpr hn] using hc
  · rw [hA n (by omega), hB n (by omega)]


lemma coefficients_of_monomial {E : Type*} [AddCommGroup E] [Module ℂ E]
    (N : ℕ) (A : ℕ → E) (n : ℕ) (w : E)
    (hA : ∀ k, N < k → A k = 0)
    (h : ∀ t : ℂˣ, ∑ k ∈ Finset.range (N+1), (t : ℂ)^k • A k = (t : ℂ)^n • w) :
    ∀ k, A k = if k = n then w else 0 := by
  classical
  let b := Basis.ofVectorSpace ℂ E
  intro k
  apply b.repr.injective
  ext i
  have heq : (∑ j ∈ Finset.range (N+1), Polynomial.monomial j (b.repr (A j) i)) =
      Polynomial.monomial n (b.repr w i) := by
    apply polynomial_eq_of_units
    intro t
    have hh := congrArg (fun x => b.repr x i) (h t)
    simpa [Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm] using hh
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff k) heq
  have hc' : (if k < N+1 then b.repr (A k) i else 0) =
      (if k = n then b.repr w i else 0) := by
    simpa [Polynomial.coeff_monomial, eq_comm] using hc
  by_cases hk : k < N+1 <;> by_cases hkn : k = n <;>
    simp_all [apply_ite]

lemma scalar_coefficients_right (ρ : LinearGroup V →* Module.End ℂ W)
    (N : ℕ) (P : ℕ → Module.End ℂ W)
    (hz : ∀ n, N < n → P n = 0)
    (h : ∀ t : ℂˣ, ρ (scalarElement V t) =
      ∑ k ∈ Finset.range (N+1), (t : ℂ)^k • P k) (n : ℕ) (s : ℂˣ) :
    P n * ρ (scalarElement V s) = (s : ℂ)^n • P n := by
  have heq := sum_coefficients_unique N
    (fun k => P k * ρ (scalarElement V s)) (fun k => (s : ℂ)^k • P k)
    (by intro k hk; simp [hz k hk]) (by intro k hk; simp [hz k hk])
    (fun t => by
      calc
        _ = ρ (scalarElement V t) * ρ (scalarElement V s) := by
          rw [h t, Finset.sum_mul]; simp only [smul_mul_assoc]
        _ = ρ (scalarElement V (t*s)) := by rw [scalarElement_mul, map_mul]
        _ = _ := by simp [h (t*s), mul_pow, smul_smul])
  exact congrFun heq n

lemma scalar_coefficients_commute (ρ : LinearGroup V →* Module.End ℂ W)
    (N : ℕ) (P : ℕ → Module.End ℂ W)
    (hz : ∀ n, N < n → P n = 0)
    (h : ∀ t : ℂˣ, ρ (scalarElement V t) =
      ∑ k ∈ Finset.range (N+1), (t : ℂ)^k • P k) (n : ℕ) (g : LinearGroup V) :
    Commute (P n) (ρ g) := by
  have heq := sum_coefficients_unique N
    (fun k => P k * ρ g) (fun k => ρ g * P k)
    (by intro k hk; simp [hz k hk]) (by intro k hk; simp [hz k hk])
    (fun t => by
      calc
        _ = ρ (scalarElement V t) * ρ g := by
          rw [h t, Finset.sum_mul]; simp only [smul_mul_assoc]
        _ = ρ g * ρ (scalarElement V t) := by
          rw [← map_mul, scalarElement_central, map_mul]
        _ = _ := by rw [h t, Finset.mul_sum]; simp only [mul_smul_comm])
  exact congrFun heq n

lemma scalar_coefficients_orthogonal (ρ : LinearGroup V →* Module.End ℂ W)
    (N : ℕ) (P : ℕ → Module.End ℂ W)
    (hz : ∀ n, N < n → P n = 0)
    (h : ∀ t : ℂˣ, ρ (scalarElement V t) =
      ∑ k ∈ Finset.range (N+1), (t : ℂ)^k • P k) (i j : ℕ) :
    P i * P j = if i = j then P i else 0 := by
  have hc := coefficients_of_monomial N (fun k => P i * P k) i (P i)
    (by intro k hk; simp [hz k hk]) (fun t => by
      rw [← scalar_coefficients_right ρ N P hz h i t, h t, Finset.mul_sum]
      simp only [mul_smul_comm]) j
  simpa [eq_comm] using hc

lemma eval_scaled_homogeneous {α : Type*} (p : MvPolynomial α ℂ) (n : ℕ)
    (hp : p.IsHomogeneous n) (x : α → ℂ) (t : ℂ) :
    MvPolynomial.eval (fun a => t * x a) p = t^n * MvPolynomial.eval x p := by
  classical
  rw [p.as_sum, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hdeg : ∑ a ∈ d.support, d a = n := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hp (MvPolynomial.mem_support_iff.mp hd)
  rw [hdeg]
  ring


/-- Extract the unique degree that contributes at a point with the given scaling law. -/
lemma eval_homogeneousComponent_of_scaling {α : Type*} (p : MvPolynomial α ℂ)
    (n : ℕ) (x : α → ℂ)
    (h : ∀ t : ℂˣ, MvPolynomial.eval (fun a => (t : ℂ) * x a) p =
      (t : ℂ)^n * MvPolynomial.eval x p) :
    MvPolynomial.eval x (MvPolynomial.homogeneousComponent n p) = MvPolynomial.eval x p := by
  have hc := coefficients_of_monomial p.totalDegree
    (fun k => MvPolynomial.eval x (MvPolynomial.homogeneousComponent k p))
    n (MvPolynomial.eval x p)
    (by intro k hk; rw [MvPolynomial.homogeneousComponent_eq_zero k p hk, map_zero])
    (fun t => by
      calc
        _ = MvPolynomial.eval (fun a => (t : ℂ) * x a)
            (∑ k ∈ Finset.range (p.totalDegree+1), MvPolynomial.homogeneousComponent k p) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro k hk
          exact (eval_scaled_homogeneous _ k (MvPolynomial.homogeneousComponent_isHomogeneous k p)
            x (t : ℂ)).symm
        _ = _ := by rw [MvPolynomial.sum_homogeneousComponent]; exact h t) n
  simpa using hc

lemma scalar_coefficients_range (ρ : LinearGroup V →* Module.End ℂ W)
    (N : ℕ) (P : ℕ → Module.End ℂ W)
    (hz : ∀ n, N < n → P n = 0)
    (h : ∀ t : ℂˣ, ρ (scalarElement V t) =
      ∑ k ∈ Finset.range (N+1), (t : ℂ)^k • P k) (n : ℕ) :
    LinearMap.range (P n) = weightSpace ρ n := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩ t
    have hc : ρ (scalarElement V t) * P n = (t : ℂ)^n • P n :=
      (scalar_coefficients_commute ρ N P hz h n (scalarElement V t)).symm.eq.trans
        (scalar_coefficients_right ρ N P hz h n t)
    exact DFunLike.congr_fun hc v
  · intro w hw
    have hc := coefficients_of_monomial N (fun k => P k w) n w
      (by intro k hk; simp [hz k hk])
      (fun t => by
        have he := DFunLike.congr_fun (h t) w
        simpa using he.symm.trans (hw t)) n
    exact ⟨w, by simpa using hc⟩

lemma projections_internal (N : ℕ) (P : ℕ → Module.End ℂ W)
    (ho : ∀ i j, P i * P j = if i = j then P i else 0)
    (hs : ∑ k ∈ Finset.range (N+1), P k = 1) :
    DirectSum.IsInternal (fun n => LinearMap.range (P n)) := by
  classical
  have h_on : ∀ i j w, w ∈ LinearMap.range (P j) →
      P i w = if i = j then w else 0 := by
    rintro i j w ⟨v, rfl⟩
    have hc := DFunLike.congr_fun (ho i j) v
    by_cases hij : i=j <;> simpa [hij] using hc
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hvsum i hi
    have hc := congrArg (P i) hvsum
    simp only [map_sum, map_zero] at hc
    have he : ∑ j ∈ s, P i (v j) = v i := by
      calc
        _ = ∑ j ∈ s, if i = j then v j else 0 :=
          Finset.sum_congr rfl (fun j hj => h_on i j (v j) (hv j hj))
        _ = v i := by simp [hi]
    exact he.symm.trans hc
  · apply top_unique
    intro w hw
    have he : ∑ k ∈ Finset.range (N+1), P k w = w := by
      simpa using DFunLike.congr_fun hs w
    rw [← he]
    exact Submodule.sum_mem _ (fun k hk =>
      (le_iSup (fun n => LinearMap.range (P n)) k) ⟨w, rfl⟩)


lemma scalar_mul_matrixCoordinates {d : ℕ} (b : Basis (Fin d) ℂ V)
    (t : ℂˣ) (g : LinearGroup V) :
    matrixCoordinates b (scalarElement V t * g) =
      fun ij => (t : ℂ) * matrixCoordinates b g ij := by
  funext ij
  simp [matrixCoordinates, Specs.AdvancedFiniteGroupRepresentations.matrixCoordinates,
    LinearMap.toMatrix_apply]

lemma polynomial_weight_isHomogeneous {d m : ℕ}
    (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) (n : ℕ)
    (h : IsPolynomialRepresentation b c ρ)
    (hw : ∀ t : ℂˣ, ρ (scalarElement V t) = (t : ℂ)^n • 1) :
    IsHomogeneousRepresentation b c ρ n := by
  intro i j
  obtain ⟨p, hp⟩ := h i j
  refine ⟨MvPolynomial.homogeneousComponent n p,
    MvPolynomial.homogeneousComponent_isHomogeneous n p, ?_⟩
  intro g
  apply Eq.trans _ (hp g)
  apply eval_homogeneousComponent_of_scaling
  intro t
  rw [← scalar_mul_matrixCoordinates, hp, map_mul, hw]
  simp [hp]

lemma range_subrepresentation_homogeneous [FiniteDimensional ℂ W] {d m : ℕ}
    (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) (h : IsPolynomialRepresentation b c ρ)
    (U : Submodule ℂ W) (hU : IsInvariant ρ U) (n : ℕ) (hw : U ≤ weightSpace ρ n) :
    IsHomogeneousRepresentation b (Module.finBasis ℂ U)
      (restrictedRepresentation ρ U hU) n := by
  apply polynomial_weight_isHomogeneous b (Module.finBasis ℂ U) _ n
    (invariant_subspace_isPolynomial b c ρ h U hU (Module.finBasis ℂ U))
  intro t
  ext w
  exact hw w.property t


/-- Every polynomial representation splits as the internal direct sum of its
homogeneous polynomial representations, with the scalar coefficients as projections. -/
theorem homogeneous_decomposition [FiniteDimensional ℂ W] {d m : ℕ}
    (b : Basis (Fin d) ℂ V) (c : Basis (Fin m) ℂ W)
    (ρ : LinearGroup V →* Module.End ℂ W) (hp : IsPolynomialRepresentation b c ρ) :
    Nonempty (HomogeneousDecomposition b ρ) := by
  obtain ⟨N, P, hz, h⟩ := scalar_polynomial_expansion b c ρ hp
  have hr := scalar_coefficients_range ρ N P hz h
  have hi : ∀ n, IsInvariant ρ (LinearMap.range (P n)) := by
    intro n
    rw [hr n]
    exact weightSpace_invariant ρ n
  have ho := scalar_coefficients_orthogonal ρ N P hz h
  have hs := scalar_coefficients_sum ρ N P h
  refine ⟨{ bound := N
            projection := P
            zero_above := hz
            orthogonal := ho
            sum_projection := hs
            commute := scalar_coefficients_commute ρ N P hz h
            scalar_expansion := h
            invariant := hi
            internal := projections_internal N P ho hs
            homogeneous := fun n => range_subrepresentation_homogeneous b c ρ hp
              (LinearMap.range (P n)) (hi n) n (le_of_eq (hr n))
            weight_characterization := fun _ => hr
            zero_dimension := ?_ }⟩
  intro hd
  subst d
  have hc : ∀ n, P n = if n = 0 then 1 else 0 := by
    apply coefficients_of_monomial N P 0 1 hz
    intro t
    rw [← h t, zero_dimension_group_trivial b (scalarElement V t), map_one]
    simp
  constructor
  · rw [hc 0, ite_eq_left rfl]
    exact LinearMap.range_eq_top.mpr (fun w => ⟨w, rfl⟩)
  · intro n hn
    simp [hc n, Nat.ne_of_gt hn]
end AdvancedFiniteGroupRepresentations
