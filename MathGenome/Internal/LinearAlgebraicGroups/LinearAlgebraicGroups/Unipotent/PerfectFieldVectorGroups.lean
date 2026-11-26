import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.PerfectFieldVectorGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.KilledByPVectorEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.AdditiveEquations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Coalgebra WithConv
open scoped TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Unipotent

open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.Specs.Unipotent
  LinearAlgebraicGroups.Specs.AdditiveEquations Polynomial

variable {k : Type u} [Field k]


section AdditiveRelations

variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable {A : Type u} [CommRing A] [Algebra k A]

/-- Evaluate a finite sum of Frobenius powers with the indicated coefficients. -/
private def frobeniusEval (p : ℕ) (x : A) : (ℕ →₀ k) →ₗ[k] A :=
  Finsupp.linearCombination k (fun n ↦ x ^ (p ^ n))

omit [CharP k p] in
private theorem frobeniusEval_add [CharP A p] (x y : A) (f : ℕ →₀ k) :
    frobeniusEval p (x + y) f = frobeniusEval p x f + frobeniusEval p y f := by
  simp only [frobeniusEval, Finsupp.linearCombination_apply, add_pow_expChar_pow, smul_add,
    Finsupp.sum_add]

/-- The coefficient operation for precomposition by `c X ^ (p ^ m)`. -/
private def rightMonomial (p m : ℕ) (c : k) : (ℕ →₀ k) →ₗ[k] (ℕ →₀ k) :=
  Finsupp.linearCombination k (fun n ↦ Finsupp.single (n + m) (c ^ (p ^ n)))

omit [Fact p.Prime] [CharP k p] in
private theorem rightMonomial_coeff (m : ℕ) (c : k) (f : ℕ →₀ k) (n : ℕ) :
    rightMonomial p m c f (n + m) = f n * c ^ (p ^ n) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, Finsupp.add_apply, hf, hg, add_mul]
  | single i a =>
    simp only [rightMonomial, Finsupp.linearCombination_single, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst i
      rfl
    · simp

omit [Fact p.Prime] [CharP k p] in
private theorem frobeniusEval_rightMonomial (m : ℕ) (c : k) (x : A) (f : ℕ →₀ k) :
    frobeniusEval (k := k) p x (rightMonomial p m c f) =
      frobeniusEval p (c • x ^ (p ^ m)) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single n a =>
    simp only [frobeniusEval, rightMonomial, Finsupp.linearCombination_single, map_smul,
      smul_pow, smul_smul, ← pow_mul]
    rw [← pow_add, add_comm m n]

private def relationDegree (f : ℕ →₀ k) : ℕ :=
  f.support.sup Nat.succ

private theorem relationDegree_pos {f : ℕ →₀ k} (hf : f ≠ 0) : 0 < relationDegree f := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hf
  exact (Nat.zero_lt_succ i).trans_le (Finset.le_sup (f := Nat.succ) hi)

private theorem relationDegree_top {f : ℕ →₀ k} (hf : f ≠ 0) :
    f (relationDegree f - 1) ≠ 0 := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup f.support (Finsupp.support_nonempty_iff.mpr hf) Nat.succ
  have : relationDegree f - 1 = i := by simp [relationDegree, he]
  exact this.symm ▸ Finsupp.mem_support_iff.mp hi

private theorem relationDegree_bound {f : ℕ →₀ k} {n : ℕ}
    (hn : relationDegree f ≤ n) : f n = 0 := by
  by_contra h
  have := Finset.le_sup (f := Nat.succ) (Finsupp.mem_support_iff.mpr h)
  change n + 1 ≤ relationDegree f at this
  omega

private theorem rightMonomial_cancel [PerfectRing k p] (f g : ℕ →₀ k)
    (hf : f ≠ 0) (hg : g ≠ 0) (hle : relationDegree f ≤ relationDegree g) :
    ∃ m c, relationDegree (g - rightMonomial p m c f) < relationDegree g := by
  let a := relationDegree f - 1
  let b := relationDegree g - 1
  let m := b - a
  have ha := relationDegree_top hf
  have hfa : relationDegree f = a + 1 := by
    have := relationDegree_pos hf
    dsimp [a]
    omega
  have hgb : relationDegree g = b + 1 := by
    have := relationDegree_pos hg
    dsimp [b]
    omega
  have hab : a + m = b := by omega
  obtain ⟨c, hc⟩ := (bijective_iterateFrobenius k p a).surjective (g b / f a)
  change c ^ (p ^ a) = g b / f a at hc
  refine ⟨m, c, ?_⟩
  rw [hgb, Nat.lt_succ_iff]
  apply Finset.sup_le
  intro n hn
  by_contra hnb
  have hbn : b ≤ n := by omega
  have hz : (g - rightMonomial p m c f) n = 0 := by
    rw [Finsupp.sub_apply]
    have hn' : n - m + m = n := by omega
    rw [← hn', rightMonomial_coeff, hn']
    rcases hbn.eq_or_lt with he | hlt
    · have : n - m = a := by omega
      rw [this, hc, ← he, mul_div_cancel₀ _ ha, sub_self]
    · have hg₀ : g n = 0 := relationDegree_bound (by omega)
      have hf₀ : f (n - m) = 0 := relationDegree_bound (by omega)
      simp [hg₀, hf₀]
  exact (Finsupp.mem_support_iff.mp hn) hz

end AdditiveRelations


open private hopfMap_ker from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private connectedPrimeSpectrum_of_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private isReduced_of_smooth_algebra from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

section PrimitiveCoordinates

variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable {A : Type u} [CommRing A] [HopfAlgebra k A]

private theorem primitive_frobeniusPower {x : A} (hx : Bialgebra.IsPrimitiveElem k x)
    (n : ℕ) : Bialgebra.IsPrimitiveElem k (x ^ (p ^ n)) := by
  have : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  have : CharP (A ⊗[k] A) p := charP_of_injective_algebraMap' k p
  apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr
  change Bialgebra.comulAlgHom k A (x ^ (p ^ n)) = _
  rw [map_pow]
  change comul x ^ (p ^ n) = _
  rw [hx.comul_eq_tmul_add_tmul, add_pow_char_pow]
  simp [Algebra.TensorProduct.tmul_pow]

/-- An integral primitive element lives in a finite reduced connected subalgebra. -/
private theorem primitive_of_algebraic [IsReduced A] [ConnectedSpace (PrimeSpectrum A)]
    {x : A} (hx : Bialgebra.IsPrimitiveElem k x) (ha : IsIntegral k x) : x = 0 := by
  let B := Algebra.adjoin k ({x} : Set A)
  let f : B →ₐ[k] k := (Bialgebra.counitAlgHom k A).comp B.val
  let z : B := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  let : Module.Finite k B := Algebra.finite_adjoin_simple_of_isIntegral ha
  let : IsArtinianRing B := IsArtinianRing.of_finite k B
  have hfB : Function.Injective B.val := Subtype.val_injective
  let : IsReduced B := isReduced_of_injective B.val hfB
  let : ConnectedSpace (PrimeSpectrum B) :=
    connectedPrimeSpectrum_of_injective B.val.toRingHom hfB
  have hsub : Subsingleton (PrimeSpectrum B) :=
    subsingleton_of_preconnected_totallyDisconnected
  let q : PrimeSpectrum B := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  have hz : z ∈ nilradical B := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro I hI
    have hi : (⟨I, hI⟩ : PrimeSpectrum B) = q := hsub.elim _ _
    change z ∈ (⟨I, hI⟩ : PrimeSpectrum B).asIdeal
    rw [hi]
    exact hx.counit_eq_zero
  change z ∈ (⊥ : Ideal B).radical at hz
  rw [Ideal.radical_bot_of_isReduced, Ideal.mem_bot] at hz
  exact congrArg Subtype.val hz

omit [CharP k p] in
private theorem integral_of_frobeniusRelation {x : A} (f : ℕ →₀ k) (hf : f ≠ 0)
    (he : frobeniusEval p x f = 0) : IsIntegral k x := by
  let g : k[X] := frobeniusEval p (X : k[X]) f
  have hcoeff (n : ℕ) : g.coeff (p ^ n) = f n := by
    change (frobeniusEval p (X : k[X]) f).coeff (p ^ n) = _
    clear_value g
    clear g hf he
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [map_add, coeff_add, Finsupp.add_apply, hf, hg]
    | single i a =>
      have hpi : Function.Injective (fun n : ℕ ↦ p ^ n) :=
        Nat.pow_right_injective (Fact.out : p.Prime).two_le
      simp [frobeniusEval, Finsupp.linearCombination_single, coeff_smul, coeff_X_pow,
        Finsupp.single_apply, hpi.eq_iff, eq_comm]
  have hg : g ≠ 0 := by
    intro hg
    apply hf
    ext n
    simp [← hcoeff n, hg]
  have hge : aeval x g = 0 := by
    unfold g
    change (aeval x).toLinearMap (frobeniusEval p (X : k[X]) f) = 0
    rw [frobeniusEval, Finsupp.apply_linearCombination k (aeval x).toLinearMap]
    simpa [frobeniusEval, Function.comp_def] using he
  refine ⟨C g.leadingCoeff⁻¹ * g, ?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hg)]
  · change aeval x (C g.leadingCoeff⁻¹ * g) = 0
    rw [map_mul, hge, mul_zero]

omit [Fact p.Prime] [CharP k p] in
private theorem sum_frobeniusEval_curry {ι : Type u} [Fintype ι]
    (x : ι → A) (c : (ι × ℕ) →₀ k) :
    (∑ i, frobeniusEval p (x i) (c.curry i)) =
      c.sum (fun ij a ↦ a • x ij.1 ^ (p ^ ij.2)) := by
  rw [← Finsupp.sum_curry_index c (fun i n a ↦ a • x i ^ (p ^ n))]
  exact (Finsupp.sum_fintype _ _ (by intro i; simp)).symm

omit [Fact p.Prime] [CharP k p] in
private theorem relationOfAdditiveEquation {ι : Type u} [Fintype ι]
    (x : ι → A) {f : MvPolynomial ι k} (hf : f ≠ 0)
    (had : IsAdditivePolynomial p f) (hz : MvPolynomial.aeval x f = 0) :
    ∃ a : ι → ℕ →₀ k, (∃ i, a i ≠ 0) ∧ (∑ i, frobeniusEval p (x i) (a i)) = 0 := by
  obtain ⟨c, rfl⟩ := had
  refine ⟨c.curry, ?_, ?_⟩
  · by_contra h
    have hc : c.curry = 0 := Finsupp.ext (fun i ↦ not_ne_iff.mp fun hi ↦ h ⟨i, hi⟩)
    have hc0 : c = 0 := Finsupp.curryEquiv.injective hc
    exact hf (by rw [hc0, Finsupp.sum_zero_index])
  · rw [sum_frobeniusEval_curry]
    simpa only [Finsupp.sum, map_sum, map_smul, map_pow, MvPolynomial.aeval_X] using hz

private theorem adjoin_range_update {ι : Type u} [DecidableEq ι]
    (x : ι → A) {i j : ι} (hij : i ≠ j) (c : k) (e : ℕ) :
    Algebra.adjoin k (Set.range (Function.update x i (x i + c • x j ^ e))) =
      Algebra.adjoin k (Set.range x) := by
  let y := Function.update x i (x i + c • x j ^ e)
  apply le_antisymm <;> apply Algebra.adjoin_le <;> rintro _ ⟨l, rfl⟩
  · have mem (l : ι) : x l ∈ Algebra.adjoin k (Set.range x) := Algebra.subset_adjoin ⟨l, rfl⟩
    by_cases h : l = i
    · subst l
      rw [Function.update_self]
      exact add_mem (mem i) (Subalgebra.smul_mem _ (pow_mem (mem j) e) c)
    · rw [Function.update_of_ne h]
      exact mem l
  · have mem (l : ι) : y l ∈ Algebra.adjoin k (Set.range y) := Algebra.subset_adjoin ⟨l, rfl⟩
    by_cases h : l = i
    · subst l
      have hi : y i = x i + c • x j ^ e := Function.update_self ..
      have hj : y j = x j := Function.update_of_ne hij.symm ..
      have hi' := mem i
      have hj' := mem j
      rw [hi] at hi'
      rw [hj] at hj'
      simpa using sub_mem hi' (Subalgebra.smul_mem _ (pow_mem hj' e) c)
    · have hm := mem l
      have hy : y l = x l := Function.update_of_ne h ..
      exact hy ▸ hm

/-- Elementary additive changes of coordinates reduce a nonzero additive relation
to one involving a single primitive generator. -/
private theorem exists_algebraic_coordinate [PerfectRing k p] [CharP A p]
    {ι : Type u} [Fintype ι] (x : ι → A)
    (hp : ∀ i, Bialgebra.IsPrimitiveElem k (x i))
    (f : ι → ℕ →₀ k) (hf : ∃ i, f i ≠ 0)
    (he : (∑ i, frobeniusEval p (x i) (f i)) = 0) :
    ∃ (y : ι → A) (i : ι), (∀ j, Bialgebra.IsPrimitiveElem k (y j)) ∧
      Algebra.adjoin k (Set.range y) = Algebra.adjoin k (Set.range x) ∧ IsIntegral k (y i) := by
  classical
  let weight (f : ι → ℕ →₀ k) := ∑ i, relationDegree (f i)
  suffices key : ∀ n (x : ι → A), (∀ i, Bialgebra.IsPrimitiveElem k (x i)) →
      ∀ f : ι → ℕ →₀ k, (∃ i, f i ≠ 0) → (∑ i, frobeniusEval p (x i) (f i)) = 0 →
      weight f = n → ∃ (y : ι → A) (i : ι), (∀ j, Bialgebra.IsPrimitiveElem k (y j)) ∧
        Algebra.adjoin k (Set.range y) = Algebra.adjoin k (Set.range x) ∧ IsIntegral k (y i) by
    exact key _ x hp f hf he rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hp f hf he hw
    let s := Finset.univ.filter fun i ↦ f i ≠ 0
    obtain ⟨l, hl⟩ := hf
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s (fun i ↦ relationDegree (f i))
      ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
    have hfi := (Finset.mem_filter.mp hi).2
    by_cases hother : ∃ j, j ≠ i ∧ f j ≠ 0
    · obtain ⟨j, hji, hfj⟩ := hother
      obtain ⟨m, c, hr⟩ := rightMonomial_cancel (p := p) (f i) (f j) hfi hfj
        (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfj⟩))
      let t := c • x j ^ (p ^ m)
      let y := Function.update x i (x i + t)
      let g := Function.update f j (f j - rightMonomial p m c (f i))
      have hpy (l : ι) : Bialgebra.IsPrimitiveElem k (y l) := by
        by_cases h : l = i
        · subst l
          simp only [y, Function.update_self]
          exact (hp i).add ((primitive_frobeniusPower (p := p) (hp j) m).smul c)
        · simpa only [y, Function.update_of_ne h] using hp l
      have hg : ∃ l, g l ≠ 0 := ⟨i, by simpa [g, Function.update_of_ne hji.symm] using hfi⟩
      have hgy (l : ι) : frobeniusEval p (y l) (g l) =
          frobeniusEval p (x l) (f l) +
            (if l = i then frobeniusEval p t (f i) else 0) -
            (if l = j then frobeniusEval p t (f i) else 0) := by
        by_cases hi' : l = i
        · subst l
          simp [y, g, hji.symm, frobeniusEval_add]
        · by_cases hj' : l = j
          · subst l
            simp [y, g, hji, t, frobeniusEval_rightMonomial]
          · simp [y, g, hi', hj']
      have hey : (∑ l, frobeniusEval p (y l) (g l)) = 0 := by
        simp [hgy, Finset.sum_sub_distrib, Finset.sum_add_distrib, he]
      have hwg : weight g < n := by
        rw [← hw]
        apply Finset.sum_lt_sum
        · intro l _
          by_cases h : l = j
          · subst l
            simpa only [g, Function.update_self] using hr.le
          · simp [g, Function.update_of_ne h]
        · exact ⟨j, Finset.mem_univ _, by simpa [g] using hr⟩
      obtain ⟨z, l, hpz, hz, hl⟩ := ih _ hwg y hpy g hg hey rfl
      exact ⟨z, l, hpz, hz.trans (adjoin_range_update x hji.symm c (p ^ m)), hl⟩
    · refine ⟨x, i, hp, rfl, integral_of_frobeniusRelation (p := p) (f i) hfi ?_⟩
      rw [← he]
      symm
      apply Finset.sum_eq_single i
      · intro j _ hj
        have : f j = 0 := not_ne_iff.mp fun h ↦ hother ⟨j, hj, h⟩
        simp [this]
      · simp

end PrimitiveCoordinates


private def primitivePresentation {ι A : Type u} [CommRing A] [HopfAlgebra k A]
    (h : StandardGroups.HopfOperations k (MvPolynomial ι k))
    (hδ : ∀ i, h.delta (MvPolynomial.X i) =
      MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i)
    (hε : ∀ i, h.epsilon (MvPolynomial.X i) = 0) (x : ι → A)
    (hp : ∀ i, Bialgebra.IsPrimitiveElem k (x i)) :
    @BialgHom k (MvPolynomial ι k) A _ _ _ _ _ h.hopf.toCoalgebraStruct _ := by
  letI := h.hopf.toBialgebra
  let f : MvPolynomial ι k →ₐ[k] A := MvPolynomial.aeval x
  refine BialgHom.ofAlgHom f (MvPolynomial.algHom_ext fun i ↦ ?_)
    (MvPolynomial.algHom_ext fun i ↦ ?_)
  · change counit (R := k) (f (MvPolynomial.X i)) = h.epsilon (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X, hε, (hp i).counit_eq_zero]
  · change Algebra.TensorProduct.map f f (h.delta (MvPolynomial.X i)) =
      comul (f (MvPolynomial.X i))
    rw [hδ, MvPolynomial.aeval_X, (hp i).comul_eq_tmul_add_tmul]
    simp [f, add_comm]

private theorem primitiveCoordinates {ι : Type u}
    (h : StandardGroups.HopfOperations k (MvPolynomial ι k))
    (hδ : ∀ i, h.delta (MvPolynomial.X i) =
      MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i) :
    HasPrimitiveCoordinates h := by
  let := h.hopf.toBialgebra
  intro i
  apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr
  change h.delta (MvPolynomial.X i) = _
  rw [hδ, add_comm]

private def reindexAdditivePoints {ι κ : Type u} (e : ι ≃ κ) :
    StandardGroups.additivePowerPoints k ι ≅ StandardGroups.additivePowerPoints k κ :=
  NatIso.ofComponents (fun R ↦
    (show (ι → Multiplicative R) ≃* (κ → Multiplicative R) from
      { toFun := fun a j ↦ a (e.symm j)
        invFun := fun b i ↦ b (e i)
        left_inv := fun a ↦ funext fun i ↦ by simp
        right_inv := fun b ↦ funext fun j ↦ by simp
        map_mul' := fun _ _ ↦ rfl }).toGrpIso)
    (by intro R S a; apply GrpCat.ext; intro x; rfl)

private theorem remove_zero_coordinate {A ι : Type u} [CommRing A] [Algebra k A]
    (x : ι → A) {i : ι} (hi : x i = 0) :
    Algebra.adjoin k (Set.range fun j : {j // j ≠ i} ↦ x j.val) =
      Algebra.adjoin k (Set.range x) := by
  classical
  apply le_antisymm
  · exact Algebra.adjoin_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.val, rfl⟩)
  · apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    by_cases h : j = i
    · rw [h, hi]
      exact zero_mem _
    · exact Algebra.subset_adjoin ⟨⟨j, h⟩, rfl⟩

/-- A reduced connected Hopf algebra generated by finitely many primitive elements
is a polynomial Hopf algebra over a perfect field of positive characteristic. -/
private theorem vector_of_primitive_generators {p : ℕ} [Fact p.Prime] [CharP k p]
    [PerfectRing k p] (A : HopfAlgebraCategory k)
    [_root_.IsReduced A] [ConnectedSpace (PrimeSpectrum A)]
    {ι : Type u} [Fintype ι] (x : ι → A) (hp : ∀ i, Bialgebra.IsPrimitiveElem k (x i))
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    ∃ d, Nonempty ((groupPointsFunctor k).obj (specGroup A) ≅
      StandardGroups.additivePowerPoints k (Index.{u} d)) := by
  classical
  have : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  have : CharP A p := charP_of_injective_algebraMap' k p
  suffices key : ∀ n (ι : Type u) [Fintype ι], Fintype.card ι = n →
      ∀ x : ι → A, (∀ i, Bialgebra.IsPrimitiveElem k (x i)) →
        Algebra.adjoin k (Set.range x) = ⊤ →
        ∃ d, Nonempty ((groupPointsFunctor k).obj (specGroup A) ≅
          StandardGroups.additivePowerPoints k (Index.{u} d)) by
    exact key _ ι rfl x hp hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ι _ hcard x hp hx
    obtain ⟨h, hδ, hε, _, _, _, e, _⟩ := StandardGroups.additivePowerSpecification k ι
    let := h.hopf
    let B := CommHopfAlgCat.of k (MvPolynomial ι k)
    let : Bialgebra k B := B.hopfAlgebra.toBialgebra
    let : Coalgebra k B := B.hopfAlgebra.toCoalgebra
    let : CoalgebraStruct k B := B.hopfAlgebra.toCoalgebraStruct
    have hX := primitiveCoordinates h hδ
    let f : B ⟶ A := CommHopfAlgCat.ofHom (primitivePresentation h hδ hε x hp)
    have hsur : Function.Surjective f.hom := by
      change Function.Surjective (MvPolynomial.aeval x)
      rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hx]
    by_cases hInj : Function.Injective f.hom
    · let u : B ≅ A := CommHopfAlgCat.isoMk (BialgEquiv.ofBijective (R := k) (A := B) (B := A) f.hom ⟨hInj, hsur⟩)
      let v := (hopfSpec (CommRingCat.of k)).mapIso u.op
      exact ⟨Fintype.card ι, ⟨(groupPointsFunctor k).mapIso v ≪≫ e ≪≫
        reindexAdditivePoints ((Fintype.equivFin ι).trans Equiv.ulift.symm)⟩⟩
    · let I := RingHom.ker f.hom.toAlgHom
      have hI : I ≠ ⊥ := fun hi ↦ hInj
        ((RingHom.injective_iff_ker_eq_bot f.hom.toAlgHom).mpr hi)
      let : I.IsHopfIdeal k := @hopfMap_ker k _ B A f hsur
      obtain ⟨S, hs, hadd⟩ := AdditiveEquations.hopfIdealAdditiveGenerators k ι p h hX I
      have hnonzero : ∃ r ∈ S, r ≠ 0 := by
        by_contra hzero
        apply hI
        rw [hs]
        apply le_antisymm (Ideal.span_le.mpr ?_) bot_le
        intro r hr
        exact not_ne_iff.mp (fun h ↦ hzero ⟨r, hr, h⟩)
      obtain ⟨r, hr, hr0⟩ := hnonzero
      have hrI : r ∈ I := hs.symm ▸ Ideal.subset_span (by exact hr)
      have hrx : MvPolynomial.aeval x r = 0 := hrI
      obtain ⟨a, ha, hae⟩ := relationOfAdditiveEquation x hr0 (hadd r hr).2 hrx
      obtain ⟨y, i, hpy, hy, hyi⟩ := exists_algebraic_coordinate x hp a ha hae
      have hz : y i = 0 := primitive_of_algebraic (hpy i) hyi
      have hlt : Fintype.card {j : ι // j ≠ i} < n :=
        hcard ▸ Fintype.card_subtype_lt (x := i) (not_not_intro rfl)
      exact ih _ hlt _ rfl (fun j ↦ y j.val) (fun j ↦ hpy j.val)
        ((remove_zero_coordinate y hz).trans (hy.trans hx))

private def groupIsoOfPoints {G H : Specs.GroupScheme k}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) : G ≅ H := by
  let f := ((groupHomComparison k G H hG).surjective e.hom).choose
  have hf : (groupPointsFunctor k).map f = e.hom :=
    ((groupHomComparison k G H hG).surjective e.hom).choose_spec
  let g := ((groupHomComparison k H G hH).surjective e.inv).choose
  have hg : (groupPointsFunctor k).map g = e.inv :=
    ((groupHomComparison k H G hH).surjective e.inv).choose_spec
  refine ⟨f, g, ?_, ?_⟩
  · apply (groupHomComparison k G G hG).injective
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G)
    rw [Functor.map_comp, hf, hg, e.hom_inv_id]
    exact ((groupPointsFunctor k).map_id G).symm
  · apply (groupHomComparison k H H hH).injective
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H)
    rw [Functor.map_comp, hg, hf, e.inv_hom_id]
    exact ((groupPointsFunctor k).map_id H).symm

set_option maxHeartbeats 800000 in
theorem perfectFieldVectorGroups : PerfectFieldVectorGroups.{u} := by
  intro k _ _ p _ _ H _ _ hu hc hp
  obtain ⟨d, V, ⟨eV⟩, i, hi⟩ := killedByPVectorEmbedding p H hu hc hp
  obtain ⟨h, hδ, _, _, _, _, eW, _⟩ :=
    StandardGroups.additivePowerSpecification k (Index.{u} d)
  let := h.hopf
  let B := CommHopfAlgCat.of k (MvPolynomial (Index.{u} d) k)
  let : Bialgebra k B := B.hopfAlgebra.toBialgebra
  let : Coalgebra k B := B.hopfAlgebra.toCoalgebra
  let : CoalgebraStruct k B := B.hopfAlgebra.toCoalgebraStruct
  let W := Specs.StandardGroups.spectrum k (MvPolynomial (Index.{u} d) k)
  let j : V.val ≅ W.val := groupIsoOfPoints V.property.1 W.property.1 (eV ≪≫ eW.symm)
  have hj : IsIso j.hom.hom.hom.left := by
    change IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map j.hom)
    infer_instance
  have hi' : IsClosedImmersion (i ≫ j.hom).hom.hom.left := by
    change IsClosedImmersion (i.hom.hom.left ≫ j.hom.hom.hom.left)
    let := hi
    infer_instance
  obtain ⟨I, ⟨hI, e, _⟩, _⟩ :=
    (closedSubgroupClassification k B H.val (i ≫ j.hom)).mp hi'
  let := hI
  let A := hopfQuotient B I
  let q := hopfQuotientMap B I
  have he : IsIso e.hom.hom.hom.left := by
    change IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map e.hom)
    infer_instance
  have hs : Smooth (specGroup A).X.hom := by
    have : IsIso e.inv.hom.hom.left := by
      change IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map e.inv)
      infer_instance
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  let : Algebra.Smooth k A := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hs
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)
  have : _root_.IsReduced A := isReduced_of_smooth_algebra k A
  have : ConnectedSpace (PrimeSpectrum A) :=
    e.hom.hom.hom.left.homeomorph.connectedSpace_iff.mp
      (inferInstance : ConnectedSpace H.val.X.left)
  let x : Index.{u} d → A := fun i ↦ q.hom (MvPolynomial.X i)
  have hpx (i : Index.{u} d) : Bialgebra.IsPrimitiveElem k (x i) := by
    exact ((primitiveCoordinates h hδ) i).map q.hom
  have hxa : Algebra.adjoin k (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    have hq : MvPolynomial.aeval x = q.hom.toAlgHom :=
      MvPolynomial.algHom_ext fun i ↦ MvPolynomial.aeval_X _ i
    rw [hq]
    exact Ideal.Quotient.mk_surjective
  obtain ⟨n, ⟨iso⟩⟩ := vector_of_primitive_generators (p := p) A x hpx hxa
  let T := StandardGroups.additivePowerGroup k (Index.{u} n)
  let t := StandardGroups.additivePowerGroupPointsIso k (Index.{u} n)
  let u := (groupPointsFunctor k).mapIso e ≪≫ iso ≪≫ t.symm
  exact ⟨n, T, ⟨groupIsoOfPoints H.property.1 T.property.1 u⟩, ⟨t⟩⟩

end LinearAlgebraicGroups.Unipotent
