import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.LinearGradedNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.PolynomialDimension
import MathGenome.Internal.AlgebraCore.P103.Ch04.IntegralDimension
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

namespace P103.Ch06.LinearGradedNormalization
open P103.Graded MvPolynomial
open P103.Specs.Ch06.LinearGradedNormalization
universe u v

variable {k : Type u} {C : Type v} [Field k] [CommRing C] [Algebra k C]

lemma scalar_mem_zero (G : NonnegativeGrading C) (hzero : Connected k G) (a : k) :
    algebraMap k C a ∈ G.piece 0 := (hzero _).mpr ⟨a, rfl⟩

/-- Evaluation of degree-one elements respects every homogeneous degree. -/
lemma aeval_mem_piece (G : NonnegativeGrading C) (hzero : Connected k G)
    {ι : Type*} (x : ι → C) (hx : ∀ i, x i ∈ G.piece 1)
    {n : ℕ} {f : MvPolynomial ι k} (hf : f.IsHomogeneous n) :
    aeval x f ∈ G.piece (n : ℤ) := by
  classical
  rw [← f.support_sum_monomial_coeff, map_sum]
  apply (G.piece (n : ℤ)).sum_mem
  intro d hd
  rw [aeval_monomial]
  have hdeg := hf (mem_support_iff.mp hd)
  have hprod := SetLike.prod_pow_mem_graded G.piece (fun _ : ι => (1 : ℤ)) x
    (F := d.support) (fun i => d i) (fun i _ => hx i)
  have heq : (∑ i ∈ d.support, (d i : ℤ)) = (n : ℤ) := by
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finsupp.sum] at hdeg
    exact_mod_cast hdeg
  simp only [nsmul_eq_mul, mul_one] at hprod
  rw [heq] at hprod
  simpa only [zero_add, Finsupp.prod] using
    SetLike.mul_mem_graded (scalar_mem_zero G hzero (f.coeff d)) hprod

/-- Standardness over the actual degree-zero ring is standardness over k. -/
lemma standard_generators (G : NonnegativeGrading C) (hzero : Connected k G)
    (hstd : Specs.P103.Graded.standardValue G) :
    ∃ s : Finset C, (∀ a ∈ s, a ∈ G.piece 1) ∧
      Algebra.adjoin k (s : Set C) = ⊤ := by
  obtain ⟨s, hs, hgen⟩ := hstd
  refine ⟨s, hs, ?_⟩
  apply top_unique
  intro c hc
  clear hc
  have hc : c ∈ Algebra.adjoin (Base G) (s : Set C) := by rw [hgen]; trivial
  induction hc using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap a =>
    obtain ⟨r, hr⟩ := (hzero (a : C)).mp a.2
    change (a : C) ∈ Algebra.adjoin k (s : Set C)
    rw [← hr]
    exact (Algebra.adjoin k (s : Set C)).algebraMap_mem r
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

lemma finiteType_of_standard (G : NonnegativeGrading C) (hzero : Connected k G)
    (hstd : Specs.P103.Graded.standardValue G) : Algebra.FiniteType k C := by
  obtain ⟨s, _, hs⟩ := standard_generators G hzero hstd
  exact ⟨s, hs⟩

/-- Homogeneous components of a relation are still relations. -/
lemma aeval_homogeneousComponent_eq_zero (G : NonnegativeGrading C)
    (hzero : Connected k G) {ι : Type*} (x : ι → C)
    (hx : ∀ i, x i ∈ G.piece 1) {f : MvPolynomial ι k}
    (hf : aeval x f = 0) (n : ℕ) : aeval x (homogeneousComponent n f) = 0 := by
  classical
  by_cases hn : n < f.totalDegree + 1
  · let π : C →+ C :=
      { toFun := fun c => (DirectSum.decompose G.piece c (n : ℤ) : C)
        map_zero' := by simp
        map_add' := by
          intro a b
          rw [DirectSum.decompose_add]
          rfl }
    have hπ (i : ℕ) : π (aeval x (homogeneousComponent i f)) =
        if i = n then aeval x (homogeneousComponent i f) else 0 := by
      have hm := aeval_mem_piece G hzero x hx (homogeneousComponent_isHomogeneous i f)
      dsimp [π]
      split_ifs with hi
      · subst i
        exact DirectSum.decompose_of_mem_same G.piece hm
      · exact DirectSum.decompose_of_mem_ne G.piece hm (by exact_mod_cast hi)
    have heq := congrArg (fun p : MvPolynomial ι k => π (aeval x p))
      (sum_homogeneousComponent f)
    simp only [map_sum, hπ, hf, map_zero] at heq
    simpa only [Finset.sum_ite_eq', Finset.mem_range.mpr hn, ite_true] using heq
  · rw [homogeneousComponent_eq_zero n (φ := f) (by omega), map_zero]

lemma exists_homogeneous_relation (G : NonnegativeGrading C)
    (hzero : Connected k G) {ι : Type*} (x : ι → C)
    (hx : ∀ i, x i ∈ G.piece 1) (hdep : ¬ AlgebraicIndependent k x) :
    ∃ (N : ℕ) (f : MvPolynomial ι k), f ≠ 0 ∧ f.IsHomogeneous N ∧ aeval x f = 0 := by
  classical
  rw [algebraicIndependent_iff_injective_aeval] at hdep
  have hker : RingHom.ker (aeval x) ≠ ⊥ := fun h =>
    hdep ((RingHom.injective_iff_ker_eq_bot _).mpr h)
  obtain ⟨f, hf, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hrel : aeval x f = 0 := hf
  obtain ⟨N, hN⟩ : ∃ N, homogeneousComponent N f ≠ 0 := by
    by_contra! h
    apply hne
    rw [← sum_homogeneousComponent f]
    exact Finset.sum_eq_zero (fun i _ => h i)
  exact ⟨N, homogeneousComponent N f, hN, homogeneousComponent_isHomogeneous N f,
    aeval_homogeneousComponent_eq_zero G hzero x hx hrel N⟩

/-- Eliminate one integral generator while retaining module finiteness. -/
lemma finite_drop_of_integral {n : ℕ} (z : Fin (n + 1) → C)
    (hfin : Module.Finite (Algebra.adjoin k (Set.range z)) C)
    (hint : IsIntegral (Algebra.adjoin k (Set.range (z ∘ Fin.succ))) (z 0)) :
    Module.Finite (Algebra.adjoin k (Set.range (z ∘ Fin.succ))) C := by
  classical
  let A := Algebra.adjoin k (Set.range z)
  let B := Algebra.adjoin k (Set.range (z ∘ Fin.succ))
  have hBA : B ≤ A := Algebra.adjoin_mono (by
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, rfl⟩)
  let _ : Algebra B A := (Subalgebra.inclusion hBA).toRingHom.toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let f : A →ₐ[B] C := IsScalarTower.toAlgHom B A C
  have hclosure : A ≤ (integralClosure B C).restrictScalars k := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => exact hint
    | succ i =>
      have hm : z i.succ ∈ B := Algebra.subset_adjoin ⟨i, rfl⟩
      exact isIntegral_algebraMap (R := B) (A := C) (x := ⟨z i.succ, hm⟩)
  have : Algebra.IsIntegral B A := ⟨fun a =>
    (isIntegral_algHom_iff f Subtype.val_injective).mp (hclosure a.2)⟩
  have : Module.Finite A C := hfin
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.trans A
  have : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite (Set.finite_range z)
  have : Algebra.FiniteType k C := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k A)
    (inferInstance : Algebra.FiniteType A C)
  have : Algebra.FiniteType B C := Algebra.FiniteType.of_restrictScalars_finiteType k B C
  exact Algebra.IsIntegral.finite

/-- A relation monic up to a unit makes the first generator integral over
all the others. -/
lemma first_integral_of_relation {n : ℕ} (z : Fin (n + 1) → C)
    (f : MvPolynomial (Fin (n + 1)) k) (hf : aeval z f = 0)
    (hu : IsUnit (finSuccEquiv k n f).leadingCoeff) :
    IsIntegral (Algebra.adjoin k (Set.range (z ∘ Fin.succ))) (z 0) := by
  classical
  let B := Algebra.adjoin k (Set.range (z ∘ Fin.succ))
  let b : MvPolynomial (Fin n) k →ₐ[k] B :=
    aeval (fun i => ⟨z i.succ, Algebra.subset_adjoin ⟨i, rfl⟩⟩)
  let q := finSuccEquiv k n f
  let q' := (hu.unit⁻¹ : (MvPolynomial (Fin n) k)ˣ) • q
  have hmon : q'.Monic := Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu
  refine ⟨q'.map b.toRingHom, hmon.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hb : (algebraMap B C).comp b.toRingHom = (aeval (z ∘ Fin.succ)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [b, B]
    · intro i
      simp [b]
  rw [hb]
  change Polynomial.eval₂ (aeval (z ∘ Fin.succ)).toRingHom (z 0) (hu.unit⁻¹ • q) = 0
  rw [Units.smul_def, Polynomial.eval₂_smul]
  suffices hq : Polynomial.eval₂ (aeval (z ∘ Fin.succ)).toRingHom (z 0) q = 0 by
    rw [hq, mul_zero]
  have heval : (Polynomial.eval₂RingHom (aeval (z ∘ Fin.succ)).toRingHom (z 0)).comp
      (finSuccEquiv k n).toRingHom = (aeval z).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [finSuccEquiv_apply]
    · intro i
      cases i using Fin.cases <;> simp [finSuccEquiv_apply]
  exact (RingHom.congr_fun heval f).trans hf

/-- A homogeneous polynomial nonzero on the first coordinate axis has scalar
unit leading coefficient when viewed as a polynomial in the first variable. -/
lemma homogeneous_axis_leadingCoeff {n N : ℕ}
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous N)
    (hv : eval (Fin.cons 1 0) f ≠ 0) :
    IsUnit (finSuccEquiv k n f).leadingCoeff := by
  classical
  let q := finSuccEquiv k n f
  have hbound : q.natDegree < N + 1 := by
    have := hf.totalDegree_le
    have := degreeOf_le_totalDegree f (0 : Fin (n + 1))
    rw [← natDegree_finSuccEquiv] at this
    dsimp [q]
    omega
  have hc : q.coeff N = MvPolynomial.C (constantCoeff (q.coeff N)) := by
    have h := hf.finSuccEquiv_coeff_isHomogeneous N 0 (by omega)
    apply totalDegree_eq_zero_iff_eq_C.mp
    exact (totalDegree_zero_iff_isHomogeneous (Fin n)).mpr h
  have hlow : ∀ i ∈ Finset.range N, constantCoeff (q.coeff i) = 0 := by
    intro i hi
    have hi : i < N := Finset.mem_range.mp hi
    apply (hf.finSuccEquiv_coeff_isHomogeneous i (N - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    omega
  have heval : eval (Fin.cons 1 0) f = constantCoeff (q.coeff N) := by
    rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map,
      Polynomial.eval_eq_sum_range' hbound]
    simp only [eval_zero, one_pow, mul_one, Finset.sum_range_succ, map_add, map_sum,
      Finset.sum_eq_zero hlow, zero_add]
  have hcoeff : q.coeff N ≠ 0 := by
    intro h
    apply hv
    rw [heval, h, map_zero]
  have hdeg : q.natDegree = N := by
    exact le_antisymm (by omega) (Polynomial.le_natDegree_of_ne_zero hcoeff)
  rw [Polynomial.leadingCoeff, hdeg, hc]
  exact (heval ▸ hv).isUnit.map MvPolynomial.C

noncomputable def linearSubstitution {n : ℕ} (v : Fin (n + 1) → k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval (Fin.cons (MvPolynomial.C (v 0) * X 0)
    (fun i => X i.succ + MvPolynomial.C (v i.succ) * X 0))

noncomputable def inverseLinearSubstitution {n : ℕ} (v : Fin (n + 1) → k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval (Fin.cons (MvPolynomial.C (v 0)⁻¹ * X 0)
    (fun i => X i.succ - MvPolynomial.C (v i.succ / v 0) * X 0))

lemma linearSubstitution_comp_inverse {n : ℕ} (v : Fin (n + 1) → k) (hv : v 0 ≠ 0) :
    (linearSubstitution v).comp (inverseLinearSubstitution v) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [linearSubstitution, inverseLinearSubstitution, MvPolynomial.algebraMap_eq,
      ← mul_assoc, ← MvPolynomial.C_mul, hv]
  | succ i =>
    simp only [AlgHom.comp_apply, inverseLinearSubstitution, linearSubstitution,
      aeval_X, Fin.cons_succ, Fin.cons_zero, map_sub, map_mul, aeval_C,
      AlgHom.id_apply, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← MvPolynomial.C_mul, div_mul_cancel₀ _ hv]
    ring

lemma inverseLinearSubstitution_comp {n : ℕ} (v : Fin (n + 1) → k) (hv : v 0 ≠ 0) :
    (inverseLinearSubstitution v).comp (linearSubstitution v) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [linearSubstitution, inverseLinearSubstitution, MvPolynomial.algebraMap_eq,
      ← mul_assoc, ← MvPolynomial.C_mul, hv]
  | succ i =>
    simp only [AlgHom.comp_apply, inverseLinearSubstitution, linearSubstitution,
      aeval_X, Fin.cons_succ, Fin.cons_zero, map_add, map_mul, aeval_C,
      AlgHom.id_apply, MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    simp only [div_eq_mul_inv]
    ring

noncomputable def linearChange {n : ℕ} (v : Fin (n + 1) → k) (hv : v 0 ≠ 0) :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  AlgEquiv.ofAlgHom (linearSubstitution v) (inverseLinearSubstitution v)
    (linearSubstitution_comp_inverse v hv) (inverseLinearSubstitution_comp v hv)

lemma linearSubstitution_homogeneous {n N : ℕ} (v : Fin (n + 1) → k)
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous N) :
    (linearSubstitution v f).IsHomogeneous N := by
  simpa only [one_mul, linearSubstitution] using hf.aeval (n := 1)
    (Fin.cons (MvPolynomial.C (v 0) * X 0)
      (fun i => X i.succ + MvPolynomial.C (v i.succ) * X 0)) (fun i => by
        cases i using Fin.cases with
        | zero => exact isHomogeneous_C_mul_X _ _
        | succ i => exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _))

lemma eval_axis_linearSubstitution {n : ℕ} (v : Fin (n + 1) → k)
    (f : MvPolynomial (Fin (n + 1)) k) :
    eval (Fin.cons 1 0) (linearSubstitution v f) = eval v f := by
  have h : (eval (Fin.cons 1 0)).comp (linearSubstitution v).toRingHom = eval v := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [linearSubstitution]
    · intro i
      cases i using Fin.cases <;> simp [linearSubstitution]
  exact RingHom.congr_fun h f

lemma exists_linear_monic_change [Infinite k] {n N : ℕ}
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous N) (hne : f ≠ 0) :
    ∃ (v : Fin (n + 1) → k) (hv : v 0 ≠ 0),
      IsUnit (finSuccEquiv k n (linearChange v hv f)).leadingCoeff := by
  have hp : (f * X 0).IsHomogeneous (N + 1) := hf.mul (isHomogeneous_X _ _)
  obtain ⟨v, hv⟩ : ∃ v, eval v (f * X 0) ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hne (X_ne_zero _) (hp.eq_zero_of_forall_eval_eq_zero h)
  have h0 : v 0 ≠ 0 := by
    intro h
    apply hv
    simp [h]
  refine ⟨v, h0, homogeneous_axis_leadingCoeff (linearSubstitution_homogeneous v hf) ?_⟩
  change eval (Fin.cons 1 0) (linearSubstitution v f) ≠ 0
  rw [eval_axis_linearSubstitution]
  exact (mul_ne_zero_iff.mp (by simpa only [map_mul, eval_X] using hv)).1

lemma inverseLinearSubstitution_homogeneous {n N : ℕ} (v : Fin (n + 1) → k)
    {f : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous N) :
    (inverseLinearSubstitution v f).IsHomogeneous N := by
  simpa only [one_mul, inverseLinearSubstitution] using hf.aeval (n := 1)
    (Fin.cons (MvPolynomial.C (v 0)⁻¹ * X 0)
      (fun i => X i.succ - MvPolynomial.C (v i.succ / v 0) * X 0)) (fun i => by
        cases i using Fin.cases with
        | zero => exact isHomogeneous_C_mul_X _ _
        | succ i => exact (isHomogeneous_X _ _).sub (isHomogeneous_C_mul_X _ _))

/-- Induction on the number of linear generators, allowing a finite extension
of their generated algebra so that elimination does not require a new grading. -/
lemma normalize_finite_family [Infinite k] [Nontrivial C]
    (G : NonnegativeGrading C) (hzero : Connected k G) :
    ∀ (n : ℕ) (x : Fin n → C), (∀ i, x i ∈ G.piece 1) →
      Module.Finite (Algebra.adjoin k (Set.range x)) C →
      ∃ (d : ℕ) (y : Fin d → C), (∀ i, y i ∈ G.piece 1) ∧
        AlgebraicIndependent k y ∧ Module.Finite (Algebra.adjoin k (Set.range y)) C := by
  intro n
  induction n with
  | zero =>
    intro x hx hfin
    exact ⟨0, x, hx, algebraicIndependent_empty_type, hfin⟩
  | succ n ih =>
    intro x hx hfin
    by_cases hind : AlgebraicIndependent k x
    · exact ⟨n + 1, x, hx, hind, hfin⟩
    obtain ⟨N, f, hne, hf, hrel⟩ := exists_homogeneous_relation G hzero x hx hind
    obtain ⟨v, hv, hu⟩ := exists_linear_monic_change hf hne
    let T := linearChange v hv
    let z : Fin (n + 1) → C := fun i => aeval x (T.symm (X i))
    have hz : ∀ i, z i ∈ G.piece 1 := by
      intro i
      apply aeval_mem_piece G hzero x hx
      exact inverseLinearSubstitution_homogeneous v (isHomogeneous_X _ _)
    have hzmap : aeval z = (aeval x).comp T.symm.toAlgHom := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
      rfl
    have hzadjoin : Algebra.adjoin k (Set.range z) = Algebra.adjoin k (Set.range x) := by
      rw [← aeval_range, ← aeval_range, hzmap, AlgHom.range_comp,
        (AlgHom.range_eq_top T.symm.toAlgHom).mpr T.symm.surjective, Algebra.map_top]
    have hzrel : aeval z (T f) = 0 := by
      rw [hzmap]
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using hrel
    have hfinz : Module.Finite (Algebra.adjoin k (Set.range z)) C := hzadjoin.symm ▸ hfin
    exact ih (z ∘ Fin.succ) (fun i => hz i.succ)
      (finite_drop_of_integral z hfinz (first_integral_of_relation z (T f) hzrel hu))

lemma finite_aeval_of_adjoin {ι : Type*} (y : ι → C)
    (hfin : Module.Finite (Algebra.adjoin k (Set.range y)) C) : (aeval (R := k) y).Finite := by
  have hv : (aeval (R := k) y).range.val.Finite := by
    rw [aeval_range]
    exact hfin
  have h := hv.comp (AlgHom.Finite.of_surjective (aeval (R := k) y).rangeRestrict
    (aeval (R := k) y).rangeRestrict_surjective)
  simpa only [AlgHom.val_comp_rangeRestrict] using h

/-- Linear graded Noether normalization, including the number of variables. -/
theorem normalization_map : normalization_mapType.{u,v} := by
  intro k C _ _ _ _ _ G hzero hstd
  classical
  obtain ⟨s, hs, hgen⟩ := standard_generators G hzero hstd
  let x : Fin s.card → C := fun i => (s.equivFin.symm i : C)
  have hx : ∀ i, x i ∈ G.piece 1 := fun i => hs _ (s.equivFin.symm i).2
  have hrange : Set.range x = (s : Set C) := by
    ext c
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hc
      exact ⟨s.equivFin ⟨c, hc⟩, by simp [x]⟩
  have hfin : Module.Finite (Algebra.adjoin k (Set.range x)) C := by
    rw [hrange, hgen]
    exact Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subalgebra k C) C)
      (by intro c; exact ⟨⟨c, trivial⟩, rfl⟩)
  obtain ⟨d, y, hy, hind, hfiny⟩ := normalize_finite_family G hzero s.card x hx hfin
  let g : MvPolynomial (Fin d) k →ₐ[k] C := aeval y
  have hinj : Function.Injective g := algebraicIndependent_iff_injective_aeval.mp hind
  have hgfin : g.Finite := finite_aeval_of_adjoin y hfiny
  refine ⟨d, g, hinj, hgfin, ?_, ?_, ?_⟩
  · intro n f hf
    exact aeval_mem_piece G hzero y hy hf
  · intro i
    simpa only [g, aeval_X] using hy i
  · have hdim := P103.Ch04.IntegralDimension.dimension_eq
      (MvPolynomial (Fin d) k) C g.toRingHom hgfin.to_isIntegral
    rw [(RingHom.injective_iff_ker_eq_bot g.toRingHom).mp hinj] at hdim
    exact hdim.trans ((ringKrullDim_eq_of_ringEquiv
      (RingEquiv.quotientBot (MvPolynomial (Fin d) k))).trans
      (P103.Ch06.PolynomialDimension.polynomial_dimension k d))

theorem normalization_elements : normalization_elementsType.{u,v} := by
  intro k C _ _ _ _ _ G hzero hstd
  obtain ⟨d, g, hinj, hfin, _, hdeg, hdim⟩ := normalization_map k C G hzero hstd
  refine ⟨d, g ∘ MvPolynomial.X, hdeg, ?_, ?_, hdim⟩
  · rw [algebraicIndependent_iff_injective_aeval, ← MvPolynomial.aeval_unique g]
    exact hinj
  · have hrange : g.range.val.Finite :=
      AlgHom.Finite.of_comp_finite (f := g.rangeRestrict) (g := g.range.val)
        (by simpa using hfin)
    have hfg : Module.Finite g.range C := hrange
    rwa [MvPolynomial.aeval_unique g, MvPolynomial.aeval_range] at hfg

theorem dimension_zero : dimension_zeroType.{u,v} := by
  intro k C _ _ _ _ _ G hzero hstd hdim
  obtain ⟨d, y, _, _, hfin, hd⟩ := normalization_elements k C G hzero hstd
  have hd0 : d = 0 := by
    rw [hdim] at hd
    exact_mod_cast hd.symm
  subst d
  have hyempty : Set.range y = ∅ := by simp
  rw [hyempty, Algebra.adjoin_empty] at hfin
  have := hfin
  exact Module.Finite.trans (⊥ : Subalgebra k C) C

end P103.Ch06.LinearGradedNormalization
