import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.RegularTorusCohomology

open scoped TensorProduct Classical

namespace LinearAlgebraicGroups.RegularTorusCohomology

noncomputable section

universe u

variable {R M W : Type*} [CommRing R] [CommGroup M] [AddCommGroup W] [Module R W]

open LinearAlgebraicGroups.Specs.RegularTorusCohomology

@[simp] theorem tensorCoefficients_monomial {D : Type*} [CommMonoid D] (w : W) (m : D) :
    tensorCoefficients R D W (w ⊗ₜ[R] MonoidAlgebra.of R D m) = Finsupp.single m w := by
  classical
  simp [tensorCoefficients, ← MonoidAlgebra.basis_apply]

@[simp] theorem constantCoefficient_apply (p : MonoidAlgebra R M) :
    constantCoefficient R M p = p.coeff 1 := rfl

theorem translationInvariant : TranslationInvariant := by
  intro R S M _ _ _ _
  constructor
  · intro r p
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp_all [TensorProduct.tmul_add, mul_add]
    | single m a =>
      classical
      by_cases h : m = 1 <;>
        simp [MonoidAlgebra.scalarTensorEquiv_tmul, MonoidAlgebra.coeff_single, h, eq_comm,
          Algebra.smul_def]
  · intro t p
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp_all
    | single m a =>
      classical
      rw [translation, MonoidAlgebra.lift_single]
      by_cases h : m = 1
      · subst m
        simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single]
      · simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, MonoidAlgebra.single_mul_single,
          MonoidAlgebra.coeff_single, h, eq_comm]

@[simp] theorem omitVariable_apply {n : ℕ} (i : Fin (n + 1)) (f : Regular M W n)
    (a : Fin (n + 1) → M) :
    omitVariable (R := R) n i f a = if a i = 1 then f (i.removeNth a) else 0 := by
  classical
  change Finsupp.mapDomain (@Fin.insertNth n (fun _ => M) i 1) f a = _
  by_cases h : a i = 1
  · rw [ite_eq_left h]
    have he : @Fin.insertNth n (fun _ => M) i 1 (i.removeNth a) = a :=
      Fin.insertNth_eq_iff.2 ⟨h.symm, rfl⟩
    rw [← he, Finsupp.mapDomain_apply_of_injective (Fin.insertNth_right_injective _)]
    simp
  · rw [ite_eq_right h]
    apply Finsupp.mapDomain_of_notMem_range _ _
    rintro ⟨b, hb⟩
    exact h (by simpa using (congrFun hb i).symm)

@[simp] theorem average_apply {n : ℕ} (i : Fin (n + 1)) (f : Regular M W (n + 1))
    (a : Fin n → M) :
    average (R := R) n i f a = f (@Fin.insertNth n (fun _ => M) i 1 a) := rfl

@[simp] theorem regularTensorEquiv_monomial {R M : Type u} [CommRing R] [CommGroup M]
    {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ} (w : W) (a : Fin n → M) :
    regularTensorEquiv R M W n (w ⊗ₜ[R] coordinateBasis R M n a) = Finsupp.single a w := by
  classical
  simp [regularTensorEquiv]

theorem coordinateBasis_cons {R M : Type u} [CommRing R] [CommGroup M]
    (n : ℕ) (m : M) (a : Fin n → M) :
    coordinateBasis R M (n + 1) (Fin.cons m a) =
      (show coordinatePower R M (n + 1) from
        MonoidAlgebra.of R M m ⊗ₜ[R] coordinateBasis R M n a) := by
  change ((MonoidAlgebra.basis M R).tensorProduct (coordinateBasis R M n)).reindex
    (Fin.consEquiv (fun _ => M)) (Fin.cons m a) = _
  rw [Module.Basis.reindex_apply]
  change ((MonoidAlgebra.basis M R).tensorProduct (coordinateBasis R M n)) (m, a) = _
  simp

theorem tensorAveraging : TensorAveraging := by
  intro R M _ _ W _ _ n f
  classical
  let F := (regularTensorEquiv R M W n).toLinearMap.comp (averageFirstTensor n)
  let G := (average (R := R) (M := M) (W := W) n 0).comp
    (regularTensorEquiv R M W (n + 1)).toLinearMap
  have h : F = G := by
    apply TensorProduct.ext'
    intro w p
    let L : coordinatePower R M (n + 1) →ₗ[R] Regular M W n :=
      F.comp (TensorProduct.mk R W _ w)
    let J : coordinatePower R M (n + 1) →ₗ[R] Regular M W n :=
      G.comp (TensorProduct.mk R W _ w)
    have he : L = J := by
      apply (coordinateBasis R M (n + 1)).ext
      intro a
      rw [← Fin.cons_self_tail a]
      change regularTensorEquiv R M W n
          (averageFirstTensor n (w ⊗ₜ[R] coordinateBasis R M (n + 1) (Fin.cons (a 0) (Fin.tail a)))) =
        average (R := R) n 0
          (regularTensorEquiv R M W (n + 1)
            (w ⊗ₜ[R] coordinateBasis R M (n + 1) (Fin.cons (a 0) (Fin.tail a))))
      rw [regularTensorEquiv_monomial]
      ext b
      simp only [average_apply, Fin.insertNth_zero', Finsupp.single_apply]
      rw [coordinateBasis_cons]
      change regularTensorEquiv R M W n
        (((TensorProduct.lid R _).toLinearMap.lTensor W)
          ((((constantCoefficient R M).rTensor _).lTensor W)
            (w ⊗ₜ[R] (MonoidAlgebra.of R M (a 0) ⊗ₜ[R] coordinateBasis R M n (Fin.tail a))))) b = _
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, constantCoefficient_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.coeff_single]
      by_cases h0 : a 0 = 1
      · simp only [h0, ite_true, one_smul, regularTensorEquiv_monomial, Finsupp.single_apply,
          Fin.cons_inj, true_and]
      · have hb : a ≠ Fin.cons 1 b :=
          fun he => h0 (congrFun he 0)
        simp [Ne.symm h0, hb]
    exact LinearMap.congr_fun he p
  exact LinearMap.congr_fun h f

private theorem diagonalPull_apply {n : ℕ} (f : Regular M W n) (a : Fin n → M) (m : M) :
    diagonalPull (R := R) n f (a, m) = if m = ∏ i, a i then f a else 0 := by
  classical
  change Finsupp.mapDomain (fun a : Fin n → M => (a, ∏ i, a i)) f (a, m) = _
  split_ifs with h
  · subst m
    exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => congrArg Prod.fst h) f a
  · apply Finsupp.mapDomain_of_notMem_range _ _
    rintro ⟨b, hb⟩
    have hb' : b = a := congrArg Prod.fst hb
    subst b
    exact h (congrArg Prod.snd hb).symm

private theorem coefficientPull_apply (ρ : TorusComodule R M W) {n : ℕ}
    (f : Regular M W n) (a : Fin n → M) (m : M) :
    coefficientPull ρ n f (a, m) = coactionCoefficients ρ (f a) m := by
  classical
  have h :
      (Finsupp.lapply (a, m)).comp (coefficientPull ρ n) =
        (Finsupp.lapply m).comp ((coactionCoefficients ρ).comp (Finsupp.lapply a)) := by
    apply Finsupp.lhom_ext
    intro b w
    simp only [LinearMap.comp_apply, coefficientPull, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
      Finsupp.lapply_apply]
    by_cases h : a = b
    · subst b
      rw [Finsupp.single_eq_same]
      exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => congrArg Prod.snd h) _ _
    · rw [Finsupp.single_eq_of_ne h, map_zero, Finsupp.zero_apply]
      exact Finsupp.mapDomain_of_notMem_range _ _ (fun ⟨_, he⟩ => h (congrArg Prod.fst he).symm)
  exact LinearMap.congr_fun h f

theorem equivarianceCriterion : EquivarianceCriterion := by
  intro R M W _ _ _ _ ρ n f
  classical
  have h (a : Fin n → M) (m : M) :
      (tensorCoefficients R M W) (f a ⊗ₜ[R] MonoidAlgebra.of R M (∏ i, a i)) m =
        (if m = ∏ i, a i then f a else 0) := by
    simp only [tensorCoefficients_monomial, Finsupp.single_apply, eq_comm]
  constructor
  · intro hf a
    apply (tensorCoefficients R M W).injective
    ext m
    rw [h, ← diagonalPull_apply (R := R) f a m, hf, coefficientPull_apply]
    rfl
  · intro hf
    ext ⟨a, m⟩
    rw [diagonalPull_apply, coefficientPull_apply, ← h]
    exact congrArg (fun x => tensorCoefficients R M W x m) (hf a).symm

theorem Equivariant.omitVariable {ρ : TorusComodule R M W} {n : ℕ}
    {f : Regular M W n} (hf : Equivariant ρ f) (i : Fin (n + 1)) :
    Equivariant ρ (omitVariable (R := R) n i f) := by
  classical
  rw [equivarianceCriterion] at hf ⊢
  intro a
  rw [omitVariable_apply]
  split_ifs with h
  · have hp := Fin.mul_prod_removeNth i a
    rw [h, one_mul] at hp
    rw [← hp]
    exact hf _
  · simp

theorem Equivariant.average {ρ : TorusComodule R M W} {n : ℕ}
    {f : Regular M W (n + 1)} (hf : Equivariant ρ f) (i : Fin (n + 1)) :
    Equivariant ρ (average (R := R) n i f) := by
  rw [equivarianceCriterion] at hf ⊢
  intro a
  simpa [Fin.prod_insertNth] using hf (@Fin.insertNth n (fun _ => M) i 1 a)

theorem Equivariant.alternatingOmission {ρ : TorusComodule R M W} {n : ℕ}
    {f : Regular M W n} (hf : Equivariant ρ f) :
    Equivariant ρ (differential (R := R) n f) := by
  unfold Equivariant
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun x : ((Fin (n + 1) → M) × M) →₀ W => (-1 : ℤ) ^ (i : ℕ) • x)
      (hf.omitVariable i)

private theorem average_omit_zero (n : ℕ) (f : Regular M W n) :
    average (R := R) n 0 (omitVariable (R := R) n 0 f) = f := by
  ext a
  classical
  simp

private theorem average_omit_succ (n : ℕ) (i : Fin (n + 1)) (f : Regular M W (n + 1)) :
    average (R := R) (n + 1) 0 (omitVariable (R := R) (n + 1) i.succ f) =
      omitVariable (R := R) n i (average (R := R) n 0 f) := by
  ext a
  classical
  simp only [average_apply, omitVariable_apply, Fin.insertNth_zero', Fin.cons_succ]
  have he : @Fin.removeNth (n + 1) (fun _ => M) i.succ (Fin.cons 1 a) =
      Fin.cons 1 (@Fin.removeNth n (fun _ => M) i a) := by
    funext j
    exact congrFun (Fin.cons_comp_succ_succAbove (1 : M) a i) j
  rw [he]

theorem contraction (n : ℕ) (f : Regular M W (n + 1)) :
    differential (R := R) n (average (R := R) n 0 f) +
      average (R := R) (n + 1) 0 (differential (R := R) (n + 1) f) = f := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Fin.sum_univ_succ (n := n + 1)]
  simp only [Fin.val_zero, pow_zero, one_zsmul, map_add, map_sum, map_zsmul,
    average_omit_zero, average_omit_succ, Fin.val_succ, pow_succ, mul_neg_one,
    neg_smul, Finset.sum_neg_distrib, map_neg]
  abel

private theorem omit_omit_swap (n : ℕ) (f : Regular M W n)
    (i : Fin (n + 1)) (j : Fin (n + 2)) (hji : (j : ℕ) ≤ i) :
    omitVariable (R := R) (n + 1) j (omitVariable (R := R) n i f) =
      omitVariable (R := R) (n + 1) i.succ
        (omitVariable (R := R) n (j.castLT (Nat.lt_of_le_of_lt hji i.isLt)) f) := by
  classical
  let j' : Fin (n + 1) := j.castLT (Nat.lt_of_le_of_lt hji i.isLt)
  have hj : j = j'.castSucc := rfl
  have h1 : j.succAbove i = i.succ :=
    Fin.succAbove_of_le_castSucc j i hji
  have h2 : i.succ.succAbove j' = j :=
    (Fin.succAbove_succ_of_le i j' hji).trans hj.symm
  have h3 : i.predAbove j = j' := by
    rw [hj, Fin.predAbove_castSucc_of_le _ _ hji]
  ext a
  have h4 := Fin.removeNth_removeNth_eq_swap a i j
  rw [h1, h3] at h4
  simp only [omitVariable_apply]
  change (if a j = 1 then if a (j.succAbove i) = 1 then f (i.removeNth (j.removeNth a)) else 0
    else 0) = (if a i.succ = 1 then if a (i.succ.succAbove j') = 1 then
      f (j'.removeNth (i.succ.removeNth a)) else 0 else 0)
  rw [h1, h2, h4]
  split_ifs <;> rfl

-- Adapted from Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean (AlternatingFaceMapComplex.d_squared). Copyright (c) 2021 Joël Riou. All rights reserved.
-- Released under Apache 2.0, see LICENSE. MathGenome adapts the index pairing and sum proof to regular torus cochains.
theorem differential_squared (n : ℕ) (f : Regular M W n) :
    differential (R := R) (n + 1) (differential (R := R) n f) = 0 := by
  classical
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, Finset.smul_sum]
  rw [← Finset.sum_product']
  let P := Fin (n + 1) × Fin (n + 2)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr($(h).snd),
      by simpa [φ, Fin.castSucc_castLT] using! congr(Fin.castSucc $(h).fst)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    have hji : (j : ℕ) ≤ i := (Finset.mem_filter.mp hij).2
    dsimp [φ]
    rw [omit_omit_swap n f i j hji]
    simp only [pow_succ, mul_neg_one, neg_smul]
    rw [smul_neg, neg_neg, smul_smul, smul_smul, mul_comm]

theorem homogeneousContraction : HomogeneousContraction := by
  intro R M W _ _ _ _ ρ n
  exact ⟨fun f hf => ⟨hf.alternatingOmission, differential_squared (n + 1) f⟩,
    fun f hf => ⟨hf.average 0, contraction (n + 1) f⟩⟩

@[simp] theorem lastCoefficient_apply {D : Type*} (c : (D × M) →₀ W) (a : D) :
    lastCoefficient (R := R) c a = c (a, 1) := rfl

private theorem lastCoefficient_single {D : Type*} (a : D) (b : M) (w : W) :
    lastCoefficient (R := R) (Finsupp.single (a, b) w) =
      if b = 1 then Finsupp.single a w else 0 := by
  ext d
  by_cases h : b = 1 <;> simp [Finsupp.single_apply, h]

private theorem lastCoefficient_fixed {D E : Type*} (g : E → D) (b : M) (q : E →₀ W) :
    lastCoefficient (R := R) (Finsupp.mapDomain (fun x => (g x, b)) q) =
      if b = 1 then Finsupp.mapDomain g q else 0 := by
  by_cases hb : b = 1
  · simp only [ite_eq_left hb]
    have h : (lastCoefficient (R := R)).comp (Finsupp.lmapDomain _ _ (fun x => (g x, b))) =
        (Finsupp.lmapDomain W R g) := by
      apply Finsupp.lhom_ext
      intro a w
      simp [lastCoefficient_single, hb]
    exact LinearMap.congr_fun h q
  · simp only [ite_eq_right hb]
    have h : (lastCoefficient (R := R)).comp (Finsupp.lmapDomain W R (fun x => (g x, b))) = 0 := by
      apply Finsupp.lhom_ext
      intro a w
      simp [lastCoefficient_single, hb]
    exact LinearMap.congr_fun h q

@[simp] theorem actPolynomial_single {D : Type*} [CommGroup D] (ρ : TorusComodule R M W)
    (g : M →* D) (a : D) (w : W) :
    actPolynomial ρ g (Finsupp.single a w) =
      Finsupp.mapDomain (fun m => a * g m) (coactionCoefficients ρ w) := by
  simp [actPolynomial]

private theorem average_inhomogeneousOne (ρ : TorusComodule R M W) :
    (lastCoefficient (R := R)).comp (inhomogeneousOne ρ) =
      (inhomogeneousZero ρ).comp (Finsupp.lapply 1) + LinearMap.id := by
  apply Finsupp.lhom_ext
  intro a w
  simp only [LinearMap.comp_apply, inhomogeneousOne, LinearMap.add_apply, LinearMap.sub_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, actPolynomial_single, map_add, map_sub,
    lastCoefficient_single, inhomogeneousZero, LinearMap.id_apply, Finsupp.lapply_apply, ite_true]
  have he : (fun m : M => (1, a) * (MonoidHom.inl M M) m) = (fun m => (m, a)) := by
    funext m
    simp
  rw [he, lastCoefficient_fixed]
  by_cases h : a = 1
  · subst a
    simp [Finsupp.mapDomain_fun_id]
  · simp [h]

private theorem average_inhomogeneousTwo (ρ : TorusComodule R M W) :
    (lastCoefficient (R := R)).comp (inhomogeneousTwo ρ) =
      (inhomogeneousOne ρ).comp (averageLast (R := R)) - LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro ⟨a, b⟩ w
  simp only [LinearMap.comp_apply, inhomogeneousTwo, LinearMap.add_apply, LinearMap.sub_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, actPolynomial_single, map_add, map_sub,
    lastCoefficient_single, LinearMap.id_apply]
  have he : (fun m : M => ((1, a), b) *
        ((MonoidHom.inl (M × M) M).comp (MonoidHom.inl M M)) m) =
      (fun m : M => ((m, a), b)) := by
    funext m
    simp
  rw [he, lastCoefficient_fixed]
  simp only [ite_true]
  by_cases h : b = 1
  · subst b
    simp [inhomogeneousOne, actPolynomial_single]
  · simp [h]

theorem inhomogeneousCoboundaries : InhomogeneousCoboundaries := by
  intro R M W _ _ _ _ ρ
  constructor
  · intro c hc
    have h := LinearMap.congr_fun (average_inhomogeneousOne ρ) c
    simp only [LinearMap.comp_apply, hc, map_zero, LinearMap.add_apply, LinearMap.id_apply,
      Finsupp.lapply_apply] at h
    rw [map_neg, neg_eq_iff_add_eq_zero]
    exact h.symm
  · intro c hc
    have h := LinearMap.congr_fun (average_inhomogeneousTwo ρ) c
    simp only [LinearMap.comp_apply, hc, map_zero, LinearMap.sub_apply, LinearMap.id_apply] at h
    exact sub_eq_zero.mp h.symm

section PointEvaluation

variable {D E S : Type*} [CommRing S] [Algebra R S]

@[simp] theorem evaluatePolynomial_single (t : D → S) (a : D) (w : W) :
    evaluatePolynomial (R := R) t (Finsupp.single a w) = t a ⊗ₜ[R] w := by
  simp [evaluatePolynomial]

@[simp] theorem pointAction_tmul (ρ : TorusComodule R M W) (t : M →* S) (s : S) (w : W) :
    pointAction ρ t (s ⊗ₜ[R] w) = s • evaluatePolynomial t (coactionCoefficients ρ w) := by
  simp [pointAction, LinearMap.toSpanSingleton]

theorem evaluatePolynomial_mapDomain (g : D → E) (t : E → S) (c : D →₀ W) :
    evaluatePolynomial (R := R) t (Finsupp.mapDomain g c) =
      evaluatePolynomial (R := R) (t ∘ g) c := by
  have h : (evaluatePolynomial (R := R) t).comp (Finsupp.lmapDomain W R g) =
      evaluatePolynomial (R := R) (t ∘ g) := by
    apply Finsupp.lhom_ext
    intro a w
    simp
  exact LinearMap.congr_fun h c

private theorem evaluatePolynomial_scale (t : D → S) (s : S) (c : D →₀ W) :
    evaluatePolynomial (R := R) (fun a => s * t a) c =
      s • evaluatePolynomial (R := R) t c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, smul_add]
  | single a w => simp [TensorProduct.smul_tmul', smul_eq_mul]

theorem evaluatePolynomial_act [CommGroup D] (ρ : TorusComodule R M W)
    (g : M →* D) (t : D →* S) (c : D →₀ W) :
    evaluatePolynomial t (actPolynomial ρ g c) =
      pointAction ρ (t.comp g) (evaluatePolynomial t c) := by
  have h : (evaluatePolynomial (R := R) t).comp (actPolynomial ρ g) =
      ((pointAction ρ (t.comp g)).restrictScalars R).comp (evaluatePolynomial t) := by
    apply Finsupp.lhom_ext
    intro a w
    simp only [LinearMap.comp_apply, actPolynomial_single, evaluatePolynomial_single,
      LinearMap.restrictScalars_apply, pointAction_tmul, evaluatePolynomial_mapDomain]
    change evaluatePolynomial (R := R) (fun m => t (a * g m)) (coactionCoefficients ρ w) = _
    simp only [map_mul]
    exact evaluatePolynomial_scale (t.comp g) (t a) (coactionCoefficients ρ w)
  exact LinearMap.congr_fun h c

theorem inhomogeneousPointFormulas : InhomogeneousPointFormulas := by
  intro R M W S _ _ _ _ _ _ ρ t s z
  refine ⟨?_, ?_, ?_⟩
  · intro w
    simp [inhomogeneousZero]
  · intro c
    have h₁ : (⇑(t.coprod s) ∘ fun a : M => (1, a)) = ⇑s := by
      funext a
      simp
    have h₂ : (⇑(t.coprod s) ∘ fun a : M => (a, a)) = ⇑(t * s) := rfl
    have h₃ : (⇑(t.coprod s) ∘ fun a : M => (a, 1)) = ⇑t := by
      funext a
      simp
    simp only [inhomogeneousOne, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, Finsupp.lmapDomain_apply, map_add, map_sub,
      evaluatePolynomial_act, evaluatePolynomial_mapDomain, MonoidHom.coprod_comp_inl, h₁, h₂, h₃]
  · intro c
    let p := (t.coprod s).coprod z
    have h₁ : (⇑p ∘ fun a : M × M => ((1, a.1), a.2)) = ⇑(s.coprod z) := by
      funext a
      simp [p]
    have h₂ : (⇑p ∘ fun a : M × M => ((a.1, a.1), a.2)) = ⇑((t * s).coprod z) := rfl
    have h₃ : (⇑p ∘ fun a : M × M => (a, a.2)) = ⇑(t.coprod (s * z)) := by
      funext a
      simp [p, mul_assoc]
    have h₄ : (⇑p ∘ fun a : M × M => (a, 1)) = ⇑(t.coprod s) := by
      funext a
      simp [p]
    change evaluatePolynomial p (inhomogeneousTwo ρ c) = _
    simp only [inhomogeneousTwo, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, Finsupp.lmapDomain_apply, map_add, map_sub,
      evaluatePolynomial_act, evaluatePolynomial_mapDomain, h₁, h₂, h₃, h₄]
    simp [p, ← MonoidHom.comp_assoc]

/-- Evaluation at the universal point reads the entire regular polynomial. -/
theorem evaluatePolynomial_universal [CommGroup D] (c : D →₀ W) :
    evaluatePolynomial (R := R) (MonoidAlgebra.of R D) c =
      TensorProduct.comm R W (MonoidAlgebra R D) ((tensorCoefficients R D W).symm c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single a w =>
    rw [evaluatePolynomial_single, ← tensorCoefficients_monomial (R := R) w a, LinearEquiv.symm_apply_apply]
    rfl

private theorem evaluatePolynomial_coefficientPull (ρ : TorusComodule R M W) {n : ℕ}
    (q : (Fin n → M) →* S) (t : M →* S) (f : Regular M W n) :
    evaluatePolynomial (q.coprod t) (coefficientPull ρ n f) =
      pointAction ρ t (evaluatePolynomial q f) := by
  have h : (evaluatePolynomial (R := R) (q.coprod t)).comp (coefficientPull ρ n) =
      ((pointAction ρ t).restrictScalars R).comp (evaluatePolynomial q) := by
    apply Finsupp.lhom_ext
    intro a w
    simp only [LinearMap.comp_apply, coefficientPull, Finsupp.lsum_single,
      Finsupp.lmapDomain_apply, evaluatePolynomial_mapDomain, evaluatePolynomial_single,
      LinearMap.restrictScalars_apply, pointAction_tmul]
    exact evaluatePolynomial_scale t (q a) (coactionCoefficients ρ w)
  exact LinearMap.congr_fun h f

private theorem evaluatePolynomial_diagonalPull {n : ℕ} (p : Fin n → M →* S)
    (t : M →* S) (f : Regular M W n) :
    evaluatePolynomial ((tupleCharacter p).coprod t) (diagonalPull (R := R) n f) =
      evaluatePolynomial (R := R) (tupleCharacter (fun i => t * p i)) f := by
  rw [diagonalPull, Finsupp.lmapDomain_apply, evaluatePolynomial_mapDomain]
  have h : (⇑((tupleCharacter p).coprod t) ∘ (fun a : Fin n → M => (a, ∏ i, a i))) =
      ⇑(tupleCharacter (fun i => t * p i)) := by
    funext a
    simp [tupleCharacter, map_prod, Finset.prod_mul_distrib, mul_comm]
  rw [h]

private theorem tupleCharacter_split {n : ℕ} (q : (Fin n → M) →* S) :
    tupleCharacter (fun i => q.comp (MonoidHom.mulSingle (fun _ : Fin n => M) i)) = q := by
  apply MonoidHom.ext
  intro a
  change (∏ i, q (Pi.mulSingle i (a i))) = q a
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem homogeneousPointCriterion : HomogeneousPointCriterion := by
  intro R M _ _ W _ _ ρ n f
  constructor
  · intro hf S _ _ t p
    rw [← evaluatePolynomial_diagonalPull p t f, hf, evaluatePolynomial_coefficientPull]
  · intro hf
    let D := Fin n → M
    let A := MonoidAlgebra R (D × M)
    let g : (D × M) →* A := MonoidAlgebra.of R (D × M)
    let q := g.comp (MonoidHom.inl D M)
    let t := g.comp (MonoidHom.inr D M)
    let p : Fin n → M →* A := fun i => q.comp (MonoidHom.mulSingle (fun _ : Fin n => M) i)
    have hq : tupleCharacter p = q := tupleCharacter_split q
    have he := hf A t p
    rw [← evaluatePolynomial_diagonalPull p t f, ← evaluatePolynomial_coefficientPull,
      hq, show q.coprod t = g from MonoidHom.coprod_unique g] at he
    change diagonalPull (R := R) n f = coefficientPull ρ n f
    change evaluatePolynomial (MonoidAlgebra.of R (D × M)) _ =
      evaluatePolynomial (MonoidAlgebra.of R (D × M)) _ at he
    rw [evaluatePolynomial_universal, evaluatePolynomial_universal] at he
    exact (tensorCoefficients R (D × M) W).symm.injective
      ((TensorProduct.comm R W A).injective he)

theorem omissionPointFormula : OmissionPointFormula := by
  intro R M W S _ _ _ _ _ _ n i p f
  rw [omitVariable, Finsupp.lmapDomain_apply, evaluatePolynomial_mapDomain]
  have h : (⇑(tupleCharacter p) ∘ @Fin.insertNth n (fun _ => M) i 1) =
      ⇑(tupleCharacter (fun j => p (i.succAbove j))) := by
    funext a
    change (∏ j, p j (@Fin.insertNth n (fun _ => M) i 1 a j)) =
      ∏ j, p (i.succAbove j) (a j)
    rw [Fin.prod_univ_succAbove _ i]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [h]

private theorem evaluatePolynomial_universal_injective [CommGroup D] :
    Function.Injective (evaluatePolynomial (R := R) (W := W) (MonoidAlgebra.of R D)) := by
  intro f g h
  rw [evaluatePolynomial_universal, evaluatePolynomial_universal] at h
  exact (tensorCoefficients R D W).symm.injective
    ((TensorProduct.comm R W (MonoidAlgebra R D)).injective h)

theorem inhomogeneousCocycleCriterion : InhomogeneousCocycleCriterion := by
  intro R M _ _ W _ _ ρ
  constructor
  · intro c
    constructor
    · intro hc S _ _ t s
      rw [← (inhomogeneousPointFormulas ρ t s 1).2.1 c, hc, map_zero]
    · intro hc
      let A := MonoidAlgebra R (M × M)
      let g := MonoidAlgebra.of R (M × M)
      let t := g.comp (MonoidHom.inl M M)
      let s := g.comp (MonoidHom.inr M M)
      have h := hc A t s
      rw [← (inhomogeneousPointFormulas ρ t s 1).2.1 c,
        show t.coprod s = g from MonoidHom.coprod_unique g, ← map_zero (evaluatePolynomial g)] at h
      exact evaluatePolynomial_universal_injective h
  · intro c
    constructor
    · intro hc S _ _ t s z
      rw [← (inhomogeneousPointFormulas ρ t s z).2.2 c, hc, map_zero]
    · intro hc
      let A := MonoidAlgebra R ((M × M) × M)
      let g := MonoidAlgebra.of R ((M × M) × M)
      let p := g.comp (MonoidHom.inl (M × M) M)
      let z := g.comp (MonoidHom.inr (M × M) M)
      let t := p.comp (MonoidHom.inl M M)
      let s := p.comp (MonoidHom.inr M M)
      have h := hc A t s z
      rw [← (inhomogeneousPointFormulas ρ t s z).2.2 c,
        show t.coprod s = p from MonoidHom.coprod_unique p,
        show p.coprod z = g from MonoidHom.coprod_unique g, ← map_zero (evaluatePolynomial g)] at h
      exact evaluatePolynomial_universal_injective h

/-- Evaluation of coaction coefficients agrees with evaluating the character
factor of the tensor coaction by the algebra map of the point. -/
theorem evaluatePolynomial_tensorCoefficients [CommGroup D] (t : D →* S)
    (x : W ⊗[R] MonoidAlgebra R D) :
    evaluatePolynomial t (tensorCoefficients R D W x) =
      TensorProduct.comm R W S
        (((MonoidAlgebra.lift R S D t).toLinearMap.lTensor W) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul w p =>
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp [TensorProduct.tmul_add, hp, hq]
    | single m a =>
      have h : MonoidAlgebra.single m a = a • MonoidAlgebra.of R D m := by simp
      rw [h, TensorProduct.tmul_smul]
      simp only [map_smul, tensorCoefficients_monomial, evaluatePolynomial_single,
        LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, MonoidAlgebra.lift_of,
        TensorProduct.comm_tmul]

theorem pointAction_one_tmul (ρ : TorusComodule R M W) (t : M →* S) (w : W) :
    pointAction ρ t (1 ⊗ₜ[R] w) =
      TensorProduct.comm R W S
        (((MonoidAlgebra.lift R S M t).toLinearMap.lTensor W) (ρ.coaction w)) := by
  rw [pointAction_tmul, one_smul]
  exact evaluatePolynomial_tensorCoefficients t (ρ.coaction w)

end PointEvaluation

end

end LinearAlgebraicGroups.RegularTorusCohomology
