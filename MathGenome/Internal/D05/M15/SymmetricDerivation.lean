import MathGenome.Internal.Specs.D05.M15.SymmetricDerivation
import MathGenome.Internal.D05.M15.Symmetric
import MathGenome.Internal.D05.M15.TensorDerivation
import MathGenome.Internal.D05.M15.Normalization.DividedPowers
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace D05.M15.SymmetricDerivation
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev S := _root_.SymmetricAlgebra K V
abbrev extend := @Specs.D05.M15.SymmetricDerivation.extend
abbrev contraction := @Specs.D05.M15.SymmetricDerivation.contraction
abbrev induced := @Specs.D05.M15.SymmetricDerivation.induced
abbrev IsDerivation := @Specs.D05.M15.SymmetricDerivation.IsDerivation
abbrev word := @Specs.D05.M15.SymmetricDerivation.word
abbrev homogeneous := @Specs.D05.M15.SymmetricDerivation.homogeneous

private theorem firstOrder_fst (f : V →ₗ[K] S (K := K) (V := V)) (x : S (K := K) (V := V)) :
    (_root_.SymmetricAlgebra.lift (Specs.D05.M15.SymmetricDerivation.firstOrderGenerator f) x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K (S (K := K) (V := V)) (S (K := K) (V := V))).comp
      (_root_.SymmetricAlgebra.lift (Specs.D05.M15.SymmetricDerivation.firstOrderGenerator f)) =
      AlgHom.id K _ := by
    apply _root_.SymmetricAlgebra.algHom_ext
    ext v
    change (_root_.SymmetricAlgebra.lift
      (Specs.D05.M15.SymmetricDerivation.firstOrderGenerator f) (_root_.SymmetricAlgebra.ι K V v)).fst = _
    rw [_root_.SymmetricAlgebra.lift_ι_apply]
    rfl
  exact DFunLike.congr_fun h x

theorem extend_generator (f : V →ₗ[K] S (K := K) (V := V)) (v : V) :
    extend f (_root_.SymmetricAlgebra.ι K V v) = f v := by
  change (_root_.SymmetricAlgebra.lift
    (Specs.D05.M15.SymmetricDerivation.firstOrderGenerator f) (_root_.SymmetricAlgebra.ι K V v)).snd = _
  rw [_root_.SymmetricAlgebra.lift_ι_apply]
  rfl

theorem extend_one (f : V →ₗ[K] S (K := K) (V := V)) : extend f 1 = 0 := by
  simp [extend, Specs.D05.M15.SymmetricDerivation.extend]

theorem extend_mul (f : V →ₗ[K] S (K := K) (V := V)) (x y : S (K := K) (V := V)) :
    extend f (x * y) = extend f x * y + x * extend f y := by
  simp only [extend, Specs.D05.M15.SymmetricDerivation.extend, LinearMap.coe_mk,
    AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul, firstOrder_fst]
  change x * _ + _ * y = _ * y + x * _
  exact add_comm _ _

theorem one_of_leibniz (D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
    (hD : IsDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  simp only [one_mul, mul_one] at h
  exact add_eq_left.mp h.symm

theorem derivation_ext (D E : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
    (hD : IsDerivation D) (hE : IsDerivation E)
    (h : ∀ v, D (_root_.SymmetricAlgebra.ι K V v) = E (_root_.SymmetricAlgebra.ι K V v)) :
    D = E := by
  ext x
  induction x using _root_.SymmetricAlgebra.induction with
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
      one_of_leibniz D hD, one_of_leibniz E hE]
  | ι v => exact h v
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => rw [hD, hE, hx, hy]

theorem extend_unique (f : V →ₗ[K] S (K := K) (V := V))
    (D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
    (hD : IsDerivation D) (h : ∀ v, D (_root_.SymmetricAlgebra.ι K V v) = f v) :
    D = extend f :=
  derivation_ext D (extend f) hD (extend_mul f)
    (fun v => (h v).trans (extend_generator f v).symm)

theorem unique_extension (f : V →ₗ[K] S (K := K) (V := V)) :
    ∃! D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V),
      IsDerivation D ∧ ∀ v, D (_root_.SymmetricAlgebra.ι K V v) = f v := by
  exact ⟨extend f, ⟨extend_mul f, extend_generator f⟩,
    fun D h => extend_unique f D h.1 h.2⟩

theorem contraction_generator (φ : Module.Dual K V) (v : V) :
    contraction φ (_root_.SymmetricAlgebra.ι K V v) = algebraMap K _ (φ v) :=
  extend_generator _ v

theorem contraction_one (φ : Module.Dual K V) : contraction φ 1 = 0 := extend_one _

theorem contraction_mul (φ : Module.Dual K V) (x y : S (K := K) (V := V)) :
    contraction φ (x * y) = contraction φ x * y + x * contraction φ y := extend_mul _ x y

theorem contraction_scalar (φ : Module.Dual K V) (a : K) :
    contraction φ (algebraMap K _ a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, contraction_one, smul_zero]

theorem induced_generator (A : V →ₗ[K] V) (v : V) :
    induced A (_root_.SymmetricAlgebra.ι K V v) = _root_.SymmetricAlgebra.ι K V (A v) :=
  extend_generator _ v

theorem induced_one (A : V →ₗ[K] V) : induced A 1 = 0 := extend_one _

theorem induced_mul (A : V →ₗ[K] V) (x y : S (K := K) (V := V)) :
    induced A (x * y) = induced A x * y + x * induced A y := extend_mul _ x y

theorem induced_scalar (A : V →ₗ[K] V) (a : K) : induced A (algebraMap K _ a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, induced_one, smul_zero]

/-- A finite product rule in a commutative algebra, derived from ordinary Leibniz. -/
theorem derivation_prod (D : S (K := K) (V := V) →ₗ[K] S (K := K) (V := V))
    (hD : IsDerivation D) {I : Type*} [DecidableEq I] (s : Finset I) (g : I → S (K := K) (V := V)) :
    D (∏ i ∈ s, g i) = ∑ j ∈ s, D (g j) * ∏ i ∈ s.erase j, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_of_leibniz D hD]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, hD, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hja : j ≠ a := ne_of_mem_of_not_mem hj ha
    rw [Finset.erase_insert_of_ne hja.symm, Finset.prod_insert (by simp [ha])]
    ac_rfl

theorem contraction_word (φ : Module.Dual K V) (p : ℕ) (x : Fin p → V) :
    contraction φ (word p x) =
      ∑ j : Fin p, φ (x j) • ∏ i ∈ (Finset.univ.erase j), _root_.SymmetricAlgebra.ι K V (x i) := by
  rw [word, Specs.D05.M15.SymmetricDerivation.word,
    derivation_prod _ (contraction_mul φ)]
  apply Finset.sum_congr rfl
  intro j _
  rw [contraction_generator, Algebra.smul_def]

/-- Actual descent of the tensor derivation through the symmetric quotient. -/
theorem tensor_descent (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V) :
    induced A (_root_.SymmetricAlgebra.algHom K V t) =
      _root_.SymmetricAlgebra.algHom K V (D05.M15.TensorDerivation.induced A t) := by
  induction t using _root_.TensorAlgebra.induction with
  | algebraMap a => simp only [AlgHom.commutes, induced_scalar, TensorDerivation.induced_scalar, map_zero]
  | ι v =>
    change induced A (_root_.SymmetricAlgebra.ι K V v) = _
    rw [induced_generator, TensorDerivation.induced_generator]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, induced_mul, TensorDerivation.induced_mul, map_add, hx, hy]

theorem ideal_invariant (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V)
    (ht : t ∈ Specs.D05.M15.Symmetric.commutatorIdeal K V) :
    D05.M15.TensorDerivation.induced A t ∈ Specs.D05.M15.Symmetric.commutatorIdeal K V := by
  have hq : _root_.SymmetricAlgebra.algHom K V t = 0 := by
    simpa only [map_zero, sub_zero] using (D05.M15.Symmetric.quotient_eq_iff t 0).mpr (by simpa using ht)
  have h := tensor_descent A t
  rw [hq, map_zero] at h
  have := (D05.M15.Symmetric.quotient_eq_iff (TensorDerivation.induced A t) 0).mp
    (h.symm.trans (map_zero _).symm)
  simpa only [sub_zero] using this

theorem commutator_formula (A : V →ₗ[K] V) (u v : V) :
    TensorDerivation.induced A
      (_root_.TensorAlgebra.ι K u * _root_.TensorAlgebra.ι K v -
        _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K u) =
      (_root_.TensorAlgebra.ι K (A u) * _root_.TensorAlgebra.ι K v -
        _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.ι K (A u)) +
      (_root_.TensorAlgebra.ι K u * _root_.TensorAlgebra.ι K (A v) -
        _root_.TensorAlgebra.ι K (A v) * _root_.TensorAlgebra.ι K u) := by
  simp only [map_sub, TensorDerivation.induced_mul, TensorDerivation.induced_generator]
  abel

theorem word_eq_homogeneousMap (p : ℕ) (x : Fin p → V) :
    word p x = Specs.D05.M15.Symmetric.homogeneousMap K V p (PiTensorProduct.tprod K x) :=
  (D05.M15.Symmetric.homogeneousMap_tprod p x).symm

theorem induced_word (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V) :
    induced A (word p x) = ∑ j : Fin p, word p (Function.update x j (A (x j))) := by
  classical
  simp only [word_eq_homogeneousMap, Specs.D05.M15.Symmetric.homogeneousMap, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, TensorPower.toTensorAlgebra_tprod]
  rw [tensor_descent, TensorDerivation.induced_word, map_sum]

theorem word_cons {p : ℕ} (v : V) (x : Fin p → V) :
    word (p + 1) (Fin.cons v x) = _root_.SymmetricAlgebra.ι K V v * word p x := by
  simp [word, Specs.D05.M15.SymmetricDerivation.word, Fin.prod_univ_succ]

theorem word_symmetric (p : ℕ) (x : Fin p → V) (σ : Equiv.Perm (Fin p)) :
    word (K := K) p (x ∘ σ) = word p x :=
  Equiv.prod_comp σ (fun i => _root_.SymmetricAlgebra.ι K V (x i))

/-- The deletion formula is symmetric and multilinear, and hence has a unique
linear factor through the accepted degree-p symmetric quotient. -/
theorem contraction_power_factor (φ : Module.Dual K V) (p : ℕ) :
    ∃! L : Specs.D05.M15.Symmetric.symmetricPower K V p →ₗ[K] S (K := K) (V := V),
      ∀ x, L (Specs.D05.M15.Symmetric.elementary K V p x) =
        ∑ j : Fin p, φ (x j) • ∏ i ∈ (Finset.univ.erase j), _root_.SymmetricAlgebra.ι K V (x i) := by
  let b := (contraction φ).compMultilinearMap
    ((Specs.D05.M15.Symmetric.homogeneousMap K V p).compMultilinearMap (PiTensorProduct.tprod K))
  have hb (x : Fin p → V) : b x = contraction φ (word p x) := by
    simp only [b, LinearMap.compMultilinearMap_apply, word_eq_homogeneousMap]
  have hs (x : Fin p → V) (σ : Equiv.Perm (Fin p)) : b (x ∘ σ) = b x := by
    rw [hb, hb, word_symmetric]
  obtain ⟨L, hL, hu⟩ := (D05.M15.Symmetric.power_universal p b).mp hs
  refine ⟨L, ?_, ?_⟩
  · intro x
    rw [hL, hb, contraction_word]
  · intro M hM
    apply hu
    intro x
    rw [hM, hb, contraction_word]

theorem induced_power_factor (A : V →ₗ[K] V) (p : ℕ) :
    ∃! L : Specs.D05.M15.Symmetric.symmetricPower K V p →ₗ[K] S (K := K) (V := V),
      ∀ x, L (Specs.D05.M15.Symmetric.elementary K V p x) =
        ∑ j : Fin p, word p (Function.update x j (A (x j))) := by
  let b := (induced A).compMultilinearMap
    ((Specs.D05.M15.Symmetric.homogeneousMap K V p).compMultilinearMap (PiTensorProduct.tprod K))
  have hb (x : Fin p → V) : b x = induced A (word p x) := by
    simp only [b, LinearMap.compMultilinearMap_apply, word_eq_homogeneousMap]
  have hs (x : Fin p → V) (σ : Equiv.Perm (Fin p)) : b (x ∘ σ) = b x := by
    rw [hb, hb, word_symmetric]
  obtain ⟨L, hL, hu⟩ := (D05.M15.Symmetric.power_universal p b).mp hs
  refine ⟨L, ?_, ?_⟩
  · intro x
    rw [hL, hb, induced_word]
  · intro M hM
    apply hu
    intro x
    rw [hM, hb, induced_word]

theorem word_mem (p : ℕ) (x : Fin p → V) : word p x ∈ homogeneous (K := K) (V := V) p :=
  ⟨PiTensorProduct.tprod K x, (word_eq_homogeneousMap p x).symm⟩

theorem scalar_mem (a : K) : algebraMap K (S (K := K) (V := V)) a ∈ homogeneous (K := K) (V := V) 0 := by
  have h := (homogeneous (K := K) (V := V) 0).smul_mem a (word_mem 0 (Fin.elim0))
  simpa [word, Specs.D05.M15.SymmetricDerivation.word, Algebra.algebraMap_eq_smul_one] using h

theorem generator_mul_mem (v : V) (p : ℕ) (y : S (K := K) (V := V))
    (hy : y ∈ homogeneous (K := K) (V := V) p) :
    _root_.SymmetricAlgebra.ι K V v * y ∈ homogeneous (K := K) (V := V) (p + 1) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, mul_smul_comm]
    apply Submodule.smul_mem
    rw [← word_eq_homogeneousMap, ← word_cons]
    exact word_mem _ _
  | add a b ha hb =>
    rw [map_add, mul_add]
    exact Submodule.add_mem _ ha hb

theorem contraction_homogeneous_zero (φ : Module.Dual K V) (y : S (K := K) (V := V))
    (hy : y ∈ homogeneous (K := K) (V := V) 0) : contraction φ y = 0 := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, ← word_eq_homogeneousMap]
    simp [word, Specs.D05.M15.SymmetricDerivation.word, contraction_one]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

/-- Contraction takes degree p+1 into degree p, with degree zero killed separately. -/
theorem contraction_homogeneous (φ : Module.Dual K V) (p : ℕ) (y : S (K := K) (V := V))
    (hy : y ∈ homogeneous (K := K) (V := V) (p + 1)) :
    contraction φ y ∈ homogeneous (K := K) (V := V) p := by
  induction p generalizing y with
  | zero =>
    obtain ⟨t, rfl⟩ := hy
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smul, ← word_eq_homogeneousMap]
      apply Submodule.smul_mem
      simpa [word, Specs.D05.M15.SymmetricDerivation.word, contraction_generator] using scalar_mem (V := V) (φ (x 0))
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  | succ p ih =>
    obtain ⟨t, rfl⟩ := hy
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smul, ← word_eq_homogeneousMap]
      apply Submodule.smul_mem
      rw [← Fin.cons_self_tail x, word_cons, contraction_mul, contraction_generator,
        ← Algebra.smul_def]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (word_mem _ _)
      · exact generator_mul_mem _ _ _ (ih _ (word_mem _ _))
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb

theorem induced_homogeneous (A : V →ₗ[K] V) (p : ℕ) (t : TensorPower K p V) :
    induced A (Specs.D05.M15.Symmetric.homogeneousMap K V p t) =
      Specs.D05.M15.Symmetric.homogeneousMap K V p (TensorDerivation.onPower A p t) := by
  change induced A (_root_.SymmetricAlgebra.algHom K V (TensorPower.toTensorAlgebra t)) = _
  rw [tensor_descent, TensorDerivation.induced_homogeneous]
  rfl

theorem induced_degree (A : V →ₗ[K] V) (p : ℕ) (y : S (K := K) (V := V))
    (hy : y ∈ homogeneous (K := K) (V := V) p) :
    induced A y ∈ homogeneous (K := K) (V := V) p := by
  obtain ⟨t, rfl⟩ := hy
  exact ⟨TensorDerivation.onPower A p t, (induced_homogeneous A p t).symm⟩

theorem contraction_pow (φ : Module.Dual K V) (v : V) (p : ℕ) :
    contraction φ ((_root_.SymmetricAlgebra.ι K V v) ^ p) =
      ((p : K) * φ v) • (_root_.SymmetricAlgebra.ι K V v) ^ (p - 1) := by
  classical
  have h := contraction_word φ p (fun _ => v)
  simpa [word, Specs.D05.M15.SymmetricDerivation.word, Finset.prod_const,
    Finset.card_erase_of_mem, ← Nat.cast_smul_eq_nsmul K, smul_smul] using h

theorem contraction_dividedPower [CharZero K] (φ : Module.Dual K V) (v : V) (p : ℕ) :
    contraction φ (Normalization.DividedPowers.dividedPower K (S (K := K) (V := V))
      (_root_.SymmetricAlgebra.ι K V v) (p + 1)) =
      φ v • Normalization.DividedPowers.dividedPower K (S (K := K) (V := V))
        (_root_.SymmetricAlgebra.ι K V v) p := by
  change contraction φ (((p + 1).factorial : K)⁻¹ • (_root_.SymmetricAlgebra.ι K V v) ^ (p + 1)) =
    φ v • ((p.factorial : K)⁻¹ • (_root_.SymmetricAlgebra.ι K V v) ^ p)
  rw [map_smul, contraction_pow, Nat.add_sub_cancel, smul_smul, smul_smul]
  congr 1
  have hp : (p.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  have hs : ((p + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero p)
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

end D05.M15.SymmetricDerivation
