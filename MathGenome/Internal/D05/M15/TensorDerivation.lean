import MathGenome.Internal.Specs.D05.M15.TensorDerivation
import MathGenome.Internal.D05.M15.TensorAlgebra
import MathGenome.Internal.D05.M15.TensorMaps

namespace D05.M15.TensorDerivation
open scoped TensorProduct
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev induced := @Specs.D05.M15.TensorDerivation.induced
noncomputable abbrev onPower := @Specs.D05.M15.TensorDerivation.onPower
abbrev IsDerivation := @Specs.D05.M15.TensorDerivation.IsDerivation

private theorem firstOrder_fst (A : V →ₗ[K] V) (x : _root_.TensorAlgebra K V) :
    (_root_.TensorAlgebra.lift K
      (Specs.D05.M15.TensorDerivation.firstOrderGenerator A) x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K (_root_.TensorAlgebra K V)
      (_root_.TensorAlgebra K V)).comp
      (_root_.TensorAlgebra.lift K
        (Specs.D05.M15.TensorDerivation.firstOrderGenerator A)) = AlgHom.id K _ := by
    apply _root_.TensorAlgebra.hom_ext
    ext v
    simp only [_root_.TensorAlgebra.lift_ι_apply, AlgHom.comp_apply, AlgHom.id_apply,
      LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rfl
  exact DFunLike.congr_fun h x

theorem induced_generator (A : V →ₗ[K] V) (v : V) :
    induced A (_root_.TensorAlgebra.ι K v) = _root_.TensorAlgebra.ι K (A v) := by
  change (_root_.TensorAlgebra.lift K
    (Specs.D05.M15.TensorDerivation.firstOrderGenerator A) (_root_.TensorAlgebra.ι K v)).snd = _
  rw [_root_.TensorAlgebra.lift_ι_apply]
  rfl

theorem induced_one (A : V →ₗ[K] V) : induced A 1 = 0 := by
  simp [induced, Specs.D05.M15.TensorDerivation.induced]

theorem induced_leibniz (A : V →ₗ[K] V) : IsDerivation (induced A) := by
  intro x y
  simp only [induced, Specs.D05.M15.TensorDerivation.induced, LinearMap.coe_mk,
    AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul, firstOrder_fst]
  change x * _ + _ * y = _ * y + x * _
  exact add_comm _ _

theorem induced_mul (A : V →ₗ[K] V) (x y : _root_.TensorAlgebra K V) :
    induced A (x * y) = induced A x * y + x * induced A y :=
  induced_leibniz A x y

theorem one_of_leibniz (D : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  simp only [one_mul, mul_one] at h
  exact (add_eq_left.mp h.symm)

theorem derivation_ext (D E : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D) (hE : IsDerivation E)
    (h : ∀ v, D (_root_.TensorAlgebra.ι K v) = E (_root_.TensorAlgebra.ι K v)) : D = E := by
  apply LinearMap.ext
  intro x
  induction x using _root_.TensorAlgebra.induction with
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
      one_of_leibniz D hD, one_of_leibniz E hE]
  | ι v => exact h v
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => rw [hD, hE, hx, hy]

theorem induced_unique (A : V →ₗ[K] V)
    (D : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D)
    (h : ∀ v, D (_root_.TensorAlgebra.ι K v) = _root_.TensorAlgebra.ι K (A v)) :
    D = induced A :=
  derivation_ext D (induced A) hD (induced_leibniz A)
    (fun v => (h v).trans (induced_generator A v).symm)

private theorem word_cons {p : ℕ} (v : V) (x : Fin p → V) :
    _root_.TensorAlgebra.tprod K V (p + 1) (Fin.cons v x) =
      _root_.TensorAlgebra.ι K v * _root_.TensorAlgebra.tprod K V p x := by
  simp [ _root_.TensorAlgebra.tprod_apply, List.ofFn_succ]

theorem induced_word (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V) :
    induced A (_root_.TensorAlgebra.tprod K V p x) =
      ∑ j : Fin p, _root_.TensorAlgebra.tprod K V p (Function.update x j (A (x j))) := by
  classical
  induction x using Fin.consInduction with
  | elim0 => simp [ _root_.TensorAlgebra.tprod_apply, induced_one]
  | cons v x ih =>
    rw [word_cons, induced_leibniz, induced_generator, ih, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update,
      word_cons, Finset.mul_sum]

theorem onPower_tprod (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V) :
    onPower A p (PiTensorProduct.tprod K x) =
      ∑ j : Fin p, PiTensorProduct.tprod K (Function.update x j (A (x j))) := by
  classical
  simp only [onPower, Specs.D05.M15.TensorDerivation.onPower,
    LinearMap.sum_apply, PiTensorProduct.map_tprod]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext i
  by_cases h : i = j
  · subst i; simp
  · simp [Function.update_of_ne h]

theorem induced_homogeneous (A : V →ₗ[K] V) (p : ℕ) (t : TensorPower K p V) :
    induced A (TensorPower.toTensorAlgebra t) =
      TensorPower.toTensorAlgebra (onPower A p t) := by
  have h : (induced A).comp (TensorPower.toTensorAlgebra (R := K) (n := p)) =
      TensorPower.toTensorAlgebra.comp (onPower A p) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      onPower_tprod, map_sum, TensorPower.toTensorAlgebra_tprod]
    exact induced_word A p x
  exact LinearMap.congr_fun h t

theorem slot_sum_multilinear (A : V →ₗ[K] V) (p : ℕ) :
    ∃ m : MultilinearMap K (fun _ : Fin p => V) (TensorPower K p V),
      ∀ x, m x = ∑ j : Fin p, PiTensorProduct.tprod K (Function.update x j (A (x j))) := by
  exact ⟨(onPower A p).compMultilinearMap (PiTensorProduct.tprod K), onPower_tprod A p⟩

theorem induced_add (A B : V →ₗ[K] V) : induced (A + B) = induced A + induced B := by
  symm
  apply induced_unique
  · intro x y
    simp only [LinearMap.add_apply, induced_mul, add_mul, mul_add]
    abel
  · intro v
    simp [induced_generator]

theorem induced_smul (a : K) (A : V →ₗ[K] V) : induced (a • A) = a • induced A := by
  symm
  apply induced_unique
  · intro x y
    simp only [LinearMap.smul_apply, induced_mul, smul_add,
      smul_mul_assoc, mul_smul_comm]
  · intro v
    simp [induced_generator]

/-- Cancellation of the mixed terms works in every characteristic. -/
theorem commutator_leibniz
    (D E : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V)
    (hD : IsDerivation D) (hE : IsDerivation E) :
    IsDerivation (D.comp E - E.comp D) := by
  change ∀ x y, D (x * y) = D x * y + x * D y at hD
  change ∀ x y, E (x * y) = E x * y + x * E y at hE
  intro x y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hD, hE,
    map_add, sub_mul, mul_sub]
  abel

theorem induced_commutator (A B : V →ₗ[K] V) :
    (induced A).comp (induced B) - (induced B).comp (induced A) =
      induced (A.comp B - B.comp A) := by
  apply induced_unique
  · exact commutator_leibniz _ _ (induced_leibniz A) (induced_leibniz B)
  · intro v
    simp [induced_generator]

theorem onPower_zero (A : V →ₗ[K] V) : onPower A 0 = 0 := by
  classical
  simp [onPower, Specs.D05.M15.TensorDerivation.onPower]

theorem induced_scalar (A : V →ₗ[K] V) (a : K) :
    induced A (algebraMap K (_root_.TensorAlgebra K V) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, induced_one, smul_zero]

theorem induced_finite_sum (A : V →ₗ[K] V) (s : Finset ℕ)
    (c : (p : ℕ) → TensorPower K p V) :
    induced A (∑ p ∈ s, TensorPower.toTensorAlgebra (c p)) =
      ∑ p ∈ s, TensorPower.toTensorAlgebra (onPower A p (c p)) := by
  simp only [map_sum, induced_homogeneous]

theorem unique_extension (A : V →ₗ[K] V) :
    ∃! D : _root_.TensorAlgebra K V →ₗ[K] _root_.TensorAlgebra K V,
      IsDerivation D ∧ ∀ v, D (_root_.TensorAlgebra.ι K v) = _root_.TensorAlgebra.ι K (A v) := by
  exact ⟨induced A, ⟨induced_leibniz A, induced_generator A⟩,
    fun D h => induced_unique A D h.1 h.2⟩

/-- The algebra homomorphism applies A in all slots and preserves the unit. -/
theorem homomorphism_word (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V) :
    _root_.TensorAlgebra.lift K ((_root_.TensorAlgebra.ι K).comp A)
      (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x)) =
        TensorPower.toTensorAlgebra (PiTensorProduct.tprod K (fun i => A (x i))) := by
  rw [D05.M15.TensorAlgebra.elementary_word, map_list_prod, List.map_ofFn,
    D05.M15.TensorAlgebra.elementary_word]
  simp only [Function.comp_def, _root_.TensorAlgebra.lift_ι_apply, LinearMap.comp_apply]

theorem homomorphism_one (A : V →ₗ[K] V) :
    _root_.TensorAlgebra.lift K ((_root_.TensorAlgebra.ι K).comp A) 1 = 1 :=
  map_one _

theorem derivation_ne_homomorphism (A : V →ₗ[K] V) :
    induced A ≠ (_root_.TensorAlgebra.lift K ((_root_.TensorAlgebra.ι K).comp A)).toLinearMap := by
  intro h
  have h1 := LinearMap.congr_fun h 1
  exact zero_ne_one (by simpa only [induced_one, AlgHom.toLinearMap_apply, map_one] using h1)

private theorem duality_pure (A : V →ₗ[K] V) (p : ℕ)
    (φ : Fin p → Module.Dual K V) (x : Fin p → V) :
    PiTensorProduct.dualDistrib (onPower A.dualMap p (PiTensorProduct.tprod K φ))
      (PiTensorProduct.tprod K x) =
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod K φ)
      (onPower A p (PiTensorProduct.tprod K x)) := by
  classical
  simp only [onPower_tprod, map_sum, LinearMap.sum_apply, PiTensorProduct.dualDistrib_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i = j
  · subst i; simp [LinearMap.dualMap_apply]
  · simp [Function.update_of_ne h]

/-- Tensor evaluation, without any finite-dimensional or perfection hypothesis. -/
theorem tensor_duality (A : V →ₗ[K] V) (p : ℕ)
    (α : TensorPower K p (Module.Dual K V)) (t : TensorPower K p V) :
    PiTensorProduct.dualDistrib (onPower A.dualMap p α) t =
      PiTensorProduct.dualDistrib α (onPower A p t) := by
  induction α using PiTensorProduct.induction_on with
  | smul_tprod r φ =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod s x =>
      simp only [map_smul, LinearMap.smul_apply, duality_pure]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add α β hα hβ => simp only [map_add, LinearMap.add_apply, hα, hβ]

theorem onPower_unique (A : V →ₗ[K] V) (p : ℕ)
    (L : TensorPower K p V →ₗ[K] TensorPower K p V)
    (hL : ∀ x : Fin p → V,
      L (PiTensorProduct.tprod K x) =
        ∑ j : Fin p, PiTensorProduct.tprod K (Function.update x j (A (x j)))) :
    L = onPower A p := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  exact (hL x).trans (onPower_tprod A p x).symm

theorem onPower_leibniz (A : V →ₗ[K] V) (p q : ℕ)
    (x : TensorPower K p V) (y : TensorPower K q V) :
    onPower A (p + q) (TensorPower.mulEquiv (x ⊗ₜ[K] y)) =
      TensorPower.mulEquiv (onPower A p x ⊗ₜ[K] y) +
        TensorPower.mulEquiv (x ⊗ₜ[K] onPower A q y) := by
  apply D05.M15.TensorAlgebra.homogeneous_injective (p + q)
  rw [← induced_homogeneous, ← D05.M15.TensorAlgebra.homogeneous_multiplication,
    induced_mul, map_add, ← D05.M15.TensorAlgebra.homogeneous_multiplication,
    ← D05.M15.TensorAlgebra.homogeneous_multiplication,
    induced_homogeneous, induced_homogeneous]

theorem onPower_commutator (A B : V →ₗ[K] V) (p : ℕ) (t : TensorPower K p V) :
    onPower A p (onPower B p t) - onPower B p (onPower A p t) =
      onPower (A.comp B - B.comp A) p t := by
  apply D05.M15.TensorAlgebra.homogeneous_injective p
  simpa only [map_sub, ← induced_homogeneous, LinearMap.sub_apply, LinearMap.comp_apply] using
    LinearMap.congr_fun (induced_commutator A B) (TensorPower.toTensorAlgebra t)

end D05.M15.TensorDerivation
