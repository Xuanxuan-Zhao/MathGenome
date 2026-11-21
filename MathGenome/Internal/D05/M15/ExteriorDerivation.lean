import MathGenome.Internal.Specs.D05.M15.ExteriorDerivation
import MathGenome.Internal.D05.M15.TensorDerivation
import MathGenome.Internal.D05.M15.Exterior
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M15.WedgeSign
import MathGenome.Internal.D05.M04.Trace

noncomputable section
namespace D05.M15.ExteriorDerivation
open Specs.D05.M15.ExteriorDerivation
universe u v w
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev induced := @Specs.D05.M15.ExteriorDerivation.induced
abbrev IsDerivation := @Specs.D05.M15.ExteriorDerivation.IsDerivation

private theorem firstOrder_fst (A : V →ₗ[K] V) (x : _root_.ExteriorAlgebra K V) :
    (firstOrderLift A x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K (_root_.ExteriorAlgebra K V)
      (_root_.ExteriorAlgebra K V)).comp (firstOrderLift A) = AlgHom.id K _ := by
    apply _root_.ExteriorAlgebra.hom_ext
    ext v
    simp only [firstOrderLift, _root_.ExteriorAlgebra.lift_ι_apply, AlgHom.comp_apply,
      AlgHom.id_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rfl
  exact DFunLike.congr_fun h x

theorem induced_generator (A : V →ₗ[K] V) (v : V) :
    induced A (_root_.ExteriorAlgebra.ι K v) = _root_.ExteriorAlgebra.ι K (A v) := by
  change (firstOrderLift A (_root_.ExteriorAlgebra.ι K v)).snd = _
  rw [firstOrderLift, _root_.ExteriorAlgebra.lift_ι_apply]
  rfl

theorem induced_one (A : V →ₗ[K] V) : induced A 1 = 0 := by
  change (firstOrderLift A 1).snd = 0
  simp

theorem induced_leibniz (A : V →ₗ[K] V) : IsDerivation (induced A) := by
  intro x y
  change (firstOrderLift A (x * y)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul, firstOrder_fst, firstOrder_fst]
  exact add_comm _ _

theorem induced_mul (A : V →ₗ[K] V) (x y : _root_.ExteriorAlgebra K V) :
    induced A (x * y) = induced A x * y + x * induced A y := induced_leibniz A x y

theorem one_of_leibniz (D : _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V)
    (hD : IsDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  simp only [one_mul, mul_one] at h
  exact add_eq_left.mp h.symm

theorem induced_scalar (A : V →ₗ[K] V) (a : K) :
    induced A (algebraMap K (_root_.ExteriorAlgebra K V) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, induced_one, smul_zero]

theorem derivation_ext (D E : _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V)
    (hD : IsDerivation D) (hE : IsDerivation E)
    (h : ∀ v, D (_root_.ExteriorAlgebra.ι K v) = E (_root_.ExteriorAlgebra.ι K v)) : D = E := by
  apply LinearMap.ext
  intro x
  induction x using _root_.ExteriorAlgebra.induction with
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
      one_of_leibniz D hD, one_of_leibniz E hE]
  | ι v => exact h v
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => rw [hD, hE, hx, hy]

theorem unique_extension (A : V →ₗ[K] V) :
    ∃! D : _root_.ExteriorAlgebra K V →ₗ[K] _root_.ExteriorAlgebra K V,
      IsDerivation D ∧ ∀ v, D (_root_.ExteriorAlgebra.ι K v) = _root_.ExteriorAlgebra.ι K (A v) := by
  refine ⟨induced A, ⟨induced_leibniz A, induced_generator A⟩, ?_⟩
  intro D hD
  exact derivation_ext D (induced A) hD.1 (induced_leibniz A)
    (fun v => (hD.2 v).trans (induced_generator A v).symm)

theorem square_derivative : Specs.D05.M15.ExteriorDerivation.square_derivative := by
  intro K V _ _ _ A v
  rw [D05.M15.TensorDerivation.induced_mul,
    D05.M15.TensorDerivation.induced_generator]

theorem quotient_descent (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V) :
    induced A (_root_.TensorAlgebra.toExterior t) =
      _root_.TensorAlgebra.toExterior (D05.M15.TensorDerivation.induced A t) := by
  induction t using _root_.TensorAlgebra.induction with
  | algebraMap a =>
    rw [AlgHom.commutes, induced_scalar, D05.M15.TensorDerivation.induced_scalar, map_zero]
  | ι v =>
    rw [_root_.TensorAlgebra.toExterior_ι, induced_generator,
      D05.M15.TensorDerivation.induced_generator, _root_.TensorAlgebra.toExterior_ι]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy =>
    rw [map_mul, induced_mul, D05.M15.TensorDerivation.induced_mul,
      map_add, map_mul, map_mul, hx, hy]

theorem ideal_preserved (A : V →ₗ[K] V) (t : _root_.TensorAlgebra K V)
    (ht : t ∈ D05.M15.Exterior.definingIdeal K V) :
    D05.M15.TensorDerivation.induced A t ∈ D05.M15.Exterior.definingIdeal K V := by
  apply (D05.M15.Exterior.quotient_kernel _).mp
  rw [← quotient_descent, (D05.M15.Exterior.quotient_kernel t).mpr ht, map_zero]

private theorem quotient_word (p : ℕ) (x : Fin p → V) :
    _root_.TensorAlgebra.toExterior (_root_.TensorAlgebra.tprod K V p x) =
      _root_.ExteriorAlgebra.ιMulti K p x := by
  rw [_root_.TensorAlgebra.tprod_apply, _root_.ExteriorAlgebra.ιMulti_apply,
    map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, _root_.TensorAlgebra.toExterior_ι]

theorem induced_word (A : V →ₗ[K] V) (p : ℕ) (x : Fin p → V) :
    induced A (_root_.ExteriorAlgebra.ιMulti K p x) =
      ∑ j : Fin p, _root_.ExteriorAlgebra.ιMulti K p (Function.update x j (A (x j))) := by
  rw [← quotient_word, quotient_descent, D05.M15.TensorDerivation.induced_word, map_sum]
  simp only [quotient_word]

theorem degree_preserved (A : V →ₗ[K] V) (p : ℕ) (x : _root_.ExteriorAlgebra K V)
    (hx : x ∈ ⋀[K]^p V) : induced A x ∈ ⋀[K]^p V := by
  rw [← _root_.ExteriorAlgebra.ιMulti_span_fixedDegree K p] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨y, rfl⟩
    rw [induced_word]
    exact Submodule.sum_mem _ (fun j _ => (exteriorPower.ιMulti K p _).property)
  | zero => simpa only [map_zero] using (⋀[K]^p V).zero_mem
  | add y z _ _ hy hz => simpa only [map_add] using (⋀[K]^p V).add_mem hy hz
  | smul a y _ hy => simpa only [map_smul] using (⋀[K]^p V).smul_mem a hy

theorem power_restriction (A : V →ₗ[K] V) (p : ℕ) :
    ∃! D : (⋀[K]^p V) →ₗ[K] (⋀[K]^p V),
      ∀ x, (D x : _root_.ExteriorAlgebra K V) = induced A x := by
  refine ⟨((induced A).comp (⋀[K]^p V).subtype).codRestrict (⋀[K]^p V)
    (fun x => degree_preserved A p x x.property), fun _ => rfl, ?_⟩
  intro D hD
  apply LinearMap.ext
  intro x
  exact Subtype.ext (hD x)

theorem degree_zero (A : V →ₗ[K] V) (x : ⋀[K]^0 V) : induced A x = 0 := by
  have hx := (D05.M15.Exterior.degree_zero (K := K) (V := V))
  rcases hx with ⟨e, _, he⟩
  have hx : (x : _root_.ExteriorAlgebra K V) = algebraMap K _ (e x) := by
    simpa using he (e x)
  rw [hx, induced_scalar]

theorem homomorphism_one (A : V →ₗ[K] V) : _root_.ExteriorAlgebra.map A 1 = 1 := map_one _

/-- Only the diagonal coordinate survives when one entry of a full basis wedge changes. -/
theorem basis_wedge_update (n : ℕ) (b : Module.Basis (Fin n) K V)
    (v : V) (j : Fin n) :
    _root_.ExteriorAlgebra.ιMulti K n (Function.update b j v) =
      b.repr v j • _root_.ExteriorAlgebra.ιMulti K n b := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  rw [(_root_.ExteriorAlgebra.ιMulti K n).map_update_sum]
  simp only [(_root_.ExteriorAlgebra.ιMulti K n).map_update_smul]
  rw [Finset.sum_eq_single j]
  · rw [Function.update_eq_self]
  · intro i _ hij
    rw [(_root_.ExteriorAlgebra.ιMulti K n).map_update_self b (Ne.symm hij), smul_zero]
  · simp

theorem top_basis_trace (n : ℕ) (b : Module.Basis (Fin n) K V) (A : V →ₗ[K] V) :
    induced A (_root_.ExteriorAlgebra.ιMulti K n b) =
      (∑ j : Fin n, b.repr (A (b j)) j) • _root_.ExteriorAlgebra.ιMulti K n b := by
  rw [induced_word, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun j _ => basis_wedge_update n b (A (b j)) j)

/-- Full-degree alternating maps are determined by their value on a basis. -/
theorem top_alternating_ext {H : Type*} [AddCommGroup H] [Module K H]
    {n : ℕ} (b : Module.Basis (Fin n) K V)
    {f g : AlternatingMap K V H (Fin n)} (h : f b = g b) : f = g := by
  apply b.ext_alternating
  intro i hi
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
  change f (b ∘ σ) = g (b ∘ σ)
  rw [f.map_perm, g.map_perm, h]

theorem top_trace [FiniteDimensional K V] (A : V →ₗ[K] V)
    (x : ⋀[K]^(Module.finrank K V) V) :
    induced A x = LinearMap.trace K V A • (x : _root_.ExteriorAlgebra K V) := by
  let b := Module.finBasis K V
  have h : (induced A).comp (⋀[K]^(Module.finrank K V) V).subtype =
      LinearMap.trace K V A • (⋀[K]^(Module.finrank K V) V).subtype := by
    apply exteriorPower.linearMap_ext
    apply top_alternating_ext b
    change induced A (_root_.ExteriorAlgebra.ιMulti K _ b) =
      LinearMap.trace K V A • _root_.ExteriorAlgebra.ιMulti K _ b
    rw [LinearMap.trace_eq_matrix_trace K b A]
    simpa only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply] using top_basis_trace _ b A
  exact LinearMap.congr_fun h x

theorem top_determinant [FiniteDimensional K V] (A : V →ₗ[K] V)
    (x : ⋀[K]^(Module.finrank K V) V) :
    _root_.ExteriorAlgebra.map A x = LinearMap.det A • (x : _root_.ExteriorAlgebra K V) := by
  let b := Module.finBasis K V
  let ω : AlternatingMap K V (_root_.ExteriorAlgebra K V) (Fin (Module.finrank K V)) :=
    _root_.ExteriorAlgebra.ιMulti K (Module.finrank K V)
  have hω : ω = b.det.smulRight (ω b) := by
    apply top_alternating_ext b
    simp only [AlternatingMap.smulRight_apply, b.det_self, one_smul]
  have h : (_root_.ExteriorAlgebra.map A).toLinearMap.comp
      (⋀[K]^(Module.finrank K V) V).subtype =
      LinearMap.det A • (⋀[K]^(Module.finrank K V) V).subtype := by
    apply exteriorPower.linearMap_ext
    apply top_alternating_ext b
    change _root_.ExteriorAlgebra.map A (ω b) = LinearMap.det A • ω b
    rw [_root_.ExteriorAlgebra.map_apply_ιMulti]
    change ω (A ∘ b) = _
    conv_lhs => rw [hω]
    simp only [AlternatingMap.smulRight_apply, b.det_comp, b.det_self, mul_one]
  exact LinearMap.congr_fun h x

theorem naturality : Specs.D05.M15.ExteriorDerivation.naturality := by
  intro K V W _ _ _ _ _ A B f hf x
  induction x using _root_.ExteriorAlgebra.induction with
  | algebraMap a => rw [AlgHom.commutes, induced_scalar, induced_scalar, map_zero]
  | ι v =>
    rw [_root_.ExteriorAlgebra.map_apply_ι, induced_generator, induced_generator,
      _root_.ExteriorAlgebra.map_apply_ι]
    exact congrArg (_root_.ExteriorAlgebra.ι K) (LinearMap.congr_fun hf v)
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, induced_mul, map_add, hx, hy]

theorem tensor_naturality : Specs.D05.M15.ExteriorDerivation.tensor_naturality := by
  intro K V W _ _ _ _ _ A B f hf x
  induction x using _root_.TensorAlgebra.induction with
  | algebraMap a =>
    rw [AlgHom.commutes, D05.M15.TensorDerivation.induced_scalar,
      D05.M15.TensorDerivation.induced_scalar, map_zero]
  | ι v =>
    rw [D05.M15.WedgeSign.tensor_map_generator, D05.M15.TensorDerivation.induced_generator,
      D05.M15.TensorDerivation.induced_generator, D05.M15.WedgeSign.tensor_map_generator]
    exact congrArg (_root_.TensorAlgebra.ι K) (LinearMap.congr_fun hf v)
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy =>
    simp only [map_mul, D05.M15.TensorDerivation.induced_mul, map_add, hx, hy]

noncomputable abbrev symmetricInduced := @Specs.D05.M15.ExteriorDerivation.symmetricInduced

private theorem symmetricFirstOrder_fst (A : V →ₗ[K] V) (x : SymmetricAlgebra K V) :
    (SymmetricAlgebra.lift (symmetricFirstOrderGenerator A) x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K (SymmetricAlgebra K V) (SymmetricAlgebra K V)).comp
      (SymmetricAlgebra.lift (symmetricFirstOrderGenerator A)) = AlgHom.id K _ := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    change (SymmetricAlgebra.lift (symmetricFirstOrderGenerator A)
      (SymmetricAlgebra.ι K V v)).fst = SymmetricAlgebra.ι K V v
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  exact DFunLike.congr_fun h x

theorem symmetric_generator (A : V →ₗ[K] V) (v : V) :
    symmetricInduced A (SymmetricAlgebra.ι K V v) = SymmetricAlgebra.ι K V (A v) := by
  change (SymmetricAlgebra.lift (symmetricFirstOrderGenerator A) (SymmetricAlgebra.ι K V v)).snd = _
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

theorem symmetric_leibniz (A : V →ₗ[K] V) (x y : SymmetricAlgebra K V) :
    symmetricInduced A (x * y) = symmetricInduced A x * y + x * symmetricInduced A y := by
  change (SymmetricAlgebra.lift (symmetricFirstOrderGenerator A) (x * y)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul, symmetricFirstOrder_fst, symmetricFirstOrder_fst]
  exact add_comm _ _

theorem symmetric_scalar (A : V →ₗ[K] V) (a : K) :
    symmetricInduced A (algebraMap K (SymmetricAlgebra K V) a) = 0 := by
  change (SymmetricAlgebra.lift (symmetricFirstOrderGenerator A)
    (algebraMap K (SymmetricAlgebra K V) a)).snd = 0
  rw [AlgHom.commutes]
  rfl

theorem symmetric_naturality : Specs.D05.M15.ExteriorDerivation.symmetric_naturality := by
  intro K V W _ _ _ _ _ A B f hf x
  induction x using SymmetricAlgebra.induction with
  | algebraMap a => rw [AlgHom.commutes, symmetric_scalar, symmetric_scalar, map_zero]
  | ι v =>
    rw [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, symmetric_generator,
      symmetric_generator, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
    exact congrArg (SymmetricAlgebra.ι K W) (LinearMap.congr_fun hf v)
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, symmetric_leibniz, map_add, hx, hy]

end D05.M15.ExteriorDerivation
