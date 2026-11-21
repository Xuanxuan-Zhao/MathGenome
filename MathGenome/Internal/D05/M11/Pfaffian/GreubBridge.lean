import MathGenome.Internal.Specs.D05.M11.Pfaffian.GreubBridge
import MathGenome.Internal.D05.M11.Pfaffian.Identities
import MathGenome.Internal.D05.M15.WedgeSign.Bivectors
import MathGenome.Internal.D05.M15.InnerTensor.ExteriorMetric
import Mathlib.Tactic.Ring

noncomputable section
namespace D05.M11.Pfaffian.GreubBridge
open scoped BigOperators
open Specs.D05.M11.Pfaffian.GreubBridge
open Specs.D05.M15.WedgeSign.BivectorNormalForm
local notation "vectorVolume" => Specs.D05.M11.Pfaffian.GreubBridge.volume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem metric_agreement : Specs.D05.M11.Pfaffian.GreubBridge.metric_agreement := by
  intro V _ _ _ p u v
  apply D05.M15.InnerTensor.ExteriorMetric.sesquilinear_unique p (exteriorMetric p)
  intro x y
  rw [D05.M15.InnerTensor.ExteriorMetric.bilinear_elementary]
  congr 1
  ext i j
  exact real_inner_comm _ _

/-- Our independent definition is the upstream metric-operator construction. -/
lemma phi_eq_metricOperator {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V)
    (z : ⋀[ℝ]^2 V) :
    phi b z = D05.M15.WedgeSign.Bivectors.metricOperator (metricIdentification b) z := rfl

lemma metricIdentification_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (x y : V) :
    metricIdentification b x y = inner ℝ x y := by
  have he : (metricIdentification b).toLinearMap = innerₗ V := by
    apply b.toBasis.ext
    intro i
    apply b.toBasis.ext
    intro j
    change ((b.toBasis.equiv b.toBasis.dualBasis (Equiv.refl _))
      (b.toBasis i)) (b.toBasis j) = inner ℝ (b i) (b j)
    rw [Module.Basis.equiv_apply]
    simp [OrthonormalBasis.inner_eq_ite]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

lemma phi_form {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V)
    (z : ⋀[ℝ]^2 V) (x y : V) :
    inner ℝ (phi b z x) y = form z (innerₗ V x) (innerₗ V y) := by
  rw [← metricIdentification_apply b]
  change metricIdentification b
    ((metricIdentification b).symm (form z (metricIdentification b x) ∘ₗ
      (metricIdentification b).toLinearMap)) y = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [LinearMap.comp_apply]
  congr 2 <;> ext t <;> exact metricIdentification_apply b _ _

theorem generator_formula : Specs.D05.M11.Pfaffian.GreubBridge.generator_formula := by
  intro V _ _ n b u v x
  apply ext_inner_right ℝ
  intro y
  rw [phi_form, D05.M15.WedgeSign.BivectorNormalForm.elementary]
  simp only [innerₗ_apply_apply, inner_sub_left, real_inner_smul_left, D05.firstInner]
  simp only [real_inner_comm]

lemma phi_injective {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) :
    Function.Injective (phi b) := by
  intro z t h
  let := Module.Finite.of_basis b.toBasis
  apply D05.M15.WedgeSign.BivectorNormalForm.ext_pairing
  intro f g
  obtain ⟨x, rfl⟩ := (metricIdentification b).surjective f
  obtain ⟨y, rfl⟩ := (metricIdentification b).surjective g
  have hf (v : V) : metricIdentification b v = innerₗ V v := by
    ext w; exact metricIdentification_apply b v w
  rw [hf, hf, ← phi_form, ← phi_form, h]

theorem generator_matrix : Specs.D05.M11.Pfaffian.GreubBridge.generator_matrix := by
  intro V _ _ n b i j r s
  classical
  rw [LinearMap.toMatrix_apply, generator_formula]
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul, OrthonormalBasis.coe_toBasis, D05.firstInner, OrthonormalBasis.inner_eq_ite]
  split_ifs <;> simp_all

/-- The form coordinates of Greub's negative bivector are -A. -/
lemma bivector_matrix {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) (hA : ∀ i j, A i j = -(A j i)) (i j) :
    matrix b.toBasis (bivector b A) i j = -(A i j) := by
  classical
  have hz : bivector b A =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (-(A i j)) • wedge (b i) (b j) := by
    unfold bivector
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    have hi : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext j; simp
    rw [hi]
    apply Finset.sum_congr rfl
    intro j _
    exact (neg_smul (A i j) (wedge (b i) (b j))).symm
  rw [hz]
  have hh := D05.M15.WedgeSign.BivectorNormalForm.matrix_entries
    b.toBasis (fun i j => -(A i j)) i j
  simp only [OrthonormalBasis.coe_toBasis] at hh
  rw [hh]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij]
  · have ha := hA i i
    have ha0 : A i i = 0 := by linarith
    simp [ha0]
  · simp [hji, not_lt_of_gt hji, hA i j]

/-- A coordinate of the operator is the transposed coordinate of its bivector form. -/
lemma phi_matrix {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (z : ⋀[ℝ]^2 V) (i j) :
    LinearMap.toMatrix b.toBasis b.toBasis (phi b z) i j = matrix b.toBasis z j i := by
  have he (k : Fin n) : innerₗ V (b k) = b.toBasis.coord k := by
    apply b.toBasis.ext
    intro l
    simp [OrthonormalBasis.inner_eq_ite]
  rw [LinearMap.toMatrix_apply]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis]
  rw [real_inner_comm, phi_form, he, he]
  rfl

theorem matrix_inverse : Specs.D05.M11.Pfaffian.GreubBridge.matrix_inverse := by
  intro V _ _ m b A hA
  ext i j
  rw [phi_matrix, bivector_matrix b A hA, ← hA]

theorem inverse_image : Specs.D05.M11.Pfaffian.GreubBridge.inverse_image := by
  intro V _ _ m b T hT z
  have hi : phi b (bivector b (LinearMap.toMatrix b.toBasis b.toBasis T)) = T := by
    apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    exact matrix_inverse b _ hT
  constructor
  · intro h
    exact phi_injective b (h.trans hi.symm)
  · intro h
    rw [h, hi]

/-- Transport the dual coordinate exterior algebra to the vector basis. -/
def coordinateToVector {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V) :
    Specs.D05.M11.Pfaffian.Covectors (2*m) →ₗ[ℝ] V :=
  ((Specs.D05.M11.Pfaffian.coordinateBasis (2*m)).equiv b.toBasis (Equiv.refl _)).toLinearMap

lemma coordinateToVector_basis {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V) (i) :
    coordinateToVector b (Specs.D05.M11.Pfaffian.coordinateBasis (2*m) i) = b i := by
  exact Module.Basis.equiv_apply _ _ _ _

lemma bivector_coe {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V)
    (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) :
    (bivector b A : ExteriorAlgebra ℝ V) =
      (-1 : ℝ) • ExteriorAlgebra.map (coordinateToVector b) (omega A) := by
  simp only [bivector, Submodule.coe_neg, Submodule.coe_sum, SetLike.val_smul,
    omega, Specs.D05.M11.Pfaffian.omega_value, map_sum, map_smul, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateToVector_basis,
    D05.M15.WedgeSign.Bivectors.wedge_coe, neg_one_smul]

lemma transported_volume {m : ℕ} (b : OrthonormalBasis (Fin (2*m)) ℝ V) :
    ExteriorAlgebra.map (coordinateToVector b) (D05.M11.Pfaffian.volume m) =
      (vectorVolume b : ExteriorAlgebra ℝ V) := by
  rw [D05.M11.Pfaffian.volume, Specs.D05.M11.Pfaffian.volume_value,
    ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  ext i
  exact coordinateToVector_basis b i

theorem divided_power_normalization :
    Specs.D05.M11.Pfaffian.GreubBridge.divided_power_normalization := by
  intro V _ _ m b A hA
  apply Subtype.ext
  change (Nat.factorial m : ℝ)⁻¹ • (bivector b A : ExteriorAlgebra ℝ V)^m = _
  rw [bivector_coe, smul_pow, ← map_pow]
  have hn := congrArg (ExteriorAlgebra.map (coordinateToVector b))
    (D05.M11.Pfaffian.wedge_normalization m A hA)
  rw [map_smul, map_smul, transported_volume] at hn
  rw [smul_comm, hn, smul_smul]
  rfl

theorem volume_unit : Specs.D05.M11.Pfaffian.GreubBridge.volume_unit := by
  intro V _ _ m b
  rw [Specs.D05.M11.Pfaffian.GreubBridge.volume, D05.M15.InnerTensor.ExteriorMetric.bilinear_elementary]
  have he : (fun i j : Fin (2*m) => innerₗ V (b i) (b j)) =
      (1 : Matrix (Fin (2*m)) (Fin (2*m)) ℝ) := by
    ext i j
    simp [OrthonormalBasis.inner_eq_ite, Matrix.one_apply]
  rw [he, Matrix.det_one]

theorem volume_norm : Specs.D05.M11.Pfaffian.GreubBridge.volume_norm := by
  intro V _ _ m b c
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [volume_unit b]
  ring

theorem scalar_bridge : Specs.D05.M11.Pfaffian.GreubBridge.scalar_bridge := by
  intro V _ _ m b A hA c _
  unfold greubPfaffian
  rw [divided_power_normalization b A hA]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [volume_unit b]
  ring

theorem square_bridge : Specs.D05.M11.Pfaffian.GreubBridge.square_bridge := by
  intro V _ _ m b A hA c hc
  have hp := (D05.M11.Pfaffian.Identities.identities m A A hA).2
  have hs : ((-1 : ℝ)^m)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
    simp
  have he : greubPfaffian b A c ^ 2 = c^2 * D05.M05.determinant A := by
    rw [scalar_bridge b A hA c hc, mul_pow, mul_pow, hs, mul_one, hp]
  exact ⟨he, by rw [volume_norm]; exact he⟩

end D05.M11.Pfaffian.GreubBridge
