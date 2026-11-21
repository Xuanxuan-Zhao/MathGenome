import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsConjugations
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

open scoped TensorProduct
open Complex
universe u v
namespace LieAlgebrasAndRepresentations.RealForms

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

@[simp] theorem complexifyMap_tmul (S : LieSubalgebra ℝ L) (a : ℂ) (x : S) :
    complexifyMap S (a ⊗ₜ[ℝ] x) = a • (x : L) := rfl

variable (V : Type u) [AddCommGroup V] [Module ℝ V]
noncomputable def tensorRe : ℂ ⊗[ℝ] V →ₗ[ℝ] V :=
  TensorProduct.lift ((LinearMap.lsmul ℝ V).comp Complex.reLm)
noncomputable def tensorIm : ℂ ⊗[ℝ] V →ₗ[ℝ] V :=
  TensorProduct.lift ((LinearMap.lsmul ℝ V).comp Complex.imLm)

@[simp] theorem tensorRe_tmul (a : ℂ) (x : V) : tensorRe V (a ⊗ₜ[ℝ] x) = a.re • x := rfl
@[simp] theorem tensorIm_tmul (a : ℂ) (x : V) : tensorIm V (a ⊗ₜ[ℝ] x) = a.im • x := rfl

theorem tensor_decomposition (z : ℂ ⊗[ℝ] V) :
    (1 : ℂ) ⊗ₜ[ℝ] tensorRe V z + I ⊗ₜ[ℝ] tensorIm V z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [tensorRe_tmul, tensorIm_tmul, ← TensorProduct.smul_tmul]
    rw [← TensorProduct.add_tmul]
    congr 1
    simp [Complex.real_smul, Complex.re_add_im]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add]
    rw [add_add_add_comm, hx, hy]

variable {V}
theorem one_tmul_injective : Function.Injective (fun x : V => (1 : ℂ) ⊗ₜ[ℝ] x) := by
  intro x y h
  simpa using congrArg (tensorRe V) h

variable (σ : Conjugation L)

/-- The displayed real and imaginary parts in the source are fixed vectors. -/
theorem fixed_decomposition (x : L) :
    ∃ u v : σ.fixed, (u : L) + I • (v : L) = x := by
  let : StarAddMonoid L :=
    { star := σ.map
      star_involutive := σ.involutive
      star_add := map_add σ.map }
  let : StarModule ℂ L := ⟨σ.antilinear⟩
  refine ⟨⟨realPart x, ?_⟩, ⟨imaginaryPart x, ?_⟩, ?_⟩
  · exact (realPart x).property.star_eq
  · exact (imaginaryPart x).property.star_eq
  · exact realPart_add_I_smul_imaginaryPart x

/-- The sum of the fixed space and its imaginary multiple is direct. -/
theorem fixed_sum_eq_zero (x y : σ.fixed) (h : (x : L) + I • (y : L) = 0) :
    x = 0 ∧ y = 0 := by
  have hx : σ.map (x : L) = x := x.property
  have hy : σ.map (y : L) = y := y.property
  have h' := congrArg σ.map h
  simp only [map_add, σ.antilinear, hx, hy, Complex.star_def, Complex.conj_I,
    neg_smul, map_zero] at h'
  have h2 : (2 : ℂ) • (y : L) = 0 := by
    have hi : I • (y : L) + I • (y : L) = 0 := by
      calc
        _ = ((x : L) + I • (y : L)) - ((x : L) + -(I • (y : L))) := by module
        _ = 0 := by rw [h, h']; simp
    have := congrArg (fun z : L => -I • z) hi
    simpa [smul_add, smul_smul, two_smul ℂ] using this
  have hy0 : (y : L) = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  constructor
  · apply Subtype.ext
    simpa [hy0] using h
  · exact Subtype.ext hy0

theorem fixed_isRealForm : IsRealForm σ.fixed := by
  constructor
  · apply (complexifyMap σ.fixed).toLinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    have hz : complexifyMap σ.fixed z = 0 := hz
    have hd := tensor_decomposition σ.fixed z
    have he : (tensorRe σ.fixed z : L) + I • (tensorIm σ.fixed z : L) = 0 := by
      simpa using (congrArg (complexifyMap σ.fixed) hd).trans hz
    obtain ⟨hr, hi⟩ := fixed_sum_eq_zero σ _ _ he
    rw [hr, hi, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero] at hd
    exact hd.symm
  · intro x
    obtain ⟨a, b, h⟩ := fixed_decomposition σ x
    exact ⟨1 ⊗ₜ[ℝ] a + I ⊗ₜ[ℝ] b, by simpa using h⟩


/-- The natural Lie isomorphism is evaluation on pure tensors. -/
theorem fixed_complexification :
    ∃ e : (ℂ ⊗[ℝ] σ.fixed) ≃ₗ⁅ℂ⁆ L,
      ∀ a x, e (a ⊗ₜ[ℝ] x) = a • (x : L) := by
  exact ⟨LieEquiv.ofBijective (complexifyMap σ.fixed) (fixed_isRealForm σ),
    fun _ _ => rfl⟩

section Coefficients
variable (A : Type u) [LieRing A] [LieAlgebra ℝ A]

@[simp] theorem coefficientConjugationMap_tmul (a : ℂ) (x : A) :
    coefficientConjugationMap A (a ⊗ₜ[ℝ] x) = star a ⊗ₜ[ℝ] x := rfl

theorem coefficient_antilinear (a : ℂ) (z : ℂ ⊗[ℝ] A) :
    coefficientConjugationMap A (a • z) = star a • coefficientConjugationMap A z := by
  induction z using TensorProduct.inductionOn with
  | tmul b x => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp_all [smul_add]

theorem coefficient_involutive : Function.Involutive (coefficientConjugationMap A) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp_all

/-- Coefficient conjugation is itself a conjugation of a complex Lie algebra. -/
def coefficientConjugation : Conjugation (ℂ ⊗[ℝ] A) where
  map := coefficientConjugationMap A
  antilinear := coefficient_antilinear A
  involutive := coefficient_involutive A

theorem tensorIm_coefficientConjugation (z : ℂ ⊗[ℝ] A) :
    tensorIm A (coefficientConjugationMap A z) = -tensorIm A z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp_all [add_comm]

/-- Coefficient conjugation fixes exactly the original real algebra. -/
theorem coefficient_fixed_iff (z : ℂ ⊗[ℝ] A) :
    coefficientConjugationMap A z = z ↔ ∃ x : A, (1 : ℂ) ⊗ₜ[ℝ] x = z := by
  constructor
  · intro h
    have hi : tensorIm A z = 0 := by
      have hneg := tensorIm_coefficientConjugation A z
      rw [h] at hneg
      have h2 : (2 : ℝ) • tensorIm A z = 0 := by
        simpa [two_smul] using (eq_neg_iff_add_eq_zero.mp hneg)
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    refine ⟨tensorRe A z, ?_⟩
    simpa [hi] using tensor_decomposition A z
  · rintro ⟨x, rfl⟩
    simp

/-- A real Lie algebra is naturally isomorphic to the coefficient-fixed algebra. -/
theorem coefficient_fixed_equiv :
    ∃ e : A ≃ₗ⁅ℝ⁆ (coefficientConjugation A).fixed,
      ∀ x, (e x : ℂ ⊗[ℝ] A) = (1 : ℂ) ⊗ₜ[ℝ] x := by
  let f : A →ₗ⁅ℝ⁆ (coefficientConjugation A).fixed :=
    { toFun := fun x => ⟨1 ⊗ₜ[ℝ] x, by simp [Conjugation.fixed, coefficientConjugation]⟩
      map_add' := by intros; apply Subtype.ext; exact TensorProduct.tmul_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact TensorProduct.tmul_smul _ _ _
      map_lie' := by intros; apply Subtype.ext; simp [LieAlgebra.ExtendScalars.bracket_tmul] }
  refine ⟨LieEquiv.ofBijective f ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro x y h
    exact one_tmul_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨x, hx⟩ := (coefficient_fixed_iff A z).mp z.property
    exact ⟨x, Subtype.ext hx⟩
end Coefficients


variable {H : Type v} [LieRing H] [LieAlgebra ℂ H]

/-- Transport along a complex Lie isomorphism. -/
def Conjugation.transport (τ : Conjugation L) (e : L ≃ₗ⁅ℂ⁆ H) : Conjugation H where
  map :=
    { toLinearMap := (e.toLinearEquiv.restrictScalars ℝ).toLinearMap.comp
        (τ.map.toLinearMap.comp (e.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap)
      map_lie' := by intro x y; simp [e.map_lie, e.symm.map_lie, τ.map.map_lie] }
  antilinear a x := by
    change e (τ.map (e.symm (a • x))) = star a • e (τ.map (e.symm x))
    rw [map_smul, τ.antilinear, map_smul]
  involutive x := by
    change e (τ.map (e.symm (e (τ.map (e.symm x))))) = x
    rw [e.symm_apply_apply, τ.involutive, e.apply_symm_apply]

/-- Every real form is recovered from coefficient conjugation under evaluation. -/
theorem real_form_converse (S : LieSubalgebra ℝ L) (hS : IsRealForm S) :
    ∃ τ : Conjugation L, τ.fixed = S ∧
      ∃ e : (ℂ ⊗[ℝ] S) ≃ₗ⁅ℂ⁆ L,
        (∀ a x, e (a ⊗ₜ[ℝ] x) = a • (x : L)) ∧
        ∀ z, τ.map (e z) = e (coefficientConjugationMap S z) := by
  let e := LieEquiv.ofBijective (complexifyMap S) hS
  let τ := (coefficientConjugation S).transport e
  have he (a : ℂ) (x : S) : e (a ⊗ₜ[ℝ] x) = a • (x : L) := rfl
  have ht (z : ℂ ⊗[ℝ] S) : τ.map (e z) = e (coefficientConjugationMap S z) := by
    change e (coefficientConjugationMap S (e.symm (e z))) = _
    rw [e.symm_apply_apply]
  refine ⟨τ, ?_, e, he, ht⟩
  ext x
  change τ.map x = x ↔ x ∈ S
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := e.surjective x
    change e z = x at hz
    subst x
    rw [ht] at hx
    obtain ⟨a, ha⟩ := (coefficient_fixed_iff S z).mp (e.injective hx)
    rw [← ha, he, one_smul]
    exact a.property
  · intro hx
    let a : S := ⟨x, hx⟩
    have : e (1 ⊗ₜ[ℝ] a) = x := by simp [he, a]
    rw [← this, ht]
    simp

section BaseChange
variable {A : Type u} {B : Type v} [LieRing A] [LieAlgebra ℝ A]
  [LieRing B] [LieAlgebra ℝ B]

/-- Scalar extension of a real Lie isomorphism. -/
noncomputable def complexifyEquiv (e : A ≃ₗ⁅ℝ⁆ B) :
    (ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] B) :=
  { LinearEquiv.baseChange ℝ ℂ A B e.toLinearEquiv with
    map_lie' := by
      intro x y
      induction x using TensorProduct.inductionOn with
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | tmul b y => simp [LieAlgebra.ExtendScalars.bracket_tmul, e.map_lie]
        | add y z hy hz => simp_all [lie_add]
      | add x y hx hy => simp_all [add_lie] }

@[simp] theorem complexifyEquiv_tmul (e : A ≃ₗ⁅ℝ⁆ B) (a : ℂ) (x : A) :
    complexifyEquiv e (a ⊗ₜ[ℝ] x) = a ⊗ₜ[ℝ] e x := rfl
end BaseChange


variable (τ : Conjugation H)

/-- Agreement on the real form forces compatibility with conjugation. -/
theorem intertwines_of_restriction (e : σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed)
    (a : L ≃ₗ⁅ℂ⁆ H) (h : ∀ x : σ.fixed, a (x : L) = (e x : H)) :
    Intertwines σ τ a := by
  intro x
  obtain ⟨u, v, huv⟩ := fixed_decomposition σ x
  have hu : σ.map (u : L) = u := u.property
  have hv : σ.map (v : L) = v := v.property
  have heu : τ.map (e u : H) = e u := (e u).property
  have hev : τ.map (e v : H) = e v := (e v).property
  rw [← huv, map_add, map_smul, h, h, map_add, τ.antilinear, heu, hev,
    map_add, σ.antilinear, hu, hv, map_add, map_smul, h, h]

/-- Each real isomorphism extends uniquely, and the extension intertwines conjugations. -/
theorem extend_real_isomorphism (e : σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed) :
    ∃! a : L ≃ₗ⁅ℂ⁆ H,
      (∀ x : σ.fixed, a (x : L) = (e x : H)) ∧ Intertwines σ τ a := by
  obtain ⟨Es, hs⟩ := fixed_complexification σ
  obtain ⟨Et, ht⟩ := fixed_complexification τ
  let a := Es.symm.trans ((complexifyEquiv e).trans Et)
  have hEs (x : σ.fixed) : Es.symm (x : L) = 1 ⊗ₜ[ℝ] x := by
    apply Es.toLinearEquiv.symm_apply_eq.mpr
    simpa using (hs 1 x).symm
  have ha (x : σ.fixed) : a (x : L) = (e x : H) := by
    change Et (complexifyEquiv e (Es.symm (x : L))) = _
    rw [hEs, complexifyEquiv_tmul, ht, one_smul]
  refine ⟨a, ⟨ha, intertwines_of_restriction σ τ e a ha⟩, ?_⟩
  intro b hb
  apply LieEquiv.ext
  intro x
  obtain ⟨u, v, huv⟩ := fixed_decomposition σ x
  rw [← huv, map_add, map_smul, map_add, map_smul, ha, ha, hb.1, hb.1]

/-- An intertwining complex isomorphism restricts to a real Lie isomorphism. -/
theorem restrict_complex_isomorphism (a : L ≃ₗ⁅ℂ⁆ H) (h : Intertwines σ τ a) :
    ∃ e : σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed,
      ∀ x : σ.fixed, (e x : H) = a (x : L) := by
  let f : σ.fixed →ₗ⁅ℝ⁆ τ.fixed :=
    { toFun := fun x => ⟨a (x : L), by
        change τ.map (a (x : L)) = a (x : L)
        rw [h, x.property]⟩
      map_add' := by intros; apply Subtype.ext; exact map_add a _ _
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact (a.toLinearEquiv.restrictScalars ℝ).map_smul r (x : L)
      map_lie' := by intros; apply Subtype.ext; exact a.map_lie _ _ }
  refine ⟨LieEquiv.ofBijective f ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro x y hxy
    apply Subtype.ext
    exact a.injective (congrArg Subtype.val hxy)
  · intro y
    have hx : σ.map (a.symm (y : H)) = a.symm (y : H) := by
      apply a.injective
      change a (σ.map (a.symm (y : H))) = a (a.symm (y : H))
      rw [← h, a.apply_symm_apply, y.property]
    refine ⟨⟨a.symm (y : H), hx⟩, ?_⟩
    apply Subtype.ext
    exact a.apply_symm_apply _

/-- Intrinsic isomorphism of forms is equivalent to intertwining of conjugations. -/
theorem forms_isomorphic_iff :
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed) ↔
      ∃ a : L ≃ₗ⁅ℂ⁆ H, Intertwines σ τ a := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨a, ha, _⟩ := extend_real_isomorphism σ τ e
    exact ⟨a, ha.2⟩
  · rintro ⟨a, ha⟩
    obtain ⟨e, _⟩ := restrict_complex_isomorphism σ τ a ha
    exact ⟨e⟩


/-- The source's explicit decomposition, before multiplication of the second part by `I`. -/
theorem fixed_parts_formula (x : L) :
    ∃ u v : σ.fixed,
      (u : L) = (2 : ℂ)⁻¹ • (x + σ.map x) ∧
      (v : L) = ((2 : ℂ) * I)⁻¹ • (x - σ.map x) ∧
      (u : L) + I • (v : L) = x := by
  let : StarAddMonoid L :=
    { star := σ.map
      star_involutive := σ.involutive
      star_add := map_add σ.map }
  let : StarModule ℂ L := ⟨σ.antilinear⟩
  refine ⟨⟨realPart x, (realPart x).property.star_eq⟩,
    ⟨imaginaryPart x, (imaginaryPart x).property.star_eq⟩, ?_, ?_, ?_⟩
  · have hr : (realPart x : L) = (2 : ℝ)⁻¹ • (x + σ.map x) := realPart_apply_coe x
    simpa [← Complex.coe_smul, Complex.ofReal_inv] using hr
  · have hi : (imaginaryPart x : L) = -I • (2 : ℝ)⁻¹ • (x - σ.map x) :=
      imaginaryPart_apply_coe x
    simpa [← Complex.coe_smul, Complex.ofReal_inv, smul_smul, mul_inv_rev, Complex.inv_I]
      using hi
  · exact realPart_add_I_smul_imaginaryPart x

/-- Complete coefficient-conjugation construction, with an independent existence type. -/
theorem coefficient_converse (A : Type u) [LieRing A] [LieAlgebra ℝ A] :
    ∃ ρ : Conjugation (ℂ ⊗[ℝ] A),
      ρ.map = coefficientConjugationMap A ∧
      ∃ e : A ≃ₗ⁅ℝ⁆ ρ.fixed,
        ∀ x, (e x : ℂ ⊗[ℝ] A) = (1 : ℂ) ⊗ₜ[ℝ] x := by
  exact ⟨coefficientConjugation A, rfl, coefficient_fixed_equiv A⟩

theorem Conjugation.ext_map {ρ κ : Conjugation L} (h : ρ.map = κ.map) : ρ = κ := by
  cases ρ
  cases κ
  cases h
  rfl

/-- A conjugation is determined by its embedded real form. -/
theorem conjugation_eq_of_fixed_eq (ρ κ : Conjugation L) (h : ρ.fixed = κ.fixed) :
    ρ = κ := by
  apply Conjugation.ext_map
  apply LieHom.ext
  intro x
  obtain ⟨u, v, huv⟩ := fixed_decomposition ρ x
  have hu : ρ.map (u : L) = u := u.property
  have hv : ρ.map (v : L) = v := v.property
  have hku : κ.map (u : L) = u := by
    change (u : L) ∈ κ.fixed
    rw [← h]
    exact u.property
  have hkv : κ.map (v : L) = v := by
    change (v : L) ∈ κ.fixed
    rw [← h]
    exact v.property
  rw [← huv, map_add, map_add, ρ.antilinear, κ.antilinear, hu, hv, hku, hkv]

/-- Real forms and conjugations correspond, without any semisimplicity assumption. -/
theorem real_form_iff_conjugation (S : LieSubalgebra ℝ L) :
    IsRealForm S ↔ ∃! ρ : Conjugation L, ρ.fixed = S := by
  constructor
  · intro hS
    obtain ⟨ρ, hρ, _⟩ := real_form_converse S hS
    exact ⟨ρ, hρ, fun κ hκ => conjugation_eq_of_fixed_eq κ ρ (hκ.trans hρ.symm)⟩
  · rintro ⟨ρ, hρ, _⟩
    rw [← hρ]
    exact fixed_isRealForm ρ

end LieAlgebrasAndRepresentations.RealForms
