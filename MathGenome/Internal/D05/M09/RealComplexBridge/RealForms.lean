import MathGenome.Internal.Specs.D05.M09.RealComplexBridge.RealForms
import MathGenome.Internal.D05.M09.RealComplexBridge
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Algebraic real forms and conjugations, including arbitrary-dimensional spaces. -/
namespace D05.M09.RealComplexBridge.RealForms

open Specs.D05.M09.RealComplexBridge
open Specs.D05.M09.RealComplexBridge.RealForms
open Complexification

universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

@[simp] theorem conjugation_add (J : Conjugation V) (x y : V) :
    J (x + y) = J x + J y := J.toMap.map_add x y

@[simp] theorem conjugation_sub (J : Conjugation V) (x y : V) :
    J (x - y) = J x - J y := J.toMap.map_sub x y

@[simp] theorem conjugation_smul (J : Conjugation V) (z : ℂ) (v : V) :
    J (z • v) = (starRingEnd ℂ z) • J v := J.toMap.map_smulₛₗ z v

@[simp] theorem conjugation_twice (J : Conjugation V) (v : V) : J (J v) = v :=
  J.involutive v

@[simp] theorem mem_fixedSpace (J : Conjugation V) (v : V) :
    v ∈ fixedSpace J ↔ J v = v := Iff.rfl

@[simp] theorem conjugation_I (J : Conjugation V) (v : V) :
    J (Complex.I • v) = -Complex.I • J v := by
  rw [conjugation_smul]
  rw [Complex.conj_I]

private theorem inverse_two_I : (2 * Complex.I : ℂ)⁻¹ = -Complex.I * (2 : ℂ)⁻¹ := by
  rw [mul_inv_rev, Complex.inv_I]

theorem decomposition_formulas : Specs.D05.M09.RealComplexBridge.RealForms.decomposition_formulas := by
  intro V _ _ J v
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fixedSpace, conjugation_smul, conjugation_add, conjugation_twice]
    have hc : starRingEnd ℂ ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp [map_ofNat]
    rw [hc, add_comm]
  · rw [mem_fixedSpace, conjugation_smul, conjugation_sub, conjugation_twice]
    have hc : starRingEnd ℂ ((2 * Complex.I : ℂ)⁻¹) =
        -(2 * Complex.I : ℂ)⁻¹ := by simp [map_mul, map_inv₀, map_ofNat]
    rw [hc, ← neg_sub v (J v), smul_neg, neg_smul, neg_neg]
  · rw [inverse_two_I]
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

/-- Projection recovers the real part of any expression in fixed vectors. -/
theorem real_projection (J : Conjugation V) (x y : fixedSpace J) :
    (2 : ℂ)⁻¹ • (((x : V) + Complex.I • (y : V)) +
      J ((x : V) + Complex.I • (y : V))) = (x : V) := by
  rw [conjugation_add, conjugation_I, x.property, y.property]
  module

/-- Projection recovers its imaginary part, with the source's 1/(2i) convention. -/
theorem imaginary_projection (J : Conjugation V) (x y : fixedSpace J) :
    (2 * Complex.I : ℂ)⁻¹ • (((x : V) + Complex.I • (y : V)) -
      J ((x : V) + Complex.I • (y : V))) = (y : V) := by
  rw [conjugation_add, conjugation_I, x.property, y.property, inverse_two_I]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

theorem fixed_real_form : Specs.D05.M09.RealComplexBridge.RealForms.fixed_real_form := by
  intro V _ _ J v
  obtain ⟨hx, hy, hv⟩ := decomposition_formulas J v
  refine ⟨(⟨_, hx⟩, ⟨_, hy⟩), hv.symm, ?_⟩
  rintro ⟨x,y⟩ h
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [h] using (real_projection J x y).symm
  · simpa only [h] using (imaginary_projection J x y).symm

theorem real_form_iff_bijective :
    Specs.D05.M09.RealComplexBridge.RealForms.real_form_iff_bijective := by
  intro V _ _ W
  exact (Function.bijective_iff_existsUnique (naturalMap W)).symm

/-- The inverse is chosen from unique decomposition, while the forward map is canonical. -/
noncomputable def realFormEquiv (W : Submodule ℝ V) (hW : IsRealForm W) :
    Complexification W ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (naturalMap W) ((real_form_iff_bijective W).mp hW)

@[simp] theorem realFormEquiv_apply (W : Submodule ℝ V) (hW : IsRealForm W) (x y : W) :
    realFormEquiv W hW (pair x y) = (x : V) + Complex.I • (y : V) := rfl

theorem natural_isomorphism :
    Specs.D05.M09.RealComplexBridge.RealForms.natural_isomorphism := by
  intro V _ _ W hW
  exact ⟨realFormEquiv W hW, fun _ _ => rfl⟩

theorem internal_direct_sum :
    Specs.D05.M09.RealComplexBridge.RealForms.internal_direct_sum := by
  intro V _ _ W hW
  have hinj := ((real_form_iff_bijective W).mp hW).1
  constructor
  · apply top_unique
    intro v _
    obtain ⟨⟨x,y⟩, hv, _⟩ := hW v
    exact Submodule.mem_sup.mpr ⟨x, x.property, Complex.I • (y : V),
      ⟨y, y.property, rfl⟩, hv⟩
  · apply le_antisymm
    · intro v hv
      obtain ⟨y, hy, hiy⟩ := hv.2
      have he : naturalMap W (pair ⟨v, hv.1⟩ 0) =
          naturalMap W (pair 0 ⟨y, hy⟩) := by
        change v + Complex.I • (0 : V) = 0 + multiplyI y
        simpa [multiplyI] using hiy.symm
      have hp := congrArg (fun p : Complexification W => ((re p : W) : V)) (hinj he)
      exact hp
    · exact bot_le

/-- The canonical conjugation of the upstream pair model. -/
def pairConjugation {W : Type u} [AddCommGroup W] [Module ℝ W] :
    Conjugation (Complexification W) where
  toMap :=
    { toFun := fun p => pair (re p) (-im p)
      map_add' := by
        intro p q
        apply D05.M09.RealComplexBridge.ext <;> simp <;> module
      map_smul' := by
        intro z p
        apply D05.M09.RealComplexBridge.ext <;> simp <;> module }
  involutive p := by
    apply D05.M09.RealComplexBridge.ext <;> simp

/-- Transport the actual conjugate-linear involution along a complex isomorphism. -/
def transportConjugation {U : Type*} [AddCommGroup U] [Module ℂ U]
    (e : U ≃ₗ[ℂ] V) (J : Conjugation U) : Conjugation V where
  toMap := e.toLinearMap.comp (J.toMap.comp e.symm.toLinearMap)
  involutive v := by
    change e (J (e.symm (e (J (e.symm v))))) = v
    rw [e.symm_apply_apply, J.involutive, e.apply_symm_apply]

@[simp] theorem transportConjugation_apply {U : Type*} [AddCommGroup U] [Module ℂ U]
    (e : U ≃ₗ[ℂ] V) (J : Conjugation U) (v : V) :
    transportConjugation e J v = e (J (e.symm v)) := rfl

/-- Any two conjugations fixing a real form agree on its unique decompositions. -/
theorem conjugation_unique (W : Submodule ℝ V) (hW : IsRealForm W)
    (J J' : Conjugation V) (hJ : ∀ x : W, J x = x) (hJ' : ∀ x : W, J' x = x) :
    J = J' := by
  have hm : J.toMap = J'.toMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨x,y⟩, hv, _⟩ := hW v
    rw [← hv, conjugation_add, conjugation_I, conjugation_add, conjugation_I,
      hJ, hJ, hJ', hJ']
  cases J
  cases J'
  cases hm
  rfl

theorem conjugation_of_real_form :
    Specs.D05.M09.RealComplexBridge.RealForms.conjugation_of_real_form := by
  intro V _ _ W hW
  let e := realFormEquiv W hW
  let J := transportConjugation e pairConjugation
  have hformula (x y : W) : J ((x : V) + Complex.I • (y : V)) =
      (x : V) - Complex.I • (y : V) := by
    change e (pairConjugation (e.symm (e (pair x y)))) = _
    rw [e.symm_apply_apply]
    change (x : V) + Complex.I • ((-y : W) : V) = _
    simp [sub_eq_add_neg]
  have hfix (x : W) : J x = x := by simpa using hformula x 0
  refine ⟨J, hformula, ?_, ?_⟩
  · ext v
    constructor
    · intro hvfix
      change J v = v at hvfix
      obtain ⟨⟨x,y⟩, hv, _⟩ := hW v
      have hy : (y : V) = 0 := by
        have hp := imaginary_projection J ⟨x, hfix x⟩ ⟨y, hfix y⟩
        simpa only [hv, hvfix, sub_self, smul_zero] using hp.symm
      rw [← hv, hy, smul_zero, add_zero]
      exact x.property
    · intro hv
      exact hfix ⟨v,hv⟩
  · intro J' hJ'
    exact conjugation_unique W hW J' J hJ' hfix

theorem basis_criterion : Specs.D05.M09.RealComplexBridge.RealForms.basis_criterion := by
  intro V ι _ _ W b
  obtain ⟨bC, hbC⟩ := D05.M09.RealComplexBridge.basis_extension b
  constructor
  · intro hW
    refine ⟨bC.map (realFormEquiv W hW), ?_⟩
    intro i
    simp only [Module.Basis.map_apply, hbC]
    change (b i : V) + Complex.I • (0 : V) = (b i : V)
    simp
  · rintro ⟨B,hB⟩
    let e := bC.equiv B (Equiv.refl ι)
    have he : e.toLinearMap = naturalMap W := by
      apply bC.ext
      intro i
      change e (bC i) = naturalMap W (bC i)
      rw [Module.Basis.equiv_apply, Equiv.refl_apply, hB, hbC]
      change (b i : V) = (b i : V) + Complex.I • (0 : V)
      simp
    apply (real_form_iff_bijective W).mpr
    rw [← he]
    exact e.bijective

theorem dimension_from_real_form :
    Specs.D05.M09.RealComplexBridge.RealForms.dimension_from_real_form := by
  intro V _ _ W _ hW
  obtain ⟨B,_⟩ := (basis_criterion W (Module.finBasis ℝ W)).mp hW
  have hfinite := B.finiteDimensional_of_finite
  exact ⟨hfinite, by rw [Module.finrank_eq_card_basis B, Fintype.card_fin]⟩

theorem dimension_of_fixed_space :
    Specs.D05.M09.RealComplexBridge.RealForms.dimension_of_fixed_space := by
  intro V _ _ _ J
  exact (dimension_from_real_form (fixedSpace J) (fixed_real_form J)).2

theorem preserves_iff_commutes :
    Specs.D05.M09.RealComplexBridge.RealForms.preserves_iff_commutes := by
  intro V _ _ J T
  constructor
  · intro hT v
    obtain ⟨⟨x,y⟩, hv, _⟩ := fixed_real_form J v
    have hx : J (T x) = T x := hT x x.property
    have hy : J (T y) = T y := hT y y.property
    rw [← hv, conjugation_add, conjugation_I, x.property, y.property,
      map_add, map_smul, map_add, map_smul, conjugation_add, conjugation_smul, hx, hy]
    rw [Complex.conj_I]
  · intro hT v hv
    change J (T v) = T v
    rw [← hT v, (mem_fixedSpace J v).mp hv]

end D05.M09.RealComplexBridge.RealForms
