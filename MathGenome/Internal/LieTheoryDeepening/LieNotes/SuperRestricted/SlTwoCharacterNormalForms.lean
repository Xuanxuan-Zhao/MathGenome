import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SlTwoCharacterNormalForms
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedSlTwo
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.ReducedEnveloping
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.Ring

/-! Normal forms for the nonzero characters of split restricted `sl₂`. -/

namespace LieNotes.SuperRestricted.SlTwoCharacterNormalForms

open _root_.Specs.LieNotes.SuperRestricted.SlTwoCharacterNormalForms
open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open Shared.Lie (U inclusion)
open Matrix

universe u

variable {k : Type u} [Field k]

abbrev tracePairing := @tracePairingValue

private theorem trace_zero (X : Model k) : X.val.trace = 0 := X.property

private theorem bottom_right (X : Model k) : X.val 1 1 = -(X.val 0 0) := by
  have h := trace_zero X
  rw [trace_fin_two] at h
  exact eq_neg_of_add_eq_zero_right h

private theorem coordinates (X : Model k) :
    X.val = !![X.val 0 0, X.val 0 1; X.val 1 0, -(X.val 0 0)] := by
  calc
    X.val = !![X.val 0 0, X.val 0 1; X.val 1 0, X.val 1 1] := eta_fin_two X.val
    _ = _ := by rw [bottom_right]

private theorem matrix_units :
    (E k).val = !![0, 1; 0, 0] ∧ (F k).val = !![0, 0; 1, 0] ∧
      (H k).val = !![1, 0; 0, -1] :=
  LieAlgebrasAndRepresentations.sl2_matrices k

private theorem trace_coordinates (X : Model k) :
    tracePairing X (E k) = X.val 1 0 ∧ tracePairing X (F k) = X.val 0 1 ∧
      tracePairing X (H k) = 2 * X.val 0 0 := by
  rcases matrix_units (k := k) with ⟨he, hf, hh⟩
  change trace (X.val * (E k).val) = _ ∧ trace (X.val * (F k).val) = _ ∧
    trace (X.val * (H k).val) = _
  rw [he, hf, hh]
  have hx := coordinates X
  constructor
  · conv_lhs => rw [hx]
    simp [trace_fin_two]
  constructor
  · conv_lhs => rw [hx]
    simp [trace_fin_two]
  · conv_lhs => rw [hx]
    simp [trace_fin_two, two_mul]

private theorem two_ne_zero_of_char {p : ℕ} [CharP k p] (hp : 2 < p) : (2 : k) ≠ 0 := by
  change ((2 : ℕ) : k) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff k p]
  exact fun h => (not_le_of_gt hp) (Nat.le_of_dvd (by decide) h)

theorem traceDuality : traceDualityType.{u} := by
  intro k _ p _ hp
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_char hp
  refine ⟨?_, ?_⟩
  · intro X Y h
    have he := congrArg (fun χ : Model k →ₗ[k] k => χ (E k)) h
    have hf := congrArg (fun χ : Model k →ₗ[k] k => χ (F k)) h
    have hh := congrArg (fun χ : Model k →ₗ[k] k => χ (H k)) h
    simp only [(trace_coordinates X).1, (trace_coordinates X).2.1, (trace_coordinates X).2.2,
      (trace_coordinates Y).1, (trace_coordinates Y).2.1, (trace_coordinates Y).2.2] at he hf hh
    apply Subtype.ext
    rw [coordinates X, coordinates Y, he, hf, mul_left_cancel₀ h2 hh]
  · intro χ
    let a := χ (H k) / 2
    let X : Model k := ⟨!![a, χ (F k); χ (E k), -a], by
      change trace !![a, χ (F k); χ (E k), -a] = 0
      simp [trace_fin_two]⟩
    obtain ⟨b, hb0, hb1, hb2⟩ := RestrictedSlTwo.basis k
    refine ⟨X, b.ext fun i => ?_⟩
    rcases trace_coordinates X with ⟨he, hf, hh⟩
    fin_cases i
    · simpa [hb0, X] using he
    · simpa [hb1, X] using hf
    · change tracePairing X (b 2) = χ (b 2)
      rw [hb2, hh]
      change 2 * (χ (H k) / 2) = χ (H k)
      field_simp [h2]

/-- Matrix conjugation, viewed on the trace-zero Lie subalgebra. -/
private def conjLinear (P : (Mat₂ k)ˣ) : Model k →ₗ[k] Model k where
  toFun X := ⟨(P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k), by
    change trace ((P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k)) = 0
    rw [trace_units_conj, trace_zero]⟩
  map_add' X Y := Subtype.ext (by
    change (P : Mat₂ k) * (X.val + Y.val) * (↑P⁻¹ : Mat₂ k) = _
    rw [mul_add, add_mul]
    rfl)
  map_smul' a X := Subtype.ext (by
    change (P : Mat₂ k) * (a • X.val) * (↑P⁻¹ : Mat₂ k) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl)

private theorem conj_mul (P : (Mat₂ k)ˣ) (A B : Mat₂ k) :
    ((P : Mat₂ k) * A * (↑P⁻¹ : Mat₂ k)) * ((P : Mat₂ k) * B * (↑P⁻¹ : Mat₂ k)) =
      (P : Mat₂ k) * (A * B) * (↑P⁻¹ : Mat₂ k) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (↑P⁻¹ : Mat₂ k) (P : Mat₂ k), Units.inv_mul, one_mul]

private def conjugate (P : (Mat₂ k)ˣ) : Model k ≃ₗ⁅k⁆ Model k where
  __ := conjLinear P
  invFun := conjLinear P⁻¹
  left_inv X := Subtype.ext (by
    change (↑P⁻¹ : Mat₂ k) * ((P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k)) * (P : Mat₂ k) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, one_mul, Matrix.mul_assoc,
      Units.inv_mul, mul_one])
  right_inv X := Subtype.ext (by
    change (P : Mat₂ k) * ((↑P⁻¹ : Mat₂ k) * X.val * (P : Mat₂ k)) * (↑P⁻¹ : Mat₂ k) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, one_mul, Matrix.mul_assoc,
      Units.mul_inv, mul_one])
  map_lie' {X Y} := Subtype.ext (by
    change (P : Mat₂ k) * (X.val * Y.val - Y.val * X.val) * (↑P⁻¹ : Mat₂ k) =
      ((P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k)) * ((P : Mat₂ k) * Y.val * (↑P⁻¹ : Mat₂ k)) -
      ((P : Mat₂ k) * Y.val * (↑P⁻¹ : Mat₂ k)) * ((P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k))
    rw [mul_sub, sub_mul, conj_mul, conj_mul])

theorem conjugation : conjugationType.{u} := by
  intro k _ P
  exact ⟨conjugate P, fun _ => rfl⟩

private theorem trace_conjugate (P : (Mat₂ k)ˣ) (X Y : Model k) :
    tracePairing (conjugate P X) (conjugate P Y) = tracePairing X Y := by
  change trace (((P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k)) *
    ((P : Mat₂ k) * Y.val * (↑P⁻¹ : Mat₂ k))) = trace (X.val * Y.val)
  rw [conj_mul, trace_units_conj]


/-- The columns of the change of basis are a vector and its image. -/
private theorem cyclic_basis (X : Model k) (hX : X ≠ 0) (h2 : (2 : k) ≠ 0) :
    ∃ Q : Mat₂ k, Q.det ≠ 0 ∧ X.val * Q = Q * !![0, -X.val.det; 1, 0] := by
  let a := X.val 0 0
  let b := X.val 0 1
  let c := X.val 1 0
  have hmat : X.val = !![a, b; c, -a] := coordinates X
  have hdet : -X.val.det = a * a + b * c := by
    rw [hmat, det_fin_two_of]
    ring
  have hvec : ∃ r s : k, r * (c * r - a * s) - (a * r + b * s) * s ≠ 0 := by
    by_cases hc : c = 0
    · by_cases hb : b = 0
      · have ha : a ≠ 0 := by
          intro ha
          apply hX
          apply Subtype.ext
          rw [hmat, ha, hb, hc, neg_zero]
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        exact ⟨1, 1, by simpa [hc, hb, ← neg_add', ← two_mul] using
          neg_ne_zero.mpr (mul_ne_zero h2 ha)⟩
      · exact ⟨0, 1, by simpa using neg_ne_zero.mpr hb⟩
    · exact ⟨1, 0, by simpa using hc⟩
  obtain ⟨r, s, hrs⟩ := hvec
  refine ⟨!![r, a * r + b * s; s, c * r - a * s], by rwa [det_fin_two_of], ?_⟩
  rw [hdet, hmat, mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem conjugate_of_basis (X : Model k) (S D : Mat₂ k) (hS : S.det ≠ 0)
    (h : X.val * S = S * D) :
    ∃ P : (Mat₂ k)ˣ, (conjugate P X).val = D := by
  let R := Matrix.GeneralLinearGroup.mkOfDetNeZero S hS
  refine ⟨R⁻¹, ?_⟩
  have hR : (R : Mat₂ k) = S := rfl
  change (↑R⁻¹ : Mat₂ k) * X.val * (R : Mat₂ k) = D
  have hm : X.val * (R : Mat₂ k) = (R : Mat₂ k) * D := by simpa only [hR] using h
  rw [Matrix.mul_assoc, hm, ← Matrix.mul_assoc, Units.inv_mul, one_mul]

private theorem matrix_normal_forms [IsAlgClosed k] (X : Model k) (hX : X ≠ 0)
    (h2 : (2 : k) ≠ 0) :
    (∃ (r : k) (P : (Mat₂ k)ˣ), r ≠ 0 ∧ (conjugate P X).val = diagonal ![r, -r]) ∨
      ∃ P : (Mat₂ k)ˣ, conjugate P X = E k := by
  obtain ⟨Q, hQ, hcomp⟩ := cyclic_basis X hX h2
  let d := -X.val.det
  let C : Mat₂ k := !![0, d; 1, 0]
  by_cases hd : d = 0
  · let B : Mat₂ k := !![0, 1; 1, 0]
    have hB : B.det ≠ 0 := by simp [B, det_fin_two_of]
    have hCB : C * B = B * (E k).val := by
      rw [(matrix_units (k := k)).1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [C, B, hd, Matrix.mul_apply, Fin.sum_univ_two]
    have hXB : X.val * (Q * B) = (Q * B) * (E k).val := by
      rw [← Matrix.mul_assoc, hcomp, Matrix.mul_assoc Q C B, hCB, ← Matrix.mul_assoc]
    obtain ⟨P, hP⟩ := conjugate_of_basis X (Q * B) (E k).val
      (by rw [det_mul]; exact mul_ne_zero hQ hB) hXB
    exact Or.inr ⟨P, Subtype.ext hP⟩
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq d (n := 2) (by decide)
    have hr0 : r ≠ 0 := by
      intro hz
      apply hd
      simpa [hz] using hr.symm
    let B : Mat₂ k := !![r, -r; 1, 1]
    let D : Mat₂ k := diagonal ![r, -r]
    have hB : B.det ≠ 0 := by
      simpa [B, det_fin_two_of, two_mul] using mul_ne_zero h2 hr0
    have hCB : C * B = B * D := by
      simp [C, B, D, diagonal_vec2, ← hr, pow_two]
    have hXB : X.val * (Q * B) = (Q * B) * D := by
      rw [← Matrix.mul_assoc, hcomp, Matrix.mul_assoc Q C B, hCB, ← Matrix.mul_assoc]
    obtain ⟨P, hP⟩ := conjugate_of_basis X (Q * B) D
      (by rw [det_mul]; exact mul_ne_zero hQ hB) hXB
    exact Or.inl ⟨r, P, hr0, hP⟩

private theorem trace_transport (P : (Mat₂ k)ˣ) (X : Model k) :
    (tracePairing X).comp (conjugate P).symm.toLinearEquiv.toLinearMap =
      tracePairing (conjugate P X) := by
  ext Y
  change tracePairing X ((conjugate P).symm Y) = tracePairing (conjugate P X) Y
  simpa using (trace_conjugate P X ((conjugate P).symm Y)).symm

private theorem charpoly_transport (P : (Mat₂ k)ˣ) (X : Model k) :
    (conjugate P X).val.charpoly = X.val.charpoly := by
  change ((P : Mat₂ k) * X.val * (↑P⁻¹ : Mat₂ k)).charpoly = X.val.charpoly
  rw [Matrix.coe_units_inv]
  exact charpoly_units_conj P X.val

theorem characterNormalForms : characterNormalFormsType.{u} := by
  intro k _ _ p _ hp χ hχ
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_char hp
  obtain ⟨X, hX⟩ := (traceDuality (k := k) hp).2 χ
  have hX0 : X ≠ 0 := by
    rintro rfl
    apply hχ
    rw [← hX]
    ext Y
    change Matrix.trace ((0 : Mat₂ k) * Y.val) = 0
    simp
  rcases matrix_normal_forms X hX0 h2 with ⟨a, P, ha, hP⟩ | ⟨P, hP⟩
  · refine ⟨X, P, conjugate P, hX.symm, fun _ => rfl, ?_⟩
    have hχ' := trace_transport P X
    rw [← hX]
    refine ⟨hχ', Or.inl ⟨a, ha, ?_, hP, ?_, ?_⟩⟩
    · intro heq
      apply mul_ne_zero h2 ha
      rw [two_mul, add_eq_zero_iff_eq_neg]
      exact heq
    · rw [← charpoly_transport P X, hP, charpoly_diagonal, Fin.prod_univ_two]
      rfl
    · rw [hχ']
      have hcoords := trace_coordinates (conjugate P X)
      rw [hP, diagonal_vec2] at hcoords
      obtain ⟨he, hf, hh⟩ := hcoords
      exact ⟨he, hf, hh, hh.symm ▸ mul_ne_zero h2 ha⟩
  · refine ⟨X, P, conjugate P, hX.symm, fun _ => rfl, ?_⟩
    have hχ' := trace_transport P X
    rw [← hX]
    refine ⟨hχ', Or.inr ⟨hP, ?_, ?_⟩⟩
    · rw [← charpoly_transport P X, hP, (matrix_units (k := k)).1, charpoly_fin_two]
      simp [trace_fin_two, det_fin_two_of]
    · rw [hχ', hP]
      have hcoords := trace_coordinates (E k)
      rw [(matrix_units (k := k)).1] at hcoords
      obtain ⟨he, hf, hh⟩ := hcoords
      exact ⟨he, by simpa using hh, hf⟩


section ReducedConjugation

attribute [local instance 100] LieRing.ofAssociativeRing

open ReducedEnveloping (ReducedEnvelopingAlgebra quotientMap pCenterElement reducedRelations)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open UniversalEnvelopingAlgebra (lift lift_ι_apply)

variable {p : ℕ} [CharP k p] [NeZero p]
variable (power : restrictedPowerValue k p (Model k))

private theorem conj_pow (P : (Mat₂ k)ˣ) (M : Mat₂ k) (n : ℕ) :
    ((P : Mat₂ k) * M * (↑P⁻¹ : Mat₂ k)) ^ n =
      (P : Mat₂ k) * M ^ n * (↑P⁻¹ : Mat₂ k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, conj_mul, ← pow_succ]

private theorem conjugation_preserves_power (P : (Mat₂ k)ˣ) (c : Model k ≃ₗ⁅k⁆ Model k)
    (hc : IsMatrixConjugation P c) (hpow : ∀ X, (power.val X).val = X.val ^ p) :
    ∀ X, c (power.val X) = power.val (c X) := by
  intro X
  apply Subtype.ext
  rw [hc, hpow, hpow, hc, conj_pow]

/-- A character-compatible restricted Lie equivalence descends through the reduced relations. -/
private theorem exists_reduced_map (χ ψ : Model k →ₗ[k] k)
    (c : Model k ≃ₗ⁅k⁆ Model k)
    (hc : ∀ X, c (power.val X) = power.val (c X))
    (hχ : ∀ X, ψ (c X) = χ X) :
    ∃ f : ReducedEnvelopingAlgebra power χ →ₐ[k] ReducedEnvelopingAlgebra power ψ,
      ∀ X, f (quotientMap power χ (inclusion k (Model k) X)) =
        quotientMap power ψ (inclusion k (Model k) (c X)) := by
  let l : Model k →ₗ⁅k⁆ ReducedEnvelopingAlgebra power ψ :=
    (quotientMap power ψ).toLieHom.comp ((inclusion k (Model k)).comp c.toLieHom)
  let g : U k (Model k) →ₐ[k] ReducedEnvelopingAlgebra power ψ := lift k l
  have hg (X : Model k) :
      g (inclusion k (Model k) X) = quotientMap power ψ (inclusion k (Model k) (c X)) :=
    lift_ι_apply k l X
  have hzero : ∀ a : U k (Model k), a ∈ reducedRelations power χ → g a = 0 := by
    have hspan :
        TwoSidedIdeal.span (Set.range fun X : Model k =>
          pCenterElement power X - algebraMap k (U k (Model k)) (χ X ^ p)) ≤
          TwoSidedIdeal.ker g := by
      apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨X, rfl⟩
      apply (TwoSidedIdeal.mem_ker g).mpr
      change g (inclusion k (Model k) X ^ p - inclusion k (Model k) (power.val X) -
        algebraMap k (U k (Model k)) (χ X ^ p)) = 0
      rw [map_sub, map_sub, map_pow, hg, hg, hc, AlgHom.commutes, ← hχ X, ← map_pow, ← map_sub]
      exact sub_eq_zero.mpr ((ReducedEnveloping.quotientMap_spec power ψ).2.2 (c X))
    exact fun a ha => (TwoSidedIdeal.mem_ker g).mp (hspan ha)
  let f := Ideal.Quotient.liftₐ (reducedRelations power χ) g hzero
  have hf : f.comp (quotientMap power χ) = g :=
    Ideal.Quotient.liftₐ_comp _ _ _
  exact ⟨f, fun X => (congrArg (fun m => m (inclusion k (Model k) X)) hf).trans (hg X)⟩

private theorem reduced_hom_ext (χ : Model k →ₗ[k] k) {B : Type u} [Ring B] [Algebra k B]
    {f g : ReducedEnvelopingAlgebra power χ →ₐ[k] B}
    (h : ∀ X, f (quotientMap power χ (inclusion k (Model k) X)) =
      g (quotientMap power χ (inclusion k (Model k) X))) : f = g := by
  have hcomp : f.comp (quotientMap power χ) = g.comp (quotientMap power χ) :=
    UniversalEnvelopingAlgebra.hom_ext k (LieHom.ext h)
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := (ReducedEnveloping.quotientMap_spec power χ).1 a
  exact congrArg (fun m => m b) hcomp

theorem reducedConjugation : reducedConjugationType.{u} := by
  intro k _ p _ _ power hpow P c hc χ
  let ψ := χ.comp c.symm.toLinearEquiv.toLinearMap
  have hfwd : ∀ X, c (power.val X) = power.val (c X) :=
    conjugation_preserves_power power P c hc hpow
  have hbwd (X : Model k) : c.symm (power.val X) = power.val (c.symm X) := by
    apply c.injective
    change c (c.symm (power.val X)) = c (power.val (c.symm X))
    rw [LieEquiv.apply_symm_apply, hfwd, LieEquiv.apply_symm_apply]
  have hχ (X : Model k) : ψ (c X) = χ X := by
    change χ (c.symm (c X)) = χ X
    rw [LieEquiv.symm_apply_apply]
  obtain ⟨f, hf⟩ := exists_reduced_map power χ ψ c hfwd hχ
  obtain ⟨g, hg⟩ := exists_reduced_map power ψ χ c.symm hbwd (fun _ => rfl)
  have hfg : f.comp g = AlgHom.id k (ReducedEnvelopingAlgebra power ψ) := by
    apply reduced_hom_ext power ψ
    intro X
    change f (g (quotientMap power ψ (inclusion k (Model k) X))) = _
    rw [hg, hf, LieEquiv.apply_symm_apply]
    rfl
  have hgf : g.comp f = AlgHom.id k (ReducedEnvelopingAlgebra power χ) := by
    apply reduced_hom_ext power χ
    intro X
    change g (f (quotientMap power χ (inclusion k (Model k) X))) = _
    rw [hf, hg, LieEquiv.symm_apply_apply]
    rfl
  exact ⟨AlgEquiv.ofAlgHom f g hfg hgf, hf⟩

end ReducedConjugation

section ModuleTransport

universe v

variable {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]

private def pullbackClasses (f : A →ₐ[k] B) : ModuleClass.{u, v} k B → ModuleClass.{u, v} k A :=
  Quotient.map (pullback f) (by
    rintro M N ⟨e, he⟩
    exact ⟨e, fun a => he (f a)⟩)

private theorem simple_pullback (f : A ≃ₐ[k] B) (M : AlgebraModule.{u, v} k B) :
    Simple (pullback f.toAlgHom M) ↔ Simple M := by
  let : Module B M.1 := Module.compHom M.1 M.2.toRingHom
  let : Module A M.1 := Module.compHom M.1 (M.2.comp f.toAlgHom).toRingHom
  let σ : A →+* B := f.toAlgHom.toRingHom
  let : RingHomSurjective σ := ⟨f.surjective⟩
  let identity : M.1 →ₛₗ[σ] M.1 :=
    { AddMonoidHom.id M.1 with
      map_smul' := fun _ _ => rfl }
  change IsSimpleModule A M.1 ↔ IsSimpleModule B M.1
  exact identity.isSimpleModule_iff_of_bijective Function.bijective_id

theorem moduleTransport : moduleTransportType.{u, v} := by
  intro k _ A B _ _ _ _ f
  let T : ModuleClass.{u, v} k A ≃ ModuleClass.{u, v} k B :=
    { toFun := pullbackClasses f.symm.toAlgHom
      invFun := pullbackClasses f.toAlgHom
      left_inv := by
        intro Q
        refine Quotient.inductionOn Q fun M => Quotient.sound ?_
        refine ⟨LinearEquiv.refl k M.1, fun a m => ?_⟩
        change M.2 (f.symm (f a)) m = M.2 a m
        rw [f.symm_apply_apply]
      right_inv := by
        intro Q
        refine Quotient.inductionOn Q fun N => Quotient.sound ?_
        refine ⟨LinearEquiv.refl k N.1, fun b n => ?_⟩
        change N.2 (f (f.symm b)) n = N.2 b n
        rw [f.apply_symm_apply] }
  exact ⟨T, fun M => ⟨rfl, simple_pullback f.symm M, rfl⟩,
    fun N => ⟨rfl, simple_pullback f N, rfl⟩⟩

end ModuleTransport

end LieNotes.SuperRestricted.SlTwoCharacterNormalForms
