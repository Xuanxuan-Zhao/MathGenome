import Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import Mathlib.Tactic.NoncommRing
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.RingTheory.PowerBasis
import Batteries.Tactic.OpenPrivate
import LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs
import LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators
import LinearAlgebraicGroups.Arithmetic.QuaternionScalarCliffordLift
import LinearAlgebraicGroups.Arithmetic.QuaternionHyperbolicRadicals
import LinearAlgebraicGroups.Arithmetic.SplitQuadraticPairSpinComparison
import LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import LinearAlgebraicGroups.Descent.RelativeRank

open MulOpposite
open _root_.Specs.RM03.CSA (isCentralSimple degree reducedNorm)
open LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.QuaternionSpinCharacteristicTwo
open Specs.Arithmetic.CharacteristicTwoQuadraticPairs
open Specs.SymplecticDivisionForms (antiValue)
open Specs.SymplecticInvolutionModels (HermitianPairing quaternionConjugate)

set_option linter.unusedSectionVars false

section Columns

variable {F : Type u} [Field F] [CharP F 2]
  {B : Type v} [DivisionRing B] [Algebra F B]
  {s : B ≃ₐ[F] Bᵐᵒᵖ} {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V]

local notation "bar" => antiValue s
local notation:75 x:75 " ◁ " a:76 => (op a • x)

private theorem two_eq_zero (F : Type u) [Field F] [CharP F 2]
    {B : Type v} [DivisionRing B] [Algebra F B] : (2 : B) = 0 := by
  rw [← map_ofNat (algebraMap F B) 2, CharP.ofNat_eq_zero F 2, map_zero]

private theorem add_self_column (F : Type u) [Field F] [CharP F 2]
    {B : Type v} [DivisionRing B] [Algebra F B] (x : B) : x + x = 0 := by
  rw [← two_mul, two_eq_zero F, zero_mul]

private theorem column_cancel (F : Type u) [Field F] [CharP F 2]
    {B : Type v} [DivisionRing B] [Algebra F B] (a b : B) : a + b + b = a := by
  rw [add_assoc, add_self_column (F := F), add_zero]

private theorem bar_add (x y : B) : bar (x + y) = bar x + bar y := by
  simp [antiValue]

private theorem bar_mul (x y : B) : bar (x * y) = bar y * bar x := by
  simp [antiValue]

private theorem bar_inv (x : B) : bar x⁻¹ = (bar x)⁻¹ := by
  simp [antiValue]

private theorem bar_scalar (a : F) : bar (algebraMap F B a) = algebraMap F B a := by
  simp [antiValue, AlgEquiv.commutes]

private theorem bar_add_eq_trace (hB : isCentralSimple F B)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (a : B) :
    bar a + a = algebraMap F B (reducedTrace hB a) := by
  rw [hs, quaternionConjugate, sub_add_cancel]

private theorem bar_bar (hB : isCentralSimple F B)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (a : B) :
    bar (bar a) = a := by
  have hh := congrArg (antiValue s) (bar_add_eq_trace hB hs a)
  rw [bar_add, bar_scalar] at hh
  exact add_right_cancel (hh.trans ((add_comm a (bar a)).trans (bar_add_eq_trace hB hs a)).symm)

private theorem bar_ne_zero {b : B} (hb : b ≠ 0) : bar b ≠ 0 := by
  simpa [antiValue] using s.injective.ne hb

private theorem class_scalar (a : F) : scalarClass F (algebraMap F B a) = 0 :=
  (Submodule.Quotient.mk_eq_zero (scalarLine F B)).mpr (show algebraMap F B a ∈ scalarLine F B from ⟨a, rfl⟩)

private theorem class_bar (hB : isCentralSimple F B)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (a : B) :
    scalarClass F (bar a) = scalarClass F a := by
  have hh := congrArg (scalarClass F) (bar_add_eq_trace hB hs a)
  rw [map_add, class_scalar] at hh
  have hz : scalarClass F a + scalarClass F a = 0 := by
    rw [← map_add, add_self_column (F := F), map_zero]
  exact add_right_cancel (hh.trans hz.symm)

private theorem class_cancel (a b : ScalarClasses F B) : a + b + b = a := by
  obtain ⟨x, rfl⟩ := (scalarLine F B).mkQ_surjective b
  rw [add_assoc, ← map_add, add_self_column (F := F), map_zero, add_zero]

private theorem hermitian_bar (h : HermitianPairing s V) (x y : V) :
    bar (h.value x y) = h.value y x :=
  (h.hermitian x y).symm

private theorem hermitian_add_left (h : HermitianPairing s V) (x y z : V) :
    h.value (x + y) z = h.value x z + h.value y z := by
  rw [← hermitian_bar h z (x + y), h.add_right, bar_add, hermitian_bar, hermitian_bar]

private theorem hermitian_smul_left (h : HermitianPairing s V) (x y : V) (a : B) :
    h.value (x ◁ a) y = bar a * h.value x y := by
  rw [← hermitian_bar h y (x ◁ a), h.smul_right, bar_mul, hermitian_bar]

private theorem hermitian_zero_right (h : HermitianPairing s V) (x : V) :
    h.value x 0 = 0 := by
  simpa using h.smul_right x x 0

private theorem norm_eq_add_bar
    (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    (x : V) (b : B) (hb : scalarClass F b = refinement h ell x) :
    h.value x x = bar b + b := by
  have hh := ht x x
  rw [← hermitian_bar h x (ell x)] at hh
  change (scalarLine F B).mkQ b =
    (scalarLine F B).mkQ (h.value x (ell x)) at hb
  obtain ⟨a, ha⟩ := (Submodule.Quotient.eq (scalarLine F B)).mp hb
  have ha' : b - h.value x (ell x) = algebraMap F B a := ha.symm
  have hb' := sub_eq_iff_eq_add.mp ha'
  have hbarScalar : bar (algebraMap F B a) = algebraMap F B a := by
    simp [antiValue, AlgEquiv.commutes]
  rw [← hh, hb', bar_add, hbarScalar]
  calc
    _ = bar (h.value x (ell x)) + h.value x (ell x) +
          (algebraMap F B a + algebraMap F B a) := by rw [add_self_column F, add_zero]
    _ = _ := by abel

private theorem preserves_column_hermitian
    (h : HermitianPairing s V) (w₀ : V) (b : B)
    (hn : h.value w₀ w₀ = bar b + b) (p q : B × V × B) :
    columnHermitian h (upper h w₀ b p) (upper h w₀ b q) = columnHermitian h p q ∧
    columnHermitian h (lower h w₀ b p) (lower h w₀ b q) = columnHermitian h p q := by
  rcases p with ⟨x, y, z⟩
  rcases q with ⟨x', y', z'⟩
  constructor <;>
    simp only [columnHermitian, upper, lower, bar_add, bar_mul, hermitian_add_left,
      h.add_right, h.smul_right, hermitian_smul_left, hermitian_bar, hn] <;>
    noncomm_ring <;>
    simp [two_eq_zero (B := B) F]

private theorem preserves_column_quadratic (href : RefinementIdentities.{u,v,w})
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, bar a = quaternionConjugate hB a)
    (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    (w₀ : V) (b : B) (hb : scalarClass F b = refinement h ell w₀) (p : B × V × B) :
    columnQuadratic h ell (upper h w₀ b p) = columnQuadratic h ell p ∧
    columnQuadratic h ell (lower h w₀ b p) = columnQuadratic h ell p := by
  obtain ⟨hscale, hclass, hadd, _⟩ := href hB hd s hs h ell ht
  have hr (a : B) : refinement h ell (w₀ ◁ a) = scalarClass F (bar a * b * a) :=
    (hscale w₀ a).trans (hclass a _ _ hb.symm)
  rcases p with ⟨x, y, z⟩
  constructor
  · simp only [columnQuadratic, upper, bar_add, bar_mul, add_mul, map_add, hadd, hr,
      h.smul_right, hermitian_bar]
    calc
      _ = (scalarClass F (bar x * z) + refinement h ell y +
          (scalarClass F (h.value y w₀ * z) + scalarClass F (h.value y w₀ * z))) +
          (scalarClass F (bar z * bar b * z) + scalarClass F (bar z * b * z)) := by abel
      _ = _ := by rw [← add_assoc (scalarClass F (bar x * z) + refinement h ell y),
          class_cancel, hclass z _ _ (class_bar hB hs b), ← add_assoc, class_cancel]
  · simp only [columnQuadratic, lower, mul_add, map_add, hadd, hr, h.smul_right, ← mul_assoc]
    have hm : scalarClass F (bar x * h.value w₀ y) = scalarClass F (h.value y w₀ * x) := by
      rw [← class_bar hB hs (h.value y w₀ * x), bar_mul, hermitian_bar]
    rw [hm]
    calc
      _ = ((scalarClass F (bar x * z) + refinement h ell y) +
          scalarClass F (h.value y w₀ * x) + scalarClass F (h.value y w₀ * x)) +
          scalarClass F (bar x * b * x) + scalarClass F (bar x * b * x) := by abel
      _ = _ := by rw [class_cancel, class_cancel]

private theorem column_smul_add (x : V) (a b : B) :
    x ◁ a + x ◁ b = x ◁ (a + b) := by
  rw [op_add, add_smul]

private theorem column_smul_mul (x : V) (a b : B) :
    (x ◁ a) ◁ b = x ◁ (a * b) := by
  rw [op_mul, mul_smul]

private theorem weyl_word_columns (hB : isCentralSimple F B)
    (hs : ∀ a, bar a = quaternionConjugate hB a)
    (h : HermitianPairing s V) (w₀ : V) (b : B)
    (hn : h.value w₀ w₀ = bar b + b) (hb : b ≠ 0) (x : B) (y : V) (z : B) :
    weylWord h w₀ b (x, y, z) =
      (b * z, perpendicularRotation h w₀ b y, (bar b)⁻¹ * x) := by
  have hbar := bar_ne_zero (s := s) hb
  have hfirst : x + h.value w₀ (y + w₀ ◁ ((bar b)⁻¹ * x)) +
      b * (z + b⁻¹ * h.value w₀ y + (bar b)⁻¹ * x) = b * z := by
    simp only [h.add_right, h.smul_right, hn]
    noncomm_ring [mul_inv_cancel_left₀ hb, mul_inv_cancel_left₀ hbar]
    simp [two_eq_zero (B := B) F]
  have hmiddle : y + w₀ ◁ ((bar b)⁻¹ * x) +
      w₀ ◁ (z + b⁻¹ * h.value w₀ y + (bar b)⁻¹ * x) =
      perpendicularRotation h w₀ b y + w₀ ◁ z := by
    simp only [perpendicularRotation, add_assoc, column_smul_add]
    congr 2
    rw [show (bar b)⁻¹ * x + (z + (b⁻¹ * h.value w₀ y + (bar b)⁻¹ * x)) =
      b⁻¹ * h.value w₀ y + z + ((bar b)⁻¹ * x + (bar b)⁻¹ * x) by abel]
    rw [add_self_column F, add_zero]
  have hlast : z + b⁻¹ * h.value w₀ y + (bar b)⁻¹ * x +
      (bar b)⁻¹ * h.value w₀ (perpendicularRotation h w₀ b y + w₀ ◁ z) +
      (bar b)⁻¹ * (b * z) = (bar b)⁻¹ * x := by
    simp only [perpendicularRotation, h.add_right, h.smul_right, hn]
    noncomm_ring [mul_inv_cancel_left₀ hb, inv_mul_cancel_left₀ hbar]
    simp [two_eq_zero (B := B) F]
  simp only [weylWord, Function.comp_apply, lower, upper, column_smul_mul,
    hermitian_smul_left, bar_inv, bar_bar hB hs, hfirst, hmiddle, hlast,
    inv_mul_cancel_left₀ hb]
  rw [add_assoc, column_smul_add, add_self_column F, op_zero, zero_smul, add_zero]

private theorem radical_words (href : RefinementIdentities.{u,v,w}) : RadicalWords.{u,v,w} := by
  intro F _ _ B _ _ hB hd s hs V _ _ h ell ht w₀ b hclass
  have hn := norm_eq_add_bar h ell ht w₀ b hclass
  refine ⟨preserves_column_hermitian h w₀ b hn, preserves_column_quadratic href hB hd hs h ell ht w₀ b hclass, ?_⟩
  intro hb
  have hbar := bar_ne_zero (s := s) hb
  obtain ⟨hscale, hdescend, _, _⟩ := href hB hd s hs h ell ht
  have hr (a : B) : refinement h ell (w₀ ◁ a) = scalarClass F (antiValue s a * b * a) :=
    (hscale w₀ a).trans (hdescend a _ _ hclass.symm)
  refine ⟨?_, ?_, weyl_word_columns hB hs h w₀ b hn hb⟩
  · rw [hr, bar_inv, mul_assoc, mul_inv_cancel₀ hb, mul_one]
  · rw [hr, bar_inv, bar_bar hB hs, inv_mul_cancel₀ hb, one_mul]

private theorem vector_add_self (_h : HermitianPairing s V) (x : V) : x + x = 0 := by
  calc
    x + x = x ◁ (1 + 1 : B) := by rw [← column_smul_add, op_one, one_smul]
    _ = 0 := by rw [add_self_column F, op_zero, zero_smul]

private theorem exists_nonzero_norm (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (h : HermitianPairing s V) {x : V}
    (hx : x ≠ 0) : ∃ y, h.value y y ≠ 0 := by
  obtain ⟨y, hxy⟩ := h.nondegenerate x hx
  obtain ⟨_, _, _, _, htrace⟩ :=
    SymplecticInvolutionModels.quaternionConjugation.{u,v,u} hB hd
  obtain ⟨b, hb⟩ := htrace 1
  let z := y ◁ ((h.value x y)⁻¹ * b)
  have hz : h.value x z = b := by
    dsimp only [z]
    rw [h.smul_right, ← mul_assoc, mul_inv_cancel₀ hxy, one_mul]
  by_contra! hzero
  have hsum := hzero (x + z)
  rw [hermitian_add_left, h.add_right, h.add_right, hzero x, hzero z, zero_add, add_zero,
    ← hermitian_bar h x z, hz, add_comm b, bar_add_eq_trace hB hs, hb, map_one] at hsum
  exact one_ne_zero hsum

private def rightPairing (h : HermitianPairing s V) (x : V) : V →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun y := op (h.value x y)
  map_add' y z := by rw [h.add_right, op_add]
  map_smul' a y := by
    obtain ⟨a⟩ := a
    change op (h.value x (op a • y)) = op a * op (h.value x y)
    rw [h.smul_right, op_mul]

private theorem rightPairing_apply (h : HermitianPairing s V) (x y : V) :
    rightPairing h x y = op (h.value x y) := rfl

private theorem hermitian_sub_right (h : HermitianPairing s V) (x y z : V) :
    h.value x (y - z) = h.value x y - h.value x z := op_injective (by
  simpa only [rightPairing_apply, op_sub] using (rightPairing h x).map_sub y z)

private theorem hermitian_zero_left (h : HermitianPairing s V) (x : V) : h.value 0 x = 0 := by
  rw [← hermitian_bar h x 0, hermitian_zero_right]
  simp [antiValue]

private def rotationMap (h : HermitianPairing s V) (w₀ : V) (b : B) : V →ₗ[Bᵐᵒᵖ] V :=
  LinearMap.id +
    ((LinearMap.toSpanSingleton Bᵐᵒᵖ V w₀).comp (LinearMap.mulRight Bᵐᵒᵖ (op b⁻¹))).comp
      (rightPairing h w₀)

private theorem rotationMap_apply (h : HermitianPairing s V) (w₀ y : V) (b : B) :
    rotationMap h w₀ b y = perpendicularRotation h w₀ b y := rfl

private theorem rotation_preserves (hwords : RadicalWords.{u,v,w})
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (h : HermitianPairing s V)
    (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    (w₀ : V) (b : B) (hb : b ≠ 0) (hq : scalarClass F b = refinement h ell w₀) :
    (∀ x y, h.value (perpendicularRotation h w₀ b x) (perpendicularRotation h w₀ b y) =
      h.value x y) ∧
    (∀ x, refinement h ell (perpendicularRotation h w₀ b x) = refinement h ell x) := by
  obtain ⟨hu, hqu, hw⟩ := hwords hB hd hs h ell ht w₀ b hq
  obtain ⟨hb₁, hb₂, hw⟩ := hw hb
  obtain ⟨hl₁, hql₁, _⟩ := hwords hB hd hs h ell ht (w₀ ◁ b⁻¹) (bar b)⁻¹ hb₁
  obtain ⟨hl₂, hql₂, _⟩ := hwords hB hd hs h ell ht (w₀ ◁ (bar b)⁻¹) (bar b)⁻¹ hb₂
  have hcol (x : V) : weylWord h w₀ b (0, x, 0) = (0, perpendicularRotation h w₀ b x, 0) := by
    simpa only [mul_zero] using hw 0 x 0
  constructor
  · intro x y
    have hh (p q : B × V × B) :
        columnHermitian h (weylWord h w₀ b p) (weylWord h w₀ b q) = columnHermitian h p q := by
      simp only [weylWord, Function.comp_apply]
      rw [(hl₁ _ _).2, (hu _ _).1, (hl₂ _ _).2]
    simpa [hcol, columnHermitian, antiValue] using hh (0, x, 0) (0, y, 0)
  · intro x
    have hh (p : B × V × B) :
        columnQuadratic h ell (weylWord h w₀ b p) = columnQuadratic h ell p := by
      simp only [weylWord, Function.comp_apply]
      rw [(hql₁ _).2, (hqu _).1, (hql₂ _).2]
    simpa [hcol, columnQuadratic, antiValue] using hh (0, x, 0)

private theorem rotation_equiv [Module.Finite Bᵐᵒᵖ V]
    (hwords : RadicalWords.{u,v,w}) (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (h : HermitianPairing s V)
    (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    (w₀ : V) (b : Bˣ) (hq : scalarClass F (b : B) = refinement h ell w₀) :
    ∃ r : V ≃ₗ[Bᵐᵒᵖ] V,
      (∀ x, r x = perpendicularRotation h w₀ b x) ∧
      (∀ x y, h.value (r x) (r y) = h.value x y) ∧
      (∀ x, refinement h ell (r x) = refinement h ell x) := by
  obtain ⟨hh, hq⟩ := rotation_preserves hwords hB hd hs h ell ht w₀ b b.ne_zero hq
  let r := rotationMap h w₀ b
  have hinj : Function.Injective r := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx₀
    obtain ⟨y, hy⟩ := h.nondegenerate x hx₀
    have hh' := hh x y
    rw [← rotationMap_apply, show rotationMap h w₀ (b : B) x = 0 from hx,
      hermitian_zero_left] at hh'
    exact hy hh'.symm
  exact ⟨LinearEquiv.ofBijective r ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩,
    fun x => rotationMap_apply h w₀ x b, hh, hq⟩

private theorem rotation_align_step (href : RefinementIdentities.{u,v,w})
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, bar a = quaternionConjugate hB a)
    (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    {x y : V} (hxy : refinement h ell x = refinement h ell y)
    (hb : h.value (x + y) x ≠ 0) :
    ∃ b : Bˣ, scalarClass F (b : B) = refinement h ell (x + y) ∧
      perpendicularRotation h (x + y) b x = y := by
  obtain ⟨_, _, hadd, _⟩ := href hB hd s hs h ell ht
  refine ⟨Units.mk0 _ hb, ?_, ?_⟩
  · change scalarClass F (h.value (x + y) x) = refinement h ell (x + y)
    obtain ⟨c, hc⟩ := h.central_norm x
    rw [hermitian_add_left, map_add, hc, class_scalar, zero_add, hadd, hxy]
    have hyy := class_cancel (0 : ScalarClasses F B) (refinement h ell y)
    rw [zero_add] at hyy
    rw [hyy, zero_add]
    rw [← hermitian_bar h x y, class_bar hB hs]
  · change x + (x + y) ◁ ((h.value (x + y) x)⁻¹ * h.value (x + y) x) = y
    rw [inv_mul_cancel₀ hb, op_one, one_smul, ← add_assoc, vector_add_self h, zero_add]

private theorem rotation_align [Module.Finite Bᵐᵒᵖ V]
    (href : RefinementIdentities.{u,v,w}) (hwords : RadicalWords.{u,v,w})
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (h : HermitianPairing s V)
    (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    {x y : V} (hx : h.value x x ≠ 0) (hxy : refinement h ell x = refinement h ell y) :
    ∃ (r : V ≃ₗ[Bᵐᵒᵖ] V) (l : List (V × Bˣ)),
      (∀ p ∈ l, scalarClass F (p.2 : B) = refinement h ell p.1) ∧
      (∀ z, r z = l.foldr (fun p z₀ => perpendicularRotation h p.1 (p.2 : B) z₀) z) ∧
      (∀ z z', h.value (r z) (r z') = h.value z z') ∧
      (∀ z, refinement h ell (r z) = refinement h ell z) ∧ r x = y := by
  have step {a b : V} (hq : refinement h ell a = refinement h ell b)
      (hn : h.value (a + b) a ≠ 0) :
      ∃ (p : Bˣ) (r : V ≃ₗ[Bᵐᵒᵖ] V),
        scalarClass F (p : B) = refinement h ell (a + b) ∧
        (∀ z, r z = perpendicularRotation h (a + b) p z) ∧
        (∀ z z', h.value (r z) (r z') = h.value z z') ∧
        (∀ z, refinement h ell (r z) = refinement h ell z) ∧ r a = b := by
    obtain ⟨p, hp, hr⟩ := rotation_align_step href hB hd hs h ell ht hq hn
    obtain ⟨r, hform, hH, hQ⟩ := rotation_equiv hwords hB hd hs h ell ht (a + b) p hp
    exact ⟨p, r, hp, hform, hH, hQ, (hform a).trans hr⟩
  by_cases hn : h.value (x + y) x = 0
  · have hyx : h.value y x = h.value x x := by
      rw [hermitian_add_left] at hn
      exact add_left_cancel (hn.trans (add_self_column F (h.value x x)).symm)
    obtain ⟨b, hb⟩ : ∃ b : Bˣ, scalarClass F (b : B) = refinement h ell x := by
      obtain ⟨t, ht'⟩ := (scalarLine F B).mkQ_surjective (refinement h ell x)
      have htn : t ≠ 0 := by
        intro hz
        have he := norm_eq_add_bar h ell ht x t ht'
        rw [hz] at he
        exact hx (by simpa [antiValue] using he)
      exact ⟨Units.mk0 t htn, ht'⟩
    obtain ⟨r, hr, hH, hQ⟩ := rotation_equiv hwords hB hd hs h ell ht x b hb
    let x' := r x
    have hn' : h.value (x' + y) x' ≠ 0 := by
      change h.value (r x + y) (r x) ≠ 0
      rw [hermitian_add_left, hH, hr x, perpendicularRotation, h.add_right, h.smul_right, hyx,
        ← add_assoc, add_self_column F, zero_add]
      exact mul_ne_zero hx (mul_ne_zero (inv_ne_zero b.ne_zero) hx)
    obtain ⟨p, r', hp, hr', hH', hQ', he⟩ := step ((hQ x).trans hxy) hn'
    refine ⟨r.trans r', [(x' + y, p), (x, b)], ?_, ?_, ?_, ?_, he⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl)
      · exact hp
      · exact hb
    · intro z
      change r' (r z) = perpendicularRotation h (r x + y) p (perpendicularRotation h x b z)
      rw [hr' (r z), hr z]
    · intro z z'
      exact (hH' _ _).trans (hH z z')
    · intro z
      exact (hQ' _).trans (hQ z)
  · obtain ⟨p, r, hp, hr, hH, hQ, he⟩ := step hxy hn
    refine ⟨r, [(x + y, p)], ?_, hr, hH, hQ, he⟩
    simpa only [List.mem_singleton, forall_eq] using hp

private def perpendicularSubmodule (h : HermitianPairing s V) (e : V) : Submodule Bᵐᵒᵖ V :=
  (rightPairing h e).ker

private theorem mem_perpendicular (h : HermitianPairing s V) (e y : V) :
    y ∈ perpendicularSubmodule h e ↔ h.value e y = 0 := by
  change op (h.value e y) = 0 ↔ _
  rw [← op_zero (α := B), op_inj]

private theorem hermitian_zero_swap (h : HermitianPairing s V) {x y : V}
    (hxy : h.value x y = 0) : h.value y x = 0 := by
  rw [← hermitian_bar h x y, hxy]
  simp [antiValue]

private def perpendicularProject (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) : V →ₗ[Bᵐᵒᵖ] perpendicularSubmodule h e :=
  (LinearMap.id -
    ((LinearMap.toSpanSingleton Bᵐᵒᵖ V e).comp
      (LinearMap.mulRight Bᵐᵒᵖ (op (h.value e e)⁻¹))).comp
      (rightPairing h e)).codRestrict _ (fun y => by
        apply (mem_perpendicular h e _).mpr
        change h.value e (y - e ◁ ((h.value e e)⁻¹ * h.value e y)) = 0
        rw [hermitian_sub_right, h.smul_right, mul_inv_cancel_left₀ he, sub_self])

private theorem perpendicularProject_apply (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) (y : V) :
    (perpendicularProject h e he y : V) = y - e ◁ ((h.value e e)⁻¹ * h.value e y) := rfl

private theorem pairing_perpendicularProject (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) (x : perpendicularSubmodule h e) (y : V) :
    h.value x (perpendicularProject h e he y) = h.value x y := by
  have hxe := hermitian_zero_swap h ((mem_perpendicular h e _).mp x.property)
  rw [perpendicularProject_apply, hermitian_sub_right, h.smul_right, hxe, zero_mul, sub_zero]

private def perpendicularPairing (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) : HermitianPairing s (perpendicularSubmodule h e) where
  value x y := h.value x y
  add_right x y z := h.add_right x y z
  smul_right x y a := h.smul_right x y a
  hermitian x y := h.hermitian x y
  central_norm x := h.central_norm x
  nondegenerate x hx := by
    obtain ⟨y, hy⟩ := h.nondegenerate x (fun hzero => hx (Subtype.ext hzero))
    exact ⟨perpendicularProject h e he y, fun hz => hy ((pairing_perpendicularProject h e he x y).symm.trans hz)⟩

private def perpendicularEndomorphism (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) (ell : V →ₗ[Bᵐᵒᵖ] V) :
    perpendicularSubmodule h e →ₗ[Bᵐᵒᵖ] perpendicularSubmodule h e :=
  (perpendicularProject h e he).comp (ell.comp (perpendicularSubmodule h e).subtype)

private theorem perpendicular_trace_one (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell) :
    IsTraceOne (perpendicularPairing h e he) (perpendicularEndomorphism h e he ell) := by
  intro x y
  change h.value (perpendicularProject h e he (ell x)) y +
      h.value x (perpendicularProject h e he (ell y)) = h.value x y
  rw [← hermitian_bar h y (perpendicularProject h e he (ell x)),
    pairing_perpendicularProject, hermitian_bar, pairing_perpendicularProject]
  exact ht x y

private theorem perpendicular_refinement (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) (ell : V →ₗ[Bᵐᵒᵖ] V) (x : perpendicularSubmodule h e) :
    refinement (perpendicularPairing h e he) (perpendicularEndomorphism h e he ell) x =
      refinement h ell x := by
  change scalarClass F (h.value x (perpendicularProject h e he (ell x))) =
    scalarClass F (h.value x (ell x))
  rw [pairing_perpendicularProject]

private theorem perpendicular_word_apply (h : HermitianPairing s V) (e : V)
    (he : h.value e e ≠ 0) (l : List (perpendicularSubmodule h e × Bˣ))
    (x : perpendicularSubmodule h e) (a : B) :
    (l.map (fun p => ((p.1 : V), p.2))).foldr
        (fun p t => perpendicularRotation h p.1 (p.2 : B) t) (x + e ◁ a) =
      (l.foldr (fun p t => perpendicularRotation (perpendicularPairing h e he) p.1 (p.2 : B) t) x :
        perpendicularSubmodule h e) + e ◁ a := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, ih]
    let y := l.foldr
      (fun p t => perpendicularRotation (perpendicularPairing h e he) p.1 (p.2 : B) t) x
    change perpendicularRotation h (p.1 : V) p.2 ((y : V) + e ◁ a) =
      perpendicularRotation h (p.1 : V) p.2 y + e ◁ a
    have hp := hermitian_zero_swap h ((mem_perpendicular h e _).mp p.1.property)
    simp only [perpendicularRotation, h.add_right, h.smul_right, hp, zero_mul, add_zero]
    exact add_right_comm _ _ _

private def HasRotationWord (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V)
    (g : V ≃ₗ[Bᵐᵒᵖ] V) : Prop :=
  ∃ l : List (V × Bˣ),
    (∀ p ∈ l, scalarClass F (p.2 : B) = refinement h ell p.1) ∧
    ∀ y, g y = l.foldr (fun p y₀ => perpendicularRotation h p.1 (p.2 : B) y₀) y

/-- Polarization and right scaling recover the full pairing from the refinement. -/
private theorem pairing_preserved_by_refinement (href : RefinementIdentities.{u,v,w})
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, antiValue s a = quaternionConjugate hB a)
    (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    (g : V ≃ₗ[Bᵐᵒᵖ] V) (hg : ∀ x, refinement h ell (g x) = refinement h ell x) :
    ∀ x y, h.value (g x) (g y) = h.value x y := by
  obtain ⟨_, _, hadd, tr, htr, _⟩ := href hB hd s hs h ell ht
  have hclass (x y : V) : scalarClass F (h.value (g x) (g y)) = scalarClass F (h.value x y) := by
    have he := hg (x + y)
    rw [map_add, hadd, hadd, hg x, hg y] at he
    exact add_left_cancel he
  intro x y
  by_contra hne
  let d := h.value (g x) (g y) - h.value x y
  have hd' : d ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨_, _, _, _, htrace⟩ :=
    SymplecticInvolutionModels.quaternionConjugation.{u,v,u} hB hd
  obtain ⟨b, hb⟩ := htrace 1
  let a := d⁻¹ * b
  have hc := hclass x (op a • y)
  rw [map_smul, h.smul_right, h.smul_right] at hc
  have hz : scalarClass F (d * a) = 0 := by
    change scalarClass F ((h.value (g x) (g y) - h.value x y) * a) = 0
    rw [sub_mul, map_sub, hc, sub_self]
  rw [show d * a = b from by rw [show a = d⁻¹ * b from rfl, mul_inv_cancel_left₀ hd']] at hz
  have he := congrArg tr hz
  rw [htr, hb, map_zero] at he
  exact one_ne_zero he

private theorem perpendicular_generation (href : RefinementIdentities.{u,v,w}) :
    PerpendicularGeneration.{u,v,w} := by
  intro F _ _ B _ _ hB hd s hs
  have hw : RadicalWords.{u,v,w} := radical_words href
  have generate (n : ℕ) :
      ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] [Module.Finite Bᵐᵒᵖ V],
        Module.finrank Bᵐᵒᵖ V = n →
        ∀ (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V), IsTraceOne h ell →
          ∀ g : V ≃ₗ[Bᵐᵒᵖ] V,
            (∀ x y, h.value (g x) (g y) = h.value x y) →
            (∀ x, refinement h ell (g x) = refinement h ell x) →
            HasRotationWord h ell g := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ _ hn h ell ht g hgH hgQ
      by_cases hv : ∃ x : V, x ≠ 0
      · obtain ⟨x, hx⟩ := hv
        obtain ⟨e, he⟩ := exists_nonzero_norm hB hd hs h hx
        obtain ⟨r, l, hl, hr, hrH, hrQ, hre⟩ :=
          rotation_align href hw hB hd hs h ell ht he (hgQ e).symm
        let f := g.trans r.symm
        have hfe : f e = e := r.injective (by simpa [f] using hre.symm)
        have hfH (x y : V) : h.value (f x) (f y) = h.value x y := by
          rw [← hrH (f x) (f y)]
          simpa [f] using hgH x y
        have hfQ (x : V) : refinement h ell (f x) = refinement h ell x := by
          rw [← hrQ (f x)]
          simpa [f] using hgQ x
        let W := perpendicularSubmodule h e
        have hW : W ≠ ⊤ := by
          intro htop
          have hmem : e ∈ W := by rw [htop]; exact Submodule.mem_top
          exact he ((mem_perpendicular h e _).mp hmem)
        have hdim : Module.finrank Bᵐᵒᵖ W < n :=
          (Submodule.finrank_lt hW).trans_eq hn
        let fW := (f.toLinearMap.comp W.subtype).codRestrict W (fun x => by
          apply (mem_perpendicular h e _).mpr
          change h.value e (f x) = 0
          rw [← hfe, hfH]
          exact (mem_perpendicular h e _).mp x.property)
        have hfWinj : Function.Injective fW := by
          intro a b hab
          exact Subtype.ext (f.injective (congrArg Subtype.val hab))
        let gW := LinearEquiv.ofBijective fW ⟨hfWinj, LinearMap.injective_iff_surjective.mp hfWinj⟩
        have hgW (x : W) : (gW x : V) = f x := rfl
        let hW' := perpendicularPairing h e he
        let ellW := perpendicularEndomorphism h e he ell
        have HgW (x y : W) : hW'.value (gW x) (gW y) = hW'.value x y := hfH x y
        have QgW (x : W) : refinement hW' ellW (gW x) = refinement hW' ellW x := by
          rw [perpendicular_refinement, perpendicular_refinement, hgW, hfQ]
        obtain ⟨m, hm, hrep⟩ :=
          ih _ hdim rfl hW' ellW (perpendicular_trace_one h e he ell ht) gW HgW QgW
        let m' := m.map (fun (p : W × Bˣ) => ((p.1 : V), p.2))
        have hm' (p : V × Bˣ) (hp : p ∈ m') :
            scalarClass F (p.2 : B) = refinement h ell p.1 := by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact (hm q hq).trans (perpendicular_refinement h e he ell q.1)
        have hf (x : V) :
            f x = m'.foldr (fun p t => perpendicularRotation h p.1 (p.2 : B) t) x := by
          let a := (h.value e e)⁻¹ * h.value e x
          let y := perpendicularProject h e he x
          have hy : (y : V) + e ◁ a = x := sub_add_cancel x _
          have hstep := perpendicular_word_apply h e he m y a
          rw [← hrep y, hgW, hy] at hstep
          calc
            f x = f ((y : V) + e ◁ a) := congrArg f hy.symm
            _ = f y + e ◁ a := by rw [map_add, map_smul, hfe]
            _ = _ := hstep.symm
        refine ⟨l ++ m', ?_, ?_⟩
        · intro p hp
          exact (List.mem_append.mp hp).elim (hl p) (hm' p)
        · intro x
          calc
            g x = r (f x) := (r.apply_symm_apply (g x)).symm
            _ = (l ++ m').foldr (fun p t => perpendicularRotation h p.1 (p.2 : B) t) x := by
              rw [List.foldr_append, ← hf, hr]
      · push Not at hv
        exact ⟨[], by simp, fun y => (hv (g y)).trans (hv y).symm⟩
  intro V _ _ _ h ell ht g hgQ
  exact generate _ rfl h ell ht g
    (pairing_preserved_by_refinement href hB hd hs h ell ht g hgQ) hgQ

open Polynomial
open scoped commutatorElement

open private quadratic_identity from LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators

private theorem conjugate_mul_eq_norm (hB : isCentralSimple F B)
    (hd : degree F B = 2) (hs : ∀ a, bar a = quaternionConjugate hB a) (a : B) :
    bar a * a = algebraMap F B (reducedNorm hB a) := by
  have hquad : a * a - algebraMap F B (reducedTrace hB a) * a =
      -algebraMap F B (reducedNorm hB a) :=
    eq_neg_of_add_eq_zero_left (quadratic_identity hB hd a)
  rw [hs, quaternionConjugate, sub_mul, ← neg_sub, hquad, neg_neg]

private theorem nonscalar_of_trace_ne_zero
    (hB : isCentralSimple F B) (hs : ∀ a, bar a = quaternionConjugate hB a)
    {b : B} (hb : reducedTrace hB b ≠ 0) : b ∉ Set.range (algebraMap F B) := by
  rintro ⟨c, hc⟩
  have hz : bar b + b = 0 := by
    rw [← hc, bar_scalar, add_self_column F]
  apply hb
  apply (algebraMap F B).injective
  rw [map_zero, ← bar_add_eq_trace hB hs]
  exact hz

private theorem exists_quadratic_field
    (hB : isCentralSimple F B) (hd : degree F B = 2)
    (hs : ∀ a, bar a = quaternionConjugate hB a) (b : B) (ht : reducedTrace hB b ≠ 0) :
    ∃ (E : Type v) (_ : Field E) (_ : Algebra F E)
      (_ : Algebra.IsSeparable F E) (i : E →ₐ[F] B),
      b ∈ Set.range i ∧ Module.finrank F E = 2 ∧
      ∀ e : Eˣ, i (e : E) ∉ Set.range (algebraMap F B) →
        ∃ (c : F) (r : Fˣ), i (e : E) = algebraMap F B (r : F) * (b + algebraMap F B c) := by
  let q : F[X] := -(C (reducedTrace hB b) * X) + C (reducedNorm hB b)
  let p : F[X] := X ^ 2 + q
  have hqdeg : q.natDegree ≤ 1 := calc
    q.natDegree ≤ max (-(C (reducedTrace hB b) * X)).natDegree
        (C (reducedNorm hB b)).natDegree := natDegree_add_le _ _
    _ ≤ 1 := by simp [natDegree_C_mul_X _ ht]
  have hqdeg' : q.degree < (2 : ℕ) := degree_le_natDegree.trans_lt (by
    exact_mod_cast (show q.natDegree < 2 by omega))
  have hmonic : p.Monic := monic_X_pow_add hqdeg'
  have hpdeg : p.natDegree = 2 := by
    change (X ^ 2 + q).natDegree = 2
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]
    omega
  have heval : aeval b p = 0 := by
    simpa [p, q, sub_eq_add_neg, pow_two, add_assoc] using
      (show b * b - algebraMap F B (reducedTrace hB b) * b +
        algebraMap F B (reducedNorm hB b) = 0 from quadratic_identity hB hd b)
  have hbi : IsIntegral F b := ⟨p, hmonic, heval⟩
  have hbmin := minpoly.irreducible hbi
  have hbdiv : minpoly F b ∣ p := minpoly.dvd F b heval
  have hminDeg : 2 ≤ (minpoly F b).natDegree := by
    have hpos := degree_pos_of_irreducible hbmin
    have hl : 0 < (minpoly F b).natDegree := by
      exact_mod_cast hpos.trans_le degree_le_natDegree
    have hne : (minpoly F b).natDegree ≠ 1 := by
      intro hone
      apply nonscalar_of_trace_ne_zero hB hs ht
      apply minpoly.mem_range_of_degree_eq_one
      exact (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < (1 : ℕ))).mpr hone
    omega
  have hmin : p = minpoly F b :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hbi) hmonic hbdiv (hpdeg ▸ hminDeg)
  have hpirr : Irreducible p := hmin ▸ hbmin
  have hder : derivative p = -C (reducedTrace hB b) := by
    have htwo : (1 : F) + 1 = 0 := by
      simpa only [one_add_one_eq_two] using (CharP.ofNat_eq_zero F 2)
    simp [p, q, htwo]
  have hpsep : p.Separable := (separable_iff_derivative_ne_zero hpirr).mpr (by simp [hder, ht])
  let S := Algebra.adjoin F ({b} : Set B)
  let E : Type v := S
  let i : E →ₐ[F] B := S.val
  have hinji : Function.Injective i := Subtype.val_injective
  let bE : E := ⟨b, Algebra.subset_adjoin rfl⟩
  have hi : i bE = b := rfl
  have hgen (x : E) : ∃ f : F[X], aeval bE f = x := by
    obtain ⟨f, hf⟩ := Algebra.adjoin_eq_exists_aeval (x := b) F x
    refine ⟨f, hinji ?_⟩
    rw [← AlgHom.comp_apply, ← aeval_algHom, hi]
    exact hf
  have hminE : minpoly F bE = p := by
    rw [← minpoly.algHom_eq i hinji, hi, ← hmin]
  have hdimE : (minpoly F bE).natDegree = 2 := hminE ▸ hpdeg
  have hbiE : IsIntegral F bE := (isIntegral_algHom_iff i hinji).mp hbi
  let bpow : Module.Basis (Fin (minpoly F bE).natDegree) F E :=
    Module.Basis.mk (linearIndependent_pow bE) (by
      intro x _
      obtain ⟨f, hf⟩ := hgen x
      exact hbiE.mem_span_pow ⟨f, hf.symm⟩)
  let β : Module.Basis (Fin 2) F E := bpow.reindex (finCongr hdimE)
  have hβ (j : Fin 2) : β j = bE ^ (j : ℕ) := by
    simp only [β, Module.Basis.reindex_apply, bpow, Module.Basis.mk_apply,
      finCongr_symm_apply_coe]
  have hβ₀ : β 0 = 1 := by simpa using hβ 0
  have hβ₁ : β 1 = bE := by simpa using hβ 1
  let : Module.Finite F E := Module.Finite.of_basis β
  have hEfield : IsField E := by
    refine ⟨⟨0, 1, zero_ne_one⟩, ?_, ?_⟩
    · intro x y
      obtain ⟨f, rfl⟩ := hgen x
      obtain ⟨g, rfl⟩ := hgen y
      rw [← map_mul, mul_comm f g, map_mul]
    · intro x hx
      have hinj : Function.Injective (LinearMap.mulLeft F x) := by
        intro y z hyz
        apply hinji
        have hn : i x ≠ 0 := by simpa only [map_zero i] using hinji.ne hx
        apply mul_right_injective₀ hn
        simpa only [LinearMap.mulLeft_apply, map_mul] using congrArg i hyz
      exact (LinearMap.injective_iff_surjective.mp hinj) 1
  let : Field E := hEfield.toField
  have hspan (x : E) : x =
      algebraMap F E (β.repr x 0) + algebraMap F E (β.repr x 1) * bE := by
    simpa [Fin.sum_univ_two, hβ₀, hβ₁, Algebra.smul_def] using (β.sum_repr x).symm
  have hsroot : IsSeparable F bE := by
    change (minpoly F bE).Separable
    rwa [hminE]
  let : Algebra.IsSeparable F E := ⟨fun x => by
    rw [hspan x]
    exact Field.isSeparable_add (isSeparable_algebraMap _)
      (Field.isSeparable_mul (isSeparable_algebraMap _) hsroot)⟩
  refine ⟨E, inferInstance, inferInstance, inferInstance, i, ⟨bE, hi⟩,
    (Module.finrank_eq_card_basis β).trans (Fintype.card_fin 2), ?_⟩
  intro e he
  let a := β.repr (e : E) 1
  let c := β.repr (e : E) 0
  have hie : i (e : E) = algebraMap F B c + algebraMap F B a * b := by
    simpa only [map_add, map_mul, i.commutes, hi] using congrArg i (hspan (e : E))
  have ha : a ≠ 0 := by
    intro ha
    exact he ⟨c, by simp [hie, ha]⟩
  refine ⟨c / a, Units.mk0 a ha, ?_⟩
  change i (e : E) = algebraMap F B a * (b + algebraMap F B (c / a))
  rw [hie, mul_add, ← map_mul, mul_div_cancel₀ _ ha, add_comm]

private theorem fixed_field_words (href : RefinementIdentities.{u,v,w}) :
    FixedFieldWords.{u,v,w} := by
  intro F _ _ B _ _ hB hd s hs V _ _ _ h ell ht
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨w₀, hw₀⟩ := exists_nonzero_norm hB hd hs h hx
  let b := h.value w₀ (ell w₀)
  have hb : scalarClass F b = refinement h ell w₀ := rfl
  have htr : reducedTrace hB b ≠ 0 := by
    have hn := norm_eq_add_bar h ell ht w₀ b hb
    rw [bar_add_eq_trace hB hs] at hn
    intro hz
    exact hw₀ (by simpa [hz] using hn)
  obtain ⟨E, _, _, _, i, hbi, hdim, hfam⟩ := exists_quadratic_field hB hd hs b htr
  refine ⟨w₀, b, E, ‹Field E›, ‹Algebra F E›, ‹Algebra.IsSeparable F E›, i,
    hw₀, hb, htr, hbi, hdim, hfam, ?_⟩
  intro c
  have hbn : b + algebraMap F B c ≠ 0 := by
    intro hz
    apply nonscalar_of_trace_ne_zero hB hs htr
    exact ⟨-c, (map_neg _ _).trans (eq_neg_of_add_eq_zero_left hz).symm⟩
  let b₀ := Units.mk0 (b + algebraMap F B c) hbn
  refine ⟨b₀, rfl, ?_⟩
  intro a
  dsimp only
  let aBar := (Units.opEquiv (Units.map s.toMonoidHom a)).unop
  let t := ⁅aBar, b₀⁆
  let b₁ := antiValue s (a : B) * (b₀ : B) * (a : B)
  let N := algebraMap F B (reducedNorm hB (a : B))
  change scalarClass F b₁ = refinement h ell (w₀ ◁ (a : B)) ∧
    perpendicularRotation h (w₀ ◁ (a : B)) b₁ = perpendicularRotation h w₀ (b₀ : B) ∧
    ∀ p, let q := weylWord h w₀ (b₀ : B) p
      weylWord h (w₀ ◁ (a : B)) b₁ p =
        (N * (t : B) * q.1, q.2.1, (N * antiValue s (t : B))⁻¹ * q.2.2)
  have hb₀ : scalarClass F (b₀ : B) = refinement h ell w₀ := by
    change scalarClass F (b + algebraMap F B c) = _
    rw [map_add, class_scalar, add_zero, hb]
  have hbar := bar_ne_zero (s := s) a.ne_zero
  have hb₁ : b₁ ≠ 0 := mul_ne_zero (mul_ne_zero hbar b₀.ne_zero) a.ne_zero
  obtain ⟨hscale, hdescend, _, _⟩ := href hB hd s hs h ell ht
  have hq₁ : scalarClass F b₁ = refinement h ell (w₀ ◁ (a : B)) :=
    ((hscale w₀ (a : B)).trans (hdescend _ _ _ hb₀.symm)).symm
  have hrot : perpendicularRotation h (w₀ ◁ (a : B)) b₁ =
      perpendicularRotation h w₀ (b₀ : B) := by
    funext y
    simp only [perpendicularRotation, column_smul_mul, hermitian_smul_left, b₁, mul_inv_rev,
      mul_assoc, mul_inv_cancel_left₀ a.ne_zero, inv_mul_cancel_left₀ hbar]
  have ha : (a : B) = (antiValue s (a : B))⁻¹ * N := by
    dsimp only [N]
    rw [← conjugate_mul_eq_norm hB hd hs, inv_mul_cancel_left₀ hbar]
  have htval : (t : B) =
      antiValue s (a : B) * (b₀ : B) * (antiValue s (a : B))⁻¹ * (b₀ : B)⁻¹ := by
    change ((⁅aBar, b₀⁆ : Bˣ) : B) = _
    simp only [commutatorElement_def, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hcomm (x : B) : N * x = x * N := Algebra.commutes _ _
  have hratio : b₁ = N * (t : B) * (b₀ : B) := by
    calc
      b₁ = (antiValue s (a : B) * (b₀ : B) * (antiValue s (a : B))⁻¹) * N := by
        exact (congrArg (fun x => antiValue s (a : B) * (b₀ : B) * x) ha).trans
          (mul_assoc _ _ _).symm
      _ = N * (t : B) * (b₀ : B) := by
        rw [← hcomm, htval, mul_assoc N, inv_mul_cancel_right₀ b₀.ne_zero]
  have hw : RadicalWords.{u,v,w} := radical_words href
  obtain ⟨_, _, hw₀'⟩ := hw hB hd hs h ell ht w₀ (b₀ : B) hb₀
  obtain ⟨_, _, hw₁'⟩ := hw hB hd hs h ell ht (w₀ ◁ (a : B)) b₁ hq₁
  refine ⟨hq₁, hrot, ?_⟩
  have hbarRatio :
      (antiValue s b₁)⁻¹ =
        (N * antiValue s (t : B))⁻¹ * (antiValue s (b₀ : B))⁻¹ := by
    rw [hratio, bar_mul, bar_mul, show antiValue s N = N from bar_scalar _,
      ← hcomm, mul_inv_rev]
  rintro ⟨x, y, z⟩
  dsimp only
  rw [(hw₀' b₀.ne_zero).2.2, (hw₁' hb₁).2.2, hrot, hbarRatio, hratio]
  simp only [mul_assoc]

end Columns

section ScaleCocharacter

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open Specs.Arithmetic.QuaternionSpinScaleCover
open Specs.Arithmetic.QuaternionScalarCliffordLift
  (scalarPairMatrix scalarDiagonal LiftsScalarPair IsPairDiagonal)
open Specs.SymplecticDivisionForms (extendAnti tensorMap)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open CocharacterDynamics (cocharacterPoint mapPoints_unitPoint unitPoint)


variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

private noncomputable abbrev fieldProjection (M : SpinModel G D) :
    GroupPoints G.val (CommAlgCat.of F F) →* (F ⊗[F] ρ.fixedSubalgebra)ˣ :=
  spinVectorProjection M (CommAlgCat.of F F)

private def scalarUnit (R : TestAlgebra F) : Rˣ →* (R ⊗[F] B)ˣ :=
  Units.map (algebraMap R (R ⊗[F] B)).toMonoidHom

private theorem spin_projection_injective_of_reduced [CharP F 2]
    (M : SpinModel G D) (R : TestAlgebra F) [_root_.IsReduced R] :
    Function.Injective (spinVectorProjection M R) := by
  intro x y hxy
  let π : Points G.val.X R →* Points M.neutral.val.X R :=
    (((groupPointsFunctor F).map M.projection).app R).hom
  have hπ : π x = π y := by
    let : IsOpenImmersion M.inclusion.hom.hom.left := M.openImmersion
    let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono M.inclusion.hom.hom).mp
    apply M.fullFaithful R
    change M.fullPoints R ((x ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom) =
      M.fullPoints R ((y ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom)
    rw [Category.assoc, Category.assoc]
    exact hxy
  have hker : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hπ, mul_inv_cancel]
  let p : Points M.kernel.group.X R := M.isKernel.lift (x * y⁻¹) (toUnit _) hker
  have hp : p ≫ M.kernel.inclusion.hom.hom = x * y⁻¹ := M.isKernel.lift_fst _ _ _
  let a := (M.kernelPoints R p).val
  have ha : (a : R) ^ 2 = 1 := (mem_rootsOfUnity' 2 a).mp (M.kernelPoints R p).property
  have htwo : (2 : R) = 0 := by
    rw [← map_ofNat (algebraMap F R) 2, CharP.ofNat_eq_zero F 2, map_zero]
  have ha₁ : (a : R) = 1 := by
    apply sub_eq_zero.mp
    apply IsNilpotent.eq_zero
    refine ⟨2, ?_⟩
    rw [sub_sq, ha, htwo, zero_mul, zero_mul, sub_zero, one_pow, one_add_one_eq_two, htwo]
  have hp₁ : p = 1 := by
    apply (M.kernelPoints R).injective
    rw [map_one]
    exact Subtype.ext (Units.ext ha₁)
  have hxy₁ : x * y⁻¹ = 1 := by
    rw [← hp, hp₁]
    exact map_one (((groupPointsFunctor F).map M.kernel.inclusion).app R).hom
  exact mul_inv_eq_one.mp hxy₁

open scoped commutatorElement
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

open private exists_mixed_commutator
  from LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators

private theorem normAt_base {J : Type u} [Fintype J] (b : Module.Basis J F B) (x : B) :
    normAt hB b ((1 : F) ⊗ₜ[F] x) = reducedNorm hB x := by
  change _ = RM03.CSA.reducedNorm hB x
  rw [← RM03.CSA.reducedNorm_basis_eval hB b x]
  simp [normAt, MvPolynomial.eval₂_id, smul_eq_mul]
  rfl

private def tensorUnits : Bˣ ≃* (F ⊗[F] B)ˣ :=
  Units.mapEquiv (Algebra.TensorProduct.lid F B).symm.toMulEquiv

/-- The norm-one word theorem and the scalar words generate all scale lifts
on the characteristic-two field, where the vector projection is injective. -/
private theorem scale_preimage_mem_of_mixed_words [CharP F 2]
    [FiniteDimensional F K] [IsGalois F K]
    (hcover : SpinScaleCover.{u}) (hnorm : QuaternionNormOnUnits.{u})
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (hrank : 4 ≤ Fintype.card I) (hd : degree F B = 2)
    {E : Type u} [Field E] [Algebra F E] (iE : E →ₐ[F] B) (hE : Module.finrank F E = 2)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F)))
    (hscalar : ∀ r : Fˣ, ∃ g ∈ H,
      fieldProjection M g =
        quaternionScale Q (CommAlgCat.of F F) (scalarUnit (CommAlgCat.of F F) r))
    (hmixed : ∀ a : Bˣ, ∀ b : Eˣ, ∃ g ∈ H,
      fieldProjection M g =
        quaternionScale Q (CommAlgCat.of F F) (tensorUnits ⁅a, Units.map iE.toMonoidHom b⁆)) :
    ∀ x : spinScalePreimage M Q (CommAlgCat.of F F), x.val.1 ∈ H := by
  let : Module.Finite F B := hB.2.2
  let b := (Module.finBasis F B).reindex (Equiv.ulift.{u}.symm)
  obtain ⟨_, N, e, hN, he, _, _, _⟩ := hcover M hrank hB hd d Q b
  let R := CommAlgCat.of F F
  obtain ⟨N', hN', hs⟩ := hnorm hB hd b R
  intro x
  let r := (e R x).val.2
  have hn : N R x.val.2 = r ^ 2 := by
    have h := (e R x).property
    change N R (e R x).val.1 = r ^ 2 at h
    rwa [he R x] at h
  have hnr : N R (scalarUnit R r) = r ^ 2 :=
    (Units.ext ((hN R _).trans (hN' _).symm)).trans (hs r)
  let t := tensorUnits.symm (x.val.2 * (scalarUnit R r)⁻¹)
  have ht : tensorUnits t = x.val.2 * (scalarUnit R r)⁻¹ :=
    tensorUnits.apply_symm_apply _
  have htN : N R (tensorUnits t) = 1 := by
    rw [ht, map_mul, map_inv, hn, hnr, mul_inv_cancel]
  have htn : reducedNorm hB (t : B) = 1 := by
    have h := hN R (tensorUnits t)
    rw [htN] at h
    change 1 = normAt hB b ((1 : F) ⊗ₜ[F] (t : B)) at h
    simpa only [normAt_base] using h.symm
  obtain ⟨g, hg, hgv⟩ : ∃ g ∈ H,
      fieldProjection M g = quaternionScale Q R (tensorUnits t) := by
    by_cases ht₁ : t = 1
    · exact ⟨1, H.one_mem, by simp [ht₁]⟩
    · obtain ⟨a, b₀, hab⟩ := exists_mixed_commutator hB hd iE hE htn ht₁
      rw [hab]
      exact hmixed a b₀
  obtain ⟨z, hz, hzv⟩ := hscalar r
  have hprojection : fieldProjection M (g * z) = fieldProjection M x.val.1 := by
    rw [map_mul, hgv, hzv, ← map_mul, ht, inv_mul_cancel_right]
    exact x.property.symm
  exact (spin_projection_injective_of_reduced M R hprojection) ▸ H.mul_mem hg hz

end ScaleCocharacter

section GenerationReductions

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj RatFunc
open Specs.GeometricRadicals (IsSemisimple)
open Specs.Arithmetic.NontrialitarianSpinModels (HasFixedVectorVertex)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral localPlus)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData SeparatingParameter)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (StrongApproximation)
open CocharacterDynamics (oppositeCocharacter existsLimitDecomposition)

open private central_iff_comp_eq_zero cocharacter_into_finite_is_zero
  from LinearAlgebraicGroups.Descent.RelativeRank
open private liftToSchemeKernel from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private reductive_of_semisimple
  from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

private theorem noncentral_of_ne_zero {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    (hG : IsSemisimple G) (c : Cocharacter G.val) (hc : c ≠ 0) : IsNoncentral c := by
  have hR := reductive_of_semisimple G hG
  obtain ⟨Z, Q, q, hq, _⟩ := Descent.AdjointCocharacters.adjointQuotientExists G hR
  by_contra hcentral
  have hcentral' : Specs.RelativeRank.IsCentralCocharacter c := by
    intro X g
    by_contra hg
    exact hcentral ⟨X, g, hg⟩
  obtain ⟨a, ha⟩ := liftToSchemeKernel hq.2.1 c ((central_iff_comp_eq_zero hq c).mp hcentral')
  have hfin := (Reductive.CentralDerived.semisimpleIffFiniteCentre G hR Z hq.1).mp hG
  have hz := cocharacter_into_finite_is_zero (Specs.Unipotent.closedSubgroupAlgebraicGroup Z) hfin a
  exact hc (ha.symm.trans ((congrArg (fun a => a ≫ Z.inclusion) hz).trans zero_comp))

private theorem arithmetic_absolute_simplicity {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (hG : AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G) :
    Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G := by
  refine ⟨hG.1, ?_, ?_⟩
  · rintro ⟨e⟩
    exact hG.2.1 ((Grp.isZero_trivial _).of_iso e)
  · intro N hN
    exact (hG.2.2 N hN).imp (fun hz => ⟨hz.iso (Grp.isZero_trivial _)⟩) id

private theorem separating_parameter_arithmetic_field {F : Type u} [Field F]
    (k : Type v) [Field k] [Finite k] [Algebra k F] (t : SeparatingParameter k F) :
    IsCharacteristicTwoArithmeticField.{u,v} F := by
  let : Algebra k⟮X⟯ F := t.rationalAlgebra
  exact Or.inl ⟨k, inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem strongApproximation_of_completion_density
    (hiso : NontrialitarianIsotropy.{u,v}) (F : Type u) [Field F] [CharP F 2]
    (hF : IsCharacteristicTwoArithmeticField.{u,v} F) (D : GlobalFieldData.{u,v} F)
    (G : AffineAlgebraicGroup F) (n : ℕ) (hn : 4 ≤ n)
    (hG : AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G)
    (hsc : SimplyConnectedLattice.GeometricallySimplyConnected G)
    (hv : HasFixedVectorVertex G n) (i : MatrixRealization G)
    (S : Finset D.Place) (hS : S.Nonempty)
    (hloc : ∀ w : D.Place, Dense (localPlus D i w)) : StrongApproximation D i S := by
  obtain ⟨c, hc⟩ := hiso F hF G n hn hG hsc hv
  have hc' := noncentral_of_ne_zero G hG.1 c hc
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨Q⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  exact ((OppositeRadicals.approximation D G i
    (arithmetic_absolute_simplicity hG) c hc' P Q).2.2.2.2 S hS).2
      (fun w => hloc w.val)

end GenerationReductions

theorem radicalWords : RadicalWords.{u,v,w} :=
  radical_words CharacteristicTwoQuadraticPairs.refinementIdentities

theorem perpendicularGeneration : PerpendicularGeneration.{u,v,w} :=
  perpendicular_generation CharacteristicTwoQuadraticPairs.refinementIdentities

theorem fixedFieldWords : FixedFieldWords.{u,v,w} :=
  fixed_field_words CharacteristicTwoQuadraticPairs.refinementIdentities

theorem scalarPairLift : ScalarPairLift.{u} :=
  QuaternionScalarCliffordLift.scalarCliffordLift


section RationalPoints

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.GeometricRadicals (IsReductive)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition HasLimit oppositeCocharacter existsLimitDecomposition)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open Specs.IntegralModels (MatrixRealization)

open private contracts_mem_sections field_point_centralizes from LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
open private testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from LinearAlgebraicGroups.Relative.RationalDensity

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {c : Cocharacter G.val}

private theorem contract_of_factor (D : LimitDecomposition c)
    (q : GroupPoints D.contracting.group (CommAlgCat.of F F)) :
    HasLimit c (q ≫ D.contracting.inclusion.hom.hom) 1 :=
  (D.contracting_points (CommAlgCat.of F F) _).2 ⟨q, rfl⟩

private theorem cut_section {J X : SchemeOver F} (m : J ⟶ X)
    (q : 𝟙_ (SchemeOver F) ⟶ J)
    (p : (testSpec F).obj (op (CommAlgCat.of F F)) ⟶ X)
    (h : q ≫ m = (rationalSourceIso F).hom ≫ p) :
    p = ((rationalSourceIso F).inv ≫ q) ≫ m := by
  rw [Category.assoc, h, (rationalSourceIso F).inv_hom_id_assoc]

private theorem contracts_of_section (D : LimitDecomposition c)
    (p : GroupPoints G.val (CommAlgCat.of F F))
    (hp : testPointSections G.val p ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F))) :
    HasLimit c p 1 := by
  obtain ⟨q, hq⟩ := hp
  have he := cut_section D.contracting.inclusion.hom.hom q p hq
  rw [he]
  exact contract_of_factor D ((rationalSourceIso F).inv ≫ q)

private theorem contracting_sections_le_oppositeWords
    {c' : Cocharacter G.val} (D : LimitDecomposition c')
    (h : ∀ p : GroupPoints G.val (CommAlgCat.of F F), HasLimit c' p 1 → p ∈ oppositeWords c) :
    SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ≤
      (oppositeWords c).map (testPointSections G.val).toMonoidHom := by
  intro p hp
  let e := testPointSections G.val
  let q := e.symm p
  have he : e q = p := e.apply_symm_apply p
  have hp' : e q ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F)) := by
    rwa [he]
  exact ⟨q, h q (contracts_of_section D q hp'), he⟩

private theorem oppositeWords_eq_top
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (htop : SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
      SubgroupSections E.contracting (𝟙_ (SchemeOver F)) = ⊤) :
    oppositeWords c = ⊤ := by
  let e := testPointSections G.val
  let J := (oppositeWords c).map e.toMonoidHom
  have hD : SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ≤ J :=
    contracting_sections_le_oppositeWords D (fun _ hp => Subgroup.subset_closure (Or.inl hp))
  have hE : SubgroupSections E.contracting (𝟙_ (SchemeOver F)) ≤ J :=
    contracting_sections_le_oppositeWords E (fun _ hp => Subgroup.subset_closure (Or.inr hp))
  have hJ : ⊤ ≤ J := by
    rw [← htop]
    exact sup_le hD hE
  refine top_unique fun p _ => ?_
  obtain ⟨q, hq, he⟩ := hJ (Subgroup.mem_top (e p))
  exact e.injective he ▸ hq

private theorem sections_eq_top_of_levi [Infinite F] (hG : IsReductive G)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hlevi : ∀ g : GroupPoints G.val (CommAlgCat.of F F), Centralizes c g →
      testPointSections G.val g ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
        SubgroupSections E.contracting (𝟙_ (SchemeOver F))) :
    SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
      SubgroupSections E.contracting (𝟙_ (SchemeOver F)) = ⊤ := by
  let e := testPointSections G.val
  let L := SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
    SubgroupSections E.contracting (𝟙_ (SchemeOver F))
  have hC : SubgroupSections D.centralizer (𝟙_ (SchemeOver F)) ≤ L := by
    intro p hp
    have hm : e (e.symm p) ∈ L := hlevi (e.symm p) (field_point_centralizes D hp)
    rwa [e.apply_symm_apply p] at hm
  have ht := RelativeRayGeneration.twoRadicals_sup_centralizer hG D E
  apply top_unique
  rw [← ht]
  exact sup_le le_rfl hC

private theorem point_of_section_comp (p : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    (testPointSections G.val).symm p =
      toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ p := by
  change (rationalSourceIso F).inv ≫ p = toUnit _ ≫ p
  exact congrArg (· ≫ p) (toUnit_unique _ _)

private theorem fieldPointSurjective :
    Function.Surjective (fun q : 𝟙_ (SchemeOver F) ⟶ G.val.X =>
      (toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ q :
        Points G.val.X (CommAlgCat.of F F))) := by
  intro p
  let e := testPointSections G.val
  obtain ⟨q, hq⟩ := e.symm.surjective p
  exact ⟨q, (point_of_section_comp q).symm.trans hq⟩

private theorem exists_mem_of_subgroup_eq_top {A B : Type*} [Group A] {H : Subgroup A}
    (h : H = ⊤) {f : A → B} (hf : Function.Surjective f) (b : B) :
    ∃ a ∈ H, f a = b := by
  obtain ⟨a, ha⟩ := hf b
  rw [h]
  exact ⟨a, Subgroup.mem_top a, ha⟩

private theorem point_of_section_top
    (h : unipotentGenerated G = ⊤) (p : Points G.val.X (CommAlgCat.of F F)) :
    ∃ q ∈ unipotentGenerated G, toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ q = p :=
  exists_mem_of_subgroup_eq_top h (fieldPointSurjective (G := G)) p


private noncomputable def radicalSectionWords (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c)) :
    Subgroup (𝟙_ (SchemeOver F) ⟶ G.val.X) :=
  SubgroupSections D.contracting (𝟙_ (SchemeOver F)) ⊔
    SubgroupSections E.contracting (𝟙_ (SchemeOver F))

private noncomputable def radicalPointWords (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c)) :
    Subgroup (GroupPoints G.val (CommAlgCat.of F F)) :=
  (radicalSectionWords D E).comap (testPointSections G.val).toMonoidHom

private theorem mem_comap_sup_left {A B : Type*} [Group A] [Group B]
    (f : A →* B) (S T : Subgroup B) {p : A} (hp : f p ∈ S) : p ∈ (S ⊔ T).comap f :=
  Subgroup.mem_comap.mpr (Subgroup.mem_sup_left hp)

private theorem mem_comap_sup_right {A B : Type*} [Group A] [Group B]
    (f : A →* B) (S T : Subgroup B) {p : A} (hp : f p ∈ T) : p ∈ (S ⊔ T).comap f :=
  Subgroup.mem_comap.mpr (Subgroup.mem_sup_right hp)

private theorem contracting_rational_point_in_sections {c' : Cocharacter G.val} (D : LimitDecomposition c')
    {p : GroupPoints G.val (CommAlgCat.of F F)} (hp : HasLimit c' p 1) :
    testPointSections G.val p ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F)) :=
  contracts_mem_sections D hp

private theorem limit_mem_radicalPointWords (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c))
    {p : GroupPoints G.val (CommAlgCat.of F F)} (hp : HasLimit c p 1) :
    p ∈ radicalPointWords D E := by
  have h : testPointSections G.val p ∈ SubgroupSections D.contracting (𝟙_ (SchemeOver F)) :=
    contracting_rational_point_in_sections D hp
  exact mem_comap_sup_left (testPointSections G.val).toMonoidHom
    (SubgroupSections D.contracting (𝟙_ (SchemeOver F)))
    (SubgroupSections E.contracting (𝟙_ (SchemeOver F))) h

private theorem opposite_limit_mem_radicalPointWords (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c))
    {p : GroupPoints G.val (CommAlgCat.of F F)} (hp : HasLimit (oppositeCocharacter c) p 1) :
    p ∈ radicalPointWords D E := by
  have h : testPointSections G.val p ∈ SubgroupSections E.contracting (𝟙_ (SchemeOver F)) :=
    contracting_rational_point_in_sections E hp
  exact mem_comap_sup_right (testPointSections G.val).toMonoidHom
    (SubgroupSections D.contracting (𝟙_ (SchemeOver F)))
    (SubgroupSections E.contracting (𝟙_ (SchemeOver F))) h

private theorem unipotentGenerated_eq_top_of_radicalSections (hG : IsReductive G)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (htop : radicalSectionWords D E = ⊤) :
    unipotentGenerated G = ⊤ := by
  have hle : radicalSectionWords D E ≤ unipotentGenerated G :=
    RelativeRayGeneration.twoRadicals_le_unipotentGenerated hG D E
  rw [htop] at hle
  exact top_unique hle

private theorem radicalSections_eq_top_of_levi [Infinite F] (hG : IsReductive G)
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hlevi : ∀ g : GroupPoints G.val (CommAlgCat.of F F), Centralizes c g →
      g ∈ radicalPointWords D E) :
    radicalSectionWords D E = ⊤ :=
  sections_eq_top_of_levi hG D E
    (fun g h => (Subgroup.mem_comap.mp (hlevi g h)))

end RationalPoints


section QuaternionGeneration

open Specs.AdjointRepresentation (GroupPoints)

open AlgebraicGeometry CategoryTheory Matrix ValuativeRel
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix commutatorElement
open Specs.GeometricRadicals (IsReductive IsSemisimple)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open Specs.Arithmetic.QuaternionSpinScaleCover
open Specs.Arithmetic.QuaternionHyperbolicRadicals (ComplementRefinement ActsOnColumns column)
open Specs.SymplecticDivisionForms (extendAnti)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open CocharacterDynamics (HasLimit oppositeCocharacter existsLimitDecomposition)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open private testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private contracts_mem_sections from LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

open private smooth_baseChange_iff connected_baseChange_iff
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private reductive_of_groupIso from LinearAlgebraicGroups.RootData.RankOneFlag
open private reductive_of_semisimple
  from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private cliffordSpin_semisimple from LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
open private diagonalQuaternionScale_val scaleDiagonal
  from LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover
open private extendAnti_tmul antiValue_one from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open private localField_infinite from LinearAlgebraicGroups.Arithmetic.SplitQuadraticPairSpinComparison

set_option backward.isDefEq.respectTransparency false

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

private theorem spin_model_reductive (M : SpinModel G D) (hrank : 4 ≤ Fintype.card I) :
    IsReductive G := by
  classical
  let e : Fin ((Fintype.card I - 1) + 1) ≃ I :=
    (finCongr (by omega)).trans (Fintype.equivFin I).symm
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  have hs : IsSemisimple M.splitCover.spin := cliffordSpin_semisimple M.splitCover e hrank
  have hR := reductive_of_groupIso (B := baseChangedAlgebraicGroup K G) M.splitSource.symm
    (reductive_of_semisimple M.splitCover.spin hs)
  have hG₁ : Smooth G.val.X.hom := (smooth_baseChange_iff (K := K) G.val.X).mp hR.1
  let : GeometricallyConnected (baseChangedAlgebraicGroup K G).val.X.hom := hR.2.1
  have hc : ConnectedSpace (baseChangedAlgebraicGroup K G).val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (baseChangedAlgebraicGroup K G).val.X.hom
  let : ConnectedSpace G.val.X.left := (connected_baseChange_iff (K := K) G).mp hc
  have hG₂ := geometricallyConnected_of_connected G
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension G hG₁ hG₂).mp hR

private theorem complement_dimension [CharP F 2]
    (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2) :
    2 + d = Fintype.card I := by
  let e : QuaternionPairIndex d ≃ Fin (2 + d) :=
    finSumFinEquiv
  let A := Q.matrixModel.trans (Matrix.reindexAlgEquiv F B e)
  obtain ⟨P⟩ := CharacteristicTwoQuadraticPairs.quaternionPairRecovery D hB hd _ A
  exact P.rank

private abbrev ColumnTriple (B : Type u) (d : ℕ) := B × (Fin d → B) × B

private def tensorColumn (p : ColumnTriple B d) : QuaternionPairIndex d → F ⊗[F] B :=
  fun j => (1 : F) ⊗ₜ[F] column p.1 p.2.1 p.2.2 j

private theorem tensorColumn_matrix_ext {A C : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d)
    (F ⊗[F] B)} (h : ∀ p : ColumnTriple B d, A *ᵥ tensorColumn p = C *ᵥ tensorColumn p) :
    A = C := by
  ext i j
  let v : QuaternionPairIndex d → B := Pi.single j (1 : B)
  let p : ColumnTriple B d := (v (Sum.inl 0), v ∘ Sum.inr, v (Sum.inl 1))
  have he : tensorColumn (F := F) p = Pi.single j 1 := by
    funext r
    have hr : column p.1 p.2.1 p.2.2 r = v r := by
      rcases r with r | r
      · fin_cases r <;> rfl
      · rfl
    change (1 : F) ⊗ₜ[F] column p.1 p.2.1 p.2.2 r = _
    rw [hr]
    by_cases hj : r = j
    · subst r
      simp [v, Algebra.TensorProduct.one_def]
    · simp [v, Pi.single_eq_of_ne hj]
  simpa [he] using congrFun (h p) i

private theorem actsOnColumns_mulVec (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d)
    {g : GroupPoints G.val (CommAlgCat.of F F)} {f : ColumnTriple B d → ColumnTriple B d}
    (h : ActsOnColumns M Q g f) (p : ColumnTriple B d) :
    let R := CommAlgCat.of F F
    Q.matrixAt R (fieldProjection M g).val *ᵥ tensorColumn p = tensorColumn (f p) :=
  h p

private theorem actsOnColumns_mul (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    {g h : GroupPoints G.val (CommAlgCat.of F F)} {a b : ColumnTriple B d → ColumnTriple B d}
    (hg : ActsOnColumns M Q g a) (hh : ActsOnColumns M Q h b) :
    ActsOnColumns M Q (g * h) (a ∘ b) := by
  let R := CommAlgCat.of F F
  intro p
  change (Q.matrixAt R (fieldProjection M (g * h)).val) *ᵥ tensorColumn p =
    tensorColumn (a (b p))
  rw [map_mul, Units.val_mul, map_mul, ← Matrix.mulVec_mulVec]
  change _ *ᵥ (Q.matrixAt R (fieldProjection M h).val *ᵥ tensorColumn p) = _
  rw [actsOnColumns_mulVec M Q hh]
  exact actsOnColumns_mulVec M Q hg (b p)

private theorem actsOnColumns_one (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d) :
    ActsOnColumns M Q 1 id := by
  let R := CommAlgCat.of F F
  intro p
  change Q.matrixAt R (fieldProjection M 1).val *ᵥ tensorColumn p = tensorColumn p
  rw [map_one, Units.val_one, map_one, one_mulVec]

private def scaleColumns (Q : QuaternionHyperbolicPresentation D hB d) (t : Bˣ)
    (p : ColumnTriple B d) : ColumnTriple B d :=
  ((t : B) * p.1, p.2.1, (antiValue Q.conjugation.anti (t : B))⁻¹ * p.2.2)

private theorem quaternionScale_mulVec [CharP F 2] (Q : QuaternionHyperbolicPresentation D hB d)
    (t : Bˣ) (p : ColumnTriple B d) :
    let R := CommAlgCat.of F F
    Q.matrixAt R (quaternionScale Q R (tensorUnits t)).val *ᵥ tensorColumn p =
      tensorColumn (scaleColumns Q t p) := by
  let R := CommAlgCat.of F F
  change Q.matrixAt R ((Q.matrixAt R).symm (diagonalQuaternionScale
    (extendAnti Q.conjugation.anti R).toMonoidHom d (tensorUnits t)).val) *ᵥ _ = _
  rw [AlgEquiv.apply_symm_apply, diagonalQuaternionScale_val]
  have ht : (tensorUnits (F := F) t).val = (1 : F) ⊗ₜ[F] (t : B) :=
    Algebra.TensorProduct.lid_symm_apply F (t : B)
  have hz : unop ((extendAnti Q.conjugation.anti R).toMonoidHom (tensorUnits t).inv) =
      (1 : F) ⊗ₜ[F] (antiValue Q.conjugation.anti (t : B))⁻¹ := by
    change antiValue (extendAnti Q.conjugation.anti R)
      ((1 : R) ⊗ₜ[F] (↑t⁻¹ : B)) = _
    rw [extendAnti_tmul, Units.val_inv_eq_inv_val, bar_inv]
  rw [ht, hz, scaleDiagonal]
  funext i
  rw [Matrix.mulVec_diagonal]
  rcases i with i | i
  · fin_cases i <;> simp [tensorColumn, column, scaleColumns, Algebra.TensorProduct.tmul_mul_tmul]
  · simp [tensorColumn, column, scaleColumns]

private theorem scale_of_left_ratio [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d)
    {g g₀ : GroupPoints G.val (CommAlgCat.of F F)} {f : ColumnTriple B d → ColumnTriple B d}
    (t : Bˣ) (hg₀ : ActsOnColumns M Q g₀ f)
    (hg : ActsOnColumns M Q g (scaleColumns Q t ∘ f)) :
    fieldProjection M (g * g₀⁻¹) =
      quaternionScale Q (CommAlgCat.of F F) (tensorUnits t) := by
  let R := CommAlgCat.of F F
  have h : fieldProjection M g =
      quaternionScale Q R (tensorUnits t) * fieldProjection M g₀ := by
    apply Units.ext
    apply (Q.matrixAt R).injective
    rw [Units.val_mul, map_mul]
    apply tensorColumn_matrix_ext
    intro p
    rw [← Matrix.mulVec_mulVec, actsOnColumns_mulVec M Q hg₀, quaternionScale_mulVec]
    exact actsOnColumns_mulVec M Q hg p
  rw [map_mul, map_inv, h, mul_inv_cancel_right]

private theorem scale_of_right_ratio [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d)
    {g g₀ : GroupPoints G.val (CommAlgCat.of F F)} {f : ColumnTriple B d → ColumnTriple B d}
    (t : Bˣ) (hg₀ : ActsOnColumns M Q g₀ f)
    (hg : ActsOnColumns M Q g (f ∘ scaleColumns Q t)) :
    fieldProjection M (g₀⁻¹ * g) =
      quaternionScale Q (CommAlgCat.of F F) (tensorUnits t) := by
  let R := CommAlgCat.of F F
  have h : fieldProjection M g =
      fieldProjection M g₀ * quaternionScale Q R (tensorUnits t) := by
    apply Units.ext
    apply (Q.matrixAt R).injective
    rw [Units.val_mul, map_mul]
    apply tensorColumn_matrix_ext
    intro p
    rw [← Matrix.mulVec_mulVec, quaternionScale_mulVec, actsOnColumns_mulVec M Q hg₀]
    exact actsOnColumns_mulVec M Q hg p
  rw [map_mul, map_inv, h, inv_mul_cancel_left]

private abbrev ContainsOppositeLimits (c : Cocharacter G.val)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F))) : Prop :=
  (∀ p, HasLimit c p 1 → p ∈ H) ∧ (∀ p, HasLimit (oppositeCocharacter c) p 1 → p ∈ H)

private theorem weyl_word_lift [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2)
    (W : ComplementRefinement Q) (c : Cocharacter G.val)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F))) (hH : ContainsOppositeLimits c H)
    (hLift : ∀ w b, scalarClass F b = refinement W.pairing W.complementAction w →
      ∃ gPlus gMinus : GroupPoints G.val (CommAlgCat.of F F),
        HasLimit c gPlus 1 ∧ HasLimit (oppositeCocharacter c) gMinus 1 ∧
        ActsOnColumns M Q gPlus (upper W.pairing w b) ∧
        ActsOnColumns M Q gMinus (lower W.pairing w b))
    (w₀ : Fin d → B) (b : Bˣ) (hb : scalarClass F (b : B) = refinement W.pairing W.complementAction w₀) :
    ∃ g ∈ H, ActsOnColumns M Q g (weylWord W.pairing w₀ b) := by
  obtain ⟨hleft, hright, _⟩ := (radicalWords hB hd Q.canonical W.pairing
    W.complementAction W.complementTraceOne w₀ b hb).2.2 b.ne_zero
  obtain ⟨mid, _, hmid, _, hm, _⟩ := hLift w₀ b hb
  obtain ⟨_, lhs, _, hlhs, _, hl⟩ := hLift _ _ hleft
  obtain ⟨_, rhs, _, hrhs, _, hr⟩ := hLift _ _ hright
  have hword : lhs * (mid * rhs) ∈ H :=
    H.mul_mem (hH.2 lhs hlhs)
      (H.mul_mem (hH.1 mid hmid) (hH.2 rhs hrhs))
  exact ⟨_, hword, actsOnColumns_mul M Q hl (actsOnColumns_mul M Q hm hr)⟩


private abbrev HasColumnLifts (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (W : ComplementRefinement Q) (c : Cocharacter G.val) : Prop :=
  ∀ (w₀ : Fin d → B) (b : B), scalarClass F b = refinement W.pairing W.complementAction w₀ →
    ∃ gPlus gMinus : GroupPoints G.val (CommAlgCat.of F F),
      HasLimit c gPlus 1 ∧ HasLimit (oppositeCocharacter c) gMinus 1 ∧
      ActsOnColumns M Q gPlus (upper W.pairing w₀ b) ∧
      ActsOnColumns M Q gMinus (lower W.pairing w₀ b)

private def diagonalColumns (Q : QuaternionHyperbolicPresentation D hB d)
    (r : (Fin d → B) → (Fin d → B)) (b : Bˣ) (p : ColumnTriple B d) : ColumnTriple B d :=
  ((b : B) * p.1, r p.2.1, (antiValue Q.conjugation.anti (b : B))⁻¹ * p.2.2)

private theorem rotation_word_lift [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2)
    (W : ComplementRefinement Q) (c : Cocharacter G.val)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F))) (hH : ContainsOppositeLimits c H)
    (hLift : HasColumnLifts M Q W c)
    (w₀ : Fin d → B) (b : Bˣ) (hb : scalarClass F (b : B) = refinement W.pairing W.complementAction w₀) :
    ∃ g ∈ H,
      ActsOnColumns M Q g (diagonalColumns Q (perpendicularRotation W.pairing w₀ b) b) := by
  have h₀ : scalarClass F (1 : B) = refinement W.pairing W.complementAction (0 : Fin d → B) := by
    change scalarClass F (1 : B) = scalarClass F (W.pairing.value 0 (W.complementAction 0))
    rw [map_zero, hermitian_zero_right]
    exact (map_one (algebraMap F B) ▸ class_scalar (B := B) (1 : F)).trans (map_zero _).symm
  obtain ⟨g, hg, hgw⟩ := weyl_word_lift M Q hd W c H hH hLift w₀ b hb
  obtain ⟨g₀, hg₀, hg₀w⟩ := weyl_word_lift M Q hd W c H hH hLift (0 : Fin d → B) 1 h₀
  have hw := (radicalWords hB hd Q.canonical W.pairing
    W.complementAction W.complementTraceOne w₀ b hb).2.2 b.ne_zero
  have hw₀ := (radicalWords hB hd Q.canonical W.pairing
    W.complementAction W.complementTraceOne 0 (1 : B) h₀).2.2 one_ne_zero
  have he : weylWord W.pairing w₀ (b : B) ∘ weylWord W.pairing 0 1 =
      diagonalColumns Q (perpendicularRotation W.pairing w₀ b) b := by
    funext p
    rcases p with ⟨x, y, z⟩
    change weylWord W.pairing w₀ (b : B) (weylWord W.pairing 0 1 (x, y, z)) = _
    rw [hw₀.2.2]
    simp only [antiValue_one, one_mul, inv_one, perpendicularRotation, smul_zero, add_zero]
    exact hw.2.2 z y x
  refine ⟨g * g₀, H.mul_mem hg hg₀, ?_⟩
  rw [← he]
  exact actsOnColumns_mul M Q hgw hg₀w

private theorem complement_word_lift [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2)
    (W : ComplementRefinement Q) (c : Cocharacter G.val)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F))) (hH : ContainsOppositeLimits c H)
    (hLift : HasColumnLifts M Q W c)
    (l : List ((Fin d → B) × Bˣ))
    (hl : ∀ p ∈ l, scalarClass F (p.2 : B) = refinement W.pairing W.complementAction p.1) :
    ∃ g ∈ H, ∃ b : Bˣ,
      ActsOnColumns M Q g
        (diagonalColumns Q (fun y => l.foldr
          (fun p => perpendicularRotation W.pairing p.1 (p.2 : B)) y) b) := by
  induction l with
  | nil =>
    refine ⟨1, H.one_mem, 1, ?_⟩
    have he : diagonalColumns Q (fun y => ([] : List ((Fin d → B) × Bˣ)).foldr
        (fun p => perpendicularRotation W.pairing p.1 (p.2 : B)) y) 1 = id := by
      funext p
      simp [diagonalColumns, antiValue_one]
    rw [he]
    exact actsOnColumns_one M Q
  | cons p l ih =>
    obtain ⟨x, hx, hx'⟩ := rotation_word_lift M Q hd W c H hH hLift p.1 p.2
      (hl p (List.mem_cons_self))
    obtain ⟨y, hy, b, hy'⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    refine ⟨x * y, H.mul_mem hx hy, p.2 * b, ?_⟩
    have he : diagonalColumns Q (perpendicularRotation W.pairing p.1 (p.2 : B)) p.2 ∘
        diagonalColumns Q (fun y₀ => l.foldr
          (fun q => perpendicularRotation W.pairing q.1 (q.2 : B)) y₀) b =
      diagonalColumns Q (fun y₀ => (p :: l).foldr
        (fun q => perpendicularRotation W.pairing q.1 (q.2 : B)) y₀) (p.2 * b) := by
      funext p₀
      simp only [Function.comp_apply, diagonalColumns, Units.val_mul, bar_mul, _root_.mul_inv_rev,
        List.foldr_cons, mul_assoc]
    rw [← he]
    exact actsOnColumns_mul M Q hx' hy'

private theorem remove_complement [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2)
    (W : ComplementRefinement Q) (c : Cocharacter G.val)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F))) (hH : ContainsOppositeLimits c H)
    (hLift : HasColumnLifts M Q W c)
    (hCentral : ∀ g : GroupPoints G.val (CommAlgCat.of F F), Centralizes c g →
      ∃ (t : Bˣ) (r : (Fin d → B) ≃ₗ[Bᵐᵒᵖ] (Fin d → B)),
        (∀ x y, W.pairing.value (r x) (r y) = W.pairing.value x y) ∧
        (∀ x, refinement W.pairing W.complementAction (r x) =
          refinement W.pairing W.complementAction x) ∧
        ActsOnColumns M Q g (diagonalColumns Q r t))
    (x : GroupPoints G.val (CommAlgCat.of F F)) (hx : Centralizes c x) :
    ∃ y ∈ H, ∃ t : (F ⊗[F] B)ˣ,
      fieldProjection M (y⁻¹ * x) =
        quaternionScale Q (CommAlgCat.of F F) t := by
  obtain ⟨a, r, _, hr', hx'⟩ := hCentral x hx
  let e : (Fin d → B) ≃ₗ[Bᵐᵒᵖ] (Fin d → Bᵐᵒᵖ) :=
    { Equiv.piCongrRight (fun _ => MulOpposite.opEquiv) with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let : Module.Finite Bᵐᵒᵖ (Fin d → B) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  obtain ⟨l, hl, hr₀⟩ := perpendicularGeneration hB hd Q.canonical W.pairing
    W.complementAction W.complementTraceOne r hr'
  obtain ⟨y, hy, b, hy'⟩ := complement_word_lift M Q hd W c H hH hLift l hl
  let t := b⁻¹ * a
  have he : diagonalColumns Q r a =
      diagonalColumns Q (fun y₀ => l.foldr
        (fun p => perpendicularRotation W.pairing p.1 (p.2 : B)) y₀) b ∘ scaleColumns Q t := by
    funext p
    have hb : b * t = a := mul_inv_cancel_left _ _
    have h₁ := congrArg (fun s : Bˣ => (s : B)) hb
    have h₂ := congrArg (fun s : Bˣ => (antiValue Q.conjugation.anti (s : B))⁻¹) hb
    simp only [Units.val_mul, bar_mul, _root_.mul_inv_rev] at h₂
    simp only [Units.val_mul] at h₁
    simp only [diagonalColumns, Function.comp_apply, scaleColumns, ← mul_assoc, h₁, h₂, hr₀]
  rw [he] at hx'
  exact ⟨y, hy, tensorUnits t, scale_of_right_ratio M Q t hy' hx'⟩

private def centralUnit (r : Fˣ) : Bˣ := Units.map (algebraMap F B).toMonoidHom r

private theorem centralUnit_commute (r : Fˣ) (b : Bˣ) : Commute (centralUnit r) b :=
  Units.ext (Algebra.commutes (r : F) (b : B))

private theorem tensorUnits_centralUnit (r : Fˣ) :
    tensorUnits (centralUnit (B := B) r) = scalarUnit (CommAlgCat.of F F) r := by
  apply Units.ext
  change (1 : F) ⊗ₜ[F] (algebraMap F B (r : F)) = (r : F) ⊗ₜ[F] (1 : B)
  apply (Algebra.TensorProduct.lid F B).injective
  simp [Algebra.TensorProduct.lid_tmul, Algebra.algebraMap_eq_smul_one]

private theorem scalar_word [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2)
    (W : ComplementRefinement Q) (c : Cocharacter G.val)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F))) (hH : ContainsOppositeLimits c H)
    (hLift : HasColumnLifts M Q W c)
    (r : Fˣ) :
    ∃ g ∈ H, fieldProjection M g =
      quaternionScale Q (CommAlgCat.of F F) (scalarUnit (CommAlgCat.of F F) r) := by
  let b : Bˣ := centralUnit r
  have hb : scalarClass F (b : B) = refinement W.pairing W.complementAction 0 := by
    change scalarClass F (algebraMap F B (r : F)) =
      scalarClass F (W.pairing.value 0 (W.complementAction 0))
    rw [map_zero, hermitian_zero_right, map_zero]
    exact class_scalar (r : F)
  obtain ⟨g, hg, hgv⟩ := rotation_word_lift M Q hd W c H hH hLift 0 b hb
  have he : diagonalColumns Q (perpendicularRotation W.pairing 0 (b : B)) b =
      scaleColumns Q b ∘ id := by
    funext p
    simp [diagonalColumns, scaleColumns, perpendicularRotation]
  rw [he] at hgv
  have hscale := scale_of_left_ratio M Q b (actsOnColumns_one M Q) hgv
  rw [inv_one, mul_one, show tensorUnits b = _ from tensorUnits_centralUnit (B := B) r] at hscale
  exact ⟨g, hg, hscale⟩

private theorem commutator_mul_central (a b : Bˣ) (r : Fˣ) :
    ⁅a, centralUnit r * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, (centralUnit_commute r a).symm.commutator_eq, one_mul]
  rw [(centralUnit_commute r (⁅a, b⁆ : Bˣ)).eq, mul_inv_cancel_right]

private theorem fixed_field_scale_words [CharP F 2] (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (hd : degree F B = 2)
    (W : ComplementRefinement Q) (c : Cocharacter G.val)
    (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F))) (hH : ContainsOppositeLimits c H)
    (hLift : HasColumnLifts M Q W c)
    (hne : 0 < d) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : Algebra.IsSeparable F E)
      (i : E →ₐ[F] B), Module.finrank F E = 2 ∧
      ∀ a : Bˣ, ∀ b : Eˣ, ∃ g ∈ H,
        fieldProjection M g =
          quaternionScale Q (CommAlgCat.of F F) (tensorUnits ⁅a, Units.map i.toMonoidHom b⁆) := by
  let : Nonempty (Fin d) := ⟨⟨0, hne⟩⟩
  let s := Q.conjugation.anti
  obtain ⟨w, b, E, _, _, _, i, _, hb, _, _, hdim, hfamily, hratio⟩ :=
    fixedFieldWords hB hd Q.canonical W.pairing W.complementAction W.complementTraceOne
  refine ⟨E, inferInstance, inferInstance, inferInstance, i, hdim, ?_⟩
  intro a t
  by_cases ht : i (t : E) ∈ Set.range (algebraMap F B)
  · obtain ⟨r, hr⟩ := ht
    have hr' : r ≠ 0 := by
      intro hz
      exact t.ne_zero (i.injective (by
        change i (t : E) = i 0
        rw [← hr, hz, map_zero, map_zero]))
    have hc : Units.map i.toMonoidHom t = centralUnit (Units.mk0 r hr') := Units.ext hr.symm
    refine ⟨1, H.one_mem, ?_⟩
    rw [hc, (centralUnit_commute (Units.mk0 r hr') a).symm.commutator_eq, map_one, map_one, map_one]
  obtain ⟨z, r, hr⟩ := hfamily t ht
  obtain ⟨b₀, hb₀, hwords⟩ := hratio z
  have hc : Units.map i.toMonoidHom t = centralUnit r * b₀ :=
    Units.ext (by change i (t : E) = algebraMap F B (r : F) * (b₀ : B); rw [hb₀, hr])
  rw [hc, commutator_mul_central]
  have hb₀' : scalarClass F (b₀ : B) = refinement W.pairing W.complementAction w := by
    rw [hb₀, map_add, class_scalar, add_zero, hb]
  let a' := Units.mk0 (antiValue s (a : B)) (bar_ne_zero a.ne_zero)
  have haa : (Units.opEquiv (Units.map s.toMonoidHom a')).unop = a :=
    Units.ext (Q.conjugation.square (a : B))
  obtain ⟨hform, _, hW⟩ := hwords a'
  let b₁ := antiValue s (a' : B) * (b₀ : B) * (a' : B)
  let b₁u := Units.mk0 b₁ (mul_ne_zero (mul_ne_zero (bar_ne_zero a'.ne_zero) b₀.ne_zero) a'.ne_zero)
  obtain ⟨g₀, hg₀, hg₀w⟩ := weyl_word_lift M Q hd W c H hH hLift w b₀ hb₀'
  obtain ⟨g₁, hg₁, hg₁w⟩ := weyl_word_lift M Q hd W c H hH hLift _ b₁u hform
  have hn : reducedNorm hB (a' : B) ≠ 0 := by
    intro hz
    have he := conjugate_mul_eq_norm hB hd Q.canonical (a' : B)
    rw [hz, map_zero] at he
    exact mul_ne_zero (bar_ne_zero a'.ne_zero) a'.ne_zero he
  let r₁ := Units.mk0 (reducedNorm hB (a' : B)) hn
  let u := centralUnit r₁ * (⁅a, b₀⁆ : Bˣ)
  have he : weylWord W.pairing (op (a' : B) • w) b₁ =
      scaleColumns Q u ∘ weylWord W.pairing w (b₀ : B) := by
    funext p
    have hp := hW p
    dsimp only at hp
    rw [haa] at hp
    refine hp.trans ?_
    simp only [Function.comp_apply, scaleColumns, u, Units.val_mul, bar_mul, centralUnit]
    change (_, _, (_ * _)⁻¹ * _) = (_, _, (antiValue s (↑(⁅a, b₀⁆ : Bˣ) : B) *
      antiValue s (algebraMap F B (r₁ : F)))⁻¹ * _)
    rw [bar_scalar, ← Algebra.commutes]
    rfl
  rw [show (b₁u : B) = b₁ from rfl, he] at hg₁w
  have hU := scale_of_left_ratio M Q u hg₀w hg₁w
  obtain ⟨gS, hgS, hS⟩ := scalar_word M Q hd W c H hH hLift r₁
  let g := gS⁻¹ * (g₁ * g₀⁻¹)
  refine ⟨g, H.mul_mem (H.inv_mem hgS) (H.mul_mem hg₁ (H.inv_mem hg₀)), ?_⟩
  dsimp only [g]
  rw [map_mul, map_inv, hU, hS, ← map_inv, ← map_mul, ← tensorUnits_centralUnit,
    ← map_inv, ← map_mul]
  simp only [u, inv_mul_cancel_left]


private theorem levi_mem_of_removed_complement
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (c : Cocharacter G.val) (H : Subgroup (GroupPoints G.val (CommAlgCat.of F F)))
    (hremove : ∀ x : GroupPoints G.val (CommAlgCat.of F F), Centralizes c x →
      ∃ y ∈ H, ∃ t : (F ⊗[F] B)ˣ,
        fieldProjection M (y⁻¹ * x) = quaternionScale Q (CommAlgCat.of F F) t)
    (hscale : ∀ z : spinScalePreimage M Q (CommAlgCat.of F F), z.val.1 ∈ H)
    (x : GroupPoints G.val (CommAlgCat.of F F)) (hx : Centralizes c x) :
    x ∈ H := by
  obtain ⟨y, hy, t, ht⟩ := hremove x hx
  have hmem : y⁻¹ * x ∈ H := hscale ⟨(y⁻¹ * x, t), ht⟩
  have hmul := H.mul_mem hy hmem
  rwa [mul_inv_cancel_left] at hmul

private theorem quaternion_generation [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [FiniteDimensional F K] [IsGalois F K]
    (M : SpinModel G D) (hrank : 4 ≤ Fintype.card I) (hd : degree F B = 2)
    (Q : QuaternionHyperbolicPresentation D hB d) :
    ∃ (W : ComplementRefinement Q) (c : Cocharacter G.val),
      Specs.Arithmetic.QuaternionScalarCliffordLift.IsPairDiagonal M Q c ∧
      Specs.Arithmetic.OppositeRadicals.IsNoncentral c ∧
      HasColumnLifts M Q W c ∧
      (∀ x : GroupPoints G.val (CommAlgCat.of F F), Centralizes c x →
        ∃ y ∈ oppositeWords c, ∃ t : (F ⊗[F] B)ˣ,
          fieldProjection M (y⁻¹ * x) =
            quaternionScale Q (CommAlgCat.of F F) t) ∧
      (oppositeWords c = ⊤) ∧ unipotentGenerated G = ⊤ := by
  let := localField_infinite F
  obtain ⟨W⟩ := QuaternionHyperbolicRadicals.recoverComplement hB hd Q
  obtain ⟨_, _, f, _, _, _, _, _, ⟨c₀, _, hdiag, hnoncentral, _⟩, _⟩ := scalarPairLift M hrank hB hd Q
  let c := c₀ ≫ f
  have hdiag' : Specs.Arithmetic.QuaternionHyperbolicRadicals.IsPairDiagonal M Q c := by
    intro R r
    refine (hdiag R r).trans ?_
    change Matrix.fromBlocks (Matrix.map (!![(r : R), 0; 0, (↑r⁻¹ : R)] : Matrix (Fin 2) (Fin 2) R)
      (algebraMap R (R ⊗[F] B))) 0 0 1 = _
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hLift : HasColumnLifts M Q W c :=
    QuaternionHyperbolicRadicals.oppositeColumnActions M hrank hB hd Q c hdiag' W
  have hCentral := QuaternionHyperbolicRadicals.centralizerColumns M hrank hB hd Q c hdiag' W
  obtain ⟨D₀⟩ := existsLimitDecomposition G c
  obtain ⟨D₁⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  let H := radicalPointWords D₀ D₁
  have hH : ContainsOppositeLimits c H :=
    ⟨fun _ => limit_mem_radicalPointWords D₀ D₁, fun _ => opposite_limit_mem_radicalPointWords D₀ D₁⟩
  have hremove := remove_complement M Q hd W c H hH hLift hCentral
  have hdpos : 0 < d := by
    have h := complement_dimension Q hd
    omega
  obtain ⟨E, _, _, _, iE, hE, hmix⟩ := fixed_field_scale_words M Q hd W c H hH hLift hdpos
  have hScale := scale_preimage_mem_of_mixed_words QuaternionSpinScaleCover.spinScaleCover
    QuaternionSpinScaleCover.quaternionNormOnUnits M Q hrank hd iE hE H
    (scalar_word M Q hd W c H hH hLift) hmix
  have hR := spin_model_reductive M hrank
  have hLev := levi_mem_of_removed_complement M Q c H hremove hScale
  have htop := radicalSections_eq_top_of_levi hR D₀ D₁ hLev
  have hop := oppositeWords_eq_top D₀ D₁ htop
  have hplus := unipotentGenerated_eq_top_of_radicalSections hR D₀ D₁ htop
  refine ⟨W, c, hdiag, hnoncentral, hLift, ?_, hop, hplus⟩
  intro x hx
  obtain ⟨y, _, t, ht⟩ := hremove x hx
  exact ⟨y, hop.symm ▸ Subgroup.mem_top y, t, ht⟩

theorem quaternionLocalGeneration : QuaternionLocalGeneration.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ _ _ _ _ ρ G D M hI hB hd d Q i
  obtain ⟨W, c, hdiag, hnc, hLift, hremove, htop, _⟩ := quaternion_generation M hI hd Q
  have hall : ∀ x : PointsIn i F, x ∈ oppositeClosure i c := by
    intro x
    apply subset_closure
    change x ∈ oppositeWords c
    rw [htop]
    exact Subgroup.mem_top x
  refine ⟨W, c, hdiag, hnc, hLift, hremove,
    (fun x => hall x.val.1), (fun x _ => hall x), Set.eq_univ_of_forall (fun x => hall x)⟩

end QuaternionGeneration

section NontrialitarianGeneration

open Specs.AdjointRepresentation (GroupPoints)

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Matrix ValuativeRel Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.GeometricRadicals (IsReductive)
open Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel HasFixedVectorVertex)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Arithmetic.SplitQuadraticPairSpinComparison (RecoveredForm)
open Specs.Arithmetic.QuaternionSpinScaleCover (QuaternionHyperbolicPresentation)
open Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open private reductive_of_semisimple
  from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from LinearAlgebraicGroups.Relative.RationalDensity
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

private theorem unipotentGenerated_eq_top_of_spin_model
    {F K I : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D) (hI : 4 ≤ Fintype.card I)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G) :
    unipotentGenerated G = ⊤ := by
  obtain ⟨r, B, _, _, hB, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation
    F ρ.fixedSubalgebra D.centralSimple
  have hB' : _root_.Specs.RM03.CSA.isCentralSimple F B := ⟨inferInstance, hB.1, hB.2⟩
  have hsquare := CharacteristicTwoQuadraticPairs.localSquareDegree F
  obtain ⟨_, hdiv⟩ := CharacteristicTwoQuadraticPairs.divisionDegreeOverSquares hsquare
    D.centralSimple hB' r hr e (toDivisionInvolution D.involution).anti
  have hR := reductive_of_semisimple G hG.1
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hd | hd
  · obtain ⟨iso⟩ := SymplecticInvolutionModels.degreeOneDivision hB' hd
    let e' := e.trans iso.mapMatrix
    obtain ⟨hr', H, ell, q, hAdj, hEll, hTrace, hq, hpolar, hreg, hisom⟩ :=
      CharacteristicTwoQuadraticPairs.splitPairRecovery D r e'
    let P : RecoveredForm (D := D) e' := ⟨hr', H, ell, q, hAdj, hEll, hTrace, hq,
      hpolar, hreg, hisom⟩
    have h₈ : 8 ≤ r := by omega
    obtain ⟨_, _, _, _, _, _, B₀, C₀, htop⟩ :=
      SplitQuadraticPairSpinComparison.localSplitSpinGeneration M hG r h₈ e' P
    have hle := RelativeRayGeneration.twoRadicals_le_unipotentGenerated hR B₀ C₀
    exact top_unique (htop ▸ hle)
  · obtain ⟨P⟩ := CharacteristicTwoQuadraticPairs.quaternionPairRecovery D hB' hd r e
    have h₄ : 4 ≤ r := P.rank.symm ▸ hI
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, Q, _⟩ :=
      QuaternionHyperbolicRadicals.arithmeticPresentation M hB' hd r h₄ e
    obtain ⟨_, _, _, _, _, _, _, htop⟩ := quaternion_generation M hI hd Q
    exact htop

private theorem nontrialitarian_local_top (F : Type u) [Field F] [CharP F 2] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F)
    (n : ℕ) (hn : 4 ≤ n) (hG : AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G)
    (hsc : SimplyConnectedLattice.GeometricallySimplyConnected G) (hv : HasFixedVectorVertex G n) :
    unipotentGenerated G = ⊤ := by
  obtain ⟨K, _, _, _, _, ρ, D, _, _, ⟨M⟩⟩ :=
    NontrialitarianSpinModels.nontrialitarianSpinModel F G n hn hG hsc hv
  have hI : 4 ≤ Fintype.card (ULift.{u} (Fin n)) := by simpa using hn
  exact unipotentGenerated_eq_top_of_spin_model M hI (arithmetic_absolute_simplicity hG)

theorem nontrialitarianLocalGeneration : NontrialitarianLocalGeneration.{u} := by
  intro F _ _ _ _ _ G n hn hG hsc hv i
  have h := nontrialitarian_local_top F G n hn hG hsc hv
  have hset : {g : PointsIn i F | ∃ p ∈ unipotentGenerated G,
      toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ p = g} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    let p : Points G.val.X (CommAlgCat.of F F) := g
    exact point_of_section_top h p
  rw [hset]
  exact dense_univ

end NontrialitarianGeneration

section FieldExtension

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.Arithmetic.NontrialitarianSpinModels
  (EquivariantSpinTrivialization SplitSpinVectorImage conjugate matrixInner)
open Specs.Arithmetic.OddSpinModels (hyperbolicForm)

open private matrixInner_mul conjugate_map matrixInner_ext_ground matrix_action_of_projectiveCocycle
  hyperbolicForm_map from LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

private theorem finite_galois_field_over_extension
    (F K L : Type u) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [FiniteDimensional F K] [IsGalois F K] :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra L T) (_ : FiniteDimensional L T)
      (_ : IsGalois L T) (_ : Algebra F T) (_ : IsScalarTower F L T)
      (_ : Algebra K T), IsScalarTower F K T := by
  obtain ⟨p, hp, hsplit⟩ := IsGalois.is_separable_splitting_field F K
  let q := p.map (algebraMap F L)
  let T := q.SplittingField
  have hs : (p.map (algebraMap F T)).Splits := by
    rw [IsScalarTower.algebraMap_eq F L T, ← Polynomial.map_map]
    exact Polynomial.IsSplittingField.splits T q
  let e : K →ₐ[F] T := Polynomial.IsSplittingField.lift K p hs
  let : Algebra K T := e.toRingHom.toAlgebra
  let : IsScalarTower F K T := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  refine ⟨T, inferInstance, inferInstance, inferInstance, ?_, inferInstance, inferInstance,
    inferInstance, inferInstance⟩
  exact IsGalois.of_separable_splitting_field (p := q) hp.map

variable {F K L T I : Type u} [Field F] [Field K] [Field L] [Field T]
  [Algebra F K] [Algebra F L] [Algebra F T] [Algebra K T] [Algebra L T]
  [IsScalarTower F K T] [IsScalarTower F L T] [IsGalois F K]
  [Fintype I] [DecidableEq I] {G : AffineAlgebraicGroup F}

private def restrictGalois : Gal(T/L) →* Gal(K/F) :=
  (AlgEquiv.restrictNormalHom K).comp (AlgEquiv.restrictScalarsHom F)

private theorem restrictGalois_apply (σ : Gal(T/L)) (x : K) :
    algebraMap K T (restrictGalois (F := F) σ x) = σ (algebraMap K T x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars F) K x

private theorem map_matrixInner_eq {R S J : Type u} [CommRing R] [CommRing S]
    [Fintype J] [DecidableEq J] (f : R →+* S) {g h : (Matrix J J R)ˣ}
    (he : matrixInner g = matrixInner h) :
    matrixInner (Matrix.GeneralLinearGroup.map f g) =
      matrixInner (Matrix.GeneralLinearGroup.map f h) := by
  apply matrixInner_ext_ground f
  intro X
  rw [← conjugate_map, ← conjugate_map]
  exact congrArg (fun Y : Matrix J J R => Y.map f) (DFunLike.congr_fun he X)

private theorem projective_cocycle (C : EquivariantSpinTrivialization (K := K) (I := I) G) :
    matrixInner (C.g 1) = matrixInner 1 ∧
    ∀ σ τ, matrixInner (C.g (σ * τ)) =
      matrixInner (C.g σ * Matrix.GeneralLinearGroup.map σ.toRingHom (C.g τ)) := by
  constructor
  · apply AlgEquiv.ext
    intro X
    have h := C.action.one_act X
    rw [C.actionFormula] at h
    change conjugate (C.g 1) (X.map (1 : Gal(K/F))) = X at h
    have he : X.map (1 : Gal(K/F)) = X := by ext; rfl
    rw [he] at h
    change conjugate (C.g 1) X = conjugate 1 X
    have h1 : conjugate (1 : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) X = X := by
      change 1 * X * 1 = X
      simp
    rw [h1]
    exact h
  · intro σ τ
    apply AlgEquiv.ext
    intro X
    let Y := X.map (σ * τ).symm.toRingHom
    have h := C.action.mul_act σ τ Y
    rw [C.actionFormula, C.actionFormula, C.actionFormula] at h
    have hp : Y.map (σ * τ).toRingHom = X := by
      ext i j
      exact (σ * τ).apply_symm_apply _
    change conjugate (C.g (σ * τ)) (Y.map (σ * τ).toRingHom) =
      conjugate (C.g σ) ((conjugate (C.g τ) (Y.map τ.toRingHom)).map σ.toRingHom) at h
    rw [conjugate_map] at h
    have hcomp : (Y.map τ.toRingHom).map σ.toRingHom = Y.map (σ * τ).toRingHom := rfl
    rw [hcomp, hp] at h
    exact h.trans (DFunLike.congr_fun (matrixInner_mul K _ _).symm X)

private def extendedConjugator (C : EquivariantSpinTrivialization (K := K) (I := I) G)
    (σ : Gal(T/L)) : (Matrix (I ⊕ I) (I ⊕ I) T)ˣ :=
  Matrix.GeneralLinearGroup.map (algebraMap K T) (C.g (restrictGalois (F := F) σ))

set_option maxHeartbeats 800000 in
private theorem extended_action (C : EquivariantSpinTrivialization (K := K) (I := I) G) :
    ∃ ρ : AlgebraAction L T (Matrix (I ⊕ I) (I ⊕ I) T),
      ∀ σ X, ρ.act σ X = conjugate (extendedConjugator C σ) (X.map σ) := by
  let r : Gal(T/L) →* Gal(K/F) := restrictGalois
  let g : Gal(T/L) → (Matrix (I ⊕ I) (I ⊕ I) T)ˣ := extendedConjugator C
  obtain ⟨h₁, hμ⟩ := projective_cocycle C
  apply matrix_action_of_projectiveCocycle g
  · have he := map_matrixInner_eq (algebraMap K T) h₁
    change matrixInner (Matrix.GeneralLinearGroup.map (algebraMap K T) (C.g (r 1))) = _
    rw [map_one r, he, map_one]
    ext i j
    simp [matrixInner, conjugate]
  · intro σ τ
    have hσ (b : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) :
        Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap K T) b) =
          Matrix.GeneralLinearGroup.map (algebraMap K T) (Matrix.GeneralLinearGroup.map (r σ).toRingHom b) := by
      apply Units.ext
      ext i j
      exact (restrictGalois_apply (F := F) σ (b.val i j)).symm
    change matrixInner (Matrix.GeneralLinearGroup.map (algebraMap K T) (C.g (r (σ * τ)))) =
      matrixInner (Matrix.GeneralLinearGroup.map (algebraMap K T) (C.g (r σ)) *
        Matrix.GeneralLinearGroup.map σ.toRingHom
          (Matrix.GeneralLinearGroup.map (algebraMap K T) (C.g (r τ))))
    rw [hσ, ← (Matrix.GeneralLinearGroup.map (algebraMap K T)).map_mul, r.map_mul]
    exact map_matrixInner_eq (algebraMap K T) (hμ (r σ) (r τ))

private theorem similitude_extension (g : (Matrix (I ⊕ I) (I ⊕ I) K)ˣ) (c : Kˣ)
    (hg : ∀ x, hyperbolicForm I K (g.val *ᵥ x) = (c : K) * hyperbolicForm I K x) :
    ∀ x : I ⊕ I → T,
      hyperbolicForm I T ((Matrix.GeneralLinearGroup.map (algebraMap K T) g).val *ᵥ x) =
        algebraMap K T (c : K) * hyperbolicForm I T x := by
  let m := (Matrix.GeneralLinearGroup.map (algebraMap K T) g).val
  let e := ((Pi.basisFun K (I ⊕ I)).baseChange T).equivFun
  let q := hyperbolicForm I T
  let q₁ : QuadraticForm T (T ⊗[K] (I ⊕ I → K)) := q.comp (m.toLin'.comp e.toLinearMap)
  let q₂ : QuadraticForm T (T ⊗[K] (I ⊕ I → K)) := (algebraMap K T (c : K)) • (q.comp e.toLinearMap)
  have heq : q₁ = q₂ := by
    apply baseChange_ext
    intro y
    have hy : e ((1 : T) ⊗ₜ[K] y) = algebraMap K T ∘ y := by
      ext i
      simp [e, Module.Basis.equivFun_apply, Algebra.smul_def]
    have hm : m *ᵥ (algebraMap K T ∘ y) = algebraMap K T ∘ (g.val *ᵥ y) := by
      funext i
      exact (RingHom.map_mulVec (algebraMap K T) g.val y i).symm
    change q (m *ᵥ e ((1 : T) ⊗ₜ[K] y)) =
      algebraMap K T (c : K) * q (e ((1 : T) ⊗ₜ[K] y))
    rw [hy, hm]
    change hyperbolicForm I T (algebraMap K T ∘ (g.val *ᵥ y)) =
      algebraMap K T (c : K) * hyperbolicForm I T (algebraMap K T ∘ y)
    rw [← hyperbolicForm_map, ← hyperbolicForm_map, hg, map_mul]
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun heq y


open private groupBaseChangeTowerIso groupBaseChangeTowerIso_fst
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private splitSpinScalarComparison splitKernelFieldComparison spinVectorMatrix
  splitKernelPoint_natural spinModel_of_trivialization
  from LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels

private def exchangeBaseChange :
    groupBaseChange F L ⋙ groupBaseChange L T ≅ groupBaseChange F K ⋙ groupBaseChange K T :=
  (groupBaseChangeTowerIso (K := L) (L := T)) ≪≫
    (groupBaseChangeTowerIso (K := K) (L := T)).symm

private abbrev twiceRestricted (F A T : Type u) [Field F] [Field A] [Field T]
    [Algebra F A] [Algebra A T] (S : TestAlgebra T) : TestAlgebra F :=
  (restrictTestAlgebra F A).obj ((restrictTestAlgebra A T).obj S)

private def twiceBasedPoint (A : Type u) [Field A] [Algebra F A] [Algebra A T]
    (H : GroupScheme F) (S : TestAlgebra T)
    (p : Points ((groupBaseChange F A ⋙ groupBaseChange A T).obj H).X S) :
    Points H.X (twiceRestricted F A T S) :=
  baseChangePoint F A H.X ((restrictTestAlgebra A T).obj S)
    (baseChangePoint A T ((groupBaseChange F A).obj H).X S p)

private theorem tower_point_left (A : Type u) [Field A] [Algebra F A] [Algebra A T]
    [IsScalarTower F A T] (H : GroupScheme F) (S : TestAlgebra T)
    (p : Points ((groupBaseChange F A ⋙ groupBaseChange A T).obj H).X S) :
    (baseChangePoint F T H.X S
      (p ≫ ((groupBaseChangeTowerIso (K := A) (L := T)).app H).hom.hom.hom)).left =
      (twiceBasedPoint A H S p).left := by
  change (p.left ≫ ((groupBaseChangeTowerIso (K := A) (L := T)).app H).hom.hom.hom.left) ≫
      Limits.pullback.fst H.X.hom (fieldSpecMap F T) =
    (p.left ≫ Limits.pullback.fst ((groupBaseChange F A).obj H).X.hom (fieldSpecMap A T)) ≫
      Limits.pullback.fst H.X.hom (fieldSpecMap F A)
  rw [Category.assoc, groupBaseChangeTowerIso_fst, Category.assoc]
  rfl

private theorem exchange_point_left (H : GroupScheme F) (S : TestAlgebra T)
    (p : Points ((groupBaseChange F L ⋙ groupBaseChange L T).obj H).X S) :
    let a := (exchangeBaseChange (F := F) (K := K) (L := L) (T := T)).app H
    (twiceBasedPoint K H S (p ≫ a.hom.hom.hom)).left = (twiceBasedPoint L H S p).left := by
  let a := (groupBaseChangeTowerIso (k := F) (K := L) (L := T)).app H
  let b := (groupBaseChangeTowerIso (k := F) (K := K) (L := T)).app H
  let x : Points ((groupBaseChange F K ⋙ groupBaseChange K T).obj H).X S :=
    p ≫ (a ≪≫ b.symm).hom.hom.hom
  change (twiceBasedPoint K H S x).left = (twiceBasedPoint L H S p).left
  have hx : x ≫ b.hom.hom.hom = p ≫ a.hom.hom.hom := by
    change p ≫ (a.hom ≫ b.inv).hom.hom ≫ b.hom.hom.hom = _
    rw [Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom, b.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [← tower_point_left K H S x, hx, tower_point_left L H S p]

private def twiceRestrictedMap (S : TestAlgebra T) :
    twiceRestricted F L T S ⟶ twiceRestricted F K T S := by
  let R := twiceRestricted F L T S
  let U := twiceRestricted F K T S
  let f : R →ₐ[F] U :=
    { toRingHom := RingHom.id S
      commutes' := fun x => by
        change algebraMap T S (algebraMap L T (algebraMap F L x)) =
          algebraMap T S (algebraMap K T (algebraMap F K x))
        rw [← IsScalarTower.algebraMap_apply F L T, ← IsScalarTower.algebraMap_apply F K T] }
  exact ConcreteCategory.ofHom (C := CommAlgCat F) f

private theorem exchange_point (H : GroupScheme F) (S : TestAlgebra T)
    (p : Points ((groupBaseChange F L ⋙ groupBaseChange L T).obj H).X S) :
    let a := (exchangeBaseChange (F := F) (K := K) (L := L) (T := T)).app H
    twiceBasedPoint K H S (p ≫ a.hom.hom.hom) =
      mapPoints (twiceRestrictedMap S) (twiceBasedPoint L H S p) := by
  intro a
  apply Over.OverMorphism.ext
  change (twiceBasedPoint K H S (p ≫ a.hom.hom.hom)).left =
    Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ (twiceBasedPoint L H S p).left
  change _ = Spec.map (𝟙 (CommRingCat.of S)) ≫ _
  simpa only [Spec.map_id, Category.id_comp] using exchange_point_left (K := K) H S p

private def restrictSemilinearMap (S : TestAlgebra T)
    (f : (restrictTestAlgebra L T).obj S ⟶ (restrictTestAlgebra L T).obj S) :
    twiceRestricted F K T S ⟶ twiceRestricted F K T S := by
  let R := twiceRestricted F K T S
  let a : R →ₐ[F] R :=
    { toRingHom := f.hom.toRingHom
      commutes' := fun x => by
        change f.hom (algebraMap T S (algebraMap K T (algebraMap F K x))) =
          algebraMap T S (algebraMap K T (algebraMap F K x))
        rw [← IsScalarTower.algebraMap_apply F K T, IsScalarTower.algebraMap_apply F L T]
        exact f.hom.commutes (algebraMap F L x) }
  exact ConcreteCategory.ofHom (C := CommAlgCat F) a

private theorem exchange_semilinear_points (H : GroupScheme F) (S : TestAlgebra T)
    (f : (restrictTestAlgebra L T).obj S ⟶ (restrictTestAlgebra L T).obj S)
    (x y : Points ((groupBaseChange F L ⋙ groupBaseChange L T).obj H).X S)
    (h : baseChangePoint L T ((groupBaseChange F L).obj H).X S y =
      mapPoints f (baseChangePoint L T ((groupBaseChange F L).obj H).X S x)) :
    let a := (exchangeBaseChange (F := F) (K := K) (L := L) (T := T)).app H
    twiceBasedPoint K H S (y ≫ a.hom.hom.hom) =
      mapPoints (restrictSemilinearMap S f) (twiceBasedPoint K H S (x ≫ a.hom.hom.hom)) := by
  intro a
  apply Over.OverMorphism.ext
  change (twiceBasedPoint K H S (y ≫ a.hom.hom.hom)).left =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      (twiceBasedPoint K H S (x ≫ a.hom.hom.hom)).left
  rw [exchange_point_left H S y, exchange_point_left H S x]
  have hl := congrArg (fun z : Points ((groupBaseChange F L).obj H).X
    ((restrictTestAlgebra L T).obj S) => z.left) h
  change (baseChangePoint L T ((groupBaseChange F L).obj H).X S y).left =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      (baseChangePoint L T ((groupBaseChange F L).obj H).X S x).left at hl
  change (baseChangePoint L T ((groupBaseChange F L).obj H).X S y).left ≫
      Limits.pullback.fst H.X.hom (fieldSpecMap F L) =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      (baseChangePoint L T ((groupBaseChange F L).obj H).X S x).left ≫
        Limits.pullback.fst H.X.hom (fieldSpecMap F L)
  rw [hl, Category.assoc]


variable (C : EquivariantSpinTrivialization (K := K) (I := I) G)

private def extendedSpinComparison (P : SplitSpinVectorImage T I)
    (v : (groupBaseChange K T).obj C.split.spin.val ≅ P.spin.val) :
    (groupBaseChange L T).obj ((groupBaseChange F L).obj G.val) ≅ P.spin.val :=
  (exchangeBaseChange (F := F) (K := K) (L := L) (T := T)).app G.val ≪≫
    (groupBaseChange K T).mapIso C.comparison ≪≫ v

private theorem extended_vector_equivariance (P : SplitSpinVectorImage T I)
    (v : (groupBaseChange K T).obj C.split.spin.val ≅ P.spin.val)
    (hv : ∀ (S : TestAlgebra T) (z : Points ((groupBaseChange K T).obj C.split.spin.val).X S),
      spinVectorMatrix P S (z ≫ v.hom.hom.hom) =
        spinVectorMatrix C.split ((restrictTestAlgebra K T).obj S)
          (baseChangePoint K T C.split.spin.val.X S z))
    (S : TestAlgebra T) (σ : Gal(T/L))
    (f : (restrictTestAlgebra L T).obj S ⟶ (restrictTestAlgebra L T).obj S)
    (hf : ∀ b, f.hom (algebraMap T S b) = algebraMap T S (σ b))
    (x y : Points ((groupBaseChange L T).obj ((groupBaseChange F L).obj G.val)).X S)
    (hxy : baseChangePoint L T ((groupBaseChange F L).obj G.val).X S y =
      mapPoints f (baseChangePoint L T ((groupBaseChange F L).obj G.val).X S x)) :
    let v' := extendedSpinComparison (L := L) C P v
    spinVectorMatrix P S (y ≫ v'.hom.hom.hom) =
      conjugate (Matrix.GeneralLinearGroup.map (algebraMap T S) (extendedConjugator C σ))
        ((spinVectorMatrix P S (x ≫ v'.hom.hom.hom)).map f.hom) := by
  let a := (exchangeBaseChange (F := F) (K := K) (L := L) (T := T)).app G.val
  let U := (restrictTestAlgebra K T).obj S
  let f' : twiceRestricted F K T S ⟶ twiceRestricted F K T S := restrictSemilinearMap S f
  let δ : Gal(K/F) := restrictGalois (F := F) σ
  have hf' (b : K) : f'.hom (algebraMap K U b) = algebraMap K U (δ b) := by
    change f.hom (algebraMap T S (algebraMap K T b)) =
      algebraMap T S (algebraMap K T (δ b))
    rw [hf, restrictGalois_apply]
  let base (z : Points ((groupBaseChange L T).obj ((groupBaseChange F L).obj G.val)).X S) :=
    baseChangePoint K T ((groupBaseChange F K).obj G.val).X S (z ≫ a.hom.hom.hom)
  have hbase : baseChangePoint F K G.val.X U (base y) =
      mapPoints f' (baseChangePoint F K G.val.X U (base x)) :=
    exchange_semilinear_points G.val S f x y hxy
  have hVector (z : Points ((groupBaseChange L T).obj ((groupBaseChange F L).obj G.val)).X S) :
      spinVectorMatrix P S (z ≫ (extendedSpinComparison (L := L) C P v).hom.hom.hom) =
        spinVectorMatrix C.split U (base z ≫ C.comparison.hom.hom.hom) := by
    let p : Points ((groupBaseChange K T).obj ((groupBaseChange F K).obj G.val)).X S :=
      z ≫ a.hom.hom.hom
    let w := p ≫ ((groupBaseChange K T).map C.comparison.hom).hom.hom
    have hz : baseChangePoint K T C.split.spin.val.X S w = base z ≫ C.comparison.hom.hom.hom :=
      baseChangePointsSchemeNaturality K T C.comparison.hom.hom.hom S p
    have he : z ≫ (extendedSpinComparison (L := L) C P v).hom.hom.hom = w ≫ v.hom.hom.hom := by
      simp only [extendedSpinComparison, Iso.trans_hom, Functor.mapIso_hom, Grp.comp_hom_hom,
        Category.assoc, p, w, a]
    rw [he, hv S w, hz]
  dsimp only
  rw [hVector y, hVector x]
  exact C.equivariance U δ f' hf' (base x) (base y) hbase

private def extendedScalarComparison
    (P : SplitSpinVectorImage L I) (Q : SplitSpinVectorImage T I)
    (b : (groupBaseChange F L).obj C.reference.kernel.group ≅ P.kernel.group)
    (d : (groupBaseChange K T).obj C.split.kernel.group ≅ Q.kernel.group) :
    (groupBaseChange L T).obj P.kernel.group ≅ Q.kernel.group :=
  ((groupBaseChange L T).mapIso b).symm ≪≫
    (exchangeBaseChange (F := F) (K := K) (L := L) (T := T)).app C.reference.kernel.group ≪≫
    (groupBaseChange K T).mapIso C.splitScalar ≪≫ d

private theorem extended_scalar_inclusion
    (P : SplitSpinVectorImage L I) (Q : SplitSpinVectorImage T I)
    (b : (groupBaseChange F L).obj C.reference.kernel.group ≅ P.kernel.group)
    (v : (groupBaseChange K T).obj C.split.spin.val ≅ Q.spin.val)
    (d : (groupBaseChange K T).obj C.split.kernel.group ≅ Q.kernel.group)
    (hd : (groupBaseChange K T).map C.split.kernel.inclusion ≫ v.hom = d.hom ≫ Q.kernel.inclusion) :
    (groupBaseChange L T).map (b.inv ≫ (groupBaseChange F L).map C.scalar) ≫
        (extendedSpinComparison (L := L) C Q v).hom =
      (extendedScalarComparison C P Q b d).hom ≫ Q.kernel.inclusion := by
  let a := exchangeBaseChange (F := F) (K := K) (L := L) (T := T)
  have hn : (groupBaseChange L T).map ((groupBaseChange F L).map C.scalar) ≫ a.hom.app G.val =
      a.hom.app C.reference.kernel.group ≫
        (groupBaseChange K T).map ((groupBaseChange F K).map C.scalar) :=
    a.hom.naturality C.scalar
  simp only [extendedSpinComparison, extendedScalarComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  change (groupBaseChange L T).map b.inv ≫
      (groupBaseChange L T).map ((groupBaseChange F L).map C.scalar) ≫
      a.hom.app G.val ≫ (groupBaseChange K T).map C.comparison.hom ≫ v.hom =
    (groupBaseChange L T).map b.inv ≫ a.hom.app C.reference.kernel.group ≫
      (groupBaseChange K T).map C.splitScalar.hom ≫ d.hom ≫ Q.kernel.inclusion
  rw [← Category.assoc ((groupBaseChange L T).map ((groupBaseChange F L).map C.scalar)),
    hn, Category.assoc]
  have h := congrArg (groupBaseChange K T).map C.scalarInclusion
  simp only [Functor.map_comp] at h
  rw [← Category.assoc ((groupBaseChange K T).map ((groupBaseChange F K).map C.scalar)),
    h, Category.assoc, hd]

private theorem extended_scalar_value
    (P : SplitSpinVectorImage L I) (Q : SplitSpinVectorImage T I)
    (b : (groupBaseChange F L).obj C.reference.kernel.group ≅ P.kernel.group)
    (d : (groupBaseChange K T).obj C.split.kernel.group ≅ Q.kernel.group)
    (hb : ∀ (R : TestAlgebra L) (x : Points ((groupBaseChange F L).obj C.reference.kernel.group).X R),
      (C.reference.kernelPoints ((restrictTestAlgebra F L).obj R)
        (baseChangePoint F L C.reference.kernel.group.X R x)).val.val =
      (P.kernelPoints R (x ≫ b.hom.hom.hom)).val.val)
    (hd : ∀ (R : TestAlgebra T) (x : Points ((groupBaseChange K T).obj C.split.kernel.group).X R),
      (C.split.kernelPoints ((restrictTestAlgebra K T).obj R)
        (baseChangePoint K T C.split.kernel.group.X R x)).val.val =
      (Q.kernelPoints R (x ≫ d.hom.hom.hom)).val.val)
    (S : TestAlgebra T) (x : Points ((groupBaseChange L T).obj P.kernel.group).X S) :
    (P.kernelPoints ((restrictTestAlgebra L T).obj S) (baseChangePoint L T P.kernel.group.X S x)).val.val =
      (Q.kernelPoints S (x ≫ (extendedScalarComparison C P Q b d).hom.hom.hom)).val.val := by
  let a := (exchangeBaseChange (F := F) (K := K) (L := L) (T := T)).app C.reference.kernel.group
  let y : Points ((groupBaseChange F L ⋙ groupBaseChange L T).obj C.reference.kernel.group).X S :=
    x ≫ ((groupBaseChange L T).map b.inv).hom.hom
  let z : Points ((groupBaseChange F K ⋙ groupBaseChange K T).obj C.reference.kernel.group).X S :=
    y ≫ a.hom.hom.hom
  let w : Points ((groupBaseChange K T).obj C.split.kernel.group).X S :=
    z ≫ ((groupBaseChange K T).map C.splitScalar.hom).hom.hom
  let U := (restrictTestAlgebra L T).obj S
  let V := (restrictTestAlgebra K T).obj S
  have h₁ := hb U (baseChangePoint L T ((groupBaseChange F L).obj C.reference.kernel.group).X S y)
  have he : baseChangePoint L T ((groupBaseChange F L).obj C.reference.kernel.group).X S y ≫ b.hom.hom.hom =
      baseChangePoint L T P.kernel.group.X S x := by
    have h := baseChangePointsSchemeNaturality L T b.inv.hom.hom S x
    change baseChangePoint L T ((groupBaseChange F L).obj C.reference.kernel.group).X S y =
      baseChangePoint L T P.kernel.group.X S x ≫ b.inv.hom.hom at h
    rw [h, Category.assoc, ← Grp.comp_hom_hom, b.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [he] at h₁
  have h₂ := C.scalarValue V (baseChangePoint K T ((groupBaseChange F K).obj C.reference.kernel.group).X S z)
  have hf : baseChangePoint K T C.split.kernel.group.X S w =
      baseChangePoint K T ((groupBaseChange F K).obj C.reference.kernel.group).X S z ≫
        C.splitScalar.hom.hom.hom :=
    baseChangePointsSchemeNaturality K T C.splitScalar.hom.hom.hom S z
  have hmap := exchange_point (F := F) (K := K) (L := L) C.reference.kernel.group S y
  change twiceBasedPoint K C.reference.kernel.group S z =
    mapPoints (twiceRestrictedMap S) (twiceBasedPoint L C.reference.kernel.group S y) at hmap
  have hcon : (C.reference.kernelPoints (twiceRestricted F K T S)
      (twiceBasedPoint K C.reference.kernel.group S z)).val.val =
      (C.reference.kernelPoints (twiceRestricted F L T S)
        (twiceBasedPoint L C.reference.kernel.group S y)).val.val := by
    let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
      (Fintype.equivFin (I ⊕ I)).injective
    rw [hmap, splitKernelPoint_natural C.reference]
    rfl
  have hresult : x ≫ (extendedScalarComparison C P Q b d).hom.hom.hom = w ≫ d.hom.hom.hom := by
    simp only [extendedScalarComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Grp.comp_hom_hom, Category.assoc, y, z, w, a]
  rw [hresult, ← hd S w, hf, ← h₂]
  exact h₁.symm.trans hcon.symm

set_option maxHeartbeats 900000 in
include C in
private theorem extendSpinTrivialization (hI : 4 ≤ Fintype.card I) :
    Nonempty (EquivariantSpinTrivialization (K := T) (I := I) (baseChangedAlgebraicGroup L G)) := by
  let e : Fin ((Fintype.card I - 1) + 1) ≃ I := (finCongr (by omega)).trans (Fintype.equivFin I).symm
  let : LinearOrder (I ⊕ I) := LinearOrder.lift' (Fintype.equivFin (I ⊕ I))
    (Fintype.equivFin (I ⊕ I)).injective
  obtain ⟨P⟩ := NontrialitarianSpinModels.splitSpinImage L I hI
  obtain ⟨Q⟩ := NontrialitarianSpinModels.splitSpinImage T I hI
  obtain ⟨v, hv⟩ := splitSpinScalarComparison C.split Q e
  obtain ⟨d, hd, hd'⟩ := splitKernelFieldComparison C.split Q e v (fun S z => (hv S z).1)
  obtain ⟨s, hs⟩ := splitSpinScalarComparison C.reference P e
  obtain ⟨b, _, hb⟩ := splitKernelFieldComparison C.reference P e s (fun S z => (hs S z).1)
  obtain ⟨ρ, hρ⟩ := extended_action (L := L) (T := T) C
  refine ⟨{ reference := P
            split := Q
            comparison := extendedSpinComparison (L := L) C Q v
            g := extendedConjugator C
            multiplier := fun σ => Units.map (algebraMap K T).toMonoidHom
              (C.multiplier (restrictGalois (F := F) σ))
            action := ρ
            actionFormula := hρ
            similarity := ?_
            equivariance := ?_
            scalar := b.inv ≫ (groupBaseChange F L).map C.scalar
            splitScalar := extendedScalarComparison C P Q b d
            scalarInclusion := extended_scalar_inclusion C P Q b v d hd
            scalarValue := extended_scalar_value C P Q b d hb hd' }⟩
  · intro σ
    exact similitude_extension _ _ (C.similarity (restrictGalois (F := F) σ))
  · intro S σ R f hf x y hxy
    change spinVectorMatrix Q S (y ≫ (extendedSpinComparison (L := L) C Q v).hom.hom.hom) =
      conjugate (Matrix.GeneralLinearGroup.map (algebraMap T S) (extendedConjugator C σ))
        ((spinVectorMatrix Q S (x ≫ (extendedSpinComparison (L := L) C Q v).hom.hom.hom)).map f.hom)
    exact extended_vector_equivariance C Q v (fun R z => (hv R z).2) S σ f hf x y hxy

end

end FieldExtension

section GlobalGeneration

open AlgebraicGeometry CategoryTheory Matrix ValuativeRel
open Specs.Arithmetic.NontrialitarianSpinModels
  (EquivariantSpinTrivialization HasFixedVectorVertex)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Arithmetic.OppositeRadicals (localPlus)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (StrongApproximation)
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData SeparatingParameter)
open Specs.IntegralModels (MatrixRealization)
open private spinModel_of_trivialization
  from LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
open private localPlus_eq_univ from LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration

set_option backward.isDefEq.respectTransparency false

private theorem local_top_of_scalar_extension
    {F K L I : Type u} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I] [Nonempty I]
    [CharP L 2] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {G : AffineAlgebraicGroup F}
    (C : EquivariantSpinTrivialization (K := K) (I := I) G) (hI : 4 ≤ Fintype.card I)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G) :
    unipotentGenerated (baseChangedAlgebraicGroup L G) = ⊤ := by
  obtain ⟨T, _, _, _, _, _, _, _, hTower⟩ := finite_galois_field_over_extension F K L
  let : IsScalarTower F K T := hTower
  let G' := baseChangedAlgebraicGroup L G
  have hG' := OppositeRadicals.absolutelyAlmostSimpleFieldExtension (F := L) G hG
  obtain ⟨C'⟩ := extendSpinTrivialization (L := L) (T := T) C hI
  obtain ⟨D'⟩ := NontrialitarianSpinModels.quadraticPairDescent L T I C'.action
    (fun σ => ⟨C'.g σ, C'.multiplier σ, C'.actionFormula σ, C'.similarity σ⟩)
  obtain ⟨M⟩ := spinModel_of_trivialization G' hG'.1.2.1 hI C' D'
  exact unipotentGenerated_eq_top_of_spin_model M hI hG'

private theorem finite_place_local_plus_dense
    {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I] [Nonempty I]
    {G : AffineAlgebraicGroup F}
    (C : EquivariantSpinTrivialization (K := K) (I := I) G) (hI : 4 ≤ Fintype.card I)
    (hG : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple G)
    (D : GlobalFieldData.{u,v} F) (i : MatrixRealization G) (w : D.FinitePlace) :
    Dense (localPlus D i (.inl w)) := by
  let L := D.FiniteCompletion w
  let : Field L := inferInstanceAs (Field (D.FiniteCompletion w))
  let : ValuativeRel L := inferInstanceAs (ValuativeRel (D.FiniteCompletion w))
  let : TopologicalSpace L := inferInstanceAs (TopologicalSpace (D.FiniteCompletion w))
  let : IsNonarchimedeanLocalField L := GlobalFieldData.finiteCompletion_isLocalField D w
  let : Algebra F L := LinearAlgebraicGroups.Arithmetic.AdelicGroups.completionAlgebra D (.inl w)
  let : CharP L 2 := charP_of_injective_algebraMap (algebraMap F L).injective 2
  have htop := local_top_of_scalar_extension (L := L) C hI hG
  rw [localPlus_eq_univ D i (.inl w) htop]
  exact dense_univ

theorem nontrialitarianStrongApproximation : NontrialitarianStrongApproximation.{u,v} := by
  intro F _ _ k _ _ _ t G n hn hG hsc hv i S hS
  let D := GlobalFieldData.function k t
  apply strongApproximation_of_completion_density CharacteristicTwoQuadraticPairs.nontrialitarianIsotropy
    F (separating_parameter_arithmetic_field k t) D G n hn hG hsc hv i S hS
  obtain ⟨K, _, _, _, _, ⟨C⟩⟩ := NontrialitarianSpinModels.finiteEquivariantSpinReference
    F G n hn hG hsc hv
  let I := ULift.{u} (Fin n)
  let : Nonempty I := ⟨ULift.up ⟨0, by omega⟩⟩
  have hI : 4 ≤ Fintype.card I := by simpa [I] using hn
  intro w
  rcases w with w | w
  · exact finite_place_local_plus_dense C hI (arithmetic_absolute_simplicity hG) D i w
  · exact PEmpty.elim w

end GlobalGeneration

end LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
