import Specs.LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
import LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import LinearAlgebraicGroups.Arithmetic.AdditiveStrongApproximation
import Mathlib.Topology.Instances.Matrix
import Mathlib.GroupTheory.Commutator.Finite
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Topology.Algebra.IsOpenUnits
import MathGenome.Internal.D07.Ch20.Hilbert90Additive
import MathGenome.Internal.D07.Ch20.Hilbert90Multiplicative
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.QuaternionSplitting
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.RealClasses
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.SimpleRing.Congr

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct WithZero commutatorElement Matrix
open RM03.CSA
open Topology Filter ValuativeRel

namespace LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

open Spec

private theorem norm_algEquiv {F A B : Type*} [Field F] [Ring A] [Ring B]
    [Algebra F A] [Algebra F B] (hA : IsCentralSimple F A) (hB : IsCentralSimple F B)
    (e : A ≃ₐ[F] B) (x : A) :
    reducedNorm hA x = reducedNorm hB (e x) := by
  obtain ⟨s⟩ := algEquiv_matrix_algebraicClosure hB
  have hd : degree F B = degree F A := congrArg Nat.sqrt e.toLinearEquiv.finrank_eq.symm
  let s' := ((Algebra.TensorProduct.congr (AlgEquiv.refl : AlgebraicClosure F ≃ₐ[AlgebraicClosure F] _) e).trans
    s).trans (Matrix.reindexAlgEquiv _ _ (finCongr hd))
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [reducedNorm_map hA x s', reducedNorm_map hB (e x) s]
  simp [s']

private theorem norm_field {F : Type*} [Field F] (hF : IsCentralSimple F F) (x : F) :
    reducedNorm hF x = x := by
  have hd : degree F F = 1 := by simp [degree]
  obtain ⟨s⟩ := algEquiv_matrix_algebraicClosure hF
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [reducedNorm_map hF x s]
  have hs : (1 : AlgebraicClosure F) ⊗ₜ[F] x =
      algebraMap (AlgebraicClosure F) (BaseChange F (AlgebraicClosure F) F)
        (algebraMap F (AlgebraicClosure F) x) := by
    change (1 : AlgebraicClosure F) ⊗ₜ[F] x = (algebraMap F (AlgebraicClosure F) x) ⊗ₜ[F] (1 : F)
    calc
      (1 : AlgebraicClosure F) ⊗ₜ[F] x =
          (1 : AlgebraicClosure F) ⊗ₜ[F] (x • (1 : F)) := by simp
      _ = x • (1 : AlgebraicClosure F) ⊗ₜ[F] (1 : F) := by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = (algebraMap F (AlgebraicClosure F)) x ⊗ₜ[F] (1 : F) := by
        change (x • (1 : AlgebraicClosure F)) ⊗ₜ[F] (1 : F) = _
        rw [Algebra.smul_def, mul_one]
  rw [hs, s.commutes, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, hd, pow_one, mul_one]

private theorem norm_quaternion (h : IsCentralSimple ℝ (Quaternion ℝ)) (x : Quaternion ℝ) :
    reducedNorm h x = Quaternion.normSq x := by
  open _root_.Specs.D07.Ch23.QuaternionAlgebra in
  have he : x = (x.re : H) + x.imI • iH + x.imJ • jH + x.imK • kH := by
    ext <;> simp [iH, jH, kH, _root_.Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.iH,
      _root_.Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.jH,
      _root_.Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.kH]
  conv_lhs => rw [he]
  exact (RM03.Brauer.QuaternionSplitting.reduced_norm h x.re x.imI x.imJ x.imK).trans
    (Quaternion.normSq_def' x).symm

private theorem commutator_of_mul_eq {G : Type*} [Group G] {a b x : G}
    (h : a * b = x * (b * a)) : ⁅a, b⁆ = x := by
  rw [commutatorElement_def, h]
  group

private theorem quaternion_commutator (x : (Quaternion ℝ)ˣ)
    (hx : Quaternion.normSq (x : Quaternion ℝ) = 1) :
    ∃ a b : (Quaternion ℝ)ˣ, ⁅a, b⁆ = x := by
  let q : Quaternion ℝ := x
  change Quaternion.normSq q = 1 at hx
  have hq : q * star q = 1 := by simpa [hx] using Quaternion.self_mul_star q
  by_cases hneg : q = -1
  · let i : Quaternion ℝ := ⟨0, 1, 0, 0⟩
    let j : Quaternion ℝ := ⟨0, 0, 1, 0⟩
    have hi : i ≠ 0 := by intro h; have := congrArg (fun z : Quaternion ℝ => z.imI) h; norm_num [i] at this
    have hj : j ≠ 0 := by intro h; have := congrArg (fun z : Quaternion ℝ => z.imJ) h; norm_num [j] at this
    refine ⟨Units.mk0 i hi, Units.mk0 j hj, commutator_of_mul_eq ?_⟩
    apply Units.ext
    change i * j = q * (j * i)
    rw [hneg]
    ext <;> norm_num [i, j, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]
  · obtain ⟨v, hv, hconj⟩ : ∃ v : Quaternion ℝ, v ≠ 0 ∧ v * q = star q * v := by
      by_cases hz : q.imI = 0 ∧ q.imJ = 0
      · let v : Quaternion ℝ := ⟨0, 1, 0, 0⟩
        refine ⟨v, ?_, ?_⟩
        · intro h
          have := congrArg (fun z : Quaternion ℝ => z.imI) h
          norm_num [v] at this
        · ext <;> simp [v, hz.1, hz.2]
      · let v : Quaternion ℝ := ⟨0, -q.imJ, q.imI, 0⟩
        refine ⟨v, ?_, ?_⟩
        · intro h
          exact hz ⟨by simpa [v] using congrArg (fun z : Quaternion ℝ => z.imJ) h,
            by simpa [v] using congrArg (fun z : Quaternion ℝ => z.imI) h⟩
        · ext <;> simp [v] <;> ring
    have hu : 1 + q ≠ 0 := by
      intro h
      apply hneg
      simpa [add_comm] using eq_neg_of_add_eq_zero_left (show q + 1 = 0 by simpa [add_comm] using h)
    refine ⟨Units.mk0 (1 + q) hu, Units.mk0 v hv, commutator_of_mul_eq ?_⟩
    apply Units.ext
    change (1 + q) * v = q * (v * (1 + q))
    calc
      (1 + q) * v = v + q * v := by rw [add_mul, one_mul]
      _ = q * (v * (1 + q)) := by rw [mul_add, mul_one, hconj, mul_add, ← mul_assoc, hq,
        one_mul, add_comm]

theorem realDivision : RealDivision.{v} := by
  intro B _ _ hB x hx
  letI := hB.2.2
  obtain ⟨n, h, _⟩ := D07.Ch23.Frobenius.finiteDimensionalClassification B
  rcases h with ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · have hn := norm_algEquiv hB (show IsCentralSimple ℝ ℝ from
        ⟨inferInstance, inferInstance, inferInstance⟩) e.symm (x : B)
    rw [norm_field] at hn
    change reducedNorm hB (x : B) = 1 at hx
    rw [hx] at hn
    have h : x = 1 := Units.ext (e.symm.injective (by simpa using hn.symm))
    exact ⟨1, 1, by simp [h]⟩
  · have hcenter : e Complex.I ∈ Subalgebra.center ℝ B := by
      apply Subalgebra.mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mul_comm]
    letI := hB.2.1
    obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hcenter
    have hi : Complex.I = algebraMap ℝ ℂ r := e.injective (hr.trans (e.commutes r).symm)
    simpa using congrArg Complex.im hi
  · let hH := isCentralSimple_of_isCentralDivision ℝ (Quaternion ℝ)
      RM03.Brauer.quaternion_isCentralDivision
    let y := Units.map e.symm.toMonoidHom x
    change reducedNorm hB (x : B) = 1 at hx
    have hy : Quaternion.normSq (y : Quaternion ℝ) = 1 := by
      rw [← norm_quaternion hH]
      exact (norm_algEquiv hB hH e.symm (x : B)).symm.trans hx
    obtain ⟨a, b, hab⟩ := quaternion_commutator y hy
    refine ⟨Units.map e.toMonoidHom a, Units.map e.toMonoidHom b, ?_⟩
    rw [← map_commutatorElement, hab]
    exact Units.ext (e.apply_symm_apply _)

theorem complexDivision : ComplexDivision.{v} := by
  intro B _ _ hB x hx
  letI := hB.2.2
  have hs : Function.Surjective (algebraMap ℂ B) := by
    intro y
    let f := minpoly ℂ y
    have hfirr : Irreducible f := minpoly.irreducible (IsIntegral.of_finite ℂ y)
    have hfd := (IsAlgClosed.splits f).natDegree_eq_one_of_irreducible hfirr
    have hm : f.Monic := minpoly.monic (IsIntegral.of_finite ℂ y)
    have hf : f = Polynomial.X + Polynomial.C (f.coeff 0) := hm.eq_X_add_C hfd
    have hy := minpoly.aeval ℂ y
    change Polynomial.aeval y f = 0 at hy
    rw [hf, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at hy
    exact ⟨-f.coeff 0, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hy).symm⟩
  let e := AlgEquiv.ofBijective (Algebra.ofId ℂ B) ⟨(algebraMap ℂ B).injective, hs⟩
  have hn := norm_algEquiv hB (show IsCentralSimple ℂ ℂ from
    ⟨inferInstance, inferInstance, inferInstance⟩) e.symm (x : B)
  rw [norm_field] at hn
  change reducedNorm hB (x : B) = 1 at hx
  rw [hx] at hn
  exact Units.ext (e.symm.injective (by simpa using hn.symm))

/-- The norm on units takes values in the scalar units. -/
noncomputable def normUnits {F A : Type*} [Field F] [Ring A] [Algebra F A]
    (hA : IsCentralSimple F A) : Aˣ →* Fˣ :=
  Units.map
    { toFun := reducedNorm hA
      map_one' := reducedNorm_one hA
      map_mul' := reducedNorm_mul hA }

theorem commutator_norm_one {F A : Type*} [Field F] [Ring A] [Algebra F A]
    (hA : IsCentralSimple F A) {x : Aˣ} (hx : x ∈ commutator Aˣ) :
    x ∈ normOne hA := by
  change reducedNorm hA (x : A) = 1
  have hk : commutator Aˣ ≤ (normUnits hA).ker := by
    change ⁅(⊤ : Subgroup Aˣ), (⊤ : Subgroup Aˣ)⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact congrArg Units.val (hk hx)

section FinitePlace

open LocalDivisionAlgebras

variable {F B : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [DivisionRing B] [Algebra F B]

private theorem unit_value_of_norm_one (hB : IsCentralSimple F B)
    {w : Valuation B ℤᵐ⁰} (hw : IsDivisionValuation hB w)
    {x : Bˣ} (hx : x ∈ normOne hB) : w (x : B) = 1 := by
  change reducedNorm hB (x : B) = 1 at hx
  rw [hw.1]
  change baseValue F (reducedNorm hB (x : B)) = 1
  rw [hx]
  simp [baseValue]

private theorem residue_eq_iff_sub_lt (w : Valuation B ℤᵐ⁰) (x y : w.integer) :
    residue w x = residue w y ↔ w ((x : B) - (y : B)) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  rfl

private theorem value_one_add (w : Valuation B ℤᵐ⁰) {z : B} (hz : w z < 1) :
    w (1 + z) = 1 := by
  exact w.map_one_add_of_lt hz

private theorem val_add_unit_ne (w : Valuation B ℤᵐ⁰) {z : B} (hz : w z < 1) :
    1 + z ≠ 0 := by
  intro he
  have h := value_one_add w hz
  rw [he, map_zero] at h
  exact zero_ne_one h

private theorem valuation_of_diff_mul_unit (w : Valuation B ℤᵐ⁰) (x y : Bˣ)
    (hy : w (y : B) = 1) :
    w ((x * y⁻¹ : Bˣ).val - 1) = w ((x : B) - (y : B)) := by
  rw [show (x * y⁻¹ : Bˣ).val - 1 = ((x : B) - (y : B)) * y.inv by
    rw [sub_mul, y.val_inv, Units.val_mul, y.inv_eq_val_inv]]
  have hy' : w y.inv = 1 := by
    have h := congrArg w y.val_inv
    rw [map_mul, hy, one_mul, map_one] at h
    exact h
  rw [map_mul, hy', mul_one]

private theorem valuation_of_unit_mul_diff (w : Valuation B ℤᵐ⁰) (x y z : Bˣ)
    (hx : w (x : B) = 1) :
    w (((x * y : Bˣ) : B) - ((x * z : Bˣ) : B)) = w ((y : B) - (z : B)) := by
  simp only [Units.val_mul, ← mul_sub, map_mul, hx, one_mul]

private theorem lt_layer_of_lt_one {v : ℤᵐ⁰} (h : v < 1) :
    v ≤ WithZero.exp (-1) := by
  by_cases hv : v = 0
  · simp [hv]
  · lift v to (Multiplicative ℤ) using hv with a
    change WithZero.exp a.toAdd < 1 at h
    change WithZero.exp a.toAdd ≤ WithZero.exp (-1)
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable (hB : IsCentralSimple F B) {w : Valuation B ℤᵐ⁰}
    (hw : IsDivisionValuation hB w) (r : ResidueData (F := F) w)
    (P : CyclicPresentation (F := F) w r)

attribute [local instance] CyclicPresentation.fieldL CyclicPresentation.algebraL

private abbrev integralEmbed : P.vL.valuationSubring →+* w.integer :=
  P.embed.toRingHom.restrict P.vL.valuationSubring.toSubring w.integer fun x hx => by
    change w (P.embed x) ≤ 1
    rw [P.restrict_val]
    exact pow_le_one₀ zero_le hx

private abbrev reduceL : P.vL.valuationSubring →+* ResidueRing w :=
  P.residueEquiv.toRingHom.comp (IsLocalRing.residue _)

private theorem reduceL_surjective : Function.Surjective (reduceL r P) :=
  P.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := P.vL.valuationSubring))

private theorem reduceL_embed (a : P.vL.valuationSubring) :
    residue w (integralEmbed r P a) = reduceL r P a :=
  (P.residue_eq a _ rfl).symm

private theorem residue_generator :
    letI := r.isField.toField
    letI := r.algebra
    ∀ σ, σ ∈ Subgroup.zpowers (P.residueAutEquiv P.τ) := by
  intro σ
  obtain ⟨s, rfl⟩ := P.residueAutEquiv.surjective σ
  have hs : s ∈ Subgroup.zpowers P.τ := P.gen.ge (Subgroup.mem_top _)
  obtain ⟨i, rfl⟩ := hs
  exact ⟨i, (map_zpow _ _ _).symm⟩

private theorem integral_conj (a : P.L) (k : ℕ) :
    P.embed a * (P.uniformizer : B) ^ k =
      (P.uniformizer : B) ^ k * P.embed (((P.τ⁻¹) ^ k) a) := by
  have h (x : P.L) :
      P.embed x * (P.uniformizer : B) = (P.uniformizer : B) * P.embed (P.τ⁻¹ x) := by
    simpa using (P.conjugation (P.τ⁻¹ x)).symm
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ,
      pow_succ' (P.τ⁻¹) k, AlgEquiv.mul_apply]

include hw in
/-- The first-order determinant constraint on layers that are powers of the scalar
uniformizer. The matrix Taylor formula is evaluated in the integral maximal subfield. -/
private theorem layer_trace_zero
    (y : w.integer) {m : ℕ} (hm : 0 < m)
    (h : reducedNorm hB (1 + algebraMap F B (P.parameter ^ m) * (y : B)) = 1) :
    letI := r.isField.toField
    letI := r.algebra
    Algebra.trace (BaseResidue F) (ResidueRing w) (residue w y) = 0 := by
  classical
  letI : Field P.L := P.fieldL
  letI : Algebra F P.L := P.algebraL
  letI := r.isField.toField
  letI := r.algebra
  letI := rightSubfieldModule P.embed
  letI := Algebra.TensorProduct.rightAlgebra (R := F) (A := B) (B := P.L)
  obtain ⟨act, hact⟩ := subfieldTensorAction_isomorphism P.embed hB.2 P.degree
  let s := ((baseChangeEquivTensor F P.L B).trans act).trans (LinearMap.toMatrixAlgEquiv P.basis)
  let f : B →ₐ[F] Matrix (Fin (degree F B)) (Fin (degree F B)) P.L :=
    (s.toAlgHom.restrictScalars F).comp Algebra.TensorProduct.includeRight
  let O := P.vL.valuationSubring
  have hp (i : Fin (degree F B)) : P.basis i ∈ w.integer := by
    rw [w.mem_integer_iff, P.basis_eq, map_pow, P.value_uniformizer]
    exact pow_le_one₀ zero_le (by simp)
  have hf (i j : Fin (degree F B)) : f (y : B) i j = P.basis.repr ((y : B) * P.basis j) i := by
    change LinearMap.toMatrix P.basis P.basis
      (act ((baseChangeEquivTensor F P.L B) (1 ⊗ₜ[F] (y : B)))) i j = _
    rw [LinearMap.toMatrix_apply]
    change P.basis.repr (act.toAlgHom ((y : B) ⊗ₜ[F] (1 : P.L)) (P.basis j)) i = _
    rw [hact, subfieldTensorAction_tmul, map_one, mul_one]
  let M : Matrix (Fin (degree F B)) (Fin (degree F B)) O := fun i j =>
    ⟨f (y : B) i j, (hf i j).symm ▸
      (P.integral_coordinates _).mp (w.integer.mul_mem y.2 (hp j)) i⟩
  have hM : M.map O.subtype = f (y : B) := rfl
  let t : O := ⟨algebraMap F P.L P.parameter, by
    change P.vL (algebraMap F P.L P.parameter) ≤ 1
    rw [P.base_value, P.value_parameter]
    simp⟩
  have ht₀ : t ≠ 0 := by
    intro ht
    have hz : (t : P.L) = 0 := congrArg Subtype.val ht
    have hv : P.vL (t : P.L) = WithZero.exp (-1) := (P.base_value _).trans P.value_parameter
    rw [hz, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have htres : reduceL r P t = 0 := by
    rw [← reduceL_embed, residue_eq_zero_iff]
    change w (P.embed (algebraMap F P.L P.parameter)) < 1
    rw [P.restrict_val, P.base_value, P.value_parameter]
    exact pow_lt_one₀ zero_le (by simp) (degree_pos hB).ne'
  have hdet : (1 + (t ^ m) • M).det = 1 := by
    apply O.subtype_injective
    rw [RingHom.map_det, map_one]
    have h' := reducedNorm_map hB (1 + algebraMap F B (P.parameter ^ m) * (y : B)) s
    rw [h, map_one] at h'
    change 1 = (f (1 + algebraMap F B (P.parameter ^ m) * (y : B))).det at h'
    rw [map_add, map_one, map_mul, f.commutes, IsScalarTower.algebraMap_apply F P.L,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul, map_pow] at h'
    change ((1 + (t ^ m) • M).map O.subtype).det = 1
    rw [Matrix.map_add, Matrix.map_one, Matrix.map_smul, hM]
    exact h'.symm
    all_goals intros; rfl
  let Q := (1 + (Polynomial.X : Polynomial O) • M.map Polynomial.C).det.divX.divX.eval (t ^ m)
  have hzero : (M.trace + Q * t ^ m) * t ^ m = 0 := by
    have hh := Matrix.det_one_add_smul (t ^ m) M
    rw [hdet] at hh
    change 1 = 1 + M.trace * t ^ m + Q * (t ^ m) ^ 2 at hh
    apply add_left_cancel (a := (1 : O))
    calc
      1 + (M.trace + Q * t ^ m) * t ^ m = 1 + M.trace * t ^ m + Q * (t ^ m) ^ 2 := by ring
      _ = 1 + 0 := by simpa using hh.symm
  have htrace : reduceL r P M.trace = 0 := by
    have he := (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero _ ht₀)
    have he' := congrArg (reduceL r P) he
    simpa [map_add, map_mul, map_pow, htres, zero_pow hm.ne'] using he'
  obtain ⟨_, a, _, ha, _, hres⟩ := reduction_of_norm_trace hB w hw r y
  let aL : O := ⟨algebraMap F P.L (a : F), by
    change P.vL (algebraMap F P.L (a : F)) ≤ 1
    rw [P.base_value]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toOrderIso.le_iff_le.mpr a.2 |>.trans_eq
      (map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F))⟩
  have hta : M.trace = aL := by
    apply Subtype.ext
    change O.subtype M.trace = algebraMap F P.L (a : F)
    rw [AddMonoidHom.map_trace O.subtype, hM, ha, reducedTrace_map hB s]
    rfl
  rw [hta] at htrace
  change P.residueEquiv (IsLocalRing.residue O aL) = 0 at htrace
  rw [P.residue_scalar a aL rfl, hres] at htrace
  exact (algebraMap (BaseResidue F) (ResidueRing w)).injective (by simpa using htrace)

private def integralTranslate (σ : P.L ≃ₐ[F] P.L)
    (hσ : ∀ a, P.vL (σ a) = P.vL a) (a : P.vL.valuationSubring) :
    P.vL.valuationSubring :=
  ⟨σ (a : P.L), by change P.vL (σ (a : P.L)) ≤ 1; rw [hσ]; exact a.2⟩

private theorem value_embed_of_residue_ne (a : P.vL.valuationSubring) (ha : reduceL r P a ≠ 0) :
    w (P.embed (a : P.L)) = 1 := by
  have hh := (integralEmbed r P a).2
  change w (P.embed (a : P.L)) ≤ 1 at hh
  refine hh.antisymm (le_of_not_gt fun h => ha ?_)
  rw [← reduceL_embed, residue_eq_zero_iff]
  exact h

private theorem value_one_ne_zero (w : Valuation B ℤᵐ⁰) {x : B}
    (hx : w x = 1) : x ≠ 0 := by
  intro h
  simp [h] at hx

include hw r P in
private theorem residue_commutator (x : Bˣ) (hx : x ∈ normOne hB) :
    ∃ c ∈ commutator Bˣ, w ((x : B) - (c : B)) < 1 := by
  letI := r.isField.toField
  letI := r.algebra
  letI := r.finite
  letI : IsGalois (BaseResidue F) (ResidueRing w) := inferInstance
  let xO : w.integer := ⟨(x : B), (unit_value_of_norm_one hB hw hx).le⟩
  have hxne : residue w xO ≠ 0 := by
    rw [ne_eq, residue_eq_zero_iff]
    exact not_lt_of_ge (unit_value_of_norm_one hB hw hx).ge
  obtain ⟨a, _, ha, _, hnorm, _⟩ := reduction_of_norm_trace hB w hw r xO
  change reducedNorm hB (x : B) = 1 at hx
  have hnx : Algebra.norm (BaseResidue F) (residue w xO) = 1 := by
    rw [← hnorm, show a = 1 from Subtype.ext (ha.trans hx), map_one]
  let σ := P.residueAutEquiv P.τ
  obtain ⟨u, hu₀, hu⟩ :=
    (D07.Ch20.Hilbert90Multiplicative.hilbert90 (BaseResidue F) (ResidueRing w)
      σ (residue_generator r P) (residue w xO) hxne).mp hnx
  obtain ⟨aL, haL⟩ := reduceL_surjective r P u
  let bL := integralTranslate r P P.τ P.τ_preserves_value aL
  have hbL : reduceL r P bL = σ u := by
    change P.residueEquiv (IsLocalRing.residue _ bL) = _
    rw [P.residue_aut P.τ aL bL rfl]
    exact congrArg σ haL
  have haV := value_embed_of_residue_ne r P aL (haL ▸ hu₀)
  have hbV := value_embed_of_residue_ne r P bL (hbL ▸ (map_ne_zero σ).mpr hu₀)
  let aB := Units.mk0 (P.embed (aL : P.L)) (value_one_ne_zero w haV)
  let bB := Units.mk0 (P.embed (bL : P.L)) (value_one_ne_zero w hbV)
  let c := ⁅aB, P.uniformizer⁆
  have hc : c ∈ commutator Bˣ := Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  let cO : w.integer := ⟨(c : B), (unit_value_of_norm_one hB hw (commutator_norm_one hB hc)).le⟩
  have hconj : P.uniformizer * aB = bB * P.uniformizer := Units.ext (P.conjugation (aL : P.L))
  have hcb : c * bB = aB := by
    have he : P.uniformizer * aB * P.uniformizer⁻¹ = bB := by rw [hconj, mul_inv_cancel_right]
    rw [← he]
    dsimp only [c]
    rw [commutatorElement_def]
    group
  have hcbO : cO * integralEmbed r P bL = integralEmbed r P aL :=
    Subtype.ext (congrArg Units.val hcb)
  have hh : residue w cO * σ u = u := by
    have h := congrArg (residue w) hcbO
    rwa [map_mul, reduceL_embed, reduceL_embed, hbL, haL] at h
  refine ⟨c, hc, (residue_eq_iff_sub_lt w xO cO).mp ?_⟩
  exact hu.trans ((eq_div_iff ((map_ne_zero σ).mpr hu₀)).mpr hh).symm

private theorem inverse_pow_preserves_value (k : ℕ) (a : P.L) :
    P.vL (((P.τ⁻¹) ^ k) a) = P.vL a := by
  have hi (x : P.L) : P.vL (P.τ⁻¹ x) = P.vL x := by
    simpa using (P.τ_preserves_value (P.τ⁻¹ x)).symm
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, hi, ih]

include hB in
private theorem tau_order : orderOf P.τ = degree F B := by
  letI : FiniteDimensional F P.L :=
    Module.finite_of_finrank_pos (by rw [P.degree]; exact degree_pos hB)
  letI := P.galois
  exact (orderOf_eq_card_of_zpowers_eq_top P.gen).trans
    ((IsGalois.card_aut_eq_finrank F P.L).trans P.degree)

include hw in
/-- First-order conjugation on a valuation layer. Away from a central layer the
residue multiplier is invertible. On a central layer additive Hilbert 90 applies. -/
private theorem conjugation_on_layer (k : ℕ) (hk : 0 < k) (y : w.integer)
    (hy : reducedNorm hB (1 + (P.uniformizer : B) ^ k * (y : B)) = 1) :
    ∃ (a : Bˣ) (b₀ b₁ : w.integer),
      (a : B) * (1 + (P.uniformizer : B) ^ k * (b₀ : B)) =
        (1 + (P.uniformizer : B) ^ k * (b₁ : B)) * (a : B) ∧
      residue w b₁ - residue w b₀ = residue w y := by
  classical
  letI := r.isField.toField
  letI := r.algebra
  letI := r.finite
  letI : IsGalois (BaseResidue F) (ResidueRing w) := inferInstance
  by_cases hd : degree F B ∣ k
  · obtain ⟨m, rfl⟩ := hd
    have hm : 0 < m := Nat.pos_of_ne_zero (fun he => by simp [he] at hk)
    have hp : (P.uniformizer : B) ^ degree F B = _ := P.power_uniformizer
    rw [pow_mul, hp, ← map_pow] at hy
    have ht := layer_trace_zero hB hw r P y hm hy
    let σ := P.residueAutEquiv P.τ
    have htn : Algebra.trace (BaseResidue F) (ResidueRing w) (-residue w y) = 0 := by
      rw [map_neg, ht, neg_zero]
    obtain ⟨u, hu⟩ := (D07.Ch20.Hilbert90Additive.additive_hilbert90
      (BaseResidue F) (ResidueRing w) σ (residue_generator r P) (-residue w y)).mp htn
    obtain ⟨b, hb⟩ := reduceL_surjective r P u
    let b' := integralTranslate r P P.τ P.τ_preserves_value b
    refine ⟨P.uniformizer, integralEmbed r P b, integralEmbed r P b', ?_, ?_⟩
    · change (P.uniformizer : B) * (1 + (P.uniformizer : B) ^ _ * P.embed (b : P.L)) =
        (1 + (P.uniformizer : B) ^ _ * P.embed (b' : P.L)) * (P.uniformizer : B)
      rw [mul_add, add_mul, mul_one, one_mul, ← mul_assoc, ← pow_succ', pow_succ,
        mul_assoc, P.conjugation, ← mul_assoc]
      rfl
    · rw [reduceL_embed, reduceL_embed, hb]
      change P.residueEquiv (IsLocalRing.residue _ b') - u = _
      rw [P.residue_aut P.τ b b' rfl]
      change σ (reduceL r P b) - u = _
      rw [hb]
      simpa only [neg_neg, neg_sub] using (congrArg Neg.neg hu).symm
  · let s : P.L ≃ₐ[F] P.L := (P.τ⁻¹) ^ k
    let σ := P.residueAutEquiv s
    have hs : s ≠ 1 := by
      intro hs
      apply hd
      rw [← tau_order hB r P, orderOf_dvd_iff_pow_eq_one]
      have he := congrArg Inv.inv hs
      simpa [s, inv_pow] using he
    have hσ : σ ≠ 1 := by
      intro h
      apply hs
      exact P.residueAutEquiv.injective (h.trans (map_one _).symm)
    obtain ⟨u, hu⟩ : ∃ u : ResidueRing w, σ u ≠ u := by
      by_contra! hh
      exact hσ (AlgEquiv.ext hh)
    have hu₀ : u ≠ 0 := fun h => hu (by simp [h])
    have hu' : σ u / u - 1 ≠ 0 := by
      rw [sub_ne_zero, ne_eq, div_eq_iff hu₀, one_mul]
      exact hu
    obtain ⟨a, ha⟩ := reduceL_surjective r P u
    obtain ⟨b, hb⟩ := reduceL_surjective r P (residue w y / (σ u / u - 1))
    let a' := integralTranslate r P s (inverse_pow_preserves_value r P k) a
    have ha' : reduceL r P a' = σ u := by
      change P.residueEquiv (IsLocalRing.residue _ a') = _
      rw [P.residue_aut s a a' rfl]
      exact congrArg σ ha
    have ha₀ : (a : P.L) ≠ 0 := by
      intro he
      have h : a = 0 := Subtype.ext he
      exact hu₀ (ha.symm.trans (by rw [h, map_zero]))
    let A := Units.mk0 (P.embed (a : P.L)) ((map_ne_zero P.embed).mpr ha₀)
    let d : P.vL.valuationSubring := ⟨(a : P.L)⁻¹, by
      have hv := value_embed_of_residue_ne r P a (ha ▸ hu₀)
      rw [P.restrict_val] at hv
      have hdeg : _root_.Specs.RM03.CSA.degree F B ≠ 0 := (degree_pos hB).ne'
      have hh := (pow_left_inj₀ (a := P.vL (a : P.L)) (b := 1) zero_le zero_le
        hdeg).mp (by rwa [one_pow])
      change P.vL (a : P.L)⁻¹ ≤ 1
      rw [P.vL.map_inv, hh, inv_one]⟩
    have had : a * d = 1 := Subtype.ext (mul_inv_cancel₀ ha₀)
    have hdr : reduceL r P d = u⁻¹ := by
      have he := congrArg (reduceL r P) had
      rw [map_mul, map_one, ha] at he
      exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at he)
    refine ⟨A, integralEmbed r P b, integralEmbed r P (a' * b * d), ?_, ?_⟩
    · change P.embed (a : P.L) * (1 + (P.uniformizer : B) ^ k * P.embed (b : P.L)) =
        (1 + (P.uniformizer : B) ^ k * P.embed ((a' : P.L) * (b : P.L) * (a : P.L)⁻¹)) *
          P.embed (a : P.L)
      rw [mul_add, add_mul, mul_one, one_mul, ← mul_assoc, integral_conj r P (a : P.L) k]
      simp only [map_mul, mul_assoc]
      change _ + (P.uniformizer : B) ^ k * (P.embed (a' : P.L) * P.embed (b : P.L)) = _
      rw [← map_mul P.embed (a : P.L)⁻¹, inv_mul_cancel₀ ha₀, map_one, mul_one]
    · rw [reduceL_embed, reduceL_embed, map_mul, map_mul, ha', hb, hdr]
      calc
        σ u * (residue w y / (σ u / u - 1)) * u⁻¹ -
            residue w y / (σ u / u - 1) =
            (residue w y / (σ u / u - 1)) * (σ u / u - 1) := by
          rw [div_eq_mul_inv (σ u)]
          ring
        _ = _ := div_mul_cancel₀ _ hu'

private theorem lt_power_of_strict {t v : ℤᵐ⁰} (ht : t = WithZero.exp (-1)) (k : ℕ)
    (h : v < t ^ k) : v ≤ t ^ (k + 1) := by
  have ht₀ : t ^ k ≠ 0 := pow_ne_zero _ (by simp [ht])
  have hh : v / t ^ k < 1 := by
    rw [div_lt_iff₀ (pos_of_ne_zero ht₀), one_mul]
    exact h
  have h' := lt_layer_of_lt_one hh
  rw [← ht, div_le_iff₀ (pos_of_ne_zero ht₀), ← pow_succ'] at h'
  exact h'

include hw in
private theorem improve_approximation (k : ℕ) (hk : 0 < k) (x : Bˣ)
    (hx : x ∈ normOne hB)
    (hclose : w ((x : B) - 1) ≤ (w (P.uniformizer : B)) ^ k) :
    ∃ c ∈ commutator Bˣ, w ((x : B) - (c : B)) ≤ (w (P.uniformizer : B)) ^ (k + 1) := by
  let π := (P.uniformizer : B)
  let t := (w π) ^ k
  have hπ₀ : π ^ k ≠ 0 := pow_ne_zero _ (Units.ne_zero P.uniformizer)
  have ht₀ : 0 < t := zero_lt_iff.mpr (pow_ne_zero _ (by simp [π, P.value_uniformizer]))
  have ht : t < 1 := pow_lt_one₀ zero_le (by simp [π, P.value_uniformizer]) hk.ne'
  let y : w.integer := ⟨(π ^ k)⁻¹ * ((x : B) - 1), by
    change w ((π ^ k)⁻¹ * ((x : B) - 1)) ≤ 1
    rw [map_mul, w.map_inv, map_pow, ← div_eq_inv_mul, div_le_iff₀ ht₀, one_mul]
    exact hclose⟩
  have he : (x : B) = 1 + π ^ k * (y : B) := by
    change (x : B) = 1 + π ^ k * ((π ^ k)⁻¹ * ((x : B) - 1))
    rw [← mul_assoc, mul_inv_cancel₀ hπ₀, one_mul, add_comm, sub_add_cancel]
  have hN : reducedNorm hB (1 + π ^ k * (y : B)) = 1 := he ▸ hx
  obtain ⟨a, b₀, b₁, hab, hb⟩ := conjugation_on_layer hB hw r P k hk y hN
  have hsmall (b : w.integer) : w (π ^ k * (b : B)) < 1 := by
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_right' b.2).trans_lt ht
  let z₀ := Units.mk0 (1 + π ^ k * (b₀ : B)) (val_add_unit_ne w (hsmall b₀))
  let z₁ := Units.mk0 (1 + π ^ k * (b₁ : B)) (val_add_unit_ne w (hsmall b₁))
  have hz : a * z₀ = z₁ * a := Units.ext hab
  let c := ⁅a, z₀⁆
  have hc : c ∈ commutator Bˣ := Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  have hcz : c * z₀ = z₁ := by
    dsimp only [c]
    rw [← conj_eq_commutatorElement_mul]
    change a * z₀ * a⁻¹ = z₁
    rw [hz, mul_inv_cancel_right]
  have hdiff : w ((y : B) + (b₀ : B) - (b₁ : B)) < 1 := by
    apply (residue_eq_iff_sub_lt w (y + b₀) b₁).mp
    rw [map_add, ← hb, sub_add_cancel]
  have hxz : w (((x * z₀ : Bˣ) : B) - (z₁ : B)) < t := by
    rw [Units.val_mul, he]
    change w ((1 + π ^ k * (y : B)) * (1 + π ^ k * (b₀ : B)) -
      (1 + π ^ k * (b₁ : B))) < t
    rw [show (1 + π ^ k * (y : B)) * (1 + π ^ k * (b₀ : B)) - (1 + π ^ k * (b₁ : B)) =
      π ^ k * ((y : B) + (b₀ : B) - (b₁ : B)) +
        (π ^ k * (y : B)) * (π ^ k * (b₀ : B)) by noncomm_ring]
    apply w.map_add_lt
    · rw [map_mul, map_pow]
      exact mul_lt_of_lt_one_right ht₀ hdiff
    · rw [map_mul, map_mul, map_pow]
      exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right' y.2) zero_le).trans_lt
        (mul_lt_of_lt_one_right ht₀ (hsmall b₀))
  refine ⟨c, hc, lt_power_of_strict P.value_uniformizer k ?_⟩
  have hz₀ : w (z₀ : B) = 1 := value_one_add w (hsmall b₀)
  rw [← hcz, Units.val_mul, Units.val_mul, ← sub_mul, map_mul, hz₀, mul_one] at hxz
  exact hxz

include hw r P in
private theorem approximate_at_depth (x : Bˣ) (hx : x ∈ normOne hB) (k : ℕ) (hk : 0 < k) :
    ∃ c ∈ commutator Bˣ, w ((x : B) - (c : B)) ≤ (w (P.uniformizer : B)) ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k = 0
    · obtain ⟨c, hc, hlt⟩ := residue_commutator hB hw r P x hx
      refine ⟨c, hc, ?_⟩
      rw [h, zero_add, pow_one, P.value_uniformizer]
      exact lt_layer_of_lt_one hlt
    · obtain ⟨c, hc, hclose⟩ := ih (Nat.pos_of_ne_zero h)
      let y := x * c⁻¹
      have hcV := unit_value_of_norm_one hB hw (commutator_norm_one hB hc)
      have hyV : w ((y : B) - 1) ≤ (w (P.uniformizer : B)) ^ k :=
        (valuation_of_diff_mul_unit w x c hcV).trans_le hclose
      have hy : y ∈ normOne hB := by
        have hc' := commutator_norm_one hB ((commutator Bˣ).inv_mem hc)
        change reducedNorm hB (c⁻¹ : Bˣ).val = 1 at hc'
        change reducedNorm hB (x : B) = 1 at hx
        change reducedNorm hB ((x : B) * (c⁻¹ : Bˣ).val) = 1
        rw [reducedNorm_mul, hx, hc', mul_one]
      obtain ⟨d, hd, hdc⟩ := improve_approximation hB hw r P k (Nat.pos_of_ne_zero h) y hy hyV
      refine ⟨d * c, (commutator Bˣ).mul_mem hd hc, ?_⟩
      have e : x = y * c := by simp [y]
      calc
        w ((x : B) - ((d * c : Bˣ) : B)) =
            w (((y * c : Bˣ) : B) - ((d * c : Bˣ) : B)) := congrArg (fun a : Bˣ =>
              w ((a : B) - ((d * c : Bˣ) : B))) e
        _ = w ((y : B) - (d : B)) := by
          simp only [Units.val_mul, ← sub_mul, map_mul, hcV, mul_one]
        _ ≤ _ := hdc

private theorem value_diff_inv (w : Valuation B ℤᵐ⁰) (x y : Bˣ)
    (hx : w (x : B) = 1) (hy : w (y : B) = 1) :
    w (((x⁻¹ : Bˣ) : B) - ((y⁻¹ : Bˣ) : B)) = w ((x : B) - (y : B)) := by
  change w (x.inv - y.inv) = _
  have hi (u : Bˣ) (hu : w (u : B) = 1) : w u.inv = 1 := by
    have h := congrArg w u.val_inv
    rwa [map_mul, hu, one_mul, map_one] at h
  rw [show x.inv - y.inv = x.inv * ((y : B) - (x : B)) * y.inv by
    rw [mul_sub, sub_mul, mul_assoc x.inv (y : B), y.val_inv, x.inv_val, mul_one, one_mul]]
  rw [map_mul, map_mul, hi x hx, hi y hy, one_mul, mul_one, ← neg_sub, w.map_neg]

open private rankOne from LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras

private theorem basis_tendsto_of_small_values
    (b c : Module.Basis (Fin (Module.finrank F B)) F B)
    (hc : ∀ x, x ∈ w.integer ↔ ∀ j, c.equivFun x j ∈ Integers F)
    (hw : IsDivisionValuation hB w) (t : F) (ht : baseValue F t = WithZero.exp (-1))
    (f : ℕ → B) (v : B) (hf : ∀ k, w (v - f k) ≤ (baseValue F t) ^ (degree F B * k)) :
    letI : TopologicalSpace B := coordinateTopology b
    Tendsto f atTop (𝓝 v) := by
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne := rankOne F
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  letI : TopologicalSpace B := coordinateTopology b
  have ht₀ : t ≠ 0 := by
    intro he
    rw [he] at ht
    have hz : baseValue F (0 : F) = 0 := by simp [baseValue]
    rw [hz] at ht
    exact WithZero.exp_ne_zero ht.symm
  have ht₁ : ‖t‖ < 1 := by
    apply Valued.toNormedField.norm_lt_one_iff.mpr
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
    have h : e (valuation F t) < e 1 := by
      change baseValue F t < e 1
      rw [map_one, ht]
      simp
    exact e.toOrderIso.lt_iff_lt.mp h
  let z (k : ℕ) := ((t ^ k)⁻¹ : F) • (v - f k)
  have hz (k : ℕ) : z k ∈ w.integer := by
    have ht' : 0 < (baseValue F t) ^ (_root_.Specs.RM03.CSA.degree F B * k) := by
      rw [ht]
      exact pow_pos (zero_lt_iff.mpr WithZero.exp_ne_zero) _
    change w (z k) ≤ 1
    rw [show z k = algebraMap F B ((t ^ k)⁻¹) * (v - f k) by exact Algebra.smul_def _ _,
      map_mul, hw.2, show baseValue F ((t ^ k)⁻¹) = ((baseValue F t) ^ k)⁻¹ by
        change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
          (valuation F ((t ^ k)⁻¹)) = _
        simp only [map_inv₀, map_pow]
        rfl, inv_pow, ← pow_mul, mul_comm k (_root_.Specs.RM03.CSA.degree F B), ← div_eq_inv_mul,
      div_le_iff₀ ht', one_mul]
    exact hf k
  have hscale (k : ℕ) : v - f k = (t ^ k) • z k := by
    rw [show z k = ((t ^ k)⁻¹ : F) • (v - f k) from rfl, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero _ ht₀), one_smul]
  have hsmall (j : Fin (Module.finrank F B)) :
      Tendsto (fun k => c.repr (v - f k) j) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun k : ℕ => ‖t‖ ^ k)
    · intro k
      have hk : ‖c.equivFun (z k) j‖ ≤ 1 :=
        Valued.toNormedField.norm_le_one_iff.mpr ((hc _).mp (hz k) j)
      rw [← Module.Basis.equivFun_apply, hscale k, map_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) hk
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht₁
  have hb (i : Fin (Module.finrank F B)) :
      Tendsto (fun k => b.repr (v - f k) i) atTop (𝓝 0) := by
    simp_rw [← b.sum_repr_mul_repr c (v - f _) i]
    have hs := tendsto_finsetSum Finset.univ (fun j _ =>
      (hsmall j).const_mul (b.repr (c j) i))
    simpa only [mul_zero, Finset.sum_const_zero] using hs
  rw [nhds_induced, tendsto_comap_iff]
  apply tendsto_pi_nhds.mpr
  intro i
  have hs := tendsto_const_nhds.sub (hb i) (a := b.repr v i)
  simpa only [Function.comp_apply, map_sub, Finsupp.sub_apply, sub_sub_cancel, sub_zero] using hs

universe u v

theorem nonarchimedeanDivision : NonarchimedeanDivision.{u,v} := by
  classical
  intro F _ _ _ _ B _ _ hB b
  letI : TopologicalSpace B := coordinateTopology b
  intro x hx
  obtain ⟨w, hw, _⟩ := valuation_exists hB
  obtain ⟨r⟩ := residue_field hB w hw
  obtain ⟨_, _, ⟨P⟩⟩ := cyclic_structure hB w hw r
  obtain ⟨c, hc⟩ := (integer_lattice hB w hw).2
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Bˣ,
      ∀ k, g k ∈ commutator Bˣ ∧
        w ((x : B) - (g k : B)) ≤ (w (P.uniformizer : B)) ^ (degree F B * (k + 1)) := by
    choose g hg using fun k : ℕ =>
      approximate_at_depth hB hw r P x hx (degree F B * (k + 1))
        (Nat.mul_pos (degree_pos hB) (Nat.succ_pos _))
    exact ⟨g, hg⟩
  have hclose k : w ((x : B) - (g k : B)) ≤ (baseValue F P.parameter) ^ (degree F B * k) := by
    rw [P.value_parameter]
    have hh := (hg k).2
    rw [P.value_uniformizer, Nat.mul_succ, pow_add] at hh
    exact hh.trans (mul_le_of_le_one_right' (pow_le_one₀ zero_le (by simp)))
  have hgo : Tendsto (fun k => ((g k : Bˣ) : B)) atTop (𝓝 (x : B)) :=
    basis_tendsto_of_small_values hB b c hc hw P.parameter P.value_parameter _ _ hclose
  have hV := unit_value_of_norm_one hB hw hx
  have hginv : Tendsto (fun k => (((g k)⁻¹ : Bˣ) : B)) atTop (𝓝 ((x⁻¹ : Bˣ) : B)) := by
    apply basis_tendsto_of_small_values hB b c hc hw P.parameter P.value_parameter
    intro k
    rw [value_diff_inv w x (g k) hV (unit_value_of_norm_one hB hw (commutator_norm_one hB (hg k).1))]
    exact hclose k
  apply mem_closure_of_tendsto (f := g) (b := atTop)
  · rw [Units.isInducing_embedProduct.nhds_eq_comap x, tendsto_comap_iff]
    exact hgo.prodMk_nhds (MulOpposite.opHomeomorph.continuous.continuousAt.tendsto.comp hginv)
  · exact Eventually.of_forall fun k => (hg k).1

end FinitePlace

section CoordinateUnits

variable {F A ι : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Ring A] [Algebra F A] [Fintype ι]

/-- In the finite-dimensional topology every scalar-valued linear coordinate is continuous. -/
private theorem continuous_linear_coordinate (b : Module.Basis ι F A) (f : A →ₗ[F] F) :
    letI := coordinateTopology b
    Continuous f := by
  letI := coordinateTopology b
  have h (x : A) : f x = ∑ i, b.repr x i * f (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [show (⇑f : A → F) = fun x => ∑ i, b.repr x i * f (b i) from funext h]
  have hcoord : Continuous (fun (x : A) (i : ι) => b.repr x i) := continuous_induced_dom
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp hcoord).mul continuous_const

private theorem linear_coordinate_continuous {V ι' : Type*} [AddCommGroup V]
    [Module F V] [Finite ι'] (b : Module.Basis ι F A) (c : Module.Basis ι' F V)
    (f : A →ₗ[F] V) :
    letI := coordinateTopology b
    letI := coordinateTopology c
    Continuous f := by
  letI := coordinateTopology b
  letI := coordinateTopology c
  exact continuous_induced_rng.mpr (continuous_pi fun i =>
    continuous_linear_coordinate b ((c.coord i).comp f))

private def regularMatrix [DecidableEq ι] (b : Module.Basis ι F A) : A →ₐ[F] Matrix ι ι F :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul F A)

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem regularMatrix_isUnit [DecidableEq ι] (b : Module.Basis ι F A) (a : A) :
    IsUnit (regularMatrix b a) ↔ IsUnit a := by
  exact (isUnit_map_iff (LinearMap.toMatrixAlgEquiv b) (Algebra.lmul F A a)).trans
    Algebra.lmul_isUnit_iff

private theorem regularMatrix_continuous [DecidableEq ι] (b : Module.Basis ι F A) :
    letI := coordinateTopology b
    Continuous (regularMatrix b) := by
  letI := coordinateTopology b
  apply continuous_matrix
  intro i j
  have h (a : A) : regularMatrix b a i j = b.repr (a * b j) i :=
    Algebra.toMatrix_lmul' b a i j
  simp_rw [h]
  exact continuous_linear_coordinate b ((b.coord i).comp (LinearMap.mulRight F (b j)))

private def regularEval (b : Module.Basis ι F A) (M : Matrix ι ι F) : A :=
  b.equivFun.symm (M *ᵥ b.equivFun 1)

private theorem regularEval_continuous (b : Module.Basis ι F A) :
    letI := coordinateTopology b
    Continuous (regularEval b) := by
  letI := coordinateTopology b
  apply continuous_induced_rng.mpr
  have he (M : Matrix ι ι F) :
      (fun i => b.repr (regularEval b M) i) = M *ᵥ b.equivFun 1 := by
    change b.equivFun (b.equivFun.symm _) = _
    exact b.equivFun.apply_symm_apply _
  change Continuous (fun M i => b.repr (regularEval b M) i)
  rw [show (fun M i => b.repr (regularEval b M) i) = _ from funext he]
  apply continuous_pi
  intro i
  refine continuous_finsetSum _ fun j _ => ?_
  have hi : Continuous (fun M : Matrix ι ι F => M i) := continuous_apply i
  have hj : Continuous (fun v : ι → F => v j) := continuous_apply j
  exact (hj.comp hi).mul continuous_const

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem regularEval_regular [DecidableEq ι] (b : Module.Basis ι F A) (x : A) :
    regularEval b (regularMatrix b x) = x := by
  apply b.equivFun.injective
  rw [regularEval, b.equivFun.apply_symm_apply]
  change (LinearMap.toMatrix b b (Algebra.lmul F A x)) *ᵥ (b.repr 1 : ι → F) = b.repr x
  rw [LinearMap.toMatrix_mulVec_repr]
  change (b.repr (x * 1) : ι → F) = b.repr x
  rw [mul_one]

private theorem continuousMul_coordinates (b : Module.Basis ι F A) :
    letI := coordinateTopology b
    ContinuousMul A := by
  classical
  letI := coordinateTopology b
  have he : Function.LeftInverse (regularEval b) (regularMatrix b) := regularEval_regular b
  exact (he.isEmbedding (regularEval_continuous b) (regularMatrix_continuous b)).isInducing
    |>.continuousMul (regularMatrix b)

variable [ContinuousInv₀ F] [T1Space F]

private theorem units_open_embedding (b : Module.Basis ι F A) :
    letI := coordinateTopology b
    IsOpenEmbedding (Units.val : Aˣ → A) := by
  classical
  letI := coordinateTopology b
  let m := regularMatrix b
  have hm : Continuous m := regularMatrix_continuous b
  refine ⟨Units.isEmbedding_val_mk' (f := fun a => regularEval b ((m a)⁻¹)) ?_ ?_, ?_⟩
  · apply (regularEval_continuous b).comp_continuousOn
    intro a ha
    have hd : (m a).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _ |>.mp ((regularMatrix_isUnit b a).mpr ha)).ne_zero
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_matrix_inv (m a) ?_).comp hm.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  · intro a
    have hh : (m (a : A))⁻¹ = m ((a⁻¹ : Aˣ) : A) := by
      let M := Units.map m.toMonoidHom a
      exact (Matrix.nonsing_inv_eq_ringInverse _).trans (Ring.inverse_unit M)
    rw [hh]
    exact regularEval_regular b _
  · have he : Set.range (Units.val : Aˣ → A) = {a | (m a).det ≠ 0} := by
      ext a
      rw [Set.mem_ofPred_eq, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
        regularMatrix_isUnit]
      rfl
    rw [he]
    exact isClosed_singleton.isOpen_compl.preimage hm.matrix_det

end CoordinateUnits

section MatrixWords

open Matrix

variable {B ι : Type*} [Ring B] [Fintype ι] [DecidableEq ι]

/-- The diagonal matrix of a tuple of units. -/
def diagonalUnits : (ι → Bˣ) →* (Matrix ι ι B)ˣ where
  toFun d :=
    { val := diagonal fun i => (d i : B)
      inv := diagonal fun i => ((d i)⁻¹ : Bˣ)
      val_inv := by simp [diagonal_mul_diagonal, ← Units.val_mul, diagonal_one]
      inv_val := by simp [diagonal_mul_diagonal, ← Units.val_mul, diagonal_one] }
  map_one' := Units.ext (by simp [diagonal_one])
  map_mul' _ _ := Units.ext (by simp [diagonal_mul_diagonal])

@[simp] theorem val_diagonalUnits (d : ι → Bˣ) :
    (diagonalUnits d : Matrix ι ι B) = diagonal (fun i => (d i : B)) := rfl

/-- Put a unit in one diagonal position and put identities elsewhere. -/
def diagonalSlot (i : ι) : Bˣ →* (Matrix ι ι B)ˣ := diagonalUnits.comp
  { toFun a := Function.update 1 i a
    map_one' := Function.update_eq_self i (1 : ι → Bˣ)
    map_mul' a b := by
      ext k
      by_cases hk : k = i <;> simp [hk] }

@[simp] theorem val_diagonalSlot (i : ι) (a : Bˣ) :
    (diagonalSlot i a : Matrix ι ι B) =
      diagonal (fun k => if k = i then (a : B) else 1) := by
  change diagonal (fun k => (Function.update (1 : ι → Bˣ) i a k : B)) = _
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

theorem elementary_mem_elementaryGroup (i j : ι) (hij : i ≠ j) (a : B) :
    elementary i j hij a ∈ elementaryGroup ι :=
  Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩

@[simp] theorem val_elementary (i j : ι) (hij : i ≠ j) (a : B) :
    (elementary i j hij a : Matrix ι ι B) = 1 + single i j a := rfl

theorem elementary_mul (i j : ι) (hij : i ≠ j) (a b : B) :
    elementary i j hij a * elementary i j hij b = elementary i j hij (a + b) := by
  apply Units.ext
  simp [add_mul, mul_add, single_mul_single_of_ne _ _ _ _ hij.symm, ← single_add, add_assoc]

private def signedInterchange (i j : ι) (hij : i ≠ j) (a : Bˣ) : (Matrix ι ι B)ˣ :=
  elementary i j hij (a : B) * elementary j i hij.symm (-((a⁻¹ : Bˣ) : B)) *
    elementary i j hij (a : B)

private theorem val_signedInterchange (i j : ι) (hij : i ≠ j) (a : Bˣ) :
    (signedInterchange i j hij a : Matrix ι ι B) =
      1 + single i i (-1) + single j j (-1) +
        single i j (a : B) + single j i (-((a⁻¹ : Bˣ) : B)) := by
  have ha : (a : B) * (-((a⁻¹ : Bˣ) : B)) = -1 := by simp [← Units.val_mul]
  have hb : (-((a⁻¹ : Bˣ) : B)) * (a : B) = -1 := by simp [← Units.val_mul]
  simp only [signedInterchange, Units.val_mul, val_elementary, add_mul, mul_add, one_mul,
    mul_one, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    ha, hb, neg_one_mul, add_zero]
  simp only [← single_neg]
  abel

private theorem signedInterchange_mem (i j : ι) (hij : i ≠ j) (a : Bˣ) :
    signedInterchange i j hij a ∈ elementaryGroup ι :=
  (elementaryGroup ι).mul_mem
    ((elementaryGroup ι).mul_mem (elementary_mem_elementaryGroup _ _ _ _)
      (elementary_mem_elementaryGroup _ _ _ _))
    (elementary_mem_elementaryGroup _ _ _ _)

/-- The two-coordinate diagonal step given by the word of elementary operations. -/
theorem diagonal_pair_mem (i j : ι) (hij : i ≠ j) (a : Bˣ) :
    diagonalSlot i a * diagonalSlot j a⁻¹ ∈ elementaryGroup ι := by
  have he : (diagonalSlot i a * diagonalSlot j a⁻¹) * signedInterchange i j hij 1 =
      signedInterchange i j hij a := by
    apply Units.ext
    simp only [Units.val_mul, val_diagonalSlot, val_signedInterchange, diagonal_mul_diagonal]
    ext k l
    simp only [diagonal_mul, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Units.val_one,
      inv_one]
    by_cases hki : i = k <;> by_cases hkj : j = k <;>
      by_cases hli : i = l <;> by_cases hlj : j = l <;> by_cases hkl : k = l <;>
      simp_all [Ne.symm]
  rw [← eq_mul_inv_iff_mul_eq] at he
  rw [he]
  exact (elementaryGroup ι).mul_mem (signedInterchange_mem _ _ _ _)
    ((elementaryGroup ι).inv_mem (signedInterchange_mem _ _ _ _))

/-- One-slot commutators lift to elementary words using a second position. -/
theorem diagonalSlot_commutator_mem (i j : ι) (hij : i ≠ j) (a b : Bˣ) :
    diagonalSlot j ⁅a, b⁆ ∈ elementaryGroup ι := by
  let D (c : Bˣ) := diagonalSlot i c * diagonalSlot j c⁻¹
  have hd (c : Bˣ) : D c ∈ elementaryGroup ι := diagonal_pair_mem i j hij c
  have he : D a⁻¹ * D b⁻¹ * (D (a⁻¹ * b⁻¹))⁻¹ = diagonalSlot j ⁅a, b⁆ := by
    simp only [D, diagonalSlot, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      ← map_mul, ← map_inv]
    apply congrArg (diagonalUnits (ι := ι) (B := B))
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [commutatorElement_def, mul_assoc]
  rw [← he]
  exact (elementaryGroup ι).mul_mem ((elementaryGroup ι).mul_mem (hd _) (hd _))
    ((elementaryGroup ι).inv_mem (hd _))

private theorem elementary_commutator_of_unit (i j : ι) (hij : i ≠ j)
    (c : Bˣ) (a b : B) (hab : (c : B) * b = a + b) :
    ⁅diagonalSlot i c, elementary i j hij b⁆ = elementary i j hij a := by
  apply commutator_of_mul_eq
  rw [← mul_assoc, elementary_mul]
  apply Units.ext
  simp only [Units.val_mul, val_diagonalSlot, val_elementary, add_mul, mul_add, one_mul, mul_one]
  congr 1
  ext k l
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases hk : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := hk
    simp [hij.symm, hab]
  · simp [hk]

theorem elementaryGroup_le_commutator {F : Type*} [Field F] [Infinite F] [Algebra F B]
    [Nontrivial B] :
    elementaryGroup (B := B) ι ≤ commutator (Matrix ι ι B)ˣ := by
  classical
  apply (Subgroup.closure_le _).2
  rintro _ ⟨i, j, hij, a, rfl⟩
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset F)
  have hc₀ : c ≠ 0 := fun h => hc (by simp [h])
  have hc₁ : c - 1 ≠ 0 := sub_ne_zero.mpr fun h => hc (by simp [h])
  let d := Units.map (algebraMap F B).toMonoidHom (Units.mk0 c hc₀)
  let b := algebraMap F B (c - 1)⁻¹ * a
  have hcb : (d : B) * b = a + b := by
    apply sub_eq_iff_eq_add.mp
    change algebraMap F B c * b - b = a
    calc
      algebraMap F B c * b - b = algebraMap F B (c - 1) * b := by simp [sub_mul]
      _ = a := by
        dsimp only [b]
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc₁, map_one, one_mul]
  rw [← elementary_commutator_of_unit i j hij d a b hcb]
  exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)

end MatrixWords

section Elimination

open Matrix

variable {B : Type*} [DivisionRing B]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem exists_elementary_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (r c : α → ι) (a : α → B)
    (h : ∀ i ∈ s, ∀ j ∈ s, c i ≠ r j) :
    ∃ L ∈ elementaryGroup (B := B) ι, (L : Matrix ι ι B) = 1 + ∑ i ∈ s, single (r i) (c i) (a i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, (elementaryGroup ι).one_mem, by simp⟩
  | @insert i s hi ih =>
    have hij : r i ≠ c i := (h i (Finset.mem_insert_self _ _) i (Finset.mem_insert_self _ _)).symm
    obtain ⟨L, hL, hval⟩ := ih (fun j hj k hk => h j (Finset.mem_insert_of_mem hj) k
      (Finset.mem_insert_of_mem hk))
    have hz : single (r i) (c i) (a i) * (∑ j ∈ s, single (r j) (c j) (a j)) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact single_mul_single_of_ne _ _ _ _ (h i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj)) _
    refine ⟨elementary (r i) (c i) hij (a i) * L,
      (elementaryGroup ι).mul_mem (elementary_mem_elementaryGroup _ _ _ _) hL, ?_⟩
    simp [hval, Finset.sum_insert hi, add_mul, mul_add, hz, add_assoc, add_left_comm]

private theorem clear_pivot (M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B)
    (h : M (.inr ()) (.inr ()) ≠ 0) :
    ∃ L ∈ elementaryGroup (B := B) (ι ⊕ Unit), ∃ R ∈ elementaryGroup (B := B) (ι ⊕ Unit),
      IsTwoBlockDiagonal ((L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B) * M *
        (R : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B)) := by
  let o : ι ⊕ Unit := .inr ()
  let a := M o o
  let f (i : ι) := -(M (.inl i) o * a⁻¹)
  let g (i : ι) := -(a⁻¹ * M o (.inl i))
  obtain ⟨L, hL, heL⟩ := exists_elementary_sum Finset.univ Sum.inl (fun _ => o) f
    (by intro i _ j _; exact Sum.inr_ne_inl)
  obtain ⟨R, hR, heR⟩ := exists_elementary_sum Finset.univ (fun _ => o) Sum.inl g
    (by intro i _ j _; exact Sum.inl_ne_inr)
  refine ⟨L, hL, R, hR, ?_⟩
  let N := (L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B) * M
  have hn (k) : N o k = M o k := by
    change ((L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B) * M) o k = _
    rw [heL, add_mul, one_mul, Finset.sum_mul, Matrix.add_apply, Matrix.sum_apply]
    simp [o, Finset.sum_eq_zero]
  have hcol (i : ι) : N (.inl i) o = 0 := by
    change ((L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B) * M) (.inl i) o = _
    rw [heL, add_mul, one_mul, Finset.sum_mul, Matrix.add_apply, Matrix.sum_apply,
      Finset.sum_eq_single i]
    · simp [f, a, o, h]
    · intro j _ hj
      exact single_mul_apply_of_ne _ _ _ _ _ (fun e => hj (Sum.inl.inj e).symm) _
    · simp
  constructor
  · ext i j
    cases j
    change (N * (R : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B)) (.inl i) o = 0
    rw [heR, mul_add, mul_one, Finset.mul_sum, Matrix.add_apply, Matrix.sum_apply, hcol]
    simp [o, Finset.sum_eq_zero]
  · ext i j
    cases i
    change (N * (R : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B)) o (.inl j) = 0
    rw [heR, mul_add, mul_one, Finset.mul_sum, Matrix.add_apply, Matrix.sum_apply,
      Finset.sum_eq_single j]
    · simp [g, hn, a, o, h]
    · intro i _ hi
      exact mul_single_apply_of_ne _ _ _ _ _ (fun e => hi (Sum.inl.inj e).symm) _
    · simp

private theorem make_block_diagonal (M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B) :
    ∃ L ∈ elementaryGroup (B := B) (ι ⊕ Unit), ∃ R ∈ elementaryGroup (B := B) (ι ⊕ Unit),
      IsTwoBlockDiagonal ((L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B) * M *
        (R : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B)) := by
  by_cases hm : M.IsTwoBlockDiagonal
  · exact ⟨1, (elementaryGroup _).one_mem, 1, (elementaryGroup _).one_mem, by simpa⟩
  by_cases hp : M (.inr ()) (.inr ()) = 0
  swap
  · exact clear_pivot M hp
  have h : ∃ i : ι, M (.inl i) (.inr ()) ≠ 0 ∨ M (.inr ()) (.inl i) ≠ 0 := by
    by_contra! hz
    apply hm
    exact ⟨by ext i j; cases j; exact (hz i).1, by ext i j; cases i; exact (hz j).2⟩
  obtain ⟨i, hi | hi⟩ := h
  · let e := elementary (.inr () : ι ⊕ Unit) (.inl i) Sum.inr_ne_inl (1 : B)
    have ha : ((e : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B) * M) (.inr ()) (.inr ()) ≠ 0 := by
      simpa [e, add_mul, Matrix.add_apply, hp] using hi
    obtain ⟨L, hL, R, hR, he⟩ := clear_pivot _ ha
    exact ⟨L * e, (elementaryGroup _).mul_mem hL (elementary_mem_elementaryGroup _ _ _ _),
      R, hR, by simpa [mul_assoc] using he⟩
  · let e := elementary (.inl i : ι ⊕ Unit) (.inr ()) Sum.inl_ne_inr (1 : B)
    have ha : (M * (e : Matrix (ι ⊕ Unit) (ι ⊕ Unit) B)) (.inr ()) (.inr ()) ≠ 0 := by
      simpa [e, mul_add, Matrix.add_apply, hp] using hi
    obtain ⟨L, hL, R, hR, he⟩ := clear_pivot _ ha
    exact ⟨L, hL, e * R, (elementaryGroup _).mul_mem (elementary_mem_elementaryGroup _ _ _ _) hR,
      by simpa [mul_assoc] using he⟩

private theorem map_elementaryGroup_le
    (f : (Matrix ι ι B)ˣ →* (Matrix κ κ B)ˣ)
    (hf : ∀ (i j : ι) (hij : i ≠ j) (a : B), f (elementary i j hij a) ∈ elementaryGroup κ) :
    (elementaryGroup ι).map f ≤ elementaryGroup κ := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).2
  rintro _ ⟨i, j, hij, a, rfl⟩
  exact hf i j hij a

private def extendMatrix : Matrix ι ι B →* Matrix (ι ⊕ Unit) (ι ⊕ Unit) B where
  toFun M := fromBlocks M 0 0 1
  map_one' := fromBlocks_one
  map_mul' _ _ := by simp [fromBlocks_multiply]

private theorem extend_mem_elementaryGroup (L : (Matrix ι ι B)ˣ) (hL : L ∈ elementaryGroup ι) :
    Units.map (extendMatrix (ι := ι) (B := B)) L ∈ elementaryGroup (B := B) (ι ⊕ Unit) := by
  refine map_elementaryGroup_le (Units.map extendMatrix) ?_ (Subgroup.mem_map_of_mem _ hL)
  intro i j hij a
  have he : Units.map extendMatrix (elementary i j hij a) =
      elementary (.inl i : ι ⊕ Unit) (.inl j) (Sum.inl_injective.ne hij) a := by
    apply Units.ext
    change fromBlocks (1 + single i j a) 0 0 1 = 1 + single (.inl i) (.inl j) a
    ext (k | k) (l | l) <;> simp [Matrix.single_apply, Matrix.one_apply]
  rw [he]
  exact elementary_mem_elementaryGroup _ _ _ _

private theorem reindex_mem_elementaryGroup (e : ι ≃ κ)
    (L : (Matrix ι ι B)ˣ) (hL : L ∈ elementaryGroup ι) :
    Units.map (Matrix.reindexAlgEquiv ℤ B e).toMonoidHom L ∈ elementaryGroup κ := by
  refine map_elementaryGroup_le (Units.map (Matrix.reindexAlgEquiv ℤ B e).toMonoidHom) ?_
    (Subgroup.mem_map_of_mem _ hL)
  intro i j hij a
  have he : Units.map (Matrix.reindexAlgEquiv ℤ B e).toMonoidHom (elementary i j hij a) =
      elementary (e i) (e j) (e.injective.ne hij) a := by
    apply Units.ext
    change Matrix.reindexAlgEquiv ℤ B e (1 + single i j a) = 1 + single (e i) (e j) a
    rw [map_add, map_one]
    congr 1
    ext k l
    simp [Matrix.reindexAlgEquiv, Matrix.single_apply, e.eq_symm_apply]
  rw [he]
  exact elementary_mem_elementaryGroup _ _ _ _

/-- Two products of elementary matrices bring any square matrix over a division ring
to diagonal form. -/
theorem elementary_diagonalize (n : ℕ) (M : Matrix (Fin n) (Fin n) B) :
    ∃ L ∈ elementaryGroup (B := B) (Fin n), ∃ R ∈ elementaryGroup (B := B) (Fin n), ∃ d : Fin n → B,
      (L : Matrix (Fin n) (Fin n) B) * M * (R : Matrix (Fin n) (Fin n) B) = diagonal d := by
  induction n with
  | zero =>
    refine ⟨1, (elementaryGroup _).one_mem, 1, (elementaryGroup _).one_mem, 1, ?_⟩
    ext i
    exact Fin.elim0 i
  | succ n ih =>
    let e : Fin (n + 1) ≃ Fin n ⊕ Unit := Fintype.equivOfCardEq (by simp)
    let f := Matrix.reindexAlgEquiv ℤ B e
    obtain ⟨L, hL, R, hR, hblock⟩ := make_block_diagonal (f M)
    let N := (L : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) B) * f M *
      (R : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) B)
    let c (i : Unit) := N (.inr i) (.inr i)
    have hN : N = fromBlocks (toBlocks₁₁ N) 0 0 (diagonal c) := by
      rw [← fromBlocks_toBlocks N, hblock.1, hblock.2]
      congr 1
    obtain ⟨l, hl, r, hr, d, hd⟩ := ih (toBlocks₁₁ N)
    let L' := Units.map extendMatrix l * L
    let R' := R * Units.map extendMatrix r
    have hL' : L' ∈ elementaryGroup (Fin n ⊕ Unit) :=
      (elementaryGroup _).mul_mem (extend_mem_elementaryGroup l hl) hL
    have hR' : R' ∈ elementaryGroup (Fin n ⊕ Unit) :=
      (elementaryGroup _).mul_mem hR (extend_mem_elementaryGroup r hr)
    have h' :
        (L' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) B) * f M *
            (R' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) B) = diagonal (Sum.elim d c) := by
      calc
        _ = fromBlocks (l : Matrix (Fin n) (Fin n) B) 0 0 1 * N *
            fromBlocks (r : Matrix (Fin n) (Fin n) B) 0 0 1 := by
          change (fromBlocks (l : Matrix (Fin n) (Fin n) B) 0 0 1 * (L : Matrix _ _ B)) *
              f M * ((R : Matrix _ _ B) * fromBlocks (r : Matrix (Fin n) (Fin n) B) 0 0 1) = _
          simp [N, mul_assoc]
        _ = _ := by
          rw [hN]
          simp [fromBlocks_multiply, hd, fromBlocks_diagonal]
    let L₀ := Units.map f.symm.toMonoidHom L'
    let R₀ := Units.map f.symm.toMonoidHom R'
    refine ⟨L₀, reindex_mem_elementaryGroup e.symm L' hL',
      R₀, reindex_mem_elementaryGroup e.symm R' hR', (Sum.elim d c) ∘ e, ?_⟩
    have he := congrArg f.symm h'
    rw [map_mul, map_mul, AlgEquiv.symm_apply_apply] at he
    change (L₀ : Matrix _ _ B) * M * (R₀ : Matrix _ _ B) = _ at he ⊢
    rw [he]
    ext i j
    simp [f, Matrix.reindexAlgEquiv, Matrix.diagonal_apply]

end Elimination

section MatrixNorm

variable {F L B ι : Type*} [Field F] [Field L] [Algebra F L]
  [Ring B] [Algebra F B] [Fintype ι] [DecidableEq ι]

private def matrixBaseChangeLinear :
    (L ⊗[F] Matrix ι ι B) ≃ₗ[L] Matrix ι ι (L ⊗[F] B) :=
  (TensorProduct.piRight F L L (fun _ : ι => ι → B)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight F L L (fun _ : ι => B))

private theorem matrixBaseChangeLinear_tmul (a : L) (x : Matrix ι ι B) (i j : ι) :
    matrixBaseChangeLinear (a ⊗ₜ[F] x) i j = a ⊗ₜ[F] x i j :=
  rfl

private def matrixBaseChange : (L ⊗[F] Matrix ι ι B) ≃ₐ[L] Matrix ι ι (L ⊗[F] B) :=
  AlgEquiv.ofLinearEquiv matrixBaseChangeLinear (by
    ext i j
    change matrixBaseChangeLinear ((1 : L) ⊗ₜ[F] (1 : Matrix ι ι B)) i j = _
    rw [matrixBaseChangeLinear_tmul]
    by_cases h : i = j <;> simp [Matrix.one_apply, h, ← Algebra.TensorProduct.one_def]
  ) (by
    intro x y
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp [mul_add, hy₁, hy₂]
      | tmul b y =>
        ext i j
        simp only [Algebra.TensorProduct.tmul_mul_tmul, matrixBaseChangeLinear_tmul,
          Matrix.mul_apply, TensorProduct.tmul_sum]
  )

private theorem matrixBaseChange_tmul (a : L) (x : Matrix ι ι B) (i j : ι) :
    matrixBaseChange (a ⊗ₜ[F] x) i j = a ⊗ₜ[F] x i j :=
  rfl

end MatrixNorm

section DiagonalNorm

variable {F B : Type*} [Field F] [DivisionRing B] [Algebra F B]

/-- The reduced norm of a diagonal unit supported in one position is its coefficient's
reduced norm over the division algebra. -/
theorem reducedNorm_diagonalSlot (hB : IsCentralSimple F B) {m : ℕ} (hm : 0 < m)
    (hA : IsCentralSimple F (Matrix (Fin m) (Fin m) B)) (i : Fin m) (a : Bˣ) :
    reducedNorm hA (diagonalSlot i a : Matrix (Fin m) (Fin m) B) = reducedNorm hB (a : B) := by
  let L := AlgebraicClosure F
  let n := degree F B
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
  let e₁ := (matrixBaseChange (F := F) (L := L) (B := B) (ι := Fin m)).trans
    ((e.mapMatrix.trans (Matrix.compAlgEquiv (Fin m) (Fin n) L L)).trans
      (Matrix.reindexAlgEquiv L L (Equiv.prodComm (Fin m) (Fin n))))
  have hdeg := degree_matrix_division hA (show IsCentralDivision F B from hB.2) hm (AlgEquiv.refl)
  let r : Fin n × Fin m ≃ Fin (degree F (Matrix (Fin m) (Fin m) B)) :=
    Fintype.equivOfCardEq (by simp [hdeg, n, Nat.mul_comm])
  let e₂ := e₁.trans (Matrix.reindexAlgEquiv L L r)
  apply (algebraMap F L).injective
  rw [reducedNorm_map hA _ e₂, reducedNorm_map hB _ e]
  change Matrix.det (Matrix.reindex r r (e₁ (1 ⊗ₜ[F] (diagonalSlot i a : Matrix _ _ B)))) = _
  rw [Matrix.det_reindex_self]
  let D (j : Fin m) : Matrix (Fin n) (Fin n) L := if j = i then e (1 ⊗ₜ[F] (a : B)) else 1
  have hD : e₁ (1 ⊗ₜ[F] (diagonalSlot i a : Matrix _ _ B)) = Matrix.blockDiagonal D := by
    ext ⟨j, k⟩ ⟨j', k'⟩
    change (e (matrixBaseChange ((1 : L) ⊗ₜ[F] (diagonalSlot i a : Matrix _ _ B)) k k')) j j' =
      (Matrix.blockDiagonal D) (j, k) (j', k')
    rw [matrixBaseChange_tmul, val_diagonalSlot, Matrix.blockDiagonal_apply]
    by_cases h : k = k'
    · subst k'
      by_cases hk : k = i
      · simp [D, hk]
      · have h1 : e ((1 : L) ⊗ₜ[F] (1 : B)) = 1 := by
          rw [← Algebra.TensorProduct.one_def, map_one]
        simp [D, hk, h1]
    · simp [h]
  rw [hD, Matrix.det_blockDiagonal]
  simp only [D, apply_ite Matrix.det, Matrix.det_one]
  simp

end DiagonalNorm

section DiagonalReduction

variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [Ring B]

private theorem consolidate_diagonal (j : ι) (d : ι → Bˣ) :
    ∃ L ∈ elementaryGroup (B := B) ι, ∃ a : Bˣ, L * diagonalUnits d = diagonalSlot j a := by
  classical
  suffices ∀ s : Finset ι, ∀ d : ι → Bˣ, (∀ i, i ≠ j → i ∉ s → d i = 1) →
      ∃ L ∈ elementaryGroup (B := B) ι, ∃ a : Bˣ, L * diagonalUnits d = diagonalSlot j a by
    apply this (Finset.univ.erase j) d
    intro k hkj hk
    exact (hk (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩)).elim
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro d hd
    refine ⟨1, (elementaryGroup ι).one_mem, d j, ?_⟩
    simp only [one_mul, diagonalSlot, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    apply congrArg diagonalUnits
    funext k
    by_cases hk : k = j <;> simp [hk, hd]
  | @insert i s hi ih =>
    intro d hd
    by_cases hij : i = j
    · subst i
      exact ih d (fun k hk hks => hd k hk (by simp [hk, hks]))
    · let d' := Function.update (Function.update d i 1) j (d i * d j)
      have hs' (k : ι) (hk : k ≠ j) (hks : k ∉ s) : d' k = 1 := by
        by_cases hki : k = i
        · simp [d', hki, hij]
        · simp [d', hk, hki, hd k hk (by simp [hki, hks])]
      obtain ⟨L, hL, a, he⟩ := ih d' hs'
      let P := diagonalSlot i (d i)⁻¹ * diagonalSlot j (d i)
      have hP : P ∈ elementaryGroup ι := by
        simpa [P] using diagonal_pair_mem i j hij (d i)⁻¹
      have hstep : P * diagonalUnits d = diagonalUnits d' := by
        simp only [P, diagonalSlot, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
          ← map_mul]
        apply congrArg diagonalUnits
        funext k
        by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [d']
      exact ⟨L * P, (elementaryGroup ι).mul_mem hL hP, a, by rwa [mul_assoc, hstep]⟩

/-- Reducing an invertible matrix to a single nonidentity diagonal entry
using elementary matrices on the left and right. -/
theorem elementary_single_diagonal {B : Type*} [DivisionRing B]
    {m : ℕ} (j : Fin m) (x : (Matrix (Fin m) (Fin m) B)ˣ) :
    ∃ L ∈ elementaryGroup (B := B) (Fin m), ∃ R ∈ elementaryGroup (B := B) (Fin m), ∃ a : Bˣ,
      L * x * R = diagonalSlot j a := by
  obtain ⟨L, hL, R, hR, d, hd⟩ := elementary_diagonalize m (x : Matrix _ _ B)
  let y := L * x * R
  have hy : (y : Matrix _ _ B) = Matrix.diagonal d := hd
  have hn (i : Fin m) : d i ≠ 0 := by
    have he := congrArg (fun M : Matrix (Fin m) (Fin m) B => M i i) y.val_inv
    let Y : Matrix (Fin m) (Fin m) B := (y⁻¹ : (Matrix (Fin m) (Fin m) B)ˣ)
    change ((y : Matrix (Fin m) (Fin m) B) * Y) i i = (1 : Matrix (Fin m) (Fin m) B) i i at he
    rw [hy, Matrix.diagonal_mul] at he
    intro h
    simp [h] at he
  let u (i : Fin m) := Units.mk0 (d i) (hn i)
  have hu : y = diagonalUnits u := Units.ext hy
  obtain ⟨P, hP, a, ha⟩ := consolidate_diagonal j u
  refine ⟨P * L, (elementaryGroup _).mul_mem hP hL, R, hR, a, ?_⟩
  rw [← hu] at ha
  simpa [y, mul_assoc] using ha

end DiagonalReduction

section MatrixTransfer

variable {F B : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Ring B] [Algebra F B]

private theorem continuous_diagonalSlot {ι κ η : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Fintype η] (b : Module.Basis κ F B)
    (c : Module.Basis η F (Matrix ι ι B)) (i : ι) :
    letI := coordinateTopology b
    letI := coordinateTopology c
    Continuous (diagonalSlot i : Bˣ → (Matrix ι ι B)ˣ) := by
  letI := coordinateTopology b
  letI := coordinateTopology c
  let f (a : B) : Matrix ι ι B := Matrix.diagonal (fun k => if k = i then a else 1)
  have hf : Continuous f := by
    let g : B →ₗ[F] Matrix ι ι B := Matrix.singleLinearMap F i i
    have he (a : B) : f a = (1 - Matrix.single i i 1) + g a := by
      ext k l
      change f a k l = (((1 - Matrix.single i i 1) + Matrix.single i i a) : Matrix ι ι B) k l
      by_cases hk : k = i <;> by_cases hl : l = i <;>
        simp_all [f, Matrix.diagonal_apply, Matrix.one_apply, Ne.symm]
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro j
    change Continuous (fun a => c.repr (f a) j)
    simp_rw [he, map_add, Finsupp.add_apply]
    exact continuous_const.add (continuous_linear_coordinate b ((c.coord j).comp g))
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous (fun a : Bˣ => (diagonalSlot i a : Matrix ι ι B))
    simp only [val_diagonalSlot]
    exact hf.comp Units.continuous_val
  · change Continuous (fun a : Bˣ => (((diagonalSlot i a)⁻¹ : (Matrix ι ι B)ˣ) : Matrix ι ι B))
    simp only [← map_inv, val_diagonalSlot]
    exact hf.comp Units.continuous_coe_inv

end MatrixTransfer

section MatrixDensity

variable {F B : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [Infinite F]
  [DivisionRing B] [Algebra F B] {m : ℕ}

private theorem matrix_normOne_subset_closure (hB : IsCentralSimple F B)
    (hdense : denseCommutators hB) (hA : IsCentralSimple F (Matrix (Fin m) (Fin m) B))
    (i : Fin m) (C : Subgroup (Matrix (Fin m) (Fin m) B)ˣ)
    (he : elementaryGroup (Fin m) ≤ C)
    (hc : (commutator Bˣ).map (diagonalSlot i) ≤ C)
    (b : Module.Basis (Fin (Module.finrank F (Matrix (Fin m) (Fin m) B)))
      F (Matrix (Fin m) (Fin m) B)) :
    letI := coordinateTopology b
    normOne hA ⊆ closure (C : Set (Matrix (Fin m) (Fin m) B)ˣ) := by
  letI := coordinateTopology b
  letI : ContinuousMul (Matrix (Fin m) (Fin m) B) := continuousMul_coordinates b
  letI := hB.2.2
  let c := Module.finBasis F B
  letI := coordinateTopology c
  intro x hx
  obtain ⟨L, hL, R, hR, a, ha⟩ := elementary_single_diagonal i x
  have hnorm : a ∈ normOne hB := by
    have hL₁ := commutator_norm_one hA (elementaryGroup_le_commutator (F := F) hL)
    have hR₁ := commutator_norm_one hA (elementaryGroup_le_commutator (F := F) hR)
    change reducedNorm hA (L : Matrix _ _ B) = 1 at hL₁
    change reducedNorm hA (R : Matrix _ _ B) = 1 at hR₁
    change reducedNorm hA (x : Matrix _ _ B) = 1 at hx
    change reducedNorm hB (a : B) = 1
    rw [← reducedNorm_diagonalSlot hB (Nat.zero_lt_of_lt i.isLt) hA i a, ← ha,
      Units.val_mul, Units.val_mul, reducedNorm_mul, reducedNorm_mul, hL₁, hx, hR₁, mul_one, mul_one]
  have haC : diagonalSlot i a ∈ C.topologicalClosure := by
    have hcont := continuous_diagonalSlot c b i
    have hsub : (commutator Bˣ : Set Bˣ) ⊆ (diagonalSlot i) ⁻¹' ↑C.topologicalClosure := by
      intro y hy
      change diagonalSlot i y ∈ closure (C : Set _)
      exact subset_closure (hc (Subgroup.mem_map_of_mem (diagonalSlot i) hy))
    exact closure_minimal hsub (C.isClosed_topologicalClosure.preimage hcont) (hdense c hnorm)
  change x ∈ C.topologicalClosure
  have hx' : x = L⁻¹ * diagonalSlot i a * R⁻¹ := by rw [← ha]; group
  rw [hx']
  exact C.topologicalClosure.mul_mem
    (C.topologicalClosure.mul_mem (C.topologicalClosure.inv_mem (subset_closure (he hL))) haC)
    (C.topologicalClosure.inv_mem (subset_closure (he hR)))

end MatrixDensity

theorem matrixTransfer : MatrixTransfer.{u,v} := by
  classical
  intro F _ _ _ _ B _ _ hB hdense m hm hA
  let i : Fin m := ⟨0, hm⟩
  have hE : elementaryGroup (B := B) (Fin m) ≤ commutator _ :=
    elementaryGroup_le_commutator (F := F)
  refine ⟨fun b => matrix_normOne_subset_closure hB hdense hA i _ hE ?_ b, ?_⟩
  · rw [map_commutator_eq, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · intro hm₂
    refine ⟨fun _ h => commutator_norm_one hA (hE h), ?_⟩
    intro b
    let j : Fin m := ⟨1, hm₂⟩
    have hji : j ≠ i := fun h => by simpa [j, i] using congrArg Fin.val h
    apply matrix_normOne_subset_closure hB hdense hA i _ le_rfl _ b
    rw [Subgroup.map_le_iff_le_comap]
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    change diagonalSlot i ⁅a, b⁆ ∈ elementaryGroup (Fin m)
    exact diagonalSlot_commutator_mem j i hji a b

private theorem denseCommutators_of_algEquiv {F A A' : Type*}
    [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [Ring A] [Ring A'] [Algebra F A] [Algebra F A']
    (hA : IsCentralSimple F A) (hA' : IsCentralSimple F A') (e : A ≃ₐ[F] A')
    (h : denseCommutators hA') : denseCommutators hA := by
  intro b
  letI := coordinateTopology b
  let c := (b.map e.toLinearEquiv).reindex (finCongr e.toLinearEquiv.finrank_eq)
  letI := coordinateTopology c
  intro x hx
  let f := Units.map e.symm.toMonoidHom
  let x' := Units.map e.toMonoidHom x
  have hx' : x' ∈ normOne hA' := (norm_algEquiv hA hA' e (x : A)).symm.trans hx
  have he : f x' = x := Units.ext (e.symm_apply_apply _)
  have hf : Continuous f :=
    (linear_coordinate_continuous c b e.symm.toLinearMap).units_map e.symm.toMonoidHom
  have hc : (commutator (A')ˣ).map f ≤ commutator Aˣ := by
    rw [map_commutator_eq, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hs : (commutator (A')ˣ : Set (A')ˣ) ⊆ f ⁻¹' closure (commutator Aˣ : Set Aˣ) :=
    fun _ hy => subset_closure (hc (Subgroup.mem_map_of_mem f hy))
  rw [← he]
  exact closure_minimal hs (isClosed_closure.preimage hf) (h c hx')

private theorem denseCommutators_of_division {F : Type u} {A : Type v} [Field F]
    [TopologicalSpace F] [IsTopologicalDivisionRing F] [Infinite F] [Ring A] [Algebra F A]
    (hA : IsCentralSimple F A)
    (h : ∀ {B : Type v} [DivisionRing B] [Algebra F B] (hB : IsCentralSimple F B),
      denseCommutators hB) :
    denseCommutators hA := by
  letI := hA.2.1
  letI := hA.2.2
  obtain ⟨m, B, _, _, hB, hm, ⟨e⟩⟩ := MatrixDivision.exists_presentation F A hA
  let hM : IsCentralSimple F (Matrix (Fin m) (Fin m) B) :=
    ⟨hA.1.of_ringEquiv e.toRingEquiv, Algebra.IsCentral.of_algEquiv F A _ e,
      Module.Finite.equiv e.toLinearEquiv⟩
  let hB' := isCentralSimple_of_isCentralDivision F B hB
  exact denseCommutators_of_algEquiv hA hM e (matrixTransfer hB' (h hB') m hm hM).1

theorem localAlgebras : LocalAlgebras.{u,v} := by
  refine ⟨?_, ?_, ?_⟩
  · intro F _ _ _ _ A _ _ hA
    letI : Infinite ℤᵐ⁰ := Infinite.of_injective WithZero.exp WithZero.exp_injective
    letI : Infinite F := Infinite.of_surjective _
      ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
        (ValuativeRel.valuation_surjective (K := F)))
    exact denseCommutators_of_division hA nonarchimedeanDivision
  · intro A _ _ hA
    apply denseCommutators_of_division hA
    intro B _ _ hB c
    letI := coordinateTopology c
    intro x hx
    obtain ⟨a, b, rfl⟩ := realDivision hB x hx
    exact subset_closure (Subgroup.commutator_mem_commutator (by trivial) (by trivial))
  · intro A _ _ hA
    apply denseCommutators_of_division hA
    intro B _ _ hB c
    letI := coordinateTopology c
    intro x hx
    rw [complexDivision hB x hx]
    exact subset_closure ((commutator Bˣ).one_mem)

private theorem localField_of_complete_discrete {F : Type*} [Field F] [ValuativeRel F]
    [UniformSpace F] [IsUniformAddGroup F] [IsValuativeTopology F] [CompleteSpace F]
    [Finite (IsLocalRing.ResidueField (valuation F).valuationSubring)]
    (e : ValueGroupWithZero F ≃*o ℤᵐ⁰) : IsNonarchimedeanLocalField F := by
  have h := ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff.mp ⟨e⟩
  letI : ValuativeRel.IsNontrivial F := h.2.1
  letI : ValuativeRel.IsRankLeOne F := ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr h.2.2
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : IsCyclic (ValueGroupWithZero F)ˣ :=
    (Units.mapEquiv e.toMulEquiv).isCyclic.mpr inferInstance
  letI : IsDiscreteValuationRing (Valued.integer F) :=
    (valuation F).valuationSubring_isDiscreteValuationRing
  letI : Finite (Valued.ResidueField F) := inferInstanceAs
    (Finite (IsLocalRing.ResidueField (valuation F).valuationSubring))
  letI : NormedField F := Valued.toNormedField F (ValueGroupWithZero F)
  letI : ProperSpace F :=
    Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨⟩

theorem completeDiscreteAlgebras : CompleteDiscreteAlgebras.{u,v} := by
  intro F _ _ _ _ _ _ _ he A _ _ hA
  obtain ⟨e⟩ := he
  letI := localField_of_complete_discrete e
  exact localAlgebras.1 hA

section CommutatorWords

variable {G : Type*} [Group G]

private theorem commutatorWord_mem (L : List (G × G)) :
    commutatorWord L ∈ commutator G := by
  induction L with
  | nil => exact (commutator G).one_mem
  | cons z L ih =>
    exact (commutator G).mul_mem (Subgroup.commutator_mem_commutator (by trivial) (by trivial)) ih

private theorem commutatorWord_append (L W : List (G × G)) :
    commutatorWord (L ++ W) = commutatorWord L * commutatorWord W := by
  simp [commutatorWord]

private theorem exists_word_of_mem_commutator {x : G} (hx : x ∈ commutator G) :
    ∃ W : List (G × G), commutatorWord W = x := by
  rw [commutator_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := mem_commutatorSet_iff.mp hx
    exact ⟨[(a, b)], by simp [commutatorWord]⟩
  | one => exact ⟨[], rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨V, rfl⟩ := hx
    obtain ⟨W, rfl⟩ := hy
    exact ⟨V ++ W, commutatorWord_append _ _⟩
  | inv x hxc hx =>
    clear hxc
    obtain ⟨W, rfl⟩ := hx
    refine ⟨W.reverse.map Prod.swap, ?_⟩
    induction W with
    | nil => simp [commutatorWord]
    | cons p W ih =>
      simp only [List.reverse_cons, List.map_append, List.map_singleton, commutatorWord_append, ih]
      simp [commutatorWord, commutatorElement_inv]

private theorem commutator_mem_closure_of_denseRange {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H) (hf : DenseRange f) :
    commutator H ≤ ((commutator G).map f).topologicalClosure := by
  let C := ((commutator G).map f).topologicalClosure
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  have hcont : Continuous (fun q : H × H => ⁅q.1, q.2⁆) := by
    simp only [commutatorElement_def]
    fun_prop
  apply hf.induction_on₂ (p := fun x y => ⁅x, y⁆ ∈ C)
    (Subgroup.isClosed_topologicalClosure _ |>.preimage hcont) _ a b
  intro x y
  rw [← map_commutatorElement]
  exact subset_closure (Subgroup.mem_map_of_mem f
    (Subgroup.commutator_mem_commutator (by trivial) (by trivial)))

end CommutatorWords

section Simultaneous

open IsDedekindDomain

private theorem infinite_primes_integral {R A : Type*} [CommRing R] [CommRing A]
    [IsDedekindDomain R] [IsDedekindDomain A] [Infinite (HeightOneSpectrum R)]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A] :
    Infinite (HeightOneSpectrum A) := by
  classical
  have ex (p : HeightOneSpectrum R) :
      ∃ q : HeightOneSpectrum A, q.asIdeal.under R = p.asIdeal := by
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := A) p.asIdeal
    have he := (Ideal.liesOver_iff Q p.asIdeal).mp hl
    refine ⟨⟨Q, hQ.isPrime, ?_⟩, he.symm⟩
    intro h
    apply p.ne_bot
    rw [he, h, Ideal.under, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R A)
  choose q hq using ex
  exact Infinite.of_injective q fun p p' e => HeightOneSpectrum.ext
    ((hq p).symm.trans ((congrArg (fun q : HeightOneSpectrum A => q.asIdeal.under R) e).trans (hq p')))

private theorem infinite_polynomial_primes (F : Type*) [Field F] :
    Infinite (HeightOneSpectrum (Polynomial F)) := by
  classical
  by_contra! h
  letI : Fintype (HeightOneSpectrum (Polynomial F)) := Fintype.ofFinite _
  let f (p : HeightOneSpectrum (Polynomial F)) := Submodule.IsPrincipal.generator p.asIdeal
  let P := ∏ p, f p
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ he =>
    p.ne_bot ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p.asIdeal).mpr he)
  let z : Polynomial F := Polynomial.X * P + 1
  have hd : 0 < z.natDegree := by
    have he : (1 : Polynomial F).natDegree < (Polynomial.X * P).natDegree := by
      rw [Polynomial.natDegree_X_mul hP, Polynomial.natDegree_one]
      omega
    dsimp only [z]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt he]
    simpa using he
  have hzu : ¬ IsUnit z := fun h => hd.ne' (Polynomial.natDegree_eq_zero_of_isUnit h)
  have hz₀ : z ≠ 0 := fun h => hd.ne' (h ▸ Polynomial.natDegree_zero)
  obtain ⟨I, hI, hIZ⟩ := Ideal.exists_le_maximal (Ideal.span {z})
    (Ideal.span_singleton_ne_top hzu)
  have hz : z ∈ I := hIZ (Ideal.subset_span (by simp))
  let p : HeightOneSpectrum (Polynomial F) := ⟨I, hI.isPrime, fun h =>
    hz₀ (by simpa only [h, Ideal.mem_bot] using hz)⟩
  have hp : f p ∣ P := Finset.dvd_prod_of_mem f (Finset.mem_univ p)
  obtain ⟨Q, hQ⟩ := hp
  have hf : f p ∈ I := Submodule.IsPrincipal.generator_mem p.asIdeal
  have hpI : P ∈ I := hQ ▸ I.mul_mem_right Q hf
  have h1 : (1 : Polynomial F) ∈ I := by
    have hh := I.sub_mem hz (I.mul_mem_left Polynomial.X hpI)
    simpa [z] using hh
  exact hI.ne_top (I.eq_top_of_isUnit_mem h1 isUnit_one)

open scoped NumberField Polynomial

private theorem infinite_places {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) :
    Infinite D.Place := by
  cases D with
  | number h =>
    letI := h
    letI : Infinite (HeightOneSpectrum ℤ) :=
      Infinite.of_injective (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
        (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective
    letI : Infinite (HeightOneSpectrum (𝓞 K)) := infinite_primes_integral (R := ℤ)
    exact Infinite.of_injective Sum.inl Sum.inl_injective
  | function F t =>
    letI : Algebra F[X] K := t.polynomialAlgebra
    letI : Infinite (HeightOneSpectrum F[X]) := infinite_polynomial_primes F
    letI : FaithfulSMul F[X] t.integerRing :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y he =>
        (transcendental_iff_injective.mp t.transcendental) (congrArg
          (fun z : t.integerRing => (z : K)) he)
    letI : Algebra.IsIntegral F[X] t.integerRing := by
      change Algebra.IsIntegral F[X] ↥(integralClosure F[X] K)
      exact integralClosure.AlgebraIsIntegral
    letI : Infinite (HeightOneSpectrum t.integerRing) := infinite_primes_integral (R := F[X])
    exact Infinite.of_injective (Sum.inl ∘ t.placeOfPrime)
      (Sum.inl_injective.comp t.placeOfPrime_injective)

private theorem dense_scalar_diagonal {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (T : Finset D.Place) : DenseRange (fun (a : K) (p : T) => D.embedding p.1 a) := by
  classical
  letI := infinite_places D
  obtain ⟨o, ho⟩ := Infinite.exists_notMem_finset T
  let j : T ↪ ({o}ᶜ : Set D.Place) :=
    ⟨fun p => ⟨p.val, fun h => ho ((Set.mem_singleton_iff.mp h) ▸ p.property)⟩,
      fun x y h => Subtype.ext (congrArg (fun p : ({o}ᶜ : Set D.Place) => p.val) h)⟩
  let T' := T.attach.map j
  let pOf (q : T') : T :=
    ⟨q.1.1, by
      obtain ⟨p, _, hp⟩ := Finset.mem_map.mp q.2
      exact (congrArg Subtype.val hp) ▸ p.2⟩
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUn
  obtain ⟨y, hy⟩ := hUn
  obtain ⟨V, hV, hVU⟩ := isOpen_pi_iff'.mp hU y hy
  obtain ⟨a, ha, _⟩ := additiveFiniteTuples D {o} (Set.singleton_nonempty _) T'
    (fun q => V (pOf q)) (fun q => (hV (pOf q)).1)
    (fun q => ⟨y (pOf q), (hV (pOf q)).2⟩)
  refine ⟨_, hVU ?_, a, rfl⟩
  intro p _
  have hj : j p ∈ T' := Finset.mem_map.mpr ⟨p, Finset.mem_attach _ _, rfl⟩
  exact ha ⟨j p, hj⟩

variable {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
  {A : Type w} [Ring A] [Algebra K A]

private instance completionDivisionRing (p : D.Place) : IsTopologicalDivisionRing (D.Completion p) := by
  cases p with
  | inl q => exact inferInstanceAs (IsTopologicalDivisionRing (D.FiniteCompletion q))
  | inr q =>
    cases D with
    | number h => exact inferInstanceAs (IsTopologicalDivisionRing q.Completion)
    | function => exact q.elim

private instance completionT1 (p : D.Place) : T1Space (D.Completion p) := by
  cases p with
  | inl q => exact inferInstanceAs (T1Space (D.FiniteCompletion q))
  | inr q =>
    cases D with
    | number h => exact inferInstanceAs (T1Space q.Completion)
    | function => exact q.elim

variable (T : Finset D.Place)

local instance completionAlgebra (p : T) : Algebra K (D.Completion p.1) := (D.embedding p.1).toAlgebra

private abbrev Completed (p : T) := D.Completion p.1 ⊗[K] A

private def localize (p : T) : A →ₐ[K] Completed (A := A) D T p :=
  Algebra.TensorProduct.includeRight

private theorem dense_algebra_diagonal (hA : IsCentralSimple K A)
    (b : ∀ p : T, Module.Basis (Fin (Module.finrank (D.Completion p.1) (Completed (A := A) D T p)))
      (D.Completion p.1) (Completed (A := A) D T p)) :
    letI (p : T) := coordinateTopology (b p)
    DenseRange (fun (a : A) (p : T) => localize D T p a) := by
  classical
  letI := hA.2.2
  letI (p : T) := coordinateTopology (b p)
  let I := Fin (Module.finrank K A)
  let c := Module.finBasis K A
  let b₀ (p : T) := c.baseChange (D.Completion p.1)
  let Φ (x : I → ∀ p : T, D.Completion p.1) (p : T) : Completed (A := A) D T p :=
    (b₀ p).equivFun.symm (fun i => x i p)
  have hΦcont : Continuous Φ := by
    apply continuous_pi
    intro p
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro j
    have he (x : I → ∀ p : T, D.Completion p.1) :
        (b p).repr (Φ x p) j = ∑ i, (b p).repr (b₀ p i) j * x i p := by
      rw [← (b p).sum_repr_mul_repr (b₀ p)]
      apply Finset.sum_congr rfl
      intro i _
      change (b p).repr (b₀ p i) j * (b₀ p).equivFun ((b₀ p).equivFun.symm
        (fun i => x i p)) i = _
      rw [(b₀ p).equivFun.apply_symm_apply]
    change Continuous (fun x => (b p).repr (Φ x p) j)
    simp_rw [he]
    refine continuous_finsetSum _ fun i _ => ?_
    have hi : Continuous (fun x : I → ∀ p : T, D.Completion p.1 => x i) := continuous_apply i
    have hp : Continuous (fun x : ∀ p : T, D.Completion p.1 => x p) := continuous_apply p
    exact continuous_const.mul (hp.comp hi)
  have hΦsurj : Function.Surjective Φ := by
    intro y
    exact ⟨fun i p => (b₀ p).equivFun (y p) i, funext fun p => (b₀ p).equivFun.symm_apply_apply _⟩
  have hd := hΦsurj.denseRange.comp (DenseRange.piMap (fun _ : I => dense_scalar_diagonal D T)) hΦcont
  have he :
      (fun a p => localize (A := A) D T p a) =
        (Φ ∘ Pi.map (fun (_ : I) (a : K) (p : T) => D.embedding p.1 a)) ∘ c.equivFun := by
    funext a p
    apply (b₀ p).equivFun.injective
    apply funext
    intro i
    change (b₀ p).repr (1 ⊗ₜ[K] a) i =
      (b₀ p).equivFun ((b₀ p).equivFun.symm (fun i => D.embedding p.1 (c.equivFun a i))) i
    rw [(b₀ p).equivFun.apply_symm_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    rfl
  rw [he, DenseRange, Set.range_comp, c.equivFun.surjective.range_eq, Set.image_univ]
  exact hd 

set_option maxHeartbeats 1000000 in
theorem simultaneousApproximation : SimultaneousApproximation.{u,v,w} := by
  classical
  intro K _ D A _ _ hA T Ap b
  letI (p : T) := coordinateTopology (b p)
  intro L U hU hL
  by_cases hT : T.Nonempty
  · letI (p : T) : ContinuousMul (Completed (A := A) D T p) := continuousMul_coordinates (b p)
    let V := ∀ p : T, (Completed (A := A) D T p)ˣ
    let φ : Aˣ →* V := MonoidHom.pi fun p => (localize D T p).toMonoidHom |> Units.map
    let j : V → ∀ p : T, Completed (A := A) D T p := Pi.map fun _ => Units.val
    have hj : IsOpenEmbedding j := IsOpenEmbedding.piMap fun p => units_open_embedding (b p)
    have hd : DenseRange φ := by
      rw [DenseRange, dense_iff_inter_open]
      intro O hO hOn
      obtain ⟨z, hz, a, ha⟩ := (dense_iff_inter_open.mp (dense_algebra_diagonal D T hA b))
        (j '' O) (hj.isOpenMap O hO) (hOn.image j)
      obtain ⟨y, hy, hzy⟩ := hz
      obtain ⟨p, hp⟩ := hT
      let p₀ : T := ⟨p, hp⟩
      have he (p : T) : localize (A := A) D T p a = (y p : Completed (A := A) D T p) :=
        congrFun (ha.trans hzy.symm) p
      have hAu : IsUnit a := by
        letI : Algebra K (D.Completion p₀.1) := (D.embedding p₀.1).toAlgebra
        have hlocal := isCentralSimple_baseChange (L := D.Completion p₀.1) hA
        have hn := (reducedNorm_ne_zero_iff_isUnit hlocal _).mpr (y p₀).isUnit
        rw [← he p₀] at hn
        change reducedNorm hlocal (1 ⊗ₜ[K] a) ≠ 0 at hn
        rw [reducedNorm_baseChange hA a hlocal] at hn
        refine (reducedNorm_ne_zero_iff_isUnit hA a).mp fun h => hn ?_
        rw [h, map_zero]
      exact ⟨y, hy, hAu.unit, funext fun p => Units.ext (by
        change localize (A := A) D T p (hAu.unit : A) = _
        rw [hAu.unit_spec]
        exact he p)⟩
    let x : V := fun p => commutatorWord (L p)
    have hx : x ∈ commutator V := by
      rw [commutator_def, ← Subgroup.pi_top Set.univ (f := fun p : T =>
          (Completed (A := A) D T p)ˣ), Subgroup.commutator_pi_pi_of_finite]
      exact (Subgroup.mem_pi _).mpr fun p _ => commutatorWord_mem (L p)
    have hxcl := commutator_mem_closure_of_denseRange φ hd hx
    obtain ⟨_, hy, a, ha, rfl⟩ := mem_closure_iff.mp hxcl (Set.pi Set.univ U)
      (isOpen_set_pi Set.finite_univ fun p _ => hU p) (fun p _ => hL p)
    obtain ⟨W, rfl⟩ := exists_word_of_mem_commutator ha
    exact ⟨W, commutator_norm_one hA ha, fun p => hy p (Set.mem_univ p)⟩
  · refine ⟨[], ?_, ?_⟩
    · exact commutator_norm_one hA (commutatorWord_mem [])
    · intro p
      exact (hT ⟨p.1, p.2⟩).elim

end Simultaneous

end LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
