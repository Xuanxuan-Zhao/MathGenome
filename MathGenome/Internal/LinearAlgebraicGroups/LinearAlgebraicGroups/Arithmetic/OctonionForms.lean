import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OctonionForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.PeirceFrames
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.Adjoints
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.QuaternionNorm
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SplitApproximation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionInnerAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

noncomputable section

open scoped TensorProduct WithZero Ring Polynomial
universe u v w
open ValuativeRel RM03.CSA

namespace LinearAlgebraicGroups.Arithmetic.OctonionForms

open Specs.OctonionForms
open LocalDivisionAlgebras
open _root_.LinearAlgebraicGroups.Composition
open Composition.Specification

theorem splitQuaternionNormSurjective : SplitQuaternionNormSurjective.{u,v} := by
  intro F _ B _ _ hB hd ⟨e⟩ c hc
  let e' : B ≃ₐ[F] Matrix (Fin (degree F B)) (Fin (degree F B)) F := hd.symm ▸ e
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (degree F B)) (Fin (degree F B)) F, M.det = c := by
    rw [hd]
    refine ⟨Matrix.diagonal ![c, 1], ?_⟩
    rw [Matrix.det_fin_two]
    simp
  let x := e'.symm M
  have hx : reducedNorm hB x = c := by
    rw [reducedNorm_eq_det hB x e', AlgEquiv.apply_symm_apply, hM]
  exact ⟨((reducedNorm_ne_zero_iff_isUnit hB x).mp (hx ▸ hc)).unit,
    by rw [IsUnit.unit_spec, hx]⟩

private theorem reducedNorm_one_add_scalar {F : Type u} [Field F]
    {B : Type v} [DivisionRing B] [Algebra F B] (hB : IsCentralSimple F B)
    (hd : degree F B = 2) (a : F) (x : B) :
    reducedNorm hB (1 + a • x) =
      1 + a * reducedTrace hB x + a ^ 2 * reducedNorm hB x := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [reducedNorm_map hB _ e, map_add, map_add, map_one, map_mul, map_mul, map_pow,
    reducedTrace_map hB e, reducedNorm_map hB _ e]
  let f : B →ₐ[F] Matrix (Fin (degree F B)) (Fin (degree F B)) (AlgebraicClosure F) :=
    (e.toAlgHom.restrictScalars F).comp Algebra.TensorProduct.includeRight
  change (f (1 + a • x)).det =
    1 + algebraMap F (AlgebraicClosure F) a * (f x).trace +
    (algebraMap F (AlgebraicClosure F) a) ^ 2 * (f x).det
  rw [map_add, map_one, map_smul, ← IsScalarTower.algebraMap_smul (AlgebraicClosure F)]
  generalize algebraMap F (AlgebraicClosure F) a = b
  generalize f x = M
  revert M
  rw [hd]
  intro M
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp
  ring

/-- A norm with residue one is obtained by lifting the simple root zero of
the norm polynomial along a direction of unit reduced trace. -/
private theorem principal_unit_norm {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : IsCentralSimple F B) (hd : degree F B = 2)
    (b : B) (A T d : Integers F) (hA : IsUnit A) (hT : IsUnit T)
    (ha : (A : F) = reducedNorm hB b) (ht : (T : F) = reducedTrace hB b)
    (hres : IsLocalRing.residue _ d = 1) :
    ∃ x : B, reducedNorm hB x = (d : F) := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  let R := Integers F
  let I := IsLocalRing.maximalIdeal R
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (valuation F).integer) (valuation F).integer :=
    inferInstance
  have hInv : IsUnit A⁻¹ʳ := by
    rw [Ring.inverse_of_isUnit hA]
    exact Units.isUnit _
  let p : R[X] := Polynomial.C (A⁻¹ʳ) *
    (Polynomial.C A * Polynomial.X ^ 2 + Polynomial.C T * Polynomial.X +
      Polynomial.C (1 - d))
  have hmonic : p.Monic := by
    have H : p = Polynomial.X ^ 2 + Polynomial.C (A⁻¹ʳ * T) * Polynomial.X +
        Polynomial.C (A⁻¹ʳ * (1 - d)) := by
      dsimp [p]
      rw [mul_add, mul_add, ← mul_assoc, ← Polynomial.C_mul, Ring.inverse_mul_cancel _ hA,
        Polynomial.C_1, one_mul, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul]
    rw [H, add_assoc]
    apply Polynomial.monic_X_pow_add
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · calc
        _ ≤ Polynomial.degree (Polynomial.C (A⁻¹ʳ * T)) +
            Polynomial.degree (Polynomial.X : R[X]) := Polynomial.degree_mul_le _ _
        _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le (by simp)
        _ < 2 := by decide
    · exact Polynomial.degree_C_le.trans_lt (by decide)
  have hzero : p.eval 0 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change IsLocalRing.residue R (p.eval 0) = 0
    have hh : IsLocalRing.residue R d = 1 := hres
    simp [p, hh]
  have hderiv : IsUnit ((Ideal.Quotient.mk I) (p.derivative.eval 0)) := by
    apply IsUnit.map
    simpa [p, Polynomial.derivative_mul, Polynomial.derivative_pow] using
      hInv.mul hT
  obtain ⟨t, hp, _⟩ := HenselianRing.is_henselian p hmonic 0 hzero hderiv
  change p.eval t = 0 at hp
  simp only [p, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X] at hp
  have heq := (mul_eq_zero.mp hp).resolve_left hInv.ne_zero
  refine ⟨1 + (t : F) • b, ?_⟩
  rw [reducedNorm_one_add_scalar hB hd, ← ha, ← ht]
  have hf := congrArg (fun z : Integers F => (z : F)) heq
  change (A : F) * (t : F) ^ 2 + (T : F) * (t : F) + (1 - (d : F)) = 0 at hf
  linear_combination hf

private theorem baseValue_eq_one {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) :
    baseValue F x = 1 ↔ valuation F x = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  change e (valuation F x) = 1 ↔ _
  rw [← map_one e]
  exact e.injective.eq_iff

theorem localQuaternionNormSurjective : LocalQuaternionNormSurjective.{u,v} := by
  intro F _ _ _ _ B _ _ hB hd c hc
  obtain ⟨w, hw, _⟩ := valuation_exists hB
  obtain ⟨r⟩ := residue_field hB w hw
  letI := r.isField.toField
  letI := r.algebra
  letI := r.finite
  obtain ⟨wsurj, _, ⟨pres⟩⟩ := cyclic_structure hB w hw r
  letI := pres.residue_separable
  let red := IsLocalRing.residue (Integers F)
  have hred := reduction_of_norm_trace hB w hw r
  obtain ⟨y, hy⟩ := wsurj (baseValue F c)
  have hyN : baseValue F (reducedNorm hB y) = baseValue F c := (hw.1 y).symm.trans hy
  have hyp : reducedNorm hB y ≠ 0 := by
    intro hz
    rw [hz] at hyN
    exact hc (by simpa [baseValue] using hyN.symm)
  let ν : Valuation F ℤᵐ⁰ := LocalDivisionRamification.normalizedValuation F
  have hval : ν (c / reducedNorm hB y) = 1 := by
    rw [map_div₀]
    change baseValue F c / baseValue F (reducedNorm hB y) = 1
    rw [hyN, div_self]
    simpa [ν] using (map_ne_zero ν |>.mpr hc)
  have hval' : valuation F (c / reducedNorm hB y) = 1 :=
    (baseValue_eq_one _).mp hval
  let d : Integers F := ⟨c / reducedNorm hB y, hval'.le⟩
  have hdunit : IsUnit d := by
    by_contra h
    exact hval'.not_lt ((Valuation.mem_maximalIdeal_iff F (valuation F)).mp
      ((IsLocalRing.mem_maximalIdeal d).mpr h))
  obtain ⟨z, hz⟩ := FiniteField.unitsMap_norm_surjective (BaseResidue F) (ResidueRing w)
    (Units.map red hdunit.unit)
  obtain ⟨z₀, hz₀⟩ := residue_surjective w (z : ResidueRing w)
  obtain ⟨A₀, _, hA₀, _, hN₀, _⟩ := hred z₀
  have hredA₀ : red A₀ = red d := by
    rw [hN₀, hz₀]
    simpa [red] using congrArg Units.val hz
  have hi₀ : IsUnit A₀ :=
    (IsLocalRing.residue_ne_zero_iff_isUnit A₀).mp
      (hredA₀ ▸ ((IsLocalRing.residue_ne_zero_iff_isUnit d).mpr hdunit))
  let d' : Integers F := d * A₀⁻¹ʳ
  have hd' : red d' = 1 := by
    change red (d * A₀⁻¹ʳ) = 1
    rw [map_mul, ← hredA₀, ← map_mul, Ring.mul_inverse_cancel _ hi₀, map_one]
  obtain ⟨bbar, hbbar⟩ := Algebra.trace_surjective (BaseResidue F) (ResidueRing w) 1
  obtain ⟨b, hb⟩ := residue_surjective w bbar
  obtain ⟨A, T, hA, hT, hAn, hTt⟩ := hred b
  have hT1 : red T = 1 := hTt.trans (hb ▸ hbbar)
  have hbn : bbar ≠ 0 := by
    intro e
    simp [e] at hbbar
  have hAu : IsUnit A := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit A).mp
    rw [hAn, hb]
    simpa using hbn
  have hTu : IsUnit T :=
    (IsLocalRing.residue_ne_zero_iff_isUnit T).mp (by rw [hT1]; exact one_ne_zero)
  obtain ⟨x, hx⟩ := principal_unit_norm hB hd _ A T d' hAu hTu hA hT hd'
  have hnorm : reducedNorm hB (y * (z₀ : B) * x) = c := by
    rw [reducedNorm_mul, reducedNorm_mul, show reducedNorm hB (z₀ : B) = (A₀ : F) from hA₀.symm, hx]
    have hm : (A₀ : F) * (d' : F) = (d : F) := by
      have h : A₀ * d' = d := by
        dsimp [d']
        rw [mul_left_comm, Ring.mul_inverse_cancel _ hi₀, mul_one]
      exact congrArg (fun a : Integers F => (a : F)) h
    rw [mul_assoc, hm]
    change reducedNorm hB y * (c / reducedNorm hB y) = c
    exact mul_div_cancel₀ c hyp
  exact ⟨((reducedNorm_ne_zero_iff_isUnit hB _).mp (hnorm ▸ hc)).unit,
    by rw [IsUnit.unit_spec, hnorm]⟩

theorem algebraicallyClosedSplit : AlgebraicallyClosedSplit.{u,v} := by
  intro k _ _ C _ _ _ _ n hn
  obtain ⟨e⟩ := Peirce.points_over_algebraically_closed hn
  apply Peirce.isotropic_field_split hn
  refine ⟨e.val, ?_, e.property.2⟩
  intro he
  have h : compositionTrace n e.val = 1 := e.property.1
  rw [he, map_zero] at h
  exact zero_ne_one h

theorem complexSplit : ComplexSplit.{v} :=
  algebraicallyClosedSplit (k := ℂ)

theorem realSplitOrPositive : RealSplitOrPositive.{v} := by
  intro C _ _ _ _ n hn
  by_cases hi : isotropic n
  · exact Or.inl (Peirce.isotropic_field_split hn hi)
  right
  have h := IsOctonionNorm.toNormLaws hn
  intro x hx
  by_contra! hle
  have hneg : n x < 0 := hle.lt_of_ne fun e => hi ⟨x, hx, e⟩
  let r := compositionTrace n x / 2
  let y := x - r • (1 : C)
  have hyt : compositionTrace n y = 0 := by
    rw [show y = x - r • (1 : C) by rfl, map_sub, compositionTrace_scalar h]
    dsimp [r]
    ring
  have H (s : ℝ) : n (s • (1 : C) + y) = s ^ 2 + n y := by
    rw [QuadraticMap.map_add n, ← QuadraticMap.polarBilin_apply_apply, norm_scalar h,
      show n.polarBilin (s • (1 : C)) y = n.polarBilin y (s • 1) from
        QuadraticMap.polar_comm n _ _, map_smul, ← compositionTrace_apply, hyt]
    simp
  have hx' : r • (1 : C) + y = x := by simp [y, add_sub_cancel]
  have hyneg : n y < 0 := by
    have hh := H r
    rw [hx'] at hh
    linarith [sq_nonneg r]
  let s := Real.sqrt (-n y)
  have hs : s ^ 2 = -n y := Real.sq_sqrt (by linarith)
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  apply hi
  refine ⟨s • (1 : C) + y, ?_, by rw [H, hs, neg_add_cancel]⟩
  intro hz
  have ht := congrArg (compositionTrace n) hz
  rw [map_add, compositionTrace_scalar h, hyt, map_zero, add_zero] at ht
  linarith

section LocalSplitting

open Module QuaternionSpecification

open private exists_norm_ne_zero_orthogonal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.QuaternionNorm

variable {k : Type u} [Field k] {C : Type v} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C}

private theorem exists_separable_generator (hn : FieldNormConditions n)
    (hDim : finrank k C = 8) :
    ∃ x : C, compositionTrace n x ^ 2 - 4 * n x ≠ 0 := by
  letI := hn.finite
  letI := hn.nontrivial
  have h := IsFieldCompositionNorm.toNormLaws hn
  by_cases h2 : (2 : k) = 0
  · have ht : compositionTrace n ≠ 0 := by
      intro H
      apply one_ne_zero (α := C)
      apply hn.nondegenerate.2 1
      intro x
      exact LinearMap.congr_fun H x
    obtain ⟨x, hx⟩ := (LinearMap.surjective_iff_ne_zero.mpr ht) 1
    refine ⟨x, ?_⟩
    have h4 : (4 : k) = 0 := by linear_combination 2 * h2
    rw [hx, h4]
    simp
  · let W : Submodule k C := k ∙ (1 : C)
    have hWdim : finrank k W = 1 := finrank_span_singleton one_ne_zero
    have hOne : n.polarBilin (1 : C) 1 = (2 : k) := compositionTrace_one h
    have hRefl : n.polarBilin.IsRefl := fun x y hxy =>
      (QuadraticMap.polar_comm n y x).trans hxy
    have hW : (LinearMap.BilinForm.restrict n.polarBilin W).Nondegenerate :=
      LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ hRefl
        (LinearMap.BilinForm.isCompl_span_singleton_orthogonal (hOne.trans_ne h2)).disjoint
    obtain ⟨x, hx, hN⟩ := exists_norm_ne_zero_orthogonal hn W hW
      (by rw [hWdim, hDim]; decide)
    have ht : compositionTrace n x = 0 :=
      (QuadraticMap.polar_comm n x 1).trans (hx 1 (Submodule.mem_span_singleton_self 1))
    have h4 : (4 : k) ≠ 0 := by rw [show (4 : k) = 2 * 2 by ring]; exact mul_ne_zero h2 h2
    exact ⟨x, by simpa [ht] using mul_ne_zero h4 hN⟩

open Polynomial in
private theorem quadraticAlgebra_etale (a b : k) (h : b ^ 2 + 4 * a ≠ 0) :
    Algebra.Etale k (QuadraticAlgebra k a b) := by
  let D := QuadraticAlgebra k a b
  let f : k[X] := X ^ 2 - (C b * X + C a)
  have hmonic : f.Monic := by
    apply monic_X_pow_sub
    apply lt_of_le_of_lt (degree_add_le _ _) (max_lt _ _)
    · exact (degree_mul_le _ _).trans_lt (by
        calc
          _ ≤ 0 + 1 := add_le_add degree_C_le (by simp)
          _ < 2 := by decide)
    · exact degree_C_le.trans_lt (by decide)
  let P : StandardEtalePair k := ⟨f, hmonic, f.derivative, ⟨1, 0, 1, by simp⟩⟩
  let ω : D := QuadraticAlgebra.omega
  have hω : ω ^ 2 = algebraMap k D a + algebraMap k D b * ω := by
    rw [QuadraticAlgebra.omega_pow_two_eq_add]
    change a • (1 : D) + b • ω = _
    simp [Algebra.smul_def]
  have hf (A : Type u) [CommRing A] [Algebra k A] (x : A) :
      aeval x f = x ^ 2 - (algebraMap k A b * x + algebraMap k A a) := by simp [f]
  have hp : P.HasMap ω := by
    constructor
    · change aeval ω f = 0
      rw [hf D ω, hω, add_comm, sub_self]
    · change IsUnit (aeval ω f.derivative)
      have H : aeval ω f.derivative = 2 * ω - algebraMap k D b := by
        simp [f, derivative_pow, derivative_mul, map_ofNat]
      rw [H]
      have hsq : (2 * ω - algebraMap k D b) ^ 2 = algebraMap k D (b ^ 2 + 4 * a) := by
        simp only [map_add, map_pow, map_mul, map_ofNat]
        linear_combination 4 * hω
      exact isUnit_of_dvd_unit (dvd_pow_self _ (by decide : 2 ≠ 0))
        (hsq ▸ ((isUnit_iff_ne_zero.mpr h).map (algebraMap k D)))
  let g := P.lift ω hp
  have hP := P.hasMap_X.1
  change aeval P.X f = 0 at hP
  rw [hf P.Ring P.X, sub_eq_zero, add_comm] at hP
  let t : D →ₐ[k] P.Ring := QuadraticAlgebra.lift ⟨P.X, by
    simpa [pow_two, Algebra.smul_def] using hP⟩
  have ht : t ω = P.X := by
    change (0 : k) • (1 : P.Ring) + (1 : k) • P.X = P.X
    simp
  have hg : g P.X = ω := P.lift_X _ _
  let e : P.Ring ≃ₐ[k] D := AlgEquiv.ofAlgHom g t
    (QuadraticAlgebra.algHom_ext (by change g (t ω) = ω; rw [ht, hg]))
    (P.hom_ext (by change t (g P.X) = P.X; rw [hg, ht]))
  exact Algebra.Etale.of_equiv e

private theorem exists_quadratic_subalgebra (hn : FieldNormConditions n)
    (hDim : finrank k C = 8) :
    ∃ (D : UnitalSubalgebra k C)
      (ha : ∀ x y z : D, (x * y) * z = x * (y * z)) (hc : ∀ x y : D, x * y = y * x),
      letI : CommRing D := commutativeSubalgebraRing D ha hc
      letI : Algebra k D := Algebra.ofModule (R := k) (A := D) smul_mul_assoc mul_smul_comm
      Algebra.Etale k D ∧ finrank k D = 2 ∧ FieldNormConditions (D.restrictNorm n) := by
  obtain ⟨x, hx⟩ := exists_separable_generator hn hDim
  have hL := IsFieldCompositionNorm.toNormLaws hn
  let a := -n x
  let b := compositionTrace n x
  let Q := QuadraticAlgebra k a b
  have hd : b ^ 2 + 4 * a ≠ 0 := by simpa [a, b, sub_eq_add_neg] using hx
  have hsq : x * x = a • (1 : C) + b • x := by
    have H := composition_quadratic_equation hL x
    dsimp [a, b]
    calc
      x * x = (x * x - compositionTrace n x • x + n x • (1 : C)) +
          ((-n x) • (1 : C) + compositionTrace n x • x) := by rw [neg_smul]; abel
      _ = _ := by rw [H, zero_add]
  let f : Q →ₗ[k] C :=
    (QuadraticAlgebra.reₗ a b).smulRight (1 : C) + (QuadraticAlgebra.imₗ a b).smulRight x
  have hf (s : Q) : f s = s.re • (1 : C) + s.im • x := rfl
  have hf1 : f 1 = 1 := by
    change (1 : k) • (1 : C) + (0 : k) • x = 1
    simp
  have hfw : f QuadraticAlgebra.omega = x := by simp [hf]
  have hfm (s t : Q) : f (s * t) = f s * f t := by
    change (s.re * t.re + a * s.im * t.im) • (1 : C) +
        (s.re * t.im + s.im * t.re + b * s.im * t.im) • x =
      (s.re • (1 : C) + s.im • x) * (t.re • (1 : C) + t.im • x)
    simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hsq,
      smul_add, smul_smul, add_smul]
    module
  have detect {s : Q} (h1 : n.polarBilin (f s) 1 = 0)
      (hx' : n.polarBilin (f s) x = 0) : s = 0 := by
    have hone : n.polarBilin (1 : C) 1 = 2 := compositionTrace_one hL
    have hxx : n.polarBilin x x = 2 * n x := by
      simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_mul]
    have hbx : n.polarBilin (1 : C) x = b := QuadraticMap.polar_comm n _ _
    have hxb : n.polarBilin x 1 = b := rfl
    simp only [hf, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hone, hxx, hbx, hxb] at h1 hx'
    have h1' : (s.re * (b ^ 2 + 4 * a)) = 0 := by
      dsimp [a]
      linear_combination b * hx' - (2 * n x) * h1
    have hx'' : (s.im * (b ^ 2 + 4 * a)) = 0 := by
      dsimp [a]
      linear_combination b * h1 - 2 * hx'
    ext
    · exact (mul_eq_zero.mp h1').resolve_right hd
    · exact (mul_eq_zero.mp hx'').resolve_right hd
  have hfinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro s hs
    apply detect <;> simp [hs]
  let D : UnitalSubalgebra k C :=
    { toSubmodule := LinearMap.range f
      one_mem' := ⟨1, hf1⟩
      mul_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨s * t, hfm s t⟩ }
  let e : Q ≃ₗ[k] D := LinearEquiv.ofInjective f hfinj
  have he1 : e 1 = 1 := Subtype.ext hf1
  have hem (s t : Q) : e (s * t) = e s * e t := Subtype.ext (hfm s t)
  have ha (x y z : D) : (x * y) * z = x * (y * z) := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := e.surjective z
    simp only [← hem, mul_assoc]
  have hc (x y : D) : x * y = y * x := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    simp only [← hem, mul_comm]
  refine ⟨D, ha, hc, ?_⟩
  letI : CommRing D := commutativeSubalgebraRing D ha hc
  letI : Algebra k D := Algebra.ofModule (R := k) (A := D) smul_mul_assoc mul_smul_comm
  let E : Q ≃ₐ[k] D := AlgEquiv.ofLinearEquiv e he1 hem
  letI : Algebra.Etale k Q := quadraticAlgebra_etale a b hd
  refine ⟨Algebra.Etale.of_equiv E, e.finrank_eq.symm.trans (QuadraticAlgebra.finrank_eq_two _ _),
    Module.Finite.of_surjective e.toLinearMap e.surjective, e.injective.nontrivial, ?_,
    fun s t => hL.map_mul (s : C) (t : C)⟩
  have hreg (z : D) (hz : ∀ t : D, (D.restrictNorm n).polarBilin z t = 0) : z = 0 := by
    obtain ⟨s, rfl⟩ := e.surjective z
    have h1 := hz (e 1)
    have hx := hz (e QuadraticAlgebra.omega)
    rw [UnitalSubalgebra.polarBilin_restrictNorm] at h1 hx
    change n.polarBilin (f s) (f 1) = 0 at h1
    change n.polarBilin (f s) (f QuadraticAlgebra.omega) = 0 at hx
    rw [hf1] at h1
    rw [hfw] at hx
    rw [detect h1 hx, map_zero]
  refine ⟨hreg, fun z hz => hreg z fun t => ?_⟩
  exact (QuadraticMap.polar_comm (D.restrictNorm n) _ _).trans (hz t)

private theorem nondegenerate_restricted (D : UnitalSubalgebra k C)
    (hD : FieldNormConditions (D.restrictNorm n)) :
    (LinearMap.BilinForm.restrict n.polarBilin D.toSubmodule).Nondegenerate := by
  convert hD.nondegenerate using 1
  ext x y
  exact (UnitalSubalgebra.polarBilin_restrictNorm D n x y).symm

theorem nonarchimedeanSplit : NonarchimedeanSplit.{u,v} := by
  intro F _ _ _ _ C _ _ _ _ n hn
  by_cases hi : isotropic n
  · exact Peirce.isotropic_field_split hn hi
  exfalso
  have ⟨hN, hDim⟩ := (octonion_norm_iff_field n).mp hn
  letI := hN.finite
  obtain ⟨D, haD, hcD, hEt, hDdim, hD⟩ := exists_quadratic_subalgebra hN hDim
  obtain ⟨a, ha, haN⟩ := exists_norm_ne_zero_orthogonal hN D.toSubmodule
    (nondegenerate_restricted D hD) (by change finrank F D < finrank F C; rw [hDdim, hDim]; decide)
  obtain ⟨B, hBsum, σ, hσ, _, haB, e, hCSA, hBdim, hDeg, _, hNrd, _⟩ :=
    orthogonal_quaternion_model hN hD ha haN haD hcD hEt hDdim
  obtain ⟨_, _, _, _, ⟨B', hB'sum, hB'norm⟩, _, _, _⟩ := orthogonal_doubling hN hD ha haN
  have hBB' : B = B' := by
    apply SetLike.ext
    intro x
    change x ∈ B.toSubmodule ↔ x ∈ B'.toSubmodule
    rw [hBsum, hB'sum]
  have hBN : FieldNormConditions (B.restrictNorm n) := hBB'.symm ▸ hB'norm
  letI : Ring B := associativeSubalgebraRing B haB
  letI : Algebra F B := Algebra.ofModule (R := F) (A := B) smul_mul_assoc mul_smul_comm
  have hUnit (x : B) : IsUnit x ∨ x = 0 := by
    by_cases hx : x = 0
    · exact Or.inr hx
    left
    apply (reducedNorm_ne_zero_iff_isUnit hCSA x).mp
    rw [← hNrd]
    intro hxnorm
    exact hi ⟨x, fun H => hx (Subtype.ext H), hxnorm⟩
  letI : Nontrivial B := hBN.nontrivial
  letI : DivisionRing B := DivisionRing.ofIsUnitOrEqZero hUnit
  obtain ⟨c, hc, hcN⟩ := exists_norm_ne_zero_orthogonal hN B.toSubmodule
    (nondegenerate_restricted B hBN) (by change finrank F B < finrank F C; rw [hBdim, hDim]; decide)
  obtain ⟨x, hx⟩ := localQuaternionNormSurjective (B := B) hCSA hDeg (-n c) (neg_ne_zero.mpr hcN)
  obtain ⟨_, _, hdisj, _, _, _, hdoubling, _⟩ := orthogonal_doubling hN hBN hc hcN
  apply hi
  have hzero := hdoubling (x : B) 1
  change n (((x : B) : C) + (1 : C) * c) =
    n ((x : B) : C) - (-n c) * n (1 : C) at hzero
  rw [one_mul, hNrd, hx, field_norm_one hN, mul_one, sub_self] at hzero
  refine ⟨_, ?_, hzero⟩
  intro hz
  have hcEq : c = -((x : B) : C) := eq_neg_of_add_eq_zero_right hz
  have hcB : c ∈ B.toSubmodule := hcEq.symm ▸ B.toSubmodule.neg_mem (x : B).property
  have hcM : c ∈ B.rightMultiple c :=
    UnitalSubalgebra.mem_rightMultiple.mpr ⟨1, by simp⟩
  have hcz : c = 0 := by
    simpa using hdisj.le_bot (show c ∈ B.toSubmodule ⊓ B.rightMultiple c from ⟨hcB, hcM⟩)
  exact hcN (by simp [hcz])

end LocalSplitting

theorem finiteCompletionSplit : FiniteCompletionSplit.{u,v,w} := by
  intro k _ D p C _ _ _ _ n hn
  exact nonarchimedeanSplit hn

section RealFrameAlgebra

open Module

variable {C : Type v} [NonAssocRing C] [Module ℝ C]
    [IsScalarTower ℝ C C] [SMulCommClass ℝ C C] {n : QuadraticForm ℝ C}

private structure UnitDouble (n : QuadraticForm ℝ C)
    (D : UnitalSubalgebra ℝ C) (a : C) where
  algebra : UnitalSubalgebra ℝ C
  fieldNorm : FieldNormConditions (algebra.restrictNorm n)
  coordinates : (D × D) ≃ₗ[ℝ] algebra
  apply_coordinates (x y : D) : (coordinates (x, y) : C) = (x : C) + (y : C) * a
  coordinates_mul (x y u v : D) :
    coordinates (x, y) * coordinates (u, v) =
      coordinates (x * u - conjugate (D.restrictNorm n) v * y,
        v * x + y * conjugate (D.restrictNorm n) u)
  coordinates_norm (x y : D) : n (coordinates (x, y) : C) = n (x : C) + n (y : C)

open private mem_doubling_sum from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OrthogonalDoubling

private def unitDouble (hn : FieldNormConditions n) (D : UnitalSubalgebra ℝ C)
    (hD : FieldNormConditions (D.restrictNorm n)) (a : C)
    (ha : a ∈ D.toSubmodule.orthogonalBilin n.polarBilin) (hna : n a = 1) :
    UnitDouble n D a := by
  have ha₀ : n a ≠ 0 := hna.trans_ne one_ne_zero
  choose E hE hEN using (orthogonal_doubling hn hD ha ha₀).2.2.2.2.1
  obtain ⟨_, _, hdisj, hInj, _, hMul, hNorm, _⟩ := orthogonal_doubling hn hD ha ha₀
  let L : D × D →ₗ[ℝ] C := (SMulMemClass.subtype D).coprod
    (((LinearMap.mul ℝ C).flip a).comp (SMulMemClass.subtype D))
  have hL (x y : D) : L (x,y) = (x : C) + (y : C) * a := rfl
  have hmem (p : D × D) : L p ∈ E.toSubmodule := by
    rcases p with ⟨x,y⟩
    rw [hE, hL]
    exact mem_doubling_sum.mpr ⟨x, y, rfl⟩
  let M : D × D →ₗ[ℝ] E := L.codRestrict E.toSubmodule hmem
  have hM (x y : D) : (M (x, y) : C) = (x : C) + (y : C) * a := rfl
  have hM_inj : Function.Injective M := by
    apply (injective_iff_map_eq_zero M).mpr
    rintro ⟨x,y⟩ H
    have H' := congrArg Subtype.val H
    change (x : C) + (y : C) * a = 0 at H'
    have hy : (y : C) * a ∈ D.rightMultiple a := UnitalSubalgebra.mem_rightMultiple.mpr ⟨y, rfl⟩
    have he : (x : C) = -((y : C) * a) := eq_neg_of_add_eq_zero_left H'
    have hx : (x : C) ∈ D.rightMultiple a := he ▸ (D.rightMultiple a).neg_mem hy
    have hx0 : (x : C) = 0 := by
      simpa using hdisj.le_bot (show (x : C) ∈ D.toSubmodule ⊓ D.rightMultiple a from ⟨x.property, hx⟩)
    have hy0 : y = 0 := hInj (by simpa [hx0] using H')
    exact Prod.ext (Subtype.ext hx0) hy0
  have hM_surj : Function.Surjective M := by
    rintro ⟨z,hz⟩
    change z ∈ E.toSubmodule at hz
    rw [hE] at hz
    obtain ⟨x,y,h⟩ := mem_doubling_sum.mp hz
    exact ⟨(x,y), Subtype.ext h⟩
  let F := LinearEquiv.ofBijective M ⟨hM_inj, hM_surj⟩
  refine ⟨E, hEN, F, hM, ?_, ?_⟩
  · intro x y u v
    apply Subtype.ext
    change ((x : C) + (y : C) * a) * ((u : C) + (v : C) * a) =
      ((x : C) * (u : C) - (conjugate (D.restrictNorm n) v : C) * (y : C)) +
        ((v : C) * (x : C) + (y : C) * (conjugate (D.restrictNorm n) u : C)) * a
    simpa only [hna, neg_smul, one_smul, sub_eq_add_neg,
      UnitalSubalgebra.coe_conjugate_restrictNorm] using hMul x y u v
  · intro x y
    change n ((x : C) + (y : C) * a) = _
    simpa only [hna, neg_mul, one_mul, sub_neg_eq_add] using hNorm x y

private structure RealCompositionIso (n : QuadraticForm ℝ C)
    (D E : UnitalSubalgebra ℝ C) where
  linear : D ≃ₗ[ℝ] E
  one : linear 1 = 1
  mul (x y : D) : linear (x * y) = linear x * linear y
  norm (x : D) : E.restrictNorm n (linear x) = D.restrictNorm n x

private theorem RealCompositionIso.conjugate {D E : UnitalSubalgebra ℝ C}
    (f : RealCompositionIso n D E) (x : D) :
    f.linear (conjugate (D.restrictNorm n) x) = conjugate (E.restrictNorm n) (f.linear x) := by
  have htr : compositionTrace (E.restrictNorm n) (f.linear x) = compositionTrace (D.restrictNorm n) x := by
    rw [compositionTrace_apply, compositionTrace_apply, ← f.one]
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← f.linear.map_add, f.norm]
  rw [conjugate_apply, conjugate_apply, htr, map_sub, map_smul, f.one]

private theorem UnitDouble.coordinates_one {D : UnitalSubalgebra ℝ C} {a : C}
    (P : UnitDouble n D a) : P.coordinates (1,0) = 1 := by
  apply Subtype.ext
  rw [P.apply_coordinates]
  change (1 : C) + 0 * a = 1
  simp

private def UnitDouble.compare {D E : UnitalSubalgebra ℝ C} {a b : C}
    (P : UnitDouble n D a) (Q : UnitDouble n E b) (f : RealCompositionIso n D E) :
    RealCompositionIso n P.algebra Q.algebra := by
  let F := (P.coordinates.symm.trans (f.linear.prodCongr f.linear)).trans Q.coordinates
  have hF (x y : D) : F (P.coordinates (x,y)) = Q.coordinates (f.linear x, f.linear y) := by
    simp [F]
  refine ⟨F, ?_, ?_, ?_⟩
  · simp only [← P.coordinates_one, hF, f.one, map_zero, Q.coordinates_one]
  · intro a b
    obtain ⟨⟨x,y⟩,rfl⟩ := P.coordinates.surjective a
    obtain ⟨⟨u,v⟩,rfl⟩ := P.coordinates.surjective b
    simp only [P.coordinates_mul, Q.coordinates_mul, hF, map_add, map_sub, f.mul, f.conjugate]
  · intro a
    obtain ⟨⟨x,y⟩,rfl⟩ := P.coordinates.surjective a
    rw [hF, UnitalSubalgebra.restrictNorm_apply, Q.coordinates_norm,
      UnitalSubalgebra.restrictNorm_apply, P.coordinates_norm]
    exact congrArg₂ (· + ·) (f.norm x) (f.norm y)

private theorem UnitDouble.compare_coordinates {D E : UnitalSubalgebra ℝ C} {a b : C}
    (P : UnitDouble n D a) (Q : UnitDouble n E b) (f : RealCompositionIso n D E) (x y : D) :
    (P.compare Q f).linear (P.coordinates (x,y)) = Q.coordinates (f.linear x, f.linear y) := by
  simp [UnitDouble.compare]

private theorem UnitDouble.finrank_algebra {D : UnitalSubalgebra ℝ C} {a : C}
    [FiniteDimensional ℝ C] (P : UnitDouble n D a) :
    finrank ℝ P.algebra = finrank ℝ D + finrank ℝ D := by
  letI : Module.Finite ℝ D := by
    change Module.Finite ℝ D.toSubmodule
    infer_instance
  rw [← P.coordinates.finrank_eq, Module.finrank_prod]

private def scalarSubalgebra (C : Type v) [NonAssocRing C] [Module ℝ C]
    [IsScalarTower ℝ C C] [SMulCommClass ℝ C C] : UnitalSubalgebra ℝ C where
  toSubmodule := ℝ ∙ (1 : C)
  one_mem' := Submodule.mem_span_singleton_self _
  mul_mem' := by
    intro x y hx hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.mem_span_singleton.mpr ⟨r * s, by simp [smul_smul, mul_comm r s]⟩

private theorem positiveSubalgebra_fieldNorm (hn : FieldNormConditions n)
    (hp : ∀ x : C, x ≠ 0 → 0 < n x) (D : UnitalSubalgebra ℝ C) :
    FieldNormConditions (D.restrictNorm n) := by
  letI := hn.finite
  letI := hn.nontrivial
  have hfin : Module.Finite ℝ D := by
    change Module.Finite ℝ D.toSubmodule
    infer_instance
  have hreg (x : D) (hx : (D.restrictNorm n).polarBilin x x = 0) : x = 0 := by
    rw [UnitalSubalgebra.polarBilin_restrictNorm, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self] at hx
    apply Subtype.ext
    by_contra h
    simp only [two_nsmul] at hx
    exact (add_pos (hp x h) (hp x h)).ne' hx
  exact ⟨hfin, ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x : D => (x : C)) h)⟩⟩,
    ⟨fun x hx => hreg x (hx x), fun x hx => hreg x (hx x)⟩,
    fun x y => hn.multiplicative (x : C) (y : C)⟩

private structure RealOctonionFrame (n : QuadraticForm ℝ C) where
  a : C
  b : C
  c : C
  norm_a : n a = 1
  norm_b : n b = 1
  norm_c : n c = 1
  orth_one_a : n.polarBilin 1 a = 0
  orth_one_b : n.polarBilin 1 b = 0
  orth_a_b : n.polarBilin a b = 0
  orth_one_c : n.polarBilin 1 c = 0
  orth_a_c : n.polarBilin a c = 0
  orth_b_c : n.polarBilin b c = 0
  orth_ab_c : n.polarBilin (a * b) c = 0

variable (hn : FieldNormConditions n) (hp : ∀ x : C, x ≠ 0 → 0 < n x)
    (p : RealOctonionFrame n)

private def RealOctonionFrame.firstDouble : UnitDouble n (scalarSubalgebra C) p.a :=
  unitDouble hn (scalarSubalgebra C) (positiveSubalgebra_fieldNorm hn hp _) p.a
    (by
      intro x hx
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [p.orth_one_a]) p.norm_a

private theorem RealOctonionFrame.firstDouble_repr (z : (p.firstDouble hn hp).algebra) :
    ∃ r s : ℝ, (z : C) = r • (1 : C) + s • p.a := by
  obtain ⟨⟨x, y⟩, rfl⟩ := (p.firstDouble hn hp).coordinates.surjective z
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x.property
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp y.property
  refine ⟨r, s, ?_⟩
  rw [(p.firstDouble hn hp).apply_coordinates, ← hr, ← hs, smul_mul_assoc, one_mul]

private def RealOctonionFrame.secondDouble : UnitDouble n (p.firstDouble hn hp).algebra p.b :=
  unitDouble hn _ (p.firstDouble hn hp).fieldNorm p.b
    (by
      intro x hx
      obtain ⟨r,s,eq⟩ := p.firstDouble_repr hn hp ⟨x,hx⟩
      change x = r • (1 : C) + s • p.a at eq
      rw [eq]
      simp [p.orth_one_b, p.orth_a_b]) p.norm_b

private def RealOctonionFrame.thirdDouble : UnitDouble n (p.secondDouble hn hp).algebra p.c :=
  unitDouble hn _ (p.secondDouble hn hp).fieldNorm p.c
    (by
      intro x hx
      obtain ⟨⟨y,z⟩,eq⟩ := (p.secondDouble hn hp).coordinates.surjective ⟨x,hx⟩
      have H := congrArg Subtype.val eq
      change ((p.secondDouble hn hp).coordinates (y,z) : C) = x at H
      obtain ⟨r,s,hr⟩ := p.firstDouble_repr hn hp y
      obtain ⟨t,u,ht⟩ := p.firstDouble_repr hn hp z
      rw [← H, (p.secondDouble hn hp).apply_coordinates, hr, ht, add_mul,
        smul_mul_assoc, smul_mul_assoc, one_mul]
      simp [p.orth_one_c, p.orth_a_c, p.orth_b_c, p.orth_ab_c]) p.norm_c

private theorem RealOctonionFrame.thirdDouble_top (hDim : finrank ℝ C = 8) :
    (p.thirdDouble hn hp).algebra.toSubmodule = ⊤ := by
  letI := hn.finite
  letI := hn.nontrivial
  apply Submodule.eq_top_of_finrank_eq
  change finrank ℝ (p.thirdDouble hn hp).algebra = finrank ℝ C
  have hScalar : finrank ℝ (scalarSubalgebra C) = 1 := finrank_span_singleton one_ne_zero
  have h₁ := (p.firstDouble hn hp).finrank_algebra
  have h₂ := (p.secondDouble hn hp).finrank_algebra
  have h₃ := (p.thirdDouble hn hp).finrank_algebra
  omega

private def UnitDouble.include {D : UnitalSubalgebra ℝ C} {a : C} (P : UnitDouble n D a)
    (x : D) : P.algebra := P.coordinates (x, 0)

private theorem UnitDouble.coe_include {D : UnitalSubalgebra ℝ C} {a : C}
    (P : UnitDouble n D a) (x : D) : (P.include x : C) = (x : C) := by
  simp [UnitDouble.include, P.apply_coordinates]

private def UnitDouble.generator {D : UnitalSubalgebra ℝ C} {a : C} (P : UnitDouble n D a) :
    P.algebra := P.coordinates (0, 1)

private theorem UnitDouble.coe_generator {D : UnitalSubalgebra ℝ C} {a : C}
    (P : UnitDouble n D a) : (P.generator : C) = a := by
  simp [UnitDouble.generator, P.apply_coordinates]

private theorem UnitDouble.compare_include {D E : UnitalSubalgebra ℝ C} {a b : C}
    (P : UnitDouble n D a) (Q : UnitDouble n E b) (e : RealCompositionIso n D E) (x : D) :
    (P.compare Q e).linear (P.include x) = Q.include (e.linear x) := by
  simp [UnitDouble.include, P.compare_coordinates]

private theorem UnitDouble.compare_generator {D E : UnitalSubalgebra ℝ C} {a b : C}
    (P : UnitDouble n D a) (Q : UnitDouble n E b) (e : RealCompositionIso n D E) :
    (P.compare Q e).linear P.generator = Q.generator := by
  simp [UnitDouble.generator, P.compare_coordinates, e.one]

include hn hp in
private theorem RealOctonionFrame.exists_automorphism (hDim : finrank ℝ C = 8)
    (q : RealOctonionFrame n) :
    ∃ f : C ≃ₗ[ℝ] C, f 1 = 1 ∧ (∀ x y, f (x*y) = f x * f y) ∧
      (∀ x, n (f x) = n x) ∧ f p.a = q.a ∧ f p.b = q.b ∧ f p.c = q.c := by
  let e₀ : RealCompositionIso n (scalarSubalgebra C) (scalarSubalgebra C) :=
    ⟨LinearEquiv.refl _ _, rfl, fun _ _ => rfl, fun _ => rfl⟩
  let P₁ := p.firstDouble hn hp
  let P₂ := p.secondDouble hn hp
  let P₃ := p.thirdDouble hn hp
  let Q₁ := q.firstDouble hn hp
  let Q₂ := q.secondDouble hn hp
  let Q₃ := q.thirdDouble hn hp
  let e₁ := P₁.compare Q₁ e₀
  let e₂ := P₂.compare Q₂ e₁
  let e₃ := P₃.compare Q₃ e₂
  let i : P₃.algebra ≃ₗ[ℝ] C := LinearEquiv.ofTop _ (p.thirdDouble_top hn hp hDim)
  let j : Q₃.algebra ≃ₗ[ℝ] C := LinearEquiv.ofTop _ (q.thirdDouble_top hn hp hDim)
  let f := (i.symm.trans e₃.linear).trans j
  have hOn (x : P₃.algebra) : f (x : C) = (e₃.linear x : C) := by
    change j (e₃.linear (i.symm (i x))) = j (e₃.linear x)
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · have h := hOn 1
    rw [e₃.one] at h
    exact h
  · intro x y
    obtain ⟨x, rfl⟩ := i.surjective x
    obtain ⟨y, rfl⟩ := i.surjective y
    change f ((x*y : P₃.algebra) : C) = f (x : C) * f (y : C)
    rw [hOn, hOn, hOn, e₃.mul]
    rfl
  · intro x
    obtain ⟨x, rfl⟩ := i.surjective x
    change n (f (x : C)) = n (x : C)
    rw [hOn]
    exact e₃.norm x
  · have ha := hOn (P₃.include (P₂.include P₁.generator))
    have hb := hOn (P₃.include P₂.generator)
    have hc := hOn P₃.generator
    exact ⟨by
      simpa only [P₃.coe_include, P₂.coe_include, P₁.coe_generator, e₃,
        P₃.compare_include, e₂, P₂.compare_include, e₁, P₁.compare_generator,
        Q₃.coe_include, Q₂.coe_include, Q₁.coe_generator] using ha,
      by
        simpa only [P₃.coe_include, P₂.coe_generator, e₃, P₃.compare_include,
          e₂, P₂.compare_generator, Q₃.coe_include, Q₂.coe_generator] using hb,
      by simpa only [P₃.coe_generator, e₃, P₃.compare_generator, Q₃.coe_generator] using hc⟩

private theorem UnitDouble.linearMap_eq {D : UnitalSubalgebra ℝ C} {a : C}
    (P : UnitDouble n D a) {f g : C →ₗ[ℝ] C}
    (hf : ∀ x y, f (x*y) = f x * f y) (hg : ∀ x y, g (x*y) = g x * g y)
    (hD : ∀ x : D, f (x : C) = g (x : C)) (ha : f a = g a) (x : P.algebra) :
    f (x : C) = g (x : C) := by
  obtain ⟨⟨x,y⟩,rfl⟩ := P.coordinates.surjective x
  rw [P.apply_coordinates, map_add, map_add, hf, hg, hD x, hD y, ha]

include hn hp in
private theorem RealOctonionFrame.automorphism_ext (hDim : finrank ℝ C = 8)
    {f g : C ≃ₗ[ℝ] C} (hf₁ : f 1 = 1) (hg₁ : g 1 = 1)
    (hf : ∀ x y, f (x*y) = f x * f y) (hg : ∀ x y, g (x*y) = g x * g y)
    (ha : f p.a = g p.a) (hb : f p.b = g p.b) (hc : f p.c = g p.c) : f = g := by
  let P₁ := p.firstDouble hn hp
  let P₂ := p.secondDouble hn hp
  let P₃ := p.thirdDouble hn hp
  have H₀ (x : scalarSubalgebra C) : f (x : C) = g (x : C) := by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x.property
    simp [← hr, hf₁, hg₁]
  have H₁ := P₁.linearMap_eq (f := f.toLinearMap) (g := g.toLinearMap) hf hg H₀ ha
  have H₂ := P₂.linearMap_eq hf hg H₁ hb
  have H₃ := P₃.linearMap_eq hf hg H₂ hc
  ext x
  apply H₃ ⟨x, ?_⟩
  change x ∈ P₃.algebra.toSubmodule
  rw [p.thirdDouble_top hn hp hDim]
  exact Submodule.mem_top

end RealFrameAlgebra

section OrthogonalChoices

open Set Module Topology
open scoped InnerProductSpace

variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]

private def orthogonalUnitVectors {r : ℕ} (w : Fin r → C) : Set C :=
  {x | ‖x‖ = 1 ∧ ∀ i, ⟪w i, x⟫_ℝ = 0}

private theorem orthogonalUnitVectors_connected {r : ℕ} (w : Fin r → C)
    (hr : r + 1 < finrank ℝ C) : IsConnected (orthogonalUnitVectors w) := by
  classical
  let W := Submodule.span ℝ (Set.range w)
  have hW : finrank ℝ W ≤ r := by
    letI := Fintype.ofFinite (Set.range w)
    calc
      finrank ℝ W ≤ Fintype.card (Set.range w) := by
        simpa only [Set.toFinset_card] using finrank_span_le_card (R := ℝ) (Set.range w)
      _ ≤ r := by simpa using (Fintype.card_range_le w)
  have hdim : 1 < finrank ℝ Wᗮ := by
    have h := W.finrank_add_finrank_orthogonal
    omega
  have h := isConnected_sphere (one_lt_rank_of_one_lt_finrank hdim) (0 : Wᗮ) zero_le_one
  have he : (fun x : Wᗮ => (x : C)) '' Metric.sphere 0 1 = orthogonalUnitVectors w := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hnorm : ‖(y : C)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
      exact ⟨hnorm, fun i => W.inner_right_of_mem_orthogonal
        (Submodule.subset_span ⟨i, rfl⟩) y.property⟩
    · rintro ⟨hx, horth⟩
      have hxW : x ∈ Wᗮ := by
        rw [W.mem_orthogonal]
        intro y hy
        let L : C →ₗ[ℝ] ℝ := (innerₗ C x)
        have hle : W ≤ L.ker := Submodule.span_le.mpr (by
          rintro _ ⟨i, rfl⟩
          change ⟪x, w i⟫_ℝ = 0
          exact (real_inner_comm _ _).trans (horth i))
        exact (real_inner_comm _ _).trans (hle hy)
      exact ⟨⟨x, hxW⟩, by simpa [Metric.mem_sphere, dist_zero_right] using hx, rfl⟩
  rw [← he]
  exact h.image Subtype.val continuous_subtype_val.continuousOn

private abbrev OrthogonalChoices {X : Type*} {r : ℕ} (w : X → Fin r → C) :=
  {p : X × C // p.2 ∈ orthogonalUnitVectors (w p.1)}

private theorem orthogonalChoices_compact_connected {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [ConnectedSpace X] [T2Space X] {r : ℕ} (w : X → Fin r → C)
    (hw : ∀ i, Continuous (fun x => w x i)) (hr : r + 1 < finrank ℝ C) :
    CompactSpace (OrthogonalChoices w) ∧ ConnectedSpace (OrthogonalChoices w) := by
  let Y : Set (X × C) := {p | p.2 ∈ orthogonalUnitVectors (w p.1)}
  have hY : IsClosed Y := by
    have hN : IsClosed {p : X × C | ‖p.2‖ = 1} :=
      isClosed_eq (continuous_norm.comp continuous_snd) continuous_const
    have hO : IsClosed (⋂ i, {p : X × C | ⟪w p.1 i, p.2⟫_ℝ = 0}) :=
      isClosed_iInter fun i => isClosed_eq ((hw i).comp continuous_fst |>.inner continuous_snd)
        continuous_const
    convert hN.inter hO using 1
    ext p
    simp [Y, orthogonalUnitVectors]
  have hc : CompactSpace (OrthogonalChoices w) := by
    apply isCompact_iff_compactSpace.mp
    apply (isCompact_univ.prod (isCompact_sphere (0 : C) 1)).of_isClosed_subset hY
    rintro ⟨x,y⟩ ⟨hy,-⟩
    exact ⟨mem_univ _, by simpa [Metric.mem_sphere, dist_zero_right] using hy⟩
  letI := hc
  refine ⟨hc, ?_⟩
  let f : OrthogonalChoices w → X := fun p => p.val.1
  have hf : Continuous f := continuous_fst.comp continuous_subtype_val
  have hF (x : X) : IsConnected (f ⁻¹' {x}) := by
    let g : orthogonalUnitVectors (w x) → OrthogonalChoices w := fun y => ⟨(x, y),y.property⟩
    have hg : Continuous g :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _
    have he : range g = f ⁻¹' {x} := by
      ext p
      constructor
      · rintro ⟨y, rfl⟩
        rfl
      · rintro hp
        obtain ⟨⟨z,y⟩,hy⟩ := p
        change z = x at hp
        subst z
        exact ⟨⟨y,hy⟩, rfl⟩
    letI := isConnected_iff_connectedSpace.mp (orthogonalUnitVectors_connected (w x) hr)
    rw [← he]
    exact isConnected_range hg
  have hsurj : Function.Surjective f := fun x => (hF x).1
  have hq : IsCoinducing f := by
    apply IsCoinducing.of_isClosed_preimage_iff_isClosed
    intro s
    constructor
    · intro hs
      rw [← image_preimage_eq s hsurj]
      exact hf.isClosedMap (f ⁻¹' s) hs
    · exact fun hs => hs.preimage hf
  have H := hq.isConnected_preimage_of_isClosed hF (t := univ) isClosed_univ isConnected_univ
  apply (connectedSpace_iff_univ).mpr
  simpa only [preimage_univ] using H

end OrthogonalChoices

section RealTopology

open Module
open private octonion_norm_comp_equiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.Adjoints

variable {C : Type v} [NonAssocRing C] [Module ℝ C]
    [IsScalarTower ℝ C C] [SMulCommClass ℝ C C] {n : QuadraticForm ℝ C}

private theorem realNorm_preserved (hn : OctonionNormConditions n) (f : C ≃ₗ[ℝ] C)
    (hm : ∀ x y, f (x * y) = f x * f y) (x : C) : n (f x) = n x :=
  DFunLike.congr_fun (octonion_norm_unique (octonion_norm_comp_equiv hn f hm) hn).1 x

private theorem realNorm_sq (hp : ∀ x : C, x ≠ 0 → 0 < n x) (x : C) :
    letI := (realNormCore n hp).toNormedAddCommGroup
    ‖x‖ ^ 2 = n x := by
  change Real.sqrt (n.associated x x) ^ 2 = n x
  rw [show n.associated x x = n x from QuadraticMap.associated_eq_self_apply ℝ n x]
  refine Real.sq_sqrt ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (hp x hx).le

open Set in
theorem realCompact : RealCompact.{v} := by
  intro C _ _ _ _ n hn hp b
  letI := realNormCore n hp
  letI := (realNormCore n hp).toNormedAddCommGroup
  letI : InnerProductSpace ℝ C := InnerProductSpace.ofCore inferInstance
  letI := hn.finite
  let f (a : Fin 8 → C) : C →ₗ[ℝ] C := b.constr ℝ a
  have hf (a : Fin 8 → C) (i : Fin 8) : f a (b i) = a i := b.constr_basis ℝ a i
  have hcont (x : C) : Continuous (fun a => f a x) := by
    let L : (Fin 8 → C) →ₗ[ℝ] C := (LinearMap.applyₗ x).comp (b.constr ℝ).toLinearMap
    exact L.continuous_of_finiteDimensional
  have hncont : Continuous n := by
    have H (x : C) : n x = ‖x‖ ^ 2 := (realNorm_sq hp x).symm
    rw [show (⇑n) = fun x : C => ‖x‖ ^ 2 from funext H]
    exact continuous_norm.pow 2
  let P : C →L[ℝ] C →L[ℝ] C := (LinearMap.mul ℝ C).toContinuousBilinearMap
  have hmulcont (x y : C) : Continuous (fun a => f a x * f a y) :=
    (P.continuous.comp (hcont x)).clm_apply (hcont y)
  let S : Set (Fin 8 → C) := {a | f a 1 = 1 ∧
    (∀ x y, f a (x * y) = f a x * f a y) ∧ ∀ x, n (f a x) = n x}
  have hS : IsClosed S := by
    have h1 : IsClosed {a | f a 1 = 1} := isClosed_eq (hcont _) continuous_const
    have h2 : IsClosed (⋂ x : C, ⋂ y : C, {a | f a (x * y) = f a x * f a y}) :=
      isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_eq (hcont _) (hmulcont _ _)
    have h3 : IsClosed (⋂ x : C, {a | n (f a x) = n x}) :=
      isClosed_iInter fun x => isClosed_eq (hncont.comp (hcont x)) continuous_const
    convert h1.inter (h2.inter h3) using 1
    ext a
    simp [S]
  have heq : realAutomorphismColumns b = S := by
    ext a
    constructor
    · rintro ⟨E, hE, h1, h2⟩
      have h : f a = E.toLinearMap := b.ext fun i => (hf a i).trans (hE i).symm
      change f a 1 = 1 ∧ (∀ x y, f a (x * y) = f a x * f a y) ∧ ∀ x, n (f a x) = n x
      rw [h]
      exact ⟨h1, h2, realNorm_preserved hn E h2⟩
    · rintro ⟨h1, h2, h3⟩
      have hInj : Function.Injective (f a) := by
        apply (injective_iff_map_eq_zero _).mpr
        intro x hx
        by_contra hx'
        have H := h3 x
        rw [hx, map_zero] at H
        exact (hp x hx').ne' H.symm
      let e := LinearEquiv.ofBijective (f a) ⟨hInj, LinearMap.injective_iff_surjective.mp hInj⟩
      exact ⟨e, hf a, h1, h2⟩
  rw [heq]
  let T := Set.pi Set.univ (fun i => Metric.sphere (0 : C) ‖b i‖)
  have hT : IsCompact T := isCompact_univ_pi fun i => isCompact_sphere _ _
  apply hT.of_isClosed_subset hS
  rintro a ⟨_, _, h⟩ i -
  have H := h (b i)
  rw [hf] at H
  rw [← realNorm_sq hp (a i), ← realNorm_sq hp (b i)] at H
  rw [Metric.mem_sphere, dist_zero_right]
  simpa only [abs_of_nonneg (norm_nonneg _)] using (sq_eq_sq_iff_abs_eq_abs _ _).mp H

open scoped InnerProductSpace
open Topology in
theorem realConnected : RealConnected.{v} := by
  classical
  intro C _ _ _ _ n hn hp b₀
  letI := realNormCore n hp
  letI := (realNormCore n hp).toNormedAddCommGroup
  letI : InnerProductSpace ℝ C := InnerProductSpace.ofCore inferInstance
  letI := hn.finite
  obtain ⟨hN, hDim⟩ := (octonion_norm_iff_field n).mp hn
  let w₁ : Unit → Fin 1 → C := fun _ => ![1]
  let X₁ := OrthogonalChoices w₁
  obtain ⟨h₁c, h₁n⟩ := orthogonalChoices_compact_connected w₁ (fun _ => continuous_const)
    (by rw [hDim]; decide)
  letI : CompactSpace X₁ := h₁c
  letI : ConnectedSpace X₁ := h₁n
  let a₁ (x : X₁) : C := x.val.2
  have ha₁ : Continuous a₁ := continuous_snd.comp continuous_subtype_val
  let w₂ : X₁ → Fin 2 → C := fun x => ![1, a₁ x]
  let X₂ := OrthogonalChoices w₂
  obtain ⟨h₂c, h₂n⟩ := orthogonalChoices_compact_connected w₂ (by
    intro i
    fin_cases i
    · exact continuous_const
    · exact ha₁) (by rw [hDim]; decide)
  letI : CompactSpace X₂ := h₂c
  letI : ConnectedSpace X₂ := h₂n
  let a₂ (y : X₂) : C := a₁ y.val.1
  let b₂ (y : X₂) : C := y.val.2
  have ha₂ : Continuous a₂ := ha₁.comp (continuous_fst.comp continuous_subtype_val)
  have hb₂ : Continuous b₂ := continuous_snd.comp continuous_subtype_val
  let P : C →L[ℝ] C →L[ℝ] C := (LinearMap.mul ℝ C).toContinuousBilinearMap
  let w₃ : X₂ → Fin 4 → C := fun y => ![1, a₂ y, b₂ y, a₂ y * b₂ y]
  let X₃ := OrthogonalChoices w₃
  obtain ⟨_, h₃n⟩ := orthogonalChoices_compact_connected w₃ (by
    intro i
    fin_cases i
    · exact continuous_const
    · exact ha₂
    · exact hb₂
    · exact (P.continuous.comp ha₂).clm_apply hb₂) (by rw [hDim]; decide)
  letI : ConnectedSpace X₃ := h₃n
  let a₃ (z : X₃) : C := a₂ z.val.1
  let b₃ (z : X₃) : C := b₂ z.val.1
  let c₃ (z : X₃) : C := z.val.2
  have pol (x y : C) (h : ⟪x,y⟫_ℝ = 0) : n.polarBilin x y = 0 := by
    have H := congrArg (fun L : C →ₗ[ℝ] C →ₗ[ℝ] ℝ => L x y)
      (QuadraticMap.two_nsmul_associated ℝ n)
    simp only [two_nsmul, LinearMap.add_apply] at H
    change ⟪x,y⟫_ℝ + ⟪x,y⟫_ℝ = n.polarBilin x y at H
    simpa only [h, zero_add] using H.symm
  have norm_one (x : C) (hx : ‖x‖ = 1) : n x = 1 := by
    rw [← realNorm_sq hp x, hx, one_pow]
  let frame (z : X₃) : RealOctonionFrame n :=
    { a := a₃ z
      b := b₃ z
      c := c₃ z
      norm_a := norm_one _ z.val.1.val.1.property.1
      norm_b := norm_one _ z.val.1.property.1
      norm_c := norm_one _ z.property.1
      orth_one_a := pol _ _ (z.val.1.val.1.property.2 0)
      orth_one_b := pol _ _ (z.val.1.property.2 0)
      orth_a_b := pol _ _ (z.val.1.property.2 1)
      orth_one_c := pol _ _ (z.property.2 0)
      orth_a_c := pol _ _ (z.property.2 1)
      orth_b_c := pol _ _ (z.property.2 2)
      orth_ab_c := pol _ _ (z.property.2 3) }
  let z₀ : X₃ := Classical.choice inferInstance
  let p := frame z₀
  let X := realAutomorphismColumns b₀
  letI : CompactSpace X := isCompact_iff_compactSpace.mp (realCompact hn hp b₀)
  let f (u : X) : C ≃ₗ[ℝ] C := Classical.choose u.property
  have hf (u : X) : (∀ i, f u (b₀ i) = u.val i) ∧ f u 1 = 1 ∧
      (∀ x y, f u (x * y) = f u x * f u y) ∧ ∀ x, n (f u x) = n x := by
    obtain ⟨hb, h₁, hm⟩ := Classical.choose_spec u.property
    exact ⟨hb, h₁, hm, realNorm_preserved hn (f u) hm⟩
  have hfcont (x : C) : Continuous (fun u : X => f u x) := by
    let L : (Fin 8 → C) →ₗ[ℝ] C := (LinearMap.applyₗ x).comp (b₀.constr ℝ).toLinearMap
    have hL (u : X) : L u.val = f u x := by
      have h : b₀.constr ℝ u.val = (f u).toLinearMap :=
        b₀.ext fun i => (b₀.constr_basis ℝ u.val i).trans ((hf u).1 i).symm
      exact LinearMap.congr_fun h x
    have hv : Continuous (fun u : X => (u : Fin 8 → C)) := continuous_subtype_val
    rw [← funext hL]
    exact L.continuous_of_finiteDimensional.comp hv
  have f_norm (u : X) (x : C) : ‖f u x‖ = ‖x‖ := by
    have H := (hf u).2.2.2 x
    rw [← realNorm_sq hp, ← realNorm_sq hp] at H
    simpa only [abs_of_nonneg (norm_nonneg _)] using (sq_eq_sq_iff_abs_eq_abs _ _).mp H
  have f_inner (u : X) (x y : C) : ⟪f u x, f u y⟫_ℝ = ⟪x,y⟫_ℝ := by
    have E : n.comp (f u).toLinearMap = n := QuadraticMap.ext (hf u).2.2.2
    have H := congrArg (fun q : QuadraticForm ℝ C => q.associated x y) E
    rw [QuadraticMap.associated_comp] at H
    exact H
  let e₁ (u : X) : X₁ := ⟨((),f u p.a), by
    refine ⟨(f_norm u _).trans z₀.val.1.val.1.property.1, ?_⟩
    intro i
    fin_cases i
    change ⟪(1 : C), f u p.a⟫_ℝ = 0
    rw [← (hf u).2.1, f_inner]
    exact z₀.val.1.val.1.property.2 0⟩
  let e₂ (u : X) : X₂ := ⟨(e₁ u,f u p.b), by
    refine ⟨(f_norm u _).trans z₀.val.1.property.1, ?_⟩
    intro i
    fin_cases i
    · change ⟪(1 : C), f u p.b⟫_ℝ = 0
      rw [← (hf u).2.1, f_inner]
      exact z₀.val.1.property.2 0
    · change ⟪f u p.a, f u p.b⟫_ℝ = 0
      rw [f_inner]
      exact z₀.val.1.property.2 1⟩
  let e₃ (u : X) : X₃ := ⟨(e₂ u,f u p.c), by
    refine ⟨(f_norm u _).trans z₀.property.1, ?_⟩
    intro i
    fin_cases i
    · change ⟪(1 : C), f u p.c⟫_ℝ = 0
      rw [← (hf u).2.1, f_inner]
      exact z₀.property.2 0
    · change ⟪f u p.a, f u p.c⟫_ℝ = 0
      rw [f_inner]
      exact z₀.property.2 1
    · change ⟪f u p.b, f u p.c⟫_ℝ = 0
      rw [f_inner]
      exact z₀.property.2 2
    · change ⟪f u p.a * f u p.b, f u p.c⟫_ℝ = 0
      rw [← (hf u).2.2.1, f_inner]
      exact z₀.property.2 3⟩
  have he₁ : Continuous e₁ := (continuous_const.prodMk (hfcont p.a)).subtype_mk _
  have he₂ : Continuous e₂ := (he₁.prodMk (hfcont p.b)).subtype_mk _
  have he₃ : Continuous e₃ := (he₂.prodMk (hfcont p.c)).subtype_mk _
  have hinj : Function.Injective e₃ := by
    intro u v eq
    have hEq : f u = f v := p.automorphism_ext hN hp hDim
      (hf u).2.1 (hf v).2.1 (hf u).2.2.1 (hf v).2.2.1
      (congrArg a₃ eq) (congrArg b₃ eq) (congrArg c₃ eq)
    apply Subtype.ext
    funext i
    rw [← (hf u).1 i, ← (hf v).1 i, hEq]
  have hsurj : Function.Surjective e₃ := by
    intro z
    obtain ⟨g, h₁, hm, _, ha, hb, hc⟩ := p.exists_automorphism hN hp hDim (frame z)
    let u : X := ⟨fun i => g (b₀ i), g, fun _ => rfl, h₁, hm⟩
    have hg : f u = g := by
      apply LinearEquiv.toLinearMap_injective
      apply b₀.ext
      intro i
      exact (hf u).1 i
    refine ⟨u, ?_⟩
    have heq₁ : e₁ u = z.val.1.val.1 := by
      apply Subtype.ext
      apply Prod.ext (Subsingleton.elim _ _)
      change f u p.a = a₃ z
      rwa [hg]
    have heq₂ : e₂ u = z.val.1 := by
      apply Subtype.ext
      apply Prod.ext heq₁
      change f u p.b = b₃ z
      rwa [hg]
    apply Subtype.ext
    apply Prod.ext heq₂
    change f u p.c = c₃ z
    rwa [hg]
  have H := isHomeomorph_iff_continuous_bijective.mpr ⟨he₃, hinj, hsurj⟩
  exact isConnected_iff_connectedSpace.mpr ((H.homeomorph e₃).connectedSpace_iff.mpr h₃n)

end RealTopology

section NormWeights

open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open WeightDecomposition
open LinearAlgebraicGroups.RationalRepresentations (trivialLinearMap)
open private linearMap_ext_weights from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition

theorem nontrivialNormCoactionSplit : NontrivialNormCoactionSplit.{u} := by
  classical
  intro k _ C _ _ _ _ n hn
  dsimp only
  intro ρ hρ hpres
  letI := hn.projective
  let M := IntegerCharacters.{u}
  let A := groupAlgebra k M
  apply Peirce.isotropic_field_split hn
  by_contra hi
  apply hρ
  apply linearMap_ext_weights ρ
  intro m v
  have hv := mem_weightSpace.mp v.property
  by_cases hm : m = 1
  · subst m
    simpa [trivialLinearMap, ← MonoidAlgebra.one_def] using hv
  have hsq : m * m ≠ 1 := by
    intro h
    apply hm
    apply ULift.ext
    have H := congrArg (fun a : M => Multiplicative.toAdd a.down) h
    change Multiplicative.toAdd m.down + Multiplicative.toAdd m.down = 0 at H
    change Multiplicative.toAdd m.down = 0
    omega
  have H := hpres (v : C)
  rw [hv, TensorProduct.comm_tmul, normBaseChange_tmul] at H
  have hcoeff :
      (MonoidAlgebra.single (m * m) (n (v : C)) : MonoidAlgebra k M) =
        MonoidAlgebra.single 1 (n (v : C)) := by
    change ((MonoidAlgebra.of k M m : MonoidAlgebra k M) * MonoidAlgebra.of k M m) *
       algebraMap k (MonoidAlgebra k M) (n (v : C)) = _ at H
    rw [← map_mul] at H
    simpa [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single] using H
  have hNv : n (v : C) = 0 := by
    have e := congrArg (fun f : MonoidAlgebra k M => f.coeff (m * m)) hcoeff
    simpa [hsq, Ne.symm hsq] using e
  have hv0 : (v : C) = 0 := by
    by_contra hnz
    exact hi ⟨v, hnz, hNv⟩
  simp [hv0]

end NormWeights

section Cocharacters

open AlgebraicGeometry CategoryTheory WithConv
open Composition.OctonionAutomorphismSpecification
open Specs (GroupScheme)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (matrixAction schemePoints)
open LinearAlgebraicGroups.RationalRepresentations
open private matrixActionEquiv matrixAction_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme
open private octonionAlgebra_preserves_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms

variable {k C : Type u} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C]

private def linearPointsInBasis {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : AutomorphismGroup k C) (b : Module.Basis ι k C) :
    (groupPointsFunctor k).obj A.generalLinear ≅ Specs.StandardGroups.generalLinearPoints k ι := by
  let E (S : CommAlgCat k) :=
    (A.linearPoints S).trans (matrixActionEquiv b S).symm
  refine NatIso.ofComponents (fun S => MulEquiv.toGrpIso (E S)) ?_
  intro S T f
  apply GrpCat.ext
  intro p
  change E T (((schemePoints k).obj A.generalLinear).map f p) =
    Matrix.GeneralLinearGroup.map f.hom.toRingHom (E S p)
  apply (matrixActionEquiv b T).injective
  apply Units.ext
  apply (b.baseChange T).ext
  intro i
  have H := A.scalarChange f p ((b.baseChange S) i)
  have HM := matrixAction_natural b f.hom (E S p) ((b.baseChange S) i)
  have hb : f.hom.toLinearMap.rTensor C ((b.baseChange S) i) = (b.baseChange T) i := by
    simp [Module.Basis.baseChange_apply]
  rw [hb] at H HM
  change f.hom.toLinearMap.rTensor C ((matrixActionEquiv b S (E S p)).val ((b.baseChange S) i)) =
    (matrixActionEquiv b T (Matrix.GeneralLinearGroup.map f.hom.toRingHom (E S p))).val
      ((b.baseChange T) i) at HM
  have he : matrixActionEquiv b S (E S p) = A.linearPoints S p :=
    (matrixActionEquiv b S).apply_symm_apply _
  rw [he] at HM
  have ht (q : ((schemePoints k).obj A.generalLinear).obj T) :
      matrixActionEquiv b T (E T q) = A.linearPoints T q :=
    (matrixActionEquiv b T).apply_symm_apply _
  rw [ht]
  exact H.trans HM

set_option maxRecDepth 1200 in
set_option maxHeartbeats 580000 in
theorem octonionSplitOfCocharacter : OctonionSplitOfCocharacter.{u} := by
  classical
  intro k C _ _ _ _ _ n hn A hc
  obtain ⟨c, test, t, ht⟩ := hc
  letI := hn.projective
  letI := hn.finite
  have hDim := ((octonion_norm_iff_field n).mp hn).2
  let b : Module.Basis (ULift.{u} (Fin 8)) k C :=
    (Module.finBasis k C).reindex ((finCongr hDim).trans Equiv.ulift.symm)
  let H := groupAlgebra k IntegerCharacters
  let G : AffineGroupCategory k := (affineHopfSpec k).obj (Opposite.op H)
  let e := hopfSpecPointIso H
  let L := A.generalLinear
  let l := linearPointsInBasis A b
  let f : Specs.RationalRepresentations.representation G L l := c ≫ A.inclusion
  obtain ⟨E, hE⟩ := representationCoactionComparison H b G L e l
  let ρ := E f
  let p (S : CommAlgCat k) (g : H →ₐ[k] S) :=
    ((schemePoints k).map c).app S (e.hom.app S (toConv g))
  have eval_eq (S : CommAlgCat k) (g : H →ₐ[k] S) (x : C) :
      TensorProduct.comm k C S (evaluate H ρ g x) =
        (A.subgroupPoints S (p S g)).val.val (1 ⊗ₜ[k] x) := by
    let F : C →ₗ[k] S ⊗[k] C :=
      (TensorProduct.comm k C S).toLinearMap.comp (evaluate H ρ g)
    let U : Module.End S (S ⊗[k] C) := (A.subgroupPoints S (p S g)).val.val
    let F' : C →ₗ[k] S ⊗[k] C := (U.restrictScalars k).comp (TensorProduct.mk k S C 1)
    suffices F = F' from DFunLike.congr_fun this x
    apply b.ext
    intro j
    have EVAL := evaluationComparison H b G L e l f ρ (hE f) S g j
    let m : Matrix.GeneralLinearGroup (ULift.{u} (Fin 8)) S :=
      l.hom.app S (((groupPointsFunctor k).map f).app S (e.hom.app S (toConv g)))
    have hm : (matrixActionEquiv b S m).val = U := by
      have hm' : m = (matrixActionEquiv b S).symm
          (A.linearPoints S (((schemePoints k).map A.inclusion).app S (p S g))) := by
        change l.hom.app S (((groupPointsFunctor k).map (c ≫ A.inclusion)).app S
          (e.hom.app S (toConv g))) = _
        rw [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
        rfl
      rw [hm', MulEquiv.apply_symm_apply, A.evaluatesInclusion]
    have hcoeff (i : ULift.{u} (Fin 8)) :
        m.val i j = (b.baseChange S).repr (U ((b.baseChange S) j)) i := by
      rw [← hm]
      have hM : LinearMap.toMatrix (b.baseChange S) (b.baseChange S)
          (matrixActionEquiv b S m).val = m.val :=
        (Matrix.toLinAlgEquiv (b.baseChange S)).symm_apply_apply m.val
      exact (congrArg (fun M : Matrix _ _ S => M i j) hM.symm).trans
        (LinearMap.toMatrix_apply _ _ _ _ _)
    change TensorProduct.comm k C S (evaluate H ρ g (b j)) = U (1 ⊗ₜ[k] b j)
    change evaluate H ρ g (b j) = ∑ i, b i ⊗ₜ[k] m.val i j at EVAL
    rw [EVAL, map_sum]
    simp only [TensorProduct.comm_tmul, hcoeff]
    simpa only [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (b.baseChange S).sum_repr (U ((b.baseChange S) j))
  apply nontrivialNormCoactionSplit hn ρ
  · intro h
    obtain ⟨g, hg⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app test)).2 t
    let a := ofConv g
    have hgt : e.hom.app test (toConv a) = t := hg
    have ha : p test a ≠ 1 := by
      change ((groupPointsFunctor k).map c).app test (e.hom.app test (toConv a)) ≠ 1
      rwa [hgt]
    apply ha
    apply (A.subgroupPoints test).injective
    rw [map_one]
    apply Subtype.ext
    apply Units.ext
    apply (b.baseChange test).ext
    intro i
    have HE := eval_eq test a (b i)
    rw [show evaluate H ρ a (b i) = b i ⊗ₜ[k] (1 : test) by
      simp [evaluate, h, trivialLinearMap]] at HE
    simpa [Module.Basis.baseChange_apply] using HE.symm
  · intro x
    let S := CommAlgCat.of k H
    let U := (A.subgroupPoints S (p S (AlgHom.id k H))).val
    have hU := (octonionAlgebra_preserves_iff S U).mp
      (A.subgroupPoints S (p S (AlgHom.id k H))).property
    have hnU := octonion_automorphism_invariance hn S
      (LinearMap.GeneralLinearGroup.toLinearEquiv U) hU.1 hU.2
    have heval := eval_eq S (AlgHom.id k H) x
    have he : evaluate H ρ (AlgHom.id k H) x = ρ.coaction x := by
      simp [evaluate]
    rw [he] at heval
    change Composition.Specification.normBaseChange S n (TensorProduct.comm k C S (ρ.coaction x)) = _
    rw [heval]
    have hval := congrArg (fun q : QuadraticForm S (S ⊗[k] C) => q (1 ⊗ₜ[k] x)) hnU.1
    change Composition.Specification.normBaseChange S n (U.val (1 ⊗ₜ[k] x)) =
      Composition.Specification.normBaseChange S n (1 ⊗ₜ[k] x) at hval
    rw [hval, normBaseChange_tmul]
    simp only [one_mul]
    rfl

end Cocharacters

section OctonionScalarDescent

open Module
open LinearAlgebraicGroups.Descent (SemilinearAction)

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {V : Type w} [NonAssocRing V] [Module K V] [Module k V]
    [IsScalarTower k K V] [IsScalarTower K V V] [SMulCommClass K V V]
    [IsScalarTower k V V] [SMulCommClass k V V]
    {n : QuadraticForm K V} (ρ : SemilinearAction k K V)

private abbrev fixedOctonionAlgebra (h₁ : ∀ g, ρ.act g 1 = 1)
    (hm : ∀ g x y, ρ.act g (x * y) = ρ.act g x * ρ.act g y) :
    UnitalSubalgebra k V where
  toSubmodule := ρ.fixed
  one_mem' := h₁
  mul_mem' := fun hx hy g => by
    rw [hm, hx g, hy g]

variable [FiniteDimensional k K] [IsGalois k K]
    (hq : ∀ g x, n (ρ.act g x) = g (n x))

private def fixedNormValue (x : ρ.fixed) : k :=
  (SemilinearAction.unitEquiv (k := k) (K := K)).symm
    ⟨n (x : V), fun g => by
      change g (n (x : V)) = n (x : V)
      rw [← hq, x.property g]⟩

private theorem coe_fixedNormValue (x : ρ.fixed) :
    algebraMap k K (fixedNormValue ρ hq x) = n (x : V) :=
  congrArg Subtype.val ((SemilinearAction.unitEquiv (k := k) (K := K)).apply_symm_apply _)

private def fixedCompositionNorm : QuadraticForm k ρ.fixed := by
  let q := fixedNormValue ρ hq
  have hq' (x : ρ.fixed) : algebraMap k K (q x) = n (x : V) := coe_fixedNormValue ρ hq x
  have hp (x y : ρ.fixed) :
      algebraMap k K (QuadraticMap.polar q x y) = n.polarBilin (x : V) (y : V) := by
    simp only [QuadraticMap.polar, map_sub, hq', Submodule.coe_add,
      QuadraticMap.polarBilin_apply_apply]
  refine QuadraticMap.ofPolar q ?_ ?_ ?_
  · intro a x
    apply (algebraMap k K).injective
    rw [smul_eq_mul, map_mul, hq', hq', map_mul]
    change n (a • (x : V)) = _ 
    rw [← IsScalarTower.algebraMap_smul K, n.map_smul]
    rfl
  · intro x x' y
    apply (algebraMap k K).injective
    rw [map_add, hp, hp, hp]
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
  · intro a x y
    apply (algebraMap k K).injective
    rw [smul_eq_mul, map_mul, hp, hp]
    change n.polarBilin (a • (x : V)) (y : V) = _
    rw [← IsScalarTower.algebraMap_smul K, map_smul, LinearMap.smul_apply]
    rfl

private theorem fixedCompositionNorm_map (x : ρ.fixed) :
    algebraMap k K (fixedCompositionNorm ρ hq x) = n (x : V) :=
  coe_fixedNormValue ρ hq x

private theorem fixedCompositionNorm_polar (x y : ρ.fixed) :
    algebraMap k K ((fixedCompositionNorm ρ hq).polarBilin x y) =
      n.polarBilin (x : V) (y : V) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, map_sub,
    fixedCompositionNorm_map, Submodule.coe_add]

variable (h₁ : ∀ g, ρ.act g 1 = 1)
    (hm : ∀ g x y, ρ.act g (x * y) = ρ.act g x * ρ.act g y)

private theorem fixedCompositionNorm_octonion (hn : OctonionNormConditions n) :
    let D := fixedOctonionAlgebra ρ h₁ hm
    OctonionNormConditions (show QuadraticForm k D from fixedCompositionNorm ρ hq) := by
  dsimp only
  let D := fixedOctonionAlgebra ρ h₁ hm
  obtain ⟨hN, hDim⟩ := (octonion_norm_iff_field n).mp hn
  letI := hN.nontrivial
  letI := hN.finite
  obtain ⟨hfinite, hfinrank⟩ := ρ.finiteDimensional_fixed
  apply (octonion_norm_iff_field _).mpr
  refine ⟨⟨hfinite, ⟨⟨0,1,fun h => zero_ne_one (congrArg (fun x : D => (x : V)) h)⟩⟩, ?_, ?_⟩,
    hfinrank.trans hDim⟩
  · have hreg (x : D) (hx : ∀ y : D, (fixedCompositionNorm ρ hq).polarBilin x y = 0) :
        x = 0 := by
      let L := n.polarBilin (x : V)
      have hker : Submodule.span K (ρ.fixed : Set V) ≤ L.ker := by
        apply Submodule.span_le.mpr
        intro y hy
        change n.polarBilin (x : V) y = 0
        rw [← fixedCompositionNorm_polar ρ hq x ⟨y,hy⟩, hx ⟨y,hy⟩, map_zero]
      rw [ρ.span_fixed_eq_top] at hker
      apply Subtype.ext
      exact hN.nondegenerate.1 (x : V) (fun y => hker Submodule.mem_top)
    exact ⟨hreg, fun x hx => hreg x (fun y => (QuadraticMap.polar_comm _ _ _).trans (hx y))⟩
  · intro x y
    change fixedCompositionNorm ρ hq (x * y) = fixedCompositionNorm ρ hq x * fixedCompositionNorm ρ hq y
    apply (algebraMap k K).injective
    simp only [map_mul (algebraMap k K), fixedCompositionNorm_map]
    exact hN.multiplicative (x : V) (y : V)

private theorem fixedOctonion_descentEquiv (hn : OctonionNormConditions n) :
    let D := fixedOctonionAlgebra ρ h₁ hm
    let q : QuadraticForm k D := fixedCompositionNorm ρ hq
    letI := (fixedCompositionNorm_octonion ρ hq h₁ hm hn).projective
    let e : K ⊗[k] D ≃ₗ[K] V := ρ.descentEquiv
    e 1 = 1 ∧ (∀ x y, e (x * y) = e x * e y) ∧
      (∀ x, n (e x) = Composition.Specification.normBaseChange K q x) := by
  dsimp only
  let D := fixedOctonionAlgebra ρ h₁ hm
  let q : QuadraticForm k D := fixedCompositionNorm ρ hq
  letI := (fixedCompositionNorm_octonion ρ hq h₁ hm hn).projective
  let e : K ⊗[k] D ≃ₗ[K] V := ρ.descentEquiv
  change e 1 = 1 ∧ (∀ x y, e (x * y) = e x * e y) ∧
      (∀ x, n (e x) = Composition.Specification.normBaseChange K q x)
  have he (s : K) (x : D) : e (s ⊗ₜ[k] x) = s • (x : V) := rfl
  refine ⟨by change e (1 ⊗ₜ[k] (1 : D)) = 1; rw [he]; simp, ?_, ?_⟩
  · intro x y
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      induction y using TensorProduct.inductionOn with
      | tmul t y =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, he, smul_mul_smul]
        rfl
      | add x y hx hy => simp only [mul_add, map_add, hx, hy]
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  · have H : (n.comp e.toLinearMap).polarBilin =
        (Composition.Specification.normBaseChange K q).polarBilin := by
      rw [polar_normBaseChange]
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      induction x using TensorProduct.inductionOn with
      | tmul s x =>
        induction y using TensorProduct.inductionOn with
        | tmul t y =>
          rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
            LinearMap.BilinForm.baseChange_tmul]
          change n.polarBilin (e (s ⊗ₜ[k] x)) (e (t ⊗ₜ[k] y)) = _
          rw [he, he]
          change n.polarBilin (s • (x : V)) (t • (y : V)) =
            (fixedCompositionNorm ρ hq).polarBilin x y • (s*t)
          have h : n.polarBilin (s • (x : V)) (t • (y : V)) =
              s * t * n.polarBilin (x : V) (y : V) := by
            simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
            ring
          rw [h, Algebra.smul_def, fixedCompositionNorm_polar]
          ring
        | add x y hx hy => simp only [map_add, hx, hy]
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    intro x
    change (n.comp e.toLinearMap) x = _
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe, he, n.map_smul, normBaseChange_tmul]
      change (s*s) * n (x : V) = (s*s) * algebraMap k K (fixedCompositionNorm ρ hq x)
      rw [fixedCompositionNorm_map]
    | add x y hx hy =>
      rw [QuadraticMap.map_add (n.comp e.toLinearMap),
        QuadraticMap.map_add (Composition.Specification.normBaseChange K q), hx, hy]
      rw [← QuadraticMap.polarBilin_apply_apply, H, QuadraticMap.polarBilin_apply_apply]


theorem finiteOctonionScalarDescent : FiniteOctonionScalarDescent.{u,v,w} := by
  intro k K _ _ _ _ _ V _ _ _ _ _ _ _ _ n hn ρ h₁ hm hq
  let D := fixedOctonionAlgebra ρ h₁ hm
  let q : QuadraticForm k D := fixedCompositionNorm ρ hq
  have hqNorm : OctonionNormConditions q := fixedCompositionNorm_octonion ρ hq h₁ hm hn
  refine ⟨D, q, hqNorm, rfl, ?_⟩
  exact ⟨ρ.descentEquiv, fun _ _ => rfl, fixedOctonion_descentEquiv ρ hq h₁ hm hn⟩

end OctonionScalarDescent

section SplitGroup

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Composition.PeirceSpecification (ZornIsomorphism)
open Composition.OctonionAutomorphismSpecification
open LinearAlgebraicGroups.Specs.GeometricRadicals
open LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms (schemePoints)

section G2RootLattice
open Set Module
private def shortRoots : Finset (ℤ × ℤ) :=
  {(1,0), (0,1), (-1,-1), (-1,0), (0,-1), (1,1)}

private def longRoots : Finset (ℤ × ℤ) :=
  {(-1,1), (1,-1), (2,1), (-2,-1), (1,2), (-1,-2)}

private def allRoots : Finset (ℤ × ℤ) := shortRoots ∪ longRoots

private theorem roots_with_second_one {t : ℤ × ℤ} (ht : t ∈ allRoots) (h : t.2 = 1) :
    -1 ≤ t.1 ∧ t.1 ≤ 2 := by
  simp only [allRoots, shortRoots, longRoots, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at ht
  rcases ht with (rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl) <;> norm_num at *

private theorem roots_with_sum_one {t : ℤ × ℤ} (ht : t ∈ allRoots) (h : t.1 + t.2 = 1) :
    t = (1,0) ∨ t = (0,1) := by
  simp only [allRoots, shortRoots, longRoots, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at ht
  rcases ht with (rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl) <;> norm_num at *

section CoordinateLattice

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : _root_.RootPairing I ℤ X Y) (e : X ≃ₗ[ℤ] (ℤ × ℤ))
    (hR : Set.range (e ∘ P.root) = (allRoots : Set (ℤ × ℤ)))

include hR in
private theorem g2_corootCoordinates {a b : I}
    (ha : e (P.root a) = (1,0)) (hb : e (P.root b) = (-1,1)) :
    (∀ x : ℤ × ℤ, P.toLinearMap (e.symm x) (P.coroot a) = 2 * x.1 - x.2) ∧
    ∀ x : ℤ × ℤ, P.toLinearMap (e.symm x) (P.coroot b) = -x.1 + x.2 := by
  obtain ⟨c, hc⟩ : (2,1) ∈ Set.range (e ∘ P.root) := hR.symm ▸ (by decide : (2,1) ∈ allRoots)
  change e (P.root c) = (2,1) at hc
  have coord_reflect (i j : I) :
      e (P.root j) - (P.pairing j i) • e (P.root i) ∈ allRoots := by
    have hs : e (P.root (P.reflectionPerm i j)) ∈ allRoots := by
      change e (P.root (P.reflectionPerm i j)) ∈ (allRoots : Set (ℤ × ℤ))
      rw [← hR]
      exact ⟨P.reflectionPerm i j, rfl⟩
    rwa [P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_smul] at hs
  let L : ℤ × ℤ →ₗ[ℤ] ℤ := (P.toLinearMap.flip (P.coroot a)).comp e.symm.toLinearMap
  let M : ℤ × ℤ →ₗ[ℤ] ℤ := (P.toLinearMap.flip (P.coroot b)).comp e.symm.toLinearMap
  have hL (i : I) : L (e (P.root i)) = P.pairing i a := by
    change P.toLinearMap (e.symm (e (P.root i))) (P.coroot a) = _
    rw [LinearEquiv.symm_apply_apply, P.root_coroot_eq_pairing]
  have hM (i : I) : M (e (P.root i)) = P.pairing i b := by
    change P.toLinearMap (e.symm (e (P.root i))) (P.coroot b) = _
    rw [LinearEquiv.symm_apply_apply, P.root_coroot_eq_pairing]
  have hLa : L (1,0) = 2 := by rw [← ha, hL, P.pairing_same]
  have hMb : M (-1,1) = 2 := by rw [← hb, hM, P.pairing_same]
  have coord (f : ℤ × ℤ →ₗ[ℤ] ℤ) (x y : ℤ) :
      f (x,y) = x * f (1,0) + y * f (0,1) := by
    have he : (x,y) = x • ((1,0) : ℤ × ℤ) + y • ((0,1) : ℤ × ℤ) := by
      ext <;> simp
    nth_rw 1 [he]
    simp only [map_add, map_smul, smul_eq_mul]
  have hLb : L (0,1) = -1 := by
    have H := coord_reflect a b
    have J := coord_reflect a c
    rw [← hL, ha, hb, coord L, hLa] at H
    rw [← hL, ha, hc, coord L, hLa] at J
    have Hr := roots_with_second_one H (by simp)
    have Jr := roots_with_second_one J (by simp)
    simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul] at Hr Jr
    omega
  have hMa : M (1,0) = -1 := by
    have H := coord_reflect b a
    rw [← hM, ha, hb] at H
    have hsum : (((1,0) : ℤ × ℤ) - M (1,0) • (-1,1)).1 +
        (((1,0) : ℤ × ℤ) - M (1,0) • (-1,1)).2 = 1 := by
      simp
    have K := roots_with_sum_one H hsum
    have ho : M (1,0) = 0 ∨ M (1,0) = -1 := by
      rcases K with K | K
      · left
        have H := congrArg Prod.snd K
        simp at H
        exact H
      · right
        have H := congrArg Prod.snd K
        simp at H
        omega
    rcases ho with hzero | hminus
    · obtain ⟨d, hd⟩ : (0,1) ∈ Set.range (e ∘ P.root) :=
        hR.symm ▸ (by decide : (0,1) ∈ allRoots)
      change e (P.root d) = (0,1) at hd
      have hm : M (0,1) = 2 := by
        rw [coord M, hzero] at hMb
        simpa using hMb
      have H := coord_reflect b d
      rw [← hM, hd, hb, hm] at H
      change ((2,-1) : ℤ × ℤ) ∈ allRoots at H
      exact False.elim ((by decide : ((2,-1) : ℤ × ℤ) ∉ allRoots) H)
    · exact hminus
  have hMc : M (0,1) = 1 := by
    rw [coord M, hMa] at hMb
    omega
  refine ⟨fun ⟨x,y⟩ => ?_, fun ⟨x,y⟩ => ?_⟩
  · change L (x,y) = _
    rw [coord, hLa, hLb]
    ring
  · change M (x,y) = _
    rw [coord, hMa, hMc]
    ring

include hR in
private theorem g2_simpleCorootSpan {a b : I}
    (ha : e (P.root a) = (1,0)) (hb : e (P.root b) = (-1,1)) :
    Submodule.span ℤ ({P.coroot a, P.coroot b} : Set Y) = ⊤ := by
  obtain ⟨hL,hM⟩ := g2_corootCoordinates P e hR ha hb
  apply Submodule.eq_top_iff'.mpr
  intro z
  let A := P.toLinearMap (e.symm (1,0)) z
  let B := P.toLinearMap (e.symm (0,1)) z
  let w := (A+B) • P.coroot a + (A+2*B) • P.coroot b
  have heq : w = z := by
    apply P.toLinearMap.flip.toPerfPair.injective
    ext x
    obtain ⟨⟨m,n⟩,rfl⟩ := e.symm.surjective x
    have hmn : ((m,n) : ℤ × ℤ) = m • ((1,0) : ℤ × ℤ) + n • ((0,1) : ℤ × ℤ) := by
      ext <;> simp
    change P.toLinearMap (e.symm (m,n)) w = P.toLinearMap (e.symm (m,n)) z
    conv_rhs => rw [hmn]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    change P.toLinearMap (e.symm (m,n)) w = m * A + n * B
    simp only [w, LinearMap.map_add, LinearMap.map_smul_of_tower, smul_eq_mul, hL, hM]
    ring
  rw [← heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

include hR in
private theorem corootSpan_eq_top :
    Submodule.span ℤ (Set.range P.coroot) = ⊤ := by
  obtain ⟨a, ha⟩ : (1,0) ∈ Set.range (e ∘ P.root) := hR.symm ▸ (by decide : (1,0) ∈ allRoots)
  obtain ⟨b, hb⟩ : (-1,1) ∈ Set.range (e ∘ P.root) := hR.symm ▸ (by decide : (-1,1) ∈ allRoots)
  apply top_le_iff.mp
  rw [← g2_simpleCorootSpan P e hR ha hb]
  exact Submodule.span_mono (Set.pair_subset_iff.mpr
    ⟨Set.mem_range_self a, Set.mem_range_self b⟩)

private theorem g2_simpleRootSpan {a b : I}
    (ha : e (P.root a) = (1,0)) (hb : e (P.root b) = (-1,1)) :
    Submodule.span ℤ ({P.root a, P.root b} : Set X) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro z
  obtain ⟨⟨x,y⟩,rfl⟩ := e.symm.surjective z
  have hz : e.symm (x,y) = (x+y) • P.root a + y • P.root b := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, map_add, map_smul, map_smul, ha, hb]
    ext <;> simp
  rw [hz]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

include hR in
private theorem g2_base [Finite I] :
    ∃ (B : P.Base) (i : Fin 2 ≃ B.support),
      (∀ s t, P.pairing (i t).val (i s).val = g2CartanMatrix s t) ∧ P.IsRootSystem := by
  classical
  obtain ⟨a, ha⟩ : (1,0) ∈ Set.range (e ∘ P.root) := hR.symm ▸ (by decide : (1,0) ∈ allRoots)
  obtain ⟨b, hb⟩ : (-1,1) ∈ Set.range (e ∘ P.root) := hR.symm ▸ (by decide : (-1,1) ∈ allRoots)
  change e (P.root a) = (1,0) at ha
  change e (P.root b) = (-1,1) at hb
  have hab : a ≠ b := by
    rintro rfl
    simp [ha] at hb
  let S : Finset I := {a,b}
  have hxs : P.root '' (S : Set I) = {P.root a, P.root b} := by simp [S]
  have hys : P.coroot '' (S : Set I) = {P.coroot a, P.coroot b} := by simp [S]
  have hX := g2_simpleRootSpan P e ha hb
  have hY := g2_simpleCorootSpan P e hR ha hb
  have li : LinearIndepOn ℤ P.root S := by
    have hl : LinearIndependent ℤ ![P.root a, P.root b] := by
      apply LinearIndependent.of_comp e.toLinearMap
      have hc : e.toLinearMap ∘ ![P.root a, P.root b] =
          ![((1,0) : ℤ × ℤ), (-1,1)] := by
        funext j
        fin_cases j <;> simp [ha,hb]
      rw [hc]
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      have h₁ := congrArg Prod.fst hg
      have h₂ := congrArg Prod.snd hg
      simp at h₁ h₂
      fin_cases i
      · change g 0 = 0
        omega
      · change g 1 = 0
        omega
    let f : Fin 2 → I := ![a,b]
    have hf : Function.Injective f := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [f]
    have hS : Set.range f = (S : Set I) := by
      ext i
      constructor
      · rintro ⟨j,rfl⟩
        fin_cases j <;> simp [S,f]
      · intro h
        rcases (show i = a ∨ i = b by simpa [S] using h) with rfl | rfl
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    rw [← hS, linearIndepOn_range_iff hf]
    convert hl using 1
    funext j
    fin_cases j <;> rfl
  obtain ⟨hL,hM⟩ := g2_corootCoordinates P e hR ha hb
  have hpairA (i : I) : P.pairing i a = 2 * (e (P.root i)).1 - (e (P.root i)).2 := by
    rw [← P.root_coroot_eq_pairing, ← hL, LinearEquiv.symm_apply_apply]
  have hpairB (i : I) : P.pairing i b = -(e (P.root i)).1 + (e (P.root i)).2 := by
    rw [← P.root_coroot_eq_pairing, ← hM, LinearEquiv.symm_apply_apply]
  have hneg : Set.Pairwise (S : Set I) (fun i j => P.pairingIn ℤ i j ≤ 0) := by
    have H (i : I) (hi : i ∈ (S : Set I)) : i = a ∨ i = b := by simpa [S] using hi
    intro i hi j hj hij
    rcases H i hi with rfl | rfl <;> rcases H j hj with rfl | rfl
    · exact (hij rfl).elim
    · norm_num [show P.pairingIn ℤ _ _ = P.pairing _ _ from P.algebraMap_pairingIn ℤ _ _,
        hpairB, ha]
    · norm_num [show P.pairingIn ℤ _ _ = P.pairing _ _ from P.algebraMap_pairingIn ℤ _ _,
        hpairA, hb]
    · exact (hij rfl).elim
  let B := RootPairing.Base.mkOfPairwiseLEZero P li hneg
    (fun i => by rw [hys, hY]; trivial) (fun i => by rw [hxs, hX]; trivial)
  let f : Fin 2 → B.support :=
    ![⟨a, by change a ∈ S; simp [S]⟩, ⟨b, by change b ∈ S; simp [S]⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have he := congrArg Subtype.val h
      fin_cases i <;> fin_cases j <;> simp_all [f]
    · intro j
      have hj : j.val = a ∨ j.val = b := by
        have h := j.property
        change j.val ∈ S at h
        simpa [S] using h
      rcases hj with h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext h.symm⟩
  refine ⟨B, Equiv.ofBijective f hf, ?_, ⟨?_, corootSpan_eq_top P e hR⟩⟩
  · intro i j
    change P.pairing (f j).val (f i).val = _
    fin_cases i <;> fin_cases j <;> norm_num [f, g2CartanMatrix, hpairA, hpairB, ha, hb]
  · apply top_le_iff.mp
    rw [← hX]
    exact Submodule.span_mono (Set.pair_subset_iff.mpr
      ⟨Set.mem_range_self a, Set.mem_range_self b⟩)

end CoordinateLattice

private def rootNeighbours (x : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  allRoots.filter fun y => x + y ∈ allRoots

private theorem rootNeighbours_card (x : allRoots) :
    (rootNeighbours x.val).card = if x.val ∈ shortRoots then 6 else 4 := by
  revert x
  decide

private theorem isShort_of_root_permutation (f : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ))
    (hf : ∀ x, f x ∈ allRoots ↔ x ∈ allRoots) {x : ℤ × ℤ} (hx : x ∈ allRoots) :
    f x ∈ shortRoots ↔ x ∈ shortRoots := by
  have he : (rootNeighbours x).map f.toEquiv.toEmbedding = rootNeighbours (f x) := by
    ext v
    obtain ⟨y,rfl⟩ := f.surjective v
    simp [rootNeighbours, hf, ← map_add]
  have hc : (rootNeighbours (f x)).card = (rootNeighbours x).card := by
    rw [← he, Finset.card_map]
  rw [rootNeighbours_card ⟨f x, (hf x).mpr hx⟩,
    rootNeighbours_card ⟨x,hx⟩] at hc
  by_cases h : f x ∈ shortRoots <;> by_cases j : x ∈ shortRoots <;> simp_all

private theorem distinct_short_difference {x y : ℤ × ℤ} (hx : x ∈ shortRoots) (hy : y ∈ shortRoots)
    (hne : x ≠ y) (hopp : x ≠ -y) : x - y ∈ allRoots := by
  have h : ∀ (x y : shortRoots), x.val ≠ y.val → x.val ≠ -y.val →
    x.val - y.val ∈ allRoots := by decide
  exact h ⟨x,hx⟩ ⟨y,hy⟩ hne hopp

private def sumModThree : (ℤ × ℤ) →+ ZMod 3 where
  toFun t := (t.1 + t.2 : ℤ)
  map_zero' := by simp
  map_add' x y := by
    simp [add_add_add_comm]

private theorem sumModThree_long (x : longRoots) : sumModThree x.val = 0 := by
  revert x
  decide

section Diagram

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : _root_.RootPairing I ℤ X Y) (e : X ≃ₗ[ℤ] (ℤ × ℤ))
    (hR : Set.range (e ∘ P.root) = (allRoots : Set (ℤ × ℤ)))

include hR in
private theorem rootSpan_eq_top : Submodule.span ℤ (Set.range P.root) = ⊤ := by
  apply Submodule.map_injective_of_injective e.injective
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range]
  rw [← Set.range_comp]
  change Submodule.span ℤ (Set.range (e ∘ P.root)) = ⊤
  rw [hR]
  apply Submodule.eq_top_iff'.mpr
  rintro ⟨x,y⟩
  have h : ((x,y) : ℤ × ℤ) = x • ((1,0) : ℤ × ℤ) + y • ((0,1) : ℤ × ℤ) := by
    ext <;> simp
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by decide)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by decide)))

include hR in
private theorem basedEquiv_eq_id (b : P.Base) (f : P.Equiv P)
    (hf : f.indexEquiv '' (b.support : Set I) = b.support) :
    f = RootPairing.Equiv.id P := by
  classical
  letI : P.IsRootSystem := ⟨rootSpan_eq_top P e hR, corootSpan_eq_top P e hR⟩
  have hcard : b.support.card = 2 := by
    rw [← Fintype.card_coe, ← Module.finrank_eq_card_basis b.toWeightBasis, e.finrank_eq,
      Module.finrank_prod, Module.finrank_self]
  obtain ⟨i,j,hij,hs⟩ := Finset.card_eq_two.mp hcard
  have hi : i ∈ b.support := by simp [hs]
  have hj : j ∈ b.support := by simp [hs]
  have roots (l : I) : e (P.root l) ∈ allRoots := by
    change e (P.root l) ∈ (allRoots : Set (ℤ × ℤ))
    rw [← hR]
    exact ⟨l,rfl⟩
  let F := (e.symm.trans f.weightEquiv).trans e
  have hfRoot (l : I) : F (e (P.root l)) = e (P.root (f.indexEquiv l)) := by
    simp [F, RootPairing.Hom.root_weightMap_apply]
  have hF (x : ℤ × ℤ) : F x ∈ allRoots ↔ x ∈ allRoots := by
    constructor
    · intro h
      have h' : F x ∈ Set.range (e ∘ P.root) := hR.symm ▸ h
      obtain ⟨l,hl⟩ := h'
      obtain ⟨l',rfl⟩ := f.indexEquiv.surjective l
      have he : e (P.root l') = x := F.injective ((hfRoot l').trans hl)
      exact he ▸ roots l'
    · intro h
      have h' : x ∈ Set.range (e ∘ P.root) := hR.symm ▸ h
      obtain ⟨l,rfl⟩ := h'
      exact (hfRoot l).symm ▸ roots (f.indexEquiv l)
  have short (l : I) : e (P.root (f.indexEquiv l)) ∈ shortRoots ↔ e (P.root l) ∈ shortRoots := by
    rw [← hfRoot l]
    exact isShort_of_root_permutation F hF (roots l)
  have hboth_short : ¬ (e (P.root i) ∈ shortRoots ∧ e (P.root j) ∈ shortRoots) := by
    rintro ⟨hi',hj'⟩
    have he : e (P.root i) ≠ e (P.root j) := fun h => hij (P.root.injective (e.injective h))
    have hn : e (P.root i) ≠ -e (P.root j) := by
      rw [← map_neg]
      exact fun h => b.root_ne_neg_of_ne hi hj hij (e.injective h)
    have hr := distinct_short_difference hi' hj' he hn
    have h : e (P.root i) - e (P.root j) ∈ Set.range (e ∘ P.root) := hR.symm ▸ hr
    obtain ⟨l,hl⟩ := h
    apply b.sub_notMem_range_root hi hj
    refine ⟨l,e.injective ?_⟩
    simpa only [map_sub, Function.comp_apply] using hl
  have hboth_long : ¬ (e (P.root i) ∉ shortRoots ∧ e (P.root j) ∉ shortRoots) := by
    rintro ⟨hi',hj'⟩
    have long (l : I) (hl : e (P.root l) ∉ shortRoots) : e (P.root l) ∈ longRoots :=
      (Finset.mem_union.mp (roots l)).resolve_left hl
    let L := sumModThree.toIntLinearMap.comp e.toLinearMap
    have hle : Submodule.span ℤ (P.root '' (b.support : Set I)) ≤ L.ker := by
      apply Submodule.span_le.mpr
      rintro x ⟨l,hl,rfl⟩
      rw [hs] at hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact sumModThree_long ⟨_,long _ hi'⟩
      · obtain rfl := Finset.mem_singleton.mp hl
        exact sumModThree_long ⟨_,long _ hj'⟩
    rw [b.span_int_root_support, rootSpan_eq_top P e hR] at hle
    have h : L (e.symm (1,0)) = 0 := hle (Submodule.mem_top : e.symm (1,0) ∈ (⊤ : Submodule ℤ X))
    change sumModThree (e (e.symm (1,0))) = 0 at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact (by decide : sumModThree (1,0) ≠ 0) h
  have hfix (l : I) (hl : l ∈ b.support) : f.indexEquiv l = l := by
    have hm : f.indexEquiv l ∈ b.support := by
      change f.indexEquiv l ∈ (b.support : Set I)
      rw [← hf]
      exact ⟨l,hl,rfl⟩
    rw [hs] at hl hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl hm
    rcases hl with E | E
    · subst l
      rcases hm with H|H
      · exact H
      · have h := short i
        rw [H] at h
        by_cases h' : e (P.root i) ∈ shortRoots
        · exact (hboth_short ⟨h',h.mpr h'⟩).elim
        · exact (hboth_long ⟨h',fun hj' => h' (h.mp hj')⟩).elim
    · subst l
      rcases hm with H|H
      · have h := short j
        rw [H] at h
        by_cases h' : e (P.root j) ∈ shortRoots
        · exact (hboth_short ⟨h.mpr h',h'⟩).elim
        · exact (hboth_long ⟨fun hi' => h' (h.mp hi'),h'⟩).elim
      · exact H
  have hw : f.weightEquiv.toLinearMap = LinearMap.id := by
    apply b.toWeightBasis.ext
    intro l
    change f.weightEquiv (b.toWeightBasis l) = b.toWeightBasis l
    simp [RootPairing.Hom.root_weightMap_apply, hfix l.val l.property]
  have hw' (x : X) : f.weightEquiv x = x := LinearMap.congr_fun hw x
  apply RootPairing.Equiv.ext
  · ext x
    exact hw' x
  · ext y
    apply P.toLinearMap.flip.toPerfPair.injective
    ext x
    change P.toLinearMap x (f.coweightEquiv y) = P.toLinearMap x y
    rw [← f.toLinearMap_weightEquiv, hw']
  · ext l
    apply P.root.injective
    change P.root (f.indexEquiv l) = P.root l
    rw [← RootPairing.Hom.root_weightMap_apply, ← RootPairing.Equiv.weightEquiv_apply, hw']

end Diagram

section FrameCharacters

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open LinearAlgebraicGroups.Specs.CharacterPairing (absoluteRoots)
open LinearAlgebraicGroups.Specs.AbstractPairing (Datum)
open LinearAlgebraicGroups.Specs.SchemeCentre (rootLattice)
open LinearAlgebraicGroups.Composition.OctonionAutomorphismSpecification
open Set


variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {ε : Fin 3 → Character T.group}

private def frameWeights : Fin 3 → (ℤ × ℤ) := ![(1,0), (0,1), (-1,-1)]

private theorem mem_allRoots_iff (x : ℤ × ℤ) :
    x ∈ allRoots ↔ (∃ i j : Fin 3, i ≠ j ∧ x = frameWeights i - frameWeights j) ∨
      (∃ i : Fin 3, x = frameWeights i ∨ x = -frameWeights i) := by
  constructor
  · intro h
    have H : ∀ x : allRoots,
        (∃ i j : Fin 3, i ≠ j ∧ x.val = frameWeights i - frameWeights j) ∨
          (∃ i : Fin 3, x.val = frameWeights i ∨ x.val = -frameWeights i) := by decide
    exact H ⟨x,h⟩
  · rintro (⟨i,j,h,rfl⟩|⟨i,rfl|rfl⟩)
    · have H : ∀ i j : Fin 3, i ≠ j → frameWeights i - frameWeights j ∈ allRoots := by decide
      exact H i j h
    · fin_cases i <;> decide
    · fin_cases i <;> decide

private theorem frameCharacterCoordinates (h : HasG2Roots T ε) (D : Datum T) :
    ∃ e : Additive (Character T.group) ≃ₗ[ℤ] (ℤ × ℤ),
      Set.range (e ∘ D.rootDatum.root) = (allRoots : Set (ℤ × ℤ)) := by
  classical
  let X := Additive (Character T.group)
  let a : X := Additive.ofMul (ε 0)
  let b : X := Additive.ofMul (ε 1)
  let F : ℤ × ℤ →ₗ[ℤ] X := (LinearMap.id.smulRight a).coprod (LinearMap.id.smulRight b)
  have hF (r s : ℤ) : F (r,s) = r • a + s • b := rfl
  have hS : Additive.ofMul (ε 2) = -(a + b) := by
    apply eq_neg_of_add_eq_zero_right
    change Additive.ofMul (ε 0 * ε 1 * ε 2) = Additive.ofMul 1
    exact congrArg Additive.ofMul (by simpa only [Fin.prod_univ_three] using h.1)
  have hweight (i : Fin 3) : F (frameWeights i) = Additive.ofMul (ε i) := by
    fin_cases i
    · change F (1,0) = a
      simp [hF]
    · change F (0,1) = b
      simp [hF]
    · change F (-1,-1) = Additive.ofMul (ε 2)
      rw [hS, hF]
      simp only [neg_zsmul, one_zsmul, neg_add]
  have H (x : X) : x.toMul ∈ absoluteRoots T ↔ ∃ t ∈ allRoots, F t = x := by
    constructor
    · intro hx
      rw [h.2.2.1] at hx
      change (∃ i j : Fin 3, i ≠ j ∧ x.toMul = ε i * (ε j)⁻¹) ∨
        (∃ i : Fin 3, x.toMul = ε i ∨ x.toMul = (ε i)⁻¹) at hx
      rcases hx with ⟨i,j,hij,he⟩ | ⟨i,he|he⟩
      · refine ⟨_, (mem_allRoots_iff _).mpr (Or.inl ⟨i,j,hij,rfl⟩), ?_⟩
        rw [map_sub, hweight, hweight]
        change Additive.ofMul (ε i / ε j) = x
        rw [div_eq_mul_inv]
        exact congrArg Additive.ofMul he.symm
      · exact ⟨_, (mem_allRoots_iff _).mpr (Or.inr ⟨i, Or.inl rfl⟩),
          (hweight i).trans (congrArg Additive.ofMul he.symm)⟩
      · refine ⟨_, (mem_allRoots_iff _).mpr (Or.inr ⟨i, Or.inr rfl⟩), ?_⟩
        rw [map_neg, hweight]
        exact congrArg Additive.ofMul he.symm
    · rintro ⟨t,ht,rfl⟩
      rw [h.2.2.1]
      rcases (mem_allRoots_iff _).mp ht with ⟨i,j,hij,rfl⟩ | ⟨i,rfl|rfl⟩
      · refine Or.inl ⟨i,j,hij,?_⟩
        rw [map_sub, hweight, hweight]
        exact div_eq_mul_inv _ _
      · exact Or.inr ⟨i, Or.inl (congrArg Additive.toMul (hweight i))⟩
      · exact Or.inr ⟨i, Or.inr (by rw [map_neg, hweight]; rfl)⟩
  have hsurj : Function.Surjective F := by
    apply LinearMap.range_eq_top.mp
    let M : Subgroup (Character T.group) :=
      { carrier := {x | Additive.ofMul x ∈ F.range}
        one_mem' := F.range.zero_mem
        mul_mem' := fun hx hy => F.range.add_mem hx hy
        inv_mem' := fun hx => F.range.neg_mem hx }
    have hle : rootLattice T ≤ M := by
      rw [rootLattice, Subgroup.closure_le]
      intro x hx
      change Additive.ofMul x ∈ F.range
      obtain ⟨t,_,ht⟩ := (H (Additive.ofMul x)).mp hx
      exact ⟨t,ht⟩
    rw [h.2.2.2] at hle
    apply Submodule.eq_top_iff'.mpr
    intro x
    exact hle (Subgroup.mem_top x.toMul)
  have hinj : Function.Injective F := by
    apply (injective_iff_map_eq_zero F).mpr
    rintro ⟨r,s⟩ hz
    rw [hF] at hz
    have hz' : ε 0 ^ r * ε 1 ^ s = 1 := congrArg Additive.toMul hz
    let z : Fin 3 → ℤ := ![r,s,0]
    have hprod : (∏ i, ε i ^ z i) = 1 := by
      rw [Fin.prod_univ_three]
      change ε 0 ^ r * ε 1 ^ s * ε 2 ^ (0 : ℤ) = 1
      simp only [zpow_zero, mul_one, hz']
    have he := (h.2.1 z).mp hprod
    exact Prod.ext (he 0 2) (he 1 2)
  let e := (LinearEquiv.ofBijective F ⟨hinj,hsurj⟩).symm
  refine ⟨e, ?_⟩
  ext t
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨t, ht, he⟩ := (H (D.rootDatum.root x)).mp (by
      rw [D.root_eq]
      exact x.property)
    have hh : e (F t) = t := (LinearEquiv.ofBijective F ⟨hinj,hsurj⟩).symm_apply_apply _
    change e (D.rootDatum.root x) ∈ allRoots
    rwa [← he, hh]
  · intro ht
    have hx := (H (F t)).mpr ⟨t,ht,rfl⟩
    refine ⟨⟨(F t).toMul,hx⟩, ?_⟩
    change e (D.rootDatum.root ⟨(F t).toMul,hx⟩) = t
    rw [D.root_eq]
    exact (LinearEquiv.ofBijective F ⟨hinj,hsurj⟩).symm_apply_apply _
end FrameCharacters

end G2RootLattice


open private automorphismAlgebraicGroup octonionAutomorphismGroup_reductive_semisimple
  exists_closedFrameTorus frameTorus_isSplit frameTorus_geometricallyMaximal
  rootFrameCharacters hasG2Roots_of_tangent_weights splitFrame_absoluteRoots
  trivial_centre_of_root_lattice from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms

variable {k : Type u} [Field k] {C : Type v} [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {n : QuadraticForm k C}

private theorem splitOctonionStructure (hn : OctonionNormConditions n)
    (A : AutomorphismGroup k C) (F : ZornIsomorphism n) :
    IsAdjointG2 (automorphismAlgebraicGroup A) := by
  letI := hn.projective
  obtain ⟨hR, hS⟩ := octonionAutomorphismGroup_reductive_semisimple hn A
  obtain ⟨i, hc, hi⟩ := exists_closedFrameTorus F A
  let T : ClosedSubgroup (automorphismAlgebraicGroup A).val := ⟨frameTorus k, i, hc⟩
  have hm : IsGeometricallyMaximal T := frameTorus_geometricallyMaximal F A i hi hc
  have hs : IsSplitTorus T.group := frameTorus_isSplit (K := k)
  let e : T.group ≅ frameTorus k := Iso.refl _
  have hF : IsFrameTorus F A (e.inv ≫ T.inclusion) := by simpa [e, T] using hi
  have hroots := hasG2Roots_of_tangent_weights e (splitFrame_absoluteRoots F A T e hF)
  exact ⟨hR, hS, trivial_centre_of_root_lattice
    LinearAlgebraicGroups.RootData.SchemeCentre.schemeCentre hR T hs hm hroots.2.2.2,
    T, rootFrameCharacters e, hs, hm, hroots⟩

private def automorphismGroupAlongIso (G : AffineAlgebraicGroup k) (A : AutomorphismGroup k C)
    (e : G.val ≅ A.group) : AutomorphismGroup k C where
  group := G.val
  generalLinear := A.generalLinear
  inclusion := e.hom ≫ A.inclusion
  closed := by
    let : IsClosedImmersion A.inclusion.hom.hom.left := A.closed
    let U := Grp.forget (SchemeOver k) ⋙ Over.forget _
    have : IsIso e.hom.hom.hom.left := show IsIso (U.map e.hom) from inferInstance
    change IsClosedImmersion (e.hom.hom.hom.left ≫ A.inclusion.hom.hom.left)
    infer_instance
  groupAffine := G.property.1
  linearAffine := A.linearAffine
  groupFiniteType := G.property.2.1
  linearFiniteType := A.linearFiniteType
  groupQuasiCompact := G.property.2.2
  linearQuasiCompact := A.linearQuasiCompact
  linearPoints := A.linearPoints
  subgroupPoints S := (((schemePoints k).mapIso e).app S).groupIsoToMulEquiv.trans (A.subgroupPoints S)
  evaluatesInclusion S x := by
    rw [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
    exact A.evaluatesInclusion S _
  scalarChange := A.scalarChange

private theorem splitReductiveOfZorn (G : AffineAlgebraicGroup k)
    (A : AutomorphismGroup k C) (e : G.val ≅ A.group)
    (hn : OctonionNormConditions n) (F : ZornIsomorphism n) :
    IsSplitReductive G := by
  have h : IsAdjointG2 G := splitOctonionStructure hn (automorphismGroupAlongIso G A e) F
  obtain ⟨hR, _, _, T, _, hs, hm, _⟩ := h
  exact ⟨hR, T, hs, hm⟩

section SplitStructure

open LinearAlgebraicGroups.Specs.GeometricRadicals
open LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open LinearAlgebraicGroups.Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)
open LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open LinearAlgebraicGroups.Specs.Pinning (AttachedDatum SplitBorelPair)

private theorem g2_simplyConnected {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hR : IsReductive G) (hS : IsSemisimple G) (T : ClosedSubgroup G.val)
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (ε : Fin 3 → Character T.group) (h : HasG2Roots T ε) : GeometricallySimplyConnected G := by
  obtain ⟨hT, ⟨D⟩⟩ := LinearAlgebraicGroups.RootData.AbstractPairing.abstractPairing G hR T hs hm
  letI := hT
  obtain ⟨e,he⟩ := frameCharacterCoordinates h D
  apply (LinearAlgebraicGroups.Classification.SimplyConnectedLattice.latticeCriterion G hS T hs hm D).mpr
  exact corootSpan_eq_top D.rootDatum e he

private theorem g2_basedAutomorphisms {k : Type u} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (ε : Fin 3 → Character P.T.group) (h : HasG2Roots P.T ε) :
    Subsingleton (Aut D.toBased) := by
  letI := D.comm
  obtain ⟨e,he⟩ := frameCharacterCoordinates h D.datum
  have H (f : Aut D.toBased) : f = 1 := by
    apply Aut.ext
    apply Iso.ext
    apply Subtype.ext
    exact basedEquiv_eq_id D.datum.rootDatum e he D.base f.asIso.hom.val f.asIso.hom.property
  exact ⟨fun f g => (H f).trans (H g).symm⟩

private theorem splitOctonionSimplyConnected {k : Type u} [Field k] {C : Type v}
    [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    {n : QuadraticForm k C} (hn : OctonionNormConditions n) (A : AutomorphismGroup k C)
    (F : ZornIsomorphism n) : GeometricallySimplyConnected (automorphismAlgebraicGroup A) := by
  obtain ⟨hR,hS,_,T,ε,hs,hm,h⟩ := splitOctonionStructure hn A F
  exact g2_simplyConnected _ hR hS T hs hm ε h

end SplitStructure

section Adjoint

open Opposite CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Specs.AutomorphismSequence (AdjointQuotient SplitSequence RelativeAut innerAut)
open LinearAlgebraicGroups.Specs.GeometricRadicals
open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem centreInclusion_eq_one (hG : HasTrivialCentre G.val) (Q : AdjointQuotient G) :
    Q.centre.inclusion.hom.hom = 1 := by
  have hc : IsClosedImmersion Q.centre.inclusion.hom.hom.left := Q.centre.isClosedImmersion
  have ha : IsAffine G.val.X.left := G.property.1
  have ha' : IsAffine Q.centre.group.X.left :=
    isAffine_of_isAffineHom Q.centre.inclusion.hom.hom.left
  obtain ⟨S,⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha'
  apply (cancel_epi e.hom).mp
  rw [MonObj.comp_one]
  apply hG S.unop
  exact (Q.isCentre _ _).mpr ⟨e.hom,rfl⟩

private theorem adjointProjection_isIso (hG : HasTrivialCentre G.val) (Q : AdjointQuotient G) :
    IsIso Q.projection := by
  have ht := centreInclusion_eq_one hG Q
  have hkernel (Z : SchemeOver k) (a : Z ⟶ G.val.X) (ha : a ≫ Q.projection.hom.hom = 1) :
      a = 1 := by
    have hh : a ≫ Q.projection.hom.hom = toUnit Z ≫ η[Q.quotient.val.X] := ha
    let a' := Q.kernel.lift a (toUnit Z) hh
    have H : a' ≫ Q.centre.inclusion.hom.hom = a := Q.kernel.lift_fst a (toUnit Z) hh
    rw [ht, MonObj.comp_one] at H
    exact H.symm
  have : Mono Q.projection.hom.hom := by
    constructor
    intro Z a b h
    have hh := hkernel Z (a * b⁻¹) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel])
    exact div_eq_one.mp hh
  have : Flat Q.projection.hom.hom.left := Q.fppf.1
  have : Surjective Q.projection.hom.hom.left := Q.fppf.2.1
  have : IsAffine G.val.X.left := G.property.1
  have : IsAffine Q.quotient.val.X.left := Q.quotient.property.1
  let U := Over.forget (Spec (CommRingCat.of k))
  letI : IsIso (U.map Q.projection.hom.hom) := by
    change IsIso Q.projection.hom.hom.left
    exact Flat.isIso_of_surjective_of_mono _
  letI : IsIso Q.projection.hom.hom := isIso_of_reflects_iso Q.projection.hom.hom U
  let e : G.val ≅ Q.quotient.val := Grp.mkIso' (asIso Q.projection.hom.hom)
  have he : e.hom = Q.projection := Grp.hom_ext _ _ rfl
  exact he ▸ e.isIso_hom

open LinearAlgebraicGroups.Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.Specs.Pinning (PinnedGroup AttachedDatum)
open LinearAlgebraicGroups.Specs.AutomorphismSequence (groupSections)

private theorem adjointCoercion_bijective {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) (hZ : HasTrivialCentre P.pair.G.val)
    [Subsingleton (Aut D.toBased)] (S : SchemeOver k) :
    Function.Bijective (fun g : S ⟶ P.pair.G.val.X => (innerAut g : RelativeAut P.pair.G.val S)) := by
  letI := adjointProjection_isIso hZ Q
  let e : P.pair.G.val.X ≅ Q.quotient.val.X := (Grp.forget (SchemeOver k)).mapIso (asIso Q.projection)
  constructor
  · intro g h eq
    have eq1 : (⟨g ≫ Q.projection.hom.hom⟩ : (groupSections Q.quotient.val).obj (op S)) =
        ⟨h ≫ Q.projection.hom.hom⟩ := E.innerInjective _
          ((E.onLift S g).trans (eq.trans (E.onLift S h).symm))
    have : Mono Q.projection.hom.hom := inferInstanceAs (Mono e.hom)
    exact (cancel_mono Q.projection.hom.hom).mp (congrArg ULift.down eq1)
  · intro a
    have ha : E.outer.app (op S) a = 1 := by
      apply ULift.ext
      apply LocallyConstant.ext
      intro x
      exact Subsingleton.elim _ _
    obtain ⟨⟨p⟩,hp⟩ := (E.exact (op S) a).mp ha
    change S ⟶ Q.quotient.val.X at p
    refine ⟨p ≫ e.inv, ?_⟩
    change innerAut (p ≫ e.inv) = a
    have hcomp : (p ≫ e.inv) ≫ Q.projection.hom.hom = p := by
      change (p ≫ e.inv) ≫ e.hom = p
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact (E.onLift S (p ≫ e.inv)).symm.trans
      ((congrArg (fun x : S ⟶ Q.quotient.val.X => E.inner.app (op S) ⟨x⟩) hcomp).trans hp)

end Adjoint

section InnerForm

open Opposite
open LinearAlgebraicGroups.Specs.Pinning
open LinearAlgebraicGroups.Specs.AutomorphismSequence
open LinearAlgebraicGroups.Specs.RelativeFormComparison
open LinearAlgebraicGroups.Descent.NonabelianCohomology

open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private exists_coordinate_model standard descend_standard_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso extendedSpecIso_hom_fst from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private schemeIsoEquiv hopfIsoEquiv restrict_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

private theorem g2_relativeAutomorphisms_inner {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hG : IsAdjointG2 G) (S : SchemeOver k) :
    Function.Bijective (fun g : S ⟶ G.val.X => (innerAut g : RelativeAut G.val S)) := by
  obtain ⟨hR, _, hZ, T, ε, hs, hm, h⟩ := hG
  let A := LinearAlgebraicGroups.Classification.Pinning.standardAdditiveLine k
  let B := splitBorelPair G hR T hs hm
  obtain ⟨U,⟨p⟩⟩ := LinearAlgebraicGroups.Classification.Pinning.pinningsExist A B
  let P : PinnedGroup A := ⟨B,U,p⟩
  obtain ⟨D,l,Q,E,_,_⟩ := LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.automorphismSequences P
  letI : Subsingleton (Aut D.toBased) := g2_basedAutomorphisms D ε h
  exact adjointCoercion_bijective E hZ S

private theorem finiteTrivialization {k : Type u} [Field k]
    (G H : AffineAlgebraicGroup k) (S : Type u) [Field S] [Algebra k S] [IsGalois k S]
    (e : (groupBaseChange k S).obj G.val ≅ (groupBaseChange k S).obj H.val) :
    ∃ K : FiniteGaloisIntermediateField k S,
      Nonempty (relativePoints G.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K)) := by
  obtain ⟨P,hP,⟨g⟩⟩ := exists_coordinate_model G
  obtain ⟨Q,hQ,⟨h⟩⟩ := exists_coordinate_model H
  let i := (hopfIsoEquiv (extendedGroupIso (k := k) S) g h).symm (schemeIsoEquiv S G.val H.val e)
  obtain ⟨K,j,_,_⟩ := LinearAlgebraicGroups.Descent.Forms.finiteLevelIsomorphisms P Q hP hQ ⊥ i
  exact ⟨K, ⟨hopfIsoEquiv (extendedGroupIso (k := k) K) g h j⟩⟩

private theorem descendInvariantRelativeIso {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsGalois k K] (G H : AffineAlgebraicGroup k)
    (i : relativePoints G.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K))
    (hi : ∀ σ : Gal(K/k), restrictIso (fieldMap k K σ) i = i) : Nonempty (G.val ≅ H.val) := by
  obtain ⟨P, _, ⟨g⟩⟩ := exists_coordinate_model G
  obtain ⟨Q, _, ⟨h⟩⟩ := exists_coordinate_model H
  let t := extendedGroupIso (k := k) K
  obtain ⟨e, _, he⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.hopfIsomorphismComparison
    t (extendedSpecIso_hom_fst K) g h
  let j := e.symm i
  have hj (σ : Gal(K/k)) : HopfConjugates σ j j := by
    apply (he σ j j).mpr
    rw [e.apply_symm_apply]
    exact hi σ
  have hEq : (standard K P).Equivariant (standard K Q) j.hom := fun σ x => hj σ x
  obtain ⟨d, _⟩ := descend_standard_iso j hEq
  exact ⟨g.symm ≪≫ LinearAlgebraicGroups.Descent.Forms.spectrumIso d ≪≫ h⟩

private theorem isomorphicOfSameDisplacement {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsGalois k K] {G₀ G H : AffineAlgebraicGroup k}
    (i : relativePoints G₀.val (fieldTest k K) ≅ relativePoints G.val (fieldTest k K))
    (j : relativePoints G₀.val (fieldTest k K) ≅ relativePoints H.val (fieldTest k K))
    (h : ∀ σ : Gal(K/k), transportedAut k K i σ = transportedAut k K j σ) :
    Nonempty (G.val ≅ H.val) := by
  apply descendInvariantRelativeIso G H (i.symm ≪≫ j)
  intro σ
  have h₁ : restrictIso (fieldMap k K σ) i ≪≫ i.symm =
      restrictIso (fieldMap k K σ) j ≪≫ j.symm := congrArg Aut.asIso (h σ)
  have h₂ : restrictIso (fieldMap k K σ) j = restrictIso (fieldMap k K σ) i ≪≫ i.symm ≪≫ j := by
    rw [← Iso.trans_assoc, h₁, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  rw [restrict_trans]
  change (restrictIso (fieldMap k K σ) i).symm ≪≫ restrictIso (fieldMap k K σ) j = _
  rw [h₂, Iso.symm_self_id_assoc]

end InnerForm

section ScalarChange

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.GeometricRadicals (IsSplitTorus IsReductive GeometricGroup baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint unitCoordinates)
open private gm_baseChange unitEquiv unitEquiv_unitPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private map_comp_apply baseInclusion extension_dualMap relativePointRestrict
  relativePointRestrict_naturality relativePointRestrict_scale restriction_constants pointRestrict
  pointRestrict_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation
open private splitTorus_hom_descends groupBaseChange_map_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
open private split_baseChange_dimension standard_torus_dimension dimension_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private isAffine_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
open private extendSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open Specs.AbstractPairing (Root)
open Specs.Pinning (SplitBorelPair AttachedDatum)
open private geometricallyMaximal_of_maximal_split inverseBaseChangeIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private reductive_dimension_eq_lie_finrank from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev Gm (k : Type u) [Field k] : GroupScheme k :=
  specGroup (groupAlgebra k IntegerCharacters)

private theorem splitGm (k : Type u) [Field k] : IsSplitTorus (Gm k) := by
  obtain ⟨e⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) 1
  let a : StandardLattice.{u} 1 ≃* IntegerCharacters.{u} :=
    MulEquiv.funUnique (Fin 1) IntegerCharacters
  exact ⟨1, ⟨(hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k a)).op ≪≫ e⟩⟩

private theorem unitPoint_surjective (R : TestAlgebra k) :
    Function.Surjective (unitPoint R) := by
  intro p
  exact ⟨unitEquiv R p, (unitEquiv R).injective (unitEquiv_unitPoint R _)⟩

private abbrev extendCharacter {T : GroupScheme k}
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k)) (χ : Character T) :
    Character ((groupBaseChange k K).obj T) :=
  (groupBaseChange k K).map χ ≫ e.inv

private theorem extendCharacter_bijective {T : GroupScheme k} (hT : IsSplitTorus T)
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k)) :
    Function.Bijective (extendCharacter (T := T) e) := by
  constructor
  · intro a b h
    exact groupBaseChange_map_injective ((cancel_mono e.inv).mp h)
  · intro a
    obtain ⟨b, hb⟩ := splitTorus_hom_descends (K := K) hT (splitGm k) (a ≫ e.hom)
    exact ⟨b, by change (groupBaseChange k K).map b ≫ e.inv = a; simp [hb]⟩

private theorem extendCharacter_point {T : GroupScheme k}
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k))
    (χ : Character T) (R : TestAlgebra K) (t : GroupPoints ((groupBaseChange k K).obj T) R) :
    pointRestrict K (Gm k) R ((t ≫ (extendCharacter e χ).hom.hom) ≫ e.hom.hom.hom) =
      pointRestrict K T R t ≫ χ.hom.hom := by
  have h : extendCharacter e χ ≫ e.hom = (groupBaseChange k K).map χ := by
    simp [extendCharacter]
  have h' := congrArg (fun f => f.hom.hom) h
  rw [Category.assoc, ← Grp.comp_hom_hom, h']
  exact baseChangePointsSchemeNaturality k K χ.hom.hom R t

private theorem extendCharacter_at_point {T : GroupScheme k}
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      pointRestrict K (Gm k) R (unitPoint R s ≫ e.hom.hom.hom) =
        unitPoint ((restrictTestAlgebra k K).obj R) s)
    (χ : Character T) (R : TestAlgebra K) (t : GroupPoints ((groupBaseChange k K).obj T) R) :
    ∃ s : Rˣ, t ≫ (extendCharacter e χ).hom.hom = unitPoint R s ∧
      pointRestrict K T R t ≫ χ.hom.hom = unitPoint ((restrictTestAlgebra k K).obj R) s := by
  obtain ⟨s, hs⟩ := unitPoint_surjective R (t ≫ (extendCharacter e χ).hom.hom)
  refine ⟨s, hs.symm, ?_⟩
  rw [← extendCharacter_point e χ R t, ← hs]
  exact he R s

private theorem characterValue_at_unit {T : GroupScheme k} (χ : Character T) (R : TestAlgebra k)
    (t : GroupPoints T R) {s : Rˣ} (hs : t ≫ χ.hom.hom = unitPoint R s) :
    characterValue χ R t = (s : R) := by
  unfold characterValue
  rw [hs]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (unitCoordinates R s)).op)).unop.hom
      (MonoidAlgebra.single (Specs.DiagonalizableGroups.integerGenerator) 1) = _
  rw [Functor.FullyFaithful.preimage_map]
  change unitCoordinates R s (MonoidAlgebra.single
    (Specs.DiagonalizableGroups.integerGenerator) 1) = _
  simp [unitCoordinates, Specs.DiagonalizableGroups.integerGenerator]
  change (↑(s ^ (1 : ℤ)) : R) = ↑s
  rw [zpow_one]

private theorem extendCharacter_value {T : GroupScheme k}
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      pointRestrict K (Gm k) R (unitPoint R s ≫ e.hom.hom.hom) =
        unitPoint ((restrictTestAlgebra k K).obj R) s)
    (χ : Character T) (R : TestAlgebra K) (t : GroupPoints ((groupBaseChange k K).obj T) R) :
    characterValue (extendCharacter e χ) R t =
      characterValue χ ((restrictTestAlgebra k K).obj R) (pointRestrict K T R t) := by
  obtain ⟨s, hs, hs'⟩ := extendCharacter_at_point e he χ R t
  exact (characterValue_at_unit _ _ _ hs).trans (characterValue_at_unit _ _ _ hs').symm

private theorem extendCharacter_mul {T : GroupScheme k} (hT : IsAffine T.X.left)
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k))
    (a b : Character T) :
    extendCharacter e (a * b) = extendCharacter e a * extendCharacter e b := by
  let L := Gm k
  let F := groupBaseChange k K
  letI := hT
  apply (LinearAlgebraicGroups.groupHomComparison K _ _ (isAffine_baseChange K T)).injective
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro t
  change t ≫ (extendCharacter e (a * b)).hom.hom =
    t ≫ (extendCharacter e a * extendCharacter e b).hom.hom
  apply (cancel_mono e.hom.hom.hom).mp
  apply (pointRestrict K L R).injective
  rw [extendCharacter_point]
  change (pointRestrict K T R t ≫ (a.hom.hom * b.hom.hom)) =
    pointRestrict K L R ((t ≫ ((extendCharacter e a).hom.hom *
      (extendCharacter e b).hom.hom)) ≫ e.hom.hom.hom)
  rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.mul_comp,
    (pointRestrict K L R).map_mul, extendCharacter_point, extendCharacter_point]

private theorem extend_adj_weight (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      pointRestrict K (Gm k) R (unitPoint R s ≫ e.hom.hom.hom) =
        unitPoint ((restrictTestAlgebra k K).obj R) s)
    (χ : Character T.group) (v : Lie k G.val) (hv : v ∈ adjointWeightVectors T χ)
    (q : Lie K ((groupBaseChange k K).obj G.val))
    (hq : pointRestrict K G.val (CommAlgCat.of K (DualNumber K)) q.toMul.val =
      mapPoints (extendDualNumber K) v.toMul.val) :
    q ∈ adjointWeightVectors (extendSubgroup K T) (extendCharacter e χ) := by
  intro R t
  let R₀ := (restrictTestAlgebra k K).obj R
  let a : CommAlgCat.of K K ⟶ R := CommAlgCat.ofHom (Algebra.ofId K R)
  let a₀ : CommAlgCat.of k k ⟶ R₀ :=
    ConcreteCategory.ofHom (C := CommAlgCat k) (Y := R₀) (@Algebra.ofId k R₀ _ _ R₀.algebra)
  let t₀ := pointRestrict K T.group R t
  let H := (groupBaseChange k K).obj G.val
  let j : GroupPoints H R := t ≫ ((groupBaseChange k K).map T.inclusion).hom.hom
  let p : GroupPoints H (CommAlgCat.of K (DualNumber R)) := mapPoints (dualMap a) q.toMul.val
  let g : GroupPoints H (CommAlgCat.of K (DualNumber R)) := mapPoints (constants R) j
  change g * p * g⁻¹ = mapPoints (scale R (characterValue (extendCharacter e χ) R t)) p
  have hp₀ : relativePointRestrict K G.val (CommAlgCat.of K K) q.toMul.val =
      mapPoints (dualMap (baseInclusion (k := k) K)) v.toMul.val := by
    change mapPoints (dualRestriction K (CommAlgCat.of K K)).hom
      (pointRestrict K G.val (CommAlgCat.of K (DualNumber K)) q.toMul.val) = _
    rw [hq, ← map_comp_apply, extension_dualMap]
  have hp : relativePointRestrict K G.val R p = mapPoints (dualMap a₀) v.toMul.val := by
    change relativePointRestrict K G.val R (mapPoints (dualMap a) q.toMul.val) = _
    rw [relativePointRestrict_naturality, hp₀, ← map_comp_apply]
    congr 1
  have hg : relativePointRestrict K G.val R g = mapPoints (constants R₀)
      (t₀ ≫ T.inclusion.hom.hom) := by
    change mapPoints (dualRestriction K R).hom
      (pointRestrict K G.val (CommAlgCat.of K (DualNumber R)) (mapPoints (constants R) j)) = _
    rw [pointRestrict_naturality K G.val (constants R) j, ← map_comp_apply, restriction_constants]
    congr 1
    exact baseChangePointsSchemeNaturality k K T.inclusion.hom.hom R t
  apply (relativePointRestrict K G.val R).injective
  rw [(relativePointRestrict K G.val R).map_mul, (relativePointRestrict K G.val R).map_mul,
    (relativePointRestrict K G.val R).map_inv, relativePointRestrict_scale, hp, hg,
    extendCharacter_value e he]
  exact hv R₀ t₀

private theorem absoluteRoot_baseChange (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group)
    (e : Gm K ≅ (groupBaseChange k K).obj (Gm k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      pointRestrict K (Gm k) R (unitPoint R s ≫ e.hom.hom.hom) =
        unitPoint ((restrictTestAlgebra k K).obj R) s)
    (χ : Character T.group) (hχ : χ ∈ absoluteRoots T) :
    extendCharacter e χ ∈ absoluteRoots (extendSubgroup K T) := by
  let H := baseChangedAlgebraicGroup K G
  let s := identityLieStructure G
  let t := identityLieStructure H
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : LieRing (Specs.Lie K ((groupBaseChange k K).obj G.val)) := t.lieRing
  letI : LieAlgebra K (Specs.Lie K ((groupBaseChange k K).obj G.val)) := t.lieAlgebra
  obtain ⟨f, hf⟩ := (identityLieBracketBaseChange k K G).2 s t
  obtain ⟨hne,v,hv,hv0⟩ := hχ
  have hI := (extendCharacter_bijective hT e).1
  have he₁ : extendCharacter (T := T.group) e 1 = 1 := by
    let hA := (Unipotent.closedSubgroupAlgebraicGroup T).property.1
    have w := extendCharacter_mul hA e 1 1
    rw [mul_one] at w
    exact (mul_left_cancel ((mul_one _).trans w)).symm
  refine ⟨fun h => hne (hI (h.trans he₁.symm)), f (1 ⊗ₜ[k] v),
    extend_adj_weight G T e he χ v hv _ (hf v), ?_⟩
  intro h
  apply hv0
  have hm : f (1 ⊗ₜ[k] v) = f (0 : K ⊗[k] Lie k G.val) :=
    h.trans f.toLinearEquiv.map_zero.symm
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff (A := K) k (Specs.Lie k G.val) v).mp (f.injective hm)

private theorem reductiveDimension_baseChange (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (hGK : IsReductive (baseChangedAlgebraicGroup K G)) :
    topologicalKrullDim (baseChangedAlgebraicGroup K G).val.X.left =
      topologicalKrullDim G.val.X.left := by
  let s := identityLieStructure G
  let t := identityLieStructure (baseChangedAlgebraicGroup K G)
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : LieRing (Lie K ((groupBaseChange k K).obj G.val)) := t.lieRing
  letI : LieAlgebra K (Lie K ((groupBaseChange k K).obj G.val)) := t.lieAlgebra
  obtain ⟨f, _⟩ := (identityLieBracketBaseChange k K G).2 s t
  rw [reductive_dimension_eq_lie_finrank _ hGK t, reductive_dimension_eq_lie_finrank _ hG s]
  exact congrArg (fun n : ℕ => (n : WithBot ℕ∞))
    (f.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange)

private def geometricBorelPair (P : SplitBorelPair k) : SplitBorelPair (AlgebraicClosure k) := by
  let K := AlgebraicClosure k
  let H := GeometricGroup P.G
  let T := extendSubgroup K P.T
  have hH : IsReductive H :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
      (K := K) P.G P.reductive.1 P.reductive.2.1).2 P.reductive
  have hs : IsSplitTorus T.group := (split_baseChange_dimension K P.split).1
  have hm : GeometricRadicals.IsMaximalTorus T := P.maximal.choose_spec
  exact splitBorelPair H hH T hs (geometricallyMaximal_of_maximal_split H T hm hs)

private theorem geometricBorelPair_group (P : SplitBorelPair k) :
    (geometricBorelPair P).G = GeometricGroup P.G := rfl

private theorem card_absoluteRoots_geometric (P : SplitBorelPair k) :
    Nat.card (Root P.T) = Nat.card (Root (geometricBorelPair P).T) := by
  let K := AlgebraicClosure k
  let Q := geometricBorelPair P
  obtain ⟨_, hP⟩ := RootData.RootGroups.rootDimension P.G P.reductive P.T P.split P.maximal
  obtain ⟨_, hQ⟩ := RootData.RootGroups.rootDimension Q.G Q.reductive Q.T Q.split Q.maximal
  have hT : topologicalKrullDim Q.T.group.X.left = topologicalKrullDim P.T.group.X.left :=
    (split_baseChange_dimension K P.split).2
  have hG : topologicalKrullDim Q.G.val.X.left = topologicalKrullDim P.G.val.X.left :=
    reductiveDimension_baseChange (K := K) P.G P.reductive Q.reductive
  rw [hG, hT] at hQ
  have he := hP.symm.trans hQ
  obtain ⟨r,⟨e⟩⟩ := P.split
  rw [dimension_of_iso e, standard_torus_dimension r] at he
  have h : r + (absoluteRoots P.T).ncard = r + (absoluteRoots Q.T).ncard := by
    exact_mod_cast he
  simpa only [Nat.card_coe_set_eq] using Nat.add_left_cancel h

private theorem rootSpan_of_datumEquiv {I J X Y U V : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup U] [AddCommGroup V]
    {P : RootPairing I ℤ X Y} {Q : RootPairing J ℤ U V} (e : P.Equiv Q)
    (h : Submodule.span ℤ (Set.range P.root) = ⊤) :
    Submodule.span ℤ (Set.range Q.root) = ⊤ := by
  have hf : e.weightEquiv '' Set.range P.root = Set.range Q.root := by
    rw [← Set.range_comp]
    rw [show ⇑e.weightEquiv ∘ P.root = Q.root ∘ e.indexEquiv from e.root_weightMap]
    exact e.indexEquiv.surjective.range_comp _
  change e.weightEquiv.toLinearMap '' Set.range P.root = Set.range Q.root at hf
  rw [← hf, ← Submodule.map_span, h, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.weightEquiv.surjective
-- Adapted from Mathlib/LinearAlgebra/RootSystem/Hom.lean (RootPairing.Equiv.mk'). Copyright (c) 2024 Scott Carnahan. All rights reserved. Released under Apache 2.0, see LICENSE. MathGenome adapts the root-pairing equivalence construction to integral lattices.
/-- Once the character-lattice comparison carries the roots onto the roots,
the finite spanning root set determines the coroot reflections. -/
private def datumEquivOfRoots {I J X Y U V : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup U] [AddCommGroup V]
    [Module.Free ℤ U] [Finite J]
    (P : RootPairing I ℤ X Y) (Q : RootPairing J ℤ U V)
    (hspan : Submodule.span ℤ (Set.range Q.root) = ⊤)
    (f : X ≃ₗ[ℤ] U) (a : I ≃ J) (hf : ∀ i, f (P.root i) = Q.root (a i)) :
    P.Equiv Q where
  weightMap := f
  coweightMap := Q.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)
  indexEquiv := a
  weight_coweight_transpose := by ext; simp
  root_weightMap := funext hf
  coroot_coweightMap := by
    funext j
    obtain ⟨i,rfl⟩ := a.surjective j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    apply P.flip.toPerfPair.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    apply f.dualMap.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    let p := (P.toLinearMap.flip (P.coroot i)).comp f.symm.toLinearMap
    let q := Q.toLinearMap.flip (Q.coroot (a i))
    change q = p
    apply Module.Dual.eq_of_preReflection_mapsTo (Set.finite_range Q.root) hspan
    · exact Q.coroot_root_two (a i)
    · exact Q.mapsTo_reflection_root (a i)
    · change P.toLinearMap (f.symm (Q.root (a i))) (P.coroot i) = 2
      rw [← hf, LinearEquiv.symm_apply_apply]
      exact P.coroot_root_two i
    · rintro _ ⟨j,rfl⟩
      obtain ⟨l,rfl⟩ := a.surjective j
      refine ⟨a (P.reflectionPerm i l), ?_⟩
      rw [← hf, P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_smul, hf i, hf l]
      simp only [Module.preReflection_apply, p, LinearMap.comp_apply, LinearMap.flip_apply,
        LinearEquiv.coe_coe, ← hf l, LinearEquiv.symm_apply_apply, P.root_coroot_eq_pairing]
  bijective_weightMap := f.bijective
  bijective_coweightMap := (Q.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)).bijective

private theorem geometricDatumEquiv (P : SplitBorelPair k) (D : AttachedDatum P)
    (E : AttachedDatum (geometricBorelPair P))
    (h : Submodule.span ℤ (Set.range E.toBased.datum.root) = ⊤) :
    Nonempty (D.toBased.datum.Equiv E.toBased.datum) := by
  classical
  let K := AlgebraicClosure k
  let Q := geometricBorelPair P
  letI := D.comm
  letI := E.comm
  letI := E.toBased.freeX
  letI : Finite (Root P.T) := D.datum.finiteRoots
  letI : Finite (Root Q.T) := E.datum.finiteRoots
  obtain ⟨e,he⟩ := gm_baseChange k K
  have hb := extendCharacter_bijective P.split e
  let f₀ : Character P.T.group →* Character Q.T.group :=
    { toFun := extendCharacter e
      map_one' := by
        have w := extendCharacter_mul (Unipotent.closedSubgroupAlgebraicGroup P.T).property.1 e 1 1
        rw [mul_one] at w
        exact (mul_left_cancel ((mul_one _).trans w)).symm
      map_mul' := extendCharacter_mul (Unipotent.closedSubgroupAlgebraicGroup P.T).property.1 e }
  let f := MulEquiv.ofBijective f₀ hb
  let a : Root P.T → Root Q.T := fun i =>
    ⟨f i.val, absoluteRoot_baseChange P.G P.T P.split e he i.val i.property⟩
  letI := Fintype.ofFinite (Root P.T)
  letI := Fintype.ofFinite (Root Q.T)
  have ha : Function.Bijective a := (Fintype.bijective_iff_injective_and_card a).mpr
    ⟨fun i j hij => Subtype.ext (f.injective (congrArg Subtype.val hij)),
      by simpa only [← Nat.card_eq_fintype_card] using card_absoluteRoots_geometric P⟩
  letI : Finite E.toBased.I := E.toBased.finiteRoots
  let fX : D.toBased.X ≃ₗ[ℤ] E.toBased.X := f.toAdditive.toIntLinearEquiv
  refine ⟨datumEquivOfRoots D.toBased.datum E.toBased.datum h fX (Equiv.ofBijective a ha) ?_⟩
  intro i
  change fX (D.datum.rootDatum.root i) = E.datum.rootDatum.root (a i)
  rw [D.datum.root_eq, E.datum.root_eq]
  rfl

end ScalarChange

section AbsoluteType

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open LinearAlgebraicGroups.Specs.Pinning
open LinearAlgebraicGroups.Specs.SimplyConnectedLattice (corootLattice)
open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open private splitBorelPair rootFullRank_iff semisimple_iff_corootFullRank restrictCharacters
  restrictCharacters_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private scalarExtendedAutomorphisms
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms

private theorem rootSpan_of_g2Cartan {I X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (B : P.Base) (a : Fin 2 ≃ B.support)
    (h : ∀ i j, P.pairing (a j).val (a i).val = g2CartanMatrix i j)
    (hinj : Function.Injective (restrictCharacters P)) :
    Submodule.span ℤ (Set.range P.root) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  let A := P.toLinearMap x (P.coroot (a 0).val)
  let B₁ := P.toLinearMap x (P.coroot (a 1).val)
  let w := (2*A+3*B₁) • P.root (a 0).val + (A+2*B₁) • P.root (a 1).val
  let L : Y →ₗ[ℤ] ℤ := P.toLinearMap (w - x)
  have zero_on_simple (i : Fin 2) : L (P.coroot (a i).val) = 0 := by
    simp only [L, w, map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, P.root_coroot_eq_pairing, h]
    fin_cases i <;>
      norm_num [g2CartanMatrix, A, B₁] <;> ring
  have hker : Submodule.span ℤ (Set.range P.coroot) ≤ L.ker := by
    rw [← B.span_int_coroot_support, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := a.surjective ⟨i,hi⟩
    change L (P.coroot i) = 0
    exact (congrArg (fun t : B.support ↦ L (P.coroot t.val)) hj).symm.trans (zero_on_simple j)
  have hw : w = x := by
    apply hinj
    ext y
    have hz : P.toLinearMap (w - x) y.val = 0 := hker y.property
    rw [map_sub, LinearMap.sub_apply] at hz
    exact sub_eq_zero.mp hz
  rw [← hw]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

private theorem rootSystem_of_g2Cartan {k : Type u} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (hS : IsSemisimple P.G) (h : HasG2Cartan D.toBased) :
    D.toBased.datum.IsRootSystem := by
  letI := D.comm
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  obtain ⟨a, ha⟩ := h
  let P₀ := D.datum.rootDatum
  have hy := (semisimple_iff_corootFullRank P D).mp hS
  have hx := (rootFullRank_iff P D).mp hS
  have h₁ : Function.Injective (restrictCharacters P₀) :=
    restrictCharacters_injective P₀ ((Submodule.finiteQuotient_iff _).mpr hy)
  have h₂ : Function.Injective (restrictCharacters P₀.flip) :=
    restrictCharacters_injective P₀.flip ((Submodule.finiteQuotient_iff _).mpr hx)
  let a' : Fin 2 ≃ D.base.flip.support := (Equiv.swap 0 1).trans a
  have ha' (i j : Fin 2) : P₀.flip.pairing (a' j).val (a' i).val = g2CartanMatrix i j := by
    change P₀.pairing (a (Equiv.swap 0 1 i)).val (a (Equiv.swap 0 1 j)).val = _
    refine (ha (Equiv.swap 0 1 j) (Equiv.swap 0 1 i)).trans ?_
    fin_cases i <;> fin_cases j <;> decide
  exact ⟨rootSpan_of_g2Cartan P₀ D.base a ha h₁,
    rootSpan_of_g2Cartan P₀.flip D.base.flip a' ha' h₂⟩

private theorem splitModel_rootDatum {k : Type u} [Field k] {C : Type v}
    [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    {n : QuadraticForm k C} (hn : OctonionNormConditions n) (A : AutomorphismGroup k C)
    (F : ZornIsomorphism n) :
    ∃ (Q : SplitBorelPair k) (D : AttachedDatum Q), Q.G = automorphismAlgebraicGroup A ∧
      ∃ (B : D.toBased.datum.Base) (e : Fin 2 ≃ B.support),
        (∀ i j, D.toBased.datum.pairing (e j).val (e i).val = g2CartanMatrix i j) ∧
        D.toBased.datum.IsRootSystem := by
  obtain ⟨hR, _, _, T, ε, hs, hm, h⟩ := splitOctonionStructure hn A F
  let Q := splitBorelPair _ hR T hs hm
  let D := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Q
  letI : IsCommMonObj Q.T.group.X := D.comm
  letI : Finite (LinearAlgebraicGroups.Specs.AbstractPairing.Root Q.T) := D.datum.finiteRoots
  have hQ : HasG2Roots Q.T ε := h
  obtain ⟨e, he⟩ := frameCharacterCoordinates hQ D.datum
  exact ⟨Q,D,rfl,g2_base D.datum.rootDatum e he⟩

private theorem absoluteG2_geometricIso {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsAbsoluteG2 G) (A : AutomorphismGroup k (Zorn k)) :
    Nonempty ((GeometricGroup G).val ≅ (GeometricGroup (automorphismAlgebraicGroup A)).val) := by
  let K := AlgebraicClosure k
  obtain ⟨hS, P, hP, D, a, ha⟩ := hG
  have hS' : IsSemisimple P.G := hP ▸
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.semisimpleFieldExtension
      (K := K) G hS.1 hS.2.1).mpr hS
  have hDat : HasG2Cartan D.toBased := ⟨a, ha⟩
  letI : D.toBased.datum.IsRootSystem := rootSystem_of_g2Cartan D hS' hDat
  letI := D.toBased.reduced
  letI := D.toBased.finiteRoots
  have hn := Composition.octonion_norm_baseChange
    (Composition.Zorn.isOctonion k) K
  letI := (Composition.Zorn.isOctonion k).projective
  obtain ⟨F⟩ := algebraicallyClosedSplit hn
  let A' := scalarExtendedAutomorphisms (K := K) A
  obtain ⟨Q, E, hQ, B, b, hb, hE⟩ := splitModel_rootDatum hn A' F
  letI := hE
  letI := E.toBased.reduced
  letI := E.toBased.finiteRoots
  let j := a.symm.trans b
  have hm (i t : D.toBased.base.support) :
      B.cartanMatrix (j i) (j t) = D.toBased.base.cartanMatrix i t := by
    obtain ⟨i, rfl⟩ := a.surjective i
    obtain ⟨t, rfl⟩ := a.surjective t
    change E.toBased.datum.pairingIn ℤ (b (a.symm (a i))).val (b (a.symm (a t))).val =
      D.toBased.datum.pairingIn ℤ (a i).val (a t).val
    simp only [Equiv.symm_apply_apply]
    have h₁ : E.toBased.datum.pairingIn ℤ (b i).val (b t).val =
        E.toBased.datum.pairing (b i).val (b t).val :=
      E.toBased.datum.algebraMap_pairingIn ℤ _ _
    have h₂ : D.toBased.datum.pairingIn ℤ (a i).val (a t).val =
        D.toBased.datum.pairing (a i).val (a t).val :=
      D.toBased.datum.algebraMap_pairingIn ℤ _ _
    exact h₁.trans ((hb t i).trans ((ha t i).symm.trans h₂.symm))
  let f := D.toBased.base.equivOfCartanMatrixEq B j hm
  obtain ⟨e⟩ := (LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 K).2.1
    P Q D E |>.mpr ⟨f⟩
  have hIso : Nonempty (P.G.val ≅ Q.G.val) := ⟨e⟩
  rw [hP, hQ] at hIso
  exact hIso

open private groupBaseChangeTower
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private splitTorus_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
open private inverseBaseChangeIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
private theorem torus_split_of_sepClosed {k : Type u} [Field k] [IsSepClosed k]
    {T : GroupScheme k} (hT : Specs.GeometricRadicals.IsTorus T) : IsSplitTorus T := by
  obtain ⟨E, _, _, _, h⟩ := hT
  let f : E →ₐ[k] k := IsSepClosed.lift
  letI : Algebra E k := f.toRingHom.toAlgebra
  let q := inverseBaseChangeIso (K := E) (fun x : k => f.commutes x)
  obtain ⟨r, ⟨g⟩⟩ := splitTorus_baseChange (k := E) (K := k) h
  exact ⟨r, ⟨(q.app T).symm ≪≫ g⟩⟩

private def sepClosedBorelPair {k : Type u} [Field k] [IsSepClosed k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) : SplitBorelPair k := by
  letI := hG.2.1
  let hC := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  let h := LinearAlgebraicGroups.MaximalToriExist.geometricallyMaximalTorusExists G hG.1 hC
  exact splitBorelPair G hG h.choose (torus_split_of_sepClosed (k := k) h.choose_spec.1) h.choose_spec.2

private theorem sepClosedBorelPair_group {k : Type u} [Field k] [IsSepClosed k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) :
    (sepClosedBorelPair G hG).G = G := rfl

/-- The geometric Cartan type determines the separable splitting model. -/
theorem absoluteG2IsForm : AbsoluteG2IsForm.{u} := by
  intro k _ G hG
  let S := SeparableClosure k
  let K := AlgebraicClosure k
  let L := AlgebraicClosure S
  have hn := Composition.Zorn.isOctonion k
  obtain ⟨A, _⟩ := Composition.OctonionAutomorphisms.octonionAutomorphisms hn
  let H := automorphismAlgebraicGroup A
  let Gs := baseChangedAlgebraicGroup S G
  let Hs := baseChangedAlgebraicGroup S H
  have hRG := reductive_of_semisimple G hG.1
  obtain ⟨hRH, _⟩ := octonionAutomorphismGroup_reductive_semisimple hn A
  have hGs : IsReductive Gs :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
      (K := S) G hRG.1 hRG.2.1).mpr hRG
  have hHs : IsReductive Hs :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
      (K := S) H hRH.1 hRH.2.1).mpr hRH
  let P := sepClosedBorelPair Gs hGs
  let Q := sepClosedBorelPair Hs hHs
  let Pg := geometricBorelPair P
  let Qg := geometricBorelPair Q
  have hP : P.G = Gs := sepClosedBorelPair_group Gs hGs
  have hQ : Q.G = Hs := sepClosedBorelPair_group Hs hHs
  have hPg : Pg.G = GeometricGroup Gs := (geometricBorelPair_group P).trans (congrArg _ hP)
  have hQg : Qg.G = GeometricGroup Hs := (geometricBorelPair_group Q).trans (congrArg _ hQ)
  letI : Algebra S L := inferInstanceAs (Algebra S (AlgebraicClosure S))
  letI : Algebra k L := inferInstanceAs (Algebra k (AlgebraicClosure S))
  let j : K →ₐ[k] L := IsAlgClosed.lift
  letI : Algebra K L := j.toRingHom.toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let tS := groupBaseChangeTower (k := k) (K := S) L
  let tK := groupBaseChangeTower (k := k) (K := K) L
  obtain ⟨g⟩ := absoluteG2_geometricIso G hG A
  let gg : Pg.G.val ≅ Qg.G.val := by
    rw [hPg, hQg]
    change ((groupBaseChange S L).obj Gs.val) ≅ ((groupBaseChange S L).obj Hs.val)
    exact (tS.app G.val).symm ≪≫ tK.app G.val ≪≫
      (groupBaseChange K L).mapIso g ≪≫ (tK.app H.val).symm ≪≫ tS.app H.val
  let DP := LinearAlgebraicGroups.Classification.Pinning.attachedDatum P
  let DQ := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Q
  let DPg := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Pg
  let DQg := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Qg
  let hc := LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 L
  obtain ⟨d⟩ := (hc.2.1 Pg Qg DPg DQg).mp ⟨gg⟩
  letI := hn.projective
  let AL := scalarExtendedAutomorphisms (K := L) A
  have hnL := Composition.octonion_norm_baseChange hn L
  obtain ⟨F⟩ := algebraicallyClosedSplit hnL
  obtain ⟨M, DM, hM, _, _, _, hspan⟩ := splitModel_rootDatum hnL AL F
  have eqM : M.G.val ≅ Qg.G.val := by
    rw [hM, hQg]
    change ((groupBaseChange k L).obj H.val) ≅ ((groupBaseChange S L).obj Hs.val)
    exact tS.app H.val
  obtain ⟨dM⟩ := (hc.2.1 M Qg DM DQg).mp ⟨eqM⟩
  have hQspan := rootSpan_of_datumEquiv dM hspan.span_root_eq_top
  have hPspan := rootSpan_of_datumEquiv (d.symm _ _) hQspan
  obtain ⟨dp⟩ := geometricDatumEquiv P DP DPg hPspan
  obtain ⟨dq⟩ := geometricDatumEquiv Q DQ DQg hQspan
  let e := (dq.symm _ _).comp (d.comp dp)
  have hIso := ((LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 S).2.1
    P Q DP DQ).mpr ⟨e⟩
  rw [hP, hQ] at hIso
  exact ⟨A, hIso⟩

end AbsoluteType

end SplitGroup


section SplitForms

open AlgebraicGeometry CategoryTheory Opposite CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup AffineGroupScheme)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsSplitReductive)
open LinearAlgebraicGroups.Specs.AutomorphismSequence (relativePoints innerAut)
open LinearAlgebraicGroups.Specs.RelativeFormComparison (fieldTest transportedAut)
open LinearAlgebraicGroups.Specs.RelativeRank (relativeRank)
open LinearAlgebraicGroups.Specs.Unipotent (baseChangedAlgebraicGroup)
open Composition.OctonionAutomorphismSpecification
open Composition.PeirceSpecification (ZornIsomorphism)
open LinearAlgebraicGroups.Descent (SemilinearAction)
open private automorphismAlgebraicGroup scalarExtendedAutomorphisms
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
open private positive_rank_iff_cocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank

private theorem hasNontrivialSplitCocharacter_iff_relativeRank_pos {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) :
    HasNontrivialSplitCocharacter G.val ↔ 0 < relativeRank G := by
  refine Iff.trans ?_ (positive_rank_iff_cocharacter G).symm
  constructor
  · rintro ⟨c, S, t, ht⟩
    refine ⟨c, ?_⟩
    rintro rfl
    apply ht
    let p : Points (specGroup (groupAlgebra k IntegerCharacters.{u})).X S := t
    exact MonObj.comp_one p
  · rintro ⟨c, hc⟩
    let T := specGroup (groupAlgebra k IntegerCharacters.{u})
    let S := CommAlgCat.of k (groupAlgebra k IntegerCharacters.{u})
    refine ⟨c, S, 𝟙 T.X, ?_⟩
    intro ht
    apply hc
    apply Grp.hom_ext
    change 𝟙 T.X ≫ c.hom.hom = toUnit T.X ≫ η[G.val.X] at ht
    change c.hom.hom = toUnit T.X ≫ η[G.val.X]
    simpa only [Category.id_comp] using ht

theorem splitOctonionGroupStructure : SplitOctonionGroupStructure.{u,v} := by
  intro k _ C _ _ _ _ n hn ⟨F⟩ A
  exact ⟨splitOctonionStructure hn A F, splitOctonionSimplyConnected hn A F⟩

theorem finiteG2InnerTrivialization : FiniteG2InnerTrivialization.{u} := by
  intro k _ G ⟨A,e⟩
  let H := automorphismAlgebraicGroup A
  let n := Composition.ZornSpecification.norm k
  have hn : OctonionNormConditions n := Composition.Zorn.isOctonion k
  let F : ZornIsomorphism n := ⟨LinearEquiv.refl _ _, rfl, fun _ _ => rfl, fun _ => rfl⟩
  obtain ⟨e⟩ := e
  obtain ⟨K,⟨i⟩⟩ := finiteTrivialization H G (SeparableClosure k) e.symm
  have hH : IsAdjointG2 H := splitOctonionStructure hn A F
  have hb := g2_relativeAutomorphisms_inner H hH (fieldTest k K)
  refine ⟨A, K, inferInstance, inferInstance, inferInstance, inferInstance, i, ?_⟩
  intro σ
  exact hb.existsUnique (transportedAut k K i σ)

/-- A form of the split octonion automorphism scheme is obtained from the
fixed octonion algebra for the uniquely lifted inner descent datum. -/
private theorem octonionDescentOfForm : G2OctonionDescentOfForm.{u} := by
  intro k _ G hG
  obtain ⟨A₀, K, _, _, _, _, i, hi⟩ := finiteG2InnerTrivialization G hG
  let H : AffineGroupScheme k := ⟨G.val, G.property.1⟩
  choose c hc using fun σ => (hi σ).exists
  have hLift σ : innerAut (c σ) = transportedAut k K i σ ∧
      ∀ g, innerAut g = transportedAut k K i σ → g = c σ :=
    ⟨hc σ, fun g hg => (hi σ).unique hg (hc σ)⟩
  obtain ⟨_, _, ρ, hρ, h₁, hm, hq⟩ := OctonionInnerAction.octonionInnerAction A₀ H i c hLift
  have hn := octonion_norm_baseChange (Zorn.isOctonion k) K
  let C := fixedOctonionAlgebra ρ h₁ hm
  let q : QuadraticForm k C := fixedCompositionNorm ρ hq
  have hqNorm : OctonionNormConditions q := fixedCompositionNorm_octonion ρ hq h₁ hm hn
  letI := hqNorm.projective
  let e : (K ⊗[k] C) ≃ₗ[K] (K ⊗[k] Zorn k) := ρ.descentEquiv
  obtain ⟨he₁, hem, hen⟩ := fixedOctonion_descentEquiv ρ hq h₁ hm hn
  have hEquiv σ x :
      (A₀.subgroupPoints (CommAlgCat.of k K) (c σ)).val.val
        ((SemilinearAction.scalarExtension (k := k) (K := K) (Zorn k)).act σ (e x)) =
      e ((SemilinearAction.scalarExtension (k := k) (K := K) C).act σ x) :=
    (hρ σ (e x)).symm.trans (ρ.descent_equivariant σ x).symm
  obtain ⟨A, _⟩ := Composition.OctonionAutomorphisms.octonionAutomorphisms hqNorm
  obtain ⟨j, _, hj⟩ := OctonionEquivariantAutomorphisms.equivariantAutomorphisms
    hqNorm A₀ A c e he₁ hem hen hEquiv
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, q, hqNorm, A, ?_⟩
  exact isomorphicOfSameDisplacement
    (G₀ := automorphismAlgebraicGroup A₀) (G := G) (H := automorphismAlgebraicGroup A) i j
    (fun σ => (hc σ).symm.trans (hj σ).symm)

theorem g2OctonionDescent : G2OctonionDescent.{u} := by
  intro k _ G hG
  exact octonionDescentOfForm G (absoluteG2IsForm G hG)

private theorem g2FormBaseChangeSplit {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (hG : IsAbsoluteG2 G)
    (hsplit : ∀ {C : Type u} [NonAssocRing C] [Module K C] [IsScalarTower K C C]
      [SMulCommClass K C C] {n : QuadraticForm K C},
      OctonionNormConditions n → Nonempty (ZornIsomorphism n)) :
    IsSplitReductive (baseChangedAlgebraicGroup K G) := by
  obtain ⟨C, _, _, _, _, n, hn, A, ⟨e⟩⟩ := g2OctonionDescent G hG
  let : Module.Projective k C := hn.projective
  let B := scalarExtendedAutomorphisms (K := K) (automorphismGroupAlongIso G A e)
  have hnK := octonion_norm_baseChange hn K
  obtain ⟨F⟩ := hsplit hnK
  exact splitReductiveOfZorn (automorphismAlgebraicGroup B) B (Iso.refl _) hnK F

theorem finiteCompletionG2Split : FiniteCompletionG2Split.{u,w} := by
  intro k _ G hG D p
  letI : Algebra k (D.FiniteCompletion p) := (D.embedding (.inl p)).toAlgebra
  exact g2FormBaseChangeSplit G hG (fun hn => finiteCompletionSplit D p hn)

theorem complexCompletionG2Split : ComplexCompletionG2Split.{u} := by
  intro k _ _ G hG p hp
  obtain ⟨e, _⟩ := numberComplexCompletion p hp
  letI : IsAlgClosed p.Completion := ⟨fun f =>
    Polynomial.Splits.of_splits_map_of_injective e.injective
      (IsAlgClosed.splits (f.map e.toRingHom)) (fun x _ => e.surjective x)⟩
  exact g2FormBaseChangeSplit G hG algebraicallyClosedSplit

theorem realG2SplitOrCompactConnected : RealG2SplitOrCompactConnected := by
  intro G hG
  obtain ⟨C, _, _, _, _, n, hn, A, ⟨e⟩⟩ := g2OctonionDescent G hG
  rcases realSplitOrPositive hn with hsplit | hp
  · obtain ⟨F⟩ := hsplit
    exact Or.inl (splitReductiveOfZorn G A e hn F)
  · exact Or.inr ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, n, hn, hp,
      ⟨A, ⟨e⟩⟩, fun b => ⟨realCompact hn hp b, realConnected hn hp b⟩⟩

theorem isotropicG2Split_of_descent (descent : G2OctonionDescent.{u}) : IsotropicG2Split.{u} := by
  intro k _ G hG hrank
  have hc := (hasNontrivialSplitCocharacter_iff_relativeRank_pos G).mpr hrank
  obtain ⟨C, _, _, _, _, n, hn, A, ⟨e⟩⟩ := descent G hG
  let B := automorphismGroupAlongIso G A e
  obtain ⟨F⟩ := octonionSplitOfCocharacter hn B hc
  exact splitReductiveOfZorn G A e hn F

theorem isotropicG2StrongApproximation_of_descent (descent : G2OctonionDescent.{u}) :
    IsotropicG2StrongApproximation.{u,w} := by
  intro k _ G hG hrank D i S hS
  have hc := (hasNontrivialSplitCocharacter_iff_relativeRank_pos G).mpr hrank
  obtain ⟨C, _, _, _, _, n, hn, A, ⟨e⟩⟩ := descent G hG
  let B := automorphismGroupAlongIso G A e
  obtain ⟨F⟩ := octonionSplitOfCocharacter hn B hc
  have h : IsAdjointG2 G := splitOctonionStructure hn B F
  have hsc := splitOctonionSimplyConnected hn B F
  obtain ⟨_, hs, _, T, _, ht, hm, _⟩ := h
  exact LinearAlgebraicGroups.Arithmetic.SplitApproximation.splitStrongApproximation
    G hs hsc T ht hm D i S hS

theorem isotropicG2Split : IsotropicG2Split.{u} :=
  isotropicG2Split_of_descent g2OctonionDescent

theorem isotropicG2StrongApproximation : IsotropicG2StrongApproximation.{u,w} :=
  isotropicG2StrongApproximation_of_descent g2OctonionDescent

end SplitForms

end LinearAlgebraicGroups.Arithmetic.OctonionForms
