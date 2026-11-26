import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.PeirceFrames
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.ZornModel
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Basis.SMul

import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.BaseChange

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.Smooth.Pi

namespace LinearAlgebraicGroups.Composition.Peirce

open private polar_quadratic_equation norm_add from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.Adjoints

open scoped Matrix TensorProduct

universe u v w z w'

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

abbrev QuadricPoint := @PeirceSpecification.QuadricPoint
abbrev corner := @PeirceSpecification.corner
abbrev pairing := @PeirceSpecification.pairing

variable {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

local notation "τ" => compositionTrace n
local notation "B" => n.polarBilin
local notation "f[" e "]" => PeirceSpecification.complement e

lemma trace_point (e : QuadricPoint n) : τ e.val = 1 := e.property.1

lemma norm_point (e : QuadricPoint n) : n e.val = 0 := e.property.2

lemma conjugate_point (e : QuadricPoint n) : conjugate n e.val = f[e] := by
  rw [conjugate_apply, trace_point, one_smul]
  rfl

lemma trace_complement (h : NormLaws n) (e : QuadricPoint n) : τ f[e] = 1 := by
  rw [← conjugate_point, compositionTrace_conjugate h, trace_point]

lemma norm_complement (h : NormLaws n) (e : QuadricPoint n) : n f[e] = 0 := by
  rw [← conjugate_point, norm_conjugate h, norm_point]

lemma point_mul_self (h : NormLaws n) (e : QuadricPoint n) : e.val * e.val = e.val := by
  simpa only [trace_point, norm_point, one_smul, zero_smul, add_zero, sub_eq_zero] using
    composition_quadratic_equation h e.val

lemma complement_mul_self (h : NormLaws n) (e : QuadricPoint n) : f[e] * f[e] = f[e] := by
  simpa only [trace_complement h, norm_complement h, one_smul, zero_smul, add_zero, sub_eq_zero]
    using composition_quadratic_equation h f[e]

lemma point_mul_complement (h : NormLaws n) (e : QuadricPoint n) : e.val * f[e] = 0 := by
  rw [← conjugate_point, (mul_conjugate h e.val).1, norm_point, zero_smul]

lemma complement_mul_point (h : NormLaws n) (e : QuadricPoint n) : f[e] * e.val = 0 := by
  rw [← conjugate_point, (mul_conjugate h e.val).2, norm_point, zero_smul]

lemma point_add_complement (e : QuadricPoint n) : e.val + f[e] = 1 := by
  change e.val + (1 - e.val) = 1
  abel

lemma polar_point_self (e : QuadricPoint n) : B e.val e.val = 0 := by
  simp [norm_point]

lemma polar_point_complement (e : QuadricPoint n) : B e.val f[e] = 1 := by
  change B e.val (1 - e.val) = 1
  rw [map_sub, polar_point_self, sub_zero, ← compositionTrace_apply, trace_point]

theorem complementary_idempotents : PeirceSpecification.complementaryIdempotents := by
  intro R C _ _ _ _ _ n h e
  have h := (IsOctonionNorm.toNormLaws h)
  exact ⟨trace_complement h e, norm_complement h e, point_mul_self h e,
    complement_mul_self h e, point_mul_complement h e, complement_mul_point h e,
    point_add_complement e⟩

theorem independent_differentials : PeirceSpecification.independentDifferentials := by
  intro R C _ _ _ _ _ n h e
  rintro ⟨a, b⟩
  refine ⟨(a - b) • e.val + b • f[e], ?_⟩
  apply Prod.ext
  · change compositionTrace n ((a - b) • e.val + b • f[e]) = a
    rw [map_add, map_smul, map_smul, trace_point, trace_complement (IsOctonionNorm.toNormLaws h)]
    simp
  · change n.polarBilin e.val ((a - b) • e.val + b • f[e]) = b
    rw [map_add, map_smul, map_smul, polar_point_self, polar_point_complement]
    simp

/-- Correct an approximate quadric point whose two scalar errors lie in a square-zero ideal. -/
lemma square_zero_correction (h : NormLaws n) (x : C)
    (hd : (τ x - 1) * (τ x - 1) = 0) (hb : n x * n x = 0)
    (hdb : (τ x - 1) * n x = 0) :
    ∃ e : QuadricPoint n, e.val = (1 - (τ x - 1) + 2 * n x) • x - n x • (1 : C) := by
  let d := τ x - 1
  let b := n x
  let a := 1 - d + 2 * b
  have ht : τ x = 1 + d := by dsimp [d]; ring
  have hdb' : d * b = 0 := hdb
  have hb' : b * b = 0 := hb
  have hd' : d * d = 0 := hd
  have hab : a * b = b := by
    dsimp only [a]
    linear_combination -hdb' + 2 * hb'
  refine ⟨⟨a • x - b • (1 : C), ?_, ?_⟩, rfl⟩
  · change τ (a • x - b • (1 : C)) = 1
    rw [map_sub, map_smul, map_smul, compositionTrace_one h, ht, smul_eq_mul, smul_eq_mul]
    dsimp only [a]
    linear_combination -hd' + 2 * hdb'
  · rw [sub_eq_add_neg, ← neg_smul, norm_add, QuadraticMap.map_smul, norm_scalar h,
      LinearMap.map_smul₂, map_smul, ← compositionTrace_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    change a * a * b + (-b) ^ 2 + a * (-b * τ x) = 0
    rw [mul_assoc a a b, hab, hab, neg_sq, pow_two b, hb', add_zero,
      ← mul_assoc, mul_neg, hab, ht]
    linear_combination -hdb'


lemma left_projection (h : NormLaws n) (e : QuadricPoint n) (x : C) :
    e.val * (e.val * x) = e.val * x := by
  symm
  simpa only [associator_apply, point_mul_self h, sub_eq_zero] using
    ((composition_isAlternative h) e.val x).1

lemma right_projection (h : NormLaws n) (e : QuadricPoint n) (x : C) :
    (x * e.val) * e.val = x * e.val := by
  simpa only [associator_apply, point_mul_self h, sub_eq_zero] using
    ((composition_isAlternative h) e.val x).2

lemma commute_projections (h : NormLaws n) (e : QuadricPoint n) (x : C) :
    e.val * (x * e.val) = (e.val * x) * e.val :=
  ((composition_isAlternative h).flexible e.val x).symm

theorem projections : PeirceSpecification.projections := by
  intro R C _ _ _ _ _ n h e
  exact ⟨LinearMap.ext (left_projection (IsOctonionNorm.toNormLaws h) e),
    LinearMap.ext (right_projection (IsOctonionNorm.toNormLaws h) e),
    LinearMap.ext (commute_projections (IsOctonionNorm.toNormLaws h) e)⟩

lemma mem_corner_iff (e : QuadricPoint n) (i j : R) (x : C) :
    x ∈ corner e i j ↔ e.val * x = i • x ∧ x * e.val = j • x := by
  change (e.val * x - i • x = 0 ∧ x * e.val - j • x = 0) ↔ _
  simp only [sub_eq_zero]

lemma trace_smul_point (e : QuadricPoint n) (r : R) : τ (r • e.val) = r := by
  rw [map_smul, trace_point, smul_eq_mul, mul_one]

lemma trace_smul_complement (h : NormLaws n) (e : QuadricPoint n) (r : R) :
    τ (r • f[e]) = r := by
  rw [map_smul, trace_complement h, smul_eq_mul, mul_one]

lemma point_linearization (h : NormLaws n) (e : QuadricPoint n) (x : C) :
    e.val * x + x * e.val = x + τ x • e.val - B e.val x • (1 : C) := by
  simpa only [trace_point, one_smul] using polar_quadratic_equation h e.val x

lemma polar_point_eq_trace_of_left_zero (h : NormLaws n) (e : QuadricPoint n)
    {x : C} (hx : e.val * x = 0) : B e.val x = τ x := by
  have H : B x e.val = τ x := by
    have E : B (e.val * x) 1 = B x (conjugate n e.val * 1) :=
      left_mul_adjoint h e.val x 1
    rw [hx, mul_one, conjugate_point, map_zero, LinearMap.zero_apply] at E
    change 0 = B x (1 - e.val) at E
    exact (sub_eq_zero.mp (by simpa only [map_sub, ← compositionTrace_apply] using E.symm)).symm
  rw [← H]
  exact QuadraticMap.polar_comm n _ _

lemma polar_point_eq_zero_of_right_one (h : NormLaws n) (e : QuadricPoint n)
    {x : C} (hx : x * e.val = x) : B e.val x = 0 := by
  have E : B (x * e.val) e.val = B x (e.val * conjugate n e.val) :=
    right_mul_adjoint h e.val x e.val
  rw [hx, conjugate_point, point_mul_complement h, map_zero] at E
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm n x e.val] using E

lemma polar_point_eq_zero_of_left_one (h : NormLaws n) (e : QuadricPoint n)
    {x : C} (hx : e.val * x = x) : B e.val x = 0 := by
  have E : B (e.val * x) e.val = B x (conjugate n e.val * e.val) :=
    left_mul_adjoint h e.val x e.val
  rw [hx, conjugate_point, complement_mul_point h, map_zero] at E
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm n x e.val] using E

lemma eq_trace_smul_point (h : NormLaws n) (e : QuadricPoint n)
    {x : C} (hx : x ∈ corner e 1 1) : x = τ x • e.val := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff e 1 1 x).mp hx
  simp only [one_smul] at hl hr
  have E := point_linearization h e x
  rw [hl, hr, polar_point_eq_zero_of_left_one h e hl, zero_smul, sub_zero] at E
  exact add_left_cancel E

lemma eq_trace_smul_complement (h : NormLaws n) (e : QuadricPoint n)
    {x : C} (hx : x ∈ corner e 0 0) : x = τ x • f[e] := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff e 0 0 x).mp hx
  simp only [zero_smul] at hl hr
  have E := point_linearization h e x
  rw [hl, hr, zero_add, polar_point_eq_trace_of_left_zero h e hl] at E
  change x = τ x • (1 - e.val)
  rw [smul_sub]
  exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp E.symm)

theorem scalar_corners : PeirceSpecification.scalarCorners := by
  intro R C _ _ _ _ _ n h e
  have h := (IsOctonionNorm.toNormLaws h)
  constructor
  · apply le_antisymm
    · intro x hx
      exact Submodule.mem_span_singleton.mpr ⟨compositionTrace n x, (eq_trace_smul_point h e hx).symm⟩
    · rw [Submodule.span_singleton_le_iff_mem, mem_corner_iff]
      simp [point_mul_self h]
  · apply le_antisymm
    · intro x hx
      exact Submodule.mem_span_singleton.mpr ⟨compositionTrace n x, (eq_trace_smul_complement h e hx).symm⟩
    · rw [Submodule.span_singleton_le_iff_mem, mem_corner_iff]
      simp [point_mul_complement h, complement_mul_point h]

lemma trace_upper (h : NormLaws n) (e : QuadricPoint n) (x : corner e 1 0) :
    τ x.val = 0 := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff e 1 0 x.val).mp x.property
  simp only [one_smul, zero_smul] at hl hr
  have E := point_linearization h e x.val
  rw [hl, hr, add_zero, polar_point_eq_zero_of_left_one h e hl, zero_smul, sub_zero] at E
  have H : τ x.val • e.val = 0 := by
    exact add_left_cancel (E.symm.trans (add_zero x.val).symm)
  simpa only [trace_smul_point, map_zero] using congrArg (compositionTrace n) H

lemma trace_lower (h : NormLaws n) (e : QuadricPoint n) (x : corner e 0 1) :
    τ x.val = 0 := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff e 0 1 x.val).mp x.property
  simp only [one_smul, zero_smul] at hl hr
  exact (polar_point_eq_trace_of_left_zero h e hl).symm.trans
    (polar_point_eq_zero_of_right_one h e hr)

lemma norm_upper (h : NormLaws n) (e : QuadricPoint n) (x : corner e 1 0) :
    n x.val = 0 := by
  have hl : e.val * x.val = x.val := by
    simpa only [one_smul] using ((mem_corner_iff e 1 0 x.val).mp x.property).1
  rw [← hl, h.map_mul, norm_point, zero_mul]

lemma norm_lower (h : NormLaws n) (e : QuadricPoint n) (x : corner e 0 1) :
    n x.val = 0 := by
  have hr : x.val * e.val = x.val := by
    simpa only [one_smul] using ((mem_corner_iff e 0 1 x.val).mp x.property).2
  rw [← hr, h.map_mul, norm_point, mul_zero]

lemma product_mem_corner (h : NormLaws n) (e : QuadricPoint n)
    {i j s t : R} {x y : C} (hx : x ∈ corner e i j) (hy : y ∈ corner e s t) :
    x * y ∈ corner e (i + j - s) (t + s - j) := by
  obtain ⟨hxL, hxR⟩ := (mem_corner_iff e i j x).mp hx
  obtain ⟨hyL, hyR⟩ := (mem_corner_iff e s t y).mp hy
  have alt := composition_isAlternative h
  apply (mem_corner_iff e _ _ _).mpr
  constructor
  · have H := alt.associator_swap_left e.val x y
    rw [associator_apply, associator_apply, hxL, hxR, hyL, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm] at H
    calc
      e.val * (x * y) = i • (x * y) - (i • (x * y) - e.val * (x * y)) := by abel
      _ = (i + j - s) • (x * y) := by rw [H, sub_smul, add_smul]; abel
  · have H := alt.associator_swap_right x y e.val
    rw [associator_apply, associator_apply, hyR, hxR, hyL, smul_mul_assoc, mul_smul_comm,
      mul_smul_comm] at H
    calc
      (x * y) * e.val = ((x * y) * e.val - t • (x * y)) + t • (x * y) := by abel
      _ = (t + s - j) • (x * y) := by rw [H, sub_smul, add_smul]; abel

lemma pairing_apply (e : QuadricPoint n) (x : corner e 1 0) (y : corner e 0 1) :
    pairing e x y = -B x.val y.val := rfl

theorem off_diagonal_products : PeirceSpecification.offDiagonalProducts := by
  intro R C _ _ _ _ _ n hn e
  have h := IsOctonionNorm.toNormLaws hn
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simpa only [add_zero, zero_add, sub_self, sub_zero] using
      product_mem_corner h e x.property y.property
  · intro x y
    simpa only [add_zero, zero_add, sub_self, sub_zero] using
      product_mem_corner h e x.property y.property
  · intro x y
    have hxy : x.val * y.val ∈ corner e 1 1 := by
      simpa only [add_zero, sub_zero] using product_mem_corner h e x.property y.property
    have hyx : y.val * x.val ∈ corner e 0 0 := by
      simpa only [zero_add, sub_self] using product_mem_corner h e y.property x.property
    have ht : compositionTrace n (x.val * y.val) = pairing e x y := by
      rw [compositionTrace_mul_formula h, trace_upper h, trace_lower h, zero_mul, zero_sub,
        pairing_apply]
    rw [eq_trace_smul_point h e hxy, eq_trace_smul_complement h e hyx,
      compositionTrace_mul_comm h y.val x.val, ht]
    exact ⟨rfl, rfl⟩

private def selected (e : QuadricPoint n) : Bool → C
  | true => e.val
  | false => f[e]

open PeirceSpecification (eigenvalue)

private lemma selected_left (h : NormLaws n) (e : QuadricPoint n) (i : Bool) (z : C) :
    e.val * (selected e i * z) = eigenvalue R i • (selected e i * z) := by
  cases i with
  | true => simpa only [selected, eigenvalue, one_smul] using left_projection h e z
  | false =>
    change e.val * ((1 - e.val) * z) = (0 : R) • ((1 - e.val) * z)
    rw [sub_mul, one_mul, mul_sub, left_projection h, sub_self, zero_smul]

private lemma selected_right (h : NormLaws n) (e : QuadricPoint n) (j : Bool) (z : C) :
    (z * selected e j) * e.val = eigenvalue R j • (z * selected e j) := by
  cases j with
  | true => simpa only [selected, eigenvalue, one_smul] using right_projection h e z
  | false =>
    change (z * (1 - e.val)) * e.val = (0 : R) • (z * (1 - e.val))
    rw [mul_sub, mul_one, sub_mul, right_projection h, sub_self, zero_smul]

private lemma selected_commute (h : NormLaws n) (e : QuadricPoint n) (i : Bool) (z : C) :
    (selected e i * z) * e.val = selected e i * (z * e.val) := by
  cases i with
  | true => exact (commute_projections h e z).symm
  | false =>
    change ((1 - e.val) * z) * e.val = (1 - e.val) * (z * e.val)
    rw [sub_mul, one_mul, sub_mul, sub_mul, one_mul, commute_projections h]

private def component (h : NormLaws n) (e : QuadricPoint n) (i j : Bool) :
    C →ₗ[R] corner e (eigenvalue R i) (eigenvalue R j) :=
  ((LinearMap.mul R C (selected e i)).comp ((LinearMap.mul R C).flip (selected e j))).codRestrict
    _ fun z => (mem_corner_iff e _ _ _).mpr ⟨selected_left h e i _,
      by rw [LinearMap.comp_apply]; change (selected e i * (z * selected e j)) * e.val = _
         rw [selected_commute h, selected_right h, mul_smul_comm]; rfl⟩

private lemma component_apply (h : NormLaws n) (e : QuadricPoint n) (i j : Bool) (x : C) :
    (component h e i j x).val = selected e i * (x * selected e j) := rfl

private lemma component_of_corner (h : NormLaws n) (e : QuadricPoint n) (i j s t : Bool)
    (x : corner e (eigenvalue R s) (eigenvalue R t)) :
    (component h e i j x.val).val = if i = s ∧ j = t then x.val else 0 := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff e _ _ _).mp x.property
  rw [component_apply]
  have L (a : Bool) : selected e a * x.val = if a = s then x.val else 0 := by
    cases a <;> cases s <;>
      simp_all only [selected, eigenvalue, zero_smul, one_smul, Bool.false_eq_true,
        Bool.true_eq_false, ite_false, ite_true, PeirceSpecification.complement, sub_mul,
        one_mul, sub_zero, sub_self]
  have P (b : Bool) : x.val * selected e b = if b = t then x.val else 0 := by
    cases b <;> cases t <;>
      simp_all only [selected, eigenvalue, zero_smul, one_smul, Bool.false_eq_true,
        Bool.true_eq_false, ite_false, ite_true, PeirceSpecification.complement, mul_sub,
        mul_one, sub_zero, sub_self]
  rw [P]
  by_cases hj : j = t <;> simp [hj, L]

private lemma components_sum (h : NormLaws n) (e : QuadricPoint n) (x : C) :
    (component h e true true x).val + (component h e true false x).val +
    (component h e false true x).val + (component h e false false x).val = x := by
  simp only [component_apply, selected, PeirceSpecification.complement, sub_mul, mul_sub,
    one_mul, mul_one]
  abel

private lemma point_in_corner (h : NormLaws n) (e : QuadricPoint n) :
    e.val ∈ corner e (eigenvalue R true) (eigenvalue R true) :=
  (mem_corner_iff e _ _ _).mpr (by simp [eigenvalue, point_mul_self h])

private lemma complement_in_corner (h : NormLaws n) (e : QuadricPoint n) :
    f[e] ∈ corner e (eigenvalue R false) (eigenvalue R false) :=
  (mem_corner_iff e _ _ _).mpr
    (by simp [eigenvalue, point_mul_complement h, complement_mul_point h])

private lemma component_point (h : NormLaws n) (e : QuadricPoint n) (i j : Bool) :
    (component h e i j e.val).val = if i = true ∧ j = true then e.val else 0 :=
  component_of_corner h e i j true true ⟨e.val, point_in_corner h e⟩

private lemma component_complement (h : NormLaws n) (e : QuadricPoint n) (i j : Bool) :
    (component h e i j f[e]).val = if i = false ∧ j = false then f[e] else 0 :=
  component_of_corner h e i j false false ⟨f[e], complement_in_corner h e⟩

local notation "V[" e "]" => corner e (1 : R) 0
local notation "W[" e "]" => corner e (0 : R) 1

private def assemble (e : QuadricPoint n) : (R × V[e] × W[e] × R) →ₗ[R] C :=
  ((LinearMap.id (R := R) (M := R)).smulRight e.val).coprod
    ((corner e (1 : R) 0).subtype.coprod
      ((corner e (0 : R) 1).subtype.coprod (LinearMap.id.smulRight f[e])))

private lemma assemble_apply (e : QuadricPoint n) (x : R × V[e] × W[e] × R) :
    assemble e x = x.1 • e.val + (x.2.1.val + (x.2.2.1.val + x.2.2.2 • f[e])) := rfl

private def disassemble (h : NormLaws n) (e : QuadricPoint n) :
    C →ₗ[R] (R × V[e] × W[e] × R) :=
  ((compositionTrace n).comp ((corner e _ _).subtype.comp (component h e true true))).prod
    ((component h e true false).prod ((component h e false true).prod
      ((compositionTrace n).comp ((corner e _ _).subtype.comp (component h e false false)))))

private lemma disassemble_left (h : NormLaws n) (e : QuadricPoint n)
    (x : R × V[e] × W[e] × R) : disassemble h e (assemble e x) = x := by
  rcases x with ⟨a, x, y, b⟩
  have X (i j : Bool) := component_of_corner h e i j true false x
  have Y (i j : Bool) := component_of_corner h e i j false true y
  have P := component_point h e
  have Q := component_complement h e
  rw [assemble_apply]
  refine Prod.ext ?_ (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) ?_))
  · change τ (component h e true true _).val = a
    rw [map_add, map_add, map_add, map_smul, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul, X, Y, P, Q]
    simp [trace_point]
  · change (component h e true false _).val = x.val
    rw [map_add, map_add, map_add, map_smul, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul, X, Y, P, Q]
    simp
  · change (component h e false true _).val = y.val
    rw [map_add, map_add, map_add, map_smul, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul, X, Y, P, Q]
    simp
  · change τ (component h e false false _).val = b
    rw [map_add, map_add, map_add, map_smul, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul, X, Y, P, Q]
    simp [trace_smul_complement h]

private lemma disassemble_right (h : NormLaws n) (e : QuadricPoint n) (x : C) :
    assemble e (disassemble h e x) = x := by
  rw [assemble_apply]
  change τ (component h e true true x).val • e.val +
    ((component h e true false x).val +
    ((component h e false true x).val + τ (component h e false false x).val • f[e])) = x
  have P := eq_trace_smul_point h e (component h e true true x).property
  have Q := eq_trace_smul_complement h e (component h e false false x).property
  rw [← P, ← Q, ← add_assoc, ← add_assoc]
  exact components_sum h e x

/-- The Peirce coordinate isomorphism sends a quadruple to the sum of its four components. -/
def decomposition (h : NormLaws n) (e : QuadricPoint n) :
    (R × V[e] × W[e] × R) ≃ₗ[R] C :=
  LinearEquiv.ofLinearMap (assemble e) (disassemble h e)
    (LinearMap.ext (disassemble_right h e)) (LinearMap.ext (disassemble_left h e))

theorem decomposition_apply (h : NormLaws n) (e : QuadricPoint n)
    (x : R × V[e] × W[e] × R) :
    decomposition h e x = x.1 • e.val + x.2.1.val + x.2.2.1.val + x.2.2.2 • f[e] := by
  change assemble e x = _
  rw [assemble_apply]
  abel

theorem direct_decomposition : PeirceSpecification.directDecomposition := by
  intro R C _ _ _ _ _ n hn e
  have h := IsOctonionNorm.toNormLaws hn
  exact ⟨decomposition h e, decomposition_apply h e⟩

private lemma polar_symm (x y : C) : B x y = B y x := QuadraticMap.polar_comm n _ _

private lemma polar_upper_component (h : NormLaws n) (e : QuadricPoint n)
    (x : V[e]) (z : C) : B x.val z = B x.val (component h e false true z).val := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff e 1 0 x.val).mp x.property
  simp only [one_smul, zero_smul] at hl hr
  have hf : x.val * f[e] = x.val := by
    change x.val * (1 - e.val) = _
    rw [mul_sub, mul_one, hr, sub_zero]
  have adjR : B (x.val * f[e]) z = B x.val (z * conjugate n f[e]) :=
    right_mul_adjoint h f[e] x.val z
  rw [hf, ← conjugate_point e, conjugate_involutive h] at adjR
  have adjL : B (e.val * x.val) (z * e.val) = B x.val (conjugate n e.val * (z * e.val)) :=
    left_mul_adjoint h e.val x.val (z * e.val)
  rw [hl, conjugate_point] at adjL
  exact adjR.trans adjL

private lemma polar_lower_component (h : NormLaws n) (e : QuadricPoint n)
    (x : W[e]) (z : C) : B x.val z = B x.val (component h e true false z).val := by
  obtain ⟨hl, hr⟩ := (mem_corner_iff e 0 1 x.val).mp x.property
  simp only [one_smul, zero_smul] at hl hr
  have hf : f[e] * x.val = x.val := by
    change (1 - e.val) * x.val = _
    rw [sub_mul, one_mul, hl, sub_zero]
  have adjR : B (x.val * e.val) z = B x.val (z * conjugate n e.val) :=
    right_mul_adjoint h e.val x.val z
  rw [hr, conjugate_point] at adjR
  have adjL : B (f[e] * x.val) (z * f[e]) = B x.val (conjugate n f[e] * (z * f[e])) :=
    left_mul_adjoint h f[e] x.val (z * f[e])
  rw [hf, ← conjugate_point e, conjugate_involutive h, conjugate_point] at adjL
  exact adjR.trans adjL

private lemma restrict_perfect_left (hn : IsOctonionNorm n)
    (U T : Submodule R C) (pU : C →ₗ[R] U) (pT : C →ₗ[R] T)
    (hU : ∀ (u : U) z, B u.val z = B u.val (pT z).val)
    (hT : ∀ (t : T) z, B t.val z = B t.val (pU z).val)
    (hfix : ∀ t : T, pT t.val = t) (P : U →ₗ[R] T →ₗ[R] R) (hP : ∀ u t, P u t = -B u.val t.val) :
    Function.Bijective P := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply hn.perfect.bijective_left.injective
    ext z
    rw [hU x, hU y]
    exact neg_injective (by simpa only [hP] using LinearMap.congr_fun hxy (pT z))
  · intro g
    obtain ⟨x, hx⟩ := hn.perfect.bijective_left.surjective ((-g).comp pT)
    refine ⟨pU x, ?_⟩
    ext t
    rw [hP, polar_symm, ← hT t x, polar_symm]
    have E := LinearMap.congr_fun hx t.val
    change B x t.val = -(g (pT t.val)) at E
    rw [E, hfix, neg_neg]

theorem perfect_pairing : PeirceSpecification.perfectPairing := by
  intro R C _ _ _ _ _ n hn e
  have h := IsOctonionNorm.toNormLaws hn
  refine ⟨restrict_perfect_left hn _ _ (component h e true false) (component h e false true)
      (polar_upper_component h e) (polar_lower_component h e) ?_ (pairing e) (pairing_apply e),
    restrict_perfect_left hn _ _ (component h e false true) (component h e true false)
      (polar_lower_component h e) (polar_upper_component h e) ?_ (pairing e).flip ?_⟩
  · intro w
    exact Subtype.ext (by simpa using component_of_corner h e false true false true w)
  · intro v
    exact Subtype.ext (by simpa using component_of_corner h e true false true false v)
  · intro w v
    exact congrArg Neg.neg (QuadraticMap.polar_comm n v.val w.val)

section Field

variable {k : Type u} [Field k] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
  {q : QuadraticForm k C}

private lemma exists_trace_one (h : NormLaws q) : ∃ w, compositionTrace q w = 1 := by
  have h1 : (1 : C) ≠ 0 := by
    intro E
    have H := h.map_one
    rw [E, map_zero] at H
    exact zero_ne_one H
  have hn : ∃ w, compositionTrace q w ≠ 0 := by
    by_contra! hn
    exact h1 (h.nondegenerate.2 1 hn)
  obtain ⟨w, hw⟩ := hn
  exact ⟨(compositionTrace q w)⁻¹ • w, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩

private lemma exists_trace_one_polar_one (h : NormLaws q) {x : C}
    (hx : x ≠ 0) (hqx : q x = 0) :
    ∃ y, compositionTrace q y = 1 ∧ q.polarBilin x y = 1 := by
  obtain ⟨w, hw⟩ := exists_trace_one h
  suffices hex : ∃ z, compositionTrace q z = 0 ∧ q.polarBilin x z ≠ 0 by
    obtain ⟨z, hz, hB⟩ := hex
    refine ⟨w + ((1 - q.polarBilin x w) / q.polarBilin x z) • z, ?_, ?_⟩
    · rw [map_add, map_smul, hz, smul_zero, add_zero, hw]
    · rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hB]
      ring
  by_contra! H
  have Eq (z : C) :
      q.polarBilin x z = compositionTrace q z * q.polarBilin x w := by
    have E := H (z - compositionTrace q z • w)
    have t : compositionTrace q (z - compositionTrace q z • w) = 0 := by
      rw [map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]
    have E := E t
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at E
    exact E
  let a := q.polarBilin x w
  have hx' : x = a • (1 : C) := by
    apply LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.nondegenerate.1)
    ext z
    rw [Eq, LinearMap.map_smul₂, smul_eq_mul, mul_comm]
    congr 1
    exact QuadraticMap.polar_comm q _ _
  have E := hqx
  rw [hx', norm_scalar h, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)] at E
  exact hx (by rw [hx', E, zero_smul])

theorem points_of_isotropic_norm : PeirceSpecification.pointsOfIsotropicNorm := by
  intro k C _ _ _ _ _ q hn hiso
  have h := IsOctonionNorm.toNormLaws hn
  obtain ⟨x, hx, hqx⟩ := hiso
  by_cases ht : compositionTrace q x = 0
  · obtain ⟨y, hy, hB⟩ := exists_trace_one_polar_one h hx hqx
    refine ⟨⟨y + (-q y) • x, ?_, ?_⟩⟩
    · change compositionTrace q (y + (-q y) • x) = 1
      rw [map_add, map_smul, ht, smul_zero, add_zero, hy]
    · have hBy : q.polarBilin y x = 1 := (QuadraticMap.polar_comm q y x).trans hB
      rw [norm_add, QuadraticMap.map_smul, hqx, smul_zero, map_smul, hBy,
        smul_eq_mul, mul_one]
      ring
  · refine ⟨⟨(compositionTrace q x)⁻¹ • x, ?_, ?_⟩⟩
    · change compositionTrace q ((compositionTrace q x)⁻¹ • x) = 1
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ ht]
    · rw [QuadraticMap.map_smul, hqx, smul_zero]

private theorem points_over_algebraically_closed_aux (hn : IsOctonionNorm q) [IsAlgClosed k] :
    Nonempty (QuadricPoint q) := by
  have h := IsOctonionNorm.toNormLaws hn
  have h1 : (1 : C) ≠ 0 := by
    intro E
    have H := h.map_one
    rw [E, map_zero] at H
    exact zero_ne_one H
  let U := Submodule.span k ({1} : Set C)
  have hU : U ≠ ⊤ := by
    intro E
    have H := finrank_span_singleton (K := k) h1
    change Module.finrank k U = 1 at H
    rw [E, finrank_top, ((octonion_norm_iff_field q).mp hn).2] at H
    omega
  obtain ⟨x, hx⟩ : ∃ x : C, x ∉ U := by
    by_contra! H
    exact hU (eq_top_iff.mpr fun x _ => H x)
  let P := Polynomial.C (1 : k) * Polynomial.X ^ 2 +
    Polynomial.C (compositionTrace q x) * Polynomial.X + Polynomial.C (q x)
  have hP : P.degree ≠ 0 := by
    dsimp only [P]
    rw [Polynomial.degree_quadratic one_ne_zero]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P hP
  apply points_of_isotropic_norm hn
  refine ⟨x + a • (1 : C), ?_, ?_⟩
  · intro E
    apply hx
    have hxa : x = (-a) • (1 : C) := by rw [eq_neg_of_add_eq_zero_left E, neg_smul]
    exact Submodule.mem_span_singleton.mpr ⟨-a, hxa.symm⟩
  · change P.eval a = 0 at ha
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, one_mul] at ha
    rw [norm_add, norm_scalar h, map_smul, ← compositionTrace_apply, smul_eq_mul]
    rw [← ha]
    ring


end Field

theorem points_over_algebraically_closed : PeirceSpecification.pointsOverAlgebraicallyClosed := by
  intro k C _ _ _ _ _ q hn _
  exact points_over_algebraically_closed_aux hn

private lemma component_retract (h : NormLaws n) (e : QuadricPoint n) (i j : Bool) :
    component h e i j ∘ₗ (corner e _ _).subtype = LinearMap.id := by
  ext x
  exact (component_of_corner h e i j i j x).trans (by simp)

private lemma projective_corner_pair (hn : IsOctonionNorm n) (e : QuadricPoint n) (i j : Bool) :
    Module.Finite R (corner e (eigenvalue R i) (eigenvalue R j)) ∧
      Module.Projective R (corner e (eigenvalue R i) (eigenvalue R j)) := by
  letI := hn.projective
  letI := hn.finite
  have h := IsOctonionNorm.toNormLaws hn
  have ha := component_retract h e i j
  exact ⟨Module.Finite.of_surjective _ (LinearMap.surjective_of_comp_eq_id _ _ ha),
    Module.Projective.of_split _ _ ha⟩

theorem projective_corners : PeirceSpecification.projectiveCorners := by
  intro R C _ _ _ _ _ n hn e
  exact ⟨(projective_corner_pair hn e true false).1, (projective_corner_pair hn e true false).2,
    (projective_corner_pair hn e false true).1, (projective_corner_pair hn e false true).2⟩

section BaseChange

variable (S : Type w) [CommRing S] [Algebra R S]

/-- Extend a point of the quadric along a ring map by tensoring it with one. -/
noncomputable def pointBaseChange [Module.Projective R C]
    (e : QuadricPoint n) : QuadricPoint (Specification.normBaseChange S n) :=
  ⟨(1 : S) ⊗ₜ[R] e.val,
    by rw [compositionTrace_baseChange_tmul, trace_point, map_one, mul_one],
    by rw [normBaseChange_tmul, norm_point, map_zero, mul_zero]⟩

private lemma selected_baseChange [Module.Projective R C] (e : QuadricPoint n) (i : Bool) :
    selected (pointBaseChange S e) i = (1 : S) ⊗ₜ[R] selected e i := by
  cases i
  · change 1 - (1 : S) ⊗ₜ[R] e.val = (1 : S) ⊗ₜ[R] (1 - e.val)
    rw [TensorProduct.tmul_sub]
    rfl
  · rfl

private theorem component_baseChange (hn : IsOctonionNorm n) (e : QuadricPoint n) (i j : Bool) :
    letI := hn.projective
    let h := IsOctonionNorm.toNormLaws hn
    let hS := IsOctonionNorm.toNormLaws (octonion_norm_baseChange hn S)
    let eS := pointBaseChange S e
    ((corner e _ _).subtype ∘ₗ component h e i j).baseChange S =
      (corner eS _ _).subtype ∘ₗ component hS eS i j := by
  intro h hS eS
  letI := hn.projective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  rw [LinearMap.baseChange_tmul]
  change s ⊗ₜ[R] (component h e i j x).val = (component hS eS i j (s ⊗ₜ[R] x)).val
  rw [component_apply, component_apply]
  dsimp only [eS]
  rw [selected_baseChange, selected_baseChange, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The inclusion of each Peirce corner induces an isomorphism onto the extended corner. -/
noncomputable def cornerBaseChange (hn : IsOctonionNorm n) (e : QuadricPoint n) (i j : Bool) :
    letI := hn.projective
    (S ⊗[R] corner e (eigenvalue R i) (eigenvalue R j)) ≃ₗ[S]
      corner (pointBaseChange S e) (eigenvalue S i) (eigenvalue S j) := by
  letI := hn.projective
  let h := IsOctonionNorm.toNormLaws hn
  let hS := IsOctonionNorm.toNormLaws (octonion_norm_baseChange hn S)
  let eS := pointBaseChange S e
  let U := corner e (eigenvalue R i) (eigenvalue R j)
  let US := corner eS (eigenvalue S i) (eigenvalue S j)
  let f := U.subtype.baseChange S
  let g := (component h e i j).baseChange S
  have hg : g ∘ₗ f = LinearMap.id := by
    rw [← LinearMap.baseChange_comp]
    rw [component_retract, LinearMap.baseChange_id]
  have hf : f ∘ₗ g = US.subtype ∘ₗ component hS eS i j :=
    (LinearMap.baseChange_comp (A := S) _ _).symm.trans (component_baseChange S hn e i j)
  have hsub : ∀ z, f z ∈ US := by
    intro z
    have H := LinearMap.congr_fun hf (f z)
    change f (g (f z)) = (component hS eS i j (f z)).val at H
    rw [show g (f z) = z from LinearMap.congr_fun hg z] at H
    exact H ▸ (component hS eS i j (f z)).property
  refine LinearEquiv.ofLinearMap (f.codRestrict US hsub) (g ∘ₗ US.subtype) ?_ ?_
  · ext x
    change f (g x.val) = x.val
    have H := LinearMap.congr_fun hf x.val
    change f (g x.val) = (component hS eS i j x.val).val at H
    exact H.trans (by simpa using component_of_corner hS eS i j i j x)
  · exact hg

theorem cornerBaseChange_tmul (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (i j : Bool) (s : S) (x : corner e (eigenvalue R i) (eigenvalue R j)) :
    letI := hn.projective
    (cornerBaseChange S hn e i j (s ⊗ₜ[R] x)).val = s ⊗ₜ[R] x.val := by
  letI := hn.projective
  rfl

theorem pairing_baseChange_tmul (hn : IsOctonionNorm n) (e : QuadricPoint n) (s t : S)
    (x : corner e 1 0) (y : corner e 0 1) :
    letI := hn.projective
    pairing (pointBaseChange S e)
      (cornerBaseChange S hn e true false (s ⊗ₜ[R] x))
      (cornerBaseChange S hn e false true (t ⊗ₜ[R] y)) =
        s * t * algebraMap R S (pairing e x y) := by
  letI := hn.projective
  change -(Specification.normBaseChange S n).polarBilin
      (s ⊗ₜ[R] x.val) (t ⊗ₜ[R] y.val) =
        s * t * algebraMap R S (-n.polarBilin x.val y.val)
  rw [polar_normBaseChange,
    LinearMap.BilinForm.baseChange_tmul, map_neg, Algebra.smul_def]
  ring


theorem base_change_corners : PeirceSpecification.baseChangeCorners := by
  intro R C _ _ _ _ _ n hn e S _ _
  letI := hn.projective
  refine ⟨pointBaseChange S e, rfl, ?_⟩
  intro i j
  exact ⟨cornerBaseChange S hn e i j, cornerBaseChange_tmul S hn e i j⟩

theorem base_change_pairing : PeirceSpecification.baseChangePairing := by
  intro R C _ _ _ _ _ n hn e S _ _
  letI := hn.projective
  exact ⟨pointBaseChange S e, rfl, cornerBaseChange S hn e true false,
    cornerBaseChange S hn e false true, cornerBaseChange_tmul S hn e true false,
    cornerBaseChange_tmul S hn e false true, pairing_baseChange_tmul S hn e⟩

end BaseChange

theorem corner_rank : PeirceSpecification.cornerRank := by
  intro R C _ _ _ _ _ n hn e p
  letI := p.nontrivial
  letI := hn.finite
  letI := hn.projective
  have h := IsOctonionNorm.toNormLaws hn
  let V := corner e (1 : R) 0
  let W := corner e (0 : R) 1
  obtain ⟨hFV, hPV, hFW, hPW⟩ := projective_corners hn e
  letI : Module.Finite R V := hFV
  letI : Module.Projective R V := hPV
  letI : Module.Finite R W := hFW
  letI : Module.Projective R W := hPW
  let S := Localization.AtPrime p.asIdeal
  let eS := pointBaseChange S e
  have hnS := octonion_norm_baseChange hn S
  obtain ⟨hFVS, hPVS, _, _⟩ := projective_corners hnS eS
  letI : Module.Finite S (corner eS 1 0) := hFVS
  letI : Module.Projective S (corner eS 1 0) := hPVS
  letI : IsLocalRing S := inferInstanceAs (IsLocalRing (Localization.AtPrime p.asIdeal))
  letI : Module.Free S (corner eS 1 0) :=
    Module.free_of_flat_of_isLocalRing (R := S) (P := ↥(corner eS 1 0))
  letI := perfect_pairing hnS eS
  have heq : Module.rankAtStalk V p = Module.rankAtStalk W p := by
    rw [Module.rankAtStalk_eq_finrank_tensorProduct, Module.rankAtStalk_eq_finrank_tensorProduct]
    calc
      _ = Module.finrank S (corner eS 1 0) := (cornerBaseChange S hn e true false).finrank_eq
      _ = Module.finrank S (corner eS 0 1) := Module.finrank_of_isPerfPair (pairing eS)
      _ = _ := (cornerBaseChange S hn e false true).finrank_eq.symm
  have hsum := congrFun (Module.rankAtStalk_eq_of_equiv (decomposition h e)) p
  change Module.rankAtStalk (R × V × W × R) p = Module.rankAtStalk C p at hsum
  rw [hn.rank_eight p] at hsum
  have hr : Module.rankAtStalk (R := R) (R × V × W × R) =
      Module.rankAtStalk R + (Module.rankAtStalk V + (Module.rankAtStalk W + Module.rankAtStalk R)) := by
    rw [Module.rankAtStalk_prod R (V × W × R),
      Module.rankAtStalk_prod V (W × R), Module.rankAtStalk_prod W R]
  rw [hr, Module.rankAtStalk_self] at hsum
  change 1 + (Module.rankAtStalk V p + (Module.rankAtStalk W p + 1)) = 8 at hsum
  change Module.rankAtStalk V p = 3 ∧ Module.rankAtStalk W p = 3
  omega

private lemma norm_of_off_diagonal_sum (h : NormLaws n) (e : QuadricPoint n)
    (x : V[e]) (y : W[e]) : n (x.val + y.val) = -pairing e x y := by
  rw [norm_add, norm_upper h, norm_lower h, zero_add, zero_add, pairing_apply, neg_neg]

lemma norm_in_corners_aux (h : NormLaws n) (e : QuadricPoint n) (a b : R)
    (x : V[e]) (y : W[e]) :
    n (a • e.val + x.val + y.val + b • f[e]) = a * b - pairing e x y := by
  have hl : e.val * x.val = x.val := by
    simpa only [one_smul] using ((mem_corner_iff e 1 0 x.val).mp x.property).1
  have hr : y.val * e.val = y.val := by
    simpa only [one_smul] using ((mem_corner_iff e 0 1 y.val).mp y.property).2
  have hE : B e.val (x.val + y.val) = 0 := by
    rw [map_add, polar_point_eq_zero_of_left_one h e hl, polar_point_eq_zero_of_right_one h e hr,
      zero_add]
  have hF : B f[e] (x.val + y.val) = 0 := by
    change B (1 - e.val) (x.val + y.val) = 0
    rw [LinearMap.map_sub₂, hE, sub_zero, polar_symm (1 : C), ← compositionTrace_apply,
      map_add, trace_upper h e x, trace_lower h e y, zero_add]
  rw [show a • e.val + x.val + y.val + b • f[e] =
      (a • e.val + b • f[e]) + (x.val + y.val) by abel,
    norm_add, norm_of_off_diagonal_sum h e, LinearMap.map_add₂, LinearMap.map_smul₂,
    LinearMap.map_smul₂, hE, hF, smul_zero, smul_zero, zero_add, add_zero]
  rw [norm_add, QuadraticMap.map_smul, QuadraticMap.map_smul, norm_point, norm_complement h,
    smul_zero, smul_zero, zero_add, zero_add, LinearMap.map_smul₂, map_smul,
    polar_point_complement]
  simp [sub_eq_add_neg]

theorem norm_in_corners : PeirceSpecification.normInCorners := by
  intro R C _ _ _ _ _ n hn e
  exact norm_in_corners_aux (IsOctonionNorm.toNormLaws hn) e

theorem cross_pairing_identity : PeirceSpecification.crossPairingIdentity := by
  intro R C _ _ _ _ _ n hn e x x' y y'
  have h := IsOctonionNorm.toNormLaws hn
  obtain ⟨hv, hu, hp⟩ := off_diagonal_products hn e
  let u := (⟨y.val * y'.val, hu y y'⟩ : corner e 1 0)
  let v := (⟨x.val * x'.val, hv x x'⟩ : corner e 0 1)
  refine ⟨u, v, rfl, rfl, ?_⟩
  have H := h.map_mul (x.val + y.val) (x'.val + y'.val)
  have H' : (x.val + y.val) * (x'.val + y'.val) =
      pairing e x y' • e.val + u.val + v.val +
        pairing e x' y • PeirceSpecification.complement e := by
    rw [add_mul, mul_add, mul_add, (hp x y').1, (hp x' y).2]
    change v.val + _ + (_ + u.val) = _
    abel
  rw [H', norm_in_corners_aux h, norm_of_off_diagonal_sum h e, norm_of_off_diagonal_sum h e,
    neg_mul_neg] at H
  rw [← H]
  ring

open Module (Basis)
open PeirceSpecification (OrientedBasis ZornIsomorphism volume)

private def upperProduct (hn : IsOctonionNorm n) (e : QuadricPoint n) (x y : V[e]) : W[e] :=
  ⟨x.val * y.val, (off_diagonal_products hn e).1 x y⟩

private def lowerProduct (hn : IsOctonionNorm n) (e : QuadricPoint n) (x y : W[e]) : V[e] :=
  ⟨x.val * y.val, (off_diagonal_products hn e).2.1 x y⟩

private lemma traceVolume_alternating (h : NormLaws n) (U : Submodule R C)
    (hU : ∀ x : U, x.val * x.val = 0) :
    ∃ A : U [⋀^Fin 3]→ₗ[R] R, ∀ x, A x = volume (n := n) U x := by
  let A : U [⋀^Fin 3]→ₗ[R] R := {
    toMultilinearMap := MultilinearMap.mk' (volume (n := n) U) (by
      intro x i a b
      fin_cases i <;>
        simp [volume, add_mul, mul_add]) (by
      intro x i a b
      fin_cases i <;>
        simp [volume, smul_mul_assoc, mul_smul_comm])
    map_eq_zero_of_eq' := by
      intro x i j hij hne
      have h01 (H : x 0 = x 1) : volume (n := n) U x = 0 := by
        dsimp [volume]
        rw [← compositionTrace_mul_assoc h, H, hU, zero_mul, map_zero]
      have h02 (H : x 0 = x 2) : volume (n := n) U x = 0 := by
        dsimp [volume]
        rw [← compositionTrace_mul_assoc h,
          ← compositionTrace_mul_cyclic h (x 2).val (x 0).val (x 1).val,
          ← H, hU, zero_mul, map_zero]
      have h12 (H : x 1 = x 2) : volume (n := n) U x = 0 := by
        dsimp [volume]
        rw [H, hU, mul_zero, map_zero]
      fin_cases i <;> fin_cases j <;>
        first
        | contradiction
        | exact h01 hij
        | exact h01 hij.symm
        | exact h02 hij
        | exact h02 hij.symm
        | exact h12 hij
        | exact h12 hij.symm }
  exact ⟨A, fun _ => rfl⟩

theorem alternating_volume : PeirceSpecification.alternatingVolume := by
  intro R C _ _ _ _ _ n hn e
  have h := IsOctonionNorm.toNormLaws hn
  refine ⟨traceVolume_alternating h _ ?_, traceVolume_alternating h _ ?_⟩ <;> intro x
  · simpa [trace_upper h e x, norm_upper h e x] using composition_quadratic_equation h x.val
  · simpa [trace_lower h e x, norm_lower h e x] using composition_quadratic_equation h x.val

private lemma volume_upper (hn : IsOctonionNorm n) (e : QuadricPoint n) (x : Fin 3 → V[e]) :
    volume (n := n) _ x = pairing e (x 0) (upperProduct hn e (x 1) (x 2)) := by
  unfold volume
  exact (congrArg (compositionTrace n) ((off_diagonal_products hn e).2.2
    (x 0) (upperProduct hn e (x 1) (x 2))).1).trans (trace_smul_point e _)

private lemma volume_lower (hn : IsOctonionNorm n) (e : QuadricPoint n) (y : Fin 3 → W[e]) :
    volume (n := n) _ y = pairing e (lowerProduct hn e (y 1) (y 2)) (y 0) := by
  unfold volume
  exact (congrArg (compositionTrace n) ((off_diagonal_products hn e).2.2
    (lowerProduct hn e (y 1) (y 2)) (y 0)).2).trans
      (trace_smul_complement (IsOctonionNorm.toNormLaws hn) e _)

private noncomputable def lowerBasis (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : Basis (Fin 3) R V[e]) : Basis (Fin 3) R W[e] :=
  letI := perfect_pairing hn e
  b.dualBasis.map (pairing e).flip.toPerfPair.symm

private lemma pairing_lowerBasis (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : Basis (Fin 3) R V[e]) (x : V[e]) (i : Fin 3) :
    pairing e x (lowerBasis hn e b i) = b.equivFun x i := by
  letI := perfect_pairing hn e
  simp [lowerBasis, Basis.equivFun_apply]

private lemma pairing_upperBasis (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : Basis (Fin 3) R V[e]) (y : W[e]) (i : Fin 3) :
    pairing e (b i) y = (lowerBasis hn e b).equivFun y i := by
  let d := lowerBasis hn e b
  calc
    pairing e (b i) y = pairing e (b i) (∑ j, d.equivFun y j • d j) :=
      congrArg (pairing e (b i)) (d.sum_equivFun y).symm
    _ = d.equivFun y i := by
      rw [map_sum]
      simp [d, pairing_lowerBasis, Basis.equivFun_self, eq_comm (a := i)]

private lemma pairing_coordinates (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : Basis (Fin 3) R V[e]) (x : V[e]) (y : W[e]) :
    pairing e x y = dotProduct (b.equivFun x) ((lowerBasis hn e b).equivFun y) := by
  calc
    pairing e x y = pairing e (∑ i, b.equivFun x i • b i) y :=
      congrArg (fun v => pairing e v y) (b.sum_equivFun x).symm
    _ = _ := by
      simp only [LinearMap.map_sum₂, LinearMap.map_smul₂, pairing_upperBasis hn e b,
        smul_eq_mul, dotProduct]

private lemma volume_in_basis (U : Submodule R C) (b : Basis (Fin 3) R U)
    (H : ∃ A : U [⋀^Fin 3]→ₗ[R] R, ∀ x, A x = volume (n := n) U x) (x y z : U) :
    volume (n := n) U ![x, y, z] = volume (n := n) U b *
      dotProduct (b.equivFun x) (crossProduct (b.equivFun y) (b.equivFun z)) := by
  obtain ⟨A, hA⟩ := H
  have hm : (b.toMatrix ![x, y, z])ᵀ = ![b.equivFun x, b.equivFun y, b.equivFun z] := by
    ext i j
    fin_cases i <;> simp [Basis.toMatrix_apply, Basis.equivFun_apply, Matrix.transpose_apply]
  calc
    volume (n := n) U ![x, y, z] = A ![x, y, z] := (hA _).symm
    _ = A b * b.det ![x, y, z] := by
      nth_rw 1 [A.eq_smul_basis_det b]
      rfl
    _ = _ := by rw [hA, triple_product_eq_det, Basis.det_apply, ← Matrix.det_transpose, hm]

private lemma upperProduct_coordinates (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : Basis (Fin 3) R V[e]) (x y : V[e]) :
    (lowerBasis hn e b).equivFun (upperProduct hn e x y) =
      volume (n := n) _ b • crossProduct (b.equivFun x) (b.equivFun y) := by
  funext i
  have H : volume (n := n) _ ![b i, x, y] = pairing e (b i) (upperProduct hn e x y) :=
    volume_upper hn e _
  rw [← pairing_upperBasis hn e b, ← H]
  rw [volume_in_basis _ b (alternating_volume hn e).1]
  simp [Basis.equivFun_apply, dotProduct, eq_comm (a := i)]

private lemma lowerProduct_coordinates (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : Basis (Fin 3) R V[e]) (x y : W[e]) :
    b.equivFun (lowerProduct hn e x y) = volume (n := n) _ (lowerBasis hn e b) •
      crossProduct ((lowerBasis hn e b).equivFun x) ((lowerBasis hn e b).equivFun y) := by
  let d := lowerBasis hn e b
  funext i
  have H : volume (n := n) _ ![d i, x, y] = pairing e (lowerProduct hn e x y) (d i) :=
    volume_lower hn e _
  rw [← pairing_lowerBasis hn e b, ← H]
  rw [volume_in_basis _ d (alternating_volume hn e).2]
  simp [d, Basis.equivFun_apply, dotProduct, eq_comm (a := i)]

private lemma volume_mul_volume (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : Basis (Fin 3) R V[e]) : volume (n := n) _ b * volume (n := n) _ (lowerBasis hn e b) = -1 := by
  let d := lowerBasis hn e b
  obtain ⟨x, y, hx, hy, H⟩ := cross_pairing_identity hn e (b 1) (b 2) (d 1) (d 2)
  have hx' : x = lowerProduct hn e (d 1) (d 2) := Subtype.ext hx
  have hy' : y = upperProduct hn e (b 1) (b 2) := Subtype.ext hy
  rw [hx', hy', pairing_coordinates hn e b, lowerProduct_coordinates, upperProduct_coordinates] at H
  simp only [d, pairing_lowerBasis, Basis.equivFun_apply, Basis.repr_self, dotProduct,
    Fin.sum_univ_three, cross_apply, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply, Fin.isValue] at H
  simpa [mul_comm] using H

theorem oriented_basis_exists : PeirceSpecification.orientedBasisExists := by
  intro R C _ _ _ _ _ n hn e hb
  obtain ⟨b⟩ := hb
  obtain ⟨a, ha⟩ : IsUnit (volume (n := n) _ b) :=
    isUnit_iff_exists_inv.mpr ⟨-volume (n := n) _ (lowerBasis hn e b), by
      rw [mul_neg, volume_mul_volume hn e b, neg_neg]⟩
  let w : Fin 3 → Rˣ := ![a⁻¹, 1, 1]
  refine ⟨⟨b.unitsSMul w, ?_⟩⟩
  have hw0 : w 0 = a⁻¹ := rfl
  have hw1 : w 1 = 1 := rfl
  have hw2 : w 2 = 1 := rfl
  unfold volume
  simp only [Basis.unitsSMul_apply, hw0, hw1, hw2, one_smul]
  change compositionTrace n (((↑(a⁻¹) : R) • (b 0).val) * ((b 1).val * (b 2).val)) = 1
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  change (↑(a⁻¹) : R) * volume (n := n) _ b = 1
  rw [← ha, ← Units.val_mul, inv_mul_cancel, Units.val_one]

private lemma mul_in_corners (hn : IsOctonionNorm n) (e : QuadricPoint n) (a b c d : R)
    (x x' : V[e]) (y y' : W[e]) :
    (a • e.val + x.val + y.val + b • f[e]) * (c • e.val + x'.val + y'.val + d • f[e]) =
      (a * c + pairing e x y') • e.val +
        (a • x' + d • x + lowerProduct hn e y y').val +
        (c • y + b • y' + upperProduct hn e x x').val +
        (b * d + pairing e x' y) • f[e] := by
  have h := IsOctonionNorm.toNormLaws hn
  have upper (v : V[e]) : e.val * v.val = v.val ∧ v.val * e.val = 0 ∧
      f[e] * v.val = 0 ∧ v.val * f[e] = v.val := by
    obtain ⟨hL, hR⟩ := (mem_corner_iff e 1 0 v.val).mp v.property
    simp only [one_smul, zero_smul] at hL hR
    exact ⟨hL, hR, by simp [PeirceSpecification.complement, sub_mul, hL],
      by simp [PeirceSpecification.complement, mul_sub, hR]⟩
  have lower (w : W[e]) : e.val * w.val = 0 ∧ w.val * e.val = w.val ∧
      f[e] * w.val = w.val ∧ w.val * f[e] = 0 := by
    obtain ⟨hL, hR⟩ := (mem_corner_iff e 0 1 w.val).mp w.property
    simp only [one_smul, zero_smul] at hL hR
    exact ⟨hL, hR, by simp [PeirceSpecification.complement, sub_mul, hL],
      by simp [PeirceSpecification.complement, mul_sub, hR]⟩
  obtain ⟨_, hrx, _, hrfx⟩ := upper x
  obtain ⟨hlx, _, hlfx, _⟩ := upper x'
  obtain ⟨_, hry, _, hrfy⟩ := lower y
  obtain ⟨hly, _, hlfy, _⟩ := lower y'
  have mixed := (off_diagonal_products hn e).2.2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, point_mul_self h,
    point_mul_complement h, complement_mul_point h, complement_mul_self h,
    hlx, hlfx, hly, hlfy, hrx, hrfx, hry, hrfy, (mixed x y').1, (mixed x' y).2,
    smul_add, smul_smul, smul_zero, add_zero, zero_add, add_smul, Submodule.coe_add, Submodule.coe_smul,
    lowerProduct, upperProduct]
  rw [mul_comm c a, mul_comm d b]
  abel

/-- An oriented basis and its pairing-dual basis give the coordinates of a Zorn isomorphism. -/
noncomputable def zornOfBasis (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (frame : OrientedBasis e) : ZornIsomorphism n := by
  let h := IsOctonionNorm.toNormLaws hn
  let b := frame.val
  let d := lowerBasis hn e b
  let L := (Zorn.coordinates R).trans (((LinearEquiv.refl R R).prodCongr
    (b.equivFun.symm.prodCongr (d.equivFun.symm.prodCongr (LinearEquiv.refl R R)))).trans
      (decomposition h e))
  have hL (a z : R) (x y : Fin 3 → R) :
      L (Zorn.ofCoordinates (a, x, y, z)) =
        a • e.val + (b.equivFun.symm x).val + (d.equivFun.symm y).val + z • f[e] :=
    decomposition_apply h e (a, b.equivFun.symm x, d.equivFun.symm y, z)
  have hb : volume (n := n) _ b = 1 := frame.property
  have hd : volume (n := n) _ d = -1 := by
    simpa [hb, d] using volume_mul_volume hn e b
  refine ⟨L, ?_, ?_, ?_⟩
  · change L (Zorn.ofCoordinates (1, 0, 0, 1)) = 1
    rw [hL]
    simpa using point_add_complement e
  · rintro ⟨a, x, y, z⟩ ⟨a', x', y', z'⟩
    change L (Zorn.ofCoordinates (Specification.zornProduct (a, x, y, z) (a', x', y', z'))) =
      L (Zorn.ofCoordinates (a, x, y, z)) * L (Zorn.ofCoordinates (a', x', y', z'))
    have hu : upperProduct hn e (b.equivFun.symm x) (b.equivFun.symm x') =
        d.equivFun.symm (crossProduct x x') := by
      apply d.equivFun.injective
      simpa only [d, LinearEquiv.apply_symm_apply, hb, one_smul] using
        upperProduct_coordinates hn e b (b.equivFun.symm x) (b.equivFun.symm x')
    have hw : lowerProduct hn e (d.equivFun.symm y) (d.equivFun.symm y') =
        -b.equivFun.symm (crossProduct y y') := by
      apply b.equivFun.injective
      simpa only [← show d = lowerBasis hn e b from rfl, LinearEquiv.apply_symm_apply,
        hd, neg_smul, one_smul, map_neg] using
        lowerProduct_coordinates hn e b (d.equivFun.symm y) (d.equivFun.symm y')
    simp only [Specification.zornProduct, hL, mul_in_corners hn e, pairing_coordinates hn e b,
      ← show d = lowerBasis hn e b from rfl, LinearEquiv.apply_symm_apply, hu, hw, map_add,
      map_neg, map_smul, sub_eq_add_neg, dotProduct_comm y x']
  · rintro ⟨a, x, y, z⟩
    change n (L (Zorn.ofCoordinates (a, x, y, z))) =
      ZornSpecification.norm R (Zorn.ofCoordinates (a, x, y, z))
    rw [hL, norm_in_corners_aux h, pairing_coordinates hn e b, Zorn.norm_formula]
    change a * z - dotProduct (b.equivFun (b.equivFun.symm x)) (d.equivFun (d.equivFun.symm y)) =
      a * z - dotProduct x y
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem is_split_octonion_of_zorn_isomorphism (F : ZornIsomorphism n) : IsSplitOctonion n := by
  let L := F.toLinearEquiv.symm.trans (Zorn.coordinates R)
  refine ⟨L, ?_, ?_, ?_⟩
  · change Zorn.coordinates R (F.toLinearEquiv.symm 1) = Specification.zornUnit
    rw [← F.map_one, LinearEquiv.symm_apply_apply, Zorn.coordinates_one]
  · intro x y
    have h : F.toLinearEquiv.symm (x * y) = F.toLinearEquiv.symm x * F.toLinearEquiv.symm y := by
      apply F.toLinearEquiv.injective
      rw [F.map_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    change Zorn.coordinates R (F.toLinearEquiv.symm (x * y)) =
      Specification.zornProduct (L x) (L y)
    rw [h, Zorn.coordinates_mul]
    rfl
  · intro x
    simpa only [L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Zorn.norm_formula] using
      F.map_norm (F.toLinearEquiv.symm x)

theorem isotropic_field_split : PeirceSpecification.isotropicFieldSplit := by
  intro R C _ _ _ _ _ n hn hi
  obtain ⟨e⟩ := points_of_isotropic_norm hn hi
  obtain ⟨hV, _, _, _⟩ := projective_corners hn e
  letI := hV
  let p : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hr := (corner_rank hn e p).1
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  obtain ⟨b⟩ := oriented_basis_exists hn e ⟨(Module.finBasis R _).reindex (finCongr hr)⟩
  exact ⟨zornOfBasis hn e b⟩

section TensorMap

variable {R : Type u} {M : Type v} {S : Type w} {T : Type z} [CommRing R]
  [AddCommGroup M] [Module R M] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- The map on a scalar-extended module induced by a homomorphism of the scalar rings. -/
abbrev tensorMap (f : S →ₐ[R] T) : (S ⊗[R] M) →ₗ[R] (T ⊗[R] M) :=
  PeirceSpecification.tensorMap f

@[simp] lemma tensorMap_tmul (f : S →ₐ[R] T) (s : S) (x : M) :
    tensorMap f (s ⊗ₜ[R] x) = f s ⊗ₜ[R] x := rfl

@[simp] lemma tensorMap_id (x : S ⊗[R] M) : tensorMap (AlgHom.id R S) x = x := by
  exact LinearMap.congr_fun (LinearMap.rTensor_id M S) x

lemma tensorMap_comp {U : Type*} [CommRing U] [Algebra R U] (f : S →ₐ[R] T)
    (g : T →ₐ[R] U) (x : S ⊗[R] M) :
    tensorMap (g.comp f) x = tensorMap g (tensorMap f x) := by
  exact LinearMap.congr_fun (LinearMap.rTensor_comp (M := M) g.toLinearMap f.toLinearMap) x

lemma tensorMap_smul (f : S →ₐ[R] T) (s : S) (x : S ⊗[R] M) :
    tensorMap f (s • x) = f s • tensorMap f x := by
  induction x using TensorProduct.inductionOn with
  | tmul t y => simp [TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

lemma polar_tensorMap [Module.Projective R M] (n : QuadraticForm R M) (f : S →ₐ[R] T)
    (x y : S ⊗[R] M) :
    (normBaseChange T n).polarBilin (tensorMap f x) (tensorMap f y) =
      f ((normBaseChange S n).polarBilin x y) := by
  have H : LinearMap.BilinForm.baseChange S n.polarBilin = (normBaseChange S n).polarBilin :=
    (polar_normBaseChange S n).symm
  have H' : LinearMap.BilinForm.baseChange T n.polarBilin = (normBaseChange T n).polarBilin :=
    (polar_normBaseChange T n).symm
  rw [← H, ← H']
  suffices ∀ a m b n', (LinearMap.BilinForm.baseChange T n.polarBilin)
        (tensorMap f (a ⊗ₜ[R] m)) (tensorMap f (b ⊗ₜ[R] n')) =
      f ((LinearMap.BilinForm.baseChange S n.polarBilin) (a ⊗ₜ[R] m) (b ⊗ₜ[R] n')) by
    induction x using TensorProduct.inductionOn with
    | tmul a m =>
      induction y using TensorProduct.inductionOn with
      | tmul b n' => exact this a m b n'
      | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  intro a m b n'
  simp only [tensorMap_tmul, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def,
    map_mul, AlgHom.commutes]

lemma norm_tensorMap [Module.Projective R M] (n : QuadraticForm R M) (f : S →ₐ[R] T)
    (x : S ⊗[R] M) :
    normBaseChange T n (tensorMap f x) = f (normBaseChange S n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp [map_mul, AlgHom.commutes]
  | add x y hx hy =>
    rw [map_add, QuadraticMap.map_add (normBaseChange T n),
      QuadraticMap.map_add (normBaseChange S n), map_add, map_add, hx, hy]
    rw [← QuadraticMap.polarBilin_apply_apply, polar_tensorMap]
    rfl

end TensorMap

section TensorRing

variable {R : Type u} {C : Type v} {S : Type w} {T : Type z} [CommRing R]
  [NonAssocRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

@[simp] lemma tensorMap_one (f : S →ₐ[R] T) : tensorMap f (1 : S ⊗[R] C) = 1 := by
  simp [Algebra.TensorProduct.one_def]

lemma tensorMap_mul (f : S →ₐ[R] T) (x y : S ⊗[R] C) :
    tensorMap f (x * y) = tensorMap f x * tensorMap f y := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | tmul t y => simp [Algebra.TensorProduct.tmul_mul_tmul, map_mul]
    | add y z hy hz => rw [mul_add, map_add, map_add, mul_add, hy, hz]
  | add x z hx hz => rw [add_mul, map_add, map_add, add_mul, hx, hz]

lemma trace_tensorMap [Module.Projective R C] (n : QuadraticForm R C) (f : S →ₐ[R] T)
    (x : S ⊗[R] C) :
    compositionTrace (normBaseChange T n) (tensorMap f x) =
      f (compositionTrace (normBaseChange S n) x) := by
  simp only [compositionTrace_apply]
  rw [← tensorMap_one f, polar_tensorMap]

end TensorRing

section Coordinates

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite free module with a specified retraction onto a projective module. -/
private structure FiniteCoordinates where
  size : ℕ
  fromFree : (Fin size → R) →ₗ[R] M
  toFree : M →ₗ[R] (Fin size → R)
  retract : fromFree ∘ₗ toFree = LinearMap.id

private noncomputable def FiniteCoordinates.ofProjective [Module.Finite R M] [Module.Projective R M] :
    FiniteCoordinates R M := by
  let h := Module.Finite.exists_fin' R M
  let m := h.choose
  let f := h.choose_spec.choose
  have hf := h.choose_spec.choose_spec
  let s := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  exact ⟨m, f, s.choose, s.choose_spec⟩

variable {R M} (c : FiniteCoordinates R M)
variable (S : Type w) [CommRing S] [Algebra R S]

private noncomputable def FiniteCoordinates.generator (i : Fin c.size) : M :=
  c.fromFree (Pi.basisFun R (Fin c.size) i)

private noncomputable def FiniteCoordinates.coordinate (i : Fin c.size) : (S ⊗[R] M) →ₗ[S] S :=
  ((Algebra.linearMap R S).comp ((LinearMap.proj i).comp c.toFree)).liftBaseChange S

private lemma FiniteCoordinates.coordinate_tmul (i : Fin c.size) (s : S) (x : M) :
    c.coordinate S i (s ⊗ₜ[R] x) = s * algebraMap R S (c.toFree x i) := rfl

private lemma FiniteCoordinates.coordinate_tensorMap {T : Type z} [CommRing T] [Algebra R T]
    (i : Fin c.size) (f : S →ₐ[R] T) (x : S ⊗[R] M) :
    c.coordinate T i (tensorMap f x) = f (c.coordinate S i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp only [tensorMap_tmul, c.coordinate_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma FiniteCoordinates.reconstruct (x : S ⊗[R] M) :
    ∑ i, c.coordinate S i x ⊗ₜ[R] c.generator i = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    simp only [c.coordinate_tmul]
    have h : ∑ i, c.toFree x i • c.generator i = x := by
      change ∑ i, c.toFree x i • c.fromFree (Pi.basisFun R (Fin c.size) i) = x
      simp_rw [← map_smul, ← map_sum]
      have hB := (Pi.basisFun R (Fin c.size)).sum_equivFun (c.toFree x)
      rw [Pi.basisFun_equivFun] at hB
      rw [LinearEquiv.refl_apply] at hB
      rw [hB]
      exact LinearMap.congr_fun c.retract x
    calc
      ∑ i, (s * algebraMap R S (c.toFree x i)) ⊗ₜ[R] c.generator i =
          ∑ i, s ⊗ₜ[R] (c.toFree x i • c.generator i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
      _ = s ⊗ₜ[R] x := by rw [← TensorProduct.tmul_sum, h]
  | add y z hy hz =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hy, hz]

private noncomputable def FiniteCoordinates.generic : MvPolynomial (Fin c.size) R ⊗[R] M :=
  ∑ i, MvPolynomial.X i ⊗ₜ[R] c.generator i

private lemma FiniteCoordinates.map_generic (f : MvPolynomial (Fin c.size) R →ₐ[R] S) :
    tensorMap f c.generic = ∑ i, f (MvPolynomial.X i) ⊗ₜ[R] c.generator i := by
  simp only [FiniteCoordinates.generic, map_sum, tensorMap_tmul]

private lemma FiniteCoordinates.eval_generic (x : S ⊗[R] M) :
    tensorMap (MvPolynomial.aeval fun i => c.coordinate S i x) c.generic = x := by
  rw [c.map_generic]
  simp only [MvPolynomial.aeval_X, c.reconstruct]

end Coordinates

section Quadric

variable {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] [Module.Projective R C]
  (n : QuadraticForm R C) (c : FiniteCoordinates R C)

private noncomputable def quadricEquation : Fin c.size ⊕ Bool → MvPolynomial (Fin c.size) R
  | .inl i => c.coordinate _ i c.generic - MvPolynomial.X i
  | .inr false => compositionTrace (normBaseChange _ n) c.generic - 1
  | .inr true => normBaseChange _ n c.generic

private noncomputable def quadricIdeal : Ideal (MvPolynomial (Fin c.size) R) :=
  Ideal.span (Set.range (quadricEquation n c))

private abbrev QuadricRing := MvPolynomial (Fin c.size) R ⧸ quadricIdeal n c

private noncomputable def genericPoint :
    QuadricPoint (C := QuadricRing n c ⊗[R] C) (normBaseChange (QuadricRing n c) n) := by
  let q := Ideal.Quotient.mkₐ R (quadricIdeal n c)
  have hq i : q (quadricEquation n c i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  refine ⟨tensorMap q c.generic, ?_, ?_⟩
  · rw [trace_tensorMap]
    have h := hq (.inr false)
    rw [quadricEquation, map_sub, map_one, sub_eq_zero] at h
    exact h
  · rw [norm_tensorMap]
    exact hq (.inr true)

variable {S : Type w} [CommRing S] [Algebra R S]

private lemma genericPoint_eval (f : QuadricRing n c →ₐ[R] S) :
    tensorMap f (genericPoint n c).val =
      tensorMap (f.comp (Ideal.Quotient.mkₐ R (quadricIdeal n c))) c.generic :=
  (tensorMap_comp _ _ _).symm

private lemma quadricRing_coord (f : QuadricRing n c →ₐ[R] S) (i : Fin c.size) :
    c.coordinate S i (tensorMap f (genericPoint n c).val) =
      f (Ideal.Quotient.mkₐ R (quadricIdeal n c) (MvPolynomial.X i)) := by
  rw [genericPoint_eval, c.coordinate_tensorMap]
  let q := Ideal.Quotient.mkₐ R (quadricIdeal n c)
  have h : q (quadricEquation n c (.inl i)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self _))
  rw [quadricEquation, map_sub, sub_eq_zero] at h
  exact congrArg f h

private noncomputable def evaluatePoint (f : QuadricRing n c →ₐ[R] S) :
    QuadricPoint (normBaseChange S n) :=
  ⟨tensorMap f (genericPoint n c).val, by rw [trace_tensorMap, trace_point, map_one],
    by rw [norm_tensorMap, (genericPoint n c).property.2, map_zero]⟩

private lemma evaluatePoint_bijective :
    Function.Bijective (evaluatePoint n c (S := S)) := by
  constructor
  · intro f g h
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    exact (quadricRing_coord n c f i).symm.trans
      ((congrArg (fun e : QuadricPoint (normBaseChange S n) => c.coordinate S i e.val) h).trans
      (quadricRing_coord n c g i))
  · intro e
    let l : MvPolynomial (Fin c.size) R →ₐ[R] S := MvPolynomial.aeval (c.coordinate S · e.val)
    have hv : tensorMap l c.generic = e.val := c.eval_generic S e.val
    have hl : quadricIdeal n c ≤ RingHom.ker l.toRingHom := by
      apply Ideal.span_le.mpr
      rintro x ⟨i, rfl⟩
      change l (quadricEquation n c i) = 0
      rcases i with i | (_ | _)
      · rw [quadricEquation, map_sub, ← c.coordinate_tensorMap, hv]
        simp only [l, MvPolynomial.aeval_X, sub_self]
      · rw [quadricEquation, map_sub, map_one, ← trace_tensorMap, hv, trace_point, sub_self]
      · rw [quadricEquation, ← norm_tensorMap, hv, norm_point]
    refine ⟨Ideal.Quotient.liftₐ _ l (fun x hx => RingHom.mem_ker.mp (hl hx)), Subtype.ext ?_⟩
    change tensorMap _ (genericPoint n c).val = e.val
    rw [genericPoint_eval, Ideal.Quotient.liftₐ_comp, hv]

end Quadric

section Geometry

variable {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C} [Module.Projective R C]

variable {S : Type w} {T : Type z} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Application of a homomorphism of test algebras to a quadric point. -/
noncomputable def mapPoint (f : S →ₐ[R] T) (e : QuadricPoint (normBaseChange S n)) :
    QuadricPoint (normBaseChange T n) :=
  ⟨tensorMap f e.val, by rw [trace_tensorMap, trace_point, map_one],
    by rw [norm_tensorMap, norm_point, map_zero]⟩

@[simp] lemma mapPoint_val (f : S →ₐ[R] T) (e : QuadricPoint (normBaseChange S n)) :
    (mapPoint f e).val = tensorMap f e.val := rfl

private lemma lift_point (hn : IsOctonionNorm n) (I : Ideal S) (hI : I ^ 2 = ⊥) :
    Function.Surjective (mapPoint (n := n) (Ideal.Quotient.mkₐ R I)) := by
  intro e
  let q := Ideal.Quotient.mkₐ R I
  obtain ⟨x, hx⟩ : ∃ x, tensorMap q x = e.val :=
    LinearMap.rTensor_surjective C (Ideal.Quotient.mkₐ_surjective R I) e.val
  let d := compositionTrace (normBaseChange S n) x - 1
  let b := normBaseChange S n x
  have hd : q d = 0 := by
    rw [show d = _ - 1 from rfl, map_sub, map_one, ← trace_tensorMap, hx, trace_point, sub_self]
  have hb : q b = 0 := by
    change q (normBaseChange S n x) = 0
    rw [← norm_tensorMap, hx, norm_point]
  have kill {r s : S} (hr : q r = 0) (hs : q s = 0) : r * s = 0 := by
    have h := Ideal.mul_mem_mul (Ideal.Quotient.eq_zero_iff_mem.mp hr)
      (Ideal.Quotient.eq_zero_iff_mem.mp hs)
    rw [← pow_two, hI] at h
    exact h
  let h := IsOctonionNorm.toNormLaws (octonion_norm_baseChange hn S)
  obtain ⟨e', he'⟩ := square_zero_correction h x (kill hd hd) (kill hb hb) (kill hd hb)
  refine ⟨e', Subtype.ext ?_⟩
  rw [mapPoint_val, he', map_sub, tensorMap_smul, tensorMap_smul, hx]
  change (q (1 - d + 2 * b)) • e.val - q b • tensorMap q (1 : S ⊗[R] C) = e.val
  simp [hd, hb]

variable {A : Type u} [CommRing A] [Algebra R A]

private lemma quadric_smooth_of_representation (hn : IsOctonionNorm n)
    (e : QuadricPoint (normBaseChange A n)) [Algebra.FinitePresentation R A]
    (he : ∀ (T : Type u) [CommRing T] [Algebra R T],
      Function.Bijective (fun f : A →ₐ[R] T => mapPoint f e)) :
    Algebra.Smooth R A := by
  refine ⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_, inferInstance⟩
  intro T _ _ I hI f
  obtain ⟨x, hx⟩ := lift_point hn I hI (mapPoint f e)
  obtain ⟨g, hg⟩ := (he T).surjective x
  refine ⟨g, (he (T ⧸ I)).injective (Subtype.ext ?_)⟩
  have hh := congrArg Subtype.val hx
  change tensorMap (Ideal.Quotient.mkₐ R I) x.val = tensorMap f e.val at hh
  exact (tensorMap_comp _ _ _).trans ((congrArg _ (congrArg Subtype.val hg)).trans hh)

set_option backward.isDefEq.respectTransparency false in
private lemma quadric_surjective_of_representation (hn : IsOctonionNorm n)
    (e : QuadricPoint (normBaseChange A n))
    (he : ∀ (T : Type u) [CommRing T] [Algebra R T],
      Function.Bijective (fun f : A →ₐ[R] T => mapPoint f e)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R A)) := by
  intro p
  let K := AlgebraicClosure p.asIdeal.ResidueField
  letI : Algebra R K :=
    ((algebraMap p.asIdeal.ResidueField K).comp (algebraMap R p.asIdeal.ResidueField)).toAlgebra
  letI : Field K := AlgebraicClosure.instField p.asIdeal.ResidueField
  letI : IsAlgClosed K := AlgebraicClosure.isAlgClosed p.asIdeal.ResidueField
  obtain ⟨x⟩ := @points_over_algebraically_closed K (K ⊗[R] C) _ _ _ _ _
    (normBaseChange K n) (octonion_norm_baseChange hn K) _
  obtain ⟨g, _⟩ := (he K).surjective x
  refine ⟨⟨RingHom.ker g.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  apply PrimeSpectrum.ext
  change (RingHom.ker g.toRingHom).comap (algebraMap R A) = p.asIdeal
  have hcomp : g.toRingHom.comp (algebraMap R A) = algebraMap R K :=
    RingHom.ext fun r => g.commutes r
  rw [RingHom.comap_ker, hcomp]
  change RingHom.ker ((algebraMap p.asIdeal.ResidueField K).comp
    (algebraMap R p.asIdeal.ResidueField)) = p.asIdeal
  rw [RingHom.ker_comp_of_injective _ (RingHom.injective _), Ideal.ker_algebraMap_residueField]

private lemma quadricRing_finitePresentation (c : FiniteCoordinates R C) :
    Algebra.FinitePresentation R (QuadricRing n c) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

end Geometry

theorem quadric_scheme : PeirceSpecification.quadricScheme.{u, v, w} := by
  intro R C _ _ _ _ _ n hn
  letI := hn.projective
  letI := hn.finite
  let c := FiniteCoordinates.ofProjective R C
  let e := genericPoint n c
  letI := quadricRing_finitePresentation (n := n) c
  have he (S : Type u) [CommRing S] [Algebra R S] :
      Function.Bijective (fun f : QuadricRing n c →ₐ[R] S => mapPoint f e) :=
    evaluatePoint_bijective n c
  letI := quadric_smooth_of_representation hn e he
  have hs := quadric_surjective_of_representation hn e he
  refine ⟨QuadricRing n c, inferInstance, inferInstance, e, ?_, ‹_›, hs,
    Module.FaithfullyFlat.of_comap_surjective hs⟩
  intro S _ _
  have h := evaluatePoint_bijective n c (S := S)
  exact ⟨fun f g hfg => h.injective (Subtype.ext hfg),
    fun x => ⟨(h.surjective x).choose, congrArg Subtype.val (h.surjective x).choose_spec⟩⟩

section TransportCorner

variable {S D E : Type*} [CommRing S] [NonAssocRing D] [NonAssocRing E]
  [Module S D] [Module S E] [IsScalarTower S D D] [IsScalarTower S E E]
  [SMulCommClass S D D] [SMulCommClass S E E]
  {q : QuadraticForm S D} {q' : QuadraticForm S E}

private lemma corner_image_iff (L : D ≃ₗ[S] E) (hL : ∀ x y, L (x * y) = L x * L y)
    (e : QuadricPoint q) (e' : QuadricPoint q') (he : L e.val = e'.val) (i j : S) (x : D) :
    L x ∈ corner e' i j ↔ x ∈ corner e i j := by
  rw [mem_corner_iff, mem_corner_iff, ← he, ← hL, ← hL, ← map_smul, ← map_smul]
  exact and_congr L.injective.eq_iff L.injective.eq_iff

private def transportCorner (L : D ≃ₗ[S] E) (hL : ∀ x y, L (x * y) = L x * L y)
    (e : QuadricPoint q) (e' : QuadricPoint q') (he : L e.val = e'.val) (i j : S) :
    corner e i j ≃ₗ[S] corner e' i j :=
  L.ofSubmodules _ _ <| by
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (corner_image_iff L hL e e' he i j x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := L.surjective y
      exact ⟨x, (corner_image_iff L hL e e' he i j x).mp hy, rfl⟩

end TransportCorner

section ScalarTower

open TensorProduct.AlgebraTensorModule (cancelBaseChange)

variable {R : Type u} {C : Type v} {A : Type w} {S : Type z}
  [CommRing R] [NonAssocRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [CommRing A] [Algebra R A] [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]

local notation "cancel" => cancelBaseChange R A S S C
local notation "inc" => IsScalarTower.toAlgHom R A S

lemma cancel_scalar_tmul (s : S) (x : A ⊗[R] C) :
    cancel (s ⊗ₜ[A] x) = s • tensorMap inc x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp [TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]

lemma cancel_scalar_mul (x y : S ⊗[A] (A ⊗[R] C)) :
    cancel (x * y) = cancel x * cancel y := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | tmul t b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, cancel_scalar_tmul, cancel_scalar_tmul,
        cancel_scalar_tmul, tensorMap_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    | add x y hx hy =>
      have h : (s ⊗ₜ[A] a) * (x + y) = (s ⊗ₜ[A] a) * x + (s ⊗ₜ[A] a) * y :=
        map_add (Algebra.TensorProduct.mul (s ⊗ₜ[A] a)) x y
      rw [h, map_add, hx, hy, map_add, mul_add]
  | add x z hx hz =>
    have h : (x + z) * y = x * y + z * y :=
      map_add ((Algebra.TensorProduct.mul).flip y) x z
    rw [h, map_add, hx, hz, map_add, add_mul]


variable [Module.Projective R C] {n : QuadraticForm R C}

set_option maxHeartbeats 1200000 in
/-- The identification of Peirce spaces under any further scalar extension of the test ring. -/
noncomputable def cornerAlong (hn : IsOctonionNorm n) (e : QuadricPoint (normBaseChange A n))
    (i j : Bool) :
    (S ⊗[A] corner e (eigenvalue A i) (eigenvalue A j)) ≃ₗ[S]
      corner (mapPoint (IsScalarTower.toAlgHom R A S) e) (eigenvalue S i) (eigenvalue S j) := by
  let hA := octonion_norm_baseChange hn A
  letI := hA.projective
  let eS := pointBaseChange S e
  let e' := mapPoint (IsScalarTower.toAlgHom R A S) e
  have he : cancel eS.val = e'.val := by
    change cancel ((1 : S) ⊗ₜ[A] e.val) = tensorMap (IsScalarTower.toAlgHom R A S) e.val
    rw [cancel_scalar_tmul, one_smul]
  exact (cornerBaseChange S hA e i j).trans
    (transportCorner cancel cancel_scalar_mul eS e' he (eigenvalue S i) (eigenvalue S j))

set_option maxHeartbeats 600000 in
lemma cornerAlong_tmul (hn : IsOctonionNorm n) (e : QuadricPoint (normBaseChange A n))
    (i j : Bool) (s : S) (x : corner e (eigenvalue A i) (eigenvalue A j)) :
    (cornerAlong hn e i j (s ⊗ₜ[A] x)).val = s • tensorMap inc x.val := by
  change cancel ((cornerBaseChange S (octonion_norm_baseChange hn A) e i j (s ⊗ₜ[A] x)).val) = _
  rw [cornerBaseChange_tmul, cancel_scalar_tmul]

end ScalarTower

section FrameLocal

variable {R : Type u} {C : Type v} {A : Type w}
  [CommRing R] [NonAssocRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [CommRing A] [Algebra R A] [Module.Projective R C] {n : QuadraticForm R C}

set_option backward.isDefEq.respectTransparency false in
theorem local_oriented_basis (hn : IsOctonionNorm n) (e : QuadricPoint (normBaseChange A n))
    (p : PrimeSpectrum A) :
    ∃ r : A, r ∉ p.asIdeal ∧
      Nonempty (PeirceSpecification.OrientedBasis
        (mapPoint (IsScalarTower.toAlgHom R A (Localization.Away r)) e)) := by
  let hnA := octonion_norm_baseChange hn A
  let V := corner e 1 0
  letI : Module.Finite A V := (projective_corners hnA e).1
  letI : Module.Projective A V := (projective_corners hnA e).2.1
  letI : Module.FinitePresentation A V := Module.finitePresentation_of_projective A V
  let L := Localization.AtPrime p.asIdeal
  haveI : Module.Free L (L ⊗[A] V) := by
    have hL : p ∈ Module.freeLocus A V := by rw [Module.freeLocus_eq_univ]; trivial
    exact (Module.mem_freeLocus_iff_tensor p L).mp hL
  have hLdim : Module.finrank L (L ⊗[A] V) = 3 :=
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl V).symm.finrank_eq.trans
      (corner_rank hnA e p).1
  obtain ⟨r, hr, hfree, hdim⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (M := V) (M' := L ⊗[A] V) p.asIdeal.primeCompl (TensorProduct.mk A L V 1) L

  refine ⟨r, hr, ?_⟩
  let S := Localization.Away r
  haveI : Nontrivial S :=
    (IsLocalization.map (M := .powers r) (T := p.asIdeal.primeCompl) L
      (RingHom.id A) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  have h3 : Module.finrank S (LocalizedModule.Away r V) = 3 :=
    hdim.trans hLdim
  letI := hfree
  have hf : Module.Finite S (LocalizedModule.Away r V) :=
    Module.Finite.of_isLocalizedModule (.powers r) (Rₚ := S) (LocalizedModule.mkLinearMap _ V)
  let b := (Module.finBasis S (LocalizedModule.Away r V)).reindex (finCongr h3)
  let E := (LocalizedModule.equivTensorProduct (.powers r) V).trans
    (cornerAlong (S := S) hn e true false)
  exact oriented_basis_exists (octonion_norm_baseChange hn S)
    (mapPoint (IsScalarTower.toAlgHom R A S) e) ⟨b.map E⟩

theorem local_oriented_bases : PeirceSpecification.localOrientedBases := by
  intro R C _ _ _ _ _ n hn A _ _ e p
  letI := hn.projective
  obtain ⟨r, hr, b⟩ := local_oriented_basis hn e p
  exact ⟨r, hr, _, rfl, b⟩

end FrameLocal

section StandardFrame

variable (R : Type u) [CommRing R]

private lemma zorn_trace (x : Zorn R) :
    compositionTrace (Zorn.norm R) x = (Zorn.coordinates R x).1 + (Zorn.coordinates R x).2.2.2 := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  rw [compositionTrace_apply]
  change _ = a + b
  rw [full_polar_formula, Zorn.norm_formula, Zorn.norm_formula, Zorn.norm_one]
  change (a + 1) * (b + 1) - (u + 0) ⬝ᵥ (v + 0) - (a * b - u ⬝ᵥ v) - 1 = a + b
  simp only [add_zero]
  ring

/-- The first diagonal idempotent of the coordinate Zorn algebra. -/
def firstPoint : QuadricPoint (Zorn.norm R) :=
  ⟨Zorn.first R, by rw [zorn_trace]; exact add_zero 1, by
    rw [Zorn.norm_formula]
    change (1 : R) * 0 - (0 : Fin 3 → R) ⬝ᵥ 0 = 0
    simp⟩

private def upperColumn (i : Fin 3) : Zorn R :=
  Zorn.ofCoordinates (0, Pi.single i 1, 0, 0)

private def lowerColumn (i : Fin 3) : Zorn R :=
  Zorn.ofCoordinates (0, 0, Pi.single i 1, 0)

private lemma lowerColumn_eq_mul (i : Fin 3) :
    lowerColumn R i = upperColumn R (i + 1) * upperColumn R (i + 2) := by
  have h : crossProduct (Pi.single (i + 1) (1 : R)) (Pi.single (i + 2) 1) = Pi.single i 1 := by
    funext j
    fin_cases i <;> fin_cases j <;> simp [cross_apply]
  change (0, 0, Pi.single i 1, 0) =
    Specification.zornProduct ((0 : R), Pi.single (i + 1) 1, 0, 0)
      (0, Pi.single (i + 2) 1, 0, 0)
  simp [Specification.zornProduct, h]

private lemma first_upper_iff (x : Zorn R) :
    x ∈ corner (firstPoint R) 1 0 ↔
      ∃ u : Fin 3 → R, x = Zorn.ofCoordinates (0, u, 0, 0) := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
  rw [mem_corner_iff]
  change (Specification.zornProduct ((1 : R), 0, 0, 0) (a, u, v, b) =
      (1 : R) • (a, u, v, b) ∧
    Specification.zornProduct (a, u, v, b) ((1 : R), 0, 0, 0) = (0 : R) • (a, u, v, b)) ↔
    ∃ t : Fin 3 → R, (a, u, v, b) = (0, t, 0, 0)
  simp [Specification.zornProduct, Prod.mk.injEq, eq_comm, ← Prod.mk_zero_zero]
  tauto

private def upperEquiv : (Fin 3 → R) ≃ₗ[R] corner (firstPoint R) 1 0 where
  toFun u := ⟨Zorn.ofCoordinates (0, u, 0, 0), (first_upper_iff R _).mpr ⟨u, rfl⟩⟩
  invFun x := (Zorn.coordinates R x.val).2.1
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨u, hu⟩ := (first_upper_iff R _).mp x.property
    exact Subtype.ext (by change Zorn.ofCoordinates (0, (Zorn.coordinates R x.val).2.1, 0, 0) = x.val
                          rw [hu]
                          rfl)
  map_add' u v := by
    apply Subtype.ext
    change Zorn.ofCoordinates (0, u + v, 0, 0) =
      Zorn.ofCoordinates ((0 : R), u, 0, 0) + Zorn.ofCoordinates (0, v, 0, 0)
    rw [← map_add]
    congr 1
    simp
  map_smul' r u := by
    apply Subtype.ext
    change (0, r • u, 0, 0) = (r * 0, r • u, r • (0 : Fin 3 → R), r * 0)
    simp

private noncomputable def firstBasis : Basis (Fin 3) R (corner (firstPoint R) 1 0) :=
  (Pi.basisFun R _).map (upperEquiv R)

private lemma firstBasis_apply (i : Fin 3) : (firstBasis R i).val = upperColumn R i := by
  rw [firstBasis, Basis.map_apply, Pi.basisFun_apply]
  rfl

private lemma firstBasis_volume : volume (n := Zorn.norm R) _ (firstBasis R) = 1 := by
  simp only [volume, firstBasis_apply]
  have h : upperColumn R 1 * upperColumn R 2 = lowerColumn R 0 :=
    (lowerColumn_eq_mul R (0 : Fin 3)).symm
  rw [h]
  rw [zorn_trace]
  change (0 * 0 + Pi.single (0 : Fin 3) (1 : R) ⬝ᵥ Pi.single 0 1) + (0 * 0 + (0 : Fin 3 → R) ⬝ᵥ 0) = 1
  simp

end StandardFrame

section FrameEquivalence

variable {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

private lemma ZornIsomorphism.map_trace (F : ZornIsomorphism n) (x : Zorn R) :
    compositionTrace n (F.toLinearEquiv x) = compositionTrace (Zorn.norm R) x := by
  simp only [compositionTrace_apply, full_polar_formula]
  rw [← F.map_one, ← map_add, F.map_norm, F.map_norm, F.map_norm]

private def image_first (F : ZornIsomorphism n) : QuadricPoint n :=
  ⟨F.toLinearEquiv (Zorn.first R), (ZornIsomorphism.map_trace F _).trans (trace_point (firstPoint R)),
    (F.map_norm _).trans (norm_point (firstPoint R))⟩

private lemma upper_image_iff (F : ZornIsomorphism n) (x : Zorn R) :
    F.toLinearEquiv x ∈ corner (image_first F) 1 0 ↔ x ∈ corner (firstPoint R) 1 0 := by
  rw [mem_corner_iff, mem_corner_iff]
  change (F.toLinearEquiv (Zorn.first R) * F.toLinearEquiv x = 1 • F.toLinearEquiv x ∧
    F.toLinearEquiv x * F.toLinearEquiv (Zorn.first R) = 0 • F.toLinearEquiv x) ↔ _
  rw [← F.map_mul, ← F.map_mul, ← map_smul, ← map_smul]
  exact and_congr F.toLinearEquiv.injective.eq_iff F.toLinearEquiv.injective.eq_iff

private noncomputable def imageUpper (F : ZornIsomorphism n) :
    corner (firstPoint R) 1 0 ≃ₗ[R] corner (image_first F) 1 0 := by
  apply F.toLinearEquiv.ofSubmodules
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (upper_image_iff F x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := F.toLinearEquiv.surjective y
    exact ⟨x, (upper_image_iff F x).mp hy, rfl⟩

private noncomputable def imageFrame (F : ZornIsomorphism n) : OrientedBasis (image_first F) := by
  refine ⟨(firstBasis R).map (imageUpper F), ?_⟩
  simp only [volume, Basis.map_apply, imageUpper, LinearEquiv.ofSubmodules_apply,
    ← F.map_mul, ZornIsomorphism.map_trace]
  exact firstBasis_volume R

private lemma imageFrame_apply (F : ZornIsomorphism n) (i : Fin 3) :
    ((imageFrame F).val i).val = F.toLinearEquiv (upperColumn R i) := by
  simp only [imageFrame, Basis.map_apply, imageUpper, LinearEquiv.ofSubmodules_apply, firstBasis_apply]

private lemma zornIsomorphism_ext (F G : ZornIsomorphism n)
    (h₁ : F.toLinearEquiv (Zorn.first R) = G.toLinearEquiv (Zorn.first R))
    (hu : ∀ i, F.toLinearEquiv (upperColumn R i) = G.toLinearEquiv (upperColumn R i)) : F = G := by
  have hl (i : Fin 3) : F.toLinearEquiv (lowerColumn R i) = G.toLinearEquiv (lowerColumn R i) := by
    rw [lowerColumn_eq_mul, F.map_mul, G.map_mul, hu, hu]
  have h₂ : F.toLinearEquiv (Zorn.second R) = G.toLinearEquiv (Zorn.second R) := by
    have h : Zorn.second R = 1 - Zorn.first R := by
      apply (Zorn.coordinates R).injective
      change ((0 : R), (0 : Fin 3 → R), (0 : Fin 3 → R), (1 : R)) =
        ((1 : R), 0, 0, 1) - ((1 : R), 0, 0, 0)
      simp
    rw [h, map_sub, map_sub, F.map_one, G.map_one, h₁]
  have h : F.toLinearEquiv = G.toLinearEquiv := by
    apply LinearEquiv.toLinearMap_injective
    apply (Zorn.coordinateBasis R).ext
    rintro (i | i)
    · cases i with
      | none =>
        have hh : Zorn.coordinateBasis R (Sum.inl none) = Zorn.first R := by
          simp [Zorn.coordinateBasis, Zorn.pairedFunctions, Zorn.pairedColumns,
            Pi.basisFun_apply, LinearEquiv.piOptionEquivProd, ZornSpecification.first]
          rfl
        simpa only [hh, LinearEquiv.coe_coe] using h₁
      | some i =>
        have hh : Zorn.coordinateBasis R (Sum.inl (some i)) = upperColumn R i := by
          simp [Zorn.coordinateBasis, Zorn.pairedFunctions, Zorn.pairedColumns,
            upperColumn, Pi.basisFun_apply, Pi.single_apply, LinearEquiv.piOptionEquivProd, funext_iff]
        simpa only [hh, LinearEquiv.coe_coe] using hu i
    · cases i with
      | none =>
        have hh : Zorn.coordinateBasis R (Sum.inr none) = Zorn.second R := by
          simp [Zorn.coordinateBasis, Zorn.pairedFunctions, Zorn.pairedColumns,
            Pi.basisFun_apply, LinearEquiv.piOptionEquivProd, ZornSpecification.second]
          rfl
        simpa only [hh, LinearEquiv.coe_coe] using h₂
      | some i =>
        have hh : Zorn.coordinateBasis R (Sum.inr (some i)) = -lowerColumn R i := by
          simp [Zorn.coordinateBasis, Zorn.pairedFunctions, Zorn.pairedColumns,
            lowerColumn, Pi.basisFun_apply, Pi.single_apply, LinearEquiv.piOptionEquivProd]
          apply (Zorn.coordinates R).injective
          rw [map_neg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          simp only [Prod.neg_mk, neg_zero, Prod.mk.injEq, neg_inj]
          exact ⟨trivial, rfl, funext (fun j => (Pi.single_apply i (1 : R) j).symm), trivial⟩
        rw [hh, map_neg, map_neg, LinearEquiv.coe_coe, LinearEquiv.coe_coe, hl i]
  cases F
  cases G
  cases h
  rfl

private lemma zornOfBasis_first (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : OrientedBasis e) :
    (zornOfBasis hn e b).toLinearEquiv (Zorn.first R) = e.val := by
  let d := lowerBasis hn e b.val
  change decomposition (IsOctonionNorm.toNormLaws hn) e
    (1, b.val.equivFun.symm 0, d.equivFun.symm 0, 0) = _
  simp only [decomposition_apply, map_zero, one_smul, ZeroMemClass.coe_zero, zero_smul, add_zero]

private lemma zornOfBasis_upper (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : OrientedBasis e) (i : Fin 3) :
    (zornOfBasis hn e b).toLinearEquiv (upperColumn R i) = (b.val i).val := by
  let d := lowerBasis hn e b.val
  have h : b.val.equivFun.symm (Pi.single i 1) = b.val i := by
    apply b.val.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext j
    simp only [Pi.single_apply, Basis.equivFun_self, eq_comm (a := j)]
  change decomposition (IsOctonionNorm.toNormLaws hn) e
    (0, b.val.equivFun.symm (Pi.single i 1), d.equivFun.symm 0, 0) = _
  simp only [decomposition_apply, h, map_zero, ZeroMemClass.coe_zero, zero_smul, add_zero, zero_add]

private lemma oriented_frames_ext (d e : Σ x : QuadricPoint n, OrientedBasis x)
    (h : d.1.val = e.1.val) (hb : ∀ i, ((d.2.val i)).val = ((e.2.val i)).val) : d = e := by
  obtain ⟨d, bd⟩ := d
  obtain ⟨e, be⟩ := e
  have hde : d = e := Subtype.ext h
  subst e
  apply congrArg (Sigma.mk d)
  apply Subtype.ext
  apply DFunLike.coe_injective
  funext i
  exact Subtype.ext (hb i)

/-- An isomorphism from the split Zorn model is determined by its first idempotent and upper frame. -/
noncomputable def frameEquiv (hn : IsOctonionNorm n) :
    ZornIsomorphism n ≃ (Σ e : QuadricPoint n, OrientedBasis e) where
  toFun F := ⟨image_first F, imageFrame F⟩
  invFun p := zornOfBasis hn p.1 p.2
  left_inv F := zornIsomorphism_ext _ F (zornOfBasis_first hn _ _)
    (fun i => (zornOfBasis_upper hn _ _ i).trans (imageFrame_apply F i))
  right_inv p := oriented_frames_ext _ p (zornOfBasis_first hn _ _)
    (fun i => (imageFrame_apply _ i).trans (zornOfBasis_upper hn _ _ i))

theorem zorn_frame_equivalence : PeirceSpecification.zornFrameEquivalence :=
  fun hn => ⟨frameEquiv hn, fun F => ⟨rfl, imageFrame_apply F⟩⟩

private lemma volume_change_of_basis (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : OrientedBasis e) (x : Fin 3 → corner e 1 0) :
    volume (n := n) _ x = (b.val.toMatrix x).det := by
  obtain ⟨a, ha⟩ := (alternating_volume hn e).1
  have hab : a b.val = 1 := (ha _).trans b.property
  calc
    _ = a x := (ha _).symm
    _ = _ := by
      nth_rw 1 [a.eq_smul_basis_det b.val]
      rw [smul_apply, hab, one_smul, Basis.det_apply]

/-- The ordered basis whose columns, in the given oriented basis, are the columns of a matrix in SL₃. -/
noncomputable def frameSMul (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : OrientedBasis e) (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    OrientedBasis e := by
  let b' := (Pi.basisFun R (Fin 3)).map (g.toLin'.trans b.val.equivFun.symm)
  have h : b.val.toMatrix b' = (g : Matrix (Fin 3) (Fin 3) R) := by
    apply Matrix.ext
    intro i j
    rw [Basis.toMatrix_apply, ← Basis.equivFun_apply, Basis.map_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, Pi.basisFun_apply, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  exact ⟨b', (volume_change_of_basis hn e b _).trans (h ▸ g.property)⟩

theorem frameSMul_matrix (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : OrientedBasis e) (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    b.val.toMatrix (frameSMul hn e b g).val = (g : Matrix (Fin 3) (Fin 3) R) := by
  apply Matrix.ext
  intro i j
  change b.val.repr (b.val.equivFun.symm (g.toLin' (Pi.basisFun R (Fin 3) j))) i = _
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one,
    Matrix.col_apply]

/-- The determinant-one change of basis acts simply transitively on the oriented frames. -/
noncomputable def orientedFrameEquivSL (hn : IsOctonionNorm n) (e : QuadricPoint n)
    (b : OrientedBasis e) :
    Matrix.SpecialLinearGroup (Fin 3) R ≃ OrientedBasis e := by
  apply Equiv.ofBijective (frameSMul hn e b)
  constructor
  · intro g g' h
    apply Subtype.ext
    rw [← frameSMul_matrix hn e b g, ← frameSMul_matrix hn e b g', h]
  · intro b'
    have h : (b.val.toMatrix b'.val).det = 1 :=
      (volume_change_of_basis hn e b _).symm.trans b'.property
    let g : Matrix.SpecialLinearGroup (Fin 3) R := ⟨b.val.toMatrix b'.val, h⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply DFunLike.coe_injective
    funext j
    apply b.val.repr.injective
    ext i
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i j) (frameSMul_matrix hn e b g)
    exact he

end FrameEquivalence

section SplitQuadric

open scoped Polynomial
open MvPolynomial (X)
open PeirceSpecification (SplitVars SplitQuadricRing scalarVar upperVar lowerVar splitEquation)

private lemma irreducible_linear {D : Type u} [CommRing D] [IsDomain D]
    {p q : D} (hp : Prime p) (hq : ¬p ∣ q) :
    Irreducible (Polynomial.C p * Polynomial.X + Polynomial.C q) := by
  let P := Polynomial.C p * Polynomial.X + Polynomial.C q
  have hdeg : P.natDegree = 1 := Polynomial.natDegree_linear hp.ne_zero
  have hP : P ≠ 0 := fun H => by simp [H] at hdeg
  have hunit (f g : D[X]) (h : P = f * g) (hf : f.natDegree = 0) : IsUnit f := by
    have hp' : p = f.coeff 0 * g.coeff 1 := by
      have E := congrArg (fun t : D[X] => t.coeff 1) h
      rw [Polynomial.eq_C_of_natDegree_eq_zero hf, Polynomial.coeff_C_mul] at E
      simpa [P, Polynomial.coeff_C_mul] using E
    have hq' : q = f.coeff 0 * g.coeff 0 := by
      have E := congrArg (fun t : D[X] => t.coeff 0) h
      simpa [P, Polynomial.coeff_C_mul] using E
    have hfU : IsUnit (f.coeff 0) := by
      rcases hp.irreducible.isUnit_or_isUnit hp' with h | h
      · exact h
      · have hd : p ∣ f.coeff 0 * g.coeff 1 := hp' ▸ dvd_refl p
        exact False.elim (hq (hq'.symm ▸ dvd_mul_of_dvd_left (h.dvd_mul_right.mp hd) _))
    nth_rw 1 [Polynomial.eq_C_of_natDegree_eq_zero hf]
    exact hfU.map Polynomial.C
  change Irreducible P
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp h
    rw [← hc, Polynomial.natDegree_C] at hdeg
    contradiction
  · intro f g hfg
    have hf : f ≠ 0 := by intro h; exact hP (by rw [hfg, h, zero_mul])
    have hg : g ≠ 0 := by intro h; exact hP (by rw [hfg, h, mul_zero])
    have hd : f.natDegree + g.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul hf hg, ← hfg, hdeg]
    rcases Nat.eq_zero_or_pos f.natDegree with hz | hz
    · exact Or.inl (hunit f g hfg hz)
    · exact Or.inr (hunit g f (hfg.trans (mul_comm f g)) (by omega))

private def swapVariable : SplitVars → SplitVars
  | none => some none
  | some none => none
  | some (some i) => some (some i)

private def swapVariables : SplitVars ≃ SplitVars where
  toFun := swapVariable
  invFun := swapVariable
  left_inv := by rintro (_ | (_ | _)) <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

private noncomputable def remainingPolynomial (R : Type u) [CommRing R] :
    MvPolynomial (Option (Fin 5)) R :=
  X none ^ 2 - X none + X (some 1) * X (some 3) + X (some 2) * X (some 4)

private lemma equation_linear (R : Type u) [CommRing R] :
    ((MvPolynomial.renameEquiv R swapVariables).trans (MvPolynomial.optionEquivLeft R _))
      (splitEquation R) =
    Polynomial.C (X (some 0)) * Polynomial.X + Polynomial.C (remainingPolynomial R) := by
  simp only [splitEquation, map_pow, map_sub, map_add, map_mul, Fin.sum_univ_three,
    AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  simp [scalarVar, upperVar, lowerVar, swapVariables, swapVariable, remainingPolynomial]
  ring

private lemma split_quadric_domain_field (K : Type u) [Field K] : IsDomain (SplitQuadricRing K) := by
  let E := (MvPolynomial.renameEquiv K swapVariables).trans (MvPolynomial.optionEquivLeft K _)
  have hh : ¬ (X (some (0 : Fin 5)) : MvPolynomial (Option (Fin 5)) K) ∣ remainingPolynomial K := by
    rintro ⟨q, hq⟩
    let f : Option (Fin 5) → K := fun i => if i = some 1 ∨ i = some 3 then 1 else 0
    have h := congrArg (MvPolynomial.eval f) hq
    simp [remainingPolynomial, f] at h
  have hi := irreducible_linear (MvPolynomial.X_prime (R := K) (i := some (0 : Fin 5))) hh
  have hp : Prime (splitEquation K) := by
    rw [← (MulEquiv.prime_iff E.toMulEquiv)]
    change Prime (((MvPolynomial.renameEquiv K swapVariables).trans
      (MvPolynomial.optionEquivLeft K _)) (splitEquation K))
    rw [equation_linear]
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hi
  letI : (Ideal.span {splitEquation K}).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  infer_instance

private noncomputable def scalarPolynomial (R : Type u) [CommRing R] :
    (MvPolynomial (Option (Fin 5)) R)[X] :=
  Polynomial.X ^ 2 - Polynomial.X +
    Polynomial.C (X (some 0) * X none + X (some 1) * X (some 3) + X (some 2) * X (some 4))

private lemma equation_monic (R : Type u) [CommRing R] :
    MvPolynomial.optionEquivLeft R _ (splitEquation R) = scalarPolynomial R := by
  simp [splitEquation, Fin.sum_univ_three, scalarVar, upperVar, lowerVar, scalarPolynomial, map_add]

private lemma scalarPolynomial_monic (R : Type u) [CommRing R] [Nontrivial R] :
    (scalarPolynomial R).Monic := by
  unfold scalarPolynomial
  rw [sub_add_eq_add_sub]
  have h : Polynomial.degree ((-Polynomial.X : (MvPolynomial (Option (Fin 5)) R)[X]) +
      Polynomial.C (X (some 0) * X none + X (some 1) * X (some 3) + X (some 2) * X (some 4))) < 2 := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    rw [max_lt_iff, Polynomial.degree_neg, Polynomial.degree_X]
    exact ⟨by decide, Polynomial.degree_C_le.trans_lt (by decide)⟩
  rw [add_sub_assoc, sub_eq_add_neg, add_comm (Polynomial.C _) (-Polynomial.X)]
  exact Polynomial.monic_X_pow_add h

private lemma scalarPolynomial_degree (R : Type u) [CommRing R] [Nontrivial R] :
    0 < (scalarPolynomial R).degree := by
  have hc : (scalarPolynomial R).coeff 2 = 1 := by simp [scalarPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  exact lt_of_lt_of_le (by decide : (0 : WithBot ℕ) < 2)
    (Polynomial.le_degree_of_ne_zero (hc ▸ one_ne_zero))

private noncomputable def quadricAdjoinRoot (R : Type u) [CommRing R] :
    SplitQuadricRing R ≃ₐ[R] AdjoinRoot (scalarPolynomial R) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.optionEquivLeft R _)
    (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {scalarPolynomial R} =
        Ideal.span {MvPolynomial.optionEquivLeft R _ (splitEquation R)}
      rw [equation_monic])

private lemma split_quadric_dimension_field (K : Type u) [Field K] :
    ringKrullDim (SplitQuadricRing K) = 6 := by
  let P := MvPolynomial (Option (Fin 5)) K
  let A := AdjoinRoot (scalarPolynomial K)
  letI : Algebra.IsIntegral P A := AdjoinRoot.isIntegral_of_monic (scalarPolynomial_monic K)
  have hinj : Function.Injective (algebraMap P A) :=
    AdjoinRoot.of.injective_of_monic_of_degree_pos (scalarPolynomial_monic K) (scalarPolynomial_degree K)
  letI : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have hd : ringKrullDim P = 6 := by
    change ringKrullDim (MvPolynomial (Option (Fin 5)) K) = 6
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  rw [ringKrullDim_eq_of_ringEquiv (quadricAdjoinRoot K).toRingEquiv]
  change ringKrullDim A = 6
  apply le_antisymm
  · rw [← hd]
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap P A))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under hpq
  · obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (show (6 : ℕ) ≤ ringKrullDim P by rw [hd]; exact le_rfl)
    obtain ⟨Q, hQ, hQover⟩ := (inferInstance : Nonempty (Ideal.primesOver l.head.asIdeal A))
    obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩

/-- The split quadric ring commutes with arbitrary extension of the base ring. -/
noncomputable def splitQuadricBaseChange (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] : (S ⊗[R] SplitQuadricRing R) ≃ₐ[S] SplitQuadricRing S := by
  let P := MvPolynomial SplitVars R
  let I : Ideal P := Ideal.span {splitEquation R}
  let E := Algebra.TensorProduct.tensorQuotientEquiv (R := R) S P S I
  let F : (S ⊗[R] P) ≃ₐ[S] MvPolynomial SplitVars S := MvPolynomial.algebraTensorAlgEquiv R S
  refine E.trans (Ideal.quotientEquivAlg _ _ F ?_)
  rw [show I = Ideal.span {splitEquation R} from rfl, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton]
  congr 2
  change splitEquation S = F (1 ⊗ₜ[R] splitEquation R)
  have h : F (1 ⊗ₜ[R] splitEquation R) =
      (1 : S) • MvPolynomial.map (algebraMap R S) (splitEquation R) :=
    MvPolynomial.algebraTensorAlgEquiv_tmul R S (1 : S) (splitEquation R)
  rw [h, one_smul]
  simp [splitEquation]

theorem split_quadric_fibers : PeirceSpecification.splitQuadricFibers := by
  intro R _ K _ _
  let e := splitQuadricBaseChange R K
  letI := split_quadric_domain_field K
  exact ⟨e.toMulEquiv.isDomain _, (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).trans
    (split_quadric_dimension_field K)⟩

end SplitQuadric

section Product

variable {R : Type u} [CommRing R] {C : Type v} [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C]
variable {I : Type w} [Fintype I] (S : I → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]

private abbrev componentModule (i : I) : Module (∀ i, S i) (S i ⊗[R] C) :=
  Module.compHom _ (Pi.evalRingHom S i)

private abbrev zornComponentModule (i : I) : Module (∀ i, S i) (Zorn (S i)) :=
  Module.compHom _ (Pi.evalRingHom S i)

private noncomputable def tensorPi :
    letI (i : I) := componentModule (R := R) (C := C) S i
    ((∀ i, S i) ⊗[R] C) ≃ₗ[(∀ i, S i)] ∀ i, S i ⊗[R] C := by
  classical
  letI (i : I) := componentModule (R := R) (C := C) S i
  let L : ((∀ i, S i) ⊗[R] C) →ₗ[(∀ i, S i)] (∀ i, S i ⊗[R] C) :=
    LinearMap.pi fun i =>
      { toFun := PeirceSpecification.tensorMap (Pi.evalAlgHom R S i)
        map_add' := map_add _
        map_smul' := by
          intro r x
          exact tensorMap_smul (Pi.evalAlgHom R S i) r x }
  have h : (L : ((∀ i, S i) ⊗[R] C) → _) = TensorProduct.piLeft R C S := by
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul s x =>
      funext i
      simp [L, TensorProduct.piLeft, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply LinearEquiv.ofBijective L
  rw [h]
  exact (TensorProduct.piLeft R C S).bijective

private lemma tensorPi_apply (x : (∀ i, S i) ⊗[R] C) (i : I) :
    (tensorPi S x) i = tensorMap (Pi.evalAlgHom R S i) x := rfl

private def fromZornPi (x : ∀ i, Zorn (S i)) : Zorn (∀ i, S i) :=
  Zorn.ofCoordinates (fun i => (Zorn.coordinates (S i) (x i)).1,
    fun j i => (Zorn.coordinates (S i) (x i)).2.1 j,
    fun j i => (Zorn.coordinates (S i) (x i)).2.2.1 j,
    fun i => (Zorn.coordinates (S i) (x i)).2.2.2)

private def zornPi :
    letI (i : I) := zornComponentModule S i
    Zorn (∀ i, S i) ≃ₗ[(∀ i, S i)] ∀ i, Zorn (S i) := by
  letI (i : I) := zornComponentModule S i
  refine
    { toFun := fun x i => ZornSpecification.mapCoordinates (Pi.evalRingHom S i) x
      invFun := fromZornPi S
      left_inv := by
        intro x
        obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates (∀ i, S i)).symm.surjective x
        rfl
      right_inv := by
        intro x
        funext i
        apply (Zorn.coordinates (S i)).injective
        rfl
      map_add' := by
        intro x y
        obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates (∀ i, S i)).symm.surjective x
        obtain ⟨⟨c, w, z, d⟩, rfl⟩ := (Zorn.coordinates (∀ i, S i)).symm.surjective y
        rfl
      map_smul' := by
        intro r x
        obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates (∀ i, S i)).symm.surjective x
        rfl }

private lemma zornPi_apply (x : Zorn (∀ i, S i)) (i : I) :
    zornPi S x i = ZornSpecification.mapCoordinates (Pi.evalRingHom S i) x := rfl

variable [Module.Projective R C] {n : QuadraticForm R C}

private noncomputable def zornProductIsomorphism
    (F : ∀ i, ZornIsomorphism (normBaseChange (S i) n)) : ZornIsomorphism (normBaseChange (∀ i, S i) n) := by
  letI (i : I) := componentModule (R := R) (C := C) S i
  letI (i : I) := zornComponentModule S i
  let E : (∀ i, Zorn (S i)) ≃ₗ[(∀ i, S i)] (∀ i, S i ⊗[R] C) :=
    LinearEquiv.piCongrRight fun i =>
    { toFun := (F i).toLinearEquiv
      invFun := (F i).toLinearEquiv.symm
      left_inv := (F i).toLinearEquiv.left_inv
      right_inv := (F i).toLinearEquiv.right_inv
      map_add' := (F i).toLinearEquiv.map_add
      map_smul' := fun r x => (F i).toLinearEquiv.map_smul (r i) x }
  let L := (zornPi S).trans (E.trans (tensorPi S).symm)
  have hL (x : Zorn (∀ i, S i)) (i : I) :
      tensorMap (Pi.evalAlgHom R S i) (L x) =
        (F i).toLinearEquiv (ZornSpecification.mapCoordinates (Pi.evalRingHom S i) x) := by
    rw [← tensorPi_apply]
    exact congrFun ((tensorPi S).apply_symm_apply (E (zornPi S x))) i
  refine ⟨L, ?_, ?_, ?_⟩
  · apply (tensorPi S).injective
    funext i
    change tensorMap (Pi.evalAlgHom R S i) (L 1) =
      tensorMap (Pi.evalAlgHom R S i) (1 : (∀ i, S i) ⊗[R] C)
    rw [hL, tensorMap_one]
    exact (F i).map_one
  · intro x y
    apply (tensorPi S).injective
    funext i
    change tensorMap (Pi.evalAlgHom R S i) (L (x * y)) =
      tensorMap (Pi.evalAlgHom R S i) (L x * L y)
    rw [hL, tensorMap_mul, hL, hL,
      Zorn.mapCoordinates_mul, (F i).map_mul]
  · intro x
    funext i
    change (Pi.evalAlgHom R S i) (normBaseChange (∀ i, S i) n (L x)) =
      (Pi.evalRingHom S i) (Zorn.norm (∀ i, S i) x)
    rw [← norm_tensorMap, hL, (F i).map_norm, Zorn.mapCoordinates_norm]

end Product

theorem faithfully_flat_split : PeirceSpecification.faithfullyFlatSplit.{u, v} := by
  classical
  intro R C _ _ _ _ _ n hn
  letI := hn.projective
  obtain ⟨A, _, _, e, _, hAsmooth, _, hAff⟩ := quadric_scheme.{u, v, u} hn
  choose r hr hb using local_oriented_basis hn e
  let U (p : PrimeSpectrum A) : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen (r p)
  have hU (p : PrimeSpectrum A) : IsOpen (U p) := (PrimeSpectrum.basicOpen (r p)).2
  have hcov : (Set.univ : Set (PrimeSpectrum A)) ⊆ ⋃ p, U p :=
    fun p _ => Set.mem_iUnion.mpr ⟨p, hr p⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  let S (i : t) := Localization.Away (r i.val)
  let T := ∀ i : t, S i
  letI (i : t) : Algebra.Smooth A (S i) := Algebra.Smooth.of_isLocalization_Away (r i.val)
  letI (i : t) : Algebra.FinitePresentation A (S i) := inferInstanceAs (Algebra.FinitePresentation A (S i))
  letI : Algebra.Smooth A T :=
    ⟨(Algebra.FormallySmooth.pi_iff S).mpr fun _ => inferInstance, inferInstance⟩
  have hT : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)) := by
    intro p
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ p))
    obtain ⟨hit, hip⟩ := Set.mem_iUnion.mp hi
    let j : t := ⟨i, hit⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (S j))) := by
      rwa [PrimeSpectrum.localization_away_comap_range _ (r i)]
    obtain ⟨q, hq⟩ := hp
    let g := Pi.evalAlgHom A S j
    refine ⟨PrimeSpectrum.comap g.toRingHom q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    have hh : g.toRingHom.comp (algebraMap A T) = algebraMap A (S j) :=
      RingHom.ext fun a => g.commutes a
    rwa [hh]
  letI := Module.FaithfullyFlat.of_comap_surjective hT
  let F (i : t) : ZornIsomorphism (normBaseChange (S i) n) :=
    zornOfBasis (octonion_norm_baseChange hn (S i)) _ (hb i.val).some
  exact ⟨T, inferInstance, inferInstance, Algebra.Smooth.comp R A T,
    Module.FaithfullyFlat.trans R A T, ⟨zornProductIsomorphism S F⟩⟩

open PeirceSpecification (SplitVars SplitQuadricRing scalarVar upperVar lowerVar splitEquation)

section SplitPoints

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

private noncomputable def splitGenerator (i : SplitVars) : SplitQuadricRing R :=
  Ideal.Quotient.mk (Ideal.span {splitEquation R}) (MvPolynomial.X i)

private def assignZornCoordinates (a : S) (x y : Fin 3 → S) : SplitVars → S
  | none => a
  | some none => y 0
  | some (some i) => ![x 0, x 1, x 2, y 1, y 2] i

private lemma evaluate_splitEquation (f : MvPolynomial SplitVars R →ₐ[R] S)
    (z : SplitVars → S) (hf : ∀ i, f (MvPolynomial.X i) = z i) :
    f (splitEquation R) =
      z scalarVar ^ 2 - z scalarVar + dotProduct (z ∘ upperVar) (z ∘ lowerVar) := by
  simp only [splitEquation, map_pow, map_sub, map_add, map_sum, map_mul, hf,
    dotProduct, Function.comp_apply]

private def zornOfAssignment (z : SplitVars → S) : Zorn S :=
  Zorn.ofCoordinates (z scalarVar, z ∘ upperVar, z ∘ lowerVar, 1 - z scalarVar)

private lemma assignment_roundtrip (z : SplitVars → S) :
    assignZornCoordinates (z scalarVar) (z ∘ upperVar) (z ∘ lowerVar) = z := by
  funext i
  rcases i with (_ | (_ | i))
  · rfl
  · rfl
  · fin_cases i <;> rfl

private noncomputable def splitPointFromHom (f : SplitQuadricRing R →ₐ[R] S) :
    QuadricPoint (Zorn.norm S) := by
  let z : SplitVars → S := fun i => f (splitGenerator i)
  refine ⟨zornOfAssignment z, ?_, ?_⟩
  · rw [zorn_trace]
    change z scalarVar + (1 - z scalarVar) = 1
    ring
  · have hp : Ideal.Quotient.mkₐ R (Ideal.span {splitEquation R}) (splitEquation R) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have h := congrArg f hp
    rw [map_zero] at h
    change (f.comp (Ideal.Quotient.mkₐ R (Ideal.span {splitEquation R}))) (splitEquation R) = 0 at h
    rw [evaluate_splitEquation _ z (fun _ => rfl)] at h
    rw [Zorn.norm_formula]
    change z scalarVar * (1 - z scalarVar) - dotProduct (z ∘ upperVar) (z ∘ lowerVar) = 0
    linear_combination -h

private lemma splitPointFromHom_bijective :
    Function.Bijective (splitPointFromHom (R := R) (S := S)) := by
  constructor
  · intro f g h
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    have hval := congrArg (fun e : QuadricPoint (Zorn.norm S) => Zorn.coordinates S e.val) h
    have he := congrArg (fun c : Specification.ZornCoordinates S =>
      assignZornCoordinates c.1 c.2.1 c.2.2.1) hval
    change assignZornCoordinates (f (splitGenerator scalarVar))
        ((fun i => f (splitGenerator i)) ∘ upperVar) ((fun i => f (splitGenerator i)) ∘ lowerVar) =
      assignZornCoordinates (g (splitGenerator scalarVar))
        ((fun i => g (splitGenerator i)) ∘ upperVar) ((fun i => g (splitGenerator i)) ∘ lowerVar) at he
    rw [assignment_roundtrip (fun i => f (splitGenerator i)),
      assignment_roundtrip (fun i => g (splitGenerator i))] at he
    exact congrFun he
  · rintro ⟨e, ht, hn⟩
    obtain ⟨⟨a, x, y, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective e
    let z := assignZornCoordinates a x y
    have ha : z scalarVar = a := rfl
    have hx : z ∘ upperVar = x := by funext i; fin_cases i <;> rfl
    have hy : z ∘ lowerVar = y := by funext i; fin_cases i <;> rfl
    have htrace : a + b = 1 := by
      change compositionTrace (Zorn.norm S) (Zorn.ofCoordinates (a, x, y, b)) = 1 at ht
      rw [zorn_trace] at ht
      exact ht
    have hb : b = 1 - a := (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using htrace))
    have hnorm : a * b - dotProduct x y = 0 := by
      change Zorn.norm S (Zorn.ofCoordinates (a, x, y, b)) = 0 at hn
      rw [Zorn.norm_formula] at hn
      exact hn
    let p : MvPolynomial SplitVars R →ₐ[R] S := MvPolynomial.aeval z
    have hp : p (splitEquation R) = 0 := by
      rw [evaluate_splitEquation p z (MvPolynomial.aeval_X z), ha, hx, hy, hb] at *
      linear_combination -hnorm
    have hI : Ideal.span {splitEquation R} ≤ RingHom.ker p.toRingHom :=
      Ideal.span_le.mpr (by rintro _ rfl; exact RingHom.mem_ker.mpr hp)
    refine ⟨Ideal.Quotient.liftₐ _ p (fun _ ha => RingHom.mem_ker.mp (hI ha)), Subtype.ext ?_⟩
    apply (Zorn.coordinates S).injective
    have hvar (i : SplitVars) :
        (Ideal.Quotient.liftₐ _ p (fun _ ha => RingHom.mem_ker.mp (hI ha))) (splitGenerator i) = z i :=
      MvPolynomial.aeval_X z i
    change ( _, _, _, _) = (a, x, y, b)
    simp only [hvar, ha, hx, hy, hb]

private lemma zorn_coordinateMap_smul {T : Type w} [CommRing T] (f : S →+* T)
    (s : S) (x : Zorn S) :
    ZornSpecification.mapCoordinates f (s • x) = f s • ZornSpecification.mapCoordinates f x := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  apply (Zorn.coordinates T).injective
  change (f (s * a), fun i => f (s * u i), fun i => f (s * v i), f (s * b)) =
    (f s * f a, fun i => f s * f (u i), fun i => f s * f (v i), f s * f b)
  simp only [map_mul]

private lemma zorn_coordinateMap_add {T : Type w} [CommRing T] (f : S →+* T) (x y : Zorn S) :
    ZornSpecification.mapCoordinates f (x + y) =
      ZornSpecification.mapCoordinates f x + ZornSpecification.mapCoordinates f y := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  obtain ⟨⟨c, w, z, d⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective y
  apply (Zorn.coordinates T).injective
  change (f (a + c), fun i => f (u i + w i), fun i => f (v i + z i), f (b + d)) =
    (f a + f c, fun i => f (u i) + f (w i), fun i => f (v i) + f (z i), f b + f d)
  simp only [map_add]

lemma zorn_baseChange_naturality {T : Type w} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (x : S ⊗[R] Zorn R) :
    Zorn.baseChange R T (tensorMap f x) =
      ZornSpecification.mapCoordinates f.toRingHom (Zorn.baseChange R S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    rw [tensorMap_tmul, Zorn.baseChange_tmul, Zorn.baseChange_tmul, zorn_coordinateMap_smul]
    congr 1
    obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates R).symm.surjective x
    apply (Zorn.coordinates T).injective
    change (algebraMap R T a, fun i => algebraMap R T (u i), fun i => algebraMap R T (v i), algebraMap R T b) =
      (f (algebraMap R S a), fun i => f (algebraMap R S (u i)), fun i => f (algebraMap R S (v i)),
        f (algebraMap R S b))
    simp only [AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy, zorn_coordinateMap_add]

private lemma trace_zorn_baseChange (x : S ⊗[R] Zorn R) :
    compositionTrace (Zorn.norm S) (Zorn.baseChange R S x) =
      compositionTrace (normBaseChange S (Zorn.norm R)) x := by
  simp only [compositionTrace_apply, Zorn.baseChange_polar,
    LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Zorn.baseChange_one]

private noncomputable def zornQuadricOver :
    QuadricPoint (normBaseChange S (Zorn.norm R)) ≃ QuadricPoint (Zorn.norm S) where
  toFun x := ⟨Zorn.baseChange R S x.val, (trace_zorn_baseChange x.val).trans (trace_point x),
    by
      have h := DFunLike.congr_fun (Zorn.baseChange_norm (R := R) (S := S)) x.val
      exact h ▸ x.property.2⟩
  invFun x := ⟨(Zorn.baseChange R S).symm x.val, by
    rw [← trace_zorn_baseChange, LinearEquiv.apply_symm_apply, trace_point],
    by
      rw [Zorn.baseChange_norm, QuadraticMap.comp_apply]
      exact ((congrArg (Zorn.norm S) ((Zorn.baseChange R S).apply_symm_apply x.val))).trans (norm_point x)⟩
  left_inv x := Subtype.ext ((Zorn.baseChange R S).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((Zorn.baseChange R S).apply_symm_apply x.val)

set_option maxHeartbeats 600000 in
private noncomputable def splitUniversalPoint (R : Type u) [CommRing R] :
    QuadricPoint (C := SplitQuadricRing R ⊗[R] Zorn R)
      (normBaseChange (SplitQuadricRing R) (Zorn.norm R)) :=
  (zornQuadricOver (R := R) (S := SplitQuadricRing R)).symm
    (splitPointFromHom (AlgHom.id R (SplitQuadricRing R)))

set_option maxHeartbeats 700000 in
private lemma split_eval (f : SplitQuadricRing R →ₐ[R] S) :
    Zorn.baseChange R S (tensorMap f (splitUniversalPoint R).val) = (splitPointFromHom f).val := by
  rw [zorn_baseChange_naturality]
  have h := congrArg Subtype.val ((zornQuadricOver (R := R) (S := SplitQuadricRing R)).apply_symm_apply
    (splitPointFromHom (AlgHom.id R (SplitQuadricRing R))))
  change Zorn.baseChange R (SplitQuadricRing R) (splitUniversalPoint R).val =
    (splitPointFromHom (AlgHom.id R (SplitQuadricRing R))).val at h
  rw [h]
  apply (Zorn.coordinates S).injective
  change (f (splitGenerator scalarVar), (fun i => f (splitGenerator (upperVar i))),
      (fun i => f (splitGenerator (lowerVar i))), f (1 - splitGenerator scalarVar)) =
    (f (splitGenerator scalarVar), (fun i => f (splitGenerator (upperVar i))),
      (fun i => f (splitGenerator (lowerVar i))), 1 - f (splitGenerator scalarVar))
  rw [map_sub, map_one]

private lemma split_evaluation_bijective :
    Function.Bijective (fun f : SplitQuadricRing R →ₐ[R] S =>
      mapPoint (n := Zorn.norm R) f (splitUniversalPoint R)) := by
  have he := splitPointFromHom_bijective (R := R) (S := S)
  constructor
  · intro f g h
    apply he.injective
    apply Subtype.ext
    rw [← split_eval f, ← split_eval g]
    exact congrArg (Zorn.baseChange R S) (congrArg Subtype.val h)
  · intro e
    obtain ⟨f, hf⟩ := he.surjective (zornQuadricOver (R := R) (S := S) e)
    refine ⟨f, Subtype.ext ((Zorn.baseChange R S).injective ?_)⟩
    exact (split_eval f).trans (congrArg Subtype.val hf)

theorem split_quadric_scheme : PeirceSpecification.splitQuadricScheme.{u, v} := by
  intro R _
  letI : Algebra.FinitePresentation R (SplitQuadricRing R) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_singleton _))
  refine ⟨splitUniversalPoint R, ?_, quadric_smooth_of_representation (Zorn.isOctonion R) (splitUniversalPoint R) ?_⟩
  · intro S _ _
    have h := split_evaluation_bijective (R := R) (S := S)
    exact ⟨fun f g hfg => h.injective (Subtype.ext hfg),
      fun x => ⟨(h.surjective x).choose, congrArg Subtype.val (h.surjective x).choose_spec⟩⟩
  · intro T _ _
    exact split_evaluation_bijective

end SplitPoints

open PeirceSpecification (SplitAutomorphism)
open private octonion_norm_comp_equiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.Adjoints

section FrameAction

variable {R : Type u} {C : Type v} [CommRing R] [NonAssocRing C] [Module R C]
  [IsScalarTower R C C] [SMulCommClass R C C] {n : QuadraticForm R C}

theorem frameSMul_apply (hn : IsOctonionNorm n) (e : QuadricPoint n) (b : OrientedBasis e)
    (g : Matrix.SpecialLinearGroup (Fin 3) R) (j : Fin 3) :
    (frameSMul hn e b g).val j = ∑ i, g i j • b.val i := by
  let b' := (frameSMul hn e b g).val
  rw [← b.val.sum_equivFun (b' j)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i j) (frameSMul_matrix hn e b g)

theorem frameSMul_one (hn : IsOctonionNorm n) (e : QuadricPoint n) (b : OrientedBasis e) :
    frameSMul hn e b 1 = b := by
  apply Subtype.ext
  apply DFunLike.coe_injective
  funext j
  rw [frameSMul_apply]
  simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, eq_comm]

theorem frameSMul_mul (hn : IsOctonionNorm n) (e : QuadricPoint n) (b : OrientedBasis e)
    (g h : Matrix.SpecialLinearGroup (Fin 3) R) :
    frameSMul hn e (frameSMul hn e b g) h = frameSMul hn e b (g * h) := by
  apply Subtype.ext
  apply DFunLike.coe_injective
  funext j
  simp_rw [frameSMul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul]
  change (∑ k, h k j * g i k) • b.val i =
    ((g * h : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i j • b.val i
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  simp only [mul_comm]

theorem oriented_frame_action : PeirceSpecification.orientedFrameAction := by
  intro R C _ _ _ _ _ n hn e
  exact ⟨frameSMul hn e, frameSMul_apply hn e,
    fun b => ⟨frameSMul_one hn e b, (orientedFrameEquivSL hn e b).bijective⟩,
    frameSMul_mul hn e⟩

end FrameAction

section ExtendFrame

variable {R : Type u} {C : Type v} {A : Type w} {S : Type z}
  [CommRing R] [NonAssocRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  [CommRing A] [Algebra R A] [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
  [Module.Projective R C] {n : QuadraticForm R C}

local notation "inc" => IsScalarTower.toAlgHom R A S

/-- Extend an oriented basis of a Peirce space along a scalar ring map. -/
noncomputable def extendFrame (hn : IsOctonionNorm n) (e : QuadricPoint (normBaseChange A n))
    (b : OrientedBasis e) : OrientedBasis (mapPoint inc e) := by
  let L : (S ⊗[A] corner e 1 0) ≃ₗ[S] corner (mapPoint inc e) 1 0 :=
    cornerAlong (S := S) hn e true false
  let c : Basis (Fin 3) S (corner (mapPoint inc e) 1 0) := (b.val.baseChange S).map L
  have hc (i : Fin 3) : (c i).val = tensorMap inc (b.val i).val := by
    change ((cornerAlong (S := S) hn e true false) ((b.val.baseChange S) i)).val = _
    rw [Basis.baseChange_apply]
    exact (cornerAlong_tmul hn e true false (1 : S) (b.val i)).trans (one_smul _ _)
  refine ⟨c, ?_⟩
  change compositionTrace (normBaseChange S n) ((c 0).val * ((c 1).val * (c 2).val)) = 1
  simp only [hc, ← tensorMap_mul, trace_tensorMap]
  rw [show compositionTrace (normBaseChange A n)
    ((b.val 0).val * ((b.val 1).val * (b.val 2).val)) = 1 from b.property, map_one]

theorem extendFrame_apply (hn : IsOctonionNorm n) (e : QuadricPoint (normBaseChange A n))
    (b : OrientedBasis e) (i : Fin 3) :
    ((extendFrame (S := S) hn e b).val i).val = tensorMap inc (b.val i).val := by
  change ((cornerAlong (S := S) hn e true false) ((b.val.baseChange S) i)).val = _
  rw [Basis.baseChange_apply]
  exact (cornerAlong_tmul hn e true false (1 : S) (b.val i)).trans (one_smul _ _)

theorem extendFrame_action (hn : IsOctonionNorm n) (e : QuadricPoint (normBaseChange A n))
    (b : OrientedBasis e) (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    extendFrame (S := S) hn e (frameSMul (octonion_norm_baseChange hn A) e b g) =
      frameSMul (octonion_norm_baseChange hn S) (mapPoint inc e)
        (extendFrame (S := S) hn e b) (Matrix.SpecialLinearGroup.map (algebraMap A S) g) := by
  apply Subtype.ext
  apply DFunLike.coe_injective
  funext j
  apply Subtype.ext
  rw [extendFrame_apply, frameSMul_apply, frameSMul_apply]
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, map_sum, tensorMap_smul,
    extendFrame_apply]
  rfl

end ExtendFrame

section SplitAutomorphism

variable (R : Type u) [CommRing R]

private noncomputable def normIsoOfAutomorphism (F : SplitAutomorphism R) :
    ZornIsomorphism (Zorn.norm R) := by
  refine ⟨F.val, F.property.1, F.property.2, fun x => ?_⟩
  have h := (octonion_norm_unique (octonion_norm_comp_equiv (Zorn.isOctonion R)
    F.val F.property.2) (Zorn.isOctonion R)).1
  exact DFunLike.congr_fun h x

private def forgetNorm (F : ZornIsomorphism (Zorn.norm R)) : SplitAutomorphism R :=
  ⟨F.toLinearEquiv, F.map_one, F.map_mul⟩

/-- The isomorphism taking a split automorphism to its idempotent and its three upper columns. -/
noncomputable def splitAutomorphismFrames :
    SplitAutomorphism R ≃ (Σ e : QuadricPoint (Zorn.norm R), OrientedBasis e) :=
  (Equiv.mk (normIsoOfAutomorphism R) (forgetNorm R)
    (fun f => Subtype.ext (by rfl)) (by rintro ⟨L, h₁, hm, hq⟩; rfl)).trans
      (frameEquiv (Zorn.isOctonion R))

theorem split_automorphism_frame_equivalence : PeirceSpecification.splitAutomorphismFrameEquivalence :=
  fun R _ => ⟨splitAutomorphismFrames R, fun F => ⟨rfl, imageFrame_apply (normIsoOfAutomorphism R F)⟩⟩

end SplitAutomorphism

section Charts

variable {S : Type v} [CommRing S]

private noncomputable def fiberFromBasis (e : QuadricPoint (Zorn.norm S)) (b : OrientedBasis e) :
    {F : SplitAutomorphism S // F.val (Zorn.first S) = e.val} :=
  ⟨forgetNorm S (zornOfBasis (Zorn.isOctonion S) e b), zornOfBasis_first _ _ _⟩

private lemma fiberFromBasis_upper (e : QuadricPoint (Zorn.norm S)) (b : OrientedBasis e) (i : Fin 3) :
    (fiberFromBasis e b).val.val (upperColumn S i) = (b.val i).val :=
  zornOfBasis_upper (Zorn.isOctonion S) e b i

private lemma zornFrame_fiberFromBasis (e : QuadricPoint (Zorn.norm S)) (b : OrientedBasis e) :
    splitAutomorphismFrames S (fiberFromBasis e b).val = ⟨e, b⟩ :=
  (frameEquiv (Zorn.isOctonion S)).apply_symm_apply ⟨e, b⟩

private lemma frame_value_of_fst
    (p : Σ e : QuadricPoint (Zorn.norm S), OrientedBasis e)
    (e : QuadricPoint (Zorn.norm S)) (h : p.1 = e) :
    ∃ b : OrientedBasis e, (⟨e, b⟩ : Σ e' : QuadricPoint (Zorn.norm S), OrientedBasis e') = p := by
  obtain ⟨x, b⟩ := p
  change x = e at h
  subst e
  exact ⟨b, rfl⟩

private lemma fiberFromBasis_bijective (e : QuadricPoint (Zorn.norm S)) :
    Function.Bijective (fiberFromBasis e) := by
  constructor
  · intro b c h
    have eq := congrArg (fun f => splitAutomorphismFrames S f.val) h
    rw [zornFrame_fiberFromBasis, zornFrame_fiberFromBasis] at eq
    exact eq_of_heq (Sigma.mk.inj eq).2
  · intro F
    have h : (splitAutomorphismFrames S F.val).1 = e := Subtype.ext F.property
    obtain ⟨b, hb⟩ := frame_value_of_fst (splitAutomorphismFrames S F.val) e h
    refine ⟨b, Subtype.ext ((splitAutomorphismFrames S).injective ?_)⟩
    exact (zornFrame_fiberFromBasis e b).trans hb

private noncomputable def trivializeEvaluation (e : QuadricPoint (Zorn.norm S)) (b : OrientedBasis e) :
    Matrix.SpecialLinearGroup (Fin 3) S ≃ {F : SplitAutomorphism S // F.val (Zorn.first S) = e.val} :=
  (orientedFrameEquivSL (Zorn.isOctonion S) e b).trans
    (Equiv.ofBijective (fiberFromBasis e) (fiberFromBasis_bijective e))

private lemma trivializeEvaluation_apply (e : QuadricPoint (Zorn.norm S)) (b : OrientedBasis e)
    (g : Matrix.SpecialLinearGroup (Fin 3) S) (i : Fin 3) :
    (trivializeEvaluation e b g).val.val (upperColumn S i) = ∑ j, g j i • (b.val j).val := by
  change (fiberFromBasis e (frameSMul (Zorn.isOctonion S) e b g)).val.val (upperColumn S i) = _
  rw [fiberFromBasis_upper, frameSMul_apply, AddSubmonoidClass.coe_finsetSum]
  simp only [SetLike.val_smul]

variable {R : Type u} [CommRing R] [Algebra R S]

private noncomputable def zornFrameOver
    (e : QuadricPoint (normBaseChange S (Zorn.norm R))) (b : OrientedBasis e) :
    OrientedBasis (zornQuadricOver (R := R) (S := S) e) := by
  let E := Zorn.baseChange R S
  let L := transportCorner E (Zorn.baseChange_mul (R := R) (S := S)) e (zornQuadricOver e) rfl 1 0
  let c := b.val.map L
  have h (i : Fin 3) : (c i).val = E (b.val i).val := by
    rw [show c i = L (b.val i) from Basis.map_apply _ _ _]
    rfl
  refine ⟨c, ?_⟩
  change compositionTrace (Zorn.norm S) ((c 0).val * ((c 1).val * (c 2).val)) = 1
  simp only [h, ← Zorn.baseChange_mul, trace_zorn_baseChange, E]
  exact b.property

private lemma zornFrameOver_apply
    (e : QuadricPoint (normBaseChange S (Zorn.norm R))) (b : OrientedBasis e) (i : Fin 3) :
    ((zornFrameOver e b).val i).val = Zorn.baseChange R S (b.val i).val := rfl

end Charts

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem split_frame_charts : PeirceSpecification.splitFrameCharts.{u, v} := by
  intro R A _ _ _ e p
  have hn := Zorn.isOctonion R
  obtain ⟨r, hr, ⟨b⟩⟩ := local_oriented_basis hn e p
  let L := Localization.Away r
  let l := IsScalarTower.toAlgHom R A L
  let eL := mapPoint l e
  refine ⟨r, hr, (fun i => ((zornFrameOver eL b).val i).val), ?_⟩
  intro S _ _ f
  letI : Algebra L S := f.toRingHom.toAlgebra
  letI : IsScalarTower R L S := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  let eS := mapPoint f eL
  let y := zornQuadricOver (R := R) (S := S) eS
  have he : y.val = Zorn.baseChange R S (tensorMap (f.comp l) e.val) := by
    change Zorn.baseChange R S (tensorMap f (tensorMap l e.val)) = _
    rw [tensorMap_comp]
  change ∃ E : Matrix.SpecialLinearGroup (Fin 3) S ≃
      {F : SplitAutomorphism S // F.val (Zorn.first S) = Zorn.baseChange R S (tensorMap (f.comp l) e.val)},
      ∀ g i, (E g).val.val (upperColumn S i) =
        ∑ j, g j i • ZornSpecification.mapCoordinates f.toRingHom ((zornFrameOver eL b).val j).val
  rw [← he]
  let bS : OrientedBasis eS := extendFrame (S := S) hn eL b
  let d : OrientedBasis y := zornFrameOver eS bS
  have hcol (j : Fin 3) : (d.val j).val =
      ZornSpecification.mapCoordinates f.toRingHom ((zornFrameOver eL b).val j).val := by
    calc
      (d.val j).val = Zorn.baseChange R S (bS.val j).val := zornFrameOver_apply eS bS j
      _ = Zorn.baseChange R S (tensorMap f (b.val j).val) :=
        congrArg (Zorn.baseChange R S) (extendFrame_apply hn eL b j)
      _ = ZornSpecification.mapCoordinates f.toRingHom
          (Zorn.baseChange R L (b.val j).val) := zorn_baseChange_naturality f _
      _ = _ := rfl
  refine ⟨trivializeEvaluation y d, fun g i => ?_⟩
  rw [trivializeEvaluation_apply]
  simp only [hcol]

open PeirceSpecification (SplitQuadricRing)

section PolynomialEquations

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type w} {J : Type w'} (eqs : J → MvPolynomial ι R)

private abbrev EquationRing := MvPolynomial ι R ⧸ Ideal.span (Set.range eqs)

private noncomputable def equationGenerator (i : ι) : EquationRing eqs :=
  Ideal.Quotient.mk (Ideal.span (Set.range eqs)) (MvPolynomial.X i)

private lemma evaluate_generators (f : EquationRing eqs →ₐ[R] S) :
    MvPolynomial.aeval (fun i => f (equationGenerator eqs i)) =
      f.comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range eqs))) := by
  apply MvPolynomial.algHom_ext
  intro i
  exact MvPolynomial.aeval_X _ i

private noncomputable def equationsPoint (f : EquationRing eqs →ₐ[R] S) :
    {a : ι → S // ∀ j, MvPolynomial.aeval a (eqs j) = 0} :=
  ⟨fun i => f (equationGenerator eqs i), fun j => by
    rw [evaluate_generators, AlgHom.comp_apply]
    exact (congrArg f (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self j)))).trans (map_zero f)⟩

private lemma equationsPoint_bijective : Function.Bijective (equationsPoint eqs (S := S)) := by
  constructor
  · intro f g hf
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    exact congrFun (congrArg Subtype.val hf)
  · intro a
    have h : Ideal.span (Set.range eqs) ≤ RingHom.ker (MvPolynomial.aeval a.val).toRingHom :=
      Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact RingHom.mem_ker.mpr (a.property j))
    refine ⟨Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a.val)
      (fun _ hx => RingHom.mem_ker.mp (h hx)), ?_⟩
    apply Subtype.ext
    funext i
    exact MvPolynomial.aeval_X _ i

end PolynomialEquations

section OctonionMatrices

private abbrev ZornIndex := Option (Fin 3) ⊕ Option (Fin 3)

variable {S : Type v} {T : Type w} [CommRing S] [CommRing T]

private abbrev zornLinear (M : Matrix ZornIndex ZornIndex S) : Zorn S →ₗ[S] Zorn S :=
  (Zorn.pairedFunctions S).symm.toLinearMap ∘ₗ
    Matrix.toLin' M ∘ₗ (Zorn.pairedFunctions S).toLinearMap

private abbrev zornMatrix (L : Zorn S →ₗ[S] Zorn S) : Matrix ZornIndex ZornIndex S :=
  LinearMap.toMatrix' ((Zorn.pairedFunctions S).toLinearMap ∘ₗ L ∘ₗ
    (Zorn.pairedFunctions S).symm.toLinearMap)

private lemma zornLinear_zornMatrix (L : Zorn S →ₗ[S] Zorn S) : zornLinear (zornMatrix L) = L := by
  ext1 x
  simp [Matrix.toLin'_toMatrix']

private lemma zornMatrix_zornLinear (A : Matrix ZornIndex ZornIndex S) : zornMatrix (zornLinear A) = A := by
  rw [← LinearMap.toMatrix'_toLin' A]
  ext1 x
  simp

private lemma zornLinear_mul (M N : Matrix ZornIndex ZornIndex S) :
    zornLinear (M * N) = zornLinear M ∘ₗ zornLinear N := by
  ext1 x
  simp

private lemma zornLinear_one : zornLinear (1 : Matrix ZornIndex ZornIndex S) = LinearMap.id := by
  ext1 x
  simp

private lemma pairedFunctions_mapCoordinates (φ : S →+* T) (x : Zorn S) (i : ZornIndex) :
    Zorn.pairedFunctions T (ZornSpecification.mapCoordinates φ x) i =
      φ (Zorn.pairedFunctions S x i) := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  rcases i with (i | i) <;> cases i
  · rfl
  · rfl
  · rfl
  · exact (map_neg φ _).symm

private lemma zornLinear_natural (φ : S →+* T) (M : Matrix ZornIndex ZornIndex S) (x : Zorn S) :
    ZornSpecification.mapCoordinates φ (zornLinear M x) =
      zornLinear (φ.mapMatrix M) (ZornSpecification.mapCoordinates φ x) := by
  apply (Zorn.pairedFunctions T).injective
  funext i
  rw [pairedFunctions_mapCoordinates]
  have h (j : ZornIndex) : Zorn.pairedFunctions T (ZornSpecification.mapCoordinates φ x) j =
      (φ ∘ Zorn.pairedFunctions S x) j := pairedFunctions_mapCoordinates φ x j
  simp only [zornLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]
  rw [show Zorn.pairedFunctions T (ZornSpecification.mapCoordinates φ x) = φ ∘ Zorn.pairedFunctions S x
    from funext h]
  exact φ.map_mulVec M (Zorn.pairedFunctions S x) i

private lemma map_zorn_one (φ : S →+* T) : ZornSpecification.mapCoordinates φ (1 : Zorn S) = 1 := by
  apply (Zorn.coordinates T).injective
  change (φ 1, (fun _ : Fin 3 => φ 0), (fun _ : Fin 3 => φ 0), φ 1) =
    (1, (0 : Fin 3 → T), (0 : Fin 3 → T), 1)
  simp [Pi.zero_def]

private noncomputable def zornBasis (S : Type v) [CommRing S] : Basis ZornIndex S (Zorn S) :=
  (Pi.basisFun S ZornIndex).map (Zorn.pairedFunctions S).symm

private lemma map_zornBasis (φ : S →+* T) (i : ZornIndex) :
    ZornSpecification.mapCoordinates φ (zornBasis S i) = zornBasis T i := by
  apply (Zorn.pairedFunctions T).injective
  funext j
  rw [pairedFunctions_mapCoordinates]
  simp only [zornBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  by_cases h : j = i <;> simp [h]

private lemma multiplicative_on_basis {L : Zorn S →ₗ[S] Zorn S}
    (h : ∀ i j, L (zornBasis S i * zornBasis S j) = L (zornBasis S i) * L (zornBasis S j))
    (x y : Zorn S) : L (x * y) = L x * L y := by
  have H : (LinearMap.mul S (Zorn S)).compr₂ L =
      (LinearMap.mul S (Zorn S)).compl₁₂ L L := by
    apply (zornBasis S).ext
    intro i
    apply (zornBasis S).ext
    exact h i
  exact LinearMap.congr_fun (LinearMap.congr_fun H x) y

end OctonionMatrices

section AutomorphismEquations

private abbrev AutomorphismVars := Bool × (ZornIndex × ZornIndex)
private abbrev AutomorphismRelation :=
  (Bool × (ZornIndex × ZornIndex)) ⊕ (ZornIndex ⊕ (ZornIndex × ZornIndex × ZornIndex))

variable {S : Type v} {T : Type w} [CommRing S] [CommRing T]

private def autoMatrix (x : AutomorphismVars → S) (b : Bool) : Matrix ZornIndex ZornIndex S :=
  Matrix.of fun i j => x (b, i, j)

private noncomputable def autoRelation (x : AutomorphismVars → S) : AutomorphismRelation → S
  | .inl (b, i, j) => (autoMatrix x b * autoMatrix x (!b)) i j - (1 : Matrix ZornIndex ZornIndex S) i j
  | .inr (.inl j) =>
    Zorn.pairedFunctions S (zornLinear (autoMatrix x true) 1) j - Zorn.pairedFunctions S 1 j
  | .inr (.inr (i, j, k)) =>
    let L := zornLinear (autoMatrix x true)
    Zorn.pairedFunctions S (L (zornBasis S i * zornBasis S j)) k -
      Zorn.pairedFunctions S (L (zornBasis S i) * L (zornBasis S j)) k

private lemma autoMatrix_map (f : S →+* T) (x : AutomorphismVars → S) (b : Bool) :
    f.mapMatrix (autoMatrix x b) = autoMatrix (f ∘ x) b := rfl

private lemma autoRelation_map (f : S →+* T) (x : AutomorphismVars → S) (k : AutomorphismRelation) :
    f (autoRelation x k) = autoRelation (f ∘ x) k := by
  rcases k with ⟨b, i, j⟩ | (j | ⟨i, j, k⟩)
  · simp only [autoRelation, map_sub]
    congr 1
    · exact congrArg (fun M : Matrix ZornIndex ZornIndex T => M i j)
        (f.mapMatrix.map_mul (autoMatrix x b) (autoMatrix x (!b)))
    · exact congrArg (fun M : Matrix ZornIndex ZornIndex T => M i j) (map_one f.mapMatrix)
  · simp only [autoRelation, map_sub, ← pairedFunctions_mapCoordinates, zornLinear_natural,
      autoMatrix_map, map_zorn_one]
  · simp only [autoRelation, map_sub, ← pairedFunctions_mapCoordinates, Zorn.mapCoordinates_mul,
      zornLinear_natural, autoMatrix_map, map_zornBasis]

private abbrev AutomorphismSolution (S : Type v) [CommRing S] :=
  {x : AutomorphismVars → S // ∀ k, autoRelation x k = 0}

private noncomputable def automorphismOfSolution (x : AutomorphismSolution S) :
    SplitAutomorphism S := by
  let L := zornLinear (autoMatrix x.val true)
  have inv (b : Bool) : autoMatrix x.val b * autoMatrix x.val (!b) = 1 := by
    ext i j
    exact sub_eq_zero.mp (x.property (.inl (b, i, j)))
  let E : Zorn S ≃ₗ[S] Zorn S :=
    LinearEquiv.ofLinearMap L (zornLinear (autoMatrix x.val false))
      ((zornLinear_mul _ _).symm.trans ((congrArg zornLinear (inv true)).trans zornLinear_one))
      ((zornLinear_mul _ _).symm.trans ((congrArg zornLinear (inv false)).trans zornLinear_one))
  refine ⟨E, ?_, ?_⟩
  · apply (Zorn.pairedFunctions S).injective
    funext j
    exact sub_eq_zero.mp (x.property (.inr (.inl j)))
  · refine multiplicative_on_basis (L := L) ?_
    intro i j
    apply (Zorn.pairedFunctions S).injective
    funext k
    exact sub_eq_zero.mp (x.property (.inr (.inr (i, j, k))))

private lemma automorphismOfSolution_linear (x : AutomorphismSolution S) :
    (automorphismOfSolution x).val.toLinearMap = zornLinear (autoMatrix x.val true) := rfl

private lemma automorphismOfSolution_inverse (x : AutomorphismSolution S) :
    (automorphismOfSolution x).val.symm.toLinearMap = zornLinear (autoMatrix x.val false) := rfl

private lemma automorphismOfSolution_bijective :
    Function.Bijective (automorphismOfSolution (S := S)) := by
  constructor
  · intro x y he
    have h₁ := congrArg (fun F : SplitAutomorphism S => F.val.toLinearMap) he
    have h₂ := congrArg (fun F : SplitAutomorphism S => F.val.symm.toLinearMap) he
    rw [automorphismOfSolution_linear, automorphismOfSolution_linear] at h₁
    rw [automorphismOfSolution_inverse, automorphismOfSolution_inverse] at h₂
    have eqM (b : Bool) : autoMatrix x.val b = autoMatrix y.val b := by
      cases b
      · simpa only [zornMatrix_zornLinear] using congrArg zornMatrix h₂
      · simpa only [zornMatrix_zornLinear] using congrArg zornMatrix h₁
    apply Subtype.ext
    funext ⟨b, i, j⟩
    exact congrArg (fun M : Matrix ZornIndex ZornIndex S => M i j) (eqM b)
  · intro F
    let x : AutomorphismVars → S := fun ⟨b, i, j⟩ =>
      (if b then zornMatrix F.val.toLinearMap else zornMatrix F.val.symm.toLinearMap) i j
    have h₁ : zornLinear (autoMatrix x true) = F.val.toLinearMap := zornLinear_zornMatrix _
    have h₂ : zornLinear (autoMatrix x false) = F.val.symm.toLinearMap := zornLinear_zornMatrix _
    have inv (b : Bool) : autoMatrix x b * autoMatrix x (!b) = 1 := by
      apply Function.LeftInverse.injective (f := zornLinear) (g := zornMatrix) zornMatrix_zornLinear
      rw [zornLinear_mul, zornLinear_one]
      cases b
      · change zornLinear (autoMatrix x false) ∘ₗ zornLinear (autoMatrix x true) = _
        rw [h₁, h₂]
        exact LinearMap.ext F.val.symm_apply_apply
      · change zornLinear (autoMatrix x true) ∘ₗ zornLinear (autoMatrix x false) = _
        rw [h₁, h₂]
        exact LinearMap.ext F.val.apply_symm_apply
    have hx (k : AutomorphismRelation) : autoRelation x k = 0 := by
      rcases k with ⟨b, i, j⟩ | (j | ⟨i, j, k⟩)
      · rw [autoRelation, inv, sub_self]
      · rw [autoRelation, h₁]
        exact sub_eq_zero.mpr (congrArg (fun z => Zorn.pairedFunctions S z j) F.property.1)
      · simp only [autoRelation, h₁, LinearEquiv.coe_coe, F.property.2, sub_self]
    refine ⟨⟨x, hx⟩, Subtype.ext (LinearEquiv.toLinearMap_injective ?_)⟩
    exact (automorphismOfSolution_linear ⟨x, hx⟩).trans h₁

variable (R : Type u) [CommRing R]

private noncomputable def autoEquation (R : Type u) [CommRing R] :
    AutomorphismRelation → MvPolynomial AutomorphismVars R :=
  autoRelation MvPolynomial.X

private abbrev AutomorphismRing :=
  EquationRing (autoEquation R)

variable {R} [Algebra R S] [Algebra R T]

private noncomputable def solutionOfHom (f : AutomorphismRing R →ₐ[R] S) :
    AutomorphismSolution S := by
  let p := equationsPoint (autoEquation R) f
  refine ⟨p.val, fun k => ?_⟩
  let g : MvPolynomial AutomorphismVars R →ₐ[R] S := MvPolynomial.aeval p.val
  have h := autoRelation_map (S := MvPolynomial AutomorphismVars R) (T := S) g.toRingHom MvPolynomial.X k
  have hx : g.toRingHom ∘ MvPolynomial.X = p.val :=
    funext (MvPolynomial.aeval_X p.val)
  rw [hx] at h
  exact h.symm.trans (p.property k)

private lemma solutionOfHom_bijective : Function.Bijective (solutionOfHom (R := R) (S := S)) := by
  constructor
  · intro f g h
    apply (equationsPoint_bijective (autoEquation R)).injective
    exact Subtype.ext (congrArg (fun x : AutomorphismSolution S => x.val) h)
  · intro x
    have hx (k : AutomorphismRelation) :
        MvPolynomial.aeval x.val (autoEquation R k) = 0 := by
      let g : MvPolynomial AutomorphismVars R →ₐ[R] S := MvPolynomial.aeval x.val
      have h := autoRelation_map (S := MvPolynomial AutomorphismVars R) (T := S) g.toRingHom MvPolynomial.X k
      have hX : g.toRingHom ∘ MvPolynomial.X = x.val :=
        funext (MvPolynomial.aeval_X x.val)
      rw [hX, x.property k] at h
      exact h
    obtain ⟨f, hf⟩ := (equationsPoint_bijective (autoEquation R)).surjective ⟨x.val, hx⟩
    exact ⟨f, Subtype.ext (congrArg (fun p :
      {a : AutomorphismVars → S // ∀ j, MvPolynomial.aeval a (autoEquation R j) = 0} => p.val) hf)⟩

private noncomputable def evaluateAutomorphism (f : AutomorphismRing R →ₐ[R] S) :
    SplitAutomorphism S :=
  automorphismOfSolution (solutionOfHom f)

private lemma evaluateAutomorphism_bijective :
    Function.Bijective (evaluateAutomorphism (R := R) (S := S)) :=
  automorphismOfSolution_bijective.comp solutionOfHom_bijective

set_option maxHeartbeats 800000 in
private lemma evaluateAutomorphism_natural (f : AutomorphismRing R →ₐ[R] S)
    (g : S →ₐ[R] T) (z : Zorn S) :
    (evaluateAutomorphism (g.comp f)).val (ZornSpecification.mapCoordinates g.toRingHom z) =
      ZornSpecification.mapCoordinates g.toRingHom ((evaluateAutomorphism f).val z) := by
  have h (b : Bool) : autoMatrix (solutionOfHom (g.comp f)).val b =
      g.toRingHom.mapMatrix (autoMatrix (solutionOfHom f).val b) := rfl
  change zornLinear (autoMatrix (solutionOfHom (g.comp f)).val true)
      (ZornSpecification.mapCoordinates g.toRingHom z) =
      ZornSpecification.mapCoordinates g.toRingHom (zornLinear (autoMatrix (solutionOfHom f).val true) z)
  rw [h]
  exact (zornLinear_natural g.toRingHom _ z).symm

private lemma map_zorn_first (φ : S →+* T) :
    ZornSpecification.mapCoordinates φ (Zorn.first S) = Zorn.first T := by
  apply (Zorn.coordinates T).injective
  change (φ 1, (fun _ : Fin 3 => φ 0), (fun _ : Fin 3 => φ 0), φ 0) =
    (1, (0 : Fin 3 → T), (0 : Fin 3 → T), 0)
  simp [Pi.zero_def]

set_option maxHeartbeats 900000 in
theorem split_evaluation_scheme : PeirceSpecification.splitEvaluationScheme.{u, v} := by
  intro R _
  let D := AutomorphismRing R
  let F := evaluateAutomorphism (AlgHom.id R D)
  obtain ⟨ρ, hρ⟩ := (splitPointFromHom_bijective (R := R) (S := D)).surjective
    (splitAutomorphismFrames D F).1
  have hr : (splitPointFromHom ρ).val = F.val (Zorn.first D) := congrArg Subtype.val hρ
  let E (S : Type v) [CommRing S] [Algebra R S] : (D →ₐ[R] S) ≃ SplitAutomorphism S :=
    Equiv.ofBijective (evaluateAutomorphism (R := R) (S := S)) evaluateAutomorphism_bijective
  refine ⟨D, inferInstance, inferInstance, ρ, ?_, splitUniversalPoint R, ?_, E, ?_, ?_⟩
  · exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  · intro S _ _
    have h := split_evaluation_bijective (R := R) (S := S)
    exact ⟨fun f g hfg => h.injective (Subtype.ext hfg),
      fun x => ⟨(h.surjective x).choose, congrArg Subtype.val (h.surjective x).choose_spec⟩⟩
  · intro S _ _ f
    change (evaluateAutomorphism f).val (Zorn.first S) =
      Zorn.baseChange R S (tensorMap (f.comp ρ) (splitUniversalPoint R).val)
    have h := evaluateAutomorphism_natural (AlgHom.id R D) f (Zorn.first D)
    rw [AlgHom.comp_id, map_zorn_first, ← show F = evaluateAutomorphism (AlgHom.id R D) from rfl,
      ← hr, ← split_eval ρ, ← zorn_baseChange_naturality, ← tensorMap_comp] at h
    exact h
  · intro S T _ _ _ _ f g x
    exact evaluateAutomorphism_natural f g x

end AutomorphismEquations

section SpecialLinearThree

open PeirceSpecification (sl3Equation SL3Ring)

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

private lemma sl3Equation_eval (x : Fin 3 × Fin 3 → S) :
    MvPolynomial.aeval x (sl3Equation R ()) =
      (Matrix.of fun i j : Fin 3 => x (i, j)).det - 1 := by
  let A : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3 × Fin 3) R) :=
    Matrix.of fun i j => MvPolynomial.X (i, j)
  let f : MvPolynomial (Fin 3 × Fin 3) R →ₐ[R] S := MvPolynomial.aeval x
  change f (A.det - 1) = _
  rw [map_sub, map_one, show f A.det = (A.map f).det from f.toRingHom.map_det A]
  have H : A.map f = Matrix.of (fun i j => x (i, j)) :=
    Matrix.ext fun i j => MvPolynomial.aeval_X x (i, j)
  rw [H]

private noncomputable def sl3Point (f : SL3Ring R →ₐ[R] S) :
    Matrix.SpecialLinearGroup (Fin 3) S :=
  ⟨Matrix.of fun i j => f (equationGenerator (sl3Equation R) (i, j)),
    sub_eq_zero.mp ((sl3Equation_eval (equationsPoint (sl3Equation R) f).val).symm.trans
      ((equationsPoint (sl3Equation R) f).property ()))⟩

private lemma sl3Point_bijective : Function.Bijective (sl3Point (R := R) (S := S)) := by
  constructor
  · intro f g hf
    apply (equationsPoint_bijective (sl3Equation R)).injective
    apply Subtype.ext
    funext p
    exact congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) S => M p.1 p.2) hf
  · intro M
    let x : Fin 3 × Fin 3 → S := fun p => M p.1 p.2
    obtain ⟨f, hf⟩ := (equationsPoint_bijective (sl3Equation R)).surjective ⟨x, by
      intro j
      cases j
      rw [sl3Equation_eval]
      exact sub_eq_zero.mpr M.property⟩
    refine ⟨f, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
    exact congrArg (fun a => a.val (i, j)) hf

private lemma sl3Point_natural {T : Type w} [CommRing T] [Algebra R T]
    (f : SL3Ring R →ₐ[R] S) (g : S →ₐ[R] T) :
    sl3Point (g.comp f) = Matrix.SpecialLinearGroup.map g.toRingHom (sl3Point f) :=
  Matrix.SpecialLinearGroup.ext _ _ fun _ _ => rfl

private lemma sl3_square_zero_lift (I : Ideal S) (hI : I ^ 2 = ⊥)
    (g : Matrix.SpecialLinearGroup (Fin 3) (S ⧸ I)) :
    ∃ G : Matrix.SpecialLinearGroup (Fin 3) S,
      Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk I) G = g := by
  classical
  choose a ha using fun i j => Ideal.Quotient.mk_surjective (I := I) (g i j)
  let A : Matrix (Fin 3) (Fin 3) S := Matrix.of a
  have ha' : A.map (Ideal.Quotient.mk I) = (g : Matrix (Fin 3) (Fin 3) (S ⧸ I)) :=
    Matrix.ext ha
  have hd : Ideal.Quotient.mk I A.det = 1 :=
    ((Ideal.Quotient.mk I).map_det A).trans (congrArg Matrix.det ha') |>.trans g.property
  have hh : (A.det - 1) ^ 2 = 0 := by
    have h : A.det - 1 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, hd, map_one, sub_self])
    have hm := Ideal.pow_mem_pow h 2
    rw [hI] at hm
    exact hm
  let D : Matrix (Fin 3) (Fin 3) S := Matrix.diagonal ![2 - A.det, 1, 1]
  let G : Matrix.SpecialLinearGroup (Fin 3) S := ⟨D * A, by
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    change (2 - A.det) * 1 * 1 * A.det = 1
    linear_combination -hh⟩
  use G
  apply Subtype.ext
  change (D * A).map (Ideal.Quotient.mk I) = _
  rw [Matrix.map_mul, ha']
  have hD : D.map (Ideal.Quotient.mk I) = 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [D, Matrix.diagonal, hd, map_ofNat]
  rw [hD, one_mul]

theorem special_linear_three_scheme : PeirceSpecification.specialLinearThreeScheme.{u, v} := by
  intro R _
  let E (S : Type v) [CommRing S] [Algebra R S] :=
    Equiv.ofBijective (sl3Point (R := R) (S := S)) sl3Point_bijective
  refine ⟨⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_,
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))⟩, E, ?_⟩
  · intro S _ _ I hI f
    obtain ⟨G, hG⟩ := sl3_square_zero_lift I hI (sl3Point f)
    obtain ⟨g, hg⟩ := (sl3Point_bijective (R := R)).surjective G
    exact ⟨g, sl3Point_bijective.injective
      ((sl3Point_natural g (Ideal.Quotient.mkₐ R I)).trans
        ((congrArg (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk I)) hg).trans hG))⟩
  · intro S T _ _ _ _ f g
    exact sl3Point_natural f g

end SpecialLinearThree

section ChartNaturality

private lemma split_automorphism_ext {S : Type u} [CommRing S] (F G : SplitAutomorphism S)
    (h : F.val (Zorn.first S) = G.val (Zorn.first S))
    (hu : ∀ i, F.val (upperColumn S i) = G.val (upperColumn S i)) :
    F = G :=
  Subtype.ext (congrArg PeirceSpecification.ZornIsomorphism.toLinearEquiv
    (zornIsomorphism_ext (normIsoOfAutomorphism S F) (normIsoOfAutomorphism S G) h hu))

private lemma map_upperColumn {S : Type u} {T : Type v} [CommRing S] [CommRing T]
    (f : S →+* T) (i : Fin 3) :
    ZornSpecification.mapCoordinates f (upperColumn S i) = upperColumn T i := by
  apply (Zorn.coordinates T).injective
  change (f 0, f ∘ (Pi.single i 1 : Fin 3 → S), (fun _ : Fin 3 => f 0), f 0) =
    (0, (Pi.single i 1 : Fin 3 → T), 0, 0)
  simp [Pi.zero_def]
  funext j
  by_cases h : j = i <;> simp [h]

private lemma map_zorn_comp {S T U : Type*} [CommRing S] [CommRing T] [CommRing U]
    (f : S →+* T) (g : T →+* U) (x : Zorn S) :
    ZornSpecification.mapCoordinates g (ZornSpecification.mapCoordinates f x) =
      ZornSpecification.mapCoordinates (g.comp f) x := by
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := (Zorn.coordinates S).symm.surjective x
  rfl

private def addZornMap {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) : Zorn S →+ Zorn T where
  toFun := ZornSpecification.mapCoordinates f
  map_zero' := by
    apply (Zorn.coordinates T).injective
    change (f 0, (fun _ : Fin 3 => f 0), (fun _ : Fin 3 => f 0), f 0) = (0, 0, 0, 0)
    simp [Pi.zero_def]
  map_add' := zorn_coordinateMap_add f

set_option maxHeartbeats 700000 in
theorem split_frame_chart_naturality : PeirceSpecification.splitFrameChartNaturality.{u, v} := by
  intro R A _ _ _ e b F hfirst hupper S T _ _ _ _ f h g x
  obtain ⟨D, _, _, ρ, _, d, hd, M, heval, hmap⟩ := split_evaluation_scheme.{u, v} R
  obtain ⟨a, ha⟩ := (M S).surjective (F S f g)
  have eq : M T (h.comp a) = F T (h.comp f) (Matrix.SpecialLinearGroup.map h.toRingHom g) := by
    apply split_automorphism_ext
    · have H := hmap S T a h (Zorn.first S)
      rw [map_zorn_first, ha, hfirst] at H
      rw [H, hfirst, tensorMap_comp]
      exact (zorn_baseChange_naturality h (tensorMap f e.val)).symm
    · intro i
      have H := hmap S T a h (upperColumn S i)
      rw [map_upperColumn, ha] at H
      rw [H]
      have HS : (F S f g).val (upperColumn S i) =
          ∑ j, g j i • ZornSpecification.mapCoordinates f.toRingHom (b j) := hupper S f g i
      have HT : (F T (h.comp f) (Matrix.SpecialLinearGroup.map h.toRingHom g)).val
          (upperColumn T i) =
          ∑ j, h (g j i) • ZornSpecification.mapCoordinates (h.comp f).toRingHom (b j) :=
        hupper T (h.comp f) (Matrix.SpecialLinearGroup.map h.toRingHom g) i
      rw [HS, HT]
      change addZornMap h.toRingHom (∑ j, g j i • ZornSpecification.mapCoordinates f.toRingHom (b j)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      change ZornSpecification.mapCoordinates h.toRingHom
        (g j i • ZornSpecification.mapCoordinates f.toRingHom (b j)) = _
      rw [zorn_coordinateMap_smul, map_zorn_comp]
      rfl
  exact eq ▸ ha ▸ hmap S T a h x

end ChartNaturality

section Stabilizer

private def composeZorn (F G : ZornIsomorphism (Zorn.norm R)) :
    ZornIsomorphism (Zorn.norm R) where
  toLinearEquiv := G.toLinearEquiv.trans F.toLinearEquiv
  map_one := by rw [LinearEquiv.trans_apply, G.map_one, F.map_one]
  map_mul x y := by simp only [LinearEquiv.trans_apply, G.map_mul, F.map_mul]
  map_norm x := by rw [LinearEquiv.trans_apply, F.map_norm, G.map_norm]

/-- The SL₃ chart at the standard frame consists of the automorphisms fixing the first
diagonal idempotent. -/
noncomputable def firstIdempotentStabilizer (R : Type u) [CommRing R] :
    Matrix.SpecialLinearGroup (Fin 3) R ≃
      {F : SplitAutomorphism R // F.val (Zorn.first R) = Zorn.first R} :=
  trivializeEvaluation (firstPoint R) ⟨firstBasis R, firstBasis_volume R⟩

/-- Changing a frame by a determinant-one matrix is right composition with its standard
stabilizer automorphism. -/
theorem frame_action_by_composition (e : QuadricPoint (Zorn.norm R)) (b : OrientedBasis e)
    (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (trivializeEvaluation e b g).val.val =
      (firstIdempotentStabilizer R g).val.val.trans (fiberFromBasis e b).val.val := by
  let F := normIsoOfAutomorphism R (fiberFromBasis e b).val
  let G := normIsoOfAutomorphism R (firstIdempotentStabilizer R g).val
  let H := normIsoOfAutomorphism R (trivializeEvaluation e b g).val
  suffices h : H = composeZorn F G from congrArg ZornIsomorphism.toLinearEquiv h
  apply zornIsomorphism_ext
  · change (trivializeEvaluation e b g).val.val (Zorn.first R) =
      (fiberFromBasis e b).val.val ((firstIdempotentStabilizer R g).val.val (Zorn.first R))
    rw [(trivializeEvaluation e b g).property, (firstIdempotentStabilizer R g).property,
      (fiberFromBasis e b).property]
  · intro i
    let b₀ : OrientedBasis (firstPoint R) := ⟨firstBasis R, firstBasis_volume R⟩
    change (trivializeEvaluation e b g).val.val (upperColumn R i) =
      (fiberFromBasis e b).val.val ((trivializeEvaluation (firstPoint R) b₀ g).val.val (upperColumn R i))
    rw [trivializeEvaluation_apply e b g i, trivializeEvaluation_apply (firstPoint R) b₀ g i, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, show (b₀.val j).val = upperColumn R j from firstBasis_apply R j, fiberFromBasis_upper]

theorem firstIdempotentStabilizer_mul (g h : Matrix.SpecialLinearGroup (Fin 3) R) :
    (firstIdempotentStabilizer R (g * h)).val.val =
      (firstIdempotentStabilizer R h).val.val.trans (firstIdempotentStabilizer R g).val.val := by
  let b : OrientedBasis (firstPoint R) := ⟨firstBasis R, firstBasis_volume R⟩
  have H := frame_action_by_composition (firstPoint R) (frameSMul (Zorn.isOctonion R) (firstPoint R) b g) h
  change (fiberFromBasis (firstPoint R)
    (frameSMul (Zorn.isOctonion R) (firstPoint R) (frameSMul (Zorn.isOctonion R) (firstPoint R) b g) h)).val.val =
    (firstIdempotentStabilizer R h).val.val.trans (firstIdempotentStabilizer R g).val.val at H
  rw [frameSMul_mul] at H
  exact H

theorem split_stabilizer : PeirceSpecification.splitStabilizer := by
  intro R _
  exact ⟨firstIdempotentStabilizer R, firstIdempotentStabilizer_mul⟩

end Stabilizer

end LinearAlgebraicGroups.Composition.Peirce
