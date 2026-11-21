import MathGenome.Internal.Specs.D05.M09.RealComplexBridge
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M03.LinearMap
import Mathlib.LinearAlgebra.Basis.Basic

/-! Complexification on W × W, with its specified scalar action, map extension,
and the basis obtained by embedding a real basis. -/
namespace D05.M09.RealComplexBridge

open Specs.D05.M09.RealComplexBridge
open Specs.D05.M09.RealComplexBridge.Complexification
open scoped BigOperators

universe u v w

abbrev complexification (W : Type u) := Complexification W

variable {W : Type u} {U : Type v}

@[ext] theorem ext {z t : Complexification W} (hr : re z = re t) (hi : im z = im t) :
    z = t := Prod.ext hr hi

@[simp] theorem re_pair (x y : W) : re (pair x y) = x := rfl
@[simp] theorem im_pair (x y : W) : im (pair x y) = y := rfl
variable [AddCommGroup W]

@[simp] theorem re_zero : re (0 : Complexification W) = 0 := rfl
@[simp] theorem im_zero : im (0 : Complexification W) = 0 := rfl
@[simp] theorem re_add (z t : Complexification W) : re (z + t) = re z + re t := rfl
@[simp] theorem im_add (z t : Complexification W) : im (z + t) = im z + im t := rfl
variable [Module ℝ W] [AddCommGroup U] [Module ℝ U]

@[simp] theorem re_smul (a : ℂ) (z : Complexification W) :
    re (a • z) = a.re • re z - a.im • im z := rfl
@[simp] theorem im_smul (a : ℂ) (z : Complexification W) :
    im (a • z) = a.im • re z + a.re • im z := rfl

@[simp] theorem re_real_smul (a : ℝ) (z : Complexification W) :
    re (a • z) = a • re z := by
  change a • re z - (0 : ℝ) • im z = a • re z
  simp

@[simp] theorem im_real_smul (a : ℝ) (z : Complexification W) :
    im (a • z) = a • im z := by
  change (0 : ℝ) • re z + a • im z = a • im z
  simp

theorem coordinate_operations : Specs.D05.M09.RealComplexBridge.coordinate_operations := by
  intro W _ _ x y u v z
  constructor
  · apply ext <;> simp
  · rfl

theorem complex_vector_space : Specs.D05.M09.RealComplexBridge.complex_vector_space := by
  intro W _ _ a b x y
  exact ⟨smul_add a x y, add_smul a b x, mul_smul a b x, one_smul ℂ x⟩

/-- The original real vectors occupy the first copy. -/
def includeReal : W →ₗ[ℝ] Complexification W where
  toFun x := pair x 0
  map_add' x y := by apply ext <;> simp
  map_smul' a x := by
    change pair (a • x) 0 = (a : ℂ) • pair x 0
    apply ext <;> simp

theorem real_embedding : Specs.D05.M09.RealComplexBridge.real_embedding := by
  intro W _ _
  refine ⟨includeReal, fun _ => rfl, ?_⟩
  intro x y h
  exact congrArg re h

theorem real_imag_decomposition : Specs.D05.M09.RealComplexBridge.real_imag_decomposition := by
  intro W _ _ x y
  apply ext <;> simp

/-- A real-linear map acts on both copies; its complex linearity is verified here. -/
def complexifyMap (L : W →ₗ[ℝ] U) : Complexification W →ₗ[ℂ] Complexification U where
  toFun z := pair (L (re z)) (L (im z))
  map_add' z t := by apply ext <;> simp
  map_smul' a z := by
    apply ext <;> simp

@[simp] theorem complexifyMap_pair (L : W →ₗ[ℝ] U) (x y : W) :
    complexifyMap L (pair x y) = pair (L x) (L y) := rfl

theorem extension_formula : Specs.D05.M09.RealComplexBridge.extension_formula := by
  intro W U _ _ _ _ L
  exact ⟨complexifyMap L, fun _ _ => rfl⟩

theorem unique_complex_extension : Specs.D05.M09.RealComplexBridge.unique_complex_extension := by
  intro W U _ _ _ _ L
  refine ⟨complexifyMap L, ?_, ?_⟩
  · intro x
    simp
  · intro F hF
    apply LinearMap.ext
    intro z
    obtain ⟨x, y⟩ := z
    change F (pair x y) = pair (L x) (L y)
    rw [real_imag_decomposition x y, map_add, map_smul, hF x, hF y]
    exact (real_imag_decomposition (L x) (L y)).symm

/-- Additive coordinate maps commute with arbitrary finite sums. -/
def realPart : Complexification W →+ W where
  toFun := re
  map_zero' := rfl
  map_add' _ _ := rfl

def imagPart : Complexification W →+ W where
  toFun := im
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Module ℝ W] in
@[simp] theorem re_sum {I : Type*} (s : Finset I) (f : I → Complexification W) :
    re (∑ i ∈ s, f i) = ∑ i ∈ s, re (f i) := map_sum realPart f s

omit [Module ℝ W] in
@[simp] theorem im_sum {I : Type*} (s : Finset I) (f : I → Complexification W) :
    im (∑ i ∈ s, f i) = ∑ i ∈ s, im (f i) := map_sum imagPart f s

/-- Separate the two coordinates of a finite complex relation. -/
theorem lifted_independent {I : Type w} (b : Module.Basis I ℝ W) :
    LinearIndependent ℂ (fun i => pair (b i) 0) := by
  rw [linearIndependent_iff']
  intro s a ha i hi
  have hr : ∑ j ∈ s, (a j).re • b j = 0 := by
    simpa using congrArg re ha
  have hm : ∑ j ∈ s, (a j).im • b j = 0 := by
    simpa using congrArg im ha
  apply Complex.ext
  · exact (linearIndependent_iff'.mp b.linearIndependent) s (fun j => (a j).re) hr i hi
  · exact (linearIndependent_iff'.mp b.linearIndependent) s (fun j => (a j).im) hm i hi

/-- Embed a real spanning expansion, then multiply the imaginary expansion by i. -/
theorem lifted_span {I : Type w} (b : Module.Basis I ℝ W) :
    Submodule.span ℂ (Set.range (fun i => pair (b i) 0)) = ⊤ := by
  let p := Submodule.span ℂ (Set.range (fun i => pair (b i) 0))
  have hx : ∀ x : W, pair x 0 ∈ p := by
    intro x
    have hb : x ∈ Submodule.span ℝ (Set.range b) := by rw [b.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact p.zero_mem
    | add x y _ _ hx hy =>
      convert p.add_mem hx hy using 1; apply ext <;> simp
    | smul a x _ hx =>
      convert p.smul_mem (a : ℂ) hx using 1; apply ext <;> simp
  apply top_unique
  intro z _
  obtain ⟨x, y⟩ := z
  change pair x y ∈ p
  rw [real_imag_decomposition]
  exact p.add_mem (hx x) (p.smul_mem Complex.I (hx y))

theorem basis_independent_span : Specs.D05.M09.RealComplexBridge.basis_independent_span := by
  intro W I _ _ b
  exact ⟨lifted_independent b, lifted_span b⟩

theorem basis_extension : Specs.D05.M09.RealComplexBridge.basis_extension := by
  intro W I _ _ b
  exact (D05.M02.Basis.basis_iff_independent_span (fun i => pair (b i) 0)).mpr
    ⟨lifted_independent b, lifted_span b⟩

end D05.M09.RealComplexBridge
