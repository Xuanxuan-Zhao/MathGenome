import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.LinearAlgebra.Complex.Module
import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M03.LinearMap
import Mathlib.Tactic.Abel

/-!
Canonical pair model and independent statements for the complexification
paragraph of K05.09.real_complex_bridge, paper.tex:1358–1367.
The real space W is arbitrary; basis index types may be infinite or empty.
The structures below are constructed from the displayed coordinate formulas,
with their module laws proved, rather than postulated as certificates.
-/
namespace Specs.D05.M09.RealComplexBridge

universe u v w

/-- A fresh type for W ⊕ W, to distinguish its complex action from a product action. -/
def Complexification (W : Type u) := W × W

namespace Complexification

instance {W : Type u} [AddCommGroup W] : AddCommGroup (Complexification W) :=
  inferInstanceAs (AddCommGroup (W × W))

/-- Coordinates in the pair model. -/
def pair {W : Type u} (x y : W) : Complexification W := (x, y)
def re {W : Type u} (z : Complexification W) : W := z.1
def im {W : Type u} (z : Complexification W) : W := z.2

instance {W : Type u} [AddCommGroup W] [Module ℝ W] : SMul ℂ (Complexification W) :=
  ⟨fun a z => pair (a.re • re z - a.im • im z) (a.im • re z + a.re • im z)⟩

instance complexModule {W : Type u} [AddCommGroup W] [Module ℝ W] :
    Module ℂ (Complexification W) :=
  Module.ofMinimalAxioms
    (by
      intro a x y
      apply Prod.ext
      · change a.re • (x.1 + y.1) - a.im • (x.2 + y.2) =
          (a.re • x.1 - a.im • x.2) + (a.re • y.1 - a.im • y.2)
        simp only [smul_add]; abel
      · change a.im • (x.1 + y.1) + a.re • (x.2 + y.2) =
          (a.im • x.1 + a.re • x.2) + (a.im • y.1 + a.re • y.2)
        simp only [smul_add]; abel)
    (by
      intro a b x
      apply Prod.ext
      · change (a + b).re • x.1 - (a + b).im • x.2 =
          (a.re • x.1 - a.im • x.2) + (b.re • x.1 - b.im • x.2)
        simp only [Complex.add_re, Complex.add_im, add_smul]; abel
      · change (a + b).im • x.1 + (a + b).re • x.2 =
          (a.im • x.1 + a.re • x.2) + (b.im • x.1 + b.re • x.2)
        simp only [Complex.add_re, Complex.add_im, add_smul]; abel)
    (by
      intro a b x
      apply Prod.ext
      · change (a * b).re • x.1 - (a * b).im • x.2 =
          a.re • (b.re • x.1 - b.im • x.2) - a.im • (b.im • x.1 + b.re • x.2)
        simp only [Complex.mul_re, Complex.mul_im, sub_smul, add_smul,
          smul_sub, smul_add, mul_smul]; abel
      · change (a * b).im • x.1 + (a * b).re • x.2 =
          a.im • (b.re • x.1 - b.im • x.2) + a.re • (b.im • x.1 + b.re • x.2)
        simp only [Complex.mul_re, Complex.mul_im, sub_smul, add_smul,
          smul_sub, smul_add, mul_smul]; abel)
    (by
      intro x
      apply Prod.ext
      · change (1 : ℝ) • x.1 - (0 : ℝ) • x.2 = x.1
        simp
      · change (0 : ℝ) • x.1 + (1 : ℝ) • x.2 = x.2
        simp)

end Complexification

/-- Required value of the type construction: the underlying vectors are pairs. -/
def complexification_type : Type (u + 1) := Type u → Type u
def complexification_value : complexification_type.{u} := Complexification

open Complexification

/-- Addition and the complex scalar action are exactly the paper's formulas. -/
def coordinate_operations : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (x y u v : W) (z : ℂ),
    pair x y + pair u v = pair (x + u) (y + v) ∧
    z • pair x y = pair (z.re • x - z.im • y) (z.im • x + z.re • y)

/-- All four vector-space identities for the displayed scalar action. -/
def complex_vector_space : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W]
    (a b : ℂ) (x y : Complexification W),
    a • (x + y) = a • x + a • y ∧
    (a + b) • x = a • x + b • x ∧
    (a * b) • x = a • (b • x) ∧ (1 : ℂ) • x = x

/-- The original real space embeds as x + i0, real linearly and injectively. -/
def real_embedding : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W],
    ∃ e : W →ₗ[ℝ] Complexification W,
      (∀ x, e x = pair x 0) ∧ Function.Injective e

/-- Every pair decomposes in the way used to force uniqueness of an extension. -/
def real_imag_decomposition : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module ℝ W] (x y : W),
    pair x y = pair x 0 + Complex.I • pair y 0

/-- The componentwise function is complex linear (existence and its exact formula). -/
def extension_formula : Prop :=
  ∀ {W : Type u} {U : Type v} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup U] [Module ℝ U] (L : W →ₗ[ℝ] U),
    ∃ F : Complexification W →ₗ[ℂ] Complexification U,
      ∀ x y, F (pair x y) = pair (L x) (L y)

/-- Uniqueness assumes agreement only on the embedded original real space. -/
def unique_complex_extension : Prop :=
  ∀ {W : Type u} {U : Type v} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup U] [Module ℝ U] (L : W →ₗ[ℝ] U),
    ∃! F : Complexification W →ₗ[ℂ] Complexification U,
      ∀ x, F (pair x 0) = pair (L x) 0

/-- A real basis, embedded as w_j + i0, is a complex basis of the pair model. -/
def basis_extension : Prop :=
  ∀ {W : Type u} {I : Type w} [AddCommGroup W] [Module ℝ W]
    (b : Module.Basis I ℝ W),
    ∃ B : Module.Basis I ℂ (Complexification W), ∀ i, B i = pair (b i) 0

/-- Explicit independence and spanning for the same embedded family. -/
def basis_independent_span : Prop :=
  ∀ {W : Type u} {I : Type w} [AddCommGroup W] [Module ℝ W]
    (b : Module.Basis I ℝ W),
    LinearIndependent ℂ (fun i => pair (b i) 0) ∧
      Submodule.span ℂ (Set.range (fun i => pair (b i) 0)) = ⊤

end Specs.D05.M09.RealComplexBridge
