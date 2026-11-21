import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootForm
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootSystems
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Complex.Module

/-! LA-D05, source res:D05 and the global coroot convention.
The real Cartan is the real span of the actual Killing-normalized Lie coroots. -/

open scoped TensorProduct

universe u

namespace Specs.LieAlgebrasAndRepresentations.RealRootSpace

open RootDecomposition RootForm

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L)

noncomputable abbrev killing : LinearMap.BilinForm ℂ H :=
  (TraceCriterion.killingForm_value ℂ L).restrict H.toSubmodule

noncomputable def realCartan : Submodule ℝ H :=
  Submodule.span ℝ (coroot_value H '' rootSet_value H)

abbrev E := Module.Dual ℝ (realCartan H)

noncomputable def realKilling : LinearMap.BilinForm ℝ (realCartan H) where
  toFun x := Complex.reLm.comp (((killing H x).restrictScalars ℝ).comp (realCartan H).subtype)
  map_add' x y := by
    ext z
    change (killing H ((x : H) + (y : H)) z).re = _
    rw [map_add, LinearMap.add_apply, Complex.add_re]
    rfl
  map_smul' r x := by
    ext z
    change (killing H ((r : ℂ) • (x : H)) z).re = r * (killing H x z).re
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

noncomputable def rootRestriction (α : Module.Dual ℂ H) : E H :=
  Complex.reLm.comp ((α.restrictScalars ℝ).comp (realCartan H).subtype)

noncomputable def realRoots : Set (E H) :=
  rootRestriction H '' rootSet_value H

noncomputable def cartanSum : realCartan H × realCartan H →ₗ[ℝ] H :=
  (realCartan H).subtype.coprod
    (((Complex.I • (LinearMap.id : H →ₗ[ℂ] H)).restrictScalars ℝ).comp
      (realCartan H).subtype)

noncomputable def rationalSpan : Submodule ℚ (E H) :=
  Submodule.span ℚ (realRoots H)

section ScalarExtension

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- The canonical scalar extension of a linear map into an S-module. -/
noncomputable def extendScalars (f : M →ₗ[R] N) : S ⊗[R] M →ₗ[S] N :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : S →ₗ[S] S).smulRight f)

@[simp] theorem extendScalars_tmul (f : M →ₗ[R] N) (s : S) (m : M) :
    extendScalars f (s ⊗ₜ m) = s • f m := rfl

end ScalarExtension

def Positive : Prop := ∀ x : realCartan H, x ≠ 0 → 0 < realKilling H x x

theorem realKilling_symm (x y : realCartan H) :
    realKilling H x y = realKilling H y x :=
  congrArg Complex.re (LieModule.traceForm_comm ℂ L L (x : H) (y : H))

theorem realKilling_nondegenerate (hp : Positive H) : (realKilling H).Nondegenerate := by
  have h (x : realCartan H) (hx : ∀ y, realKilling H x y = 0) : x = 0 := by
    by_contra hn
    exact (ne_of_gt (hp x hn)) (hx x)
  exact ⟨h, fun x hx => h x fun y => (realKilling_symm H x y).trans (hx y)⟩

noncomputable def riesz (hp : Positive H) : E H ≃ₗ[ℝ] realCartan H :=
  ((realKilling H).toDual (realKilling_nondegenerate H hp)).symm

/-- The extension is complex-linear in its argument in the Cartan, and
real-linear in the real functional being extended. -/
noncomputable def extension (hp : Positive H) : E H →ₗ[ℝ] Module.Dual ℂ H :=
  ((killing H).restrictScalars ℝ).comp ((realCartan H).subtype.comp (riesz H hp).toLinearMap)

@[instance_reducible] noncomputable def dualCore (hp : Positive H) : InnerProductSpace.Core ℝ (E H) where
  inner x y := realKilling H (riesz H hp x) (riesz H hp y)
  conj_inner_symm x y := realKilling_symm H _ _
  re_inner_nonneg x := by
    change 0 ≤ realKilling H (riesz H hp x) (riesz H hp x)
    by_cases h : riesz H hp x = 0
    · rw [h]; simp
    · exact (hp _ h).le
  definite x hx := by
    apply (riesz H hp).injective
    rw [map_zero]
    by_contra hn
    exact (ne_of_gt (hp _ hn)) hx
  add_left x y z := by simp only [map_add, LinearMap.add_apply]
  smul_left x y r := by
    simp only [map_smul, LinearMap.smul_apply, RCLike.conj_to_real, smul_eq_mul]

noncomputable def dualComplexification (hp : Positive H) :
    ℂ ⊗[ℝ] E H →ₗ[ℂ] Module.Dual ℂ H :=
  extendScalars (extension H hp)

noncomputable def rationalExtension : ℝ ⊗[ℚ] rationalSpan H →ₗ[ℝ] E H :=
  extendScalars (R := ℚ) (S := ℝ) (M := rationalSpan H) (N := E H) (rationalSpan H).subtype

/-- All assertions use the same real Cartan and Killing-induced Euclidean dual. -/
structure Realization : Prop where
  roots_span : Submodule.span ℂ (rootSet_value H) = ⊤
  cartan_sum : Function.Bijective (cartanSum H)
  killing_restrict_real : ∀ x y : realCartan H, killing H x y = (realKilling H x y : ℂ)
  killing_positive : Positive H
  roots_restrict_real : ∀ α ∈ rootSet_value H, ∀ x : realCartan H,
    α x = (rootRestriction H α x : ℂ)
  riesz_pairing : ∀ x : E H, ∀ u : realCartan H,
    killing H (riesz H killing_positive x) u = (x u : ℂ)
  extension_formula : ∀ x : E H, ∀ u v : realCartan H,
    extension H killing_positive x ((u : H) + Complex.I • (v : H)) =
      (x u : ℂ) + Complex.I * (x v : ℂ)
  extension_root : ∀ α ∈ rootSet_value H,
    extension H killing_positive (rootRestriction H α) = α
  dual_complexification : Function.Bijective (dualComplexification H killing_positive)
  root_system :
    letI := (dualCore H killing_positive).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (dualCore H killing_positive).toCore
    LieAlgebrasAndRepresentations.IsRootSystem (realRoots H)
  root_form_agrees : ∀ α ∈ rootSet_value H, ∀ β ∈ rootSet_value H,
    ((dualCore H killing_positive).inner (rootRestriction H α) (rootRestriction H β) : ℂ) =
      rootForm_value H α β
  riesz_coroot : ∀ α ∈ rootSet_value H,
    letI := (dualCore H killing_positive).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (dualCore H killing_positive).toCore
    (riesz H killing_positive (LieAlgebrasAndRepresentations.coroot (rootRestriction H α)) : H) =
      coroot_value H α
  coroot_evaluation : ∀ x : E H, ∀ α ∈ rootSet_value H,
    letI := (dualCore H killing_positive).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (dualCore H killing_positive).toCore
    extension H killing_positive x (coroot_value H α) =
      (inner ℝ x (LieAlgebrasAndRepresentations.coroot (rootRestriction H α)) : ℂ)
  root_form_rational : ∀ α ∈ rootSet_value H, ∀ β ∈ rootSet_value H,
    ∃ r : ℚ, (dualCore H killing_positive).inner (rootRestriction H α) (rootRestriction H β) =
      (r : ℝ)
  rational_extension : Function.Bijective (rationalExtension H)

namespace Realization

variable {H} (d : Realization H)

/-- The direct-sum isomorphism `(u,v) ↦ u + i • v` of real vector spaces. -/
noncomputable def cartanDecomposition : (realCartan H × realCartan H) ≃ₗ[ℝ] H :=
  LinearEquiv.ofBijective (cartanSum H) d.cartan_sum

/-- The natural extension of real functionals to the complex Cartan. -/
noncomputable abbrev j : E H →ₗ[ℝ] Module.Dual ℂ H :=
  extension H d.killing_positive

/-- The Riesz isomorphism for the real restriction of the Killing form. -/
noncomputable abbrev q : E H ≃ₗ[ℝ] realCartan H :=
  riesz H d.killing_positive

noncomputable def complexification : ℂ ⊗[ℝ] E H ≃ₗ[ℂ] Module.Dual ℂ H :=
  LinearEquiv.ofBijective (dualComplexification H d.killing_positive) d.dual_complexification

@[simp] theorem complexification_tmul (c : ℂ) (x : E H) :
    d.complexification (c ⊗ₜ x) = c • d.j x := rfl

noncomputable def rationalEquiv : ℝ ⊗[ℚ] rationalSpan H ≃ₗ[ℝ] E H :=
  LinearEquiv.ofBijective (rationalExtension H) d.rational_extension

@[simp] theorem rationalEquiv_tmul (r : ℝ) (v : rationalSpan H) :
    d.rationalEquiv (r ⊗ₜ v) = r • (v : E H) := rfl

include d in
theorem rational_finrank :
    Module.finrank ℚ (rationalSpan H) = Module.finrank ℝ (E H) := by
  let : Module.Free ℚ (rationalSpan H) := Module.Free.of_divisionRing ℚ (rationalSpan H)
  calc
    _ = Module.finrank ℝ (ℝ ⊗[ℚ] rationalSpan H) :=
      (Module.finrank_baseChange (R := ℝ) (S := ℚ) (M' := rationalSpan H)).symm
    _ = _ := (rationalEquiv d).finrank_eq

@[instance_reducible]
noncomputable def normedAddCommGroup : NormedAddCommGroup (E H) :=
  (dualCore H d.killing_positive).toNormedAddCommGroup

@[instance_reducible]
noncomputable def innerProductSpace :
    letI := d.normedAddCommGroup
    InnerProductSpace ℝ (E H) :=
  InnerProductSpace.ofCore (dualCore H d.killing_positive).toCore

noncomputable def rootSystem :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    LieAlgebrasAndRepresentations.RootSystem (E H) :=
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  ⟨realRoots H, d.root_system⟩

end Realization

def realizationType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra], Realization H

def realizationOfMaximalToralType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H → Realization H

def zeroRankType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] [Subsingleton L],
    ∀ H : LieSubalgebra ℂ L,
      rootSet_value H = ∅ ∧ realRoots H = ∅ ∧ Subsingleton (E H)

end Specs.LieAlgebrasAndRepresentations.RealRootSpace
