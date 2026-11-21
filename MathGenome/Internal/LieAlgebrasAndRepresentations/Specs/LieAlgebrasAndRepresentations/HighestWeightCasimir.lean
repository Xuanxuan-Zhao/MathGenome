import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ModuleCasimir
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt

/-! LA-H02-Casimir, Chapter 8, especially source lines 3572–3577 and
3605–3623. The form is arbitrary, rather than fixed to the Killing form.
The square of a complex weight means the diagonal of the complex bilinear
extension of the real form. All root sums are over the entire positive system. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir

open Module
open RootDecomposition VermaModules
open SolvableRadical (IsSemisimple_value)
open _root_.LieAlgebrasAndRepresentations.ModuleCasimir (action)
open UniversalEnvelopingAlgebra (ι)
open scoped BigOperators Classical

universe u v i j

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

abbrev Form := LinearMap.BilinForm ℂ L
abbrev PositiveRoot (H : LieSubalgebra ℂ L) (φ : Direction H) :=
  SerreRelations.positive H φ

def casimir_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (B : Form (L := L)), B.Nondegenerate →
    ∀ {I : Type i} [Fintype I], Basis I ℂ L → U L

def casimir_value (B : Form (L := L)) (hB : B.Nondegenerate)
    {I : Type i} [Fintype I] (b : Basis I ℂ L) : U L :=
  ∑ k, ι ℂ (b k) * ι ℂ (B.dualBasis hB b k)

def weightRepresentative_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    (H : LieSubalgebra ℂ L) → Form (L := L) → Module.Dual ℂ H →ₗ[ℂ] H

/-- Inverse of the restricted form when nondegenerate. The pairing theorem
establishes nondegeneracy for every form in the source hypotheses. -/
def weightRepresentative_value [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L)
    (B : Form (L := L)) : Module.Dual ℂ H →ₗ[ℂ] H := by
  classical
  let C := B.restrict H.toSubmodule
  exact if hC : C.Nondegenerate then (C.toDual hC).symm.toLinearMap else 0

def weightForm_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    (H : LieSubalgebra ℂ L) → Form (L := L) → LinearMap.BilinForm ℂ (Module.Dual ℂ H)

def weightForm_value [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L)
    (B : Form (L := L)) : LinearMap.BilinForm ℂ (Module.Dual ℂ H) := (B.restrict H.toSubmodule).compl₁₂
    (weightRepresentative_value H B) (weightRepresentative_value H B)

def rho_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L), Direction H → Module.Dual ℂ H

def rho_value (H : LieSubalgebra ℂ L) (φ : Direction H) : Module.Dual ℂ H := (1 / 2 : ℂ) • ∑ᶠ α : PositiveRoot H φ, α.val

def eigenvalue_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L), Direction H → Form (L := L) → Module.Dual ℂ H → ℂ

def eigenvalue_value [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L)
    (φ : Direction H) (B : Form (L := L)) (lam : Module.Dual ℂ H) : ℂ := weightForm_value H B lam (lam + (2 : ℂ) • rho_value H φ)

/-- The real-root-space convention of Chapter 8. The algebraic identities
hold for every nondegenerate invariant form, and the norm identity below
identifies their squares with the real norm for positive forms. -/
def PositiveOnRealRoots [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L)
    (B : Form (L := L)) : Prop :=
  ∀ lam ∈ Submodule.span ℝ (rootSet_value H), lam ≠ 0 →
    0 < (weightForm_value H B lam lam).re ∧ (weightForm_value H B lam lam).im = 0

def Normalized (H : LieSubalgebra ℂ L) (φ : Direction H) (B : Form (L := L))
    (x y : PositiveRoot H φ → L) : Prop :=
  ∀ α, x α ∈ rootSpace_value H α.val ∧ y α ∈ rootSpace_value H (-α.val) ∧ B (x α) (y α) = 1

def symmetry_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ B : Form (L := L), B.lieInvariant L → B.IsSymm

def representative_pairing_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra], IsSemisimple_value ℂ L →
    ∀ B : Form (L := L), B.lieInvariant L → B.Nondegenerate →
    (B.restrict H.toSubmodule).Nondegenerate ∧
    ∀ (α : Module.Dual ℂ H) (h : H), B (weightRepresentative_value H B α : L) (h : L) = α h

def basis_independent_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (B : Form (L := L)) (hB : B.Nondegenerate)
    {I : Type i} {J : Type j} [Fintype I] [Fintype J] (b : Basis I ℂ L) (c : Basis J ℂ L),
    casimir_value B hB b = casimir_value B hB c

def central_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (B : Form (L := L)) (hB : B.Nondegenerate), B.lieInvariant L →
    ∀ {I : Type i} [Fintype I] (b : Basis I ℂ L),
      casimir_value B hB b ∈ Subalgebra.center ℂ (U L)

def normalized_exists_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra], IsSemisimple_value ℂ L →
    ∀ (φ : Direction H) (B : Form (L := L)), B.lieInvariant L → B.Nondegenerate →
      ∃ x y, Normalized H φ B x y

def normal_order_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra], IsSemisimple_value ℂ L →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (B : Form (L := L)) (hB : B.Nondegenerate), B.lieInvariant L →
    ∀ (hC : (B.restrict H.toSubmodule).Nondegenerate)
      {I : Type i} [Fintype I] (b : Basis I ℂ L) {J : Type j} [Fintype J] (h : Basis J ℂ H)
      (x y : PositiveRoot H φ → L), Normalized H φ B x y →
      casimir_value B hB b =
        (∑ a, ι ℂ (h a : L) * ι ℂ (((B.restrict H.toSubmodule).dualBasis hC h a : H) : L)) +
        (2 : ℂ) • ι ℂ (weightRepresentative_value H B (rho_value H φ) : L) +
        (2 : ℂ) • ∑ᶠ α : PositiveRoot H φ, ι ℂ (y α) * ι ℂ (x α)

/-- The highest vector generates the entire Lie module, which can have infinite dimension. -/
def eigenvalue_action_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra], IsSemisimple_value ℂ L →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (B : Form (L := L)) (hB : B.Nondegenerate), B.lieInvariant L →
    ∀ {I : Type i} [Fintype I] (b : Basis I ℂ L)
      (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
      (lam : Module.Dual ℂ H) (w : V),
      (∀ h : H, ⁅(h : L), w⁆ = lam h • w) →
      (∀ x ∈ positive_value H φ, ⁅x, w⁆ = 0) →
      LieSubmodule.lieSpan ℂ L ({w} : Set V) = ⊤ →
      ∀ m : V, action ℂ L V (casimir_value B hB b) m = eigenvalue_value H φ B lam • m

def eigenvalue_difference_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L), IsSemisimple_value ℂ L →
    ∀ (φ : Direction H) (B : Form (L := L)), B.lieInvariant L →
    ∀ lam : Module.Dual ℂ H,
      eigenvalue_value H φ B lam = weightForm_value H B (lam + rho_value H φ) (lam + rho_value H φ) -
        weightForm_value H B (rho_value H φ) (rho_value H φ)

/-- On the real span of the roots the diagonal is the square of the norm
induced by the positive form. The identity in the complex dual is
`eigenvalue_difference_type`. -/
def real_norm_difference_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra], IsSemisimple_value ℂ L →
    ∀ (φ : Direction H) (B : Form (L := L)), B.lieInvariant L → B.Nondegenerate →
    PositiveOnRealRoots H B → ∀ lam ∈ Submodule.span ℝ (rootSet_value H),
    let norm := fun μ : Module.Dual ℂ H => Real.sqrt (weightForm_value H B μ μ).re
    eigenvalue_value H φ B lam = ((norm (lam + rho_value H φ) ^ 2 -
      norm (rho_value H φ) ^ 2 : ℝ) : ℂ)

end Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
