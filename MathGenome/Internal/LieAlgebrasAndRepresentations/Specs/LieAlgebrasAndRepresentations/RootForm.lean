import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootDecomposition
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! LA-U07: source lines 1648–1655, with the standing hypotheses at
1546–1553. The inverse below is totalized by zero away from nondegeneracy;
all characterizing assertions use the original semisimple/maximal-toral
hypotheses. The form is exactly the Killing-induced complex bilinear form,
without a rescaling or complex conjugation. -/

universe u
namespace Specs.LieAlgebrasAndRepresentations.RootForm

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

noncomputable def rootDualMap_value (H : LieSubalgebra ℂ L) :
    Module.Dual ℂ H →ₗ[ℂ] H := by
  classical
  let B := (TraceCriterion.killingForm_value ℂ L).restrict H.toSubmodule
  exact if hB : B.Nondegenerate then (B.toDual hB).symm.toLinearMap else 0

noncomputable def tAlpha_value (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) : H :=
  rootDualMap_value H α

noncomputable def rootForm_value (H : LieSubalgebra ℂ L) :
    LinearMap.BilinForm ℂ (Module.Dual ℂ H) :=
  ((TraceCriterion.killingForm_value ℂ L).restrict H.toSubmodule).compl₁₂
    (rootDualMap_value H) (rootDualMap_value H)

/-- The source's coroot normalization, used in the subsequent root-triple theorem. -/
noncomputable def coroot_value (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) : H :=
  (2 / rootForm_value H α α) • tAlpha_value H α

def rootDualMap_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L), Module.Dual ℂ H →ₗ[ℂ] H

def tAlpha_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L), Module.Dual ℂ H → H

def rootForm_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L),
    LinearMap.BilinForm ℂ (Module.Dual ℂ H)

def coroot_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L), Module.Dual ℂ H → H

def tAlpha_pairing_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
      ∀ (α : Module.Dual ℂ H) (h : H),
        TraceCriterion.killingForm_value ℂ L (tAlpha_value H α : L) (h : L) = α h

def tAlpha_unique_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
      ∀ (α : Module.Dual ℂ H) (t : H),
        (∀ h : H, TraceCriterion.killingForm_value ℂ L (t : L) (h : L) = α h) →
          t = tAlpha_value H α

def rootForm_apply_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (α β : Module.Dual ℂ H),
    rootForm_value H α β =
      TraceCriterion.killingForm_value ℂ L (tAlpha_value H α : L) (tAlpha_value H β : L)

def rootForm_eq_apply_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
      ∀ α β : Module.Dual ℂ H, rootForm_value H α β = α (tAlpha_value H β)

def opposite_root_bracket_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
      ∀ (α : Module.Dual ℂ H) (e f : L),
        e ∈ RootDecomposition.rootSpace_value H α →
        f ∈ RootDecomposition.rootSpace_value H (-α) →
        ⁅e, f⁆ = TraceCriterion.killingForm_value ℂ L e f • (tAlpha_value H α : L)

def coroot_eq_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H),
    coroot_value H α = (2 / rootForm_value H α α) • tAlpha_value H α

/-- Evaluation on the coroot agrees with the chapter's weight convention. -/
def coroot_pairing_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
      ∀ α β : Module.Dual ℂ H,
        β (coroot_value H α) = 2 * rootForm_value H β α / rootForm_value H α α

end Specs.LieAlgebrasAndRepresentations.RootForm
