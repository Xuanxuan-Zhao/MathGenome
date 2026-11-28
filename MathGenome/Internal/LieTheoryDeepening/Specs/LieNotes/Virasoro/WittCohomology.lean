import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VirasoroCocycle
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Defs

/-! The classification of the central cocycles in Theorem KM11. -/

noncomputable section

open LieModule.Cohomology

namespace LieNotes.Virasoro.WittCohomologySpec

local notation "W" => WittSpec.Witt

variable (Z : Type*) [AddCommGroup Z] [Module ℂ Z] [LieRingModule W Z] [LieModule ℂ W Z]

/-- The first differential, with its image regarded as a subspace of the cocycles. -/
def coboundary : (W →ₗ[ℂ] Z) →ₗ[ℂ] twoCocycle ℂ W Z :=
  (d₁₂ ℂ W Z).codRestrict (twoCocycle ℂ W Z) fun φ =>
    (mem_twoCocycle_iff ℂ W Z _).mpr <| by
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
        DFunLike.congr_fun (d₂₃_comp_d₁₂ ℂ W Z) φ

/-- The additive group induced by the cocycles' submodule structure. -/
scoped instance : AddCommGroup (twoCocycle ℂ W Z) :=
  @Submodule.addCommGroup ℂ (twoCochain ℂ W Z) _
    (Submodule.addCommGroup (twoCochain ℂ W Z)) _ (twoCocycle ℂ W Z)

/-- The second Lie cohomology, the quotient of 2-cocycles by 2-coboundaries. -/
abbrev H2 := twoCocycle ℂ W Z ⧸ LinearMap.range (coboundary Z)

/-- A central cocycle has a unique Virasoro parameter modulo coboundaries. -/
def Classification : Prop :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [LieRingModule W Z] [LieModule ℂ W Z]
    [LieModule.IsTrivial W Z] (c : twoCocycle ℂ W Z),
      ∃! z : Z, ∃ φ : W →ₗ[ℂ] Z, ∀ x y : W,
        c.val x y + d₁₂ ℂ W Z φ x y = VirasoroSpec.cocycleForm z x y

/-- The Virasoro parameter gives a linear parametrization of all cohomology classes. -/
def CohomologyEquivalence : Prop :=
  ∀ {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [LieRingModule W Z] [LieModule ℂ W Z]
    [LieModule.IsTrivial W Z],
      ∃ e : Z ≃ₗ[ℂ] H2 Z, ∀ (z : Z) (c : twoCocycle ℂ W Z),
        c.val.val = VirasoroSpec.cocycleForm z → e z = Submodule.Quotient.mk c

/-- With trivial scalar coefficients the second cohomology has complex dimension one. -/
def ScalarCohomologyDimension : Prop :=
  Module.finrank ℂ (H2 (TrivialLieModule ℂ W ℂ)) = 1

end LieNotes.Virasoro.WittCohomologySpec
