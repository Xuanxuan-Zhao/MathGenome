import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreRelations
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreFiniteType

/-! LA-F01 (res:F01, notes/005, lines 2717–2737). The Cartans are fixed maximal
toral subalgebras. A root-system isomorphism is expressed by its bijection of
the actual nonzero roots preserving all ordered Cartan pairings. The conclusion
identifies the induced map on the Cartans by evaluation against every root. -/

open scoped Classical
universe u v

namespace Specs.LieAlgebrasAndRepresentations.Reconstruction
open RootDecomposition RootForm SerreRelations
open _root_.LieAlgebrasAndRepresentations.Serre

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- A choice of nonzero opposite simple-root vectors normalized by the actual
Killing coroots. The weight conditions give the other two triple brackets. -/
def NormalizedSimpleVectors (H : LieSubalgebra ℂ L) (p : Module.Dual ℂ H →ₗ[ℝ] ℝ)
    (E F : simple H p → L) : Prop :=
  ∀ i, E i ∈ rootSpace_value H i.val ∧ F i ∈ rootSpace_value H (-i.val) ∧
    E i ≠ 0 ∧ F i ≠ 0 ∧ ⁅E i, F i⁆ = (coroot_value H i.val : L)

/-- Identification with the actual Serre quotient for the chosen simple roots. -/
def serre_reconstruction_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (p : Module.Dual ℂ H →ₗ[ℝ] ℝ), (∀ a ∈ rootSet_value H, p a ≠ 0) →
    ∀ E F : simple H p → L, NormalizedSimpleVectors H p E F →
      ∃ (A : Matrix (simple H p) (simple H p) ℤ) (g : Algebra A ≃ₗ⁅ℂ⁆ L),
        (∀ i j, j.val (coroot_value H i.val) = (A i j : ℂ)) ∧
        (∀ i, g (e A i) = E i ∧ g (f A i) = F i ∧
          g (h A i) = (coroot_value H i.val : L)) ∧
        (cartan A).map g.toLinearEquiv.toLinearMap = H.toSubmodule

/-- Every root-system isomorphism extends on the fixed Cartans, and compatible
choices of simple-root triples can be carried to one another by the extension. -/
def root_system_reconstruction_type : Prop :=
  ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [LieRing M] [LieAlgebra ℂ M] [FiniteDimensional ℂ M],
    SolvableRadical.IsSemisimple_value ℂ L → SolvableRadical.IsSemisimple_value ℂ M →
    ∀ (H : LieSubalgebra ℂ L) (K : LieSubalgebra ℂ M),
      MaximalTori.IsMaximalToral_value H → MaximalTori.IsMaximalToral_value K →
    ∀ σ : rootSet_value H ≃ rootSet_value K,
      (∀ a b, (σ b).val (coroot_value K (σ a).val) = b.val (coroot_value H a.val)) →
      ∃ (p : Module.Dual ℂ H →ₗ[ℝ] ℝ) (q : Module.Dual ℂ K →ₗ[ℝ] ℝ)
        (s : simple H p ≃ simple K q)
        (E F : simple H p → L) (E' F' : simple K q → M)
        (c : H ≃ₗ[ℂ] K) (g : L ≃ₗ⁅ℂ⁆ M),
        (∀ a ∈ rootSet_value H, p a ≠ 0) ∧
        (∀ a ∈ rootSet_value K, q a ≠ 0) ∧
        (∀ i, (s i).val = (σ ⟨i.val, i.property.1.1⟩).val) ∧
        NormalizedSimpleVectors H p E F ∧ NormalizedSimpleVectors K q E' F' ∧
        (∀ a : rootSet_value H, ∀ x : H, (σ a).val (c x) = a.val x) ∧
        (∀ x : H, g (x : L) = (c x : M)) ∧
        (∀ i, g (E i) = E' (s i) ∧ g (F i) = F' (s i) ∧
          g (coroot_value H i.val : L) = (coroot_value K (s i).val : M))

end Specs.LieAlgebrasAndRepresentations.Reconstruction
