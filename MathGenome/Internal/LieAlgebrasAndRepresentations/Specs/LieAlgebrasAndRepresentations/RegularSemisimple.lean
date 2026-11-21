import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2Model
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
LA-D06, source lines 1799–1878, under the chapter convention at 1559–1565.
`zeroMultiplicity` is algebraic multiplicity, exactly as in the upstream Specs.
No positive-dimensional or nontriviality hypothesis is added.
The local conjugation assertion uses the basis-coordinate norm on the finite-dimensional space;
its exponential is the convergent Banach-algebra exponential of the adjoint.
-/
universe u
namespace Specs.LieAlgebrasAndRepresentations.RegularSemisimple
open MinimalZeroMultiplicityLocus
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The centralizer of one element, as a Lie subalgebra of the original algebra. -/
def elementCentralizer (x : L) : LieSubalgebra ℂ L where
  carrier := {y | ⁅x, y⁆ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    exact (lie_add x y z).trans (by rw [hy, hz, add_zero])
  smul_mem' := by
    intro c y hy
    change ⁅x, c • y⁆ = 0
    rw [lie_smul, show ⁅x, y⁆ = 0 from hy, smul_zero]
  lie_mem' := by
    intro y z hy hz
    change ⁅x, ⁅y, z⁆⁆ = 0
    rw [leibniz_lie, show ⁅x, y⁆ = 0 from hy, show ⁅x, z⁆ = 0 from hz,
      zero_lie, lie_zero, add_zero]

/-- The root hyperplane complement, defined before identifying it with the
minimal-multiplicity locus restricted to a maximal torus. -/
def rootRegular (H : LieSubalgebra ℂ L) : Set H :=
  {h | ∀ α ∈ RootDecomposition.rootSet_value H, α h ≠ 0}

/-- The connected dense open assertion is supplied by the upstream polynomial locus theorem. -/
def density_type : Prop := MinimalZeroMultiplicityLocus.topology_type.{u}

def regular_semisimple_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ x : L, x ∈ minimalMultiplicityLocus L → (LieAlgebra.ad ℂ L x).IsSemisimple

def regular_centralizer_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ x : L, x ∈ minimalMultiplicityLocus L →
      MaximalTori.IsMaximalToral_value (elementCentralizer x) ∧
      Module.finrank ℂ (elementCentralizer x) = minimalZeroMultiplicity L ∧
      x ∈ elementCentralizer x ∧
      ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H → x ∈ H →
        H = elementCentralizer x

def toral_rank_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H →
      Module.finrank ℂ H = minimalZeroMultiplicity L

def toral_regular_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H →
      {h : H | (h : L) ∈ minimalMultiplicityLocus L} = rootRegular H

def centralizer_lower_bound_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ x : L, minimalZeroMultiplicity L ≤ Module.finrank ℂ (elementCentralizer x)

/-- The rank-one boundary in lines 1987–1991. The standard upper root vector
of the trace-zero matrix algebra has minimal ordinary centralizer dimension,
and its adjoint zero multiplicity is strictly above the minimum. -/
def centralizer_minimum_boundary_type : Prop :=
  let L := Sl2Model.Model ℂ
  let e := Sl2Model.E ℂ
  Module.finrank ℂ (elementCentralizer e) = 1 ∧
  (∀ x : L, Module.finrank ℂ (elementCentralizer e) ≤
    Module.finrank ℂ (elementCentralizer x)) ∧
  minimalZeroMultiplicity L = 1 ∧
  zeroMultiplicity L e = 3 ∧
  e ∉ minimalMultiplicityLocus L

section Normed
variable [FiniteDimensional ℂ L]

/-- Use basis coordinates to give the algebra its ordinary finite-dimensional norm. -/
noncomputable abbrev algebraNorm : NormedAddCommGroup L :=
  NormedAddCommGroup.induced L (Fin (Module.finrank ℂ L) → ℂ)
    (Module.finBasis ℂ L).equivFun (Module.finBasis ℂ L).equivFun.injective

noncomputable def conjugationMap (H : LieSubalgebra ℂ L) (M : Submodule ℂ L) :
    M × H → L :=
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  fun p => (NormedSpace.exp
    (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L (p.1 : L)))) (p.2 : L)

/-- The derivative at (0,h) is (y,z) ↦ [y,h]+z and is invertible for every
linear complement M. The open partial homeomorphism is the actual local
inverse supplied by the finite-dimensional inverse function theorem. -/
def local_conjugation_at_type : Prop :=
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L :=
    NormedSpace.induced ℂ L (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  SolvableRadical.IsSemisimple_value ℂ L →
  ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H →
  ∀ M : Submodule ℂ L, IsCompl M H.toSubmodule →
  ∀ h : H, h ∈ rootRegular H →
    ∃ e : (M × H) ≃L[ℂ] L,
      (∀ p : M × H, e p = ⁅(p.1 : L), (h : L)⁆ + (p.2 : L)) ∧
      HasStrictFDerivAt (conjugationMap H M) (e : (M × H) →L[ℂ] L) (0, h) ∧
      ∃ φ : OpenPartialHomeomorph (M × H) L,
        (φ : M × H → L) = conjugationMap H M ∧ (0, h) ∈ φ.source
end Normed

def local_conjugation_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    local_conjugation_at_type (L := L)
end Specs.LieAlgebrasAndRepresentations.RegularSemisimple
