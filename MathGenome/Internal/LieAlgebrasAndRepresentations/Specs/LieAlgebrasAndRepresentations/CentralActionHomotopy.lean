import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ModuleCasimir

/-! LA-C03, source lines 1259–1321: the central-action comparison homotopy.
The boundary below is the constructed CE boundary, on the original tensor
products. No exactness or homotopy certificate is a hypothesis. -/
noncomputable section
open CategoryTheory
open AdvancedHomologicalAlgebra.CE AdvancedHomologicalAlgebra.CE.Ext
open P103.Specs.Ch11.ExtTorDefinitions
universe u v w
namespace LieAlgebrasAndRepresentations.CentralActionHomotopy
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Left multiplication by a central element on any left U-module. -/
def centralLinear (C : U k g) (hC : C ∈ Subalgebra.center k (U k g))
    (N : Type w) [AddCommGroup N] [Module (U k g) N] : N →ₗ[U k g] N where
  toFun z := C • z
  map_add' := smul_add C
  map_smul' a z := by
    change C • (a • z) = a • (C • z)
    rw [smul_smul, smul_smul, (Subalgebra.mem_center_iff.mp hC) a]

/-- The degree -1 component is zero. The first equation is the degree-zero
homotopy equation, using the augmentation rather than a fictitious d₀. -/
def ChainContraction [Module.Free k g] (C : U k g)
    (h : ∀ n, V k g n →ₗ[U k g] V k g (n+1)) : Prop :=
  (∀ z, (boundaryData k g).differential 0 (h 0 z) = C • z) ∧
  ∀ n z, (boundaryData k g).differential (n+1) (h (n+1) z) + h n ((boundaryData k g).differential n z) = C • z

/-- H in positive degrees is precomposition with h; H out of degree zero
is zero. These are precisely δH+Hδ in degrees zero and n+1. -/
def InducedContraction [Module.Free k g] (C : U k g)
    (h : ∀ n, V k g n →ₗ[U k g] V k g (n+1))
    (N : Type w) [AddCommGroup N] [Module (U k g) N] : Prop :=
  (∀ (F : V k g 0 →ₗ[U k g] N) z,
    (F.comp ((boundaryData k g).differential 0)).comp (h 0) z = C • F z) ∧
  ∀ n (F : V k g (n+1) →ₗ[U k g] N) z,
    (F.comp (h n)).comp ((boundaryData k g).differential n) z +
      (F.comp ((boundaryData k g).differential (n+1))).comp (h (n+1)) z = C • F z

end LieAlgebrasAndRepresentations.CentralActionHomotopy

namespace LieAlgebrasAndRepresentations.CentralActionHomotopy
variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]

/-- The U-action extending the original Lie representation, rather than an
unrelated U-module structure on the coefficient carrier. -/
abbrev coefficientModule (M : Type w) [AddCommGroup M] [Module k M]
    [LieRingModule g M] [LieModule k g M] : Module (U k g) M :=
  Module.compHom M (ModuleCasimir.action k g M).toRingHom

end LieAlgebrasAndRepresentations.CentralActionHomotopy

namespace Specs.LieAlgebrasAndRepresentations.CentralActionHomotopy
open _root_.LieAlgebrasAndRepresentations.CentralActionHomotopy
open _root_.LieAlgebrasAndRepresentations.ModuleCasimir

/-- A stronger ring-level statement supplies the source's comparison homotopy
for every central augmentation-zero element, on the canonical CE complex. -/
def central_nullhomotopy_type : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g] (C : U k g) (hC : C ∈ Subalgebra.center k (U k g)),
    Shared.Lie.augmentation k g C = 0 →
    ∃ h : ∀ n, V k g n →ₗ[U k g] V k g (n+1),
      ChainContraction k g C h ∧
      ∀ (N : Type w) [AddCommGroup N] [Module (U k g) N],
        InducedContraction k g C h N ∧
        Nonempty (Homotopy
          (homPostMap (chain k g ((boundaryData k g).differential) ((boundaryData k g).augmented))
            (centralLinear k g C hC N)) 0)

/-- The precise finite-dimensional semisimple application, with the actual
module-dependent Casimir and the original coefficient representation. -/
def module_casimir_nullhomotopy_type : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M] [LieModule.IsIrreducible k g M],
    SolvableRadical.IsSemisimple_value k g → ¬ LieModule.IsTrivial g M →
    ∃ (C : U k g) (hC : CasimirProperties k g M C)
      (h : ∀ n, V k g n →ₗ[U k g] V k g (n+1)),
      ChainContraction k g C h ∧
      letI := coefficientModule k g M
      InducedContraction k g C h M ∧
      (∀ n (F : V k g n →ₗ[U k g] M) z,
        F (C • z) = action k g M C (F z)) ∧
      Nonempty (Homotopy
        (homPostMap (chain k g ((boundaryData k g).differential) ((boundaryData k g).augmented))
          (centralLinear k g C hC.1 M)) 0)

end Specs.LieAlgebrasAndRepresentations.CentralActionHomotopy
