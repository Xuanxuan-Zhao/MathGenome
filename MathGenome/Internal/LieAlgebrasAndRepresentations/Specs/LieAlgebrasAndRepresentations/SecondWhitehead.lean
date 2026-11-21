import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AbelianExtensions
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing

/-! LA-I05, Lie volume expanded lines 4210–4230. The field has characteristic
zero; both the semisimple Lie algebra and the specified coefficient module
are finite dimensional. H² is the cycles modulo boundaries of the canonical
exterior Chevalley–Eilenberg differential (equivalently any differential with
its specified formula). Extensions retain the specified kernel action. -/
noncomputable section
universe u v w z
namespace Specs.LieAlgebrasAndRepresentations.SecondWhitehead
open _root_.AdvancedHomologicalAlgebra.CE
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions
open _root_.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
open P103.Specs.Ch10.Complexes

variable (k : Type u) (g : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule g M] [LieModule k g M]

def cocycleExactStatement : Prop :=
  SolvableRadical.IsSemisimple_value k g →
    ∀ c : LieModule.Cohomology.twoCocycle k g M,
      ∃ b : g →ₗ[k] M, LieModule.Cohomology.d₁₂ k g M b = c.val

def secondWhiteheadStatement : Prop :=
  SolvableRadical.IsSemisimple_value k g →
    Subsingleton (Homology (ceCochain k g M) 2)

def canonicalVanishingStatement : Prop :=
  SolvableRadical.IsSemisimple_value k g →
    ∀ δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M),
      HasLieCEFormula δ → Subsingleton (CEH2 δ)

/-- The section lands in the supplied middle algebra, whose universe is
independent of both the quotient and the coefficient module. -/
def extensionSplitsStatement : Prop :=
  SolvableRadical.IsSemisimple_value k g →
    ∀ E : Extension.{u,v,w,z} k g M, HasLieSection E



def cocycleExactType : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M],
    cocycleExactStatement k g M

def secondWhiteheadType : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M],
    secondWhiteheadStatement k g M

def canonicalVanishingType : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M],
    canonicalVanishingStatement k g M

def extensionSplitsType : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M],
    extensionSplitsStatement.{u,v,w,z} k g M

end Specs.LieAlgebrasAndRepresentations.SecondWhitehead
