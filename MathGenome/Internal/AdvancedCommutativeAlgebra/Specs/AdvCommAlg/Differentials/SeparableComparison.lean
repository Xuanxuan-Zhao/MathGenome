import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TowerMaps
import Mathlib.FieldTheory.Separable

/-! Independent specifications for the general comparison in KD-22,
paper.tex:429–445. `Algebra.IsSeparable K L` means every element is
separable algebraic over K; no finiteness assumption is imposed. The base A
is any commutative ring and the scalar tower expresses the given ring map
A → K and its composite A → L. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w
open scoped TensorProduct

/-- The canonical map, with its prescribed scalar structures, is bijective. -/
def separableComparisonBijective : Prop :=
  ∀ (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L],
    Function.Bijective (towerMapUValue A K L)

/-- An L-linear isomorphism whose underlying map is the canonical map,
including its action on the universal differentials. -/
def separableComparison : Prop :=
  ∀ (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L],
    ∃ e : (L ⊗[K] KaehlerDifferential A K) ≃ₗ[L] KaehlerDifferential A L,
      e.toLinearMap = towerMapUValue A K L ∧
      ∀ k : K, e (1 ⊗ₜ[K] KaehlerDifferential.D A K k) =
        KaehlerDifferential.D A L (algebraMap K L k)

/-- In particular the relative module vanishes, also for infinite extensions. -/
def separableVanishing : Prop :=
  ∀ (K : Type v) (L : Type w) [Field K] [Field L]
    [Algebra K L] [Algebra.IsSeparable K L],
    Subsingleton (KaehlerDifferential K L)

end Specs.AdvCommAlg.Differentials
