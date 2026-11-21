import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.FiberProductRegularInCodimensionOne
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions

/-! SN-12: the coordinates and the principal quotient in the source example.
The quotient is written as a module quotient by `(x,z)A`, with its canonical
A-action; this is the underlying module of the principal ring quotient. -/
noncomputable section
universe u
namespace AdvCommAlg.Normality.FiberProduct
variable (k : Type u) [Field k]

def diagonalVariable : Ring k := pairVariable k 0 + pairVariable k 2

def principalSubmodule : Submodule (Ring k) (Ring k) :=
  Ideal.ofList [diagonalVariable k] • ⊤

abbrev PrincipalQuotient := Ring k ⧸ principalSubmodule k

def socleClass : PrincipalQuotient k := Submodule.Quotient.mk (pairVariable k 0)

namespace Specs

def principalSubmodule_eq_spanType : Prop :=
  ∀ (k : Type u) [Field k], principalSubmodule k =
    (Ideal.span {diagonalVariable k} : Ideal (Ring k))

def diagonalVariable_regularType : Prop :=
  ∀ (k : Type u) [Field k], IsSMulRegular (Ring k) (diagonalVariable k)

def socleClass_ne_zeroType : Prop :=
  ∀ (k : Type u) [Field k], socleClass k ≠ 0

def maximalIdeal_smul_socleClassType : Prop :=
  ∀ (k : Type u) [Field k] (a : Ring k),
    a ∈ IsLocalRing.maximalIdeal (Ring k) → a • socleClass k = 0

def quotient_depth_zeroType : Prop :=
  ∀ (k : Type u) [Field k],
    AdvCommAlg.Depth.Specs.depthValue (Ring k) (PrincipalQuotient k) = 0

def depth_oneType : Prop :=
  ∀ (k : Type u) [Field k], AdvCommAlg.Depth.Specs.depthValue (Ring k) (Ring k) = 1

-- Noetherianity is a conclusion of the prerequisite. Its dictionary is quantified
-- here so that these Specs do not import that implementation.
def not_serreCondition_twoType : Prop :=
  ∀ (k : Type u) [Field k] [IsNoetherianRing (Ring k)],
    ¬ AdvCommAlg.CohenMacaulay.Specs.RingSerreConditionValue (Ring k) 2

def counterexampleType : Prop :=
  ∀ (k : Type u) [Field k], ∃ hN : IsNoetherianRing (Ring k),
    ringKrullDim (Ring k) = 2 ∧
      AdvCommAlg.Depth.Specs.depthValue (Ring k) (Ring k) = 1 ∧
      @AdvCommAlg.Normality.Specs.RegularInCodimensionValue (Ring k) _ hN 1 ∧
        ¬ @AdvCommAlg.CohenMacaulay.Specs.RingSerreConditionValue (Ring k) _ hN 2

end Specs
end AdvCommAlg.Normality.FiberProduct
