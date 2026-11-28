import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Basic

open scoped TensorProduct

namespace Specs.LieNotes.Coboundary

universe u v

set_option linter.checkUnivs false

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]

def SchoutenType :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ⋀[k]^2 g →ₗ[k] ⋀[k]^2 g →ₗ[k] ⋀[k]^3 g

private def wedgeThree : g →ₗ[k] g →ₗ[k] g →ₗ[k] ⋀[k]^3 g :=
  ((multilinearCurryLeftEquiv k (fun _ : Fin 2 => g) (⋀[k]^3 g)).toLinearMap.comp
    (exteriorPower.ιMulti k 3 (M := g)).toMultilinearMap.curryLeft).compr₂
    (MultilinearMap.ofSubsingletonₗ k k g (⋀[k]^3 g) (0 : Fin 1)).symm.toLinearMap

/-- The bilinear map on tensor squares induced by
`(a, b, c, d) ↦ [a, c] ∧ b ∧ d`. -/
private def tensorBracket : (g ⊗[k] g) →ₗ[k] (g ⊗[k] g) →ₗ[k] ⋀[k]^3 g :=
  let ad : g →ₗ[k] Module.End k g := LieAlgebra.ad k g
  TensorProduct.lift <|
    ((LinearMap.lflip (R₀ := k)).toLinearMap.comp
      (ad.compr₂ (wedgeThree (k := k)))).compr₂
        (TensorProduct.lift.equiv (RingHom.id k) g g (⋀[k]^3 g)).toLinearMap

/-- Apply the tensor bracket to the unscaled antisymmetrization of each bivector. -/
noncomputable def schoutenValue : ⋀[k]^2 g →ₗ[k] ⋀[k]^2 g →ₗ[k] ⋀[k]^3 g :=
  tensorBracket.compl₁₂ alternatingTensorValue alternatingTensorValue

/-- The value on two decomposable bivectors, with the signs of Proposition LD05. -/
def SchoutenApplyType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ a b c d : g, schoutenValue (k := k) (wedge₂Value a b) (wedge₂Value c d) =
      exteriorPower.ιMulti k 3 ![⁅a, c⁆, b, d] - exteriorPower.ιMulti k 3 ![⁅a, d⁆, b, c] -
        exteriorPower.ιMulti k 3 ![⁅b, c⁆, a, d] + exteriorPower.ιMulti k 3 ![⁅b, d⁆, a, c]

def SchoutenSymmetricType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ r s : ⋀[k]^2 g, schoutenValue r s = schoutenValue s r

def SchoutenAdjointType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ (x : g) (r s : ⋀[k]^2 g),
      exteriorAdjointValue 3 x (schoutenValue r s) =
        schoutenValue (exteriorAdjointValue 2 x r) s + schoutenValue r (exteriorAdjointValue 2 x s)

end Specs.LieNotes.Coboundary
