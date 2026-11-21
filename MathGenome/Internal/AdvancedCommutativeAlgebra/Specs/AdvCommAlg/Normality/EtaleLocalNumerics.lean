import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.BaseChange
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! Numerical comparisons in SN-13, paper.tex:4360–4373.
No normality hypothesis is imposed. The local algebra and residue field
extension are the canonical maps at a prime and its contraction. -/
noncomputable section
universe u
open scoped TensorProduct
namespace Specs.AdvCommAlg.Normality.EtaleLocalNumerics

/-- All numerical and cotangent-space conclusions used in SN-13. -/
def localNumerics : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.Etale A B],
  IsNoetherianRing B ∧ ∀ (q : PrimeSpectrum B),
  let p := q.asIdeal.under A
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q.asIdeal
  letI := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  Module.Flat R S ∧ IsLocalHom (algebraMap R S) ∧
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S ∧
    IsField (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) ∧
    ringKrullDim R = ringKrullDim S ∧
    AdvCommAlg.Depth.Specs.depthValue R R = AdvCommAlg.Depth.Specs.depthValue S S ∧
    (letI : IsLocalHom (algebraMap R S) := inferInstance
     let k := IsLocalRing.ResidueField R
     let l := IsLocalRing.ResidueField S
     let V := IsLocalRing.CotangentSpace R
     let W := IsLocalRing.CotangentSpace S
     letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := k) (S := l) V l
     (∃ e : (V ⊗[k] l) ≃ₗ[l] W,
       ∀ (x : IsLocalRing.maximalIdeal R) (c : l),
       e ((IsLocalRing.maximalIdeal R).toCotangent x ⊗ₜ[k] c) =
         c • (IsLocalRing.maximalIdeal S).toCotangent
           ⟨algebraMap R S x, IsLocalRing.map_maximalIdeal_le (algebraMap R S)
             (Ideal.mem_map_of_mem _ x.property)⟩) ∧
     Module.finrank k V = Module.finrank l W)

end Specs.AdvCommAlg.Normality.EtaleLocalNumerics
