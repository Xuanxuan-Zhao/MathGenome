import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions
import Mathlib.AlgebraicGeometry.StructureSheaf

/-! SN-11: sections mean sections of Mathlib's genuine structure sheaf on Spec A.
The map from A is its canonical map to sections, equivalently restriction of
constant global sections. No positive-dimension assumption is imposed. -/
universe u
open TopologicalSpace Opposite AlgebraicGeometry
namespace AdvCommAlg.Normality.Specs

def codimensionTwo_restriction_bijectiveType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A],
    IsNormalValue A → ∀ U : Opens (PrimeSpectrum A),
    (∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U) →
    Function.Bijective (algebraMap A ((Spec.structureSheaf A).1.obj (op U)))

def codimensionTwo_extension_uniqueType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A],
    IsNormalValue A → ∀ U : Opens (PrimeSpectrum A),
    (∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U) →
    ∀ s : (Spec.structureSheaf A).1.obj (op U),
    ∃! a : A, algebraMap A ((Spec.structureSheaf A).1.obj (op U)) a = s

def codimensionTwo_extension_ringEquivType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A],
    IsNormalValue A → ∀ U : Opens (PrimeSpectrum A),
    (∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U) →
    ∃ e : A ≃+* (Spec.structureSheaf A).1.obj (op U),
      ∀ a : A, e a = algebraMap A ((Spec.structureSheaf A).1.obj (op U)) a

end AdvCommAlg.Normality.Specs
