import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SurfaceHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.PoincareDuality
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! The surface part of `prop:p202-cohomology-rings`, paper.tex 2604–2606
and 2645–2656. The surface, cohomology, cup product, evaluation, and local
orientation groups are the existing singular objects. An orientation is
supplied as in the source; no perfectness or classification certificate is
an input to the surface theorem. The integer-valued pairing is curried in
its first variable, so bijectivity means integral unimodularity. -/
noncomputable section
open CategoryTheory HomologicalComplex

namespace P202Specs.SurfaceCupPairing
open P202Specs.SingularChains P202Specs.CohomologyPairs
open P202Specs.CupProduct P202Specs.SurfaceHomology
open P202Specs.LocalOrientation

abbrev space (g : ℕ) := TopCat.of (OrientedSurface g)
abbrev firstCohomology (g : ℕ) := H ℤ (space g) 1

/-- Evaluation on the specified, oriented fundamental class. -/
def topEvaluation (X : TopCat.{0}) (μ : homology ℤ ℤ X 2) : H ℤ X 2 →ₗ[ℤ] ℤ :=
  (P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ (ordinaryComplex ℤ ℤ X) 2).flip μ

/-- The actual front/back cup product followed by actual UCT evaluation. -/
def pairing (X : TopCat.{0}) (C : CohomologyRing ℤ X) (μ : homology ℤ ℤ X 2) :
    LinearMap.BilinForm ℤ (H ℤ X 1) where
  toFun a := (topEvaluation X μ).comp (C.product 1 1 a)
  map_add' a b := by ext c; simp
  map_smul' r a := by ext c; simp

/-- Each handle contributes the ordered block [[0,1],[-1,0]]. -/
def standardValue (g : ℕ) (i j : Fin g × Fin 2) : ℤ :=
  if i.1 = j.1 then
    if i.2 = 0 ∧ j.2 = 1 then 1 else
    if i.2 = 1 ∧ j.2 = 0 then -1 else 0
  else 0

namespace Expected

def alternating : Prop :=
  ∀ (X : TopCat.{0}) (C : CohomologyRing ℤ X) (μ : homology ℤ ℤ X 2),
    (pairing X C μ).IsAlt

/-- Integral classification needed in the proof. This is a conclusion to
prove, not a supplied assumption about alternating forms. -/
def integralSymplectic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℤ V] [Module.Free ℤ V]
    [Module.Finite ℤ V] (B : LinearMap.BilinForm ℤ V),
    B.IsAlt → Function.Bijective B → ∀ g, Module.finrank ℤ V = 2*g →
      ∃ b : Module.Basis (Fin g × Fin 2) ℤ V,
        ∀ i j, B (b i) (b j) = standardValue g i j

/-- Full surface conclusion, including genus zero. The local-values clause
fixes the sign of the fundamental class. Bijectivity of top evaluation
records the orientation-normalized top generator. All products and maps
are the shared singular ones. -/
def surfacePairing : Prop :=
  ∀ (g : ℕ) (A : Manifold 2 (OrientedSurface g)) (o : Orientation ℤ A)
    (C : CohomologyRing ℤ (space g)),
    ∃ μ : homology ℤ ℤ (space g) 2,
      P202Specs.CompactOrientation.HasLocalValues ℤ o.val Set.univ
        (P202Specs.CompactOrientation.absoluteToSupported ℤ (OrientedSurface g) 2 μ) ∧
      Function.Bijective (topEvaluation (space g) μ) ∧
      Function.Bijective (pairing (space g) C μ) ∧
      (pairing (space g) C μ).IsAlt ∧
      ∃ b : Module.Basis (Fin g × Fin 2) ℤ (firstCohomology g),
        ∀ i j, pairing (space g) C μ (b i) (b j) = standardValue g i j

end Expected
end P202Specs.SurfaceCupPairing
