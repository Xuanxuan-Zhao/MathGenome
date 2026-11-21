import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellsChainsAndIntegrals
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ExteriorDerivative

/-! The C¹ ambient cell theorem, paper.tex, d04:15:cell-stokes-c1.
The form domain V is an arbitrary open neighborhood of the image, separate
from the cell target O. Writing the cell dimension as k+1 includes k=0
(the endpoint theorem), and n=0 is allowed. -/
noncomputable section
namespace Specs.D04.C15.CellStokesC1
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model

def cell_stokesType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c : Cell 1 (k+1) O)
    (V : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) V ω →
    (∀ x : cube (k+1), (c.toFun x).val ∈ V) →
    cellIntegral c (exteriorDerivative ω) = chainIntegral ω (cellBoundary c)

def chain_stokesType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (C : Chain 1 (k+1) O)
    (V : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) V ω →
    (∀ c ∈ C.support, ∀ x : cube (k+1), (c.toFun x).val ∈ V) →
    chainIntegral (exteriorDerivative ω) C = chainIntegral ω (chainBoundarySucc C)

end Specs.D04.C15.CellStokesC1
