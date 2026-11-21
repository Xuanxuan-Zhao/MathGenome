import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellsChainsAndIntegrals
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ExteriorDerivative

/-! Independent statements for chapters/15.tex, d04:15:cell-stokes.
The degree is written k+1, so k=0 includes the endpoint theorem. The open
neighborhood V of the image is separate from the cell's original target O.
There are no rank, embedding, orientation, or ambient-dimension restrictions.
The integrals and signed formal boundary are the canonical upstream objects. -/
noncomputable section
namespace Specs.D04.C15.CellStokesC2
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model

/-- Stokes for an arbitrary C² parametrized cell, including degree one. -/
def cell_stokesType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c : Cell 2 (k+1) O)
    (V : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) V ω →
    (∀ x : cube (k+1), (c.toFun x).val ∈ V) →
    cellIntegral c (exteriorDerivative ω) = chainIntegral ω (cellBoundary c)

/-- The same identity for every finite integer chain whose cell images lie
in the open domain of the C¹ ambient form. -/
def chain_stokesType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (C : Chain 2 (k+1) O)
    (V : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) V ω →
    (∀ c ∈ C.support, ∀ x : cube (k+1), (c.toFun x).val ∈ V) →
    chainIntegral (exteriorDerivative ω) C =
      chainIntegral ω (chainBoundarySucc C)

end Specs.D04.C15.CellStokesC2
