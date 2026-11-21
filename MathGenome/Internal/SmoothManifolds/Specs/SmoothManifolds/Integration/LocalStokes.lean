import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent statements for paper.tex:1857–1883, M10.03.
We use the alternating-covector realization of exterior covectors from
M07.01 (paper.tex:1454–1469). On a coordinate model a differential form is a
field of determinant-normalized continuous alternating covectors. The integral of a top form in the standard
orientation is the Lebesgue integral of its evaluation on the ordered frame.
The half-space input has compact support in the relative model and local C¹
ambient extensions, including at its true boundary; no interior-support
condition is imposed. Ambient representatives off the model are arbitrary.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SmoothManifolds.LocalStokesData
open ModelData MeasureTheory Set

abbrev CoordinateForm (n k : ℕ) :=
  Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ

/-- The ordered standard coordinate frame, starting at coordinate zero. -/
def frame (n : ℕ) (i : Fin n) : Euclidean n := Pi.single i 1

/-- Evaluation of dω on the positively oriented bulk frame. -/
def bulkCoefficient {n : ℕ} (ω : CoordinateForm (n+1) n) : Euclidean (n+1) → ℝ :=
  fun x => extDeriv ω x (frame (n+1))

/-- On the closed half-space the derivative is computed within the model.
Local C¹ extensions give this same value, independently of the extension. -/
def halfSpaceBulkCoefficient {n : ℕ} (ω : CoordinateForm (n+1) n) :
    Euclidean (n+1) → ℝ :=
  fun x => extDerivWithin ω (halfSpaceSet (n+1)) x (frame (n+1))

/-- The face uses its outward-first sign (-1)^(n+1). Evaluation on the
first n coordinate vectors is the actual restricted form coefficient.
For n=0 this is signed evaluation of a zero-covector at the left endpoint. -/
def boundaryCoefficient {n : ℕ} (ω : CoordinateForm (n+1) n) (x : Euclidean n) : ℝ :=
  (-1 : ℝ)^(n+1) *
    ω ((Fin.last n).insertNth 0 x) (fun j => frame (n+1) j.castSucc)

/-- The source's a_j: ω on the increasing frame with the j-th vector omitted
is (-1)^j a_j. Thus ω = Σ_j (-1)^j a_j dx_0∧…∧hat(dx_j)∧…∧dx_n. -/
def signedOmittedCoefficient {n : ℕ} (ω : CoordinateForm (n+1) n)
    (j : Fin (n+1)) (x : Euclidean (n+1)) : ℝ :=
  (-1 : ℝ)^j.val * ω x (j.removeNth (frame (n+1)))

end SmoothManifolds.LocalStokesData

namespace Specs.SmoothManifolds.Integration.LocalStokes
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.LocalStokesData
  MeasureTheory Set

/-- All positive dimensions, with integrability established rather than assumed. -/
def fullSpaceStokesType : Prop :=
  ∀ (n : ℕ) (ω : CoordinateForm (n+1) n),
    ContDiff ℝ 1 ω → HasCompactSupport ω →
    Integrable (bulkCoefficient ω) ∧ ∫ x, bulkCoefficient ω x = 0

/-- Local C¹ extensions up to the true boundary and compact relative support.
Both integrals are the actual coordinate integrals, with the boundary sign
inside the coefficient. This includes n+1=1. -/
def halfSpaceStokesType : Prop :=
  ∀ (n : ℕ) (ω : CoordinateForm (n+1) n),
    LocallyContDiffOn 1 (halfSpaceSet (n+1)) (fun x => ω x.val) →
    HasCompactSupport (fun x : HalfSpace (n+1) => ω x.val) →
    IntegrableOn (halfSpaceBulkCoefficient ω) (halfSpaceSet (n+1)) ∧
    Integrable (boundaryCoefficient ω) ∧
    (∫ x in halfSpaceSet (n+1), halfSpaceBulkCoefficient ω x) =
      ∫ x, boundaryCoefficient ω x

/-- The two manuscript signs give exactly -a_n, in every dimension. -/
def boundarySignType : Prop :=
  ∀ (n : ℕ) (ω : CoordinateForm (n+1) n) (x : Euclidean n),
    boundaryCoefficient ω x =
      - signedOmittedCoefficient ω (Fin.last n) ((Fin.last n).insertNth 0 x)

/-- Complete local Stokes obligation, retaining the source's coefficient sign. -/
def local_stokesType : Prop :=
  fullSpaceStokesType ∧ halfSpaceStokesType ∧ boundarySignType

end Specs.SmoothManifolds.Integration.LocalStokes
