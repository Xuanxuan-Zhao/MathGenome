import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellsChainsAndIntegrals
import Mathlib.Basic.Real.Sign

/-! Independent statements for chapters/15.tex, d04:15:boundary-square.
The objects are the upstream formal integer chains, without rank or embedding
conditions. Face indices are zero based, so i.val is the source's i-1.
The orientation comparison is made by adjoining the outward unit vector first
to the actual derivative columns of the ordered face insertion. The additional
normal statement identifies this vector geometrically, including at cube corners;
no claim that the whole cube has a smooth manifold boundary is needed. -/
noncomputable section
namespace Specs.D04.C15.BoundarySquaredAndFaceSigns
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model

def chainBoundary_squaredType : Prop :=
  ∀ {r : ℕ∞} {n : ℕ} {O : Set (E n)} (k : ℕ) (C : Chain r k O),
    chainBoundary (k-1) (chainBoundary k C) = 0

def cellBoundary_oneType : Prop :=
  ∀ {r : ℕ∞} {n : ℕ} {O : Set (E n)} (c : Cell r 1 O),
    cellBoundary c = Finsupp.single (cellFace c 0 true) 1 -
      Finsupp.single (cellFace c 0 false) 1

/-- The face insertion retains all other coordinates in increasing order,
and these are exactly its tangent columns. -/
def faceInsertion_derivativeType : Prop :=
  ∀ {k : ℕ} (i : Fin (k+1)) (ε : Bool) (x : E k) (j : Fin k),
    totalDerivative (faceInsertion i ε) x (standardBasis k j) =
      standardBasis (k+1) (i.succAbove j)

/-- The displayed normal has unit norm, annihilates the face tangent plane,
and every positive step in that direction leaves the cube. -/
def cube_face_normalType : Prop :=
  ∀ {k : ℕ} (i : Fin (k+1)) (ε : Bool) (x : E k),
    x ∈ cube k →
    let ν := if ε then standardBasis (k+1) i else -standardBasis (k+1) i
    ‖ν‖ = 1 ∧
    (∀ w : E (k+1), w i = 0 → inner ℝ ν w = 0) ∧
    ∀ t : ℝ, 0 < t → faceInsertion i ε x + t • ν ∉ cube (k+1)

/-- This normalized determinant is precisely the outward-first sign of the
face's increasing coordinate parametrization. In k=0 it compares the outward
line vector and gives +1 for the terminal point and -1 for the initial point. -/
def cube_face_signsType : Prop :=
  ∀ {k : ℕ} (i : Fin (k+1)) (ε : Bool) (x : E k),
    let d := (standardBasis (k+1)).det
      (Fin.cons (if ε then standardBasis (k+1) i else -standardBasis (k+1) i)
        (fun j : Fin k => totalDerivative (faceInsertion i ε) x (standardBasis k j)))
    let s := if ε then (-1 : ℝ)^i.val else -(-1 : ℝ)^i.val
    d = s ∧ Real.sign d = s

end Specs.D04.C15.BoundarySquaredAndFaceSigns
