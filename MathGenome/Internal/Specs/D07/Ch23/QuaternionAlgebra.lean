import MathGenome.Internal.Specs.D07.Ch08.DomainFieldQuaternionDivisionExample
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Independent specification of paper.tex:7446–7476, K07.23.quaternion_algebra.
The canonical algebra is `Quaternion ℝ`. Complex pairs are its real-linear
coordinates; `pairMul` below is the source multiplication, rather than the
componentwise multiplication on the ambient product type. No ring structure
on pairs is assumed. The bridge and the laws for these explicit operations
are conclusions. The real scalar embedding is the canonical `algebraMap`.
The source N is the squared norm, including at zero.
-/
noncomputable section

namespace Specs.D07.Ch23.QuaternionAlgebra

abbrev H := Quaternion ℝ
abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev Pair := ℂ × ℂ

def pairMul (u v : Pair) : Pair :=
  (u.1 * v.1 - u.2 * star v.2, u.1 * v.2 + u.2 * star v.1)

def pairConj (u : Pair) : Pair := (star u.1, -u.2)
def pairNorm (u : Pair) : ℝ := Complex.normSq u.1 + Complex.normSq u.2
def pairInv (u : Pair) : Pair := (pairNorm u)⁻¹ • pairConj u

def toH (u : Pair) : H := ⟨u.1.re, u.1.im, u.2.re, u.2.im⟩
def fromH (q : H) : Pair :=
  ((q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I)
def pairMatrix (u : Pair) : M := !![u.1, u.2; -star u.2, star u.1]

-- Reuse precisely the units of the earlier canonical quaternion construction.
abbrev iH := Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.iH
abbrev jH := Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.jH
abbrev kH := Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.kH

def PairCoordinates : Prop :=
  ∃ e : Pair ≃ₗ[ℝ] H, (∀ u, e u = toH u) ∧ (∀ q, e.symm q = fromH q) ∧
    (∀ u v, e (pairMul u v) = e u * e v) ∧ e (1, 0) = 1

def MatrixRepresentation : Prop :=
  ∃ f : H →ₐ[ℝ] M, Function.Injective f ∧ ∀ u, f (toH u) = pairMatrix u

def PairMatrixLaws : Prop :=
  Function.Injective pairMatrix ∧
    (∀ u v, pairMatrix (pairMul u v) = pairMatrix u * pairMatrix v) ∧
    pairMatrix (1, 0) = 1

def PairRingLaws : Prop :=
  ∀ u v w : Pair,
    pairMul (pairMul u v) w = pairMul u (pairMul v w) ∧
    pairMul (1, 0) u = u ∧ pairMul u (1, 0) = u ∧
    pairMul u (v + w) = pairMul u v + pairMul u w ∧
    pairMul (u + v) w = pairMul u w + pairMul v w

def UnitCoordinates : Prop :=
  toH (Complex.I, 0) = iH ∧ toH (0, 1) = jH ∧ toH (0, Complex.I) = kH

def UnitRelations : Prop :=
  iH * iH = -1 ∧ jH * jH = -1 ∧ kH * kH = -1 ∧
    iH * jH = kH ∧ jH * iH = -kH ∧ iH * jH = -(jH * iH)

def RealBasis : Prop :=
  (∃ b : Module.Basis (Fin 4) ℝ H, ∀ t, b t = ![1, iH, jH, kH] t) ∧
  (∃ b : Module.Basis (Fin 4) ℝ Pair,
    ∀ t, b t = ![(1, 0), (Complex.I, 0), (0, 1), (0, Complex.I)] t) ∧
    Module.finrank ℝ H = 4

def ConjugationCoordinates : Prop := ∀ u, toH (pairConj u) = star (toH u)

def NormIdentification : Prop :=
  ∀ u, pairNorm u = Quaternion.normSq (toH u) ∧
    pairNorm u = ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 ∧ pairNorm u = ‖toH u‖ ^ 2

def ConjugateProducts : Prop :=
  ∀ u, pairMul u (pairConj u) = ((pairNorm u : ℂ), 0) ∧
    pairMul (pairConj u) u = ((pairNorm u : ℂ), 0)

def PositiveNorm : Prop :=
  ∀ u, 0 ≤ pairNorm u ∧ (pairNorm u = 0 ↔ u = 0) ∧ (u ≠ 0 → 0 < pairNorm u)

def InverseFormula : Prop :=
  ∀ u, toH (pairInv u) = (toH u)⁻¹ ∧
    (u ≠ 0 → pairMul u (pairInv u) = (1, 0) ∧ pairMul (pairInv u) u = (1, 0))

/-- A genuine division ring on the canonical algebra, retaining all operations. -/
def DivisionAlgebra : Prop :=
  (∃ d : DivisionRing H, d.toRing = (inferInstance : Ring H)) ∧
    (0 : H) ≠ 1 ∧ (∀ q : H, q ≠ 0 → IsUnit q) ∧
    ¬ (∀ p q : H, p * q = q * p)

def DeterminantNorm : Prop := ∀ u, Matrix.det (pairMatrix u) = (pairNorm u : ℂ)
def NormMultiplicative : Prop := ∀ u v, pairNorm (pairMul u v) = pairNorm u * pairNorm v

def FourSquareNorm : Prop :=
  ∀ a b c d : ℝ,
    Quaternion.normSq ((a : H) + b • iH + c • jH + d • kH) =
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

/-- The two coordinate calculations used to identify the entire center. -/
def CentralizerCoordinates : Prop :=
  ∀ q : H,
    (q * iH = iH * q ↔ q.imJ = 0 ∧ q.imK = 0) ∧
    (q * iH = iH * q ∧ q * jH = jH * q ↔
      q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0)

/-- Both the canonical-algebra and complex-pair descriptions of the center. -/
def CenterReal : Prop :=
  (∀ q : H, (∀ p : H, q * p = p * q) ↔ ∃ r : ℝ, q = algebraMap ℝ H r) ∧
  (∀ u : Pair, (∀ v : Pair, pairMul u v = pairMul v u) ↔
    ∃ r : ℝ, u = ((r : ℂ), 0))

end Specs.D07.Ch23.QuaternionAlgebra
