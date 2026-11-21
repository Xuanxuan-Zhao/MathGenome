import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Independent interfaces for the finite construction in paper.tex:3625–3651.
The canonical coefficients are constructed from the original family's derivatives.
`SourceFiniteElimination` combines spectral coordinates, parameter-dependent
local inverses, and the actual Taylor jets of both nonlinear pullbacks.
No normal form or output Taylor certificate is postulated.
-/
namespace Specs.D13Unified.Ch16.CubicHomologicalElimination

open Complex
open scoped ComplexConjugate

noncomputable def eigenvalue (a b : ℝ) : ℂ := a + I * b

/-- Cast before subtracting: the imaginary weight can be negative. -/
noncomputable def divisor (a b : ℝ) (j k : ℕ) : ℂ :=
  ((j : ℂ) + k - 1) * a + I * ((j : ℂ) - k - 1) * b

@[ext] structure Quadratic where
  c20 : ℂ
  c11 : ℂ
  c02 : ℂ

@[ext] structure Cubic where
  c30 : ℂ
  c21 : ℂ
  c12 : ℂ
  c03 : ℂ

noncomputable def Quadratic.eval (q : Quadratic) (z : ℂ) : ℂ :=
  q.c20 * z ^ 2 + q.c11 * z * conj z + q.c02 * conj z ^ 2

noncomputable def Cubic.eval (p : Cubic) (z : ℂ) : ℂ :=
  p.c30 * z ^ 3 + p.c21 * z ^ 2 * conj z +
  p.c12 * z * conj z ^ 2 + p.c03 * conj z ^ 3

/-- Real directional derivative of the displayed quadratic polynomial. -/
noncomputable def Quadratic.directional (q : Quadratic) (z v : ℂ) : ℂ :=
  2 * q.c20 * z * v + q.c11 * (v * conj z + z * conj v) +
  2 * q.c02 * conj z * conj v

/-- Real directional derivative of the displayed cubic polynomial. -/
noncomputable def Cubic.directional (p : Cubic) (z v : ℂ) : ℂ :=
  3 * p.c30 * z ^ 2 * v +
  p.c21 * (2 * z * v * conj z + z ^ 2 * conj v) +
  p.c12 * (v * conj z ^ 2 + 2 * z * conj z * conj v) +
  3 * p.c03 * conj z ^ 2 * conj v

noncomputable def quadraticChange (a b : ℝ) (q : Quadratic) : Quadratic :=
  ⟨q.c20 / divisor a b 2 0, q.c11 / divisor a b 1 1,
    q.c02 / divisor a b 0 2⟩

/-- Coefficients of f₃ + Df₂ H₂. This is the cubic left by the first change
once its quadratic homological equation has been solved. -/
noncomputable def cubicAfterQuadratic (q : Quadratic) (p : Cubic)
    (h : Quadratic) : Cubic :=
  ⟨p.c30 + 2 * q.c20 * h.c20 + q.c11 * conj h.c02,
   p.c21 + 2 * q.c20 * h.c11 + q.c11 * h.c20 +
     q.c11 * conj h.c11 + 2 * q.c02 * conj h.c02,
   p.c12 + 2 * q.c20 * h.c02 + q.c11 * h.c11 +
     q.c11 * conj h.c20 + 2 * q.c02 * conj h.c11,
   p.c03 + q.c11 * h.c02 + 2 * q.c02 * conj h.c20⟩

/-- The (2,1) coefficient is deliberately set to zero, even away from a=0. -/
noncomputable def cubicChange (a b : ℝ) (g : Cubic) : Cubic :=
  ⟨g.c30 / divisor a b 3 0, 0, g.c12 / divisor a b 1 2,
    g.c03 / divisor a b 0 3⟩

noncomputable def retainedCoefficient (a b : ℝ) (q : Quadratic) (p : Cubic) : ℂ :=
  (cubicAfterQuadratic q p (quadraticChange a b q)).c21

/-- Nonresonance holds for every a as soon as b>0. The exceptional weight is
retained rather than divided by; its divisor is 2a, possibly nonzero. -/
def NonzeroDivisors : Prop :=
  ∀ (a b : ℝ), 0 < b →
    (∀ j k : ℕ, j + k = 2 → divisor a b j k ≠ 0) ∧
    (∀ j k : ℕ, j + k = 3 → (j, k) ≠ (2, 1) → divisor a b j k ≠ 0)

/-- Parameter-neighborhood nonvanishing, with no crossing assumption on a. -/
def NeighborhoodDivisors : Prop :=
  ∀ (a b : ℝ → ℝ), ContinuousAt b 0 → 0 < b 0 →
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      (∀ j k : ℕ, j + k = 2 → divisor (a μ) (b μ) j k ≠ 0) ∧
      (∀ j k : ℕ, j + k = 3 → (j, k) ≠ (2, 1) →
        divisor (a μ) (b μ) j k ≠ 0)

/-- Identities in the actual polynomial variables, not only coefficient labels. -/
def FiniteElimination : Prop :=
  ∀ (a b : ℝ) (q : Quadratic) (p : Cubic), 0 < b →
    let l := eigenvalue a b
    let h := quadraticChange a b q
    let g := cubicAfterQuadratic q p h
    let t := cubicChange a b g
    (∀ z : ℂ, q.eval z + l * h.eval z - h.directional z (l * z) = 0) ∧
    (∀ z : ℂ, g.eval z = p.eval z + q.directional z (h.eval z)) ∧
    (∀ z : ℂ,
      p.eval z + q.directional z (h.eval z) -
        h.directional z (l * h.eval z + q.eval z) +
        h.directional z (h.directional z (l * z)) = g.eval z) ∧
    (∀ z : ℂ, g.eval z + l * t.eval z - t.directional z (l * z) =
      retainedCoefficient a b q p * z ^ 2 * conj z)

/-- Smooth real local inverses for each fixed parameter. This deliberately says
nothing yet about a common neighborhood or parameter dependence of the inverse. -/
def SpatialLocalInverses : Prop :=
  (∀ q : Quadratic, ∃ e : OpenPartialHomeomorph ℂ ℂ,
    (e : ℂ → ℂ) = (fun z => z + q.eval z) ∧ 0 ∈ e.source ∧
    ContDiff ℝ ⊤ (e : ℂ → ℂ) ∧ ContDiffAt ℝ ⊤ e.symm 0) ∧
  (∀ p : Cubic, ∃ e : OpenPartialHomeomorph ℂ ℂ,
    (e : ℂ → ℂ) = (fun z => z + p.eval z) ∧ 0 ∈ e.source ∧
    ContDiff ℝ ⊤ (e : ℂ → ℂ) ∧ ContDiffAt ℝ ⊤ e.symm 0)

/-- Coefficient regularity has an explicit order; no smoothness beyond the
available differentiability of the input jet is assumed. -/
def QuadraticRegular (n : WithTop ℕ∞) (q : ℝ → Quadratic) (μ : ℝ) : Prop :=
  ContDiffAt ℝ n (fun ν => (q ν).c20) μ ∧
  ContDiffAt ℝ n (fun ν => (q ν).c11) μ ∧
  ContDiffAt ℝ n (fun ν => (q ν).c02) μ

def CubicRegular (n : WithTop ℕ∞) (p : ℝ → Cubic) (μ : ℝ) : Prop :=
  ContDiffAt ℝ n (fun ν => (p ν).c30) μ ∧
  ContDiffAt ℝ n (fun ν => (p ν).c21) μ ∧
  ContDiffAt ℝ n (fun ν => (p ν).c12) μ ∧
  ContDiffAt ℝ n (fun ν => (p ν).c03) μ

/-- Finite coefficient operations preserve the regularity of the supplied jet.
This is not a hypothesis that a C⁵ field already has a normal form. -/
def ParameterCoefficients : Prop :=
  ∀ (n : WithTop ℕ∞) (a b : ℝ → ℝ) (q : ℝ → Quadratic) (p : ℝ → Cubic) (μ : ℝ),
    ContDiffAt ℝ n a μ → ContDiffAt ℝ n b μ → 0 < b μ →
    QuadraticRegular n q μ → CubicRegular n p μ →
    let h := fun ν => quadraticChange (a ν) (b ν) (q ν)
    let g := fun ν => cubicAfterQuadratic (q ν) (p ν) (h ν)
    QuadraticRegular n h μ ∧ CubicRegular n g μ ∧
    CubicRegular n (fun ν => cubicChange (a ν) (b ν) (g ν)) μ ∧
    ContDiffAt ℝ n (fun ν => retainedCoefficient (a ν) (b ν) (q ν) (p ν)) μ

/-- A local inverse with the parameter retained as the first coordinate.
For finite positive n, the ContDiffAt assertions give Cⁿ regularity on
sufficiently small neighborhoods of the distinguished point. -/
def JointInverseAt (n : WithTop ℕ∞) (f : ℝ × ℂ → ℝ × ℂ) (μ : ℝ) : Prop :=
  ∃ e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ),
    (e : ℝ × ℂ → ℝ × ℂ) = f ∧ (μ, 0) ∈ e.source ∧
    ContDiffAt ℝ n f (μ, 0) ∧ ContDiffAt ℝ n e.symm (μ, 0) ∧
    (∀ y ∈ e.target, (e.symm y).1 = y.1)

noncomputable def quadraticFamilyChange (q : ℝ → Quadratic) (x : ℝ × ℂ) : ℝ × ℂ :=
  (x.1, x.2 + (q x.1).eval x.2)

noncomputable def cubicFamilyChange (p : ℝ → Cubic) (x : ℝ × ℂ) : ℝ × ℂ :=
  (x.1, x.2 + (p x.1).eval x.2)

def ParameterLocalInverses : Prop :=
  ∀ (n : WithTop ℕ∞), n ≠ 0 →
    (∀ (q : ℝ → Quadratic) (μ : ℝ), QuadraticRegular n q μ →
      JointInverseAt n (quadraticFamilyChange q) μ) ∧
    (∀ (p : ℝ → Cubic) (μ : ℝ), CubicRegular n p μ →
      JointInverseAt n (cubicFamilyChange p) μ)

/-- Real matrix action in the standard real basis of ℂ. -/
noncomputable def planarLinearField (r s t u : ℝ) (z : ℂ) : ℂ :=
  ⟨r * z.re + s * z.im, t * z.re + u * z.im⟩

noncomputable def linearCoordinateForward (r t a b : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re + ((r - a) / b) * z.im, (t / b) * z.im⟩

noncomputable def linearCoordinateInverse (r t a b : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re - ((r - a) / b) * (z.im / (t / b)), z.im / (t / b)⟩

/-- Real linear coordinates from the trace and determinant invariants.
`SpectralFamilyCoordinates` supplies these from the actual source derivative. -/
def RealLinearCoordinates : Prop :=
  ∀ r s t u a b : ℝ, 0 < b → r + u = 2 * a → r * u - s * t = a ^ 2 + b ^ 2 →
    ∃ S : ℂ ≃L[ℝ] ℂ,
      (S : ℂ → ℂ) = linearCoordinateForward r t a b ∧
      (S.symm : ℂ → ℂ) = linearCoordinateInverse r t a b ∧
      ∀ z, planarLinearField r s t u (S z) = S (eigenvalue a b * z)

/-- These identities connect the algebraic directional formulas to real calculus. -/
def RealPolynomialDerivatives : Prop :=
  (∀ (q : Quadratic) (z v : ℂ), fderiv ℝ q.eval z v = q.directional z v) ∧
  (∀ (p : Cubic) (z v : ℂ), fderiv ℝ p.eval z v = p.directional z v)

/-- The explicit real linear coordinates and their inverses vary with the
regularity of their entries on the nonvanishing parameter neighborhood. -/
def LinearCoordinatesRegular : Prop :=
  ∀ (n : WithTop ℕ∞) (r t a b : ℝ → ℝ) (μ : ℝ),
    ContDiffAt ℝ n r μ → ContDiffAt ℝ n t μ →
    ContDiffAt ℝ n a μ → ContDiffAt ℝ n b μ → b μ ≠ 0 → t μ ≠ 0 →
    ContDiffAt ℝ n (fun x : ℝ × ℂ =>
      (x.1, linearCoordinateForward (r x.1) (t x.1) (a x.1) (b x.1) x.2)) (μ, 0) ∧
    ContDiffAt ℝ n (fun x : ℝ × ℂ =>
      (x.1, linearCoordinateInverse (r x.1) (t x.1) (a x.1) (b x.1) x.2)) (μ, 0)

/-- The spatial derivative of the original real planar family, with ℂ used
only as the standard real plane. -/
noncomputable def linearization (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℂ →L[ℝ] ℂ :=
  fderiv ℝ (fun z => F (μ, z)) 0

/-- The complexification of the actual real derivative in the basis (1,i).
Its eigenvalues are the source's complex eigenvalues of the real 2×2 matrix. -/
noncomputable def complexifiedLinearization (F : ℝ × ℂ → ℂ) (μ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![↑((linearization F μ) 1).re, ↑((linearization F μ) I).re;
     ↑((linearization F μ) 1).im, ↑((linearization F μ) I).im]

noncomputable def spectralReal (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℝ :=
  (((linearization F μ) 1).re + ((linearization F μ) I).im) / 2

noncomputable def spectralImag (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℝ :=
  Real.sqrt (((linearization F μ) 1).re * ((linearization F μ) I).im -
    ((linearization F μ) I).re * ((linearization F μ) 1).im - spectralReal F μ ^ 2)

/-- Spectral and linear-coordinate part of the construction, starting from the
actual local C⁵ family. No parameter regularity of an eigenvalue label is assumed.
The positive branch is constructed from trace and determinant. Equilibrium is
not needed for this linear assertion, so it also applies to the source family.
This is still only one part of the full finite normal-form construction. -/
def SpectralFamilyCoordinates : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    spectralReal F 0 = 0 ∧ spectralImag F 0 = ω ∧
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      0 < spectralImag F μ ∧
      ContDiffAt ℝ 4 (spectralReal F) μ ∧ ContDiffAt ℝ 4 (spectralImag F) μ ∧
      (∀ l : ℂ, Module.End.HasEigenvalue (complexifiedLinearization F μ).toLin' l ↔
        l = eigenvalue (spectralReal F μ) (spectralImag F μ) ∨
        l = conj (eigenvalue (spectralReal F μ) (spectralImag F μ))) ∧
      (∃ S : ℂ ≃L[ℝ] ℂ,
        (S : ℂ → ℂ) = linearCoordinateForward
          ((linearization F μ) 1).re ((linearization F μ) 1).im
          (spectralReal F μ) (spectralImag F μ) ∧
        (S.symm : ℂ → ℂ) = linearCoordinateInverse
          ((linearization F μ) 1).re ((linearization F μ) 1).im
          (spectralReal F μ) (spectralImag F μ) ∧
        ∀ z, linearization F μ (S z) =
          S (eigenvalue (spectralReal F μ) (spectralImag F μ) * z)) ∧
      ContDiffAt ℝ 4 (fun x : ℝ × ℂ =>
        (x.1, linearCoordinateForward ((linearization F x.1) 1).re
          ((linearization F x.1) 1).im (spectralReal F x.1) (spectralImag F x.1) x.2))
        (μ, 0) ∧
      ContDiffAt ℝ 4 (fun x : ℝ × ℂ =>
        (x.1, linearCoordinateInverse ((linearization F x.1) 1).re
          ((linearization F x.1) 1).im (spectralReal F x.1) (spectralImag F x.1) x.2))
        (μ, 0)

/-- Conversion of a real homogeneous polynomial in x,y to z,z̄. Complex
coefficients encode the two real output components; there is no reality
restriction on the three or four complex coefficients. -/
noncomputable def quadraticOfReal (X Y Z : ℂ) : Quadratic :=
  ⟨(X - I * Y - Z) / 4, (X + Z) / 2, (X + I * Y - Z) / 4⟩

noncomputable def cubicOfReal (X Y Z W : ℂ) : Cubic :=
  ⟨(X - I * Y - Z + I * W) / 8,
   (3 * X - I * Y + Z - 3 * I * W) / 8,
   (3 * X + I * Y + Z + 3 * I * W) / 8,
   (X + I * Y - Z - I * W) / 8⟩

/-- Encode arbitrary real multilinear diagonal polynomials. Mixed entries are
summed explicitly, so these definitions require no assumed symmetry. -/
noncomputable def quadraticOfBilinear (B : ℂ [×2]→L[ℝ] ℂ) : Quadratic :=
  quadraticOfReal (B ![1, 1] / 2) ((B ![1, I] + B ![I, 1]) / 2) (B ![I, I] / 2)

noncomputable def cubicOfTrilinear (C : ℂ [×3]→L[ℝ] ℂ) : Cubic :=
  cubicOfReal (C ![1, 1, 1] / 6)
    ((C ![1, 1, I] + C ![1, I, 1] + C ![I, 1, 1]) / 6)
    ((C ![1, I, I] + C ![I, 1, I] + C ![I, I, 1]) / 6) (C ![I, I, I] / 6)

def HomogeneousJetRepresentation : Prop :=
  (∀ (B : ℂ [×2]→L[ℝ] ℂ) (z : ℂ),
    (quadraticOfBilinear B).eval z = B (fun _ => z) / 2) ∧
  (∀ (C : ℂ [×3]→L[ℝ] ℂ) (z : ℂ),
    (cubicOfTrilinear C).eval z = C (fun _ => z) / 6)

/-- The homogeneous spatial jet after a parameter-dependent real linear
change. The mixed derivatives are those of the ORIGINAL family, so a C⁴
linear basis does not lose an extra spatial derivative of the C⁵ field. -/
noncomputable def normalizedSpatialJet (F : ℝ × ℂ → ℂ)
    (S T : ℝ → ℂ →L[ℝ] ℂ) (d : ℕ) (μ : ℝ) : ℂ [×d]→L[ℝ] ℂ :=
  (T μ).compContinuousMultilinearMap
    ((iteratedFDeriv ℝ d F (μ, 0)).compContinuousLinearMap
      (fun _ => (ContinuousLinearMap.inr ℝ ℝ ℂ).comp (S μ)))

noncomputable def familyQuadratic (F : ℝ × ℂ → ℂ) (S T : ℝ → ℂ →L[ℝ] ℂ)
    (μ : ℝ) : Quadratic := quadraticOfBilinear (normalizedSpatialJet F S T 2 μ)

noncomputable def familyCubic (F : ℝ × ℂ → ℂ) (S T : ℝ → ℂ →L[ℝ] ℂ)
    (μ : ℝ) : Cubic := cubicOfTrilinear (normalizedSpatialJet F S T 3 μ)

/-- Parameter regularity and exact diagonal representation of the jets
constructed from the original C⁵ family's derivatives. This assertion does
not yet identify jets after a NONLINEAR inverse-Jacobian pullback. -/
def TaylorFamilyCoefficients : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (S T : ℝ → ℂ →L[ℝ] ℂ) (μ : ℝ),
    ContDiffAt ℝ 5 F (μ, 0) → ContDiffAt ℝ 4 S μ → ContDiffAt ℝ 4 T μ →
    QuadraticRegular 3 (familyQuadratic F S T) μ ∧
    CubicRegular 2 (familyCubic F S T) μ ∧
    (∀ z : ℂ, (familyQuadratic F S T μ).eval z =
      T μ (iteratedFDeriv ℝ 2 F (μ, 0) (fun _ => (0, S μ z))) / 2) ∧
    (∀ z : ℂ, (familyCubic F S T μ).eval z =
      T μ (iteratedFDeriv ℝ 3 F (μ, 0) (fun _ => (0, S μ z))) / 6)

noncomputable def linearNormalizedFamily (F : ℝ × ℂ → ℂ)
    (S T : ℝ → ℂ →L[ℝ] ℂ) (x : ℝ × ℂ) : ℂ := T x.1 (F (x.1, S x.1 x.2))

/-- The constructed coefficients are the actual spatial Taylor jets of the
linearly normalized family, with no global smoothness hypothesis on F. -/
def NormalizedTaylorJets : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (S T : ℝ → ℂ →L[ℝ] ℂ) (μ : ℝ),
    ContDiffAt ℝ 5 F (μ, 0) → ∀ d : ℕ, d ≤ 5 →
      iteratedFDeriv ℝ d (fun z => linearNormalizedFamily F S T (μ, z)) 0 =
        normalizedSpatialJet F S T d μ

/-- Bundled versions of the explicit real linear coordinate formulas. They
are defined even away from the nondegenerate neighborhood; invertibility is
proved only where the spectral hypotheses hold. -/
noncomputable def coordinateForwardCLM (r t a b : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (1 : ℂ) +
    Complex.imCLM.smulRight ⟨(r - a) / b, t / b⟩

noncomputable def coordinateInverseCLM (r t a b : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (1 : ℂ) +
    Complex.imCLM.smulRight ⟨-((r - a) / b) / (t / b), 1 / (t / b)⟩

noncomputable def sourceForwardCLM (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℂ →L[ℝ] ℂ :=
  coordinateForwardCLM ((linearization F μ) 1).re ((linearization F μ) 1).im
    (spectralReal F μ) (spectralImag F μ)

noncomputable def sourceInverseCLM (F : ℝ × ℂ → ℂ) (μ : ℝ) : ℂ →L[ℝ] ℂ :=
  coordinateInverseCLM ((linearization F μ) 1).re ((linearization F μ) 1).im
    (spectralReal F μ) (spectralImag F μ)

/-- The original-family jet data in the source's chosen linear basis.
The conclusions explicitly refer to the derivatives of the normalized field;
no arbitrary quadratic/cubic input or assumed Taylor certificate is used. -/
def SourceTaylorData : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      ContDiffAt ℝ 5 F (μ, 0) ∧ 0 < spectralImag F μ ∧
      ContDiffAt ℝ 4 (sourceForwardCLM F) μ ∧
      ContDiffAt ℝ 4 (sourceInverseCLM F) μ ∧
      QuadraticRegular 3 (familyQuadratic F (sourceForwardCLM F) (sourceInverseCLM F)) μ ∧
      CubicRegular 2 (familyCubic F (sourceForwardCLM F) (sourceInverseCLM F)) μ ∧
      (∀ z : ℂ,
        (familyQuadratic F (sourceForwardCLM F) (sourceInverseCLM F) μ).eval z =
          iteratedFDeriv ℝ 2 (fun w => linearNormalizedFamily F
            (sourceForwardCLM F) (sourceInverseCLM F) (μ, w)) 0 (fun _ => z) / 2) ∧
      (∀ z : ℂ,
        (familyCubic F (sourceForwardCLM F) (sourceInverseCLM F) μ).eval z =
          iteratedFDeriv ℝ 3 (fun w => linearNormalizedFamily F
            (sourceForwardCLM F) (sourceInverseCLM F) (μ, w)) 0 (fun _ => z) / 6) ∧
      (∀ z : ℂ, sourceInverseCLM F μ (sourceForwardCLM F μ z) = z) ∧
      (∀ z : ℂ, sourceForwardCLM F μ (sourceInverseCLM F μ z) = z) ∧
      (∀ z : ℂ, sourceInverseCLM F μ
          (linearization F μ (sourceForwardCLM F μ z)) =
          eigenvalue (spectralReal F μ) (spectralImag F μ) * z)

/-- The actual inverse-Jacobian pullback. Off the invertible locus the library
inverse is totalized; the identities below require genuine invertibility. -/
noncomputable def nonlinearPullback (F H : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ H z).inverse (F (H z))

/-- Exact identities for the actual pullbacks, retaining the input residual
explicitly. They do not assume an output jet, and do not yet prove that the
residual has vanishing derivatives through order three. -/
def ActualPullbackIdentities : Prop :=
  ∀ (F : ℂ → ℂ) (a b : ℝ) (q : Quadratic) (p : Cubic), 0 < b →
    let l := eigenvalue a b
    let h := quadraticChange a b q
    let g := cubicAfterQuadratic q p h
    let t := cubicChange a b g
    (∀ z : ℂ, (fderiv ℝ (fun w => w + h.eval w) z).IsInvertible →
      nonlinearPullback F (fun w => w + h.eval w) z - (l * z + g.eval z) =
        (fderiv ℝ (fun w => w + h.eval w) z).inverse
          ((F (z + h.eval z) - (l * (z + h.eval z) +
            q.eval (z + h.eval z) + p.eval (z + h.eval z))) +
            q.eval (h.eval z) + (p.eval (z + h.eval z) - p.eval z) -
            h.directional z (g.eval z))) ∧
    (∀ z : ℂ, (fderiv ℝ (fun w => w + t.eval w) z).IsInvertible →
      nonlinearPullback F (fun w => w + t.eval w) z -
        (l * z + g.c21 * z ^ 2 * conj z) =
        (fderiv ℝ (fun w => w + t.eval w) z).inverse
          ((F (z + t.eval z) - (l * (z + t.eval z) + g.eval (z + t.eval z))) +
            (g.eval (z + t.eval z) - g.eval z) -
            t.directional z (g.c21 * z ^ 2 * conj z)))

/-- All finite coefficient operations and local coordinate inverses, with
coefficients constructed from the ORIGINAL family. This partial assertion does
not identify the computed cubic with the nonlinear pullback's Taylor jet. -/
def SourceHomologicalData : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    let a := spectralReal F
    let b := spectralImag F
    let q := familyQuadratic F (sourceForwardCLM F) (sourceInverseCLM F)
    let p := familyCubic F (sourceForwardCLM F) (sourceInverseCLM F)
    let h := fun μ => quadraticChange (a μ) (b μ) (q μ)
    let g := fun μ => cubicAfterQuadratic (q μ) (p μ) (h μ)
    let t := fun μ => cubicChange (a μ) (b μ) (g μ)
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      0 < b μ ∧ QuadraticRegular 3 h μ ∧ CubicRegular 2 g μ ∧
      CubicRegular 2 t μ ∧ ContDiffAt ℝ 2 (fun ν => (g ν).c21) μ ∧
      JointInverseAt 3 (quadraticFamilyChange h) μ ∧
      JointInverseAt 2 (cubicFamilyChange t) μ ∧
      (∀ j k : ℕ, j + k = 2 → divisor (a μ) (b μ) j k ≠ 0) ∧
      (∀ j k : ℕ, j + k = 3 → (j, k) ≠ (2, 1) → divisor (a μ) (b μ) j k ≠ 0)

/-- For each fixed parameter the polynomial changes preserve the available
spatial differentiability. This does not claim joint C⁵ parameter regularity. -/
def ActualPullbackRegularity : Prop :=
  ∀ (F : ℂ → ℂ), ContDiffAt ℝ 5 F 0 →
    (∀ h : Quadratic, ContDiffAt ℝ 5 (nonlinearPullback F (fun z => z + h.eval z)) 0) ∧
    (∀ t : Cubic, ContDiffAt ℝ 5 (nonlinearPullback F (fun z => z + t.eval z)) 0)

/-- The equilibrium and linear Taylor jet of the normalized ORIGINAL field.
The equilibrium hypothesis is precisely local in the parameter. -/
def SourceNormalizedLinearJet : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      linearNormalizedFamily F (sourceForwardCLM F) (sourceInverseCLM F) (μ, 0) = 0 ∧
      ∀ z : ℂ, fderiv ℝ (fun w => linearNormalizedFamily F
        (sourceForwardCLM F) (sourceInverseCLM F) (μ, w)) 0 z =
          eigenvalue (spectralReal F μ) (spectralImag F μ) * z

/-- Actual spatial Taylor coefficients through degree three, with the usual
factorials. Complex numbers are the real plane throughout this assertion. -/
def SpatialCubicJet (F : ℂ → ℂ) (l : ℂ) (q : Quadratic) (p : Cubic) : Prop :=
  F 0 = 0 ∧ (∀ v, fderiv ℝ F 0 v = l * v) ∧
    (∀ v, q.eval v = iteratedFDeriv ℝ 2 F 0 (fun _ => v) / 2) ∧
    (∀ v, p.eval v = iteratedFDeriv ℝ 3 F 0 (fun _ => v) / 6)

noncomputable def zeroQuadratic : Quadratic := ⟨0, 0, 0⟩
noncomputable def resonantCubic (c : ℂ) : Cubic := ⟨0, c, 0, 0⟩

/-- The first computed cubic is the actual Taylor cubic of the first
inverse-Jacobian pullback, with quadratic Taylor coefficient zero. -/
def QuadraticPullbackJets : Prop :=
  ∀ (F : ℂ → ℂ) (a b : ℝ) (q : Quadratic) (p : Cubic),
    ContDiffAt ℝ 5 F 0 → 0 < b → SpatialCubicJet F (eigenvalue a b) q p →
    let h := quadraticChange a b q
    let g := cubicAfterQuadratic q p h
    SpatialCubicJet (nonlinearPullback F (fun z => z + h.eval z))
      (eigenvalue a b) zeroQuadratic g

/-- The second pullback has precisely the retained resonant cubic jet. -/
def CubicPullbackJets : Prop :=
  ∀ (F : ℂ → ℂ) (a b : ℝ) (g : Cubic),
    ContDiffAt ℝ 5 F 0 → 0 < b → SpatialCubicJet F (eigenvalue a b) zeroQuadratic g →
    let t := cubicChange a b g
    SpatialCubicJet (nonlinearPullback F (fun z => z + t.eval z))
      (eigenvalue a b) zeroQuadratic (resonantCubic g.c21)

/-- Complete finite homological construction for the original local C⁵ family.
The two vector fields are actual inverse-Jacobian pullbacks. The original
family supplies their Taylor data, rather than an assumed normal form.
Uniform remainder estimates are the separate downstream normal-form obligation. -/
def SourceFiniteElimination : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), ContDiffAt ℝ 5 F (0, 0) → 0 < ω →
    Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) →
    (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) →
    let a := spectralReal F
    let b := spectralImag F
    let S := sourceForwardCLM F
    let T := sourceInverseCLM F
    let q := familyQuadratic F S T
    let p := familyCubic F S T
    let h := fun μ => quadraticChange (a μ) (b μ) (q μ)
    let g := fun μ => cubicAfterQuadratic (q μ) (p μ) (h μ)
    let t := fun μ => cubicChange (a μ) (b μ) (g μ)
    let N := fun μ z => linearNormalizedFamily F S T (μ, z)
    let G := fun μ => nonlinearPullback (N μ) (fun z => z + (h μ).eval z)
    let K := fun μ => nonlinearPullback (G μ) (fun z => z + (t μ).eval z)
    a 0 = 0 ∧ b 0 = ω ∧
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      0 < b μ ∧ ContDiffAt ℝ 4 a μ ∧ ContDiffAt ℝ 4 b μ ∧
      ContDiffAt ℝ 4 S μ ∧ ContDiffAt ℝ 4 T μ ∧
      (∀ z, T μ (S μ z) = z) ∧ (∀ z, S μ (T μ z) = z) ∧
      (∀ z, T μ (linearization F μ (S μ z)) = eigenvalue (a μ) (b μ) * z) ∧
      QuadraticRegular 3 q μ ∧ CubicRegular 2 p μ ∧
      QuadraticRegular 3 h μ ∧ CubicRegular 2 g μ ∧ CubicRegular 2 t μ ∧
      ContDiffAt ℝ 2 (fun ν => (g ν).c21) μ ∧
      JointInverseAt 3 (quadraticFamilyChange h) μ ∧
      JointInverseAt 2 (cubicFamilyChange t) μ ∧
      (∀ j k : ℕ, j + k = 2 → divisor (a μ) (b μ) j k ≠ 0) ∧
      (∀ j k : ℕ, j + k = 3 → (j, k) ≠ (2, 1) → divisor (a μ) (b μ) j k ≠ 0) ∧
      ContDiffAt ℝ 5 (N μ) 0 ∧ ContDiffAt ℝ 5 (G μ) 0 ∧ ContDiffAt ℝ 5 (K μ) 0 ∧
      SpatialCubicJet (N μ) (eigenvalue (a μ) (b μ)) (q μ) (p μ) ∧
      SpatialCubicJet (G μ) (eigenvalue (a μ) (b μ)) zeroQuadratic (g μ) ∧
      SpatialCubicJet (K μ) (eigenvalue (a μ) (b μ)) zeroQuadratic (resonantCubic (g μ).c21)

end Specs.D13Unified.Ch16.CubicHomologicalElimination
