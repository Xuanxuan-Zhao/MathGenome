import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup

/-! K03.19.orthogonality, paper.tex:4688–4706.
The pairing acts on actual functions, using the proper componentwise Darboux
integral. Its witness is a proof of integrability, not a regularity assumption.
No quotient by functions of zero integral norm or definiteness is imposed.
Positive real indices include the diagonal square means and every distinct-index
case. The mixed formula and single-mode means also include zero/negative indices.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Orthogonality
open Ch08.Integral PeriodicSetup

abbrev pairingType := (f g : ℝ → ℂ) →
  complexIntegrableValue (fun x => f x * star (g x)) (-Real.pi) Real.pi → ℂ

def pairingValue : pairingType := fun f g h =>
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    complexIntegralValue (fun x => f x * star (g x)) h

abbrev realMeanType := (f : ℝ → ℝ) →
  realIntegrableValue f (-Real.pi) Real.pi → ℝ

def realMeanValue : realMeanType := fun f h =>
  (1 / (2 * Real.pi)) * realIntegralValue f h

def pairingIntegrability : Prop := ∀ (f g : ℝ → ℂ),
  complexIntegrableValue f (-Real.pi) Real.pi →
  complexIntegrableValue g (-Real.pi) Real.pi →
  complexIntegrableValue (fun x => f x * star (g x)) (-Real.pi) Real.pi

def modeIntegrability : Prop := ∀ n : ℤ,
  complexIntegrableValue (modeValue n) (-Real.pi) Real.pi

def modeOrthogonality : Prop := ∀ (n m : ℤ)
  (h : complexIntegrableValue (fun x => modeValue n x * star (modeValue m x))
    (-Real.pi) Real.pi),
  pairingValue (modeValue n) (modeValue m) h = if n = m then 1 else 0

def realProductIntegrability : Prop := ∀ n m : ℤ,
  realIntegrableValue (fun x => Real.cos ((n : ℝ) * x) * Real.cos ((m : ℝ) * x))
    (-Real.pi) Real.pi ∧
  realIntegrableValue (fun x => Real.sin ((n : ℝ) * x) * Real.sin ((m : ℝ) * x))
    (-Real.pi) Real.pi ∧
  realIntegrableValue (fun x => Real.sin ((n : ℝ) * x) * Real.cos ((m : ℝ) * x))
    (-Real.pi) Real.pi

def cosineMean : Prop := ∀ (n : ℤ)
  (h : realIntegrableValue (fun x => Real.cos ((n : ℝ) * x)) (-Real.pi) Real.pi),
  realMeanValue _ h = if n = 0 then 1 else 0

def sineMean : Prop := ∀ (n : ℤ)
  (h : realIntegrableValue (fun x => Real.sin ((n : ℝ) * x)) (-Real.pi) Real.pi),
  realMeanValue _ h = 0

def cosineOrthogonality : Prop := ∀ (n m : ℕ+)
  (h : realIntegrableValue (fun x => Real.cos ((n : ℝ) * x) * Real.cos ((m : ℝ) * x))
    (-Real.pi) Real.pi),
  realMeanValue _ h = if n = m then 1 / 2 else 0

def sineOrthogonality : Prop := ∀ (n m : ℕ+)
  (h : realIntegrableValue (fun x => Real.sin ((n : ℝ) * x) * Real.sin ((m : ℝ) * x))
    (-Real.pi) Real.pi),
  realMeanValue _ h = if n = m then 1 / 2 else 0

def mixedOrthogonality : Prop := ∀ (n m : ℤ)
  (h : realIntegrableValue (fun x => Real.sin ((n : ℝ) * x) * Real.cos ((m : ℝ) * x))
    (-Real.pi) Real.pi),
  realMeanValue _ h = 0

end Specs.SingleVariableAnalysis.Ch19.Orthogonality
