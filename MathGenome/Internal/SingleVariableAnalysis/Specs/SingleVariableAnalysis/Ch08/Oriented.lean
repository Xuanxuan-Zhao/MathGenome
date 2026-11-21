import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! K03.08.oriented, paper.tex:2297–2320.
The scalar integral is the existing proper Darboux integral on the compact hull,
with a minus sign for reversed endpoints. Vector values use the canonical
Euclidean spaces, including dimension zero, and are integrated componentwise.
All norm conclusions use the Euclidean norm and the ordered real Darboux
integral on [min a b, max a b]. No measure integral or additional regularity
hypothesis occurs in these statements. -/
namespace Specs.SingleVariableAnalysis.Ch08.Oriented
open Integral

abbrev realIntegrableType := (ℝ → ℝ) → ℝ → ℝ → Prop

def realIntegrableValue : realIntegrableType := fun f a b =>
  Integral.realIntegrableValue f (min a b) (max a b)

abbrev realIntegralType := (f : ℝ → ℝ) → {a b : ℝ} →
  realIntegrableValue f a b → ℝ

noncomputable def realIntegralValue : realIntegralType := fun f {a b} h =>
  if a ≤ b then Integral.realIntegralValue f h else -Integral.realIntegralValue f h

def realAgreement : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (_hab : a ≤ b)
  (h : realIntegrableValue f a b) (ho : Integral.realIntegrableValue f a b),
  realIntegralValue f h = Integral.realIntegralValue f ho

def realSymmetry : Prop := ∀ (f : ℝ → ℝ) (a b : ℝ)
  (h : realIntegrableValue f a b) (hr : realIntegrableValue f b a),
  realIntegralValue f h = -realIntegralValue f hr

def realDegenerate : Prop := ∀ (f : ℝ → ℝ) (a : ℝ),
  ∃ h : realIntegrableValue f a a, realIntegralValue f h = 0

def realAdditivity : Prop := ∀ (f : ℝ → ℝ) (a b c : ℝ)
  (_h : Integral.realIntegrableValue f (min a (min b c)) (max a (max b c))),
  ∃ (hab : realIntegrableValue f a b) (hbc : realIntegrableValue f b c)
    (hac : realIntegrableValue f a c),
    realIntegralValue f hab + realIntegralValue f hbc = realIntegralValue f hac

def realNormEstimate : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}
  (h : realIntegrableValue f a b),
  ∃ hn : Integral.realIntegrableValue (fun x => ‖f x‖) (min a b) (max a b),
    ‖realIntegralValue f h‖ ≤ Integral.realIntegralValue _ hn

abbrev realVectorIntegrableType := (n : ℕ) →
  (ℝ → EuclideanSpace ℝ (Fin n)) → ℝ → ℝ → Prop

def realVectorIntegrableValue : realVectorIntegrableType := fun n f a b =>
  ∀ j : Fin n, realIntegrableValue (fun x => f x j) a b

abbrev realVectorIntegralType := (n : ℕ) → (f : ℝ → EuclideanSpace ℝ (Fin n)) →
  {a b : ℝ} → realVectorIntegrableValue n f a b → EuclideanSpace ℝ (Fin n)

noncomputable def realVectorIntegralValue : realVectorIntegralType := fun _ f {_ _} h =>
  WithLp.toLp 2 (fun j => realIntegralValue (fun x => f x j) (h j))

def realVectorComponents : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n))
  {a b : ℝ} (h : realVectorIntegrableValue n f a b) (j : Fin n),
  realVectorIntegralValue n f h j = realIntegralValue (fun x => f x j) (h j)

def realVectorSymmetry : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n))
  (a b : ℝ) (h : realVectorIntegrableValue n f a b)
  (hr : realVectorIntegrableValue n f b a),
  realVectorIntegralValue n f h = -realVectorIntegralValue n f hr

def realVectorDegenerate : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n))
  (a : ℝ), ∃ h : realVectorIntegrableValue n f a a, realVectorIntegralValue n f h = 0

def realVectorAdditivity : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n))
  (a b c : ℝ)
  (_h : realVectorIntegrableValue n f (min a (min b c)) (max a (max b c))),
  ∃ (hab : realVectorIntegrableValue n f a b)
    (hbc : realVectorIntegrableValue n f b c)
    (hac : realVectorIntegrableValue n f a c),
    realVectorIntegralValue n f hab + realVectorIntegralValue n f hbc =
      realVectorIntegralValue n f hac

def realVectorNormEstimate : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n))
  {a b : ℝ} (h : realVectorIntegrableValue n f a b),
  ∃ hn : Integral.realIntegrableValue (fun x => ‖f x‖) (min a b) (max a b),
    ‖realVectorIntegralValue n f h‖ ≤ Integral.realIntegralValue _ hn

abbrev complexIntegrableType := (ℝ → ℂ) → ℝ → ℝ → Prop

def complexIntegrableValue : complexIntegrableType := fun f a b =>
  Integral.complexIntegrableValue f (min a b) (max a b)

abbrev complexIntegralType := (f : ℝ → ℂ) → {a b : ℝ} →
  complexIntegrableValue f a b → ℂ

noncomputable def complexIntegralValue : complexIntegralType := fun f {a b} h =>
  if a ≤ b then Integral.complexIntegralValue f h else -Integral.complexIntegralValue f h

def complexAgreement : Prop := ∀ (f : ℝ → ℂ) {a b : ℝ} (_hab : a ≤ b)
  (h : complexIntegrableValue f a b) (ho : Integral.complexIntegrableValue f a b),
  complexIntegralValue f h = Integral.complexIntegralValue f ho

def complexSymmetry : Prop := ∀ (f : ℝ → ℂ) (a b : ℝ)
  (h : complexIntegrableValue f a b) (hr : complexIntegrableValue f b a),
  complexIntegralValue f h = -complexIntegralValue f hr

def complexDegenerate : Prop := ∀ (f : ℝ → ℂ) (a : ℝ),
  ∃ h : complexIntegrableValue f a a, complexIntegralValue f h = 0

def complexAdditivity : Prop := ∀ (f : ℝ → ℂ) (a b c : ℝ)
  (_h : Integral.complexIntegrableValue f (min a (min b c)) (max a (max b c))),
  ∃ (hab : complexIntegrableValue f a b) (hbc : complexIntegrableValue f b c)
    (hac : complexIntegrableValue f a c),
    complexIntegralValue f hab + complexIntegralValue f hbc = complexIntegralValue f hac

def complexNormEstimate : Prop := ∀ (f : ℝ → ℂ) {a b : ℝ}
  (h : complexIntegrableValue f a b),
  ∃ hn : Integral.realIntegrableValue (fun x => ‖f x‖) (min a b) (max a b),
    ‖complexIntegralValue f h‖ ≤ Integral.realIntegralValue _ hn

abbrev complexVectorIntegrableType := (n : ℕ) →
  (ℝ → EuclideanSpace ℂ (Fin n)) → ℝ → ℝ → Prop

def complexVectorIntegrableValue : complexVectorIntegrableType := fun n f a b =>
  ∀ j : Fin n, complexIntegrableValue (fun x => f x j) a b

abbrev complexVectorIntegralType := (n : ℕ) → (f : ℝ → EuclideanSpace ℂ (Fin n)) →
  {a b : ℝ} → complexVectorIntegrableValue n f a b → EuclideanSpace ℂ (Fin n)

noncomputable def complexVectorIntegralValue : complexVectorIntegralType := fun _ f {_ _} h =>
  WithLp.toLp 2 (fun j => complexIntegralValue (fun x => f x j) (h j))

def complexVectorComponents : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℂ (Fin n))
  {a b : ℝ} (h : complexVectorIntegrableValue n f a b) (j : Fin n),
  complexVectorIntegralValue n f h j = complexIntegralValue (fun x => f x j) (h j)

def complexVectorSymmetry : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℂ (Fin n))
  (a b : ℝ) (h : complexVectorIntegrableValue n f a b)
  (hr : complexVectorIntegrableValue n f b a),
  complexVectorIntegralValue n f h = -complexVectorIntegralValue n f hr

def complexVectorDegenerate : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℂ (Fin n))
  (a : ℝ), ∃ h : complexVectorIntegrableValue n f a a, complexVectorIntegralValue n f h = 0

def complexVectorAdditivity : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℂ (Fin n))
  (a b c : ℝ)
  (_h : complexVectorIntegrableValue n f (min a (min b c)) (max a (max b c))),
  ∃ (hab : complexVectorIntegrableValue n f a b)
    (hbc : complexVectorIntegrableValue n f b c)
    (hac : complexVectorIntegrableValue n f a c),
    complexVectorIntegralValue n f hab + complexVectorIntegralValue n f hbc =
      complexVectorIntegralValue n f hac

def complexVectorNormEstimate : Prop := ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℂ (Fin n))
  {a b : ℝ} (h : complexVectorIntegrableValue n f a b),
  ∃ hn : Integral.realIntegrableValue (fun x => ‖f x‖) (min a b) (max a b),
    ‖complexVectorIntegralValue n f h‖ ≤ Integral.realIntegralValue _ hn

end Specs.SingleVariableAnalysis.Ch08.Oriented
