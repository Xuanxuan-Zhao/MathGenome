import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.OscillatoryIntegrals
import Mathlib.Order.Filter.Pi
import Mathlib.Algebra.Polynomial.Derivative

/-! Independent statement for paper.tex:2128–2172, general D12.08.06.

A reduced quotient `P/Q` has simple real poles precisely when every real
zero of `Q` has nonzero derivative. The zero rational function is allowed.
Each distinct real pole has its own positive deletion radius, and the
filter is the product of the right-neighborhood filters at zero. The
integrals at the two ends are ordinary one-sided improper integrals.
No integral over a pole is evaluated as a Bochner integral.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D12Complex.PrincipalValues.Definitions

/-- Distinct real denominator roots, in the real coordinate. -/
def realPoles (Q : Polynomial ℂ) : Finset ℝ :=
  (Q.roots.toFinset.filter (fun z => z.im = 0)).image Complex.re

/-- A separate positive radius tends to zero at each pole. -/
def deletionFilter (s : Finset ℝ) : Filter (s → ℝ) :=
  Filter.pi (fun _ => 𝓝[>] (0 : ℝ))

/-- The compact interval with symmetric open intervals about the poles removed.
Endpoint choices do not affect the Lebesgue integral. -/
def deletedSet (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) : Set ℝ :=
  Icc l u \ ⋃ a : s, Ioo (a.val - ε a) (a.val + ε a)

def deletedIntegral (f : ℝ → ℂ) (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ) : ℂ :=
  ∫ x in deletedSet s l u ε, f x

/-- Principal value with independently shrinking symmetric intervals and
ordinary tails. Every pair of splitting points enclosing the poles gives
the same value. Integrability on the actual finite domains is included. -/
def HasPrincipalValue (f : ℝ → ℂ) (s : Finset ℝ) (L : ℂ) : Prop :=
  ∀ l u : ℝ, l < u → (∀ a ∈ s, l < a ∧ a < u) →
    (∀ a : ℝ, a ≤ l → IntervalIntegrable f volume a l) ∧
    (∀ b : ℝ, u ≤ b → IntervalIntegrable f volume u b) ∧
    (∀ ε : s → ℝ, (∀ a, 0 < ε a) → IntegrableOn f (deletedSet s l u ε)) ∧
    ∃ Lminus Lmiddle Lplus : ℂ,
      Tendsto (fun a : ℝ => ∫ x in a..l, f x) atBot (𝓝 Lminus) ∧
      Tendsto (deletedIntegral f s l u) (deletionFilter s) (𝓝 Lmiddle) ∧
      Tendsto (fun b : ℝ => ∫ x in u..b, f x) atTop (𝓝 Lplus) ∧
      Lminus + Lmiddle + Lplus = L

end D12Complex.PrincipalValues.Definitions

namespace Specs.D12Complex.Ch08.PrincipalValues
open _root_.D12Complex _root_.D12Complex.PrincipalValues.Definitions

def realPoles_type := Polynomial ℂ → Finset ℝ
def realPoles_value : realPoles_type := fun Q =>
  (Q.roots.toFinset.filter (fun z => z.im = 0)).image Complex.re

def deletionFilter_type := (s : Finset ℝ) → Filter (s → ℝ)
def deletionFilter_value : deletionFilter_type := fun _s =>
  Filter.pi (fun _ => 𝓝[>] (0 : ℝ))

def deletedSet_type := (s : Finset ℝ) → ℝ → ℝ → (s → ℝ) → Set ℝ
def deletedSet_value : deletedSet_type := fun s l u ε =>
  Icc l u \ ⋃ a : s, Ioo (a.val - ε a) (a.val + ε a)

def deletedIntegral_type := (ℝ → ℂ) → (s : Finset ℝ) → ℝ → ℝ → (s → ℝ) → ℂ
def deletedIntegral_value : deletedIntegral_type := fun f s l u ε =>
  ∫ x in deletedSet s l u ε, f x

def HasPrincipalValue_type := (ℝ → ℂ) → Finset ℝ → ℂ → Prop
def HasPrincipalValue_value : HasPrincipalValue_type := fun f s L =>
  ∀ l u : ℝ, l < u → (∀ a ∈ s, l < a ∧ a < u) →
    (∀ a : ℝ, a ≤ l → IntervalIntegrable f volume a l) ∧
    (∀ b : ℝ, u ≤ b → IntervalIntegrable f volume u b) ∧
    (∀ ε : s → ℝ, (∀ a, 0 < ε a) → IntegrableOn f (deletedSet s l u ε)) ∧
    ∃ Lminus Lmiddle Lplus : ℂ,
      Tendsto (fun a : ℝ => ∫ x in a..l, f x) atBot (𝓝 Lminus) ∧
      Tendsto (deletedIntegral f s l u) (deletionFilter s) (𝓝 Lmiddle) ∧
      Tendsto (fun b : ℝ => ∫ x in u..b, f x) atTop (𝓝 Lplus) ∧
      Lminus + Lmiddle + Lplus = L

/-- Full principal-value identity, including existence in the declared sense. -/
def principal_value_residues_type : Prop :=
  ∀ P Q : Polynomial ℂ, IsCoprime P Q → P.degree < Q.degree →
    (∀ a : ℝ, Q.eval (a : ℂ) = 0 → Q.derivative.eval (a : ℂ) ≠ 0) →
    ∀ c : ℝ, 0 < c →
      HasPrincipalValue (fun x : ℝ =>
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * (P.eval (x : ℂ) / Q.eval (x : ℂ)))
        (realPoles Q)
        ((2 * Real.pi * Complex.I : ℂ) *
            ∑ a ∈ Q.roots.toFinset.filter (fun a => 0 < a.im),
              Residue.residue (fun z => Complex.exp (Complex.I * (c : ℂ) * z) *
                (P.eval z / Q.eval z)) a +
          (Real.pi * Complex.I : ℂ) *
            ∑ a ∈ Q.roots.toFinset.filter (fun a => a.im = 0),
              Residue.residue (fun z => Complex.exp (Complex.I * (c : ℂ) * z) *
                (P.eval z / Q.eval z)) a)

end Specs.D12Complex.Ch08.PrincipalValues
