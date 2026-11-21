import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Analysis.Analytic.Basic

/-!
Independent statements for the inversion stage of `fa2:p2:spectrum-radius`,
paper.tex 10035–10065. The Banach-algebra predicate is the accepted chapter
convention: complete, nonzero, complex, with submultiplicative norm and ‖1‖ = 1.
The resolvent is (λ1-a)⁻¹ on its resolvent set. AnalyticOnNhd means local
norm-convergent Fréchet power series, with values in the original algebra.
The exterior series uses scalar multiplication by (λ^(n+1))⁻¹, the meaning of
division of an algebra element by a complex scalar.
-/

namespace Specs.ExpandedFA.BanachAlgebra.NeumannResolvent

open Conventions

universe u

def NeumannSeries : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ b : A, ‖b‖ < 1 →
      HasSum (fun n : ℕ => b ^ n) (∑' n : ℕ, b ^ n) ∧
      (1 - b) * (∑' n : ℕ, b ^ n) = 1 ∧
      (∑' n : ℕ, b ^ n) * (1 - b) = 1

def NeumannInvertible : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ b : A, ‖b‖ < 1 → AlgebraInvertibleValue A (1 - b)

def InvertiblesOpen : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    IsOpen {a : A | AlgebraInvertibleValue A a}

def ResolventSetOpen : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A, IsOpen (AlgebraResolventSetValue ℂ A a)

def ResolventIdentity : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (lam mu : ℂ),
      lam ∈ AlgebraResolventSetValue ℂ A a → mu ∈ AlgebraResolventSetValue ℂ A a →
      AlgebraResolventValue ℂ A a lam - AlgebraResolventValue ℂ A a mu =
        (mu - lam) • (AlgebraResolventValue ℂ A a lam * AlgebraResolventValue ℂ A a mu)

def ResolventAnalytic : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A, AnalyticOnNhd ℂ (AlgebraResolventValue ℂ A a) (AlgebraResolventSetValue ℂ A a)

def ExteriorSeries : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ (a : A) (lam : ℂ), ‖a‖ < ‖lam‖ →
      lam ∈ AlgebraResolventSetValue ℂ A a ∧
      HasSum (fun n : ℕ => (lam ^ (n + 1))⁻¹ • a ^ n) (AlgebraResolventValue ℂ A a lam)

end Specs.ExpandedFA.BanachAlgebra.NeumannResolvent
