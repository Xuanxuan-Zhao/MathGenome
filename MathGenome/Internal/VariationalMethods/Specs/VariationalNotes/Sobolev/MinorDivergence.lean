import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Minors
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Independent statements for paper.tex:4013–4048.  Ambient representatives
are used only on the given open set; no extension regularity is required.
Order `n+1` includes the constant cofactor at order one. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped BigOperators ContDiff

namespace VariationalNotes.Sobolev.MinorDivergence
open Minors

/-- The classical matrix, in the same (target,domain) order as the weak gradient. -/
def classicalGradient {d m : ℕ} (u : Domain d → Vector m) (x : Domain d) :
    Gradient m d :=
  WithLp.toLp 2 (fun ij =>
    fderiv ℝ (fun y => u y ij.1) x (P102.U4.coordinateVector d ij.2))

/-- The actual representative of a minor of the canonical weak gradient. -/
def minorField {d m n : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (a : Index m d (n+1)) (u : W1p Ω m p) (x : Domain d) : ℝ :=
  minor a (gradient Ω m p u x)

/-- Ordinary pointwise multiplication of the value and cofactor representatives. -/
def fluxField {d m n : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (a : Index m d (n+1)) (u : W1p Ω m p) (l : Fin (n+1)) (x : Domain d) : ℝ :=
  value Ω m p u x (a.1.val 0) * cofactor a l (gradient Ω m p u x)

/-- The regular distributions here are required to have locally integrable
representatives, so the equality expresses the usual distributional identity. -/
def WeakIdentity {d m n : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (a : Index m d (n+1)) (u : W1p Ω m p) : Prop :=
  LocallyIntegrableOn (minorField a u) Ω volume ∧
  (∀ l, LocallyIntegrableOn (fluxField a u l) Ω volume) ∧
  P102.U4.regularDistribution Ω (minorField a u) =
    ∑ l : Fin (n+1), P102.U4.distributionPartial {a.2.val l}
      (P102.U4.regularDistribution Ω (fluxField a u l))

namespace Expected

/-- The smooth Piola cancellation, including order one. -/
def SmoothCofactorDivergence : Prop :=
  ∀ {d m n : ℕ} (Ω : Opens (Domain d)) (a : Index m d (n+1))
    (u : Domain d → Vector m), ContDiffOn ℝ (⊤ : ℕ∞) u Ω →
    ∀ x ∈ Ω, (∑ l : Fin (n+1),
      fderiv ℝ (fun y => cofactor a l (classicalGradient u y)) x
        (P102.U4.coordinateVector d (a.2.val l))) = 0

/-- The smooth divergence formula for the minor itself. -/
def SmoothMinorDivergence : Prop :=
  ∀ {d m n : ℕ} (Ω : Opens (Domain d)) (a : Index m d (n+1))
    (u : Domain d → Vector m), ContDiffOn ℝ (⊤ : ℕ∞) u Ω →
    ∀ x ∈ Ω, minor a (classicalGradient u x) =
      ∑ l : Fin (n+1), fderiv ℝ
        (fun y => u y (a.1.val 0) * cofactor a l (classicalGradient u y)) x
        (P102.U4.coordinateVector d (a.2.val l))

/-- The chapter's bounded open sets, with no boundary regularity assumptions,
and the closed endpoint p=j. The existence of `a` ensures j≤min(m,d). -/
def SobolevMinorDivergence : Prop :=
  ∀ {d m n : ℕ} (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : Exponent), (n+1 : ℕ) ≤ p.real →
    ∀ (a : Index m d (n+1)) (u : W1p Ω m p), WeakIdentity a u

/-- Smooth approximation of both actual fields in the canonical Sobolev model. -/
def SmoothApproximation : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (u : W1p Ω m p),
    ∃ (f : ℕ → Domain d → Vector m) (v : ℕ → W1p Ω m p),
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) Ω ∧
        (value Ω m p (v n) : Domain d → Vector m) =ᵐ[domainMeasure Ω] f n ∧
        (gradient Ω m p (v n) : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
          classicalGradient (f n)) ∧
      Filter.Tendsto v Filter.atTop (nhds u)

/-- A separately checkable integrability part of the weak assertion. -/
def FieldsIntegrable : Prop :=
  ∀ {d m n : ℕ} (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : Exponent), (n+1 : ℕ) ≤ p.real →
    ∀ (a : Index m d (n+1)) (u : W1p Ω m p),
      Integrable (minorField a u) (domainMeasure Ω) ∧
      ∀ l, Integrable (fluxField a u l) (domainMeasure Ω)

/-- The product-rule reduction, without asserting Piola cancellation as an axiom. -/
def SmoothMinorFromPiola : Prop := SmoothCofactorDivergence → SmoothMinorDivergence

/-- Explicit endpoint/base cases for incremental verification. -/
def SmoothCofactorOne : Prop :=
  ∀ {d m : ℕ} (a : Index m d 1) (u : Domain d → Vector m) (x : Domain d),
    (∑ l : Fin 1, fderiv ℝ (fun y => cofactor a l (classicalGradient u y)) x
      (P102.U4.coordinateVector d (a.2.val l))) = 0

def SmoothMinorOne : Prop :=
  ∀ {d m : ℕ} (a : Index m d 1) (u : Domain d → Vector m) (x : Domain d),
    minor a (classicalGradient u x) =
      ∑ l : Fin 1, fderiv ℝ
        (fun y => u y (a.1.val 0) * cofactor a l (classicalGradient u y)) x
        (P102.U4.coordinateVector d (a.2.val l))

def SobolevMinorOne : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (a : Index m d 1) (u : W1p Ω m p), WeakIdentity a u

end Expected
end VariationalNotes.Sobolev.MinorDivergence
