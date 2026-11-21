import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.MinorDivergence
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Compactness

/-! Independent statements of paper.tex, Theorem `thm:weak-minors`.
The index `n` means minor order `n+1`, so order one is included. The
Lp exponent is the actual real quotient p/(n+1). Existence of Lp classes
and their almost-everywhere identification are part of the conclusion. -/
noncomputable section
open MeasureTheory TopologicalSpace Set Filter

namespace VariationalNotes.Sobolev.WeakMinors
open Minors

def minorExponent (p : Exponent) (n : ℕ) (hp : (n+1 : ℕ) ≤ p.real) : Exponent :=
  ⟨p.real / (n+1), (le_div_iff₀ (by positivity)).2 (by simpa using hp)⟩

/-- Representatives converging weakly as genuine vector-valued Lp classes. -/
def HasWeakLpLimit {d : ℕ} (Ω : Opens (Domain d)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (q : Exponent)
    (f : ℕ → Domain d → E) (g : Domain d → E) : Prop :=
  ∃ (F : ℕ → Lp E q.ennreal (domainMeasure Ω))
    (G : Lp E q.ennreal (domainMeasure Ω)),
    (∀ k, (F k : Domain d → E) =ᵐ[domainMeasure Ω] f k) ∧
    ((G : Domain d → E) =ᵐ[domainMeasure Ω] g) ∧
    ∀ ℓ : Lp E q.ennreal (domainMeasure Ω) →L[ℝ] ℝ,
      Tendsto (fun k => ℓ (F k)) atTop (nhds (ℓ G))

/-- Weak convergence of the full vector of minors, on genuine Lp classes.
The representative equations identify both the sequence and its weak limit. -/
def MinorWeakConvergence {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (n : ℕ) (hp : (n+1 : ℕ) ≤ p.real)
    (u : ℕ → W1p Ω m p) (v : W1p Ω m p) : Prop :=
  HasWeakLpLimit Ω (minorExponent p n hp)
    (fun k x => minors (n+1) (gradient Ω m p (u k) x))
    (fun x => minors (n+1) (gradient Ω m p v x))

namespace Expected

/-- Bounded open domains; no boundary regularity or connectedness is needed.
The strict inequality is essential, and no uniform exponent replaces p/j. -/
def WeakContinuity : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : Exponent) (u : ℕ → W1p Ω m p) (v : W1p Ω m p),
      WeaklyConverges u v →
      Tendsto (fun k => value Ω m p (u k)) atTop (nhds (value Ω m p v)) →
      ∀ n : ℕ, ∀ hp : (n+1 : ℕ) < p.real, (n+1) ≤ min m d →
        MinorWeakConvergence n hp.le u v

/-- The order-one assertion follows from weak Sobolev convergence alone. -/
def FirstOrder : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u : ℕ → W1p Ω m p) (v : W1p Ω m p),
    WeaklyConverges u v → MinorWeakConvergence 0 (by simpa using p.one_le) u v

/-- The entire weakly convergent sequence converges strongly in Lp on
a bounded Lipschitz domain, also at p=1. -/
def StrongLipschitz : Prop :=
  ∀ (n : ℕ)
    (e : P102.U4.GraphPieces.Ambient n ≃ₗᵢ[ℝ] Domain (n+1))
    (Ω : Opens (Domain (n+1))),
    P102.Sobolev.Geometry.IsLipschitzOpen
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient n)) →
    ∀ (m : ℕ) (p : Exponent) (u : ℕ → W1p Ω m p) (v : W1p Ω m p),
      WeaklyConverges u v →
      Tendsto (fun k => value Ω m p (u k)) atTop (nhds (value Ω m p v))

/-- One fixed affine zero-boundary class suffices on any bounded open set.
The limit need not be assumed to lie in the affine class. -/
def StrongAffine : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (m : ℕ) (p : Exponent) (u₀ : W1p Ω m p)
      (u : ℕ → W1p Ω m p) (v : W1p Ω m p),
      (∀ k, u k ∈ affineClass Ω m p u₀) → WeaklyConverges u v →
      Tendsto (fun k => value Ω m p (u k)) atTop (nhds (value Ω m p v))

end Expected
end VariationalNotes.Sobolev.WeakMinors
