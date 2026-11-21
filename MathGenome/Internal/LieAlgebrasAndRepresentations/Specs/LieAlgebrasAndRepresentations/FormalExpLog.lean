import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompletedPrimitives
import Mathlib.RingTheory.PowerSeries.Order

/-! Formal exp/log for LA A08 (notes/005, lines 493–557).
The formal parameter is the tensor-degree marker of CompletedPrimitives.
The coefficient of degree n is defined by a finite sum through power n.
On inputs with zero constant coefficient, all further powers vanish in that
coefficient; this is a theorem obligation, rather than an analytic convergence
assumption. There is no dimension restriction on V. -/
noncomputable section
open scoped TensorProduct

namespace LieAlgebrasAndRepresentations.FormalExpLog
open CompletedPrimitives
universe u v

/-- Evaluation of a scalar series, degree by degree. Its intended domain is
series with zero constant term. The formula is total, with a junk value on
other inputs. -/
def seriesEval {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
    (G : Submodule k B) (c : ℕ → k) (p : degreeSeries G) : degreeSeries G :=
  ⟨PowerSeries.mk (fun n => ∑ m ∈ Finset.range (n+1),
      c m • PowerSeries.coeff n (p.val ^ m)), by
    intro n
    rw [PowerSeries.coeff_mk]
    apply Submodule.sum_mem
    intro m _
    exact (G ^ n).smul_mem (c m) ((p ^ m).property n)⟩

/-- The coefficients of exp(X). -/
def expCoefficients (k : Type*) [Field k] (m : ℕ) : k := (m.factorial : k)⁻¹

/-- The coefficients of log(1+X), including its zero constant term. -/
def logCoefficients (k : Type*) [Field k] (m : ℕ) : k :=
  if m = 0 then 0 else (-1 : k) ^ (m+1) / (m : k)

/-- Exponential in any homogeneous degree completion. -/
def exponential {k B : Type*} [Field k] [Ring B] [Algebra k B]
    (G : Submodule k B) (p : degreeSeries G) : degreeSeries G :=
  seriesEval G (expCoefficients k) p

/-- Logarithm in any homogeneous degree completion. Its intended domain has
constant coefficient one. -/
def logarithm {k B : Type*} [Field k] [Ring B] [Algebra k B]
    (G : Submodule k B) (g : degreeSeries G) : degreeSeries G :=
  seriesEval G (logCoefficients k) (g-1)

/-- The two formal inverse identities for a homogeneous completion. This is
an explicit proposition to be proved, never an instance or a certificate
assumed by the definitions of exponential and logarithm. -/
def InverseLaws {k B : Type*} [Field k] [Ring B] [Algebra k B]
    (G : Submodule k B) : Prop :=
  (∀ p : degreeSeries G, PowerSeries.coeff 0 p.val = 0 →
    logarithm G (exponential G p) = p) ∧
  (∀ g : degreeSeries G, PowerSeries.coeff 0 g.val = 1 →
    exponential G (logarithm G g) = g)

/-- The exponential addition identity only requires the two inputs to
commute; the coefficient algebra itself may be noncommutative. -/
def CommutingExpLaws {k B : Type*} [Field k] [Ring B] [Algebra k B]
    (G : Submodule k B) : Prop :=
  ∀ p q : degreeSeries G, PowerSeries.coeff 0 p.val = 0 →
    PowerSeries.coeff 0 q.val = 0 → Commute p q →
    exponential G (p+q) = exponential G p * exponential G q

/-- Group-like in the actual completed total-degree tensor square. The
constant coefficient condition is included explicitly. -/
def IsGroupLike (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (Δ l r : Completion k V →ₐ[k] CompletedSquare k V) (g : Completion k V) : Prop :=
  PowerSeries.coeff 0 g.val = 1 ∧ Δ g = l g * r g

end LieAlgebrasAndRepresentations.FormalExpLog

namespace Specs.LieAlgebrasAndRepresentations.FormalExpLog
open _root_.LieAlgebrasAndRepresentations.CompletedPrimitives
open _root_.LieAlgebrasAndRepresentations.FormalExpLog
universe u v

def expExpectedType : Type (max (u+1) (v+1)) :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V],
    Completion k V → Completion k V

def expExpectedValue : expExpectedType.{u,v} := fun k V _ _ _ _ => exponential (generators k V)

def logExpectedType : Type (max (u+1) (v+1)) :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V],
    Completion k V → Completion k V

def logExpectedValue : logExpectedType.{u,v} := fun k V _ _ _ _ => logarithm (generators k V)

/-- A degree-n coefficient of a positive input's mth power vanishes for m>n.
Every truncation beyond n therefore gives the same scalar-series evaluation. -/
def degreewiseExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    (p : Completion k V), Positive k V p →
      (∀ n m : ℕ, n < m → PowerSeries.coeff n (p.val ^ m) = 0) ∧
      (∀ (c : ℕ → k) (n N : ℕ), n < N →
        PowerSeries.coeff n (seriesEval (generators k V) c p).val =
          ∑ m ∈ Finset.range N, c m • PowerSeries.coeff n (p.val ^ m))

/-- Inverses on the full domains of formal exp and log, before restricting to
primitives and group-like elements. -/
def inverseExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V],
    (∀ p : Completion k V, Positive k V p →
      logarithm (generators k V) (exponential (generators k V) p) = p) ∧
    (∀ g : Completion k V, PowerSeries.coeff 0 g.val = 1 →
      exponential (generators k V) (logarithm (generators k V) g) = g)

/-- The required coproduct identities, using maps with precisely the upstream
coefficient formulas. Quantifying these maps makes the Spec independent of
any implementation, and fixes their values uniquely by coefficient extensionality. -/
def hopfExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    (Δ l r : Completion k V →ₐ[k] CompletedSquare k V),
    (∀ p n, PowerSeries.coeff n (Δ p).val =
      tensorCoproduct k V (PowerSeries.coeff n p.val)) →
    (∀ p n, PowerSeries.coeff n (l p).val = PowerSeries.coeff n p.val ⊗ₜ[k] 1) →
    (∀ p n, PowerSeries.coeff n (r p).val = 1 ⊗ₜ[k] PowerSeries.coeff n p.val) →
    (∀ p, IsCompletedPrimitive k V p →
      IsGroupLike k V Δ l r (exponential (generators k V) p)) ∧
    (∀ g, IsGroupLike k V Δ l r g →
      IsCompletedPrimitive k V (logarithm (generators k V) g))

/-- The full correspondence, with all domain conditions and both inverse laws. -/
def correspondenceExpected : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    (Δ l r : Completion k V →ₐ[k] CompletedSquare k V),
    (∀ p n, PowerSeries.coeff n (Δ p).val =
      tensorCoproduct k V (PowerSeries.coeff n p.val)) →
    (∀ p n, PowerSeries.coeff n (l p).val = PowerSeries.coeff n p.val ⊗ₜ[k] 1) →
    (∀ p n, PowerSeries.coeff n (r p).val = 1 ⊗ₜ[k] PowerSeries.coeff n p.val) →
    ∃ e : {p : Completion k V // Positive k V p ∧ IsCompletedPrimitive k V p} ≃
      {g : Completion k V // IsGroupLike k V Δ l r g},
      (∀ p, (e p).val = exponential (generators k V) p.val) ∧
      (∀ g, (e.symm g).val = logarithm (generators k V) g.val)

end Specs.LieAlgebrasAndRepresentations.FormalExpLog
