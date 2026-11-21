import MathGenome.Internal.Specs.D07.Ch07.PrimaryDecomposition
import Mathlib.Data.ZMod.Basic

/-!
Independent statements for K07.07.primary_cyclic_existence, paper.tex:3422–3431.
`ZMod n` is the additive group C_n. Positive exponents exclude trivial cyclic
factors. All products are finite, with the empty product allowed.
-/
namespace Specs.D07.Ch07.PrimaryCyclicExistence

universe u
open Specs.D07.Ch07.PrimaryDecomposition

/-- A finite abelian group of p-power cardinality has only p-power factors. -/
def PGroupDecomposition : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A] (p : ℕ), p.Prime →
    (∃ a : ℕ, Nat.card A = p ^ a) →
    ∃ (r : ℕ) (e : Fin r → ℕ), (∀ i, 0 < e i) ∧
      Nonempty (A ≃+ ((i : Fin r) → ZMod (p ^ e i)))

/-- The elementary-divisor existence statement for an arbitrary finite group. -/
def FiniteCyclicExistence : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A],
    ∃ (r : ℕ) (p e : Fin r → ℕ), (∀ i, (p i).Prime ∧ 0 < e i) ∧
      Nonempty (A ≃+ ((i : Fin r) → ZMod (p i ^ e i)))

/-- The cyclic factors can be chosen separately on the intrinsic primary
components, and their product gives the decomposition of the original group. -/
def CombinedPrimaryCyclicExistence : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A],
    ∃ (r : PrimeDivisors A → ℕ) (e : (p : PrimeDivisors A) → Fin (r p) → ℕ),
      (∀ p i, 0 < e p i) ∧
      (∀ p : PrimeDivisors A,
        Nonempty (Primary A p.val ≃+ ((i : Fin (r p)) → ZMod (p.val ^ e p i)))) ∧
      Nonempty (A ≃+ ((p : PrimeDivisors A) → (i : Fin (r p)) →
        ZMod (p.val ^ e p i)))

/-- For any trivial additive group the decomposition may have no factors. -/
def TrivialEmptyProduct : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Subsingleton A] (p : ℕ), p.Prime →
    Nonempty (A ≃+ ((i : Fin 0) → ZMod (p ^ (1 : ℕ))))

end Specs.D07.Ch07.PrimaryCyclicExistence
