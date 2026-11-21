import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.ArtinRees
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.Nakayama
import Mathlib.Data.ZMod.Basic

/-!
Independent statements for Theorem 7.3 and its warning example,
paper.tex 1198–1202. The global conventions at line 47 make R commutative
and unital, with the zero ring allowed. Finite means finitely generated.
The submodule `⨅ n : ℕ, I ^ n • ⊤` is the intersection inside M of all
IⁿM, including n = 0. The annihilating scalar is uniform over this entire
submodule. The domain conclusion concerns ideals in R itself.
`ZMod 3` is the ring/module of integers modulo 3.
-/

universe u v

namespace P103.Specs.Ch07.KrullIntersection

def stableType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    I • (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) =
      ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)

def annihilatorType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ a ∈ I, ∀ x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)), (1 - a) • x = 0

def jacobson_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    I ≤ Ring.jacobson R → (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) = ⊥

def domain_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (I : Ideal R), I ≠ ⊤ → (⨅ n : ℕ, I ^ n) = ⊥

/-- A proper ideal over a Noetherian domain need not give a zero
intersection on finite modules: (2) acts invertibly on ℤ/3. -/
def integer_counterexampleType : Prop :=
  let I : Ideal ℤ := Ideal.span {(2 : ℤ)}
  I ≠ ⊤ ∧ Module.Finite ℤ (ZMod 3) ∧
    (∀ n : ℕ, I ^ n • (⊤ : Submodule ℤ (ZMod 3)) = ⊤) ∧
    (⨅ n : ℕ, I ^ n • (⊤ : Submodule ℤ (ZMod 3))) = ⊤ ∧
    (⨅ n : ℕ, I ^ n • (⊤ : Submodule ℤ (ZMod 3))) ≠ ⊥

end P103.Specs.Ch07.KrullIntersection
