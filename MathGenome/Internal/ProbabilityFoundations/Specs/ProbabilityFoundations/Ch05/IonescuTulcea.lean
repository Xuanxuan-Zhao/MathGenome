import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.CylinderFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
Theorem `thm:ionescu-tulcea`, paper.tex §5.1. Coordinate `k` is the
paper's coordinate `k+1`, as fixed by CylinderFramework. The kernels indexed
by `n` below are the paper's `K_{n+2}`. All measurable structures are the
specified product structures. No topological or nonemptiness assumptions occur.
-/

open MeasureTheory ProbabilityTheory
open ProbabilityFoundations.Ch05.CylinderFramework

namespace ProbabilityFoundations.Ch05.IonescuTulcea

universe u
variable (S : ℕ → Type u) [∀ n, MeasurableSpace (S n)]

/-- The unique empty prefix. -/
def emptyPrefix : PrefixSpace S 0 := fun i => False.elim (by simpa using i.2)

/-- Split off the last coordinate of a nonempty prefix. -/
def prefixSplit (n : ℕ) : PrefixSpace S (n+1) ≃ᵐ (PrefixSpace S n × S n) where
  toFun x := (fun i => x ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp i.2; omega)⟩,
    x ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩)
  invFun p i := if h : (i : ℕ) < n then p.1 ⟨i, Finset.mem_range.mpr h⟩
    else cast (congrArg S (show n = (i : ℕ) by have := Finset.mem_range.mp i.2; omega)) p.2
  left_inv x := by
    funext ⟨i, hi⟩
    dsimp
    split_ifs with h
    · rfl
    · have hin : i = n := by have := Finset.mem_range.mp hi; omega
      subst i
      rfl
  right_inv p := by
    ext i
    · dsimp
      rw [dite_eq_left (Finset.mem_range.mp i.2)]
    · dsimp
      simp
  measurable_toFun := by
    exact (Measurable.of_eval (fun _ => measurable_pi_apply _)).prodMk
      (measurable_pi_apply _)
  measurable_invFun := by
    apply Measurable.of_eval
    rintro ⟨i, hi⟩
    dsimp
    split_ifs with h
    · exact (measurable_pi_apply _).comp measurable_fst
    · have hin : i = n := by have := Finset.mem_range.mp hi; omega
      subst i
      exact measurable_snd

/-- Embed the initial state into the one-coordinate prefix. -/
def initialPrefix (x : S 0) : PrefixSpace S 1 :=
  (prefixSplit S 0).symm (emptyPrefix S, x)

/-- Recursion for the nonempty prefix laws: start with the prescribed initial
law, take the kernel-induced product, and glue on the last coordinate. -/
noncomputable def nonemptyPrefixLaw (μ₁ : Measure (S 0))
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1))) :
    (n : ℕ) → Measure (PrefixSpace S (n+1))
  | 0 => μ₁.map (initialPrefix S)
  | n+1 => ((nonemptyPrefixLaw μ₁ K n).compProd (K n)).map
      (prefixSplit S (n+1)).symm

/-- The recursively prescribed laws, including the singleton prefix at length zero. -/
noncomputable def prefixLaw (μ₁ : Measure (S 0))
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1))) :
    (n : ℕ) → Measure (PrefixSpace S n)
  | 0 => Measure.dirac (emptyPrefix S)
  | n+1 => nonemptyPrefixLaw S μ₁ K n

end ProbabilityFoundations.Ch05.IonescuTulcea

namespace Specs.ProbabilityFoundations.Ch05.IonescuTulcea

open _root_.ProbabilityFoundations.Ch05.IonescuTulcea
universe u

def PrefixProbability : Prop :=
  ∀ (S : ℕ → Type u) [∀ n, MeasurableSpace (S n)]
    (μ₁ : Measure (S 0)) [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)], ∀ n, IsProbabilityMeasure (prefixLaw S μ₁ K n)

def PrefixConsistency : Prop :=
  ∀ (S : ℕ → Type u) [∀ n, MeasurableSpace (S n)]
    (μ₁ : Measure (S 0)) [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)], PrefixConsistent S (prefixLaw S μ₁ K)

def CoordinateNonempty : Prop :=
  ∀ (S : ℕ → Type u) [∀ n, MeasurableSpace (S n)]
    (μ₁ : Measure (S 0)) [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)], ∀ n, Nonempty (S n)

/-- Existence and uniqueness on the shared product sigma-algebra, which the upstream
framework identifies with the prefix-cylinder sigma-algebra. The initial marginal
is stated explicitly, as are all recursively prescribed prefix marginals. -/
def Extension : Prop :=
  ∀ (S : ℕ → Type u) [∀ n, MeasurableSpace (S n)]
    (μ₁ : Measure (S 0)) [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)],
    ∃! μ : Measure (ProductSpace S), IsProbabilityMeasure μ ∧
      μ.map (fun x => x 0) = μ₁ ∧
      ∀ n, μ.map (prefixProjection S n) = prefixLaw S μ₁ K n

end Specs.ProbabilityFoundations.Ch05.IonescuTulcea
