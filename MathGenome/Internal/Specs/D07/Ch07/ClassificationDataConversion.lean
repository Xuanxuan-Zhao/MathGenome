import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.ZMod.Basic

/-!
The normalized finite data in paper.tex, Proposition `prop:abelian-data-conversion`.
An elementary datum is a finitely supported family of multisets of positive
exponents, indexed by the actual natural prime. Multiplicity and prime labels
are retained. Invariant factors are actual natural numbers in increasing
order of divisibility, with factors of order one excluded. Empty data are allowed.
-/
namespace D07.Ch07.ClassificationDataConversion

abbrev ElementaryData := ℕ →₀ Multiset ℕ

def IsElementary (E : ElementaryData) : Prop :=
  ∀ p, ∀ e ∈ E p, Nat.Prime p ∧ 0 < e

def IsInvariant (d : List ℕ) : Prop :=
  (∀ n ∈ d, 2 ≤ n) ∧ d.Pairwise (· ∣ ·)

/-- Sort each prime's positive exponents increasingly. -/
noncomputable def row (E : ElementaryData) (p : ℕ) : List ℕ :=
  (E p).sort (· ≤ ·)

/-- The common maximum length, zero for empty data. -/
def width (E : ElementaryData) : ℕ :=
  E.support.sup fun p => (E p).card

/-- Left zero padding. -/
def pad (r : ℕ) (l : List ℕ) : List ℕ :=
  List.replicate (r - l.length) 0 ++ l

noncomputable def exponent (E : ElementaryData) (p i : ℕ) : ℕ :=
  (pad (width E) (row E p)).getD i 0

/-- The finite prime-exponent vector of one column. -/
noncomputable def column (E : ElementaryData) (i : ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset E.support (fun p => exponent E p i) (by
    intro p hp
    by_contra h
    have hz : E p = 0 := Finsupp.notMem_support_iff.mp h
    simp [exponent, row, hz, pad, List.getD_eq_getElem?_getD] at hp)

/-- Multiply the prime powers columnwise, at the maximum row length. -/
noncomputable def recombine (E : ElementaryData) : List ℕ :=
  (List.range (width E)).map fun i => (column E i).prod (· ^ ·)

/-- Split every factor by unique prime factorization and discard exponent zero. -/
noncomputable def split (d : List ℕ) : ElementaryData :=
  d.foldr (fun n E => n.factorization.mapRange
    (fun e => if e = 0 then 0 else ({e} : Multiset ℕ)) (by simp) + E) 0

/-- Products of cyclic groups represented by the two kinds of data. -/
abbrev InvariantGroup (d : List ℕ) := (i : Fin d.length) → ZMod (d.getD i 1)
abbrev ElementaryGroup (E : ElementaryData) :=
  (p : E.support) → (j : Fin (row E p.val).length) →
    ZMod (p.val ^ (row E p.val).getD j 0)

namespace Specs

def SplitNormalized : Prop := ∀ d, IsInvariant d → IsElementary (split d)
def RecombineNormalized : Prop := ∀ E, IsElementary E → IsInvariant (recombine E)
def SplitRecombine : Prop := ∀ E, IsElementary E → split (recombine E) = E
def RecombineSplit : Prop := ∀ d, IsInvariant d → recombine (split d) = d

/-- The displayed algorithm really computes the prime valuations. -/
def ColumnValuations : Prop := ∀ E, IsElementary E → ∀ i, i < width E → ∀ p,
  ((recombine E).getD i 1).factorization p = exponent E p i

/-- Padding the extracted positive valuations recovers the original row. -/
def RecoverRows : Prop := ∀ d, IsInvariant d → ∀ p,
  pad d.length (row (split d) p) = d.map (fun n => n.factorization p)

def Boundaries : Prop := split [] = 0 ∧ recombine 0 = []

/-- Each column is the same cyclic group as its pairwise coprime prime powers.
The zero exponents here give only trivial cyclic factors. -/
def ColumnCRT : Prop := ∀ E, IsElementary E → ∀ i,
  Nonempty (ZMod ((column E i).prod (· ^ ·)) ≃+
    ((p : E.support) → ZMod (p.val ^ exponent E p.val i)))

def GroupPreservation : Prop := ∀ E, IsElementary E →
  Nonempty (InvariantGroup (recombine E) ≃+ ElementaryGroup E)

def SplitGroupPreservation : Prop := ∀ d, IsInvariant d →
  Nonempty (InvariantGroup d ≃+ ElementaryGroup (split d))

/-- Equivalence of the two spaces of normalized data, with these very maps. -/
def NormalizedDataEquivalence : Prop :=
  ∃ e : {d : List ℕ // IsInvariant d} ≃ {E : ElementaryData // IsElementary E},
    (∀ d, (e d).val = split d.val) ∧
    (∀ E, (e.symm E).val = recombine E.val)

end Specs
end D07.Ch07.ClassificationDataConversion
