import MathGenome.Internal.Specs.D07.Ch19.SturmTheoremLocalSignVariation
import MathGenome.Internal.Specs.D07.Ch19.CauchyRootBound

/-! Sturm's theorem, paper.tex:5609–5666. All roots counted here are distinct
real roots. Endpoints are excluded. The zero polynomial is excluded in every
root-count theorem; constants are treated separately without constructing a chain. -/
noncomputable section
namespace Specs.D07.Ch19.SturmTheorem
open Polynomial Filter
open SturmTheoremLocalSignVariation
open scoped Classical

/-- The finite set of distinct real roots (used only with a nonzero polynomial). -/
def realRoots (f : Poly) : Finset ℝ := f.roots.toFinset

def rootCount (f : Poly) (a b : ℝ) : ℕ :=
  ((realRoots f).filter (fun x => a < x ∧ x < b)).card

def variationAtTop (L : List Poly) : ℕ :=
  (L.map (fun p => p.leadingCoeff)).signVariations

def variationAtBot (L : List Poly) : ℕ :=
  (L.map (fun p => p.leadingCoeff * (-1 : ℝ) ^ p.natDegree)).signVariations

/-- An arbitrary source Sturm chain, allowing any polynomial with the same
real roots as its squarefree first member. The additive equality also records
that natural subtraction does not truncate. -/
def IntervalCountForChain : Prop :=
  ∀ (f s : Poly) (L : List Poly), f ≠ 0 →
    (∀ x : ℝ, s.eval x = 0 ↔ f.eval x = 0) → IsSturmChain s L →
    ∀ a b : ℝ, a < b → s.eval a ≠ 0 → s.eval b ≠ 0 →
      variation L a = variation L b + rootCount f a b ∧
      rootCount f a b = variation L a - variation L b

/-- Leading coefficient and degree determine every member's eventual sign. -/
def InfinitySigns : Prop :=
  ∀ (L : List Poly), (∀ p ∈ L, p ≠ 0) →
    (∀ᶠ x in atTop, ∀ p ∈ L,
      SignType.sign (p.eval x) = SignType.sign p.leadingCoeff) ∧
    (∀ᶠ x in atBot, ∀ p ∈ L,
      SignType.sign (p.eval x) =
        SignType.sign (p.leadingCoeff * (-1 : ℝ) ^ p.natDegree))

def InfinityVariations : Prop :=
  ∀ (L : List Poly), (∀ p ∈ L, p ≠ 0) →
    (∀ᶠ x in atTop, variation L x = variationAtTop L) ∧
    (∀ᶠ x in atBot, variation L x = variationAtBot L)

def AllRootsCountForChain : Prop :=
  ∀ (f s : Poly) (L : List Poly), f ≠ 0 →
    (∀ x : ℝ, s.eval x = 0 ↔ f.eval x = 0) → IsSturmChain s L →
      variationAtBot L = variationAtTop L + (realRoots f).card ∧
      (realRoots f).card = variationAtBot L - variationAtTop L

/-- Full theorem for the source's s = f/d and its canonical signed remainder
chain, for an arbitrary chosen monic gcd d. -/
def SturmTheorem : Prop :=
  ∀ f : Poly, 0 < f.natDegree → ∀ d : Poly,
    d.Monic → d ∣ f → d ∣ f.derivative →
    (∀ q : Poly, q ∣ f → q ∣ f.derivative → q ∣ d) →
    let s := f / d
    let L := sturmSeq s s.derivative
    (∀ a b : ℝ, a < b → s.eval a ≠ 0 → s.eval b ≠ 0 →
      rootCount f a b = variation L a - variation L b) ∧
    (realRoots f).card = variationAtBot L - variationAtTop L

def ConstantRootCount : Prop :=
  ∀ c : ℝ, c ≠ 0 → (realRoots (C c)).card = 0 ∧
    ∀ a b : ℝ, rootCount (C c) a b = 0

/-- The explicit Cauchy bound also supplies admissible finite endpoints.
Mapping coefficients to C is solely for the previously proved bound. -/
def CauchyEndpoints : Prop :=
  ∀ f : Poly, 0 < f.natDegree →
    let B : ℝ := 1 + (CauchyRootBound.normalizedCoefficientMaximum
      (f.map Complex.ofRealHom) : ℝ)
    ∀ a b : ℝ, a ≤ -B → B ≤ b →
      f.eval a ≠ 0 ∧ f.eval b ≠ 0 ∧ rootCount f a b = (realRoots f).card

end Specs.D07.Ch19.SturmTheorem
