import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PostnikovTower

/-!
HA-D08, notes/002/advanced-homological-algebra.tex:1715–1770.
Ext is the shifted Hom between the actual degree-zero stalks. All categories
are abelian; the localization universe is chosen by HasDerivedCategory, as in
HA-D03. There is no injective or projective resolution hypothesis.
The finite sum below is an iterated binary biproduct over the consecutive
integer degrees a,...,a+n-1, with the empty sum equal to zero.
The conclusion asserts existence of an isomorphism and retains the finite
tower and its attachment maps. It does not specify a canonical splitting:
sections used to split triangles can require choices.
-/
set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open Specs.AdvancedHomologicalAlgebra.DerivedCategory
open Specs.AdvancedHomologicalAlgebra.StandardHeart
open Specs.AdvancedHomologicalAlgebra.PostnikovTower

namespace Specs.AdvancedHomologicalAlgebra.PostnikovSplitting

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The source vanishing condition, with Ext defined intrinsically in D(A). -/
def ExtVanishing (K : D A) : Prop :=
  ∀ i j : ℤ, j < i → ∀ f : (stalk A).obj ((HD A i).obj K) ⟶
    ((stalk A).obj ((HD A j).obj K))⟦i - j + 1⟧, f = 0

/-- A finite direct sum of the cohomology stalks, including the empty sum. -/
noncomputable def cohomologySum (K : D A) (a : ℤ) : ℕ → D A
  | 0 => 0
  | n + 1 => cohomologySum K a n ⊞ (layer A (a + (n : ℤ))).obj K

/-- A splitting for any supplied natural tower at any cohomological bounds.
Every attachment in the finite interval is zero. -/
def splittingAtBoundsType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (K : D A) (a : ℤ) (n : ℕ),
  (∀ i : ℤ, i < a → IsZero ((HD A i).obj K)) →
  (∀ i : ℤ, a + (n : ℤ) ≤ i → IsZero ((HD A i).obj K)) →
  ExtVanishing A K → ∀ T : NaturalTower A,
  Nonempty (K ≅ cohomologySum A K a n) ∧
    ∀ i : ℤ, i ∈ Finset.Ico a (a + (n : ℤ)) → (T.attachment i).app K = 0

/-- The original bounded-cohomology conclusion, with a finite tower and all
its attachments retained. This is existence, with no preferred splitting. -/
def boundedSplittingType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (K : D A),
  (∃ a b : ℤ, (∀ i : ℤ, i < a → IsZero ((HD A i).obj K)) ∧
    (∀ i : ℤ, b < i → IsZero ((HD A i).obj K))) →
  ExtVanishing A K → ∃ (a : ℤ) (n : ℕ), 0 < n ∧
    (∀ i : ℤ, i < a → IsZero ((HD A i).obj K)) ∧
    (∀ i : ℤ, a + (n : ℤ) ≤ i → IsZero ((HD A i).obj K)) ∧
    ∃ T : FiniteTower K a (a + (n : ℤ) - 1),
      (∀ i : ℤ, i ∈ Finset.Icc a (a + (n : ℤ) - 1) →
        (T.naturalTower.attachment i).app K = 0) ∧
      Nonempty (K ≅ cohomologySum A K a n)

end Specs.AdvancedHomologicalAlgebra.PostnikovSplitting
