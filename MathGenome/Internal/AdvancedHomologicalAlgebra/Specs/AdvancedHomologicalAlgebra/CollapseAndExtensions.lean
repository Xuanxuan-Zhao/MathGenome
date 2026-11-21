import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! HA-S04, source lines 538–566. The page indices are filtration degree p
and total degree n, so row q₀ means n-p=q₀. All filtrations and pages are
those of HA-F01–F04 and HA-S01, in an arbitrary abelian category. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace CollapseAndExtensions
open FilteredPage PageCohomology FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)

/-- The canonical stationary transition from the next page to this page.
The equation specifies its value on every generalized representative. -/
structure StationaryStep (r p n : ℤ) where
  iso : object F D (r+1) p n ≅ object F D r p n
  representative_formula : toPage F (r+1) p n (D.containment (r+1) p n) ≫ iso.hom =
    nextRepresentative F D r p n

/-- The whole cohomology object is its sole possible graded piece, with
both the quotient and inclusion fixing the identification. -/
structure TargetIso (p n : ℤ) where
  iso : K.homology n ≅ gradedCohomology F p n
  inclusion_quotient : (cohomologyPiece F p n).arrow ≫ iso.hom =
    cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))

/-- Stability, the canonical comparison to the abutment, and the precise
steps of the target filtration in the single-piece situation. -/
structure CollapseData (s : ℤ) (index : ℤ → ℤ) where
  supported : ∀ r, s ≤ r → ∀ p n, p ≠ index n → IsZero (object F D r p n)
  differential_zero : ∀ r (hr : 0 ≤ r), s ≤ r → ∀ p n, D.differential r hr p n = 0
  stationary : ∀ r, s ≤ r → ∀ p n, Nonempty (StationaryStep F D r p n)
  limit : ∀ p n, Nonempty (LimitIso F D s p n)
  steps_top : ∀ p n, p ≤ index n → cohomologyPiece F p n = ⊤
  steps_bot : ∀ p n, index n < p → cohomologyPiece F p n = ⊥
  target : ∀ n, Nonempty (TargetIso F (index n) n)

/-- The actual successive extension, with the stable page as quotient. -/
def limitSequence (r p n : ℤ) (L : LimitIso F D r p n) : ShortComplex A :=
  ShortComplex.mk (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))
    (cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n)) ≫ L.iso.inv)
    (by rw [← Category.assoc, cokernel.condition, zero_comp])

end CollapseAndExtensions

/-! Explicit maps for the two filtrations in the source example. Their images
are respectively 2(Z/4) and the first direct summand. -/
namespace CollapseExample

def cyclicInjection : ZMod 2 →+ ZMod 4 where
  toFun x := if x = 0 then 0 else 2
  map_zero' := rfl
  map_add' := by decide

def cyclicProjection : ZMod 4 →+ ZMod 2 where
  toFun x := (x.val : ZMod 2)
  map_zero' := rfl
  map_add' := by decide

def splitInjection : ZMod 2 →+ ZMod 2 × ZMod 2 where
  toFun x := (x, 0)
  map_zero' := rfl
  map_add' _ _ := rfl

def splitProjection : ZMod 2 × ZMod 2 →+ ZMod 2 := AddMonoidHom.snd _ _

def splitSection : ZMod 2 →+ ZMod 2 × ZMod 2 where
  toFun x := (0, x)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The two associated graded pieces, with actual quotient groups. -/
def SameGradedPieces : Prop :=
  Nonempty (ZMod 2 ≃+ cyclicInjection.range) ∧
  Nonempty ((ZMod 4 ⧸ cyclicInjection.range) ≃+ ZMod 2) ∧
  Nonempty (ZMod 2 ≃+ splitInjection.range) ∧
  Nonempty (((ZMod 2 × ZMod 2) ⧸ splitInjection.range) ≃+ ZMod 2)

/-- Both subgroups and both quotients are Z/2, but only the second quotient
has an additive section. Exactness identifies these sequences with the
subgroup filtrations and their associated graded pieces. -/
def Statement : Prop :=
  Function.Injective cyclicInjection ∧ Function.Surjective cyclicProjection ∧
  Function.Exact cyclicInjection cyclicProjection ∧
  (∀ x : ZMod 4, x ∈ cyclicInjection.range ↔ ∃ y : ZMod 4, x = 2 • y) ∧
  (∀ x : ZMod 4, x ∉ cyclicInjection.range → addOrderOf x = 4) ∧
  (¬ ∃ t : ZMod 2 →+ ZMod 4, cyclicProjection.comp t = AddMonoidHom.id _) ∧
  Function.Injective splitInjection ∧ Function.Surjective splitProjection ∧
  Function.Exact splitInjection splitProjection ∧
  (∀ x : ZMod 2 × ZMod 2, x ∈ splitInjection.range ↔ x.2 = 0) ∧
  splitProjection.comp splitSection = AddMonoidHom.id _ ∧ SameGradedPieces
end CollapseExample

namespace S04Specs
open CollapseAndExtensions FiniteFiltrationConvergence PageCohomology

def RowCollapse : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), DegreewiseFinite F →
  ∀ (D : F03Specs.PageData F) (s q₀ : ℤ), 2 ≤ s →
    (∀ p n, n-p ≠ q₀ → IsZero (object F D s p n)) →
    Nonempty (CollapseData F D s (fun n => n-q₀))

def ColumnCollapse : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), DegreewiseFinite F →
  ∀ (D : F03Specs.PageData F) (s p₀ : ℤ), 1 ≤ s →
    (∀ p n, p ≠ p₀ → IsZero (object F D s p n)) →
    Nonempty (CollapseData F D s (fun _ => p₀))

def Extensions : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {K : CochainComplex A ℤ} (F : Filtration K), DegreewiseFinite F →
  ∀ (D : F03Specs.PageData F) r p n, 0 ≤ r → Stabilized F r p n →
    ∃ L : LimitIso F D r p n, (limitSequence F D r p n L).ShortExact

/-- The representative-compatible collapsed comparisons are natural for
filtered maps, without imposing new convergence hypotheses. -/
def LimitNaturality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A} (f : FilteredMap X Y)
  (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
  (M : FilteredPageFunctoriality.MapData f D E) s p n
  (L : LimitIso X.filtration D s p n) (L' : LimitIso Y.filtration E s p n),
    M.map s p n ≫ L'.iso.hom = L.iso.hom ≫ gradedCohomologyMap f p n

/-- Naturality of the identification of the whole target with its sole
possible graded piece, by precisely the quotient and inclusion maps. -/
def TargetNaturality : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  {X Y : FilteredComplex A} (f : FilteredMap X Y) p n,
  cohomologyPiece X.filtration p n = ⊤ →
  ∀ (T : TargetIso X.filtration p n) (T' : TargetIso Y.filtration p n),
    HomologicalComplex.homologyMap f.hom n ≫ T'.iso.hom =
      T.iso.hom ≫ gradedCohomologyMap f p n

def FullStatement : Prop := RowCollapse.{v,u} ∧ ColumnCollapse.{v,u} ∧
  Extensions.{v,u} ∧ LimitNaturality.{v,u} ∧ TargetNaturality.{v,u} ∧
  CollapseExample.Statement
end S04Specs
end AdvancedHomologicalAlgebra
