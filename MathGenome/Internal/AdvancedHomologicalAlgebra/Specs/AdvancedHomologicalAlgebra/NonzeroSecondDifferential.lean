import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PageCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! The explicit example in HA-S05, source lines 607–613.
We use total-degree coordinates `(p,n)`; the two positions are `(0,1)`
and `(2,2)`, hence `(p,q)=(0,1)` and `(2,0)`. -/
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace AdvancedHomologicalAlgebra.SecondDifferentialExample
universe u
variable (k : Type u) [Field k]

/-- The copy of `k` in degrees 1 and 2, and the zero vector space elsewhere. -/
def term (n : ℤ) : Submodule k k := if n = 1 ∨ n = 2 then ⊤ else ⊥

def differential (i j : ℤ) : ModuleCat.of k (term k i) ⟶ ModuleCat.of k (term k j) :=
  if h : i = 1 ∧ j = 2 then
    ModuleCat.ofHom
      { toFun := fun x => ⟨x.val, by simp [term, h.2]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  else 0

/-- The complex `k a → k b`, with `d a = b`. -/
def complex : CochainComplex (ModuleCat.{u} k) ℤ where
  X n := ModuleCat.of k (term k n)
  d := differential k
  shape i j h := by
    dsimp [differential]
    split_ifs with h'
    · exact False.elim (h (by change i + 1 = j; omega))
    · rfl
  d_comp_d' i j l _ _ := by
    dsimp [differential]
    split_ifs <;> simp_all

/-- Filtration degrees of `a` and `b`. The value outside the support is immaterial. -/
def weight (n : ℤ) : ℤ := if n = 2 then 2 else 0

def piece (p n : ℤ) : Subobject ((complex k).X n) :=
  if p ≤ weight n then ⊤ else ⊥

/-- The decreasing filtration assigning degree 0 to `a` and degree 2 to `b`. -/
def filtration : Filtration (complex k) where
  piece := piece k
  decreasing p n := by
    dsimp [piece]
    split_ifs <;> first | exact le_rfl | exact bot_le | omega
  preserved p i j := by
    by_cases hi : p ≤ weight i
    · by_cases hj : p ≤ weight j
      · rw [show piece k p i = ⊤ from ite_eq_left hi,
          show piece k p j = ⊤ from ite_eq_left hj]
        refine ⟨(⊤ : Subobject ((complex k).X i)).arrow ≫ (complex k).d i j ≫
          inv (⊤ : Subobject ((complex k).X j)).arrow, ?_⟩
        simp [Category.assoc]
      · have hd : (complex k).d i j = 0 := by
          change differential k i j = 0
          rw [differential, dite_eq_right]
          intro h
          rcases h with ⟨rfl, rfl⟩
          simp [weight] at hi hj
          omega
        refine ⟨0, ?_⟩
        rw [hd, comp_zero, zero_comp]
    · refine ⟨0, ?_⟩
      change 0 ≫ (piece k p j).arrow = (piece k p i).arrow ≫ _
      rw [show piece k p i = ⊥ from ite_eq_right hi]
      simp

/-- An ambient basis map, usable as a generalized representative. -/
def basis (n : ℤ) (hn : n = 1 ∨ n = 2) : ModuleCat.of k k ⟶ (complex k).X n :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨x, by simp [term, hn]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

open FilteredPage

/-- All computations concern the fixed quotient pages of HA-F03. -/
structure Calculation (D : F03Specs.PageData (filtration k)) where
  aLift : ∀ r : ℤ, 0 ≤ r → r ≤ 2 →
    (ModuleCat.of k k ⟶ (almost (filtration k) r 0 1 : ModuleCat k))
  aLift_arrow : ∀ r hr hs,
    aLift r hr hs ≫ (almost (filtration k) r 0 1).arrow = basis k 1 (by simp)
  bLift : ∀ r : ℤ, 0 ≤ r → r ≤ 2 →
    (ModuleCat.of k k ⟶ (almost (filtration k) r 2 2 : ModuleCat k))
  bLift_arrow : ∀ r hr hs,
    bLift r hr hs ≫ (almost (filtration k) r 2 2).arrow = basis k 2 (by simp)
  aIso : ∀ r : ℤ, 0 ≤ r → r ≤ 2 →
    (ModuleCat.of k k ≅ PageCohomology.object (filtration k) D r 0 1)
  aIso_hom : ∀ r hr hs,
    (aIso r hr hs).hom = aLift r hr hs ≫ toPage (filtration k) r 0 1 (D.containment r 0 1)
  bIso : ∀ r : ℤ, 0 ≤ r → r ≤ 2 →
    (ModuleCat.of k k ≅ PageCohomology.object (filtration k) D r 2 2)
  bIso_hom : ∀ r hr hs,
    (bIso r hr hs).hom = bLift r hr hs ≫ toPage (filtration k) r 2 2 (D.containment r 2 2)
  support : ∀ r : ℤ, 0 ≤ r → r ≤ 2 → ∀ p n : ℤ,
    ¬ ((p = 0 ∧ n = 1) ∨ (p = 2 ∧ n = 2)) →
      IsZero (PageCohomology.object (filtration k) D r p n)
  early_differentials : ∀ r : ℤ, ∀ hr : 0 ≤ r, r ≤ 1 → ∀ p n : ℤ,
    D.differential r hr p n = 0
  second_formula : (aIso 2 (by omega) (by omega)).hom ≫
    D.differential 2 (by omega) 0 1 = (bIso 2 (by omega) (by omega)).hom
  second_isIso : IsIso (D.differential 2 (by omega) 0 1)
  third_page : ∀ p n : ℤ, IsZero (PageCohomology.object (filtration k) D 3 p n)
  acyclic : ∀ n : ℤ, IsZero ((complex k).homology n)
  finite : FiniteFiltrationConvergence.DegreewiseFinite (filtration k)

end AdvancedHomologicalAlgebra.SecondDifferentialExample

namespace AdvancedHomologicalAlgebra.S05ExampleSpecs
universe u
/-- The nonzero second differential example, over every field. -/
def FullStatement : Prop := ∀ (k : Type u) [Field k]
  (D : F03Specs.PageData (SecondDifferentialExample.filtration k)),
    Nonempty (SecondDifferentialExample.Calculation k D)
end AdvancedHomologicalAlgebra.S05ExampleSpecs

