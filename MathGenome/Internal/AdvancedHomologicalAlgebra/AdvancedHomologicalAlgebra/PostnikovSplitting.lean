import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.PostnikovSplitting
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.PostnikovTower

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CategoryTheory.Preadditive CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.DerivedCategory
open Specs.AdvancedHomologicalAlgebra.StandardHeart
open Specs.AdvancedHomologicalAlgebra.PostnikovTower
open Specs.AdvancedHomologicalAlgebra.PostnikovSplitting

namespace AdvancedHomologicalAlgebra.PostnikovSplitting
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Translating both sides by i gives precisely the Ext degree i-j+1. -/
lemma layer_hom_vanish (K : D A) (hv : ExtVanishing A K) (i j : ℤ) (hji : j < i)
    (f : (layer A i).obj K ⟶ ((layer A j).obj K)⟦(1 : ℤ)⟧) : f = 0 := by
  let X := (stalk A).obj ((HD A i).obj K)
  let Y := (stalk A).obj ((HD A j).obj K)
  let e₁ : ((layer A i).obj K)⟦i⟧ ≅ X := shiftNegShift X i
  let e₂ : (((layer A j).obj K)⟦(1 : ℤ)⟧)⟦i⟧ ≅ Y⟦i-j+1⟧ :=
    ((shiftFunctorAdd' (D A) (1 : ℤ) i (1+i) rfl).app ((layer A j).obj K)).symm ≪≫
      ((shiftFunctorAdd' (D A) (-j) (1+i) (i-j+1) (by omega)).app Y).symm
  have h := hv i j hji (e₁.inv ≫ f⟦i⟧' ≫ e₂.hom)
  have h' : f⟦i⟧' = 0 := by simpa only [IsIso.comp_left_eq_zero,
    IsIso.comp_right_eq_zero] using h
  exact (Functor.map_eq_zero_iff (shiftFunctor (D A) i)).mp h'

/-- Exactness propagates the layerwise Ext vanishing through a finite tower.
This avoids any assumption of an already chosen splitting. -/
lemma truncation_hom_vanish (K : D A) (hv : ExtVanishing A K) (T : NaturalTower A)
    (a : ℤ) (ha : IsZero (((standardT A).truncLT a).obj K)) (n : ℕ)
    (i : ℤ) (hi : a + (n : ℤ) ≤ i) :
    ∀ f : (layer A i).obj K ⟶ (((standardT A).truncLT (a + (n : ℤ))).obj K)⟦(1 : ℤ)⟧,
      f = 0 := by
  induction n with
  | zero =>
    rw [show a + ((0 : ℕ) : ℤ) = a by omega]
    intro f
    exact (Functor.map_isZero (shiftFunctor (D A) (1 : ℤ)) ha).eq_of_tgt f 0
  | succ n ih =>
    rw [show a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 by omega]
    intro f
    let j := a + (n : ℤ)
    let R := Triangle.mk ((step A j).app K) ((T.projection j).app K)
      ((T.attachment j).app K)
    let S := (CategoryTheory.shiftFunctor (Triangle (D A)) (1 : ℤ)).obj R
    have hR : R ∈ distTriang (D A) := T.distinguished j K
    have hS : S ∈ distTriang (D A) := R.shift_distinguished hR 1
    have hj : j < i := by dsimp [j]; omega
    have hz : f ≫ S.mor₂ = 0 := layer_hom_vanish A K hv i j hj _
    obtain ⟨g, hg⟩ := S.coyoneda_exact₂ hS f hz
    have hg0 : g = 0 := ih (by omega) g
    rw [hg, hg0, zero_comp]

/-- Every attachment above a lower cohomological bound vanishes. -/
lemma attachment_eq_zero (K : D A) (hv : ExtVanishing A K) (T : NaturalTower A)
    (a : ℤ) (ha : IsZero (((standardT A).truncLT a).obj K))
    (i : ℤ) (hi : a ≤ i) : (T.attachment i).app K = 0 := by
  have he : a + ((i-a).toNat : ℤ) = i := by rw [Int.toNat_of_nonneg (by omega)]; omega
  have h := truncation_hom_vanish A K hv T a ha (i-a).toNat i (by omega)
  rw [he] at h
  exact h ((T.attachment i).app K)

/-- Splitting successive triangles produces an iterated finite biproduct. -/
lemma truncation_splits (K : D A) (hv : ExtVanishing A K) (T : NaturalTower A)
    (a : ℤ) (ha : IsZero (((standardT A).truncLT a).obj K)) (n : ℕ) :
    Nonempty ((((standardT A).truncLT (a + (n : ℤ))).obj K) ≅
      cohomologySum A K a n) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, add_zero, cohomologySum] using
      Nonempty.intro ha.isoZero
  | succ n ih =>
    obtain ⟨e⟩ := ih
    let j := a + (n : ℤ)
    let R := Triangle.mk ((step A j).app K) ((T.projection j).app K)
      ((T.attachment j).app K)
    obtain ⟨e', _, _⟩ := exists_iso_binaryBiproduct_of_distTriang R
      (T.distinguished j K) (attachment_eq_zero A K hv T a ha j (by dsimp [j]; omega))
    refine ⟨?_⟩
    simpa only [R, Triangle.mk_obj₂, Triangle.mk_obj₁, Triangle.mk_obj₃,
      stage, j, cohomologySum, Int.natCast_add, Int.natCast_one, add_assoc] using
      e' ≪≫ biprod.mapIso e (Iso.refl ((layer A j).obj K))

/-- Existence at specified bounds, including the empty interval. -/
theorem splittingAtBounds : splittingAtBoundsType := by
  intro A _ _ _ K a n ha hb hv T
  have hGE : (standardT A).IsGE K a := (_root_.DerivedCategory.isGE_iff K a).mpr ha
  have hz : IsZero (((standardT A).truncLT a).obj K) :=
    (standardT A).isZero_truncLT_obj_of_isGE a K
  have hLE : (standardT A).IsLE K (a + (n : ℤ) - 1) :=
    (_root_.DerivedCategory.isLE_iff K _).mpr (fun i hi => hb i (by omega))
  have ht : IsIso (((standardT A).truncLTι (a + (n : ℤ))).app K) :=
    ((standardT A).isLE_iff_isIso_truncLTι_app (a + (n : ℤ) - 1)
      (a + (n : ℤ)) (by omega) K).mp hLE
  obtain ⟨e⟩ := truncation_splits A K hv T a hz n
  refine ⟨⟨(asIso (((standardT A).truncLTι (a + (n : ℤ))).app K)).symm ≪≫ e⟩, ?_⟩
  intro i hi
  exact attachment_eq_zero A K hv T a hz i (Finset.mem_Ico.mp hi).1

/-- A bounded object is a finite direct sum of its cohomology stalks.
Only existence is asserted: no sections or splitting isomorphism are selected
naturally or canonically. The original tower and its attachments are retained. -/
theorem boundedSplitting : boundedSplittingType := by
  intro A _ _ _ K hK hv
  obtain ⟨a, b, ha, hb⟩ := hK
  let n := (max a b - a + 1).toNat
  have hn : (n : ℤ) = max a b - a + 1 := Int.toNat_of_nonneg (by omega)
  have hnpos : 0 < n := by omega
  have hb' : ∀ i : ℤ, a + (n : ℤ) ≤ i → IsZero ((HD A i).obj K) :=
    fun i hi => hb i (by omega)
  obtain ⟨T⟩ := AdvancedHomologicalAlgebra.PostnikovTower.finiteTower A K a
    (a + (n : ℤ) - 1) (by omega) ha (fun i hi => hb' i (by omega))
  obtain ⟨he, hδ⟩ := splittingAtBounds A K a n ha hb' hv T.naturalTower
  refine ⟨a, n, hnpos, ha, hb', T, ?_, he⟩
  intro i hi
  exact hδ i (by have := Finset.mem_Icc.mp hi; exact Finset.mem_Ico.mpr ⟨this.1, by omega⟩)

end AdvancedHomologicalAlgebra.PostnikovSplitting
