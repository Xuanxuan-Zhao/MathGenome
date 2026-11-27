import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Brown
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

open CategoryTheory HomotopicalAlgebra

universe v₁ u₁ v₂ u₂

namespace DerivedFormalization.Model

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D]

/-- A functor on cofibrant objects that sends trivial cofibrations to `W`
sends all weak equivalences to `W` when `W` satisfies two-out-of-three. -/
theorem brown_cofibrant (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty]
    (F : CofibrantObject C ⥤ D)
    (hF : ∀ ⦃X Y : CofibrantObject C⦄ (f : X ⟶ Y),
      trivialCofibrations C (CofibrantObject.ι.map f) → W (F.map f))
    ⦃X Y : CofibrantObject C⦄ (f : X ⟶ Y)
    (hf : weakEquivalences C (CofibrantObject.ι.map f)) : W (F.map f) := by
  have : WeakEquivalence f.hom := ⟨hf⟩
  obtain ⟨h⟩ := (inferInstance : Nonempty (CofibrantBrownFactorization f.hom))
  let Z : CofibrantObject C := ⟨h.Z, isCofibrant_of_cofibration h.i⟩
  let i : X ⟶ Z := ObjectProperty.homMk h.i
  let p : Z ⟶ Y := ObjectProperty.homMk h.p
  let s : Y ⟶ Z := ObjectProperty.homMk h.s
  have fac : i ≫ p = f := ObjectProperty.hom_ext _ h.fac
  have section_comp : s ≫ p = 𝟙 Y := ObjectProperty.hom_ext _ h.s_p
  have hs : W (F.map s) := hF s (mem_trivialCofibrations h.s)
  have hp : W (F.map p) := W.of_precomp (F.map s) (F.map p) hs (by
    rw [← F.map_comp, section_comp]
    exact hF (𝟙 Y) (mem_trivialCofibrations (𝟙 Y.obj)))
  rw [← fac, F.map_comp]
  exact W.comp_mem _ _ (hF i (mem_trivialCofibrations h.i)) hp

/-- A functor on fibrant objects that sends trivial fibrations to `W`
sends all weak equivalences to `W` when `W` satisfies two-out-of-three. -/
theorem brown_fibrant (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty]
    (F : FibrantObject C ⥤ D)
    (hF : ∀ ⦃X Y : FibrantObject C⦄ (f : X ⟶ Y),
      trivialFibrations C (FibrantObject.ι.map f) → W (F.map f))
    ⦃X Y : FibrantObject C⦄ (f : X ⟶ Y)
    (hf : weakEquivalences C (FibrantObject.ι.map f)) : W (F.map f) := by
  have : WeakEquivalence f.hom := ⟨hf⟩
  obtain ⟨h⟩ := (inferInstance : Nonempty (FibrantBrownFactorization f.hom))
  let Z : FibrantObject C := ⟨h.Z, isFibrant_of_fibration h.p⟩
  let i : X ⟶ Z := ObjectProperty.homMk h.i
  let p : Z ⟶ Y := ObjectProperty.homMk h.p
  let r : Z ⟶ X := ObjectProperty.homMk h.r
  have fac : i ≫ p = f := ObjectProperty.hom_ext _ h.fac
  have comp_retraction : i ≫ r = 𝟙 X := ObjectProperty.hom_ext _ h.i_r
  have hr : W (F.map r) := hF r (mem_trivialFibrations h.r)
  have hi : W (F.map i) := W.of_postcomp (F.map i) (F.map r) hr (by
    rw [← F.map_comp, comp_retraction]
    exact hF (𝟙 X) (mem_trivialFibrations (𝟙 X.obj)))
  rw [← fac, F.map_comp]
  exact W.comp_mem _ _ hi (hF p (mem_trivialFibrations h.p))

end DerivedFormalization.Model
