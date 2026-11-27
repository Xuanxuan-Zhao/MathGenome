import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Whitehead
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Homotopy

namespace DerivedFormalization.Model

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra

universe v u

/-- A morphism between cofibrant fibrant objects is a weak equivalence exactly
when it has a two-sided homotopy inverse. -/
theorem whitehead {C : Type u} [Category.{v} C] [FunctorialModelCategory C] {A B : C}
    [IsCofibrant A] [IsFibrant A] [IsCofibrant B] [IsFibrant B] (f : A ⟶ B) :
    weakEquivalences C f ↔
      ∃ g : B ⟶ A, LeftHomotopic (f ≫ g) (𝟙 A) ∧ LeftHomotopic (g ≫ f) (𝟙 B) := by
  constructor
  · intro hf
    have : WeakEquivalence f := (weakEquivalence_iff f).2 hf
    obtain ⟨g, hA, hB⟩ := LeftHomotopyClass.whitehead f
    exact ⟨g, (leftHomotopic_iff_leftHomotopyRel _ _).2 hA,
      (leftHomotopic_iff_leftHomotopyRel _ _).2 hB⟩
  · rintro ⟨g, hgA, hgB⟩
    let factor := factorizationData (cofibrations C) (trivialFibrations C) f
    have : Cofibration factor.i := (cofibration_iff _).2 factor.hi
    have : IsCofibrant factor.Z := isCofibrant_of_cofibration factor.i
    obtain ⟨P, K, h₀, h₁⟩ := (leftHomotopic_iff_rightHomotopic _ _).1 hgA
    have hp₀ := (pathObjectEvaluations P).1
    have : Fibration P.val.p₀ := (fibration_iff _).2 hp₀.1
    have : WeakEquivalence P.val.p₀ := (weakEquivalence_iff _).2 hp₀.2
    -- Lift the homotopy on A to replace p ≫ g by a strict retraction of i.
    have sq : CommSq K factor.i P.val.p₀ (factor.p ≫ g) :=
      ⟨by simpa only [factor.fac_assoc] using h₀⟩
    let r := sq.lift ≫ P.val.p₁
    have hr : factor.i ≫ r = 𝟙 A := by
      dsimp only [r]
      rw [← Category.assoc, sq.fac_left, h₁]
    have hright : RightHomotopic (factor.p ≫ g) r := ⟨P, sq.lift, sq.fac_right, rfl⟩
    have hleft := (leftHomotopic_iff_rightHomotopic _ _).2 hright
    have hpost : LeftHomotopic ((factor.p ≫ g) ≫ f) factor.p := by
      simpa only [Category.assoc, Category.comp_id] using leftHomotopic_precomp hgB factor.p
    have homotopy := (homotopyEquivalence factor.Z B).1
    have hrf : LeftHomotopic (r ≫ f) factor.p :=
      homotopy.trans (homotopy.symm (leftHomotopic_postcomp hleft f)) hpost
    -- Apply two-out-of-three to r ≫ i ≫ p, which is homotopic to p.
    have hri : weakEquivalences C (r ≫ factor.i) := by
      apply of_postcomp (weakEquivalences C) _ factor.p factor.hp.2
      simpa only [Category.assoc, factor.fac] using
        (leftHomotopic_weakEquivalence_iff hrf).2 factor.hp.2
    have retract : RetractArrow factor.i (r ≫ factor.i) :=
      { i := Arrow.homMk factor.i (𝟙 _) (by
          change factor.i ≫ (r ≫ factor.i) = factor.i ≫ 𝟙 factor.Z
          rw [← Category.assoc, hr, Category.id_comp, Category.comp_id])
        r := Arrow.homMk r (𝟙 _) ((Category.comp_id _).symm)
        retract := Arrow.hom_ext _ _ hr (Category.id_comp _) }
    rw [← factor.fac]
    exact (weakEquivalences C).comp_mem _ _ (of_retract retract hri) factor.hp.2

end DerivedFormalization.Model
