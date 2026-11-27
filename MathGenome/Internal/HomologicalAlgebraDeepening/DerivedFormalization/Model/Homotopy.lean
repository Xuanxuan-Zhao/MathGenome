import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Homotopy
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.CylinderPath
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

namespace DerivedFormalization.Model

universe v u

open CategoryTheory HomotopicalAlgebra Specs.ModelHomotopy

abbrev LeftHomotopic : homotopyRelationType.{v, u} := leftHomotopicValue

abbrev RightHomotopic : homotopyRelationType.{v, u} := rightHomotopicValue

variable {C : Type u} [Category.{v} C] [ModelCategory C] {A B : C}

theorem leftHomotopic_iff_leftHomotopyRel (f g : A ⟶ B) :
    LeftHomotopic f g ↔ LeftHomotopyRel f g := by
  constructor
  · rintro ⟨P, H, h₀, h₁⟩
    exact ⟨P.val, ⟨⟨H, h₀, h₁⟩⟩⟩
  · intro h
    obtain ⟨P, good, ⟨H⟩⟩ := h.exists_good_cylinder
    exact ⟨⟨P, good⟩, H.h, H.h₀, H.h₁⟩

theorem rightHomotopic_iff_rightHomotopyRel (f g : A ⟶ B) :
    RightHomotopic f g ↔ RightHomotopyRel f g := by
  constructor
  · rintro ⟨P, K, h₀, h₁⟩
    exact ⟨P.val, ⟨⟨K, h₀, h₁⟩⟩⟩
  · intro h
    obtain ⟨P, good, ⟨K⟩⟩ := h.exists_good_pathObject
    exact ⟨⟨P, good⟩, K.h, K.h₀, K.h₁⟩

section

variable [IsCofibrant A] [IsFibrant B]

theorem leftHomotopic_iff_rightHomotopic (f g : A ⟶ B) :
    LeftHomotopic f g ↔ RightHomotopic f g :=
  (leftHomotopic_iff_leftHomotopyRel f g).trans
    (leftHomotopyRel_iff_rightHomotopyRel.trans (rightHomotopic_iff_rightHomotopyRel f g).symm)

theorem homotopyEquivalence (A B : C) [IsCofibrant A] [IsFibrant B] :
    Equivalence (LeftHomotopic (A := A) (B := B)) ∧
      Equivalence (RightHomotopic (A := A) (B := B)) := by
  have left : LeftHomotopic (A := A) (B := B) = LeftHomotopyRel (X := A) (Y := B) :=
    funext fun f => funext fun g => propext (leftHomotopic_iff_leftHomotopyRel f g)
  have right : RightHomotopic (A := A) (B := B) = RightHomotopyRel (X := A) (Y := B) :=
    funext fun f => funext fun g => propext (rightHomotopic_iff_rightHomotopyRel f g)
  rw [left, right]
  exact ⟨LeftHomotopyRel.equivalence A B, RightHomotopyRel.equivalence A B⟩

theorem leftHomotopic_iff_exists_on_cylinder (P : Cylinder A) (f g : A ⟶ B) :
    LeftHomotopic f g ↔
      ∃ H : P.val.I ⟶ B, P.val.i₀ ≫ H = f ∧ P.val.i₁ ≫ H = g := by
  constructor
  · intro h
    let _ : P.val.IsGood := P.property
    let H := ((leftHomotopic_iff_leftHomotopyRel f g).mp h).leftHomotopy P.val
    exact ⟨H.h, H.h₀, H.h₁⟩
  · rintro ⟨H, h₀, h₁⟩
    exact ⟨P, H, h₀, h₁⟩

theorem rightHomotopic_iff_exists_into_pathObject (P : PathObject B) (f g : A ⟶ B) :
    RightHomotopic f g ↔
      ∃ K : A ⟶ P.val.P, K ≫ P.val.p₀ = f ∧ K ≫ P.val.p₁ = g := by
  constructor
  · intro h
    let _ : P.val.IsGood := P.property
    let K := ((rightHomotopic_iff_rightHomotopyRel f g).mp h).rightHomotopy P.val
    exact ⟨K.h, K.h₀, K.h₁⟩
  · rintro ⟨K, h₀, h₁⟩
    exact ⟨P, K, h₀, h₁⟩

end

theorem leftHomotopic_precomp {A' A B : C}
    [IsCofibrant A'] [IsCofibrant A] [IsFibrant B] {f g : A ⟶ B}
    (h : LeftHomotopic f g) (k : A' ⟶ A) : LeftHomotopic (k ≫ f) (k ≫ g) :=
  (leftHomotopic_iff_leftHomotopyRel _ _).mpr
    (((leftHomotopic_iff_leftHomotopyRel f g).mp h).precomp k)

theorem leftHomotopic_postcomp {A B B' : C}
    [IsCofibrant A] [IsFibrant B] [IsFibrant B'] {f g : A ⟶ B}
    (h : LeftHomotopic f g) (k : B ⟶ B') : LeftHomotopic (f ≫ k) (g ≫ k) :=
  (leftHomotopic_iff_leftHomotopyRel _ _).mpr
    (((leftHomotopic_iff_leftHomotopyRel f g).mp h).postcomp k)

theorem leftHomotopic_weakEquivalence_iff [IsCofibrant A] [IsFibrant B]
    {f g : A ⟶ B} (h : LeftHomotopic f g) :
    weakEquivalences C f ↔ weakEquivalences C g := by
  obtain ⟨P, H, h₀, h₁⟩ := h
  let homotopy : P.val.LeftHomotopy f g := ⟨H, h₀, h₁⟩
  simpa only [weakEquivalence_iff] using
    HomotopicalAlgebra.Cylinder.LeftHomotopy.weakEquivalence_iff P.val homotopy

end DerivedFormalization.Model
