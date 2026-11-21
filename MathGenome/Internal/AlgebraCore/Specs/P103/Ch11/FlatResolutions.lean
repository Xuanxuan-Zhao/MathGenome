import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests

/-!
Computation from ordinary flat resolutions, paper.tex 2676–2706.
The exact augmented resolutions are the shared `LeftResolution` data, over
the opposite ring for the right variable. Flatness is tested in a universe
large enough for both coefficient modules and the terms of both resolutions.
No condition is imposed on the ring beyond `Ring`.

The target is stated relative to every projective model of Tor, rather than
one chosen model. Naturality includes changes of that projective model.
-/
namespace P103.Specs.Ch11.FlatResolutions
open CategoryTheory
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

/-- Termwise flatness on the right, in the original tensor orientation. -/
def IsRightFlat {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F : LeftResolution Rᵐᵒᵖ A) : Prop :=
  ∀ p, P103.Specs.Ch02.FlatnessTests.RightFlat.{u,max u v,max u v w}
    R (F.complex.X p)

/-- Termwise flatness on the left. -/
def IsLeftFlat {B : Type w} [AddCommGroup B] [Module R B]
    (G : LeftResolution R B) : Prop :=
  ∀ q, P103.Specs.Ch02.FlatnessTests.Flat.{u,max u w,max u v w}
    R (G.complex.X q)

/-- The canonical right-resolution identification in one arbitrary degree.
The normalization specifies its value on every projective comparison over
the identity, including comparisons into nonprojective flat resolutions. -/
structure RightComputations (R : Type u) [Ring R] (n : ℕ) where
  iso : ∀ {A : ModuleCat.{v} Rᵐᵒᵖ}
    (F : LeftResolution Rᵐᵒᵖ A), IsRightFlat.{u,v,w} F →
    (P : ProjectiveChoice Rᵐᵒᵖ A) → (B : ModuleCat.{w} R) →
    Homology (tensorComplex F.complex B) n ≃ₗ[ℤ] TorWith P.val B n
  naturality : ∀ {A A' : ModuleCat.{v} Rᵐᵒᵖ} {B B' : ModuleCat.{w} R}
    (F : LeftResolution Rᵐᵒᵖ A) (F' : LeftResolution Rᵐᵒᵖ A')
    (hF : IsRightFlat.{u,v,w} F) (hF' : IsRightFlat.{u,v,w} F')
    (P : ProjectiveChoice Rᵐᵒᵖ A) (P' : ProjectiveChoice Rᵐᵒᵖ A')
    (f : A ⟶ A') (g : B ⟶ B') (l : F.complex ⟶ F'.complex)
    (k : P.val.complex ⟶ P'.val.complex),
    ChainLift F F' f.hom l → ChainLift P.val P'.val f.hom k →
    ∀ x, iso F' hF' P' B'
      (homologyMap (tensorFirstMap l B ≫ tensorSecondMap F'.complex g.hom) n x) =
      homologyMap (tensorFirstMap k B ≫ tensorSecondMap P'.val.complex g.hom) n
        (iso F hF P B x)
  normalization : ∀ {A : ModuleCat.{v} Rᵐᵒᵖ}
    (F : LeftResolution Rᵐᵒᵖ A) (hF : IsRightFlat.{u,v,w} F)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (B : ModuleCat.{w} R)
    (l : P.val.complex ⟶ F.complex),
    ChainLift P.val F LinearMap.id l →
    ∀ x, iso F hF P B (homologyMap (tensorFirstMap l B) n x) = x

/-- The left-resolution identification. Its normalization is the usual
balanced identification on projective left resolutions, specified using
the actual augmentation maps, with no arbitrary homology automorphism.
Naturality then gives compatibility with every projective comparison Q→G.
-/
structure LeftComputations (R : Type u) [Ring R] (n : ℕ) where
  iso : ∀ {B : ModuleCat.{w} R}
    (G : LeftResolution R B), IsLeftFlat.{u,v,w} G →
    {A : ModuleCat.{v} Rᵐᵒᵖ} → (P : ProjectiveChoice Rᵐᵒᵖ A) →
    Homology (leftOrdinaryTensorComplex A G.complex) n ≃ₗ[ℤ] TorWith P.val B n
  naturality : ∀ {A A' : ModuleCat.{v} Rᵐᵒᵖ} {B B' : ModuleCat.{w} R}
    (G : LeftResolution R B) (G' : LeftResolution R B')
    (hG : IsLeftFlat.{u,v,w} G) (hG' : IsLeftFlat.{u,v,w} G')
    (P : ProjectiveChoice Rᵐᵒᵖ A) (P' : ProjectiveChoice Rᵐᵒᵖ A')
    (f : A ⟶ A') (g : B ⟶ B') (l : G.complex ⟶ G'.complex)
    (k : P.val.complex ⟶ P'.val.complex),
    ChainLift G G' g.hom l → ChainLift P.val P'.val f.hom k →
    ∀ x, iso G' hG' P'
      (homologyMap (leftTensorMap f.hom l) n x) =
      homologyMap (tensorFirstMap k B ≫ tensorSecondMap P'.val.complex g.hom) n
        (iso G hG P x)
  normalization : ∀ {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{w} R}
    (P : ProjectiveChoice Rᵐᵒᵖ A) (Q : ProjectiveChoice R B)
    (hQ : IsLeftFlat.{u,v,w} Q.val) (α : Augmentations P.val Q.val),
    ∀ z, iso Q.val hQ P (homologyMap α.right n z) = homologyMap α.left n z

def right_flat_computationsType : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ), Nonempty (RightComputations.{u,v,w} R n)

def left_flat_computationsType : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ), Nonempty (LeftComputations.{u,v,w} R n)

end
end P103.Specs.Ch11.FlatResolutions
