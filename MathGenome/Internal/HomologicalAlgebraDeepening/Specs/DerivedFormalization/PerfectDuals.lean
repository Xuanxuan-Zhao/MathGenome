import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectComplex
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! Evaluation, dualizability and biduality in the derived category (U10). -/

namespace Specs.DerivedFormalization.PerfectDuals

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Cochains (compValue derivedValue qValue)
open CochainTensor (pure isKFlat)
open CochainModels (internalHomValue)
open CochainTensorTransport (AdequateModel representedUnit representedUnitZero)
open DerivedHomModels (Models rHomValue)
open DerivedHomAdjunction (Closed Presentation homComparison)
open PerfectComplex (isBoundedFiniteProjectiveValue isPerfectValue)

universe u a v t

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {R : Type u} [CommRing R] {A : Type a} [CommRing A]
  {e : R ≃+* A} {M : AdequateModel e}
  {T : DerivedTensor.Model M} {H : Models.{u,a} R}

/-- The rank-one stalk, identified with the tensor unit of the localization. -/
def unitPresentation (T : DerivedTensor.Model M) :
    Presentation (letI := T.monoidal; 𝟙_ (derivedValue.{a} R)) :=
  ⟨(representedUnit e), T.toDescent.unitComparison.symm⟩

/-- The derived dual uses the fixed internal derived Hom and the derived unit. -/
def dualValue (T : DerivedTensor.Model M) (H : Models.{u,a} R) (P : (derivedValue.{a} R)) : (derivedValue.{a} R) :=
  letI := T.monoidal
  (rHomValue H).obj (op P, 𝟙_ (derivedValue.{a} R))

set_option linter.checkUnivs false in
def DualType :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e}, DerivedTensor.Model M → Models.{u,a} R → (derivedValue.{a} R) → (derivedValue.{a} R)

def evaluation (c : Closed T H) (P : (derivedValue.{a} R)) :
    letI := T.monoidal
    dualValue T H P ⊗ P ⟶ 𝟙_ (derivedValue.{a} R) :=
  letI := T.monoidal
  (c.equiv (dualValue T H P) P (𝟙_ (derivedValue.{a} R))).symm (𝟙 _)

/-- The mate of reassociation followed by evaluation in the last two factors. -/
def evaluationComparison (c : Closed T H) (P Y : (derivedValue.{a} R)) :
    letI := T.monoidal
    Y ⊗ dualValue T H P ⟶ (rHomValue H).obj (op P, Y) :=
  letI := T.monoidal
  c.equiv (Y ⊗ dualValue T H P) P Y
    ((α_ Y (dualValue T H P) P).hom ≫ Y ◁ evaluation c P ≫ (ρ_ Y).hom)

/-- The coevaluation corresponding to the identity of P. -/
def coevaluation (c : Closed T H) (P : (derivedValue.{a} R)) (h : IsIso (evaluationComparison c P P)) :
    letI := T.monoidal
    𝟙_ (derivedValue.{a} R) ⟶ P ⊗ dualValue T H P :=
  letI := T.monoidal
  letI := h
  c.equiv (𝟙_ (derivedValue.{a} R)) P P (λ_ P).hom ≫ inv (evaluationComparison c P P)

/-- Transposing evaluation after the symmetry gives the signed bidual map. -/
def biduality (c : Closed T H) (P : (derivedValue.{a} R)) : P ⟶ dualValue T H (dualValue T H P) :=
  letI := T.monoidal
  letI := T.symmetric
  c.equiv P (dualValue T H P) (𝟙_ (derivedValue.{a} R)) ((β_ P (dualValue T H P)).hom ≫ evaluation c P)

def PerfectDuality : Prop :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : DerivedTensor.Model M) (H : Models.{u,a} R)
    (c : Closed T H),
    letI := T.monoidal
    (∀ {P P' Y Y' : (derivedValue.{a} R)} (f : P' ⟶ P) (g : Y ⟶ Y'),
      (g ⊗ₘ (rHomValue H).map (Prod.mkHom f.op (𝟙 (𝟙_ (derivedValue.{a} R))))) ≫
          evaluationComparison c P' Y' =
        evaluationComparison c P Y ≫ (rHomValue H).map (Prod.mkHom f.op g)) ∧
    ∀ P : (derivedValue.{a} R), isPerfectValue P →
      isPerfectValue (dualValue T H P) ∧
      (∀ Y : (derivedValue.{a} R), IsIso (evaluationComparison c P Y)) ∧
      (∃ pairing : ExactPairing P (dualValue T H P),
        pairing.evaluation' = evaluation c P ∧
        ∃ h : IsIso (evaluationComparison c P P), pairing.coevaluation' = coevaluation c P h) ∧
      IsIso (biduality c P)

section Chain

variable (M)

/-- The signed internal Hom into the represented stalk over the original ring. -/
abbrev chainDual (e : R ≃+* A) (P : compValue.{a} R) := internalHomValue P (representedUnit e)

def chainEvaluation (P : compValue.{a} R) :
    CochainTensor.tensor (chainDual e P) P ⟶ (representedUnit e) :=
  (M.rawClosed P).adj.counit.app (representedUnit e)

/-- The original-ring tensor followed by evaluation, in the ordinary signed models. -/
def chainComparison (P Y : compValue.{a} R) :
    CochainTensor.tensor Y (chainDual e P) ⟶ internalHomValue P Y :=
  letI := M.chainMonoidal
  let B := chainDual e P
  (M.rawClosed P).adj.homEquiv _ _ (
    (M.tensorModel (CochainTensor.tensor Y B) P).hom ≫ (M.tensorModel Y B).hom ▷ P ≫
    (α_ Y B P).hom ≫ Y ◁ ((M.tensorModel B P).inv ≫ chainEvaluation M P ≫ M.unitModel.hom) ≫
    (ρ_ Y).hom)

def chainCoevaluation (P : compValue.{a} R) (h : IsIso (chainComparison M P P)) :
    (representedUnit e) ⟶ CochainTensor.tensor P (chainDual e P) :=
  letI := M.chainMonoidal
  letI := h
  (M.rawClosed P).adj.homEquiv _ _
    ((M.tensorModel (representedUnit e) P).hom ≫ M.unitModel.hom ▷ P ≫ (λ_ P).hom) ≫
      inv (chainComparison M P P)

def chainBiduality (P : compValue.{a} R) : P ⟶ chainDual e (chainDual e P) :=
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  let B := chainDual e P
  (M.rawClosed B).adj.homEquiv _ _
    ((M.tensorModel P B).hom ≫ (β_ P B).hom ≫ (M.tensorModel B P).inv ≫ chainEvaluation M P)

end Chain

/-- The comparison for the given presentations, using either good tensor factor. -/
def presentedTensor (T : DerivedTensor.Model M) {X Y : (derivedValue.{a} R)}
    (P : Presentation X) (S : Presentation Y)
    (h : isKFlat P.complex ∨ isKFlat S.complex) :
    letI := T.monoidal
    X ⊗ Y ≅ (qValue.{a} R).obj (CochainTensor.tensor P.complex S.complex) :=
  letI := T.monoidal
  (tensorIso P.iso S.iso).symm ≪≫ T.compare P.complex S.complex h

def dualPresentation (T : DerivedTensor.Model M) (H : Models.{u,a} R) {X : (derivedValue.{a} R)}
    (P : Presentation X) (h : IsIso (homComparison H P (unitPresentation T))) :
    Presentation (dualValue T H X) :=
  ⟨chainDual e P.complex, @asIso _ _ _ _ (homComparison H P (unitPresentation T)) h⟩

/-- The canonical derived arrows are the images of the signed maps on an
actual bounded finite projective representative over the original ring. -/
def ModelComputation : Prop :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e} (T : DerivedTensor.Model M) (H : Models.{u,a} R)
    (c : Closed T H) {X Y : (derivedValue.{a} R)} (P : Presentation X) (S : Presentation Y),
    isBoundedFiniteProjectiveValue P.complex →
    let B := chainDual e P.complex
    isBoundedFiniteProjectiveValue B ∧
    P.complex.IsKProjective ∧ B.IsKProjective ∧
    ∃ (hP : isKFlat P.complex) (hB : isKFlat B)
      (h : IsIso (homComparison H P (unitPresentation T)))
      (hC : IsIso (chainComparison M P.complex P.complex))
      (hD : IsIso (evaluationComparison c X X)),
      let L := dualPresentation T H P h
      evaluation c X =
        (presentedTensor T L P (Or.inl hB)).hom ≫
          (qValue.{a} R).map (chainEvaluation M P.complex) ≫ (unitPresentation T).iso.hom ∧
      evaluationComparison c X Y =
        (presentedTensor T S L (Or.inr hB)).hom ≫
          (qValue.{a} R).map (chainComparison M P.complex S.complex) ≫ homComparison H P S ∧
      coevaluation c X hD =
        (unitPresentation T).iso.inv ≫ (qValue.{a} R).map (chainCoevaluation M P.complex hC) ≫
          (presentedTensor T P L (Or.inl hP)).inv ∧
      biduality c X =
        P.iso.inv ≫ (qValue.{a} R).map (chainBiduality M P.complex) ≫ homComparison H L (unitPresentation T)

/-- On homogeneous vectors the formulas are the balanced evaluation and its
Koszul transpose over R, with the rank-one scalar read through e. -/
def ChainFormulas : Prop :=
  ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    (M : AdequateModel e) (P Y : compValue.{a} R),
    let B := chainDual e P
    (∀ {i j n : ℤ} (h : j + i = n) (f : B.X j) (x : P.X i),
      (chainEvaluation M P).f n (pure B P h f x) = f.v i n (by omega) x) ∧
    (∀ {i j k n : ℤ} (h : j + k = n) (hk : i + k = 0)
      (y : Y.X j) (f : B.X k) (x : P.X i),
      ((chainComparison M P Y).f n (pure Y B h y f)).v i j (by omega) x =
        e.symm ((representedUnitZero e).hom (f.v i 0 hk x)) • y) ∧
    (∀ {i j k n l : ℤ} (h : j + k = n) (hl : i + n = l) (hk : i + k ≠ 0)
      (y : Y.X j) (f : B.X k) (x : P.X i),
      ((chainComparison M P Y).f n (pure Y B h y f)).v i l hl x = 0) ∧
    (∀ {i j n : ℤ} (h : j + i = n) (x : P.X i) (f : B.X j),
      ((chainBiduality M P).f i x).v j n h f = (i * j).negOnePow • f.v i n (by omega) x)

/-- A perfect object at any original module level is perfect after moving
to the common level used for the derived adjunction. -/
def PerfectLift : Prop :=
  ∀ {R : Type u} [CommRing R] (P : derivedValue.{v} R),
    isPerfectValue P →
      isPerfectValue ((CochainCoefficientLift.liftD.{max u t,v} R).obj P)

end

end Specs.DerivedFormalization.PerfectDuals
