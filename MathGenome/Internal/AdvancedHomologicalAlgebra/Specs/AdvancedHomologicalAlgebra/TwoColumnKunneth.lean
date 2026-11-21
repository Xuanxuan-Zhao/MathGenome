import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.KunnethSpectralSequence
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-! HA-B08, source lines 1086–1134, with the ring and indexing conventions
of the tensor-complex section. A flat presentation means an actual exact
length-one flat resolution, not an assumed Tor-vanishing certificate.
All chain degrees and lower bounds are integers. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace AdvancedHomologicalAlgebra.TwoColumnKunneth
open KunnethSpectralSequence FiniteFiltrationConvergence
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch02.FlatnessTests
variable {R : Type u} [Ring R]

/-- The zero kernel also permits flat resolutions of length zero. Terms
live in the usual resolution universe; the augmentation has its original
codomain, without replacing the module by a different mathematical object. -/
structure FlatPresentation (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A] where
  F₁ : ModuleCat.{max u v} Rᵐᵒᵖ
  F₀ : ModuleCat.{max u v} Rᵐᵒᵖ
  i : F₁ →ₗ[Rᵐᵒᵖ] F₀
  ε : F₀ →ₗ[Rᵐᵒᵖ] A
  injective : Function.Injective i
  exact : Function.Exact i ε
  surjective : Function.Surjective ε
  flat₁ : RightFlat.{u,max u v,w} R F₁
  flat₀ : RightFlat.{u,max u v,w} R F₀

def HasFlatDimensionOne (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A] : Prop :=
  Nonempty (FlatPresentation.{u,v,w} (R := R) A)

/-- The differential onto its actual boundary module. -/
def boundaryProjection (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (n : ℤ) :
    P.X n →ₗ[Rᵐᵒᵖ] boundaries P (n-1) :=
  (P.d n (n-1)).hom.codRestrict _ (by
    intro x
    change ∃ y, (P.d ((ComplexShape.down ℤ).prev (n-1)) (n-1)).hom y = _
    rw [(ComplexShape.down ℤ).prev_eq' (show (ComplexShape.down ℤ).Rel n (n-1) by
      simp only [ComplexShape.down_Rel]; omega)]
    exact ⟨x,rfl⟩)

def boundaryToCycles (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (n : ℤ) :
    boundaries P n →ₗ[Rᵐᵒᵖ] cycles P n :=
  Submodule.inclusion (boundaryInclusion P n)

/-- The concrete tensor of a categorical cycle is a cycle of the original
coefficient complex. This fixes the left edge map on all representatives. -/
def tensorCycle (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) (z : P.cycles n) (m : M) :
    cycles (coefficientComplex P M) n :=
  ⟨tmul R ((P.iCycles n).hom z) m, by
    change tmul R ((P.d n ((ComplexShape.down ℤ).next n)).hom
      ((P.iCycles n).hom z)) m = 0
    have hz := congrArg (fun f => f.hom z)
      (P.iCycles_d n ((ComplexShape.down ℤ).next n))
    change (P.d n ((ComplexShape.down ℤ).next n)).hom ((P.iCycles n).hom z) = 0 at hz
    rw [hz]
    simp [tmul]⟩

def tensorCycleClass (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) (z : P.cycles n) (m : M) :
    targetHomology P M n :=
  ULift.up (homologyClass (coefficientComplex P M) n (tensorCycle P M n z m))

/-- The stationary second-page identification with the actual graded piece,
using closed representatives and the augmentation-induced target transport. -/
def secondToGraded {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w} R}
    (D : Realization T X.P X.M X.Q X.L) (p n : ℤ)
    (I : LimitIso D.tensorPages.filtration D.tensorPages.pages 2 (-p) (-n)) :
    D.tensorPages.term 2 p (n-p) ≅ D.targetGraded p n :=
  eqToIso (by
    unfold TensorPages.term PageCohomology.object
    congr 1
    omega) ≪≫ I.iso ≪≫
    transportedGradedIso D.tensorPages.filtration n _ (D.targetIso n) p

/-- One short exact sequence for the actual original target. Its image is
exactly the zeroth step of the target filtration of HA-B06. No section or
splitting is included. -/
structure Sequence (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R)
    (D : Realization T X.P X.M X.Q X.L) (n : ℤ) where
  α : Tensor R (X.P.homology n) X.M →ₗ[ℤ] targetHomology X.P X.M n
  β : targetHomology X.P X.M n →ₗ[ℤ] T.Tor (X.P.homology (n-1)) X.M 1
  injective : Function.Injective α
  exact : Function.Exact α β
  surjective : Function.Surjective β
  cycle_formula : ∀ (z : X.P.cycles n) (m : X.M),
    α (tmul R ((X.P.homologyπ n).hom z) m) = tensorCycleClass X.P X.M n z m
  image : (ModuleCat.subobjectModule (targetHomology X.P X.M n)).symm (LinearMap.range α) = D.targetPiece 0 n
  lower : D.targetPiece (-1) n = ⊥
  upper : D.targetPiece 1 n = ⊤
  stable_second : Stabilized D.tensorPages.filtration 2 (-1) (-n)
  projection_formula :
    ∃ I : LimitIso D.tensorPages.filtration D.tensorPages.pages 2 (-1) (-n),
      (D.targetPiece 1 n).arrow ≫ ModuleCat.ofHom β =
        cokernel.π (Subobject.ofLE _ _
          (transportedPiece_increasing D.tensorPages.filtration n _ (D.targetIso n) 1)) ≫
        (secondToGraded (X := X) D 1 n I).inv ≫ (D.secondIso 1 (n-1)).hom

/-- Naturality is simultaneous in arbitrary chain maps and coefficient maps;
the two outside maps are the actual tensor and canonical Tor actions. -/
structure System (T : CanonicalTheory.{u,v,w} R) (S : KunnethSpectralSequence.System T) where
  sequence : ∀ (X : Input.{u,v,w} R), (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) →
    ∀ n, Sequence T X (S.realize X) n
  natural_left : ∀ (X Y : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (hY : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (Y.P.homology q))
    (f : X.P ⟶ Y.P) (g : X.M ⟶ Y.M) (n : ℤ),
    (targetHomologyMap f g n).hom.comp (sequence X hX n).α =
      (sequence Y hY n).α.comp (tensorMap (HomologicalComplex.homologyMap f n).hom g.hom)
  natural_right : ∀ (X Y : Input.{u,v,w} R)
    (hX : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q))
    (hY : ∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (Y.P.homology q))
    (f : X.P ⟶ Y.P) (g : X.M ⟶ Y.M) (n : ℤ),
    (sequence Y hY n).β.comp (targetHomologyMap f g n).hom =
      (T.torMap 1 (HomologicalComplex.homologyMap f (n-1)) g).comp (sequence X hX n).β

namespace Specs
/-- The general corollary, for all original inputs and all integer degrees. -/
def FullStatement : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R),
    ∃ S : KunnethSpectralSequence.System T, Nonempty (System T S)

/-- The two actual cycle/boundary short exact sequences, for integer degrees. -/
def BasicExactSequences : Prop :=
  ∀ (R : Type u) [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (n : ℤ),
    (Function.Injective (cycles P n).subtype ∧
      Function.Exact (cycles P n).subtype (boundaryProjection P n) ∧
      Function.Surjective (boundaryProjection P n)) ∧
    (Function.Injective (boundaryToCycles P n) ∧
      Function.Exact (boundaryToCycles P n) (homologyClass P n) ∧
      Function.Surjective (homologyClass P n))

/-- The separately stated sufficient case, without a boundedness restriction. -/
def FlatBoundariesSuffice : Prop :=
  ∀ (R : Type u) [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ),
    FlatTerms.{u,v,w} P → (∀ q, RightFlat.{u,v,w} R (boundaries P q)) →
      (∀ q, RightFlat.{u,v,w} R (cycles P q)) ∧
      (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (P.homology q))

/-- An algebraic consequence of the actual length-one resolution hypothesis. -/
def HigherTorVanishes : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ), HasFlatDimensionOne.{u,v,w} (R := R) A →
    ∀ (M : ModuleCat.{w} R) (p : ℕ), 1 < p → Subsingleton (T.Tor A M p)

/-- The actual pages have just two possible columns, and their actual
higher differentials vanish. This does not yet assert the edge-map theorem. -/
def TwoColumnPages : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R),
    (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) →
    ∀ (D : Realization T X.P X.M X.Q X.L),
    (∀ (r : ℤ), 2 ≤ r → ∀ p q : ℤ, p < 0 ∨ 1 < p →
      IsZero (D.tensorPages.term r p q)) ∧
    (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      D.tensorPages.differential r (by omega) p q = 0)

/-- The finite target filtration has exactly the two possible graded steps,
identified canonically with the stationary second page. -/
def FiltrationCollapse : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R),
    (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) →
    ∀ (D : Realization T X.P X.M X.Q X.L),
    (∀ n, D.targetPiece (-1) n = ⊥ ∧ D.targetPiece 1 n = ⊤) ∧
    (∀ p n, Stabilized D.tensorPages.filtration 2 (-p) (-n) ∧
      Nonempty (LimitIso D.tensorPages.filtration D.tensorPages.pages 2 (-p) (-n)))

/-- The usual cycle-tensor map exists naturally for all integer complexes
and is injective under exactly the original two-column hypotheses. This
statement does not yet identify its image with the target filtration. -/
def CycleTensorInjection : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ a : ∀ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) (n : ℤ),
      Tensor R (P.homology n) M →ₗ[ℤ] targetHomology P M n,
      (∀ P M n (z : P.cycles n) m,
        a P M n (tmul R ((P.homologyπ n).hom z) m) = tensorCycleClass P M n z m) ∧
      (∀ (X : Input.{u,v,w} R),
        (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) →
        ∀ n, Function.Injective (a X.P X.M n)) ∧
      (∀ {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
        {M N : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ N) n,
        (targetHomologyMap f g n).hom.comp (a P M n) =
          (a P' N n).comp (tensorMap (HomologicalComplex.homologyMap f n).hom g.hom))
section OriginalCarriers
universe v' w'

/-- Both edges for the original inputs commute with the concrete heterogeneous
HA-B06 map, using the fixed cycle formula and stationary-page projection. -/
def OriginalNaturality : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (T' : CanonicalTheory.{u,v',w'} R)
    (X : Input.{u,v,w} R) (Y : Input.{u,v',w'} R)
    (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
    (f : OriginalInputMap X Y) (F : OriginalNaturalMap D E f) (n : ℤ)
    (A : Sequence T X D n) (B : Sequence T' Y E n),
    (F.target n).comp A.α =
      B.α.comp (tensorMap (F.pHomology n) f.coefficient) ∧
    B.β.comp (F.target n) = (F.tor (n-1) 1).comp A.β

end OriginalCarriers
end Specs

namespace IndependentResolution

open KunnethSpectralSequence.IndependentResolution (LimitComparison)
open KunnethSpectralSequence.IndependentResolution
  renaming Input → OriginalInput, Realization → OriginalRealization
universe t v' w' t'

/-- The right edge uses the signed HA-B06 second-page comparison in total
degree `n` and filtration degree one. -/
def secondTorEquiv {T : CanonicalTheory.{u,v,w} R}
    {X : OriginalInput.{u,v,w,t} R}
    (D : OriginalRealization T X) (n : ℤ) :
    (PageCohomology.object D.pages.filtration D.pages.pages 2 (-1) (-n) :
      ModuleCat.{max v t} ℤ) ≃ₗ[ℤ] T.Tor (X.P.homology (n-1)) X.M 1 :=
  (eqToIso (show PageCohomology.object D.pages.filtration D.pages.pages 2 (-1) (-n) =
      D.pages.term 2 1 (n-1) by
    unfold TensorPages.term
    rw [show 1 + (n-1) = n by omega])).toLinearEquiv.trans (D.second.equiv 1 (n-1))

/-- The edge sequence on the original coefficient quotient, for the very
signed total and augmentation attached to the given independent resolution. -/
structure Sequence (T : CanonicalTheory.{u,v,w} R) (X : OriginalInput.{u,v,w,t} R)
    (D : OriginalRealization T X) (n : ℤ) where
  α : Tensor R (X.P.homology n) X.M →ₗ[ℤ] Homology X.coefficient n
  β : Homology X.coefficient n →ₗ[ℤ] T.Tor (X.P.homology (n-1)) X.M 1
  injective : Function.Injective α
  exact : Function.Exact α β
  surjective : Function.Surjective β
  cycle_formula : ∀ (z : X.P.cycles n) (m : X.M),
    α (tmul R ((X.P.homologyπ n).hom z) m) =
      homologyClass X.coefficient n (tensorCycle X.P X.M n z m)
  image : LinearMap.range α = D.piece 0 n
  lower : D.piece (-1) n = ⊥
  upper : D.piece 1 n = ⊤
  stable_second : Stabilized D.pages.filtration 2 (-1) (-n)
  limit : LimitComparison D 2 1 n
  projection_formula : β.comp (D.piece 1 n).subtype =
    ((limit.equiv.symm.trans (secondTorEquiv D n)).toLinearMap).comp
      (D.gradedSubmodule 1 n).mkQ

namespace Specs

/-- The page objects and differentials of the actual independently sized
HA-B06 realization have only two possible columns from page two onward. -/
def Pages : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (X : OriginalInput.{u,v,w,t} R),
    (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) →
    ∀ (D : OriginalRealization T X),
    (∀ r p q : ℤ, 2 ≤ r → p < 0 ∨ 1 < p → IsZero (D.pages.term r p q)) ∧
    (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      D.pages.differential r ((by decide : (0 : ℤ) ≤ 2).trans hr) p q = 0)

/-- Collapse of the actual filtration, including the closed-representative
comparison from the stationary second page to every graded quotient. -/
def Filtration : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (X : OriginalInput.{u,v,w,t} R),
    (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) →
    ∀ (D : OriginalRealization T X),
    (∀ n, D.piece (-1) n = ⊥ ∧ D.piece 1 n = ⊤) ∧
    (∀ p n, Stabilized D.pages.filtration 2 (-p) (-n) ∧ Nonempty (LimitComparison D 2 p n))

/-- The original short exact sequence for every resolution choice and
degree, with the cycle edge and the stationary-page projection fixed. -/
def ExactSequence : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (X : OriginalInput.{u,v,w,t} R),
    (∀ q, HasFlatDimensionOne.{u,v,w} (R := R) (X.P.homology q)) →
    ∀ (D : OriginalRealization T X) (n : ℤ), Nonempty (Sequence T X D n)

/-- Both edges commute with the actual HA-B06 coefficient and Tor actions
on independent input and target resolution term levels. -/
def Naturality : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (T' : CanonicalTheory.{u,v',w'} R)
    (X : OriginalInput.{u,v,w,t} R) (Y : OriginalInput.{u,v',w',t'} R)
    (D : OriginalRealization T X) (E : OriginalRealization T' Y)
    (f : KunnethSpectralSequence.IndependentResolution.Input.Hom X Y)
    (F : KunnethSpectralSequence.IndependentResolution.NaturalMap D E f)
    (n : ℤ) (A : Sequence T X D n) (B : Sequence T' Y E n),
    (F.coefficient.homologyMap n).comp A.α =
      B.α.comp (tensorMap (F.right_homology n) f.coefficient) ∧
    B.β.comp (F.coefficient.homologyMap n) = (F.tor (n-1) 1).comp A.β

end Specs
end IndependentResolution

end AdvancedHomologicalAlgebra.TwoColumnKunneth
