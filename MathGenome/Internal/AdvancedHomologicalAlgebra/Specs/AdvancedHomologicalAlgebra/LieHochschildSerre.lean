import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckEdges
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LieQuotientCohomologyAction
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.IdealEnvelopingFreeness
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence

/-! HA-A09. The Lie algebra and both coefficient actions are the original
ones. Page index zero in the inherited row diagram denotes the classical E₂. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Shared.Lie

namespace AdvancedHomologicalAlgebra.LieHochschildSerre

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

/-- The map of enveloping algebras induced by the actual ideal quotient. -/
def envelopingQuotient (h : LieIdeal k g) : U k g →ₐ[k] U k (g ⧸ h) :=
  UniversalEnvelopingAlgebra.lift k
    ((inclusion k (g ⧸ h)).comp (LieQuotientAction.quotientMap k g h))

/-- Coextension along the ideal quotient is the functor of ideal invariants,
realized as maps from the quotient enveloping algebra. -/
abbrev idealInvariants (h : LieIdeal k g) :
    ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} (U k (g ⧸ h)) :=
  ModuleCat.coextendScalars (envelopingQuotient h).toRingHom

/-- Coextension along the augmentation realizes the invariants of a Lie algebra. -/
abbrev lieInvariants (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] :
    ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} k :=
  ModuleCat.coextendScalars (Shared.Lie.augmentation k g).toRingHom

variable (h : LieIdeal k g)

/-- The ideal followed by quotient invariants, with both adjunctions fixed. -/
abbrev quotientInvariants :
    ModuleCat.{max u v w} (U k (g ⧸ h)) ⥤ ModuleCat.{max u v w} k :=
  lieInvariants k (g ⧸ h)

set_option backward.isDefEq.respectTransparency false in
instance coextendAdditive {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.coextendScalars.{_, _, w} f).Additive where
  map_add := by
    intro X Y a b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro s
    change (a + b) (x s) = a (x s) + b (x s)
    exact rfl

/-- The underlying vector space of an enveloping-algebra module. -/
abbrev underlying (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L] :
    ModuleCat.{w} (U k L) ⥤ ModuleCat.{w} k :=
  ModuleCat.restrictScalars (algebraMap k (U k L))

/-- The representation obtained by restricting the given enveloping action. -/
def coefficientRepresentation (k : Type u) (L : Type v) [Field k] [LieRing L]
    [LieAlgebra k L] (M : ModuleCat.{w} (U k L)) :
    Representation k L ((underlying k L).obj M) :=
  letI : IsScalarTower k (U k L) ((underlying k L).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LieQuotientAction.moduleRepresentation L ((underlying k L).obj M)

/-- Evaluation at one identifies coextension with the ideal-invariant
subspace. Its action on each quotient representative is the original action. -/
def IdealInvariantsStatement : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g) (M : ModuleCat.{max u v w} (U k g)),
    ∃ e : (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M) ≃ₗ[k]
        LieQuotientAction.invariants h (coefficientRepresentation k g M),
      (∀ t, (e t).val = (show (idealInvariants.{u,v,w} h).obj M from t) (1 : U k (g ⧸ h))) ∧
      ∀ y t, (e (inclusion k (g ⧸ h) (LieQuotientAction.quotientMap k g h y) • t)).val =
        inclusion k g y • (e t).val

/-- Evaluation on the unit identifies augmentation coextension with the
subspace of vectors fixed by the given Lie algebra. -/
structure InvariantInclusion (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L] where
  evaluation : lieInvariants.{u,v,w} k L ⟶ underlying k L
  formula : ∀ M t, (evaluation.app M).hom t =
    (show (lieInvariants.{u,v,w} k L).obj M from t) (1 : k)
  injective : ∀ M, Function.Injective (evaluation.app M).hom
  range : ∀ M m, m ∈ LinearMap.range (evaluation.app M).hom ↔
    ∀ y, coefficientRepresentation k L M y m = 0

def LieInvariantsStatement : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g],
    Nonempty (InvariantInclusion.{u,v,w} k g)

/-- The categorical spectral sequence with its filtered edges and exact
five terms, before the identification of its entries with CE cohomology. -/
def DerivedStatement : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g),
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k g))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k (g ⧸ h)))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} k)
    ∃ P : GrothendieckSpectralSequence.Package
        (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h),
      Nonempty (GrothendieckEdges.ObjectEdges
        (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P)


section Cochains

variable {L : Type*} [LieRing L] [LieAlgebra k L]
  {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Given a Lie map in the opposite direction and a compatible coefficient
map, pull back the exterior arguments and postcompose on coefficients. -/
def pullback (f : L →ₗ⁅k⁆ g) (a : M →ₗ[k] N) (n : ℕ) :
    (CE.W k g n →ₗ[k] M) →ₗ[k] (CE.W k L n →ₗ[k] N) where
  toFun t := a.comp (t.comp (exteriorPower.map n f.toLinearMap))
  map_add' t s := by ext x; simp
  map_smul' r t := by ext x; simp

/-- A differential with the displayed Chevalley–Eilenberg formula. -/
def IsCEDifferential (ρ : Representation k g M)
    (d : ∀ n : ℕ, (CE.W k g n →ₗ[k] M) →ₗ[k] (CE.W k g (n+1) →ₗ[k] M)) : Prop :=
  ∀ n t x, d n t (CE.wedge k g (n+1) x) =
    (∑ i : Fin (n+1), (-1 : ℤ)^i.val •
      ρ (x i) (t (CE.wedge k g n (i.removeNth x)))) +
    CE.cochainBracketSum k g M n t x

/-- One identity handles the actual quotient pullback and the ideal
restriction with no choices of lifts. -/
def PullbackStatement : Prop :=
  ∀ (k : Type u) (g L : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    [LieRing L] [LieAlgebra k L]
    (M N : Type w) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (ρ : Representation k g M) (τ : Representation k L N)
    (f : L →ₗ⁅k⁆ g) (a : M →ₗ[k] N),
    (∀ y m, a (ρ (f y) m) = τ y (a m)) →
    ∀ d e, IsCEDifferential ρ d → IsCEDifferential τ e →
      ∀ n t, e n (pullback f a n t) = pullback f a (n+1) (d n t)

end Cochains

section CochainTheory

open CategoryTheory.Functor

variable (k) (g)

/-- The CE coboundary as a natural family on actual exterior-power cochains. -/
structure CochainTheory where
  d : ∀ (M : ModuleCat.{max u v w} (U k g)) n,
    (CE.W k g n →ₗ[k] (underlying k g).obj M) →ₗ[k]
      (CE.W k g (n+1) →ₗ[k] (underlying k g).obj M)
  formula : ∀ M, IsCEDifferential (coefficientRepresentation k g M) (d M)
  square : ∀ M n, (d M (n+1)).comp (d M n) = 0
  natural : ∀ {M N} (a : M ⟶ N) n t,
    d N n (pullback (LieHom.id : g →ₗ⁅k⁆ g) ((underlying k g).map a).hom n t) =
      pullback (LieHom.id : g →ₗ⁅k⁆ g) ((underlying k g).map a).hom (n+1) (d M n t)

variable {k g} {L : Type v} [LieRing L] [LieAlgebra k L]

/-- The cochain complex formed by the specified CE coboundary. -/
abbrev CochainTheory.complex (D : CochainTheory.{u,v,w} k g)
    (M : ModuleCat.{max u v w} (U k g)) : CochainComplex (ModuleCat.{max u v w} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (CE.W k g n →ₗ[k] (underlying k g).obj M))
    (fun n => ModuleCat.ofHom (D.d M n)) (fun n => ModuleCat.hom_ext (D.square M n))

/-- The induced map of CE complexes, with its actual argument and
coefficient maps fixed in each degree. -/
def CochainTheory.map (D : CochainTheory.{u,v,w} k g)
    (E : CochainTheory.{u,v,w} k L) {M : ModuleCat.{max u v w} (U k g)}
    {N : ModuleCat.{max u v w} (U k L)} (f : L →ₗ⁅k⁆ g)
    (a : (underlying k g).obj M ⟶ (underlying k L).obj N)
    (comm : ∀ n t, E.d N n (pullback f a.hom n t) = pullback f a.hom (n+1) (D.d M n t)) :
    D.complex M ⟶ E.complex N where
  f n := ModuleCat.ofHom (pullback f a.hom n)
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    simpa only [CochainTheory.complex, CochainComplex.of_d, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply] using comm i t

/-- The functorial CE complex, with coefficient maps acting by postcomposition. -/
def CochainTheory.functor (D : CochainTheory.{u,v,w} k g) :
    ModuleCat.{max u v w} (U k g) ⥤ CochainComplex (ModuleCat.{max u v w} k) ℕ where
  obj := D.complex
  map a := D.map D (LieHom.id : g →ₗ⁅k⁆ g) ((underlying k g).map a) (D.natural a)
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply LinearMap.ext
    intro x
    change (((underlying k g).map (𝟙 M)).hom
      (t (exteriorPower.map n (LinearMap.id (R := k)) x))) = _
    simp
  map_comp a b := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply LinearMap.ext
    intro x
    change (((underlying k g).map (a ≫ b)).hom
      (t (exteriorPower.map n (LinearMap.id (R := k)) x))) =
      (((underlying k g).map b).hom
        (((underlying k g).map a).hom
          (t (exteriorPower.map n (LinearMap.id (R := k))
            (exteriorPower.map n (LinearMap.id (R := k)) x)))))
    simp

/-- Lie algebra cohomology as cycles modulo boundaries of the actual CE
functor, with the induced maps on cocycle classes. -/
def CochainTheory.cohomology (D : CochainTheory.{u,v,w} k g) (n : ℕ) :
    ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} k :=
  D.functor ⋙ P103.Specs.Ch10.Comparison.quotientHomology (.up ℕ) n

end CochainTheory

section EdgeCochains

variable (h : LieIdeal k g)

/-- Restrict a coefficient module along the actual enveloping inclusion. -/
abbrev restrictIdeal :
    ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} (U k h) :=
  ModuleCat.restrictScalars (IdealEnveloping.inducedMap k g h).toRingHom

/-- The two cochain maps, determined by their evaluations on exterior
generators. Coextended coefficients are evaluated at one for inflation. -/
structure EdgeCochains (Dg : CochainTheory.{u,v,w} k g)
    (Dh : CochainTheory.{u,v,w} k h) (Dq : CochainTheory.{u,v,w} k (g ⧸ h)) where
  inflation : idealInvariants.{u,v,w} h ⋙ Dq.functor ⟶ Dg.functor
  restriction : Dg.functor ⟶ restrictIdeal.{u,v,w} h ⋙ Dh.functor
  inflation_formula : ∀ M n t (x : Fin n → g),
    (show CE.W k g n →ₗ[k] (underlying k g).obj M from ((inflation.app M).f n).hom t)
        (CE.wedge k g n x) =
      (show (idealInvariants.{u,v,w} h).obj M from
        (show CE.W k (g ⧸ h) n →ₗ[k]
            (underlying k (g ⧸ h)).obj ((idealInvariants.{u,v,w} h).obj M) from t)
          (CE.wedge k (g ⧸ h) n (LieQuotientAction.quotientMap k g h ∘ x))) (1 : U k (g ⧸ h))
  restriction_formula : ∀ M n t (x : Fin n → h),
    (show CE.W k h n →ₗ[k] (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M) from
      ((restriction.app M).f n).hom t) (CE.wedge k h n x) =
      (show CE.W k g n →ₗ[k] (underlying k g).obj M from t) (CE.wedge k g n (h.incl ∘ x))

/-- Existence of the original cochain maps in every degree, natural in all
ambient module homomorphisms. -/
def EdgeCochainsStatement : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g),
    ∃ (Dg : CochainTheory.{u,v,w} k g) (Dh : CochainTheory.{u,v,w} k h)
      (Dq : CochainTheory.{u,v,w} k (g ⧸ h)), Nonempty (EdgeCochains h Dg Dh Dq)

end EdgeCochains

section Comparison

open CategoryTheory.Functor
open GrothendieckSpectralSequence GrothendieckEdges
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.HomologySequence

variable (h : LieIdeal k g)

variable [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k g))]
  [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} (U k (g ⧸ h)))] [HasDerivedCategory.{(max u v w) + 1} (ModuleCat.{max u v w} k)]

/-- The comparison carries the derived unit to the class of the cochain
obtained from the invariant vector by the exterior degree-zero augmentation. -/
def PreservesCEAugmentation {A : Type*} [Category A] {L : Type v}
    [LieRing L] [LieAlgebra k L]
    (T : A ⥤ ModuleCat.{max u v w} (U k L)) (D : CochainTheory.{u,v,w} k L)
    {F V : A ⥤ ModuleCat.{max u v w} k} (unit : F ⟶ V)
    (evaluate : ∀ M : A, F.obj M → (underlying k L).obj (T.obj M))
    (e : V ≅ T ⋙ D.cohomology 0) : Prop :=
  ∀ (M : A) (m : F.obj M),
    ∃ z : cycles (D.complex (T.obj M)) 0,
      z.val (CE.wedge k L 0 Fin.elim0) = evaluate M m ∧
      (e.hom.app M).hom ((unit.app M).hom m) = homologyClass _ 0 z

/-- The derived boundary agrees on the quotient of actual exterior
cocycles with the lift-and-differentiate boundary of the coefficient sequence. -/
def PreservesCEConnectors {A : Type*} [Category A] [Abelian A]
    (C : A ⥤ CochainComplex (ModuleCat.{w} k) ℕ)
    (V : ℕ → A ⥤ ModuleCat.{w} k)
    (δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
      (V n).obj S.X₃ ⟶ (V (n+1)).obj S.X₁)
    (e : ∀ n, V n ≅ C ⋙ quotientHomology (.up ℕ) n) : Prop :=
  ∀ {S : ShortComplex A} (hS : S.ShortExact),
    DegreewiseExact (C.map S.f) (C.map S.g) ∧
    ∀ n : ℕ, Connecting (C.map S.f) (C.map S.g) n (n+1)
      (((e n).inv.app S.X₃ ≫ δ hS n ≫ (e (n+1)).hom.app S.X₁).hom)

/-- The cohomology identifications use the printed Lie derivative on
ideal cocycle classes and evaluation at one for quotient invariants. -/
structure CohomologyComparison (Dg : CochainTheory.{u,v,w} k g)
    (Dh : CochainTheory.{u,v,w} k h) (Dq : CochainTheory.{u,v,w} k (g ⧸ h)) where
  ambient : ∀ n, rightValue ((idealInvariants.{u,v,w} h) ⋙ (quotientInvariants.{u,v,w} h)) n ≅ Dg.cohomology n
  ideal : ∀ n, rightValue (idealInvariants.{u,v,w} h) n ⋙ underlying k (g ⧸ h) ≅
    restrictIdeal.{u,v,w} h ⋙ Dh.cohomology n
  quotient : ∀ n, rightValue (quotientInvariants.{u,v,w} h) n ≅ Dq.cohomology n
  quotientInclusion : InvariantInclusion.{u,v,w} k (g ⧸ h)
  ambient_augmentation : PreservesCEAugmentation.{u,v,w} (𝟭 _) Dg
    (degreeZeroUnit (idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h))
    (fun M m =>
      (show (idealInvariants.{u,v,w} h).obj M from
        (show (quotientInvariants.{u,v,w} h).obj ((idealInvariants.{u,v,w} h).obj M) from m) (1 : k))
          (1 : U k (g ⧸ h)))
    (ambient 0)
  ambient_connectors : PreservesCEConnectors Dg.functor
    (rightValue (idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h))
    (rightBoundary (idealInvariants.{u,v,w} h ⋙ quotientInvariants.{u,v,w} h)) ambient
  ideal_augmentation : PreservesCEAugmentation.{u,v,w} (restrictIdeal.{u,v,w} h) Dh
    (whiskerRight (degreeZeroUnit (idealInvariants.{u,v,w} h)) (underlying k (g ⧸ h)))
    (fun M m => (show (idealInvariants.{u,v,w} h).obj M from m) (1 : U k (g ⧸ h)))
    (ideal 0)
  ideal_connectors : PreservesCEConnectors (restrictIdeal.{u,v,w} h ⋙ Dh.functor)
    (fun n => rightValue (idealInvariants.{u,v,w} h) n ⋙ underlying k (g ⧸ h))
    (fun hS n => (underlying k (g ⧸ h)).map (rightBoundary (idealInvariants.{u,v,w} h) hS n))
    ideal
  quotient_augmentation : PreservesCEAugmentation.{u,v,w} (𝟭 _) Dq
    (degreeZeroUnit (quotientInvariants.{u,v,w} h))
    (fun M m => (show (quotientInvariants.{u,v,w} h).obj M from m) (1 : k)) (quotient 0)
  quotient_connectors : PreservesCEConnectors Dq.functor
    (rightValue (quotientInvariants.{u,v,w} h))
    (rightBoundary (quotientInvariants.{u,v,w} h)) quotient
  ideal_action : ∀ (M : (ModuleCat.{max u v w} (U k g))) (n : ℕ) (y : g)
      (z : cycles (Dh.complex ((restrictIdeal.{u,v,w} h).obj M)) n),
    ∃ z' : cycles (Dh.complex ((restrictIdeal.{u,v,w} h).obj M)) n,
      (∀ x : Fin n → h,
        z'.val (CE.wedge k h n x) =
          (show (underlying k h).obj ((restrictIdeal.{u,v,w} h).obj M) from
            coefficientRepresentation k g M y (z.val (CE.wedge k h n x))) -
          ∑ i : Fin n, z.val (CE.wedge k h n (Function.update x i ⁅y, x i⁆))) ∧
      (ideal n).inv.app M
        (homologyClass (Dh.complex ((restrictIdeal.{u,v,w} h).obj M)) n z') =
      inclusion k (g ⧸ h) (LieQuotientAction.quotientMap k g h y) •
        (show (underlying k (g ⧸ h)).obj ((rightValue (idealInvariants.{u,v,w} h) n).obj M) from
          (ideal n).inv.app M
            (homologyClass (Dh.complex ((restrictIdeal.{u,v,w} h).obj M)) n z))
/-- The edge squares identify the filtered edges with the exterior-power maps. -/
structure CEComparison (Dg : CochainTheory.{u,v,w} k g)
    (Dh : CochainTheory.{u,v,w} k h) (Dq : CochainTheory.{u,v,w} k (g ⧸ h))
    (E : EdgeCochains h Dg Dh Dq)
    (P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h))
    (O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P)
    extends CohomologyComparison h Dg Dh Dq where
  inflation_edge : ∀ (M : (ModuleCat.{max u v w} (U k g))) (n : ℕ),
    (quotient n).hom.app ((idealInvariants.{u,v,w} h).obj M) ≫ (quotientHomology (.up ℕ) n).map (E.inflation.app M) =
      (derivedFirstEdge (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P n).app M ≫ (ambient n).hom.app M
  restriction_edge : ∀ (M : (ModuleCat.{max u v w} (U k g))) (n : ℕ),
    (ambient n).hom.app M ≫ (quotientHomology (.up ℕ) n).map (E.restriction.app M) =
      (classicalColumn (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) (O.truncation n) O.degreeZero).app M ≫
        quotientInclusion.evaluation.app ((rightValue (idealInvariants.{u,v,w} h) n).obj M) ≫ (ideal n).hom.app M

/-- The second page with its actual Chevalley–Eilenberg cohomology functor.
The coefficient object is the quotient module identified by `ideal` and
`ideal_action`. -/
def CEComparison.secondPageIso
    {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
    {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
    {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
    {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
    (J : CEComparison h Dg Dh Dq E P O) (p q : ℕ) :
    objectSequence (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P ⋙
      pageEval 0 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≅
      rightValue (idealInvariants.{u,v,w} h) q ⋙ Dq.cohomology p :=
  O.objectCase.secondIso p q ≪≫ Functor.isoWhiskerLeft _ (J.quotient p)

/-- The finite filtered abutment, identified with ambient
Chevalley–Eilenberg cohomology. -/
def CEComparison.targetIso
    {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
    {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
    {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
    {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
    (J : CEComparison h Dg Dh Dq E P O) (n : ℕ) :
    objectSequence (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P ⋙
      targetEval (n : ℤ) ≅ Dg.cohomology n :=
  O.objectCase.targetIso n ≪≫ J.ambient n

/-- The bottom axis is identified by the same quotient CE comparison as
the displayed second page and by the actual degree-zero derived unit. -/
def CEComparison.rowIso
    {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
    {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
    {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
    {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
    (J : CEComparison h Dg Dh Dq E P O) (n : ℕ) :
    objectSequence _ _ P ⋙ pageEval 0 (n : ℤ) (n : ℤ) ≅
      idealInvariants.{u,v,w} h ⋙ Dq.cohomology n :=
  O.rowPage n ≪≫ Functor.isoWhiskerLeft _ (J.quotient n)

/-- The target of restriction keeps the quotient-invariant submodule,
embedded in ideal CE cohomology by evaluation and the same ideal comparison. -/
def CEComparison.restrictToInvariants
    {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
    {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
    {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
    {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
    (J : CEComparison h Dg Dh Dq E P O) (n : ℕ) :
    Dg.cohomology n ⟶ rightValue (idealInvariants.{u,v,w} h) n ⋙ quotientInvariants.{u,v,w} h :=
  (J.ambient n).inv ≫ classicalColumn _ _ (O.truncation n) O.degreeZero

/-- The differential is the page-two differential in bottom and left
axis coordinates, with the latter obtained by the degree-zero evaluation. -/
def CEComparison.transgression
    {Dg : CochainTheory.{u,v,w} k g} {Dh : CochainTheory.{u,v,w} k h}
    {Dq : CochainTheory.{u,v,w} k (g ⧸ h)} {E : EdgeCochains h Dg Dh Dq}
    {P : Package (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h)}
    {O : ObjectEdges (idealInvariants.{u,v,w} h) (quotientInvariants.{u,v,w} h) P}
    (J : CEComparison h Dg Dh Dq E P O) (M : ModuleCat.{max u v w} (U k g)) :
    (rightValue (idealInvariants.{u,v,w} h) 1 ⋙ quotientInvariants.{u,v,w} h).obj M ⟶
      (idealInvariants.{u,v,w} h ⋙ Dq.cohomology 2).obj M :=
  (O.columnPage 1).inv.app M ≫ G05FilteredEdges.transgression ((objectSequence _ _ P).obj M) ≫
    (J.rowIso h 2).hom.app M

/-- The identifications of the second-page and abutment cohomology,
natural in ambient coefficient modules. -/
def CohomologyComparisonStatement : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g),
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k g))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k (g ⧸ h)))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} k)
    ∃ (Dg : CochainTheory.{u,v,w} k g) (Dh : CochainTheory.{u,v,w} k h)
      (Dq : CochainTheory.{u,v,w} k (g ⧸ h)), Nonempty (CohomologyComparison h Dg Dh Dq)

/-- HA-A09 in the inherited diagram representation of spectral sequences.
The second page and finite filtration come from the same object package as
the edge maps. The exact sequence uses its actual page-two differential. -/
def FullStatement : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]
    (h : LieIdeal k g),
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k g))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} (U k (g ⧸ h)))
    letI := HasDerivedCategory.standard (ModuleCat.{max u v w} k)
    ∃ (Dg : CochainTheory.{u,v,w} k g) (Dh : CochainTheory.{u,v,w} k h)
      (Dq : CochainTheory.{u,v,w} k (g ⧸ h)) (E : EdgeCochains h Dg Dh Dq)
      (P : GrothendieckSpectralSequence.Package (idealInvariants.{u,v,w} h)
        (quotientInvariants.{u,v,w} h))
      (O : GrothendieckEdges.ObjectEdges (idealInvariants.{u,v,w} h)
        (quotientInvariants.{u,v,w} h) P),
      ∃ J : CEComparison h Dg Dh Dq E P O,
        (∀ (M : ModuleCat.{max u v w} (U k g)) (r : ℕ) (p n : ℤ), p < 0 ∨ n < p →
          IsZero (((objectSequence _ _ P).obj M).page r p n)) ∧
        ∀ M : ModuleCat.{max u v w} (U k g),
          ClassicalFiveTerms
            ((quotientHomology (.up ℕ) 1).map (E.inflation.app M))
            ((J.restrictToInvariants h 1).app M) (J.transgression h M)
            ((quotientHomology (.up ℕ) 2).map (E.inflation.app M))

end Comparison

end AdvancedHomologicalAlgebra.LieHochschildSerre
