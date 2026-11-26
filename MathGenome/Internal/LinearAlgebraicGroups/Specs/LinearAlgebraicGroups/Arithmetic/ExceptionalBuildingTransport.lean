import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Apartment comparisons before passing to the chamber realization. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace LinearAlgebraicGroups.Specs.ExceptionalBuildingTransport

open ExceptionalAffineBruhat
open ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model integerAlgebra)

attribute [local instance] integerAlgebra

universe u v

noncomputable section

section Apartment

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

abbrev EuclideanApartment (V : Type*) [AddCommGroup V] [Module ℚ V] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℚ V))

abbrev RealCoordinates (V : Type*) [AddCommGroup V] [Module ℚ V] :=
  (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] EuclideanApartment V

def rationalPoint (r : RealCoordinates V) (x : V) : EuclideanApartment V :=
  r (1 ⊗ₜ[ℚ] x)


/-- The linear extension of a normalized rational root functional. -/
def realFunctional (f : V →ₗ[ℚ] ℚ) : (ℝ ⊗[ℚ] V) →ₗ[ℝ] ℝ :=
  (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ).toLinearMap.comp (f.baseChange ℝ)

/-- A Euclidean coordinate system obtained from the sum of squared root evaluations. -/
def RootCoordinates {J : Type*} [Fintype J] (A : ApartmentRoots ℚ V J)
    (r : RealCoordinates V) : Prop :=
  ∀ z, ‖r z‖ ^ 2 = ∑ i, (realFunctional (A.root i) z) ^ 2

variable {V' : Type*} [AddCommGroup V'] [Module ℚ V']

def realAffine (r : RealCoordinates V) (r' : RealCoordinates V') (e : V ≃ᵃ[ℚ] V')
    (x : EuclideanApartment V) : EuclideanApartment V' :=
  r' (e.linear.toLinearMap.baseChange ℝ (r.symm x) + 1 ⊗ₜ[ℚ] e 0)

def Weights (B : Type*) :=
  {t : B → ℝ // (∀ i, 0 ≤ t i) ∧ ∑ᶠ i, t i = 1}

def cotype {B : Type*} (t : Weights B) : Set B := {i | t.val i = 0}

def simplexPoint {B : Type*} (r : RealCoordinates V) (vertex : B → V)
    (t : Weights B) : EuclideanApartment V :=
  ∑ᶠ i, t.val i • rationalPoint r (vertex i)


/-- Transport of the full signed wall equations, including their chosen coroots. -/
structure WallComparison {J J' : Type*} (A : ApartmentRoots ℚ V J)
    (A' : ApartmentRoots ℚ V' J') (p : V) (p' : V') (e : V ≃ᵃ[ℚ] V') where
  walls : J × ℤ ≃ J' × ℤ
  equation (a : J × ℤ) (x : V) : A'.wallValue (walls a) (e x) = A.wallValue a x
  coroot (a : J × ℤ) : e.linear (A.coroot a.1) = A'.coroot (walls a).1
  positive (a : J × ℤ) : A'.positive p' (walls a) ↔ A.positive p a

end Apartment

section Groups

variable {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

def wallSubgroup (T : Set (A.SimpleWall p)) : Subgroup A.affineWeylGroup :=
  Subgroup.closure (A.simpleAffineReflection p '' T)

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}

def parahoric (C : LocalComparison (j := j) (Wf := Wf) A p)
    (T : Set (A.SimpleWall p)) : Subgroup G :=
  Subgroup.closure ((C.I : Set G) ∪
    (fun i => (C.lift (C.coxeter.coxeter.simple i) : G)) '' T)

variable {K' : Type u} [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] {D' : BasedRootDatum.{u}} {M' : Model D'}
  {G' Wf' : Type u} [Group G'] [Group Wf'] {j' : G' →* FieldPoints M' K'}
  {V' : Type u} {J' : Type v} [AddCommGroup V'] [Module ℚ V']
  {A' : ApartmentRoots ℚ V' J'} {p' : V'}
  (C : LocalComparison (j := j) (Wf := Wf) A p)
  (C' : LocalComparison (j := j') (Wf := Wf') A' p')

/-- The labelled map underlying the map on chambers with barycentric weights. -/
structure MarkedTransport (φ : G →* G') (e : V ≃ᵃ[ℚ] V') where
  wall : A.SimpleWall p ≃ A'.SimpleWall p'
  ordinary : A.affineWeylGroup ≃* A'.affineWeylGroup
  wall_value (i : A.SimpleWall p) (x : V) : A'.wallValue (wall i).val (e x) = A.wallValue i.val x
  vertex (i : A.SimpleWall p) (x : V) :
    IsAlcoveVertex A p i x → IsAlcoveVertex A' p' (wall i) (e x)
  label (w : A.affineWeylGroup) (x : V) : (ordinary w).val (e x) = e (w.val x)
  simple (i : A.SimpleWall p) : ordinary (C.coxeter.coxeter.simple i) = C'.coxeter.coxeter.simple (wall i)
  lift (w : A.affineWeylGroup) : φ (C.lift w) * (C'.lift (ordinary w) : G')⁻¹ ∈ C'.T₀
  iwahori : C'.I.comap φ = C.I
  group : C'.G₀.comap φ = C.G₀
  face (T : Set (A.SimpleWall p)) : (parahoric C' (wall '' T)).comap φ = parahoric C T

/-- A marked comparison of a group of coefficient automorphisms. -/
structure CoefficientTransport (Q : C.TypeQuotient) {Γ : Type u} [Group Γ]
    (ρ : Γ →* MulAut G) (e : Γ → V ≃ᵃ[ℚ] V) (r : RealCoordinates V) where
  affine : Γ →* (V ≃ᵃ[ℚ] V)
  affine_eq (σ : Γ) : affine σ = e σ
  types : Γ →* Equiv.Perm (A.SimpleWall p)
  real_isometry (σ : Γ) : Isometry (realAffine r r (e σ))
  marked (σ : Γ) : MarkedTransport C C (ρ σ).toMonoidHom (e σ)
  wall_eq (σ : Γ) : (marked σ).wall = types σ
  quotient : Γ →* MulAut (alcoveStabilizer A (A.alcove p))
  quotient_conj (σ : Γ) (ω : alcoveStabilizer A (A.alcove p)) :
    (quotient σ ω).val.val = e σ * ω.val.val * (e σ)⁻¹
  quotient_natural (σ : Γ) :
    TypeQuotientTransport Q Q (ρ σ).toMonoidHom (quotient σ).toMonoidHom
  quotient_types (σ : Γ) (ω : alcoveStabilizer A (A.alcove p)) :
    Q.wallPerm (quotient σ ω) = types σ * Q.wallPerm ω * (types σ)⁻¹


structure ApartmentIsometries (r : RealCoordinates V) : Prop where
  ordinary (w : A.affineWeylGroup) : Isometry (realAffine r r w.val)
  extended (w : A.extendedAffineWeylGroup) : Isometry (realAffine r r w.val)

structure AdjointApartment (Q : C.TypeQuotient) (r : RealCoordinates V) : Prop where
  faithful : Function.Injective Q.wallPerm
  coefficients (Γ : Type u) [Group Γ] (ρ : Γ →* MulAut G) (e : Γ → V ≃ᵃ[ℚ] V) :
    (∀ σ, AutomorphismComparison C (ρ σ) (e σ)) → Nonempty (CoefficientTransport C Q ρ e r)

structure CentralApartment (φ : G →* G') (e : V ≃ₗ[ℚ] V')
    (r : RealCoordinates V) (r' : RealCoordinates V') where
  marked : MarkedTransport C C' φ e.toAffineEquiv
  isometry : Isometry (realAffine r r' e.toAffineEquiv)
  chambers_onto (y : C'.G₀) :
    ∃ x : C.G₀, (QuotientGroup.mk (φ x) : G' ⧸ C'.I) = QuotientGroup.mk (y : G')

end Groups


open IntegralSemisimpleModel (Integers IntegralGroup)
open ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom pointHom)
open ExceptionalValuedTorusNormalizer (invariantApartment)

section Split

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}

def SplitApartmentLevel (X : SplitLevel F c p p' e)
    (r : RealCoordinates (ℚ ⊗[ℤ] D.Y)) (r' : RealCoordinates (ℚ ⊗[ℤ] E.Y)) : Prop :=
  ApartmentIsometries (A := ApartmentRoots.split D.datum ℚ) r ∧
  ApartmentIsometries (A := ApartmentRoots.split E.datum ℚ) r' ∧
  Nonempty (CentralApartment X.sc X.ad (integralPointHom c.map (CommAlgCat.of Integers.{u} F)) e r r') ∧
  AdjointApartment X.ad X.typeQuotient r'

end Split

/-- Compatible coordinates for the marked split comparisons at all coefficient levels. -/
def SplitApartmentComparisons : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)},
    E.datum.rootSpan ℤ = ⊤ → p' = e p → ∀ (X : SplitLevel F c p p' e),
    ∃ r r', SplitApartmentLevel X r r' ∧
      ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
        [IsNonarchimedeanLocalField K] (Y : SplitLevel K c p p' e), SplitApartmentLevel Y r r'

/-- Compatible coordinates on the normalized folded comparisons over the diagram field
and all its unramified composita. -/
def FoldedApartmentComparisons : Prop :=
  ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {τ : Pinning.BasedIso D D} {τ' : Pinning.BasedIso E E}
    (A : FoldedApartment τ) (A' : FoldedApartment τ')
    (e : invariantApartment D τ ≃ₗ[ℚ] invariantApartment E τ'),
    A'.basepoint = e A.basepoint →
    ∃ (r : RealCoordinates (invariantApartment D τ)) (r' : RealCoordinates (invariantApartment E τ')),
      ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
        {G H Wf Wf' : Type u} [Group G] [Group H] [Group Wf] [Group Wf']
        {j : G →* FieldPoints M K} {j' : H →* FieldPoints M' K}
        (C : LocalComparison (j := j) (Wf := Wf) A.roots A.basepoint)
        (C' : LocalComparison (j := j') (Wf := Wf') A'.roots A'.basepoint)
        (φ : G →* H) (Q : C'.TypeQuotient) (q q' : ℕ),
        C.Bruhat q → C'.Bruhat q' → CentralComparison c φ C C' e →
        C.affine.range = A.roots.affineWeylGroup → C'.affine.range = A'.roots.affineWeylGroup →
        ApartmentIsometries (A := A.roots) r ∧ ApartmentIsometries (A := A'.roots) r' ∧
        Nonempty (CentralApartment C C' φ e r r') ∧ AdjointApartment C' Q r'

/-- The scalar map leaves the apartment and its labels unchanged, and compares the
parahoric cosets and marked length-zero representatives. -/
def ScalarApartmentComparisons : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [ValuativeRel F] [ValuativeRel K]
    [TopologicalSpace F] [TopologicalSpace K] [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D}
    {G H Wf : Type u} [Group G] [Group H] [Group Wf]
    {j : G →* FieldPoints M F} {j' : H →* FieldPoints M K}
    {V J : Type u} [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (j := j) (Wf := Wf) A p)
    (C' : LocalComparison (j := j') (Wf := Wf) A p)
    (f : F →+* K) (s : G →* H) (q q' : ℕ),
    C.Bruhat q → C'.Bruhat q' → ScalarComparison f s C C' →
    (∃ T : MarkedTransport C C' s 1, T.wall = Equiv.refl _ ∧ T.ordinary = MulEquiv.refl _) ∧
    (∀ r : RealCoordinates V, realAffine r r 1 = id) ∧
    ∀ (Q : C.TypeQuotient) (Q' : C'.TypeQuotient),
      TypeQuotientTransport Q Q' s (MonoidHom.id _) →
      (∀ g, letI := Q.normal; letI := Q'.normal
        Q'.quotient (QuotientGroup.mk (s g)) = Q.quotient (QuotientGroup.mk g)) ∧
      ∀ ω, s (Q.lift ω) * (Q'.lift ω : H)⁻¹ ∈ C'.T₀ ∧ Q'.wallPerm ω = Q.wallPerm ω

open ExceptionalIwahoriCongruence (changeRingHom)
open AdjointRepresentation (GroupPoints)

def PointComparisonSquares : Prop :=
  (∀ {R S : IntegralSemisimpleModel.IntegralAlgebra.{u}} {G H : IntegralGroup.{u}}
    (f : G ⟶ H) (a : R ⟶ S) (x : IntegralSemisimpleModel.IntegralPoints G R),
    changeRingHom H a (integralPointHom f R x) = integralPointHom f S (changeRingHom G a x)) ∧
  (∀ {F k K : Type u} [Field F] [Field k] [Field K] [Algebra F k] [Algebra F K]
    {G H : GroupScheme F} (f : G ⟶ H) (a : k →ₐ[F] K) (x : GroupPoints G (CommAlgCat.of F k)),
    coefficientPoints H a (pointHom f ((testSpec F).obj (.op (CommAlgCat.of F k))) x) =
      pointHom f ((testSpec F).obj (.op (CommAlgCat.of F K))) (coefficientPoints G a x))

end
end LinearAlgebraicGroups.Specs.ExceptionalBuildingTransport
