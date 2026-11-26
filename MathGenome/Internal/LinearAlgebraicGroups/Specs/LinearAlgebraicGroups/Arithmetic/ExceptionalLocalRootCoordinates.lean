import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.PinnedPairDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

open CategoryTheory
open scoped WithZero TensorProduct

namespace LinearAlgebraicGroups.Specs.ExceptionalLocalRootCoordinates

open ValuativeRel

noncomputable section

variable (F L : Type*) [Field F] [Field L] [Algebra F L]
  [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L]

/-- The canonical multiplicative integer valuation, with a uniformizer of value `exp (-1)`. -/
def normalizedValuation : Valuation F ℤᵐ⁰ :=
  (valuation F).map
    ⟨(IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMonoidWithZeroHom,
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).strictMono.monotone⟩

variable [ValuativeExtension F L]

omit [TopologicalSpace F] [TopologicalSpace L]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L] in
/-- Extension of the canonical valuations as used by the rings of integers. -/
theorem canonicalExtension : (valuation F).HasExtension (valuation L) :=
  ⟨fun a b ↦ ((valuation F).vle_iff_le).symm.trans
    ((ValuativeExtension.vle_iff_vle a b).symm.trans ((valuation L).vle_iff_le))⟩

attribute [local instance] canonicalExtension

/-- The inclusion of normalized value groups of the two local fields. -/
def normalizedValueGroupMap : ℤᵐ⁰ →*₀ ℤᵐ⁰ :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).toMonoidWithZeroHom.comp
    ((ValuativeExtension.mapValueGroupWithZero F L).comp
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).symm.toMonoidWithZeroHom)

/-- The index of the value groups, measured by the image of the positive generator
in logarithmic coordinates. -/
def ramificationIndex : ℤ :=
  WithZero.log (normalizedValueGroupMap F L (WithZero.exp 1))

/-- The natural map on the actual residue fields of the valuation rings. -/
abbrev residueMap :
    IsLocalRing.ResidueField (valuation F).valuationSubring →+*
      IsLocalRing.ResidueField (valuation L).valuationSubring :=
  algebraMap _ _

/-- For a ramified quadratic extension the normalized valuation doubles on the base
field and the canonical residue field map is bijective. -/
def RamifiedQuadratic : Prop :=
  ∀ (F L : Type*) [Field F] [Field L] [Algebra F L]
    [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L],
    Module.finrank F L = 2 → 1 < ramificationIndex F L →
    ramificationIndex F L = 2 ∧
      (∀ x : F, normalizedValuation L (algebraMap F L x) = (normalizedValuation F x) ^ 2) ∧
      Function.Bijective (residueMap F L)

/-- The extended normalized valuation is invariant under the involution of
a quadratic extension. -/
def InvolutionPreservesValuation : Prop :=
  ∀ {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L] (σ : Gal(L/F)), Function.Involutive σ →
    ∀ x : L, normalizedValuation L (σ x) = normalizedValuation L x

section PinnedPoints

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open AdjointCocharacters (coordinateHopf coordinateHopfMap)
open AdjointBorelCohomology (PinnedTwist)
open AutomorphismSequence (forgetPinning)

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Extend an affine point from the ground field to the splitting field, in
coordinate algebra form. -/
def extendPoint {A : Type u} [CommRing A] [Algebra k A] (p : A →ₐ[k] k) :
    (K ⊗[k] A) →ₐ[K] K :=
  AlgHom.liftEquiv k K A K ((Algebra.ofId k K).comp p)

variable {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
  {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}

/-- Extend a point of the descended group and view it as a point on the split
pinned group through the specified descent isomorphism. -/
def pinnedPointMap (d : PinnedTwist (P := P) K D l B T)
    (p : coordinateHopf G →ₐ[k] k) : extendedHopf K (coordinateHopf P.pair.G) →ₐ[K] K :=
  (extendPoint (K := K) p).comp d.groupIso.hom.hom.toAlgHom

/-- The semilinear operator on the split coordinate Hopf algebra, using the
inverse pullback of the pinned diagram action. -/
def pinnedOperator (d : PinnedTwist (P := P) K D l B T) (σ : Gal(K/k))
    (x : extendedHopf K (coordinateHopf P.pair.G)) :
    extendedHopf K (coordinateHopf P.pair.G) :=
  let f := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv
  (extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) f)).hom
    ((SemilinearAction.scalarExtension (K := K) (coordinateHopf P.pair.G)).act σ x)

/-- The (k)-points of the actual pinned descent are exactly the fixed
(K)-points on the marked split fibre, written as affine coordinate maps. -/
def PinnedFixedPoints : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := P) K D l B T),
    Function.Injective (pinnedPointMap d) ∧
      ∀ p : extendedHopf K (coordinateHopf P.pair.G) →ₐ[K] K,
        p ∈ Set.range (pinnedPointMap d) ↔
          ∀ σ x, p (pinnedOperator d σ x) = σ (p x)


/-- Extend an affine point on any test algebra along the inclusion of the
second tensor factor. -/
def extendAlgebraPoint {A R : Type u} [CommRing A] [Algebra k A]
    [CommRing R] [Algebra k R] (p : A →ₐ[k] R) : (K ⊗[k] A) →ₐ[K] (K ⊗[k] R) :=
  AlgHom.liftEquiv k K A (K ⊗[k] R) (Algebra.TensorProduct.includeRight.comp p)

/-- View an extended point of the descended group in the split pinning. -/
def pinnedAlgebraPointMap (d : PinnedTwist (P := P) K D l B T)
    {R : Type u} [CommRing R] [Algebra k R] (p : coordinateHopf G →ₐ[k] R) :
    extendedHopf K (coordinateHopf P.pair.G) →ₐ[K] (K ⊗[k] R) :=
  (extendAlgebraPoint p).comp d.groupIso.hom.hom.toAlgHom

/-- Coefficient-equivariant algebra maps describe the pinned descent on every
test algebra, including nonreduced algebras. -/
def PinnedAlgebraFixedPoints : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := P) K D l B T) (R : Type u) [CommRing R] [Algebra k R],
    Function.Injective (pinnedAlgebraPointMap d (R := R)) ∧
      ∀ p : extendedHopf K (coordinateHopf P.pair.G) →ₐ[K] (K ⊗[k] R),
        p ∈ Set.range (pinnedAlgebraPointMap d) ↔
          ∀ σ x, p (pinnedOperator d σ x) =
            (SemilinearAction.scalarExtension (K := K) R).act σ (p x)

/-- Points of the affine Hopf algebra with the convolution group law. -/
abbrev HopfPoints {F : Type u} [Field F] (H : HopfAlgebraCategory F)
    (R : Type u) [CommRing R] [Algebra F R] : Type u :=
  (convolutionPoints H).obj (CommAlgCat.of F R)

/-- The fixed-point comparison over the ground field is an isomorphism of groups
for the actual point laws. -/
def PinnedPointGroups : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := P) K D l B T),
    ∃ (H : Subgroup (HopfPoints (extendedHopf K (coordinateHopf P.pair.G)) K))
      (e : HopfPoints (coordinateHopf G) k ≃* H),
      (∀ p, ((e p).val).ofConv = pinnedPointMap d p.ofConv) ∧
      ∀ p, p ∈ H ↔ ∀ σ x, p.ofConv (pinnedOperator d σ x) = σ (p.ofConv x)

/-- Descent on a test algebra preserves the point group in convolution coordinates. -/
def PinnedAlgebraPointGroups : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := P) K D l B T) (R : Type u) [CommRing R] [Algebra k R],
    ∃ (H : Subgroup (HopfPoints (extendedHopf K (coordinateHopf P.pair.G)) (K ⊗[k] R)))
      (e : HopfPoints (coordinateHopf G) R ≃* H),
      (∀ p, ((e p).val).ofConv = pinnedAlgebraPointMap d p.ofConv) ∧
      ∀ p, p ∈ H ↔ ∀ σ x, p.ofConv (pinnedOperator d σ x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (p.ofConv x)

/-- The fixed coordinates of each singleton and swapped pair in a quadratic
descent, on the coefficients and on their units over every test algebra. -/
def QuadraticParameterDescent : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K],
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    ∀ (R : Type u) [CommRing R] [Algebra k R],
      let i : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
      let τ := (SemilinearAction.scalarExtension (K := K) R).act σ
      Function.Injective i ∧
        (∀ x, τ x = x ↔ x ∈ Set.range i) ∧
        (∀ x y, (τ y, τ x) = (x, y) ↔ y = τ x) ∧
        ∀ t : (K ⊗[k] R)ˣ, τ (t : K ⊗[k] R) = t ↔
          t ∈ Set.range (Units.map i.toMonoidHom)

/-- The paired coordinate formulas commute with every base algebra map. -/
def QuadraticParameterNaturality : Prop :=
  ∀ {k K R S : Type u} [Field k] [Field K] [Algebra k K] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (σ : Gal(K/k)) (f : R →ₐ[k] S) (x : K ⊗[k] R),
    let j := Algebra.TensorProduct.map (AlgHom.id k K) f
    j ((SemilinearAction.scalarExtension (K := K) R).act σ x) =
      (SemilinearAction.scalarExtension (K := K) S).act σ (j x)

/-- A pinned automorphism transports the simple coordinate with its character
label, as an equality of group-scheme maps. -/
def PinnedSimpleCoordinates : Prop :=
  ∀ {k : Type u} [Field k] {A : RootGroups.AdditiveLine k} (P : Pinning.PinnedGroup A)
    (f : Aut P) (a : Pinning.SimpleRoot P.pair),
    ∃! b : Pinning.SimpleRoot P.pair,
      b.val.val = Pinning.transportCharacter f.asIso.hom.torus a.val.val ∧
      ((P.pin a).val.hom ≫ (P.roots a.val).val.inclusion) ≫ f.asIso.hom.group.hom =
        (P.pin b).val.hom ≫ (P.roots b.val).val.inclusion

end PinnedPoints

section RankOne

open IntegralRootRelations (upper lower)
open Matrix

/-- Fixed points of one group automorphism, as a subgroup. -/
def fixedSubgroup {G : Type*} [Group G] (τ : MulAut G) : Subgroup G where
  carrier := {g | τ g = g}
  one_mem' := map_one τ
  mul_mem' {g h} hg hh := by
    change τ (g * h) = g * h
    rw [map_mul, show τ g = g from hg, show τ h = h from hh]
  inv_mem' {g} hg := by
    change τ g⁻¹ = g⁻¹
    rw [map_inv, show τ g = g from hg]

/-- The two absolute rank-one maps give a paired rank-one map with values in
the fixed group. It suffices to check commuting and exchange of the upper and
lower unipotent generators. The formulas retain the signs of the lower
coordinates. -/
def PairedRankOne : Prop :=
  ∀ {K G : Type*} [Field K] [Group G] (σ : K ≃+* K) (τ : MulAut G),
    Function.Involutive σ → Function.Involutive τ →
    ∀ (a b : SpecialLinearGroup (Fin 2) K →* G),
      let U := Set.range (upper (R := K)) ∪ Set.range (lower (R := K))
      (∀ A ∈ U, ∀ B ∈ U, Commute (a A) (b B)) →
      (∀ t, τ (a (upper t)) = b (upper (σ t))) →
      (∀ t, τ (a (lower t)) = b (lower (σ t))) →
      ∃ ρ : SpecialLinearGroup (Fin 2) K →* fixedSubgroup τ,
        (∀ A, (ρ A : G) = a A * b (SpecialLinearGroup.map σ.toRingHom A)) ∧
        (∀ t, (ρ (upper t) : G) = a (upper t) * b (upper (σ t))) ∧
        (∀ t, (ρ (lower t) : G) = a (lower t) * b (lower (σ t)))

end RankOne

section OrthogonalRoots

open scoped CategoryTheory.MonObj
open Pinning (AttachedDatum BasedRootDatum PinnedGroup)
open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)

universe u

/-- Orthogonal roots in a simply laced datum have no other roots in the
strict signed two-root cones. The pairing is symmetric on all roots. -/
def OrthogonalRootCombinations : Prop :=
  ∀ (D : BasedRootDatum.{u}),
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ a b, D.datum.pairing a b = 0 →
      (∀ m n : ℤ, m ≠ 0 → n ≠ 0 → m • D.datum.root a ≠ n • D.datum.root b) ∧
      ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
        m • D.datum.root a + n • D.datum.root b ∉ Set.range D.datum.root

/-- Commutation of the actual pinned root subgroups at each choice of signs
of an orthogonal pair, over all test algebras. -/
def OrthogonalRootGroups : Prop :=
  ∀ {k : Type u} [Field k] {A : RootGroups.AdditiveLine k} (P : PinnedGroup A)
    (D : AttachedDatum P.pair),
    (∀ i j, D.toBased.datum.pairing i j = D.toBased.datum.pairing j i) →
    ∀ (a b : Root P.pair.T), D.toBased.datum.pairing a b = 0 →
      ∀ i ∈ ({a, D.toBased.datum.reflectionPerm a a} : Set (Root P.pair.T)),
      ∀ j ∈ ({b, D.toBased.datum.reflectionPerm b b} : Set (Root P.pair.T)),
      ∀ (R : TestAlgebra k)
        (p : GroupPoints (P.roots i).val.group R) (q : GroupPoints (P.roots j).val.group R),
        Commute (p ≫ (P.roots i).val.inclusion.hom.hom : GroupPoints P.pair.G.val R)
          (q ≫ (P.roots j).val.inclusion.hom.hom)

end OrthogonalRoots

section IntegralCoordinates

open scoped CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel

universe u

/-- A marked absolute root point over an integral test algebra. -/
def markedRootPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (z : R) : IntegralPoints M.group R :=
  M.line.point R z ≫ (M.root a).hom.hom

/-- If conjugation by an integral representative identifies two marked root
lines over the fraction field up to scale, that scale is an integral unit.
The conjugation formula then holds over the original domain as well. -/
def IntegralRootTransportUnits : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : IntegralMarking D) (R S : IntegralAlgebra.{u})
    [IsReduced R] (f : R ⟶ S), Function.Injective f.hom →
    ∀ (g : IntegralPoints M.group R) (a b : D.I) (c : Sˣ),
      let n : IntegralPoints M.group S := (integralPointFunctor M.group).map f g
      (∀ z : S, n * markedRootPoint M S a z * n⁻¹ = markedRootPoint M S b ((c : S) * z)) →
      ∃ d : Rˣ, Units.map f.hom.toMonoidHom d = c ∧
        ∀ z : R, g * markedRootPoint M R a z * g⁻¹ = markedRootPoint M R b ((d : R) * z)

end IntegralCoordinates

section Torus

open scoped Classical

open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (IntegralAlgebra Integers IntegralMarking IntegralPoints TorusValues
  integerAlgebra torusPoint)

universe u

variable (D : BasedRootDatum.{u}) {ι : Type u} [Fintype ι]

/-- The character basis dual to a specified basis of the actual cocharacter
lattice of the marked integral torus. -/
def characterBasis (b : Module.Basis ι ℤ D.Y) : Module.Basis ι ℤ D.X :=
  b.dualBasis.map D.datum.toPerfPair.symm

/-- Torus coordinates with respect to an integral cocharacter basis. The
inverse amounts to multiplying the corresponding cocharacters. -/
def TorusBasisCoordinates : Prop :=
  ∀ (D : BasedRootDatum.{u}) {ι : Type u} [Fintype ι] (b : Module.Basis ι ℤ D.Y)
    (R : IntegralAlgebra.{u}),
    ∃ e : TorusValues D R ≃* (ι → Rˣ),
      (∀ t i, e t i = t (Multiplicative.ofAdd (characterBasis D b i))) ∧
      ∀ (u : ι → Rˣ) (x : D.X),
        e.symm u (Multiplicative.ofAdd x) = ∏ i, u i ^ (D.datum.toLinearMap x (b i))

/-- The actual simple coroot basis in the simply connected case. -/
def simpleCorootBasis (h : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Module.Basis D.base.support ℤ D.Y :=
  Module.Basis.mk D.base.linearIndepOn_coroot <| by
    change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.coroot ∘ ((↑) : D.base.support → D.I)))
    rw [Set.range_comp, Subtype.range_coe, D.base.span_int_coroot_support, h]

/-- The actual fundamental coweight basis in the adjoint case. -/
def fundamentalCoweightBasis (h : Submodule.span ℤ (Set.range D.datum.root) = ⊤) :
    Module.Basis D.base.support ℤ D.Y :=
  let b : Module.Basis D.base.support ℤ D.X :=
    Module.Basis.mk D.base.linearIndepOn_root <| by
      change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
      rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support, h]
  b.dualBasis.map D.datum.toLinearMap.flip.toPerfPair.symm

/-- The bases used to evaluate the simply connected and adjoint tori. -/
def ExceptionalCocharacterBases : Prop :=
  ∀ D : BasedRootDatum.{u},
    (∀ (h : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) (i : D.base.support),
      simpleCorootBasis D h i = D.datum.coroot i) ∧
    ∀ (h : Submodule.span ℤ (Set.range D.datum.root) = ⊤) (i j : D.base.support),
      D.datum.toLinearMap (D.datum.root j) (fundamentalCoweightBasis D h i) =
        if j = i then 1 else 0

attribute [local instance] integerAlgebra

/-- The normalized apartment translation of a marked split torus surjects
onto its cocharacter lattice. Its kernel is the unit torus. -/
def SplitTorusTranslation : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : BasedRootDatum.{u})
    {ι : Type u} [Fintype ι] (b : Module.Basis ι ℤ D.Y),
    ∃ ν : TorusValues D (CommAlgCat.of Integers.{u} K) →* Multiplicative D.Y,
      Function.Surjective ν ∧
      (∀ t x, D.datum.toLinearMap x (ν t).toAdd =
        WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd x) : K))) ∧
      ∀ t, ν t = 1 ↔
        ∀ i, normalizedValuation K (t (Multiplicative.ofAdd (characterBasis D b i)) : K) = 1

open scoped CategoryTheory.MonObj in
/-- Conjugation by the marked split torus shifts the root filtration by the
valuation of the root character. The strict threshold shifts by the same value. -/
def MarkedTorusLayerConjugation : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (t : TorusValues D (CommAlgCat.of Integers.{u} K)) (a : D.I) (z : K) (j : ℤ),
    let R := CommAlgCat.of Integers.{u} K
    let g : IntegralPoints M.group R := torusPoint D R t ≫ M.torus.hom.hom
    let c := (t (Multiplicative.ofAdd (D.datum.root a)) : K)
    let d := WithZero.log (normalizedValuation K c)
    g * markedRootPoint M R a z * g⁻¹ = markedRootPoint M R a (c * z) ∧
      (normalizedValuation K (c * z) ≤ WithZero.exp (d - j) ↔
        normalizedValuation K z ≤ WithZero.exp (-j)) ∧
      (normalizedValuation K (c * z) < WithZero.exp (d - j) ↔
        normalizedValuation K z < WithZero.exp (-j))

/-- With the extension valuation normalized on the base field, a fixed torus
factor has integral translation and a paired factor has simultaneous
half-integral translation in its two absolute cocharacter directions. -/
def FoldedTorusFactorValuations : Prop :=
  ∀ (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [ValuativeRel F] [ValuativeRel L] [TopologicalSpace F] [TopologicalSpace L]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F L],
    Module.finrank F L = 2 → 1 < ramificationIndex F L →
    ∀ (σ : Gal(L/F)), Function.Involutive σ →
      Set.range (fun u : Fˣ ↦
        ((WithZero.log (normalizedValuation L (algebraMap F L (u : F))) : ℤ) : ℚ) / 2) =
          Set.range (fun n : ℤ ↦ (n : ℚ)) ∧
      Set.range (fun u : Lˣ ↦
        (((WithZero.log (normalizedValuation L (u : L)) : ℤ) : ℚ) / 2,
         ((WithZero.log (normalizedValuation L (σ (u : L))) : ℤ) : ℚ) / 2)) =
          Set.range (fun n : ℤ ↦ ((n : ℚ) / 2, (n : ℚ) / 2))

end Torus

section PointSubgroups

/-- Reduction into the Borel cuts out the integral torus on the normalizer
when integral Weyl lifts retain their labels in the special fibre. -/
def IwahoriNormalizerIntersection : Prop :=
  ∀ {G G₀ W : Type*} [Group G] [Group G₀] [Group W]
    (K T N : Subgroup G), T ≤ N → ∀ (red : K →* G₀) (B : Subgroup G₀) (lift : W → K),
    (∀ t : K, (t : G) ∈ T → red t ∈ B) →
    (∀ w, red (lift w) ∈ B ↔ w = 1) →
    (∀ n ∈ N, ∃ (t : T) (w : W), n = (t : G) * (lift w : G)) →
    lift 1 = 1 → (B.comap red).map K.subtype ⊓ N = T ⊓ K

/-- Rational Bruhat coverage and conjugating the root groups into the
Iwahori give generation by the Iwahori and the normalizer. -/
def IwahoriNormalizerGeneration : Prop :=
  ∀ {G ι : Type*} [Group G] (I N T B : Subgroup G) (X : ι → Subgroup G),
    T ≤ N → B ≤ T ⊔ (⨆ i, X i) →
    (∀ g : G, ∃ (b c : B) (n : N), g = (b : G) * n * c) →
    (∀ i (x : X i), ∃ t : N, (t : G) * x * (t : G)⁻¹ ∈ I) → I ⊔ N = ⊤

/-- The algebraic quotient calculation after factoring the ambient point
group as the simply connected image times the torus. The subgroup of the
translation lattice is the image of the torus points that lift. -/
def OrdinarySubgroupQuotient : Prop :=
  ∀ {Gsc G Y : Type*} [Group Gsc] [Group G] [CommGroup Y]
    (p : Gsc →* G) (T : Subgroup G) (ν : T →* Y), Function.Surjective ν →
    (∀ g : G, ∃ (x : Gsc) (t : T), g = p x * t) →
    (∀ t : T, ∀ x : Gsc, (t : G) * p x * (t : G)⁻¹ ∈ p.range) →
    let H := p.range ⊔ ν.ker.map T.subtype
    let Λ := (p.range.comap T.subtype).map ν
    ∃ (_ : H.Normal) (e : G ⧸ H ≃* Y ⧸ Λ),
      ∀ t : T, e (QuotientGroup.mk (t : G)) = QuotientGroup.mk (ν t)

end PointSubgroups

section LocalPointGroups

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model IntegralPoints Integers integerAlgebra)
open ExceptionalMarkedRootDescent (MarkedFibre SimpleRootOrbit TransportedOrbit transportedLabels
  pinnedDiagram)
open ExceptionalValuedTorusNormalizer (FibreNormalizer fixedWeylGroup simplePermutation
  markedDiagramEquiv orbitProjection)
open ExceptionalIwahoriImageComparison (MarkedLocalNormalizer markedBorelReduction
  integralUnitTorus markedPositiveBorel MarkedCentralCover integralPointHom)
open OrderedRootProducts (Enumerates)

universe u

attribute [local instance] integerAlgebra

/-- The rational point group and the integral positive Borel reduction use
the same marked model as the normalizer, its translation map and its lifts. -/
structure LocalIwahori {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G : Type u} [Group G] (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (W : Type u) [Group W] where
  normalizer : MarkedLocalNormalizer K j W
  residueFibre : MarkedFibre M (IsLocalRing.ResidueField (valuation K).valuationSubring)
  residueBorel : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
    (IsLocalRing.ResidueField (valuation K).valuationSubring)))
  borel_eq : (residueBorel : Set _) = markedPositiveBorel residueFibre
    (CommAlgCat.of (IsLocalRing.ResidueField (valuation K).valuationSubring)
      (IsLocalRing.ResidueField (valuation K).valuationSubring))
  intersection : (markedBorelReduction M.group residueBorel).comap j ⊓ normalizer.normalizer =
    (integralUnitTorus (K := K) M).comap j
  generation : (markedBorelReduction M.group residueBorel).comap j ⊔ normalizer.normalizer = ⊤

/-- The Iwahori in the rational points, obtained by the marked reduction. -/
def LocalIwahori.iwahori {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G : Type u} [Group G] {j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
    {W : Type u} [Group W] (P : LocalIwahori j W) : Subgroup G :=
  (markedBorelReduction M.group P.residueBorel).comap j

/-- Identify two finite Weyl label groups without changing the marked
points, their reduction, or their torus translations. -/
def LocalIwahori.relabel {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G : Type u} [Group G] {j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
    {W W' : Type u} [Group W] [Group W'] (P : LocalIwahori j W) (e : W ≃* W') :
    LocalIwahori j W' :=
  let N := P.normalizer
  { normalizer :=
      { torus := N.torus
        normalizer := N.normalizer
        torus_le := N.torus_le
        torusPoints := N.torusPoints
        label := e.toMonoidHom.comp N.label
        labelKernel := fun n => (show e (N.label n) = 1 ↔ N.label n = 1 by
          rw [← e.map_one, e.injective.eq_iff]).trans (N.labelKernel n)
        translation := N.translation
        characterLog := N.characterLog
        word := N.word ∘ e.symm
        lift := N.lift ∘ e.symm
        lift_label := fun w => by change e (N.label (N.lift (e.symm w))) = w
                                  rw [N.lift_label, e.apply_symm_apply]
        lift_point := fun w => N.lift_point (e.symm w) }
    residueFibre := P.residueFibre
    residueBorel := P.residueBorel
    borel_eq := P.borel_eq
    intersection := P.intersection
    generation := P.generation }

/-- The split marked normalizer, Borel reduction, and their generation of
the actual field points. The basis may be the coroot or the coweight basis. -/
def SplitLocalIwahori : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    {index : Type u} [Fintype index] (_b : Module.Basis index ℤ D.Y)
    (word : D.datum.weylGroup → List D.I),
    (∀ w, ∀ a ∈ word w, a ∈ D.base.support) →
    (∀ w, ((word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w) →
    let R := CommAlgCat.of Integers.{u} K
    ∃ (P : LocalIwahori (M := M) (MonoidHom.id (IntegralPoints M.group R)) D.datum.weylGroup)
      (F : FibreNormalizer M K),
      (∀ g, ExceptionalIwahoriImageComparison.markedGroundPoint C g ∈ P.normalizer.normalizer ↔
        Normalizes C.realization.pinned.pair.T.inclusion g) ∧
      (∀ n : P.normalizer.normalizer, ∃ m, F.point m = (n : IntegralPoints M.group R) ∧
        F.label m = P.normalizer.label n) ∧
      P.normalizer.word = word ∧ Function.Surjective P.normalizer.translation ∧
      P.normalizer.translation.ker.map P.normalizer.torus.subtype = integralUnitTorus (K := K) M

/-- With the finite orbit lists and Weyl words, the ramified pinned point
group has the actual relative normalizer and projected translation lattice.
The normalizer used for generation is the one in the intersection formula. -/
def FoldedLocalIwahori : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G},
    AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q →
    ∀ {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
      (d : PinnedPairDescent.DescendedPair (l := l) K ω) (σ : Gal(K/k)),
    Module.finrank k K = 2 → σ ≠ 1 → 1 < ramificationIndex k K →
    let e := (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom
    let W := fixedWeylGroup D e
    (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
    (∀ i : D.base.support, simplePermutation D e i ≠ i →
      D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    ∀ (b : Module.Basis D.base.support ℤ D.Y),
    ((∃ h, b = ExceptionalValuedTorusNormalizer.simpleCorootBasis D h) ∨
      (∃ h, b = ExceptionalValuedTorusNormalizer.fundamentalCoweightBasis D h)) →
    ∀ (ns ps : List (TransportedOrbit D)),
    (∀ a ∈ ns ++ ps, a.1.Matches C (pinnedDiagram d.data σ) ∧
      ∀ o ∈ a.2, o.Matches C (pinnedDiagram d.data σ)) →
    Enumerates (ns.flatMap transportedLabels) {a | ¬ D.base.IsPos a} →
    Enumerates (ps.flatMap transportedLabels) {a | D.base.IsPos a} →
    ∀ (word : W → List (SimpleRootOrbit D)),
    (∀ w, ∀ o ∈ word w, o.Matches C (pinnedDiagram d.data σ)) →
    (∀ w, (((word w).flatMap SimpleRootOrbit.roots).map
      (RootPairing.weylGroup.ofIdx D.datum)).prod = w.val) →
    let R := CommAlgCat.of Integers.{u} K
    ∃ (j : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →* IntegralPoints M.group R)
      (P : LocalIwahori (M := M) j W) (F : FibreNormalizer M K)
      (S : ClosedSubgroup d.group.val),
      Function.Injective j ∧
      (∀ g, j g = ExceptionalIwahoriImageComparison.pinnedGroundPoint C d.data g) ∧
      Relative.MaximalSplitTori.IsMaximalSplitTorus S ∧
      (∀ g, g ∈ P.normalizer.normalizer ↔ Normalizes S.inclusion g) ∧
      (∀ g, g ∈ P.normalizer.normalizer ↔ Normalizes d.torus.inclusion g) ∧
      (∀ g, g ∈ P.normalizer.torus ↔ SchemeDerivedGroup.FactorsThrough d.torus g) ∧
      (∀ n : P.normalizer.normalizer, ∃ m, F.point m = j n ∧
        F.label m = (P.normalizer.label n).val) ∧
      (∀ w, P.normalizer.word w = (word w).flatMap SimpleRootOrbit.roots) ∧
      P.normalizer.translation.ker.map P.normalizer.torus.subtype =
        (integralUnitTorus (K := K) M).comap j ∧
      Set.range (fun t : P.normalizer.torus => fun i : D.base.support =>
        ((b.repr (P.normalizer.translation t).toAdd i : ℤ) : ℚ) / 2) =
        Set.range (orbitProjection (simplePermutation D e))

/-- The type-preserving subgroup and its quotient on the actual marked
adjoint group. Here `Λ` is the image of the translations that lift to the
simply connected torus. Membership in the ordinary normalizer is tested
on the translation part of the affine action. -/
def OrdinaryLocalQuotient {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A) {G G' W : Type u} [Group G] [Group G'] [Group W]
    {j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
    {j' : G' →* IntegralPoints A.group (CommAlgCat.of Integers.{u} K)}
    (P : LocalIwahori j W) (P' : LocalIwahori j' W) (p : G →* G') : Prop :=
  let N := P.normalizer
  let N' := P'.normalizer
  let U := (integralUnitTorus (K := K) A).comap j'
  let Y := N'.translation.range
  let ν := N'.translation.rangeRestrict
  let Λ := ((N.torus.map p).comap N'.torus.subtype).map ν
  let J := N.normalizer.map p ⊔ U
  let H := P'.iwahori ⊔ J
  (∀ n : N.normalizer, ∀ hn : p n ∈ N'.normalizer, N'.label ⟨p n, hn⟩ = N.label n) ∧
  (∀ t : N.torus, ∀ ht : p t ∈ N'.torus,
    (N'.translation ⟨p t, ht⟩).toAdd = c.pushCocharacter (N.translation t).toAdd) ∧
  (∀ n : N'.normalizer, (n : G') ∈ J ↔ ν (N'.torusPart n) ∈ Λ) ∧
  H = p.range ⊔ U ∧ H ⊓ N'.normalizer = J ∧
  (∀ g, g ∈ H ↔ ∃ (x : G) (t : U), g = p x * t) ∧
  ∃ (_ : H.Normal) (q : G' ⧸ H ≃* Y ⧸ Λ),
    ∀ t : N'.torus, q (QuotientGroup.mk (t : G')) = QuotientGroup.mk (ν t)

/-- The ordinary subgroup and quotient for the actual split simply connected
and adjoint integral models and their marked central map. -/
def SplitOrdinaryLocalIwahori : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A), D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
    let R := CommAlgCat.of Integers.{u} K
    let p := integralPointHom c.map R
    ∃ (P : LocalIwahori (M := M) (MonoidHom.id (IntegralPoints M.group R)) D.datum.weylGroup)
      (P' : LocalIwahori (M := A) (MonoidHom.id (IntegralPoints A.group R)) D.datum.weylGroup),
      P'.iwahori.comap p = P.iwahori ∧
      Function.Surjective P.normalizer.translation ∧ Function.Surjective P'.normalizer.translation ∧
      Set.range (fun t : P.normalizer.torus => c.pushCocharacter (P.normalizer.translation t).toAdd) =
        (E.datum.corootSpan ℤ : Set E.Y) ∧
      OrdinaryLocalQuotient c P P' p

/-- The ordinary subgroup comparison for the two ramified pinned forms.
Only one set of finite root words is needed: the central map identifies
the roots and carries the words to those of the other model. -/
def FoldedOrdinaryLocalIwahori : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension k K]
    {D E : BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A), D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
    ∀ (C : MarkedFibre M k) (C' : MarkedFibre A k)
      {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
      {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
      {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G}
      {Q' : AutomorphismSequence.AdjointQuotient C'.realization.pinned.pair.G},
    AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q →
    AutomorphismSequence.SplitSequence C'.realization.pinned C'.realization.attached l' Q' →
    ∀ {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
      {ω' : Gal(K/k) →* Aut C'.realization.attached.toBased}
      (d : PinnedPairDescent.DescendedPair (l := l) K ω)
      (d' : PinnedPairDescent.DescendedPair (l := l') K ω') (σ : Gal(K/k)),
    Module.finrank k K = 2 → σ ≠ 1 → 1 < ramificationIndex k K →
    let e := (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom
    let e' := (markedDiagramEquiv C'.realization (d'.data.outer σ)).asIso.hom
    let W := fixedWeylGroup D e
    (∀ a, c.rootEquiv (e.val.indexEquiv a) = e'.val.indexEquiv (c.rootEquiv a)) →
    (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
    (∀ i : D.base.support, simplePermutation D e i ≠ i →
      D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    ∀ (ns ps : List (TransportedOrbit D)),
    (∀ a ∈ ns ++ ps, a.1.Matches C (pinnedDiagram d.data σ) ∧
      ∀ o ∈ a.2, o.Matches C (pinnedDiagram d.data σ)) →
    Enumerates (ns.flatMap transportedLabels) {a | ¬ D.base.IsPos a} →
    Enumerates (ps.flatMap transportedLabels) {a | D.base.IsPos a} →
    ∀ (word : W → List (SimpleRootOrbit D)),
    (∀ w, ∀ o ∈ word w, o.Matches C (pinnedDiagram d.data σ)) →
    (∀ w, (((word w).flatMap SimpleRootOrbit.roots).map
      (RootPairing.weylGroup.ofIdx D.datum)).prod = w.val) →
    let R := CommAlgCat.of Integers.{u} K
    ∃ (f : d.group.val ⟶ d'.group.val)
      (j : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →* IntegralPoints M.group R)
      (j' : (𝟙_ (SchemeOver k) ⟶ d'.group.val.X) →* IntegralPoints A.group R)
      (P : LocalIwahori (M := M) j W) (P' : LocalIwahori (M := A) j' W),
      let p := ExceptionalIwahoriImageComparison.pointHom f (𝟙_ (SchemeOver k))
      CentralIsogenies.IsCentralIsogeny f ∧
      (∀ g, j g = ExceptionalIwahoriImageComparison.pinnedGroundPoint C d.data g) ∧
      (∀ g, j' g = ExceptionalIwahoriImageComparison.pinnedGroundPoint C' d'.data g) ∧
      (∀ g, j' (p g) = integralPointHom c.map R (j g)) ∧
      P'.iwahori.comap p = P.iwahori ∧ OrdinaryLocalQuotient c P P' p

end LocalPointGroups

section NormalizerAction

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model IntegralPoints Integers integerAlgebra TorusValues torusPoint
  integralPointFunctor)
open ExceptionalMarkedRootDescent (markedRootPoint markedWeylWord markedWall)
open ExceptionalIwahoriImageComparison (MarkedLocalNormalizer integralUnitTorus)
open ExceptionalValuedTorusNormalizer (FibreNormalizer invariantApartment fixedWeylGroup
  orbitProjection simplePermutation valuationRingInclusion)

universe u

attribute [local instance] integerAlgebra

/-- A marked normalizer element permutes the root slots by its actual Weyl
label. The difference in integer depths is the root pairing with the
translation, with the sign convention of the affine root half-spaces. -/
def MarkedNormalizerRootLayers : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} {G W : Type u} [Group G] [Group W]
    (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (N : MarkedLocalNormalizer K j W) (q : W →* D.datum.weylGroup),
    (∀ w, ((N.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = q w) →
    let R := CommAlgCat.of Integers.{u} K
    let x := markedRootPoint M.toIntegralMarking R
    let v := normalizedValuation K
    ∀ (n : N.normalizer) (a : D.I),
      let b := (q (N.label n)).val.indexEquiv a
      let d := D.datum.toLinearMap (D.datum.root b) (N.translation (N.torusPart n)).toAdd
      ∃ c : Kˣ, v (c : K) = WithZero.exp d ∧
        ∀ (u : K),
          j n * x a u * (j n)⁻¹ = x b ((c : K) * u) ∧
          ∀ m : ℤ,
            (v u ≤ WithZero.exp (-m) ↔ v ((c : K) * u) ≤ WithZero.exp (-(m - d))) ∧
            (v u < WithZero.exp (-m) ↔ v ((c : K) * u) < WithZero.exp (-(m - d)))

/-- The affine action and its kernel for a marked normalizer sitting in
the split normalizer. Rescaling by one half uses the base-field units of
depth in the ramified quadratic case. -/
def MarkedNormalizerApartment : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    {index : Type u} [Fintype index] (_b : Module.Basis index ℤ D.Y)
    {G W : Type u} [Group G] [Group W]
    (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (N : MarkedLocalNormalizer K j W) (q : W →* D.datum.weylGroup),
    Function.Injective q →
    (∀ n : N.normalizer, ∃ m, F.point m = j n ∧ F.label m = q (N.label n)) →
    ∀ r : ℚˣ,
      let V := ℚ ⊗[ℤ] D.Y
      ∃ a : N.normalizer →* (V ≃ᵃ[ℚ] V),
        a.ker.map N.normalizer.subtype = (integralUnitTorus (K := K) M).comap j ∧
        (∀ (n : N.normalizer) (x : V),
          a n x = ((q (N.label n)).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) x +
            ((r : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd)) ∧
        letI := F.torusComm
        let R := CommAlgCat.of Integers.{u} K
        ∀ (n : N.normalizer) (m : 𝟙_ (SchemeOver K) ⟶ F.identification.normalizer.group.X),
          F.label m = q (N.label n) →
          F.point m ∈ ((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range →
          ∀ (t : TorusValues D R), j n * (F.point m)⁻¹ = torusPoint D R t ≫ M.torus.hom.hom →
            ∀ χ, D.datum.toLinearMap χ (N.translation (N.torusPart n)).toAdd =
              WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd χ) : K))

/-- The folded action restricts to the invariant cocharacter apartment
with the same unit-torus kernel. The translation vectors are the ones in
the projected lattice of the marked rational torus. -/
def FoldedNormalizerApartment : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    (e : Pinning.BasedIso D D) (b : Module.Basis D.base.support ℤ D.Y),
    ((∃ h, b = ExceptionalValuedTorusNormalizer.simpleCorootBasis D h) ∨
      (∃ h, b = ExceptionalValuedTorusNormalizer.fundamentalCoweightBasis D h)) →
    Function.Involutive e.val.indexEquiv →
    (∀ i : D.base.support, simplePermutation D e i ≠ i →
      D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    ∀ {G : Type u} [Group G] (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
      (N : MarkedLocalNormalizer K j (fixedWeylGroup D e)),
    (∀ n : N.normalizer, ∃ m, F.point m = j n ∧ F.label m = (N.label n).val) →
    Set.range (fun t : N.torus => fun i : D.base.support =>
      ((b.repr (N.translation t).toAdd i : ℤ) : ℚ) / 2) =
      Set.range (orbitProjection (simplePermutation D e)) →
    let V := invariantApartment D e
    ∃ a : N.normalizer →* (V ≃ᵃ[ℚ] V),
      a.ker.map N.normalizer.subtype = (integralUnitTorus (K := K) M).comap j ∧
      ∀ (n : N.normalizer) (x : V),
        (a n x).val = ((N.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y) x.val +
          ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd)

/-- A transported rank-one wall word is in the actual rational normalizer
with the specified finite label. For a fixed orbit use a singleton list
and a parameter in the base field. For a paired orbit use the two
commuting rank-one terms at the conjugate parameters. -/
def MarkedWallNormalizer : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    {G W : Type u} [Group G] [Group W]
    (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (N : MarkedLocalNormalizer K j W) (q : W →* D.datum.weylGroup),
    Function.Injective q →
    (∀ n : N.normalizer, ∃ m, F.point m = j n ∧ F.label m = q (N.label n)) →
    ∀ (transport : List D.I), (∀ a ∈ transport, a ∈ D.base.support) →
    ∀ (orbit : List (D.base.support × Kˣ)),
    let R := CommAlgCat.of Integers.{u} K
    let s := RootPairing.weylGroup.ofIdx D.datum
    let w := (transport.map s).prod
    let m := markedWeylWord M.toIntegralMarking R transport
    ∀ (l : W), q l = w * (orbit.map fun p => s p.1.val).prod * w⁻¹ →
    ∀ g : G, j g = m * (orbit.map fun p => markedWall M.toIntegralMarking R p.1.val p.2).prod * m⁻¹ →
      ∃ n : N.normalizer, (n : G) = g ∧ N.label n = l

/-- The translation of a transported wall is the coroot times the log of
its parameter valuation. For an orthogonal pair the two coroot terms add.
Combine this with the half-scale affine action for the ramified form. -/
def MarkedWallDisplacements : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    {index : Type u} [Fintype index] (_b : Module.Basis index ℤ D.Y)
    {G W : Type u} [Group G] [Group W]
    (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (N : MarkedLocalNormalizer K j W) (q : W →* D.datum.weylGroup),
    Function.Injective q →
    (∀ n : N.normalizer, ∃ m, F.point m = j n ∧ F.label m = q (N.label n)) →
    ∀ (transport : List D.I), (∀ a ∈ transport, a ∈ D.base.support) →
    let R := CommAlgCat.of Integers.{u} K
    let s := RootPairing.weylGroup.ofIdx D.datum
    let w := (transport.map s).prod
    let c := w.val.coweightEquiv.symm
    let m := markedWeylWord M.toIntegralMarking R transport
    let wall := markedWall M.toIntegralMarking R
    let z := fun (a : D.base.support) (u : Kˣ) =>
      WithZero.log (normalizedValuation K (u : K)) • D.datum.coroot a.val
    (∀ (a : D.base.support) (p : Kˣ) (n : N.normalizer),
      q (N.label n) = w * s a.val * w⁻¹ →
      j n = m * wall a.val p * m⁻¹ →
      (N.translation (N.torusPart n)).toAdd = c (z a p)) ∧
    (∀ (a b : D.base.support) (p v : Kˣ) (n : N.normalizer),
      (∀ a b, D.datum.pairing a b = D.datum.pairing b a) → D.datum.pairing a b = 0 →
      q (N.label n) = w * (s a.val * s b.val) * w⁻¹ →
      j n = m * (wall a.val p * wall b.val v) * m⁻¹ →
      (N.translation (N.torusPart n)).toAdd = c (z a p + z b v))

open scoped Classical in
/-- Preservation of the signed affine thresholds by a split normalizer
element implies that it normalizes the marked Iwahori. In particular the
finite affine geometry can apply this to the alcove stabilizer. -/
def SplitIwahoriStabilizer : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    {index : Type u} [Fintype index] (_b : Module.Basis index ℤ D.Y),
    let R := CommAlgCat.of Integers.{u} K
    let j := MonoidHom.id (IntegralPoints M.group R)
    ∀ (P : LocalIwahori (M := M) j D.datum.weylGroup),
    let N := P.normalizer
    (∀ w, ((N.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w) →
    (∀ n : N.normalizer, ∃ m, F.point m = (n : IntegralPoints M.group R) ∧ F.label m = N.label n) →
    ∀ (n : N.normalizer),
    let perm := (N.label n).val.indexEquiv
    let depth := fun a : D.I => if D.base.IsPos a then (0 : ℤ) else 1
    (∀ a, depth (perm a) = depth a -
      D.datum.toLinearMap (D.datum.root (perm a)) (N.translation (N.torusPart n)).toAdd) →
    ∀ g : IntegralPoints M.group R, g ∈ P.iwahori ↔
      (n : IntegralPoints M.group R) * g * (n : IntegralPoints M.group R)⁻¹ ∈ P.iwahori

end NormalizerAction

section PinnedWalls

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model IntegralPoints Integers integerAlgebra)
open ExceptionalMarkedRootDescent (MarkedFibre SimpleRootOrbit pinnedDiagram markedWeylWord wallMatrix)
open ExceptionalValuedTorusNormalizer (FibreNormalizer)
open ExceptionalIwahoriImageComparison (MarkedLocalNormalizer pinnedGroundPoint)
open AdjointBorelCohomology (PinnedTwist)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutation)
open Matrix (SpecialLinearGroup)

universe u

attribute [local instance] integerAlgebra

/-- The pinned action on a simple orbit can be read directly from the
finite diagram permutation and the root pairing on the marked datum. -/
def PinnedSimpleOrbitCriterion : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G},
    SplitSequence C.realization.pinned C.realization.attached l Q →
    ∀ {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
      (d : PinnedTwist K C.realization.attached l B T) (σ : Gal(K/k))
      (o : SimpleRootOrbit D),
    let e := (markedDiagramEquiv C.realization (d.outer σ)).asIso.hom
    o.Matches C (pinnedDiagram d σ) ↔
      match o.2 with
      | none => simplePermutation D e o.1 = o.1
      | some b => D.datum.pairing o.1 b = 0 ∧
          simplePermutation D e o.1 = b ∧ simplePermutation D e b = o.1

/-- The descended singleton and paired rank-one maps on rational points
give normalizer lifts at every unit parameter. The input label only
records the finite folded reflection for the indicated orbit. -/
def PinnedRankOneWallLifts : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k) (F : FibreNormalizer M K)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
    let R := CommAlgCat.of Integers.{u} K
    let H := (𝟙_ (SchemeOver k) ⟶ G.val.X)
    ∀ {W : Type u} [Group W] (j : H →* IntegralPoints M.group R)
      (N : MarkedLocalNormalizer K j W) (q : W →* D.datum.weylGroup),
    (∀ g, j g = pinnedGroundPoint C d g) →
    Function.Injective q →
    (∀ n : N.normalizer, ∃ m, F.point m = j n ∧ F.label m = q (N.label n)) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
    let word := w.flatMap SimpleRootOrbit.roots
    let s := RootPairing.weylGroup.ofIdx D.datum
    let e := (word.map s).prod
    let n := markedWeylWord M.toIntegralMarking R word
    (∀ a : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, none) →
      ∃ ρ : SpecialLinearGroup (Fin 2) k →* H,
        (∀ A, j (ρ A) = n *
          (show IntegralPoints M.group R from
            (M.rankOne a).app R (SpecialLinearGroup.map (algebraMap k K) A)) * n⁻¹) ∧
        ∀ v : W, q v = e * s a.val * e⁻¹ → ∀ p : kˣ, ∃ m : N.normalizer,
          (m : H) = ρ (wallMatrix p) ∧ N.label m = v) ∧
    (∀ a b : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, some b) →
      ∃ ρ : SpecialLinearGroup (Fin 2) K →* H,
        (∀ A, j (ρ A) = n * ((show IntegralPoints M.group R from (M.rankOne a).app R A) *
          (show IntegralPoints M.group R from
            (M.rankOne b).app R (SpecialLinearGroup.map σ.toRingHom A))) * n⁻¹) ∧
        ∀ v : W, q v = e * (s a.val * s b.val) * e⁻¹ → ∀ p : Kˣ, ∃ m : N.normalizer,
          (m : H) = ρ (wallMatrix p) ∧ N.label m = v)

end PinnedWalls

end

end LinearAlgebraicGroups.Specs.ExceptionalLocalRootCoordinates
