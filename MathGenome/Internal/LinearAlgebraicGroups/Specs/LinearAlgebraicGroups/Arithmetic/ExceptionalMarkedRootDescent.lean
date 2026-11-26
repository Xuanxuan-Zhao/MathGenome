import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.PinnedPairDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import Mathlib.NumberTheory.LocalField.Basic

open CategoryTheory
open scoped WithZero TensorProduct

namespace LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent

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
open Matrix (SpecialLinearGroup)

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
attribute [local instance] IntegralSemisimpleModel.integerAlgebra

open Pinning (BasedRootDatum)
open IntegralSemisimpleModel
universe u

/-- Multiplication by a nonzero parameter shifts both valuation thresholds
by its additive valuation, in the integer normalization of the parameter field. -/
def RootFiltrationShift (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (c : Kˣ) : Prop :=
  let v := normalizedValuation K
  let d := WithZero.log (v (c : K))
  ∀ (z : K) (j : ℤ),
    (v ((c : K) * z) ≤ WithZero.exp (d - j) ↔ v z ≤ WithZero.exp (-j)) ∧
    (v ((c : K) * z) < WithZero.exp (d - j) ↔ v z < WithZero.exp (-j))

/-- Conjugation carries the images of the weak and strict parameter layers
onto the root layers at the shifted threshold. -/
def RootLayerConjugation (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {H : Type u} [Group H]
    (x : K → H) (t : H) (c : Kˣ) : Prop :=
  let v := normalizedValuation K
  let d := WithZero.log (v (c : K))
  ∀ j : ℤ,
    (MulAut.conj t '' (x '' {z | v z ≤ WithZero.exp (-j)}) =
      x '' {z | v z ≤ WithZero.exp (d - j)}) ∧
    (MulAut.conj t '' (x '' {z | v z < WithZero.exp (-j)}) =
      x '' {z | v z < WithZero.exp (d - j)})

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


end Torus

section Walls
universe u

open Matrix (SpecialLinearGroup)
open scoped Matrix
open IntegralRootRelations (upper lower diagonal)
open IntegralSemisimpleModel Pinning
open scoped CategoryTheory.MonObj

variable {R : Type*} [CommRing R]

/-- The C04 rank-one word, with upper-right entry (a). -/
def rankOneMatrixWord (a : Rˣ) : SpecialLinearGroup (Fin 2) R :=
  upper (a : R) * lower (-(↑a⁻¹ : R)) * upper (a : R)

/-- The wall representative used in F12 has upper-right entry (-a). -/
def wallMatrix (a : Rˣ) : SpecialLinearGroup (Fin 2) R :=
  rankOneMatrixWord (-a)

/-- The identities use units, so they hold on every test algebra. In
particular the wall factorization has no restriction on characteristic. -/
def WallMatrixRelations : Prop :=
  ∀ {R : Type u} [CommRing R] (a t : Rˣ),
    (rankOneMatrixWord a).val = !![0, (a : R); -(↑a⁻¹ : R), 0] ∧
    rankOneMatrixWord a = diagonal a * rankOneMatrixWord 1 ∧
    wallMatrix a ^ 2 = diagonal (-1) ∧
    (∀ z : R,
      wallMatrix a * upper z * (wallMatrix a)⁻¹ =
        lower (-(↑a⁻¹ : R) ^ 2 * z) ∧
      wallMatrix a * lower z * (wallMatrix a)⁻¹ =
        upper (-(a : R) ^ 2 * z)) ∧
    upper (t : R) * wallMatrix a =
      lower (↑t⁻¹ : R) * diagonal (t * a⁻¹) * upper (-(a : R) ^ 2 * (↑t⁻¹ : R))

/-- The wall word evaluated in a marked integral group via the marked rank-one map. -/
def markedWall {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (i : D.I) (a : Sˣ) : IntegralPoints M.group S :=
  (M.rankOne i).app S (wallMatrix a)

/-- The normalizer word, its conjugation on both marked lines and the signed
factorization of (x_i(t)n) in the actual marked group. -/
def MarkedWallRelations : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (i : D.I) (a t : Sˣ),
    let j := D.datum.reflectionPerm i i
    let x := markedRootPoint M S
    let h := fun b : Sˣ =>
      torusPoint D S (cocharacter D (D.datum.coroot i) S b) ≫ M.torus.hom.hom
    let n := markedWall M S i a
    n = x i (-(a : S)) * x j (↑a⁻¹ : S) * x i (-(a : S)) ∧
    n ^ 2 = h (-1) ∧
    (∀ z : S, n * x i z * n⁻¹ = x j (-(↑a⁻¹ : S) ^ 2 * z) ∧
      n * x j z * n⁻¹ = x i (-(a : S) ^ 2 * z)) ∧
    x i (t : S) * n =
      x j (↑t⁻¹ : S) * h (t * a⁻¹) * x i (-(a : S) ^ 2 * (↑t⁻¹ : S))

end Walls

section OrderedCoordinates

open AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open IntegralSemisimpleModel Pinning
open OrderedRootProducts (Enumerates)
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
universe u

/-- The ordered marked absolute root factors, with one coordinate per label. -/
def orderedRootPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (v : D.I → R) :
    IntegralPoints M.group R :=
  (l.map fun a => markedRootPoint M R a (v a)).prod

/-- The point form of the marked triangular cell. -/
def markedCellPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (v : D.I → R) (t : IntegralPoints (splitTorus D) R) : IntegralPoints M.group R :=
  orderedRootPoint M R negative v *
    ((t ≫ M.torus.hom.hom) * orderedRootPoint M R positive v)

/-- In both orders the marked triangular chart is injective on every test
algebra. The reverse chart uses the reversed negative and positive lists. -/
def MarkedCellCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : IntegralMarking D) (R : IntegralAlgebra.{u})
      (negative positive : List D.I),
    Enumerates negative {i | ¬ D.base.IsPos i} →
    Enumerates positive {i | D.base.IsPos i} →
      Function.Injective (fun q : (D.I → R) × IntegralPoints (splitTorus D) R =>
        markedCellPoint M R negative positive q.1 q.2) ∧
      Function.Injective (fun q : (D.I → R) × IntegralPoints (splitTorus D) R =>
        orderedRootPoint M R positive.reverse q.1 *
          ((q.2 ≫ M.torus.hom.hom) * orderedRootPoint M R negative.reverse q.1))

end OrderedCoordinates

section MarkedFibre

open IntegralSemisimpleModel Pinning RootGroups
open AdjointRepresentation (GroupPoints)
open RationalRealization (Realization)
open CharacterPairing (characterValue)
open scoped CategoryTheory.MonObj
universe u

attribute [local instance] integerAlgebra

/-- Coordinates on the actual pinned field fibre of the specified integral
model. The field parameters compare with the integral maps on all test algebras. -/
structure MarkedFibre {D : BasedRootDatum.{u}} (M : Model D)
    (k : Type u) [Field k] where
  line : RootGroups.AdditiveLine k
  realization : Realization D line
  groupIso : (fibre k).obj M.group ≅ realization.pinned.pair.G.val
  torusIso : (fibre k).obj (splitTorus D) ≅ realization.pinned.pair.T.group
  coordinate : ∀ a : D.I, RootCoordinate line realization.pinned.pair.T
    (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val
    (realization.datumIso.val.indexEquiv a).val
  torus_comm : (fibre k).map M.torus ≫ groupIso.hom =
    torusIso.hom ≫ realization.pinned.pair.T.inclusion
  simple_eq : ∀ a : D.base.support, (coordinate a).val =
    (realization.pinned.pin (realization.simpleRoot a)).val
  torus_eval : ∀ (R : TestAlgebra k)
    (s : GroupPoints ((fibre k).obj (splitTorus D)) R)
    (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
    forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
      ∀ x : D.X, characterValue (Additive.toMul (realization.datumIso.val.weightEquiv x)) R
        (s ≫ torusIso.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)
  root_eval : ∀ (a : D.I) (R : TestAlgebra k) (r : R),
    forgetFibrePoint M.group R
      (rootPoint ((coordinate a).val.hom ≫
        (realization.pinned.roots (realization.datumIso.val.indexEquiv a)).val.inclusion ≫
          groupIso.inv) R r) = markedRootPoint M.toIntegralMarking
            (CommAlgCat.of Integers.{u} R) a r

/-- The chosen model has compatible coordinates over each field. -/
def MarkedFibreExists : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D) (k : Type u) [Field k],
    Nonempty (MarkedFibre M k)

open IntegralRootRelations (upper lower)
open Matrix (SpecialLinearGroup)

/-- The four signed absolute root maps of an orthogonal pair commute in
the marked model on every test algebra over a field. -/
def MarkedOrthogonalRootCommutation : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D)
    (_hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (a b : D.I), D.datum.pairing a b = 0 →
    ∀ (k : Type u) [Field k] (R : TestAlgebra k),
      let S := CommAlgCat.of Integers.{u} R
      let U := Set.range (upper (R := S)) ∪ Set.range (lower (R := S))
      ∀ A ∈ U, ∀ B ∈ U,
        Commute ((M.rankOne a).app S A : IntegralPoints M.group S)
          ((M.rankOne b).app S B : IntegralPoints M.group S)

end MarkedFibre

section RootTransport

open Pinning RootGroups
open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open scoped CategoryTheory.MonObj
universe u

/-- An automorphism preserving the torus transports actual root coordinates
by a unique field unit on each marked line. The action is tested on every
test algebra. -/
def RootCoordinateTransport : Prop :=
  ∀ {k : Type u} [Field k] {A : RootGroups.AdditiveLine k} (P : PinnedGroup A)
    (f : P.pair.G.val ≅ P.pair.G.val) (w : P.pair.T.group ≅ P.pair.T.group),
    P.pair.T.inclusion ≫ f.hom = w.hom ≫ P.pair.T.inclusion →
    ∀ (a b : Root P.pair.T), transportCharacter w a.val = b.val →
    ∀ (x : RootCoordinate A P.pair.T (P.roots a).val a.val)
      (y : RootCoordinate A P.pair.T (P.roots b).val b.val),
      ∃! c : kˣ, ∀ (R : TestAlgebra k) (z : R),
        rootPoint ((x.val.hom ≫ (P.roots a).val.inclusion) ≫ f.hom) R z =
          rootPoint (y.val.hom ≫ (P.roots b).val.inclusion) R (algebraMap k R (c : k) * z)

end RootTransport

section WallDepth

open scoped WithZero
universe u

/-- Every integer layer in the root parameter field has a wall parameter.
Conjugation under its signed wall word shifts the two valuations by twice
the depth with opposite signs. At exact depth the middle factor is a unit
of the valuation ring, and the two unipotent factors have depths (-j,j). -/
def WallDepths : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (j : ℤ),
    let v := normalizedValuation K
    (∃ a : Kˣ, v (a : K) = WithZero.exp (-j)) ∧
    ∀ a : Kˣ, v (a : K) = WithZero.exp (-j) →
      (∀ z : K, v (-(↑a⁻¹ : K) ^ 2 * z) = WithZero.exp (j + j) * v z ∧
        v (-(a : K) ^ 2 * z) = WithZero.exp ((-j) + (-j)) * v z) ∧
      ∀ t : Kˣ, v (t : K) = WithZero.exp (-j) →
        v (↑t⁻¹ : K) = WithZero.exp j ∧
        v (↑(t * a⁻¹) : K) = 1 ∧
        v (-(a : K) ^ 2 * (↑t⁻¹ : K)) = WithZero.exp (-j)

end WallDepth

section LinkedCoordinates

open IntegralSemisimpleModel Pinning
open OrderedRootProducts (Enumerates)
open scoped CategoryTheory.MonObj
universe u

attribute [local instance] integerAlgebra

/-- A torus-preserving identification intertwining the upper coordinates
must intertwine the linked lower coordinates with the same parameter.
The dual-number test already determines the scalar in every characteristic. -/
def LinkedLowerCoordinateUniqueness : Prop :=
  ∀ (k : Type u) [Field k] {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (negative positive : List D.I),
    Enumerates negative {i | ¬ D.base.IsPos i} →
    Enumerates positive {i | D.base.IsPos i} →
    ∀ (a b : D.I), D.base.IsPos b →
    let R := CommAlgCat.of Integers.{u} (DualNumber k)
    let x := markedRootPoint M R
    let j := D.datum.reflectionPerm a a
    let l := D.datum.reflectionPerm b b
    ∀ (f : MulAut (IntegralPoints M.group R)) (c : kˣ),
      (∀ t : IntegralPoints (splitTorus D) R, ∃ s : IntegralPoints (splitTorus D) R,
        f (t ≫ M.torus.hom.hom) = s ≫ M.torus.hom.hom) →
      (∀ z : R, f (x a z) = x b z) →
      (∀ z : R, f (x j z) = x l (algebraMap k (DualNumber k) (c : k) * z)) →
      c = 1

end LinkedCoordinates

section PinnedLinkedCoordinates

open IntegralSemisimpleModel Pinning
open RootGroups (rootPoint)
universe u

/-- The labelled absolute root map of the chosen field fibre. -/
def MarkedFibre.rootMap {D : BasedRootDatum.{u}} {M : Model D}
    {k : Type u} [Field k] (C : MarkedFibre M k) (a : D.I) :
    C.line.group ⟶ C.realization.pinned.pair.G.val :=
  (C.coordinate a).val.hom ≫
    (C.realization.pinned.roots (C.realization.datumIso.val.indexEquiv a)).val.inclusion

/-- The pinned automorphism exchanges both linked maps of a simple root,
with the parameter unchanged, on every test algebra of the ground field. -/
def PinnedLinkedSimpleCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (f : Aut C.realization.pinned) (a b : D.base.support),
      let e := C.realization.datumIso.val.indexEquiv
      transportCharacter f.asIso.hom.torus (e a).val = (e b).val →
      ∀ (R : TestAlgebra k) (r : R),
        rootPoint (C.rootMap a ≫ f.asIso.hom.group.hom) R r =
          rootPoint (C.rootMap b) R r ∧
        rootPoint (C.rootMap (D.datum.reflectionPerm a a) ≫ f.asIso.hom.group.hom) R r =
          rootPoint (C.rootMap (D.datum.reflectionPerm b b)) R r

end PinnedLinkedCoordinates

section Reflection

open IntegralSemisimpleModel Pinning
open scoped CategoryTheory.MonObj
universe u

/-- The action of the actual marked wall word on the torus, tested on its
full character lattice. In particular its torus action is the reflection
with the specified root label, over every test algebra. -/
def MarkedWallTorusReflection : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (i : D.I) (a : Rˣ) (t : TorusValues D R),
    let g : IntegralPoints M.group R := torusPoint D R t ≫ M.torus.hom.hom
    let n := markedWall M R i a
    let t' := cocharacter D (D.datum.coroot i) R
      ((t (Multiplicative.ofAdd (D.datum.root i)))⁻¹) * t
    n * g * n⁻¹ = torusPoint D R t' ≫ M.torus.hom.hom ∧
    ∀ x : D.X, t' (Multiplicative.ofAdd x) =
      t (Multiplicative.ofAdd (D.datum.reflection i x))

end Reflection

section PinnedPointCriterion

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open AdjointCocharacters (coordinateHopf coordinateHopfMap)
open AdjointBorelCohomology (PinnedTwist)
open AutomorphismSequence (forgetPinning)
universe u

/-- The actual F06 fixed-point equations can be tested on the unextended
coordinate ring. The pinned lift acts by inverse pullback, paired with
the coefficient action on the test algebra. -/
def PinnedPointCriterion : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := P) K D l B T)
    (R : Type u) [CommRing R] [Algebra k R]
    (q : coordinateHopf P.pair.G →ₐ[k] K ⊗[k] R),
      let p := AlgHom.liftEquiv k K (coordinateHopf P.pair.G) (K ⊗[k] R) q
      p ∈ Set.range (pinnedAlgebraPointMap d (R := R)) ↔
        ∀ (σ : Gal(K/k)) (x : coordinateHopf P.pair.G),
          let f := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv
          q ((coordinateHopfMap (G := P.pair.G) (H := P.pair.G) f).hom x) =
            (SemilinearAction.scalarExtension (K := K) R).act σ (q x)

end PinnedPointCriterion

section LocalSL

open Matrix (SpecialLinearGroup)
open IntegralRootRelations (upper lower)
universe u

/-- Over a commutative local ring, the determinant-one rank-one functor
is generated by its two elementary one-parameter subgroups. -/
def LocalSL2Generation : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (P : SpecialLinearGroup (Fin 2) R → Prop),
    (∀ t, P (upper t)) → (∀ t, P (lower t)) →
    (∀ A B, P A → P B → P (A * B)) → ∀ A, P A

end LocalSL

section CommutingRankOne

open IntegralSemisimpleModel Pinning
open Matrix (SpecialLinearGroup)
universe u

attribute [local instance] integerAlgebra

/-- The two actual rank-one group maps at an orthogonal pair commute on
all test algebras, including algebras whose points are not generated by
elementary matrices globally. -/
def MarkedOrthogonalRankOneCommutation : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D)
    (_hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (a b : D.I), D.datum.pairing a b = 0 →
    ∀ (k : Type u) [Field k] (R : TestAlgebra k),
      let S := CommAlgCat.of Integers.{u} R
      ∀ A B : SpecialLinearGroup (Fin 2) S,
        Commute ((M.rankOne a).app S A : IntegralPoints M.group S)
          ((M.rankOne b).app S B : IntegralPoints M.group S)

end CommutingRankOne

section PairedRankOneProduct

open IntegralSemisimpleModel Pinning
open Matrix (SpecialLinearGroup)
universe u

attribute [local instance] integerAlgebra

/-- The scalar-extended test algebras, with their canonical integral
algebra structures. The splitting field is the first tensor factor. -/
def quadraticIntegralAlgebra (k K : Type u) [Field k] [Field K] [Algebra k K] :
    TestAlgebra k ⥤ IntegralAlgebra.{u} where
  obj R := @CommAlgCat.of Integers.{u} _ (K ⊗[k] R) _ (integerAlgebra _)
  map f := CommAlgCat.ofHom
    { toRingHom := (Algebra.TensorProduct.map (AlgHom.id k K) f.hom).toRingHom
      commutes' n := map_intCast (Algebra.TensorProduct.map (AlgHom.id k K) f.hom) n.down }
  map_id R := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id k K) (AlgHom.id k R) z = z
    rw [Algebra.TensorProduct.map_id]
    rfl
  map_comp {R S T} f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id k K) (g.hom.comp f.hom) z =
      Algebra.TensorProduct.map (AlgHom.id k K) g.hom
        (Algebra.TensorProduct.map (AlgHom.id k K) f.hom z)
    rw [Algebra.TensorProduct.map_id_comp]
    rfl

/-- Coefficient conjugation on the extension of a test algebra. -/
def quadraticCoefficientEquiv {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) (R : TestAlgebra k) : (K ⊗[k] R) ≃ₐ[k] (K ⊗[k] R) :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : R ≃ₐ[k] R)

/-- In the split fibre the paired rank-one word is the product of the
two marked rank-one maps with conjugate parameters. Its homomorphisms
commute with every base test-algebra map. -/
def MarkedPairedRankOneProduct : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D)
    (_hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (a b : D.I), D.datum.pairing a b = 0 →
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)),
      let E := quadraticIntegralAlgebra k K
      ∃ ρ : E ⋙ rankOnePoints.{u} ⟶ E ⋙ integralPointFunctor M.group,
        ∀ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) (K ⊗[k] R)),
          (ρ.app R A : IntegralPoints M.group (E.obj R)) =
            (M.rankOne a).app (E.obj R) A *
            (M.rankOne b).app (E.obj R) (SpecialLinearGroup.map
              (quadraticCoefficientEquiv σ R).toRingHom A)

end PairedRankOneProduct

section PinnedSchemePoints

open AlgebraicGeometry
open AdjointCocharacters (coordinateHopf coordinateHopfIso)
open AdjointBorelCohomology (PinnedTwist)
open AdjointRepresentation (GroupPoints)
open Pinning (AttachedDatum PinnedGroup)
open scoped CategoryTheory.MonObj

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Extension of a test algebra by the splitting field, viewed over the ground field. -/
abbrev extendedTestAlgebra (k K : Type u) [Field k] [Field K] [Algebra k K] :
    TestAlgebra k ⥤ TestAlgebra k where
  obj R := CommAlgCat.of k (K ⊗[k] R)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k K) f.hom)
  map_id R := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id (R := k) (A := K) (B := R)
  map_comp {R S U} f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id k K) (g.hom.comp f.hom) z =
      Algebra.TensorProduct.map (AlgHom.id k K) g.hom
        (Algebra.TensorProduct.map (AlgHom.id k K) f.hom z)
    rw [Algebra.TensorProduct.map_id_comp]
    rfl

/-- Coefficient conjugation on the scalar-extended test algebra. -/
def conjugateTestAlgebra (σ : Gal(K/k)) (R : TestAlgebra k) :
    (extendedTestAlgebra k K).obj R ⟶ (extendedTestAlgebra k K).obj R :=
  CommAlgCat.ofHom (quadraticCoefficientEquiv σ R).toAlgHom

/-- The scheme point attached to a map out of the chosen coordinate Hopf algebra. -/
def coordinatePointEquiv (G : AffineAlgebraicGroup k) (R : TestAlgebra k) :
    HopfPoints (coordinateHopf G) R ≃* GroupPoints G.val R :=
  (Spec.mapMulEquiv (R := k) (S := coordinateHopf G) (T := R)).trans
    (((groupPointsFunctor k).mapIso (coordinateHopfIso G)).app R).groupIsoToMulEquiv

variable {A : RootGroups.AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
  {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}

/-- The automorphism of the pinned model appearing in the actual twist. -/
def pinnedDiagram (d : PinnedTwist (P := P) K D l B T) (σ : Gal(K/k)) : Aut P :=
  l (d.outer σ)

/-- The descended point after extension and the specified F06 comparison. -/
def pinnedSchemePoint (d : PinnedTwist (P := P) K D l B T) (R : TestAlgebra k)
    (p : HopfPoints (coordinateHopf G) R) :
    GroupPoints P.pair.G.val ((extendedTestAlgebra k K).obj R) :=
  coordinatePointEquiv P.pair.G ((extendedTestAlgebra k K).obj R) (WithConv.toConv
    ((AlgHom.liftEquiv k K (coordinateHopf P.pair.G) (K ⊗[k] R)).symm
      (pinnedAlgebraPointMap d p.ofConv)))

/-- The coefficient and diagram action on points in the split model. -/
def pinnedSchemeAction (d : PinnedTwist (P := P) K D l B T) (σ : Gal(K/k))
    (R : TestAlgebra k) (p : GroupPoints P.pair.G.val ((extendedTestAlgebra k K).obj R)) :
    GroupPoints P.pair.G.val ((extendedTestAlgebra k K).obj R) :=
  mapPoints (conjugateTestAlgebra σ R) p ≫ (pinnedDiagram d σ).asIso.hom.group.hom.hom.hom

/-- The actual pinned comparison embeds the rational point functor into the
split point functor, with image the fixed points on every test algebra. -/
def PinnedSchemePointEmbedding : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {A : RootGroups.AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k}
    {B T : ClosedSubgroup G.val} (d : PinnedTwist (P := P) K D l B T),
    ∃ emb : convolutionPoints (coordinateHopf G) ⟶
        extendedTestAlgebra k K ⋙ (groupPointsFunctor k).obj P.pair.G.val,
      (∀ R p, emb.app R p = pinnedSchemePoint d R p) ∧
      ∀ R, Function.Injective (emb.app R) ∧
        ∀ p, p ∈ Set.range (emb.app R) ↔ ∀ σ, pinnedSchemeAction d σ R p = p

end PinnedSchemePoints

section MarkedFibrePoints

open IntegralSemisimpleModel Pinning
open AdjointRepresentation (GroupPoints)
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] integerAlgebra

/-- The integral test algebra underlying a test algebra over the ground field. -/
abbrev integralTestAlgebra (k : Type u) [Field k] : TestAlgebra k ⥤ IntegralAlgebra.{u} where
  obj R := CommAlgCat.of Integers.{u} R
  map f := CommAlgCat.ofHom
    { toRingHom := f.hom.toRingHom
      commutes' n := map_intCast f.hom n.down }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The specified fibre comparison on points, projected to the integral model. -/
def markedFibrePoint {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (R : TestAlgebra k) (p : GroupPoints C.realization.pinned.pair.G.val R) :
    IntegralPoints M.group ((integralTestAlgebra k).obj R) :=
  forgetFibrePoint M.group R (p ≫ C.groupIso.inv.hom.hom)

/-- The fibre comparison is a natural equivalence of group-valued functors. -/
def MarkedFibrePointComparison : Prop :=
  ∀ {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k] (C : MarkedFibre M k),
    ∃ e : (groupPointsFunctor k).obj C.realization.pinned.pair.G.val ≅
        integralTestAlgebra k ⋙ integralPointFunctor M.group,
      ∀ R p, e.hom.app R p = markedFibrePoint C R p

/-- A pinned diagram map matching two simple labels intertwines their full
marked rank-one maps on every test algebra. -/
def PinnedSimpleRankOneEquivariance : Prop :=
  ∀ {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (f : Aut C.realization.pinned) (a b : D.base.support),
      let e := C.realization.datumIso.val.indexEquiv
      transportCharacter f.asIso.hom.torus (e a).val = (e b).val →
      ∀ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) R)
        (p : GroupPoints C.realization.pinned.pair.G.val R),
        markedFibrePoint C R p = (M.rankOne a).app ((integralTestAlgebra k).obj R) A →
        markedFibrePoint C R (p ≫ f.asIso.hom.group.hom.hom.hom) =
          (M.rankOne b).app ((integralTestAlgebra k).obj R) A

end MarkedFibrePoints

section RelativeRankOne

open AdjointCocharacters (coordinateHopf)
open AdjointBorelCohomology (PinnedTwist)
open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel Pinning
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)

/-- The F06 comparison, expressed in the marked integral group on the
scalar-extended test algebra. -/
def pinnedMarkedPoint (R : TestAlgebra k) (p : HopfPoints (coordinateHopf G) R) :
    IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R) :=
  markedFibrePoint C ((extendedTestAlgebra k K).obj R) (pinnedSchemePoint d R p)

/-- The natural embedding has image given by the actual pinned action. -/
def PinnedMarkedPointEmbedding : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    ∃ emb : convolutionPoints (coordinateHopf G) ⟶
        quadraticIntegralAlgebra k K ⋙ integralPointFunctor M.group,
      (∀ R p, emb.app R p = pinnedMarkedPoint C d R p) ∧
      ∀ R, Function.Injective (emb.app R) ∧
        ∀ p : GroupPoints C.realization.pinned.pair.G.val ((extendedTestAlgebra k K).obj R),
          markedFibrePoint C ((extendedTestAlgebra k K).obj R) p ∈ Set.range (emb.app R) ↔
            ∀ σ, pinnedSchemeAction d σ R p = p

/-- For a singleton simple orbit the given rank-one map descends with
parameter algebra R, embedded by the standard inclusion R → L ⊗ R. -/
def PinnedSingletonRankOne : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    ∀ (a : D.base.support),
      let e := C.realization.datumIso.val.indexEquiv
      transportCharacter (pinnedDiagram d σ).asIso.hom.torus (e a).val = (e a).val →
      ∃ ρ : integralTestAlgebra k ⋙ rankOnePoints.{u} ⟶ convolutionPoints (coordinateHopf G),
        ∀ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) R),
          pinnedMarkedPoint C d R (ρ.app R A) =
            (M.rankOne a).app ((quadraticIntegralAlgebra k K).obj R)
              (SpecialLinearGroup.map
                (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom A)

/-- For a paired simple orbit the entire rank-one map descends to the
actual twist with scalar-extended parameters on every test algebra. -/
def PinnedPairRankOne : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (a b : D.base.support), D.datum.pairing a b = 0 →
      let e := C.realization.datumIso.val.indexEquiv
      let f := (pinnedDiagram d σ).asIso.hom.torus
      transportCharacter f (e a).val = (e b).val →
      transportCharacter f (e b).val = (e a).val →
      let E := quadraticIntegralAlgebra k K
      ∃ ρ : E ⋙ rankOnePoints.{u} ⟶ convolutionPoints (coordinateHopf G),
        ∀ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) (K ⊗[k] R)),
          pinnedMarkedPoint C d R (ρ.app R A) =
            (M.rankOne a).app (E.obj R) A *
              (M.rankOne b).app (E.obj R)
                (SpecialLinearGroup.map (quadraticCoefficientEquiv σ R).toRingHom A)

end RelativeRankOne

section MarkedReflection

open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel Pinning
open scoped CategoryTheory.MonObj

universe u

/-- Conjugation by the integral unit wall representative on the actual
field fibre induces the indicated reflection of the entire character lattice. -/
def MarkedFieldReflection : Prop :=
  ∀ {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (i : D.I),
    let P := C.realization.pinned.pair
    ∃ (g : P.G.val ≅ P.G.val) (w : P.T.group ≅ P.T.group),
      P.T.inclusion ≫ g.hom = w.hom ≫ P.T.inclusion ∧
      (∀ x : D.X, transportCharacter w
        (Additive.toMul (C.realization.datumIso.val.weightEquiv x)) =
          Additive.toMul (C.realization.datumIso.val.weightEquiv (D.datum.reflection i x))) ∧
      ∀ (R : TestAlgebra k) (p : GroupPoints P.G.val R),
        let n := markedWall M.toIntegralMarking ((integralTestAlgebra k).obj R) i 1
        markedFibrePoint C R (p ≫ g.hom.hom.hom) =
          n * markedFibrePoint C R p * n⁻¹

/-- A marked wall representative transports each marked root line by an
integral unit. The same unit works after every change of test algebra. -/
def IntegralRootReflectionUnits : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D) (i j : D.I),
    ∃ c : Integers.{u}ˣ, ∀ (R : IntegralAlgebra.{u}) (z : R),
      let n := markedWall M.toIntegralMarking R i 1
      n * markedRootPoint M.toIntegralMarking R j z * n⁻¹ =
        markedRootPoint M.toIntegralMarking R (D.datum.reflectionPerm i j)
          (algebraMap Integers.{u} R (c : Integers.{u}) * z)

end MarkedReflection

section RootPairCoordinates

open IntegralSemisimpleModel Pinning
open scoped CategoryTheory.MonObj

universe u

/-- Two distinct marked lines of the same sign give unique ordered
coordinates on their product, over arbitrary integral test algebras. -/
def MarkedRootPairInjectivity : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (a b : D.I), a ≠ b → (D.base.IsPos a ↔ D.base.IsPos b) →
      Function.Injective (fun p : R × R =>
        markedRootPoint M R a p.1 * markedRootPoint M R b p.2)

end RootPairCoordinates

section RelativeParameterSchemes

open IntegralSemisimpleModel
open Matrix (SpecialLinearGroup)
open IntegralRootRelations (upper)
open scoped Matrix CategoryTheory.MonObj

universe u

/-- The upper transvections are a natural homomorphism from the additive parameters. -/
def upperParameters (k : Type u) [Field k] :
    StandardGroups.additivePoints k ⟶ integralTestAlgebra k ⋙ rankOnePoints.{u} where
  app R := GrpCat.ofHom (MonoidHom.mk' (fun z : Multiplicative R => upper z.toAdd) (by
    intro x y
    apply Subtype.ext
    change (!![1, x.toAdd + y.toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) R) =
      !![1, x.toAdd; 0, 1] * !![1, y.toAdd; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]))
  naturality {R S} f := by
    apply GrpCat.ext
    intro z
    apply Subtype.ext
    change (!![1, f.hom (Multiplicative.toAdd z); 0, 1] : Matrix (Fin 2) (Fin 2) S) =
      (!![1, Multiplicative.toAdd z; 0, 1] : Matrix (Fin 2) (Fin 2) R).map f.hom
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The additive group and SL₂, and their Weil restrictions, with their
parameter functors specified on all test algebras. -/
structure RelativeParameterSchemes (k K : Type u) [Field k] [Field K] [Algebra k K] where
  additive : AffineAlgebraicGroup k
  additivePoints : (groupPointsFunctor k).obj additive.val ≅ StandardGroups.additivePoints k
  rankOne : AffineAlgebraicGroup k
  rankOnePoints : (groupPointsFunctor k).obj rankOne.val ≅
    integralTestAlgebra k ⋙ IntegralSemisimpleModel.rankOnePoints.{u}
  restrictedAdditive : AffineAlgebraicGroup k
  restrictedAdditivePoints : (groupPointsFunctor k).obj restrictedAdditive.val ≅
    extendedTestAlgebra k K ⋙ StandardGroups.additivePoints k
  restrictedRankOne : AffineAlgebraicGroup k
  restrictedRankOnePoints : (groupPointsFunctor k).obj restrictedRankOne.val ≅
    quadraticIntegralAlgebra k K ⋙ IntegralSemisimpleModel.rankOnePoints.{u}

def RelativeParameterRepresentability : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K],
    Nonempty (RelativeParameterSchemes k K)

open AdjointCocharacters (coordinateHopf)
open AdjointRepresentation (GroupPoints)
open AlgebraicGeometry

/-- A natural rank-one map between these group-valued functors is a group
scheme morphism. An injective upper parameter map gives a closed root subgroup. -/
def RelativeRankOneSchemeRealization : Prop :=
  ∀ {k : Type u} [Field k] (G U H : AffineAlgebraicGroup k)
    {P A : TestAlgebra k ⥤ GrpCat.{u}}
    (eU : (groupPointsFunctor k).obj U.val ≅ A)
    (eH : (groupPointsFunctor k).obj H.val ≅ P)
    (x : A ⟶ P) (ρ : P ⟶ convolutionPoints (coordinateHopf G)),
    (∀ R, Function.Injective (fun z : A.obj R => ρ.app R (x.app R z))) →
    ∃ (upper : U.val ⟶ H.val) (rankOne : H.val ⟶ G.val),
      IsClosedImmersion (upper ≫ rankOne).hom.hom.left ∧
      (∀ (R : TestAlgebra k) (p : GroupPoints U.val R),
        eH.hom.app R (p ≫ upper.hom.hom) = x.app R (eU.hom.app R p)) ∧
      ∀ (R : TestAlgebra k) (p : GroupPoints H.val R),
        (coordinatePointEquiv G R).symm (p ≫ rankOne.hom.hom) = ρ.app R (eH.hom.app R p)

end RelativeParameterSchemes

section IntegralWeylWords

open IntegralSemisimpleModel Pinning
open AdjointCocharacters (coordinateHopf)
open AdjointBorelCohomology (PinnedTwist)
open scoped CategoryTheory.MonObj

universe u

/-- A simple singleton or an ordered simple pair. -/
abbrev SimpleRootOrbit (D : BasedRootDatum.{u}) :=
  D.base.support × Option D.base.support

def SimpleRootOrbit.roots {D : BasedRootDatum.{u}} (o : SimpleRootOrbit D) : List D.I :=
  o.1.val :: o.2.toList.map Subtype.val

/-- Compatibility with the actual pinned involution on the selected simple orbit. -/
def SimpleRootOrbit.Matches {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k]
    (C : MarkedFibre M k) (f : Aut C.realization.pinned) (o : SimpleRootOrbit D) : Prop :=
  let e := C.realization.datumIso.val.indexEquiv
  let adj := transportCharacter f.asIso.hom.torus
  match o.2 with
  | none => adj (e o.1).val = (e o.1).val
  | some b =>
    D.datum.pairing o.1 b = 0 ∧ adj (e o.1).val = (e b).val ∧ adj (e b).val = (e o.1).val

/-- The ordered word in the integral unit wall representatives. -/
def markedWeylWord {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) : IntegralPoints M.group R :=
  (l.map fun i => markedWall M R i 1).prod

/-- The order here agrees with conjugation by the ordered word. -/
def weylWordPerm {D : BasedRootDatum.{u}} (l : List D.I) : Equiv.Perm D.I :=
  l.foldr (fun i w => D.datum.reflectionPerm i * w) 1

def IntegralWeylWordTransport : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D) (l : List D.I) (j : D.I),
    ∃ c : Integers.{u}ˣ, ∀ (R : IntegralAlgebra.{u}) (z : R),
      let n := markedWeylWord M.toIntegralMarking R l
      n * markedRootPoint M.toIntegralMarking R j z * n⁻¹ =
        markedRootPoint M.toIntegralMarking R (weylWordPerm l j)
          (algebraMap Integers.{u} R (c : Integers.{u}) * z)

/-- Words in unit representatives of simple orbits lie in the actual
descended group, also as constant points on every test algebra. -/
def PinnedWeylWordFixed : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
      ∀ (R : TestAlgebra k), ∃ p : HopfPoints (coordinateHopf G) R,
        pinnedMarkedPoint C d R p = markedWeylWord M.toIntegralMarking
          ((quadraticIntegralAlgebra k K).obj R) (w.flatMap SimpleRootOrbit.roots)

/-- Conjugating a simple relative rank-one map by the fixed word descends
with the same parameter algebra and gives the indicated conjugate in the split model. -/
def PinnedWeylRankOneTransport : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
      ∀ {P : TestAlgebra k ⥤ GrpCat.{u}} (ρ : P ⟶ convolutionPoints (coordinateHopf G)),
        ∃ ρ' : P ⟶ convolutionPoints (coordinateHopf G),
          ∀ (R : TestAlgebra k) (A : P.obj R),
            let n := markedWeylWord M.toIntegralMarking ((quadraticIntegralAlgebra k K).obj R)
              (w.flatMap SimpleRootOrbit.roots)
            pinnedMarkedPoint C d R (ρ'.app R A) = n * pinnedMarkedPoint C d R (ρ.app R A) * n⁻¹

end IntegralWeylWords

section RelativeRootModels

open AlgebraicGeometry
open AdjointCocharacters (coordinateHopf)
open AdjointRepresentation (GroupPoints)
open AdjointBorelCohomology (PinnedTwist)
open IntegralSemisimpleModel Pinning
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

/-- The embedded root and rank-one scheme morphisms, with the prescribed
upper homomorphism and the parameter functor comparisons. -/
structure RelativeRootModel {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    {A P : TestAlgebra k ⥤ GrpCat.{u}} (upper : A ⟶ P) where
  line : AffineAlgebraicGroup k
  rank : AffineAlgebraicGroup k
  linePoints : (groupPointsFunctor k).obj line.val ≅ A
  rankPoints : (groupPointsFunctor k).obj rank.val ≅ P
  upperMap : line.val ⟶ rank.val
  rankMap : rank.val ⟶ G.val
  closed : IsClosedImmersion (upperMap ≫ rankMap).hom.hom.left
  upper_eq : ∀ (R : TestAlgebra k) (p : GroupPoints line.val R),
    rankPoints.hom.app R (p ≫ upperMap.hom.hom) = upper.app R (linePoints.hom.app R p)
  pointMap : P ⟶ convolutionPoints (coordinateHopf G)
  rank_eq : ∀ (R : TestAlgebra k) (p : GroupPoints rank.val R),
    (coordinatePointEquiv G R).symm (p ≫ rankMap.hom.hom) = pointMap.app R (rankPoints.hom.app R p)

def RelativeRootModel.subgroup {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {A P : TestAlgebra k ⥤ GrpCat.{u}} {upper : A ⟶ P} (H : RelativeRootModel G upper) :
    ClosedSubgroup G.val :=
  ⟨H.line.val, H.upperMap ≫ H.rankMap, H.closed⟩

/-- The singleton relative root subgroup is an embedded additive group.
The attached rank-one map is the specified absolute map transported by
the given fixed integral Weyl word. -/
def PinnedSingletonRootModel : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
    ∀ (a : D.base.support),
      SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, none) →
      ∃ H : RelativeRootModel G (upperParameters k),
        ∀ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) R),
          let S := (quadraticIntegralAlgebra k K).obj R
          let n := markedWeylWord M.toIntegralMarking S (w.flatMap SimpleRootOrbit.roots)
          let r : IntegralPoints M.group S := (M.rankOne a).app S (SpecialLinearGroup.map
            (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom A)
          pinnedMarkedPoint C d R (H.pointMap.app R A) = n * r * n⁻¹

/-- A paired relative root is an embedded restriction of scalars of the
additive group, with the compatible restriction-of-scalars rank-one map. -/
def PinnedPairRootModel : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
    ∀ (a b : D.base.support),
      SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, some b) →
      ∃ H : RelativeRootModel G (Functor.whiskerLeft (extendedTestAlgebra k K) (upperParameters k)),
        ∀ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) (K ⊗[k] R)),
          let S := (quadraticIntegralAlgebra k K).obj R
          let n := markedWeylWord M.toIntegralMarking S (w.flatMap SimpleRootOrbit.roots)
          let r : IntegralPoints M.group S := (M.rankOne a).app S A
          let s : IntegralPoints M.group S := (M.rankOne b).app S (SpecialLinearGroup.map
            (quadraticCoefficientEquiv σ R).toRingHom A)
          pinnedMarkedPoint C d R (H.pointMap.app R A) = n * (r * s) * n⁻¹

/-- The split case uses the ordinary additive and SL₂ parameters for each
absolute root, with the original integral rank-one map on the fibre. -/
def SplitMarkedRootModel : Prop :=
  ∀ {D : BasedRootDatum.{u}} {M : Model D} {k : Type u} [Field k] (C : MarkedFibre M k)
    (a : D.I),
    ∃ H : RelativeRootModel C.realization.pinned.pair.G (upperParameters k),
      ∀ (R : TestAlgebra k) (A : SpecialLinearGroup (Fin 2) R),
        markedFibrePoint C R
          (coordinatePointEquiv C.realization.pinned.pair.G R (H.pointMap.app R A)) =
        (M.rankOne a).app ((integralTestAlgebra k).obj R) A

end RelativeRootModels

section OrderedRelativeRoots

open AdjointCocharacters (coordinateHopf)
open AdjointBorelCohomology (PinnedTwist)
open IntegralSemisimpleModel Pinning
open scoped CategoryTheory.MonObj

universe u

/-- One relative root specified by its simple orbit and the fixed word
transporting that orbit to the desired absolute root labels. -/
abbrev TransportedOrbit (D : BasedRootDatum.{u}) :=
  SimpleRootOrbit D × List (SimpleRootOrbit D)

def orbitParameter {D : BasedRootDatum.{u}} {k : Type u} [Field k] (K : Type u)
    [Field K] [Algebra k K] (R : TestAlgebra k) (b : TransportedOrbit D) : Type u :=
  match b.1.2 with
  | none => R
  | some _ => K ⊗[k] R

def orbitParameterMap {D : BasedRootDatum.{u}} {k : Type u} [Field k] (K : Type u)
    [Field K] [Algebra k K] {R S : TestAlgebra k} (f : R ⟶ S) :
    (b : TransportedOrbit D) → orbitParameter K R b → orbitParameter K S b
  | (⟨_, none⟩, _) => fun z => f.hom z
  | (⟨_, some _⟩, _) => fun z => ((quadraticIntegralAlgebra k K).map f).hom z

/-- The scalar extension of the relative root coordinate, conjugated by
its integral word. In the paired case both commuting factors appear. -/
def orbitPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k) :
    (b : TransportedOrbit D) →
      orbitParameter K R b → IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R)
  | (⟨a, none⟩, w) => fun z =>
      let S := (quadraticIntegralAlgebra k K).obj R
      let n := markedWeylWord M S (w.flatMap SimpleRootOrbit.roots)
      let j : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
      n * markedRootPoint M S a (j z) * n⁻¹
  | (⟨a, some b⟩, w) => fun z =>
      let S := (quadraticIntegralAlgebra k K).obj R
      let n := markedWeylWord M S (w.flatMap SimpleRootOrbit.roots)
      n * (markedRootPoint M S a z * markedRootPoint M S b
        (quadraticCoefficientEquiv σ R z)) * n⁻¹

def orderedParameters {D : BasedRootDatum.{u}} {k : Type u} [Field k] (K : Type u)
    [Field K] [Algebra k K] (R : TestAlgebra k) : List (TransportedOrbit D) → Type u
  | [] => PUnit
  | b :: l => orbitParameter K R b × orderedParameters K R l

def orderedParametersMap {D : BasedRootDatum.{u}} {k : Type u} [Field k] (K : Type u)
    [Field K] [Algebra k K] {R S : TestAlgebra k} (f : R ⟶ S) :
    (l : List (TransportedOrbit D)) → orderedParameters K R l → orderedParameters K S l
  | [] => fun _ => PUnit.unit
  | b :: l => fun p => (orbitParameterMap K f b p.1, orderedParametersMap K f l p.2)

def orderedOrbitPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k) :
    (l : List (TransportedOrbit D)) →
      orderedParameters K R l → IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R)
  | [] => fun _ => 1
  | b :: l => fun p => orbitPoint M σ R b p.1 * orderedOrbitPoint M σ R l p.2

/-- Ordered products of the descended root coordinates on all test algebras.
The list may use either root order and any fixed simple-orbit transports. -/
def PinnedOrderedRootProducts : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (bs : List (TransportedOrbit D)),
      (∀ b ∈ bs, b.1.Matches C (pinnedDiagram d σ) ∧
        ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ)) →
      ∃ product : ∀ R : TestAlgebra k, orderedParameters K R bs → HopfPoints (coordinateHopf G) R,
        (∀ R v, pinnedMarkedPoint C d R (product R v) =
          orderedOrbitPoint M.toIntegralMarking σ R bs v) ∧
        ∀ {R S : TestAlgebra k} (f : R ⟶ S) v,
          (convolutionPoints (coordinateHopf G)).map f (product R v) =
            product S (orderedParametersMap K f bs v)

end OrderedRelativeRoots

section RationalParameters

open AdjointCocharacters (coordinateHopf)
open AdjointBorelCohomology (PinnedTwist)
open IntegralSemisimpleModel Pinning
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] integerAlgebra

/-- The canonical identification L ⊗ F with L on rational points. -/
def evaluateGroundTensor (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (quadraticIntegralAlgebra k K).obj (CommAlgCat.of k k) ⟶ CommAlgCat.of Integers.{u} K :=
  CommAlgCat.ofHom
    { toRingHom := (Algebra.TensorProduct.rid k K K).toRingHom
      commutes' n := map_intCast (Algebra.TensorProduct.rid k K K).toRingHom n.down }

/-- The paired rational rank-one map, evaluated in the actual split model
over the splitting field. The same integral Weyl word transports both factors. -/
def PinnedRationalPairedRankOne : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
    ∀ (a b : D.base.support), SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, some b) →
      ∃ ρ : SpecialLinearGroup (Fin 2) K →* HopfPoints (coordinateHopf G) k,
        ∀ A : SpecialLinearGroup (Fin 2) K,
          let S := CommAlgCat.of Integers.{u} K
          let n := markedWeylWord M.toIntegralMarking S (w.flatMap SimpleRootOrbit.roots)
          let r : IntegralPoints M.group S := (M.rankOne a).app S A
          let s : IntegralPoints M.group S := (M.rankOne b).app S (SpecialLinearGroup.map σ.toRingHom A)
          (integralPointFunctor M.group).map (evaluateGroundTensor k K)
            (pinnedMarkedPoint C d (CommAlgCat.of k k) (ρ A)) = n * (r * s) * n⁻¹

end RationalParameters

section GroupedCoordinates

open IntegralSemisimpleModel Pinning
open OrderedRootProducts (Enumerates)
open scoped CategoryTheory.MonObj

universe u

/-- The absolute labels of a transported orbit, in its chosen block order. -/
def transportedLabels {D : BasedRootDatum.{u}} (b : TransportedOrbit D) : List D.I :=
  b.1.roots.map (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots))

/-- The absolute coordinates of the relative parameter, in the original
marked lines and with the integral coordinate changes specified by c. -/
def orbitAbsoluteCoordinates {D : BasedRootDatum.{u}}
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k)
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) :
    (b : TransportedOrbit D) → orbitParameter K R b → List (D.I × (K ⊗[k] R))
  | (⟨a, none⟩, w) => fun z =>
      let S := (quadraticIntegralAlgebra k K).obj R
      let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
      let j : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
      let x : K ⊗[k] R := algebraMap Integers.{u} S (c ((a, none), w) a : Integers.{u})
      [(p a, x * j z)]
  | (⟨a, some b⟩, w) => fun z =>
      let S := (quadraticIntegralAlgebra k K).obj R
      let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
      let x : K ⊗[k] R := algebraMap Integers.{u} S (c ((a, some b), w) a : Integers.{u})
      let y : K ⊗[k] R := algebraMap Integers.{u} S (c ((a, some b), w) b : Integers.{u})
      let v : K ⊗[k] R := z
      [(p a, x * v), (p b, y * quadraticCoefficientEquiv σ R v)]

def orderedAbsoluteCoordinates {D : BasedRootDatum.{u}}
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k)
    (c : TransportedOrbit D → D.I → Integers.{u}ˣ) :
    (bs : List (TransportedOrbit D)) →
      orderedParameters K R bs → List (D.I × (K ⊗[k] R))
  | [] => fun _ => []
  | b :: l => fun v => orbitAbsoluteCoordinates σ R c b v.1 ++ orderedAbsoluteCoordinates σ R c l v.2

def OrderedOrbitAbsoluteComparison : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D),
    ∃ c : TransportedOrbit D → D.I → Integers.{u}ˣ,
      ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k)
        (bs : List (TransportedOrbit D)) (v : orderedParameters K R bs),
        let S := (quadraticIntegralAlgebra k K).obj R
        let p := orderedAbsoluteCoordinates σ R c bs v
        p.map Prod.fst = bs.flatMap transportedLabels ∧
          orderedOrbitPoint M.toIntegralMarking σ R bs v =
            (p.map fun z => markedRootPoint M.toIntegralMarking S z.1 z.2).prod

/-- Both triangular orders have unique relative root and torus coordinates
when the labelled blocks enumerate the two sets of absolute roots. -/
def MarkedRelativeCellCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D)
    {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k)
    (ns ps : List (TransportedOrbit D)),
    Enumerates (ns.flatMap transportedLabels) {a | ¬ D.base.IsPos a} →
    Enumerates (ps.flatMap transportedLabels) {a | D.base.IsPos a} →
    let S := (quadraticIntegralAlgebra k K).obj R
    let N := orderedOrbitPoint M.toIntegralMarking σ R ns
    let P := orderedOrbitPoint M.toIntegralMarking σ R ps
    let T := IntegralPoints (splitTorus D) S
    (Function.Injective fun q : orderedParameters K R ns × T × orderedParameters K R ps =>
      N q.1 * ((q.2.1 ≫ M.torus.hom.hom) * P q.2.2)) ∧
    Function.Injective fun q : orderedParameters K R ns × T × orderedParameters K R ps =>
      P q.2.2 * ((q.2.1 ≫ M.torus.hom.hom) * N q.1)

end GroupedCoordinates

section ValuedRankOne

open IntegralRootRelations (upper lower diagonal)
open Matrix (SpecialLinearGroup)

universe u

/-- The wall computation in any rank-one image, with the parameter and
the factor depths in the field used by that rank-one map. -/
def ValuedRankOneWall : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (G : Type u) [Group G] (ρ : SpecialLinearGroup (Fin 2) K →* G) (j : ℤ),
      let v := normalizedValuation K
      ∃ a : Kˣ, v (a : K) = WithZero.exp (-j) ∧
        let n := ρ (wallMatrix a)
        let x := fun z : K => ρ (upper z)
        let y := fun z : K => ρ (lower z)
        let h := fun u : Kˣ => ρ (diagonal u)
        n = x (-(a : K)) * y (↑a⁻¹ : K) * x (-(a : K)) ∧ n ^ 2 = h (-1) ∧
        (∀ z : K, n * x z * n⁻¹ = y (-(↑a⁻¹ : K) ^ 2 * z) ∧
          n * y z * n⁻¹ = x (-(a : K) ^ 2 * z) ∧
          v (-(↑a⁻¹ : K) ^ 2 * z) = WithZero.exp (j + j) * v z ∧
          v (-(a : K) ^ 2 * z) = WithZero.exp ((-j) + (-j)) * v z) ∧
        ∀ t : Kˣ, v (t : K) = WithZero.exp (-j) →
          x (t : K) * n = y (↑t⁻¹ : K) * h (t * a⁻¹) * x (-(a : K) ^ 2 * (↑t⁻¹ : K)) ∧
          v (↑t⁻¹ : K) = WithZero.exp j ∧ v (↑(t * a⁻¹) : K) = 1 ∧
          v (-(a : K) ^ 2 * (↑t⁻¹ : K)) = WithZero.exp (-j)

end ValuedRankOne

section FixedRelativeRootCoordinates

open AdjointBorelCohomology (PinnedTwist)
open IntegralSemisimpleModel Pinning
open scoped CategoryTheory.MonObj

universe u

/-- The transported single line and paired product have exactly the
ground-field and conjugate-pair fixed parameters, on every test algebra. -/
def PinnedTransportedOrbitFixedParameters : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
    ∀ R : TestAlgebra k,
      let S := (quadraticIntegralAlgebra k K).obj R
      let n := markedWeylWord M.toIntegralMarking S (w.flatMap SimpleRootOrbit.roots)
      let x := markedRootPoint M.toIntegralMarking S
      let fixed := Set.range (pinnedMarkedPoint C d R)
      (∀ a : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, none) →
        ∀ u : K ⊗[k] R, n * x a u * n⁻¹ ∈ fixed ↔
          u ∈ Set.range (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R)) ∧
      ∀ a b : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, some b) →
        ∀ u v : K ⊗[k] R, n * (x a u * x b v) * n⁻¹ ∈ fixed ↔
          v = quadraticCoefficientEquiv σ R u

end FixedRelativeRootCoordinates

section SplitOrbitCoordinates

open IntegralSemisimpleModel Pinning
open OrderedRootProducts (Enumerates)
open scoped CategoryTheory.MonObj

universe u

/-- An absolute coordinate obtained by transporting the indicated simple
coordinate by the integral word for its block. -/
def transportedRootPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (b : TransportedOrbit D) (a : D.I) (z : S) :
    IntegralPoints M.group S :=
  let n := markedWeylWord M S (b.2.flatMap SimpleRootOrbit.roots)
  n * markedRootPoint M S a z * n⁻¹

/-- The coordinate changes are integral units, uniform over the coefficient
algebra, even when the original markings do not respect the diagram action. -/
def TransportedIntegralCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D),
    ∃ c : TransportedOrbit D → D.I → Integers.{u}ˣ,
      ∀ (S : IntegralAlgebra.{u}) (b : TransportedOrbit D) (a : D.I) (z : S),
        transportedRootPoint M.toIntegralMarking S b a z =
          markedRootPoint M.toIntegralMarking S
            (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) a)
            (algebraMap Integers.{u} S (c b a : Integers.{u}) * z)

/-- Before taking fixed points, a block has one independent split coefficient
for each of its absolute root labels. -/
def splitOrbitParameter {D : BasedRootDatum.{u}} (S : Type u)
    (b : TransportedOrbit D) : Type u :=
  match b.1.2 with
  | none => S
  | some _ => S × S

def splitOrderedParameters {D : BasedRootDatum.{u}} (S : Type u) :
    List (TransportedOrbit D) → Type u
  | [] => PUnit
  | b :: bs => splitOrbitParameter S b × splitOrderedParameters S bs

def splitOrbitPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D) (S : IntegralAlgebra.{u}) :
    (b : TransportedOrbit D) → splitOrbitParameter S b → IntegralPoints M.group S
  | (⟨a, none⟩, w) => fun v => transportedRootPoint M S ((a, none), w) a v
  | (⟨a, some b⟩, w) => fun v =>
      transportedRootPoint M S ((a, some b), w) a v.1 *
        transportedRootPoint M S ((a, some b), w) b v.2

def splitOrderedOrbitPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) : (bs : List (TransportedOrbit D)) →
      splitOrderedParameters S bs → IntegralPoints M.group S
  | [] => fun _ => 1
  | b :: bs => fun p => splitOrbitPoint M S b p.1 * splitOrderedOrbitPoint M S bs p.2

/-- Absolute coordinates in a transported marking are given by the usual
scalar inclusion for a singleton and the identity and involution for a pair. -/
def extendOrbitParameter {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k) :
    (b : TransportedOrbit D) → orbitParameter K R b → splitOrbitParameter (K ⊗[k] R) b
  | (⟨_, none⟩, _) => fun z => (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) z
  | (⟨_, some _⟩, _) => fun z => (z, quadraticCoefficientEquiv σ R z)

def extendOrderedParameters {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) (R : TestAlgebra k) :
    (bs : List (TransportedOrbit D)) → orderedParameters K R bs →
      splitOrderedParameters (K ⊗[k] R) bs
  | [] => fun _ => PUnit.unit
  | b :: bs => fun p => (extendOrbitParameter σ R b p.1, extendOrderedParameters σ R bs p.2)

/-- The unital slot maps in the transported coordinates give exactly the
ordered root products previously defined by descent. -/
def TransportedOrbitParameterComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {D : BasedRootDatum.{u}}
    (M : IntegralMarking D) (σ : Gal(K/k)) (R : TestAlgebra k)
    (bs : List (TransportedOrbit D)) (v : orderedParameters K R bs),
    let S := (quadraticIntegralAlgebra k K).obj R
    splitOrderedOrbitPoint M S bs (extendOrderedParameters σ R bs v) =
      orderedOrbitPoint M σ R bs v

/-- The two orders use the prescribed order inside each of the two lists. -/
def triangularProduct {H : Type*} [Mul H] (positiveFirst : Bool) (n t p : H) : H :=
  if positiveFirst then p * (t * n) else n * (t * p)

def markedAbsoluteCell {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (ns ps : List D.I) (positiveFirst : Bool)
    (q : (D.I → S) × IntegralPoints (splitTorus D) S) : IntegralPoints M.group S :=
  triangularProduct positiveFirst (orderedRootPoint M S ns q.1)
    (q.2 ≫ M.torus.hom.hom) (orderedRootPoint M S ps q.1)

def markedSplitCell {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (ns ps : List (TransportedOrbit D)) (positiveFirst : Bool)
    (q : splitOrderedParameters S ns × IntegralPoints (splitTorus D) S ×
      splitOrderedParameters S ps) : IntegralPoints M.group S :=
  triangularProduct positiveFirst (splitOrderedOrbitPoint M S ns q.1)
    (q.2.1 ≫ M.torus.hom.hom) (splitOrderedOrbitPoint M S ps q.2.2)

/-- Regrouping and integral changes of the root coordinates preserve the
actual integral cell, with its unique coordinates in either order. -/
def MarkedSplitCellCoordinates : Prop :=
  ∀ {D : BasedRootDatum.{u}} (M : Model D)
    (S : IntegralAlgebra.{u}) (ns ps : List (TransportedOrbit D)),
    Enumerates (ns.flatMap transportedLabels) {a | ¬ D.base.IsPos a} →
    Enumerates (ps.flatMap transportedLabels) {a | D.base.IsPos a} →
    ∀ positiveFirst : Bool, Function.Injective
      (markedSplitCell M.toIntegralMarking S ns ps positiveFirst) ∧
      Set.range (markedSplitCell M.toIntegralMarking S ns ps positiveFirst) =
        Set.range (markedAbsoluteCell M.toIntegralMarking S
          (ns.flatMap transportedLabels) (ps.flatMap transportedLabels) positiveFirst)

end SplitOrbitCoordinates

section PinnedTorusAndCell

open AdjointCocharacters (coordinateHopf coordinateHopfMap)
open AdjointBorelCohomology (PinnedTwist)
open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel Pinning
open OrderedRootProducts (Enumerates)
open Unipotent (closedSubgroupAlgebraicGroup)
open scoped CategoryTheory.MonObj

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)

/-- The torus comparison uses the torus component of the same F06 twist
that embeds the ambient group. -/
def pinnedTorusSchemePoint (R : TestAlgebra k)
    (t : HopfPoints (coordinateHopf (closedSubgroupAlgebraicGroup T)) R) :
    GroupPoints C.realization.pinned.pair.T.group ((extendedTestAlgebra k K).obj R) :=
  let H := coordinateHopf (closedSubgroupAlgebraicGroup C.realization.pinned.pair.T)
  coordinatePointEquiv (closedSubgroupAlgebraicGroup C.realization.pinned.pair.T)
    ((extendedTestAlgebra k K).obj R) (WithConv.toConv
      ((AlgHom.liftEquiv k K H (K ⊗[k] R)).symm
        ((extendAlgebraPoint (K := K) t.ofConv).comp d.torusIso.hom.hom.toAlgHom)))

/-- Inclusion of the descended torus on the chosen Hopf point groups. -/
def descendedTorusInclusion (R : TestAlgebra k)
    (t : HopfPoints (coordinateHopf (closedSubgroupAlgebraicGroup T)) R) :
    HopfPoints (coordinateHopf G) R :=
  WithConv.toConv (t.ofConv.comp (coordinateHopfMap
    (G := closedSubgroupAlgebraicGroup T) (H := G) T.inclusion).hom.toAlgHom)

def markedSplitTorusPoint (R : TestAlgebra k)
    (s : GroupPoints C.realization.pinned.pair.T.group R) :
    IntegralPoints (splitTorus D) ((integralTestAlgebra k).obj R) :=
  forgetFibrePoint (splitTorus D) R (s ≫ C.torusIso.inv.hom.hom)

def pinnedMarkedTorusPoint (R : TestAlgebra k)
    (t : HopfPoints (coordinateHopf (closedSubgroupAlgebraicGroup T)) R) :
    IntegralPoints (splitTorus D) ((quadraticIntegralAlgebra k K).obj R) :=
  markedSplitTorusPoint C ((extendedTestAlgebra k K).obj R) (pinnedTorusSchemePoint C d R t)

/-- On the marked torus the fixed points for the ambient pinned comparison
are exactly the points of its descended torus. -/
def PinnedMarkedTorusPointComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)
    (R : TestAlgebra k),
    Function.Injective (pinnedMarkedTorusPoint C d R) ∧
      (∀ t, pinnedMarkedPoint C d R (descendedTorusInclusion R t) =
        pinnedMarkedTorusPoint C d R t ≫ M.torus.hom.hom) ∧
      ∀ s : IntegralPoints (splitTorus D) ((quadraticIntegralAlgebra k K).obj R),
        s ∈ Set.range (pinnedMarkedTorusPoint C d R) ↔
          s ≫ M.torus.hom.hom ∈ Set.range (pinnedMarkedPoint C d R)

/-- The ordered relative chart uses the descended torus itself, and its
absolute slots use the scalar inclusion and the conjugate graph. -/
def pinnedRelativeCell (σ : Gal(K/k)) (R : TestAlgebra k) (ns ps : List (TransportedOrbit D))
    (positiveFirst : Bool)
    (q : orderedParameters K R ns ×
      HopfPoints (coordinateHopf (closedSubgroupAlgebraicGroup T)) R × orderedParameters K R ps) :
    IntegralPoints M.group ((quadraticIntegralAlgebra k K).obj R) :=
  markedSplitCell M.toIntegralMarking ((quadraticIntegralAlgebra k K).obj R) ns ps positiveFirst
    (extendOrderedParameters σ R ns q.1, pinnedMarkedTorusPoint C d R q.2.1,
      extendOrderedParameters σ R ps q.2.2)

/-- Every point of the actual pinned group in either split ordered cell
has unique relative root and descended torus coordinates. -/
def PinnedFixedCellCoordinates : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (ns ps : List (TransportedOrbit D)),
      (∀ b ∈ ns ++ ps, b.1.Matches C (pinnedDiagram d σ) ∧
        ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ)) →
      Enumerates (ns.flatMap transportedLabels) {a | ¬ D.base.IsPos a} →
      Enumerates (ps.flatMap transportedLabels) {a | D.base.IsPos a} →
      ∀ (R : TestAlgebra k) (positiveFirst : Bool),
        let abs := markedAbsoluteCell M.toIntegralMarking ((quadraticIntegralAlgebra k K).obj R)
          (ns.flatMap transportedLabels) (ps.flatMap transportedLabels) positiveFirst
        let rel := pinnedRelativeCell C d σ R ns ps positiveFirst
        Function.Injective rel ∧
          Set.range rel = Set.range abs ∩ Set.range (pinnedMarkedPoint C d R)

end PinnedTorusAndCell

section RationalCellCoordinates

open AdjointCocharacters (coordinateHopf)
open AdjointBorelCohomology (PinnedTwist)
open IntegralSemisimpleModel Pinning
open OrderedRootProducts (Enumerates)
open Unipotent (closedSubgroupAlgebraicGroup)

universe u

attribute [local instance] integerAlgebra

/-- A singleton uses the ground field and a pair uses the splitting field. -/
def rationalOrbitParameter {D : BasedRootDatum.{u}} (k K : Type u)
    (b : TransportedOrbit D) : Type u :=
  match b.1.2 with
  | none => k
  | some _ => K

def rationalOrderedParameters {D : BasedRootDatum.{u}} (k K : Type u) :
    List (TransportedOrbit D) → Type u
  | [] => PUnit
  | b :: bs => rationalOrbitParameter k K b × rationalOrderedParameters k K bs

/-- The absolute slots on rational points use unital ring maps in the
transported coordinates. -/
def rationalOrbitCoordinates {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) :
    (b : TransportedOrbit D) → rationalOrbitParameter k K b → splitOrbitParameter K b
  | (⟨_, none⟩, _) => fun z => algebraMap k K z
  | (⟨_, some _⟩, _) => fun z => (z, σ z)

def rationalOrderedCoordinates {D : BasedRootDatum.{u}} {k K : Type u}
    [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) :
    (bs : List (TransportedOrbit D)) → rationalOrderedParameters k K bs →
      splitOrderedParameters K bs
  | [] => fun _ => PUnit.unit
  | b :: bs => fun v => (rationalOrbitCoordinates σ b v.1, rationalOrderedCoordinates σ bs v.2)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T)

/-- The rational chart in the splitting field, with the torus descended
through the specified pinned comparison. -/
def pinnedRationalRelativeCell (σ : Gal(K/k)) (ns ps : List (TransportedOrbit D))
    (positiveFirst : Bool)
    (q : rationalOrderedParameters k K ns ×
      HopfPoints (coordinateHopf (closedSubgroupAlgebraicGroup T)) k × rationalOrderedParameters k K ps) :
    IntegralPoints M.group (CommAlgCat.of Integers.{u} K) :=
  markedSplitCell M.toIntegralMarking (CommAlgCat.of Integers.{u} K) ns ps positiveFirst
    (rationalOrderedCoordinates σ ns q.1,
      (integralPointFunctor (splitTorus D)).map (evaluateGroundTensor k K)
        (pinnedMarkedTorusPoint C d (CommAlgCat.of k k) q.2.1),
      rationalOrderedCoordinates σ ps q.2.2)

/-- The two rational charts exhaust precisely the pinned rational points in
the corresponding ordered cells of the original marked group over K. -/
def PinnedRationalFixedCellCoordinates : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (ns ps : List (TransportedOrbit D)),
      (∀ b ∈ ns ++ ps, b.1.Matches C (pinnedDiagram d σ) ∧
        ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ)) →
      Enumerates (ns.flatMap transportedLabels) {a | ¬ D.base.IsPos a} →
      Enumerates (ps.flatMap transportedLabels) {a | D.base.IsPos a} →
      ∀ positiveFirst : Bool,
        let abs := markedAbsoluteCell M.toIntegralMarking (CommAlgCat.of Integers.{u} K)
          (ns.flatMap transportedLabels) (ps.flatMap transportedLabels) positiveFirst
        let rel := pinnedRationalRelativeCell C d σ ns ps positiveFirst
        let fix := fun p : HopfPoints (coordinateHopf G) k =>
          (integralPointFunctor M.group).map (evaluateGroundTensor k K)
            (pinnedMarkedPoint C d (CommAlgCat.of k k) p)
        Function.Injective rel ∧ Set.range rel = Set.range abs ∩ Set.range fix

end RationalCellCoordinates

section RationalTorusConjugation

open AdjointCocharacters (coordinateHopf)
open AdjointBorelCohomology (PinnedTwist)
open IntegralRootRelations (upper)
open IntegralSemisimpleModel Pinning
open Matrix (SpecialLinearGroup)
open Unipotent (closedSubgroupAlgebraicGroup)
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] integerAlgebra

/-- Conjugation by the actual descended torus on transported relative root
coordinates. The multipliers are the absolute root evaluations on the split
image of the torus. The layers use the integer normalization in each
parameter field. In the ramified quadratic case the paired thresholds
`j` and `j - log v(c)` are expressed in base-field units by dividing
both by two. -/
def PinnedRelativeTorusLayerConjugation : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist (P := C.realization.pinned) K C.realization.attached l B T),
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (w : List (SimpleRootOrbit D)), (∀ o ∈ w, o.Matches C (pinnedDiagram d σ)) →
      let R := CommAlgCat.of k k
      let S := CommAlgCat.of Integers.{u} K
      let splitPoint := fun p : HopfPoints (coordinateHopf G) k =>
        (integralPointFunctor M.group).map (evaluateGroundTensor k K) (pinnedMarkedPoint C d R p)
      let torus := fun t : HopfPoints (coordinateHopf (closedSubgroupAlgebraicGroup T)) k =>
        (integralPointFunctor (splitTorus D)).map (evaluateGroundTensor k K)
          (pinnedMarkedTorusPoint C d R t)
      let g := descendedTorusInclusion (G := G) (T := T) R
      let word := w.flatMap SimpleRootOrbit.roots
      let n := markedWeylWord M.toIntegralMarking S word
      let x := fun (a : D.I) (z : K) => MulAut.conj n (markedRootPoint M.toIntegralMarking S a z)
      let χ := fun (s : TorusValues D S) (a : D.I) =>
        s (Multiplicative.ofAdd (D.datum.root (weylWordPerm word a)))
      (∀ a : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, none) →
        ∃ ρ : SpecialLinearGroup (Fin 2) k →* HopfPoints (coordinateHopf G) k,
          (∀ u : k, splitPoint (ρ (upper u)) = x a (algebraMap k K u)) ∧
          ∀ t, ∃ s : TorusValues D S, torusPoint D S s = torus t ∧
            ∃ c : kˣ, Units.map (algebraMap k K).toMonoidHom c = χ s a ∧
              (∀ u : k, g t * ρ (upper u) * (g t)⁻¹ = ρ (upper ((c : k) * u))) ∧
              RootFiltrationShift k c ∧
              RootLayerConjugation k (fun u => ρ (upper u)) (g t) c) ∧
      ∀ a b : D.base.support, SimpleRootOrbit.Matches C (pinnedDiagram d σ) (a, some b) →
        ∃ ρ : SpecialLinearGroup (Fin 2) K →* HopfPoints (coordinateHopf G) k,
          (∀ u : K, splitPoint (ρ (upper u)) = x a u * x b (σ u)) ∧
          ∀ t, ∃ s : TorusValues D S, torusPoint D S s = torus t ∧
            χ s b = Units.map σ.toMonoidHom (χ s a) ∧
            (∀ u : K, g t * ρ (upper u) * (g t)⁻¹ = ρ (upper ((χ s a : K) * u))) ∧
            RootFiltrationShift K (χ s a) ∧
            RootLayerConjugation K (fun u => ρ (upper u)) (g t) (χ s a)

end RationalTorusConjugation

open IntegralSemisimpleModel in
attribute [local instance] IntegralSemisimpleModel.integerAlgebra in
/-- Integral rescalings from the marked representatives preserve every
valuation layer, including the zero parameter. -/
def IntegralUnitValuation.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (c : Integers.{u}ˣ) (z : K),
    normalizedValuation K (algebraMap Integers.{u} K (c : Integers.{u}) * z) =
      normalizedValuation K z

end

end LinearAlgebraicGroups.Specs.ExceptionalMarkedRootDescent
