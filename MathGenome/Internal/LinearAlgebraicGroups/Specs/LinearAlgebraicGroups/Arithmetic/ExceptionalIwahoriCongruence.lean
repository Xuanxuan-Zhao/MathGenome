import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.LocalField.Basic
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.FieldTheory.AlgebraicClosure

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped WithZero TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalIwahoriCongruence

open IntegralSemisimpleModel

noncomputable section

/-- Restrict a point on the integral model along a homomorphism of test rings. -/
abbrev changeRing {R S : IntegralAlgebra.{u}} {X : IntegralScheme.{u}}
    (f : R ⟶ S) (p : integralSpec.obj (op R) ⟶ X) :
    integralSpec.obj (op S) ⟶ X :=
  integralSpec.map f.op ≫ p

/-- The residue field with its inherited algebra structure. -/
abbrev residueRing (R : IntegralAlgebra.{u}) [IsLocalRing R] : IntegralAlgebra.{u} :=
  CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField R)

/-- Reduction to the closed point of a local test ring. -/
abbrev residueHom (R : IntegralAlgebra.{u}) [IsLocalRing R] : R ⟶ residueRing R :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ Integers.{u} (IsLocalRing.maximalIdeal R))

/-- An open chart over the integers lifts an integral point precisely when
the residue point factors through the chart. The integral lift is unique. -/
def LocalChartLifting : Prop :=
  ∀ (R : IntegralAlgebra.{u}) [IsLocalRing R]
    {X Y : IntegralScheme.{u}} (c : X ⟶ Y) [IsOpenImmersion c.left]
    (p : integralSpec.obj (op R) ⟶ Y),
    (∃! z : integralSpec.obj (op R) ⟶ X, z ≫ c = p) ↔
      ∃ z : integralSpec.obj (op (CommAlgCat.of Integers.{u}
        (IsLocalRing.ResidueField R))) ⟶ X, z ≫ c = changeRing (residueHom R) p

/-- Congruence of points in an open chart is tested on the chart itself,
including when the scalar ring is a nonreduced congruence quotient. -/
def ChartCongruence : Prop :=
  ∀ {R S : IntegralAlgebra.{u}} (f : R ⟶ S)
    {X Y : IntegralScheme.{u}} (c : X ⟶ Y) [IsOpenImmersion c.left]
    (a b : integralSpec.obj (op R) ⟶ X),
    changeRing f (a ≫ c) = changeRing f (b ≫ c) ↔
      changeRing f a = changeRing f b

/-- The image of a root-parameter layer in a truncated valuation ring. -/
abbrev truncatedLayer (R : Type*) [CommRing R] [IsLocalRing R] (m n : ℕ) :=
  ↥(Submodule.map ((IsLocalRing.maximalIdeal R) ^ n).mkQ
    ((IsLocalRing.maximalIdeal R) ^ m))

/-- Each uniformizer step up to the truncation removes one residue-field factor. -/
def TruncatedLayerCardinality : Prop :=
  ∀ (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (m n : ℕ), m ≤ n →
    Nat.card (truncatedLayer R m n) =
      Nat.card (IsLocalRing.ResidueField R) ^ (n - m)

/-- Counting in each coordinate can use its own truncation exponent. The two
subgroups have the same truncated unit-torus factor. -/
def IndexFromTruncatedChart : Prop :=
  ∀ {G J : Type u} [Group G] [Fintype J] (H : Subgroup G) (N : Subgroup G)
    [N.Normal] (_hNH : N ≤ H)
    (R : J → Type u) [∀ j, CommRing (R j)] [∀ j, IsDomain (R j)]
    [∀ j, IsDiscreteValuationRing (R j)] [∀ j, Finite (IsLocalRing.ResidueField (R j))]
    (a b m : J → ℕ) (_hab : a ≤ b) (_hbm : b ≤ m)
    (q : ℕ) (_hq : 0 < q) (_hres : ∀ j, Nat.card (IsLocalRing.ResidueField (R j)) = q)
    (T : Type u) [Finite T] [Nonempty T],
    Nonempty ((G ⧸ N) ≃ T × (∀ j, truncatedLayer (R j) (a j) (m j))) →
    Nonempty ((H ⧸ N.comap H.subtype) ≃ T × (∀ j, truncatedLayer (R j) (b j) (m j))) →
    H.index = q ^ ∑ j, (b j - a j)

/-- The actual ordered tuple of root points in the cartesian product of additive lines. -/
def rootValuePoint {I : Type u} (L : AdditiveLine.{u}) (R : IntegralAlgebra.{u}) :
    (l : List I) → (Fin l.length → R) →
    (integralSpec.obj (op R) ⟶ product (fun _ : I => L.group.X) l)
  | [], _ => toUnit _
  | _ :: l, r => lift (L.point R (r 0)) (rootValuePoint L R l (Fin.tail r))

abbrev CellValues (D : Pinning.BasedRootDatum.{u}) (R : IntegralAlgebra.{u})
    (negative positive : List D.I) :=
  (Fin negative.length → R) × TorusValues D R × (Fin positive.length → R)

def cellValuePoint {D : Pinning.BasedRootDatum.{u}} (L : AdditiveLine.{u})
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (z : CellValues D R negative positive) :
    integralSpec.obj (op R) ⟶
      product (fun _ : D.I => L.group.X) negative ⊗
        ((splitTorus D).X ⊗ product (fun _ : D.I => L.group.X) positive) :=
  lift (rootValuePoint L R negative z.1)
    (lift (torusPoint D R z.2.1) (rootValuePoint L R positive z.2.2))

def cellValue {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (z : CellValues D R negative positive) : IntegralPoints M.group R :=
  cellValuePoint M.line R negative positive z ≫ cellMap M.line M.torus M.root negative positive

def mapCellValues {D : Pinning.BasedRootDatum.{u}} {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) {negative positive : List D.I} (z : CellValues D R negative positive) :
    CellValues D S negative positive :=
  (fun i => f.hom (z.1 i), (Units.map f.hom.toRingHom).comp z.2.1, fun i => f.hom (z.2.2 i))

/-- The chart is natural in the scalar ring, and the ordered coordinates are
unique on its image over every ring. -/
def MarkedChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (_hp : OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}),
    (∀ R, Function.Injective (cellValue M R negative positive)) ∧
    ∀ {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (z : CellValues D R negative positive),
      changeRing f (cellValue M R negative positive z) =
        cellValue M S negative positive (mapCellValues f z)

/-- Reducing into the marked positive part, written as the torus times the
ordered product of the positive root groups, forces exactly the negative
parameters to lie in the maximal ideal. -/
def MarkedBorelReductionChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    [IsLocalRing R] (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (_hp : OrderedRootProducts.Enumerates positive {i | D.base.IsPos i})
    (g : IntegralPoints M.group R),
    (∃ (t : TorusValues D _) (z : Fin positive.length → IsLocalRing.ResidueField R),
      changeRing (residueHom R) g = cellValue M _ negative positive (0, t, z)) ↔
    ∃! z : CellValues D R negative positive,
      cellValue M R negative positive z = g ∧
        ∀ i, z.1 i ∈ IsLocalRing.maximalIdeal R

/-- Torus reduction is equivalent to every root coordinate lying in the
maximal ideal, including coordinates whose scale has zero absolute depth. -/
def MarkedTorusReductionChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    [IsLocalRing R] (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (_hp : OrderedRootProducts.Enumerates positive {i | D.base.IsPos i})
    (g : IntegralPoints M.group R),
    (∃ t : TorusValues D _,
      changeRing (residueHom R) g = cellValue M _ negative positive (0, t, 0)) ↔
    ∃! z : CellValues D R negative positive,
      cellValue M R negative positive z = g ∧
        (∀ i, z.1 i ∈ IsLocalRing.maximalIdeal R) ∧
        ∀ i, z.2.2 i ∈ IsLocalRing.maximalIdeal R


/-- Multiply each absolute root parameter by its character evaluated on the
scaling torus point. The torus coordinate itself is unchanged. -/
def scaleCellValues {D : Pinning.BasedRootDatum.{u}} {R : IntegralAlgebra.{u}}
    {negative positive : List D.I} (t : TorusValues D R) (z : CellValues D R negative positive) :
    CellValues D R negative positive :=
  (fun i => (t (Multiplicative.ofAdd (D.datum.root negative[i])) : R) * z.1 i,
    z.2.1, fun i => (t (Multiplicative.ofAdd (D.datum.root positive[i])) : R) * z.2.2 i)

def ScaleMarkedChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (negative positive : List D.I) (t : TorusValues D R)
    (z : CellValues D R negative positive),
    MulAut.conj (torusPoint D R t ≫ M.torus.hom.hom)
      (cellValue M R negative positive z) =
        cellValue M R negative positive (scaleCellValues t z)

/-- The scaled point has integral coordinates and torus reduction exactly when
the original point is in the same ordered chart and the scaled coordinates
descend to integral coordinates with strictly positive root depths. -/
def ScaledTorusReduction : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (K E O : IntegralAlgebra.{u}) [IsLocalRing O]
    (f : K ⟶ E) (i : O ⟶ E)
    (_hf : Function.Surjective (integralSpec.map f.op).left)
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {j | ¬ D.base.IsPos j})
    (_hp : OrderedRootProducts.Enumerates positive {j | D.base.IsPos j})
    (t : TorusValues D E) (g : IntegralPoints M.group K),
    (∃ p : IntegralPoints M.group O,
      changeRing i p =
        MulAut.conj (torusPoint D E t ≫ M.torus.hom.hom) (changeRing f g) ∧
      ∃ r : TorusValues D _,
        changeRing (residueHom O) p = cellValue M _ negative positive (0, r, 0)) ↔
    ∃! z : CellValues D K negative positive,
      cellValue M K negative positive z = g ∧
      ∃ w : CellValues D O negative positive,
        mapCellValues i w = scaleCellValues t (mapCellValues f z) ∧
          (∀ j, w.1 j ∈ IsLocalRing.maximalIdeal O) ∧
          ∀ j, w.2.2 j ∈ IsLocalRing.maximalIdeal O

/-- A field-point subgroup characterized by integral reduction after conjugation
by the scaling point. Here `integral` maps the integral points to the auxiliary
field and `reduce` maps them to the residue field. -/
def scaledReductionSubgroup {G E O k : Type*} [Group G] [Group E] [Group O] [Group k]
    (extend : G →* E) (integral : O →* E) (reduce : O →* k)
    (T : Subgroup k) (s : E) : Subgroup G :=
  ((T.comap reduce).map integral).comap ((MulAut.conj s).toMonoidHom.comp extend)

/-- Comparing two scaling points across a normalizer element amounts to the
integral representative whose residue normalizes the torus. -/
def ScaledReductionCovariance : Prop :=
  ∀ {G E O k : Type*} [Group G] [Group E] [Group O] [Group k]
    (extend : G →* E) (integral : O →* E) (reduce : O →* k)
    (T : Subgroup k) (sx sy : E) (n : G) (r : O),
    (_hr : reduce r ∈ Subgroup.normalizer (T : Set k)) →
    (_he : sy * extend n * sx⁻¹ = integral r) →
    (scaledReductionSubgroup extend integral reduce T sx).map (MulAut.conj n).toMonoidHom =
      scaledReductionSubgroup extend integral reduce T sy

/-- The elements of an ordered chart satisfying the specified thresholds. -/
def thresholdSet {G J T : Type*} {K : J → Type*} {Γ : J → Type*}
    (encode : T × (∀ j, K j) → G) [∀ j, LE (Γ j)] (depth : ∀ j, K j → Γ j)
    (a : ∀ j, Γ j) : Set G :=
  encode '' {z | ∀ j, a j ≤ depth j (z.2 j)}

/-- Intersecting two chart subgroups takes the stricter threshold separately
in every parameter field and leaves the unit-torus factor untouched. -/
def ThresholdIntersection : Prop :=
  ∀ {G J T : Type*} {K : J → Type*} {Γ : J → Type*}
    (encode : T × (∀ j, K j) → G) [∀ j, LinearOrder (Γ j)] (depth : ∀ j, K j → Γ j)
    (a b : ∀ j, Γ j), Function.Injective encode →
    thresholdSet encode depth a ∩ thresholdSet encode depth b =
      thresholdSet encode depth (fun j => max (a j) (b j))

/-- A reduction quotient is determined by independently truncated coordinates.
The subgroup chart is allowed any independent torus and root parameter types. -/
def QuotientFromTruncatedCoordinates : Prop :=
  ∀ {G Q T T' J : Type u} [Group G] [Group Q] {K K' : J → Type u}
    (reduce : G →* Q) (chart : T × (∀ j, K j) → G)
    (truncT : T → T') (trunc : ∀ j, K j → K' j),
    Function.Surjective chart → Function.Surjective truncT →
    (∀ j, Function.Surjective (trunc j)) →
    (∀ z w, reduce (chart z) = reduce (chart w) ↔
      (truncT z.1 = truncT w.1 ∧ ∀ j, trunc j (z.2 j) = trunc j (w.2 j))) →
    Nonempty ((G ⧸ reduce.ker) ≃ T' × (∀ j, K' j))

/-- Truncating at depth `n` in an extension of ramification index `e` truncates
a parameter in the base ring at depth `ceil(n/e)`. -/
def RamifiedTruncation : Prop :=
  ∀ {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) (e n : ℕ), 0 < e →
    Ideal.map f (IsLocalRing.maximalIdeal R) = (IsLocalRing.maximalIdeal S) ^ e →
    Ideal.comap f ((IsLocalRing.maximalIdeal S) ^ n) =
      (IsLocalRing.maximalIdeal R) ^ ((n + e - 1) / e)

/-- Affine point topology given by evaluation on the coordinate algebra. -/
abbrev affinePointTopology (B A K : Type*) [CommRing B] [CommRing A] [CommRing K]
    [Algebra B A] [Algebra B K] [TopologicalSpace K] : TopologicalSpace (A →ₐ[B] K) :=
  TopologicalSpace.induced (fun f : A →ₐ[B] K => (f : A → K)) inferInstance

/-- A finite-type affine scheme's integral points reducing into a given set
of residue points are compact open. In a continuous fixed locus, such as
the rational points of a pinned twist, they are again compact open in
the induced rational point topology. -/
def CompactOpenAffineReduction : Prop :=
  ∀ {B A K k : Type*} [CommRing B] [CommRing A] [CommRing K] [CommRing k]
    [Algebra B A] [Algebra B K] [Algebra B k] [Algebra.FiniteType B A]
    [TopologicalSpace K] [T2Space K] [IsTopologicalRing K]
    [TopologicalSpace k] [DiscreteTopology k]
    (R : Subalgebra B K) (_hc : IsCompact (R : Set K)) (_ho : IsOpen (R : Set K))
    (red : R →ₐ[B] k) (_hr : Continuous red) (C : Set (A →ₐ[B] k)),
    letI := affinePointTopology B A K
    let I := (fun f : A →ₐ[B] R => R.val.comp f) '' {f | red.comp f ∈ C}
    IsCompact I ∧ IsOpen I ∧
      ∀ σ : (A →ₐ[B] K) → (A →ₐ[B] K), Continuous σ →
        let F := {p | σ p = p}
        IsCompact ((Subtype.val : F → (A →ₐ[B] K)) ⁻¹' I) ∧
          IsOpen ((Subtype.val : F → (A →ₐ[B] K)) ⁻¹' I)

/-- Regard a concrete ring as a canonical integral test algebra. -/
abbrev integralRing (R : Type u) [CommRing R] : IntegralAlgebra.{u} :=
  @CommAlgCat.of Integers.{u} _ R _ (integerAlgebra R)

/-- A ring homomorphism preserves the canonical algebra structures over the integers. -/
def integralRingMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    integralRing R ⟶ integralRing S :=
  letI := integerAlgebra R
  letI := integerAlgebra S
  CommAlgCat.ofHom { f with commutes' := fun x => map_intCast f x.down }

/-- Every scaling denominator is realized in a finite valued auxiliary
extension. This includes uniformizer roots in positive characteristic. -/
def FiniteScalingExtension : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (π : Kˣ) {d : ℕ}, 0 < d →
    ∃ (E : IntermediateField K (AlgebraicClosure K)),
      FiniteDimensional K E ∧
      ∃ (v : ValuativeRel E) (τ : TopologicalSpace E),
        letI := v
        letI := τ
        ValuativeExtension K E ∧ IsNonarchimedeanLocalField E ∧
          ∃ ξ : Eˣ, (ξ : E) ^ d = algebraMap K E (π : K)

/-- The root-depth test with the actual valuation of the scaled parameter.
For a rational cocharacter represented by `y/d`, `ξ` is a chosen
`d`-th root of the base uniformizer and `t = y(ξ)`. -/
def ValuedScaledChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K E : Type u} {Γ : Type*} [Field K] [Field E] [LinearOrderedCommGroupWithZero Γ]
    (f : K →+* E) (v : Valuation E Γ)
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {j | ¬ D.base.IsPos j})
    (_hp : OrderedRootProducts.Enumerates positive {j | D.base.IsPos j})
    (y : D.Y) (ξ : Eˣ) (g : IntegralPoints M.group (integralRing K)),
    let t := cocharacter D y (integralRing E) ξ
    let O := integralRing v.valuationSubring
    let i := integralRingMap v.valuationSubring.subtype
    (∃ p : IntegralPoints M.group O,
      changeRing i p = MulAut.conj (torusPoint D (integralRing E) t ≫ M.torus.hom.hom)
        (changeRing (integralRingMap f) g) ∧
      ∃ r : TorusValues D _,
        changeRing (residueHom O) p = cellValue M _ negative positive (0, r, 0)) ↔
    ∃! z : CellValues D (integralRing K) negative positive,
      cellValue M (integralRing K) negative positive z = g ∧
      (∀ χ, v (f (z.2.1 χ : K)) = 1) ∧
      (∀ j : Fin negative.length,
        v ((↑(ξ ^ D.datum.toLinearMap (D.datum.root negative[j]) y) : E) * f (z.1 j)) < 1) ∧
      (∀ j : Fin positive.length,
        v ((↑(ξ ^ D.datum.toLinearMap (D.datum.root positive[j]) y) : E) * f (z.2.2 j)) < 1)

/-- Restriction of scalars on the functor of group points. -/
abbrev changeRingHom (G : IntegralGroup.{u}) {R S : IntegralAlgebra.{u}} (f : R ⟶ S) :
    IntegralPoints G R →* IntegralPoints G S :=
  ((integralPointFunctor G).map f).hom

/-- The preimage of the positive residue Borel inside the split field points
or inside the rational points, supplied as a subgroup of the split points. -/
def iwahoriSubgroup {G : IntegralGroup.{u}} {R K : IntegralAlgebra.{u}} [IsLocalRing R]
    (i : R ⟶ K)
    (B : Subgroup (IntegralPoints G (CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField R))))
    (H : Subgroup (IntegralPoints G K)) : Subgroup H :=
  ((B.comap (changeRingHom G (residueHom R))).map (changeRingHom G i)).comap H.subtype

/-- Either order of signs gives the Iwahori chart. In the positive-first
expression the root factors of each word appear inverted in reverse
order, which gives the same parameter layers. -/
def IwahoriChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {R K : IntegralAlgebra.{u}} [IsLocalRing R] (i : R ⟶ K)
    (_hi : Function.Injective i.hom)
    (B : Subgroup (IntegralPoints M.group
      (CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField R))))
    (H : Subgroup (IntegralPoints M.group K))
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {j | ¬ D.base.IsPos j})
    (_hp : OrderedRootProducts.Enumerates positive {j | D.base.IsPos j})
    (_hB : (B : Set _) =
      Set.range (fun z : TorusValues D (CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField R)) ×
        (Fin positive.length → IsLocalRing.ResidueField R) =>
        cellValue M (CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField R))
          negative positive (0, z.1, z.2))),
    ∀ g : H,
      (g ∈ iwahoriSubgroup i B H ↔
        ∃! z : CellValues D R negative positive,
          changeRing i (cellValue M R negative positive z) = (g : IntegralPoints M.group K) ∧
          ∀ j, z.1 j ∈ IsLocalRing.maximalIdeal R) ∧
      (g ∈ iwahoriSubgroup i B H ↔
        ∃! z : CellValues D R negative positive,
          (changeRing i (cellValue M R negative positive z))⁻¹ = (g : IntegralPoints M.group K) ∧
          ∀ j, z.1 j ∈ IsLocalRing.maximalIdeal R)

/-- The actual word when the signs are exchanged by inversion. The individual
factors are the same marked root points in reverse order with inverse parameters. -/
def PositiveFirstWord : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (z : CellValues D R negative positive),
    (cellValue M R negative positive z)⁻¹ =
      (rootValuePoint M.line R positive z.2.2 ≫ rootProduct M.line M.root positive)⁻¹ *
        ((torusPoint D R z.2.1 ≫ M.torus.hom.hom)⁻¹ *
          (rootValuePoint M.line R negative z.1 ≫ rootProduct M.line M.root negative)⁻¹)

/-- The ideal of parameters of depth at least `a`, in uniformizer steps. -/
abbrev integralLayer (R : Type*) [CommRing R] [IsLocalRing R] (a : ℕ) :=
  ↥((IsLocalRing.maximalIdeal R) ^ a)

def truncateLayer (R : Type*) [CommRing R] [IsLocalRing R] (a m : ℕ)
    (x : integralLayer R a) : truncatedLayer R a m :=
  ⟨((IsLocalRing.maximalIdeal R) ^ m).mkQ (x : R), Submodule.mem_map.mpr ⟨x, x.prop, rfl⟩⟩

/-- The index from a common scalar reduction map and the independently
truncated integral root coordinates. The kernel in the larger subgroup
lies in the smaller one once the congruence depth reaches every higher
threshold. -/
def IndexByIndependentCongruence : Prop :=
  ∀ {G Q T T' J : Type u} [Group G] [Group Q] [Fintype J] [Finite T'] [Nonempty T']
    (reduce : G →* Q) (I H : Subgroup G) (_hHI : H ≤ I)
    (R : J → Type u) [∀ j, CommRing (R j)] [∀ j, IsDomain (R j)]
    [∀ j, IsDiscreteValuationRing (R j)] [∀ j, Finite (IsLocalRing.ResidueField (R j))]
    (a b m : J → ℕ) (_hab : a ≤ b) (_hbm : b ≤ m)
    (q : ℕ) (_hq : 0 < q) (_hres : ∀ j, Nat.card (IsLocalRing.ResidueField (R j)) = q)
    (chart : T × (∀ j, R j) → G) (truncateT : T → T'),
    Function.Surjective truncateT →
    (∃ t, chart (t, 0) = 1) →
    (∀ g : G, g ∈ I ↔ ∃ (t : T) (x : ∀ j, integralLayer (R j) (a j)),
      chart (t, fun j => x j) = g) →
    (∀ g : G, g ∈ H ↔ ∃ (t : T) (x : ∀ j, integralLayer (R j) (b j)),
      chart (t, fun j => x j) = g) →
    (∀ z w, reduce (chart z) = reduce (chart w) ↔
      truncateT z.1 = truncateT w.1 ∧
        ∀ j, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (R j)) ^ m j) (z.2 j) =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (R j)) ^ m j) (w.2 j)) →
    ((reduce.comp I.subtype).ker ≤ H.subgroupOf I) ∧
      H.relIndex I = q ^ ∑ j, (b j - a j)

abbrev congruenceRing (R : IntegralAlgebra.{u}) [IsLocalRing R] (n : ℕ) :=
  CommAlgCat.of Integers.{u} (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)

abbrev congruenceHom (R : IntegralAlgebra.{u}) [IsLocalRing R] (n : ℕ) :
    R ⟶ congruenceRing R n :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ Integers.{u} ((IsLocalRing.maximalIdeal R) ^ n))

/-- The reduction kernel and index for an ordered marked chart with orbit
parameters. A root parameter may occur in both absolute slots of a paired
orbit, through different embeddings of its parameter field. -/
def MarkedCongruenceIndex : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)]
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {j | ¬ D.base.IsPos j})
    (_hp : OrderedRootProducts.Enumerates positive {j | D.base.IsPos j})
    {J : Type u} [Fintype J] (P : J → Type u)
    [∀ j, CommRing (P j)] [∀ j, IsDomain (P j)] [∀ j, IsDiscreteValuationRing (P j)]
    [∀ j, Finite (IsLocalRing.ResidueField (P j))]
    (neg : Fin negative.length → J) (pos : Fin positive.length → J)
    (embedNeg : ∀ i, P (neg i) →+* R) (embedPos : ∀ i, P (pos i) →+* R)
    (_hOrbits : ∀ j, j ∈ Set.range neg ∪ Set.range pos)
    (e : J → ℕ) (_he : ∀ j, 0 < e j)
    (_hNeg : ∀ i, Ideal.map (embedNeg i) (IsLocalRing.maximalIdeal (P (neg i))) =
      (IsLocalRing.maximalIdeal R) ^ e (neg i))
    (_hPos : ∀ i, Ideal.map (embedPos i) (IsLocalRing.maximalIdeal (P (pos i))) =
      (IsLocalRing.maximalIdeal R) ^ e (pos i))
    (T : Set (TorusValues D R)) [Nonempty T],
    let chart (z : T × (∀ j, P j)) := cellValue M R negative positive
      (fun i => embedNeg i (z.2 (neg i)), z.1.val, fun i => embedPos i (z.2 (pos i)))
    ∀ (I H : Subgroup (IntegralPoints M.group R)) (_hHI : H ≤ I)
      (a b : J → ℕ) (_hab : a ≤ b) (q : ℕ)
      (_hq : 0 < q) (_hres : ∀ j, Nat.card (IsLocalRing.ResidueField (P j)) = q),
      (∃ t, chart (t, 0) = 1) →
      (∀ g, g ∈ I ↔ ∃ (t : T) (x : ∀ j, integralLayer (P j) (a j)),
        chart (t, fun j => x j) = g) →
      (∀ g, g ∈ H ↔ ∃ (t : T) (x : ∀ j, integralLayer (P j) (b j)),
        chart (t, fun j => x j) = g) →
      ∃ n : ℕ, 0 < n ∧
        ((changeRingHom M.group (congruenceHom R n)).comp I.subtype).ker ≤ H.subgroupOf I ∧
        H.relIndex I = q ^ ∑ j, (b j - a j)

/-- The affine finite-type coordinate algebra of an integral model. -/
def IntegralAffinePresentation : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D),
    ∃ A : IntegralAlgebra.{u}, Algebra.FiniteType Integers.{u} A ∧
      Nonempty (integralSpec.obj (op A) ≅ M.group.X)

def pointAlgebraEquiv (A : IntegralAlgebra.{u}) {X : IntegralScheme.{u}}
    (iso : integralSpec.obj (op A) ≅ X) (R : IntegralAlgebra.{u}) :
    (A →ₐ[Integers.{u}] R) ≃ (integralSpec.obj (op R) ⟶ X) :=
  let hom : (A →ₐ[Integers.{u}] R) ≃ (A ⟶ R) :=
    { toFun := fun f => CommAlgCat.ofHom f
      invFun := fun f => f.hom
      left_inv := fun _ => rfl
      right_inv := fun f => CommAlgCat.ofHom_hom f }
  (hom.trans Quiver.Hom.opEquiv).trans
    (((algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).homEquiv
      (X := op R) (Y := op A)).trans
      { toFun := (· ≫ iso.hom)
        invFun := (· ≫ iso.inv)
        left_inv := by intro p; simp
        right_inv := by intro p; simp })

abbrev markedPointTopology (A : IntegralAlgebra.{u}) {X : IntegralScheme.{u}}
    (iso : integralSpec.obj (op A) ≅ X) (K : Type u) [Field K] [TopologicalSpace K] :
    TopologicalSpace (integralSpec.obj (op (integralRing K)) ⟶ X) :=
  TopologicalSpace.induced (pointAlgebraEquiv A iso (integralRing K)).symm
    (@affinePointTopology Integers.{u} A K _ _ _ A.algebra (integralRing K).algebra _)

/-- The valuation ring as an algebra over the lifted integers in the local field. -/
abbrev localIntegersAlgebra (K : Type u) [Field K] [ValuativeRel K] :
    letI := integerAlgebra K
    Subalgebra Integers.{u} K :=
  letI := integerAlgebra K
  { (ValuativeRel.valuation K).valuationSubring.toSubring with
    algebraMap_mem' := fun z => by
      change (z.down : K) ∈ (ValuativeRel.valuation K).valuationSubring.toSubring
      exact intCast_mem _ _ }

abbrev localIntegers (K : Type u) [Field K] [ValuativeRel K] : IntegralAlgebra.{u} :=
  letI := integerAlgebra K
  CommAlgCat.of Integers.{u} (localIntegersAlgebra K)

instance localIntegers_isLocalRing (K : Type u) [Field K] [ValuativeRel K] :
    IsLocalRing (localIntegers K) :=
  inferInstanceAs (IsLocalRing (ValuativeRel.valuation K).valuationSubring)

abbrev localIntegersInclusion (K : Type u) [Field K] [ValuativeRel K] :
    localIntegers K ⟶ integralRing K :=
  letI := integerAlgebra K
  CommAlgCat.ofHom (localIntegersAlgebra K).val

/-- The actual subgroup defined by integral Borel reduction is compact open
in the local point topology. The intersection with a continuous fixed
locus is compact open with its induced topology. -/
def CompactOpenLocalModel : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (A : IntegralAlgebra.{u}) [Algebra.FiniteType Integers.{u} A]
    (iso : integralSpec.obj (op A) ≅ M.group.X)
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
        (IsLocalRing.ResidueField (localIntegers K))))),
    letI : TopologicalSpace (IntegralPoints M.group (integralRing K)) :=
      markedPointTopology A iso K
    let I : Subgroup (IntegralPoints M.group (integralRing K)) := (B.comap (changeRingHom M.group (residueHom (localIntegers K)))).map
      (changeRingHom M.group (localIntegersInclusion K))
    IsCompact (I : Set (IntegralPoints M.group (integralRing K))) ∧
    IsOpen (I : Set (IntegralPoints M.group (integralRing K))) ∧
      ∀ σ : IntegralPoints M.group (integralRing K) → IntegralPoints M.group (integralRing K),
        Continuous σ →
        let F : Set (IntegralPoints M.group (integralRing K)) := {g | σ g = g}
        IsCompact ((Subtype.val : F → IntegralPoints M.group (integralRing K)) ⁻¹' (↑I)) ∧
          IsOpen ((Subtype.val : F → IntegralPoints M.group (integralRing K)) ⁻¹' (↑I))

/-- The least integer parameter step for which the scaled depth is strictly positive.
The offset and the step are taken in the same additive valuation units. -/
def stepThreshold (step offset : ℤ) : ℤ := -offset / step + 1

def StepThresholdCriterion : Prop :=
  ∀ (step offset a : ℤ), 0 < step →
    (stepThreshold step offset = a ↔
      0 < offset + a * step ∧ offset + (a - 1) * step ≤ 0)

/-- Normalizing the valuation in each parameter field, restriction from a
valued extension multiplies additive depth by the image depth of a uniformizer. -/
def ValuationExtensionPowers : Prop :=
  ∀ {K E : Type u} [Field K] [Field E]
    (f : K →+* E) (vK : Valuation K ℤᵐ⁰) (vE : Valuation E ℤᵐ⁰)
    (π : Kˣ), vK (π : K) = WithZero.exp (-1 : ℤ) →
    (∀ z, vK z = 1 → vE (f z) = 1) →
    ∀ (e : ℤ), 0 < e → vE (f (π : K)) = WithZero.exp (-e) →
    ∀ z, vE (f z) = vK z ^ e

/-- If `x = y/d` and `ξ ^ d = π`, multiplying a root parameter by the
root character of `y(ξ)` imposes the integer threshold for that parameter
field. Here `k = ⟨α,y⟩`, `r` is the depth of `π` in the auxiliary field
and `e` is the depth of a parameter-field uniformizer there. -/
def ScaledParameterThreshold : Prop :=
  ∀ {K E : Type u} [Field K] [Field E]
    (f : K →+* E) (vK : Valuation K ℤᵐ⁰) (vE : Valuation E ℤᵐ⁰)
    (e : ℤ), 0 < e → (∀ z, vE (f z) = vK z ^ e) →
    ∀ (ξ π : Eˣ) (d : ℕ), 0 < d → (ξ : E) ^ d = π →
    ∀ (r k : ℤ), vE (π : E) = WithZero.exp (-r) →
    ∀ z, vE ((↑(ξ ^ k) : E) * f z) < 1 ↔
      vK z ≤ WithZero.exp (-stepThreshold ((d : ℤ) * e) (k * r))

/-- A nonnegative threshold in uniformizer steps is exactly membership of
the indicated power of the maximal ideal. -/
def IdealLayerValuation : Prop :=
  ∀ {K : Type u} [Field K] (v : Valuation K ℤᵐ⁰)
    (π : v.valuationSubring), v (π : K) = WithZero.exp (-1 : ℤ) →
    ∀ (x : v.valuationSubring) (a : ℕ),
      x ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ a ↔
        v (x : K) ≤ WithZero.exp (-(a : ℤ))

/-- The image of the marked torus on points of a scalar ring. -/
def markedTorus {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) : Subgroup (IntegralPoints M.group R) :=
  (((yonedaGrp.map M.torus).app (op (integralSpec.obj (op R)))).hom).range

/-- The subgroup of rational points with integral torus reduction after scaling. -/
def markedScaledReduction {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K E : Type u} {Γ : Type*} [Field K] [Field E] [LinearOrderedCommGroupWithZero Γ]
    (H : Subgroup (IntegralPoints M.group (integralRing K)))
    (f : K →+* E) (v : Valuation E Γ) (y : D.Y) (ξ : Eˣ) : Subgroup H :=
  let O := integralRing v.valuationSubring
  scaledReductionSubgroup ((changeRingHom M.group (integralRingMap f)).comp H.subtype)
    (changeRingHom M.group (integralRingMap v.valuationSubring.subtype))
    (changeRingHom M.group (residueHom O)) (markedTorus M _)
    (torusPoint D (integralRing E) (cocharacter D y (integralRing E) ξ) ≫ M.torus.hom.hom)

/-- The rational points in the marked open cell, expressed by one parameter
per relative root. The embeddings give the absolute slots of its orbit. -/
structure RationalRootChart {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K : Type u} [Field K] (H : Subgroup (IntegralPoints M.group (integralRing K)))
    (negative positive : List D.I) (J : Type u) (P : J → Type u) [∀ j, Field (P j)] where
  torus : Set (TorusValues D (integralRing K))
  neg : Fin negative.length → J
  pos : Fin positive.length → J
  negMap : ∀ i, P (neg i) →+* K
  posMap : ∀ i, P (pos i) →+* K
  covers : ∀ j, j ∈ Set.range neg ∪ Set.range pos
  rational : ∀ z : CellValues D (integralRing K) negative positive,
    cellValue M (integralRing K) negative positive z ∈ H ↔
      ∃ (t : torus) (x : ∀ j, P j),
        (fun i => negMap i (x (neg i)), t.val, fun i => posMap i (x (pos i))) = z

def RationalRootChart.coordinates {D : Pinning.BasedRootDatum.{u}} {M : IntegralMarking D}
    {K : Type u} [Field K] {H : Subgroup (IntegralPoints M.group (integralRing K))}
    {negative positive : List D.I} {J : Type u} {P : J → Type u} [∀ j, Field (P j)]
    (C : RationalRootChart M H negative positive J P) (t : C.torus) (x : ∀ j, P j) :
    CellValues D (integralRing K) negative positive :=
  (fun i => C.negMap i (x (C.neg i)), t.val, fun i => C.posMap i (x (C.pos i)))

/-- At a rational cocharacter point use one signed integer threshold per
rational parameter field. In a paired orbit the two embedded coordinates
use the same root pairing and the same valuation restriction. -/
def RationalScaledChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K E : Type u} [Field K] [Field E]
    (H : Subgroup (IntegralPoints M.group (integralRing K)))
    (f : K →+* E) (v : Valuation E ℤᵐ⁰)
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (_hp : OrderedRootProducts.Enumerates positive {i | D.base.IsPos i})
    {J : Type u} (P : J → Type u) [∀ j, Field (P j)]
    (C : RationalRootChart M H negative positive J P)
    (vP : ∀ j, Valuation (P j) ℤᵐ⁰) (e : J → ℤ) (_he : ∀ j, 0 < e j)
    (_hvn : ∀ i z, v (f (C.negMap i z)) = vP (C.neg i) z ^ e (C.neg i))
    (_hvp : ∀ i z, v (f (C.posMap i z)) = vP (C.pos i) z ^ e (C.pos i))
    (y : D.Y) (ξ π : Eˣ) (d : ℕ) (_hd : 0 < d) (_hpow : (ξ : E) ^ d = π)
    (r : ℤ) (_hπ : v (π : E) = WithZero.exp (-r))
    (k : J → ℤ)
    (_hkn : ∀ i : Fin negative.length, D.datum.toLinearMap (D.datum.root negative[i]) y = k (C.neg i))
    (_hkp : ∀ i : Fin positive.length, D.datum.toLinearMap (D.datum.root positive[i]) y = k (C.pos i)),
    ∀ g : H, g ∈ markedScaledReduction M H f v y ξ ↔
      ∃! z : C.torus × (∀ j, P j),
        cellValue M (integralRing K) negative positive (C.coordinates z.1 z.2) = g.val ∧
        (∀ χ, v (f (z.1.val χ : K)) = 1) ∧
        ∀ j, vP j (z.2 j) ≤ WithZero.exp (-stepThreshold ((d : ℤ) * e j) (k j * r))

/-- Count the intersection in the field points, using the original marked
chart. The second subgroup may have nonintegral parameters. Here `b` is
its threshold on integral parameters, so negative thresholds are replaced by zero. -/
def MarkedFieldCongruenceIndex : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R K : IntegralAlgebra.{u}) (i : R ⟶ K) (_hi : Function.Injective i.hom)
    [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {j | ¬ D.base.IsPos j})
    (_hp : OrderedRootProducts.Enumerates positive {j | D.base.IsPos j})
    {J : Type u} [Fintype J] (P : J → Type u)
    [∀ j, CommRing (P j)] [∀ j, IsDomain (P j)] [∀ j, IsDiscreteValuationRing (P j)]
    [∀ j, Finite (IsLocalRing.ResidueField (P j))]
    (neg : Fin negative.length → J) (pos : Fin positive.length → J)
    (embedNeg : ∀ l, P (neg l) →+* R) (embedPos : ∀ l, P (pos l) →+* R)
    (_hOrbits : ∀ j, j ∈ Set.range neg ∪ Set.range pos)
    (e : J → ℕ) (_he : ∀ j, 0 < e j)
    (_hNeg : ∀ l, Ideal.map (embedNeg l) (IsLocalRing.maximalIdeal (P (neg l))) =
      (IsLocalRing.maximalIdeal R) ^ e (neg l))
    (_hPos : ∀ l, Ideal.map (embedPos l) (IsLocalRing.maximalIdeal (P (pos l))) =
      (IsLocalRing.maximalIdeal R) ^ e (pos l))
    (T : Set (TorusValues D R)) [Nonempty T],
    let chart (z : T × (∀ j, P j)) := cellValue M R negative positive
      (fun l => embedNeg l (z.2 (neg l)), z.1.val, fun l => embedPos l (z.2 (pos l)))
    let lift := changeRingHom M.group i
    ∀ (I I' : Subgroup (IntegralPoints M.group K)) (a b : J → ℕ) (q : ℕ)
      (_hq : 0 < q) (_hres : ∀ j, Nat.card (IsLocalRing.ResidueField (P j)) = q),
      (∃ t, chart (t, 0) = 1) →
      (∀ g, g ∈ I ↔ ∃ (t : T) (x : ∀ j, integralLayer (P j) (a j)),
        lift (chart (t, fun j => x j)) = g) →
      (∀ z, lift (chart z) ∈ I' ↔ ∀ j, z.2 j ∈ (IsLocalRing.maximalIdeal (P j)) ^ b j) →
      (∀ g, g ∈ I ⊓ I' ↔ ∃ (t : T) (x : ∀ j, integralLayer (P j) (max (a j) (b j))),
        lift (chart (t, fun j => x j)) = g) ∧
      ∃ n : ℕ, 0 < n ∧
        ((changeRingHom M.group (congruenceHom R n)).comp (I.comap lift).subtype).ker ≤
          ((I ⊓ I').comap lift).subgroupOf (I.comap lift) ∧
        (I ⊓ I').relIndex I = q ^ ∑ j, (max (a j) (b j) - a j)

/-- The factors of an ordered word, indexed by the positions in its root list. -/
def markedRootFactors {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (roots : List D.I) (x : Fin roots.length → R) :
    List (IntegralPoints M.group R) :=
  List.ofFn fun l : Fin roots.length => M.line.point R (x l) ≫ (M.root roots[l]).hom.hom

/-- Either sign can be placed first, including a consecutive block of paired
root factors. The positive-first coordinates are read in reverse order with
the parameter negated in each additive factor. -/
def MarkedWordFactors : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (negative positive : List D.I) (z : CellValues D R negative positive),
    let t := torusPoint D R z.2.1 ≫ M.torus.hom.hom
    cellValue M R negative positive z =
      (markedRootFactors M R negative z.1 ++ t :: markedRootFactors M R positive z.2.2).prod ∧
    (cellValue M R negative positive z)⁻¹ =
      ((markedRootFactors M R positive (-z.2.2)).reverse ++
        t⁻¹ :: (markedRootFactors M R negative (-z.1)).reverse).prod

/-- Covariance from the normalizer's finite Weyl action and translation.
The representative is the displayed torus point times an integral Weyl
representative. The character-value equation is the apartment action with
translation given by minus the additive valuation of each character. -/
def MarkedNormalizerCovariance : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K E : Type u} {Γ : Type*} [Field K] [Field E] [LinearOrderedCommGroupWithZero Γ]
    (H : Subgroup (IntegralPoints M.group (integralRing K)))
    (f : K →+* E) (v : Valuation E Γ) (x y : D.Y) (ξ : Eˣ) (n : H),
    let O := integralRing v.valuationSubring
    let k := residueRing O
    let i := changeRingHom M.group (integralRingMap v.valuationSubring.subtype)
    let red := changeRingHom M.group (residueHom O)
    let cx := cocharacter D x (integralRing E) ξ
    let cy := cocharacter D y (integralRing E) ξ
    let point (t : TorusValues D (integralRing E)) := torusPoint D (integralRing E) t ≫ M.torus.hom.hom
    ∀ (r : IntegralPoints M.group O) (t wx : TorusValues D (integralRing E)),
      red r ∈ Subgroup.normalizer (markedTorus M k : Set (IntegralPoints M.group k)) →
      changeRing (integralRingMap f) n.val = point t * i r →
      MulAut.conj (i r) (point cx) = point wx →
      (∀ χ, v (cy χ : E) * v (t χ : E) = v (wx χ : E)) →
      (markedScaledReduction M H f v x ξ).map (MulAut.conj n).toMonoidHom =
        markedScaledReduction M H f v y ξ

/-- The action on affine points obtained by applying a field automorphism on
values and the pinned action on the coordinate algebra is continuous in the
usual local point topology. -/
def AffineTwistContinuity : Prop :=
  ∀ (A : IntegralAlgebra.{u}) {X : IntegralScheme.{u}}
    (iso : integralSpec.obj (op A) ≅ X) (K : Type u) [Field K] [TopologicalSpace K]
    (σ : integralRing K ⟶ integralRing K) (_hσ : Continuous (σ.hom : K → K))
    (α : A ⟶ A),
    letI := markedPointTopology A iso K
    letI : Algebra Integers.{u} K := (integralRing K).algebra
    let e := pointAlgebraEquiv A iso (integralRing K)
    Continuous (fun p => e (σ.hom.comp ((e.symm p).comp α.hom)))

set_option maxHeartbeats 600000 in
/-- Borel reduction in the rational root chart. `a` records the standard
thresholds, zero on positive and one on negative roots, in the uniformizer
steps of the parameter field. -/
def RationalIwahoriChart : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K : Type u} [Field K] (H : Subgroup (IntegralPoints M.group (integralRing K)))
    (v : Valuation K ℤᵐ⁰) (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (_hp : OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}),
    let O := integralRing v.valuationSubring
    let k := residueRing O
    ∀ (B : Subgroup (IntegralPoints M.group k)),
      (B : Set _) = Set.range (fun z : TorusValues D k × (Fin positive.length → k) =>
        cellValue M k negative positive (0, z.1, z.2)) →
      ∀ {J : Type u} (P : J → Type u) [∀ j, Field (P j)]
        (C : RationalRootChart M H negative positive J P)
        (vP : ∀ j, Valuation (P j) ℤᵐ⁰) (e : J → ℤ), (∀ j, 0 < e j) →
        (∀ i z, v (C.negMap i z) = vP (C.neg i) z ^ e (C.neg i)) →
        (∀ i z, v (C.posMap i z) = vP (C.pos i) z ^ e (C.pos i)) →
        ∀ a : J → ℕ, (∀ i, a (C.neg i) = 1) → (∀ i, a (C.pos i) = 0) →
        ∀ g : H, g ∈ iwahoriSubgroup (integralRingMap v.valuationSubring.subtype) B H ↔
          ∃! z : C.torus × (∀ j, P j),
            cellValue M (integralRing K) negative positive (C.coordinates z.1 z.2) = g.val ∧
            (∀ χ, v (z.1.val χ : K) = 1) ∧
            ∀ j, vP j (z.2 j) ≤ WithZero.exp (-(a j : ℤ))

/-- The positive part of the marked chart is the point group of the Borel
in the identified pinned field fibre. The torus and root compatibilities
are supplied by `Model.fieldFibre`. -/
def MarkedFibreBorel : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D) (k : Type u) [Field k]
    (A : RootGroups.AdditiveLine k) (F : RationalRealization.Realization D A)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (z : ∀ a : D.I, Pinning.RootCoordinate A F.pinned.pair.T
      (F.pinned.roots (F.datumIso.val.indexEquiv a)).val (F.datumIso.val.indexEquiv a).val),
    (fibre k).map M.torus ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion →
    (∀ (a : D.I) (r : k),
      forgetFibrePoint M.group (CommAlgCat.of k k)
        (RootGroups.rootPoint ((z a).val.hom ≫
          (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion ≫ e.inv) (CommAlgCat.of k k) r) =
        M.line.point (integralRing k) r ≫ (M.root a).hom.hom) →
    ∀ (negative positive : List D.I),
      OrderedRootProducts.Enumerates positive {j | D.base.IsPos j} →
      ∃ B : Subgroup (IntegralPoints M.group (integralRing k)),
        (B : Set (IntegralPoints M.group (integralRing k))) =
          Set.range (fun b : AdjointRepresentation.GroupPoints F.pinned.pair.B.group (CommAlgCat.of k k) =>
            forgetFibrePoint M.group (CommAlgCat.of k k) (b ≫ (F.pinned.pair.B.inclusion ≫ e.inv).hom.hom)) ∧
        (B : Set (IntegralPoints M.group (integralRing k))) =
          Set.range (fun u : TorusValues D (integralRing k) × (Fin positive.length → k) =>
            cellValue M (integralRing k) negative positive (0, u.1, u.2))

set_option maxHeartbeats 600000 in
/-- The standard alcove subgroup from scaled torus reduction agrees with
the subgroup defined by positive Borel reduction. The inequalities describe
the interior of the standard alcove in each parameter field's step units. -/
def StandardAlcoveReduction : Prop :=
  ∀ {D : Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K E : Type u} [Field K] [Field E] (H : Subgroup (IntegralPoints M.group (integralRing K)))
    (f : K →+* E) (vK : Valuation K ℤᵐ⁰) (vE : Valuation E ℤᵐ⁰)
    (_hunit : ∀ z, vE (f z) = 1 ↔ vK z = 1)
    (negative positive : List D.I)
    (_hn : OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (_hp : OrderedRootProducts.Enumerates positive {i | D.base.IsPos i}),
    let k := residueRing (integralRing vK.valuationSubring)
    ∀ (B : Subgroup (IntegralPoints M.group k)),
      (B : Set _) = Set.range (fun z : TorusValues D k × (Fin positive.length → k) =>
        cellValue M k negative positive (0, z.1, z.2)) →
      ∀ {J : Type u} (P : J → Type u) [∀ j, Field (P j)]
        (C : RationalRootChart M H negative positive J P)
        (vP : ∀ j, Valuation (P j) ℤᵐ⁰) (eK eE : J → ℤ),
        (∀ j, 0 < eK j) → (∀ j, 0 < eE j) →
        (∀ i z, vK (C.negMap i z) = vP (C.neg i) z ^ eK (C.neg i)) →
        (∀ i z, vK (C.posMap i z) = vP (C.pos i) z ^ eK (C.pos i)) →
        (∀ i z, vE (f (C.negMap i z)) = vP (C.neg i) z ^ eE (C.neg i)) →
        (∀ i z, vE (f (C.posMap i z)) = vP (C.pos i) z ^ eE (C.pos i)) →
        ∀ (y : D.Y) (ξ π : Eˣ) (d : ℕ), 0 < d → (ξ : E) ^ d = π →
        ∀ (r : ℤ), vE (π : E) = WithZero.exp (-r) →
        ∀ (k : J → ℤ),
          (∀ i : Fin negative.length, D.datum.toLinearMap (D.datum.root negative[i]) y = k (C.neg i)) →
          (∀ i : Fin positive.length, D.datum.toLinearMap (D.datum.root positive[i]) y = k (C.pos i)) →
          (∀ i, -(d : ℤ) * eE (C.neg i) < k (C.neg i) * r ∧ k (C.neg i) * r < 0) →
          (∀ i, 0 < k (C.pos i) * r ∧ k (C.pos i) * r < (d : ℤ) * eE (C.pos i)) →
          markedScaledReduction M H f vE y ξ =
            iwahoriSubgroup (integralRingMap vK.valuationSubring.subtype) B H

/-- The integer-valued normalization of the supplied local valuation. -/
def normalizedLocalValuation (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Valuation K ℤᵐ⁰ :=
  (ValuativeRel.valuation K).map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)

def LocalValuationNormalization : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
    Function.Surjective (normalizedLocalValuation K) ∧
    (normalizedLocalValuation K).valuationSubring = (ValuativeRel.valuation K).valuationSubring ∧
    ∀ (E : Type u) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra K E] [ValuativeExtension K E],
      ∃ e : ℕ, 0 < e ∧ ∀ z : K,
        normalizedLocalValuation E (algebraMap K E z) = normalizedLocalValuation K z ^ e

/-- In an integral tuple, a negative depth threshold imposes no further
restriction. This is the conversion used before taking maximum thresholds. -/
def IntegralThresholdValuation : Prop :=
  ∀ {K : Type u} [Field K] (v : Valuation K ℤᵐ⁰)
    (π : v.valuationSubring), v (π : K) = WithZero.exp (-1 : ℤ) →
    ∀ (x : v.valuationSubring) (a : ℤ),
      v (x : K) ≤ WithZero.exp (-a) ↔ x ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ a.toNat

/-- Any test algebra over the lifted integers has the canonical algebra
structure. In particular the residue algebra agrees with the one used in
the marked field-fibre comparison. -/
def CanonicalIntegralAlgebra : Prop :=
  ∀ R : IntegralAlgebra.{u}, integralRing R = R

/-- An automorphism of the affine generic fibre acts continuously on points.
The coefficients may lie in the splitting field, as in a pinned twist. -/
def AffineFibreTwistContinuity : Prop :=
  ∀ {B A K : Type*} [CommRing B] [CommRing A] [CommRing K]
    [Algebra B A] [Algebra B K] [TopologicalSpace K] [IsTopologicalRing K]
    (σ : K →ₐ[B] K), Continuous σ → ∀ (α : A →ₐ[B] A ⊗[B] K),
      letI := affinePointTopology B A K
      Continuous (fun p : A →ₐ[B] K => σ.comp
        ((Algebra.TensorProduct.lift p (AlgHom.id B K) (fun _ _ => Commute.all _ _)).comp α))

/-- Scalar extension along an embedding of topological fields gives the
subspace topology on rational points inside the split affine points. -/
def AffineScalarPointEmbedding : Prop :=
  ∀ {B A K L : Type*} [CommRing B] [CommRing A] [CommRing K] [CommRing L]
    [Algebra B A] [Algebra B K] [Algebra B L] [TopologicalSpace K] [TopologicalSpace L]
    (f : K →ₐ[B] L), Topology.IsEmbedding f →
      letI := affinePointTopology B A K
      letI := affinePointTopology B A L
      Topology.IsEmbedding (fun p : A →ₐ[B] K => f.comp p)

/-- In the finite-dimensional vector space topology of a local extension,
the scalar embedding is a topological embedding and every field automorphism
over the base is continuous. -/
def LocalFieldExtensionTopology : Prop :=
  ∀ {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] [TopologicalSpace L] [IsTopologicalRing K]
    {J : Type*} [Fintype J] (b : Module.Basis J K L),
    Continuous b.equivFun → Continuous b.equivFun.symm →
      Topology.IsEmbedding (algebraMap K L) ∧ ∀ σ : L ≃ₐ[K] L, Continuous σ

/-- The valuation of the image of a base uniformizer gives the power of the
extension maximal ideal obtained by extending the base maximal ideal. -/
def RamificationIdealMap : Prop :=
  ∀ {K L : Type u} [Field K] [Field L] (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (πK : vK.valuationSubring) (πL : vL.valuationSubring),
    vK (πK : K) = WithZero.exp (-1 : ℤ) → vL (πL : L) = WithZero.exp (-1 : ℤ) →
    ∀ (f : vK.valuationSubring →+* vL.valuationSubring) (e : ℕ),
      vL (f πK : L) = WithZero.exp (-(e : ℤ)) →
      Ideal.map f (IsLocalRing.maximalIdeal vK.valuationSubring) =
        (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e

end

end LinearAlgebraicGroups.Specs.ExceptionalIwahoriCongruence
