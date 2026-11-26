import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeBruhat
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CentralIsogenies

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj WithZero

namespace LinearAlgebraicGroups.Specs.ExceptionalIwahoriImageComparison

noncomputable section

open ValuativeRel
open IntegralSemisimpleModel
open ExceptionalValuedTorusNormalizer (FibreNormalizer valuationRingInclusion)
open GeometricRadicals (IsReductive)

universe u

attribute [local instance] integerAlgebra

/-- The reduction condition pulled back along the integral point map. -/
def borelReduction {A G G₀ : Type*} [Group A] [Group G] [Group G₀]
    (inc : A →* G) (red : A →* G₀) (B : Subgroup G₀) : Subgroup G :=
  (B.comap red).map inc

/-- The homomorphism induced by a group scheme map on points. -/
abbrev pointHom {k : Type u} [Field k] {G H : GroupScheme k}
    (f : G ⟶ H) (Y : SchemeOver k) :
    (Y ⟶ G.X) →* (Y ⟶ H.X) :=
  IsMonHom.monoidHom f.hom.hom Y

/-- Reduction modulo the maximal ideal of the valuation ring. -/
abbrev residueReduction (K : Type u) [Field K] [ValuativeRel K] :
    CommAlgCat.of Integers.{u} (valuation K).valuationSubring ⟶
      CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField (valuation K).valuationSubring) :=
  CommAlgCat.ofHom
    ({ IsLocalRing.residue (valuation K).valuationSubring with
       commutes' := fun x ↦ map_intCast (IsLocalRing.residue (valuation K).valuationSubring) x.down } :
       (valuation K).valuationSubring →ₐ[Integers.{u}] _)

/-- A subgroup picked out by reduction, pulled back to any rational subgroup
of the split field points by its marked embedding. -/
def markedBorelReduction {K : Type u} [Field K] [ValuativeRel K]
    (G : IntegralGroup.{u})
    (B : Subgroup (IntegralPoints G (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring)))) :
    Subgroup (IntegralPoints G (CommAlgCat.of Integers.{u} K)) :=
  borelReduction ((integralPointFunctor G).map (valuationRingInclusion K)).hom
    ((integralPointFunctor G).map (residueReduction K)).hom B

/-- Rational sections of the positive Borel in a marked field fibre,
viewed as points of the integral model via scalar restriction. -/
def positiveBorelPointSet {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (E : FibreNormalizer M k) :
    Set (IntegralPoints M.group (CommAlgCat.of Integers.{u} k)) :=
  Set.range fun b : 𝟙_ (SchemeOver k) ⟶ E.realization.pinned.pair.B.group.X =>
    forgetFibrePoint M.group (CommAlgCat.of k k)
      (CartesianMonoidalCategory.toUnit _ ≫ b ≫
        E.realization.pinned.pair.B.inclusion.hom.hom ≫ E.fibreIso.inv.hom.hom)

/-- The marked Borel reduction cuts out the unit torus on the absolute
normalizer over the local field. -/
def SplitIwahoriIntersection : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : Pinning.BasedRootDatum.{u}} (M : Model D)
    (F : FibreNormalizer M K)
    (E : FibreNormalizer M (IsLocalRing.ResidueField (valuation K).valuationSubring))
    {index : Type u} [Fintype index] (_b : Module.Basis index ℤ D.Y),
    letI := F.torusComm
    ∃ B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring))),
      (B : Set _) = positiveBorelPointSet E ∧
      let I := markedBorelReduction M.group B
      ∃ (j : TorusValues D (CommAlgCat.of Integers.{u} K) ≃* F.label.ker)
        (ν : TorusValues D (CommAlgCat.of Integers.{u} K) →* Multiplicative D.Y),
      (∀ x, F.point (j x).val = torusPoint D (CommAlgCat.of Integers.{u} K) x ≫ M.torus.hom.hom) ∧
      (∀ x χ, D.datum.toLinearMap χ (ν x).toAdd =
        WithZero.log (ExceptionalValuedTorusNormalizer.normalizedValuation K
          (x (Multiplicative.ofAdd χ) : K))) ∧
      I.comap F.point = ν.ker.map (F.label.ker.subtype.comp j.toMonoidHom)

open ExceptionalValuedTorusNormalizer (fixedWeylGroup fieldCoefficientAction
  simplePermutation markedNormalizerPoint)
open AdjointBorelCohomology (PinnedTwist)

/-- The reduction intersection for the fixed normalizer, identified with the
rational normalizer by the specified F06 quadratic descent. The integral
torus on the right is the kernel of the retained finite label on integral
normalizer points. -/
def FoldedIwahoriIntersection : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [ValuativeRel K]
    [FiniteDimensional k K] [IsGalois k K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (F : FibreNormalizer M k)
    (E : FibreNormalizer M (IsLocalRing.ResidueField (valuation K).valuationSubring))
    {l : Aut F.realization.attached.toBased ≃* Aut F.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K F.realization.attached l B T)
    (σ : Gal(K/k)), Module.finrank k K = 2 → σ ≠ 1 →
    letI := F.torusComm
    let C := F.identification
    let s := (l (d.outer σ)).asIso.hom
    let R := CommAlgCat.of k K
    let Y := (testSpec k).obj (Opposite.op R)
    ∀ (e : Pinning.BasedIso D D),
      (∀ i : D.base.support, Pinning.transportCharacter s.torus (F.realization.simpleRoot i).val.val =
        (F.realization.simpleRoot (simplePermutation D e i)).val.val) →
      Function.Involutive e.val.indexEquiv →
      (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
      (∀ i : D.base.support, simplePermutation D e i ≠ i →
        D.datum.pairing (simplePermutation D e i).val i.val = 0) →
      ∀ (N : ClosedSubgroup G.val),
        (∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, Normalizes T.inclusion g ↔
          ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X, n ≫ N.inclusion.hom.hom = g) →
        ∃ (a : MulAut (Y ⟶ C.normalizer.group.X)),
          (∀ n, a n ≫ C.normalizer.inclusion.hom.hom =
            n ≫ C.normalizer.inclusion.hom.hom ≫ s.group.hom.hom.hom) ∧
          let H := MonoidHom.eqLocus a.toMonoidHom (fieldCoefficientAction σ C.normalizer.group)
          ∃ (uN : (𝟙_ (SchemeOver k) ⟶ N.group.X) ≃* H)
            (q : (Y ⟶ C.normalizer.group.X) →* D.datum.weylGroup)
            (q₀ : H →* fixedWeylGroup D e)
            (j : (𝟙_ (SchemeOver k) ⟶ N.group.X) →*
              IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
            (B₀ : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
              (IsLocalRing.ResidueField (valuation K).valuationSubring)))),
            (B₀ : Set _) = positiveBorelPointSet E ∧
            (∀ h, (q₀ h).val = q h.val) ∧
            (∀ n, j n = markedNormalizerPoint F R (uN n).val) ∧
            (∀ n, q₀ (uN n) = 1 ↔ ∃ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
              t ≫ T.inclusion.hom.hom = n ≫ N.inclusion.hom.hom) ∧
            (markedBorelReduction M.group B₀).comap j =
              (q₀.comp uN.toMonoidHom).ker ⊓
                (((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range).comap j

/-- The reduction test on an integral normalizer lift and on integral
torus points determines the full intersection. -/
def ReductionIntersection : Prop :=
  ∀ {A G G₀ N W : Type*} [Group A] [Group G] [Group G₀] [Group N] [Group W]
    (inc : A →* G) (red : A →* G₀) (B : Subgroup G₀)
    (n : N →* G) (q : N →* W),
    (∀ a x, inc a = n x → q x = 1 → red a ∈ B) →
    (∀ w, ∃ a x, inc a = n x ∧ q x = w ∧ (red a ∈ B ↔ w = 1)) →
    let marked := borelReduction inc red B
    marked.comap n = q.ker ⊓ inc.range.comap n

/-- A cocharacter evaluated at a uniformizer contracts a parameter to
every weak or strict layer, including the layer containing parameter zero.
The exponent is the root pairing times the ramification index of the
parameter field. -/
def UniformizerContraction : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (c : Kˣ) (d : ℤ),
    ExceptionalMarkedRootDescent.normalizedValuation K (c : K) = WithZero.exp (-d) →
    d ≠ 0 →
    ∀ (x : K) (j : ℤ), ∃ m : ℤ,
      ExceptionalMarkedRootDescent.normalizedValuation K ((↑(c ^ m) : K) * x) <
        WithZero.exp (-j)

/-- Conjugation by powers of the actual marked torus representative brings
a split root point to the Iwahori and any prescribed strict layer. The
cocharacter may be chosen in the coroot lattice. -/
def SplitRootContraction : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (F : FibreNormalizer M K)
    (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring)))),
    letI := F.torusComm
    let R := CommAlgCat.of Integers.{u} K
    let v := ExceptionalMarkedRootDescent.normalizedValuation K
    let I := markedBorelReduction M.group B
    ∀ (a : D.I) (y : D.Y) (π : Kˣ),
      let h := D.datum.toLinearMap (D.datum.root a) y
      h ≠ 0 →
      v (π : K) = WithZero.exp (-1) →
      ∃ n : 𝟙_ (SchemeOver K) ⟶ F.identification.normalizer.group.X,
        F.label n = 1 ∧ F.point n = torusPoint D R (cocharacter D y R π) ≫ M.torus.hom.hom ∧
        ∀ (u : K) (j : ℤ), ∃ m : ℤ,
          v ((↑((π ^ h) ^ m) : K) * u) < WithZero.exp (-j) ∧
          F.point (n ^ m) *
            ExceptionalMarkedRootDescent.markedRootPoint M.toIntegralMarking R a u *
            (F.point (n ^ m))⁻¹ ∈ I

/-- A regular cocharacter contracts an entire ordered root word with
positive pairings. A base-field uniformizer in the splitting field can
have any strictly positive depth, in particular depth two. -/
def MarkedRootWordContraction : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D)
    (B₀ : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring))))
    (y : D.Y) (π : Kˣ) (e : ℤ), 0 < e →
    ExceptionalMarkedRootDescent.normalizedValuation K (π : K) = WithZero.exp (-e) →
    let R := CommAlgCat.of Integers.{u} K
    let v := ExceptionalMarkedRootDescent.normalizedValuation K
    let c := cocharacter D y R π
    let n : IntegralPoints M.group R := torusPoint D R c ≫ M.torus.hom.hom
    ∀ (l : List D.I), (∀ a ∈ l, 0 < D.datum.toLinearMap (D.datum.root a) y) →
    ∀ (x : D.I → K) (j : ℤ), ∃ m : ℕ,
      (∀ a ∈ l, v ((↑((c ^ m) (Multiplicative.ofAdd (D.datum.root a))) : K) * x a) <
        WithZero.exp (-j)) ∧
      n ^ m * ExceptionalMarkedRootDescent.orderedRootPoint M R l x * (n ^ m)⁻¹ ∈
        markedBorelReduction M.group B₀

/-- Rational double-coset coverage for the actual minimal parabolic and
rational relative normalizer of the selected pair. -/
def RationalBorelFactorization : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (_hG : IsReductive G) (S B : ClosedSubgroup G.val),
    Relative.MaximalSplitTori.IsMaximalSplitTorus S →
    Relative.MaximalSplitTori.IsMinimalParabolic G B →
    SchemeDerivedGroup.IsSubgroupOf S B →
    ∀ (N : ClosedSubgroup G.val),
      RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g) →
      ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        ∃ (b c : 𝟙_ (SchemeOver k) ⟶ B.group.X)
          (n : 𝟙_ (SchemeOver k) ⟶ N.group.X),
          g = (b ≫ B.inclusion.hom.hom) *
            (n ≫ N.inclusion.hom.hom) * (c ≫ B.inclusion.hom.hom)

/-- Positive Borel sections over any test algebra, via the marked field
comparison of the integral model. -/
def markedPositiveBorel {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (C : ExceptionalMarkedRootDescent.MarkedFibre M k) (R : TestAlgebra k) :
    Set (IntegralPoints M.group (CommAlgCat.of Integers.{u} R)) :=
  Set.range fun b : AdjointRepresentation.GroupPoints C.realization.pinned.pair.B.group R =>
    forgetFibrePoint M.group R
      (b ≫ C.realization.pinned.pair.B.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom)

/-- In the marked field fibre the Borel consists of a torus point followed
by an arbitrarily ordered product of marked positive root coordinates. -/
def MarkedPositiveBorelCoordinates : Prop :=
  ∀ {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : ExceptionalMarkedRootDescent.MarkedFibre M k) (R : TestAlgebra k)
    (l : List D.I), OrderedRootProducts.Enumerates l {a | D.base.IsPos a} →
    let S := CommAlgCat.of Integers.{u} R
    markedPositiveBorel C R =
      Set.range (fun q : IntegralPoints (splitTorus D) S × (D.I → S) =>
        (q.1 ≫ M.torus.hom.hom) *
          ExceptionalMarkedRootDescent.orderedRootPoint M.toIntegralMarking S l q.2)

/-- The Iwahori chart over the splitting field, on the specified integral
model. The variables in the valuation ring have nonnegative depth. The
negative root variables are in its maximal ideal, and all torus coordinates
are units. This criterion can be pulled back by the pinned rational embedding. -/
def IwahoriDepthCoordinates : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D},
    let O := (valuation K).valuationSubring
    let κ := IsLocalRing.ResidueField O
    ∀ (C : ExceptionalMarkedRootDescent.MarkedFibre M κ)
      (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ))),
      (B : Set _) = markedPositiveBorel C (CommAlgCat.of κ κ) →
      ∀ (l r : List D.I),
        OrderedRootProducts.Enumerates l {a | ¬ D.base.IsPos a} →
        OrderedRootProducts.Enumerates r {a | D.base.IsPos a} →
        ∀ g : IntegralPoints M.group (CommAlgCat.of Integers.{u} K),
          g ∈ markedBorelReduction M.group B ↔
            ∃ (z : D.I → O) (t : TorusValues D (CommAlgCat.of Integers.{u} O)),
              (∀ a ∈ l, valuation K (z a : K) < 1) ∧
              (integralPointFunctor M.group).map (valuationRingInclusion K)
                (ExceptionalMarkedRootDescent.markedCellPoint M.toIntegralMarking
                  (CommAlgCat.of Integers.{u} O) l r z
                  (torusPoint D (CommAlgCat.of Integers.{u} O) t)) = g

/-- Either triangular chart has unique coordinates. Its integral points
with negative parameters in the maximal ideal give the Iwahori. -/
def IwahoriOrderedCoordinates : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D},
    let O := (valuation K).valuationSubring
    let κ := IsLocalRing.ResidueField O
    ∀ (C : ExceptionalMarkedRootDescent.MarkedFibre M κ)
      (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ))),
      (B : Set _) = markedPositiveBorel C (CommAlgCat.of κ κ) →
      ∀ (l r : List D.I),
        OrderedRootProducts.Enumerates l {a | ¬ D.base.IsPos a} →
        OrderedRootProducts.Enumerates r {a | D.base.IsPos a} →
        ∀ (positiveFirst : Bool),
          let chart := ExceptionalMarkedRootDescent.markedAbsoluteCell M.toIntegralMarking
            (CommAlgCat.of Integers.{u} O) l r positiveFirst
          Function.Injective chart ∧
          ∀ g : IntegralPoints M.group (CommAlgCat.of Integers.{u} K),
            g ∈ markedBorelReduction M.group B ↔
              ∃ (z : D.I → O) (t : TorusValues D (CommAlgCat.of Integers.{u} O)),
                (∀ a ∈ l, valuation K (z a : K) < 1) ∧
                (integralPointFunctor M.group).map (valuationRingInclusion K)
                  (chart (z, torusPoint D (CommAlgCat.of Integers.{u} O) t)) = g

/-- A rational section viewed as a point of the chosen integral model. -/
def markedGroundPoint {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}}
    {M : Model D} (C : ExceptionalMarkedRootDescent.MarkedFibre M k)
    (g : 𝟙_ (SchemeOver k) ⟶ C.realization.pinned.pair.G.val.X) :
    IntegralPoints M.group (CommAlgCat.of Integers.{u} k) :=
  ExceptionalMarkedRootDescent.markedFibrePoint C (CommAlgCat.of k k)
    (CartesianMonoidalCategory.toUnit _ ≫ g)

/-- The marked positive Borel point set is a subgroup, including over the
residue field used to define the Iwahori. -/
def MarkedPositiveBorelSubgroup : Prop :=
  ∀ {k : Type u} [Field k] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : ExceptionalMarkedRootDescent.MarkedFibre M k),
    ∃ B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} k)),
      (B : Set _) = markedPositiveBorel C (CommAlgCat.of k k)

/-- Rational Bruhat for the split marked pair, followed by contraction of
the root factors by their marked coroots. -/
def SplitIwahoriGeneration : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : ExceptionalMarkedRootDescent.MarkedFibre M K)
    (B₀ : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring)))),
    let P := C.realization.pinned.pair
    let I := markedBorelReduction M.group B₀
    ∃ N : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} K)),
      (∀ g, markedGroundPoint C g ∈ N ↔ Normalizes P.T.inclusion g) ∧
      I ⊔ N = ⊤

section PinnedRationalPoints

open ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint pinnedMarkedPoint
  evaluateGroundTensor coordinatePointEquiv)
open AdjointRepresentation (GroupPoints)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : Pinning.BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
  (d : PinnedTwist K C.realization.attached l B T)

/-- The F06 comparison on sections, evaluated in the integral model
over the splitting field. -/
def pinnedGroundPoint (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    IntegralPoints M.group (CommAlgCat.of Integers.{u} K) :=
  (integralPointFunctor M.group).map (evaluateGroundTensor k K)
    (pinnedMarkedPoint C d (CommAlgCat.of k k)
      ((coordinatePointEquiv G (CommAlgCat.of k k)).symm
        (CartesianMonoidalCategory.toUnit _ ≫ g)))

end PinnedRationalPoints

section PinnedRationalComparison

/-- The quadratic rational embedding compares the two Borels and tori,
and its image satisfies the coefficient and diagram fixed-point equation. -/
def PinnedGroundPointComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : ExceptionalMarkedRootDescent.MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T) (σ : Gal(K/k)),
    Module.finrank k K = 2 → σ ≠ 1 →
    let R := CommAlgCat.of k K
    let P := C.realization.pinned.pair
    ∃ j : (𝟙_ (SchemeOver k) ⟶ G.val.X) →*
        IntegralPoints M.group (CommAlgCat.of Integers.{u} K),
      Function.Injective j ∧ (∀ g, j g = pinnedGroundPoint C d g) ∧
      (∀ b : 𝟙_ (SchemeOver k) ⟶ B.group.X,
        j (b ≫ B.inclusion.hom.hom) ∈ markedPositiveBorel C R) ∧
      (∀ (t : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} K))
        (g : 𝟙_ (SchemeOver k) ⟶ G.val.X),
        j g = t ≫ M.torus.hom.hom → SchemeDerivedGroup.FactorsThrough T g) ∧
      ∀ v : AdjointRepresentation.GroupPoints P.G.val R,
        ExceptionalMarkedRootDescent.markedFibrePoint C R v ∈ j.range ↔
          (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ v ≫
            (l (d.outer σ)).asIso.hom.group.hom.hom.hom = v

end PinnedRationalComparison

open ExceptionalMarkedRootDescent (TransportedOrbit SimpleRootOrbit transportedLabels pinnedDiagram)

/-- Contraction and rational Bruhat generate the group of the quadratic
pinned descent from its Iwahori and the actual relative normalizer. -/
def FoldedIwahoriGeneration : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : ExceptionalMarkedRootDescent.MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G},
    AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q →
    ∀ {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
      (d : PinnedPairDescent.DescendedPair (l := l) K ω)
      (σ : Gal(K/k)), Module.finrank k K = 2 → σ ≠ 1 →
    (∀ x : k, ExceptionalMarkedRootDescent.normalizedValuation K (algebraMap k K x) =
      (ExceptionalMarkedRootDescent.normalizedValuation k x) ^ 2) →
    (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
    ∀ (b : Module.Basis D.base.support ℤ D.Y),
      ((∃ h, b = ExceptionalValuedTorusNormalizer.simpleCorootBasis D h) ∨
        (∃ h, b = ExceptionalValuedTorusNormalizer.fundamentalCoweightBasis D h)) →
    ∀ (ns ps : List (TransportedOrbit D)),
      (∀ a ∈ ns ++ ps, a.1.Matches C (pinnedDiagram d.data σ) ∧
        ∀ o ∈ a.2, o.Matches C (pinnedDiagram d.data σ)) →
      OrderedRootProducts.Enumerates (ns.flatMap transportedLabels) {a | ¬ D.base.IsPos a} →
      OrderedRootProducts.Enumerates (ps.flatMap transportedLabels) {a | D.base.IsPos a} →
    ∀ (B₀ : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u}
      (IsLocalRing.ResidueField (valuation K).valuationSubring)))),
      ∃ (j : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →*
          IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
        (S : ClosedSubgroup d.group.val) (N : Relative.RelativeWeylScheme.QuotientData S),
      (∀ g, j g = pinnedGroundPoint C d.data g) ∧
      Function.Injective j ∧ Relative.MaximalSplitTori.IsMaximalSplitTorus S ∧
      (∀ g : 𝟙_ (SchemeOver k) ⟶ d.group.val.X,
        Normalizes S.inclusion g ↔ Normalizes d.torus.inclusion g) ∧
      (markedBorelReduction M.group B₀).comap j ⊔ SubgroupSections N.normalizer (𝟙_ (SchemeOver k)) = ⊤

/-- The integral group map and its point homomorphisms over each test ring. -/
abbrev integralPointHom {G H : IntegralGroup.{u}} (f : G ⟶ H) (R : IntegralAlgebra.{u}) :
    IntegralPoints G R →* IntegralPoints H R :=
  IsMonHom.monoidHom f.hom.hom (integralSpec.obj (Opposite.op R))

/-- The unit torus of the marked model inside the full splitting-field points. -/
def integralUnitTorus {K : Type u} [Field K] [ValuativeRel K]
    {D : Pinning.BasedRootDatum.{u}} (M : Model D) :
    Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} K)) :=
  ((integralPointHom M.torus (CommAlgCat.of Integers.{u} K)).comp
    ((integralPointFunctor (splitTorus D)).map (valuationRingInclusion K)).hom).range

/-- Compatibility of the ordered integral charts for a map between marked
models, with the root slots identified by the root bijection. -/
def PreservesIntegralMarking {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X) : Prop :=
  (∀ a, D.base.IsPos a ↔ E.base.IsPos (e a)) ∧
  (∀ (R : IntegralAlgebra.{u}) (a : D.I) (x : R),
    integralPointHom f R (ExceptionalMarkedRootDescent.markedRootPoint M.toIntegralMarking R a x) =
      ExceptionalMarkedRootDescent.markedRootPoint A.toIntegralMarking R (e a) x) ∧
  ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R),
    integralPointHom f R (torusPoint D R t ≫ M.torus.hom.hom) =
      torusPoint E R (t.comp χ) ≫ A.torus.hom.hom

/-- The same comparison identifies the actual rank-one maps over local
test rings and the integral Weyl words on every test ring. -/
def MarkedRankOneMapCompatibility : Prop :=
  ∀ {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X),
    PreservesIntegralMarking f e χ →
    (∀ a, e (D.datum.reflectionPerm a a) = E.datum.reflectionPerm (e a) (e a)) →
    (∀ (R : IntegralAlgebra.{u}) [IsLocalRing R] (a : D.I)
      (g : Matrix.SpecialLinearGroup (Fin 2) R),
      integralPointHom f R ((M.rankOne a).app R g) = (A.rankOne (e a)).app R g) ∧
    ∀ (R : IntegralAlgebra.{u}) (l : List D.I),
      integralPointHom f R (ExceptionalMarkedRootDescent.markedWeylWord M.toIntegralMarking R l) =
        ExceptionalMarkedRootDescent.markedWeylWord A.toIntegralMarking R (l.map e)

open ExceptionalMarkedRootDescent (rationalOrderedParameters splitOrderedOrbitPoint rationalOrderedCoordinates)

/-- A central map preserving the integral marking intertwines the root words
in the two rational quadratic charts when the simple orbit labels and their
transporting Weyl words correspond under the root bijection. -/
def FoldedRootWordCompatibility : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X),
    PreservesIntegralMarking f e χ →
    (∀ a x, e (D.datum.reflectionPerm a x) = E.datum.reflectionPerm (e a) (e x)) →
    ∀ (σ : Gal(K/k)) (l : List (TransportedOrbit D)) (l' : List (TransportedOrbit E)),
      l.Forall₂ (fun b b' => b.1.roots.map e = b'.1.roots ∧
        (b.2.flatMap SimpleRootOrbit.roots).map e = b'.2.flatMap SimpleRootOrbit.roots) l' →
      (l.flatMap transportedLabels).map e = l'.flatMap transportedLabels ∧
      ∃ j : rationalOrderedParameters k K l ≃ rationalOrderedParameters k K l',
        ∀ x, integralPointHom f (CommAlgCat.of Integers.{u} K)
          (splitOrderedOrbitPoint M.toIntegralMarking (CommAlgCat.of Integers.{u} K) l
            (rationalOrderedCoordinates σ l x)) =
          splitOrderedOrbitPoint A.toIntegralMarking (CommAlgCat.of Integers.{u} K) l'
            (rationalOrderedCoordinates σ l' (j x))

/-- On the split integral models, the adjoint Iwahori is generated by the
image of the source Iwahori and the unit torus. The comparison works at all
residue characteristics, without a lift of the adjoint torus point. -/
def SplitIwahoriImage : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K]
    {D E : Pinning.BasedRootDatum.{u}} (M : Model D) (A : Model E)
    (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X),
    PreservesIntegralMarking f e χ →
    let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
    ∀ (C : ExceptionalMarkedRootDescent.MarkedFibre M κ)
      (C' : ExceptionalMarkedRootDescent.MarkedFibre A κ)
      (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ)))
      (B' : Subgroup (IntegralPoints A.group (CommAlgCat.of Integers.{u} κ))),
      (B : Set _) = markedPositiveBorel C (CommAlgCat.of κ κ) →
      (B' : Set _) = markedPositiveBorel C' (CommAlgCat.of κ κ) →
      let p := integralPointHom f (CommAlgCat.of Integers.{u} K)
      markedBorelReduction A.group B' =
        (markedBorelReduction M.group B).map p ⊔ integralUnitTorus (K := K) A

/-- A finite-index torus map reflects the Iwahori condition, given the
scheme-theoretic torus preimage and the marked root comparison. -/
def SplitIwahoriPreimage : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : Pinning.BasedRootDatum.{u}} (M : Model D) (A : Model E)
    (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X),
    PreservesIntegralMarking f e χ → Finite ((Multiplicative D.X) ⧸ χ.range) →
    let R := CommAlgCat.of Integers.{u} K
    let p := integralPointHom f R
    (∀ g : IntegralPoints M.group R,
      (∃ t : TorusValues E R, p g = torusPoint E R t ≫ A.torus.hom.hom) →
      ∃ t : TorusValues D R, g = torusPoint D R t ≫ M.torus.hom.hom) →
    let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
    ∀ (C : ExceptionalMarkedRootDescent.MarkedFibre M κ)
      (C' : ExceptionalMarkedRootDescent.MarkedFibre A κ)
      (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ)))
      (B' : Subgroup (IntegralPoints A.group (CommAlgCat.of Integers.{u} κ))),
      (B : Set _) = markedPositiveBorel C (CommAlgCat.of κ κ) →
      (B' : Set _) = markedPositiveBorel C' (CommAlgCat.of κ κ) →
      (markedBorelReduction A.group B').comap p = markedBorelReduction M.group B

/-- A compatible map of the two pinned descents compares their Iwahoris
inside the actual rational point groups. The missing torus lifts are accounted
for by the unit points of the descended adjoint torus. -/
def FoldedIwahoriImageAndPreimage : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : Pinning.BasedRootDatum.{u}} (M : Model D) (A : Model E)
    (f : M.group ⟶ A.group) (e : D.I ≃ E.I)
    (χ : Multiplicative E.X →* Multiplicative D.X),
    PreservesIntegralMarking f e χ → Finite (Multiplicative D.X ⧸ χ.range) →
    (∀ a x, e (D.datum.reflectionPerm a x) = E.datum.reflectionPerm (e a) (e x)) →
    let R := CommAlgCat.of Integers.{u} K
    let fK := integralPointHom f R
    (∀ g : IntegralPoints M.group R,
      (∃ t : TorusValues E R, fK g = torusPoint E R t ≫ A.torus.hom.hom) →
      ∃ t : TorusValues D R, g = torusPoint D R t ≫ M.torus.hom.hom) →
    ∀ (C : ExceptionalMarkedRootDescent.MarkedFibre M k)
      (C' : ExceptionalMarkedRootDescent.MarkedFibre A k)
      {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
      {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
      {G G' : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val} {B' T' : ClosedSubgroup G'.val}
      (d : PinnedTwist K C.realization.attached l B T)
      (d' : PinnedTwist K C'.realization.attached l' B' T')
      (p : G.val ⟶ G'.val),
    let p₀ := pointHom p (𝟙_ (SchemeOver k))
    (∀ g, pinnedGroundPoint C' d' (p₀ g) = fK (pinnedGroundPoint C d g)) →
    Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    (∀ i j, E.datum.pairing i j = E.datum.pairing j i) →
    ∀ (ns ps : List (TransportedOrbit D)) (ns' ps' : List (TransportedOrbit E)),
      (∀ b ∈ ns ++ ps, b.1.Matches C (pinnedDiagram d σ) ∧
        ∀ o ∈ b.2, o.Matches C (pinnedDiagram d σ)) →
      (∀ b ∈ ns' ++ ps', b.1.Matches C' (pinnedDiagram d' σ) ∧
        ∀ o ∈ b.2, o.Matches C' (pinnedDiagram d' σ)) →
      ns.Forall₂ (fun b b' => b.1.roots.map e = b'.1.roots ∧
        (b.2.flatMap SimpleRootOrbit.roots).map e = b'.2.flatMap SimpleRootOrbit.roots) ns' →
      ps.Forall₂ (fun b b' => b.1.roots.map e = b'.1.roots ∧
        (b.2.flatMap SimpleRootOrbit.roots).map e = b'.2.flatMap SimpleRootOrbit.roots) ps' →
      OrderedRootProducts.Enumerates (ns'.flatMap transportedLabels) {a | ¬ E.base.IsPos a} →
      OrderedRootProducts.Enumerates (ps'.flatMap transportedLabels) {a | E.base.IsPos a} →
    let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
    ∀ (C₀ : ExceptionalMarkedRootDescent.MarkedFibre M κ)
      (C₀' : ExceptionalMarkedRootDescent.MarkedFibre A κ)
      (B₀ : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ)))
      (B₀' : Subgroup (IntegralPoints A.group (CommAlgCat.of Integers.{u} κ))),
      (B₀ : Set _) = markedPositiveBorel C₀ (CommAlgCat.of κ κ) →
      (B₀' : Set _) = markedPositiveBorel C₀' (CommAlgCat.of κ κ) →
    ∃ (j : (𝟙_ (SchemeOver k) ⟶ G.val.X) →* IntegralPoints M.group R)
      (j' : (𝟙_ (SchemeOver k) ⟶ G'.val.X) →* IntegralPoints A.group R),
      Function.Injective j ∧ Function.Injective j' ∧
      (∀ g, j g = pinnedGroundPoint C d g) ∧ (∀ g, j' g = pinnedGroundPoint C' d' g) ∧
      let I := (markedBorelReduction M.group B₀).comap j
      let I' := (markedBorelReduction A.group B₀').comap j'
      let U' := (integralUnitTorus (K := K) A).comap j'
      I'.comap p₀ = I ∧ I' = I.map p₀ ⊔ U' ∧
      ∀ x ∈ U', SchemeDerivedGroup.FactorsThrough T' x

/-- The cocharacter pushforward agrees with the translation on the
marked torus. Scaling both sides by one half gives the same comparison
for the apartment with base-field valuation normalization. -/
def MarkedTranslationCompatibility : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (D E : Pinning.BasedRootDatum.{u})
    (χ : E.X →ₗ[ℤ] D.X) (f : D.Y →ₗ[ℤ] E.Y),
    (∀ x y, D.datum.toLinearMap (χ x) y = E.datum.toLinearMap x (f y)) →
    let R := CommAlgCat.of Integers.{u} K
    let v := ExceptionalMarkedRootDescent.normalizedValuation K
    ∀ (t : TorusValues D R) (a : D.Y) (b : E.Y),
      (∀ x, D.datum.toLinearMap x a = WithZero.log (v (t (Multiplicative.ofAdd x) : K))) →
      (∀ x, E.datum.toLinearMap x b =
        WithZero.log (v ((t.comp χ.toAddMonoidHom.toMultiplicative) (Multiplicative.ofAdd x) : K))) →
      f a = b ∧ ∀ q : ℚ,
        TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) f (TensorProduct.tmul ℤ q a) =
          TensorProduct.tmul ℤ q b

/-- The two actual integral markings and the map on their field fibres
induced by a compatible simply connected cover. -/
structure MarkedCentralCover {D E : Pinning.BasedRootDatum.{u}} (M : Model D) (A : Model E) where
  map : M.group ⟶ A.group
  torusMap : splitTorus D ⟶ splitTorus E
  rootEquiv : D.I ≃ E.I
  pullCharacter : E.X →ₗ[ℤ] D.X
  pushCocharacter : D.Y →ₗ[ℤ] E.Y
  characterInjective : Function.Injective pullCharacter
  characterIndex : Finite (Multiplicative D.X ⧸
    pullCharacter.toAddMonoidHom.toMultiplicative.range)
  roots : ∀ a, pullCharacter (E.datum.root (rootEquiv a)) = D.datum.root a
  coroots : ∀ a, pushCocharacter (D.datum.coroot a) = E.datum.coroot (rootEquiv a)
  reflections : ∀ a b, rootEquiv (D.datum.reflectionPerm a b) =
    E.datum.reflectionPerm (rootEquiv a) (rootEquiv b)
  pairing : ∀ x y, D.datum.toLinearMap (pullCharacter x) y =
    E.datum.toLinearMap x (pushCocharacter y)
  marking : PreservesIntegralMarking map rootEquiv pullCharacter.toAddMonoidHom.toMultiplicative
  torusComm : M.torus ≫ map = torusMap ≫ A.torus
  fibre : ∀ (k : Type u) [Field k]
    (C : ExceptionalMarkedRootDescent.MarkedFibre M k)
    (C' : ExceptionalMarkedRootDescent.MarkedFibre A k),
    let f := C.groupIso.inv ≫ (fibre k).map map ≫ C'.groupIso.hom
    let fT := C.torusIso.inv ≫ (fibre k).map torusMap ≫ C'.torusIso.hom
    CentralIsogenies.IsCentralIsogeny f ∧ CentralIsogenies.IsTorusRestriction f fT ∧
      ∃ Z : ClosedSubgroup C.realization.pinned.pair.G.val,
        IsSchemeKernel f Z ∧ SchemeDerivedGroup.IsSubgroupOf Z C.realization.pinned.pair.T ∧
          Centralizes (𝟙 C.realization.pinned.pair.G.val) Z.inclusion.hom.hom

/-- The two lattice forms can be realized together using the integral
central quotient with unchanged marked root parameters. -/
def MarkedCentralCoverExists : Prop :=
  ∀ (E : Pinning.BasedRootDatum.{u}), E.datum.rootSpan ℤ = ⊤ →
    ∃ (D : Pinning.BasedRootDatum.{u}) (M : Model D) (A : Model E),
      D.datum.corootSpan ℤ = ⊤ ∧ Nonempty (MarkedCentralCover M A)

/-- The two integral lattices give the same finite Weyl labels. This
identification restricts to the fixed labels of compatible diagrams. -/
def CentralCoverWeylComparison : Prop :=
  ∀ {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A), E.datum.rootSpan ℤ = ⊤ →
    ∃ j : D.datum.weylGroup ≃* E.datum.weylGroup,
      (∀ i, j (RootPairing.weylGroup.ofIdx D.datum i) =
        RootPairing.weylGroup.ofIdx E.datum (c.rootEquiv i)) ∧
      (∀ w x, w.val.weightEquiv (c.pullCharacter x) =
        c.pullCharacter ((j w).val.weightEquiv x)) ∧
      ∀ (d : Pinning.BasedIso D D) (e : Pinning.BasedIso E E),
        (∀ i, c.rootEquiv (d.val.indexEquiv i) = e.val.indexEquiv (c.rootEquiv i)) →
        ∃ i : fixedWeylGroup D d ≃* fixedWeylGroup E e, ∀ w, (i w).val = j w.val

/-- The Iwahori image and preimage for the central cover of the actual split models. -/
def SplitIwahoriCoverComparison : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E} (c : MarkedCentralCover M A)
    (C : ExceptionalMarkedRootDescent.MarkedFibre M K) (C' : ExceptionalMarkedRootDescent.MarkedFibre A K),
    let R := CommAlgCat.of Integers.{u} K
    let p := integralPointHom c.map R
    let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
    ∀ (C₀ : ExceptionalMarkedRootDescent.MarkedFibre M κ) (C₀' : ExceptionalMarkedRootDescent.MarkedFibre A κ)
      (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ)))
      (B' : Subgroup (IntegralPoints A.group (CommAlgCat.of Integers.{u} κ))),
      (B : Set _) = markedPositiveBorel C₀ (CommAlgCat.of κ κ) →
      (B' : Set _) = markedPositiveBorel C₀' (CommAlgCat.of κ κ) →
      let I := markedBorelReduction M.group B
      let I' := markedBorelReduction A.group B'
      I' = I.map p ⊔ integralUnitTorus (K := K) A ∧ I'.comap p = I

/-- Matching diagram actions on the two actual pinned models descend the
marked central isogeny, including its torus restriction and its scheme kernel. -/
def PinnedCentralCoverComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A),
    E.datum.rootSpan ℤ = ⊤ →
    ∀ (C : ExceptionalMarkedRootDescent.MarkedFibre M k)
      (C' : ExceptionalMarkedRootDescent.MarkedFibre A k)
      {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
      {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
      {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G}
      {Q' : AutomorphismSequence.AdjointQuotient C'.realization.pinned.pair.G},
    AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q →
    AutomorphismSequence.SplitSequence C'.realization.pinned C'.realization.attached l' Q' →
    ∀ {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
      {ω' : Gal(K/k) →* Aut C'.realization.attached.toBased}
      (d : PinnedPairDescent.DescendedPair (l := l) K ω)
      (d' : PinnedPairDescent.DescendedPair (l := l') K ω'),
      Module.finrank k K = 2 → ∀ (σ : Gal(K/k)), σ ≠ 1 →
    (∀ a,
      let e := ExceptionalValuedTorusNormalizer.markedDiagramEquiv C.realization (d.data.outer σ)
      let e' := ExceptionalValuedTorusNormalizer.markedDiagramEquiv C'.realization (d'.data.outer σ)
      c.rootEquiv (e.asIso.hom.val.indexEquiv a) = e'.asIso.hom.val.indexEquiv (c.rootEquiv a)) →
    let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
    ∃ (p : d.group.val ⟶ d'.group.val) (pT : d.torus.group ⟶ d'.torus.group)
      (pB : d.borel.group ⟶ d'.borel.group),
      CentralIsogenies.IsCentralIsogeny p ∧ CentralIsogenies.IsTorusRestriction p pT ∧
      d.borel.inclusion ≫ p = pB ≫ d'.borel.inclusion ∧
      (∃ Z : ClosedSubgroup d.group.val, IsSchemeKernel p Z ∧
        SchemeDerivedGroup.IsSubgroupOf Z d.torus ∧ Centralizes (𝟙 d.group.val) Z.inclusion.hom.hom) ∧
      (∀ g : 𝟙_ (SchemeOver k) ⟶ d.group.val.X,
        SchemeDerivedGroup.FactorsThrough d'.torus (pointHom p (𝟙_ (SchemeOver k)) g) ↔
          SchemeDerivedGroup.FactorsThrough d.torus g) ∧
      (∀ g : 𝟙_ (SchemeOver k) ⟶ d.group.val.X,
        Normalizes d'.torus.inclusion (pointHom p (𝟙_ (SchemeOver k)) g) ↔
          Normalizes d.torus.inclusion g) ∧
      (pointHom p (𝟙_ (SchemeOver k))).range.Normal ∧
      d'.data.groupIso.hom ≫ extendedHopfMap K
        (AdjointCocharacters.coordinateHopfMap (G := d.group) (H := d'.group) p) =
        extendedHopfMap K (AdjointCocharacters.coordinateHopfMap
          (G := C.realization.pinned.pair.G) (H := C'.realization.pinned.pair.G) f) ≫
          d.data.groupIso.hom ∧
      ∀ g : 𝟙_ (SchemeOver k) ⟶ d.group.val.X,
        pinnedGroundPoint C' d'.data (pointHom p (𝟙_ (SchemeOver k)) g) =
          integralPointHom c.map (CommAlgCat.of Integers.{u} K) (pinnedGroundPoint C d.data g)

/-- Data on the actual field normalizer, or its pinned rational form.
The logs use the normalized valuation of the splitting field. For the
ramified quadratic form the vectors in the apartment are half these logs. -/
structure MarkedLocalNormalizer (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    {G : Type u} [Group G] (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (W : Type u) [Group W] where
  torus : Subgroup G
  normalizer : Subgroup G
  torus_le : torus ≤ normalizer
  torusPoints : ∀ g, g ∈ torus ↔ ∃ t : TorusValues D (CommAlgCat.of Integers.{u} K),
    j g = torusPoint D (CommAlgCat.of Integers.{u} K) t ≫ M.torus.hom.hom
  label : normalizer →* W
  labelKernel : ∀ n, label n = 1 ↔ (n : G) ∈ torus
  translation : torus →* Multiplicative D.Y
  characterLog : ∀ (t : torus) (v : TorusValues D (CommAlgCat.of Integers.{u} K)),
    j t = torusPoint D (CommAlgCat.of Integers.{u} K) v ≫ M.torus.hom.hom →
    ∀ x : D.X, D.datum.toLinearMap x (translation t).toAdd =
      WithZero.log (ExceptionalMarkedRootDescent.normalizedValuation K (v (Multiplicative.ofAdd x) : K))
  word : W → List D.I
  lift : W → normalizer
  lift_label : ∀ w, label (lift w) = w
  lift_point : ∀ w, j (lift w) = ExceptionalMarkedRootDescent.markedWeylWord M.toIntegralMarking
    (CommAlgCat.of Integers.{u} K) (word w)

/-- The torus part after removing the finite integral Weyl word. -/
def MarkedLocalNormalizer.torusPart {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    {G : Type u} [Group G] {j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
    {W : Type u} [Group W] (N : MarkedLocalNormalizer K j W) (n : N.normalizer) : N.torus :=
  ⟨(n * (N.lift (N.label n))⁻¹ : N.normalizer), (N.labelKernel _).mp (by simp [N.lift_label])⟩

/-- The normalizer presentation supplied by the integral Weyl words and
the character valuations of the actual split normalizer. -/
def SplitMarkedNormalizerPresentation : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    {index : Type u} [Fintype index] (_b : Module.Basis index ℤ D.Y),
    letI := F.torusComm
    ∀ (word : D.datum.weylGroup → List D.I),
      (∀ w, ∀ i ∈ word w, i ∈ D.base.support) →
      (∀ w, ((word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w) →
    let R := CommAlgCat.of Integers.{u} K
    ∃ N : MarkedLocalNormalizer (M := M) K (MonoidHom.id (IntegralPoints M.group R))
      D.datum.weylGroup,
      N.normalizer = F.point.range ∧ N.word = word ∧
      Function.Surjective N.translation ∧
      (∀ n, ∀ h : F.point n ∈ N.normalizer, N.label ⟨F.point n, h⟩ = F.label n) ∧
      N.translation.ker.map N.torus.subtype = integralUnitTorus (K := K) M

/-- The folded presentation uses the actual relative normalizer and
the fixed absolute Weyl labels. The permitted words in simple orbits
and orthogonality of the moved simple roots come from the finite folded root
calculation. Both valuations are the normalized valuations of the local fields. -/
def FoldedMarkedNormalizerPresentation : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D}
    (C : ExceptionalMarkedRootDescent.MarkedFibre M k) (F : FibreNormalizer M K)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AutomorphismSequence.AdjointQuotient C.realization.pinned.pair.G},
    AutomorphismSequence.SplitSequence C.realization.pinned C.realization.attached l Q →
    ∀ {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
      (d : PinnedPairDescent.DescendedPair (l := l) K ω)
      (σ : Gal(K/k)), Module.finrank k K = 2 → σ ≠ 1 →
    let e := (ExceptionalValuedTorusNormalizer.markedDiagramEquiv
      C.realization (d.data.outer σ)).asIso.hom
    let W := fixedWeylGroup D e
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    (∀ i : D.base.support, simplePermutation D e i ≠ i →
      D.datum.pairing (simplePermutation D e i).val i.val = 0) →
    (∀ x : k, ExceptionalMarkedRootDescent.normalizedValuation K (algebraMap k K x) =
      (ExceptionalMarkedRootDescent.normalizedValuation k x) ^ 2) →
    ∀ (b : Module.Basis D.base.support ℤ D.Y),
      ((∃ h, b = ExceptionalValuedTorusNormalizer.simpleCorootBasis D h) ∨
        (∃ h, b = ExceptionalValuedTorusNormalizer.fundamentalCoweightBasis D h)) →
    ∀ (word : W → List (SimpleRootOrbit D)),
      (∀ w, ∀ o ∈ word w, o.Matches C (pinnedDiagram d.data σ)) →
      (∀ w, (((word w).flatMap SimpleRootOrbit.roots).map
        (RootPairing.weylGroup.ofIdx D.datum)).prod = w.val) →
    let R := CommAlgCat.of Integers.{u} K
    ∃ (j : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →* IntegralPoints M.group R)
      (N : MarkedLocalNormalizer K j W) (S : ClosedSubgroup d.group.val),
      Function.Injective j ∧ (∀ g, j g = pinnedGroundPoint C d.data g) ∧
      Relative.MaximalSplitTori.IsMaximalSplitTorus S ∧
      (∀ g, g ∈ N.normalizer ↔ Normalizes S.inclusion g) ∧
      (∀ g, g ∈ N.normalizer ↔ Normalizes d.torus.inclusion g) ∧
      (∀ g, g ∈ N.torus ↔ SchemeDerivedGroup.FactorsThrough d.torus g) ∧
      (∀ n : N.normalizer, ∃ m, F.point m = j n ∧ F.label m = (N.label n).val) ∧
      (∀ w, N.word w = (word w).flatMap SimpleRootOrbit.roots) ∧
      N.translation.ker.map N.torus.subtype = (integralUnitTorus (K := K) M).comap j ∧
      Set.range (fun t : N.torus => fun i : D.base.support =>
        ((b.repr (N.translation t).toAdd i : ℤ) : ℚ) / 2) =
        Set.range (ExceptionalValuedTorusNormalizer.orbitProjection (simplePermutation D e))

/-- The reduction subgroup meets either actual marked normalizer in
the preimage of the integral unit torus. -/
def MarkedIwahoriNormalizerIntersection : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D} (F : FibreNormalizer M K)
    {G W : Type u} [Group G] [Group W]
    (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (N : MarkedLocalNormalizer K j W),
    letI := F.torusComm
    (∀ n : N.normalizer, j n ∈ F.point.range) →
    let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
    ∀ (C₀ : ExceptionalMarkedRootDescent.MarkedFibre M κ)
      (B₀ : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ))),
      (B₀ : Set _) = markedPositiveBorel C₀ (CommAlgCat.of κ κ) →
      (markedBorelReduction M.group B₀).comap j ⊓ N.normalizer =
        (integralUnitTorus (K := K) M).comap j

/-- After the split or folded point identifications, the ordinary
normalizer is the preimage of the simply connected translation lattice.
The quotient is formed in the image of the actual adjoint torus. -/
def MarkedOrdinaryIwahoriComparison : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : Pinning.BasedRootDatum.{u}} {M : Model D} {A : Model E}
    (c : MarkedCentralCover M A)
    {G G' W : Type u} [Group G] [Group G'] [Group W]
    (j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K))
    (j' : G' →* IntegralPoints A.group (CommAlgCat.of Integers.{u} K))
    (N : MarkedLocalNormalizer K j W) (N' : MarkedLocalNormalizer K j' W)
    (p : G →* G'),
    Function.Injective j' →
    (∀ g, j' (p g) = integralPointHom c.map (CommAlgCat.of Integers.{u} K) (j g)) →
    (∀ w, (N.word w).map c.rootEquiv = N'.word w) →
    N'.torus.comap p = N.torus → N'.normalizer.comap p = N.normalizer →
    p.range.Normal →
    ∀ (I : Subgroup G) (I' : Subgroup G'),
    let U := (integralUnitTorus (K := K) A).comap j'
    I ⊔ N.normalizer = ⊤ → I' ⊔ N'.normalizer = ⊤ →
    I' = I.map p ⊔ U →
    let Y := N'.translation.range
    let ν := N'.translation.rangeRestrict
    let Λ := ((N.torus.map p).comap N'.torus.subtype).map ν
    let J := N.normalizer.map p ⊔ U
    let H := I' ⊔ J
    (∀ n : N.normalizer, ∀ hn : p n ∈ N'.normalizer,
      N'.label ⟨p n, hn⟩ = N.label n) ∧
    (∀ t : N.torus, ∀ ht : p t ∈ N'.torus,
      (N'.translation ⟨p t, ht⟩).toAdd = c.pushCocharacter (N.translation t).toAdd) ∧
    (∀ n : N'.normalizer, (n : G') ∈ J ↔ ν (N'.torusPart n) ∈ Λ) ∧
    H = p.range ⊔ U ∧ H ⊓ N'.normalizer = J ∧
    (∀ g, g ∈ H ↔ ∃ (x : G) (t : U), g = p x * t) ∧
    ∃ (_ : H.Normal) (q : G' ⧸ H ≃* Y ⧸ Λ),
      ∀ t : N'.torus, q (QuotientGroup.mk (t : G')) = QuotientGroup.mk (ν t)

/-- Preservation of the signed root layers and unit torus under the
normalizer action implies preservation of the actual split Iwahori.
An alcove stabilizer preserves exactly these layers. -/
def IwahoriPreservedByLayerAction : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K]
    {D : Pinning.BasedRootDatum.{u}} {M : Model D},
    let κ := IsLocalRing.ResidueField (valuation K).valuationSubring
    let R := CommAlgCat.of Integers.{u} K
    let U := integralUnitTorus (K := K) M
    let allowed := fun (a : D.I) (x : K) =>
      valuation K x ≤ 1 ∧ (¬ D.base.IsPos a → valuation K x < 1)
    ∀ (C : ExceptionalMarkedRootDescent.MarkedFibre M κ)
      (B : Subgroup (IntegralPoints M.group (CommAlgCat.of Integers.{u} κ))),
    (B : Set _) = markedPositiveBorel C (CommAlgCat.of κ κ) →
    ∀ (n : IntegralPoints M.group R) (w : Equiv.Perm D.I) (m : D.I → Kˣ),
    (∀ t, t ∈ U ↔ n * t * n⁻¹ ∈ U) →
    (∀ a x, allowed a x ↔ allowed (w a) ((m a : K) * x)) →
    (∀ a x, n * ExceptionalMarkedRootDescent.markedRootPoint M.toIntegralMarking R a x * n⁻¹ =
      ExceptionalMarkedRootDescent.markedRootPoint M.toIntegralMarking R (w a) ((m a : K) * x)) →
    ∀ g, g ∈ markedBorelReduction M.group B ↔ n * g * n⁻¹ ∈ markedBorelReduction M.group B

/-- A central map with torus restriction faithfully flat and scheme kernel
inside the source torus has the source torus as its inverse image. Its
rational point map detects precisely membership in the torus normalizer. -/
def CentralTorusAndNormalizerPreimages : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (U : ClosedSubgroup H.val)
    (f : G.val ⟶ H.val) (fT : T.group ⟶ U.group),
    CentralIsogenies.IsTorusRestriction f fT →
    ∀ (Z : ClosedSubgroup G.val), IsSchemeKernel f Z →
      SchemeDerivedGroup.IsSubgroupOf Z T →
      (∀ (X : SchemeOver k) [IsAffine X.left] (g : X ⟶ G.val.X),
        SchemeDerivedGroup.FactorsThrough U (g ≫ f.hom.hom) ↔
          SchemeDerivedGroup.FactorsThrough T g) ∧
      ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        Normalizes U.inclusion (g ≫ f.hom.hom) ↔ Normalizes T.inclusion g

/-- The image on rational points of a central isogeny is normal, including
for a nonreduced scheme kernel. -/
def CentralIsogenyRationalImageNormal : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val),
    CentralIsogenies.IsCentralIsogeny f →
      (pointHom f (𝟙_ (SchemeOver k))).range.Normal

/-- The rational point-group calculation after establishing the marked
comparison, including the preimages of the torus and the normalizer. -/
def OrdinaryImageQuotient : Prop :=
  ∀ {Gsc G Y : Type*} [Group Gsc] [Group G] [CommGroup Y]
    (p : Gsc →* G) (Tsc Nsc : Subgroup Gsc) (T N I J : Subgroup G)
    (ν : T →* Y),
    T ≤ N →
    Function.Surjective ν →
    (∀ g : G, ∃ (x : Gsc) (t : T), g = p x * t) →
    (∀ t : T, ∀ x : Gsc, (t : G) * p x * (t : G)⁻¹ ∈ p.range) →
    T.comap p = Tsc →
    N.comap p = Nsc →
    ((ν.ker.map T.subtype : Subgroup G) ≤ I) →
    I ≤ p.range ⊔ ν.ker.map T.subtype →
    J = (Nsc.map p) ⊔ ν.ker.map T.subtype →
    p.range ≤ I ⊔ J →
    let H := I ⊔ J
    let Λ := ((Tsc.map p).comap T.subtype).map ν
    H = p.range ⊔ ν.ker.map T.subtype ∧
    H ⊓ N = J ∧
    ∃ (_ : H.Normal) (e : G ⧸ H ≃* Y ⧸ Λ),
      ∀ t : T, e (QuotientGroup.mk (t : G)) = QuotientGroup.mk (ν t)

/-- The ordinary subgroup comes from the source affine action. Matching
the finite lifts and the torus translations then gives the quotient of
the two translation lattices on the entire adjoint point group. -/
def OrdinarySubgroupFromCentralMap : Prop :=
  ∀ {Gsc G Y W Asc A : Type*} [Group Gsc] [Group G] [CommGroup Y] [Group W]
    [Group Asc] [Group A] (p : Gsc →* G)
    (Tsc Nsc Isc : Subgroup Gsc) (T N I : Subgroup G)
    (ν : T →* Y) (q : N →* W) (a₀ : Nsc →* Asc) (a : N →* A) (b : Asc →* A),
    T ≤ N → Function.Surjective ν → Function.Surjective a₀ →
    T.comap p = Tsc → N.comap p = Nsc →
    (∀ n : N, q n = 1 ↔ (n : G) ∈ T) →
    (∀ w, ∃ n : Nsc, ∃ m : N, (m : G) = p n ∧ q m = w) →
    (∀ n : Nsc, ∀ m : N, (m : G) = p n → a m = b (a₀ n)) →
    p.range.Normal →
    Isc ⊔ Nsc = ⊤ → I ⊔ N = ⊤ →
    let U := ν.ker.map T.subtype
    a.ker.map N.subtype = U →
    I = Isc.map p ⊔ U →
    let J := (b.range.comap a).map N.subtype
    let G₀ := I ⊔ J
    let Λ := ((Tsc.map p).comap T.subtype).map ν
    J = (Nsc.map p) ⊔ U ∧
    G₀ = p.range ⊔ U ∧ G₀ ⊓ N = J ∧
    ∃ (_ : G₀.Normal) (e : G ⧸ G₀ ≃* Y ⧸ Λ),
      ∀ t : T, e (QuotientGroup.mk (t : G)) = QuotientGroup.mk (ν t)

end

end LinearAlgebraicGroups.Specs.ExceptionalIwahoriImageComparison
