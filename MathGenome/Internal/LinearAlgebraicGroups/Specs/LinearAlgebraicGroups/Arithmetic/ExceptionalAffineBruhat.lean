import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.GroupAction.Quotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
The marked affine Bruhat comparison and its lattice, residue-layer and Coxeter lemmas.
-/

namespace LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat

open scoped Pointwise Matrix

abbrev E6ProjectedLattices : Prop := ExceptionalAffineRootSystems.E6ProjectedLattices

abbrev E6CoweightClass : Prop := ExceptionalAffineRootSystems.E6CoweightClass

/-- Each step of a discrete valuation filtration contributes one residue-field factor.
This is the cardinality of the integral ring modulo a depth level. -/
def ResiduePowerCounts : Prop :=
  ∀ (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (m : ℕ),
    Nat.card (R ⧸ (IsLocalRing.maximalIdeal R) ^ m) =
      Nat.card (IsLocalRing.ResidueField R) ^ m

/-- The layer between two powers of the maximal ideal, represented as the
image of the shallower ideal in the deeper quotient. -/
def ResidueLayerCounts : Prop :=
  ∀ (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] (a b : ℕ), a ≤ b →
    let P := IsLocalRing.maximalIdeal R
    Nat.card (Submodule.map (P ^ b).mkQ (P ^ a)) =
      Nat.card (IsLocalRing.ResidueField R) ^ (b - a)

variable {G : Type*} [Group G]

/-- The set of left cosets of I contained in I g I. -/
def leftCosets (I : Subgroup G) (g : G) : Set (G ⧸ I) :=
  QuotientGroup.mk '' DoubleCoset.doubleCoset g I I

/-- The stabilizer of the coset of `g` inside `I`, expressed by conjugation. -/
def conjugateIntersection (I : Subgroup G) (g : G) : Subgroup I :=
  I.comap ((MulAut.conj g⁻¹).toMonoidHom.comp I.subtype)

/-- The right-`I` quotient of a double coset has the index of the conjugate
intersection inside `I`. -/
def LeftCosetIndex : Prop :=
  ∀ {G : Type*} [Group G] (I : Subgroup G) (g : G),
    Nat.card (leftCosets I g) = (conjugateIntersection I g).index

open IntegralRootRelations (upper lower diagonal)

/-- The simple lift with root parameter `p`, where `p` may be a negative
power of the uniformizer. -/
def wallLift {K : Type*} [Field K] (p : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -(p : K); (↑p⁻¹ : K), 0], by simp [Matrix.det_fin_two]⟩

/-- Exact-depth rank-one multiplication for an affine simple wall. -/
def RankOneWallMultiplication : Prop :=
  ∀ {K : Type*} [Field K] (p t : Kˣ),
    upper (t : K) * wallLift p =
      lower (↑t⁻¹ : K) * diagonal (t * p⁻¹) * upper (-(p : K) ^ 2 / (t : K))

/-- The deeper-layer rank-one commutation and the square of the wall lift. -/
def RankOneWallConjugation : Prop :=
  ∀ {K : Type*} [Field K] (p : Kˣ),
    (∀ t : K, upper t * wallLift p =
      wallLift p * lower (- (↑p⁻¹ : K) ^ 2 * t)) ∧
    wallLift p * wallLift p = diagonal (-1 : Kˣ)

/-- The set product at a simple wall from an ordered factorization and
the two rank-one depth cases. The first root group is `A`, with next layer `Aplus`. -/
def RankOneDoubleCosetProduct : Prop :=
  ∀ {G : Type*} [Group G] (I A Aplus : Subgroup G) (g s : G),
    A ≤ I →
    (∀ i ∈ I, ∃ u ∈ A, ∃ j ∈ I, s⁻¹ * j * s ∈ I ∧ i = u * j) →
    let D := fun h => DoubleCoset.doubleCoset h I I
    ((∀ u ∈ A, g * u * g⁻¹ ∈ I) → D g * D s = D (g * s)) ∧
    ((∀ u ∈ Aplus, s⁻¹ * u * s ∈ I) →
      (∀ u ∈ A, u ∉ Aplus → g * u * s ∈ D g) →
      (∃ u ∈ A, u ∉ Aplus) → D g * D s = D (g * s) ∪ D g)

/-- The group-theoretic assembly of the double-coset decomposition. Its inputs
are the two wall multiplication formulas and the independently computed counts. -/
def CoxeterDoubleCosets : Prop :=
  ∀ {G B W : Type*} [Group G] [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (I : Subgroup G) (lift : W → G) (q : ℕ),
    2 ≤ q → lift 1 ∈ I → (∀ i, lift (cs.simple i) ^ 2 ∈ I) →
    let D := fun w => DoubleCoset.doubleCoset (lift w) I I
    (∀ w, Nat.card (leftCosets I (lift w)) = q ^ cs.length w) →
    (∀ w i, ¬cs.IsRightDescent w i → D w * D (cs.simple i) = D (w * cs.simple i)) →
    (∀ w i, cs.IsRightDescent w i → D w * D (cs.simple i) = D (w * cs.simple i) ∪ D w) →
    (∀ w, lift w ∈ Subgroup.closure ((I : Set G) ∪ Set.range (lift ∘ cs.simple))) →
    (Pairwise fun w v => Disjoint (D w) (D v)) ∧
      ⋃ w, D w = (Subgroup.closure ((I : Set G) ∪ Set.range (lift ∘ cs.simple)) : Set G)


open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct WithZero
open Pinning (BasedRootDatum BasedIso)
open IntegralSemisimpleModel (Model IntegralPoints Integers integerAlgebra integralSpec
  integralPointFunctor TorusValues)
open ExceptionalAffineRootSystems (ApartmentRoots AlcoveGeometry AlcoveCoxeterData PinnedWallSigns
  alcoveStabilizer threshold e6Partner exceptionalCartan diagramFixedSpace diagramCocharacters
  diagramAverage FoldedRootDirection foldedDepthDenominator IsLongF4Doubled)
open ExceptionalIwahoriCongruence (cellValue mapCellValues integralRing markedPointTopology
  integralRingMap changeRingHom)
open ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation ramificationIndex)
open ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom integralUnitTorus
  pinnedGroundPoint pointHom)
open ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint markedRootPoint markedWeylWord
  markedWall wallMatrix SimpleRootOrbit)
open ExceptionalValuedTorusNormalizer (markedDiagramEquiv fixedWeylGroup invariantApartment)
open OrderedRootProducts (Enumerates)

universe u v

attribute [local instance] integerAlgebra

noncomputable section

abbrev FieldPoints {D : BasedRootDatum.{u}} (M : Model D) (K : Type u) [Field K] :=
  IntegralPoints M.group (CommAlgCat.of Integers.{u} K)

abbrev residue (K : Type u) [Field K] [ValuativeRel K] :=
  IsLocalRing.ResidueField (ValuativeRel.valuation K).valuationSubring

abbrev identityPoints {D : BasedRootDatum.{u}} (M : Model D) (K : Type u) [Field K] :=
  MonoidHom.id (FieldPoints M K)

abbrev scalarPoints {D : BasedRootDatum.{u}} (M : Model D) {K E : Type u}
    [Field K] [Field E] (f : K →+* E) : FieldPoints M K →* FieldPoints M E :=
  changeRingHom M.group (integralRingMap f)

/-- The marked exceptional diagram and a choice of its standard numbering. -/
def ExceptionalNumbering (D : BasedRootDatum.{u}) (n : ℕ) (b : Fin n ≃ D.base.support) : Prop :=
  Module.finrank ℤ D.Y = n ∧
  ∀ i j, D.datum.pairing (b i) (b j) = exceptionalCartan n i j

/-- The vertex of cotype one determined by its incident simple walls. -/
def IsAlcoveVertex {V J : Type*} [AddCommGroup V] [Module ℚ V]
    (A : ApartmentRoots ℚ V J) (p : V) (i : A.SimpleWall p) (x : V) : Prop :=
  (∀ a : J × ℤ, A.positive p a → 0 ≤ A.wallValue a x) ∧
  ∀ j : A.SimpleWall p, A.wallValue j.val x = 0 ↔ j ≠ i

section LocalComparison

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf]
  {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]

/-- A root parameter changes from the transported pinning to the original
absolute coordinate by an integral unit. Keeping that unit separate makes
each underlying parameter-field embedding a ring homomorphism. -/
structure RootSlots (negative positive : List D.I) (P : J → Type u)
    [∀ i, Field (P i)] where
  torus : Set (TorusValues D (integralRing K))
  neg : Fin negative.length → J
  pos : Fin positive.length → J
  negMap : ∀ i, P (neg i) →+* K
  posMap : ∀ i, P (pos i) →+* K
  negUnit : Fin negative.length → Integers.{u}ˣ
  posUnit : Fin positive.length → Integers.{u}ˣ

def RootSlots.coordinates {negative positive : List D.I} {P : J → Type u} [∀ i, Field (P i)]
    (C : RootSlots (K := K) negative positive P) (t : C.torus) (x : ∀ i, P i) :
    ExceptionalIwahoriCongruence.CellValues D (integralRing K) negative positive :=
  (fun l => algebraMap Integers.{u} K (C.negUnit l : Integers.{u}) * C.negMap l (x (C.neg l)),
    t.val,
    fun l => algebraMap Integers.{u} K (C.posUnit l : Integers.{u}) * C.posMap l (x (C.pos l)))

/-- The absolute coordinate slots, rational parameter fields and normalized
relative directions of one ordered marked chart. -/
structure LocalRootChart (A : ApartmentRoots ℚ V J) (p : V) where
  direction : D.I → J
  negative : List D.I
  positive : List D.I
  negative_enumerates : Enumerates negative {a | ¬ D.base.IsPos a}
  positive_enumerates : Enumerates positive {a | D.base.IsPos a}
  parameter : J → Type u
  parameterField : ∀ a, Field (parameter a)
  value : ∀ a, letI := parameterField a; Valuation (parameter a) ℤᵐ⁰
  chart : letI := parameterField
          RootSlots (K := K) negative positive parameter
  neg_slots : ∀ i : Fin negative.length, chart.neg i = direction negative[i]
  pos_slots : ∀ i : Fin positive.length, chart.pos i = direction positive[i]
  rational (z : ExceptionalIwahoriCongruence.CellValues D (integralRing K) negative positive) :
    letI := parameterField
    cellValue M.toIntegralMarking (integralRing K) negative positive z ∈ j.range ↔
      ∃ (t : chart.torus) (x : ∀ i, parameter i), chart.coordinates t x = z
  signs : PinnedWallSigns A p (fun a => ∃ b, direction b = a ∧ D.base.IsPos b)

attribute [instance] LocalRootChart.parameterField

/-- The depth condition at any point of the apartment, in uniformizer steps
of the field for each root. The two charts for an intersection share these
marked coordinate slots. -/
def LocalRootChart.atPoint {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalRootChart (M := M) (j := j) A p) (x : V) (g : G) : Prop :=
  ∃! z : C.chart.torus × (∀ a, C.parameter a),
    cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
      (C.chart.coordinates z.1 z.2) = j g ∧
    (∀ χ, normalizedValuation K (z.1.val χ : K) = 1) ∧
    ∀ a, C.value a (z.2 a) ≤ WithZero.exp (-threshold (A.root a x))

/-- The comparison for one marked rational point group. All quotient
labels are images under the displayed action of the actual normalizer. -/
structure LocalComparison (A : ApartmentRoots ℚ V J) (p : V) where
  point_injective : Function.Injective j
  localIwahori : LocalIwahori j Wf
  compact_open : ∀ (B : IntegralSemisimpleModel.IntegralAlgebra.{u})
    [Algebra.FiniteType Integers.{u} B] (e : integralSpec.obj (.op B) ≅ M.group.X),
    letI : TopologicalSpace G := TopologicalSpace.induced j (markedPointTopology B e K)
    IsCompact (localIwahori.iwahori : Set G) ∧ IsOpen (localIwahori.iwahori : Set G)
  chart : LocalRootChart (M := M) (j := j) A p
  geometry : AlcoveGeometry A p
  coxeter : AlcoveCoxeterData A p
  affine : localIwahori.normalizer.normalizer →* (V ≃ᵃ[ℚ] V)
  kernel : affine.ker.map localIwahori.normalizer.normalizer.subtype =
    (integralUnitTorus (K := K) M).comap j
  lift : A.affineWeylGroup → localIwahori.normalizer.normalizer
  lift_label (w : A.affineWeylGroup) : affine (lift w) = w.val

abbrev LocalComparison.I {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) := C.localIwahori.iwahori

abbrev LocalComparison.N {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) := C.localIwahori.normalizer.normalizer

abbrev LocalComparison.T₀ {A : ApartmentRoots ℚ V J} {p : V}
    (_C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) :=
  (integralUnitTorus (K := K) M).comap j

/-- The subgroup generated by the Iwahori and the ordinary normalizer. -/
def LocalComparison.G₀ {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) : Subgroup G :=
  C.I ⊔ (A.affineWeylGroup.comap C.affine).map C.N.subtype

def LocalComparison.cell {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) (w : A.affineWeylGroup) : Set G :=
  DoubleCoset.doubleCoset ((C.lift w : C.N) : G) C.I C.I

open scoped Classical in
/-- The wall maps use the marked upper and lower coordinates and the
transported integral rank-one map at the depth of the simple wall. -/
def LocalComparison.RankOneLifts {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) : Prop :=
  ∀ a : A.SimpleWall p,
    let P := C.chart.parameter a.val.1
    let R := CommAlgCat.of Integers.{u} K
    ∃ (word : List D.I) (orbit : List (D.base.support × (P →+* K)))
      (r : Matrix.SpecialLinearGroup (Fin 2) P →* G) (t c : Pˣ) (u : C.chart.chart.torus),
      (∀ i ∈ word, i ∈ D.base.support) ∧
      orbit.length = (if (∃ i b : D.I, i ≠ b ∧
        C.chart.direction i = a.val.1 ∧ C.chart.direction b = a.val.1) then 2 else 1) ∧
      ((orbit.map fun b => ((word.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.indexEquiv
        b.1.val).Nodup) ∧
      (∀ i, C.chart.direction i = a.val.1 ↔
        i ∈ orbit.map (fun b => ((word.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.indexEquiv b.1.val)) ∧
      (∀ U, j (r U) =
        let m := markedWeylWord M.toIntegralMarking R word
        m * (orbit.map (fun b => (show FieldPoints M K from
          (M.rankOne b.1).app R (Matrix.SpecialLinearGroup.map b.2 U)))).prod * m⁻¹) ∧
      u.val = 1 ∧
      C.chart.value a.val.1 (c : P) = 1 ∧
      (∀ x : P, j (r (upper x)) =
        cellValue M.toIntegralMarking (integralRing K) C.chart.negative C.chart.positive
          (C.chart.chart.coordinates u (Function.update (fun _ => 0) a.val.1 ((c : P) * x)))) ∧
      C.chart.value a.val.1 (t : P) = WithZero.exp (-a.val.2) ∧
      (C.lift (C.coxeter.coxeter.simple a) : G) = r (wallMatrix t)

open scoped Classical in
/-- Actual Bruhat decomposition, simple multiplication and the congruence
index computed in the very chart used for positive Borel reduction. -/
structure LocalComparison.Bruhat {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) (q : ℕ) : Prop where
  rank_one : C.RankOneLifts
  ordinary_normalizer : C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype
  base_chart (g : G) : g ∈ C.I ↔ C.chart.atPoint p g
  translated_chart (w : A.affineWeylGroup) (g : G) :
    g ∈ C.I.map (MulAut.conj ((C.lift w : C.N) : G)).toMonoidHom ↔
      C.chart.atPoint (w.val p) g
  disjoint : Pairwise fun w v => Disjoint (C.cell w) (C.cell v)
  cover : ⋃ w, C.cell w = (C.G₀ : Set G)
  wall_product (w : A.affineWeylGroup) (i : A.SimpleWall p) :
    letI := C.coxeter.action
    let s := C.coxeter.coxeter.simple i
    C.cell w * C.cell s =
      if A.positive p (w • i.val) then C.cell (w * s) else C.cell (w * s) ∪ C.cell w
  congruence_index (w : A.affineWeylGroup) :
    (conjugateIntersection C.I ((C.lift w : C.N) : G)).index =
      q ^ ∑ᶠ a, (threshold (A.root a (w.val p)) - threshold (A.root a p)).toNat
  coset_count (w : A.affineWeylGroup) :
    Nat.card (leftCosets C.I ((C.lift w : C.N) : G)) = q ^ C.coxeter.coxeter.length w

end LocalComparison


section NormalizerLabels

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- The action uses the finite label in the actual marked field fibre. -/
def LocalComparison.FiniteLabels (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p)
    (q : Wf →* D.datum.weylGroup) : Prop :=
  Function.Injective q ∧
  ∃ F : ExceptionalValuedTorusNormalizer.FibreNormalizer M K,
    (∀ n : C.N, ∃ m, F.point m = j n ∧ F.label m = q (C.localIwahori.normalizer.label n)) ∧
    ∀ w, ((C.localIwahori.normalizer.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = q w

/-- Length-zero representatives and their actions on ordinary labels and
on the walls and vertices of the standard alcove. -/
structure LocalComparison.TypeQuotient
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p) where
  normal : C.G₀.Normal
  quotient : letI := normal; G ⧸ C.G₀ ≃* alcoveStabilizer A (A.alcove p)
  lift : alcoveStabilizer A (A.alcove p) → C.N
  affine_lift (ω : alcoveStabilizer A (A.alcove p)) : C.affine (lift ω) = ω.val.val
  quotient_lift (ω : alcoveStabilizer A (A.alcove p)) :
    letI := normal
    quotient (QuotientGroup.mk ((lift ω : C.N) : G)) = ω
  preserves_I (ω : alcoveStabilizer A (A.alcove p)) :
    C.I.map (MulAut.conj ((lift ω : C.N) : G)).toMonoidHom = C.I
  wallPerm : alcoveStabilizer A (A.alcove p) →* Equiv.Perm (A.SimpleWall p)
  wall_action (ω : alcoveStabilizer A (A.alcove p)) (a : A.SimpleWall p) :
    ω.val.val '' A.wallHyperplane a.val = A.wallHyperplane (wallPerm ω a).val
  vertex (a : A.SimpleWall p) : ∃! x, IsAlcoveVertex A p a x
  vertex_action (ω : alcoveStabilizer A (A.alcove p)) (a : A.SimpleWall p) (x : V) :
    IsAlcoveVertex A p a x → IsAlcoveVertex A p (wallPerm ω a) (ω.val.val x)

/-- The split comparison uses the absolute root coordinates and the
cocharacter apartment of the very model whose points define the Iwahori. -/
def SplitPointComparison (F : MarkedFibre M K) (adjoint : Bool)
    {p : ℚ ⊗[ℤ] D.Y}
    (C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p) : Prop :=
  let A := ApartmentRoots.split D.datum ℚ
  let N := C.localIwahori.normalizer
  (∀ g, ExceptionalIwahoriImageComparison.markedGroundPoint F g ∈ C.N ↔
    Normalizes F.realization.pinned.pair.T.inclusion g) ∧
  C.FiniteLabels (MonoidHom.id _) ∧
  C.chart.direction = id ∧
  (∀ i, C.chart.chart.negUnit i = 1) ∧ (∀ i, C.chart.chart.posUnit i = 1) ∧
  (∀ i, ∃ e : C.chart.parameter i ≃+* K,
    (∀ x, C.chart.value i x = normalizedValuation K (e x)) ∧
    (∀ l (h : C.chart.chart.neg l = i) (x : C.chart.parameter i),
      C.chart.chart.negMap l (h.symm ▸ x) = e x) ∧
    (∀ l (h : C.chart.chart.pos l = i) (x : C.chart.parameter i),
      C.chart.chart.posMap l (h.symm ▸ x) = e x)) ∧
  (∀ (n : C.N) (x : ℚ ⊗[ℤ] D.Y), C.affine n x =
    (N.label n).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x +
      ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd)) ∧
  (Set.range (fun t : N.torus => (1 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd)) =
    (if adjoint then (A.coweightLattice : Set _) else A.corootLattice) ∧
  C.affine.range = if adjoint then A.extendedAffineWeylGroup else A.affineWeylGroup

end NormalizerLabels

section CentralComparison

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {G H Wf Wf' : Type u} [Group G] [Group H] [Group Wf] [Group Wf']
  {j : G →* FieldPoints M K} {j' : H →* FieldPoints M' K}
  {V V' : Type u} {J J' : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
  {A : ApartmentRoots ℚ V J} {A' : ApartmentRoots ℚ V' J'} {p : V} {p' : V'}

/-- The central map compares the actual Iwahori subgroups and normalizer
actions, through the map on the marked cocharacter spaces. -/
def CentralComparison (c : MarkedCentralCover M M') (φ : G →* H)
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p)
    (C' : LocalComparison (M := M') (j := j') (Wf := Wf') A' p')
    (e : V ≃ₗ[ℚ] V') : Prop :=
  (∀ g, j' (φ g) = integralPointHom c.map (CommAlgCat.of Integers.{u} K) (j g)) ∧
  C'.I.comap φ = C.I ∧
  (∀ h, h ∈ C'.I ↔ ∃ (g : C.I) (t : C'.T₀), h = φ g * t) ∧
  C'.N.comap φ = C.N ∧
  C'.T₀.comap φ = C.T₀ ∧
  C'.localIwahori.normalizer.torus.comap φ = C.localIwahori.normalizer.torus ∧
  (∀ (n : C.N) (n' : C'.N), (n' : H) = φ n → ∀ x, e (C.affine n x) = C'.affine n' (e x)) ∧
  (∀ h, h ∈ C'.G₀ ↔ ∃ (g : G) (t : C'.T₀), h = φ g * t) ∧
  e '' A.alcove p = A'.alcove p' ∧
  ∃ d : J ≃ J',
    (∀ i, d (C.chart.direction i) = C'.chart.direction (c.rootEquiv i)) ∧
    (∀ a x, A'.root (d a) (e x) = A.root a x) ∧
    ∀ a, e (A.coroot a) = A'.coroot (d a)

end CentralComparison

section ScalarComparison

variable {F K : Type u} [Field F] [Field K] [ValuativeRel F] [ValuativeRel K]
  [TopologicalSpace F] [TopologicalSpace K] [IsNonarchimedeanLocalField F]
  [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}
  {G H Wf : Type u} [Group G] [Group H] [Group Wf]
  {j : G →* FieldPoints M F} {j' : H →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- Scalar extension acts on the given marked points and induces the
identity on both affine label groups in the common apartment. -/
def ScalarComparison (f : F →+* K) (s : G →* H)
    (C : LocalComparison (M := M) (j := j) (Wf := Wf) A p)
    (C' : LocalComparison (M := M) (j := j') (Wf := Wf) A p) : Prop :=
  Function.Injective s ∧
  (∀ g, j' (s g) = scalarPoints M f (j g)) ∧
  C'.I.comap s = C.I ∧ C'.N.comap s = C.N ∧ C'.T₀.comap s = C.T₀ ∧ C'.G₀.comap s = C.G₀ ∧
  C'.localIwahori.normalizer.torus.comap s = C.localIwahori.normalizer.torus ∧
  C.affine.range = C'.affine.range ∧
  (∀ (n : C.N) (n' : C'.N), (n' : H) = s n →
    C'.affine n' = C.affine n ∧
    C'.localIwahori.normalizer.label n' = C.localIwahori.normalizer.label n) ∧
  (∀ w, s (C.lift w) * (C'.lift w : H)⁻¹ ∈ C'.T₀) ∧
  C.chart.direction = C'.chart.direction ∧
  ∃ (hn : C.chart.negative = C'.chart.negative) (hp : C.chart.positive = C'.chart.positive)
    (e : ∀ a, C.chart.parameter a →+* C'.chart.parameter a)
    (tmap : C.chart.chart.torus → C'.chart.chart.torus),
    (∀ a x, C'.chart.value a (e a x) = C.chart.value a x) ∧
    ∀ t x, mapCellValues (integralRingMap f) (C.chart.chart.coordinates t x) =
      (hn.symm ▸ hp.symm ▸ C'.chart.chart.coordinates (tmap t) (fun a => e a (x a)))

/-- Coefficient or coefficient-and-diagram action on existing comparison
data, by the indicated affine conjugation on their labels. -/
def AutomorphismComparison
    (C : LocalComparison (M := M) (j := j') (Wf := Wf) A p) (s : MulAut H)
    (e : V ≃ᵃ[ℚ] V) : Prop :=
  C.I.map s.toMonoidHom = C.I ∧ C.N.map s.toMonoidHom = C.N ∧
  C.T₀.map s.toMonoidHom = C.T₀ ∧ C.G₀.map s.toMonoidHom = C.G₀ ∧
  C.localIwahori.normalizer.torus.map s.toMonoidHom = C.localIwahori.normalizer.torus ∧
  e '' A.alcove p = A.alcove p ∧
  (∀ (n : C.N) (n' : C.N), (n' : H) = s n → C.affine n' = e * C.affine n * e⁻¹) ∧
  ∀ w : A.affineWeylGroup, ∃ w' : A.affineWeylGroup,
    (w' : V ≃ᵃ[ℚ] V) = e * w.val * e⁻¹ ∧ s (C.lift w) * (C.lift w' : H)⁻¹ ∈ C.T₀

end ScalarComparison

/-- A finite extension of these local fields is unramified when its
normalized value group is unchanged. The finite residue fields are perfect. -/
def IsUnramifiedLocalExtension (F K : Type u) [Field F] [Field K]
    [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [Algebra F K] : Prop :=
  ∀ z : F, normalizedValuation K (algebraMap F K z) = normalizedValuation F z

open AdjointRepresentation (GroupPoints)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open PinnedPairDescent (DescendedPair)

/-- The pinned semilinear operation on the split marked model over a
coefficient field. Its geometric part is the specified pinned automorphism. -/
def pinnedCoefficientPoint {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D : BasedRootDatum.{u}} {M : Model D} (F₀ : MarkedFibre M F)
    (δ : Aut F₀.realization.pinned) (σ : Gal(K/F))
    (v : GroupPoints F₀.realization.pinned.pair.G.val (CommAlgCat.of F K)) : FieldPoints M K :=
  markedFibrePoint F₀ (CommAlgCat.of F K)
    ((testSpec F).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ v ≫ δ.asIso.hom.group.hom.hom.hom)

/-- Both split isogeny types at one field, with the canonical central map
and common identification of the two apartments. -/
structure SplitLevel (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (p : ℚ ⊗[ℤ] D.Y) (p' : ℚ ⊗[ℤ] E.Y)
    (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) where
  sc : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
    (ApartmentRoots.split D.datum ℚ) p
  ad : LocalComparison (j := identityPoints M' K) (Wf := E.datum.weylGroup)
    (ApartmentRoots.split E.datum ℚ) p'
  sc_fibre : MarkedFibre M K
  ad_fibre : MarkedFibre M' K
  sc_points : SplitPointComparison sc_fibre false sc
  ad_points : SplitPointComparison ad_fibre true ad
  sc_bruhat : sc.Bruhat (Nat.card (residue K))
  ad_bruhat : ad.Bruhat (Nat.card (residue K))
  central : CentralComparison c (integralPointHom c.map (CommAlgCat.of Integers.{u} K)) sc ad e
  typeQuotient : ad.TypeQuotient

/-- Agreement of the two adjoint type quotients on normalizer
representatives, with the alcove labels in the common apartment. -/
def TypeQuotientTransport
    {F K : Type u} [Field F] [Field K] [ValuativeRel F] [ValuativeRel K]
    [TopologicalSpace F] [TopologicalSpace K] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D}
    {G H Wf : Type u} [Group G] [Group H] [Group Wf]
    {j : G →* FieldPoints M F} {j' : H →* FieldPoints M K}
    {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V}
    {C : LocalComparison (M := M) (j := j) (Wf := Wf) A p}
    {C' : LocalComparison (M := M) (j := j') (Wf := Wf) A p}
    (Q : C.TypeQuotient) (Q' : C'.TypeQuotient) (s : G →* H)
    (α : alcoveStabilizer A (A.alcove p) →* alcoveStabilizer A (A.alcove p)) : Prop :=
  letI := Q.normal
  letI := Q'.normal
  (∀ g, Q'.quotient (QuotientGroup.mk (s g)) = α (Q.quotient (QuotientGroup.mk g))) ∧
  ∀ ω, s (Q.lift ω) * (Q'.lift (α ω) : H)⁻¹ ∈ C'.T₀

/-- Coefficient action, with trivial action on the standard apartment of
each split model. -/
def SplitLevel.Coefficients
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (X : SplitLevel K c p p' e) : Prop :=
  ∃ (a : Gal(K/F) →* MulAut (FieldPoints M K))
    (a' : Gal(K/F) →* MulAut (FieldPoints M' K)),
    (∀ σ g, a σ g = scalarPoints M σ.toRingHom g) ∧
    (∀ σ g, a' σ g = scalarPoints M' σ.toRingHom g) ∧
    (∀ σ, AutomorphismComparison X.sc (a σ) 1 ∧
      AutomorphismComparison X.ad (a' σ) 1 ∧
      TypeQuotientTransport X.typeQuotient X.typeQuotient (a' σ).toMonoidHom (MonoidHom.id _))

/-- The pinned E₆ diagram acts by the actual semilinear operators and the
nonidentity diagram automorphism inverts the length-zero quotient. -/
def SplitLevel.OuterE6Coefficients
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (X : SplitLevel K c p p' e) (b : Fin 6 ≃ D.base.support) (b' : Fin 6 ≃ E.base.support)
    (C : MarkedFibre M F) (C' : MarkedFibre M' F)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    {Q' : AdjointQuotient C'.realization.pinned.pair.G} : Prop :=
  SplitSequence C.realization.pinned C.realization.attached l Q →
  SplitSequence C'.realization.pinned C'.realization.attached l' Q' →
  ∀ (ω : Gal(K/F) →* Aut C.realization.attached.toBased)
    (ω' : Gal(K/F) →* Aut C'.realization.attached.toBased),
    let τ σ := (markedDiagramEquiv C.realization (ω σ)).asIso.hom
    let τ' σ := (markedDiagramEquiv C'.realization (ω' σ)).asIso.hom
    (∀ σ, (∀ i, (τ σ).val.indexEquiv (b i) = b i ∧ (τ' σ).val.indexEquiv (b' i) = b' i) ∨
      (∀ i, (τ σ).val.indexEquiv (b i) = b (e6Partner i) ∧
        (τ' σ).val.indexEquiv (b' i) = b' (e6Partner i))) →
    ∃ (a : Gal(K/F) →* MulAut (FieldPoints M K))
      (a' : Gal(K/F) →* MulAut (FieldPoints M' K))
      (β : Gal(K/F) →* MulAut (alcoveStabilizer (ApartmentRoots.split E.datum ℚ)
        ((ApartmentRoots.split E.datum ℚ).alcove p'))),
      (∀ σ v, a σ (markedFibrePoint C (CommAlgCat.of F K) v) = pinnedCoefficientPoint C (l (ω σ)) σ v) ∧
      (∀ σ v, a' σ (markedFibrePoint C' (CommAlgCat.of F K) v) = pinnedCoefficientPoint C' (l' (ω' σ)) σ v) ∧
      ∀ σ,
        let h := (diagramCocharacters (τ σ).val).toAffineEquiv
        let h' := (diagramCocharacters (τ' σ).val).toAffineEquiv
        AutomorphismComparison X.sc (a σ) h ∧ AutomorphismComparison X.ad (a' σ) h' ∧
        TypeQuotientTransport X.typeQuotient X.typeQuotient (a' σ).toMonoidHom (β σ).toMonoidHom ∧
        (∀ z, (β σ z).val.val = h' * z.val.val * h'⁻¹) ∧
        ((∀ i, (τ' σ).val.indexEquiv (b' i) = b' (e6Partner i)) → ∀ z, β σ z = z⁻¹)

/-- The split affine Bruhat comparison at the base field and every finite
unramified level, including the pinned action used for unramified outer E₆. -/
def SplitAffineBruhatComparison : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (n : ℕ) (b : Fin n ≃ D.base.support) (b' : Fin n ≃ E.base.support),
    (n = 6 ∨ n = 7 ∨ n = 8) →
    ExceptionalNumbering D n b → ExceptionalNumbering E n b' →
    D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
    ∃ (p : ℚ ⊗[ℤ] D.Y) (p' : ℚ ⊗[ℤ] E.Y)
      (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) (X : SplitLevel F c p p' e),
      e.toLinearMap = c.pushCocharacter.baseChange ℚ ∧ p' = e p ∧
      ∀ (K : Type u) [Field K] [Algebra F K] [FiniteDimensional F K]
        [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
        IsUnramifiedLocalExtension F K →
        ∃ Y : SplitLevel K c p p' e,
          let s := scalarPoints M (algebraMap F K)
          let s' := scalarPoints M' (algebraMap F K)
          ScalarComparison (algebraMap F K) s X.sc Y.sc ∧
          ScalarComparison (algebraMap F K) s' X.ad Y.ad ∧
          TypeQuotientTransport X.typeQuotient Y.typeQuotient s' (MonoidHom.id _) ∧
          Y.Coefficients (F := F) ∧
          ∀ (h : n = 6)
            (C : MarkedFibre M F) (C' : MarkedFibre M' F)
            (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
            (l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned)
            (Q : AdjointQuotient C.realization.pinned.pair.G)
            (Q' : AdjointQuotient C'.realization.pinned.pair.G),
            Y.OuterE6Coefficients (h ▸ b) (h ▸ b') C C' (l := l) (l' := l') (Q := Q) (Q' := Q')


open AdjointCocharacters (coordinateHopf)
open ExceptionalMarkedRootDescent (HopfPoints coordinatePointEquiv pinnedMarkedPoint pinnedDiagram)

/-- The given pinned ramified reference, with its split marking over the
base field and its actual descended group, Borel and torus. -/
structure RamifiedReference (F L : Type u) [Field F] [Field L] [Algebra F L]
    {D : BasedRootDatum.{u}} (M : Model D) where
  fibre : MarkedFibre M F
  pin : Aut fibre.realization.attached.toBased ≃* Aut fibre.realization.pinned
  adjoint : AdjointQuotient fibre.realization.pinned.pair.G
  sequence : SplitSequence fibre.realization.pinned fibre.realization.attached pin adjoint
  outer : Gal(L/F) →* Aut fibre.realization.attached.toBased
  descent : DescendedPair (l := pin) L outer

abbrev RamifiedReference.diagram {F L : Type u} [Field F] [Field L] [Algebra F L]
    {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M) (σ : Gal(L/F)) :
    BasedIso D D :=
  (markedDiagramEquiv R.fibre.realization (R.outer σ)).asIso.hom

/-- Comparison of the descended points with the split points by evaluating
the actual pinned descent over the specified field compositum. -/
def ramifiedPoint {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
    [Algebra F L] [Algebra F k] [Algebra F K] {D : BasedRootDatum.{u}} {M : Model D}
    (R : RamifiedReference F L M) (f : L →ₐ[F] K) (g : k →ₐ[F] K)
    (x : GroupPoints R.descent.group.val (CommAlgCat.of F k)) : FieldPoints M K :=
  let S := CommAlgCat.of F k
  changeRingHom M.group (integralRingMap
    (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom)
    (pinnedMarkedPoint R.fibre R.descent.data S
      ((coordinatePointEquiv R.descent.group S).symm x))

/-- An unramified coefficient extension and the ramified diagram field
form a field compositum, canonically a tensor product over the base. -/
structure DiagramCompositum (F L k : Type u) [Field F] [Field L] [Field k]
    [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (σ : Gal(L/F)) where
  field : Type u
  [fieldInstance : Field field]
  [baseAlgebra : Algebra F field]
  [leftAlgebra : Algebra L field]
  [rightAlgebra : Algebra k field]
  [leftTower : IsScalarTower F L field]
  [rightTower : IsScalarTower F k field]
  [valuation : ValuativeRel field]
  [topology : TopologicalSpace field]
  [localField : IsNonarchimedeanLocalField field]
  [leftExtension : ValuativeExtension L field]
  [rightExtension : ValuativeExtension k field]
  [rightFinite : FiniteDimensional k field]
  [rightGalois : IsGalois k field]
  tensor : (L ⊗[F] k) ≃ₐ[F] field
  left_eq (x : L) : tensor (x ⊗ₜ[F] (1 : k)) = algebraMap L field x
  right_eq (x : k) : tensor ((1 : L) ⊗ₜ[F] x) = algebraMap k field x
  degree : Module.finrank k field = 2
  diagram : Gal(field/k)
  diagram_ne : diagram ≠ 1
  diagram_extends (x : L) : diagram (algebraMap L field x) = algebraMap L field (σ x)
  coefficient : Gal(k/F) →* Gal(field/L)
  coefficient_extends (g : Gal(k/F)) (x : k) :
    coefficient g (algebraMap k field x) = algebraMap k field (g x)
  unramified : IsUnramifiedLocalExtension L field

attribute [instance] DiagramCompositum.fieldInstance DiagramCompositum.baseAlgebra
  DiagramCompositum.leftAlgebra DiagramCompositum.rightAlgebra DiagramCompositum.leftTower
  DiagramCompositum.rightTower DiagramCompositum.valuation DiagramCompositum.topology
  DiagramCompositum.localField DiagramCompositum.leftExtension DiagramCompositum.rightExtension
  DiagramCompositum.rightFinite DiagramCompositum.rightGalois

/-- The two parameter maps associated with a pair of absolute root slots
are the indicated maps, with transports of the parameter type along the
slot labels. -/
def LocalRootChart.UsesSlot {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
    {G : Type u} [Group G] {j : G →* FieldPoints M K}
    {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V] {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalRootChart (M := M) (j := j) A p) (i : D.I) (a : J)
    (e : C.parameter a →+* K) : Prop :=
  C.direction i = a ∧
  (∀ l (h : C.chart.neg l = a) (x : C.parameter a), C.negative[l] = i →
    C.chart.negMap l (h.symm ▸ x) = e x) ∧
  (∀ l (h : C.chart.pos l = a) (x : C.parameter a), C.positive[l] = i →
    C.chart.posMap l (h.symm ▸ x) = e x)

/-- The normalized dual F₄ datum on the actual invariant apartment. -/
structure FoldedApartment {D : BasedRootDatum.{u}} (τ : BasedIso D D) where
  roots : ApartmentRoots ℚ (invariantApartment D τ) FoldedRootDirection
  basepoint : invariantApartment D τ
  direction : D.I → FoldedRootDirection
  surjective : Function.Surjective direction
  orbits (i j : D.I) : direction i = direction j ↔ j = i ∨ j = τ.val.indexEquiv i
  long (i : D.I) : IsLongF4Doubled (direction i).val ↔ τ.val.indexEquiv i = i
  orthogonal (i : D.I) : τ.val.indexEquiv i ≠ i → D.datum.pairing i (τ.val.indexEquiv i) = 0
  root_value (i : D.I) (x : invariantApartment D τ) :
    roots.root (direction i) x = (foldedDepthDenominator (direction i) : ℚ) *
      (ApartmentRoots.split D.datum ℚ).root i x.val
  coroot_value (i : D.I) : (roots.coroot (direction i)).val =
    diagramAverage (diagramCocharacters τ.val) ((ApartmentRoots.split D.datum ℚ).coroot i)
  coordinates : (Fin 4 → ℚ) ≃ₗ[ℚ] invariantApartment D τ
  normalized_root (i : FoldedRootDirection) (x : Fin 4 → ℚ) :
    roots.root i (coordinates x) = ExceptionalAffineRootSystems.normalizedFoldedRoot ℚ i x
  normalized_coroot (i : FoldedRootDirection) :
    coordinates (ExceptionalAffineRootSystems.normalizedFoldedCoroot ℚ i) = roots.coroot i
  coroot_projection :
    (invariantApartment D τ).subtype '' (roots.corootLattice : Set _) =
      diagramAverage (diagramCocharacters τ.val) '' ((ApartmentRoots.split D.datum ℚ).corootLattice : Set _)
  coweight_projection :
    (invariantApartment D τ).subtype '' (roots.corootLattice : Set _) =
      diagramAverage (diagramCocharacters τ.val) '' ((ApartmentRoots.split D.datum ℚ).coweightLattice : Set _)
  affine_eq : roots.affineWeylGroup = roots.extendedAffineWeylGroup
  omega_trivial : Subsingleton (alcoveStabilizer roots (roots.alcove basepoint))

/-- The marked rational points over one coefficient level, with the
normalizer of the maximal split torus and the folded Bruhat data. -/
structure FoldedLevel {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
    [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
    (σ : Gal(L/F)) (σK : Gal(K/k)) (f : L →ₐ[F] K)
    (A : FoldedApartment (R.diagram σ)) where
  points : GroupPoints R.descent.group.val (CommAlgCat.of F k) →* FieldPoints M K
  point_eq (g) : points g = ramifiedPoint R f (IsScalarTower.toAlgHom F k K) g
  fixed_points (v : GroupPoints R.fibre.realization.pinned.pair.G.val (CommAlgCat.of F K)) :
    markedFibrePoint R.fibre (CommAlgCat.of F K) v ∈ points.range ↔
    pinnedCoefficientPoint R.fibre (R.pin (R.outer σ))
      ((σK.restrictScalars F : K ≃ₐ[F] K)) v = markedFibrePoint R.fibre (CommAlgCat.of F K) v
  ramification (x : k) : normalizedValuation K (algebraMap k K x) = (normalizedValuation k x) ^ 2
  same_residue : Nat.card (residue K) = Nat.card (residue k)
  comparison : LocalComparison (j := points) (Wf := fixedWeylGroup D (R.diagram σ))
    A.roots A.basepoint
  splitTorus : ClosedSubgroup R.descent.group.val
  split_subtorus : SchemeDerivedGroup.IsSubgroupOf splitTorus R.descent.torus
  maximal : Relative.MaximalSplitTori.IsMaximalSplitTorus splitTorus
  maximal_at_level : ∃ h : IsClosedImmersion ((groupBaseChange F k).map splitTorus.inclusion).hom.hom.left,
    Relative.MaximalSplitTori.IsMaximalSplitTorus (GeometricRadicals.baseChangedSubgroup k splitTorus h)
  normalizer (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    g ∈ comparison.N ↔ Normalizes splitTorus.inclusion g
  normalizer_torus (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    g ∈ comparison.N ↔ Normalizes R.descent.torus.inclusion g
  torus_points (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    g ∈ comparison.localIwahori.normalizer.torus ↔ SchemeDerivedGroup.FactorsThrough R.descent.torus g
  finite_labels : comparison.FiniteLabels (fixedWeylGroup D (R.diagram σ)).subtype
  directions : comparison.chart.direction = A.direction
  singleton (i : D.I) (h : (R.diagram σ).val.indexEquiv i = i) :
    ∃ e : comparison.chart.parameter (A.direction i) ≃+* k,
      comparison.chart.UsesSlot i (A.direction i) ((algebraMap k K).comp e.toRingHom) ∧
      ∀ x, comparison.chart.value (A.direction i) x = normalizedValuation k (e x)
  pair (a : FoldedRootDirection) (h : ¬IsLongF4Doubled a.val) :
    ∃ i : D.I, A.direction i = a ∧
    ∃ e : comparison.chart.parameter a ≃+* K,
      comparison.chart.UsesSlot i a e.toRingHom ∧
      comparison.chart.UsesSlot ((R.diagram σ).val.indexEquiv i) a (σK.toRingHom.comp e.toRingHom) ∧
      ∀ x, comparison.chart.value a x = normalizedValuation K (e x)
  affine (n : comparison.N) (x : invariantApartment D (R.diagram σ)) :
    let N := comparison.localIwahori.normalizer
    (comparison.affine n x).val =
      (N.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
        ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd)
  translations :
    let N := comparison.localIwahori.normalizer
    Set.range (fun t : N.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) =
      (invariantApartment D (R.diagram σ)).subtype '' (A.roots.corootLattice : Set _)
  range : comparison.affine.range = A.roots.affineWeylGroup
  bruhat : comparison.Bruhat (Nat.card (residue k))
  typeQuotient : comparison.TypeQuotient



/-- Change of scalars on the actual point functor of the descended group. -/
abbrev coefficientPoints {F k K : Type u} [Field F] [Field k] [Field K]
    [Algebra F k] [Algebra F K] (G : GroupScheme F) (f : k →ₐ[F] K) :
    GroupPoints G (CommAlgCat.of F k) →* GroupPoints G (CommAlgCat.of F K) :=
  (((groupPointsFunctor F).obj G).map (CommAlgCat.ofHom f)).hom

/-- The field-coefficient action on the descended rational group over an
unramified field, compared inside the marked split points over the
compositum with the lift of the automorphism fixing the diagram field. -/
def FoldedLevel.Coefficients
    {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} (T : DiagramCompositum F L k σ) {A : FoldedApartment (R.diagram σ)}
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A) : Prop :=
  ∃ a : Gal(k/F) →* MulAut (GroupPoints R.descent.group.val (CommAlgCat.of F k)),
    (∀ g x, a g x = coefficientPoints R.descent.group.val g.toAlgHom x) ∧
    (∀ g x, X.points (a g x) = scalarPoints M (T.coefficient g).toRingHom (X.points x)) ∧
    ∀ g, AutomorphismComparison X.comparison (a g) 1 ∧
      TypeQuotientTransport X.typeQuotient X.typeQuotient (a g).toMonoidHom (MonoidHom.id _)

/-- The ramified pinned affine comparison for both isogeny types, with
compatible marked points over every finite unramified level. -/
def RamifiedAffineBruhatComparison : Prop :=
  ∀ (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    (σ : Gal(L/F)), Module.finrank F L = 2 → σ ≠ 1 → 1 < ramificationIndex F L →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E} (c : MarkedCentralCover M M')
      (b : Fin 6 ≃ D.base.support) (b' : Fin 6 ≃ E.base.support),
    ExceptionalNumbering D 6 b → ExceptionalNumbering E 6 b' →
    D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
    ∀ (R : RamifiedReference F L M) (R' : RamifiedReference F L M'),
    let τ := R.diagram σ
    let τ' := R'.diagram σ
    (∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) →
    (∀ i, τ'.val.indexEquiv (b' i) = b' (e6Partner i)) →
    (∀ i, c.rootEquiv (τ.val.indexEquiv i) = τ'.val.indexEquiv (c.rootEquiv i)) →
    ∃ (A : FoldedApartment τ) (A' : FoldedApartment τ')
      (e : invariantApartment D τ ≃ₗ[ℚ] invariantApartment E τ')
      (φ : R.descent.group.val ⟶ R'.descent.group.val)
      (X : FoldedLevel R σ σ (AlgHom.id F L) A)
      (X' : FoldedLevel R' σ σ (AlgHom.id F L) A'),
      (∀ x, (e x).val = c.pushCocharacter.baseChange ℚ x.val) ∧ A'.basepoint = e A.basepoint ∧
      CentralIsogenies.IsCentralIsogeny φ ∧
      CentralComparison c (pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F F))))
        X.comparison X'.comparison e ∧
      ∀ (k : Type u) [Field k] [Algebra F k] [FiniteDimensional F k]
        [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeExtension F k],
        IsUnramifiedLocalExtension F k →
        ∃ (T : DiagramCompositum F L k σ)
          (Y : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
          (Y' : FoldedLevel R' σ T.diagram (IsScalarTower.toAlgHom F L T.field) A'),
          let s := coefficientPoints R.descent.group.val (Algebra.ofId F k)
          let s' := coefficientPoints R'.descent.group.val (Algebra.ofId F k)
          CentralComparison c (pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F k))))
            Y.comparison Y'.comparison e ∧
          ScalarComparison (algebraMap L T.field) s X.comparison Y.comparison ∧
          ScalarComparison (algebraMap L T.field) s' X'.comparison Y'.comparison ∧
          TypeQuotientTransport X'.typeQuotient Y'.typeQuotient s' (MonoidHom.id _) ∧
          Y.Coefficients T ∧ Y'.Coefficients T

end
end LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat
