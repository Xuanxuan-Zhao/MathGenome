import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding

/-! Single-level scaling and signed root layers for the marked ramified face. -/

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalLocalFaceCoordinates
open CategoryTheory ValuativeRel WithZero
open scoped CategoryTheory.MonObj TensorProduct WithZero
open ExceptionalAffineBruhat (FieldPoints scalarPoints RamifiedReference DiagramCompositum FoldedApartment FoldedLevel)
open ExceptionalAffineBuilding (Building Weights rationalPoint simplexPoint)
open ExceptionalIwahoriCongruence (integralRing)
open ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open ExceptionalValuedTorusNormalizer (invariantApartment valuationRingInclusion)
open IntegralSemisimpleModel (Model integerAlgebra IntegralPoints integralPointFunctor torusPoint cocharacter)
open Pinning (BasedRootDatum)

universe u

attribute [local instance] integerAlgebra ExceptionalLocalRootCoordinates.canonicalExtension

noncomputable section

open AlgebraicGeometry IsLocalRing
open scoped Classical Pointwise
open AdjointRepresentation (GroupPoints)
open ExceptionalAffineBruhat (coefficientPoints residue IsUnramifiedLocalExtension)
open ExceptionalAffineBuilding (IsBarycenter cotype parahoric standardWallSubgroup)
open ExceptionalAffineRootSystems (FoldedRootDirection IsLongF4Doubled threshold)
open ExceptionalIwahoriCongruence (CellValues cellValue changeRingHom integralRingMap)
open ExceptionalIwahoriImageComparison (residueReduction)
open ExceptionalMarkedRootDescent (wallMatrix markedWeylWord)
open IntegralRootRelations (upper lower)
open IntegralSemisimpleModel (Integers TorusValues fibre forgetFibrePoint)
open OrderedRootProducts (Enumerates)

local notation "Oᵥ[" K "]" => Valuation.valuationSubring (valuation K)
local notation "kᵥ[" K "]" => ExceptionalAffineBruhat.residue K

/-- The actual maps on the valuation ring and residue field under an
inclusion or coefficient automorphism of valued fields. -/
structure ValuedFieldMap {K E : Type u} [Field K] [Field E] [ValuativeRel K]
    [ValuativeRel E] (f : K →+* E) where
  integers : Oᵥ[K] →+* Oᵥ[E]
  [isLocal : IsLocalHom integers]
  field_eq (z : Oᵥ[K]) : (integers z : E) = f (z : K)

attribute [instance] ValuedFieldMap.isLocal

abbrev ValuedFieldMap.residue {K E : Type u} [Field K] [Field E] [ValuativeRel K]
    [ValuativeRel E] {f : K →+* E} (e : ValuedFieldMap f) : kᵥ[K] →+* kᵥ[E] :=
  letI := e.isLocal
  ResidueField.map e.integers


/-- The marked comparisons at the chosen finite unramified coefficient level. -/
structure MarkedLevel {F L : Type u} [Field F] [Field L] [Algebra F L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M) (σ : Gal(L/F))
    (A : FoldedApartment (R.diagram σ)) (k : Type u) [Field k] [Algebra F k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] where
  compositum : DiagramCompositum F L k σ
  folded : FoldedLevel R σ compositum.diagram (IsScalarTower.toAlgHom F L compositum.field) A
  building : Building folded.comparison
  coefficients : folded.Coefficients compositum

section Scaling

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}

abbrev MarkedLevel.parahoric (X : MarkedLevel R σ A k) (J : Set (A.roots.SimpleWall A.basepoint)) :=
  ExceptionalAffineBuilding.parahoric X.folded.comparison J

abbrev MarkedLevel.wallLift (X : MarkedLevel R σ A k) (a : A.roots.SimpleWall A.basepoint) :
    GroupPoints R.descent.group.val (CommAlgCat.of F k) :=
  X.folded.comparison.lift (X.folded.comparison.coxeter.coxeter.simple a)

/-- The points in one signed marked root layer, using the actual chart
and setting all other coordinates to the identity. -/
def MarkedLevel.rootLayer (X : MarkedLevel R σ A k) (a : FoldedRootDirection × ℤ) :
    Set (GroupPoints R.descent.group.val (CommAlgCat.of F k)) :=
  let C := X.folded.comparison.chart
  {g | ∃ (t : C.chart.torus) (z : C.parameter a.1), t.val = 1 ∧
    C.value a.1 z ≤ exp (-a.2) ∧
    X.folded.points g = cellValue M.toIntegralMarking (integralRing X.compositum.field)
      C.negative C.positive (C.chart.coordinates t (Function.update (fun _ => 0) a.1 z))}


/-- Points of one signed marked layer with parameter of exactly the specified
depth. -/
def MarkedLevel.exactRootLayer (X : MarkedLevel R σ A k) (a : FoldedRootDirection × ℤ) :
    Set (GroupPoints R.descent.group.val (CommAlgCat.of F k)) :=
  let C := X.folded.comparison.chart
  {g | ∃ (t : C.chart.torus) (z : C.parameter a.1), t.val = 1 ∧
    C.value a.1 z = exp (-a.2) ∧
    X.folded.points g = cellValue M.toIntegralMarking (integralRing X.compositum.field)
      C.negative C.positive (C.chart.coordinates t (Function.update (fun _ => 0) a.1 z))}

/-- The finite valued auxiliary field is supplied, with its chosen
uniformizer root and unchanged residue field. -/
structure AuxiliaryExtension (K : Type u) [Field K] [ValuativeRel K]
    (d : ℕ) (π : K) where
  field : Type u
  [fieldInstance : Field field]
  [algebra : Algebra K field]
  [valuative : ValuativeRel field]
  [topology : TopologicalSpace field]
  [localField : IsNonarchimedeanLocalField field]
  [valuativeExtension : ValuativeExtension K field]
  [finite : FiniteDimensional K field]
  root : fieldˣ
  power : (root : field) ^ d = algebraMap K field π
  residue_bijective : Function.Bijective (residueMap K field)

attribute [instance] AuxiliaryExtension.fieldInstance AuxiliaryExtension.algebra
  AuxiliaryExtension.valuative AuxiliaryExtension.topology AuxiliaryExtension.localField
  AuxiliaryExtension.valuativeExtension AuxiliaryExtension.finite

abbrev integralPointsInField (M : Model D) (K : Type u) [Field K] [ValuativeRel K] :=
  changeRingHom M.group (valuationRingInclusion K)

abbrev reduceIntegralPoints (M : Model D) (K : Type u) [Field K] [ValuativeRel K] :=
  changeRingHom M.group (residueReduction K)


/-- Scalar extension of the required homomorphism is conjugation by the
specified cocharacter value after applying the marked point comparison. -/
def scalingConjugation (X : MarkedLevel R σ A k) (π : Lˣ) (d : ℕ) (y : D.Y)
    (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L))) :
    GroupPoints R.descent.group.val (CommAlgCat.of F k) →* FieldPoints M U.field :=
  let E := U.field
  let t : FieldPoints M E :=
    torusPoint D (integralRing E) (cocharacter D y (integralRing E) U.root) ≫ M.torus.hom.hom
  (MulAut.conj t).toMonoidHom.comp
    ((scalarPoints M (algebraMap X.compositum.field E)).comp X.folded.points)

structure ScaledParahoric (X : MarkedLevel R σ A k) (J : Set (A.roots.SimpleWall A.basepoint))
    (π : Lˣ) (d : ℕ) (y : D.Y)
    (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L))) where
  integral : X.parahoric J →* IntegralPoints M.group (integralRing Oᵥ[U.field])
  conjugation : (integralPointsInField M U.field).comp integral =
    (scalingConjugation X π d y U).comp (X.parahoric J).subtype
  unique_integral (f : X.parahoric J →* IntegralPoints M.group (integralRing Oᵥ[U.field]))
      (hf : (integralPointsInField M U.field).comp f =
        (scalingConjugation X π d y U).comp (X.parahoric J).subtype) : f = integral
  coefficient_mem (s : Gal(k/F)) (g : X.parahoric J) :
    coefficientPoints R.descent.group.val s.toAlgHom g.val ∈ X.parahoric J
  equivariant (s : Gal(k/F)) (b : U.field ≃+* U.field) (b₀ : ValuedFieldMap b.toRingHom)
      (hb : ∀ z : X.compositum.field,
        b (algebraMap X.compositum.field U.field z) =
          algebraMap X.compositum.field U.field (X.compositum.coefficient s z))
      (hξ : b (U.root : U.field) = (U.root : U.field)) (g : X.parahoric J) :
    let g' : X.parahoric J :=
      ⟨coefficientPoints R.descent.group.val s.toAlgHom g.val, coefficient_mem s g⟩
    integral g' = changeRingHom M.group (integralRingMap b₀.integers) (integral g) ∧
    reduceIntegralPoints M U.field (integral g') =
      scalarPoints M b₀.residue (reduceIntegralPoints M U.field (integral g))

abbrev ScaledParahoric.reduction {X : MarkedLevel R σ A k}
    {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
    {U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L))}
    (P : ScaledParahoric X J π d y U) :
    X.parahoric J →* FieldPoints M kᵥ[U.field] :=
  (reduceIntegralPoints M U.field).comp P.integral

abbrev MarkedLevel.ParametersAtDepth (X : MarkedLevel R σ A k)
    (a : FoldedRootDirection × ℤ) :=
  {z : X.folded.comparison.chart.parameter a.1 //
    X.folded.comparison.chart.value a.1 z ≤ exp (-a.2)}

/-- Normalized residue parameters in a fixed or paired direction. The factor
for a fixed root is the residue of the indicated ratio of uniformizers. In
a pair, the conjugate slot uses the same leading coefficient, with the
additional residue of the conjugate-uniformizer ratio. The marking units
are applied separately to the individual slots of the ordered chart. -/
structure LeadingCoefficients (X : MarkedLevel R σ A k) (ϖ : Fˣ) (π : Lˣ)
    (a : FoldedRootDirection × ℤ) where
  leading : X.ParametersAtDepth a → kᵥ[X.compositum.field]
  surjective : Function.Surjective leading
  factor : D.I → kᵥ[X.compositum.field]ˣ
  normalized :
    let T := X.compositum
    let C := X.folded.comparison.chart
    let πK := algebraMap L T.field (π : L)
    let ϖk := algebraMap F k (ϖ : F)
    if IsLongF4Doubled a.1.val then
      ∃ (i : D.I) (e : C.parameter a.1 ≃+* k) (ratio : Oᵥ[L]ˣ),
        A.direction i = a.1 ∧ C.UsesSlot i a.1 ((algebraMap k T.field).comp e.toRingHom) ∧
        algebraMap F L (ϖ : F) = ((ratio : Oᵥ[L]) : L) * (π : L) ^ 2 ∧
        factor i = (Units.map ((residueMap L T.field).comp
          (IsLocalRing.residue Oᵥ[L])).toMonoidHom ratio) ^ a.2 ∧
        ∀ z : X.ParametersAtDepth a, ∃ b : Oᵥ[k],
          e z.val = ϖk ^ a.2 * (b : k) ∧
          leading z = residueMap k T.field (IsLocalRing.residue Oᵥ[k] b)
    else
      ∃ (i : D.I) (e : C.parameter a.1 ≃+* T.field) (ε : Oᵥ[L]ˣ),
        A.direction i = a.1 ∧
        C.UsesSlot i a.1 e.toRingHom ∧
        C.UsesSlot ((R.diagram σ).val.indexEquiv i) a.1 (T.diagram.toRingHom.comp e.toRingHom) ∧
        σ (π : L) = ((ε : Oᵥ[L]) : L) * (π : L) ∧
        factor i = 1 ∧
        factor ((R.diagram σ).val.indexEquiv i) =
          (Units.map ((residueMap L T.field).comp (IsLocalRing.residue Oᵥ[L])).toMonoidHom ε) ^ a.2 ∧
        ∀ z : X.ParametersAtDepth a, ∃ b : Oᵥ[T.field],
          e z.val = πK ^ a.2 * (b : T.field) ∧
          leading z = IsLocalRing.residue Oᵥ[T.field] b

/-- The condition on a unit torus tuple after ramified reduction. On the
permuted character basis it sets paired entries equal. -/
def InvariantTorusValues (τ : Pinning.BasedIso D D) (K : Type u) [Field K] :=
  {t : TorusValues D (integralRing K) //
    ∀ χ : D.X, t (Multiplicative.ofAdd (τ.val.weightEquiv χ)) = t (Multiplicative.ofAdd χ)}

variable {X : MarkedLevel R σ A k}

variable {X : MarkedLevel R σ A k}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  {U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L))}
  (P : ScaledParahoric X J π d y U)

/-- Reduction on a subset of the actual face subgroup. -/
def ScaledParahoric.image (S : Set (GroupPoints R.descent.group.val (CommAlgCat.of F k))) :
    Set (FieldPoints M kᵥ[U.field]) :=
  P.reduction '' ((↑) ⁻¹' S : Set (X.parahoric J))

abbrev MarkedLevel.iwahoriDepth (_X : MarkedLevel R σ A k) (a : FoldedRootDirection) :
    FoldedRootDirection × ℤ :=
  (a, threshold (A.roots.root a A.basepoint))

/-- The exact marked absolute coordinates obtained from one leading
coefficient per relative root direction, retaining the two ordered lists
of the marked Iwahori chart. -/
def iwahoriResidueCell (X : MarkedLevel R σ A k) (ϖ : Fˣ) (π : Lˣ)
    (x : invariantApartment D (R.diagram σ)) (b : ∀ a, LeadingCoefficients X ϖ π a)
    {K : Type u} [Field K] (e : kᵥ[X.compositum.field] →+* K)
    (t : InvariantTorusValues (R.diagram σ) K) (z : FoldedRootDirection → K) :
    FieldPoints M K :=
  let C := X.folded.comparison.chart
  let coordinate := fun (i : D.I) (unit : Integers.{u}ˣ) =>
    let a := X.iwahoriDepth (A.direction i)
    if A.roots.wallValue a x = 0 then
      algebraMap Integers.{u} K (unit : Integers.{u}) * e ((b a).factor i) * z a.1
    else 0
  cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
    ((fun n => coordinate C.negative[n] (C.chart.negUnit n)), t.val,
      (fun n => coordinate C.positive[n] (C.chart.posUnit n)))

/-- The marked line at exact scaled depth zero, with its common parameter
used in all the slots of the indicated relative direction. -/
def rootResiduePoint (X : MarkedLevel R σ A k) (ϖ : Fˣ) (π : Lˣ)
    (a : FoldedRootDirection × ℤ) (b : LeadingCoefficients X ϖ π a)
    {K : Type u} [Field K] (e : kᵥ[X.compositum.field] →+* K) (z : K) : FieldPoints M K :=
  let C := X.folded.comparison.chart
  let coordinate := fun (i : D.I) (unit : Integers.{u}ˣ) =>
    if A.direction i = a.1 then algebraMap Integers.{u} K (unit : Integers.{u}) *
      e (b.factor i) * z else 0
  cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
    ((fun n => coordinate C.negative[n] (C.chart.negUnit n)), 1,
      (fun n => coordinate C.positive[n] (C.chart.posUnit n)))

/-- A rank-one point map at the parameter field of the indicated simple wall. -/
abbrev MarkedLevel.WallRankOneMap (X : MarkedLevel R σ A k)
    (a : A.roots.SimpleWall A.basepoint) :=
  Matrix.SpecialLinearGroup (Fin 2) (X.folded.comparison.chart.parameter a.val.1) →*
    GroupPoints R.descent.group.val (CommAlgCat.of F k)

/-- The split image of the rank-one map is the product of the marked
simple rank-one maps in the root orbit, transported by a marked Weyl word. -/
def IsMarkedWallRankOne (X : MarkedLevel R σ A k) (a : A.roots.SimpleWall A.basepoint)
    (r : X.WallRankOneMap a) : Prop :=
  let K := X.compositum.field
  let S := integralRing K
  let C := X.folded.comparison.chart
  let P := C.parameter a.val.1
  ∃ (word : List D.I) (orbit : List (D.base.support × (P →+* K))),
    let w := (word.map (RootPairing.weylGroup.ofIdx D.datum)).prod
    let roots := orbit.map (fun b => w.val.indexEquiv b.1.val)
    (∀ i ∈ word, i ∈ D.base.support) ∧
    roots.Nodup ∧
    (∀ i, C.direction i = a.val.1 ↔ i ∈ roots) ∧
    ∀ z, X.folded.points (r z) =
      let m := markedWeylWord M.toIntegralMarking S word
      m * (orbit.map (fun b => (show FieldPoints M K from
        (M.rankOne b.1).app S (Matrix.SpecialLinearGroup.map b.2 z)))).prod * m⁻¹

/-- The two signed layers use the same transported rank-one map as the
marked lift. Their levels are opposite and the lift conjugates one to the other. -/
def SignedWallLayers (X : MarkedLevel R σ A k) (J : Set (A.roots.SimpleWall A.basepoint))
    (a : A.roots.SimpleWall A.basepoint) (r : X.WallRankOneMap a)
    (t : (X.folded.comparison.chart.parameter a.val.1)ˣ) : Prop :=
  let C := X.folded.comparison.chart
  let n := X.wallLift a
  let plus := X.rootLayer a.val
  let minus := X.rootLayer (A.roots.opposite a.val)
  IsMarkedWallRankOne X a r ∧
    C.value a.val.1 (t : C.parameter a.val.1) = exp (-a.val.2) ∧
    n = r (wallMatrix t) ∧
    plus = (fun z : C.parameter a.val.1 => r (upper z)) '' {z |
      C.value a.val.1 z ≤ exp (-a.val.2)} ∧
    minus = (fun z : C.parameter a.val.1 => r (lower z)) '' {z |
      C.value a.val.1 z ≤ exp a.val.2} ∧
    plus ⊆ X.folded.comparison.I ∧ plus ⊆ X.parahoric J ∧ minus ⊆ X.parahoric J ∧
    (∀ z : C.parameter a.val.1, n * r (upper z) * n⁻¹ =
      r (lower (-(↑t⁻¹ : C.parameter a.val.1) ^ 2 * z))) ∧
    (fun g => n * g * n⁻¹) '' plus = minus ∧
    r (upper (-(t : C.parameter a.val.1))) ∈ plus ∧
    r (lower (↑t⁻¹ : C.parameter a.val.1)) ∈ minus ∧
    n = r (upper (-(t : C.parameter a.val.1))) * r (lower (↑t⁻¹ : C.parameter a.val.1)) *
      r (upper (-(t : C.parameter a.val.1))) ∧
    r (upper (-(t : C.parameter a.val.1))) ∈ X.exactRootLayer a.val ∧
    r (lower (↑t⁻¹ : C.parameter a.val.1)) ∈ X.exactRootLayer (A.roots.opposite a.val)

/-- The reduced wall lift is the product of the reductions of its three
marked factors in the actual signed layers. -/
def ScaledParahoric.ReducesWallWord (P : ScaledParahoric X J π d y U)
    (a : A.roots.SimpleWall A.basepoint) (r : X.WallRankOneMap a)
    (t : (X.folded.comparison.chart.parameter a.val.1)ˣ) : Prop :=
  let C := X.folded.comparison.chart
  ∃ p q : X.parahoric J,
    p.val = r (upper (-(t : C.parameter a.val.1))) ∧
    q.val = r (lower (↑t⁻¹ : C.parameter a.val.1)) ∧
    p.val ∈ X.rootLayer a.val ∧ q.val ∈ X.rootLayer (A.roots.opposite a.val) ∧
    ∃ n : X.parahoric J, n.val = X.wallLift a ∧ n.val = r (wallMatrix t) ∧
      P.reduction n = P.reduction p * P.reduction q * P.reduction p

/-- The reduction formulas are image equalities, so every tuple of
residue parameters in the formulas lifts. -/
structure LocalReductionCoordinates (ϖ : Fˣ) (x : invariantApartment D (R.diagram σ)) where
  leading : ∀ a, LeadingCoefficients X ϖ π a
  iwahori :
    P.image (X.folded.comparison.I : Set _) =
      Set.range (fun b : InvariantTorusValues (R.diagram σ) kᵥ[U.field] ×
        (FoldedRootDirection → kᵥ[U.field]) =>
          iwahoriResidueCell X ϖ π x leading (residueMap X.compositum.field U.field) b.1 b.2)
  torus :
    P.image (X.folded.comparison.T₀ : Set _) =
      Set.range (fun t : InvariantTorusValues (R.diagram σ) kᵥ[X.compositum.field] =>
        scalarPoints M (residueMap X.compositum.field U.field)
          (torusPoint D (integralRing kᵥ[X.compositum.field]) t.val ≫ M.torus.hom.hom))
  wall (a : A.roots.SimpleWall A.basepoint) (ha : a ∈ J) :
    ∃ (r : X.WallRankOneMap a) (t : (X.folded.comparison.chart.parameter a.val.1)ˣ),
      SignedWallLayers X J a r t ∧ P.ReducesWallWord a r t ∧
      ∀ b ∈ ({a.val, A.roots.opposite a.val} : Set (FoldedRootDirection × ℤ)),
        A.roots.wallValue b x = 0 ∧
        P.image (X.rootLayer b) =
          Set.range (rootResiduePoint X ϖ π b (leading b) (residueMap X.compositum.field U.field))


end Scaling

/-- Single-level scaled integral coordinates at the chosen standard rational
barycenter of the actual adjoint ramified outer group. -/
def RamifiedLocalFaceCoordinates : Prop :=
  ∀ {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeExtension F k]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F k]
    (σ : Gal(L/F)), Module.finrank F L = 2 → σ ≠ 1 →
    1 < ExceptionalLocalRootCoordinates.ramificationIndex F L → IsUnramifiedLocalExtension F k →
    ∀ {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
      (numbering : Fin 6 ≃ D.base.support),
    ExceptionalAffineBruhat.ExceptionalNumbering D 6 numbering →
    D.datum.rootSpan ℤ = ⊤ →
    (∀ i, (R.diagram σ).val.indexEquiv (numbering i) =
      numbering (ExceptionalAffineRootSystems.e6Partner i)) →
    ∀ (A : FoldedApartment (R.diagram σ)) (X : MarkedLevel R σ A k)
      (t : Weights (A.roots.SimpleWall A.basepoint)) (x : invariantApartment D (R.diagram σ)),
    IsBarycenter (cotype t) t →
    rationalPoint X.building.realization.coordinates x =
      simplexPoint X.building.realization.coordinates X.building.realization.vertex t →
    ∀ (ϖ : Fˣ) (π : Lˣ), normalizedValuation F (ϖ : F) = exp (-1) →
    normalizedValuation L (π : L) = exp (-1) →
    ∀ (d : ℕ) (y : D.Y), 0 < d → (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y →
    ∀ (U : AuxiliaryExtension X.compositum.field d (algebraMap L X.compositum.field (π : L))),
    let J := cotype t
    J = {a | A.roots.wallValue a.val x = 0} ∧
      ∃ P : ScaledParahoric X J π d y U, Nonempty (LocalReductionCoordinates P ϖ x)

end

end LinearAlgebraicGroups.Specs.RamifiedExceptionalLocalFaceCoordinates
