import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusOrderedConvolution
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open scoped Classical MonoidalCategory BraidedCategory

namespace RepTheorySurvey.Geometric.TorusFusionSpecs

open Analytic LatticeModelSpecs TorusPerverseSpecs TorusOrderedConvolutionSpecs
open private skyscrapersProjection from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusOrderedConvolution

abbrev Marked := ℂ × ℂ
abbrev UniversalPolynomial := MvPolynomial (Fin 3) ℂ

/-- The coordinates on the universal curve are a, b and z, in that order. -/
def firstFactor : UniversalPolynomial := MvPolynomial.X 2 - MvPolynomial.X 0
def secondFactor : UniversalPolynomial := MvPolynomial.X 2 - MvPolynomial.X 1
def markedDivisor : UniversalPolynomial := firstFactor * secondFactor

/-- Coordinate ring of the complement of both marked graphs over the whole plane. -/
abbrev PuncturedCurve := Localization (Submonoid.powers markedDivisor)

def firstUnit : PuncturedCurveˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := PuncturedCurve) markedDivisor
    (dvd_mul_right firstFactor secondFactor)).unit

def secondUnit : PuncturedCurveˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := PuncturedCurve) markedDivisor
    (dvd_mul_left secondFactor firstFactor)).unit

/-- The two successive transition functions in the punctured trivialization. -/
def firstTransition {r : ℕ} (a : Labels r) (i : Fin r) : PuncturedCurveˣ :=
  firstUnit ^ a i

def secondTransition {r : ℕ} (b : Labels r) (i : Fin r) : PuncturedCurveˣ :=
  secondUnit ^ b i

def localPolynomial (p : Marked) (x : ℂ) : UniversalPolynomial →+* O :=
  (MvPolynomial.aeval ![PowerSeries.C p.1, PowerSeries.C p.2,
    t + PowerSeries.C x]).toRingHom

theorem localParameter_ne_zero (x a : ℂ) : t + PowerSeries.C (x - a) ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff 1) h
  simp [t, PowerSeries.coeff_one_X] at hc

private theorem localPolynomial_divisor (p : Marked) (x : ℂ) :
    localPolynomial p x markedDivisor =
      (t + PowerSeries.C (x - p.1)) * (t + PowerSeries.C (x - p.2)) := by
  simp [localPolynomial, markedDivisor, firstFactor, secondFactor, sub_eq_add_neg, add_assoc]

/-- Taking the Laurent expansion at z = x + t after fixing the two marked points. -/
def localExpansion (p : Marked) (x : ℂ) : PuncturedCurve →+* K :=
  IsLocalization.Away.lift (g := inclusion.comp (localPolynomial p x)) markedDivisor (by
    apply isUnit_iff_ne_zero.mpr
    change inclusion (localPolynomial p x markedDivisor) ≠ 0
    rw [localPolynomial_divisor, map_mul]
    exact mul_ne_zero
      (fun h ↦ localParameter_ne_zero x p.1 (HahnSeries.ofPowerSeries_injective (h.trans (map_zero inclusion).symm)))
      (fun h ↦ localParameter_ne_zero x p.2 (HahnSeries.ofPowerSeries_injective (h.trans (map_zero inclusion).symm))))

variable {r : ℕ}

def firstLoop (p : Marked) (x : ℂ) (a : Labels r) : Loops r :=
  fun i ↦ Units.map (localExpansion p x).toMonoidHom (firstTransition a i)

def secondLoop (p : Marked) (x : ℂ) (b : Labels r) : Loops r :=
  fun i ↦ Units.map (localExpansion p x).toMonoidHom (secondTransition b i)

def intermediateLattice (p : Marked) (x : ℂ) (a : Labels r) : TorusLattice r :=
  firstLoop p x a • (fun _ : Fin r ↦ standardLattice 1)

def terminalLattice (p : Marked) (x : ℂ) (a b : Labels r) : TorusLattice r :=
  (firstLoop p x a * secondLoop p x b) • (fun _ : Fin r ↦ standardLattice 1)

/-- The local factorization and its identification with the actual twisted product
at the collision. The two local loops are the expansions of the universal units. -/
structure LocalGeometry (D : OrderedGeometry r) : Prop where
  ownMark : ∀ (p : Marked) (a b : Labels r),
    firstLoop p p.1 a = torusMonomial r a ∧ secondLoop p p.2 b = torusMonomial r b
  positiveElsewhere : ∀ (p : Marked) (x : ℂ) (a b : Labels r),
    (x ≠ p.1 → firstLoop p x a ∈ PositiveTorus r) ∧
    (x ≠ p.2 → secondLoop p x b ∈ PositiveTorus r)
  factorization : ∀ (p : Marked) (a b : Labels r), p.1 ≠ p.2 →
    intermediateLattice p p.1 a = monomialPoint r a ∧
    intermediateLattice p p.2 a = monomialPoint r 0 ∧
    terminalLattice p p.1 a b = monomialPoint r a ∧
    terminalLattice p p.2 a b = monomialPoint r b
  diagonal : ∀ (x : ℂ) (a b : Labels r),
    let second := secondLoop (x, x) x b • (fun _ : Fin r ↦ standardLattice 1)
    let ordered := D.wholeMk (firstLoop (x, x) x a) second
    ordered = D.wholePair a b ∧
    D.terminal Set.univ Set.univ ordered = terminalLattice (x, x) x a b ∧
    terminalLattice (x, x) x a b = monomialPoint r (a + b)

def Fits (N : ℕ) (A : Set (Labels r)) : Prop :=
  ∀ a ∈ A, ∀ i, -(N : ℤ) ≤ a i ∧ a i ≤ N

/-- Clearing the pole at a by the common denominator (z-a)^N. -/
def intermediatePolynomial (N : ℕ) (p : Marked) (a : Labels r) (i : Fin r) : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C p.1) ^ ((N : ℤ) + a i).toNat

/-- Clearing poles by the common denominator ((z-a)(z-b))^N. -/
def terminalPolynomial (N : ℕ) (p : Marked) (a b : Labels r) (i : Fin r) : Polynomial ℂ :=
  intermediatePolynomial N p a i *
    (Polynomial.X - Polynomial.C p.2) ^ ((N : ℤ) + b i).toNat

def sheetSpace (A B : Set (Labels r)) : TopCat.{0} :=
  TopCat.of (Marked × OrderedGeometry.labelSpace A B)

def sectionPoint {A B : Set (Labels r)} (p : Marked) (a : A) (b : B) : sheetSpace A B :=
  (p, a, b)

def sectionMap {A B : Set (Labels r)} (a : A) (b : B) :
    TopCat.of Marked ⟶ sheetSpace A B :=
  @TopCat.ofHom _ _ _ (sheetSpace A B).str
    ⟨fun p ↦ sectionPoint p a b, continuous_id.prodMk continuous_const⟩

abbrev BoundedCoefficients (r N : ℕ) := Fin r → Fin (4 * N + 1) → ℂ

def intermediateCoefficients (N : ℕ) (p : Marked) (a : Labels r) :
    BoundedCoefficients r N :=
  fun i j ↦ (intermediatePolynomial N p a i).coeff j

def terminalCoefficients (N : ℕ) (p : Marked) (a b : Labels r) :
    BoundedCoefficients r N :=
  fun i j ↦ (terminalPolynomial N p a b i).coeff j

def orderedPlot (N : ℕ) (A B : Set (Labels r)) (z : sheetSpace A B) :
    Marked × (BoundedCoefficients r N × BoundedCoefficients r N) :=
  (z.1, intermediateCoefficients N z.1 z.2.1.val,
    terminalCoefficients N z.1 z.2.1.val z.2.2.val)

def terminalPlot (N : ℕ) (A B : Set (Labels r)) (z : sheetSpace A B) :
    Marked × BoundedCoefficients r N :=
  (z.1, terminalCoefficients N z.1 z.2.1.val z.2.2.val)

/-- The finite terminal locus with the analytic topology on its polynomial
coefficient charts. Its points retain the marked pair and the terminal lattices. -/
def terminalSpace (N : ℕ) (A B : Set (Labels r)) : TopCat.{0} :=
  TopCat.of (Set.range (terminalPlot N A B))

def terminalPoint {N : ℕ} {A B : Set (Labels r)} (z : sheetSpace A B) :
    terminalSpace N A B :=
  ⟨terminalPlot N A B z, ⟨z, rfl⟩⟩

/-- On the finite locus the ordered chains have the topology of their analytic
sections. Over the diagonal several terminal sections can have the same image. -/
structure SectionGeometry (N : ℕ) (A B : Set (Labels r)) where
  fitsFirst : Fits N A
  fitsSecond : Fits N B
  orderedEmbedding : IsEmbedding (X := sheetSpace A B) (orderedPlot N A B)
  terminalContinuous : Continuous (X := sheetSpace A B) (terminalPlot N A B)
  terminalEquality : ∀ (p : Marked) (a a' : A) (b b' : B),
    terminalPoint (N := N) (sectionPoint p a b) = terminalPoint (sectionPoint p a' b') ↔
      if p.1 = p.2 then a.val + b.val = a'.val + b'.val else a = a' ∧ b = b'

def terminalMap {N : ℕ} {A B : Set (Labels r)} (G : SectionGeometry N A B) :
    sheetSpace A B ⟶ terminalSpace N A B :=
  @TopCat.ofHom _ _ (sheetSpace A B).str _
    ⟨terminalPoint, G.terminalContinuous.subtype_mk _⟩

/-- Evaluation of a polynomial in the local coordinate z = x + t. -/
def expandPolynomial (x : ℂ) (f : Polynomial ℂ) : K :=
  f.eval₂ (algebraMap ℂ K) (inclusion (t + PowerSeries.C x))

/-- The polynomial coefficients used for the finite charts are those of the
actual rational transitions, after multiplication by the fixed denominators. -/
def ClearsPoles (N : ℕ) (A B : Set (Labels r)) : Prop :=
  ∀ (p : Marked) (a : A) (b : B) (x : ℂ) (i : Fin r),
    let u := inclusion (t + PowerSeries.C (x - p.1))
    let v := inclusion (t + PowerSeries.C (x - p.2))
    expandPolynomial x (intermediatePolynomial N p a.val i) =
        u ^ N * (firstLoop p x a.val i : K) ∧
    expandPolynomial x (terminalPolynomial N p a.val b.val i) =
        (u * v) ^ N * ((firstLoop p x a.val * secondLoop p x b.val) i : K)

def swappedPoint {A B : Set (Labels r)} (z : sheetSpace A B) : sheetSpace B A :=
  sectionPoint z.1.swap z.2.2 z.2.1

/-- Exchange on the *terminal* geometry, where swapping the marked points
does not change the terminal modification. -/
structure SectionExchange {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (H : SectionGeometry N B A) where
  swap : terminalSpace N A B ≅ terminalSpace N B A
  onPoint : ∀ z : sheetSpace A B, swap.hom (terminalMap G z) = terminalMap H (swappedPoint z)
  onCoefficients : ∀ y : terminalSpace N A B, (swap.hom y).val = (y.val.1.swap, y.val.2)

def orderedProjection (D : OrderedGeometry r) (A B : Set (Labels r)) :
    sheetSpace A B ⟶ D.space A B :=
  @TopCat.ofHom _ _ (sheetSpace A B).str (D.space A B).str
    ⟨fun z ↦ (D.labels A B).symm z.2, by
      refine Continuous.comp ?_ (continuous_snd :
        Continuous (Prod.snd : Marked × OrderedGeometry.labelSpace A B → _))
      exact continuous_bot⟩

/-- The family on labelled sheets is pulled back from the actual descent
sheaf of ordered convolution. -/
def sectionCoefficients (D : OrderedGeometry r) (A B : Set (Labels r)) :
    Families r × Families r ⥤ Sheaves (sheetSpace A B) :=
  descendedExterior D A B ⋙ inverseImage (orderedProjection D A B)

def constantCoefficients (a b : Labels r) :
    Families r × Families r ⥤ Sheaves (TopCat.of Marked) :=
  exteriorAt a b ⋙ constantSheaf (Opens.grothendieckTopology (TopCat.of Marked)) Coeff.{0}

def terminalCoefficientsSheaf (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) :
    Families r × Families r ⥤ Sheaves (terminalSpace N A B) :=
  sectionCoefficients D A B ⋙ directImage (terminalMap G)

abbrev SheetValue {A B : Set (Labels r)} (V W : Families r) (z : sheetSpace A B) :=
  fiber V z.2.1.val ⊗ fiber W z.2.2.val

/-- The map to one labelled summand is the germ along that sheet. -/
def sheetGerm (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (V W : Families r) (z : sheetSpace A B) :
    (stalk (terminalMap G z)).obj ((terminalCoefficientsSheaf D G).obj (V, W)) ⟶
      SheetValue V W z := by
  let f := orderedProjection D A B
  let F := (descendedExterior D A B).obj (V, W)
  let K := (sectionCoefficients D A B).obj (V, W)
  let p := f z
  let e := skyscrapersProjection (D.space A B)
    (fun y ↦ exteriorAt (D.labels A B y).1.val (D.labels A B y).2.val) p (V, W)
  have h : D.labels A B p = z.2 := (D.labels A B).apply_symm_apply z.2
  exact TopCat.Presheaf.stalkPushforward Coeff.{0} (terminalMap G) K.obj z ≫
    (inverseImageStalkIso f F z).inv ≫ e ≫
    eqToHom (congrArg (fun q : A × B ↦ fiber V q.1.val ⊗ fiber W q.2.val) h)

abbrev IncidentSheets {N : ℕ} {A B : Set (Labels r)} (G : SectionGeometry N A B)
    (y : terminalSpace N A B) := {z : sheetSpace A B // terminalMap G z = y}

def fiberGerm (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (V W : Families r) (y : terminalSpace N A B)
    (z : IncidentSheets G y) :
    (stalk y).obj ((terminalCoefficientsSheaf D G).obj (V, W)) ⟶ SheetValue V W z.val :=
  eqToHom (congrArg (fun y ↦ (stalk y).obj ((terminalCoefficientsSheaf D G).obj (V, W)))
    z.property.symm) ≫ sheetGerm D G V W z.val

/-- Pushforward on the finite analytic locus retains all incident sheets,
including the distinct ordered labels over a colliding terminal point. -/
structure TerminalFiber (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (V W : Families r) (y : terminalSpace N A B) where
  finite : Finite (IncidentSheets G y)
  iso : (∐ fun z : IncidentSheets G y ↦ SheetValue V W z.val) ≅
    (stalk y).obj ((terminalCoefficientsSheaf D G).obj (V, W))
  sameSheet : ∀ z : IncidentSheets G y,
    Sigma.ι _ z ≫ iso.hom ≫ fiberGerm D G V W y z = 𝟙 _
  otherSheet : ∀ z w : IncidentSheets G y, z ≠ w →
    Sigma.ι _ z ≫ iso.hom ≫ fiberGerm D G V W y w = 0

abbrev ExchangeSource (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) := terminalCoefficientsSheaf D G

abbrev ExchangeTarget (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    {G : SectionGeometry N A B} {H : SectionGeometry N B A} (S : SectionExchange G H) :=
  CategoryTheory.Prod.swap _ _ ⋙ terminalCoefficientsSheaf D H ⋙ inverseImage S.swap.hom

def exchangeStalk (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    {G : SectionGeometry N A B} {H : SectionGeometry N B A} (S : SectionExchange G H)
    (τ : ExchangeSource D G ⟶ ExchangeTarget D S)
    (V W : Families r) (y : terminalSpace N A B) :
    (stalk y).obj ((terminalCoefficientsSheaf D G).obj (V, W)) ⟶
      (stalk (S.swap.hom y)).obj ((terminalCoefficientsSheaf D H).obj (W, V)) :=
  (stalk y).map (τ.app (V, W)) ≫
    (inverseImageStalkIso S.swap.hom ((terminalCoefficientsSheaf D H).obj (W, V)) y).inv

def ActsByFlipAt (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    {G : SectionGeometry N A B} {H : SectionGeometry N B A} (S : SectionExchange G H)
    (τ : ExchangeSource D G ⟶ ExchangeTarget D S) (z : sheetSpace A B) : Prop :=
  ∀ V W : Families r,
    exchangeStalk D S τ V W (terminalMap G z) ≫
      fiberGerm D H W V _ ⟨swappedPoint z, (S.onPoint z).symm⟩ =
    sheetGerm D G V W z ≫ (β_ (fiber V z.2.1.val) (fiber W z.2.2.val)).hom

/-- The comparison extends the exchange on the distinct-point locus,
and its value on every labelled collision summand is the ordinary flip. -/
structure CoefficientExchange (D : OrderedGeometry r) {N : ℕ} {A B : Set (Labels r)}
    {G : SectionGeometry N A B} {H : SectionGeometry N B A} (S : SectionExchange G H) where
  constantOnSections : ∀ (a : A) (b : B),
    sectionCoefficients D A B ⋙ inverseImage (sectionMap a b) ≅ constantCoefficients a.val b.val
  terminalFibers : ∀ (V W : Families r) (y : terminalSpace N A B), TerminalFiber D G V W y
  terminalInDegreeZero : Nonempty
    (sectionCoefficients D A B ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedDirectImage (terminalMap G) ≅
      terminalCoefficientsSheaf D G ⋙ DerivedCategory.Plus.singleFunctor _ 0)
  exchange : ExchangeSource D G ≅ ExchangeTarget D S
  awayFlip : ∀ z : sheetSpace A B, z.1.1 ≠ z.1.2 → ActsByFlipAt D S exchange.hom z
  uniqueExtension : ∀ τ : ExchangeSource D G ⟶ ExchangeTarget D S,
    (∀ z : sheetSpace A B, z.1.1 ≠ z.1.2 → ActsByFlipAt D S τ z) → τ = exchange.hom
  diagonalFlip : ∀ (x : ℂ) (a : A) (b : B),
    ActsByFlipAt D S exchange.hom (sectionPoint (x, x) a b)

abbrev SwapsConvolution {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
    (P : OrderedProduct D g c) :=
  P.convolution ≅ CategoryTheory.Prod.swap _ _ ⋙ P.convolution

abbrev PerverseFamily {g : StageGeometry r} {c : ContinuousJets r} (V : Heart r g c) :=
  (stalkFamily r g c).obj V

def commutorStalk {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
    {P : OrderedProduct D g c} (σ : SwapsConvolution P) (V W : Heart r g c) (n : Labels r) :
    OrderedProduct.Stalk (P.convolution.obj (V, W)) n ⟶
      OrderedProduct.Stalk (P.convolution.obj (W, V)) n :=
  ((stalkFamily r g c).map (σ.hom.app (V, W))).app (Discrete.mk n)

def FlipsConvolutionSummands {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
    (P : OrderedProduct D g c) (σ : SwapsConvolution P) : Prop :=
  ∀ (V W : Heart r g c) (a b : Labels r),
    P.includeSummand V W a b ≫ commutorStalk σ V W (a + b) =
    (β_ (OrderedProduct.Stalk V a) (OrderedProduct.Stalk W b)).hom ≫
      P.includeSummand W V b a ≫
      eqToHom (congrArg (OrderedProduct.Stalk (P.convolution.obj (W, V))) (add_comm b a))

/-- Comparison with the actual ordered convolution over the diagonal. Each
incident section is sent to the original ordered summand with the same labels. -/
structure DiagonalIdentification {D : OrderedGeometry r} {g : StageGeometry r}
    {c : ContinuousJets r} (P : OrderedProduct D g c) {N : ℕ} {A B : Set (Labels r)}
    (G : SectionGeometry N A B) (V W : Heart r g c) (y : terminalSpace N A B) (n : Labels r)
    (F : TerminalFiber D G (PerverseFamily V) (PerverseFamily W) y) where
  order : ∀ z : IncidentSheets G y, z.val.2.1.val + z.val.2.2.val = n
  iso : (stalk y).obj ((terminalCoefficientsSheaf D G).obj
      (PerverseFamily V, PerverseFamily W)) ≅
    OrderedProduct.Stalk (P.convolution.obj (V, W)) n
  onSummand : ∀ z : IncidentSheets G y,
    Sigma.ι _ z ≫ F.iso.hom ≫ iso.hom =
      P.includeSummand V W z.val.2.1.val z.val.2.2.val ≫
        eqToHom (congrArg (OrderedProduct.Stalk (P.convolution.obj (V, W))) (order z))

def SpecializesToConvolution {D : OrderedGeometry r} {g : StageGeometry r}
    {c : ContinuousJets r} {P : OrderedProduct D g c} (σ : SwapsConvolution P)
    {N : ℕ} {A B : Set (Labels r)} {G : SectionGeometry N A B} {H : SectionGeometry N B A}
    {S : SectionExchange G H} (E : CoefficientExchange D S) : Prop :=
  ∀ (V W : Heart r g c), supportedPairs r g c A B (V, W) →
    ∀ (x : ℂ) (a : A) (b : B),
      let y := terminalMap G (sectionPoint (x, x) a b)
      let y' := S.swap.hom y
      let n := a.val + b.val
      ∃ (F' : TerminalFiber D H (PerverseFamily W) (PerverseFamily V) y')
        (I : DiagonalIdentification P G V W y n
          (E.terminalFibers (PerverseFamily V) (PerverseFamily W) y))
        (I' : DiagonalIdentification P H W V y' n F'),
        exchangeStalk D S E.exchange.hom (PerverseFamily V) (PerverseFamily W) y ≫ I'.iso.hom =
          I.iso.hom ≫ commutorStalk σ V W n

/-- Two-point fusion of finite-support torus objects. The exchange is the
specialization extending the distinct-point geometric interchange, with
coefficients in degree zero and with all incident summands at a collision. -/
def TorusFusion : Prop :=
  ∀ r : ℕ, ∃ (D : OrderedGeometry r) (g : StageGeometry r) (c : ContinuousJets r)
    (P : OrderedProduct D g c), Nonempty (OrderedConstraints P) ∧ LocalGeometry D ∧
    ∃ σ : SwapsConvolution P, FlipsConvolutionSummands P σ ∧
      ∀ (A B : Set (Labels r)), A.Finite → B.Finite →
        ∃ (N : ℕ) (G : SectionGeometry N A B) (H : SectionGeometry N B A)
          (S : SectionExchange G H) (E : CoefficientExchange D S),
          ClearsPoles N A B ∧ SpecializesToConvolution σ E

end RepTheorySurvey.Geometric.TorusFusionSpecs
