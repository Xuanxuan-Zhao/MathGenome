import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SteinbergPinnedDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped BigOperators

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalSteinbergSection

section CoxeterWord

variable {R I X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

/-- The rightmost reflection acts first. -/
def reflectionWord (P : RootPairing I R X Y) (roots : List I) : X ≃ₗ[R] X :=
  (roots.map P.reflection).prod

/-- The simple root at position i transported by the preceding reflections. -/
def transportedRoot (P : RootPairing I R X Y) (roots : List I)
    (i : Fin roots.length) : X :=
  reflectionWord P (roots.take i.val) (P.root (roots.get i))

/-- The diagonal-one triangular assertion in the ordered simple roots. -/
def CoxeterTriangularity : Prop :=
  ∀ {R I X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y],
  ∀ (P : RootPairing I R X Y) (roots : List I) (i : Fin roots.length),
    transportedRoot P roots i - P.root (roots.get i) ∈
      Submodule.span R (P.root '' {a | a ∈ roots.take i.val})

/-- The fundamental weight at a position pairs to one at that position and to
zero at each other position. Its Coxeter displacement is the transported root. -/
def CoxeterDisplacement : Prop :=
  ∀ {R I X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y],
  ∀ (P : RootPairing I R X Y) (roots : List I) (i : Fin roots.length) (ω : X),
    (∀ j : Fin roots.length, P.toLinearMap ω (P.coroot (roots.get j)) =
      if j = i then 1 else 0) →
    ω - reflectionWord P roots ω = transportedRoot P roots i

/-- The Coxeter displacement is injective when the independent simple roots
are listed once and their coroots detect every weight. -/
def CoxeterInjectivity : Prop :=
  ∀ {R I X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y],
  ∀ (P : RootPairing I R X Y) (roots : List I),
    roots.Nodup → LinearIndepOn R P.root {a | a ∈ roots} →
    (∀ x : X, (∀ a ∈ roots, P.toLinearMap x (P.coroot a) = 0) → x = 0) →
    Function.Injective (fun x : X ↦ x - reflectionWord P roots x)

/-- The trace weight equation identifies the entering weight with the sum
of the fundamental weights with multiplicities equal to the exponents. -/
def CoxeterWeightRouting : Prop :=
  ∀ {R I X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y],
  ∀ (P : RootPairing I R X Y) (roots : List I) (ω : Fin roots.length → X),
    (∀ i j, P.toLinearMap (ω i) (P.coroot (roots.get j)) =
      if j = i then 1 else 0) →
    Function.Injective (fun x : X ↦ x - reflectionWord P roots x) →
    ∀ (m : Fin roots.length → ℕ) (μ : X),
      reflectionWord P roots μ + (∑ i, m i • transportedRoot P roots i) = μ →
      μ = ∑ i, m i • ω i

end CoxeterWord

/-- The simply connected coroot-lattice criterion makes the simple coroots
a basis of the full cocharacter lattice. The perfect pairing then identifies
the character lattice with its tuple of simple-coroot pairings. -/
def FundamentalCoordinates : Prop :=
  ∀ {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y],
  ∀ (P : RootPairing I ℤ X Y) (b : P.Base),
    Submodule.span ℤ (Set.range P.coroot) = ⊤ →
    ∃ e : X ≃ₗ[ℤ] (b.support → ℤ), ∀ x i, e x i = P.toLinearMap x (P.coroot i.val)

/-- Fundamental coordinates on the actual torus lattice when the coroot
lattice is full, as supplied by the simply connected lattice criterion. -/
def AttachedFundamentalCoordinates : Prop :=
  ∀ {k : Type u} [Field k] (P : Pinning.SplitBorelPair k)
    (D : Pinning.AttachedDatum P),
    SimplyConnectedLattice.corootLattice D = ⊤ →
    letI := D.comm
    ∃ e : Additive (CharacterDescent.Character P.T.group) ≃ₗ[ℤ] (D.base.support → ℤ),
      ∀ x i, e x i = D.datum.rootDatum.toLinearMap x (D.datum.rootDatum.coroot i.val)

/-- Over the rational weight space the Coxeter displacement is bijective. -/
def RationalCoxeterBijectivity : Prop :=
  ∀ {I X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y]
    [Module ℚ Y] [FiniteDimensional ℚ X],
  ∀ (P : RootPairing I ℚ X Y) (roots : List I),
    roots.Nodup → LinearIndepOn ℚ P.root {a | a ∈ roots} →
    Submodule.span ℚ (P.coroot '' {a | a ∈ roots}) = ⊤ →
    Function.Bijective (fun x : X ↦ x - reflectionWord P roots x)

section RootWord

variable {J G : Type*} [Group G]

/-- The ordered Steinberg word on the chosen root points and representatives. -/
def rootWord (order : List J) (x : J → G) (n : J → G) : G :=
  (order.map fun i ↦ x i * n i).prod

/-- The root point conjugated by the preceding Weyl representatives. -/
def conjugatedRoot (order : List J) (x n : J → G) (initial : G)
    (i : Fin order.length) : G :=
  let w := initial * ((order.take i.val).map n).prod
  w * x (order.get i) * w⁻¹

/-- Move the Weyl representatives to the right by conjugating the intervening
root elements. The input root points keep their original parameters. -/
def RewriteRootWord : Prop :=
  ∀ {J G : Type*} [Group G],
  ∀ (order : List J) (x n : J → G) (initial : G),
    initial * rootWord order x n =
      ((List.finRange order.length).map (conjugatedRoot order x n initial)).prod *
        (initial * (order.map n).prod)

/-- Reordering within consecutive blocks preserves the word when the
factors in each block commute. -/
def PermuteRootWordBlocks : Prop :=
  ∀ {J G : Type*} [Group G],
  ∀ (blocks blocks' : List (List J)) (x n : J → G),
    List.Forall₂ (fun block block' ↦ block.Perm block' ∧
      (block.map fun i ↦ x i * n i).Pairwise Commute) blocks blocks' →
    rootWord blocks.flatten x n = rootWord blocks'.flatten x n

end RootWord

section TraceParameters

variable {L J : Type*} [Field L]

/-- Triangular coordinates over the split field. Heights may repeat. -/
def triangularCoordinates (d : J → L) (p : J → MvPolynomial J L) (t : J → L) : J → L :=
  fun j ↦ d j * t j + MvPolynomial.eval t (p j)

def TriangularParameters : Prop :=
  ∀ {L J : Type*} [Field L],
  ∀ (height : J → ℤ) (d : J → L) (p : J → MvPolynomial J L),
    (∀ j, 0 ≤ height j) → (∀ j, d j ≠ 0) →
    (∀ j (m : J →₀ ℕ), (p j).coeff m ≠ 0 →
      ∀ i ∈ m.support, height i < height j) →
    Function.Bijective (triangularCoordinates d p)

end TraceParameters

/-- The two paired vertices in zero-based Bourbaki numbering are 0 and 5,
and 2 and 4. Their off-diagonal Cartan entries vanish in both directions. -/
def OuterE6Orthogonality : Prop :=
  CartanMatrix.E 6 0 5 = 0 ∧ CartanMatrix.E 6 5 0 = 0 ∧
  CartanMatrix.E 6 2 4 = 0 ∧ CartanMatrix.E 6 4 2 = 0

section InvariantLaurentPolynomials

variable {L X W : Type*} [Field L] [CommGroup X] [Group W]

/-- Evaluation at a point of a split torus in its character coordinates. -/
noncomputable def laurentEvaluation (t : X →* Lˣ) : MonoidAlgebra L X →+* L :=
  MonoidAlgebra.liftNCRingHom (RingHom.id L) ((Units.coeHom L).comp t)
    (fun _ _ ↦ Commute.all _ _)

/-- Distinct finite orbits of torus points are separated by an invariant
Laurent polynomial over the same field. -/
def InvariantLaurentSeparation : Prop :=
  ∀ {L X W : Type*} [Field L] [CommGroup X] [Group W] [Fintype W],
  ∀ (a : W →* MulAut X) (t u : X →* Lˣ),
    (∀ w, t.comp (a w).toMonoidHom ≠ u) →
    ∃ p : MonoidAlgebra L X,
      (∀ w, MonoidAlgebra.mapDomainRingEquiv L (a w) p = p) ∧
      laurentEvaluation t p = 0 ∧ laurentEvaluation u p = 1

end InvariantLaurentPolynomials

section SectionPoints

open AlgebraicGeometry
open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AdjointRepresentation (GroupPoints)
open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open GeometricRadicals (GeometricGroup IsSemisimple IsTorus IsUnipotentRadical)
open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open RootGroups (AdditiveLine)
open RootWeightAction (Representation)
open CharacterDescent (Character)
open NormalizerComparison (SimpleRepresentative)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open SteinbergPinnedDescent
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction)
open RelativeFormComparison (fieldTest)
open Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle)
open _root_.LinearAlgebraicGroups.Affine (RationalPoints IsRationalJordanDecomposition)

variable {k S : Type u} [Field k] [Field S] [Algebra k S]
variable {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}

/-- The Coxeter displacement and triangularity in the simple roots of the
given pinning, in the order of the factors in the section. -/
def PinnedCoxeterIdentities (D : AttachedDatum P.pair)
    (ω : SimpleRoot P.pair → Character P.pair.T.group)
    (order : List (SimpleRoot P.pair)) : Prop :=
  letI := D.comm
  let C := D.datum.rootDatum
  let roots := order.map Subtype.val
  (∀ i : Fin order.length,
    let weight := Additive.ofMul (ω (order.get i))
    let j : Fin roots.length := Fin.cast (by simp [roots]) i
    weight - reflectionWord C roots weight = transportedRoot C roots j ∧
      transportedRoot C roots j - C.root (order.get i).val ∈
        Submodule.span ℤ (C.root '' {a | a ∈ roots.take i.val})) ∧
  Function.Injective (fun x ↦ x - reflectionWord C roots x) ∧
  Function.Bijective ((LinearMap.id - (reflectionWord C roots).toLinearMap).baseChange ℚ)

def PinnedCoxeterWord : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair), IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ (ω : SimpleRoot P.pair → Character P.pair.T.group), IsFundamental D ω →
      ∀ order : List (SimpleRoot P.pair), order.Nodup → (∀ i, i ∈ order) →
        PinnedCoxeterIdentities D ω order

/-- Evaluate the original split representation at a rational point of the
scalar-extended group, using the scalar-extension comparison of point functors. -/
noncomputable def extendedTrace {I : Type u} [Fintype I] [DecidableEq I]
    {H : GroupScheme k} (ρ : Representation H I)
    (g : RationalPoints ((groupBaseChange k S).obj H)) : S :=
  let R := CommAlgCat.of S S
  Matrix.trace (ρ.app ((restrictTestAlgebra k S).obj R) (baseChangePoint k S H.X R g)).val

/-- The fundamental characters on the pinned split torus generate the integral
invariant Laurent ring for its actual Weyl action. -/
def PinnedCharacterGeneration : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair), IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group},
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
      ∀ (M : HighestWeightModules N U), IsFundamental D M.weight →
        letI := D.comm
        ∃ W : DatumAndWeyl.Identification D.datum,
          (∀ χ, ∃ (j : CharacterRing.dominantWeights N.pair) (w : D.datum.rootDatum.weylGroup),
            CharacterRing.weylAction W w χ = j.val) ∧
          (∀ j l : CharacterRing.dominantWeights N.pair,
            (∃ w, CharacterRing.weylAction W w j.val = l.val) ↔ j = l) ∧
          Subring.closure (Set.range fun i ↦ FormalCharacters.formalCharacter P.pair.T
            (M.representation i)) = CharacterRing.invariantRing (CharacterRing.weylAction W)

/-- The geometric fibres of the same traces used in the pinned section.
With a torus scheme centralizer at a semisimple target, conjugacy holds
for the original elements. -/
def GeometricTraceFibre {K : Type u} [Field K] (H : AffineAlgebraicGroup K)
    (x y : RationalPoints H.val) : Prop :=
  ∀ {s r v w : RationalPoints H.val},
    IsRationalJordanDecomposition ⟨H.val, H.property.1⟩ x s v →
    IsRationalJordanDecomposition ⟨H.val, H.property.1⟩ y r w →
    ∃ h : RationalPoints H.val, h * s * h⁻¹ = r ∧
      ∀ (C : ClosedSubgroup H.val) (y₀ : 𝟙_ (SchemeOver K) ⟶ H.val.X),
        IsTorus C.group → SteinbergGeometricFibres.IsPointCentralizer C y₀ →
        y = (toUnit ((testSpec K).obj (Opposite.op (CommAlgCat.of K K))) ≫ y₀ :
          RationalPoints H.val) →
        r = y → h * x * h⁻¹ = y

def HasGeometricTraceFibres {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    (M : HighestWeightModules N U) : Prop :=
  ∀ x y : RationalPoints (GeometricGroup P.pair.G).val,
    (∀ i, extendedTrace (S := AlgebraicClosure k) (M.representation i) x =
      extendedTrace (S := AlgebraicClosure k) (M.representation i) y) →
      GeometricTraceFibre (GeometricGroup P.pair.G) x y

def PinnedGeometricTraceFibres : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair), IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group},
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
      ∀ (M : HighestWeightModules N U), IsFundamental D M.weight → HasGeometricTraceFibres M

/-- The splitting-field embedding on the test algebras used for geometric points. -/
noncomputable def geometricTestMap (f : S →ₐ[k] AlgebraicClosure k) :
    CommAlgCat.of k S ⟶
      (restrictTestAlgebra k (AlgebraicClosure k)).obj
        (CommAlgCat.of (AlgebraicClosure k) (AlgebraicClosure k)) := by
  let K := AlgebraicClosure k
  let T := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
  change CommAlgCat.of k S ⟶ T
  refine (CommAlgCat.homEquivCommRingCat (CommAlgCat.of k S) T).symm
    ⟨CommRingCat.ofHom f.toRingHom, ?_⟩
  ext r
  exact (f.commutes r).trans (Algebra.algebraMap_self_apply (algebraMap k K r)).symm

/-- A geometric point obtained from a splitting-field point using the
given embedding of the splitting field in the algebraic closure. -/
def IsGeometricImage (f : S →ₐ[k] AlgebraicClosure k) {H : GroupScheme k}
    (g : GroupPoints H (CommAlgCat.of k S))
    (x : RationalPoints ((groupBaseChange k (AlgebraicClosure k)).obj H)) : Prop :=
  baseChangePoint k (AlgebraicClosure k) H.X _ x = mapPoints (geometricTestMap f) g

/-- Extending the actual splitting-field points preserves each trace,
with the same embedding on its value. -/
def GeometricTraceExtension : Prop :=
  ∀ {k S I : Type u} [Field k] [Field S] [Algebra k S] [Fintype I] [DecidableEq I]
    {H : GroupScheme k} (ρ : Representation H I) (f : S →ₐ[k] AlgebraicClosure k)
    (g : GroupPoints H (CommAlgCat.of k S)),
      ∃! x : RationalPoints ((groupBaseChange k (AlgebraicClosure k)).obj H),
        IsGeometricImage f g x ∧ extendedTrace ρ x = f (Matrix.trace (ρ.app _ g).val)

/-- Matching traces over the splitting field give conjugate geometric
semisimple parts after any embedding into the algebraic closure. -/
def HasSplitFieldTraceFibres {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    (M : HighestWeightModules N U) : Prop :=
  let R := CommAlgCat.of k S
  let H := GeometricGroup P.pair.G
  ∀ (f : S →ₐ[k] AlgebraicClosure k) (g y : GroupPoints P.pair.G.val R),
    (∀ i, traceValue (M.representation i) R g = traceValue (M.representation i) R y) →
    ∃ x' y' : RationalPoints H.val, IsGeometricImage f g x' ∧ IsGeometricImage f y y' ∧
      GeometricTraceFibre H x' y'

/-- The trace tuple of the word with a complete order of the marked simple roots. -/
noncomputable def wordTraces {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    (M : HighestWeightModules N U) (n : ∀ i, SimpleRepresentative P D i)
    (blocks : List (List (SimpleRoot P.pair))) (t : SimpleRoot P.pair → S) :
    SimpleRoot P.pair → S :=
  fun i ↦ traceValue (M.representation i) (CommAlgCat.of k S) (word n blocks _ t)

/-- The trace polynomials for the chosen orbit-ordered word on every test algebra. -/
def HasWordTracePolynomials (D : AttachedDatum P.pair)
    {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    (M : HighestWeightModules N U) (n : ∀ i, SimpleRepresentative P D i)
    (blocks : List (List (SimpleRoot P.pair))) : Prop :=
  let J := Fin blocks.flatten.length
  ∃ e : J ≃ SimpleRoot P.pair, (∀ i, e i = blocks.flatten.get i) ∧
    ∀ j : J, ∃ (d : k) (p : MvPolynomial J k), d ≠ 0 ∧
      (∀ m ∈ p.support, ∀ i ∈ m.support,
        SteinbergFundamentalTraces.height D (M.weight (e i)) <
          SteinbergFundamentalTraces.height D (M.weight (e j))) ∧
      ∀ (R : TestAlgebra k) (t : SimpleRoot P.pair → R),
        traceValue (M.representation (e j)) R (word n blocks R t) =
          MvPolynomial.aeval (fun i ↦ t (e i)) (MvPolynomial.C d * MvPolynomial.X j + p)

def WordTracePolynomials : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair), IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group},
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
      ∀ (M : HighestWeightModules N U), IsFundamental D M.weight →
        ∀ (n : ∀ i, SimpleRepresentative P D i) (blocks : List (List (SimpleRoot P.pair))),
          blocks.flatten.Nodup → (∀ i, i ∈ blocks.flatten) →
          HasWordTracePolynomials D M n blocks

/-- The triangular trace equations on the actual pinned word have a unique
solution over any extension of the field of the split model. -/
def SplitTraceBijection : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group},
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U →
    ∀ (M : HighestWeightModules N U), IsFundamental D M.weight →
    ∀ (n : ∀ i, SimpleRepresentative P D i) (blocks : List (List (SimpleRoot P.pair))),
      blocks.flatten.Nodup → (∀ i, i ∈ blocks.flatten) →
      Function.Bijective (wordTraces (S := S) M n blocks)

/-- The pinned section and its trace tuple are equivariant. Every compatible
trace tuple, including that of an inner-twisted fixed point, has a unique
parameter and yields a rational point in the reference model. -/
def SectionOnPoints (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P)
    (outer : Gal(S/k) → Aut D.toBased) {G : AffineAlgebraicGroup k}
    (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    (M : HighestWeightModules N U) : Prop :=
  ∃ (n : ∀ i, SimpleRepresentative P D i)
    (blocks : List (List (SimpleRoot P.pair))),
    blocks.flatten.Nodup ∧ (∀ i, i ∈ blocks.flatten) ∧
    (∀ σ b, b ∈ blocks → (b.map (diagramPermutation D (outer σ))).Perm b) ∧
    (∀ b ∈ blocks, ∀ i ∈ b, ∀ j ∈ b, ∃ σ, diagramPermutation D (outer σ) i = j) ∧
    (∀ b ∈ blocks, b.Pairwise (fun i j ↦ i ≠ j ∧ Orthogonal D i j)) ∧
    (∀ b ∈ blocks, ∀ (R : TestAlgebra k) (t : SimpleRoot P.pair → R),
      (b.map fun i ↦ factor i (n i) R (t i)).Pairwise Commute) ∧
    PinnedCoxeterIdentities D M.weight blocks.flatten ∧
    HasGeometricTraceFibres M ∧
    HasSplitFieldTraceFibres (S := S) M ∧
    HasWordTracePolynomials D M n blocks ∧
    Function.Bijective (wordTraces (S := S) M n blocks) ∧
    let R := CommAlgCat.of k S
    let tr := fun g i ↦ traceValue (M.representation i) R g
    let wrd := word n blocks R
    let a := fun σ : Gal(S/k) ↦ pinnedAction S (l (outer σ)).asIso.hom σ
    let π := fun σ : Gal(S/k) ↦ diagramPermutation D (outer σ)
    let changeParameters := fun σ ↦ permuteParameters (π σ) (fun c : S ↦ σ c)
    (∀ σ t, a σ (wrd t) = wrd (changeParameters σ t)) ∧
    (∀ σ g, tr (a σ g) = changeParameters σ (tr g)) ∧
    ∀ (v : SimpleRoot P.pair → S),
      ((∀ σ, changeParameters σ v = v) ∨
        ∃ (y : GroupPoints P.pair.G.val R) (z : Gal(S/k) → GroupPoints P.pair.G.val R),
          tr y = v ∧ ∀ σ, z σ * a σ y * (z σ)⁻¹ = y) →
      ∃ (t : SimpleRoot P.pair → S) (x : GroupPoints G.val (CommAlgCat.of k k)),
        tr (wrd t) = v ∧ (∀ σ, changeParameters σ t = t) ∧
        mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = comparisonOnPoints e (wrd t)

/-- The Steinberg section in the pinned quasi-split reference over a separable
closure, using fundamental simple modules of the split model. -/
def ReferenceSection : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q}
    {ω : @Cocycle (Gal(S/k)) (Aut D.toBased) _ (krullTopology k S) _ ⊥
      (trivialOuterAction (k := k) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ExceptionalDiagram D (fun σ : Gal(S/k) ↦ ω σ) →
    ∃ (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U ∧
      ∃ M : HighestWeightModules N U, IsFundamental D M.weight ∧
        SectionOnPoints D l (fun σ : Gal(S/k) ↦ ω σ) V.trivialization M

open AdjointBorelCohomology (PinnedTwist)

/-- The same construction evaluated in a finite Galois splitting field of
the pinned quasi-split reference. -/
def FiniteReferenceSection : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [FiniteDimensional k S] [IsGalois k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (V : PinnedTwist (P := P) S D l B T) (_E : SplitSequence P D l Q),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ExceptionalDiagram D V.outer →
    ∃ (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U ∧
      ∃ (M : HighestWeightModules N U), IsFundamental D M.weight ∧
        ∃ (t : ∀ C : HopfAlgebraCategory k,
              specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
          (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)),
          _root_.LinearAlgebraicGroups.Descent.Forms.IsScalarExtensionComparison t ∧
          RelativeFormComparison.IsInducedByHopf t
            (AdjointCocharacters.coordinateHopfIso P.pair.G)
            (AdjointCocharacters.coordinateHopfIso G) V.groupIso e ∧
          SectionOnPoints D l V.outer e M

end SectionPoints

end LinearAlgebraicGroups.Specs.ExceptionalSteinbergSection
