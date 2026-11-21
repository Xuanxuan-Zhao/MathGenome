import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleModel
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith

/-!
Interfaces for the relative fundamental class, paper.tex 2307--2350.

All groups are ordinary, integer-indexed singular homology with finite chains.
The definitions in this file impose no homological collar/sign certificate.
The expected theorems cover intrinsic boundary geometry, the interior-characterized
relative class, compact compatibility, the outward-normal-first boundary
orientation and its fundamental-class equation, collar independence, and the
empty-boundary and zero-dimensional cases. The cap-product duality maps of T31
belong to the separately allocated duality obligation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Topology
universe u v w u₁ v₁ w₁
namespace P202Specs.RelativeFundamentalClass
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactOrientation

/-- The interior as a subtype with its given subspace topology. -/
abbrev Interior {M : Type v} (B : Set M) := {x : M // x ∉ B}

/-- The intrinsic topological boundary, using the shared half-space model.
In dimension zero that model's face is empty by definition. -/
def manifoldBoundary {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M) : Set M :=
  {x | ∃ c ∈ A.atlas, x ∈ c.source ∧
    (c x).val ∈ SmoothManifolds.ModelData.halfSpaceFace n}

abbrev CollarTime := ↥(Set.Ico (0 : ℝ) 1)
def collarZero : CollarTime := ⟨0, le_rfl, zero_lt_one⟩

/-- A specified topological collar. All fields are geometric. In particular
neither a homology isomorphism nor an orientation-sign assertion is a field. -/
structure Collar {M : Type v} [TopologicalSpace M] (B : Set M) where
  neighborhood : Set M
  isOpen_neighborhood : IsOpen neighborhood
  homeomorph : (B × CollarTime) ≃ₜ neighborhood
  zero_section : ∀ b : B, (homeomorph (b, collarZero)).val = b.val

/-- Inclusion of the collar image into the original manifold. -/
def Collar.map {M : Type v} [TopologicalSpace M] {B : Set M} (c : Collar B) :
    C(B × CollarTime, M) :=
  ⟨fun y => (c.homeomorph y).val, continuous_subtype_val.comp c.homeomorph.continuous⟩

/-- The part of a collar below a given positive time. -/
def Collar.earlyRegion {M : Type v} [TopologicalSpace M] {B : Set M}
    (c : Collar B) (t : ℝ) : Set M :=
  c.map '' {y : B × CollarTime | y.2.val < t}

/-- The closed core obtained by deleting the early collar. -/
def Collar.core {M : Type v} [TopologicalSpace M] {B : Set M}
    (c : Collar B) (t : ℝ) : Set M := (c.earlyRegion t)ᶜ

/-- The same core viewed as a subset of the interior. -/
def Collar.interiorCore {M : Type v} [TopologicalSpace M] {B : Set M}
    (c : Collar B) (t : ℝ) : Set (Interior B) :=
  Subtype.val ⁻¹' c.core t

/-- The original pair, with the actual subspace topology on the boundary. -/
def boundaryPair (M : Type v) [TopologicalSpace M] (B : Set M) : Pair.{v} :=
  ⟨TopCat.of M, B⟩

/-- Relative classes can be localized at any point outside the boundary. -/
def interiorPointMap {M : Type v} [TopologicalSpace M] (B : Set M) (x : Interior B) :
    boundaryPair M B ⟶ localPair M x.val :=
  ⟨𝟙 _, fun y hy he => x.property (he ▸ hy)⟩

/-- The actual inclusion of the punctured interior into the ambient local pair. -/
def interiorLocalInclusion {M : Type v} [TopologicalSpace M] (B : Set M) (x : Interior B) :
    localPair (Interior B) x ⟶ localPair M x.val :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩,
    fun _ hy he => hy (Subtype.ext he)⟩

/-- Local orientations are transported along the actual open inclusion.
This comparison, rather than a new choice of local homology groups, expresses
the prescribed interior orientation of a relative class. -/
def HasInteriorValues (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (B : Set M) (n : ℕ) (o : LocalChoice R n (Interior B))
    (g : relativeHomology R R (boundaryPair M B) (n : ℤ)) : Prop :=
  ∀ x : Interior B, ((relativeHomologyFunctor R R (n : ℤ)).map (interiorPointMap B x)) g =
    ((relativeHomologyFunctor R R (n : ℤ)).map (interiorLocalInclusion B x)) (o x)

/-- A class with a compact support in the interior maps to its ambient support. -/
def compactSupportInclusion {M : Type v} [TopologicalSpace M] (B : Set M)
    (K : Set (Interior B)) : supportedPair (Interior B) K ⟶ supportedPair M (Subtype.val '' K) :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, by
    rintro y hy ⟨z, hz, he⟩
    exact hy (Subtype.ext he ▸ hz)⟩

/-- Localization of a relative class at a compact subset of the interior. -/
def relativeToCompact {M : Type v} [TopologicalSpace M] (B : Set M)
    (K : Set (Interior B)) : boundaryPair M B ⟶ supportedPair M (Subtype.val '' K) :=
  ⟨𝟙 _, by
    rintro y hy ⟨z, _, he⟩
    exact z.property (he.symm ▸ hy)⟩

/-- Compatibility with a supported class uses the canonical pair maps. -/
def AgreesOnCompact (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (B : Set M) (n : ℕ) (K : Set (Interior B))
    (g : relativeHomology R R (boundaryPair M B) (n : ℤ))
    (gK : SupportedGroup R (Interior B) K n) : Prop :=
  ((relativeHomologyFunctor R R (n : ℤ)).map (relativeToCompact B K)) g =
    ((relativeHomologyFunctor R R (n : ℤ)).map (compactSupportInclusion B K)) gK

/-- The positive boundary-of-a-lift connecting homomorphism, including n=0.
Its target is H_(n-1)(B); integer subtraction gives H_(-1) when n=0. -/
def boundaryHom (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (B : Set M)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (n : ℕ) :
    relativeHomology R R (boundaryPair M B) (n : ℤ) ⟶
      homology R R (TopCat.of B) ((n : ℤ) - 1) :=
  P202Specs.ChainLES.connecting h (n : ℤ) ((n : ℤ) - 1) (by simp)

/-- The actual pair map expressing that a class with empty boundary is ordinary. -/
def emptyAbsoluteToRelative (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (n : ℕ) :
    homology R R (TopCat.of M) (n : ℤ) →ₗ[R]
      relativeHomology R R (boundaryPair M ∅) (n : ℤ) :=
  (homologyMap (projection (ordinaryFunctor R R) (boundaryPair M ∅)) (n : ℤ)).hom

/-- Local characterization in the empty-boundary branch, directly in ambient
local groups, so there is no auxiliary choice of an interior atlas. -/
def HasEmptyBoundaryValues (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (n : ℕ) (o : LocalChoice R n M)
    (g : relativeHomology R R (boundaryPair M ∅) (n : ℤ)) : Prop :=
  ∀ x : M, ((relativeHomologyFunctor R R (n : ℤ)).map
    (interiorPointMap (∅ : Set M) ⟨x, Set.notMem_empty x⟩)) g = o x

/-- The local values of an ordinary class, using the shared support projection. -/
def absoluteLocalValues (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (n : ℕ) (a : homology R R (TopCat.of M) (n : ℤ)) : LocalChoice R n M :=
  fun x => restrictPoint R (Set.mem_univ x) n (absoluteToSupported R M n a)

/-- A concrete choice by the interior characterization alone. Existence and
uniqueness under the manifold/collar hypotheses are theorems in the candidate;
no collar, core, compactness proof, or homological certificate enters this value. -/
def fundamentalClass (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (B : Set M) (n : ℕ) (o : LocalChoice R n (Interior B)) :
    relativeHomology R R (boundaryPair M B) (n : ℤ) :=
  Classical.epsilon (HasInteriorValues R B n o)

/-- The positive connecting map in positive dimension, with its degree equality
made explicit. The zero-dimensional case continues to use `boundaryHom` and
its genuine degree -1 target. -/
def boundaryHomSucc (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (B : Set M)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (q : ℕ) :
    relativeHomology R R (boundaryPair M B) ((q + 1 : ℕ) : ℤ) ⟶
      homology R R (TopCat.of B) (q : ℤ) :=
  boundaryHom R B h (q + 1) ≫ eqToHom (congrArg
    (fun j : ℤ => homology R R (TopCat.of B) j) (by omega))

/-- The local values of the actual connecting image. This does not assert that
these values are generators or give the outward-normal-first orientation. -/
def connectingLocalValues (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (B : Set M)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B))) (q : ℕ)
    (g : relativeHomology R R (boundaryPair M B) ((q + 1 : ℕ) : ℤ)) :
    LocalChoice R q B := absoluteLocalValues R q (boundaryHomSucc R B h q g)

namespace Triple
open P202Specs.RelativeSingularChains P202Specs.SingularChains

variable {M : Type v} [TopologicalSpace M]

def subspacePair (A B : Set M) : Pair.{v} :=
  ⟨TopCat.of B, Subtype.val ⁻¹' A⟩

def tripleInclusion (A B : Set M) : subspacePair A B ⟶ boundaryPair M A :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ hx => hx⟩

def tripleProjection {A B : Set M} (hAB : A ⊆ B) :
    boundaryPair M A ⟶ boundaryPair M B :=
  ⟨𝟙 _, fun _ hx => hAB hx⟩

section Categorical
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {ι : Type w₁} {shape : ComplexShape ι}
  (K : TopCat.{v} ⥤ HomologicalComplex C shape)

lemma triple_zero {A B : Set M} (hAB : A ⊆ B) :
    relativeMap K (tripleInclusion A B) ≫ relativeMap K (tripleProjection hAB) = 0 := by
  apply (cancel_epi (projection K (subspacePair A B))).mp
  rw [← Category.assoc, projection_map, Category.assoc, projection_map]
  change K.map (boundaryPair M B).inclusion ≫
    (K.map (𝟙 (boundaryPair M B).space) ≫ projection K (boundaryPair M B)) = _
  simp only [K.map_id, Category.id_comp, comp_zero]
  exact cokernel.condition _

def tripleSequence {A B : Set M} (hAB : A ⊆ B) :
    ShortComplex (HomologicalComplex C shape) :=
  ShortComplex.mk (relativeMap K (tripleInclusion A B))
    (relativeMap K (tripleProjection hAB)) (triple_zero K hAB)

/-- Inclusion of one actual subspace into another. -/
def subspaceInclusion {B D : Set M} (hBD : B ⊆ D) :
    TopCat.of B ⟶ TopCat.of D :=
  TopCat.ofHom ⟨fun b => ⟨b.val, hBD b.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The left localization morphism is the actual map C(B) → C(D,A). -/
def pairToTripleFirst (A : Set M) {B D : Set M} (hBD : B ⊆ D) :
    K.obj (boundaryPair M B).sub ⟶ relativeComplex K (subspacePair A D) :=
  K.map (subspaceInclusion hBD) ≫ projection K (subspacePair A D)

/-- The map from the original pair sequence to the localized triple sequence. -/
def pairToTripleMap {A B D : Set M} (hAD : A ⊆ D) (hBD : B ⊆ D) :
    sequence K (boundaryPair M B) ⟶ tripleSequence K hAD :=
  ShortComplex.Hom.mk (pairToTripleFirst K A hBD)
    (projection K (boundaryPair M A)) (relativeMap K (tripleProjection hBD))
    (by
      change (K.map (subspaceInclusion hBD) ≫ projection K (subspacePair A D)) ≫
        relativeMap K (tripleInclusion A D) = inclusion K (boundaryPair M B) ≫
          projection K (boundaryPair M A)
      rw [Category.assoc, projection_map, ← Category.assoc, ← K.map_comp]
      rfl)
    (by
      change projection K (boundaryPair M A) ≫ relativeMap K (tripleProjection hAD) =
        projection K (boundaryPair M B) ≫ relativeMap K (tripleProjection hBD)
      rw [projection_map, projection_map]
      rfl)

end Categorical
end Triple

namespace Box
variable {D : Type v} [TopologicalSpace D]
/-- The upper face together with all lateral faces of a closed collar box. -/
def upperLateral (S : Set D) : Set (unitInterval × D) :=
  {z | z.1 = 1 ∨ z.2 ∈ S}

def upperLateralPair (S : Set D) : Pair.{v} :=
  ⟨TopCat.of (unitInterval × D), upperLateral S⟩

/-- The two interval-end faces and the lateral subspace of a model prism. -/
def fullBoundary (S : Set D) : Set (unitInterval × D) :=
  {z | z.1 = 0 ∨ z ∈ upperLateral S}

lemma upperLateral_subset_fullBoundary (S : Set D) : upperLateral S ⊆ fullBoundary S :=
  fun _ h => Or.inr h

end Box

namespace Disk
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev UnitDisk := ↥(Metric.closedBall (0 : E) 1)
def unitPair : Pair.{v} := ⟨TopCat.of (UnitDisk E), {x | ‖x.val‖ = 1}⟩
def origin : UnitDisk E := ⟨0, by simp⟩
def toLocal : unitPair E ⟶ localPair E 0 :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, by
    intro x hx he
    change ‖x.val‖ = 1 at hx
    change x.val = 0 at he
    simpa [he] using hx⟩
def toOwnLocal : unitPair E ⟶ localPair (UnitDisk E) (origin E) :=
  ⟨𝟙 _, by
    intro w hw he
    change ‖w.val‖ = 1 at hw
    change w = origin E at he
    rw [he] at hw
    simpa [origin] using hw⟩

end Disk

namespace BoxBottom
open P202Specs.RelativeFundamentalClass.Box
variable {D : Type v} [TopologicalSpace D]
def bottomPair (S : Set D) : Pair.{v} := ⟨TopCat.of D, S⟩
def boundaryPair (S : Set D) : Pair.{v} :=
  Triple.subspacePair (upperLateral S) (fullBoundary S)
def bottomInclusion (S : Set D) : bottomPair S ⟶ boundaryPair S where
  map := TopCat.ofHom ⟨fun d => ⟨(0,d), Or.inl rfl⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩
  mapsTo := fun _ h => Or.inr h

end BoxBottom

namespace CollarLocalization
variable {M : Type v} [TopologicalSpace M]
def unionBoundaryLocalInclusion (A B : Set M) (y : B) :
    localPair B y ⟶ localPair ↥(A ∪ B) ⟨y.val, Or.inr y.property⟩ :=
  ⟨TopCat.ofHom ⟨fun b => ⟨b.val, Or.inr b.property⟩,
    continuous_subtype_val.subtype_mk _⟩,
    fun b hb he => hb (Subtype.ext (congrArg (fun d : ↥(A ∪ B) => d.val) he))⟩


def triplePointMap (A B : Set M) (y : B) (hy : y.val ∉ A) :
    Triple.subspacePair A (A ∪ B) ⟶
      localPair ↥(A ∪ B) ⟨y.val, Or.inr y.property⟩ :=
  ⟨𝟙 _, fun z hz he => hy ((congrArg (fun d : ↥(A ∪ B) => d.val) he) ▸ hz)⟩


def openPair (P : Pair.{v}) (U : Set P.space) : Pair.{v} :=
  ⟨TopCat.of U, Subtype.val ⁻¹' P.subspace⟩

def openPairInclusion (P : Pair.{v}) (U : Set P.space) : openPair P U ⟶ P :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ h => h⟩

end CollarLocalization

namespace Disk
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma boundary_ne_interior (p : E) (hp : ‖p‖ < 1)
    (x : UnitDisk E) (hx : ‖x.val‖ = 1) : x.val ≠ p := by
  intro he
  rw [he] at hx
  exact (ne_of_lt hp) hx

def toLocalAt (p : E) (hp : ‖p‖ < 1) : unitPair E ⟶ localPair E p :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩,
    fun x hx => boundary_ne_interior E p hp x hx⟩


end Disk

namespace NormPrism
open P202Specs.RelativeFundamentalClass.Box P202Specs.RelativeFundamentalClass.Disk
variable (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]
abbrev sphereSubset : Set (UnitDisk V) := (unitPair V).subspace
def prismPair : Pair.{v} :=
  ⟨TopCat.of (unitInterval × UnitDisk V), fullBoundary (sphereSubset V)⟩


def center : unitInterval × UnitDisk V := (⟨1/2, by norm_num⟩, origin V)


def toAmbientLocal : prismPair V ⟶ localPair (ℝ × V) 0 where
  map := TopCat.ofHom ⟨fun z => (2*(z.1:ℝ)-1,z.2.val),
    ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
      continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)⟩
  mapsTo := by
    intro z hz he
    change (2*(z.1:ℝ)-1,z.2.val) = (0,0) at he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    rcases hz with h0 | h1 | hS
    · rw [h0] at he1
      norm_num at he1
    · rw [h1] at he1
      norm_num at he1
    · change ‖z.2.val‖ = 1 at hS
      have hn : ‖z.2.val‖ = 0 := by simpa only [norm_zero] using congrArg norm he2
      have hh := hS.symm.trans hn
      norm_num at hh


abbrev ballToOwnLocal : unitPair (ℝ × V) ⟶
    localPair (UnitDisk (ℝ × V)) (origin (ℝ × V)) := Disk.toOwnLocal (ℝ × V)

def toOwnLocal : prismPair V ⟶ localPair (unitInterval × UnitDisk V) (center V) :=
  ⟨𝟙 _, by
    intro z hz he
    change z = center V at he
    rw [he] at hz
    change (center V).1 = 0 ∨ (center V).1 = 1 ∨ ‖(center V).2.val‖ = 1 at hz
    rcases hz with h0 | h1 | hS
    · have hh := congrArg Subtype.val h0
      norm_num [center] at hh
    · have hh := congrArg Subtype.val h1
      norm_num [center] at hh
    · change ‖(0 : V)‖ = 1 at hS
      norm_num at hS⟩


end NormPrism

namespace SubspaceLocal
variable {X : Type v} [TopologicalSpace X] [T2Space X]
def localInclusion (T : Set X) (x : T) : localPair T x ⟶ localPair X x.val :=
  ⟨TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩,
    fun _ hy he => hy (Subtype.ext he)⟩


end SubspaceLocal

namespace PrismLift
open P202Specs.AlexanderWhitney P202Specs.ShuffleModel
open scoped TensorProduct

def positiveInterval : Simplex (TopCat.of unitInterval) 1 :=
  (simplexEquiv (TopCat.of unitInterval) 1).symm
    ⟨fun z => ⟨z.weights 1, z.weights_nonneg 1, z.weights_apply_le_one 1⟩,
      (Convexity.StdSimplex.continuous_weights_apply ℝ 1).subtype_mk _⟩


def quotientChain (R : Type u) [CommRing R] (P : Pair.{w}) (n : ℕ)
    (c : Chains R P.space n) : (ordinary R R P).X (n : ℤ) :=
  (ordinaryDegreeIso R R P n).inv ((projection (chainFunctor R R) P).f n c)


def prismChain (R : Type u) [CommRing R] (D : TopCat) (n : ℕ)
    (c : Chains R D n) : Chains R (productSpace (TopCat.of unitInterval) D) (n+1) :=
  shuffle R (TopCat.of unitInterval) D (n+1)
    (Pi.single (⟨(1,n), by omega⟩ : Diagonal (n+1))
      (Finsupp.single positiveInterval 1 ⊗ₜ[R] c))


def bottomChain (R : Type u) [CommRing R] {D : Type} [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n) :
    Chains R (P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair S).space n :=
  (chainMap R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S).map).f n c


end PrismLift

namespace CollarClamp
open P202Specs.RelativeFundamentalClass.Box
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev OpenTime := ↥(Set.Ico (0 : ℝ) 2)
abbrev OpenDisk (E : Type v) [NormedAddCommGroup E] := Metric.ball (0 : E) 2
abbrev ClosedDisk (E : Type v) [NormedAddCommGroup E] := Metric.closedBall (0 : E) 1
abbrev OpenCylinder (E : Type v) [NormedAddCommGroup E] := OpenTime × OpenDisk E
abbrev ClosedPrism (E : Type v) [NormedAddCommGroup E] := unitInterval × ClosedDisk E

def timeInclusion (t : unitInterval) : OpenTime :=
  ⟨t.val, t.property.1, lt_of_le_of_lt t.property.2 (by norm_num)⟩

lemma timeInclusion_continuous : Continuous timeInclusion := continuous_subtype_val.subtype_mk _

def prismInclusion : C(ClosedPrism E, OpenCylinder E) :=
  ⟨fun z => (timeInclusion z.1,
    ⟨z.2.val, lt_of_le_of_lt z.2.property (show (1:ℝ) < 2 by norm_num)⟩),
    (timeInclusion_continuous.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩


def rim : Set (ClosedDisk E) := {x | ‖x.val‖ = 1}
def openUpper : Set (OpenCylinder E) := {z | 1 ≤ z.1.val ∨ 1 ≤ ‖z.2.val‖}
def openFull : Set (OpenCylinder E) := {z | z.1.val = 0 ∨ z ∈ openUpper}
def closedUpper : Set (ClosedPrism E) := Box.upperLateral (rim (E := E))
def closedFull : Set (ClosedPrism E) := Box.fullBoundary (rim (E := E))


lemma prismInclusion_upper {z : ClosedPrism E} (hz : z ∈ closedUpper) :
    prismInclusion z ∈ openUpper := by
  rcases hz with ht | hx
  · left
    change 1 ≤ z.1.val
    rw [ht]
    rfl
  · right
    exact le_of_eq hx.symm


lemma prismInclusion_full {z : ClosedPrism E} (hz : z ∈ closedFull) :
    prismInclusion z ∈ openFull := by
  rcases hz with ht | hu
  · left
    change z.1.val = 0
    rw [ht]
    rfl
  · exact Or.inr (prismInclusion_upper hu)


def closedPair (full : Bool) : Pair.{v} :=
  ⟨TopCat.of (ClosedPrism E), if full then closedFull else closedUpper⟩
def openPair (full : Bool) : Pair.{v} :=
  ⟨TopCat.of (OpenCylinder E), if full then openFull else openUpper⟩

def pairInclusion (full : Bool) : closedPair (E := E) full ⟶ openPair (E := E) full :=
  ⟨TopCat.ofHom prismInclusion, by
    cases full
    · exact fun _ hz => prismInclusion_upper hz
    · exact fun _ hz => prismInclusion_full hz⟩


def tripleTargetInclusion :
    Triple.subspacePair (closedUpper (E := E)) closedFull ⟶
      Triple.subspacePair (openUpper (E := E)) openFull :=
  ⟨TopCat.ofHom ⟨fun z => ⟨prismInclusion z.val, prismInclusion_full z.property⟩,
    (prismInclusion.continuous.comp continuous_subtype_val).subtype_mk _⟩,
    fun _ hz => prismInclusion_upper hz⟩

end CollarClamp

namespace CollarLocalization
variable {M : Type v} [TopologicalSpace M]
section TripleMap
variable {N : Type v} [TopologicalSpace N]

def ambientPairMap (f : C(M, N)) {A : Set M} {E : Set N}
    (hf : Set.MapsTo f A E) : boundaryPair M A ⟶ boundaryPair N E :=
  ⟨TopCat.ofHom f, hf⟩

def subspacePairMap (f : C(M, N)) {A D : Set M} {E G : Set N}
    (hfA : Set.MapsTo f A E) (hfD : Set.MapsTo f D G) :
    Triple.subspacePair A D ⟶ Triple.subspacePair E G :=
  ⟨TopCat.ofHom ⟨fun d => ⟨f d.val, hfD d.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩,
    fun _ hd => hfA hd⟩

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {ι : Type w₁} {shape : ComplexShape ι}
  (K : TopCat.{v} ⥤ HomologicalComplex C shape)

def tripleSequenceMap (f : C(M, N)) {A D : Set M} {E G : Set N}
    (hAD : A ⊆ D) (hEG : E ⊆ G)
    (hfA : Set.MapsTo f A E) (hfD : Set.MapsTo f D G) :
    Triple.tripleSequence K hAD ⟶ Triple.tripleSequence K hEG :=
  ShortComplex.Hom.mk (relativeMap K (subspacePairMap f hfA hfD))
    (relativeMap K (ambientPairMap f hfA)) (relativeMap K (ambientPairMap f hfD))
    (by
      change (relativeFunctor K).map (subspacePairMap f hfA hfD) ≫
          (relativeFunctor K).map (Triple.tripleInclusion E G) =
        (relativeFunctor K).map (Triple.tripleInclusion A D) ≫
          (relativeFunctor K).map (ambientPairMap f hfA)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)
    (by
      change (relativeFunctor K).map (ambientPairMap f hfA) ≫
          (relativeFunctor K).map (Triple.tripleProjection hEG) =
        (relativeFunctor K).map (Triple.tripleProjection hAD) ≫
          (relativeFunctor K).map (ambientPairMap f hfD)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)

end TripleMap
end CollarLocalization

namespace CollarChart
open P202Specs.RelativeFundamentalClass.CollarClamp
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] {B : Set M}
abbrev NormalizedOpenTime := ↥(Set.Ico (0 : ℝ) 2)
abbrev EarlyTime := {t : CollarTime // t.val < (1/2 : ℝ)}

def timeScaleHomeomorph : NormalizedOpenTime ≃ₜ EarlyTime where
  toFun t := ⟨⟨t.val / 4, by
      have ht0 : 0 ≤ t.val := t.property.1
      have ht2 : t.val < 2 := t.property.2
      constructor <;> linarith⟩, by
    have ht2 : t.val < 2 := t.property.2
    change t.val / 4 < 1/2
    linarith⟩
  invFun s := ⟨4 * s.val.val, by
    have hs0 : 0 ≤ s.val.val := s.val.property.1
    have hh := s.property
    constructor <;> linarith⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv s := by apply Subtype.ext; apply Subtype.ext; dsimp; ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div_const 4
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)

def timeScale : C(NormalizedOpenTime, CollarTime) :=
  ⟨fun t => (timeScaleHomeomorph t).val,
    continuous_subtype_val.comp timeScaleHomeomorph.continuous⟩


def cylinderMap (c : Collar B) (f : C(E, B)) :
    C(NormalizedOpenTime × Metric.ball (0 : E) 2, M) :=
  c.map.comp ⟨fun z => (f z.2.val, timeScale z.1),
    (f.continuous.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (timeScale.continuous.comp continuous_fst)⟩

end CollarChart

namespace CollarChart
open P202Specs.RelativeFundamentalClass.Disk
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] {B : Set M}
abbrev Cylinder := NormalizedOpenTime × Metric.ball (0 : E) 2

abbrev boxInclusion : C(unitInterval × UnitDisk E, Cylinder (E := E)) :=
  P202Specs.RelativeFundamentalClass.CollarClamp.prismInclusion

def closedParameters : Set (Cylinder (E := E)) :=
  {z | z.1.val ≤ 1 ∧ ‖z.2.val‖ ≤ 1}
def openParameters : Set (Cylinder (E := E)) :=
  {z | z.1.val < 1 ∧ ‖z.2.val‖ < 1}


def boxMap (c : Collar B) (f : C(E,B)) : C(unitInterval × UnitDisk E,M) :=
  (cylinderMap c f).comp boxInclusion

def boxImage (c : Collar B) (f : C(E,B)) : Set M := Set.range (boxMap c f)

end CollarChart

namespace BottomLocal
open P202Specs.RelativeFundamentalClass.Disk P202Specs.RelativeFundamentalClass.Box
variable (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]
abbrev sphereSubset : Set (UnitDisk V) := (unitPair V).subspace
abbrev Boundary := fullBoundary (sphereSubset V)
def center : Boundary V := ⟨(0, origin V), Or.inl rfl⟩
def bottomSubset : Set (Boundary V) := {z | z.val.1 = 0}
def bottomCenter : bottomSubset V := ⟨center V, rfl⟩


def bottomLocalMap : localPair (UnitDisk V) (origin V) ⟶ localPair (Boundary V) (center V) where
  map := TopCat.ofHom ⟨fun d => ⟨(0,d), Or.inl rfl⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩
  mapsTo := fun _ hx he => hx (congrArg (fun z : Boundary V => z.val.2) he)


abbrev diskPointMap : unitPair V ⟶ localPair (UnitDisk V) (origin V) := Disk.toOwnLocal V

def targetPointMap :
    P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair (sphereSubset V) ⟶
      localPair (Boundary V) (center V) :=
  ⟨𝟙 _, by
    intro z hz he
    change z = center V at he
    rw [he] at hz
    rcases hz with ht | hs
    · have hh := congrArg Subtype.val ht
      norm_num [center] at hh
    · change ‖(0 : V)‖ = 1 at hs
      norm_num at hs⟩

end BottomLocal

namespace CollarGlobal
open P202Specs.RelativeFundamentalClass.CollarClamp
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M]
def innerCylinder : Set (OpenCylinder E) := {z | z.1.val < 1 ∧ ‖z.2.val‖ < 1}

def deletedOutside (f : C(OpenCylinder E, M)) : Set M := (f '' innerCylinder)ᶜ

def cylinderRangePair (f : C(OpenCylinder E, M)) (B : Set M) : Pair.{v} :=
  ⟨TopCat.of (Set.range f), Subtype.val ⁻¹' (deletedOutside f ∪ B)⟩

def fullPairMap (f : C(OpenCylinder E, M)) (B : Set M)
    (hf : Function.Injective f)
    (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) :
    openPair (E := E) true ⟶ boundaryPair M (deletedOutside f ∪ B) :=
  ⟨TopCat.ofHom f, by
    intro z hz
    rcases hz with ht | hu
    · exact Or.inr ((hB z).mpr ht)
    · left
      rintro ⟨w, hw, he⟩
      have he' := hf he
      subst w
      rcases hu with ht | hx
      · exact (not_lt_of_ge ht) hw.1
      · exact (not_lt_of_ge hx) hw.2⟩

lemma preimage_deletedOutside (f : C(OpenCylinder E, M)) (hf : Function.Injective f)
    (z : OpenCylinder E) : f z ∈ deletedOutside f ↔ z ∈ openUpper := by
  change f z ∉ f '' innerCylinder ↔ 1 ≤ z.1.val ∨ 1 ≤ ‖z.2.val‖
  have him : f z ∈ f '' innerCylinder ↔ z ∈ innerCylinder := by
    constructor
    · rintro ⟨w, hw, he⟩
      exact hf he ▸ hw
    · exact fun hz => ⟨z, hz, rfl⟩
  rw [him]
  simp only [innerCylinder, Set.mem_setOf_eq, not_and_or, not_lt]


def closedCore (f : C(OpenCylinder E, M)) : Set M :=
  Set.range (f.comp (prismInclusion (E := E)))


def upperPairMap (f : C(OpenCylinder E, M)) (hf : Function.Injective f) :
    openPair (E := E) false ⟶ boundaryPair M (deletedOutside f) :=
  ⟨TopCat.ofHom f, fun z hz => (preimage_deletedOutside f hf z).mpr hz⟩


def closedTargetMap (f : C(OpenCylinder E, M)) (hf : Function.Injective f)
    (B : Set M) (hB : ∀ z, f z ∈ B ↔ z.1.val = 0) :
    Triple.subspacePair (closedUpper (E := E)) closedFull ⟶
      Triple.subspacePair (deletedOutside f) (deletedOutside f ∪ B) :=
  P202Specs.RelativeFundamentalClass.CollarLocalization.subspacePairMap
    (f.comp prismInclusion)
    (pairInclusion (E := E) false ≫ upperPairMap f hf).mapsTo
    (pairInclusion (E := E) true ≫ fullPairMap f B hf hB).mapsTo

end CollarGlobal

namespace EmbeddingLocal
variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
def localMap (f : C(X,Y)) (hf : Function.Injective f) (x : X) :
    localPair X x ⟶ localPair Y (f x) :=
  ⟨TopCat.ofHom f, fun _ hx he => hx (hf he)⟩

end EmbeddingLocal

namespace PrismLiftGeneric
open P202Specs.ChainLES P202Specs.AlexanderWhitney P202Specs.ShuffleModel
open P202Specs.RelativeFundamentalClass.PrismLift
open scoped TensorProduct
abbrev LiftedInterval := ULift.{v} unitInterval

def positiveInterval : Simplex (TopCat.of LiftedInterval.{v}) 1 :=
  (simplexEquiv (TopCat.of LiftedInterval.{v}) 1).symm
    ⟨fun z => ULift.up ⟨z.weights 1,z.weights_nonneg 1,z.weights_apply_le_one 1⟩,
      Homeomorph.ulift.symm.continuous.comp
        ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).subtype_mk _)⟩

variable {D : Type v} [TopologicalSpace D]
def downProduct : productSpace (TopCat.of LiftedInterval.{v}) (TopCat.of D) ⟶
    TopCat.of (unitInterval × D) :=
  TopCat.ofHom ⟨fun z => (z.1.down,z.2),
    (Homeomorph.ulift.continuous.comp continuous_fst).prodMk continuous_snd⟩

def liftedUpper (S : Set D) : Set (LiftedInterval.{v} × D) :=
  {z | z.1.down = 1 ∨ z.2 ∈ S}
def liftedPair (S : Set D) : Pair.{v} :=
  ⟨productSpace (TopCat.of LiftedInterval.{v}) (TopCat.of D), liftedUpper S⟩
def downPairMap (S : Set D) : liftedPair S ⟶
    boundaryPair (unitInterval × D) (Box.upperLateral S) :=
  ⟨downProduct,fun _ h => h⟩

def rawPrismChain (R : Type u) [CommRing R] (n : ℕ)
    (c : Chains R (TopCat.of D) n) : Chains R (liftedPair (Set.univ : Set D)).space (n+1) :=
  shuffle R (TopCat.of LiftedInterval.{v}) (TopCat.of D) (n+1)
    (Pi.single (⟨(1,n),by omega⟩ : Diagonal (n+1))
      (Finsupp.single positiveInterval 1 ⊗ₜ[R] c))

def prismChain (R : Type u) [CommRing R] (n : ℕ)
    (c : Chains R (TopCat.of D) n) : Chains R (TopCat.of (unitInterval × D)) (n+1) :=
  (chainMap R R downProduct).f (n+1) (rawPrismChain R n c)

def bottomChain (R : Type u) [CommRing R] (S : Set D) (n : ℕ)
    (c : Chains R (TopCat.of D) n) :
    Chains R (P202Specs.RelativeFundamentalClass.BoxBottom.boundaryPair S).space n :=
  (chainMap R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S).map).f n c

end PrismLiftGeneric

namespace BoundaryOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.ChainLES
open P202Specs.RelativeFundamentalClass.Disk P202Specs.RelativeFundamentalClass.PrismLift

variable (R : Type u) [CommRing R] (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]

def IsDiskCycle (q : ℕ) (a : Chains R (TopCat.of (UnitDisk V)) q) : Prop :=
  (ordinary R R (unitPair V)).d (q : ℤ) ((ComplexShape.down ℤ).next (q : ℤ))
    (quotientChain R (unitPair V) q a) = 0

def diskClass (q : ℕ) (a : Chains R (TopCat.of (UnitDisk V)) q)
    (ha : IsDiskCycle R V q a) : relativeHomology R R (unitPair V) (q : ℤ) :=
  cycleClass (ordinary R R (unitPair V)) ((ComplexShape.down ℤ).next (q : ℤ)) rfl
    (quotientChain R (unitPair V) q a) ha

def IsPrismCycle (q : ℕ) (a : Chains R (TopCat.of (UnitDisk V)) q) : Prop :=
  (ordinary R R (NormPrism.prismPair V)).d ((q+1 : ℕ) : ℤ) (q : ℤ)
    (quotientChain R (NormPrism.prismPair V) (q+1) (PrismLiftGeneric.prismChain R q a)) = 0

/-- The positive inward interval comes first in the actual signed shuffle. -/
def inwardClass (q : ℕ) (a : Chains R (TopCat.of (UnitDisk V)) q)
    (ha : IsPrismCycle R V q a) :
    relativeHomology R R (NormPrism.prismPair V) ((q+1 : ℕ) : ℤ) :=
  cycleClass (ordinary R R (NormPrism.prismPair V)) (q : ℤ) (by simp)
    (quotientChain R (NormPrism.prismPair V) (q+1) (PrismLiftGeneric.prismChain R q a)) ha

variable {M : Type v} [TopologicalSpace M] (B : Set M)

def bottomLocalValue (f : C(V, B)) (hf : Function.Injective f) (q : ℕ)
    (a : Chains R (TopCat.of (UnitDisk V)) q) (ha : IsDiskCycle R V q a) :
    LocalGroup R B (f 0) q :=
  ((relativeHomologyFunctor R R (q : ℤ)).map
    (toLocal V ≫ EmbeddingLocal.localMap f hf 0)) (diskClass R V q a ha)

def boxLocalMap (c : Collar B) (f : C(V, B))
    (hf : Function.Injective (CollarChart.boxMap c f)) :
    NormPrism.prismPair V ⟶ localPair M (CollarChart.boxMap c f (NormPrism.center V)) :=
  NormPrism.toOwnLocal V ≫ EmbeddingLocal.localMap (CollarChart.boxMap c f) hf (NormPrism.center V)

/-- At a boundary point the proposed boundary orientation is represented by an
actual disk cycle. Its negative positive-inward-interval-first shuffle has the
prescribed interior orientation. This is the outward-normal-first convention:
the outward normal reverses the positive collar parameter. The definition uses
neither the global relative class nor any connecting homomorphism. -/
def IsOutwardInBox (c : Collar B) (q : ℕ)
    (o : LocalChoice R (q+1) (Interior B)) (b : LocalChoice R q B)
    (f : C(V, B)) (hf : IsOpenEmbedding f) : Prop :=
  ∃ (hbox : Function.Injective (CollarChart.boxMap c f))
    (hx : CollarChart.boxMap c f (NormPrism.center V) ∉ B)
    (a : Chains R (TopCat.of (UnitDisk V)) q)
    (ha : IsDiskCycle R V q a) (hp : IsPrismCycle R V q a),
    bottomLocalValue R V B f hf.injective q a ha = b (f 0) ∧
    ((relativeHomologyFunctor R R ((q+1 : ℕ) : ℤ)).map (boxLocalMap V B c f hbox))
      (-inwardClass R V q a hp) =
    ((relativeHomologyFunctor R R ((q+1 : ℕ) : ℤ)).map
      (interiorLocalInclusion B ⟨CollarChart.boxMap c f (NormPrism.center V), hx⟩))
      (o ⟨CollarChart.boxMap c f (NormPrism.center V), hx⟩)

end BoundaryOrientation

open P202Specs.LocalOrientation

/-- The local product-box convention for the induced boundary orientation,
quantified over actual spatial charts. These are geometric collar choices,
not assumed homological or orientation-sign certificates. -/
def IsOutwardNormalFirst (R : Type u) [CommRing R] {M : Type v} [TopologicalSpace M]
    (B : Set M) (c : Collar B) (q : ℕ)
    (o : LocalChoice R (q+1) (Interior B)) (b : LocalChoice R q B) : Prop :=
  ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    (f : C(V, B)) (hf : IsOpenEmbedding f),
      BoundaryOrientation.IsOutwardInBox R V B c q o b f hf


namespace Expected
/-- The empty-boundary branch of the assigned obligation. -/
def emptyBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A), IsCompact (Set.univ : Set M) →
      Function.Bijective (emptyAbsoluteToRelative R M n) ∧
      ∃! g : relativeHomology R R (boundaryPair M ∅) (n : ℤ),
        HasEmptyBoundaryValues R n o.val g
/-- The construction and compact-compatibility part of T31. The induced boundary
orientation and connecting equation are specified separately below. -/
def interiorClass : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M), IsClosed B → ∀ (_c : Collar B)
    (A : Manifold n (Interior B)) (o : Orientation R A), IsCompact (Set.univ : Set M) →
    (∃! g : relativeHomology R R (boundaryPair M B) (n : ℤ),
      HasInteriorValues R B n o.val g) ∧
    ∀ g : relativeHomology R R (boundaryPair M B) (n : ℤ),
      HasInteriorValues R B n o.val g →
      ∀ K : Set (Interior B), IsCompact K →
      ∀ gK : SupportedGroup R (Interior B) K n,
        HasLocalValues R o.val K gK → AgreesOnCompact R B n K g gK

/-- Recognition of the boundary equation by the prescribed local values. -/
def boundaryRecognition : Prop :=
  ∀ (R : Type u) [CommRing R] (q : ℕ) (M : Type v) [TopologicalSpace M]
    (B : Set M) (A : Manifold q B) (o : Orientation R A),
    IsCompact (Set.univ : Set B) →
    ∀ (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M B)))
      (g : relativeHomology R R (boundaryPair M B) ((q + 1 : ℕ) : ℤ))
      (b : homology R R (TopCat.of B) (q : ℤ)),
      HasLocalValues R o.val Set.univ (absoluteToSupported R B q b) →
        (boundaryHomSucc R B h q g = b ↔ connectingLocalValues R B h q g = o.val)

/-- Intrinsic boundary geometry, in the inherited topology, with no smooth
structure or assumed face-invariance certificate. -/
def boundaryGeometry : Prop :=
  (∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M),
      IsClosed (manifoldBoundary A) ∧ Nonempty (Manifold n (Interior (manifoldBoundary A)))) ∧
  (∀ (q : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold (q+1) .halfSpace M),
      Nonempty (Manifold q (manifoldBoundary A))) ∧
  (∀ (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold 0 .halfSpace M),
      manifoldBoundary A = ∅)

/-- Interior characterization and compact compatibility for the original
manifold-with-boundary input and its intrinsic boundary. The closedness and
boundaryless interior required by the construction are derived from its atlas. -/
def intrinsicInteriorClass : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M),
    let B := manifoldBoundary A
    ∀ (_c : Collar B) (AI : Manifold n (Interior B)) (o : Orientation R AI),
      IsCompact (Set.univ : Set M) →
      HasInteriorValues R B n o.val (fundamentalClass R B n o.val) ∧
      (∀ g : relativeHomology R R (boundaryPair M B) (n : ℤ),
        HasInteriorValues R B n o.val g → fundamentalClass R B n o.val = g) ∧
      (∀ K : Set (Interior B), IsCompact K →
        ∀ gK : SupportedGroup R (Interior B) K n, HasLocalValues R o.val K gK →
          AgreesOnCompact R B n K (fundamentalClass R B n o.val) gK)

/-- Unoriented comparison maps used for the source's collar-box calculation.
The interval-first sign and the global induced orientation are separate. -/
def modelComparisons : Prop :=
  (∀ (R : Type u) [CommRing R] (D : Type v) [TopologicalSpace D]
      (S : Set D) (j : ℤ),
    IsIso ((relativeHomologyFunctor R R j).map (BoxBottom.bottomInclusion S))) ∧
  (∀ (R : Type u) [CommRing R] (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (j : ℤ), IsIso ((relativeHomologyFunctor R R j).map (Disk.toLocal E)))

/-- The boundary and the localized triple have the same actual local groups
away from the closed complement of the chosen collar box. -/
def localBoundaryComparison : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]
    (A B : Set M), IsClosed A → ∀ (y : B), y.val ∉ A → ∀ j : ℕ,
      IsIso ((relativeHomologyFunctor R R (j : ℤ)).map
        (CollarLocalization.unionBoundaryLocalInclusion A B y))

open P202Specs.RelativeFundamentalClass.PrismLift P202Specs.ChainLES

/-- The actual ordinary connecting map of the model prism has the lower-end
minus sign. Its only chain premise is that c is a bottom relative cycle.
The short-exactness proof is quantified, not assumed as an orientation certificate. -/
def prismBoundarySign : Prop :=
  ∀ (R : Type u) [CommRing R] (D : Type) [TopologicalSpace D]
    (S : Set D) (n : ℕ) (c : Chains R (TopCat.of D) n)
    (hc : (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S)).d
      (n : ℤ) ((ComplexShape.down ℤ).next (n : ℤ))
      (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) = 0),
    ∀ hT : P202Specs.ChainLES.DegreewiseShortExact
      (Triple.tripleSequence (ordinaryFunctor R R) (Box.upperLateral_subset_fullBoundary S)),
    ∃ hp : (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S))).d
      (n+1 : ℕ) n
      (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
        (prismChain R (TopCat.of D) n c)) = 0,
      (connecting (hT) (n+1 : ℕ) n (by simp))
        (cycleClass (ordinary R R (boundaryPair (unitInterval × D) (Box.fullBoundary S)))
          (n : ℤ) (by simp)
          (quotientChain R (boundaryPair (unitInterval × D) (Box.fullBoundary S)) (n+1)
            (prismChain R (TopCat.of D) n c)) hp) =
      -((homologyMap (relativeMap (ordinaryFunctor R R)
          (P202Specs.RelativeFundamentalClass.BoxBottom.bottomInclusion S)) (n : ℤ))
        (cycleClass (ordinary R R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S))
          ((ComplexShape.down ℤ).next (n : ℤ)) rfl
          (quotientChain R (P202Specs.RelativeFundamentalClass.BoxBottom.bottomPair S) n c) hc))

/-- The actual prism-to-local comparison at its interior midpoint, and its
actual affine comparison with ambient local homology. -/
def prismComparisons : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (j : ℤ),
    IsIso ((relativeHomologyFunctor R R j).map (NormPrism.toOwnLocal V)) ∧
    IsIso ((relativeHomologyFunctor R R j).map (NormPrism.toAmbientLocal V))

/-- The larger open collar cylinder and smaller closed prism give the same
relative groups, also in the actual target of the triple connecting map. -/
def cylinderComparisons : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℤ),
    (∀ b : Bool, IsIso ((relativeHomologyFunctor R R j).map (CollarClamp.pairInclusion (E := E) b))) ∧
    IsIso ((relativeHomologyFunctor R R j).map (CollarClamp.tripleTargetInclusion (E := E)))

end Expected
/-- The ordinary fundamental class determined by a boundary local orientation.
Its characterization and existence are proved under the compact manifold
hypotheses; the chosen value itself contains no collar or sign certificate. -/
def boundaryClass (R : Type u) [CommRing R] (B : Type v) [TopologicalSpace B]
    (q : ℕ) (b : LocalChoice R q B) : homology R R (TopCat.of B) (q : ℤ) :=
  Classical.epsilon (fun a => HasLocalValues R b Set.univ (absoluteToSupported R B q a))

namespace Expected
/-- The induced boundary orientation is constructed and uniquely characterized
by the independent outward-normal-first signed product-box convention. For this
orientation the original positive connecting map takes the relative fundamental
class to the shared ordinary boundary fundamental class. -/
def inducedBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] (q : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M), IsClosed B → ∀ (c : Collar B)
    (AI : Manifold (q+1) (Interior B)) (AB : Manifold q B) (o : Orientation R AI),
    IsCompact (Set.univ : Set M) →
    (∃! b : Orientation R AB, IsOutwardNormalFirst R B c q o.val b.val) ∧
    ∀ b : Orientation R AB, IsOutwardNormalFirst R B c q o.val b.val →
      ∀ h : P202Specs.ChainLES.DegreewiseShortExact
        (sequence (ordinaryFunctor R R) (boundaryPair M B)),
        HasLocalValues R b.val Set.univ (absoluteToSupported R B q (boundaryClass R B q b.val)) ∧
        boundaryHomSucc R B h q (fundamentalClass R B (q+1) o.val) = boundaryClass R B q b.val

/-- The boundary equation for the original manifold-with-boundary input and
its intrinsic boundary. Its closedness is derived from the half-space atlas. -/
def intrinsicBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] (q : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold (q+1) .halfSpace M),
    let B := manifoldBoundary A
    ∀ (c : Collar B) (AI : Manifold (q+1) (Interior B)) (AB : Manifold q B)
      (o : Orientation R AI), IsCompact (Set.univ : Set M) →
    (∃! b : Orientation R AB, IsOutwardNormalFirst R B c q o.val b.val) ∧
    ∀ b : Orientation R AB, IsOutwardNormalFirst R B c q o.val b.val →
      ∀ h : P202Specs.ChainLES.DegreewiseShortExact
        (sequence (ordinaryFunctor R R) (boundaryPair M B)),
        HasLocalValues R b.val Set.univ (absoluteToSupported R B q (boundaryClass R B q b.val)) ∧
        boundaryHomSucc R B h q (fundamentalClass R B (q+1) o.val) = boundaryClass R B q b.val

/-- The induced local boundary orientation is independent of the specified
collar, as is the relative class characterized by its interior values. -/
def collarIndependence : Prop :=
  ∀ (R : Type u) [CommRing R] (q : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M]
    (B : Set M), IsClosed B → ∀ (c₁ c₂ : Collar B)
    (AI : Manifold (q+1) (Interior B)) (AB : Manifold q B) (o : Orientation R AI),
    IsCompact (Set.univ : Set M) → ∀ b₁ b₂ : Orientation R AB,
      IsOutwardNormalFirst R B c₁ q o.val b₁.val →
      IsOutwardNormalFirst R B c₂ q o.val b₂.val → b₁ = b₂

/-- In dimension zero the intrinsic boundary is empty and the connecting
homomorphism has its actual degree -1 target and is zero. -/
def zeroBoundary : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold 0 .halfSpace M)
    (h : P202Specs.ChainLES.DegreewiseShortExact
      (sequence (ordinaryFunctor R R) (boundaryPair M (manifoldBoundary A)))),
    manifoldBoundary A = ∅ ∧
      IsZero (homology R R (TopCat.of (manifoldBoundary A)) (-1)) ∧
      boundaryHom R (manifoldBoundary A) h 0 = 0
end Expected

end P202Specs.RelativeFundamentalClass
