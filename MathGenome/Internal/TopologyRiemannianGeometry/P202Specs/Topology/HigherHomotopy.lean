import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.FundamentalGroupoid
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Canonical cube and relative-path objects for paper.tex, lines 898–922.
The opposite corrects Mathlib's reversed multiplication in every positive
dimension. All spaces are arbitrary topological spaces.
-/
namespace P202Specs.Topology

open scoped unitInterval _root_.Topology
universe u v w
noncomputable section

abbrev UnitCube (n : ℕ) := Fin n → unitInterval
abbrev CubeBoundary (n : ℕ) : Set (UnitCube n) := Cube.boundary (Fin n)
abbrev CubeMap (n : ℕ) {X : Type u} [TopologicalSpace X] (x : X) :=
  ↥(GenLoop (Fin n) X x)
abbrev CubeHomotopy {n : ℕ} {X : Type u} [TopologicalSpace X] {x : X}
    (a b : CubeMap n x) := a.val.HomotopyRel b.val (CubeBoundary n)

/-- Positive-dimensional groups use the paper's first-map-first product.
The same type is meaningful in dimension zero, without a group instance. -/
abbrev HigherPi (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :=
  (HomotopyGroup (Fin n) X x)ᵐᵒᵖ

def cubeClass {n : ℕ} {X : Type u} [TopologicalSpace X] {x : X}
    (a : CubeMap n x) : HigherPi n X x := MulOpposite.op (Quotient.mk _ a)

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Actual postcomposition, for all pointed continuous maps. -/
def cubeMap {n : ℕ} {x : X} {y : Y} (f : PointedMap X Y x y)
    (a : CubeMap n x) : CubeMap n y :=
  ⟨f.map.comp a.val, fun t ht => by
    change f.map (a t) = y
    exact (congrArg f.map (GenLoop.boundary a t ht)).trans f.point⟩

theorem cubeMap_homotopic {n : ℕ} {x : X} {y : Y}
    (f : PointedMap X Y x y) {a b : CubeMap n x} (h : GenLoop.Homotopic a b) :
    GenLoop.Homotopic (cubeMap f a) (cubeMap f b) := by
  obtain ⟨H⟩ := h
  exact ⟨H.compContinuousMap f.map⟩

theorem cubeMap_transAt {n : ℕ} {x : X} {y : Y}
    (f : PointedMap X Y x y) (i : Fin n) (a b : CubeMap n x) :
    cubeMap f (GenLoop.transAt i a b) =
      GenLoop.transAt i (cubeMap f a) (cubeMap f b) := by
  ext t
  change f.map (if _ then _ else _) = if _ then _ else _
  split_ifs <;> rfl

/-- The raw library map, with its library multiplication convention. -/
def rawHigherMap (n : ℕ) {x : X} {y : Y} (f : PointedMap X Y x y) :
    HomotopyGroup (Fin (n + 1)) X x →* HomotopyGroup (Fin (n + 1)) Y y where
  toFun := Quotient.map (cubeMap f) (fun _ _ => cubeMap_homotopic f)
  map_one' := by
    change Quotient.mk _ (cubeMap f GenLoop.const) = Quotient.mk _ GenLoop.const
    congr 1
    ext t
    exact f.point
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))), Quotient.map_mk]
    exact congrArg (Quotient.mk _) (cubeMap_transAt f 0 q p)

/-- Induced homomorphism with the corrected paper convention. -/
def higherInduced (n : ℕ) {x : X} {y : Y} (f : PointedMap X Y x y) :
    HigherPi (n + 1) X x →* HigherPi (n + 1) Y y := oppositeHom (rawHigherMap n f)

/-- The bridge preserves the actual loop, including its orientation. -/
def higherPiOneEquiv (x : X) : HigherPi 1 X x ≃* Pi1 X x :=
  oppositeEquiv (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x))

abbrev PathComponents (X : Type u) [TopologicalSpace X] := ZerothHomotopy X

def componentMap (f : C(X, Y)) : PathComponents X → PathComponents Y :=
  Quotient.map f (fun _ _ h => h.map f.continuous)

/-- The ordinary closed Euclidean disk, including the one-point zero-disk. -/
abbrev ClosedDisk (n : ℕ) := {z : EuclideanSpace ℝ (Fin n) // ‖z‖ ≤ 1}
def DiskBoundary (n : ℕ) : Set (ClosedDisk n) := {z | ‖z.val‖ = 1}

/-- A relative disk maps its entire boundary into the specified subspace.
This does not assert a relative group structure in dimension one. -/
def RelativeDiskMap (n : ℕ) (A : Set X) :=
  {f : C(ClosedDisk n, X) // ∀ t ∈ DiskBoundary n, f t ∈ A}

/-- The disk compression condition used in disk replacement: the entire boundary
is held pointwise fixed, and the terminal disk takes values in the subspace. -/
def RelativeDiskCondition (n : ℕ) (A : Set X) : Prop :=
  ∀ f : RelativeDiskMap n A, ∃ g : C(ClosedDisk n, A),
    Nonempty (f.val.HomotopyRel
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp g) (DiskBoundary n))

/-- A relative one-dimensional representative starts at the specified basepoint
and ends at an arbitrary point of the subspace. -/
structure RelativePath (A : Set X) (x : A) where
  map : C(unitInterval, X)
  source : map 0 = x.val
  target_mem : map 1 ∈ A

/-- Relative homotopies fix the initial endpoint and keep the terminal endpoint
in the subspace, allowing it to move. -/
def RelativePathHomotopy {A : Set X} {x : A} (a b : RelativePath A x) :=
  a.map.HomotopyWith b.map (fun f => f 0 = x.val ∧ f 1 ∈ A)

def relativePathSetoid (A : Set X) (x : A) : Setoid (RelativePath A x) where
  r a b := Nonempty (RelativePathHomotopy a b)
  iseqv := ⟨fun a => ⟨ContinuousMap.HomotopyWith.refl a.map ⟨a.source, a.target_mem⟩⟩,
    fun ⟨H⟩ => ⟨H.symm⟩, fun ⟨H⟩ ⟨K⟩ => ⟨H.trans K⟩⟩

/-- A pointed set only; no group structure is asserted. -/
def RelativePiOne (A : Set X) (x : A) := Quotient (relativePathSetoid A x)

def relativePathClass {A : Set X} {x : A} (a : RelativePath A x) : RelativePiOne A x :=
  Quotient.mk _ a

def relativeOnePoint (A : Set X) (x : A) : RelativePiOne A x :=
  relativePathClass ⟨ContinuousMap.const _ x.val, rfl, x.property⟩

instance {A : Set X} {x : A} : Inhabited (RelativePiOne A x) := ⟨relativeOnePoint A x⟩

/-- A moving-boundary homotopy over exactly the given basepoint path. This
intrinsic characterization is independent of a choice of concentric collar. -/
structure MovingCubeHomotopy {n : ℕ} {x y : X} (d : Path x y)
    (a : CubeMap n x) (b : CubeMap n y) extends a.val.Homotopy b.val where
  boundary : ∀ t z, z ∈ CubeBoundary n → toHomotopy (t, z) = d t

namespace ExpectedHigher

def classEquality : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) (a b : CubeMap n x),
    cubeClass a = cubeClass b ↔ Nonempty (CubeHomotopy a b)

def groupConvention : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X),
    (∀ (i : Fin (n + 1)) (a b : CubeMap (n + 1) x),
      cubeClass (GenLoop.transAt i a b) = cubeClass a * cubeClass b) ∧
    cubeClass (GenLoop.const : CubeMap (n + 1) x) = 1 ∧
    (∀ (i : Fin (n + 1)) (a : CubeMap (n + 1) x),
      cubeClass (GenLoop.symmAt i a) = (cubeClass a)⁻¹)

def inducedFormula : Prop :=
  ∀ (n : ℕ) (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f : PointedMap X Y x y) (a : CubeMap (n + 1) x),
    higherInduced n f (cubeClass a) = cubeClass (cubeMap f a)

def functoriality : Prop :=
  (∀ (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X),
    higherInduced n (PointedMap.id x) = MonoidHom.id (HigherPi (n + 1) X x)) ∧
  (∀ (n : ℕ) (X : Type u) (Y : Type v) (Z : Type w)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (x : X) (y : Y) (z : Z) (f : PointedMap X Y x y) (g : PointedMap Y Z y z),
    higherInduced n (g.comp f) = (higherInduced n g).comp (higherInduced n f))

def basedHomotopy : Prop :=
  ∀ (n : ℕ) (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f g : PointedMap X Y x y),
    Nonempty (f.BasedHomotopy g) → higherInduced n f = higherInduced n g

def pointedEquivalence : Prop :=
  ∀ (n : ℕ) (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (e : PointedHomotopyEquivalence X Y x y),
    ∃ E : HigherPi (n + 1) X x ≃* HigherPi (n + 1) Y y,
      (∀ a, E a = higherInduced n e.forward a) ∧
      (∀ b, E.symm b = higherInduced n e.backward b)

def piOneFormula : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (x : X) (a : CubeMap 1 x),
    higherPiOneEquiv x (cubeClass a) = loopClass (genLoopEquivOfUnique (Fin 1) a)

def piOneNaturality : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f : PointedMap X Y x y) (a : HigherPi 1 X x),
    higherPiOneEquiv y (higherInduced 0 f a) = f.induced (higherPiOneEquiv x a)

/-- Existence for every representative, with no additional hypotheses on X. -/
def movingCubeLift : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] (x y : X) (d : Path x y)
    (a : CubeMap (n + 1) x), ∃ b : CubeMap (n + 1) y,
      Nonempty (MovingCubeHomotopy d a b)

/-- Transport goes from the initial to the final basepoint, as in the collar
paragraph. The moving-homotopy identity characterizes it on all representatives,
using the separately specified existence of moving cube homotopies. -/
def basepointTransport : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] (x y : X) (d : Path x y),
    ∃ E : HigherPi (n + 1) X x ≃* HigherPi (n + 1) X y,
      ∀ (a : CubeMap (n + 1) x) (b : CubeMap (n + 1) y),
        Nonempty (MovingCubeHomotopy d a b) → E (cubeClass a) = cubeClass b

/-- The transport is determined by the path, independently of collar choices. -/
def basepointTransportUnique : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] (x y : X) (d : Path x y)
    (E E' : HigherPi (n + 1) X x ≃* HigherPi (n + 1) X y),
    (∀ (a : CubeMap (n + 1) x) (b : CubeMap (n + 1) y),
      Nonempty (MovingCubeHomotopy d a b) → E (cubeClass a) = cubeClass b) →
    (∀ (a : CubeMap (n + 1) x) (b : CubeMap (n + 1) y),
      Nonempty (MovingCubeHomotopy d a b) → E' (cubeClass a) = cubeClass b) → E = E'

/-- Explicit consequence for maps joined by an ordinary, unbased homotopy.
It is stated together with the intrinsic transport characterization so the
isomorphism is determined by the trace path rather than chosen ad hoc. -/
def unbasedHomotopy : Prop :=
  ∀ (n : ℕ) (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (F : f.Homotopy g) (x : X),
    ∃ E : HigherPi (n + 1) Y (f x) ≃* HigherPi (n + 1) Y (g x),
      (∀ (a : CubeMap (n + 1) (f x)) (b : CubeMap (n + 1) (g x)),
        Nonempty (MovingCubeHomotopy (F.evalAt x) a b) →
          E (cubeClass a) = cubeClass b) ∧
      E.toMonoidHom.comp (higherInduced n (⟨f, rfl⟩ : PointedMap X Y x (f x))) =
        higherInduced n (⟨g, rfl⟩ : PointedMap X Y x (g x))

def components : Prop :=
  (∀ (X : Type u) [TopologicalSpace X] (x y : X),
    ZerothHomotopy.mk x = ZerothHomotopy.mk y ↔ Nonempty (Path x y)) ∧
  (∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)), Nonempty (f.Homotopy g) → componentMap f = componentMap g)

def relativePathEquality : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (A : Set X) (x : A) (a b : RelativePath A x),
    relativePathClass a = relativePathClass b ↔ Nonempty (RelativePathHomotopy a b)

end ExpectedHigher
end
end P202Specs.Topology
