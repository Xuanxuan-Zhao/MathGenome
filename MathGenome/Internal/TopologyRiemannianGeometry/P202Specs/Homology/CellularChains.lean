import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains

/-! Cellular chains, paper.tex 1533–1542 and 1552–1565.
The skeleta are the actual subspaces of the given CW structure. Coefficients
are arbitrary modules (abelian-group coefficients are obtained with R = ℤ).
The total connecting-map definition below uses the usual connecting morphism
when the chain inclusion is short exact, and zero otherwise. The implementation
proves short exactness for every pair, so the fallback is never used here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w

namespace P202Specs.CellularChains
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.ChainLES

variable (X : Type w) [TopologicalSpace X] [CellStructure X]

/-- `skeletalSpace X n` is X^(n-1), including the empty space at n = 0. -/
abbrev skeletalSpace (n : ℕ) : TopCat.{w} := TopCat.of (skeletonLT X n)

/-- The actual skeletal pair (X^n, X^(n-1)). -/
def skeletalPair (n : ℕ) : Pair.{w} :=
  ⟨skeletalSpace X (n+1), {x | x.val ∈ skeletonLT X n}⟩

lemma skeletonLT_subset {m n : ℕ} (h : m ≤ n) : skeletonLT X m ⊆ skeletonLT X n := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hkm, hx⟩
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨lt_of_lt_of_le hkm h, hx⟩⟩

/-- Flattening the subspace of a skeleton uses its genuine subspace topology. -/
def lowerHomeomorph (n : ℕ) : (skeletalPair X n).sub ≃ₜ skeletalSpace X n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, skeletonLT_subset X (Nat.le_succ n) x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def lowerMap (n : ℕ) : (skeletalPair X n).sub ⟶ skeletalSpace X n :=
  TopCat.ofHom ⟨lowerHomeomorph X n, (lowerHomeomorph X n).continuous⟩

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Totalized only to make the independent definitions require no certificates. -/
def pairConnecting (P : Pair.{w}) (n : ℕ) :
    relativeHomology R M P ((n+1 : ℕ) : ℤ) ⟶
      (ordinaryComplex R M P.sub).homology (n : ℤ) :=
  open Classical in
  if h : DegreewiseShortExact (sequence (ordinaryFunctor R M) P) then
    connecting h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp)
  else 0

lemma pairConnecting_eq (P : Pair.{w}) (n : ℕ)
    (h : DegreewiseShortExact (sequence (ordinaryFunctor R M) P)) :
    pairConnecting R M P n = connecting h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp) := by
  simp [pairConnecting, h]

/-- An elementary identity needed to construct the canonical complex.
It follows from the library connecting-map identity, even for a totalized map. -/
lemma projection_pairConnecting (P : Pair.{w}) (n : ℕ) :
    homologyMap (projection (ordinaryFunctor R M) P) ((n+1 : ℕ) : ℤ) ≫
      pairConnecting R M P n = 0 := by
  classical
  by_cases h : DegreewiseShortExact (sequence (ordinaryFunctor R M) P)
  · rw [pairConnecting_eq R M P n h]
    exact (HomologicalComplex.shortExact_of_degreewise_shortExact _ h).comp_δ _ _ _
  · simp [pairConnecting, h]

abbrev chainGroup (n : ℕ) : ModuleCat.{max v w} R :=
  relativeHomology R M (skeletalPair X n) (n : ℤ)

/-- d_(n+1) = relative projection after the positive connecting map. -/
def differential (n : ℕ) : chainGroup X R M (n+1) ⟶ chainGroup X R M n :=
  pairConnecting R M (skeletalPair X (n+1)) n ≫
    (homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1)) ≫
    homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)

/-- The identity needed by `ChainComplex.of`; this is independent of cell counts. -/
lemma differential_comp (n : ℕ) :
    differential X R M (n+1) ≫ differential X R M n = 0 := by
  dsimp only [differential]
  simp only [Category.assoc]
  rw [← Category.assoc (homologyMap (projection (ordinaryFunctor R M)
    (skeletalPair X (n+1))) ((n+1 : ℕ) : ℤ)), projection_pairConnecting]
  simp

/-- Nonnegative cellular chains. All maps out of degree zero are zero by shape. -/
def cellularComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (chainGroup X R M) (differential X R M) (differential_comp X R M)

end P202Specs.CellularChains

namespace P202.Cellular

/-- A continuous map preserving the specified skeleta, with no finiteness
assumptions and no change of the CW structures. -/
structure CellularMap (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y]
    [CellStructure X] [CellStructure Y] where
  map : C(X, Y)
  skeletal : ∀ n, Set.MapsTo map (skeletonLT X n) (skeletonLT Y n)

namespace CellularMap
variable {X Y Z : Type w} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [CellStructure X] [CellStructure Y] [CellStructure Z]

def id (X : Type w) [TopologicalSpace X] [CellStructure X] : CellularMap X X :=
  ⟨ContinuousMap.id X, fun _ _ h => h⟩

def comp (g : CellularMap Y Z) (f : CellularMap X Y) : CellularMap X Z :=
  ⟨g.map.comp f.map, fun n _ h => g.skeletal n (f.skeletal n h)⟩

open P202Specs.CellularChains P202Specs.RelativeSingularChains

def onSkeleton (f : CellularMap X Y) (n : ℕ) : skeletalSpace X n ⟶ skeletalSpace Y n :=
  TopCat.ofHom ⟨fun x => ⟨f.map x.val, f.skeletal n x.property⟩,
    (f.map.continuous.comp continuous_subtype_val).subtype_mk _⟩

def onPair (f : CellularMap X Y) (n : ℕ) : skeletalPair X n ⟶ skeletalPair Y n :=
  ⟨f.onSkeleton (n+1), fun _ h => f.skeletal n h⟩

end CellularMap
end P202.Cellular

namespace P202Specs.CellularChains
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.ChainLES

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  [CellStructure X] [CellStructure Y]

/-- The prescribed map on each chain group is induced by the skeletal pair. -/
def cellularDegreeMap (f : CellularMap X Y) (n : ℕ) :
    chainGroup X R M n ⟶ chainGroup Y R M n :=
  (relativeHomologyFunctor R M (n : ℤ)).map (f.onPair n)

/-- A copy of the Euclidean disk pair in the universe of the cell labels.
The lift carries its usual transported topology; projection down is a homeomorphism. -/
def referenceDiskPair (n : ℕ) : Pair.{w} :=
  ⟨TopCat.of (ULift.{w} (Disk n)), {x | ‖x.down.val‖ = 1}⟩

/-- The universe lift is explicitly identified with the source's Euclidean disk. -/
def referenceDiskHomeomorph (n : ℕ) : (referenceDiskPair.{w} n).space ≃ₜ Disk n where
  toEquiv := Equiv.ulift
  continuous_toFun := continuous_uliftDown
  continuous_invFun := continuous_uliftUp

/-- Characteristic map of a cell as a map of disk and skeletal pairs. -/
def characteristicPairMap {X : Type w} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) : referenceDiskPair.{w} n ⟶ skeletalPair X n where
  map := TopCat.ofHom ⟨fun x => diskToSkeleton X CWStructure.boundary_lands n c x.down,
    ((characteristic X n c).continuous.comp continuous_uliftDown).subtype_mk _⟩
  mapsTo := by
    intro x hx
    change ‖x.down.val‖ = 1 at hx
    exact CWStructure.boundary_lands n c (Set.mem_univ ⟨x.down.val, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩)

namespace Expected

/-- This fixes the shift relative to the source's integer-indexed skeleta. -/
def skeletalIndexing : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X] (n : ℕ),
    skeletonLT X (n+1) = skeleton X (n : ℤ) ∧
    skeletonLT X n = skeleton X ((n : ℤ)-1)

/-- Preserving the chosen nonnegative skeleta is precisely the source's
cellularity condition; the empty skeleton adds no restriction. -/
def mapCriterion : Prop :=
  ∀ (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y] [CWStructure X] [CWStructure Y]
    (f : C(X, Y)),
    (∀ n, Set.MapsTo f (skeletonLT X n) (skeletonLT Y n)) ↔
      (∀ n : ℕ, Set.MapsTo f (skeleton X (n : ℤ)) (skeleton Y (n : ℤ)))

/-- Definitions have independently specified types and values. -/
def complex_type := ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
  (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
  ChainComplex (ModuleCat.{max v w} R) ℕ

def complex_value (X : Type w) [TopologicalSpace X] [CWStructure X]
  (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :=
  cellularComplex X R M

def formulas : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    skeleton X (-1) = ∅ ∧
    (∀ n, (cellularComplex X R M).X n = relativeHomology R M (skeletalPair X n) (n : ℤ)) ∧
    (∀ j, (cellularComplex X R M).d 0 j = 0) ∧
    (∀ n, ∃ h : DegreewiseShortExact (sequence (ordinaryFunctor R M) (skeletalPair X (n+1))),
      (cellularComplex X R M).d (n+1) n =
        connecting h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp) ≫
        (homologyFunctor R M (n : ℤ)).map
          (lowerMap X (n+1)) ≫
        homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ))

def squareZero : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ),
    differential X R M (n+1) ≫ differential X R M n = 0

def maps : Prop :=
  ∀ (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y] [CWStructure X] [CWStructure Y]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (f : CellularMap X Y),
    ∃ F : cellularComplex X R M ⟶ cellularComplex Y R M,
      ∀ n, F.f n = cellularDegreeMap R M f n

/-- The discrete zero-skeleton case, including an empty set of vertices. -/
def zeroSkeleton : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    DiscreteTopology (skeletalSpace X 1) ∧
    Nonempty (chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M)) ∧
    ∀ j : ℕ, j ≠ 0 → IsZero (relativeHomology R M (skeletalPair X 0) (j : ℤ))

/-- Direct SUM, with characteristic-map compatibility for every choice of a
reference disk orientation. All physical orientation choices are included.
The same disk equivalence is used at every cell of the given dimension. -/
def cellGroups : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ),
    Nonempty (chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M))

def orientedCoordinates : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)),
    ∃ e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M),
      ∀ c m, e ((relativeHomologyFunctor R M (n : ℤ)).map
        (characteristicPairMap n c) (g m)) = Finsupp.single c m

def relativeVanishing : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n j : ℕ),
    j ≠ n → IsZero (relativeHomology R M (skeletalPair X n) (j : ℤ))

end Expected
end P202Specs.CellularChains
