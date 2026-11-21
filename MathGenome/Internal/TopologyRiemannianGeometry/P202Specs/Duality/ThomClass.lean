import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.AbstractTubular

/-!
The first conclusion of `lem:p202-projective-thom`, paper.tex 2539–2574.
The transverse product conclusion is allocated separately.

Manifolds, tangent differentials and the quotient normal bundle are P104's
actual objects. An R-orientation is a locally compatible family of generators
of the relative cohomology of the normal fibers. Local compatibility is tested
in the given bundle trivializations, without assuming a class on the total
bundle or on the ambient manifold. No ambient orientation is part of the data.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData

universe u v
namespace P202Specs.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs

variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}

attribute [local instance] normalTopology

/-- The actual ambient relative pair, with the complement of the embedded image. -/
def ambientPair (i : P → M) : Pair.{u} :=
  ⟨TopCat.of M, (Set.range i)ᶜ⟩

/-- A normal fiber as a subspace of the actual quotient bundle total space.
Its points are quotient normal vectors, with their original base point. -/
abbrev Fiber (N : NormalBundle T S i) (p : P) :=
  {z : NormalTotal N // z.proj = p}

def fiberOrigin (N : NormalBundle T S i) (p : P) : Fiber N p :=
  ⟨normalZero N p, rfl⟩

def fiberPair (N : NormalBundle T S i) (p : P) : Pair.{u} :=
  ⟨TopCat.of (Fiber N p), {z | z ≠ fiberOrigin N p}⟩

/-- The model is lifted only to keep pair maps in the same universe as M.
At rank zero its complement is empty. -/
def modelPair (k : ℕ) : Pair.{u} :=
  ⟨TopCat.of (ULift.{u} (Euclidean k)), {z | z.down ≠ 0}⟩

/-- The homeomorphism on one fiber induced by an original normal bundle chart. -/
def fiberChart (N : NormalBundle T S i)
    (a : P) (p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    Fiber N p ≃ₜ ULift.{u} (Euclidean (n-m)) :=
  ((normalBundle N).trivialization a).preimageSingletonHomeomorph
    (by rwa [(normalBundle N).trivialization_baseSet a]) |>.trans Homeomorph.ulift.symm

lemma fiberChart_origin (N : NormalBundle T S i)
    (a : P) (p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    (fiberChart N a p hp (fiberOrigin N p)).down = 0 := by
  let e := (normalBundle N).trivialization a
  letI : e.IsLinear ℝ := (normalBundle N).linear a
  have hp' : p ∈ e.baseSet := by
    change p ∈ ((normalBundle N).trivialization a).baseSet
    rwa [(normalBundle N).trivialization_baseSet a]
  exact (e.linearEquivAt ℝ p hp').map_zero

/-- The actual induced relative map of a fiber chart. -/
def fiberCoordinates (N : NormalBundle T S i)
    (a : P) (p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    fiberPair N p ⟶ modelPair.{u} (n-m) where
  map := TopCat.ofHom ⟨fiberChart N a p hp, (fiberChart N a p hp).continuous⟩
  mapsTo := by
    intro z hz hzero
    apply hz
    apply (fiberChart N a p hp).injective
    apply ULift.ext
    exact hzero.trans (fiberChart_origin N a p hp).symm

/-- Linear coordinates in a prescribed quotient normal fiber. -/
def fiberLinearCoordinates (N : NormalBundle T S i)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    NormalFiber N p ≃ₗ[ℝ] Euclidean (n-m) := by
  let e := (normalBundle N).trivialization a
  letI : e.IsLinear ℝ := (normalBundle N).linear a
  exact e.linearEquivAt ℝ p (by
    change p ∈ ((normalBundle N).trivialization a).baseSet
    rwa [(normalBundle N).trivialization_baseSet a])

/-- The tubular map on a fixed normal fiber in its original linear coordinates.
Outside the tubular domain it is totalized by its value at the origin. -/
def fiberImage (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) (v : Euclidean (n-m)) : M := by
  classical
  let z : NormalTotal N := ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩
  exact if hz : z ∈ K.domain then (K.homeomorph ⟨z, hz⟩).val else i p

/-- The normal differential of a tubular map is the identity on the actual
quotient normal fiber. P104's bare TubularNeighborhood does not include this
first-order normalization. It rules out an unrecorded fiber reflection.
Only one pair of charts at each point is needed to test the intrinsic equality. -/
def NormalCompatible (N : NormalBundle T S i) (K : TubularNeighborhood N) : Prop :=
  ∀ p : P, ∃ (a : P) (hp : p ∈ (normalBundle N).baseSet a)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpc : i p ∈ c.source) (L : Euclidean (n-m) →L[ℝ] Euclidean n),
      HasFDerivAt (fun v => (c (fiberImage N K a p hp v)).val) L 0 ∧
      ∀ v : Euclidean (n-m),
        (LinearMap.range (N.differential p)).mkQ
          ((N.ambientTangent.fiberCoordinates.equiv c hc (i p) hpc).symm (L v)) =
            (fiberLinearCoordinates N a p hp).symm v

variable (R : Type v) [CommRing R]

/-- Locally compatible fiber generators are precisely the cohomological
R-orientation data. The generator condition includes arbitrary rings, including
the zero ring. `locally_constant` asks only for a class on the model fiber. -/
structure Orientation (N : NormalBundle T S i) (d : ℕ) where
  generator : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ)
  generates : ∀ p, Function.Bijective (fun r : R => r • generator p)
  locally_constant : ∀ p : P,
    ∃ (a : P) (U : Set P),
      IsOpen U ∧ p ∈ U ∧
      ∃ hU : U ⊆ (normalBundle N).baseSet a,
        ∃ c : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ),
          ∀ (q : P) (hq : q ∈ U),
            (relativeCohomologyFunctor R R (d : ℤ)).map
              (fiberCoordinates N a q (hU hq)).op c = generator q

/-- The part of a normal fiber lying in a tubular neighborhood's domain. -/
abbrev Slice (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) :=
  {z : NormalTotal N // z.proj = p ∧ z ∈ K.domain}

def slicePair (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) : Pair.{u} :=
  ⟨TopCat.of (Slice N K p), {z | z.val ≠ normalZero N p}⟩

/-- Restriction from the full normal fiber to the tubular slice. -/
def sliceToFiber (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) :
    slicePair N K p ⟶ fiberPair N p where
  map := TopCat.ofHom ⟨fun z => ⟨z.val, z.property.1⟩,
    continuous_subtype_val.subtype_mk _⟩
  mapsTo := by
    intro z hz heq
    exact hz (congrArg Subtype.val heq)

/-- The tubular image of a nonzero normal vector misses the embedded submanifold.
This is proved from the genuine inverse and the zero-section identity. -/
lemma tubular_mem_range_iff (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (p : P) (z : Slice N K p) :
    (K.homeomorph ⟨z.val, z.property.2⟩).val ∈ Set.range i ↔
      z.val = normalZero N p := by
  constructor
  · rintro ⟨q, hq⟩
    have heq : K.homeomorph ⟨z.val, z.property.2⟩ =
        K.homeomorph ⟨normalZero N q, K.zero_mem q⟩ :=
      Subtype.ext (hq.symm.trans (K.zero_eq q).symm)
    have hz : z.val = normalZero N q :=
      congrArg Subtype.val (K.homeomorph.injective heq)
    have hpq : p = q := z.property.1.symm.trans (congrArg Bundle.TotalSpace.proj hz)
    exact hz.trans (congrArg (normalZero N) hpq.symm)
  · intro hz
    exact ⟨p, by
      have hh : (⟨z.val, z.property.2⟩ : K.domain) =
          ⟨normalZero N p, K.zero_mem p⟩ := Subtype.ext hz
      rw [hh, K.zero_eq]⟩

/-- The normal slice mapped into the actual ambient pair by the tubular map. -/
def sliceToAmbient (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) :
    slicePair N K p ⟶ ambientPair i where
  map := TopCat.ofHom ⟨fun z => (K.homeomorph ⟨z.val, z.property.2⟩).val,
    continuous_subtype_val.comp
      (K.homeomorph.continuous.comp (continuous_subtype_val.subtype_mk _))⟩
  mapsTo := by
    intro z hz h
    exact hz ((tubular_mem_range_iff N K p z).mp h)

/-- Intrinsic fiber restriction: the ambient class gives the specified generator
on every normalized tubular normal slice. Quantifying over all tubular choices makes the
statement independent of an auxiliary neighborhood. -/
def HasFiberValues {N : NormalBundle T S i} {d : ℕ} (o : Orientation R N d)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) : Prop :=
  ∀ (K : TubularNeighborhood N), NormalCompatible N K → ∀ p : P,
    (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToAmbient N K p).op c =
      (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToFiber N K p).op (o.generator p)

/-- Full original target. Compactness is imposed only on the embedded manifold.
P104's SmoothManifold includes Hausdorffness and second countability. The rank
condition is vacuous on the empty submanifold, permitting every empty-case degree.
No ambient orientation, connectedness, positive rank, field or PID is assumed.
The existence of the tubular neighborhood is a conclusion, not a certificate. -/
def exists_unique_type : Prop :=
  ∀ (R : Type v) [CommRing R] (m n d : ℕ)
    (P M : Type u) [TopologicalSpace P] [TopologicalSpace M] [CompactSpace P]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M), IsSmoothEmbedding T S i →
    ∀ (N : NormalBundle T S i), (∀ _ : P, d = n-m) →
      ∀ o : Orientation R N d,
        (∃ K : TubularNeighborhood N, NormalCompatible N K) ∧
          ∃! c : relativeCohomology R R (ambientPair i) (d : ℤ), HasFiberValues R o c

end P202Specs.ThomClass
