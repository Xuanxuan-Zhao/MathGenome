import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleOperations
import Mathlib.Topology.Order.Compact

/-! M05.08, paper.tex:1338--1343. The bundle below is the actual quotient
of the restricted ambient tangent bundle by the image of the inclusion
differential. Both base manifolds are boundaryless; neither is assumed compact,
nonempty, or closed in any ambient space. -/
set_option autoImplicit false
namespace SmoothManifolds.AbstractTubularData
open ModelData AtlasData MapData BundleData BundleOperationsData TangentData
  QuotientData Bundle Module Set
universe u

variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}

abbrev NormalFiber (N : NormalBundle T S i) (p : P) :=
  QuotientFiber (E := fun p => TangentSpace S (i p))
    (fun p => LinearMap.range (N.differential p)) p

abbrev NormalTotal (N : NormalBundle T S i) :=
  Bundle.TotalSpace (Euclidean (n - m)) (NormalFiber N)

/-- Use the topology of the already constructed quotient bundle. -/
abbrev normalTopology (N : NormalBundle T S i) : TopologicalSpace (NormalTotal N) := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  exact N.quotient.topology
attribute [local instance] normalTopology

/-- The quotient bundle with all upstream topology arguments fixed. -/
abbrev normalBundle (N : NormalBundle T S i) :
    SmoothVectorBundle T (n - m) P (NormalFiber N) := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  exact N.quotient.bundle

def normalZero (N : NormalBundle T S i) (p : P) : NormalTotal N := ⟨p, 0⟩

def normalScale (N : NormalBundle T S i) (t : ℝ) (z : NormalTotal N) :
    NormalTotal N := ⟨z.proj, t • z.snd⟩

/-- An actual smooth linear lift of quotient classes. The right-inverse law
identifies its image as a complement of TS, without replacing quotient fibers. -/
structure NormalLift (N : NormalBundle T S i) where
  linearMap : (p : P) → NormalFiber N p →ₗ[ℝ] TangentSpace S (i p)
  right_inverse : ∀ p v, (LinearMap.range (N.differential p)).mkQ (linearMap p v) = v
  smooth : letI := N.ambientRealization.space.topology
    letI := N.pullback.space.topology
    IsSmoothMap (normalBundle N).totalManifold N.pullback.space.bundle.totalManifold
      (fun z => (⟨z.proj, linearMap z.proj z.snd⟩ :
        Bundle.TotalSpace (Euclidean n) (fun p => TangentSpace S (i p))))

/-- A local diffeomorphism near the entire zero section. This is intermediate
construction data, never an assumption of the final theorem. Total values of
`map` outside `domain` have no prescribed smoothness. -/
structure TubularGerm (N : NormalBundle T S i) where
  domain : Set (NormalTotal N)
  isOpen_domain : IsOpen domain
  zero_mem : ∀ p, normalZero N p ∈ domain
  map : NormalTotal N → M
  zero_eq : ∀ p, map (normalZero N p) = i p
  smooth : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
    S.smoothStructure.val map domain
  local_inverse : ∀ z ∈ domain,
    ∃ e : OpenPartialHomeomorph (NormalTotal N) M,
      z ∈ e.source ∧ e.source ⊆ domain ∧ EqOn e map e.source ∧
      ManifoldSmoothOn S.smoothStructure.val
        (normalBundle N).totalManifold.smoothStructure.val e.symm e.target

/-- Open neighborhoods with a genuine smooth inverse, on the prescribed
quotient normal bundle. Star-shapedness is scalar multiplication in those
quotient fibers, with every parameter in the full closed interval [0,1]. -/
structure TubularNeighborhood (N : NormalBundle T S i) where
  domain : Set (NormalTotal N)
  target : Set M
  isOpen_domain : IsOpen domain
  isOpen_target : IsOpen target
  zero_mem : ∀ p, normalZero N p ∈ domain
  star : ∀ z ∈ domain, ∀ t ∈ Icc (0 : ℝ) 1, normalScale N t z ∈ domain
  inclusion_mem : range i ⊆ target
  homeomorph : domain ≃ₜ target
  zero_eq : ∀ p, (homeomorph ⟨normalZero N p, zero_mem p⟩).val = i p
  smooth : ManifoldSmooth
    (openSubsetAtlas (normalBundle N).totalManifold.smoothStructure.val domain isOpen_domain)
    (openSubsetAtlas S.smoothStructure.val target isOpen_target) homeomorph
  inverse_smooth : ManifoldSmooth
    (openSubsetAtlas S.smoothStructure.val target isOpen_target)
    (openSubsetAtlas (normalBundle N).totalManifold.smoothStructure.val domain isOpen_domain)
    homeomorph.symm

end SmoothManifolds.AbstractTubularData

namespace Specs.SmoothManifolds.Ch05.AbstractTubular
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.AbstractTubularData
universe u

/-- The normal structure as well as the tubular diffeomorphism are outputs.
An arbitrary embedding represents an embedded submanifold with its subspace
topology; in particular the statement specializes to subset inclusion. -/
def abstract_tubularType : Prop :=
  ∀ {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M), IsSmoothEmbedding T S i →
    ∃ N : NormalBundle T S i, Nonempty (TubularNeighborhood N)

def normalLift_existsType : Prop :=
  ∀ {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M) (N : NormalBundle T S i), Nonempty (NormalLift N)

end Specs.SmoothManifolds.Ch05.AbstractTubular
