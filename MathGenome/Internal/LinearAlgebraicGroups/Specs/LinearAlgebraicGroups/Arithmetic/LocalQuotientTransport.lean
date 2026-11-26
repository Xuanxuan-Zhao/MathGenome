import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Subgroup

open Filter MeasureTheory Set
open scoped Topology InnerProductSpace

namespace LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport

universe u v w

variable {G : Type u} {G' : Type v} [Group G] [Group G']

/-- The space of cosets `Hg`, with the quotient topology when `G` is topological. -/
abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

abbrev coset (H : Subgroup G) (g : G) : RightCosets H := @Quotient.mk' _ (QuotientGroup.rightRel H) g

instance {H : Subgroup G} [TopologicalSpace G] : MeasurableSpace (RightCosets H) := borel _
instance {H : Subgroup G} [TopologicalSpace G] : BorelSpace (RightCosets H) := ⟨rfl⟩

/-- Right translation on the quotient by the left multiplication action of `H`. -/
def rightTranslate {H : Subgroup G} (a : G) : RightCosets H → RightCosets H :=
  Quotient.map' (· * a) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h

variable [TopologicalSpace G] [TopologicalSpace G']

abbrev imageSubgroup (e : G ≃ₜ* G') (H : Subgroup G) : Subgroup G' :=
  H.map e.toMulEquiv.toMonoidHom

/-- Equivariance for the right action, relative to a given isomorphism of acting groups. -/
def Equivariant (e : G ≃ₜ* G') {H : Subgroup G} {H' : Subgroup G'}
    (q : RightCosets H → RightCosets H') : Prop :=
  ∀ (x : RightCosets H) (a : G), q (rightTranslate a x) = rightTranslate (e a) (q x)

/-- Right invariance for the Borel measure and all right translations. -/
def RightInvariant {H : Subgroup G} (μ : Measure (RightCosets H)) : Prop :=
  ∀ a : G, MeasurePreserving (rightTranslate a) μ μ

noncomputable abbrev L2 {H : Subgroup G} (μ : Measure (RightCosets H)) := Lp ℂ 2 μ

/-- The unitary right translation acts on representatives by `f(x) ↦ f(xa)`. -/
noncomputable def rightOperator {H : Subgroup G} {μ : Measure (RightCosets H)}
    (hμ : RightInvariant μ) (a : G) : L2 μ →ₗᵢ[ℂ] L2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (rightTranslate a) (hμ a)

/-- The algebraic normal closure followed by topological closure. -/
abbrev closedNormalClosure [IsTopologicalGroup G] (s : Set G) : Subgroup G :=
  (Subgroup.normalClosure s).topologicalClosure

namespace Specs

/-- Membership, closedness, and discreteness with the subgroup topology. -/
def SubgroupTransport : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (e : G ≃ₜ* G') (H : Subgroup G),
  (∀ g : G, e g ∈ imageSubgroup e H ↔ g ∈ H) ∧
  (IsClosed (H : Set G) ↔ IsClosed (imageSubgroup e H : Set G')) ∧
  (DiscreteTopology H ↔ DiscreteTopology (imageSubgroup e H))

def QuotientAction : Prop :=
  ∀ {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G),
  IsOpenQuotientMap (coset H) ∧
  (∀ x y : G, coset H x = coset H y ↔ ∃ b ∈ H, x = b * y) ∧
  Continuous (fun p : RightCosets H × G => rightTranslate p.2 p.1)

/-- The quotient equivalence is induced by the isomorphism on representatives. -/
def QuotientTransport : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']
    (e : G ≃ₜ* G') (H : Subgroup G),
  ∃ q : RightCosets H ≃ₜ RightCosets (imageSubgroup e H),
    (∀ g : G, q (coset H g) = coset (imageSubgroup e H) (e g)) ∧ Equivariant e q

def MeasureTransport : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']
    (e : G ≃ₜ* G') {H : Subgroup G} {H' : Subgroup G'}
    (q : RightCosets H ≃ₜ RightCosets H') (_hq : Equivariant e q)
    (μ : Measure (RightCosets H)) (_hμ : RightInvariant μ)
    [IsFiniteMeasure μ] (_h₀ : μ ≠ 0),
  let ν := μ.map q
  IsFiniteMeasure ν ∧ ν ≠ 0 ∧ RightInvariant ν ∧
    (∀ s : Set (RightCosets H'), ν s = μ (q ⁻¹' s))

def RepresentationLaw : Prop :=
  ∀ {G : Type u} [Group G]
    [TopologicalSpace G]
    {H : Subgroup G} {μ : Measure (RightCosets H)}
    (hμ : RightInvariant μ),
  (∀ f : L2 μ, rightOperator hμ 1 f = f) ∧
  (∀ (a b : G) (f : L2 μ), rightOperator hμ (a * b) f =
    rightOperator hμ a (rightOperator hμ b f))

/-- Pullback across the inverse quotient homeomorphism preserves the right translation
representation and transports its matrix coefficients and operator limits. -/
def RepresentationTransport : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (e : G ≃ₜ* G') {H : Subgroup G} {H' : Subgroup G'}
    (q : RightCosets H ≃ₜ RightCosets H') (_hq : Equivariant e q)
    (μ : Measure (RightCosets H)) (hμ : RightInvariant μ)
    (hν : RightInvariant (μ.map q)),
  ∃ U : L2 μ ≃ₗᵢ[ℂ] L2 (μ.map q),
    (∀ f : L2 μ, (U f : RightCosets H' → ℂ) =ᵐ[μ.map q] (f ∘ q.symm)) ∧
    (∀ f : L2 (μ.map q), (U.symm f : RightCosets H → ℂ) =ᵐ[μ] (f ∘ q)) ∧
    (∀ (a : G) (f : L2 μ), U (rightOperator hμ a f) = rightOperator hν (e a) (U f)) ∧
    (∀ (a : G) (f g : L2 μ),
      ⟪rightOperator hν (e a) (U f), U g⟫_ℂ = ⟪rightOperator hμ a f, g⟫_ℂ) ∧
    (∀ {ι : Type w} (l : Filter ι) (a : ι → G) (f g : L2 μ) (z : ℂ),
      Tendsto (fun i => ⟪rightOperator hν (e (a i)) (U f), U g⟫_ℂ) l (𝓝 z) ↔
      Tendsto (fun i => ⟪rightOperator hμ (a i) f, g⟫_ℂ) l (𝓝 z)) ∧
    (∀ (c : ℂ) (f : L2 μ), (U f : RightCosets H' → ℂ) =ᵐ[μ.map q] (fun _ => c) ↔
      (f : RightCosets H → ℂ) =ᵐ[μ] (fun _ => c)) ∧
    (∀ f : L2 μ, Continuous (fun b : G' => rightOperator hν b (U f)) ↔
      Continuous (fun a : G => rightOperator hμ a f)) ∧
    (∀ {ι : Type w} (l : Filter ι) (a : ι → G) (B : L2 μ →WOT[ℂ] L2 μ),
      let V := U.toContinuousLinearEquiv
      let B' := ContinuousLinearMapWOT.ofCLM
        (V.toContinuousLinearMap.comp (B.toCLM.comp V.symm.toContinuousLinearMap))
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM
        (rightOperator hν (e (a i))).toContinuousLinearMap) l (𝓝 B') ↔
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM
        (rightOperator hμ (a i)).toContinuousLinearMap) l (𝓝 B))

def NormalClosureTransport : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']
    (e : G ≃ₜ* G') (s : Set G),
  imageSubgroup e (closedNormalClosure s) = closedNormalClosure (e '' s)

def GroupConvergence : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (e : G ≃ₜ* G') {ι : Type w} (l : Filter ι)
    (g : ι → G) (x : G),
  Tendsto (e ∘ g) l (𝓝 (e x)) ↔ Tendsto g l (𝓝 x)

/-- Includes contraction by powers (with `y = 1`) and conjugation by a varying group element
(with `n = 0`). -/
def RescalingConvergence : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (e : G ≃ₜ* G') {ι : Type w} (l : Filter ι)
    (a : G) (n : ι → ℕ) (y h : ι → G) (r : G),
  Tendsto (fun i => (e a ^ n i)⁻¹ * (e (y i))⁻¹ * e (h i) * e (y i) * e a ^ n i)
    l (𝓝 (e r)) ↔
  Tendsto (fun i => (a ^ n i)⁻¹ * (y i)⁻¹ * h i * y i * a ^ n i) l (𝓝 r)

def QuotientConvergence : Prop :=
  ∀ {G : Type u} {G' : Type v} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (e : G ≃ₜ* G') {H : Subgroup G} {H' : Subgroup G'}
    (q : RightCosets H ≃ₜ RightCosets H') (_hq : Equivariant e q)
    {ι : Type w} (l : Filter ι) (g : ι → RightCosets H) (x : RightCosets H),
  (Tendsto (q ∘ g) l (𝓝 (q x)) ↔ Tendsto g l (𝓝 x)) ∧
    ∀ a : ι → G,
      Tendsto (fun i => rightTranslate (e (a i)) (q (g i))) l (𝓝 (q x)) ↔
      Tendsto (fun i => rightTranslate (a i) (g i)) l (𝓝 x)

end Specs
end LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
