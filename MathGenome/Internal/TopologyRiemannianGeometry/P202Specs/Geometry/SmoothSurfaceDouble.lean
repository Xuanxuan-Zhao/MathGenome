import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.Collar
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-! Independent canonical objects for the collar-built double in paper.tex
5016–5031. The quotient topology is the existing Quotient topology, not a chosen
atlas topology. Smooth structures below are outputs, never input certificates.
The always-two-copy convention also applies when the boundary is empty. -/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.BoundaryData SmoothManifolds.CollarData
universe u
namespace P202Specs.SmoothSurfaceDouble
variable {M : Type u} [TopologicalSpace M]

def doubleSetoid (B : Set M) : Setoid (Bool × M) where
  r x y := x.2 = y.2 ∧ (x.1 = y.1 ∨ x.2 ∈ B)
  iseqv := {
    refl := fun x => ⟨rfl, Or.inl rfl⟩
    symm := by
      rintro x y ⟨hxy, h⟩
      exact ⟨hxy.symm, h.elim (fun e => Or.inl e.symm) (fun b => Or.inr (hxy ▸ b))⟩
    trans := by
      rintro x y z ⟨hxy, h⟩ ⟨hyz, k⟩
      refine ⟨hxy.trans hyz, ?_⟩
      rcases h with h | h
      · rcases k with k | k
        · exact Or.inl (h.trans k)
        · exact Or.inr (hxy ▸ k)
      · exact Or.inr h }

abbrev Double (B : Set M) := Quotient (doubleSetoid B)

def copy (B : Set M) (s : Bool) (x : M) : Double B := Quotient.mk _ (s, x)

noncomputable def fold (B : Set M) : Double B → M :=
  Quotient.lift Prod.snd (fun _ _ h => h.1)



def side (B : Set M) (s : Bool) : Set (Double B) :=
  {q | ∃ x, x ∉ B ∧ copy B s x = q}

/-- The actual seam, with no auxiliary parametrization. -/
def seam (B : Set M) : Set (Double B) := copy B false '' B

def seamMap (B : Set M) (q : B) : Double B := copy B false q.val

abbrev SurfaceDouble {kind : ModelKind} (S : SmoothManifold 2 kind M) :=
  Double (intrinsicBoundary S)

/-- Positive signed time labels the true copy. -/
def sign (s : Bool) : ℝ := if s then 1 else -1

abbrev SignedTime := ↥(Ioo (-1 : ℝ) 1)

def signedTime (s : Bool) (t : CollarTime) : SignedTime :=
  ⟨sign s * t.val, by
    cases s <;> simp only [sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
    · exact ⟨neg_lt_neg t.property.2, (neg_nonpos.mpr t.property.1).trans_lt zero_lt_one⟩
    · exact ⟨(by norm_num : (-1 : ℝ) < 0).trans_le t.property.1, t.property.2⟩⟩

/-- The topological bicollar has its actual product source and actual open image. -/
structure SignedCollar {kind : ModelKind} {S : SmoothManifold 2 kind M}
    (C : SmoothCollar S) where
  homeomorph : (intrinsicBoundary S × SignedTime) ≃ₜ
    (fold (intrinsicBoundary S) ⁻¹' C.neighborhood)
  copy_time : ∀ s q t,
    (homeomorph (q, signedTime s t)).val =
      copy (intrinsicBoundary S) s (C.toHomeomorph (q,t)).val

/-- Full output of the smooth gluing construction. Exact signed charts retain
both the induced boundary coordinates and the local side of each original copy.
The inverse extensions are Euclidean-valued, so they can extend across the seam
without being required to remain in a half-space. -/
structure SmoothDouble {kind : ModelKind} (S : SmoothManifold 2 kind M) where
  hausdorff : T2Space (SurfaceDouble S)
  compact : CompactSpace (SurfaceDouble S)
  secondCountable : SecondCountableTopology (SurfaceDouble S)
  copy_closedEmbedding : ∀ s, IsClosedEmbedding (copy (intrinsicBoundary S) s)
  copies_cover : range (copy (intrinsicBoundary S) false) ∪
    range (copy (intrinsicBoundary S) true) = univ
  copies_intersect : range (copy (intrinsicBoundary S) false) ∩
    range (copy (intrinsicBoundary S) true) = seam (intrinsicBoundary S)
  collar : SmoothCollar S
  bicollar : SignedCollar collar
  manifold : SmoothManifold 2 .euclidean (SurfaceDouble S)
  no_boundary : intrinsicBoundary manifold = ∅
  copy_smooth : ∀ s, IsSmoothMap S manifold (copy (intrinsicBoundary S) s)
  boundary : SmoothManifold 1 .euclidean (intrinsicBoundary S)
  boundary_inclusion_smooth : IsSmoothMap boundary S Subtype.val
  boundary_induced : ∀ e ∈ S.smoothStructure.val,
    Nonempty {q : intrinsicBoundary S // q.val ∈ e.source} →
    ∃ b ∈ boundary.smoothStructure.val, IsFaceRestriction S e b
  seam_compact : CompactSpace (intrinsicBoundary S)
  seam_finite_components : Finite (ConnectedComponents (intrinsicBoundary S))
  seam_closedEmbedding : IsClosedEmbedding (seamMap (intrinsicBoundary S))
  seam_smooth : IsSmoothMap boundary manifold (seamMap (intrinsicBoundary S))
  signed_charts : ∀ b ∈ boundary.smoothStructure.val,
    ∃ d ∈ manifold.smoothStructure.val,
      d.source = Subtype.val ''
        (bicollar.homeomorph '' (b.source ×ˢ (univ : Set SignedTime))) ∧
      d.target = {z : ModelSpace 2 .euclidean |
        (⟨Fin.init z.val, mem_univ _⟩ : ModelSpace 1 .euclidean) ∈ b.target ∧
        z.val (Fin.last 1) ∈ Ioo (-1 : ℝ) 1} ∧
      (∀ q ∈ b.source, ∀ t : SignedTime,
        (d (bicollar.homeomorph (q,t)).val).val = Fin.snoc (b q).val t.val) ∧
      (∀ z ∈ d.source,
        (z ∈ range (copy (intrinsicBoundary S) true) ↔ 0 ≤ (d z).val (Fin.last 1)) ∧
        (z ∈ range (copy (intrinsicBoundary S) false) ↔ (d z).val (Fin.last 1) ≤ 0) ∧
        (z ∈ seam (intrinsicBoundary S) ↔ (d z).val (Fin.last 1) = 0))
  chart_refinement : ∀ s e, e ∈ S.smoothStructure.val → ∀ p ∈ e.source,
    ∃ d ∈ manifold.smoothStructure.val,
      copy (intrinsicBoundary S) s p ∈ d.source ∧
      copy (intrinsicBoundary S) s ⁻¹' d.source ⊆ e.source
  inverse_coordinate_extensions : ∀ s e, e ∈ S.smoothStructure.val → ∀ p ∈ e.source,
    ∃ U : Set (SurfaceDouble S), IsOpen U ∧ copy (intrinsicBoundary S) s p ∈ U ∧
      copy (intrinsicBoundary S) s ⁻¹' U ⊆ e.source ∧
      ∃ F : SurfaceDouble S → Euclidean 2,
        (∀ z ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
          manifold.smoothStructure.val F z) ∧
        ∀ x, copy (intrinsicBoundary S) s x ∈ U →
          F (copy (intrinsicBoundary S) s x) = (e x).val

namespace Expected

def construction : Prop := ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  [CompactSpace M] (S : SmoothManifold 2 kind M), Nonempty (SmoothDouble S)

/-- The complete topological stage, independently useful for the signed atlas. -/
def topology : Prop := ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  [CompactSpace M] (S : SmoothManifold 2 kind M),
  T2Space (SurfaceDouble S) ∧ CompactSpace (SurfaceDouble S) ∧
  (∀ s, IsClosedEmbedding (copy (intrinsicBoundary S) s)) ∧
  range (copy (intrinsicBoundary S) false) ∪ range (copy (intrinsicBoundary S) true) = univ ∧
  range (copy (intrinsicBoundary S) false) ∩ range (copy (intrinsicBoundary S) true) =
    seam (intrinsicBoundary S)

/-- Collar, countability and the induced compact boundary, all constructed
without an assumed double atlas. -/
def collarTopology : Prop := ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  [CompactSpace M] (S : SmoothManifold 2 kind M),
  ∃ C : SmoothCollar S, ∃ H : SignedCollar C,
    SecondCountableTopology (SurfaceDouble S) ∧
    (∀ q t,
      ((H.homeomorph (q,t)).val ∈ range (copy (intrinsicBoundary S) true) ↔ 0 ≤ t.val) ∧
      ((H.homeomorph (q,t)).val ∈ range (copy (intrinsicBoundary S) false) ↔ t.val ≤ 0) ∧
      ((H.homeomorph (q,t)).val ∈ seam (intrinsicBoundary S) ↔ t.val = 0)) ∧
    ∃ B : SmoothManifold 1 .euclidean (intrinsicBoundary S),
      IsSmoothMap B S Subtype.val ∧
      (∀ e ∈ S.smoothStructure.val,
        Nonempty {q : intrinsicBoundary S // q.val ∈ e.source} →
        ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S e b) ∧
      CompactSpace (intrinsicBoundary S) ∧
      Finite (ConnectedComponents (intrinsicBoundary S)) ∧
      IsClosedEmbedding (seamMap (intrinsicBoundary S))

end Expected
end P202Specs.SmoothSurfaceDouble
