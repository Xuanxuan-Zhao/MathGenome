import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Independent statements for paper.tex, §v03-05, Theorem `thm:hilbert-projection`
(lines 1564–1601). The ambient space is an arbitrary complete real or complex
inner product space, with no dimension or nontriviality assumption.
-/

noncomputable section
universe u
namespace VariationalNotes.Existence.Specs

/-- The canonical choice of a nearest point, from the Hilbert projection theorem. -/
def realProjection {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : H) : H :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv x)

def realProjectionType : Type (u+1) :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H), C.Nonempty → IsClosed C → Convex ℝ C → H → H

def realProjection_nearest : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x : H, realProjection C hne hclosed hconv x ∈ C ∧
    ∀ y ∈ C, ‖x - realProjection C hne hclosed hconv x‖ ≤ ‖x - y‖

def realProjection_unique : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x p : H,
    (p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖) ↔
      p = realProjection C hne hclosed hconv x

def realProjection_existsUnique : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H) (_hne : C.Nonempty) (_hclosed : IsClosed C) (_hconv : Convex ℝ C),
  ∀ x : H, ∃! p : H, p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖

def realProjection_variational : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x p : H, p = realProjection C hne hclosed hconv x ↔
    p ∈ C ∧ ∀ y ∈ C, inner ℝ (x - p) (y - p) ≤ 0

def realProjection_firm : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x z : H,
    ‖realProjection C hne hclosed hconv x - realProjection C hne hclosed hconv z‖ ^ 2 ≤
    inner ℝ (realProjection C hne hclosed hconv x - realProjection C hne hclosed hconv z) (x - z)

def realProjection_nonexpansive : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  LipschitzWith 1 (realProjection C hne hclosed hconv)

def realProjection_continuous : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  Continuous (realProjection C hne hclosed hconv)

section Complex
-- This structure uses the existing norm, metric, and topology of H.
attribute [local instance] InnerProductSpace.complexToReal

/-- The complex projection is the projection on the underlying real Hilbert space. -/
def complexProjection {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) : H → H := realProjection C hne hclosed hconv

def complexProjectionType : Type (u+1) :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H), C.Nonempty → IsClosed C → Convex ℝ C → H → H

def complexProjection_nearest : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x : H, complexProjection C hne hclosed hconv x ∈ C ∧
    ∀ y ∈ C, ‖x - complexProjection C hne hclosed hconv x‖ ≤ ‖x - y‖

def complexProjection_unique : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x p : H,
    (p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖) ↔
      p = complexProjection C hne hclosed hconv x

def complexProjection_existsUnique : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H) (_hne : C.Nonempty) (_hclosed : IsClosed C) (_hconv : Convex ℝ C),
  ∀ x : H, ∃! p : H, p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖

def complexProjection_variational : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x p : H, p = complexProjection C hne hclosed hconv x ↔
    p ∈ C ∧ ∀ y ∈ C, (inner ℂ (x - p) (y - p)).re ≤ 0

def complexProjection_firm : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  ∀ x z : H,
    ‖complexProjection C hne hclosed hconv x - complexProjection C hne hclosed hconv z‖ ^ 2 ≤
    (inner ℂ (complexProjection C hne hclosed hconv x - complexProjection C hne hclosed hconv z) (x - z)).re

def complexProjection_nonexpansive : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  LipschitzWith 1 (complexProjection C hne hclosed hconv)

def complexProjection_continuous : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
  Continuous (complexProjection C hne hclosed hconv)

end Complex
end VariationalNotes.Existence.Specs
