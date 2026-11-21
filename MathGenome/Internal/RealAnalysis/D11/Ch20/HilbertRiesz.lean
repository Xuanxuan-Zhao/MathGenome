import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.HilbertRiesz
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Hilbert-space Riesz representation, paper.tex:5690–5692.

Mathlib's `toDual` is the conjugate-linear isometric equivalence sending
`h` to the scalar-linear functional `x ↦ inner 𝕜 h x`. Its surjectivity
proof uses the orthogonal complement of the closed kernel, with no measure
theory, separability, or dimension restriction. Since the shared paper
convention is `innerFirst x h = inner 𝕜 h x`, its inverse is precisely the
required representing vector. The convention theorem records the conjugation
bridge and both slot laws explicitly.
-/

namespace D11.Ch20.HilbertRiesz

open D11.Ch20.OrthogonalProjection

universe u v

/-- Reversing Mathlib's arguments implements the source convention, with an
explicit conjugation equality; it keeps the represented functional scalar-linear. -/
theorem inner_convention : conventionStatement.{u, v} := by
  intro 𝕜 _ H _ _
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact (inner_conj_symm y x).symm
  · intro a x y z
    simp only [innerFirst, inner_add_right, inner_smul_right]
  · intro a x y z
    simp only [innerFirst, inner_add_left, inner_smul_left, starRingEnd_apply]

/-- Existence, norm equality, and uniqueness of the Hilbert representing
vector for every bounded scalar-linear functional, including zero. -/
theorem hilbert_riesz : statement.{u, v} := by
  intro 𝕜 _ H _ _ _ ℓ
  let h : H := (InnerProductSpace.toDual 𝕜 H).symm ℓ
  have hrep (x : H) : ℓ x = innerFirst (𝕜 := 𝕜) x h :=
    (InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (x := x) (y := ℓ)).symm
  refine ⟨h, hrep, (InnerProductSpace.toDual 𝕜 H).symm.norm_map ℓ, ?_⟩
  intro k hk
  apply ext_inner_right 𝕜
  intro x
  exact (hk x).symm.trans (hrep x)

end D11.Ch20.HilbertRiesz
