import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.OrthogonalSplitting
import Mathlib.LinearAlgebra.Projection

namespace Alg01SymmetricWitt.Witt.OrthogonalSplitting

universe u v

variable {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
  [AddCommGroup V] [Module k V]

/-- The orthogonal complement for the normalized associated bilinear form. -/
def orthogonalComplement (q : QuadraticForm k V) (U : Submodule k V) : Submodule k V :=
  Specs.Alg01SymmetricWitt.Witt.OrthogonalSplitting.orthogonalComplement q U

theorem mem_orthogonalComplement (q : QuadraticForm k V) (U : Submodule k V) (x : V) :
    x ∈ orthogonalComplement q U ↔ ∀ u ∈ U, q.associated x u = 0 := by
  change x ∈ LinearMap.BilinForm.orthogonal q.associated U ↔ _
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  have hRefl := (QuadraticForm.associated_isSymm k q).isRefl
  exact ⟨fun h u hu => hRefl u x (h u hu), fun h u hu => hRefl x u (h u hu)⟩

theorem orthogonalSplitting [FiniteDimensional k V]
    (q : QuadraticForm k V) (U : Submodule k V)
    (hq : q.Nondegenerate) (hU : (q.comp U.subtype).Nondegenerate) :
    let W := orthogonalComplement q U
    IsCompl U W ∧
      (∃ e : ((q.comp U.subtype).prod (q.comp W.subtype)).IsometryEquiv q,
        ∀ z : U × W, e z = (z.1 : V) + (z.2 : V)) ∧
      (q.comp W.subtype).Nondegenerate := by
  let B : LinearMap.BilinForm k V := q.associated
  let W := orthogonalComplement q U
  have hRefl : B.IsRefl := (QuadraticForm.associated_isSymm k q).isRefl
  have hB : B.Nondegenerate := QuadraticMap.nondegenerate_associated_iff.mpr hq
  have hRestrict (S : Submodule k V) :
      (B.restrict S).Nondegenerate ↔ (q.comp S.subtype).Nondegenerate := by
    rw [← QuadraticMap.nondegenerate_associated_iff, QuadraticMap.associated_comp]
    rfl
  have hCompl : IsCompl U W :=
    B.isCompl_orthogonal_of_restrict_nondegenerate hRefl ((hRestrict U).mpr hU)
  have hWW : B.orthogonal W = U := B.orthogonal_orthogonal hB hRefl U
  have hW : (q.comp W.subtype).Nondegenerate :=
    (hRestrict W).mp <| B.nondegenerate_restrict_of_disjoint_orthogonal hRefl (by
      rw [hWW]
      exact hCompl.symm.disjoint)
  let e : ((q.comp U.subtype).prod (q.comp W.subtype)).IsometryEquiv q :=
    { U.prodEquivOfIsCompl W hCompl with
      map_app' := fun z => QuadraticMap.associated_isOrtho.mp (z.2.property z.1 z.1.property) }
  exact ⟨hCompl, ⟨e, fun _ => rfl⟩, hW⟩

end Alg01SymmetricWitt.Witt.OrthogonalSplitting
