import MathGenome.Internal.Specs.D07.Ch12.PowerBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Power bases and polynomial representatives

K07.12.power_basis, paper.tex:3607–3613.
Over a field algebraicity implies integrality. The canonical intermediate-field
power basis transports the polynomial-quotient basis along evaluation; it has
exactly the degree of the minimal polynomial as its length. Spanning supplies
a polynomial representative. The difference of two bounded representatives
would be a smaller-degree annihilator, so minimality proves uniqueness.
-/

universe u v

namespace D07.Ch12.PowerBasis

open Specs.D07.Ch12.PowerBasis
open Polynomial

theorem powerBasisExists : PowerBasisExists.{u, v} := by
  intro K L _ _ _ α hα
  let pb := IntermediateField.adjoin.powerBasis hα.isIntegral
  refine ⟨minpoly.natDegree_pos hα.isIntegral, pb.basis, ?_⟩
  intro i
  exact (congrArg (fun y : IntermediateField.adjoin K {α} => (y : L))
    (pb.basis_eq_pow i)).trans (by simp [pb])

theorem uniquePolynomialRepresentative : UniquePolynomialRepresentative.{u, v} := by
  intro K L _ _ _ α hα x
  let pb := IntermediateField.adjoin.powerBasis hα.isIntegral
  obtain ⟨p, hp, hxp⟩ := pb.exists_eq_aeval x
  have hdegree : p.degree < (minpoly K α).degree := by
    rw [degree_eq_natDegree (minpoly.ne_zero hα.isIntegral)]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hp)
  have heval : aeval α p = (x : L) := by
    have hx := congrArg (fun y : IntermediateField.adjoin K {α} => (y : L)) hxp
    simpa [pb, ← aeval_algebraMap_apply] using hx.symm
  refine ⟨p, ⟨hdegree, heval⟩, ?_⟩
  intro q hq
  apply sub_eq_zero.mp
  by_contra hne
  have hz : aeval α (q - p) = 0 := by rw [map_sub, hq.2, heval, sub_self]
  have hsmall : (q - p).degree < (minpoly K α).degree :=
    degree_sub_le q p |>.trans_lt (max_lt hq.1 hdegree)
  exact (minpoly.degree_le_of_ne_zero K α hne hz).not_gt hsmall

end D07.Ch12.PowerBasis
