import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.DualBasis
import MathGenome.Internal.AlgebraCore.P103.Ch02.Projective
import Mathlib.RingTheory.Finiteness.Cardinality

noncomputable section

universe u v w

namespace P103.Ch02.DualBasis

open P103.Specs.Ch02.DualBasis P103.Ch01

variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]

/-- Coordinates of a split embedding into a free module give a dual basis. -/
theorem dualBasis_of_retract {J : Type w} (i : P →ₗ[R] FreeModule R J)
    (r : FreeModule R J →ₗ[R] P) (h : r.comp i = LinearMap.id) :
    IsDualBasis (fun j => r (freeGenerator R J j))
      (fun j => (Finsupp.lapply j).comp i) := by
  classical
  constructor
  · intro x
    exact (i x).hasFiniteSupport
  · intro x s hs
    have hx : r (i x) = x := LinearMap.congr_fun h x
    calc
      x = ∑ j ∈ (i x).support, (i x) j • r (freeGenerator R J j) := by
        rw [← P103.Ch01.FreeModules.extension_formula R J P
          (fun j => r (freeGenerator R J j)) r (fun _ => rfl) (i x)]
        exact hx.symm
      _ = _ := by
        apply Finset.sum_subset
        · intro j hj
          exact hs j (Finsupp.mem_support_iff.mp hj)
        · intro j _ hj
          simp only [Finsupp.mem_support_iff, not_not] at hj
          simp [hj]

/-- Package the pointwise finite coefficients into a linear split embedding. -/
theorem projective_of_dualBasis : projective_of_dualBasisType.{u,v,w} := by
  intro R _ P _ _ J p φ h
  classical
  let i : P →ₗ[R] FreeModule R J :=
    { toFun := fun x => Finsupp.ofSupportFinite (fun j => φ j x) (h.1 x)
      map_add' := by intro x y; ext j; exact (φ j).map_add x y
      map_smul' := by intro a x; ext j; exact (φ j).map_smul a x }
  let r := Finsupp.linearCombination R p
  apply P103.Ch02.Projective.free_retract_projective R P J i r
  ext x
  exact (h.2 x (i x).support (fun j hj => Finsupp.mem_support_iff.mpr hj)).symm

theorem projective_iff_dualBasis : projective_iff_dualBasisType.{u,v,w} := by
  intro R _ P _ _
  constructor
  · intro h
    obtain ⟨J, Q, _, _, ⟨e⟩⟩ :=
      (P103.Ch02.Projective.projective_iff_freeSummand.{u,v,w} R P).mp h
    let i := e.toLinearMap.comp (LinearMap.inl R P Q)
    let r := (LinearMap.fst R P Q).comp e.symm.toLinearMap
    have hr : r.comp i = LinearMap.id := by ext x; simp [i, r]
    exact ⟨J, _, _, dualBasis_of_retract i r hr⟩
  · rintro ⟨J, p, φ, h⟩
    exact projective_of_dualBasis R P J p φ h

theorem finite_dualBasis : finite_dualBasisType.{u,v} := by
  intro R _ P _ _ _ _
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R P
  let e := Finsupp.linearEquivFunOnFinite R R (Fin n)
  let r := q.comp e.toLinearMap
  obtain ⟨i, hi⟩ := P103.Ch02.Projective.lifting R P (FreeModule R (Fin n)) P
    r LinearMap.id (hq.comp e.surjective)
  have hd := dualBasis_of_retract i r hi
  refine ⟨n, _, _, hd, ?_⟩
  intro x
  exact hd.2 x Finset.univ (by simp)

/-- The represented functional obeys φ(xr) = φ(x)r, in this order in R. -/
theorem right_functional_smul {R : Type u} [Ring R] {P : Type v} [AddCommGroup P]
    [Module Rᵐᵒᵖ P] (φ : P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) (x : P) (r : R) :
    MulOpposite.unop (φ (rightMul x r)) = MulOpposite.unop (φ x) * r := by
  simp [rightMul, map_smul, smul_eq_mul]

/-- Taking `unop` gives the usual scalar-valued right-linear functionals. -/
theorem right_dualBasis_iff {R : Type u} [Ring R] {P : Type v} [AddCommGroup P]
    [Module Rᵐᵒᵖ P] {J : Type w} (p : J → P) (φ : J → P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) :
    IsRightDualBasis p φ ↔ IsDualBasis p φ := by
  have hz (a : Rᵐᵒᵖ) : MulOpposite.unop a = 0 ↔ a = 0 :=
    ⟨fun h => MulOpposite.unop_injective h, fun h => congrArg MulOpposite.unop h⟩
  simp only [IsRightDualBasis, IsDualBasis, Function.support, ne_eq, hz, rightMul,
    MulOpposite.op_unop]

theorem right_projective_of_dualBasis : right_projective_of_dualBasisType.{u,v,w} := by
  intro R _ P _ _ J p φ h
  exact projective_of_dualBasis Rᵐᵒᵖ P J p φ ((right_dualBasis_iff p φ).mp h)

theorem right_projective_iff_dualBasis : right_projective_iff_dualBasisType.{u,v,w} := by
  intro R _ P _ _
  simpa only [← right_dualBasis_iff] using (projective_iff_dualBasis.{u,v,w} Rᵐᵒᵖ P)

theorem right_finite_dualBasis : right_finite_dualBasisType.{u,v} := by
  intro R _ P _ _ _ _
  obtain ⟨n, p, φ, h, hs⟩ := finite_dualBasis Rᵐᵒᵖ P
  exact ⟨n, p, φ, (right_dualBasis_iff p φ).mpr h, hs⟩

theorem empty_dualBasis : empty_dualBasisType.{u,v} := by
  intro R _ P _ _ _
  constructor
  · intro x
    exact Set.finite_empty.subset (by intro j; exact j.elim)
  · intro x s hs
    exact Subsingleton.elim _ _

end P103.Ch02.DualBasis
