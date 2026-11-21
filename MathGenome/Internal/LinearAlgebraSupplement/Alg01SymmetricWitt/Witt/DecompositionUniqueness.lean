import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.Cancellation

namespace Alg01SymmetricWitt.Witt.DecompositionUniqueness

open QuadraticMap
open Alg01SymmetricWitt.Witt.Coordinates (hyperbolicSum hyperbolicSum_apply
  hyperbolicNondegenerate nondegenerate_iff_associated_separatingLeft)

universe u v w x

section

variable {k : Type u} [Field k]
  {A : Type w} [AddCommGroup A] [Module k A]
  {A' : Type x} [AddCommGroup A'] [Module k A']

/-- Separate the first `r` planes and put them in the right summand for cancellation. -/
private def splitHyperbolicSum (q : QuadraticForm k A) (r d : ℕ) :
    ((hyperbolicSum k (r + d)).prod q).IsometryEquiv
      (((hyperbolicSum k d).prod q).prod (hyperbolicSum k r)) where
  toLinearEquiv := by
    let split : (Fin (r + d) → k × k) ≃ₗ[k]
        (Fin r → k × k) × (Fin d → k × k) :=
      (LinearEquiv.piCongrLeft' k (fun _ => k × k) finSumFinEquiv.symm).trans
        (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin d) k (k × k))
    exact (split.prodCongr (LinearEquiv.refl k A)).trans
      ((LinearEquiv.prodAssoc k (Fin r → k × k) (Fin d → k × k) A).trans
        (LinearEquiv.prodComm k (Fin r → k × k) ((Fin d → k × k) × A)))
  map_app' z := by
    change hyperbolicSum k d (fun j => z.1 (Fin.natAdd r j)) + q z.2 +
        hyperbolicSum k r (fun i => z.1 (Fin.castAdd d i)) =
      hyperbolicSum k (r + d) z.1 + q z.2
    simp only [hyperbolicSum_apply]
    rw [Fin.sum_univ_add]
    ac_rfl

variable [Invertible (2 : k)]

private theorem nondegenerate_of_anisotropic {q : QuadraticForm k A} (h : q.Anisotropic) :
    q.Nondegenerate :=
  (nondegenerate_iff_associated_separatingLeft q).2 (separatingLeft_of_anisotropic q h)

variable [FiniteDimensional k A] [FiniteDimensional k A']

/-- An anisotropic remainder prevents an isometric decomposition with extra planes. -/
private theorem hyperbolicCount_le (qA : QuadraticForm k A) (qA' : QuadraticForm k A')
    (hA : qA.Anisotropic) (hA' : qA'.Nondegenerate) {r s : ℕ}
    (h : ((hyperbolicSum k r).prod qA).Equivalent ((hyperbolicSum k s).prod qA')) :
    s ≤ r := by
  by_contra! hrs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs.le
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hrs)
  have hH := (hyperbolicNondegenerate k).2
  obtain ⟨f⟩ := h
  obtain ⟨e⟩ := Cancellation.cancel qA ((hyperbolicSum k d).prod qA') (hyperbolicSum k r)
    (nondegenerate_of_anisotropic hA) (LineCancellation.nondegenerate_prod (hH d) hA') (hH r)
    ⟨(IsometryEquiv.prodComm qA (hyperbolicSum k r)).trans
      (f.trans (splitHyperbolicSum qA' r d))⟩
  let z : (Fin d → k × k) × A' := (fun _ => (1, 0), 0)
  have hz : ((hyperbolicSum k d).prod qA') z = 0 := by simp [z]
  have hinv : e.symm z = 0 := hA _ ((e.symm.map_app z).trans hz)
  have hzero : z = 0 := by rw [← e.apply_symm_apply z, hinv, map_zero]
  have hcoord : (1 : k) = 0 :=
    congrArg (fun y : (Fin d → k × k) × A' => (y.1 ⟨0, hd⟩).1) hzero
  exact one_ne_zero hcoord

end

/-- Any two Witt decompositions have the same hyperbolic count and isometric remainders. -/
theorem decompositionUnique {k : Type u} {V : Type v} {A : Type w} {A' : Type x}
    [Field k] [Invertible (2 : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup A'] [Module k A'] [FiniteDimensional k A']
    (qV : QuadraticForm k V) (qA : QuadraticForm k A) (qA' : QuadraticForm k A')
    (r s : ℕ) (_hV : qV.Nondegenerate) (hA : qA.Anisotropic) (hA' : qA'.Anisotropic)
    (e : qV.Equivalent ((hyperbolicSum k r).prod qA))
    (e' : qV.Equivalent ((hyperbolicSum k s).prod qA')) :
    r = s ∧ qA.Equivalent qA' := by
  have h := e.symm.trans e'
  have hA_nd := nondegenerate_of_anisotropic hA
  have hA'_nd := nondegenerate_of_anisotropic hA'
  have hrs := le_antisymm (hyperbolicCount_le qA' qA hA' hA_nd h.symm)
    (hyperbolicCount_le qA qA' hA hA'_nd h)
  refine ⟨hrs, ?_⟩
  subst s
  obtain ⟨f⟩ := h
  exact Cancellation.cancel qA qA' (hyperbolicSum k r) hA_nd hA'_nd
    ((hyperbolicNondegenerate k).2 r)
    ⟨(IsometryEquiv.prodComm qA (hyperbolicSum k r)).trans
      (f.trans (IsometryEquiv.prodComm (hyperbolicSum k r) qA'))⟩

end Alg01SymmetricWitt.Witt.DecompositionUniqueness
