import MathGenome.Internal.Specs.D07.Ch21.ColumnOrthogonality
import MathGenome.Internal.D07.Ch21.CharacterCompleteness
import MathGenome.Internal.D07.Ch05.ConjugacyCounting

namespace D07.Ch21.ColumnOrthogonality

universe u r v
noncomputable section
open scoped Classical
open Specs.D07.Ch21.CharacterCompleteness
open Specs.D07.Ch21.HomPairing

variable {G : Type u} [Group G] [Fintype G]

/-- Orbit–stabilizer in a multiplication form, avoiding natural division. -/
lemma class_card_mul_centralizer_card (g : G) :
    Fintype.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g}) =
      Fintype.card G := by
  rw [← Nat.card_eq_fintype_card,
    D07.Ch05.ConjugacyCounting.conjugacy_class_card_eq_index]
  simpa only [Nat.card_eq_fintype_card] using
    (Subgroup.centralizer ({g} : Set G)).index_mul_card

/-- The conjugacy-class indicator scaled by the centralizer order. -/
def classIndicator (g : G) : classFunctions G :=
  ⟨fun x => if IsConj g x then (Nat.card (Subgroup.centralizer {g}) : ℂ) else 0, by
    intro x y hxy
    have h : IsConj g x ↔ IsConj g y :=
      ⟨fun hx => hx.trans hxy, fun hy => hy.trans hxy.symm⟩
    simp only [h]⟩

/-- Pairing against this indicator represents evaluation (conjugated because
the source's pairing is linear in its first argument). -/
lemma pairing_classIndicator (g : G) (f : classFunctions G) :
    pairingValue G (classIndicator g) f = starRingEnd ℂ (f.val g) := by
  have hs :
      (∑ x : G, (classIndicator g).val x * starRingEnd ℂ (f.val x)) =
        (Fintype.card (ConjClasses.mk g).carrier : ℂ) *
          ((Nat.card (Subgroup.centralizer {g}) : ℂ) * starRingEnd ℂ (f.val g)) := by
    calc
      _ = ∑ x : G, if IsConj g x then
          (Nat.card (Subgroup.centralizer {g}) : ℂ) * starRingEnd ℂ (f.val g) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : IsConj g x
        · simp only [classIndicator, ite_eq_left hx, f.property g x hx]
        · change (if IsConj g x then _ else _) * _ = _
          rw [ite_eq_right hx, zero_mul, ite_eq_right hx]
      _ = _ := by
        have hmem (x : G) : x ∈ (ConjClasses.mk g).carrier ↔ IsConj g x := by
          rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
          exact ⟨IsConj.symm, IsConj.symm⟩
        rw [Fintype.card_subtype]
        simp only [hmem]
        simp [Finset.sum_ite]
  have hc : (Fintype.card (ConjClasses.mk g).carrier : ℂ) *
      (Nat.card (Subgroup.centralizer {g}) : ℂ) = (Fintype.card G : ℂ) := by
    exact_mod_cast class_card_mul_centralizer_card g
  unfold pairingValue
  rw [hs, ← mul_assoc (Fintype.card (ConjClasses.mk g).carrier : ℂ), hc]
  apply inv_mul_cancel_left₀
  exact_mod_cast Fintype.card_ne_zero (α := G)

/-- Coordinates in an orthonormal basis for the normalized, linear-first
pairing are obtained by pairing the vector with each basis vector. -/
lemma repr_eq_pairing {I : Type r} [Fintype I]
    (B : Module.Basis I ℂ (classFunctions G))
    (hB : ∀ i j, pairingValue G (B i) (B j) = if i = j then 1 else 0)
    (f : classFunctions G) (j : I) : B.repr f j = pairingValue G f (B j) := by
  let L : classFunctions G →ₗ[ℂ] ℂ := {
    toFun := fun f => pairingValue G f (B j)
    map_add' := by intros; simp [pairingValue, add_mul, Finset.sum_add_distrib, mul_add]
    map_smul' := by intros; simp [pairingValue, mul_assoc, Finset.mul_sum, mul_left_comm]
  }
  have h := congrArg L (B.sum_repr f)
  simp only [map_sum, map_smul] at h
  change (∑ i, B.repr f i • pairingValue G (B i) (B j)) = pairingValue G f (B j) at h
  simpa only [hB, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- Expand the scaled class indicator in the complete orthonormal character
basis. Conjugating the resulting evaluation identity gives the source's
ordering of the two character factors. -/
theorem column_orthogonality :
    Specs.D07.Ch21.ColumnOrthogonality.SecondOrthogonality.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  obtain ⟨hf, B, hB, hO⟩ :=
    D07.Ch21.CharacterCompleteness.character_basis G I V ρ hi hne hc
  refine ⟨hf, ?_⟩
  intro g h
  have he : (∑ i, starRingEnd ℂ ((B i).val g) * (B i).val h) =
      (classIndicator g).val h := by
    calc
      _ = ∑ i, B.repr (classIndicator g) i * (B i).val h := by
        apply Finset.sum_congr rfl
        intro i _
        rw [repr_eq_pairing B hO, pairing_classIndicator]
      _ = _ := by
        have heval := congrArg (fun f : classFunctions G => f.val h)
          (B.sum_repr (classIndicator g))
        simpa only [Submodule.coe_sum, Finset.sum_apply,
          Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using heval
  have heconj := congrArg (starRingEnd ℂ) he
  simpa only [map_sum, map_mul, starRingEnd_self_apply, hB, classIndicator,
    apply_ite, map_natCast, map_zero, mul_comm] using heconj

end
end D07.Ch21.ColumnOrthogonality
