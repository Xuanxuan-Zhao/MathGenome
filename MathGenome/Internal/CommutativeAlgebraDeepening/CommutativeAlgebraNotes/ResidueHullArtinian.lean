import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ResidueHullArtinian
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.EndomorphismsOfResidueHull
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualExactDetection
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedNoetherian

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion)

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The completed scalars whose associated endomorphism vanishes on a submodule. -/
private def hullAnnihilator {E : ResidueFieldEnvelope R}
    (e : Completion R ≃ₐ[R] Module.End R E.carrier) (U : Submodule R E.carrier) :
    Ideal (Completion R) where
  carrier := {s | ∀ x ∈ U, e s x = 0}
  zero_mem' := by
    intro x _
    rw [map_zero, LinearMap.zero_apply]
  add_mem' := by
    intro a b ha hb x hx
    rw [map_add, LinearMap.add_apply, ha x hx, hb x hx, add_zero]
  smul_mem' := by
    intro a b hb x hx
    change e (a * b) x = 0
    rw [map_mul, Module.End.mul_apply, hb x hx, map_zero]

/-- A functional on the quotient detects any vector outside the submodule. -/
private theorem le_of_hullAnnihilator_le {E : ResidueFieldEnvelope R}
    (e : Completion R ≃ₐ[R] Module.End R E.carrier) {U V : Submodule R E.carrier}
    (h : hullAnnihilator e U ≤ hullAnnihilator e V) : V ≤ U := by
  intro x hx
  by_contra hxU
  have hq : U.mkQ x ≠ 0 := by
    intro hz
    exact hxU (by simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hz)
  obtain ⟨g, hg⟩ := matlisDual_separates E (U.mkQ x) hq
  let f : Module.End R E.carrier := g.comp U.mkQ
  have hf : e.symm f ∈ hullAnnihilator e U := by
    intro y hy
    rw [e.apply_symm_apply]
    change g (U.mkQ y) = 0
    have hyq : U.mkQ y = 0 := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hy
    rw [hyq, map_zero]
  have hz : e (e.symm f) x = 0 := h hf x hx
  rw [e.apply_symm_apply] at hz
  exact hg hz

/-- Over a Noetherian local ring, the residue-field injective hull is Artinian. -/
theorem residueHull_artinian [IsNoetherianRing R] (E : ResidueFieldEnvelope R) :
    IsArtinian R E.carrier := by
  let : IsNoetherianRing (Completion R) :=
    P103.Ch07.CompletedNoetherian.completed_noetherian R (IsLocalRing.maximalIdeal R)
  let e := residueHullEndomorphismEquiv E
  have h : StrictAnti (hullAnnihilator e) := by
    intro U V hUV
    exact lt_of_le_not_ge (fun _ hs x hx => hs x (hUV.le hx))
      (fun h => hUV.not_ge (le_of_hullAnnihilator_le e h))
  exact h.wellFoundedLT

end CommutativeAlgebraNotes
