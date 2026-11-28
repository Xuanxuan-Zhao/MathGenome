import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaNonzero
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SlTwoCharacterNormalForms
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaSemisimple
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaNilpotent

namespace LieNotes.SuperRestricted.BabyVermaNonzero

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaNonzero
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)

universe u w v

private theorem simple_compHom {A B : Type*} [Ring A] [Ring B] (f : A ≃+* B)
    (V : Type*) [AddCommGroup V] [Module B V] :
    letI : Module A V := Module.compHom V f.toRingHom
    IsSimpleModule A V ↔ IsSimpleModule B V := by
  let : Module A V := Module.compHom V f.toRingHom
  let : RingHomSurjective f.toRingHom := ⟨f.surjective⟩
  let identity : V →ₛₗ[f.toRingHom] V :=
    { AddMonoidHom.id V with map_smul' := fun _ _ => rfl }
  exact identity.isSimpleModule_iff_of_bijective Function.bijective_id

private theorem classifies_of_normalized
    {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {P : restrictedPowerValue k p (Model k)} {χ ψ : Model k →ₗ[k] k}
    (f : Ambient P χ ≃ₐ[k] Ambient P ψ)
    {Q : restrictedPowerValue k p (Borel k)} {j : BorelAlgebra Q ψ →ₐ[k] Ambient P ψ}
    {ι : Type v} {θ : ι → BorelAlgebra Q ψ →ₐ[k] k} {r : ι → ι → Prop}
    (hFamily : ∀ i, IsSimpleModule (Ambient P ψ) (BabyVerma j (θ i)) ∧
      Module.finrank k (BabyVerma j (θ i)) = p)
    (hLabels : ∀ i i',
      Nonempty (BabyVerma j (θ i) ≃ₗ[Ambient P ψ] BabyVerma j (θ i')) ↔ r i i')
    (hExhaust : ∀ (V : Type w) [AddCommGroup V] [Module (Ambient P ψ) V]
      [IsSimpleModule (Ambient P ψ) V],
      ∃ i, Nonempty (BabyVerma j (θ i) ≃ₗ[Ambient P ψ] V)) :
    Classifies.{u, w, v} f j θ r := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    let : Module (Ambient P χ) (BabyVerma j (θ i)) := Module.compHom _ f.toRingHom
    refine ⟨(simple_compHom f.toRingEquiv _).mpr (hFamily i).1, ?_, (hFamily i).2⟩
    apply IsScalarTower.of_algebraMap_smul
    intro a x
    change f (algebraMap k (Ambient P χ) a) • x = a • x
    rw [f.commutes, IsScalarTower.algebraMap_smul]
  · intro i i'
    let : Module (Ambient P χ) (BabyVerma j (θ i)) := Module.compHom _ f.toRingHom
    let : Module (Ambient P χ) (BabyVerma j (θ i')) := Module.compHom _ f.toRingHom
    change Nonempty (BabyVerma j (θ i) ≃ₗ[Ambient P χ] BabyVerma j (θ i')) ↔ r i i'
    rw [← hLabels i i']
    constructor
    · rintro ⟨g⟩
      refine ⟨{ g.toAddEquiv with map_smul' := ?_ }⟩
      intro b x
      obtain ⟨a, rfl⟩ := f.surjective b
      exact g.map_smul a x
    · rintro ⟨g⟩
      refine ⟨{ g.toAddEquiv with map_smul' := ?_ }⟩
      intro a x
      exact g.map_smul (f a) x
  · intro V _ _ hSimple
    let : Module (Ambient P ψ) V := Module.compHom V f.symm.toRingHom
    let : IsSimpleModule (Ambient P ψ) V := (simple_compHom f.symm.toRingEquiv V).mpr hSimple
    obtain ⟨i, ⟨g⟩⟩ := hExhaust V
    let : Module (Ambient P χ) (BabyVerma j (θ i)) := Module.compHom _ f.toRingHom
    refine ⟨i, ⟨{ g.toAddEquiv with map_smul' := ?_ }⟩⟩
    intro a x
    change g (f a • x) = a • g x
    rw [g.map_smul]
    change f.symm (f a) • g x = a • g x
    rw [f.symm_apply_apply]

/-- Both normalized families classify the simple modules of the original
reduced enveloping algebra via the isomorphism induced by matrix conjugation. -/
theorem babyVermaNonzero : babyVermaNonzeroType.{u, w} := by
  intro k _ _ p _ hp
  let : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
  obtain ⟨P, hP, _⟩ := RestrictedSlTwo.matrixRestrictedPowers (k := k) hp
  refine ⟨P, hP, ?_⟩
  intro χ hχ
  obtain ⟨X, U, c, htrace, hc, htrace', hcases⟩ :=
    SlTwoCharacterNormalForms.characterNormalForms (k := k) hp χ hχ
  obtain ⟨f, hf⟩ := SlTwoCharacterNormalForms.reducedConjugation P hP U c hc χ
  refine ⟨X, U, c, htrace, hc, htrace', f, hf, ?_⟩
  let ψ := χ.comp c.symm.toLinearEquiv.toLinearMap
  rcases hcases with ⟨a, ha, hne, hdiag, hpoly, he, hF, hh, hη⟩ |
    ⟨hX, hpoly, he, hh, hF⟩
  · obtain ⟨hCount, Q, j, hQ, hj, hjInj, θ, hFamily, hLabels, hExhaust⟩ :=
      BabyVermaSemisimple.babyVermaSemisimple.{u, w} (k := k) hp P hP ψ he hF hη
    exact Or.inl ⟨a, ha, hne, hdiag, hpoly, he, hF, hh, hη, hCount, Q, j, hQ, hj, hjInj, θ,
      fun weight => ⟨(hFamily weight).1, (hFamily weight).2.2.2⟩,
      classifies_of_normalized f
        (fun weight => ⟨(hFamily weight).2.1, (hFamily weight).2.2.1⟩) hLabels hExhaust⟩
  · obtain ⟨Q, j, hQ, hj, hjInj, θ, hFamily, _, hLabels, hExhaust, hFixed, hCount⟩ :=
      BabyVermaNilpotent.babyVermaNilpotent.{u, w} (k := k) hp P hP ψ he hh hF
    exact Or.inr ⟨hX, hpoly, he, hh, hF, Q, j, hQ, hj, hjInj, θ, fun m => (hFamily m).1,
      classifies_of_normalized f (fun m => (hFamily m).2.2) hLabels hExhaust, hFixed, hCount⟩

end LieNotes.SuperRestricted.BabyVermaNonzero
