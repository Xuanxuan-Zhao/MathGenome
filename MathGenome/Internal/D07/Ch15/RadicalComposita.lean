import MathGenome.Internal.Specs.D07.Ch15.RadicalComposita
import MathGenome.Internal.D07.Ch15.RadicalDefinition

/-! Finite composita, embeddings, and normal closures of radical towers.
There is no separability assumption anywhere in these results. -/

universe u v w t
namespace D07.Ch15.RadicalComposita
open IntermediateField
open D07.Ch15.RadicalDefinition
open Specs.D07.Ch15.RadicalDefinition
open Specs.D07.Ch15.RadicalComposita

section Helpers
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω]

/-- Append one radical adjunction, retaining zero and repeated steps. -/
theorem radical_extension_step {E F : IntermediateField K Ω}
    (hE : radicalExtensionValue K Ω E) (hF : radicalStepValue K Ω E F) :
    radicalExtensionValue K Ω F := by
  obtain ⟨r, T, hT, rfl⟩ := hE
  let U : Fin (r + 1 + 1) → IntermediateField K Ω := Fin.lastCases F T
  refine ⟨r + 1, U, ⟨?_, ?_⟩, ?_⟩
  · change U (Fin.castSucc (0 : Fin (r + 1))) = ⊥
    dsimp only [U]
    rw [Fin.lastCases_castSucc]
    exact hT.1
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [U] using hF
    · simpa only [U, Fin.succ_castSucc, Fin.lastCases_castSucc] using hT.2 j
  · simp [U]

/-- Induction on a radical tower, expressed using its last field. -/
theorem radical_extension_induction
    {P : IntermediateField K Ω → Prop} (hbot : P ⊥)
    (hstep : ∀ E F, radicalExtensionValue K Ω E → P E → radicalStepValue K Ω E F → P F)
    {E : IntermediateField K Ω} (hE : radicalExtensionValue K Ω E) : P E := by
  obtain ⟨r, T, hT, rfl⟩ := hE
  induction r with
  | zero =>
    simpa only [Fin.last_zero] using hT.1 ▸ hbot
  | succ r ih =>
    let S : Fin (r + 1) → IntermediateField K Ω := fun i => T i.castSucc
    have hS : radicalTowerValue K Ω r S := by
      refine ⟨hT.1, fun i => ?_⟩
      simpa [S, Fin.castSucc_succ] using hT.2 i.castSucc
    exact hstep _ _ ⟨r, S, hS, rfl⟩ (ih S hS) (hT.2 (Fin.last r))

/-- Raising the current field preserves a radical adjunction. -/
theorem radical_step_sup_left (B : IntermediateField K Ω)
    {E F : IntermediateField K Ω} (h : radicalStepValue K Ω E F) :
    radicalStepValue K Ω (B ⊔ E) (B ⊔ F) := by
  obtain ⟨a, n, hn, hp, rfl⟩ := h
  refine ⟨a, n, hn, (show E ≤ B ⊔ E from le_sup_right) hp, ?_⟩
  simp only [adjoin_union, adjoin_self]
  exact (sup_assoc B E (adjoin K {a})).symm

end Helpers

/-- Concatenate radical generators by raising the base of the second tower. -/
theorem radical_compositum : Compositum.{u, v} := by
  intro K Ω _ _ _ _ E F hE hF
  apply radical_extension_induction (P := fun F => radicalExtensionValue K Ω (E ⊔ F))
    (by simpa using hE) (fun F G _ ih hstep =>
      radical_extension_step ih (radical_step_sup_left E hstep)) hF

theorem finite_radical_compositum : FiniteCompositum.{u, v, t} := by
  intro K Ω _ _ _ _ ι _ E hE
  classical
  have hs (s : Finset ι) : radicalExtensionValue K Ω (⨆ i ∈ s, E i) := by
    induction s using Finset.induction_on with
    | empty => simpa using base_radical_extension K Ω
    | @insert i s hi ih =>
      simpa only [Finset.iSup_insert] using radical_compositum K Ω _ _ (hE i) ih
  let := Fintype.ofFinite ι
  simpa using hs Finset.univ

/-- Finite generation, including the empty tower. -/
theorem radical_extension_finite : ExtensionFinite.{u, v} := by
  intro K Ω _ _ _ _ E hE
  apply radical_extension_induction (P := fun E => FiniteDimensional K E) ?_ ?_ hE
  · exact (botEquiv K Ω).symm.toLinearEquiv.finiteDimensional
  · intro E F _ hfin hstep
    let := hfin
    obtain ⟨a, n, hn, hp, rfl⟩ := hstep
    have : FiniteDimensional K (adjoin K {a} : IntermediateField K Ω) :=
      adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic a).isIntegral)
    change FiniteDimensional K (adjoin K ((E : Set Ω) ∪ {a}))
    rw [adjoin_union, adjoin_self]
    infer_instance

theorem radical_step_map : StepMap.{u, v, w} := by
  intro K Ω Ω' _ _ _ _ _ _ _ σ E F h
  obtain ⟨a, n, hn, hp, rfl⟩ := h
  refine ⟨σ a, n, hn, ?_, ?_⟩
  · rw [← map_pow]
    exact ⟨a ^ n, hp, rfl⟩
  · rw [adjoin_map, Set.image_union, Set.image_singleton]
    rfl

theorem radical_tower_map : TowerMap.{u, v, w} := by
  intro K Ω Ω' _ _ _ _ _ _ _ σ r T hT
  exact ⟨by simp only [hT.1, IntermediateField.map_bot], fun i =>
    radical_step_map K Ω Ω' σ _ _ (hT.2 i)⟩

theorem radical_extension_map : ExtensionMap.{u, v, w} := by
  intro K Ω Ω' _ _ _ _ _ _ _ σ E hE
  obtain ⟨r, T, hT, rfl⟩ := hE
  exact ⟨r, fun i => (T i).map σ, radical_tower_map K Ω Ω' σ r T hT, rfl⟩

section Pullback
variable {K : Type u} {Ω : Type v} {Ω' : Type w}
  [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
  [Algebra.IsAlgebraic K Ω] [Algebra.IsAlgebraic K Ω']

/-- Pull a radical adjunction back through an embedding whose image contains it. -/
theorem radical_step_comap (σ : Ω →ₐ[K] Ω') {E F : IntermediateField K Ω'}
    (hstep : radicalStepValue K Ω' E F) (hF : F ≤ σ.fieldRange) :
    radicalStepValue K Ω (E.comap σ) (F.comap σ) := by
  have hE : E ≤ σ.fieldRange :=
    (radical_step_inclusion K Ω' E F hstep).trans hF
  obtain ⟨a, n, hn, hp, hgen⟩ := hstep
  have ha : a ∈ F := hgen.symm ▸ subset_adjoin K _ (Or.inr rfl)
  obtain ⟨b, hb⟩ := hF ha
  change σ b = a at hb
  refine ⟨b, n, hn, ?_, ?_⟩
  · change σ (b ^ n) ∈ E
    simpa only [map_pow, hb] using hp
  · have hmap : (adjoin K ((E.comap σ : Set Ω) ∪ {b})).map σ = F := by
      rw [adjoin_map, Set.image_union, Set.image_singleton, hb,
        ← coe_map, map_comap_eq_self hE]
      exact hgen.symm
    rw [← hmap, comap_map]

/-- All the fields of a tower lie in its last field, so the whole tower pulls back. -/
theorem radical_extension_comap (σ : Ω →ₐ[K] Ω') {E : IntermediateField K Ω'}
    (hE : radicalExtensionValue K Ω' E) (himage : E ≤ σ.fieldRange) :
    radicalExtensionValue K Ω (E.comap σ) := by
  obtain ⟨r, T, hT, rfl⟩ := hE
  refine ⟨r, fun i => (T i).comap σ, ⟨?_, ?_⟩, rfl⟩
  · change (T 0).comap σ = ⊥
    rw [hT.1]
    exact (congrArg (fun H : IntermediateField K Ω' => H.comap σ)
      (IntermediateField.map_bot σ)).symm.trans (comap_map σ ⊥)
  · intro i
    exact radical_step_comap σ (hT.2 i)
      ((radical_tower_monotone K Ω' r T hT (Fin.le_last i.succ)).trans himage)

end Pullback

/-- Reinterpret the tower inside its final field, then apply the embedding. -/
theorem radical_extension_image : ExtensionImage.{u, v, w} := by
  intro K Ω Ω' _ _ _ _ _ _ _ E σ hE
  have htop : radicalExtensionValue K E ⊤ := by
    have hpull := radical_extension_comap E.val hE (by rw [fieldRange_val])
    have heq : E.comap E.val = ⊤ := by
      ext x
      exact iff_of_true x.2 trivial
    rwa [heq] at hpull
  simpa only [← AlgHom.fieldRange_eq_map] using radical_extension_map K E Ω' σ ⊤ htop

/-- The finitely many conjugate image fields are radical. Their compositum
is the actual normal closure, including for inseparable extensions. -/
theorem radical_normal_closure : NormalClosure.{u, v} := by
  intro K Ω _ _ _ _ _ E hE
  let : FiniteDimensional K E := radical_extension_finite K Ω E hE
  let : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  refine ⟨inferInstance, inferInstance, ?_, le_normalClosure E, inferInstance⟩
  change radicalExtensionValue K Ω (⨆ σ : E →ₐ[K] Ω, σ.fieldRange)
  exact finite_radical_compositum K Ω (E →ₐ[K] Ω) AlgHom.fieldRange
    (fun σ => radical_extension_image K Ω Ω E σ hE)

end D07.Ch15.RadicalComposita
