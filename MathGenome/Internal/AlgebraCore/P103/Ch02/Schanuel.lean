import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.Schanuel
import MathGenome.Internal.AlgebraCore.P103.Ch01.SplitSequences
import MathGenome.Internal.AlgebraCore.P103.Ch02.Projective

namespace P103.Ch02.Schanuel

open P103.Specs.Ch02.Schanuel

/-- The fiber product of the two covers splits over either projective term. -/
theorem schanuel : schanuelType := by
  intro R _ K₁ K₂ P₁ P₂ M _ _ _ _ _ _ _ _ _ _ _ _ i₁ p₁ i₂ p₂
    hi₁ he₁ hp₁ hi₂ he₂ hp₂
  let E := LinearMap.ker
    (p₁.comp (LinearMap.fst R P₁ P₂) - p₂.comp (LinearMap.snd R P₁ P₂))
  let q₁ : E →ₗ[R] P₁ := (LinearMap.fst R P₁ P₂).comp E.subtype
  let q₂ : E →ₗ[R] P₂ := (LinearMap.snd R P₁ P₂).comp E.subtype
  have compat (x : E) : p₁ x.val.1 = p₂ x.val.2 := by
    have hx := x.property
    change p₁ x.val.1 - p₂ x.val.2 = 0 at hx
    exact sub_eq_zero.mp hx
  let j₁ : K₁ →ₗ[R] E :=
    (i₁.prod (0 : K₁ →ₗ[R] P₂)).codRestrict E (by
      intro k
      change p₁ (i₁ k) - p₂ 0 = 0
      rw [map_zero, sub_zero]
      exact (he₁ (i₁ k)).mpr ⟨k, rfl⟩)
  let j₂ : K₂ →ₗ[R] E :=
    ((0 : K₂ →ₗ[R] P₁).prod i₂).codRestrict E (by
      intro k
      change p₁ 0 - p₂ (i₂ k) = 0
      rw [map_zero, (he₂ (i₂ k)).mpr ⟨k, rfl⟩, sub_self])
  have hj₁ : Function.Injective j₁ := by
    intro a b hab
    exact hi₁ (congrArg (fun x : E => x.val.1) hab)
  have hj₂ : Function.Injective j₂ := by
    intro a b hab
    exact hi₂ (congrArg (fun x : E => x.val.2) hab)
  have hex₁ : Function.Exact j₁ q₂ := by
    intro x
    constructor
    · intro hx
      change x.val.2 = 0 at hx
      obtain ⟨k, hk⟩ := (he₁ x.val.1).mp (by rw [compat x, hx, map_zero])
      refine ⟨k, ?_⟩
      apply Subtype.ext
      exact Prod.ext hk hx.symm
    · rintro ⟨k, rfl⟩
      rfl
  have hex₂ : Function.Exact j₂ q₁ := by
    intro x
    constructor
    · intro hx
      change x.val.1 = 0 at hx
      obtain ⟨k, hk⟩ := (he₂ x.val.2).mp (by rw [← compat x, hx, map_zero])
      refine ⟨k, ?_⟩
      apply Subtype.ext
      exact Prod.ext hx.symm hk
    · rintro ⟨k, rfl⟩
      rfl
  have hq₁ : Function.Surjective q₁ := by
    intro a
    obtain ⟨b, hb⟩ := hp₂ (p₁ a)
    refine ⟨⟨(a, b), ?_⟩, rfl⟩
    change p₁ a - p₂ b = 0
    rw [hb, sub_self]
  have hq₂ : Function.Surjective q₂ := by
    intro b
    obtain ⟨a, ha⟩ := hp₁ (p₂ b)
    refine ⟨⟨(a, b), ?_⟩, rfl⟩
    change p₁ a - p₂ b = 0
    rw [ha, sub_self]
  obtain ⟨s₁, hs₁⟩ := P103.Ch02.Projective.lifting R P₁ E P₁ q₁ LinearMap.id hq₁
  obtain ⟨s₂, hs₂⟩ := P103.Ch02.Projective.lifting R P₂ E P₂ q₂ LinearMap.id hq₂
  let e₁ := P103.Ch01.SplitSequences.splitting R K₁ E P₂ j₁ q₂ hj₁ hex₁ s₂ hs₂
  let e₂ := P103.Ch01.SplitSequences.splitting R K₂ E P₁ j₂ q₁ hj₂ hex₂ s₁ hs₁
  exact ⟨e₁.trans e₂.symm⟩

/-- Schanuel's lemma on the right, with no change in assumptions. -/
theorem right_schanuel : right_schanuelType := by
  intro R _ K₁ K₂ P₁ P₂ M _ _ _ _ _ _ _ _ _ _ _ _ i₁ p₁ i₂ p₂
  exact schanuel Rᵐᵒᵖ K₁ K₂ P₁ P₂ M i₁ p₁ i₂ p₂

end P103.Ch02.Schanuel
