import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.FourFiveLemmas
import Mathlib.Algebra.FiveLemma

/-! Four and five lemmas over arbitrary unital rings.
The additive-group four lemmas are used because their hypotheses do not
require commutative scalars. All exactness and commutative-square hypotheses
are preserved when a linear map is viewed as an additive homomorphism.
-/

namespace P103.Ch01.FourFiveLemmas

open P103.Specs.Ch01.FourFiveLemmas

theorem four_injective.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} :
    four_injectiveType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} := by
  intro R _ M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ h₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃
    hh₁ hh₂ hh₄
  exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
    f₁.toAddMonoidHom f₂.toAddMonoidHom f₃.toAddMonoidHom
    g₁.toAddMonoidHom g₂.toAddMonoidHom g₃.toAddMonoidHom
    h₁.toAddMonoidHom h₂.toAddMonoidHom h₃.toAddMonoidHom h₄.toAddMonoidHom
    (AddMonoidHom.ext fun x => DFunLike.congr_fun hc₁ x)
    (AddMonoidHom.ext fun x => DFunLike.congr_fun hc₂ x)
    (AddMonoidHom.ext fun x => DFunLike.congr_fun hc₃ x)
    hf₁ hf₂ hg₁ hh₁ hh₂ hh₄

theorem four_surjective.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} :
    four_surjectiveType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} := by
  intro R _ M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ h₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃
    hh₂ hh₄ hh₅
  exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    f₂.toAddMonoidHom f₃.toAddMonoidHom f₄.toAddMonoidHom
    g₂.toAddMonoidHom g₃.toAddMonoidHom g₄.toAddMonoidHom
    h₂.toAddMonoidHom h₃.toAddMonoidHom h₄.toAddMonoidHom h₅.toAddMonoidHom
    (AddMonoidHom.ext fun x => DFunLike.congr_fun hc₂ x)
    (AddMonoidHom.ext fun x => DFunLike.congr_fun hc₃ x)
    (AddMonoidHom.ext fun x => DFunLike.congr_fun hc₄ x)
    hf₃ hg₂ hg₃ hh₂ hh₄ hh₅

theorem five_bijective.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} :
    five_bijectiveType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} := by
  intro R _ M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ h₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃
    hh₁ hh₂ hh₄ hh₅
  exact ⟨four_injective R M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ h₅ hc₁
    hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hh₁.2 hh₂.1 hh₄.1,
    four_surjective R M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ h₅ hc₁ hc₂
    hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hh₂.2 hh₄.2 hh₅.1⟩

theorem five_isomorphism.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} :
    five_isomorphismType.{uR, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10} := by
  intro R _ M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ h₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃
    hh₁ hh₂ hh₄ hh₅
  exact ⟨LinearEquiv.ofBijective h₃ (five_bijective R M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ f₁ f₂ f₃ f₄ g₁
    g₂ g₃ g₄ h₁ h₂ h₃ h₄ h₅ hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hh₁ hh₂ hh₄ hh₅), rfl⟩

/-- The element chase for a map of short exact sequences. -/
theorem short_five_bijective.{uR, u1, u2, u3, u4, u5, u6} :
    short_five_bijectiveType.{uR, u1, u2, u3, u4, u5, u6} := by
  intro R _ A B C A' B' C' _ _ _ _ _ _ _ _ _ _ _ _
    i p i' p' a b c hi hp hi' hp' hex hex' hc₁ hc₂ ha hc
  have comm₁ (y : A) : i' (a y) = b (i y) := DFunLike.congr_fun hc₁ y
  have comm₂ (x : B) : p' (b x) = c (p x) := DFunLike.congr_fun hc₂ x
  constructor
  · apply (injective_iff_map_eq_zero b).mpr
    intro x hx
    have hpx : p x = 0 := hc.1 (by
      calc
        c (p x) = p' (b x) := (DFunLike.congr_fun hc₂ x).symm
        _ = c 0 := by rw [hx, map_zero, map_zero])
    obtain ⟨y, hy⟩ := (hex x).mp hpx
    have hay : a y = 0 := hi' (by
      calc
        i' (a y) = b (i y) := DFunLike.congr_fun hc₁ y
        _ = i' 0 := by rw [hy, hx, map_zero])
    have hyz : y = 0 := ha.1 (by simpa using hay)
    rw [← hy, hyz, map_zero]
  · intro x'
    obtain ⟨z, hz⟩ := hc.2 (p' x')
    obtain ⟨x, hx⟩ := hp z
    have hd : p' (x' - b x) = 0 := by
      rw [map_sub, comm₂ x, hx, hz, sub_self]
    obtain ⟨y', hy'⟩ := (hex' (x' - b x)).mp hd
    obtain ⟨y, hy⟩ := ha.2 y'
    refine ⟨i y + x, ?_⟩
    calc
      b (i y + x) = i' (a y) + b x := by
        rw [map_add, ← comm₁ y]
      _ = x' := by rw [hy, hy', sub_add_cancel]

theorem short_five_isomorphism.{uR, u1, u2, u3, u4, u5, u6} :
    short_five_isomorphismType.{uR, u1, u2, u3, u4, u5, u6} := by
  intro R _ A B C A' B' C' _ _ _ _ _ _ _ _ _ _ _ _
    i p i' p' a b c hi hp hi' hp' hex hex' hc₁ hc₂ ha hc
  exact ⟨LinearEquiv.ofBijective b
    (short_five_bijective R A B C A' B' C' i p i' p' a b c hi hp hi' hp' hex hex' hc₁ hc₂ ha hc), rfl⟩

end P103.Ch01.FourFiveLemmas
