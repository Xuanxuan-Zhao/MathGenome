import MathGenome.Internal.D07.Ch01.GroupNormalQuotient
import MathGenome.Internal.Specs.D07.Ch04.QuotientUniversalProperty

/-!
# Descent through a normal quotient

K07.04.quotient_universal_property, paper.tex:682–689.
As in the source, existence and its necessary kernel condition reuse the
normal-quotient preliminary lemma. Surjectivity of the quotient projection
gives uniqueness, and evaluation of the factorization gives the coset formula.
-/

namespace D07.Ch04.QuotientUniversalProperty

universe u v

theorem factorization_unique (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H) (fbar₁ fbar₂ : G ⧸ N →* H)
    (h₁ : fbar₁.comp (QuotientGroup.mk' N) = f)
    (h₂ : fbar₂.comp (QuotientGroup.mk' N) = f) : fbar₁ = fbar₂ := by
  apply QuotientGroup.monoidHom_ext
  exact h₁.trans h₂.symm

theorem factorization_iff (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H) :
    (∃ fbar : G ⧸ N →* H, fbar.comp (QuotientGroup.mk' N) = f) ↔ N ≤ f.ker := by
  constructor
  · rintro ⟨fbar, hfactor⟩
    apply (D07.Ch01.GroupNormalQuotient.descends_unique_iff G H N f).mp
    refine ⟨fbar, hfactor, ?_⟩
    intro other hother
    exact factorization_unique G H N f other fbar hother hfactor
  · intro hN
    obtain ⟨fbar, hfactor, _⟩ :=
      (D07.Ch01.GroupNormalQuotient.descends_unique_iff G H N f).mpr hN
    exact ⟨fbar, hfactor⟩

theorem factorization_formula (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H) (fbar : G ⧸ N →* H)
    (hfactor : fbar.comp (QuotientGroup.mk' N) = f) (g : G) :
    fbar (QuotientGroup.mk' N g) = f g :=
  DFunLike.congr_fun hfactor g

end D07.Ch04.QuotientUniversalProperty
