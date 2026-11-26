import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerHullLifting
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerConditionsFromHull
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerHullCriterion

universe u w

namespace CommutativeAlgebraNotes.ArtinFunctor

open CategoryTheory LocalArtinAlgebra SchlessingerHullCriterionSpec

variable {k : Type u} [Field k]

section FormalFamily

variable {R : CompleteLocalAlgebra k} {F : ArtinFunctor.{u,w} k}

private theorem factors_through_truncation {A : LocalArtinAlgebra.{u,u} k}
    (a : CompleteLocalAlgebra.Hom R A) :
    ∃ (n : ℕ) (f : Hom (R.truncation n) A), (R.toTruncation n).postcomp f = a := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  let q := R.toTruncation n
  have hq : Function.Surjective q := R.toTruncation_surjective n
  have hker : RingHom.ker q.val ≤ RingHom.ker a.val := by
    let : IsLocalHom a.val.toRingHom := ⟨a.property.map_nonunit⟩
    rw [R.ker_toTruncation n, ← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
    have hle := Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le a.val.toRingHom) (n + 1)
    have hn' : IsLocalRing.maximalIdeal A ^ n = ⊥ := by
      simpa only [Ideal.zero_eq_bot] using hn
    rw [← le_bot_iff]
    exact hle.trans ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn'.le)
  let f := q.val.liftOfSurjective hq a.val hker
  have hf (r : R) : f (q r) = a r :=
    AlgHom.liftOfSurjective_apply _ hq _ _ r
  let g : Hom (R.truncation n) A := ⟨f, ⟨fun x hx => by
    obtain ⟨r, rfl⟩ := hq x
    exact (IsUnit.of_map a.val r (hf r ▸ hx)).map q.val⟩⟩
  exact ⟨n, g, CompleteLocalAlgebra.Hom.ext hf⟩

private theorem map_comp_apply {A B C : LocalArtinAlgebra.{u,u} k}
    (f : Hom A B) (g : Hom B C) (x : F.toFunctor.obj A) :
    F.toFunctor.map (g.comp f) x = F.toFunctor.map g (F.toFunctor.map f x) :=
  ConcreteCategory.congr_hom (F.toFunctor.map_comp f g) x

private theorem same_evaluation (x : CompatibleFamily R F) {A : LocalArtinAlgebra.{u,u} k}
    {m n : ℕ} (f : Hom (R.truncation m) A) (g : Hom (R.truncation n) A)
    (h : (R.toTruncation m).postcomp f = (R.toTruncation n).postcomp g) :
    F.toFunctor.map f (x.val m) = F.toFunctor.map g (x.val n) := by
  let l := max m n
  have hm : m ≤ l := le_max_left _ _
  have hn : n ≤ l := le_max_right _ _
  have hfg : f.comp (R.truncationMap hm) = g.comp (R.truncationMap hn) := by
    apply Hom.ext
    intro z
    obtain ⟨r, rfl⟩ := R.toTruncation_surjective l z
    change f (((R.toTruncation l).postcomp (R.truncationMap hm)) r) =
      g (((R.toTruncation l).postcomp (R.truncationMap hn)) r)
    rw [R.toTruncation_postcomp hm, R.toTruncation_postcomp hn]
    exact congrArg (fun b : CompleteLocalAlgebra.Hom R A => b r) h
  simpa only [map_comp_apply, x.property m l hm, x.property n l hn] using
    congrArg (fun b : Hom (R.truncation l) A => F.toFunctor.map b (x.val l)) hfg

private noncomputable def evaluate (x : CompatibleFamily R F)
    {A : LocalArtinAlgebra.{u,u} k} (a : CompleteLocalAlgebra.Hom R A) :
    F.toFunctor.obj A :=
  let h := factors_through_truncation a
  F.toFunctor.map h.choose_spec.choose (x.val h.choose)

private theorem evaluate_factor (x : CompatibleFamily R F)
    {A : LocalArtinAlgebra.{u,u} k} (n : ℕ) (f : Hom (R.truncation n) A) :
    evaluate x ((R.toTruncation n).postcomp f) = F.toFunctor.map f (x.val n) := by
  let h := factors_through_truncation ((R.toTruncation n).postcomp f)
  exact same_evaluation x h.choose_spec.choose f h.choose_spec.choose_spec

private noncomputable def fromFamily (x : CompatibleFamily R F) :
    (R.representable.{u,w}).toFunctor ⟶ F.toFunctor where
  app _ := TypeCat.ofHom fun a => evaluate x a.down
  naturality := by
    intro A B g
    apply ConcreteCategory.hom_ext
    intro a
    change evaluate x (a.down.postcomp g) = F.toFunctor.map g (evaluate x a.down)
    obtain ⟨n, f, hf⟩ := factors_through_truncation a.down
    rw [← hf, evaluate_factor]
    change evaluate x ((R.toTruncation n).postcomp (g.comp f)) = _
    rw [evaluate_factor, map_comp_apply]

private theorem naturality_apply (τ : (R.representable.{u,w}).toFunctor ⟶ F.toFunctor)
    {A B : LocalArtinAlgebra.{u,u} k} (g : Hom A B) (a : CompleteLocalAlgebra.Hom R A) :
    τ.app B (ULift.up (a.postcomp g)) = F.toFunctor.map g (τ.app A (ULift.up a)) := by
  let b : (R.representable.{u,w}).toFunctor.obj A := ULift.up a
  exact ConcreteCategory.congr_hom (τ.naturality g) b

/-- A formal object on the maximal-ideal truncations determines, and is
determined by, a transformation from the functor of local maps out of `R`. -/
theorem formalFamilyCorrespondence : FormalFamilyCorrespondence.{u,w} := by
  intro k _ R F
  change CompleteLocalAlgebra k at R
  change ArtinFunctor.{u,w} k at F
  constructor
  · intro τ
    let x : CompatibleFamily R F := ⟨
      fun n => τ.app (R.truncation n) (ULift.up (R.toTruncation n)),
      fun m n h => by
        have he := (naturality_apply τ (R.truncationMap h) (R.toTruncation n)).symm
        rw [R.toTruncation_postcomp h] at he
        exact he⟩
    refine ⟨x, fun _ => rfl, fun y hy => Subtype.ext ?_⟩
    exact funext fun n => (hy n).symm
  · intro x
    refine ⟨fromFamily x, ?_, ?_⟩
    · intro n
      change evaluate x (R.toTruncation n) = x.val n
      have he := evaluate_factor x n (Hom.id (R.truncation n))
      change evaluate x (R.toTruncation n) = F.toFunctor.map (𝟙 (R.truncation n)) (x.val n) at he
      exact he.trans (ConcreteCategory.congr_hom (F.toFunctor.map_id (R.truncation n)) (x.val n))
    · intro τ hτ
      ext A a
      obtain ⟨n, f, hf⟩ := factors_through_truncation a.down
      change τ.app A (ULift.up a.down) = evaluate x a.down
      rw [← hf, evaluate_factor, naturality_apply, hτ n]

end FormalFamily

/-- Schlessinger's hull criterion for normalized functors on local Artin
`k`-algebras with residue field `k`. -/
theorem has_hull_iff {k : Type u} [Field k] (F : ArtinFunctor.{u,w} k) :
    Nonempty F.Hull ↔ F.H1 ∧ F.H2 ∧ F.H3 := by
  refine ⟨conditions_of_hull F, ?_⟩
  rintro ⟨h₁, h₂, h₃⟩
  obtain ⟨_, _, T, _, _, _, _, _, hc, τ, _, _, hfactor, heval, htangent⟩ :=
    SchlessingerCandidate.construct F h₁ h₂ h₃
  exact ⟨⟨T.ring hc, τ, htangent,
    SchlessingerHullLifting.towerSmooth T hc τ h₁ h₂ hfactor heval htangent⟩⟩

end CommutativeAlgebraNotes.ArtinFunctor
