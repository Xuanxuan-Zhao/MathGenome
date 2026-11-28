import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Affine.ContragredientComparison
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Affine.CartanRealization
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Affine.NoCartanDisjointIdeals
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanQuotient
import Mathlib.LinearAlgebra.Dual.Lemmas
import Batteries.Tactic.OpenPrivate

namespace LieNotes.Affine

open Contragredient
open RepTheorySurvey.Affine
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.RepTheorySurvey.Affine.TriangularRootSpaces
  (coordinates affinePositive_value affineNegative_value affineCartan_value
    ClosedUnderBracket)
open Specs.RepTheorySurvey.Affine.AffineTriangularDecomposition (Conclusion)
open LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)

open private coordinates_K coordinates_d from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces

noncomputable section

universe u

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
  [LieAlgebra.IsSimple ℂ G] {B : InvariantForm G} {H : LieSubalgebra ℂ G}
  {φ : Direction H} {θ : Module.Dual ℂ H}
  {T : FiniteRootTriple H θ} {S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val}

omit [LieAlgebra.IsSimple ℂ G] in
private theorem affineRelations [Finite (AffineSimpleIndex H φ)]
    {A : Matrix (AffineSimpleIndex H φ) (AffineSimpleIndex H φ) ℤ}
    (R : Realization A (affineCartan B H))
    (hc : ∀ i, (R.h i : AffineAlgebra B) = affineSimpleH B H θ i)
    (hα : ∀ i, R.α i = affineSimpleRoot B H θ i)
    (D : Conclusion B H φ) (hθ : IsHighestFiniteRoot H φ θ) :
    Presentation.Relations R (affineCartan B H).subtype
      (affineSimpleE B T S) (affineSimpleF B T S) := by
  classical
  obtain ⟨hdiag, hoff, _, _⟩ := D.simple_triples θ hθ T S
  constructor
  · exact D.cartan_abelian
  · intro h i
    show ⁅(h : AffineAlgebra B), affineSimpleE B T S i⁆ = _
    rw [hα]
    exact (mem_affineWeightSpace B H _ _).mp (hdiag i).2.2.1 h
  · intro h i
    show ⁅(h : AffineAlgebra B), affineSimpleF B T S i⁆ = _
    rw [hα, ← neg_smul]
    exact (mem_affineWeightSpace B H _ _).mp (hdiag i).2.2.2.1 h
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      exact (hdiag i).2.2.2.2.2.1.trans (hc i).symm
    · rw [ite_eq_right hij]
      exact hoff i j hij

omit [LieAlgebra.IsSimple ℂ G] in
private theorem affineLift_surjective [Finite (AffineSimpleIndex H φ)]
    {A : Matrix (AffineSimpleIndex H φ) (AffineSimpleIndex H φ) ℤ}
    {R : Realization A (affineCartan B H)}
    (rel : Presentation.Relations R (affineCartan B H).subtype
      (affineSimpleE B T S) (affineSimpleF B T S))
    (D : Conclusion B H φ) (hθ : IsHighestFiniteRoot H φ θ) :
    Function.Surjective (Presentation.lift R _ _ _ rel) := by
  let F := Presentation.lift R _ _ _ rel
  have hsplit := D.decomposition.sup_eq_top
  obtain ⟨_, _, hpos, hneg⟩ := D.simple_triples θ hθ T S
  have rangeClosed : ClosedUnderBracket B F.range.toSubmodule :=
    fun _ _ hx hy => F.range.lie_mem hx hy
  have hC : affineCartan B H ≤ F.range.toSubmodule := by
    intro x hx
    exact ⟨Presentation.cartan R ⟨x, hx⟩, Presentation.lift_cartan R _ _ _ rel ⟨x, hx⟩⟩
  have hP : affinePositive_value B H φ ≤ F.range.toSubmodule := by
    rw [← hpos]
    refine sInf_le ⟨?_, rangeClosed⟩
    rintro _ ⟨i, rfl⟩
    exact ⟨Presentation.e R i, Presentation.lift_e R _ _ _ rel i⟩
  have hN : affineNegative_value B H φ ≤ F.range.toSubmodule := by
    rw [← hneg]
    refine sInf_le ⟨?_, rangeClosed⟩
    rintro _ ⟨i, rfl⟩
    exact ⟨Presentation.f R i, Presentation.lift_f R _ _ _ rel i⟩
  have htop : ⊤ ≤ F.range.toSubmodule := hsplit ▸ sup_le hN (sup_le hC hP)
  intro x
  exact htop (Submodule.mem_top : x ∈ ⊤)

private theorem affineLift_ker [H.IsCartanSubalgebra]
    [Finite (AffineSimpleIndex H φ)]
    {A : Matrix (AffineSimpleIndex H φ) (AffineSimpleIndex H φ) ℤ}
    {R : Realization A (affineCartan B H)}
    (hB : B.IsNormalized H) (F : Presentation.Algebra R →ₗ⁅ℂ⁆ AffineAlgebra B)
    (hF : Function.Surjective F)
    (hC : ∀ h, F (Presentation.cartan R h) = (h : AffineAlgebra B)) :
    F.ker = CartanQuotient.cartanDisjointIdeal R := by
  let J := CartanQuotient.cartanDisjointIdeal R
  have hJ := CartanQuotient.cartanDisjointIdeal_isGreatest R
  have hker : F.ker ≤ J := by
    apply hJ.2
    apply Submodule.disjoint_def.mpr
    rintro _ hx ⟨h, rfl⟩
    have hz : (h : AffineAlgebra B) = 0 := (hC h).symm.trans (LieHom.mem_ker.mp hx)
    rw [show h = 0 from Subtype.ext hz, map_zero]
  have hmap : J.map F = ⊥ := by
    by_contra hn
    apply nonzeroIdeal_meets_affineCartan B H hB (J.map F) hn
    apply (Submodule.eq_bot_iff _).mpr
    rintro x ⟨hxJ, hxC⟩
    obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective hF hxJ
    let h : affineCartan B H := ⟨x, hxC⟩
    have hdiff : (y : Presentation.Algebra R) - Presentation.cartan R h ∈ F.ker := by
      apply LieHom.mem_ker.mpr
      rw [map_sub, hy, hC, sub_self]
    have hcartan : Presentation.cartan R h ∈ J.toSubmodule := by
      simpa only [sub_sub_self] using J.sub_mem y.property (hker hdiff)
    have hz := Submodule.disjoint_def.mp hJ.1 _ hcartan ⟨h, rfl⟩
    change (h : AffineAlgebra B) = 0
    rw [← hC h, hz, map_zero]
  exact le_antisymm hker (LieIdeal.map_eq_bot_iff.mp hmap)

/-- Descend the presentation map through its actual Cartan-disjoint kernel. -/
private def comparisonEquiv {I V : Type u} [AddCommGroup V] [Module ℂ V]
    [Finite I] {A : Matrix I I ℤ} {R : Realization A V}
    (F : Presentation.Algebra R →ₗ⁅ℂ⁆ AffineAlgebra B)
    (hF : Function.Surjective F) (hker : F.ker = CartanQuotient.cartanDisjointIdeal R) :
    CartanQuotient.Algebra R ≃ₗ⁅ℂ⁆ AffineAlgebra B := by
  let q := CartanQuotient.quotientMap R
  let f : CartanQuotient.Algebra R →ₗ⁅ℂ⁆ AffineAlgebra B :=
    { (CartanQuotient.cartanDisjointIdeal R).toSubmodule.liftQ F.toLinearMap
        (by rw [← LieHom.ker_toSubmodule, hker]) with
      map_lie' := by
        intro x y
        obtain ⟨a, rfl⟩ := CartanQuotient.quotientMap_surjective R x
        obtain ⟨b, rfl⟩ := CartanQuotient.quotientMap_surjective R y
        exact F.map_lie a b }
  have hcomp (x : Presentation.Algebra R) : f (q x) = F x := rfl
  refine LieEquiv.ofBijective f ⟨?_, ?_⟩
  · apply (LieHom.ker_eq_bot f).mp
    apply (LieSubmodule.eq_bot_iff _).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := CartanQuotient.quotientMap_surjective R x
    apply LieHom.mem_ker.mp
    rw [CartanQuotient.quotientMap_ker, ← hker]
    exact LieHom.mem_ker.mpr (hcomp a ▸ LieHom.mem_ker.mp hx)
  · intro x
    obtain ⟨a, rfl⟩ := hF x
    exact ⟨q a, hcomp a⟩

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] in
private theorem comparisonEquiv_apply {I V : Type u} [AddCommGroup V] [Module ℂ V]
    [Finite I] {A : Matrix I I ℤ} {R : Realization A V}
    (F : Presentation.Algebra R →ₗ⁅ℂ⁆ AffineAlgebra B)
    (hF : Function.Surjective F) (hker : F.ker = CartanQuotient.cartanDisjointIdeal R)
    (x : Presentation.Algebra R) :
    comparisonEquiv F hF hker (CartanQuotient.quotientMap R x) = F x := rfl

omit [LieAlgebra.IsSimple ℂ G] in
private theorem affineCenter [Fintype (simpleRoots H φ)]
    {A : Matrix (AffineSimpleIndex H φ) (AffineSimpleIndex H φ) ℤ}
    (R : Realization A (affineCartan B H))
    (hα : ∀ i, R.α i = affineSimpleRoot B H θ i)
    (hmin : R.IsMinimal)
    (hrank : (A.map fun z : ℤ => (z : ℂ)).rank = Fintype.card (simpleRoots H φ))
    (D : Conclusion B H φ) (hθ : IsHighestFiniteRoot H φ θ)
    (E : CartanQuotient.Algebra R ≃ₗ⁅ℂ⁆ AffineAlgebra B)
    (he : ∀ i, E (CartanQuotient.e R i) = affineSimpleE B T S i) :
    (LieAlgebra.center ℂ (AffineAlgebra B)).toSubmodule = ℂ ∙ K B := by
  let : FiniteDimensional ℂ (affineCartan B H) := hmin.1
  let W := Submodule.span ℂ (Set.range R.α)
  have hK (i : AffineSimpleIndex H φ) : R.α i (cartanK B H) = 0 := by
    rw [hα]
    cases i <;> simp [affineSimpleRoot, alphaZero]
  have hline : W.dualCoannihilator = ℂ ∙ cartanK B H := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      change cartanK B H ∈ (W.dualCoannihilator : Set _)
      rw [Submodule.coe_dualCoannihilator_span]
      rintro _ ⟨i, rfl⟩
      exact hK i
    · have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq W
      have hW : Module.finrank ℂ W = Fintype.card (AffineSimpleIndex H φ) :=
        finrank_span_eq_card R.α_independent
      have hdimA := hmin.2
      rw [hrank, Fintype.card_option] at hdimA
      rw [hW, Fintype.card_option, hdimA] at hdim
      have hn : cartanK B H ≠ 0 := by
        intro hz
        have hc := congrArg (fun x : affineCartan B H =>
          (coordinates B (x : AffineAlgebra B)).1.2) hz
        simp only [show ((cartanK B H : affineCartan B H) : AffineAlgebra B) = K B from rfl,
          Submodule.coe_zero, map_zero, coordinates_K, Prod.fst_zero, Prod.snd_zero,
          one_ne_zero] at hc
      rw [finrank_span_singleton hn]
      omega
  obtain ⟨hdiag, _, _, _⟩ := D.simple_triples θ hθ T S
  apply le_antisymm
  · intro z hz
    have hcentral := (LieModule.mem_maxTrivSubmodule ℂ (AffineAlgebra B) (AffineAlgebra B) z).mp hz
    have hzC : z ∈ affineCartan B H := by
      change z ∈ affineCartan_value B H
      rw [← D.zero_weight]
      exact (mem_affineWeightSpace B H 0 z).mpr fun h => by
        rw [← affineBracket_eq, hcentral, LinearMap.zero_apply, zero_smul]
    let h : affineCartan B H := ⟨z, hzC⟩
    have hvanish (i : AffineSimpleIndex H φ) : R.α i h = 0 := by
      have hb := (mem_affineWeightSpace B H _ _).mp (hdiag i).2.2.1 h
      rw [← affineBracket_eq, ← lie_skew, hcentral, neg_zero, ← hα] at hb
      have hne : affineSimpleE B T S i ≠ 0 := by
        intro hz
        apply CartanQuotient.e_ne_zero R i
        apply E.injective
        change E (CartanQuotient.e R i) = E 0
        rw [he i, hz, map_zero]
      exact (smul_eq_zero.mp hb.symm).resolve_right hne
    have hh : h ∈ W.dualCoannihilator := by
      change h ∈ (W.dualCoannihilator : Set _)
      rw [Submodule.coe_dualCoannihilator_span]
      rintro _ ⟨i, rfl⟩
      exact hvanish i
    rw [hline] at hh
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hh
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact (LieModule.mem_maxTrivSubmodule ℂ (AffineAlgebra B) (AffineAlgebra B) _).mpr
      fun x => by rw [← lie_skew, centralGenerator, neg_zero]

private theorem center_iff_equiv {L M : Type u} [LieRing L] [LieAlgebra ℂ L]
    [LieRing M] [LieAlgebra ℂ M] (E : L ≃ₗ⁅ℂ⁆ M) (z : L) :
    z ∈ LieAlgebra.center ℂ L ↔ E z ∈ LieAlgebra.center ℂ M := by
  rw [LieModule.mem_maxTrivSubmodule, LieModule.mem_maxTrivSubmodule]
  constructor
  · intro hz x
    obtain ⟨y, rfl⟩ := E.surjective x
    change ⁅E y, E z⁆ = 0
    rw [← E.map_lie, hz, map_zero]
  · intro hz x
    apply E.injective
    change E ⁅x, z⁆ = E 0
    rw [E.map_lie, hz, map_zero]

/-- The affine Cartan data present the normalized untwisted loop model with
its central generator and degree derivation. -/
theorem affineContragredientComparison :
    _root_.Specs.LieNotes.Affine.ContragredientComparison.AffineContragredientComparison.{u} := by
  classical
  intro G _ _ _ _ B H _ φ hB hφ
  let D := affineTriangularDecomposition B H φ hB hφ
  constructor
  · obtain ⟨θ, hθ, _⟩ := D.highest_root
    exact ⟨θ, hθ, D.triple_choices θ hθ⟩
  intro θ hθ T S
  obtain ⟨idx, hd⟩ := affineCartanRealization B H φ hB hφ θ hθ
  let := idx
  obtain ⟨A, R, hc, hα, hGCM, hsymm, hmin, hrank⟩ := hd
  let rel := affineRelations (T := T) (S := S) R hc hα D hθ
  let F := Presentation.lift R _ _ _ rel
  have hF := affineLift_surjective rel D hθ
  have hker := affineLift_ker hB F hF (Presentation.lift_cartan R _ _ _ rel)
  let E := comparisonEquiv F hF hker
  have he (i) : E (CartanQuotient.e R i) = affineSimpleE B T S i :=
    (comparisonEquiv_apply F hF hker _).trans (Presentation.lift_e R _ _ _ rel i)
  have hcenter := affineCenter R hα hmin hrank D hθ E he
  refine ⟨idx, A, R, hc, hα, hGCM, hsymm, hmin, hrank, E, ?_, he, ?_, hcenter, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (comparisonEquiv_apply F hF hker _).trans (Presentation.lift_cartan R _ _ _ rel h)
  · intro i
    exact (comparisonEquiv_apply F hF hker _).trans (Presentation.lift_f R _ _ _ rel i)
  · ext z
    change z ∈ LieAlgebra.center ℂ (CartanQuotient.Algebra R) ↔ _
    rw [center_iff_equiv E z]
    change E z ∈ (LieAlgebra.center ℂ (AffineAlgebra B)).toSubmodule ↔ _
    rw [hcenter, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by simpa using congrArg E.symm hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by simpa using congrArg E hc⟩
  · intro c k hz
    have heq : c • K B + k • d B = 0 := by simpa using congrArg E hz
    have hcoords := congrArg (coordinates B) heq
    simp only [map_add, map_smul, map_zero, coordinates_K, coordinates_d, Prod.smul_mk,
      Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, smul_zero, zero_add, add_zero] at hcoords
    exact ⟨congrArg (fun z : ((ℤ →₀ G) × ℂ) × ℂ => z.1.2) hcoords,
      congrArg (fun z : ((ℤ →₀ G) × ℂ) × ℂ => z.2) hcoords⟩
  · rw [center_iff_equiv E, LieEquiv.apply_symm_apply]
    change d B ∉ (LieAlgebra.center ℂ (AffineAlgebra B)).toSubmodule
    rw [hcenter, Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    have hd := congrArg (fun x : AffineAlgebra B => (coordinates B x).2) hc
    simp only [map_smul, coordinates_K, coordinates_d, Prod.smul_mk, smul_zero,
      zero_ne_one] at hd
  · intro m x
    rw [← E.symm.map_lie, degreeBracket, map_smul]

end

end LieNotes.Affine
