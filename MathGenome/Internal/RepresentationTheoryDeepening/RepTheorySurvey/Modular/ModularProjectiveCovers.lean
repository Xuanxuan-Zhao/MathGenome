import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.GroupAlgebraReduction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.IdempotentLifting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplitMatrixColumns
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ModularProjectiveCovers
import Mathlib.RingTheory.Artinian.Ring

/-! Idempotent lifts and the projective covers of the modular simple columns. -/

namespace RepTheorySurvey.Modular

open scoped Matrix Matrix.Module

/-- The principal left ideal `R e`. -/
abbrev principalLeftIdeal {R : Type*} [Ring R] (e : R) : Ideal R :=
  Ideal.span {e}

private theorem mul_generator_eq_self {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) (x : principalLeftIdeal e) : (x : R) * e = x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
  rw [← ha, mul_assoc, he.eq]

/-- Right multiplication by an idempotent retracts the regular module onto its left ideal. -/
theorem principalLeftIdeal_projective {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) : Module.Projective R (principalLeftIdeal e) := by
  let retract := (LinearMap.toSpanSingleton R R e).codRestrict (principalLeftIdeal e)
    (fun a => Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
  apply Module.Projective.of_split (principalLeftIdeal e).subtype retract
  exact LinearMap.ext fun x => Subtype.ext (mul_generator_eq_self he x)

private theorem groupAlgebra_jacobson_nilpotent {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] :
    IsNilpotent (Ring.jacobson (MonoidAlgebra F G)) := by
  let : IsArtinianRing (MonoidAlgebra F G) :=
    isArtinian_of_tower F (inferInstance : IsArtinian F (MonoidAlgebra F G))
  simpa only [Ideal.jacobson_bot] using
    (IsArtinianRing.isNilpotent_jacobson_bot (R := MonoidAlgebra F G))

/-- Every idempotent of the radical quotient lifts to the modular group algebra. -/
theorem exists_modular_idempotent_lift {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (E : GroupAlgebraRadicalQuotient F G) (hE : IsIdempotentElem E) :
    ∃ e : MonoidAlgebra F G, IsIdempotentElem e ∧ groupAlgebraRadicalQuotientMap F G e = E := by
  apply exists_idempotent_lift (Ring.jacobson (MonoidAlgebra F G)) _ E hE
  obtain ⟨n, hn⟩ := groupAlgebra_jacobson_nilpotent (F := F) (G := G)
  exact Or.inl ⟨n, hn⟩

/-- Every modular idempotent lifts through coefficient reduction. -/
theorem exists_integral_idempotent_lift
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K] (S : SplittingSystem G p O K)
    (e : MonoidAlgebra (IsLocalRing.ResidueField O) G) (he : IsIdempotentElem e) :
    ∃ lift : MonoidAlgebra O G, IsIdempotentElem lift ∧ groupAlgebraReduction O G lift = e := by
  obtain ⟨equiv, hEquiv⟩ := exists_groupAlgebraReduction_quotientEquiv O G S
  obtain ⟨lift, hLift, hRed⟩ := exists_idempotent_lift
    (groupAlgebraUniformizerIdeal O G S.uniformizer)
    (Or.inr (groupAlgebraUniformizerIdeal_completeSeparated O G S))
    (equiv.symm e) (he.map equiv.symm)
  exact ⟨lift, hLift, (hEquiv lift).symm.trans
    ((congrArg equiv hRed).trans (equiv.apply_symm_apply e))⟩

open Classical in
/-- A rank-one idempotent in any selected factor lifts with zero in all other factors. -/
theorem exists_modular_rank_one_idempotent_lift
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {r : ℕ} {d : Fin r → ℕ}
    (split : GroupAlgebraRadicalQuotient F G ≃ₐ[F]
      ((j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F))
    (i : Fin r) (E : Matrix (Fin (d i)) (Fin (d i)) F)
    (hE : IsIdempotentElem E) (_ : E.rank = 1) :
    ∃ e : MonoidAlgebra F G, IsIdempotentElem e ∧ modularColumnMap split e = Pi.single i E := by
  let tuple : (j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F := Pi.single i E
  have hp : IsIdempotentElem tuple := by
    dsimp only [tuple]
    rw [IsIdempotentElem, ← Pi.single_mul, hE.eq]
  obtain ⟨e, he, heq⟩ := exists_modular_idempotent_lift _ (hp.map split.symm)
  exact ⟨e, he, (congrArg split heq).trans (split.apply_symm_apply _)⟩

private theorem eq_top_of_sup_smul_top_of_nilpotent {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {J : Ideal R} (hJ : IsNilpotent J) (U : Submodule R M)
    (hU : J • (⊤ : Submodule R M) ⊔ U = ⊤) : U = ⊤ := by
  have hQ : J • (⊤ : Submodule R (M ⧸ U)) = ⊤ := by
    have h := congrArg (Submodule.map U.mkQ) hU
    simpa only [Submodule.map_sup, Submodule.map_smul'', Submodule.mkQ_map_self, sup_bot_eq,
      Submodule.map_top, U.range_mkQ] using h
  have hPow (n : ℕ) : J ^ n • (⊤ : Submodule R (M ⧸ U)) = ⊤ := by
    induction n with
    | zero => rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ n ih =>
      rw [Submodule.pow_succ]
      change (J ^ n • J) • (⊤ : Submodule R (M ⧸ U)) = ⊤
      rw [Submodule.smul_assoc, hQ, ih]
  obtain ⟨n, hn⟩ := hJ
  have hBot := hPow n
  change J ^ n = ⊥ at hn
  rw [hn, Submodule.bot_smul] at hBot
  exact Submodule.Quotient.subsingleton_iff.mp
    ((Submodule.subsingleton_iff R).mp (subsingleton_of_bot_eq_top hBot))

/-- For each lift, the quotient of `A e` by `J(A)(A e)` is the chosen simple column,
and the quotient map followed by this identification is a projective cover. -/
theorem modular_projective_cover
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {r : ℕ} {d : Fin r → ℕ}
    (split : GroupAlgebraRadicalQuotient F G ≃ₐ[F]
      ((j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F))
    (hd : ∀ j, 0 < d j) (i : Fin r) (e : MonoidAlgebra F G) (he : IsIdempotentElem e)
    (hrank : (modularColumnMap split e i).rank = 1)
    (hOther : ∀ j, j ≠ i → modularColumnMap split e j = 0) :
    let A := MonoidAlgebra F G
    let P := principalLeftIdeal e
    let J := Ring.jacobson A
    let JP := J • (⊤ : Submodule A P)
    Module.Projective A P ∧
      ∃ top : (P ⧸ JP) ≃ₗ[A] columnModule (modularColumnMap split) i,
        Function.Surjective (top.toLinearMap.comp JP.mkQ) ∧
          ∀ U : Submodule A P, U.map (top.toLinearMap.comp JP.mkQ) = ⊤ → U = ⊤ := by
  let A := MonoidAlgebra F G
  let P := principalLeftIdeal e
  let J := Ring.jacobson A
  let JP := J • (⊤ : Submodule A P)
  let q := modularColumnMap split
  let V := columnModule q i
  let W := LinearMap.range (columnAction q i e)
  have hDim : Module.finrank F W = 1 := (column_rank q e i).trans hrank
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (hDim.symm ▸ Nat.one_pos)
  let generator : V := v.val
  have hv' : generator ≠ 0 := fun h => hv (Subtype.ext h)
  have hFixed : e • generator = generator := by
    obtain ⟨w, hw⟩ := v.property
    change columnAction q i e generator = generator
    have hw' : columnAction q i e w = generator := hw
    rw [← hw', ← Module.End.mul_apply, ← map_mul, he.eq]
  let f : P →ₗ[A] V := (LinearMap.toSpanSingleton A V generator).comp P.subtype
  have hf (x : P) : f x = (x : A) • generator := rfl
  have hSurj : Function.Surjective f := by
    let : IsSimpleModule A V := (modular_column_family hd split).simple i
    intro w
    obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff A generator).mp
      (IsSimpleModule.span_singleton_eq_top A hv') w
    refine ⟨⟨a * e, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩, ?_⟩
    rw [hf, Subtype.coe_mk, mul_smul, hFixed, ha]
  -- Elements of the principal ideal act through the image line of the idempotent.
  have hKer : LinearMap.ker f = JP := by
    apply le_antisymm
    · intro x hx
      have hxv : columnAction q i (x : A) v.val = 0 := by
        exact LinearMap.mem_ker.mp hx
      have hxAction : columnAction q i (x : A) = 0 := by
        apply LinearMap.ext
        intro w
        obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hDim hv
          (⟨columnAction q i e w, LinearMap.mem_range_self _ w⟩ : W)
        have hc' : c • v.val = columnAction q i e w :=
          congrArg Subtype.val hc
        calc
          columnAction q i (x : A) w =
              columnAction q i (x : A) (columnAction q i e w) := by
            rw [← Module.End.mul_apply, ← map_mul, mul_generator_eq_self he x]
          _ = 0 := by rw [← hc', map_smul, hxv, smul_zero]
      have hxi : q (x : A) i = 0 := by
        apply Matrix.toLinAlgEquiv'.injective
        rw [map_zero]
        exact hxAction
      have hxJ : (x : A) ∈ J := by
        change (x : A) ∈ Ring.jacobson (MonoidAlgebra F G)
        rw [← modularColumnMap_ker split, RingHom.mem_ker]
        funext j
        by_cases hji : j = i
        · subst j
          exact hxi
        · have h := congrFun (congrArg q (mul_generator_eq_self he x)) j
          change q ((x : A) * e) j = q (x : A) j at h
          rw [map_mul, Pi.mul_apply, hOther j hji, mul_zero] at h
          exact h.symm
      let gen : P := ⟨e, Ideal.mem_span_singleton_self e⟩
      have hxGen : (x : A) • gen = x := Subtype.ext (mul_generator_eq_self he x)
      exact hxGen ▸ Submodule.smul_mem_smul hxJ (Submodule.mem_top : gen ∈ ⊤)
    · apply Submodule.smul_le.mpr
      intro a ha x _
      have hqa : q a = 0 :=
        RingHom.mem_ker.mp ((modularColumnMap_ker split).symm ▸ ha)
      rw [LinearMap.mem_ker, map_smul]
      change (q a i) *ᵥ (f x : Fin (d i) → F) = 0
      rw [hqa]
      exact Matrix.zero_mulVec _
  let top : (P ⧸ JP) ≃ₗ[A] V :=
    (Submodule.quotEquivOfEq JP (LinearMap.ker f) hKer.symm).trans
      (f.quotKerEquivOfSurjective hSurj)
  refine ⟨principalLeftIdeal_projective he, top,
    top.surjective.comp (Submodule.mkQ_surjective JP), fun U hU => ?_⟩
  have hU' : U.map JP.mkQ = ⊤ := by
    simpa only [Submodule.map_comp, Submodule.map_eq_top_iff] using hU
  exact eq_top_of_sup_smul_top_of_nilpotent groupAlgebra_jacobson_nilpotent U
    ((JP.map_mkQ_eq_top U).mp hU')

end RepTheorySurvey.Modular
