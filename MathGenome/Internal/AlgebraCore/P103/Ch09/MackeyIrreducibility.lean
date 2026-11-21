import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.MackeyIrreducibility
import MathGenome.Internal.AlgebraCore.P103.Ch09.MackeyDecomposition
import MathGenome.Internal.AlgebraCore.P103.Ch09.FrobeniusHom
import MathGenome.Internal.AlgebraCore.P103.Ch09.Coinduction
import MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity
import Batteries.Tactic.OpenPrivate

noncomputable section
universe u v w
namespace P103.Ch09.MackeyIrreducibility
set_option maxHeartbeats 1000000
open scoped MonoidAlgebra DirectSum Classical
open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
attribute [local instance] inducedScalarModule inducedAlgebraModule

/-- Evaluation in the function model is a left inverse to v ↦ 1 ⊗ v. -/
theorem tensor_one_injective {G : Type u} [Group G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) :
    Function.Injective (tensor H ρ 1) := by
  intro x y h
  have hx := (functionModelData H ρ).generator_mul 1 1 x
  have hy := (functionModelData H ρ).generator_mul 1 1 y
  have hh := congrArg (fun z => ((functionModelData H ρ).equivalence z).1 1) h
  have hx' : ((functionModelData H ρ).equivalence (tensor H ρ 1 x)).1 1 = x := by
    simpa [← MonoidAlgebra.one_def] using hx
  have hy' : ((functionModelData H ρ).equivalence (tensor H ρ 1 y)).1 1 = y := by
    simpa [← MonoidAlgebra.one_def] using hy
  exact hx'.symm.trans (hh.trans hy')

theorem induced_nonzero : Specs.inducedNonzeroType.{u,v} := by
  intro G _ H V _ _ _ ρ
  exact (tensor_one_injective H ρ).nontrivial

/-- Pullback through a surjective group map preserves the source's nonzero
irreducibility convention. -/
theorem irreducible_comp {J : Type u} {K : Type w} [Group J] [Group K]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ J V) (f : K →* J) (hf : Function.Surjective f)
    (hρ : Ch08.Irreducible ℂ J V ρ) : Ch08.Irreducible ℂ K V (ρ.comp f) := by
  refine ⟨hρ.1, fun U => ?_⟩
  let U' : Subrepresentation ρ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro j x hx
        obtain ⟨a, rfl⟩ := hf j
        exact U.apply_mem_toSubmodule a hx }
  rcases hρ.2 U' with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) hb
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht

/-- The subgroup in the criterion is the whole of H when H is normal. -/
theorem normal_intersection {G : Type u} [Group G] (H : Subgroup G)
    [H.Normal] (s : G) : Mackey.intersection H H s = ⊤ := by
  apply top_unique
  intro h _
  exact Subgroup.Normal.conj_mem' inferInstance _ h.2 s

/-- The normal conjugation map is an automorphism, in particular surjective. -/
theorem normalConjugation_surjective {G : Type u} [Group G] (H : Subgroup G)
    [H.Normal] (s : G) : Function.Surjective (normalConjugation H s) := by
  intro h
  refine ⟨normalConjugation H s⁻¹ h, ?_⟩
  apply Subtype.ext
  simp [normalConjugation, mul_assoc]

/-- The twist of an irreducible normal-subgroup representation is irreducible. -/
theorem normalTwist_irreducible {G : Type u} [Group G] (H : Subgroup G)
    [H.Normal] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : Ch08.Irreducible ℂ H V ρ) (s : G) :
    Ch08.Irreducible ℂ H V (normalTwist H ρ s) :=
  irreducible_comp ρ _ (normalConjugation_surjective H s) hρ

/-- In a semisimple domain, disjoint simple submodules characterize a zero
Hom space. This form does not require either representation to be irreducible. -/
theorem no_common_iff_subsingleton_hom {J : Type u} [Group J] [Finite J]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ J V) (σ : Representation ℂ J W) :
    NoCommonConstituent ρ σ ↔ Subsingleton (ρ.IntertwiningMap σ) := by
  have : NeZero (Nat.card J : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  let E := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  have hm : NoCommonConstituent ρ σ ↔
      Subsingleton (ρ.asModule →ₗ[ℂ[J]] σ.asModule) := by
    constructor
    · intro h
      apply subsingleton_of_forall_eq 0
      intro f
      by_contra hf
      obtain ⟨S, hS, hne⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top hf
        {S : Submodule ℂ[J] ρ.asModule | IsSimpleModule ℂ[J] S}
        (IsSemisimpleModule.sSup_simples_eq_top ℂ[J] ρ.asModule)
      change IsSimpleModule ℂ[J] S at hS
      have := hS
      let g := f.comp S.subtype
      have hg : Function.Injective g := LinearMap.injective_of_ne_zero hne
      let T := LinearMap.range g
      let e : S ≃ₗ[ℂ[J]] T := LinearEquiv.ofInjective g hg
      have hT : IsSimpleModule ℂ[J] T := IsSimpleModule.congr e.symm
      exact h S T hS hT ⟨e⟩
    · intro h S T hS hT ⟨e⟩
      have := hS
      have := hT
      obtain ⟨Q, hQ⟩ := exists_isCompl S
      let f : ρ.asModule →ₗ[ℂ[J]] σ.asModule :=
        T.subtype.comp (e.toLinearMap.comp (S.projectionOnto Q hQ))
      have hf : f = 0 := Subsingleton.elim _ _
      have : Nontrivial S := IsSimpleModule.nontrivial ℂ[J] S
      obtain ⟨x, hx⟩ := exists_ne (0 : S)
      apply hx
      apply e.injective
      apply T.subtype_injective
      have heq := LinearMap.congr_fun hf (x : ρ.asModule)
      simpa [f] using heq
  rw [hm]
  exact ⟨fun h => E.injective.subsingleton, fun h => E.symm.injective.subsingleton⟩

/-- The End-dimension test used by Mackey's criterion, with its nonzero
hypothesis on the original representation (not on induction). -/
theorem irreducible_iff_end_finrank_one {J : Type u} [Group J] [Finite J]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ J V) :
    Ch08.Irreducible ℂ J V ρ ↔ Module.finrank ℂ (ρ.IntertwiningMap ρ) = 1 := by
  constructor
  · intro hρ
    have := libraryIrreducible ρ hρ
    exact Representation.IsIrreducible.finrank_intertwiningMap_self ρ
  · intro hd
    have : NeZero (Nat.card J : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    have : Nontrivial ρ.asModule := ρ.asModuleEquiv.symm.injective.nontrivial
    let E := Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ
    have hid : (LinearMap.id : Module.End ℂ[J] ρ.asModule) ≠ 0 := by
      intro h
      obtain ⟨x, hx⟩ := exists_ne (0 : ρ.asModule)
      exact hx (LinearMap.congr_fun h x)
    have hd' : Module.finrank ℂ (Module.End ℂ[J] ρ.asModule) = 1 :=
      E.finrank_eq.symm.trans hd
    have scalar := (finrank_eq_one_iff_of_nonzero' (K := ℂ) _ hid).mp hd'
    have simple : IsSimpleModule ℂ[J] ρ.asModule := by
      refine { eq_bot_or_eq_top := ?_ }
      intro S
      by_cases hs : S = ⊥
      · exact Or.inl hs
      · right
        obtain ⟨Q, hQ⟩ := exists_isCompl S
        obtain ⟨c, hc⟩ := scalar (S.projection Q hQ)
        have : Nontrivial S := (Submodule.nontrivial_iff_ne_bot).mpr hs
        obtain ⟨x, hx⟩ := exists_ne (0 : S)
        have hx' : (x : ρ.asModule) ≠ 0 := by
          intro h
          exact hx (Subtype.ext h)
        have hc' : c = 1 := by
          have h := LinearMap.congr_fun hc (x : ρ.asModule)
          have hxsmul : c • (x : ρ.asModule) = (1 : ℂ) • (x : ρ.asModule) := by
            simpa using h
          exact (smul_left_injective ℂ hx') hxsmul
        have hp : S.projection Q hQ = LinearMap.id := by simpa [hc'] using hc.symm
        have hr := Submodule.range_projection hQ
        rw [hp, LinearMap.range_id] at hr
        exact hr.symm
    have : Representation.IsIrreducible ρ :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr simple
    exact ⟨inferInstance, fun U => eq_bot_or_eq_top U⟩

/-- Finite-dimensional Hom spaces have dimension zero exactly when there is
no common simple constituent. -/
theorem no_common_iff_finrank_hom_zero {J : Type u} [Group J] [Finite J]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ J V) (σ : Representation ℂ J W) :
    NoCommonConstituent ρ σ ↔ Module.finrank ℂ (ρ.IntertwiningMap σ) = 0 := by
  rw [no_common_iff_subsingleton_hom]
  exact (Module.finrank_eq_zero_iff_of_free ℂ (ρ.IntertwiningMap σ)).symm

/-- Between irreducibles, a common constituent is precisely an isomorphism.
This does not need finiteness of the group. -/
theorem no_common_iff_not_equiv {J : Type u} [Group J]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ J V) (σ : Representation ℂ J W)
    (hρ : Ch08.Irreducible ℂ J V ρ) (hσ : Ch08.Irreducible ℂ J W σ) :
    NoCommonConstituent ρ σ ↔ ¬ Nonempty (ρ.Equiv σ) := by
  have := libraryIrreducible ρ hρ
  have := libraryIrreducible σ hσ
  constructor
  · intro h ⟨e⟩
    have he := Ch08.RegularMultiplicity.moduleEquivOfEquiv e
    have htρ : IsSimpleModule ℂ[J] (⊤ : Submodule ℂ[J] ρ.asModule) :=
      IsSimpleModule.congr Submodule.topEquiv
    have htσ : IsSimpleModule ℂ[J] (⊤ : Submodule ℂ[J] σ.asModule) :=
      IsSimpleModule.congr Submodule.topEquiv
    exact h ⊤ ⊤ htρ htσ ⟨Submodule.topEquiv.trans (he.trans Submodule.topEquiv.symm)⟩
  · intro h S T hS hT ⟨e⟩
    have : S = ⊤ := isAtom_iff_eq_top.mp (isSimpleModule_iff_isAtom.mp hS)
    have : T = ⊤ := isAtom_iff_eq_top.mp (isSimpleModule_iff_isAtom.mp hT)
    subst S
    subst T
    let em := Submodule.topEquiv.symm.trans (e.trans Submodule.topEquiv)
    let f := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm em.toLinearMap
    exact h ⟨f.ofBijective em.bijective⟩

/-- Equivalences descend through a surjective group map: the underlying linear
isomorphism is unchanged. -/
theorem equiv_comp_iff {J : Type u} {K : Type w} [Group J] [Group K]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ J V) (σ : Representation ℂ J W)
    (f : K →* J) (hf : Function.Surjective f) :
    Nonempty (Representation.Equiv (ρ.comp f) (σ.comp f)) ↔ Nonempty (ρ.Equiv σ) := by
  constructor
  · rintro ⟨e⟩
    refine ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
    intro j
    obtain ⟨a, rfl⟩ := hf j
    exact e.toIntertwiningMap.isIntertwining' a
  · rintro ⟨e⟩
    refine ⟨Representation.Equiv.mk (ρ := ρ.comp f) (σ := σ.comp f) e.toLinearEquiv ?_⟩
    intro a
    exact e.toIntertwiningMap.isIntertwining' (f a)

/-- The full normal-subgroup simplification, with no induced irreducibility
hypothesis. -/
theorem normal_disjointness : Specs.normalDisjointnessType.{u,v} := by
  intro G _ H _ V _ _ ρ hρ
  have hs (s : G) : Function.Surjective (Mackey.intersection H H s).subtype := by
    intro h
    refine ⟨⟨h, ?_⟩, rfl⟩
    rw [normal_intersection]
    trivial
  have ht (s : G) : Mackey.twist H H ρ s =
      (normalTwist H ρ s).comp (Mackey.intersection H H s).subtype := rfl
  have pointwise (s : G) : NoCommonConstituent
      (restrict (Mackey.intersection H H s) ρ) (Mackey.twist H H ρ s) ↔
      ¬ Nonempty (ρ.Equiv (normalTwist H ρ s)) := by
    rw [ht]
    change NoCommonConstituent (ρ.comp _) ((normalTwist H ρ s).comp _) ↔ _
    rw [no_common_iff_not_equiv _ _ (irreducible_comp ρ _ (hs s) hρ)
      (irreducible_comp _ _ (hs s) (normalTwist_irreducible H ρ hρ s))]
    rw [equiv_comp_iff ρ (normalTwist H ρ s) _ (hs s)]
  exact ⟨fun h s hs => (pointwise s).mp (h s hs),
    fun h s hs => (pointwise s).mpr (h s hs)⟩

/-- Postcomposition by an equivariant isomorphism is a complex linear Hom
isomorphism. -/
def homCongrRight {J : Type*} [Group J]
    {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (ρ : Representation ℂ J A) {σ : Representation ℂ J B} {τ : Representation ℂ J C}
    (e : σ.Equiv τ) : ρ.IntertwiningMap σ ≃ₗ[ℂ] ρ.IntertwiningMap τ where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  left_inv f := by ext x; exact e.toLinearEquiv.symm_apply_apply _
  right_inv f := by ext x; exact e.toLinearEquiv.apply_symm_apply _
  map_add' f g := by ext x; exact map_add e _ _
  map_smul' c f := by ext x; exact map_smul e c _

/-- Hom into a finite direct sum is the product of the Hom spaces. -/
def homDirectSumEquiv {J I : Type*} [Group J] [Fintype I]
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    {B : I → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
    (ρ : Representation ℂ J A) (σ : ∀ i, Representation ℂ J (B i)) :
    ρ.IntertwiningMap (Representation.directSum σ) ≃ₗ[ℂ]
      ∀ i, ρ.IntertwiningMap (σ i) where
  toFun f i :=
    { toLinearMap := (DFinsupp.lapply i).comp f.toLinearMap
      isIntertwining' g := by
        ext x
        exact congrArg (fun z : ⨁ i, B i => z i)
          (Representation.IntertwiningMap.isIntertwining ρ (Representation.directSum σ) f g x) }
  invFun f :=
    { toLinearMap := DFinsupp.linearEquivFunOnFintype.symm.toLinearMap.comp
        (LinearMap.pi fun i => (f i).toLinearMap)
      isIntertwining' g := by
        ext x i
        exact Representation.IntertwiningMap.isIntertwining ρ (σ i) (f i) g x }
  left_inv f := by ext x i; rfl
  right_inv f := by ext i x; rfl
  map_add' f g := by ext i x; rfl
  map_smul' c f := by ext i x; rfl

/-- Right Frobenius reciprocity for induction at finite index, derived using
the actual induction-to-coinduction comparison. -/
def rightFrobeniusEquiv {J : Type*} [Group J] (L : Subgroup J) [L.FiniteIndex]
    {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρ : Representation ℂ J A) (σ : Representation ℂ L B) :
    ρ.IntertwiningMap (induction L σ) ≃ₗ[ℂ] (restrict L ρ).IntertwiningMap σ := by
  let C := Coinduction.data L σ
  let D := inductionData L σ
  let E := functionModelData L σ
  let e : (induction L σ).Equiv C.representation :=
    (Coinduction.embedding L σ C D E).ofBijective
      ⟨Coinduction.embedding_injective L σ C D E,
        Coinduction.embedding_surjective L σ C D E⟩
  exact (homCongrRight ρ e).trans (Coinduction.adjunction L σ C ρ)

/-- The endomorphism space splits over all double cosets. This uses the right
adjunction for each summand, so the Hom spaces have the required orientation. -/
def mackeyEndEquiv {G : Type u} [Group G] [Finite G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (R : Mackey.Representatives H H) :
    (induction H ρ).IntertwiningMap (induction H ρ) ≃ₗ[ℂ]
      ∀ q : DoubleCoset.Quotient (H : Set G) H,
        (restrict (Mackey.intersection H H (R.representative q)) ρ).IntertwiningMap
          (Mackey.twist H H ρ (R.representative q)) := by
  classical
  letI : Finite (DoubleCoset.Quotient (H : Set G) H) :=
    inferInstanceAs (Finite (Quotient (DoubleCoset.setoid (H : Set G) H)))
  letI : Fintype (DoubleCoset.Quotient (H : Set G) H) := Fintype.ofFinite _
  let σ := fun q => induction (Mackey.intersection H H (R.representative q))
    (Mackey.twist H H ρ (R.representative q))
  let e : (restrict H (induction H ρ)).Equiv (Representation.directSum σ) :=
    Representation.Equiv.mk (Mackey.decompositionEquiv H H ρ R) (by
      intro h
      apply LinearMap.ext
      intro z
      apply (Mackey.decompositionEquiv H H ρ R).symm.injective
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply]
      change _ = Mackey.sumToGlobal H H ρ R
        (DirectSum.lmap (fun q => σ q h) (Mackey.decompositionEquiv H H ρ R z))
      rw [Mackey.sumToGlobal_equivariant]
      change _ = induction H ρ (h : G)
        ((Mackey.decompositionEquiv H H ρ R).symm
          (Mackey.decompositionEquiv H H ρ R z))
      rw [LinearEquiv.symm_apply_apply]
      rfl)
  exact (frobeniusEquiv H ρ (induction H ρ) (inductionData H ρ)).trans
    ((homCongrRight ρ e).trans ((homDirectSumEquiv ρ σ).trans
      (LinearEquiv.piCongrRight fun q => rightFrobeniusEquiv _ ρ _)))

/-- Pulling both arguments back by a surjection preserves the Hom space. -/
def homCompEquiv {J K : Type*} [Group J] [Group K]
    {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρ : Representation ℂ J A) (σ : Representation ℂ J B)
    (f : K →* J) (hf : Function.Surjective f) :
    ρ.IntertwiningMap σ ≃ₗ[ℂ] Representation.IntertwiningMap (ρ.comp f) (σ.comp f) where
  toFun g := ⟨g.toLinearMap, fun a => g.isIntertwining' (f a)⟩
  invFun g := ⟨g.toLinearMap, fun a => by
    obtain ⟨b, rfl⟩ := hf a
    exact g.isIntertwining' b⟩
  left_inv g := rfl
  right_inv g := rfl
  map_add' g h := rfl
  map_smul' c g := rfl

/-- Membership in the identity double coset is precisely membership in H. -/
theorem identity_coset_iff {G : Type u} [Group G] (H : Subgroup G) (s : G) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 ↔ s ∈ H := by
  rw [eq_comm, DoubleCoset.eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using H.mul_mem ha hb
  · intro hs
    exact ⟨s, hs, 1, H.one_mem, by simp⟩

/-- A section containing 1 and any prescribed nonidentity-coset representative.
This permits every s outside H to be tested without a representative-invariance
assumption. -/
def representativesWith {G : Type u} [Group G] (H : Subgroup G) (s : G) :
    Mackey.Representatives H H where
  representative q := if q = DoubleCoset.mk H H 1 then 1
    else if q = DoubleCoset.mk H H s then s else q.out
  represents q := by
    classical
    split_ifs with h h
    · exact h.symm
    · exact h.symm
    · exact DoubleCoset.out_eq' q

@[simp] theorem representativesWith_one {G : Type u} [Group G] (H : Subgroup G) (s : G) :
    (representativesWith H s).representative (DoubleCoset.mk H H 1) = 1 := by
  classical
  simp [representativesWith]

@[simp] theorem representativesWith_self {G : Type u} [Group G] (H : Subgroup G)
    (s : G) (hs : s ∉ H) :
    (representativesWith H s).representative (DoubleCoset.mk H H s) = s := by
  classical
  simp [representativesWith, (identity_coset_iff H s).not.mpr hs]

/-- The identity contribution is End_H(V), even for reducible V. -/
theorem identity_finrank {G : Type u} [Group G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) :
    Module.finrank ℂ ((restrict (Mackey.intersection H H 1) ρ).IntertwiningMap
      (Mackey.twist H H ρ 1)) = Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
  have ht : Mackey.twist H H ρ 1 = restrict (Mackey.intersection H H 1) ρ := by
    have hm : Mackey.intoSubgroup H H (1 : G) = (Mackey.intersection H H 1).subtype := by
      ext a
      simp [Mackey.intoSubgroup, Mackey.conjugation]
    exact congrArg (fun f => ρ.comp f) hm
  have hs : Function.Surjective (Mackey.intersection H H 1).subtype := by
    intro h
    refine ⟨⟨h, ?_⟩, rfl⟩
    simpa using h.2
  rw [ht]
  exact (homCompEquiv ρ ρ _ hs).finrank_eq.symm

/-- Taking ordinary dimensions in the Mackey Hom-space isomorphism. -/
theorem end_finrank_sum {G : Type u} [Group G] [Finite G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (R : Mackey.Representatives H H) :
    letI : Finite (DoubleCoset.Quotient (H : Set G) H) :=
      inferInstanceAs (Finite (Quotient (DoubleCoset.setoid (H : Set G) H)))
    letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) H)
    Module.finrank ℂ ((induction H ρ).IntertwiningMap (induction H ρ)) =
      ∑ q : DoubleCoset.Quotient (H : Set G) H,
        Module.finrank ℂ ((restrict (Mackey.intersection H H (R.representative q)) ρ).IntertwiningMap
          (Mackey.twist H H ρ (R.representative q))) := by
  classical
  letI : Finite (DoubleCoset.Quotient (H : Set G) H) :=
    inferInstanceAs (Finite (Quotient (DoubleCoset.setoid (H : Set G) H)))
  letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) H)
  rw [(mackeyEndEquiv H ρ R).finrank_eq, Module.finrank_pi_fintype]

/-- The identity endomorphism is nonzero whenever the representation is. -/
theorem end_finrank_pos {J : Type*} [Group J]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ J V) :
    0 < Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨Representation.IntertwiningMap.id ρ, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (congrArg (fun f : ρ.IntertwiningMap ρ => f x) h)

/-- A distinguished positive summand accounts for the entire sum precisely
when it is one and every other summand vanishes. -/
theorem sum_one_iff {I : Type*} [Fintype I] (f : I → ℕ) (i : I) (hi : 0 < f i) :
    (∑ j, f j) = 1 ↔ f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
  classical
  constructor
  · intro h
    have hle : f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hone : f i = 1 := by omega
    have hsplit := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ i)
    have hzero : ∑ j ∈ Finset.univ.erase i, f j = 0 := by omega
    exact ⟨hone, fun j hj => (Finset.sum_eq_zero_iff.mp hzero) j (by simp [hj])⟩
  · rintro ⟨hone, hzero⟩
    calc
      (∑ j, f j) = f i := Finset.sum_eq_single i (fun j _ hj => hzero j hj) (by simp)
      _ = 1 := hone

/-- Mackey's criterion, including the forward implication for reducible V. -/
theorem criterion : Specs.criterionType.{u,v} := by
  intro G _ _ H V _ _ _ _ ρ D
  have hD := Mackey.inductionData_unique H ρ D
  subst D
  letI : Nontrivial (Induced H ρ) := induced_nonzero H ρ
  letI : FiniteDimensional ℂ (Induced H ρ) := TensorCoordinates.induced_finiteDimensional H ρ
  letI : Finite (DoubleCoset.Quotient (H : Set G) H) :=
    inferInstanceAs (Finite (Quotient (DoubleCoset.setoid (H : Set G) H)))
  letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) H)
  let q₀ := DoubleCoset.mk H H (1 : G)
  let d (s : G) := Module.finrank ℂ
    ((restrict (Mackey.intersection H H s) ρ).IntertwiningMap (Mackey.twist H H ρ s))
  have hd₀ : d 1 = Module.finrank ℂ (ρ.IntertwiningMap ρ) := identity_finrank H ρ
  have rank_criterion (R : Mackey.Representatives H H) (hR : R.representative q₀ = 1) :
      Module.finrank ℂ ((induction H ρ).IntertwiningMap (induction H ρ)) = 1 ↔
        Module.finrank ℂ (ρ.IntertwiningMap ρ) = 1 ∧
          ∀ q, q ≠ q₀ → d (R.representative q) = 0 := by
    rw [end_finrank_sum H ρ R]
    change (∑ q, d (R.representative q)) = 1 ↔ _
    have hp : 0 < d (R.representative q₀) := by rw [hR, hd₀]; exact end_finrank_pos ρ
    rw [sum_one_iff _ q₀ hp, hR, hd₀]
  change Ch08.Irreducible ℂ G (Induced H ρ) (induction H ρ) ↔ _
  rw [irreducible_iff_end_finrank_one]
  constructor
  · intro hX
    have hρ : Ch08.Irreducible ℂ H V ρ :=
      (irreducible_iff_end_finrank_one ρ).mpr
        ((rank_criterion (representativesWith H 1) (representativesWith_one H 1)).mp hX).1
    refine ⟨hρ, fun s hs => ?_⟩
    have h := ((rank_criterion (representativesWith H s)
      (representativesWith_one H s)).mp hX).2 (DoubleCoset.mk H H s)
      ((identity_coset_iff H s).not.mpr hs)
    rw [representativesWith_self H s hs] at h
    exact (no_common_iff_finrank_hom_zero _ _).mpr h
  · rintro ⟨hρ, hdisj⟩
    apply (rank_criterion (representativesWith H 1) (representativesWith_one H 1)).mpr
    refine ⟨(irreducible_iff_end_finrank_one ρ).mp hρ, fun q hq => ?_⟩
    have hs : (representativesWith H 1).representative q ∉ H := by
      intro hs
      apply hq
      exact ((representativesWith H 1).represents q).symm.trans
        ((identity_coset_iff H _).mpr hs)
    exact (no_common_iff_finrank_hom_zero _ _).mp (hdisj _ hs)

/-- For normal H, disjointness is nonisomorphism of each conjugate outside H. -/
theorem normal_criterion : Specs.normalCriterionType.{u,v} := by
  intro G _ _ H _ V _ _ _ _ ρ D
  rw [criterion H ρ D]
  exact and_congr_right fun hρ => normal_disjointness H ρ hρ

end P103.Ch09.MackeyIrreducibility
