import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtExactSequences
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtBalance
import MathGenome.Internal.AlgebraCore.P103.Ch10.HorseshoeNaturality

namespace P103.Ch11.ExtExactSequences
open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10 P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
open P103.Specs.Ch11.ExtExactSequences
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

/-- The augmentation class is the inverse of canonical descent in degree zero. -/
theorem homClass_bijective {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] :
    Function.Bijective (homClass P B) := by
  have hc : Function.Bijective (homologyClass (homComplex P.complex B) 0) := by
    constructor
    · intro z z' h
      have he := (Submodule.Quotient.eq (cycleBoundaries (homComplex P.complex B) 0)).mp h
      rw [P103.Ch11.ExtTorDefinitions.cochain_zero_boundaries] at he
      exact sub_eq_zero.mp he
    · exact (cycleBoundaries _ 0).mkQ_surjective
  exact hc.comp (P103.Ch11.ExtTorDefinitions.homToZeroCycles_bijective P B)

/-- In degree zero, resolution maps induce exactly the original Hom arrows. -/
theorem homClass_natural {A A' : ModuleCat.{v} R}
    (P : LeftResolution R A) (Q : LeftResolution R A')
    {B B' : ModuleCat.{w} R} (f : A' ⟶ A) (g : B ⟶ B')
    (l : Q.complex ⟶ P.complex) (hl : ChainLift Q P f.hom l)
    (h : A →ₗ[R] B) :
    homologyMap (homPreMap l B ≫ homPostMap Q.complex g.hom) 0 (homClass P B h) =
      homClass Q B' (g.hom.comp (h.comp f.hom)) := by
  apply congrArg (homologyClass _ 0)
  apply Subtype.ext
  change g.hom.comp ((h.comp P.ε).comp (l.f 0).hom) = (g.hom.comp (h.comp f.hom)).comp Q.ε
  ext x
  exact congrArg (fun a => g.hom (h a)) (LinearMap.congr_fun hl x)

private theorem exact_transport
    {V W V' W' Z : Type*}
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup V'] [AddCommGroup W']
    [AddCommGroup Z]
    (eV : V →+ V') (eW : W →+ W') (f : V →+ W) (f' : V' →+ W')
    (d : W' →+ Z) (hV : Function.Surjective eV) (hW : Function.Injective eW)
    (hf : ∀ x, f' (eV x) = eW (f x)) (he : Function.Exact f' d) :
    Function.Exact f (d.comp eW) := by
  intro y
  change d (eW y) = 0 ↔ ∃ x, f x = y
  rw [he (eW y)]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := hV x
    exact ⟨v, hW ((hf v).symm.trans hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨eV x, hf x⟩

/-- Projectivity supplies all degreewise surjections in the coefficient sequence. -/
theorem second_degreewise_exact {A : ModuleCat.{v} R} (P : LeftResolution R A)
    (hP : P.IsProjective) {B₁ B₂ B₃ : ModuleCat.{w} R}
    (i : B₁ ⟶ B₂) (p : B₂ ⟶ B₃)
    (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    DegreewiseExact (homPostMap P.complex i.hom) (homPostMap P.complex p.hom) := by
  intro n
  obtain ⟨hinj, hex⟩ := P103.HomTensorExactness.homCovariant R B₁ B₂ B₃
    (P.complex.X n) i.hom p.hom hi he
  refine ⟨hinj, hex, ?_⟩
  let := hP n
  intro f
  change P.complex.X n →ₗ[R] B₃ at f
  change ∃ k : P.complex.X n →ₗ[R] B₂, p.hom.comp k = f
  exact Module.projective_lifting_property p.hom f hp

/-- The first coefficient Hom sequence is split in each resolution degree. -/
theorem first_degreewise_exact {A₁ A₂ A₃ : ModuleCat.{v} R}
    {i : A₁ ⟶ A₂} {p : A₂ ⟶ A₃} {L : LeftResolution R A₁}
    {N : LeftResolution R A₃} (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (B : ModuleCat.{w} R) :
    DegreewiseExact (homPreMap H.projection B) (homPreMap H.inclusion B) := by
  apply P103.Ch10.HorseshoeNaturality.split_exact
  apply P103.Ch10.HorseshoeNaturality.split_map (homFunctor B)
  apply P103.Ch10.HorseshoeNaturality.split_op
  exact P103.Ch10.HorseshoeNaturality.projective_split R A₁ A₂ A₃ i.hom p.hom L N H

/-- A given projective horseshoe gives the full first-variable sequence. -/
theorem first_horseshoe_sequence {A₁ A₂ A₃ : ModuleCat.{v} R}
    {i : A₁ ⟶ A₂} {p : A₂ ⟶ A₃} {L : LeftResolution R A₁}
    {N : LeftResolution R A₃} (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (B : ModuleCat.{w} R)
    (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom) :
    ∃ δ : ∀ n, ExtWith L B n →ₗ[ℤ] ExtWith N B (n + 1),
      (∀ n, FirstConnecting H B n (δ n) ∧ FirstExact H B n (δ n)) ∧
      FirstBottom (i := i) (p := p) B (δ 0) := by
  have hs := first_degreewise_exact H B
  have hd := fun n => P103.Ch10.HomologySequence.sequence
    (homPreMap H.projection B) (homPreMap H.inclusion B) hs n (n + 1) (by rfl)
  choose δ hδ huniq using hd
  refine ⟨δ, hδ, ?_⟩
  obtain ⟨hinj, hex⟩ := P103.HomTensorExactness.homContravariant R A₁ A₂ A₃ B
    i.hom p.hom he hp
  refine ⟨hinj, hex, ?_⟩
  apply exact_transport (homClass H.middle B).toAddMonoidHom (homClass L B).toAddMonoidHom
    (P103.HomTensorExactness.pre i.hom) (homologyMap (homPreMap H.inclusion B) 0).toAddMonoidHom
    (δ 0).toAddMonoidHom (homClass_bijective H.middle B).2 (homClass_bijective L B).1
    ?_ (hδ 0).2.2.1
  intro h
  have hh := homClass_natural H.middle L i (𝟙 B) H.inclusion H.augmentation_inclusion h
  exact hh

/-- Every ordinary projective horseshoe gives the first coefficient sequence. -/
theorem first_sequence : first_sequenceType.{u,v,w} := by
  intro R _ A₁ A₂ A₃ i p hi he hp B L N hL hN
  obtain ⟨H⟩ := P103.Ch10.Horseshoe.projective_horseshoe R A₁ A₂ A₃
    i.hom p.hom hi he hp L N hL hN
  exact ⟨⟨H⟩, fun H' => first_horseshoe_sequence H' B he hp⟩

theorem second_sequence : second_sequenceType.{u,v,w} := by
  intro R _ A P hP B₁ B₂ B₃ i p hi he hp
  have hs := second_degreewise_exact P hP i p hi he hp
  have hd := fun n => P103.Ch10.HomologySequence.sequence
    (homPostMap P.complex i.hom) (homPostMap P.complex p.hom) hs n (n + 1) (by rfl)
  choose δ hδ huniq using hd
  refine ⟨δ, hδ, ?_⟩
  obtain ⟨hinj, hex⟩ := P103.HomTensorExactness.homCovariant R B₁ B₂ B₃ A
    i.hom p.hom hi he
  refine ⟨hinj, hex, ?_⟩
  apply exact_transport (homClass P B₂).toAddMonoidHom (homClass P B₃).toAddMonoidHom
    (P103.HomTensorExactness.post p.hom) (homologyMap (homPostMap P.complex p.hom) 0).toAddMonoidHom
    (δ 0).toAddMonoidHom (homClass_bijective P B₂).2 (homClass_bijective P B₃).1
    ?_ (hδ 0).2.2.1
  intro h
  rfl

/-- Naturality of every connector for simultaneous coefficient changes. -/
theorem second_natural : second_naturalType.{u,v,w} := by
  intro R _ n E F A A' P Q hP hQ f B₁ B₂ B₃ B₁' B₂' B₃'
    i p i' p' a b c hi he hp hi' he' hp' hab hbc δ ε hδ hε
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists R A' A Q P hQ f.hom
  rw [F.formula ⟨P, hP⟩ ⟨Q, hQ⟩ f a l hl,
    E.formula ⟨P, hP⟩ ⟨Q, hQ⟩ f c l hl]
  have hs := second_degreewise_exact P hP i p hi he hp
  have hs' := second_degreewise_exact Q hQ i' p' hi' he' hp'
  apply (P103.Ch10.HomologySequence.naturality
    (homPostMap P.complex i.hom) (homPostMap P.complex p.hom)
    (homPostMap Q.complex i'.hom) (homPostMap Q.complex p'.hom)
    (homPreMap l B₁ ≫ homPostMap Q.complex a.hom)
    (homPreMap l B₂ ≫ homPostMap Q.complex b.hom)
    (homPreMap l B₃ ≫ homPostMap Q.complex c.hom)
    ?_ ?_ hs hs' n (n + 1) (by rfl) δ ε hδ hε).2.2.1
  · apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change P.complex.X k →ₗ[R] B₁ at h
    apply LinearMap.ext
    intro x
    exact congrArg (fun t : B₁ ⟶ B₂' => t.hom (h ((l.f k).hom x))) hab
  · apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change P.complex.X k →ₗ[R] B₂ at h
    apply LinearMap.ext
    intro x
    exact congrArg (fun t : B₂ ⟶ B₃' => t.hom (h ((l.f k).hom x))) hbc

theorem first_natural : first_naturalType.{u,v,w} := by
  intro R _ n E F A₁ A₂ A₃ A₁' A₂' A₃' i p i' p' a b c
    hi he hp hi' he' hp' hab hbc L N L' N' hL hN hL' hN' H H' B B' g δ ε hδ hε
  obtain ⟨α, β, γ, ha, hb, hc, hl, hr⟩ :=
    P103.Ch10.HorseshoeNaturality.projective_diagram R A₁' A₂' A₃' A₁ A₂ A₃
      i' p' i p a b c hi' he' hp' hi he hp hab hbc L' N' L N hL' hN' hL hN H' H
  rw [F.formula ⟨N, hN⟩ ⟨N', hN'⟩ c g γ hc,
    E.formula ⟨L, hL⟩ ⟨L', hL'⟩ a g α ha]
  apply (P103.Ch10.HomologySequence.naturality
    (homPreMap H.projection B) (homPreMap H.inclusion B)
    (homPreMap H'.projection B') (homPreMap H'.inclusion B')
    (homPreMap γ B ≫ homPostMap N'.complex g.hom)
    (homPreMap β B ≫ homPostMap H'.middle.complex g.hom)
    (homPreMap α B ≫ homPostMap L'.complex g.hom)
    ?_ ?_ (first_degreewise_exact H B) (first_degreewise_exact H' B')
    n (n + 1) (by rfl) δ ε hδ hε).2.2.1
  · apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change N.complex.X k →ₗ[R] B at h
    apply LinearMap.ext
    intro x
    exact congrArg (fun y => g.hom (h y))
      (congrArg (fun t => (t.f k).hom x) hr).symm
  · apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change H.middle.complex.X k →ₗ[R] B at h
    apply LinearMap.ext
    intro x
    exact congrArg (fun y => g.hom (h y))
      (congrArg (fun t => (t.f k).hom x) hl).symm

theorem coefficient_arrows : coefficient_arrowsType.{u,v,w} := by
  intro R _ n E
  constructor
  · intro A₁ A₂ A₃ i p L N hL hN H B
    constructor
    · exact (E.formula ⟨N, hN⟩ ⟨H.middle, H.projective⟩ p (𝟙 B)
        H.projection H.augmentation_projection).symm
    · exact (E.formula ⟨H.middle, H.projective⟩ ⟨L, hL⟩ i (𝟙 B)
        H.inclusion H.augmentation_inclusion).symm
  · intro A P hP B B' g
    exact (E.formula ⟨P, hP⟩ ⟨P, hP⟩ (𝟙 A) g (𝟙 P.complex) (by rfl)).symm

theorem injective_sequence : injective_sequenceType.{u,v,w} := by
  intro R _ A B₁ B₂ B₃ i p hi he hp L N
  obtain ⟨H⟩ := P103.Ch10.Horseshoe.injective_horseshoe R B₁ B₂ B₃
    i.hom p.hom hi he hp L N
  refine ⟨⟨H⟩, ?_⟩
  intro H
  have hs := P103.Ch10.HorseshoeNaturality.split_exact _ _
    (P103.Ch10.HorseshoeNaturality.split_map (covariantHom A) H.inclusion H.projection
      (P103.Ch10.HorseshoeNaturality.injective_split R B₁ B₂ B₃ i.hom p.hom L N H))
  have hd := fun n => P103.Ch10.HomologySequence.sequence
    (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.inclusion)
    (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.projection) hs n (n + 1) (by rfl)
  choose δ hδ huniq using hd
  exact ⟨δ, hδ, (P103.Ch10.HorseshoeNaturality.cochain_zero_exact _ _ hs).1⟩

theorem connectors_linear : connectors_linearType.{u,v,w} := by
  intro K _ n E F
  constructor
  · intro A₁ A₂ A₃ i p hi he hp L N hL hN H B δ hδ r x
    have h := first_natural K n E F
      A₁ A₂ A₃ A₁ A₂ A₃ i p i p (𝟙 _) (𝟙 _) (𝟙 _)
      hi he hp hi he hp (by simp) (by simp)
      L N L N hL hN hL hN H H B B (scalarMap B r) δ δ hδ hδ
    exact (LinearMap.congr_fun h x).symm
  · intro A P hP B₁ B₂ B₃ i p hi he hp δ hδ r x
    have h := second_natural K n E F
      A A P P hP hP (𝟙 _) B₁ B₂ B₃ B₁ B₂ B₃ i p i p
      (scalarMap B₁ r) (scalarMap B₂ r) (scalarMap B₃ r)
      hi he hp hi he hp (scalarMap_naturality i r).symm (scalarMap_naturality p r).symm
      δ δ hδ hδ
    exact (LinearMap.congr_fun h x).symm

/-- Postcomposition on the vertical resolution gives an actual map of the
unsigned Hom bicomplexes and hence of their signed totals. -/
def homBicomplexPostMap (C : ChainComplex (ModuleCat.{v} R) ℕ)
    {D E : CochainComplex (ModuleCat.{w} R) ℕ} (m : D ⟶ E) :
    homBicomplex C D ⟶ homBicomplex C E where
  f k := ((covariantHom (C.X k)).mapHomologicalComplex (ComplexShape.up ℕ)).map m
  comm' j k _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    rfl

abbrev homTotalPostMap (C : ChainComplex (ModuleCat.{v} R) ℕ)
    {D E : CochainComplex (ModuleCat.{w} R) ℕ} (m : D ⟶ E) :=
  HomologicalComplex₂.total.map (homBicomplexPostMap C m) (ComplexShape.up ℕ)

/-- Direct sums preserve componentwise split short exact sequences. The
splittings are allowed to vary with both indices and need not be complex maps. -/
theorem total_degreewise_split
    {K L M : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (φ : K ⟶ L) (ψ : L ⟶ M)
    (hs : ∀ p q, ∃ h : (φ.f p).f q ≫ (ψ.f p).f q = 0,
      Nonempty (ShortComplex.mk ((φ.f p).f q) ((ψ.f p).f q) h).Splitting) :
    P103.Specs.Ch10.HorseshoeNaturality.DegreewiseSplit
      (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ))
      (HomologicalComplex₂.total.map ψ (ComplexShape.up ℕ)) := by
  classical
  let hc p q := (hs p q).choose
  let sp p q := (hs p q).choose_spec.some
  intro n
  let r : (L.total (ComplexShape.up ℕ)).X n ⟶ (K.total (ComplexShape.up ℕ)).X n :=
    L.totalDesc (fun p q h => (sp p q).r ≫ K.ιTotal (ComplexShape.up ℕ) p q n h)
  let s : (M.total (ComplexShape.up ℕ)).X n ⟶ (L.total (ComplexShape.up ℕ)).X n :=
    M.totalDesc (fun p q h => (sp p q).s ≫ L.ιTotal (ComplexShape.up ℕ) p q n h)
  have hzero : (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n ≫
      (HomologicalComplex₂.total.map ψ (ComplexShape.up ℕ)).f n = 0 := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    simp only [HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ιTotal_map,
      comp_zero]
    rw [← Category.assoc, hc p q, zero_comp]
  refine ⟨hzero, ⟨{ r := r, s := s, f_r := ?_, s_g := ?_, id := ?_ }⟩⟩
  · apply HomologicalComplex₂.total.hom_ext
    intro p q h
    dsimp [r]
    simp only [HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ι_totalDesc,
      Category.comp_id]
    rw [← Category.assoc]
    rw [(sp p q).f_r, Category.id_comp]
  · apply HomologicalComplex₂.total.hom_ext
    intro p q h
    dsimp [s]
    simp only [Category.assoc, HomologicalComplex₂.ι_totalDesc_assoc, HomologicalComplex₂.ιTotal_map,
      Category.comp_id]
    rw [← Category.assoc]
    rw [(sp p q).s_g, Category.id_comp]
  · apply HomologicalComplex₂.total.hom_ext
    intro p q h
    dsimp [r, s]
    simp only [Preadditive.comp_add, Category.comp_id, Category.assoc,
      HomologicalComplex₂.ι_totalDesc_assoc, HomologicalComplex₂.ιTotal_map,
      HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ι_totalDesc,
      ]
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, (sp p q).id, Category.id_comp]

/-- The total sequence is degreewise split, although none of its degreewise
sections needs to commute with the differentials. -/
theorem total_hom_degreewise_exact {A : ModuleCat.{v} R} (P : LeftResolution R A)
    {B₁ B₂ B₃ : ModuleCat.{w} R} {i : B₁ ⟶ B₂} {p : B₂ ⟶ B₃}
    {L : InjectiveResolution R B₁} {N : InjectiveResolution R B₃}
    (H : Horseshoe.InjectiveData i.hom p.hom L N) :
    DegreewiseExact (homTotalPostMap P.complex H.inclusion)
      (homTotalPostMap P.complex H.projection) := by
  apply P103.Ch10.HorseshoeNaturality.split_exact
  apply total_degreewise_split
  intro k q
  obtain ⟨h, ⟨s⟩⟩ := P103.Ch10.HorseshoeNaturality.injective_split
    R B₁ B₂ B₃ i.hom p.hom L N H q
  exact ⟨by change (covariantHom (P.complex.X k)).map (H.inclusion.f q) ≫
      (covariantHom (P.complex.X k)).map (H.projection.f q) = 0
            rw [← Functor.map_comp, h, Functor.map_zero],
    ⟨s.map (covariantHom (P.complex.X k))⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem projective_augmentation_square {A : ModuleCat.{v} R}
    (P : LeftResolution R A) {B B' : ModuleCat.{w} R}
    (I : InjectiveResolution R B) (J : InjectiveResolution R B')
    (g : B ⟶ B') (m : I.complex ⟶ J.complex)
    (hm : CochainLift (ofInjective I) J g.hom m)
    (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
    (α' : homComplex P.complex B' ⟶ homTotal P.complex J.complex)
    (hα : IsProjectiveAugmentation P I α) (hα' : IsProjectiveAugmentation P J α') :
    homPostMap P.complex g.hom ≫ α' = α ≫ homTotalPostMap P.complex m := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hα n, hα' n]
  simp only [homTotalPostMap, Category.assoc, HomologicalComplex₂.ιTotal_map]
  have hpre : (homPostMap P.complex g.hom).f n ≫
      ModuleCat.ofHom (P103.HomTensorExactness.post (P := P.complex.X n) J.η).toIntLinearMap =
      ModuleCat.ofHom (P103.HomTensorExactness.post (P := P.complex.X n) I.η).toIntLinearMap ≫
        ((homBicomplexPostMap P.complex m).f n).f 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change P.complex.X n →ₗ[R] B at h
    apply LinearMap.ext
    intro x
    exact (LinearMap.congr_fun hm (h x)).symm
  rw [← Category.assoc, ← Category.assoc, hpre]

set_option backward.isDefEq.respectTransparency false in
theorem injective_augmentation_square {A : ModuleCat.{v} R}
    (P : LeftResolution R A) {B B' : ModuleCat.{w} R}
    (I : InjectiveResolution R B) (J : InjectiveResolution R B')
    (m : I.complex ⟶ J.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex)
    (β' : injectiveHom A J.complex ⟶ homTotal P.complex J.complex)
    (hβ : IsInjectiveAugmentation P I β) (hβ' : IsInjectiveAugmentation P J β') :
    injectiveHomMap (LinearMap.id : A →ₗ[R] A) m ≫ β' = β ≫ homTotalPostMap P.complex m := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hβ n, hβ' n]
  simp only [homTotalPostMap, Category.assoc, HomologicalComplex₂.ιTotal_map]
  have hpre : (injectiveHomMap (LinearMap.id : A →ₗ[R] A) m).f n ≫
      ModuleCat.ofHom (P103.HomTensorExactness.pre (Q := J.complex.X n) P.ε).toIntLinearMap =
      ModuleCat.ofHom (P103.HomTensorExactness.pre (Q := I.complex.X n) P.ε).toIntLinearMap ≫
        ((homBicomplexPostMap P.complex m).f 0).f n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    rfl
  rw [← Category.assoc, ← Category.assoc, hpre]

/-- The comparisons are supplied by the proved upstream balance theorem. -/
theorem balanced_comparisons : balanced_comparisonsType.{u,v,w} := by
  intro R _ A B P I hP
  obtain ⟨α, β, hα, hβ, hqα, hqβ, he⟩ :=
    P103.Ch11.ExtBalance.balance R A B P I hP
  choose e he using he
  exact ⟨e, fun n => ⟨α, β, hα, hβ, hqα, hqβ, he n⟩⟩

/-- In particular, both ordinary arrows of each horseshoe sequence agree. -/
theorem balance_arrows : balance_arrowsType.{u,v,w} := by
  intro R _ n E A A' B B' P Q hP hQ I J f g m hm e e' he he'
  obtain ⟨α, β, hα, hβ, hqα, _, he⟩ := he
  obtain ⟨α', β', hα', hβ', hqα', _, he'⟩ := he'
  exact P103.Ch11.ExtBalance.balance_natural_extMaps n E ⟨P, hP⟩ ⟨Q, hQ⟩
    I J f g m hm α β α' β' hα hβ hα' hβ' hqα hqα' e e' he he'

/-- The two computations of the coefficient connector agree, using the
short exact sequence of total complexes as the common comparison sequence. -/
theorem balance_connecting : balance_connectingType.{u,v,w} := by
  intro R _ A P hP B₁ B₂ B₃ i p hi he hp L N H n δ ε hδ hε eN eL heN heL
  obtain ⟨αN, βN, haN, hbN, hqaN, hqbN, heN⟩ := heN
  obtain ⟨αL, βL, haL, hbL, hqaL, hqbL, heL⟩ := heL
  obtain ⟨αM, βM, haM, hbM⟩ := P103.Ch11.ExtBalance.augmentation_maps R A B₂ P H.middle
  have hs := total_hom_degreewise_exact P H
  obtain ⟨τ, hτ, _⟩ := P103.Ch10.HomologySequence.sequence
    (homTotalPostMap P.complex H.inclusion) (homTotalPostMap P.complex H.projection)
    hs n (n + 1) (by rfl)
  have hα := (P103.Ch10.HomologySequence.naturality
    (homPostMap P.complex i.hom) (homPostMap P.complex p.hom)
    (homTotalPostMap P.complex H.inclusion) (homTotalPostMap P.complex H.projection)
    αL αM αN
    (projective_augmentation_square P L H.middle i H.inclusion
      H.augmentation_inclusion αL αM haL haM)
    (projective_augmentation_square P H.middle N p H.projection
      H.augmentation_projection αM αN haM haN)
    (second_degreewise_exact P hP i p hi he hp) hs n (n + 1) (by rfl) δ τ hδ hτ.1).2.2.1
  have hsI := P103.Ch10.HorseshoeNaturality.split_exact _ _
    (P103.Ch10.HorseshoeNaturality.split_map (covariantHom A) H.inclusion H.projection
      (P103.Ch10.HorseshoeNaturality.injective_split R B₁ B₂ B₃ i.hom p.hom L N H))
  have hβ := (P103.Ch10.HomologySequence.naturality
    (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.inclusion)
    (injectiveHomMap (LinearMap.id : A →ₗ[R] A) H.projection)
    (homTotalPostMap P.complex H.inclusion) (homTotalPostMap P.complex H.projection)
    βL βM βN
    (injective_augmentation_square P L H.middle H.inclusion βL βM hbL hbM)
    (injective_augmentation_square P H.middle N H.projection βM βN hbM hbN)
    hsI hs n (n + 1) (by rfl) ε τ hε hτ.1).2.2.1
  apply LinearMap.ext
  intro x
  apply (hqaL (n + 1)).1
  calc
    homologyMap αL (n + 1) (eL (ε x)) = homologyMap βL (n + 1) (ε x) :=
      DFunLike.congr_fun heL (ε x)
    _ = τ (homologyMap βN n x) := DFunLike.congr_fun hβ x
    _ = τ (homologyMap αN n (eN x)) :=
      congrArg τ (DFunLike.congr_fun heN x).symm
    _ = homologyMap αL (n + 1) (δ (eN x)) :=
      (DFunLike.congr_fun hα (eN x)).symm

theorem right_sequences : right_sequencesType.{u,v,w} := by
  intro R _
  exact ⟨first_sequence Rᵐᵒᵖ,
    second_sequence Rᵐᵒᵖ,
    first_natural Rᵐᵒᵖ,
    second_natural Rᵐᵒᵖ,
    coefficient_arrows Rᵐᵒᵖ,
    injective_sequence Rᵐᵒᵖ,
    balanced_comparisons Rᵐᵒᵖ,
    balance_arrows Rᵐᵒᵖ,
    balance_connecting Rᵐᵒᵖ⟩

end
end P103.Ch11.ExtExactSequences
