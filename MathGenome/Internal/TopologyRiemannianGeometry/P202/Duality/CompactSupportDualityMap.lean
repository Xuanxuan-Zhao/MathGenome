import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactSupportDualityMap
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.ExcisionMayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CapProducts

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
universe u v
namespace P202.CompactSupport
open P202Specs.CompactSupport P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation P202Specs.CompactOrientation

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

@[simp] theorem ofSupport_transition (p : ℤ) (K L : Support M) (h : K ≤ L)
    (a : supportedCohomology R M p K) :
    ofSupport R M p L (transition R M p K L h a) = ofSupport R M p K a :=
  Module.DirectLimit.of_f

theorem representatives : Expected.representatives.{u,v} := by
  intro R _ M _ p a
  exact Module.DirectLimit.exists_of a

theorem equalityWitness : Expected.equalityWitness.{u,v} := by
  intro R _ M _ p K L a b
  constructor
  · intro h
    let N := K ⊔ L
    have he : ofSupport R M p N (transition R M p K N le_sup_left a) =
        ofSupport R M p N (transition R M p L N le_sup_right b) := by
      simpa using h
    obtain ⟨Q, hNQ, hQ⟩ := Module.DirectLimit.exists_eq_of_of_eq he
    refine ⟨Q, le_sup_left.trans hNQ, le_sup_right.trans hNQ, ?_⟩
    have h₁ := DirectedSystem.map_map' (transition R M p) (show K ≤ N from le_sup_left) hNQ a
    have h₂ := DirectedSystem.map_map' (transition R M p) (show L ≤ N from le_sup_right) hNQ b
    exact h₁.symm.trans (hQ.trans h₂)
  · rintro ⟨N, hKN, hLN, h⟩
    rw [← ofSupport_transition R M p K N hKN a,
      ← ofSupport_transition R M p L N hLN b, h]

@[simp] theorem descend_ofSupport (p : ℤ) {V : Type*} [AddCommGroup V] [Module R V]
    (f : ∀ K : Support M, supportedCohomology R M p K →ₗ[R] V)
    (hf : ∀ K L h a, f L (transition R M p K L h a) = f K a)
    (K : Support M) (a : supportedCohomology R M p K) :
    descend R M p f hf (ofSupport R M p K a) = f K a := by
  simp only [descend, ofSupport, Module.DirectLimit.lift_of]

@[ext] theorem hom_ext (p : ℤ) {V : Type*} [AddCommGroup V] [Module R V]
    {f g : CompactCohomology R M p →ₗ[R] V}
    (h : ∀ K, f.comp (ofSupport R M p K) = g.comp (ofSupport R M p K)) : f = g :=
  Module.DirectLimit.hom_ext h

theorem negative : Expected.negative.{u,v} := by
  intro R _ M _ p hp
  apply subsingleton_of_forall_eq 0
  intro a
  obtain ⟨K, b, rfl⟩ := representatives R M p a
  haveI := ModuleCat.subsingleton_of_isZero
    ((P202.CohomologyPairs.negative R R).2 (supportedPair M K) p hp).2
  rw [Subsingleton.elim b 0, map_zero]

/-- Identification of the negative-degree source with the canonical zero module.
No assertion about the target of a duality map is needed for this equivalence. -/
def negativeEquiv (p : ℤ) (hp : p < 0) : CompactCohomology R M p ≃ₗ[R] PUnit := by
  haveI := negative R M p hp
  exact LinearEquiv.ofSubsingleton _ _

/-- Relative cochains embed in ordinary cochains because the quotient
projection on chains is surjective, in every integer degree. -/
lemma cochainInclusion_injective (K : Support M) (p : ℤ) :
    Function.Injective ((cochainInclusion R M K).f p) := by
  intro a b h
  change (ordinary R R (supportedPair M K)).X p →ₗ[R] R at a b
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := P202.CapProducts.projection_surjective R (supportedPair M K) p z
  change (a.comp ((projection (ordinaryFunctor R R) (supportedPair M K)).f p).hom) =
    (b.comp ((projection (ordinaryFunctor R R) (supportedPair M K)).f p).hom) at h
  exact LinearMap.congr_fun h c

lemma intoUnion_injective (K : Support M) (p : ℤ) :
    Function.Injective ((intoUnion R M K).f p) := by
  intro a b h
  exact cochainInclusion_injective R M K p (congrArg Subtype.val h)

/-- A cochain cycle can be lifted through an embedding once its underlying
cochain has been lifted. -/
lemma liftCocycle {C D : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (f : C ⟶ D) (p : ℤ) (hf : Function.Injective (f.f (p+1)))
    (z : D.cycles p) (x : C.X p) (hx : f.f p x = D.iCycles p z) :
    ∃ y : C.cycles p, C.iCycles p y = x ∧ cyclesMap f p y = z := by
  have hclosed : C.d p (p+1) x = 0 := by
    apply hf
    rw [map_zero]
    have H := congrArg (fun t => t x) (f.comm p (p+1))
    simp only [ModuleCat.comp_apply] at H
    rw [← H, hx]
    exact congrArg (fun t => t z) (D.iCycles_d p (p+1))
  have hker : (C.sc p).g x = 0 := by
    change C.d p ((ComplexShape.up ℤ).next p) x = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel p (p+1) by rfl)]
    exact hclosed
  let y := (C.sc p).moduleCatCyclesIso.inv ⟨x, hker⟩
  have hy : C.iCycles p y = x :=
    congrArg (fun t => t ⟨x, hker⟩) (C.sc p).moduleCatCyclesIso_inv_iCycles
  refine ⟨y, hy, ?_⟩
  apply (ModuleCat.mono_iff_injective (D.iCycles p)).mp inferInstance
  have H := congrArg (fun t => t y) (cyclesMap_i f p)
  simp only [ModuleCat.comp_apply] at H
  rw [H, hy, hx]

lemma cochain_class_zero_iff (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (p : ℤ) (z : C.cycles p) :
    C.homologyπ p z = 0 ↔ ∃ x : C.X (p-1), C.d (p-1) p x = C.iCycles p z := by
  change (C.sc p).homologyπ z = 0 ↔ _
  rw [P202.CupProduct.shortComplex_homologyπ_eq_zero_iff]
  change (∃ x : C.X ((ComplexShape.up ℤ).prev p), C.d _ p x = C.iCycles p z) ↔ _
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (p-1) p by
    change p-1+1=p; omega)]

@[simp] lemma unionComparison_ofSupport (p : ℤ) (K : Support M)
    (a : supportedCohomology R M p K) :
    unionComparison R M p (ofSupport R M p K a) = homologyMap (intoUnion R M K) p a := by
  simp only [unionComparison, descend, ofSupport, Module.DirectLimit.lift_of]

lemma intoUnion_enlarge (p : ℤ) {K L : Support M} (h : K ≤ L)
    (a : (supportedCochains R M K).X p) :
    (intoUnion R M L).f p ((cochainTransition R M h).f p a) =
      (intoUnion R M K).f p a :=
  congrArg (fun f => f.f p a) (intoUnion_transition R M h)

lemma unionComparison_surjective (p : ℤ) : Function.Surjective (unionComparison R M p) := by
  intro a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((unionComplex R M).homologyπ p)).mp
    inferInstance a
  obtain ⟨K, b, hb⟩ := ((unionComplex R M).iCycles p z).property
  have hb' : (intoUnion R M K).f p b = (unionComplex R M).iCycles p z := Subtype.ext hb
  obtain ⟨y, _, hy⟩ := liftCocycle R (intoUnion R M K) p
    (intoUnion_injective R M K (p+1)) z b hb'
  refine ⟨ofSupport R M p K ((supportedCochains R M K).homologyπ p y), ?_⟩
  rw [unionComparison_ofSupport]
  have H := congrArg (fun t => t y) (homologyπ_naturality (intoUnion R M K) p)
  simp only [ModuleCat.comp_apply] at H
  rw [H, hy]

lemma unionComparison_injective (p : ℤ) : Function.Injective (unionComparison R M p) := by
  apply (unionComparison R M p).ker_eq_bot.mp
  apply le_antisymm
  · intro a ha
    change unionComparison R M p a = 0 at ha
    obtain ⟨K, b, rfl⟩ := representatives R M p a
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((supportedCochains R M K).homologyπ p)).mp inferInstance b
    rw [unionComparison_ofSupport] at ha
    have H := congrArg (fun t => t z) (homologyπ_naturality (intoUnion R M K) p)
    simp only [ModuleCat.comp_apply] at H
    rw [H] at ha
    obtain ⟨x, hx⟩ := (cochain_class_zero_iff R (unionComplex R M) p _).mp ha
    obtain ⟨L, y, hy⟩ := x.property
    let N := K ⊔ L
    let zN := cyclesMap (cochainTransition R M (show K ≤ N from le_sup_left)) p z
    have hzN : (supportedCochains R M N).homologyπ p zN = 0 := by
      apply (cochain_class_zero_iff R (supportedCochains R M N) p zN).mpr
      refine ⟨(cochainTransition R M (show L ≤ N from le_sup_right)).f (p-1) y, ?_⟩
      apply intoUnion_injective R M N p
      have hf := congrArg (fun t => t
        ((cochainTransition R M (show L ≤ N from le_sup_right)).f (p-1) y))
        ((intoUnion R M N).comm (p-1) p)
      simp only [ModuleCat.comp_apply] at hf
      rw [← hf, intoUnion_enlarge]
      have hy' : (intoUnion R M L).f (p-1) y = x := Subtype.ext hy
      rw [hy', hx]
      have hz := congrArg (fun t => t z)
        (cyclesMap_i (cochainTransition R M (show K ≤ N from le_sup_left)) p)
      simp only [ModuleCat.comp_apply] at hz
      have hz' := congrArg (fun t => t z) (cyclesMap_i (intoUnion R M K) p)
      simp only [ModuleCat.comp_apply] at hz'
      change _ = (intoUnion R M N).f p
        ((supportedCochains R M N).iCycles p zN)
      rw [show (supportedCochains R M N).iCycles p zN = _ from hz,
        intoUnion_enlarge, hz']
    have hn := congrArg (fun t => t z)
      (homologyπ_naturality (cochainTransition R M (show K ≤ N from le_sup_left)) p)
    simp only [ModuleCat.comp_apply] at hn
    change transition R M p K N le_sup_left
      ((supportedCochains R M K).homologyπ p z) = _ at hn
    change ofSupport R M p K ((supportedCochains R M K).homologyπ p z) = 0
    rw [← ofSupport_transition R M p K N le_sup_left, hn, hzN, map_zero]
  · exact bot_le

theorem unionEquivalence : Expected.unionEquivalence.{u,v} := by
  intro R _ M _ p
  exact ⟨unionComparison_injective R M p, unionComparison_surjective R M p⟩

/-- Cohomology commutes with this directed union; this is the canonical
comparison isomorphism, not an arbitrary isomorphism of modules. -/
def unionEquiv (p : ℤ) : CompactCohomology R M p ≃ₗ[R] (unionComplex R M).homology p :=
  LinearEquiv.ofBijective (unionComparison R M p) (unionEquivalence R M p)

/-- Normalize the ambient space in the upstream differential cap system. -/
abbrev supportCapSystem (K : Support M) :
    P202.CapProducts.CapSystem (supportedCochains R M K)
      (ordinary R R (supportedPair M K)) (ordinaryComplex R R (TopCat.of M)) :=
  P202.CapProducts.relativeSystem R (supportedPair M K)

/-- The actual relative chain cap is compatible with restriction of homological
support and extension of cohomological support. -/
lemma chainCap_transition (p : ℕ) (q : ℤ) {K L : Support M} (h : K ≤ L)
    (a : (supportedCochains R M K).X (p : ℤ))
    (z : (ordinary R R (supportedPair M L)).X q) :
    P202.CapProducts.relativeChainCap R (supportedPair M K) p q a
      ((relativeMap (ordinaryFunctor R R) (supportPairMap M h)).f q z) =
    P202.CapProducts.relativeChainCap R (supportedPair M L) p q
      ((cochainTransition R M h).f (p : ℤ) a) z := by
  obtain ⟨c, rfl⟩ := P202.CapProducts.projection_surjective R (supportedPair M L) q z
  have H := projection_map (ordinaryFunctor R R) (supportPairMap M h)
  change projection (ordinaryFunctor R R) (supportedPair M L) ≫
    relativeMap (ordinaryFunctor R R) (supportPairMap M h) =
    (ordinaryFunctor R R).map (𝟙 (TopCat.of M)) ≫
      projection (ordinaryFunctor R R) (supportedPair M K) at H
  have hid : (ordinaryFunctor R R).map (𝟙 (TopCat.of M)) =
      𝟙 (ordinaryComplex R R (TopCat.of M)) := (ordinaryFunctor R R).map_id _
  rw [hid] at H
  have H' : (relativeMap (ordinaryFunctor R R) (supportPairMap M h)).f q
      ((projection (ordinaryFunctor R R) (supportedPair M L)).f q c) =
    (projection (ordinaryFunctor R R) (supportedPair M K)).f q c := by
    exact congrArg (fun f => f.f q c) (H.trans (Category.id_comp _))
  rw [H', P202.CapProducts.relativeChainCap_lift,
    P202.CapProducts.relativeChainCap_lift]
  have ha := congrArg (fun f => f.f (p : ℤ) a) (cochainInclusion_transition R M h)
  change (cochainInclusion R M L).f (p : ℤ)
    ((cochainTransition R M h).f (p : ℤ) a) = (cochainInclusion R M K).f (p : ℤ) a at ha
  change P202.CapProducts.cap R (TopCat.of M) p q
    (ordinaryCochainsEquiv R R (TopCat.of M) p ((cochainInclusion R M K).f (p : ℤ) a)) c =
    P202.CapProducts.cap R (TopCat.of M) p q
      (ordinaryCochainsEquiv R R (TopCat.of M) p
        ((cochainInclusion R M L).f (p : ℤ) ((cochainTransition R M h).f (p : ℤ) a))) c
  rw [ha]

lemma homologyCap_transition (p : ℕ) (q : ℤ) {K L : Support M} (h : K ≤ L)
    (a : supportedCohomology R M (p : ℤ) K)
    (z : relativeHomology R R (supportedPair M L) q) :
    (supportCapSystem R M K).homologyOp p q a
      (((relativeHomologyFunctor R R q).map (supportPairMap M h)) z) =
    (supportCapSystem R M L).homologyOp p q
      (transition R M (p : ℤ) K L h a) z := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((supportedCochains R M K).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinary R R (supportedPair M L)).homologyπ q)).mp inferInstance z
  have ha := congrArg (fun f => f a) (homologyπ_naturality (cochainTransition R M h) (p : ℤ))
  have hz := congrArg (fun f => f z)
    (homologyπ_naturality (relativeMap (ordinaryFunctor R R) (supportPairMap M h)) q)
  simp only [ModuleCat.comp_apply] at ha hz
  change homologyMap (cochainTransition R M h) (p : ℤ)
    ((supportedCochains R M K).homologyπ (p : ℤ) a) = _ at ha
  change ((relativeHomologyFunctor R R q).map (supportPairMap M h))
    ((ordinary R R (supportedPair M L)).homologyπ q z) = _ at hz
  change _ = (supportCapSystem R M L).homologyOp p q
    (homologyMap (cochainTransition R M h) (p : ℤ)
      ((supportedCochains R M K).homologyπ (p : ℤ) a)) _
  rw [ha, hz, P202.CapProducts.CapSystem.homologyOp_rep,
    P202.CapProducts.CapSystem.homologyOp_rep]
  congr 1
  apply P202.CapProducts.cycles_injective
  rw [P202.CapProducts.CapSystem.cycleOp_i, P202.CapProducts.CapSystem.cycleOp_i]
  change P202.CapProducts.relativeChainCap R (supportedPair M K) p q
      ((supportedCochains R M K).iCycles (p : ℤ) a)
      ((ordinary R R (supportedPair M K)).iCycles q
        (cyclesMap (relativeMap (ordinaryFunctor R R) (supportPairMap M h)) q z)) =
    P202.CapProducts.relativeChainCap R (supportedPair M L) p q
      ((supportedCochains R M L).iCycles (p : ℤ)
        (cyclesMap (cochainTransition R M h) (p : ℤ) a))
      ((ordinary R R (supportedPair M L)).iCycles q z)
  have ha' := congrArg (fun f => f a) (cyclesMap_i (cochainTransition R M h) (p : ℤ))
  have hz' := congrArg (fun f => f z)
    (cyclesMap_i (relativeMap (ordinaryFunctor R R) (supportPairMap M h)) q)
  simp only [ModuleCat.comp_apply] at ha' hz'
  rw [ha', hz']
  exact chainCap_transition R M p q h _ _

/-- The existing ordinary singular map, with normalized domain and codomain. -/
abbrev ordinaryMap {X Y : TopCat.{v}} (f : X ⟶ Y) :
    ordinaryComplex R R X ⟶ ordinaryComplex R R Y := (ordinaryFunctor R R).map f

/-- Naturality of the relative cochain represented as an ambient cochain. -/
lemma relativeValue_natural {P Q : Pair.{v}} (f : P ⟶ Q) (p : ℕ)
    (a : (relativeCochains R R Q).X (p : ℤ)) :
    P202.CapProducts.relativeValue R P p
      (((relativeCochainFunctor R R).map f.op).f (p : ℤ) a) =
    P202Specs.CupProduct.pullback R f.map p (P202.CapProducts.relativeValue R Q p a) := by
  have H := congrArg (fun t => t.f (p : ℤ) a) (cochainSequenceMap R R f).comm₁₂
  change (relativeToAbsolute R R P).f (p : ℤ)
    (((relativeCochainFunctor R R).map f.op).f (p : ℤ) a) =
    (((ordinaryCochainFunctor R R).map f.map.op).f (p : ℤ)
      ((relativeToAbsolute R R Q).f (p : ℤ) a)) at H
  change ordinaryCochainsEquiv R R P.space p _ = _
  rw [H, P202.CupProduct.ordinaryCochainsEquiv_pullback]
  rfl

/-- Naturality at the quotient chain level, without assuming naturality of a
chosen representative or of a chosen pair-product implementation. -/
lemma relativeChainCap_natural {P Q : Pair.{v}} (f : P ⟶ Q) (p : ℕ) (q : ℤ)
    (a : (relativeCochains R R Q).X (p : ℤ)) (z : (ordinary R R P).X q) :
    ((ordinaryFunctor R R).map f.map).f (q-p)
      (P202.CapProducts.relativeChainCap R P p q
        (((relativeCochainFunctor R R).map f.op).f (p : ℤ) a) z) =
    P202.CapProducts.relativeChainCap R Q p q a
      ((relativeMap (ordinaryFunctor R R) f).f q z) := by
  obtain ⟨c, rfl⟩ := P202.CapProducts.projection_surjective R P q z
  have H := congrArg (fun t => t.f q c) (projection_map (ordinaryFunctor R R) f)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at H
  rw [P202.CapProducts.relativeChainCap_lift, H,
    P202.CapProducts.relativeChainCap_lift, relativeValue_natural]
  exact P202.CapProducts.ordinaryNatural R f.map p q _ c

/-- Naturality on the actual relative cohomology and homology groups. -/
lemma homologyCap_natural {P Q : Pair.{v}} (f : P ⟶ Q) (p : ℕ) (q : ℤ)
    (a : relativeCohomology R R Q (p : ℤ)) (z : relativeHomology R R P q) :
    (homologyMap (ordinaryMap R f.map) (q-p))
      ((P202.CapProducts.relativeSystem R P).homologyOp p q
        (((relativeCohomologyFunctor R R (p : ℤ)).map f.op) a) z) =
    (P202.CapProducts.relativeSystem R Q).homologyOp p q a
      (((relativeHomologyFunctor R R q).map f) z) := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relativeCochains R R Q).homologyπ (p : ℤ))).mp inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((ordinary R R P).homologyπ q)).mp inferInstance z
  have ha := congrArg (fun t => t a)
    (homologyπ_naturality ((relativeCochainFunctor R R).map f.op) (p : ℤ))
  have hz := congrArg (fun t => t z)
    (homologyπ_naturality (relativeMap (ordinaryFunctor R R) f) q)
  simp only [ModuleCat.comp_apply] at ha hz
  change (((relativeCohomologyFunctor R R (p : ℤ)).map f.op)
    ((relativeCochains R R Q).homologyπ (p : ℤ) a)) = _ at ha
  change (((relativeHomologyFunctor R R q).map f)
    ((ordinary R R P).homologyπ q z)) = _ at hz
  rw [ha, hz, P202.CapProducts.CapSystem.homologyOp_rep,
    P202.CapProducts.CapSystem.homologyOp_rep]
  have ht := congrArg (fun t => t
    ((P202.CapProducts.relativeSystem R P).cycleOp p q
      (cyclesMap ((relativeCochainFunctor R R).map f.op) (p : ℤ) a) z))
    (homologyπ_naturality (ordinaryMap R f.map) (q-p))
  simp only [ModuleCat.comp_apply] at ht
  change (homologyMap (ordinaryMap R f.map) (q-p)) _ = _ at ht
  rw [ht]
  congr 1
  apply (ModuleCat.mono_iff_injective ((ordinaryComplex R R Q.space).iCycles (q-p))).mp inferInstance
  have hi := congrArg (fun t => t
    ((P202.CapProducts.relativeSystem R P).cycleOp p q
      (cyclesMap ((relativeCochainFunctor R R).map f.op) (p : ℤ) a) z))
    (cyclesMap_i (ordinaryMap R f.map) (q-p))
  simp only [ModuleCat.comp_apply] at hi
  rw [hi, P202.CapProducts.CapSystem.cycleOp_i, P202.CapProducts.CapSystem.cycleOp_i]
  have ha' := congrArg (fun t => t a)
    (cyclesMap_i ((relativeCochainFunctor R R).map f.op) (p : ℤ))
  have hz' := congrArg (fun t => t z) (cyclesMap_i (relativeMap (ordinaryFunctor R R) f) q)
  simp only [ModuleCat.comp_apply] at ha' hz'
  change (ordinaryMap R f.map).f (q-p)
    (P202.CapProducts.relativeChainCap R P p q _ _) =
      P202.CapProducts.relativeChainCap R Q p q _ _
  rw [ha', hz']
  exact relativeChainCap_natural R f p q _ _

/-- The unique top-dimensional class with the prescribed local orientation. -/
def fundamentalClass {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (K : Support M) : SupportedGroup R M K n :=
  (P202.CompactOrientation.compactClass R n M A o K K.isCompact).exists.choose

lemma fundamentalClass_values {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (K : Support M) : HasLocalValues R o.val K (fundamentalClass R M A o K) :=
  (P202.CompactOrientation.compactClass R n M A o K K.isCompact).exists.choose_spec

lemma fundamentalClass_compatible {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    {K L : Support M} (h : K ≤ L) :
    ((relativeHomologyFunctor R R (n : ℤ)).map (supportPairMap M h))
      (fundamentalClass R M A o L) = fundamentalClass R M A o K :=
  P202.CompactOrientation.compatibility R n M A o K L K.isCompact L.isCompact h
    _ _ (fundamentalClass_values R M A o K) (fundamentalClass_values R M A o L)

/-- Cap with the fundamental class near one compact support. -/
def supportedDuality {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (p : ℕ) (K : Support M) :
    supportedCohomology R M (p : ℤ) K →ₗ[R] homology R R (TopCat.of M) ((n : ℤ)-p) :=
  (LinearMap.applyₗ' R (fundamentalClass R M A o K)).comp
    ((supportCapSystem R M K).homologyOp p (n : ℤ))

lemma supportedDuality_compatible {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (p : ℕ) (K L : Support M) (h : K ≤ L)
    (a : supportedCohomology R M (p : ℤ) K) :
    supportedDuality R M A o p L (transition R M (p : ℤ) K L h a) =
      supportedDuality R M A o p K a := by
  change (supportCapSystem R M L).homologyOp p (n : ℤ)
    (transition R M (p : ℤ) K L h a) (fundamentalClass R M A o L) = _
  rw [← homologyCap_transition, fundamentalClass_compatible]
  rfl

/-- The compact-support duality map on nonnegative cohomological degrees. -/
def duality {n : ℕ} (A : Manifold n M) (o : Orientation R A) (p : ℕ) :
    CompactCohomology R M (p : ℤ) →ₗ[R] homology R R (TopCat.of M) ((n : ℤ)-p) :=
  descend R M (p : ℤ) (supportedDuality R M A o p)
    (supportedDuality_compatible R M A o p)

@[simp] theorem duality_ofSupport {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (p : ℕ) (K : Support M) (a : supportedCohomology R M (p : ℤ) K) :
    duality R M A o p (ofSupport R M (p : ℤ) K a) = supportedDuality R M A o p K a :=
  descend_ofSupport R M (p : ℤ) _ _ K a

/-- Extend D to negative cohomological degrees by the zero map. The target
remains the actual ordinary homology in degree n-p. -/
def dualityInt {n : ℕ} (A : Manifold n M) (o : Orientation R A) (p : ℤ) :
    CompactCohomology R M p →ₗ[R] homology R R (TopCat.of M) ((n : ℤ)-p) := by
  by_cases hp : 0 ≤ p
  · exact (show p.toNat = p from Int.toNat_of_nonneg hp) ▸ duality R M A o p.toNat
  · exact 0

@[simp] lemma dualityInt_negative {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (p : ℤ) (hp : p < 0) : dualityInt R M A o p = 0 := by
  simp [dualityInt, not_le.mpr hp]

@[simp] lemma dualityInt_nat {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (p : ℕ) : dualityInt R M A o (p : ℤ) = duality R M A o p := by
  simp [dualityInt]

lemma duality_zero_above {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (p : ℕ) (hp : n < p) : duality R M A o p = 0 := by
  haveI := ModuleCat.subsingleton_of_isZero
    (P202.SingularChains.ordinary_negative_homology R R (TopCat.of M) ((n : ℤ)-p) (by omega))
  exact Subsingleton.elim _ _

/-- The local pair near K is the excised ambient pair; the extra isomorphism
only removes the double-complement representation of the open subspace. -/
lemma openPairInclusion_factor (U : Set M) (hU : IsOpen U) (K : Support U)
    (hK : IsClosed (ambientSupport M U K : Set M)) :
    ∃ e : supportedPair U K ≅
      (P202.LocalOrientation.openSupportExcisionData U hU (ambientSupport M U K) hK
        (by rintro x ⟨y, _, rfl⟩; exact y.property)).excised,
      (openPairInclusion M U K) = e.hom ≫
        (P202.LocalOrientation.openSupportExcisionData U hU (ambientSupport M U K) hK
          (by rintro x ⟨y, _, rfl⟩; exact y.property)).inclusion := by
  let e₁ := P202.LocalOrientation.supportedPairIsoOfHomeomorph (Homeomorph.refl U)
    (K : Set U) (Subtype.val ⁻¹' (ambientSupport M U K : Set M))
    (fun x => by
      change x ∈ K ↔ x.val ∈ Subtype.val '' (K : Set U)
      exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, he⟩ => Subtype.val_injective he ▸ hy⟩)
  let e₂ := P202.LocalOrientation.openSupportExcisionIso U hU (ambientSupport M U K)
    hK (by rintro x ⟨y, _, rfl⟩; exact y.property)
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  apply PairMap.ext
  rfl

theorem openExcision : Expected.openExcision.{u,v} := by
  intro R _ M _ _ U hU K p
  obtain ⟨e, he⟩ := openPairInclusion_factor M U hU K (ambientSupport M U K).isCompact.isClosed
  let D := P202.LocalOrientation.openSupportExcisionData U hU (ambientSupport M U K)
    (ambientSupport M U K).isCompact.isClosed (by rintro x ⟨y, _, rfl⟩; exact y.property)
  haveI := P202.CohomologyExcisionMV.excision R R D p
  change IsIso ((relativeCohomologyFunctor R R p).map (openPairInclusion M U K).op)
  rw [he, op_comp, CategoryTheory.Functor.map_comp]
  infer_instance

section OpenExtension
variable [T2Space M] (U : Set M) (hU : IsOpen U)

/-- Extension by excision for a single compact support. -/
def extendAt (K : Support U) (p : ℤ) :
    supportedCohomology R U p K →ₗ[R]
      supportedCohomology R M p (ambientSupport M U K) := by
  haveI := openExcision R M U hU K p
  exact (asIso (openPullback R M U K p)).inv.hom

@[simp] lemma openPullback_extendAt (K : Support U) (p : ℤ)
    (a : supportedCohomology R U p K) :
    openPullback R M U K p (extendAt R M U hU K p a) = a := by
  haveI := openExcision R M U hU K p
  exact congrArg (fun f => f a) (asIso (openPullback R M U K p)).inv_hom_id

lemma extendAt_compatible (p : ℤ) {K L : Support U} (h : K ≤ L)
    (a : supportedCohomology R U p K) :
    extendAt R M U hU L p (transition R U p K L h a) =
      transition R M p (ambientSupport M U K) (ambientSupport M U L)
        (ambientSupport_mono M U h) (extendAt R M U hU K p a) := by
  haveI := openExcision R M U hU L p
  apply (asIso (openPullback R M U L p)).toLinearEquiv.injective
  change openPullback R M U L p _ = openPullback R M U L p _
  rw [openPullback_extendAt]
  have hs : openPairInclusion M U L ≫ supportPairMap M (ambientSupport_mono M U h) =
      supportPairMap U h ≫ openPairInclusion M U K := by
    apply PairMap.ext; rfl
  have H := congrArg ((relativeCohomologyFunctor R R p).map) (congrArg Quiver.Hom.op hs)
  rw [op_comp, op_comp, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at H
  have H' := congrArg (fun f => f (extendAt R M U hU K p a)) H
  change transition R U p K L h a = _
  change _ = transition R U p K L h
    (openPullback R M U K p (extendAt R M U hU K p a)) at H'
  rw [openPullback_extendAt] at H'
  exact H'.symm

/-- Covariant extension of compact supports along an open inclusion. -/
def extendOpen (p : ℤ) : CompactCohomology R U p →ₗ[R] CompactCohomology R M p :=
  descend R U p
    (fun K => (ofSupport R M p (ambientSupport M U K)).comp (extendAt R M U hU K p))
    (by
      intro K L h a
      simp only [LinearMap.comp_apply, extendAt_compatible, ofSupport_transition])

@[simp] lemma extendOpen_ofSupport (p : ℤ) (K : Support U)
    (a : supportedCohomology R U p K) :
    extendOpen R M U hU p (ofSupport R U p K a) =
      ofSupport R M p (ambientSupport M U K) (extendAt R M U hU K p a) := by
  simp only [extendOpen, descend_ofSupport, LinearMap.comp_apply]

end OpenExtension

/-- Excision takes the compact fundamental class of an open submanifold
to the ambient compact fundamental class, since their point values agree. -/
lemma fundamentalClass_open {n : ℕ} (A : Manifold n M) (oM : Orientation R A)
    (U : Set M) (AU : Manifold n U) (oU : Orientation R AU)
    (ho : OpenOrientationCompatible R M oM.val oU.val) (K : Support U) :
    ((relativeHomologyFunctor R R (n : ℤ)).map (openPairInclusion M U K))
      (fundamentalClass R U AU oU K) =
        fundamentalClass R M A oM (ambientSupport M U K) := by
  apply P202.CompactOrientation.hasLocalValues_unique R
    (P202.CompactOrientation.localDetection R n M A (ambientSupport M U K)
      (ambientSupport M U K).isCompact) _ (fundamentalClass_values R M A oM _)
  rintro x hx
  change x ∈ Subtype.val '' (K : Set U) at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hs : openPairInclusion M U K ≫ pointMap (show y.val ∈ ambientSupport M U K from
      ⟨y, hy, rfl⟩) = pointMap hy ≫ P202Specs.LocalOrientation.openLocalInclusion U y := by
    apply PairMap.ext; rfl
  have H := congrArg (fun f => f (fundamentalClass R U AU oU K))
    (congrArg ((relativeHomologyFunctor R R (n : ℤ)).map) hs)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at H
  change restrictPoint R _ n
    (((relativeHomologyFunctor R R (n : ℤ)).map (openPairInclusion M U K))
      (fundamentalClass R U AU oU K)) =
    ((relativeHomologyFunctor R R (n : ℤ)).map (P202Specs.LocalOrientation.openLocalInclusion U y))
      (restrictPoint R hy n (fundamentalClass R U AU oU K)) at H
  rw [H, fundamentalClass_values R U AU oU K y hy]
  exact ho y

/-- The finite-chain homology square for extension along an oriented open inclusion. -/
theorem duality_open {n : ℕ} (A : Manifold n M) (oM : Orientation R A)
    (U : Set M) (hU : IsOpen U) (AU : Manifold n U) (oU : Orientation R AU)
    (ho : OpenOrientationCompatible R M oM.val oU.val) (p : ℕ)
    (a : CompactCohomology R U (p : ℤ)) :
    letI : T2Space M := A.hausdorff
    homologyMap (ordinaryMap R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of U ⟶ TopCat.of M)) ((n : ℤ)-p) (duality R U AU oU p a) =
    duality R M A oM p (extendOpen R M U hU (p : ℤ) a) := by
  letI : T2Space M := A.hausdorff
  obtain ⟨K, a, rfl⟩ := representatives R U (p : ℤ) a
  rw [extendOpen_ofSupport, duality_ofSupport, duality_ofSupport]
  let b := extendAt R M U hU K (p : ℤ) a
  have hb : ((relativeCohomologyFunctor R R (p : ℤ)).map (openPairInclusion M U K).op) b = a :=
    openPullback_extendAt R M U hU K (p : ℤ) a
  change homologyMap (ordinaryMap R (openPairInclusion M U K).map) ((n : ℤ)-p)
    ((P202.CapProducts.relativeSystem R (supportedPair U K)).homologyOp p (n : ℤ) a
      (fundamentalClass R U AU oU K)) =
    (P202.CapProducts.relativeSystem R (supportedPair M (ambientSupport M U K))).homologyOp
      p (n : ℤ) b (fundamentalClass R M A oM (ambientSupport M U K))
  rw [← hb, homologyCap_natural, fundamentalClass_open R M A oM U AU oU ho]

/-- All integer cohomological degrees, including the canonical zero source/map
when the cohomological degree is negative. No target vanishing is used there. -/
theorem dualityInt_open {n : ℕ} (A : Manifold n M) (oM : Orientation R A)
    (U : Set M) (hU : IsOpen U) (AU : Manifold n U) (oU : Orientation R AU)
    (ho : OpenOrientationCompatible R M oM.val oU.val) (p : ℤ)
    (a : CompactCohomology R U p) :
    letI : T2Space M := A.hausdorff
    homologyMap (ordinaryMap R (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of U ⟶ TopCat.of M)) ((n : ℤ)-p) (dualityInt R U AU oU p a) =
    dualityInt R M A oM p (extendOpen R M U hU p a) := by
  letI : T2Space M := A.hausdorff
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [dualityInt_nat, dualityInt_nat]
    exact duality_open R M A oM U hU AU oU ho p a
  · rw [dualityInt_negative R U AU oU p (by omega),
      dualityInt_negative R M A oM p (by omega), LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply]

/-- The representative formula for every cocycle and every lift of every
relative cycle having the prescribed local fundamental values. -/
theorem duality_represents {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (p : ℕ) (K : Support M)
    (a : (supportedCochains R M K).cycles (p : ℤ))
    (z : (ordinary R R (supportedPair M K)).cycles (n : ℤ))
    (c : (ordinaryComplex R R (TopCat.of M)).X (n : ℤ))
    (hc : (projection (ordinaryFunctor R R) (supportedPair M K)).f (n : ℤ) c =
      (ordinary R R (supportedPair M K)).iCycles (n : ℤ) z)
    (hz : HasLocalValues R o.val K ((ordinary R R (supportedPair M K)).homologyπ (n : ℤ) z)) :
    ∃ v : (ordinaryComplex R R (TopCat.of M)).cycles ((n : ℤ)-p),
      (ordinaryComplex R R (TopCat.of M)).iCycles ((n : ℤ)-p) v =
        P202Specs.CapProducts.cap R (TopCat.of M) p (n : ℤ)
          (ordinaryCochainsEquiv R R (TopCat.of M) p
            ((cochainInclusion R M K).f (p : ℤ)
              ((supportedCochains R M K).iCycles (p : ℤ) a))) c ∧
      dualityInt R M A o (p : ℤ)
        (ofSupport R M (p : ℤ) K ((supportedCochains R M K).homologyπ (p : ℤ) a)) =
        (ordinaryComplex R R (TopCat.of M)).homologyπ ((n : ℤ)-p) v := by
  obtain ⟨v, hv, hclass⟩ := (P202.CapProducts.pairProductsData R).relative_represents
    (supportedPair M K) p (n : ℤ) a z c hc
  refine ⟨v, hv, ?_⟩
  rw [dualityInt_nat, duality_ofSupport]
  have hμ : (ordinary R R (supportedPair M K)).homologyπ (n : ℤ) z =
      fundamentalClass R M A o K :=
    P202.CompactOrientation.hasLocalValues_unique R
      (P202.CompactOrientation.localDetection R n M A K K.isCompact) hz
      (fundamentalClass_values R M A o K)
  change (supportCapSystem R M K).homologyOp p (n : ℤ)
    ((supportedCochains R M K).homologyπ (p : ℤ) a) (fundamentalClass R M A o K) = _
  rw [← hμ]
  simp only [P202.CapProducts.pairProductsData, TensorProduct.lift.tmul] at hclass
  exact hclass

/-- All required constructions with their independent representative laws. -/
def dualityData : DualityData.{u,v} R where
  D n M _ A o p := dualityInt R M A o p
  extend M _ _ U hU p := extendOpen R M U hU p
  represents n M _ A o p K a z c hc hz := duality_represents R M A o p K a z c hc hz
  extension_represents := by
    intro M _ _ U hU p K b
    rw [extendOpen_ofSupport]
    haveI := openExcision R M U hU K p
    have H := congrArg (fun f => f b) (asIso (openPullback R M U K p)).hom_inv_id
    change extendAt R M U hU K p (openPullback R M U K p b) = b at H
    rw [H]
  negative n M _ A o p hp := dualityInt_negative R M A o p hp
  above := by
    intro n M _ A o p hp
    rw [dualityInt_nat]
    exact duality_zero_above R M A o p hp
  naturality := by
    intro n M _ A oM U hU AU oU ho p a
    exact dualityInt_open R M A oM U hU AU oU ho p a

theorem construction : Expected.construction.{u,v} := fun R _ => ⟨dualityData R⟩

abbrev compactCohomology := @P202Specs.CompactSupport.CompactCohomology

end P202.CompactSupport
