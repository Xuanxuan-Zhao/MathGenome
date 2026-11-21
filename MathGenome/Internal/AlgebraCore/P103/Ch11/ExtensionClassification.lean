import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtensionClassification
import MathGenome.Internal.AlgebraCore.P103.Ch01.FourFiveLemmas
import MathGenome.Internal.AlgebraCore.P103.Ch02.Projective
import MathGenome.Internal.AlgebraCore.P103.Ch11.DimensionShifting
import Mathlib.Tactic.Abel

namespace P103.Ch11.ExtensionClassification
open CategoryTheory
open P103.Specs.Ch11.ExtensionClassification
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.Horseshoe P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.ExtExactSequences
open P103.Specs.Ch10.HomologySequence
noncomputable section
set_option maxHeartbeats 400000
universe u v
variable {R : Type u} [Ring R]

/-- Descent through an injective map onto its image, retaining the equation. -/
def factorThroughInjection {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R X] [Module R Y] [Module R Z]
    (i : Y →ₗ[R] Z) (hi : Function.Injective i) (f : X →ₗ[R] Z)
    (hf : ∀ x, f x ∈ LinearMap.range i) : X →ₗ[R] Y :=
  (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp (f.codRestrict _ hf)

theorem factorThroughInjection_spec {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R X] [Module R Y] [Module R Z]
    (i : Y →ₗ[R] Z) (hi : Function.Injective i) (f : X →ₗ[R] Z)
    (hf : ∀ x, f x ∈ LinearMap.range i) :
    i.comp (factorThroughInjection i hi f hf) = f := by
  ext x
  exact congrArg Subtype.val ((LinearEquiv.ofInjective i hi).apply_symm_apply ⟨f x, hf x⟩)

theorem maps_are_isomorphisms : maps_are_isomorphismsType.{u,v} := by
  intro R _ A B E F f hi hp
  have hf : Function.Bijective f :=
    P103.Ch01.FourFiveLemmas.short_five_bijective R B E.middle A B F.middle A
      E.i E.p F.i F.p LinearMap.id f LinearMap.id
      E.injective E.surjective F.injective F.surjective E.exact F.exact
      (by simpa using hi.symm) (by simpa using hp)
      Function.bijective_id Function.bijective_id
  exact ⟨hf, LinearEquiv.ofBijective f hf, hi, hp⟩

theorem lift_representatives : lift_representativesType.{u,v} := by
  intro R _ A B S E
  letI := S.projective
  constructor
  · obtain ⟨l, hl⟩ := Module.projective_lifting_property E.p S.ε E.surjective
    have h : ∀ k, (l.comp S.j) k ∈ LinearMap.range E.i := by
      intro k
      apply (E.exact _).mp
      change E.p (l (S.j k)) = 0
      rw [← LinearMap.comp_apply, hl]
      exact (S.exact _).mpr ⟨k, rfl⟩
    exact ⟨l, factorThroughInjection E.i E.injective (l.comp S.j) h,
      hl, factorThroughInjection_spec E.i E.injective (l.comp S.j) h⟩
  · intro l l' φ φ' hl hl'
    have h : ∀ p, (l' - l) p ∈ LinearMap.range E.i := by
      intro p
      apply (E.exact _).mp
      change E.p (l' p - l p) = 0
      rw [map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply, hl'.1, hl.1, sub_self]
    let ψ := factorThroughInjection E.i E.injective (l' - l) h
    have hψ : E.i.comp ψ = l' - l := factorThroughInjection_spec E.i E.injective _ h
    refine ⟨ψ, ?_⟩
    ext k
    apply E.injective
    change E.i (φ' k - φ k) = E.i (ψ (S.j k))
    rw [map_sub, ← LinearMap.comp_apply E.i φ', hl'.2,
      ← LinearMap.comp_apply E.i φ, hl.2,
      ← LinearMap.comp_apply E.i ψ, hψ]
    rfl

/-- The two representative maps for the graph quotient. -/
@[simp] theorem graph_i_apply {A B : ModuleCat.{v} R} (S : Presentation A)
    (φ : S.K →ₗ[R] B) (b : B) :
    (graphData S φ).i b = Submodule.Quotient.mk (b,0) := rfl

@[simp] theorem graph_p_apply {A B : ModuleCat.{v} R} (S : Presentation A)
    (φ : S.K →ₗ[R] B) (b : B) (p : S.P) :
    (graphData S φ).p (Submodule.Quotient.mk (b,p)) = S.ε p := rfl

theorem graph_exact : graph_exactType.{u,v} := by
  intro R _ A B S φ
  let N := LinearMap.range (graphRelation S φ)
  refine ⟨?_, ?_, ?_⟩
  · intro b b' h
    have hm : (b - b', (0 : S.P)) ∈ N := by
      simpa using (Submodule.Quotient.eq N).mp h
    obtain ⟨k, hk⟩ := hm
    have hkj : S.j k = 0 := by
      have hs := congrArg Prod.snd hk
      change -S.j k = 0 at hs
      exact neg_eq_zero.mp hs
    have hk0 : k = 0 := S.injective (hkj.trans (map_zero S.j).symm)
    have hb := congrArg Prod.fst hk
    change φ k = b - b' at hb
    rw [hk0, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  · intro q
    obtain ⟨⟨b,p⟩, rfl⟩ := N.mkQ_surjective q
    change S.ε p = 0 ↔ ∃ b', (graphData S φ).i b' = Submodule.Quotient.mk (b,p)
    constructor
    · intro hp
      obtain ⟨k, hk⟩ := (S.exact p).mp hp
      refine ⟨b + φ k, ?_⟩
      apply (Submodule.Quotient.eq N).mpr
      refine ⟨k, ?_⟩
      apply Prod.ext
      · change φ k = b + φ k - b
        abel
      · change -S.j k = 0 - p
        rw [hk, zero_sub]
    · rintro ⟨b', h⟩
      have hh := congrArg (graphData S φ).p h
      change S.ε 0 = S.ε p at hh
      simpa using hh.symm
  · intro a
    obtain ⟨p, hp⟩ := S.surjective a
    exact ⟨Submodule.Quotient.mk (0,p), hp⟩

/-- Changing a representative by a restriction gives the source's shear map. -/
theorem graph_equivalence : graph_equivalenceType.{u,v} := by
  intro R _ A B S φ φ' ψ hφ
  let N := LinearMap.range (graphRelation S φ)
  let N' := LinearMap.range (graphRelation S φ')
  let shear : B × S.P →ₗ[R] B × S.P :=
    ((LinearMap.fst R B S.P) - ψ.comp (LinearMap.snd R B S.P)).prod
      (LinearMap.snd R B S.P)
  have hm : N ≤ N'.comap shear := by
    rintro _ ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    apply Prod.ext
    · change φ' k = φ k - ψ (-S.j k)
      rw [hφ]
      simp
    · rfl
  let f := N.mapQ N' shear hm
  have hi : f.comp (graphData S φ).i = (graphData S φ').i := by
    ext b
    change Submodule.Quotient.mk (b - ψ 0, (0 : S.P)) = Submodule.Quotient.mk (b,0)
    rw [map_zero, sub_zero]
  have hp : (graphData S φ').p.comp f = (graphData S φ).p := by
    apply LinearMap.ext
    intro q
    obtain ⟨⟨b,p⟩, rfl⟩ := N.mkQ_surjective q
    rfl
  have hf := maps_are_isomorphisms R A B
    ⟨graphData S φ, graph_exact R A B S φ⟩
    ⟨graphData S φ', graph_exact R A B S φ'⟩ f hi hp
  exact ⟨LinearEquiv.ofBijective f hf.1, (fun _ _ => rfl), hi, hp⟩

/-- Every extension with a lift is isomorphic to its graph-quotient model. -/
theorem graph_model {A B : ModuleCat.{v} R} (S : Presentation A)
    (E : Extension A B) (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B)
    (hl : IsLiftRepresentative S E l φ) :
    Extension.Equivalent ⟨graphData S φ, graph_exact R A B S φ⟩ E := by
  let N := LinearMap.range (graphRelation S φ)
  let t : B × S.P →ₗ[R] E.middle := E.i.coprod l
  have ht : N ≤ LinearMap.ker t := by
    rintro _ ⟨k, rfl⟩
    change E.i (φ k) + l (-S.j k) = 0
    have hk : E.i (φ k) = l (S.j k) := LinearMap.congr_fun hl.2 k
    rw [hk, map_neg, add_neg_cancel]
  let f := N.liftQ t ht
  apply (maps_are_isomorphisms R A B
    ⟨graphData S φ, graph_exact R A B S φ⟩ E f ?_ ?_).2
  · ext b
    change E.i b + l 0 = E.i b
    rw [map_zero, add_zero]
  · apply LinearMap.ext
    intro q
    obtain ⟨⟨b,p⟩, rfl⟩ := N.mkQ_surjective q
    change E.p (E.i b + l p) = S.ε p
    rw [map_add, (E.exact _).mpr ⟨b, rfl⟩, zero_add]
    exact LinearMap.congr_fun hl.1 p

variable {A B : ModuleCat.{v} R}

def chosenLift (S : Presentation A) (E : Extension A B) : S.P →ₗ[R] E.middle :=
  Classical.choose (lift_representatives R A B S E).1

def chosenRepresentative (S : Presentation A) (E : Extension A B) : S.K →ₗ[R] B :=
  Classical.choose (Classical.choose_spec (lift_representatives R A B S E).1)

theorem chosenRepresentative_spec (S : Presentation A) (E : Extension A B) :
    IsLiftRepresentative S E (chosenLift S E) (chosenRepresentative S E) :=
  Classical.choose_spec (Classical.choose_spec (lift_representatives R A B S E).1)

def extensionToCoker (S : Presentation A) (E : Extension A B) : PresentationCoker S B :=
  Submodule.Quotient.mk (chosenRepresentative S E)

theorem extensionToCoker_formula (S : Presentation A) (E : Extension A B)
    (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B) (h : IsLiftRepresentative S E l φ) :
    extensionToCoker S E = Submodule.Quotient.mk φ := by
  apply (Submodule.Quotient.eq _).mpr
  obtain ⟨ψ, hψ⟩ := (lift_representatives R A B S E).2 l (chosenLift S E)
    φ (chosenRepresentative S E) h (chosenRepresentative_spec S E)
  exact ⟨ψ, hψ.symm⟩

theorem extensionToCoker_equivalent (S : Presentation A) (E F : Extension A B)
    (h : E.Equivalent F) : extensionToCoker S E = extensionToCoker S F := by
  obtain ⟨e, hi, hp⟩ := h
  let l := chosenLift S E
  let φ := chosenRepresentative S E
  have hE := chosenRepresentative_spec S E
  have hF : IsLiftRepresentative S F (e.toLinearMap.comp l) φ := by
    constructor
    · ext p
      change F.p (e (l p)) = S.ε p
      calc
        F.p (e (l p)) = E.p (l p) := LinearMap.congr_fun hp _
        _ = S.ε p := LinearMap.congr_fun hE.1 _
    · ext k
      change F.i (φ k) = e (l (S.j k))
      calc
        F.i (φ k) = e (E.i (φ k)) := (LinearMap.congr_fun hi _).symm
        _ = e (l (S.j k)) := congrArg e (LinearMap.congr_fun hE.2 k)
  exact (extensionToCoker_formula S E l φ hE).trans
    (extensionToCoker_formula S F _ φ hF).symm

/-- The graph model's tautological lift restricts to exactly φ, with positive sign. -/
def graphLift (S : Presentation A) (φ : S.K →ₗ[R] B) : S.P →ₗ[R] GraphModule S φ :=
  (LinearMap.range (graphRelation S φ)).mkQ.comp (LinearMap.inr R B S.P)

theorem graphLift_spec (S : Presentation A) (φ : S.K →ₗ[R] B) :
    IsLiftRepresentative S ⟨graphData S φ, graph_exact R A B S φ⟩ (graphLift S φ) φ := by
  constructor
  · ext p
    rfl
  · ext k
    apply (Submodule.Quotient.eq _).mpr
    exact ⟨k, by simp [graphRelation]⟩

def classesToCoker (S : Presentation A) : ExtensionClasses A B → PresentationCoker S B :=
  Quotient.lift (extensionToCoker S) (extensionToCoker_equivalent S)

@[simp] theorem classesToCoker_mk (S : Presentation A) (E : Extension A B) :
    classesToCoker S (extensionClass E) = extensionToCoker S E := rfl

theorem classesToCoker_bijective (S : Presentation A) : Function.Bijective (classesToCoker (B := B) S) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | _ E =>
      induction y using Quotient.inductionOn with | _ F =>
        intro h
        apply Quotient.sound
        have hm := (Submodule.Quotient.eq _).mp h
        obtain ⟨ψ, hψ⟩ := hm
        let φ := chosenRepresentative S E
        let φ' := chosenRepresentative S F
        have hφ : φ = φ' + ψ.comp S.j := by
          change restriction S B ψ = φ - φ' at hψ
          change ψ.comp S.j = φ - φ' at hψ
          rw [hψ]
          abel
        obtain ⟨e, _, hi, hp⟩ := graph_equivalence R A B S φ' φ ψ hφ
        have hg : Extension.Equivalent
            ⟨graphData S φ', graph_exact R A B S φ'⟩
            ⟨graphData S φ, graph_exact R A B S φ⟩ := ⟨e, hi, hp⟩
        have hE := graph_model S E _ φ (chosenRepresentative_spec S E)
        have hF := graph_model S F _ φ' (chosenRepresentative_spec S F)
        exact Setoid.trans (Setoid.symm hE) (Setoid.trans (Setoid.symm hg) hF)
  · intro q
    obtain ⟨φ, rfl⟩ := (LinearMap.range (restriction S B)).mkQ_surjective q
    refine ⟨extensionClass ⟨graphData S φ, graph_exact R A B S φ⟩, ?_⟩
    exact extensionToCoker_formula S _ _ φ (graphLift_spec S φ)

/-- The algebraic classification, prior to identifying the cokernel with Ext. -/
def presentationClassification (S : Presentation A) : ExtensionClasses A B ≃ PresentationCoker S B :=
  Equiv.ofBijective (classesToCoker S) (classesToCoker_bijective S)

/-- Compare the two positive connecting conventions by an explicit lift chase.
Precomposition reverses the short exact sequence and contributes the minus. -/
theorem connecting_sign (S : Presentation A) (E : Extension A B)
    (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B) (hl : IsLiftRepresentative S E l φ)
    (L : LeftResolution R S.K) (Q : LeftResolution R A)
    (H : ProjectiveData S.j S.ε L Q)
    (δ : ExtWith L B 0 →ₗ[ℤ] ExtWith Q B 1)
    (η : ExtWith Q A 0 →ₗ[ℤ] ExtWith Q B 1)
    (hδ : FirstConnecting (i := ModuleCat.ofHom S.j) (p := ModuleCat.ofHom S.ε) H B 0 δ)
    (hη : SecondConnecting Q (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) 0 η) :
    η (homClass Q A LinearMap.id) = -δ (homClass L B φ) := by
  let z := P103.Ch11.ExtTorDefinitions.homToZeroCycles L B φ
  have hs := P103.Ch11.ExtExactSequences.first_degreewise_exact (i := ModuleCat.ofHom S.j) (p := ModuleCat.ofHom S.ε) H B
  obtain ⟨b, a, hb, ha⟩ := P103.Ch10.HomologySequence.lifts
    (homPreMap H.projection B) (homPreMap H.inclusion B) hs (by rfl) z
  change H.middle.complex.X 0 →ₗ[R] B at b
  let aa : Q.complex.X 1 →ₗ[R] B := a.val
  change b.comp (H.inclusion.f 0).hom = φ.comp L.ε at hb
  change aa.comp (H.projection.f 1).hom = b.comp (H.middle.complex.d 1 0).hom at ha
  have htδ : δ (homClass L B φ) = homologyClass _ 1 a := hδ z b a hb ha
  have hsplit := P103.Ch10.HorseshoeNaturality.split_exact H.inclusion H.projection
    (P103.Ch10.HorseshoeNaturality.projective_split R S.K S.P A S.j S.ε L Q H)
  let w : H.middle.complex.X 0 →ₗ[R] E.middle := l.comp H.middle.ε - E.i.comp b
  have hw : LinearMap.ker (H.projection.f 0).hom ≤ LinearMap.ker w := by
    intro x hx
    obtain ⟨y, rfl⟩ := ((hsplit 0).2.1 x).mp hx
    change l (H.middle.ε ((H.inclusion.f 0).hom y)) - E.i (b ((H.inclusion.f 0).hom y)) = 0
    have hi : H.middle.ε ((H.inclusion.f 0).hom y) = S.j (L.ε y) :=
      LinearMap.congr_fun H.augmentation_inclusion y
    have hb' : b ((H.inclusion.f 0).hom y) = φ (L.ε y) := LinearMap.congr_fun hb y
    have hlj : E.i (φ (L.ε y)) = l (S.j (L.ε y)) := LinearMap.congr_fun hl.2 _
    rw [hi, hb', hlj, sub_self]
  obtain ⟨t, ht⟩ := P103.Ch10.Horseshoe.descend_surjective
    (H.projection.f 0).hom (hsplit 0).2.2 w hw
  have htp : E.p.comp t = Q.ε := by
    ext x
    obtain ⟨y, rfl⟩ := (hsplit 0).2.2 x
    change E.p (t ((H.projection.f 0).hom y)) = Q.ε ((H.projection.f 0).hom y)
    rw [← LinearMap.comp_apply t, ht]
    change E.p (l (H.middle.ε y) - E.i (b y)) = _
    rw [map_sub, (E.exact _).mpr ⟨b y, rfl⟩, sub_zero]
    have hlp : E.p (l (H.middle.ε y)) = S.ε (H.middle.ε y) := LinearMap.congr_fun hl.1 _
    exact hlp.trans (LinearMap.congr_fun H.augmentation_projection y).symm
  have htd : E.i.comp (-aa) = t.comp (Q.complex.d 1 0).hom := by
    ext x
    obtain ⟨y, rfl⟩ := (hsplit 1).2.2 x
    have hc := P103.Ch10.HomologySequence.comm_apply H.projection 1 0 y
    have hay : aa ((H.projection.f 1).hom y) = b ((H.middle.complex.d 1 0).hom y) :=
      LinearMap.congr_fun ha y
    change E.i (-aa ((H.projection.f 1).hom y)) = t ((Q.complex.d 1 0).hom ((H.projection.f 1).hom y))
    rw [hay, hc, ← LinearMap.comp_apply t, ht]
    change E.i (-b ((H.middle.complex.d 1 0).hom y)) =
      l (H.middle.ε ((H.middle.complex.d 1 0).hom y)) - E.i (b ((H.middle.complex.d 1 0).hom y))
    have hy : H.middle.ε ((H.middle.complex.d 1 0).hom y) = 0 :=
      LinearMap.congr_fun (P103.Ch10.Comparison.augmentation_square H.middle) y
    rw [hy, map_zero, zero_sub, map_neg]
  have htη := hη (P103.Ch11.ExtTorDefinitions.homToZeroCycles Q A LinearMap.id) t (-a) htp htd
  change η (homClass Q A LinearMap.id) = homologyClass _ 1 (-a) at htη
  rw [htη, map_neg, ← htδ]

/-- Zero in the presentation cokernel is exactly the existence of a section. -/
theorem extensionToCoker_eq_zero_iff (S : Presentation A) (E : Extension A B) :
    extensionToCoker S E = 0 ↔ E.IsSplit := by
  constructor
  · intro h
    obtain ⟨ψ, hψ⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
    change ψ.comp S.j = chosenRepresentative S E at hψ
    let l := chosenLift S E
    have hl := chosenRepresentative_spec S E
    let r : S.P →ₗ[R] E.middle := l - E.i.comp ψ
    have hr : LinearMap.ker S.ε ≤ LinearMap.ker r := by
      intro p hp
      obtain ⟨k, rfl⟩ := (S.exact p).mp hp
      change l (S.j k) - E.i (ψ (S.j k)) = 0
      have hk : ψ (S.j k) = chosenRepresentative S E k := LinearMap.congr_fun hψ k
      have hlk : E.i (chosenRepresentative S E k) = l (S.j k) := LinearMap.congr_fun hl.2 k
      rw [hk, hlk, sub_self]
    obtain ⟨t, ht⟩ := P103.Ch10.Horseshoe.descend_surjective S.ε S.surjective r hr
    refine ⟨t, ?_⟩
    ext a
    obtain ⟨p, rfl⟩ := S.surjective a
    change E.p (t (S.ε p)) = S.ε p
    rw [← LinearMap.comp_apply t, ht]
    change E.p (l p - E.i (ψ p)) = S.ε p
    rw [map_sub, (E.exact _).mpr ⟨ψ p, rfl⟩, sub_zero]
    exact LinearMap.congr_fun hl.1 p
  · rintro ⟨t, ht⟩
    have hrep : IsLiftRepresentative S E (t.comp S.ε) 0 := by
      constructor
      · ext p
        exact LinearMap.congr_fun ht (S.ε p)
      · ext k
        change E.i 0 = t (S.ε (S.j k))
        rw [(S.exact _).mpr ⟨k,rfl⟩, map_zero, map_zero]
    rw [extensionToCoker_formula S E _ 0 hrep]
    rfl

/-- Pushing out a short exact module sequence keeps it short exact. -/
theorem pushout_exact {B' : ModuleCat.{v} R} (E : Extension A B) (β : B ⟶ B') :
    (pushoutData E β).IsShortExact := by
  let N := LinearMap.range (pushoutRelation E β)
  refine ⟨?_, ?_, ?_⟩
  · intro b b' h
    have hm : (b - b', (0 : E.middle)) ∈ N := by
      simpa using (Submodule.Quotient.eq N).mp h
    obtain ⟨k,hk⟩ := hm
    have hki : E.i k = 0 := neg_eq_zero.mp (congrArg Prod.snd hk)
    have hk0 : k = 0 := E.injective (hki.trans (map_zero E.i).symm)
    have hb := congrArg Prod.fst hk
    change β.hom k = b - b' at hb
    rw [hk0, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  · intro q
    obtain ⟨⟨b,x⟩,rfl⟩ := N.mkQ_surjective q
    change E.p x = 0 ↔ ∃ b', (pushoutData E β).i b' = Submodule.Quotient.mk (b,x)
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := (E.exact x).mp hx
      refine ⟨b + β.hom k, (Submodule.Quotient.eq N).mpr ⟨k, ?_⟩⟩
      apply Prod.ext
      · change β.hom k = b + β.hom k - b
        abel
      · change -E.i k = 0 - x
        rw [hk, zero_sub]
    · rintro ⟨b',h⟩
      have hh := congrArg (pushoutData E β).p h
      change E.p 0 = E.p x at hh
      simpa using hh.symm
  · intro a
    obtain ⟨x,hx⟩ := E.surjective a
    exact ⟨Submodule.Quotient.mk (0,x), hx⟩

/-- Pulling back a short exact module sequence keeps it short exact. -/
theorem pullback_exact {A' : ModuleCat.{v} R} (E : Extension A B) (α : A' ⟶ A) :
    (pullbackData E α).IsShortExact := by
  refine ⟨?_, ?_, ?_⟩
  · intro b b' h
    exact E.injective (congrArg (fun x => x.val.1) h)
  · intro q
    change q.val.2 = 0 ↔ ∃ b, (pullbackData E α).i b = q
    constructor
    · intro hq
      have hx : E.p q.val.1 = 0 := by
        have hm := q.property
        change E.p q.val.1 - α.hom q.val.2 = 0 at hm
        simpa [hq] using hm
      obtain ⟨b,hb⟩ := (E.exact _).mp hx
      exact ⟨b, Subtype.ext (Prod.ext hb hq.symm)⟩
    · rintro ⟨b,rfl⟩
      rfl
  · intro a'
    obtain ⟨x,hx⟩ := E.surjective (α.hom a')
    exact ⟨⟨(x,a'), by change E.p x - α.hom a' = 0; rw [hx, sub_self]⟩, rfl⟩

/-- The canonical comparison map into the coefficient pushout. -/
def intoPushout {B' : ModuleCat.{v} R} (E : Extension A B) (β : B ⟶ B') :
    E.middle →ₗ[R] (pushoutData E β).middle :=
  (LinearMap.range (pushoutRelation E β)).mkQ.comp (LinearMap.inr R B' E.middle)

theorem pushout_squares {B' : ModuleCat.{v} R} (E : Extension A B) (β : B ⟶ B') :
    (intoPushout E β).comp E.i = (pushoutData E β).i.comp β.hom ∧
    (pushoutData E β).p.comp (intoPushout E β) = E.p := by
  constructor
  · ext b
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-b, ?_⟩
    simp [pushoutRelation]
  · ext x
    rfl

/-- The canonical comparison map out of the coefficient pullback. -/
def fromPullback {A' : ModuleCat.{v} R} (E : Extension A B) (α : A' ⟶ A) :
    (pullbackData E α).middle →ₗ[R] E.middle :=
  (LinearMap.fst R E.middle A').comp (pullbackSubmodule E α).subtype

theorem pullback_squares {A' : ModuleCat.{v} R} (E : Extension A B) (α : A' ⟶ A) :
    (fromPullback E α).comp (pullbackData E α).i = E.i ∧
    E.p.comp (fromPullback E α) = α.hom.comp (pullbackData E α).p := by
  constructor
  · rfl
  · ext q
    exact sub_eq_zero.mp q.property

section AdequateUniverse
variable {A B : ModuleCat.{max u v} R}

/-- The degree-zero projective term gives a presentation of every module. -/
def resolutionPresentation (Q : LeftResolution R A) (hQ : Q.IsProjective) : Presentation A where
  K := ModuleCat.of R (LinearMap.ker Q.ε)
  P := Q.complex.X 0
  j := (LinearMap.ker Q.ε).subtype
  ε := Q.ε
  injective := Subtype.val_injective
  exact := by
    intro p
    exact ⟨fun h => ⟨⟨p,h⟩,rfl⟩, fun ⟨k,h⟩ => h ▸ k.property⟩
  surjective := Q.surjective
  projective := hQ 0

/-- A presentation's cokernel is Ext¹ with the normalization imposed by the
second-variable connector. The comparison works for every extension lift. -/
theorem exists_presentationEquiv (S : Presentation A) (Q : LeftResolution R A)
    (hQ : Q.IsProjective) :
    ∃ c : PresentationCoker S B ≃ₗ[ℤ] ExtWith Q B 1,
      IsPresentationEquiv S Q c ∧
      ∀ (E : Extension A B) (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B),
        IsLiftRepresentative S E l φ →
        ∀ (η : ExtWith Q A 0 →ₗ[ℤ] ExtWith Q B 1),
          SecondConnecting Q (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) 0 η →
          c (Submodule.Quotient.mk φ) = η (homClass Q A LinearMap.id) := by
  obtain ⟨L,hL⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution R S.K
  obtain ⟨⟨H⟩, hh⟩ := P103.Ch11.DimensionShifting.ext_first R S.K S.P A
    (ModuleCat.ofHom S.j) (ModuleCat.ofHom S.ε) S.injective S.exact S.surjective
    S.projective B L Q hL hQ
  obtain ⟨δ,hδ,_,e,he⟩ := hh H
  let c := e.symm.trans (LinearEquiv.neg ℤ)
  have hc (φ : S.K →ₗ[R] B) : c (Submodule.Quotient.mk φ) = -δ 0 (homClass L B φ) := by
    change -e.symm (Submodule.Quotient.mk φ) = _
    rw [he]
  have hformula (E : Extension A B) (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B)
      (hl : IsLiftRepresentative S E l φ)
      (η : ExtWith Q A 0 →ₗ[ℤ] ExtWith Q B 1)
      (hη : SecondConnecting Q (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) 0 η) :
      c (Submodule.Quotient.mk φ) = η (homClass Q A LinearMap.id) := by
    rw [hc]
    exact (connecting_sign S E l φ hl L Q H (δ 0) η (hδ 0) hη).symm
  refine ⟨c, ?_, hformula⟩
  intro L' _ H' δ' hδ' φ
  let E : Extension A B := ⟨graphData S φ, graph_exact R A B S φ⟩
  obtain ⟨η,hη,_⟩ := P103.Ch11.ExtExactSequences.second_sequence R A Q hQ
    B E.middle A (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) E.injective E.exact E.surjective
  exact (hformula E (graphLift S φ) φ (graphLift_spec S φ) (η 0) (hη 0).1).trans
    (connecting_sign S E (graphLift S φ) φ (graphLift_spec S φ) L' Q H' δ' (η 0) hδ' (hη 0).1)

/-- Full extension classification with its connecting formula and inverse. -/
theorem classification : classificationType.{u,v} := by
  intro R _ A B Q hQ
  let S := resolutionPresentation Q hQ
  obtain ⟨c,hc,hcf⟩ := exists_presentationEquiv (B := B) S Q hQ
  let e := (presentationClassification (B := B) S).trans c.toEquiv
  have he : RepresentsConnector Q e := by
    intro E η hη
    exact hcf E (chosenLift S E) (chosenRepresentative S E) (chosenRepresentative_spec S E) η hη
  refine ⟨e, he, ?_, ?_⟩
  · intro E
    change c (extensionToCoker S E) = 0 ↔ E.IsSplit
    rw [← map_zero c, c.injective.eq_iff]
    exact extensionToCoker_eq_zero_iff S E
  · intro S'
    obtain ⟨c',hc',hcf'⟩ := exists_presentationEquiv (B := B) S' Q hQ
    have hrep (E : Extension A B) (l : S'.P →ₗ[R] E.middle) (φ : S'.K →ₗ[R] B)
        (hl : IsLiftRepresentative S' E l φ) : e (extensionClass E) = c' (Submodule.Quotient.mk φ) := by
      obtain ⟨η,hη,_⟩ := P103.Ch11.ExtExactSequences.second_sequence R A Q hQ
        B E.middle A (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) E.injective E.exact E.surjective
      exact (he E (η 0) (hη 0).1).trans (hcf' E l φ hl (η 0) (hη 0).1).symm
    refine ⟨c',hc',hrep,?_⟩
    intro φ
    refine ⟨graph_exact R A B S' φ, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hrep _ _ φ (graphLift_spec S' φ)).symm

end AdequateUniverse

/-- Naturality of a connector on a literal Hom representative. -/
theorem connecting_natural_hom
    {X X' C C' D D' : ModuleCat.{v} R}
    (P : LeftResolution R X) (Q : LeftResolution R X')
    (hP : P.IsProjective) (hQ : Q.IsProjective)
    (T0 : ExtMaps.{u,v,v} R 0) (T1 : ExtMaps.{u,v,v} R 1)
    (E : Extension C D) (F : Extension C' D')
    (f : X' ⟶ X) (β : D ⟶ D') (m : E.middle →ₗ[R] F.middle) (γ : C ⟶ C')
    (hi : m.comp E.i = F.i.comp β.hom) (hp : F.p.comp m = γ.hom.comp E.p)
    (δ : ExtWith P C 0 →ₗ[ℤ] ExtWith P D 1)
    (η : ExtWith Q C' 0 →ₗ[ℤ] ExtWith Q D' 1)
    (hδ : SecondConnecting P (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) 0 δ)
    (hη : SecondConnecting Q (ModuleCat.ofHom F.i) (ModuleCat.ofHom F.p) 0 η)
    (h : X →ₗ[R] C) :
    T1.map ⟨P,hP⟩ ⟨Q,hQ⟩ f β (δ (homClass P C h)) =
      η (homClass Q C' (γ.hom.comp (h.comp f.hom))) := by
  have hh := P103.Ch11.ExtExactSequences.second_natural R 0 T0 T1 X X' P Q hP hQ f
    D E.middle C D' F.middle C'
    (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p)
    (ModuleCat.ofHom F.i) (ModuleCat.ofHom F.p) β (ModuleCat.ofHom m) γ
    E.injective E.exact E.surjective F.injective F.exact F.surjective
    (by apply ModuleCat.hom_ext; exact hi)
    (by apply ModuleCat.hom_ext; exact hp.symm) δ η hδ hη
  have hv : T1.map ⟨P,hP⟩ ⟨Q,hQ⟩ f β (δ (homClass P C h)) =
      η (T0.map ⟨P,hP⟩ ⟨Q,hQ⟩ f γ (homClass P C h)) :=
    LinearMap.congr_fun hh (homClass P C h)
  exact hv.trans (congrArg η
    (P103.Ch11.DimensionShifting.homClass_map ⟨P,hP⟩ ⟨Q,hQ⟩ T0 f γ h))


/-- The induced pushout and pullback functions agree with both Ext actions. -/
theorem naturality : P103.Specs.Ch11.ExtensionClassification.naturalityType.{u,v} := by
  intro R _ A A' B B' Q Q' hQ hQ' T e ep er he hep her β α
  obtain ⟨T0⟩ := P103.Ch11.ExtTorDefinitions.ext_bifunctorial R 0
  constructor
  · let push : ExtensionClasses A B → ExtensionClasses A B' :=
      fun x => ep.symm (T.map ⟨Q,hQ⟩ ⟨Q,hQ⟩ (𝟙 A) β (e x))
    refine ⟨push, ?_, ?_⟩
    · intro E
      let F : Extension A B' := ⟨pushoutData E β, pushout_exact E β⟩
      refine ⟨pushout_exact E β, ?_⟩
      apply ep.injective
      change ep (ep.symm _) = ep (extensionClass F)
      rw [ep.apply_symm_apply]
      obtain ⟨δ,hδ,_⟩ := P103.Ch11.ExtExactSequences.second_sequence R A Q hQ
        B E.middle A (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) E.injective E.exact E.surjective
      obtain ⟨η,hη,_⟩ := P103.Ch11.ExtExactSequences.second_sequence R A Q hQ
        B' F.middle A (ModuleCat.ofHom F.i) (ModuleCat.ofHom F.p) F.injective F.exact F.surjective
      rw [he E (δ 0) (hδ 0).1, hep F (η 0) (hη 0).1]
      have hs := pushout_squares E β
      simpa using connecting_natural_hom Q Q hQ hQ T0 T E F
        (𝟙 A) β (intoPushout E β) (𝟙 A) hs.1 (by simpa using hs.2)
        (δ 0) (η 0) (hδ 0).1 (hη 0).1 LinearMap.id
    · intro x
      exact ep.apply_symm_apply _
  · let pull : ExtensionClasses A B → ExtensionClasses A' B :=
      fun x => er.symm (T.map ⟨Q,hQ⟩ ⟨Q',hQ'⟩ α (𝟙 B) (e x))
    refine ⟨pull, ?_, ?_⟩
    · intro E
      let F : Extension A' B := ⟨pullbackData E α, pullback_exact E α⟩
      refine ⟨pullback_exact E α, ?_⟩
      apply er.injective
      change er (er.symm _) = er (extensionClass F)
      rw [er.apply_symm_apply]
      obtain ⟨δ,hδ,_⟩ := P103.Ch11.ExtExactSequences.second_sequence R A Q hQ
        B E.middle A (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) E.injective E.exact E.surjective
      obtain ⟨η,hη,_⟩ := P103.Ch11.ExtExactSequences.second_sequence R A' Q' hQ'
        B E.middle A (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) E.injective E.exact E.surjective
      obtain ⟨ζ,hζ,_⟩ := P103.Ch11.ExtExactSequences.second_sequence R A' Q' hQ'
        B F.middle A' (ModuleCat.ofHom F.i) (ModuleCat.ofHom F.p) F.injective F.exact F.surjective
      rw [he E (δ 0) (hδ 0).1, her F (ζ 0) (hζ 0).1]
      have hfirst := connecting_natural_hom Q Q' hQ hQ' T0 T E E
        α (𝟙 B) LinearMap.id (𝟙 A) (by ext; rfl) (by ext; rfl)
        (δ 0) (η 0) (hδ 0).1 (hη 0).1 LinearMap.id
      have hs := pullback_squares E α
      have hcoeff := connecting_natural_hom Q' Q' hQ' hQ' T0 T F E
        (𝟙 A') (𝟙 B) (fromPullback E α) α (by simpa using hs.1) hs.2
        (ζ 0) (η 0) (hζ 0).1 (hη 0).1 LinearMap.id
      rw [T.id] at hcoeff
      have hfirst' : T.map ⟨Q,hQ⟩ ⟨Q',hQ'⟩ α (𝟙 B) (δ 0 (homClass Q A LinearMap.id)) =
          η 0 (homClass Q' A α.hom) := by simpa using hfirst
      have hcoeff' : ζ 0 (homClass Q' A' LinearMap.id) = η 0 (homClass Q' A α.hom) := by
        simpa using hcoeff
      exact hfirst'.trans hcoeff'.symm
    · intro x
      exact er.apply_symm_apply _

theorem right_classification : right_classificationType.{u,v} := by
  intro R _
  exact ⟨classification Rᵐᵒᵖ, naturality Rᵐᵒᵖ⟩

end
end P103.Ch11.ExtensionClassification
