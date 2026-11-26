import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.WeilHilbert90
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SmoothPoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.Parabolics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.Trace.Basic
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Descent.AdjointBorelCohomology

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointBorelCohomology NonabelianCohomology

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 60000
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem finiteAdditiveVanishing : FiniteAdditiveVanishing.{u} := by
  classical
  intro k K _ _ _ _ _ v hv
  obtain ⟨x, hx⟩ := Algebra.trace_surjective k K (1 : k)
  have hsum : ∑ σ : Gal(K/k), σ x = 1 := by
    rw [← trace_eq_sum_automorphisms (K := k) x, hx, map_one]
  let t := ∑ σ : Gal(K/k), σ x * v σ
  refine ⟨t, fun τ => ?_⟩
  apply eq_sub_iff_add_eq.mpr
  calc
    v τ + τ t = (∑ σ : Gal(K/k), σ x) * v τ + τ t := by rw [hsum, one_mul]
    _ = ∑ σ : Gal(K/k), (τ * σ) x * v (τ * σ) := by
      simp only [t, map_sum, map_mul, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      -- Reindex the sum that multiplies v τ before combining terms.
      have hperm (f : Gal(K/k) → K) :
          ∑ σ : Gal(K/k), f (τ * σ) = ∑ σ : Gal(K/k), f σ :=
        Equiv.sum_comp (Equiv.mulLeft τ) f
      rw [show (∑ σ : Gal(K/k), (σ x * v τ + τ (σ x) * τ (v σ))) =
          ∑ σ : Gal(K/k), ((τ * σ) x * v τ + τ (σ x) * τ (v σ)) from by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hperm (fun σ => σ x * v τ)]]
      apply Finset.sum_congr rfl
      intro σ _
      rw [hv, mul_add]
      rfl
    _ = t := Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => σ x * v σ)

open private groupH1_eq_basepoint_of_finite from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.WeilHilbert90

theorem additiveVanishing : AdditiveVanishing.{u} := by
  intro k S _ _ _ _ G e
  apply groupH1_eq_basepoint_of_finite
  intro K _ _ _ _ a ha
  let f : NonabelianCohomology.Points k K G.X ≃* Multiplicative K :=
    (e.app (CommAlgCat.of k K)).groupIsoToMulEquiv
  have hact (σ : Gal(K/k)) (p : NonabelianCohomology.Points k K G.X) :
      (f (pointAction k K G.X σ p)).toAdd = σ (f p).toAdd :=
    congrArg Multiplicative.toAdd
      (e.hom.naturality_apply (CommAlgCat.ofHom σ.toAlgHom) p)
  obtain ⟨t, ht⟩ := finiteAdditiveVanishing k K (fun σ => (f (a σ)).toAdd) (by
    intro σ τ
    rw [ha, map_mul]
    change (f (a σ)).toAdd + (f (pointAction k K G.X σ (a τ))).toAdd = _
    rw [hact])
  refine ⟨f.symm (Multiplicative.ofAdd (-t)), fun σ => ?_⟩
  apply f.injective
  apply Multiplicative.toAdd.injective
  rw [map_mul, map_inv]
  change (f (a σ)).toAdd =
    -(f (f.symm (Multiplicative.ofAdd (-t)))).toAdd +
      (f (pointAction k K G.X σ (f.symm (Multiplicative.ofAdd (-t))))).toAdd
  rw [hact, f.apply_symm_apply]
  simpa [sub_eq_add_neg] using ht σ

section Extensions

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
variable {U B T : Type u} [Group U] [Group B] [Group T]
variable [TopologicalSpace U] [TopologicalSpace B] [TopologicalSpace T]
variable [DiscreteTopology U] [DiscreteTopology B] [DiscreteTopology T]
variable {ρU : Γ →* MulAut U} {ρB : Γ →* MulAut B} {ρT : Γ →* MulAut T}

omit [DiscreteTopology U] [DiscreteTopology T] in
private theorem extensionVanishing (i : U →* B) (q : B →* T)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hker : ∀ b, q b = 1 ↔ b ∈ Set.range i)
    (hiEquiv : ∀ σ a, i (ρU σ a) = ρB σ (i a))
    (hqEquiv : ∀ σ b, q (ρB σ b) = ρT σ (q b))
    (hact : ∀ b, Continuous (fun σ => ρB σ b))
    (hU : ∀ x : H1 ρU, x = basepoint ρU)
    (hT : ∀ x : H1 ρT, x = basepoint ρT) :
    ∀ x : H1 ρB, x = basepoint ρB := by
  intro x
  refine Quotient.inductionOn x fun a => ?_
  let c : Cocycle ρT := ⟨fun σ => q (a σ),
    (continuous_of_discreteTopology (f := q)).comp a.property.1, fun σ τ => by
      simp only [a.property.2 σ τ, map_mul, hqEquiv]⟩
  obtain ⟨t, ht⟩ := classOf_eq_iff.mp (hT (classOf c))
  obtain ⟨b, rfl⟩ := hq t
  let adjusted : Γ → B := fun σ => b⁻¹ * a σ * ρB σ b
  have hadj : Continuous adjusted := (continuous_const.mul a.property.1).mul (hact b)
  have hker' (σ : Γ) : adjusted σ ∈ Set.range i := by
    apply (hker _).mp
    have he : 1 = (q b)⁻¹ * q (a σ) * ρT σ (q b) := ht σ
    simpa only [adjusted, map_mul, map_inv, hqEquiv] using he.symm
  let lift : Set.range i → U := fun y => y.property.choose
  let d (σ : Γ) : U := lift ⟨adjusted σ, hker' σ⟩
  have hd (σ : Γ) : i (d σ) = adjusted σ := (hker' σ).choose_spec
  have hcont : Continuous d :=
    (continuous_of_discreteTopology (f := lift)).comp (hadj.subtype_mk hker')
  let aU : Cocycle ρU := ⟨d, hcont, fun σ τ => by
    apply hi
    rw [map_mul, hiEquiv, hd, hd, hd]
    simp only [adjusted, a.property.2 σ τ, map_mul, map_inv, MulAut.mul_apply]
    group⟩
  obtain ⟨u, hu⟩ := classOf_eq_iff.mp (hU (classOf aU))
  apply classOf_eq_iff.mpr
  refine ⟨b * i u, fun σ => ?_⟩
  have h := congrArg i (hu σ)
  change i 1 = i (u⁻¹ * d σ * ρU σ u) at h
  rw [map_one, map_mul, map_mul, map_inv, hd, hiEquiv] at h
  change (1 : B) = (b * i u)⁻¹ * a σ * ρB σ (b * i u)
  simpa only [adjusted, mul_inv_rev, map_mul, mul_assoc] using h

end Extensions

section SchemeExtensions

variable {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]

private abbrev SchemePoints (G : GroupScheme k) := NonabelianCohomology.Points k S G.X

private def pointsHom {G H : GroupScheme k} (f : G ⟶ H) :
    SchemePoints (S := S) G →* SchemePoints (S := S) H where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

omit [IsSepClosure k S] in
private theorem pointsHom_equiv {G H : GroupScheme k} (f : G ⟶ H) (σ : Gal(S/k))
    (x : SchemePoints (S := S) G) :
    pointsHom f (pointAction k S G.X σ x) = pointAction k S H.X σ (pointsHom f x) := by
  change (_ ≫ x) ≫ f.hom.hom = _ ≫ x ≫ f.hom.hom
  exact Category.assoc _ _ _

open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem schemeExtensionVanishing {B T : AffineAlgebraicGroup k}
    (U : ClosedSubgroup B.val) (q : B.val ⟶ T.val) (hker : IsSchemeKernel q U)
    (hq : Function.Surjective (pointsHom (S := S) q)) (hsB : Smooth B.val.X.hom)
    (hU : ∀ x : groupH1 k U.group.X S, x = groupBasepoint k U.group.X S)
    (hT : ∀ x : groupH1 k T.val.X S, x = groupBasepoint k T.val.X S) :
    ∀ x : groupH1 k B.val.X S, x = groupBasepoint k B.val.X S := by
  let : TopologicalSpace (SchemePoints (S := S) U.group) := ⊥
  let : TopologicalSpace (SchemePoints (S := S) B.val) := ⊥
  let : TopologicalSpace (SchemePoints (S := S) T.val) := ⊥
  let : DiscreteTopology (SchemePoints (S := S) U.group) := ⟨rfl⟩
  let : DiscreteTopology (SchemePoints (S := S) B.val) := ⟨rfl⟩
  let : DiscreteTopology (SchemePoints (S := S) T.val) := ⟨rfl⟩
  letI : IsClosedImmersion U.inclusion.hom.hom.left := U.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  have hi : Function.Injective (pointsHom (S := S) U.inclusion) :=
    fun _ _ h => (cancel_mono U.inclusion.hom.hom).mp h
  have hact : ∀ b : SchemePoints (S := S) B.val,
      Continuous (fun σ => pointAction k S B.val.X σ b) := by
    letI : Smooth B.val.X.hom := hsB
    intro b
    have hc : Continuous (fun t : Gal(S/k) × SchemePoints (S := S) B.val =>
        pointAction k S B.val.X t.1 t.2) :=
      continuousPointAction (k := k) (S := S) (H := B.val.X)
    have hd : Continuous (fun σ : Gal(S/k) => (σ, b)) :=
      continuous_id.prodMk continuous_const
    have h : Continuous ((fun t : Gal(S/k) × SchemePoints (S := S) B.val =>
        pointAction k S B.val.X t.1 t.2) ∘ (fun σ : Gal(S/k) => (σ, b))) :=
      Continuous.comp hc hd
    exact h
  exact extensionVanishing (pointsHom U.inclusion) (pointsHom q) hi hq
    (fun b => (schemeKernel_sections hker b).symm)
    (pointsHom_equiv U.inclusion) (pointsHom_equiv q) hact hU hT

private theorem smoothSurjectivePoints {B T : AffineAlgebraicGroup k}
    (q : B.val ⟶ T.val) (hs : Smooth q.hom.hom.left) (hq : Surjective q.hom.hom.left) :
    Function.Surjective (pointsHom (S := S) q) := by
  intro x
  let q' := q.hom.hom
  let x' : Spec (CommRingCat.of S) ⟶ T.val.X.left := x.left
  let p : pullback q'.left x' ⟶ Spec (CommRingCat.of S) := pullback.snd _ _
  have hp := IsPullback.of_hasPullback q'.left x'
  letI : Smooth p := MorphismProperty.of_isPullback hp hs
  letI : Surjective p := MorphismProperty.of_isPullback hp hq
  letI : IsAffine B.val.X.left := B.property.1
  letI : IsAffine T.val.X.left := T.property.1
  letI : IsAffineHom q'.left := inferInstance
  letI : IsAffineHom p := MorphismProperty.of_isPullback hp inferInstance
  have hne : Nonempty (pullback q'.left x' : Scheme) :=
    ⟨(p.surjective (IsLocalRing.closedPoint S)).choose⟩
  letI : IsSepClosed S := IsSepClosure.sep_closed (k := k)
  obtain ⟨s, hs⟩ := exists_rational_point_of_smooth p hne
  let g := s ≫ pullback.fst q'.left x'
  have hg : g ≫ q'.left = x' := by
    dsimp [g]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
  rw [← Over.w q', ← Category.assoc, hg, Over.w x]

open Specs.HomogeneousQuotient (RepresentabilityAndTorsor)
open Specs.Unipotent (IsFppfGroupQuotient)
open private compareRepresentatives compareRepresentatives_projection quotientSmooth
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

private theorem smoothQuotient {B T : AffineAlgebraicGroup k}
    (U : ClosedSubgroup B.val) (q : B.val ⟶ T.val) (hq : IsFppfGroupQuotient U q)
    (hU : Smooth U.group.X.hom) : Smooth q.hom.hom.left := by
  obtain ⟨⟨P⟩, _⟩ := HomogeneousQuotient.homogeneousQuotient k B U
  obtain ⟨e, he⟩ := hq.2.2.2.2
  let j := compareRepresentatives P e
  have hp := compareRepresentatives_projection P q.hom.hom e he
  haveI : Smooth P.projection.left := quotientSmooth B P hU
  haveI : IsIso j.hom.left := (Over.forget _).map_isIso j.hom
  have hh : P.projection.left ≫ j.hom.left = q.hom.hom.left :=
    congrArg Over.Hom.left hp
  rw [← hh]
  infer_instance

private theorem vanishingOfGroupIso {G H : GroupScheme k} (e : G ≅ H)
    (hH : ∀ x : groupH1 k H.X S, x = groupBasepoint k H.X S) :
    ∀ x : groupH1 k G.X S, x = groupBasepoint k G.X S := by
  let : TopologicalSpace (SchemePoints (S := S) G) := ⊥
  let : TopologicalSpace (SchemePoints (S := S) H) := ⊥
  let : DiscreteTopology (SchemePoints (S := S) G) := ⟨rfl⟩
  let : DiscreteTopology (SchemePoints (S := S) H) := ⟨rfl⟩
  intro x
  refine Quotient.inductionOn x fun a => ?_
  let f := pointsHom (S := S) e.hom
  let g := pointsHom (S := S) e.inv
  have hg (p) : g (f p) = p := by
    let F := Grp.forget (SchemeOver k)
    change (p ≫ F.map e.hom) ≫ F.map e.inv = p
    rw [Category.assoc, ← F.map_comp, e.hom_inv_id, F.map_id]
    exact Category.comp_id p
  let a' : Cocycle (pointAction k S H.X) :=
    ⟨fun σ => f (a σ), (continuous_of_discreteTopology (f := f)).comp a.property.1,
      fun σ τ => by simp only [a.property.2 σ τ, map_mul, f, pointsHom_equiv]⟩
  obtain ⟨b, hb⟩ := classOf_eq_iff.mp (hH (classOf a'))
  apply classOf_eq_iff.mpr
  refine ⟨g b, fun σ => ?_⟩
  have he : 1 = b⁻¹ * f (a σ) * pointAction k S H.X σ b := hb σ
  change 1 = (g b)⁻¹ * a σ * pointAction k S G.X σ (g b)
  have h := congrArg g he
  rw [map_one, map_mul, map_mul, map_inv, hg] at h
  change 1 = (g b)⁻¹ * a σ * pointsHom e.inv (pointAction k S H.X σ b) at h
  rwa [pointsHom_equiv] at h

private theorem trivialVanishing :
    ∀ x : groupH1 k (Grp.trivial (SchemeOver k)).X S,
      x = groupBasepoint k (Grp.trivial (SchemeOver k)).X S := by
  let : TopologicalSpace (SchemePoints (S := S) (Grp.trivial (SchemeOver k))) := ⊥
  intro x
  refine Quotient.inductionOn x fun a => ?_
  apply congrArg (classOf (ρ := pointAction k S (Grp.trivial (SchemeOver k)).X))
  apply Subtype.ext
  funext σ
  exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _

private theorem trivialSmooth : Smooth (Grp.trivial (SchemeOver k)).X.hom := by
  change Smooth (𝟙 (Spec (CommRingCat.of k)))
  infer_instance

private theorem isoSmooth {G H : GroupScheme k} (e : G ≅ H)
    (h : Smooth H.X.hom) : Smooth G.X.hom := by
  letI : IsIso e.hom.hom.hom.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map_isIso e.hom
  letI := h
  rw [← Over.w e.hom.hom.hom]
  infer_instance

open private affineSmooth_iff_lifts from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

private theorem smoothOfAdditivePointIso (G : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj G.val ≅ StandardGroups.additivePoints k) :
    Smooth G.val.X.hom := by
  apply (affineSmooth_iff_lifts G.val.X G.property.1 G.property.2.1).mpr
  intro R _ _ J hJ y
  let r := CommAlgCat.of k R
  let s := CommAlgCat.of k (R ⧸ J)
  let π : r ⟶ s := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k J)
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
    ((e.hom.app s y : Multiplicative (R ⧸ J)).toAdd)
  refine ⟨e.inv.app r (Multiplicative.ofAdd z), ?_⟩
  change ((groupPointsFunctor k).obj G.val).map π
    (e.inv.app r (Multiplicative.ofAdd z)) = y
  rw [← e.inv.naturality_apply]
  have he : (StandardGroups.additivePoints k).map π (Multiplicative.ofAdd z) =
      e.hom.app s y := congrArg Multiplicative.ofAdd hz
  rw [he]
  exact e.hom_inv_id_app_apply s y

theorem splitUnipotentVanishing : SplitUnipotentVanishing.{u} := by
  intro k S _ _ _ _ G hG
  obtain ⟨n, C, hC⟩ := hG.2
  have step (i : ℕ) (hi : i ≤ n) :
      Smooth (C.term i).val.X.hom ∧
        (∀ x : groupH1 k (C.term i).val.X S, x = groupBasepoint k (C.term i).val.X S) := by
    refine Nat.decreasingInduction (motive := fun j _ =>
      Smooth (C.term j).val.X.hom ∧
        (∀ x : groupH1 k (C.term j).val.X S, x = groupBasepoint k (C.term j).val.X S)) ?_ ?_ hi
    · intro j hj ih
      obtain ⟨T, q, hq, hT⟩ := hC j hj
      let U : ClosedSubgroup (C.term j).val := ⟨_, C.step j, C.closed j⟩
      have hs := smoothQuotient U q hq ih.1
      have hT' : Smooth T.val.X.hom ∧
          (∀ x : groupH1 k T.val.X S, x = groupBasepoint k T.val.X S) := by
        rcases hT with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        · exact ⟨isoSmooth e trivialSmooth, vanishingOfGroupIso e trivialVanishing⟩
        · exact ⟨smoothOfAdditivePointIso T e, additiveVanishing k S T.val e⟩
      letI := hs
      letI := hT'.1
      have hB : Smooth (C.term j).val.X.hom := by
        rw [← Over.w q.hom.hom]
        infer_instance
      exact ⟨hB, schemeExtensionVanishing U q hq.1
        (smoothSurjectivePoints q hs hq.2.2.1) hB ih.2 hT'.2⟩
    · exact ⟨isoSmooth C.bottom trivialSmooth, vanishingOfGroupIso C.bottom trivialVanishing⟩
  exact vanishingOfGroupIso C.top.symm (step 0 (Nat.zero_le n)).2

end SchemeExtensions

section BorelImage

open Specs.AdjointCocharacters (IsAdjointQuotient)
open Specs.GeometricRadicals (IsReductive GeometricGroup baseChangedSubgroup)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.QuotientEmbedding (Presentation)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private preimageSubgroup preimageSquare smoothImage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private subgroupOf_mutual_iso borel_of_containing_borel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private full_preimage_of_surjective_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private descends quotientDescends
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private solvable_iff_sections rationalMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private smooth_extend_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private geometricLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalFlagLifting

variable {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k}

private theorem fullBorelPreimage {B Z : ClosedSubgroup G.val} {A : ClosedSubgroup Q.val}
    {q : G.val ⟶ Q.val} {p : B.group ⟶ A.group} (hz : IsSchemeKernel q Z)
    (hZ : IsSubgroupOf Z B) (hp : p ≫ A.inclusion = B.inclusion ≫ q)
    (hf : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left)
    (hl : LocallyOfFinitePresentation p.hom.hom.left) :
    IsPullback B.inclusion.hom.hom p.hom.hom q.hom.hom A.inclusion.hom.hom := by
  let J := preimageSubgroup q A
  let r : J.group ⟶ A.group := pullback.snd q A.inclusion
  have hr : J.inclusion ≫ q = r ≫ A.inclusion := pullback.condition
  have hBJ : IsSubgroupOf B J :=
    ⟨pullback.lift B.inclusion p hp.symm, pullback.lift_fst _ _ _⟩
  have hJB := full_preimage_of_surjective_subgroup hz hZ hp.symm hr hf hs hl
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hBJ hJB
  let F := Grp.forget (SchemeOver k)
  letI := A.isClosedImmersion
  letI : Mono A.inclusion.hom.hom := Over.mono_of_mono_left _
  have hF : e.hom.hom.hom ≫ J.inclusion.hom.hom = B.inclusion.hom.hom :=
    congrArg F.map he
  have hFr : J.inclusion.hom.hom ≫ q.hom.hom = r.hom.hom ≫ A.inclusion.hom.hom :=
    congrArg F.map hr
  have hFp : p.hom.hom ≫ A.inclusion.hom.hom = B.inclusion.hom.hom ≫ q.hom.hom :=
    congrArg F.map hp
  have her : e.hom.hom.hom ≫ r.hom.hom = p.hom.hom := by
    apply (cancel_mono A.inclusion.hom.hom).mp
    rw [Category.assoc, ← hFr, ← Category.assoc, hF, hFp]
  refine IsPullback.of_iso_pullback ⟨hFp.symm⟩
    (F.mapIso e ≪≫ (preimageSquare q A).isoPullback) ?_ ?_
  · change (e.hom.hom.hom ≫ _) ≫ _ = _
    rw [Category.assoc, IsPullback.isoPullback_hom_fst]
    exact hF
  · change (e.hom.hom.hom ≫ _) ≫ _ = _
    rw [Category.assoc, IsPullback.isoPullback_hom_snd]
    exact her

private theorem flagComparison {B : ClosedSubgroup G.val} {A : ClosedSubgroup Q.val}
    {q : G.val ⟶ Q.val} {p : B.group ⟶ A.group}
    (h : IsPullback B.inclusion.hom.hom p.hom.hom q.hom.hom A.inclusion.hom.hom)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hfinite : LocallyOfFinitePresentation q.hom.hom.left)
    (P : Presentation B) (P' : Presentation A) :
    ∃ e : P.scheme ≅ P'.scheme, P.projection ≫ e.hom = q.hom.hom ≫ P'.projection := by
  let f := q.hom.hom
  have hmem (T : SchemeOver k) (g : T ⟶ G.val.X) :
      g ∈ SubgroupSections B T ↔ g ≫ f ∈ SubgroupSections A T := by
    change (∃ b : T ⟶ B.group.X, b ≫ B.inclusion.hom.hom = g) ↔
      ∃ a : T ⟶ A.group.X, a ≫ A.inclusion.hom.hom = g ≫ f
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b ≫ p.hom.hom, by rw [Category.assoc, ← h.w, ← Category.assoc]⟩
    · rintro ⟨a, ha⟩
      exact ⟨h.lift g a ha.symm, h.lift_fst _ _ _⟩
  have hproj (T : SchemeOver k) (g₁ g₂ : T ⟶ G.val.X) :
      g₁ ≫ (f ≫ P'.projection) = g₂ ≫ (f ≫ P'.projection) ↔
        g₁ ≫ P.projection = g₂ ≫ P.projection := by
    simp only [← Category.assoc]
    rw [projection_eq_iff P', projection_eq_iff P]
    have hm := (hmem T (g₁⁻¹ * g₂)).symm
    simpa only [f, MonObj.mul_comp, GrpObj.inv_comp] using hm
  obtain ⟨g, hg⟩ := quotientDescends P (f ≫ P'.projection)
    (fun T a b hab => (hproj T a b).mpr ((projection_eq_iff P a b).mpr hab))
  letI : Flat f.left := hflat
  letI : Surjective f.left := hsurj
  letI : LocallyOfFinitePresentation f.left := hfinite
  letI := P.flat
  letI := P.surjective
  letI := P.finitePresentation
  letI := P'.flat
  letI := P'.surjective
  letI := P'.finitePresentation
  letI : Flat (f ≫ P'.projection).left := Flat.comp f.left P'.projection.left
  letI : Surjective (f ≫ P'.projection).left := by
    change Surjective (f.left ≫ P'.projection.left)
    infer_instance
  letI : LocallyOfFinitePresentation (f ≫ P'.projection).left := by
    change LocallyOfFinitePresentation (f.left ≫ P'.projection.left)
    infer_instance
  obtain ⟨j, hj⟩ := descends (f ≫ P'.projection) P.projection
    (fun T a b hab => (hproj T a b).mp hab)
  letI : Epi P.projection := Over.epi_of_epi_left _
  letI : Epi (f ≫ P'.projection) := Over.epi_of_epi_left _
  refine ⟨⟨g, j, ?_, ?_⟩, hg⟩
  · apply (cancel_epi P.projection).mp
    rw [← Category.assoc, hg, hj, Category.comp_id]
  · apply (cancel_epi (f ≫ P'.projection)).mp
    rw [← Category.assoc, hj, hg, Category.comp_id]

open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem groundBorelSmooth {B : ClosedSubgroup G.val}
    (hB : IsKBorel B) : Smooth B.group.X.hom := by
  obtain ⟨c, h⟩ := hB
  exact (smooth_extend_iff (AlgebraicClosure k) B.group.X).mp h.1.1

private theorem imageIsBorel {B : ClosedSubgroup G.val} {A : ClosedSubgroup Q.val}
    (p : B.group ⟶ A.group) (hB : IsKBorel B) (ha : Smooth A.group.X.hom)
    (hs : Surjective p.hom.hom.left)
    (hl : LocallyOfFinitePresentation p.hom.hom.left)
    (hcontains : Specs.BorelProper.ContainsGeometricBorel A) : IsKBorel A := by
  obtain ⟨cA, C, hC, hCA⟩ := hcontains
  obtain ⟨cB, hB⟩ := hB
  let K := AlgebraicClosure k
  let AK := GeometricGroup (closedSubgroupAlgebraicGroup A)
  let BK := GeometricGroup (closedSubgroupAlgebraicGroup B)
  let pK : BK.val ⟶ AK.val := (groupBaseChange k K).map p
  have hp := (baseChangeMapPullback (K := K) p.hom.hom).flip
  letI : Surjective pK.hom.hom.left := MorphismProperty.of_isPullback hp hs
  letI : LocallyOfFinitePresentation pK.hom.hom.left := MorphismProperty.of_isPullback hp hl
  have hAs : Smooth AK.val.X.hom := (smooth_extend_iff K A.group.X).mpr ha
  letI : ConnectedSpace BK.val.X.left := hB.1.2.1
  have hAc : ConnectedSpace AK.val.X.left :=
    (show Surjective pK.hom.hom.left from inferInstance).1.connectedSpace
      pK.hom.hom.left.continuous
  have hpoints : Function.Surjective (rationalMap pK) := by
    intro a
    obtain ⟨b, hb⟩ := geometricLift (K := K) pK.hom.hom a
    exact ⟨b, hb⟩
  letI := (solvable_iff_sections BK hB.1.1 hB.1.2.1).mp hB.1.2.2
  have hsolv := (solvable_iff_sections AK hAs hAc).mpr
    (Group.isSolvable_of_surjective hpoints)
  exact ⟨cA, borel_of_containing_borel hC ⟨hAs, hAc, hsolv⟩ hCA⟩

theorem adjointBorelImage : AdjointBorelImage.{u} := by
  intro k _ G Q B Z q hG hQ hB hZ hq
  let D := closedSubgroupAlgebraicGroup B
  obtain ⟨I, p, j, hfac, hcan, -⟩ :=
    schemeImageFactorization D Q (B.inclusion ≫ q)
  let A : ClosedSubgroup Q.val := ⟨I.val, j, hfac.2.2.2.2.2⟩
  obtain ⟨hp, hf, hs, hl, haff, _⟩ := hfac
  have hBp := fullBorelPreimage (A := A) hq.2.1 hZ hp hf hs hl
  have hBn := groundBorelSmooth hB
  have hAn := smoothImage D I p hf hs hBn
  have hflags := flagComparison (B := B) (A := A) (p := p) hBp hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
  obtain ⟨⟨P⟩, _⟩ := HomogeneousQuotient.homogeneousQuotient k G B
  obtain ⟨⟨P'⟩, _⟩ := HomogeneousQuotient.homogeneousQuotient k Q A
  have hGc : ConnectedSpace G.val.X.left := by
    letI := hG.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  have hQc : ConnectedSpace Q.val.X.left := by
    letI := hQ.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton Q.val.X.hom
  have hcontains : Specs.BorelProper.ContainsGeometricBorel B := by
    obtain ⟨h, hb⟩ := hB
    exact ⟨h, _, hb, 𝟙 _, Category.id_comp _⟩
  have hproper := (BorelProper.quotientProperIff G hG.1 hGc B hBn P).mpr hcontains
  have hproper' (P' : Presentation A) : IsProper P'.scheme.hom := by
    obtain ⟨e, _⟩ := hflags P P'
    letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom.left _).mp
      ((Over.w e.hom).symm ▸ hproper)
  have hc := (BorelProper.quotientProperIff Q hQ.1 hQc A hAn P').mp (hproper' P')
  have hBa := imageIsBorel (A := A) p hB hAn hs hl hc
  have hred (K : Type u) [Field K] [Algebra k K] :
      IsReduced ((groupBaseChange k K).obj A.group).X.left := by
    let X := ((groupBaseChange k K).obj A.group).X
    letI : Smooth X.hom := (smooth_extend_iff K A.group.X).mpr hAn
    exact isReduced_of_smooth_over_field X.hom
  exact ⟨⟨A, p, ⟨hp, hf, hs, hl, haff, A.isClosedImmersion⟩, hcan, hBp, hred,
    hAn, hBa, RootData.BorelNormalizer.groundFieldBorelNormalizer Q hQ A hBa,
    ⟨P'⟩, hproper', hflags⟩⟩

open private centre_le_of_selfCentralizer
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus

theorem adjointBorelForPair : AdjointBorelForPair.{u} := by
  intro k _ G B T hG hB htor hmax hTB
  obtain ⟨Z, Q, q, hq, hQ⟩ := AdjointCocharacters.adjointQuotientExists G hG
  have hZT : IsSubgroupOf Z T := centre_le_of_selfCentralizer hq.1
    (Reductive.TorusCentralizer.maximalTorusCentralizer G hG T htor hmax)
  obtain ⟨i, hi⟩ := hZT
  obtain ⟨j, hj⟩ := hTB
  have hZB : IsSubgroupOf Z B := ⟨i ≫ j, by rw [Category.assoc, hj, hi]⟩
  exact ⟨Z, Q, q, hq, hQ, ⟨i, hi⟩, adjointBorelImage B Z q hG hQ hB hZB hq⟩

open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsTorus IsMaximalTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (IsFppfGroupQuotient)

open private centre_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
open private geometric_preimage_maximal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private torus_baseChange_algClosure factors_of_range_subset
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private exists_maximal_torus_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private baseChangeKernelSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private torus_smooth_connected_solvable
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem imageIsMaximal {T Z : ClosedSubgroup G.val} {A : ClosedSubgroup Q.val}
    {q : G.val ⟶ Q.val} {p : T.group ⟶ A.group}
    (hq : IsAdjointQuotient Z q) (hG : IsReductive G)
    (hT : IsGeometricallyMaximal T) (hA : IsTorus A.group)
    (hp : p ≫ A.inclusion = T.inclusion ≫ q) :
    IsGeometricallyMaximal A := by
  let K := AlgebraicClosure k
  let GK := GeometricGroup G
  let QK := GeometricGroup Q
  let F := groupBaseChange k K
  obtain ⟨hZc, hZcent⟩ := centre_baseChange hq.1 K
  let ZK := baseChangedSubgroup K Z hZc
  let qK : GK.val ⟶ QK.val := F.map q
  have hZker : IsSchemeKernel qK ZK := baseChangeKernelSquare q Z.inclusion hq.2.1
  have hGK := (Reductive.RadicalBaseChange.reductiveFieldExtension
    (K := K) G hG.1 hG.2.1).mpr hG
  obtain ⟨hcT, hmT⟩ := hT
  let TK : ClosedSubgroup GK.val := baseChangedSubgroup K T hcT
  have hcA := LinearAlgebraicGroups.baseChangeClosedSubgroup k K A.inclusion A.isClosedImmersion
  let AK : ClosedSubgroup QK.val := baseChangedSubgroup K A hcA
  have hAK : IsTorus AK.group := torus_baseChange_algClosure (closedSubgroupAlgebraicGroup A) hA
  obtain ⟨M, hM, j, hj⟩ := exists_maximal_torus_over QK AK hAK
  let P := preimageSubgroup qK M
  let r : P.group ⟶ M.group := pullback.snd qK M.inclusion
  have hr : P.inclusion ≫ qK = r ≫ M.inclusion := pullback.condition
  have hP := preimageSquare qK M
  have hPS : IsPullback P.inclusion.hom.hom.left r.hom.hom.left
      qK.hom.hom.left M.inclusion.hom.hom.left := hP.map (Over.forget (Spec (CommRingCat.of K)))
  have hqs := (baseChangeMapPullback (K := K) q.hom.hom).flip
  have hrf : Flat r.hom.hom.left :=
    MorphismProperty.of_isPullback hPS (MorphismProperty.of_isPullback hqs hq.2.2.2.1)
  have hrs : Surjective r.hom.hom.left :=
    MorphismProperty.of_isPullback hPS (MorphismProperty.of_isPullback hqs hq.2.2.2.2.1)
  have hrl : LocallyOfFinitePresentation r.hom.hom.left :=
    MorphismProperty.of_isPullback hPS (MorphismProperty.of_isPullback hqs hq.2.2.2.2.2)
  have hmP := geometric_preimage_maximal (G := GK) (Q := QK) (P := P) (T := M)
    hGK hZker hZcent hP hrf hrl hM
  have he : F.map p ≫ j ≫ M.inclusion = TK.inclusion ≫ qK := by
    rw [hj]
    exact (F.map_comp p A.inclusion).symm.trans
      ((congrArg F.map hp).trans (F.map_comp T.inclusion q))
  have hTP : IsSubgroupOf TK P := ⟨pullback.lift TK.inclusion (F.map p ≫ j) (by
    simpa only [Category.assoc] using he.symm), pullback.lift_fst _ _ _⟩
  obtain ⟨i, hi⟩ := hmT.2 P hmP.1 hTP
  have hR : (i ≫ F.map p) ≫ AK.inclusion = r ≫ M.inclusion := by
    change i ≫ TK.inclusion = P.inclusion at hi
    have hf : F.map p ≫ AK.inclusion = TK.inclusion ≫ qK := by
      change F.map p ≫ F.map A.inclusion = F.map T.inclusion ≫ F.map q
      rw [← F.map_comp, ← F.map_comp, hp]
    rw [Category.assoc, hf, ← Category.assoc, hi, hr]
  letI : Smooth M.group.X.hom :=
    (torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup M) hM.1).1
  letI : IsReduced M.group.X.left := isReduced_of_smooth_over_field M.group.X.hom
  obtain ⟨f, hf⟩ := factors_of_range_subset M.inclusion.hom.hom
    AK.inclusion.hom.hom AK.isClosedImmersion (by
      rintro y ⟨x, rfl⟩
      obtain ⟨a, ha⟩ := hrs.1 x
      have h := congrArg (fun v : P.group ⟶ QK.val => v.hom.hom.left a) hR
      refine ⟨(i ≫ F.map p).hom.hom.left a, ?_⟩
      change ((i ≫ F.map p).hom.hom.left ≫ AK.inclusion.hom.hom.left) a =
        (M.inclusion.hom.hom.left) x
      exact h.trans (by
        change (r.hom.hom.left ≫ M.inclusion.hom.hom.left) a = _
        rw [Scheme.Hom.comp_apply, ha]))
  obtain ⟨g, hg⟩ := factor_group_through_subgroup AK M.inclusion f hf
  refine ⟨hcA, hAK, fun S hS hAS => ?_⟩
  obtain ⟨v, hv⟩ := hAS
  have hh : IsSubgroupOf M S := ⟨g ≫ v, by rw [Category.assoc, hv, hg]⟩
  obtain ⟨w, hw⟩ := hM.2 S hS hh
  exact ⟨w ≫ g, by rw [Category.assoc, hg, hw]⟩

open private represented_quotient_of_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private scheme_kernel_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

theorem adjointTorusImage : AdjointTorusImage.{u} := by
  intro k _ G Q B T Z q D hG hq hT hmax j hj z hz
  let T₀ := closedSubgroupAlgebraicGroup T
  let B₀ := closedSubgroupAlgebraicGroup D.subgroup
  obtain ⟨I, p, i, hfac, hcan, -⟩ := schemeImageFactorization T₀ B₀ (j ≫ D.projection)
  let A : ClosedSubgroup D.subgroup.group := ⟨I.val, i, hfac.2.2.2.2.2⟩
  let AQ := subgroupOfSubgroup D.subgroup A
  have hi : p ≫ AQ.inclusion = T.inclusion ≫ q := by
    change p ≫ i ≫ D.subgroup.inclusion = _
    rw [← Category.assoc, hfac.1, Category.assoc, D.factor.1, ← Category.assoc, hj]
  have hAz := CentralFrobeniusDescent.torus_of_flat_surjective
    T₀ I p hT hfac.2.1 hfac.2.2.1
  have hAm := imageIsMaximal (A := AQ) (T := T) (Z := Z) (p := p) hq hG hmax hAz hi
  have hzc : IsClosedImmersion z.hom.hom.left := by
    letI := T.isClosedImmersion
    have hleft : z.hom.hom.left ≫ T.inclusion.hom.hom.left = Z.inclusion.hom.hom.left :=
      congrArg (fun a : Z.group ⟶ G.val => a.hom.hom.left) hz
    letI : IsClosedImmersion (z.hom.hom.left ≫ T.inclusion.hom.hom.left) :=
      hleft.symm ▸ Z.isClosedImmersion
    exact IsClosedImmersion.of_comp_isClosedImmersion z.hom.hom.left T.inclusion.hom.hom.left
  have hk : IsSchemeKernel p ⟨Z.group, z, hzc⟩ := by
    let Z₀ := closedSubgroupAlgebraicGroup Z
    apply scheme_kernel_of_points (A := T₀) (B := Z₀) (C := I) p z hzc
    intro R t
    change t ≫ p.hom.hom = 1 ↔ ∃ a : Points Z.group.X R, a ≫ z.hom.hom = t
    letI := AQ.isClosedImmersion
    letI := T.isClosedImmersion
    letI : Mono AQ.inclusion.hom.hom := Over.mono_of_mono_left _
    letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
    have he : p.hom.hom ≫ AQ.inclusion.hom.hom = T.inclusion.hom.hom ≫ q.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hi
    rw [← cancel_mono AQ.inclusion.hom.hom, MonObj.one_comp, Category.assoc, he,
      ← Category.assoc, ← schemeKernel_sections hq.2.1]
    change (∃ a : Points Z.group.X R, a ≫ Z.inclusion.hom.hom = t ≫ T.inclusion.hom.hom) ↔ _
    have hz' : z.hom.hom ≫ T.inclusion.hom.hom = Z.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map hz
    simp only [← hz', ← Category.assoc, cancel_mono]
  exact ⟨A, p, hzc, hAz, hAm, hfac, hcan, represented_quotient_of_kernel
    (G := T₀) (Q := I) p ⟨_, z, hzc⟩ hk hfac.2.1 hfac.2.2.1 hfac.2.2.2.1⟩

open private pushRadical pushSubgroup transported_kernel projection_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
open private limitSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private geometricMaximal_of_maximal isKBorel_iff_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private isSplitTorus_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags

open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.StandardParabolicLevi (IsContractingRadical)
open Specs.BorelsAndChambers (contractingSubgroup)

private theorem isIso_of_fieldExtension (K : Type u) [Field K] [Algebra k K]
    {X Y : GroupScheme k} (f : X ⟶ Y) (h : IsIso ((groupBaseChange k K).map f)) :
    IsIso f := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  let F' := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  letI : IsIso ((groupBaseChange k K).map f) := h
  have hi : IsIso ((baseChange k K).map f.hom.hom).left :=
    F'.map_isIso ((groupBaseChange k K).map f)
  have hp := baseChangeMapPullback (K := K) f.hom.hom
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst Y.X.hom (fieldSpecMap k K)) := by
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  letI : IsIso (F.map f) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme) hp hq hi
  let J := Over.forget (Spec (CommRingCat.of k))
  letI : IsIso (J.map f.hom.hom) := ‹IsIso (F.map f)›
  letI : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom J
  let e : X ≅ Y := Grp.mkIso' (asIso f.hom.hom)
  have he : e.hom = f := Grp.hom_ext _ _ rfl
  exact he ▸ e.isIso_hom

private theorem pushRadicalBaseChange {A C : AffineAlgebraicGroup k}
    (e : A.val ≅ C.val) (R : ClosedSubgroup C.val)
    (hR : ∃ c : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map R.inclusion).hom.hom.left,
      IsUnipotentRadical (GeometricGroup C) (baseChangedSubgroup (AlgebraicClosure k) R c)) :
    ∃ c : IsClosedImmersion ((groupBaseChange k (AlgebraicClosure k)).map
        (pushSubgroup R e.symm).inclusion).hom.hom.left,
      IsUnipotentRadical (GeometricGroup A)
        (baseChangedSubgroup (AlgebraicClosure k) (pushSubgroup R e.symm) c) := by
  obtain ⟨c, hr⟩ := hR
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let Y := pushSubgroup R e.symm
  let YK := pushSubgroup (baseChangedSubgroup K R c) (F.mapIso e.symm)
  have hYK := pushRadical (B := GeometricGroup A) (F.mapIso e.symm) hr
  have hh : F.map Y.inclusion = YK.inclusion := F.map_comp R.inclusion e.inv
  have h : IsClosedImmersion (F.map Y.inclusion).hom.hom.left := hh.symm ▸ YK.isClosedImmersion
  refine ⟨h, ?_⟩
  let YK' := baseChangedSubgroup K Y h
  have he : YK' = YK := by
    change Specs.ClosedSubgroup.mk (F.obj R.group) (F.map Y.inclusion) h =
      Specs.ClosedSubgroup.mk (F.obj R.group) YK.inclusion YK.isClosedImmersion
    congr 1
  change IsUnipotentRadical (GeometricGroup A) YK'
  rw [he]
  exact hYK

private theorem isIso_torus_to_limit {B : ClosedSubgroup G.val} {T : ClosedSubgroup B.group}
    {c : Specs.CharacterDescent.Cocharacter G.val} (D : LimitDecomposition c)
    (e : B.group ≅ D.parabolic.group) (hG : IsReductive G) (hB : IsKBorel B)
    (hTm : IsGeometricallyMaximal (subgroupOfSubgroup B T)) (hD : IsContractingRadical D) :
    IsIso (T.inclusion ≫ e.hom ≫ D.limit) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let GK := GeometricGroup G
  let C := closedSubgroupAlgebraicGroup D.parabolic
  let A := closedSubgroupAlgebraicGroup B
  let U := pushSubgroup (contractingSubgroup D) e.symm
  let q₁ := e.hom ≫ D.limit
  let s₁ := D.sectionMap ≫ e.inv
  have hs₁ : s₁ ≫ q₁ = 𝟙 _ := by simp [s₁, q₁, D.section_limit]
  have hk₁ : IsSchemeKernel q₁ U := transported_kernel e (Iso.refl _)
    (by simp [U, pushSubgroup]) D.isKernel
  obtain ⟨cu, hu⟩ := pushRadicalBaseChange (A := A) (C := C) e
    (contractingSubgroup D) hD.2
  let UK := baseChangedSubgroup K U cu
  have hk₁K : IsSchemeKernel (F.map q₁) UK := baseChangeKernelSquare q₁ U.inclusion hk₁
  obtain ⟨cb, hb⟩ := hB
  obtain ⟨ct, ht⟩ := hTm
  let BK := baseChangedSubgroup K B cb
  let TK := baseChangedSubgroup K (subgroupOfSubgroup B T) ct
  have hTK : IsMaximalTorus TK := ht
  have hTB : IsSubgroupOf TK BK := ⟨F.map T.inclusion, (F.map_comp T.inclusion B.inclusion).symm⟩
  have hGK := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  obtain ⟨_, _, _, _, _, _, hdec⟩ := RootData.BorelPositivity.borelPositivity GK hGK TK
    (isSplitTorus_of_torus (closedSubgroupAlgebraicGroup (G := GK) TK) hTK.1)
    (geometricMaximal_of_maximal GK TK hTK)
  obtain ⟨R, j, q₂, hR, _, hj, hs₂, hk₂, _, _⟩ :=
    hdec BK ((isKBorel_iff_of_isAlgClosed GK BK).mpr hb) hTB
  have hj' : j = F.map T.inclusion := by
    letI := BK.isClosedImmersion
    letI : Mono BK.inclusion.hom.hom := Over.mono_of_mono_left _
    let F' := Grp.forget (SchemeOver K)
    apply Grp.hom_ext
    apply (cancel_mono BK.inclusion.hom.hom).mp
    exact congrArg F'.map (hj.trans (F.map_comp T.inclusion B.inclusion))
  obtain ⟨er, her⟩ := subgroupOf_mutual_iso
    (hu.2.2 R hR.1 hR.2.1) (hR.2.2 UK hu.1 hu.2.1)
  have hk₂' : IsSchemeKernel q₂ UK := by
    have h := transported_kernel (Iso.refl BK.group) er.symm (by
      simp only [Iso.refl_hom, Category.comp_id]
      rw [← her, Iso.symm_hom, Iso.inv_hom_id_assoc]) hk₂
    simpa only [Iso.refl_hom, Category.id_comp] using h
  have hs₁K : F.map s₁ ≫ F.map q₁ = 𝟙 _ := by rw [← F.map_comp, hs₁, F.map_id]
  obtain ⟨i, hi⟩ := projection_iso hk₂' hk₁K hs₂ hs₁K
  have hi' : F.map (T.inclusion ≫ q₁) = i.hom := by
    rw [F.map_comp, ← hj', ← hi, ← Category.assoc, hs₂]
    exact Category.id_comp i.hom
  exact isIso_of_fieldExtension K _ (hi'.symm ▸ i.isIso_hom)

private theorem kernel_comp_iso {k : Type u} [Field k]
    {X Y V : GroupScheme k} {U : ClosedSubgroup X} {p : X ⟶ Y}
    (hp : IsSchemeKernel p U) (e : Y ≅ V) :
    IsSchemeKernel (p ≫ e.hom) U := by
  let F := Grp.forget (SchemeOver k)
  apply hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (F.mapIso e)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change F.map p ≫ F.map e.hom = 𝟙 _ ≫ F.map (p ≫ e.hom)
    rw [Category.id_comp, F.map_comp]
  · change η[Y.X] ≫ e.hom.hom.hom = 𝟙 _ ≫ η[V.X]
    rw [Category.id_comp, IsMonHom.one_hom]

private theorem quotientWithTorusSection {k : Type u} [Field k]
    {G : AffineAlgebraicGroup k} {U T : ClosedSubgroup G.val}
    {C : GroupScheme k} (p : G.val ⟶ C)
    (hp : IsSchemeKernel p U) (hsm : Smooth p.hom.hom.left)
    (e : T.group ≅ C) (he : T.inclusion ≫ p = e.hom) :
    ∃ q : G.val ⟶ T.group, IsFppfGroupQuotient (G := G)
      (Q := closedSubgroupAlgebraicGroup T) U q ∧ T.inclusion ≫ q = 𝟙 _ := by
  let q := p ≫ e.inv
  have hq : T.inclusion ≫ q = 𝟙 T.group := by
    rw [← Category.assoc T.inclusion p e.inv, he]
    exact e.hom_inv_id
  have hk : IsSchemeKernel q U := kernel_comp_iso hp e.symm
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsIso (F.map e.inv) := F.map_isIso e.inv
  letI : Smooth (F.map p) := hsm
  have hs : Smooth q.hom.hom.left := by
    change Smooth (F.map (p ≫ e.inv))
    rw [F.map_comp]
    infer_instance
  letI := hs
  have hsurj : Surjective q.hom.hom.left := by
    refine ⟨fun y => ⟨T.inclusion.hom.hom.left y, ?_⟩⟩
    exact congrArg (fun f : T.group ⟶ T.group => f.hom.hom.left y) hq
  exact ⟨q, represented_quotient_of_kernel (G := G)
    (Q := closedSubgroupAlgebraicGroup T) q U hk inferInstance hsurj inferInstance, hq⟩

theorem borelTorusQuotient : BorelTorusQuotient.{u} := by
  intro k _ G B hG hB T hTm
  have hpar : Specs.BorelProper.IsParabolic G B := by
    refine ⟨hG, groundBorelSmooth hB, ?_⟩
    obtain ⟨c, hc⟩ := hB
    exact ⟨c, _, hc, 𝟙 _, Category.id_comp _⟩
  obtain ⟨c, D, e, U, i, L, j, _, _, _, hk, _, _, hD, hU, hsplit⟩ :=
    Relative.Parabolics.rationalParabolics.1 G B hpar
  let A := closedSubgroupAlgebraicGroup B
  let p : A.val ⟶ D.centralizer.group := e.hom ≫ D.limit
  have hiso : IsIso (T.inclusion ≫ p) := isIso_torus_to_limit (T := T) D e hG hB hTm hD
  let eT := asIso (T.inclusion ≫ p)
  let V := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : Smooth (V.map D.limit) := limitSmooth D hD.1.1.1
  letI : IsIso (V.map e.hom) := V.map_isIso e.hom
  have hs : Smooth p.hom.hom.left := by
    change Smooth (V.map (e.hom ≫ D.limit))
    rw [V.map_comp]
    infer_instance
  obtain ⟨q, hq, hT⟩ := quotientWithTorusSection (G := A) (T := T) p hk hs eT rfl
  exact ⟨U, q, hU, hsplit, hq, hT⟩


theorem borelVanishingWithInducedQuotient : BorelVanishingWithInducedQuotient.{u} := by
  intro k S _ _ _ _ G B hG hB U hU T q hq I _ E _ _ _ _ W hW P hP e
  have hBsm := groundBorelSmooth hB
  have hpar : Specs.BorelProper.IsParabolic G B := by
    refine ⟨hG, hBsm, ?_⟩
    obtain ⟨c, hc⟩ := hB
    exact ⟨c, _, hc, 𝟙 _, Category.id_comp _⟩
  obtain ⟨c, D, e₀, U₀, i, L, j, _, _, _, _, _, _, _, hU₀, hsplit⟩ :=
    Relative.Parabolics.rationalParabolics.1 G B hpar
  obtain ⟨eU, _⟩ := subgroupOf_mutual_iso (hU.2.2 U₀ hU₀.1 hU₀.2.1)
    (hU₀.2.2 U hU.1 hU.2.1)
  obtain ⟨e⟩ := e
  have hQ : ∀ x : groupH1 k T.val.X S, x = groupBasepoint k T.val.X S :=
    vanishingOfGroupIso e.symm (WeilHilbert90.product_vanishing k S I E W hW P hP)
  have hs := smoothQuotient (B := closedSubgroupAlgebraicGroup B) U q hq hU.1.1
  exact schemeExtensionVanishing (B := closedSubgroupAlgebraicGroup B) U q hq.1
    (smoothSurjectivePoints (S := S) (B := closedSubgroupAlgebraicGroup B)
      (T := T) q hs hq.2.2.1) hBsm
    (vanishingOfGroupIso eU.symm (splitUnipotentVanishing k S _ hsplit)) hQ

end BorelImage

section Pinning

open Specs.Pinning (PinnedGroup SimpleRoot transportCharacter pinGraph)
open Specs.RootGroups (AdditiveLine)

theorem pinnedSimpleRootPermutation : PinnedSimpleRootPermutation.{u} := by
  classical
  intro k _ L P
  have hfinite := RootData.CharacterPairing.finiteAbsoluteRoots P.pair.G P.pair.T P.pair.split
  letI : Finite (Specs.AbstractPairing.Root P.pair.T) := hfinite.to_subtype
  refine ⟨Finite.of_injective Subtype.val Subtype.val_injective, ?_⟩
  have hex (f : Aut P) (α : SimpleRoot P.pair) :
      ∃ β : SimpleRoot P.pair, β.val.val = transportCharacter f.asIso.hom.torus α.val.val := by
    let x := (α.val.val, (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion)
    let y := (transportCharacter f.asIso.hom.torus x.1, x.2 ≫ f.asIso.hom.group.hom)
    have hmem : y ∈ pinGraph P := by
      rw [← f.asIso.hom.pin_comm]
      exact ⟨x, ⟨α, rfl⟩, rfl⟩
    obtain ⟨β, hβ⟩ := hmem
    exact ⟨β, congrArg Prod.fst hβ⟩
  choose r hr using hex
  have heq {a b : SimpleRoot P.pair} (h : a.val.val = b.val.val) : a = b :=
    Subtype.ext (Subtype.ext h)
  have hone (α : SimpleRoot P.pair) : r 1 α = α := by
    apply heq
    rw [hr]
    change 𝟙 _ ≫ α.val.val = α.val.val
    exact Category.id_comp _
  have hmul (f g : Aut P) (α : SimpleRoot P.pair) : r (f * g) α = r f (r g α) := by
    apply heq
    rw [hr, hr, hr]
    change (f.asIso.hom.torus.inv ≫ g.asIso.hom.torus.inv) ≫ α.val.val =
      f.asIso.hom.torus.inv ≫ g.asIso.hom.torus.inv ≫ α.val.val
    exact Category.assoc _ _ _
  let act (f : Aut P) : Equiv.Perm (SimpleRoot P.pair) :=
    { toFun := r f
      invFun := r f⁻¹
      left_inv := fun α => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun α => by rw [← hmul, mul_inv_cancel, hone] }
  refine ⟨{ toFun := act, map_one' := ?_, map_mul' := ?_ }, hr⟩
  · apply Equiv.ext
    exact hone
  · intro f g
    apply Equiv.ext
    exact hmul f g

end Pinning


section AdjointCharacters

open Specs.AdjointCocharacters (coordinateHopfMap coordinateHopfIso)
local notation "coordinateAlgebra" => Specs.AdjointCocharacters.coordinateHopf
open Specs.AutomorphismSequence (groupSections forgetPinning)
open Specs.CentralTorus (IsSchemeCentre)
open Specs.Fppf (IsFppf)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.CharacterDescent (Character GeometricCharacters)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open Specs.Pinning (PinnedGroup SimpleRoot transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.SmoothnessAndIsogenies (pullbackCharacter)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private extendedGroupIso extendedSpecIso_natural specGroupMap_comp specGroupMap_injective
  tensorMap_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private coordinatePresentationMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private baseChangeMapPullback baseChangeKernelSquare
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private centre_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem extendedGroupIso_natural {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    specGroupMap (extendedHopfMap K f) ≫ (extendedGroupIso K A).hom =
      (extendedGroupIso K B).hom ≫ (groupBaseChange k K).map (specGroupMap f) :=
  Grp.hom_ext _ _ (extendedSpecIso_natural K f)

private def extendedCoordinateIso (G : AffineAlgebraicGroup k) :
    specGroup (extendedHopf K (coordinateAlgebra G)) ≅ (groupBaseChange k K).obj G.val :=
  extendedGroupIso K (coordinateAlgebra G) ≪≫
    (groupBaseChange k K).mapIso (coordinateHopfIso G)

private theorem extendedCoordinateIso_natural {G H : AffineAlgebraicGroup k} (f : G.val ⟶ H.val) :
    specGroupMap (extendedHopfMap K (coordinateHopfMap f)) ≫ (extendedCoordinateIso (K := K) H).hom =
      (extendedCoordinateIso (K := K) G).hom ≫ (groupBaseChange k K).map f := by
  let F := groupBaseChange k K
  change _ ≫ (extendedGroupIso K (coordinateAlgebra H)).hom ≫ F.map (coordinateHopfIso H).hom =
    (extendedGroupIso K (coordinateAlgebra G)).hom ≫ F.map (coordinateHopfIso G).hom ≫ F.map f
  have hf : specGroupMap (coordinateHopfMap f) ≫ (coordinateHopfIso H).hom =
      (coordinateHopfIso G).hom ≫ f := by
    rw [coordinatePresentationMap]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, extendedGroupIso_natural, Category.assoc, ← F.map_comp, hf, F.map_comp]

private theorem extendedCoordinateIso_comm {G G₀ H H₀ : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (f₀ : G₀.val ⟶ H₀.val)
    (eG : extendedHopf K (coordinateAlgebra G₀) ≅ extendedHopf K (coordinateAlgebra G))
    (eH : extendedHopf K (coordinateAlgebra H₀) ≅ extendedHopf K (coordinateAlgebra H))
    (h : eH.hom ≫ extendedHopfMap K (coordinateHopfMap (G := G) (H := H) f) =
      extendedHopfMap K (coordinateHopfMap (G := G₀) (H := H₀) f₀) ≫ eG.hom) :
    let E (X Y : AffineAlgebraicGroup k)
        (e : extendedHopf K (coordinateAlgebra Y) ≅ extendedHopf K (coordinateAlgebra X)) :=
      (extendedCoordinateIso (K := K) X).symm ≪≫
        (hopfSpec (CommRingCat.of K)).mapIso e.op ≪≫ extendedCoordinateIso (K := K) Y
    (E G G₀ eG).hom ≫ (groupBaseChange k K).map f₀ =
      (groupBaseChange k K).map f ≫ (E H H₀ eH).hom := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Iso.op_hom]
  rw [Category.assoc, Category.assoc, ← extendedCoordinateIso_natural f₀]
  have hh := congrArg (fun a => specGroupMap a) h
  rw [specGroupMap_comp, specGroupMap_comp] at hh
  change specGroupMap (extendedHopfMap K (coordinateHopfMap f)) ≫
    (hopfSpec (CommRingCat.of K)).map eH.hom.op =
    (hopfSpec (CommRingCat.of K)).map eG.hom.op ≫
      specGroupMap (extendedHopfMap K (coordinateHopfMap f₀)) at hh
  rw [← Category.assoc ((hopfSpec (CommRingCat.of K)).map eG.hom.op),
    ← hh, Category.assoc, ← Category.assoc (extendedCoordinateIso (K := K) G).inv]
  have hn := extendedCoordinateIso_natural (K := K) f
  have hm :
      (extendedCoordinateIso (K := K) G).inv ≫ specGroupMap (extendedHopfMap K (coordinateHopfMap f)) =
        (groupBaseChange k K).map f ≫ (extendedCoordinateIso (K := K) H).inv := by
    rw [← cancel_mono (extendedCoordinateIso (K := K) H).hom, Category.assoc,
      Category.assoc, hn, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hm, Category.assoc]

private theorem baseChangeFppf {X Y : GroupScheme k} (p : X ⟶ Y) (hp : IsFppf p.hom.hom.left) :
    IsFppf ((groupBaseChange k K).map p).hom.hom.left := by
  have h := baseChangeMapPullback (K := K) p.hom.hom
  exact ⟨MorphismProperty.of_isPullback h.flip hp.1, MorphismProperty.of_isPullback h.flip hp.2.1,
    MorphismProperty.of_isPullback h.flip hp.2.2⟩

private theorem baseChangeTorusKernel {G T Y : GroupScheme k}
    (i : T ⟶ G) (p : T ⟶ Y) (hi : IsClosedImmersion i.hom.hom.left)
    {Z : ClosedSubgroup G} (hz : IsSchemeCentre Z) (z : Z.group ⟶ T)
    (hzi : z ≫ i = Z.inclusion)
    (hk : IsPullback z.hom.hom (toUnit _) p.hom.hom η[Y.X])
    {S : SchemeOver K} (x : S ⟶ ((groupBaseChange k K).obj T).X) :
    x ≫ ((groupBaseChange k K).map p).hom.hom = 1 ↔
      Centralizes (𝟙 ((groupBaseChange k K).obj G))
        (x ≫ ((groupBaseChange k K).map i).hom.hom) := by
  let F := groupBaseChange k K
  let U := Grp.forget (SchemeOver K)
  obtain ⟨hc, hzK⟩ := centre_baseChange hz K
  have hkK := baseChangeKernelSquare (K := K) p z hk
  let hcb : IsClosedImmersion (F.map i).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) i.hom.hom).flip hi
  letI := hcb
  letI : Mono (F.map i).hom.hom := Over.mono_of_mono_left _
  have he : (F.map z).hom.hom ≫ (F.map i).hom.hom = (F.map Z.inclusion).hom.hom := by
    change U.map (F.map z) ≫ U.map (F.map i) = U.map (F.map Z.inclusion)
    rw [← U.map_comp, ← F.map_comp, hzi]
  change _ ↔ Centralizes (𝟙 (F.obj G)) (x ≫ (F.map i).hom.hom)
  refine (show _ ↔ ∃ a : S ⟶ (F.obj Z.group).X, a ≫ (F.map z).hom.hom = x from ?_).trans
    ((hzK S (x ≫ (F.map i).hom.hom)).trans ?_).symm
  · constructor
    · intro hx
      change x ≫ (F.map p).hom.hom = toUnit S ≫ η[(F.obj Y).X] at hx
      exact ⟨hkK.lift x (toUnit S) hx, hkK.lift_fst _ _ _⟩
    · rintro ⟨v, rfl⟩
      change (v ≫ (F.map z).hom.hom) ≫ (F.map p).hom.hom = toUnit S ≫ η[(F.obj Y).X]
      rw [Category.assoc, hkK.w, ← Category.assoc, comp_toUnit]
  · change (∃ a : S ⟶ (F.obj Z.group).X,
      a ≫ (F.map Z.inclusion).hom.hom = x ≫ (F.map i).hom.hom) ↔ _
    simp only [← he, ← Category.assoc, cancel_mono]

private theorem centralizesIso {G H : GroupScheme K} (e : G ≅ H) {S : SchemeOver K}
    (x : S ⟶ G.X) :
    Centralizes (𝟙 G) x ↔ Centralizes (𝟙 H) (x ≫ e.hom.hom.hom) := by
  simp only [centralizes_iff]
  change (∀ (V : SchemeOver K) (a : V ⟶ S) (b : V ⟶ G.X), Commute (a ≫ x) (b ≫ 𝟙 _)) ↔
    (∀ (V : SchemeOver K) (a : V ⟶ S) (b : V ⟶ H.X),
      Commute (a ≫ x ≫ e.hom.hom.hom) (b ≫ 𝟙 _))
  simp only [Category.comp_id]
  let e₁ := yonedaGrp.mapIso e
  have hi : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X :=
    congrArg (Grp.forget (SchemeOver K)).map e.inv_hom_id
  have hj : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
    congrArg (Grp.forget (SchemeOver K)).map e.hom_inv_id
  constructor
  · intro h V a b
    have h' := (h V a (b ≫ e.inv.hom.hom)).map (e₁.hom.app (op V)).hom
    change Commute ((a ≫ x) ≫ e.hom.hom.hom) ((b ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) at h'
    simpa only [Category.assoc, hi, Category.comp_id] using h'
  · intro h V a b
    have h' := (h V a (b ≫ e.hom.hom.hom)).map (e₁.inv.app (op V)).hom
    change Commute ((a ≫ x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom)
      ((b ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) at h'
    simpa only [Category.assoc, hj, Category.comp_id] using h'

open private descends_iso_of_locallySurjective groupSectionsMap groupSectionsMap_locallySurjective
  groupSections_isSheaf groupSectionsFullyFaithful
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private theorem quotientIsoOfKernel {X Y X' Y' : GroupScheme K}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (e : X ≅ X')
    (hp : IsFppf p.hom.hom.left) (hp' : IsFppf p'.hom.hom.left)
    (hker : ∀ (S : SchemeOver K) (x : S ⟶ X.X),
      x ≫ p.hom.hom = 1 ↔ (x ≫ e.hom.hom.hom) ≫ p'.hom.hom = 1) :
    ∃ d : Y ≅ Y', p ≫ d.hom = e.hom ≫ p' := by
  let ff := groupSectionsFullyFaithful (k := K)
  let F := yonedaGrp (C := SchemeOver K) ⋙
      (Functor.whiskeringRight _ _ _).obj Specs.Fppf.liftGroups.{u,u+1}
  let e' := F.mapIso e
  have hk (S : (SchemeOver K)ᵒᵖ) (x y : (groupSections X).obj S) :
      (groupSectionsMap p).app S x = (groupSectionsMap p).app S y ↔
      (groupSectionsMap p').app S (e'.hom.app S x) =
        (groupSectionsMap p').app S (e'.hom.app S y) := by
    let v := ((groupSectionsMap p).app S).hom
    let w := (((e'.hom ≫ groupSectionsMap p').app S)).hom
    change v x = v y ↔ w x = w y
    rw [← div_eq_one (a := v x), ← div_eq_one (a := w x), ← map_div v, ← map_div w]
    change ULift.up ((x / y).down ≫ p.hom.hom) = ULift.up 1 ↔
      ULift.up (((x / y).down ≫ e.hom.hom.hom) ≫ p'.hom.hom) = ULift.up 1
    simpa only [ULift.up_inj] using hker S.unop (x / y).down
  obtain ⟨d, hd⟩ := descends_iso_of_locallySurjective (groupSectionsMap p)
    (groupSectionsMap p') e' (groupSectionsMap_locallySurjective p hp)
    (groupSectionsMap_locallySurjective p' hp') (groupSections_isSheaf Y)
    (groupSections_isSheaf Y') hk
  refine ⟨ff.preimageIso d, ff.map_injective ?_⟩
  change F.map (p ≫ ff.preimage d.hom) = F.map (e.hom ≫ p')
  rw [Functor.map_comp, Functor.map_comp]
  have hpre : F.map (ff.preimage d.hom) = d.hom := ff.map_preimage d.hom
  rw [hpre]
  exact hd

open Specs.DiagonalizableGroups (diagonalRestriction diagonalClosedInclusion FGAbelianGroup groupAlgebraMap)
open Specs.SchemeCentre (rootLattice)
open private monomialCharacter monomialCharacter_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private theorem splitTorusProjection {L : AdditiveLine k} (P : PinnedGroup L) :
    let T := P.pair.T
    let N := rootLattice T
    ∃ (p : T.group ⟶ specGroup (groupAlgebra k N))
      (Z : ClosedSubgroup P.pair.G.val) (z : Z.group ⟶ T.group),
      IsSchemeCentre Z ∧ z ≫ T.inclusion = Z.inclusion ∧ IsFppf p.hom.hom.left ∧
      IsPullback z.hom.hom (toUnit _) p.hom.hom η[(specGroup (groupAlgebra k N)).X] ∧
      ∀ m : N, p ≫ monomialCharacter (k := k) m = m.val := by
  let T := P.pair.T
  let M := Character T.group
  let N := rootLattice T
  let Y := specGroup (groupAlgebra k N)
  obtain ⟨hfg, e, he, hc, hCentre, _⟩ :=
    RootData.SchemeCentre.schemeCentre P.pair.G P.pair.reductive T P.pair.split P.pair.maximal
  letI : Group.FG M := hfg
  let i := diagonalClosedInclusion k N
  let p₀ := diagonalRestriction k N
  let p := e.inv ≫ p₀
  let Z : ClosedSubgroup P.pair.G.val := ⟨specGroup (groupAlgebra k (M ⧸ N)), i ≫ e.hom ≫ T.inclusion, hc⟩
  let z := i ≫ e.hom
  obtain ⟨c, hf, hs, hl, hk, _⟩ :=
    LinearAlgebraicGroups.DiagonalizableGroups.diagonalRestrictionKernelAndQuotient k M N
  let F := Grp.forget (SchemeOver k)
  let V := F ⋙ Over.forget (Spec (CommRingCat.of k))
  have hp : IsFppf p.hom.hom.left := by
    haveI : IsIso (V.map e.inv) := V.map_isIso e.inv
    letI : Flat (V.map p₀) := hf
    letI : Surjective (V.map p₀) := hs
    letI : LocallyOfFinitePresentation (V.map p₀) := hl
    change IsFppf (V.map (e.inv ≫ p₀))
    rw [V.map_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hk' : IsPullback z.hom.hom (toUnit Z.group.X) p.hom.hom η[Y.X] := by
    apply hk.of_iso (Iso.refl _) (F.mapIso e) (Iso.refl _) (Iso.refl _)
    · change F.map i ≫ F.map e.hom = 𝟙 _ ≫ F.map z
      rw [Category.id_comp, ← F.map_comp]
    · exact toUnit_unique _ _
    · change F.map p₀ ≫ 𝟙 _ = F.map e.hom ≫ F.map p
      rw [Category.comp_id, ← F.map_comp, show e.hom ≫ p = p₀ from Iso.hom_inv_id_assoc e p₀]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨p, Z, z, hCentre, Category.assoc _ _ _, hp, hk', ?_⟩
  intro m
  change (e.inv ≫ p₀) ≫ monomialCharacter m = m.val
  have hm : p₀ ≫ monomialCharacter (k := k) m =
      monomialCharacter (k := k) m.val := monomialCharacter_natural N.subtype m
  rw [Category.assoc, hm]
  exact (congrArg (e.inv ≫ ·) (he m.val).symm).trans (Iso.inv_hom_id_assoc e _)


private theorem coordinateHopfMap_comp {G H J : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (g : H.val ⟶ J.val) :
    coordinateHopfMap (G := G) (H := J) (f ≫ g) =
      coordinateHopfMap (G := H) (H := J) g ≫ coordinateHopfMap (G := G) (H := H) f := by
  apply specGroupMap_injective
  simp only [specGroupMap_comp, coordinatePresentationMap, Category.assoc, Iso.inv_hom_id_assoc]

private def characterCoordinates {G : AffineAlgebraicGroup k} (χ : Character G.val) :
    groupAlgebra k IntegerCharacters ⟶ coordinateAlgebra G :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((coordinateHopfIso G).hom ≫ χ)).unop

private theorem characterCoordinates_spec {G : AffineAlgebraicGroup k} (χ : Character G.val) :
    specGroupMap (characterCoordinates χ) = (coordinateHopfIso G).hom ≫ χ :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _

private theorem characterCoordinates_comp {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (χ : Character H.val) :
    characterCoordinates (G := G) (f ≫ χ) = characterCoordinates χ ≫ coordinateHopfMap f := by
  apply specGroupMap_injective
  simp only [specGroupMap_comp, characterCoordinates_spec, coordinatePresentationMap,
    Category.assoc, Iso.inv_hom_id_assoc]

private theorem coordinateHopfMap_surjective {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (hf : IsClosedImmersion f.hom.hom.left) :
    Function.Surjective (coordinateHopfMap (G := G) (H := H) f).hom := by
  apply (hopfMapClosedImmersion k (coordinateHopfMap f)).mp
  rw [coordinatePresentationMap]
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsIso (F.map (coordinateHopfIso G).hom) := F.map_isIso _
  letI : IsIso (F.map (coordinateHopfIso H).inv) := F.map_isIso _
  letI : IsClosedImmersion (F.map f) := hf
  change IsClosedImmersion (F.map ((coordinateHopfIso G).hom ≫ f ≫ (coordinateHopfIso H).inv))
  rw [F.map_comp, F.map_comp]
  infer_instance

private theorem coordinateHopfMap_injective {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (hf : IsFppf f.hom.hom.left) :
    Function.Injective (coordinateHopfMap (G := G) (H := H) f).hom := by
  let g := coordinateHopfMap (G := G) (H := H) f
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsIso (F.map (coordinateHopfIso G).hom) := F.map_isIso _
  letI : IsIso (F.map (coordinateHopfIso H).inv) := F.map_isIso _
  letI : Flat (F.map f) := hf.1
  letI : Surjective (F.map f) := hf.2.1
  have h : Flat (F.map (specGroupMap g)) ∧ Surjective (F.map (specGroupMap g)) := by
    rw [coordinatePresentationMap, F.map_comp, F.map_comp]
    exact ⟨inferInstance, inferInstance⟩
  let j := CommRingCat.ofHom g.hom.toAlgHom.toRingHom
  have hff := (flat_and_surjective_SpecMap_iff j).mp h
  letI : Algebra (coordinateAlgebra H) (coordinateAlgebra G) := j.hom.toAlgebra
  letI : Module.FaithfullyFlat (coordinateAlgebra H) (coordinateAlgebra G) := hff
  exact FaithfulSMul.algebraMap_injective (coordinateAlgebra H) (coordinateAlgebra G)

open private extendedHopfMap_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem actionOnHopfQuotient {A A' B B' : HopfAlgebraCategory k}
    (i : A ⟶ B) (i' : A' ⟶ B') (g : A ⟶ A) (t : B ⟶ B)
    (a : extendedHopf K A ≅ extendedHopf K A')
    (b : extendedHopf K B ≅ extendedHopf K B')
    (hi : Function.Surjective i.hom)
    (hcomp : g ≫ i = i ≫ t)
    (hcomm : a.hom ≫ extendedHopfMap K i' = extendedHopfMap K i ≫ b.hom)
    (σ : Gal(K/k))
    (hact : ∀ y : extendedHopf K A,
      (SemilinearAction.scalarExtension (K := K) A').act σ (a.hom.hom y) =
        a.hom.hom ((extendedHopfMap K g).hom
          ((SemilinearAction.scalarExtension (K := K) A).act σ y)))
    (x : extendedHopf K B) :
    (SemilinearAction.scalarExtension (K := K) B').act σ (b.hom.hom x) =
      b.hom.hom ((extendedHopfMap K t).hom
        ((SemilinearAction.scalarExtension (K := K) B).act σ x)) := by
  let E := LinearAlgebraicGroups.CharacterDescent.extendedHopfFunctor (k := k) K
  have h : E.map g ≫ E.map i = E.map i ≫ E.map t := by
    rw [← E.map_comp, ← E.map_comp, hcomp]
  have hsurj : Function.Surjective (E.map i).hom :=
    tensorMap_surjective (K := K) i.hom.toAlgHom hi
  obtain ⟨y, hy⟩ := hsurj x
  let s := SemilinearAction.scalarExtension (k := k) (K := K) A
  let s' := SemilinearAction.scalarExtension (k := k) (K := K) A'
  let v := SemilinearAction.scalarExtension (k := k) (K := K) B
  let v' := SemilinearAction.scalarExtension (k := k) (K := K) B'
  have hm (z : _) : b.hom.hom ((E.map i).hom z) = (E.map i').hom (a.hom.hom z) :=
    (DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom hcomm) z).symm
  have hn (z : _) : (E.map i').hom (s'.act σ z) = v'.act σ ((E.map i').hom z) :=
    extendedHopfMap_equivariant K i' σ z
  have hk (z : _) : (E.map i).hom (s.act σ z) = v.act σ ((E.map i).hom z) :=
    extendedHopfMap_equivariant K i σ z
  have ht (z : _) : (E.map i).hom ((E.map g).hom z) = (E.map t).hom ((E.map i).hom z) :=
    DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom h) z
  change v'.act σ (b.hom.hom x) = b.hom.hom ((E.map t).hom (v.act σ x))
  calc
    _ = v'.act σ (b.hom.hom ((E.map i).hom y)) := congrArg (fun z => v'.act σ (b.hom.hom z)) hy.symm
    _ = v'.act σ ((E.map i').hom (a.hom.hom y)) := congrArg (v'.act σ) (hm y)
    _ = (E.map i').hom (s'.act σ (a.hom.hom y)) := (hn _).symm
    _ = (E.map i').hom (a.hom.hom ((E.map g).hom (s.act σ y))) :=
      congrArg (E.map i').hom (hact y)
    _ = b.hom.hom ((E.map i).hom ((E.map g).hom (s.act σ y))) := (hm _).symm
    _ = b.hom.hom ((E.map t).hom ((E.map i).hom (s.act σ y))) :=
      congrArg b.hom.hom (ht _)
    _ = b.hom.hom ((E.map t).hom (v.act σ ((E.map i).hom y))) :=
      congrArg (fun z => b.hom.hom ((E.map t).hom z)) (hk y)
    _ = _ := congrArg (fun z => b.hom.hom ((E.map t).hom (v.act σ z))) hy

private theorem twistedTorusAction {L : AdditiveLine k} {P : PinnedGroup L}
    {D : Specs.Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (F : PinnedTwist K D l B T) (σ : Gal(K/k))
    (x : extendedHopf K (coordinateAlgebra (closedSubgroupAlgebraicGroup P.pair.T))) :
    let T₀ := closedSubgroupAlgebraicGroup P.pair.T
    let T₁ := closedSubgroupAlgebraicGroup T
    let a := (l (F.outer σ)).asIso.hom.torus.inv
    (SemilinearAction.scalarExtension (K := K) (coordinateAlgebra T₁)).act σ
      (F.torusIso.hom.hom x) =
    F.torusIso.hom.hom ((extendedHopfMap K (coordinateHopfMap (G := T₀) (H := T₀) a)).hom
      ((SemilinearAction.scalarExtension (K := K) (coordinateAlgebra T₀)).act σ x)) := by
  let T₀ := closedSubgroupAlgebraicGroup P.pair.T
  let T₁ := closedSubgroupAlgebraicGroup T
  let a := (l (F.outer σ)).asIso.inv
  let r₀ := coordinateHopfMap (G := T₀) (H := P.pair.G) P.pair.T.inclusion
  let r₁ := coordinateHopfMap (G := T₁) (H := G) T.inclusion
  let g := coordinateHopfMap (G := P.pair.G) (H := P.pair.G) a.group.hom
  let t := coordinateHopfMap (G := T₀) (H := T₀) a.torus.hom
  have h₀ := congrArg (fun f : T₀.val ⟶ P.pair.G.val =>
      coordinateHopfMap (G := T₀) (H := P.pair.G) f) a.torus_comm
  have hleft : coordinateHopfMap (G := T₀) (H := P.pair.G)
        (P.pair.T.inclusion ≫ a.group.hom) = g ≫ r₀ :=
    coordinateHopfMap_comp (G := T₀) (H := P.pair.G) (J := P.pair.G)
      P.pair.T.inclusion a.group.hom
  have hright : coordinateHopfMap (G := T₀) (H := P.pair.G)
        (a.torus.hom ≫ P.pair.T.inclusion) = r₀ ≫ t :=
    coordinateHopfMap_comp (G := T₀) (H := T₀) (J := P.pair.G) a.torus.hom P.pair.T.inclusion
  have hi : Function.Surjective r₀.hom :=
    coordinateHopfMap_surjective (G := T₀) (H := P.pair.G) P.pair.T.inclusion P.pair.T.isClosedImmersion
  let f := (l (F.outer σ)).asIso.hom
  have ha : a = Specs.Pinning.PinnedIso.symm f := by
    apply (cancel_epi f).mp
    exact (l (F.outer σ)).asIso.hom_inv_id.trans (Groupoid.comp_inv f).symm
  have ht : a.torus.hom = f.torus.inv :=
    congrArg (fun v : P ⟶ P => v.torus.hom) ha
  exact (actionOnHopfQuotient r₀ r₁ g t F.groupIso F.torusIso hi
    (hleft.symm.trans (h₀.trans hright)) F.torusComm σ (F.twistedAction σ) x).trans
    (congrArg (fun v : T₀.val ⟶ T₀.val => F.torusIso.hom.hom
      ((extendedHopfMap K (coordinateHopfMap (G := T₀) (H := T₀) v)).hom
        ((SemilinearAction.scalarExtension (K := K) (coordinateAlgebra T₀)).act σ x))) ht)

private theorem extendedCharacterValue_comp {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (χ : Character H.val) :
    (extendedHopfMap K (coordinateHopfMap (G := G) (H := H) f)).hom (extendedCharacterValue K H χ) =
      extendedCharacterValue K G (f ≫ χ) := by
  let m := MonoidAlgebra.of k IntegerCharacters integerGenerator
  let g := coordinateHopfMap (G := G) (H := H) f
  have he : (characterCoordinates (G := G) (f ≫ χ)).hom m =
      g.hom ((characterCoordinates (G := H) χ).hom m) :=
    DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom
      (characterCoordinates_comp (G := G) (H := H) f χ)) m
  exact congrArg (fun a : coordinateAlgebra G => (1 : K) ⊗ₜ[k] a) he.symm

private theorem extendedCharacterValue_twist {L : AdditiveLine k} {P : PinnedGroup L}
    {D : Specs.Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (F : PinnedTwist K D l B T) (σ : Gal(K/k)) (χ : Character P.pair.T.group) :
    let T₀ := closedSubgroupAlgebraicGroup P.pair.T
    (SemilinearAction.scalarExtension (K := K) (coordinateAlgebra (closedSubgroupAlgebraicGroup T))).act σ
      (F.torusIso.hom.hom (extendedCharacterValue K T₀ χ)) =
    F.torusIso.hom.hom (extendedCharacterValue K T₀
      (transportCharacter (l (F.outer σ)).asIso.hom.torus χ)) := by
  let T₀ := closedSubgroupAlgebraicGroup P.pair.T
  let a := (l (F.outer σ)).asIso.hom.torus.inv
  let m := (characterCoordinates (G := T₀) χ).hom (MonoidAlgebra.of k _ integerGenerator)
  have hfixed : (SemilinearAction.scalarExtension (K := K) (coordinateAlgebra T₀)).act σ
      (extendedCharacterValue K T₀ χ) = extendedCharacterValue K T₀ χ :=
    congrArg (fun c : K => c ⊗ₜ[k] m) (map_one σ)
  change _ = F.torusIso.hom.hom (extendedCharacterValue K T₀ (a ≫ χ))
  calc
    _ = F.torusIso.hom.hom ((extendedHopfMap K (coordinateHopfMap (G := T₀) (H := T₀) a)).hom
        ((SemilinearAction.scalarExtension (K := K) (coordinateAlgebra T₀)).act σ
          (extendedCharacterValue K T₀ χ))) :=
      twistedTorusAction F σ (extendedCharacterValue K T₀ χ)
    _ = F.torusIso.hom.hom (extendedCharacterValue K T₀ (a ≫ χ)) :=
      (congrArg (fun z => F.torusIso.hom.hom
        ((extendedHopfMap K (coordinateHopfMap (G := T₀) (H := T₀) a)).hom z)) hfixed).trans
        (congrArg F.torusIso.hom.hom (extendedCharacterValue_comp (K := K) (G := T₀) (H := T₀) a χ))

private def coordinatesToSpectrum (T : AffineAlgebraicGroup k) {C : HopfAlgebraCategory k}
    (p : T.val ⟶ specGroup C) : C ⟶ coordinateAlgebra T :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage ((coordinateHopfIso T).hom ≫ p)).unop

private theorem coordinatesToSpectrum_spec (T : AffineAlgebraicGroup k) {C : HopfAlgebraCategory k}
    (p : T.val ⟶ specGroup C) :
    specGroupMap (coordinatesToSpectrum T p) = (coordinateHopfIso T).hom ≫ p :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _

private theorem quotientCoordinateComparison {T T₀ A : AffineAlgebraicGroup k}
    {C : HopfAlgebraCategory k}
    (p : T.val ⟶ A.val) (p₀ : T₀.val ⟶ specGroup C)
    (c : extendedHopf K (coordinateAlgebra T₀) ≅ extendedHopf K (coordinateAlgebra T))
    (e : (groupBaseChange k K).obj A.val ≅ (groupBaseChange k K).obj (specGroup C))
    (h : (groupBaseChange k K).map p ≫ e.hom =
        ((extendedCoordinateIso (K := K) T).inv ≫ specGroupMap c.hom ≫
          (extendedCoordinateIso (K := K) T₀).hom) ≫ (groupBaseChange k K).map p₀) :
    ∃ d : extendedHopf K C ≅ extendedHopf K (coordinateAlgebra A),
      d.hom ≫ extendedHopfMap K (coordinateHopfMap (G := T) (H := A) p) =
        extendedHopfMap K (coordinatesToSpectrum T₀ p₀) ≫ c.hom := by
  let F := groupBaseChange k K
  let C₀ := extendedGroupIso K C
  let C₁ := extendedCoordinateIso (K := K) A
  let E := C₁ ≪≫ e ≪≫ C₀.symm
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of K)
  let d := (ff.preimageIso E).unop
  have hd : specGroupMap d.hom ≫ C₀.hom = C₁.hom ≫ e.hom := by
    have hh : specGroupMap d.hom = E.hom := ff.map_preimage E.hom
    simp only [hh, E, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn : specGroupMap (extendedHopfMap K (coordinatesToSpectrum T₀ p₀)) ≫ C₀.hom =
      (extendedCoordinateIso (K := K) T₀).hom ≫ F.map p₀ := by
    rw [extendedGroupIso_natural, coordinatesToSpectrum_spec, F.map_comp]
    rfl
  refine ⟨d, specGroupMap_injective ?_⟩
  rw [specGroupMap_comp, specGroupMap_comp, ← cancel_mono C₀.hom]
  simp only [Category.assoc, hd, hn]
  rw [← Category.assoc _ C₁.hom, extendedCoordinateIso_natural, Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

private theorem rootCoordinate_pullback {T : AffineAlgebraicGroup k} {N : Type u} [CommGroup N]
    (p : T.val ⟶ specGroup (groupAlgebra k N)) (m : N) (χ : Character T.val)
    (h : p ≫ monomialCharacter (k := k) m = χ) :
    (extendedHopfMap K (coordinatesToSpectrum T p)).hom (1 ⊗ₜ[k] MonoidAlgebra.of k N m) =
      extendedCharacterValue K T χ := by
  let f := groupAlgebraMap k ((zpowersHom N m).comp MulEquiv.ulift.toMonoidHom)
  have he : characterCoordinates (G := T) χ = f ≫ coordinatesToSpectrum T p := by
    apply specGroupMap_injective
    rw [characterCoordinates_spec, specGroupMap_comp, coordinatesToSpectrum_spec, Category.assoc]
    exact congrArg ((coordinateHopfIso T).hom ≫ ·) h.symm
  have hg : f.hom (MonoidAlgebra.of k _ integerGenerator) = MonoidAlgebra.of k N m := by
    change MonoidAlgebra.mapDomainBialgHom k
      ((zpowersHom N m).comp MulEquiv.ulift.toMonoidHom) (MonoidAlgebra.single integerGenerator 1) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    congr 1
    exact zpow_one m
  change (1 : K) ⊗ₜ[k] (coordinatesToSpectrum T p).hom (MonoidAlgebra.of k N m) =
    (1 : K) ⊗ₜ[k] (characterCoordinates (G := T) χ).hom (MonoidAlgebra.of k _ integerGenerator)
  rw [he]
  change _ = (1 : K) ⊗ₜ[k] (coordinatesToSpectrum T p).hom (f.hom (MonoidAlgebra.of k _ integerGenerator))
  rw [hg]

open _root_.LinearAlgebraicGroups.CharacterDescent
  (baseChangeCharacterMap baseChangeCharacterMap_bijective monomialCharacterEquiv groupAlgebraBaseChange)
open private groupLikeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem pinnedAdjointBasis {L : AdditiveLine k} {P : PinnedGroup L}
    [Finite (SimpleRoot P.pair)] {D : Specs.Pinning.AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G A : AffineAlgebraicGroup k} {B T Z : ClosedSubgroup G.val}
    (F : PinnedTwist K D l B T)
    (r : Aut P →* Equiv.Perm (SimpleRoot P.pair))
    (hr : ∀ f α, (r f α).val.val = transportCharacter f.asIso.hom.torus α.val.val)
    (p : T.group ⟶ A.val) (hp : IsFppf p.hom.hom.left)
    (hz : IsSchemeCentre Z) (z : Z.group ⟶ T.group) (hzi : z ≫ T.inclusion = Z.inclusion)
    (hk : IsPullback z.hom.hom (toUnit _) p.hom.hom η[A.val.X]) :
    let T₀ := closedSubgroupAlgebraicGroup P.pair.T
    let T₁ := closedSubgroupAlgebraicGroup T
    ∃ b : PermutedCharacterBasis K (SimpleRoot P.pair) A (r.comp (l.toMonoidHom.comp F.outer)),
      (∀ α, (pullbackCharacter K (coordinateHopfMap (G := T₁) (H := A) p) (b.basis α).toMul).val =
        F.torusIso.hom.hom (extendedCharacterValue K T₀ α.val.val)) ∧
      Specs.CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateAlgebra A)) := by
  let T₀ := closedSubgroupAlgebraicGroup P.pair.T
  let T₁ := closedSubgroupAlgebraicGroup T
  let U := groupBaseChange k K
  let N := rootLattice P.pair.T
  let C := groupAlgebra k N
  let eT : U.obj T.group ≅ U.obj P.pair.T.group :=
    (extendedCoordinateIso (K := K) T₁).symm ≪≫
      (hopfSpec (CommRingCat.of K)).mapIso F.torusIso.op ≪≫ extendedCoordinateIso (K := K) T₀
  let eG : U.obj G.val ≅ U.obj P.pair.G.val :=
    (extendedCoordinateIso (K := K) G).symm ≪≫
      (hopfSpec (CommRingCat.of K)).mapIso F.groupIso.op ≪≫ extendedCoordinateIso (K := K) P.pair.G
  have hc : eT.hom ≫ U.map P.pair.T.inclusion = U.map T.inclusion ≫ eG.hom :=
    extendedCoordinateIso_comm (G := T₁) (G₀ := T₀) (H := G) (H₀ := P.pair.G)
      T.inclusion P.pair.T.inclusion F.torusIso F.groupIso F.torusComm
  obtain ⟨p₀, Z₀, z₀, hz₀, hzi₀, hp₀, hk₀, hroot⟩ := splitTorusProjection P
  have hker (S : SchemeOver K) (x : S ⟶ (U.obj T.group).X) :
      x ≫ (U.map p).hom.hom = 1 ↔
        (x ≫ eT.hom.hom.hom) ≫ (U.map p₀).hom.hom = 1 := by
    have he : eT.hom.hom.hom ≫ (U.map P.pair.T.inclusion).hom.hom =
        (U.map T.inclusion).hom.hom ≫ eG.hom.hom.hom :=
      congrArg (Grp.forget (SchemeOver K)).map hc
    exact (baseChangeTorusKernel T.inclusion p T.isClosedImmersion hz z hzi hk x).trans
      ((centralizesIso eG (x ≫ (U.map T.inclusion).hom.hom)).trans (by
        rw [Category.assoc, ← he, ← Category.assoc]
        exact (baseChangeTorusKernel P.pair.T.inclusion p₀ P.pair.T.isClosedImmersion
          hz₀ z₀ hzi₀ hk₀ (x ≫ eT.hom.hom.hom)).symm))
  obtain ⟨d, hd⟩ := quotientIsoOfKernel (U.map p) (U.map p₀) eT
    (baseChangeFppf p hp) (baseChangeFppf p₀ hp₀) hker
  obtain ⟨j, hj⟩ := quotientCoordinateComparison (T := T₁) (T₀ := T₀) (A := A)
    (C := C) p p₀ F.torusIso d hd
  obtain ⟨b, hb⟩ := AutomorphismSequence.simpleRootsBasis P D
  letI : Module.Finite ℤ (Additive N) := Module.Finite.of_basis b
  letI : Group.FG N := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  let m : FGAbelianGroup.{u} := ⟨CommGrpCat.of N, inferInstance⟩
  have hs : Specs.CharacterDescent.IsDiagonalizable C := ⟨m, ⟨Iso.refl C⟩⟩
  let cb := MulEquiv.ofBijective (baseChangeCharacterMap K C) (baseChangeCharacterMap_bijective K C hs)
  let e := ((monomialCharacterEquiv (M := N) k).trans cb).trans (groupLikeIso j)
  let bas := b.map e.toAdditive.toIntLinearEquiv
  let f := coordinateHopfMap (G := T₁) (H := A) p
  have hrb (α : SimpleRoot P.pair) :
      (pullbackCharacter K f (bas α).toMul).val =
        F.torusIso.hom.hom (extendedCharacterValue K T₀ α.val.val) := by
    let a := (b α).toMul
    have ha : (bas α).toMul.val = j.hom.hom (1 ⊗ₜ[k] MonoidAlgebra.of k N a) := by
      rw [Module.Basis.map_apply]
      rfl
    change (extendedHopfMap K f).hom (bas α).toMul.val = _
    rw [ha]
    have hj' := DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom hj)
      ((1 : K) ⊗ₜ[k] MonoidAlgebra.of k N a)
    change (extendedHopfMap K f).hom (j.hom.hom (1 ⊗ₜ[k] MonoidAlgebra.of k N a)) =
      F.torusIso.hom.hom ((extendedHopfMap K (coordinatesToSpectrum T₀ p₀)).hom
        (1 ⊗ₜ[k] MonoidAlgebra.of k N a)) at hj'
    rw [hj']
    exact congrArg F.torusIso.hom.hom
      (rootCoordinate_pullback (K := K) (T := T₀) (N := N) p₀ a α.val.val
        ((hroot a).trans (hb α)))
  have hsK : Specs.CharacterDescent.IsDiagonalizable (extendedHopf K (coordinateAlgebra A)) :=
    ⟨m, ⟨(CommHopfAlgCat.isoMk (groupAlgebraBaseChange k K N).symm) ≪≫ j⟩⟩
  refine ⟨⟨bas, ?_⟩, hrb, hsK⟩
  intro σ α
  have hinj : Function.Injective (extendedHopfMap K f).hom :=
    Module.Flat.lTensor_preserves_injective_linearMap f.hom.toLinearMap
      (coordinateHopfMap_injective (G := T₁) (H := A) p hp)
  apply hinj
  refine (extendedHopfMap_equivariant K f σ (bas α).toMul.val).trans ?_
  change (SemilinearAction.scalarExtension (K := K) (coordinateAlgebra T₁)).act σ
      (pullbackCharacter K f (bas α).toMul).val =
    (pullbackCharacter K f (bas (r (l (F.outer σ)) α)).toMul).val
  rw [hrb, hrb, hr]
  exact extendedCharacterValue_twist F σ α.val.val

end AdjointCharacters


private def orbitRepresentativeValues {Γ I M : Type u} [Group Γ] [MulAction Γ I]
    [MulAction Γ M] (v : {v : I → M // ∀ (σ : Γ) i, v (σ • i) = σ • v i})
    (o : MulAction.orbitRel.Quotient Γ I) :
    {x : M // ∀ σ : Γ, σ ∈ MulAction.stabilizer Γ o.out → σ • x = x} :=
  ⟨v.val o.out, fun σ hσ => ((v.property σ o.out).symm.trans
    (congrArg v.val (MulAction.mem_stabilizer_iff.mp hσ)))⟩

private theorem orbitRepresentativeValues_bijective {Γ I M : Type u} [Group Γ]
    [MulAction Γ I] [MulAction Γ M] :
    Function.Bijective (orbitRepresentativeValues (Γ := Γ) (I := I) (M := M)) := by
  classical
  let O := MulAction.orbitRel.Quotient Γ I
  let q : I → O := Quotient.mk (MulAction.orbitRel Γ I)
  have hrep (i : I) : ∃ g : Γ, g • (q i).out = i :=
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact (Quotient.out_eq (q i)).symm))
  choose g hg using hrep
  constructor
  · intro v w he
    apply Subtype.ext
    funext i
    have h := congrArg (fun a => (a (q i)).val) he
    have hv := v.property (g i) (q i).out
    have hw := w.property (g i) (q i).out
    rw [hg i] at hv hw
    exact hv.trans ((congrArg (g i • ·) h).trans hw.symm)
  · intro x
    let v : I → M := fun i => g i • (x (q i)).val
    have hval (o : O) (i : I) (s : Γ) (hs : s • o.out = i) :
        v i = s • (x o).val := by
      have hh : o.out ∈ MulAction.orbit Γ i :=
        MulAction.mem_orbit_iff.mpr ⟨s⁻¹, by rw [← hs, inv_smul_smul]⟩
      have hq : o = q i := (Quotient.out_eq o).symm.trans
        (Quotient.sound (MulAction.orbitRel_apply.mpr hh))
      subst o
      have hst : s⁻¹ * g i ∈ MulAction.stabilizer Γ (q i).out :=
        MulAction.mem_stabilizer_iff.mpr (calc
          (s⁻¹ * g i) • (q i).out = s⁻¹ • i := by rw [mul_smul, hg i]
          _ = (q i).out := (congrArg (s⁻¹ • ·) hs).symm.trans (inv_smul_smul _ _))
      have hfix := (x (q i)).property (s⁻¹ * g i) hst
      change g i • (x (q i)).val = _
      rw [mul_smul] at hfix
      exact (smul_inv_smul s (g i • (x (q i)).val)).symm.trans
        (congrArg (s • ·) hfix)
    have heq (s : Γ) (i : I) : v (s • i) = s • v i := by
      rw [hval (q i) (s • i) (s * g i) (by rw [mul_smul, hg]), mul_smul]
    refine ⟨⟨v, heq⟩, ?_⟩
    funext o
    apply Subtype.ext
    exact (hval o o.out 1 (one_smul _ _)).trans (one_smul _ _)

section FixedScalars

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (V : Type u) [AddCommGroup V] [Module k V]

open private repr_act from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces

private theorem tensorFixedField_range (J : Subgroup Gal(K/k)) :
    Set.range (TensorProduct.map (IntermediateField.val (IntermediateField.fixedField J)).toLinearMap
      (LinearMap.id : V →ₗ[k] V)) =
    {x : K ⊗[k] V | ∀ σ ∈ J, (SemilinearAction.scalarExtension (K := K) V).act σ x = x} := by
  classical
  let E := IntermediateField.fixedField J
  let f := TensorProduct.map E.val.toLinearMap (LinearMap.id : V →ₗ[k] V)
  ext x
  constructor
  · rintro ⟨y, rfl⟩ σ hσ
    change (SemilinearAction.scalarExtension (K := K) V).act σ (f y) = f y
    induction y using TensorProduct.inductionOn with
    | tmul a v =>
      change σ (a : K) ⊗ₜ[k] v = (a : K) ⊗ₜ[k] v
      rw [(IntermediateField.mem_fixedField_iff J (a : K)).mp a.property σ hσ]
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro hx
    let b := Module.Free.chooseBasis k V
    let s := SemilinearAction.scalarExtension (k := k) (K := K) V
    have hb (i : _) : b.baseChange K i ∈ s.fixed := by
      intro σ
      simp [s]
    have hc (i : _) : (b.baseChange K).repr x i ∈ E := by
      apply (IntermediateField.mem_fixedField_iff J _).mpr
      intro σ hσ
      rw [← repr_act s (b.baseChange K) hb σ, hx σ hσ]
    refine ⟨∑ i ∈ ((b.baseChange K).repr x).support, (⟨(b.baseChange K).repr x i, hc i⟩ : E)
      ⊗ₜ[k] b i, ?_⟩
    change f _ = x
    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans ((b.baseChange K).linearCombination_repr x)
    change (b.baseChange K).repr x i ⊗ₜ[k] b i =
      (b.baseChange K).repr x i • b.baseChange K i
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end FixedScalars

section TensorUnits

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (R : TestAlgebra k)

private def tensorAutomorphism (σ : Gal(K/k)) : K ⊗[k] R →ₐ[k] K ⊗[k] R :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k R)

private theorem tensorAutomorphism_apply (σ : Gal(K/k)) (x : K ⊗[k] R) :
    tensorAutomorphism R σ x = (SemilinearAction.scalarExtension (K := K) R).act σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

@[instance_reducible] private def tensorUnitAction : MulAction Gal(K/k) (K ⊗[k] R)ˣ where
  smul σ := Units.map (tensorAutomorphism R σ).toMonoidHom
  one_smul x := by
    apply Units.ext
    exact (tensorAutomorphism_apply R 1 _).trans
      ((SemilinearAction.scalarExtension (k := k) (K := K) R).one_act _)
  mul_smul σ τ x := by
    apply Units.ext
    change tensorAutomorphism R (σ * τ) (x : K ⊗[k] R) =
      tensorAutomorphism R σ (tensorAutomorphism R τ (x : K ⊗[k] R))
    simp only [tensorAutomorphism_apply, SemilinearAction.mul_act]

private def fixedFieldTensor (J : Subgroup Gal(K/k)) :
    R ⊗[k] IntermediateField.fixedField J →ₐ[k] K ⊗[k] R :=
  (Algebra.TensorProduct.map (IntermediateField.val _) (AlgHom.id k R)).comp
    (Algebra.TensorProduct.comm k R (IntermediateField.fixedField J)).toAlgHom

private theorem fixedFieldTensor_injective (J : Subgroup Gal(K/k)) :
    Function.Injective (fixedFieldTensor R J) := by
  let e := Algebra.TensorProduct.comm k R (IntermediateField.fixedField J)
  let f := IntermediateField.val (IntermediateField.fixedField J)
  change Function.Injective ((Algebra.TensorProduct.map f (AlgHom.id k R)).comp e.toAlgHom)
  exact (Module.Flat.rTensor_preserves_injective_linearMap (M := R) f.toLinearMap
    Subtype.val_injective).comp e.injective

private theorem fixedFieldTensor_range (J : Subgroup Gal(K/k)) :
    Set.range (fixedFieldTensor R J) =
      {x | ∀ σ ∈ J, tensorAutomorphism R σ x = x} := by
  let e := Algebra.TensorProduct.comm k R (IntermediateField.fixedField J)
  simp only [tensorAutomorphism_apply]
  change Set.range ((Algebra.TensorProduct.map (IntermediateField.val _) (AlgHom.id k R)) ∘ e) = _
  rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
  exact tensorFixedField_range R J

private def fixedFieldTensorUnits (J : Subgroup Gal(K/k)) :
    (R ⊗[k] IntermediateField.fixedField J)ˣ ≃
      {x : (K ⊗[k] R)ˣ // ∀ σ ∈ J, letI := tensorUnitAction (K := K) R; σ • x = x} := by
  letI := tensorUnitAction (K := K) R
  let f := fixedFieldTensor R J
  refine Equiv.ofBijective (fun x => ⟨Units.map f.toMonoidHom x, ?_⟩) ⟨?_, ?_⟩
  · intro σ hσ
    apply Units.ext
    exact (fixedFieldTensor_range R J ▸ Set.mem_range_self (f := fixedFieldTensor R J) x.val) σ hσ
  · intro x y h
    exact Units.map_injective (fixedFieldTensor_injective R J) (congrArg Subtype.val h)
  · intro x
    have hf (σ : Gal(K/k)) (hσ : σ ∈ J) :
        tensorAutomorphism R σ (x.val : K ⊗[k] R) = x.val :=
      congrArg Units.val (x.property σ hσ)
    have hfi (σ : Gal(K/k)) (hσ : σ ∈ J) :
        tensorAutomorphism R σ (x.val⁻¹ : (K ⊗[k] R)ˣ).val = (x.val⁻¹).val :=
      congrArg (fun v : (K ⊗[k] R)ˣ => (v⁻¹).val) (x.property σ hσ)
    have hxa : (x.val : K ⊗[k] R) ∈ Set.range f := by
      change _ ∈ Set.range (fixedFieldTensor R J)
      rw [fixedFieldTensor_range]
      exact hf
    have hxb : (x.val⁻¹ : (K ⊗[k] R)ˣ).val ∈ Set.range f := by
      change _ ∈ Set.range (fixedFieldTensor R J)
      rw [fixedFieldTensor_range]
      exact hfi
    obtain ⟨a, ha⟩ := hxa
    obtain ⟨b, hb⟩ := hxb
    have hab : a * b = 1 := fixedFieldTensor_injective R J (show f (a * b) = f 1 from by
      rw [map_mul f, ha, hb]
      exact x.val.val_inv.trans f.map_one.symm)
    refine ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, Subtype.ext (Units.ext ha)⟩

end TensorUnits


section CharacterEvaluation

open Coalgebra
open WithConv
open Specs.CharacterDescent (IsDiagonalizable GeometricCharacters)
open _root_.LinearAlgebraicGroups.CharacterDescent (geometricAction)
open private groupLikeSpanOfSplit groupAlgebraOfCharacters
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private liftCharacters_single from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private restrictConvolution restrictConvolution_mul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private def groupLikeEvaluation {F : Type u} [Field F] {A : HopfAlgebraCategory F}
    {R : Type u} [CommRing R] [Algebra F R] (f : A →ₐ[F] R) :
    GroupLike F A →* Rˣ :=
  (Units.map f.toMonoidHom).comp (GroupLike.toUnits F)

private theorem groupLikeEvaluation_basis_ext {F : Type u} [Field F] {A : HopfAlgebraCategory F}
    {I M : Type u} [CommGroup M] (b : Module.Basis I ℤ (Additive (GroupLike F A)))
    {f g : GroupLike F A →* M} (h : ∀ i, f (b i).toMul = g (b i).toMul) : f = g := by
  apply MonoidHom.toAdditive.injective
  apply AddMonoidHom.toIntLinearMap_injective
  apply b.ext
  exact h

private theorem characterEvaluation_bijective {F : Type u} [Field F] {A : HopfAlgebraCategory F}
    {R : Type u} [CommRing R] [Algebra F R] {I : Type u}
    (hA : IsDiagonalizable A) (b : Module.Basis I ℤ (Additive (GroupLike F A))) :
    Function.Bijective (fun (f : A →ₐ[F] R) i => groupLikeEvaluation f (b i).toMul) := by
  have hspan := groupLikeSpanOfSplit A hA
  constructor
  · intro f g h
    have he := groupLikeEvaluation_basis_ext b (f := groupLikeEvaluation f)
      (g := groupLikeEvaluation g) (congrFun h)
    apply AlgHom.toLinearMap_injective
    apply LinearMap.ext_on_range hspan
    intro x
    exact congrArg Units.val (DFunLike.congr_fun he x)
  · intro v
    let m : GroupLike F A →* Rˣ := (b.constr ℤ fun i => Additive.ofMul (v i)).toAddMonoidHom.toMultiplicative
    let e := groupAlgebraOfCharacters A hspan
    let f : A →ₐ[F] R := ((MonoidAlgebra.lift F R _)
      ((Units.coeHom R).comp m)).comp e.inv.hom.toAlgHom
    have he (x : GroupLike F A) : e.inv.hom x.val = MonoidAlgebra.of F (GroupLike F A) x := by
      have hx : e.hom.hom (MonoidAlgebra.of F (GroupLike F A) x) = x.val :=
        liftCharacters_single (MonoidHom.id _) x
      rw [← hx]
      exact DFunLike.congr_fun (congrArg CommHopfAlgCat.Hom.hom e.hom_inv_id) _
    refine ⟨f, funext fun i => Units.ext ?_⟩
    change f (b i).toMul.val = (v i).val
    change (MonoidAlgebra.lift F R _) ((Units.coeHom R).comp m)
        (e.inv.hom (b i).toMul.val) = _
    rw [he, MonoidAlgebra.lift_of]
    exact congrArg (fun z : Additive Rˣ => z.toMul.val) (Module.Basis.constr_basis b ℤ _ i)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {A : HopfAlgebraCategory k} (R : TestAlgebra k)

private def extendCoordinatePoint (f : A →ₐ[k] R) : extendedHopf K A →ₐ[K] K ⊗[k] R :=
  Algebra.TensorProduct.map (AlgHom.id K K) f

private theorem extendCoordinatePoint_injective :
    Function.Injective (extendCoordinatePoint (K := K) (A := A) R) := by
  intro f g h
  ext a
  apply (Algebra.TensorProduct.includeRight_injective (B := R) (algebraMap k K).injective)
  exact DFunLike.congr_fun h (1 ⊗ₜ[k] a)

private theorem extendCoordinatePoint_mul (f g : WithConv (A →ₐ[k] R)) :
    extendCoordinatePoint (K := K) R (f * g).ofConv =
      (toConv (extendCoordinatePoint (K := K) R f.ofConv) *
        toConv (extendCoordinatePoint (K := K) R g.ofConv)).ofConv := by
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro a
  let j : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
  let f' := toConv (extendCoordinatePoint (K := K) R f.ofConv)
  let g' := toConv (extendCoordinatePoint (K := K) R g.ofConv)
  have hf : restrictConvolution f' = toConv (j.comp f.ofConv) := by
    apply ofConv_injective
    exact AlgHom.ext fun _ => rfl
  have hg : restrictConvolution g' = toConv (j.comp g.ofConv) := by
    apply ofConv_injective
    exact AlgHom.ext fun _ => rfl
  have hm := (restrictConvolution_mul f' g').trans (congrArg₂ (· * ·) hf hg)
  exact DFunLike.congr_fun ((AlgHom.comp_convMul_distrib j f g).trans (congrArg ofConv hm).symm) a

private theorem extendCoordinatePoint_equivariant (f : A →ₐ[k] R)
    (σ : Gal(K/k)) (x : extendedHopf K A) :
    extendCoordinatePoint R f ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
      (SemilinearAction.scalarExtension (K := K) R).act σ (extendCoordinatePoint R f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

open private scalarExtension_fixed_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem exists_extendCoordinatePoint [IsGalois k K]
    (f : extendedHopf K A →ₐ[K] K ⊗[k] R)
    (hf : ∀ (σ : Gal(K/k)) (x : extendedHopf K A),
      f ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
        (SemilinearAction.scalarExtension (K := K) R).act σ (f x)) :
    ∃ g : A →ₐ[k] R, extendCoordinatePoint R g = f := by
  let j : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
  let e := AlgEquiv.ofInjective j (Algebra.TensorProduct.includeRight_injective
    (B := R) (algebraMap k K).injective)
  let v : A →ₐ[k] K ⊗[k] R := (f.restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hv (a : A) : v a ∈ j.range := by
    have h (σ : Gal(K/k)) :
        (SemilinearAction.scalarExtension (K := K) R).act σ (v a) = v a := by
      change (SemilinearAction.scalarExtension (K := K) R).act σ (f (1 ⊗ₜ[k] a)) = _
      rw [← hf]
      change f (σ 1 ⊗ₜ[k] a) = _
      rw [map_one σ]
      rfl
    obtain ⟨b, hb⟩ := scalarExtension_fixed_surjective K R ⟨v a, h⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  refine ⟨e.symm.toAlgHom.comp (v.codRestrict j.range hv), ?_⟩
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro a
  change ((e (e.symm ⟨v a, hv a⟩)).val) = v a
  rw [e.apply_symm_apply]

variable {I : Type u} {H : AffineAlgebraicGroup k}
variable {r : Gal(K/k) →* Equiv.Perm I}

private def pointCharacters (b : PermutedCharacterBasis K I H r)
    (f : Specs.AdjointCocharacters.coordinateHopf H →ₐ[k] R) (i : I) :
    (K ⊗[k] R)ˣ :=
  groupLikeEvaluation (extendCoordinatePoint R f) (b.basis i).toMul

private theorem pointCharacters_equivariant (b : PermutedCharacterBasis K I H r)
    (f : Specs.AdjointCocharacters.coordinateHopf H →ₐ[k] R) (σ : Gal(K/k)) (i : I) :
    letI := tensorUnitAction (K := K) R
    pointCharacters R b f (r σ i) = σ • pointCharacters R b f i := by
  letI := tensorUnitAction (K := K) R
  apply Units.ext
  change extendCoordinatePoint R f (b.basis (r σ i)).toMul.val =
    tensorAutomorphism R σ (extendCoordinatePoint R f (b.basis i).toMul.val)
  rw [tensorAutomorphism_apply, ← extendCoordinatePoint_equivariant, b.permutation]

private theorem pointCharacters_bijective [IsGalois k K] (b : PermutedCharacterBasis K I H r)
    (hH : IsDiagonalizable (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H))) :
    letI := MulAction.compHom I r
    letI := tensorUnitAction (K := K) R
    Function.Bijective (fun f =>
      (⟨pointCharacters R b f, pointCharacters_equivariant R b f⟩ :
        {v : I → (K ⊗[k] R)ˣ // ∀ (σ : Gal(K/k)) i, v (σ • i) = σ • v i})) := by
  letI := MulAction.compHom I r
  letI := tensorUnitAction (K := K) R
  let A := Specs.AdjointCocharacters.coordinateHopf H
  let E := extendedHopf K A
  let hEval := characterEvaluation_bijective (A := E) (R := K ⊗[k] R) hH b.basis
  constructor
  · intro f g h
    exact extendCoordinatePoint_injective R (hEval.1 (congrArg Subtype.val h))
  · intro v
    obtain ⟨e, he⟩ := hEval.2 v.val
    change (fun i => groupLikeEvaluation e (b.basis i).toMul) = v.val at he
    have heq (σ : Gal(K/k)) (x : E) :
        e ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
          (SemilinearAction.scalarExtension (K := K) R).act σ (e x) := by
      let p := (geometricAction K A σ).asHom.hom
      let q := Units.map (tensorAutomorphism R σ).toMonoidHom
      have he' : (groupLikeEvaluation e).comp p = q.comp (groupLikeEvaluation e) := by
        apply groupLikeEvaluation_basis_ext b.basis
        intro i
        have hp : p (b.basis i).toMul = (b.basis (r σ i)).toMul :=
          GroupLike.val_injective (b.permutation σ i)
        change groupLikeEvaluation e (p (b.basis i).toMul) =
          q (groupLikeEvaluation e (b.basis i).toMul)
        have hi (j : I) : groupLikeEvaluation e (b.basis j).toMul = v.val j :=
          congrFun he j
        rw [hp, hi, hi]
        exact v.property σ i
      let s := SemilinearAction.scalarExtension (k := k) (K := K) A
      let t := SemilinearAction.scalarExtension (k := k) (K := K) R
      have hlin : e.toLinearMap.comp (s.operator σ) = (t.operator σ).comp e.toLinearMap := by
        apply LinearMap.ext_on_range (groupLikeSpanOfSplit E hH)
        intro x
        exact (congrArg Units.val (DFunLike.congr_fun he' x)).trans (tensorAutomorphism_apply R σ _)
      exact DFunLike.congr_fun hlin x
    obtain ⟨f, hf⟩ := exists_extendCoordinatePoint R e heq
    refine ⟨f, Subtype.ext ?_⟩
    change (fun i => groupLikeEvaluation (extendCoordinatePoint R f) (b.basis i).toMul) = v.val
    rw [hf]
    exact he


private def orbitPoint (b : PermutedCharacterBasis K I H r)
    (f : Specs.AdjointCocharacters.coordinateHopf H →ₐ[k] R) :
    letI := MulAction.compHom I r
    (o : MulAction.orbitRel.Quotient Gal(K/k) I) →
      (R ⊗[k] IntermediateField.fixedField (MulAction.stabilizer Gal(K/k) o.out))ˣ := by
  letI := MulAction.compHom I r
  letI := tensorUnitAction (K := K) R
  intro o
  let J := MulAction.stabilizer Gal(K/k) o.out
  let v : {v : I → (K ⊗[k] R)ˣ // ∀ (σ : Gal(K/k)) i, v (σ • i) = σ • v i} :=
    ⟨pointCharacters R b f, pointCharacters_equivariant R b f⟩
  exact (fixedFieldTensorUnits R J).symm (orbitRepresentativeValues v o)

private theorem orbitPoint_spec (b : PermutedCharacterBasis K I H r)
    (f : Specs.AdjointCocharacters.coordinateHopf H →ₐ[k] R) :
    letI := MulAction.compHom I r
    ∀ o : MulAction.orbitRel.Quotient Gal(K/k) I,
      Units.map (fixedFieldTensor R (MulAction.stabilizer Gal(K/k) o.out)).toMonoidHom
        (orbitPoint R b f o) = pointCharacters R b f o.out := by
  letI := MulAction.compHom I r
  letI := tensorUnitAction (K := K) R
  intro o
  let J := MulAction.stabilizer Gal(K/k) o.out
  let v : {v : I → (K ⊗[k] R)ˣ // ∀ (σ : Gal(K/k)) i, v (σ • i) = σ • v i} :=
    ⟨pointCharacters R b f, pointCharacters_equivariant R b f⟩
  exact congrArg Subtype.val ((fixedFieldTensorUnits R J).apply_symm_apply (orbitRepresentativeValues v o))

private theorem orbitPoint_bijective [IsGalois k K] (b : PermutedCharacterBasis K I H r)
    (h : IsDiagonalizable (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H))) :
    Function.Bijective (orbitPoint R b) := by
  letI := MulAction.compHom I r
  letI := tensorUnitAction (K := K) R
  let O := MulAction.orbitRel.Quotient Gal(K/k) I
  let E := Equiv.piCongrRight fun o : O =>
    (fixedFieldTensorUnits R (MulAction.stabilizer Gal(K/k) o.out)).symm
  exact E.bijective.comp (orbitRepresentativeValues_bijective.comp (pointCharacters_bijective R b h))

open _root_.LinearAlgebraicGroups.WeilRestriction (extendedUnits tensorMap)

private theorem fixedFieldTensor_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (J : Subgroup Gal(K/k)) (x : R ⊗[k] IntermediateField.fixedField J) :
    fixedFieldTensor S J ((tensorMap k (IntermediateField.fixedField J) f.hom) x) =
      (Algebra.TensorProduct.map (AlgHom.id K K) f.hom) (fixedFieldTensor R J x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem pointCharacters_natural {R S : TestAlgebra k}
    (b : PermutedCharacterBasis K I H r) (f : R ⟶ S)
    (x : Specs.AdjointCocharacters.coordinateHopf H →ₐ[k] R) (i : I) :
    pointCharacters S b (f.hom.comp x) i =
      Units.map (Algebra.TensorProduct.map (AlgHom.id K K) f.hom).toMonoidHom
        (pointCharacters R b x i) := by
  apply Units.ext
  change extendCoordinatePoint S (f.hom.comp x) (b.basis i).toMul.val = _
  have h : extendCoordinatePoint S (f.hom.comp x) =
      (Algebra.TensorProduct.map (AlgHom.id K K) f.hom).comp (extendCoordinatePoint R x) :=
    Algebra.TensorProduct.ext_ring (AlgHom.ext fun _ => rfl)
  exact AlgHom.congr_fun h _

private def orbitCoordinate (b : PermutedCharacterBasis K I H r) :
    letI := MulAction.compHom I r
    (o : MulAction.orbitRel.Quotient Gal(K/k) I) →
    convolutionPoints (Specs.AdjointCocharacters.coordinateHopf H) ⟶
      extendedUnits k (IntermediateField.fixedField (MulAction.stabilizer Gal(K/k) o.out)) := by
  letI := MulAction.compHom I r
  intro o
  let A := Specs.AdjointCocharacters.coordinateHopf H
  let J := MulAction.stabilizer Gal(K/k) o.out
  let E := IntermediateField.fixedField J
  have hmul (R : TestAlgebra k) (x y : WithConv (A →ₐ[k] R)) :
      orbitPoint R b (x * y).ofConv o = orbitPoint R b x.ofConv o * orbitPoint R b y.ofConv o := by
    let f := Units.map (fixedFieldTensor R J).toMonoidHom
    apply Units.map_injective (fixedFieldTensor_injective R J)
    change f (orbitPoint R b (x * y).ofConv o) =
      f (orbitPoint R b x.ofConv o * orbitPoint R b y.ofConv o)
    rw [map_mul f]
    change Units.map (fixedFieldTensor R J).toMonoidHom (orbitPoint R b (x * y).ofConv o) =
      Units.map (fixedFieldTensor R J).toMonoidHom (orbitPoint R b x.ofConv o) *
        Units.map (fixedFieldTensor R J).toMonoidHom (orbitPoint R b y.ofConv o)
    rw [orbitPoint_spec, orbitPoint_spec, orbitPoint_spec]
    apply Units.ext
    let α := (b.basis o.out).toMul
    change extendCoordinatePoint R (x * y).ofConv α.val =
      extendCoordinatePoint R x.ofConv α.val * extendCoordinatePoint R y.ofConv α.val
    rw [extendCoordinatePoint_mul]
    exact (AlgHom.convMul_apply _ _ _).trans (by
      rw [α.2.comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul])
  letI (R : TestAlgebra k) := convolutionGroup A R
  refine
    { app := fun R => GrpCat.ofHom
        { toFun := fun x => orbitPoint R b x.ofConv o
          map_one' := by
            have h := hmul R 1 1
            rw [one_mul] at h
            exact mul_eq_left.mp h.symm
          map_mul' := hmul R }
      naturality := ?_ }
  intro R S f
  apply GrpCat.ext
  intro x
  let x' : A →ₐ[k] R := x.ofConv
  let z := orbitPoint R b x' o
  change orbitPoint S b (f.hom.comp x') o = Units.map (tensorMap k E f.hom).toMonoidHom z
  apply Units.map_injective (fixedFieldTensor_injective S J)
  apply Units.ext
  change (Units.map (fixedFieldTensor S J).toMonoidHom
    (orbitPoint S b (f.hom.comp x') o)).val =
    fixedFieldTensor S J ((tensorMap k E f.hom) z.val)
  rw [orbitPoint_spec, fixedFieldTensor_natural, pointCharacters_natural]
  exact congrArg (fun w : (K ⊗[k] R)ˣ =>
    (Algebra.TensorProduct.map (AlgHom.id K K) f.hom) w.val) (orbitPoint_spec R b x' o).symm

end CharacterEvaluation

section WeilProduct

open _root_.LinearAlgebraicGroups.WeilRestriction (multiplicativeRestriction multiplicativeRestrictionUnits)
open Specs.CharacterDescent (IsDiagonalizable)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {I : Type u} {r : Gal(K/k) →* Equiv.Perm I}
variable {H : AffineAlgebraicGroup k}

private theorem affinePointIso {G V : GroupScheme k} (f : G ⟶ V)
    (hG : IsAffine G.X.left) (hV : IsAffine V.X.left)
    (h : ∀ R, Function.Bijective (((groupPointsFunctor k).map f).app R)) :
    Nonempty (G ≅ V) := by
  let F := groupPointsFunctor k
  letI (R : TestAlgebra k) : IsIso ((F.map f).app R) :=
    (MulEquiv.ofBijective ((F.map f).app R).hom (h R)).toGrpIso.isIso_hom
  letI : IsIso (F.map f) := NatIso.isIso_of_isIso_app (F.map f)
  let e := asIso (F.map f)
  obtain ⟨g, hg⟩ := (groupHomComparison k V G hV).2 e.inv
  change F.map g = e.inv at hg
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · apply (groupHomComparison k G G hG).1
    change F.map (f ≫ g) = F.map (𝟙 G)
    rw [F.map_comp, hg, F.map_id]
    exact e.hom_inv_id
  · apply (groupHomComparison k V V hV).1
    change F.map (g ≫ f) = F.map (𝟙 V)
    rw [F.map_comp, hg, F.map_id]
    exact e.inv_hom_id

private theorem orbitWeilProduct [Finite I] [Module.Finite k K] [IsGalois k K]
    (b : PermutedCharacterBasis K I H r)
    (hH : IsDiagonalizable (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H))) :
    IsOrbitWeilProduct K r H := by
  letI := MulAction.compHom I r
  let O := MulAction.orbitRel.Quotient Gal(K/k) I
  let E (o : O) := IntermediateField.fixedField (MulAction.stabilizer Gal(K/k) o.out)
  let W (o : O) := multiplicativeRestriction k (E o)
  let w (o : O) := multiplicativeRestrictionUnits k (E o)
  let P : Fan (fun o : O => (W o).val) := Fan.mk (∏ᶜ fun o : O => (W o).val) (Pi.π _)
  have hP := productIsProduct (fun o : O => (W o).val)
  let F := groupPointsFunctor k
  let C := Specs.AdjointCocharacters.coordinateHopf H
  let e := hopfSpecPointIso C ≪≫ F.mapIso (Specs.AdjointCocharacters.coordinateHopfIso H)
  have hπ (o : O) := (groupHomComparison k H.val (W o).val H.property.1).2
    (e.inv ≫ orbitCoordinate b o ≫ (w o).inv)
  choose π hπ using hπ
  let f : H.val ⟶ P.pt := Fan.IsLimit.lift hP π
  have hf (o : O) : f ≫ P.proj o = π o := Fan.IsLimit.fac hP π o
  refine ⟨W, fun o => ⟨w o⟩, P, ⟨hP⟩, ?_⟩
  have hPaff : IsAffine P.pt.X.left := by
    let U := Grp.forget (SchemeOver k)
    let D := Discrete.functor (fun o : O => (W o).val) ⋙ U
    let V := CommRingCat.of k
    let adj := algΓAlgSpecAdjunction V
    let L := algΓ V
    let R := algSpec V
    let ff := algSpec.fullyFaithful (R := V)
    letI := ff.full
    letI := ff.faithful
    letI : R.IsRightAdjoint := adj.isRightAdjoint
    let a : D ⟶ (D ⋙ L) ⋙ R := D.whiskerLeft adj.unit
    letI (o : Discrete O) : IsIso (a.app o) := (adj.isIso_unit_app_iff_mem_essImage).mpr
      (essImage_algSpec.mpr (W o.as).property.1)
    letI : IsIso a := NatIso.isIso_of_isIso_app a
    have hP' : IsLimit (U.mapCone P) := isLimitOfPreserves U hP
    let C := R.mapCone (limit.cone (D ⋙ L))
    have hC : IsLimit C := isLimitOfPreserves R (limit.isLimit (D ⋙ L))
    let d := hP'.conePointUniqueUpToIso ((IsLimit.postcomposeHomEquiv (asIso a).symm C).symm hC)
    let d' := (Over.forget (Spec V)).mapIso d
    exact @IsAffine.of_isIso _ _ d'.hom d'.isIso_hom (isAffine_Spec _)
  have hR (R : TestAlgebra k) : Function.Bijective ((F.map f).app R) := by
    let U := Grp.forget (SchemeOver k)
    let h := (Fan.isLimitMapConeEquiv U (fun o : O => (W o).val) P) (isLimitOfPreserves U hP)
    let q : (F.obj P.pt).obj R ≃ (∀ o : O, (F.obj (W o).val).obj R) :=
      { toFun := fun x o => ((F.map (P.proj o)).app R) x
        invFun := fun x => Fan.IsLimit.lift h x
        left_inv := fun x => Fan.IsLimit.hom_ext h _ _ (fun o => Fan.IsLimit.fac h _ o)
        right_inv := fun x => funext (fun o => Fan.IsLimit.fac h _ o) }
    let v := q.trans (Equiv.piCongrRight fun o => ((w o).app R).groupIsoToMulEquiv.toEquiv)
    have hv (x : (F.obj H.val).obj R) :
        v (((F.map f).app R) x) = orbitPoint R b ((((e.app R).symm).hom) x).ofConv := by
      funext o
      change (w o).hom.app R (((F.map (P.proj o)).app R) (((F.map f).app R) x)) = _
      have hcomp : F.map f ≫ F.map (P.proj o) = e.inv ≫ orbitCoordinate b o ≫ (w o).inv := by
        rw [← F.map_comp, hf]
        exact hπ o
      have heq := ConcreteCategory.congr_hom (congrArg (fun a => a.app R) hcomp) x
      let y := (orbitCoordinate b o).app R (e.inv.app R x)
      change ((F.map (P.proj o)).app R) (((F.map f).app R) x) = (w o).inv.app R y at heq
      have hy : (w o).hom.app R ((w o).inv.app R y) = y :=
        ConcreteCategory.congr_hom (congrArg (fun a => a.app R) (w o).inv_hom_id) y
      exact (congrArg ((w o).hom.app R ·) heq).trans hy
    have hcomp : Function.Bijective (fun x => v (((F.map f).app R) x)) := by
      simp only [hv]
      have he : Function.Bijective (fun x : (F.obj H.val).obj R => (e.inv.app R x).ofConv) :=
        (WithConv.equiv (A := C →ₐ[k] R)).bijective.comp
          ((e.app R).symm.groupIsoToMulEquiv.toEquiv.bijective)
      exact (orbitPoint_bijective R b hH).comp he
    exact (v.bijective.of_comp_iff' _).mp hcomp
  obtain ⟨d⟩ := affinePointIso f H.property.1 hPaff hR
  exact ⟨d.symm⟩

end WeilProduct


section PinnedDescent

open Specs.Fppf (IsFppf)
open Specs.Pinning (PinnedGroup SimpleRoot)
open Specs.RootGroups (AdditiveLine)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

/-- The Borel of the adjoint quotient of the pinned quasi-split twist has
trivial first Galois cohomology. The quotient torus is a product of Weil
restrictions over the orbits of the simple roots. -/
theorem adjointBorelCohomology : TwistedAdjointBorel.{u} := by
  intro k K _ _ _ _ _ L P D l _ _ G B T F hG hB hT hmax j hj
  obtain ⟨Z, Q, q, hq, hQ, ⟨z, hz⟩, ⟨Dq⟩⟩ :=
    adjointBorelForPair G B T hG hB hT hmax ⟨j, hj⟩
  obtain ⟨Td, p, hzc, hTd, hTdm, hp, _, hker⟩ :=
    adjointTorusImage Dq hG hq hT hmax j hj z hz
  obtain ⟨U, π, hU, hsU, hπ, hsec⟩ := borelTorusQuotient Q Dq.subgroup hQ Dq.borel Td hTdm
  obtain ⟨hf, r, hr⟩ := pinnedSimpleRootPermutation P
  letI := hf
  let A := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup Dq.subgroup) Td
  have hpf : IsFppf p.hom.hom.left := ⟨hker.2.1, hker.2.2.1, hker.2.2.2.1⟩
  obtain ⟨b, hb, hsplit⟩ := pinnedAdjointBasis (A := A) F r hr p hpf hq.1 z hz hker.1
  have hW := orbitWeilProduct b hsplit
  refine ⟨Z, Q, q, hq, hQ, Dq, z, hz, hzc, Td, p, U, π,
    hp, hTd, hTdm, hker, hU, hsU, hπ, hsec, ⟨r, b, hr, hb, hW⟩, ?_⟩
  intro S _ _ _ x
  letI := MulAction.compHom (SimpleRoot P.pair) (r.comp (l.toMonoidHom.comp F.outer))
  let O := MulAction.orbitRel.Quotient Gal(K/k) (SimpleRoot P.pair)
  let E (o : O) := IntermediateField.fixedField (MulAction.stabilizer Gal(K/k) o.out)
  obtain ⟨W, hW, V, ⟨hV⟩, hA⟩ := hW
  exact borelVanishingWithInducedQuotient k S Q Dq.subgroup hQ Dq.borel U hU A π hπ
    O (fun o => E o) W (fun o => Classical.choice (hW o)) V hV hA x

end PinnedDescent

end

end LinearAlgebraicGroups.Descent.AdjointBorelCohomology
