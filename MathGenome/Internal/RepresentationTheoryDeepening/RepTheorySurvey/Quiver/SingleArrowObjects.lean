import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SingleArrowObjects
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.ModuleVertices
import Mathlib.LinearAlgebra.Projection

/-! Classification of the finite-dimensional representations of a single arrow. -/

open CategoryTheory CategoryTheory.Limits
open scoped RM03.OneArrowSpec

namespace RepTheorySurvey.Quiver.SingleArrowObjects

universe w d

open RM03.QuiverRepresentation
open RM03.OneArrowSpec (edge representation)
open SingleArrowObjectsSpec (Kind Vertex Rep FiniteRep)

noncomputable abbrev S₁ := SingleArrowObjectsSpec.S₁
noncomputable abbrev S₂ := SingleArrowObjectsSpec.S₂
abbrev P₁ := SingleArrowObjectsSpec.P₁
noncomputable abbrev representative := SingleArrowObjectsSpec.representative

variable {k : Type w} [Field k]

private theorem arrow_representation {X Y : Type (max w d)}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] (T : X →ₗ[k] Y) :
    arrow (representation T) edge = T :=
  arrow_ofArrows _ _ edge

/-- Build a representation morphism from a commuting square at the unique arrow. -/
def homMk {V W : Rep.{w, d} k} (f : V.vertex false →ₗ[k] W.vertex false)
    (g : V.vertex true →ₗ[k] W.vertex true) (h : g.comp (V.arrow edge) = (W.arrow edge).comp f) :
    V ⟶ W :=
  RM03.QuiverRepresentation.homMk
    (fun i => match i with | false => f | true => g)
    (by
      intro i j a
      rcases a with ⟨⟨⟩, rfl, rfl⟩
      exact h)

@[simp]
theorem component_homMk_false {V W : Rep.{w, d} k} (f : V.vertex false →ₗ[k] W.vertex false)
    (g : V.vertex true →ₗ[k] W.vertex true) (h) :
    component (homMk f g h) false = f := rfl

@[simp]
theorem component_homMk_true {V W : Rep.{w, d} k} (f : V.vertex false →ₗ[k] W.vertex false)
    (g : V.vertex true →ₗ[k] W.vertex true) (h) :
    component (homMk f g h) true = g := rfl

private def isoMk {V W : Rep.{w, d} k} (f : V.vertex false ≃ₗ[k] W.vertex false)
    (g : V.vertex true ≃ₗ[k] W.vertex true)
    (h : ∀ x, g (V.arrow edge x) = W.arrow edge (f x)) : V ≅ W where
  hom := homMk f.toLinearMap g.toLinearMap (LinearMap.ext h)
  inv := homMk f.symm.toLinearMap g.symm.toLinearMap (by
    ext x
    apply g.injective
    simpa using (h (f.symm x)).symm)
  hom_inv_id := by
    apply RM03.QuiverRepresentation.hom_ext
    intro i
    cases i <;> ext x <;> simp
  inv_hom_id := by
    apply RM03.QuiverRepresentation.hom_ext
    intro i
    cases i <;> ext x <;> simp

theorem finite_representatives : SingleArrowObjectsSpec.FiniteRepresentatives.{w, d} := by
  intro k _ j
  cases j
  · exact Forms.finite_vertexSimple k false
  · exact Forms.finite_vertexSimple k true
  · intro i
    cases i <;> change Module.Finite k (ULift.{d} k) <;> infer_instance

private theorem identity_arrow :
    (P₁.{w, d} k).arrow edge = LinearMap.id :=
  arrow_representation (LinearMap.id : ULift.{d} k →ₗ[k] ULift.{d} k)

private theorem indecomposable_identity : Indecomposable (P₁.{w, d} k) := by
  let P := P₁.{w, d} k
  have id_ne_zero : (𝟙 P : P ⟶ P) ≠ 0 := by
    intro h
    have h' := LinearMap.congr_fun (congrArg (fun f => component f false) h)
      (ULift.up (1 : k))
    exact one_ne_zero (congrArg ULift.down h')
  refine ⟨fun h => id_ne_zero (h.eq_of_src _ _), fun Y Z e => ?_⟩
  let p : P ⟶ P := e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by simp [p, Category.assoc]
  let p₀ : ULift.{d} k →ₗ[k] ULift.{d} k := component p false
  let p₁ : ULift.{d} k →ₗ[k] ULift.{d} k := component p true
  have hc : p₁ = p₀ := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (naturality p edge.toPath) x
    change p₁ (arrow (P₁.{w, d} k) edge x) =
      arrow (P₁.{w, d} k) edge (p₀ x) at h
    rw [identity_arrow] at h
    exact h
  let c : k := (p₀ (ULift.up 1)).down
  have hf (x : ULift.{d} k) : p₀ x = x.down • ULift.up c := by
    have hx : x.down • (ULift.up (1 : k) : ULift.{d} k) = x := by
      apply ULift.ext
      simp
    calc
      p₀ x = p₀ (x.down • ULift.up 1) := congrArg p₀ hx.symm
      _ = x.down • ULift.up c := p₀.map_smul _ _
  have hcc : c * c = c := by
    have h := LinearMap.congr_fun (congrArg (fun f => component f false) hp) (ULift.up 1)
    change p₀ (ULift.up c) = ULift.up c at h
    exact congrArg ULift.down ((hf (ULift.up c)).symm.trans h)
  have lift_eq (q : P ⟶ P)
      (h0 : p₀ = (component q false : ULift.{d} k →ₗ[k] ULift.{d} k))
      (h1 : p₀ = (component q true : ULift.{d} k →ₗ[k] ULift.{d} k)) :
      p = q := by
    apply RM03.QuiverRepresentation.hom_ext
    intro i
    cases i
    · exact h0
    · exact hc.trans h1
  have hzero : p = 0 ∨ p = 𝟙 P := by
    have hroot : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
    rcases mul_eq_zero.mp hroot with h | h
    · have h0 : p₀ = 0 := LinearMap.ext fun x => by
        rw [hf, h]
        exact smul_zero _
      exact Or.inl (lift_eq 0 h0 h0)
    · have h := sub_eq_zero.mp h
      have h0 : p₀ = LinearMap.id := LinearMap.ext fun x => by
        change p₀ x = x
        rw [hf, h]
        apply ULift.ext
        simp
      exact Or.inr (lift_eq (𝟙 P) h0 h0)
  rcases hzero with h | h
  · left
    apply (IsZero.iff_id_eq_zero Y).2
    have hh := congrArg (fun f => biprod.inl ≫ e.inv ≫ f ≫ e.hom ≫ biprod.fst) h
    simpa [p, Category.assoc] using hh
  · right
    apply (IsZero.iff_id_eq_zero Z).2
    have hh := congrArg (fun f => biprod.inr ≫ e.inv ≫ f ≫ e.hom ≫ biprod.snd) h
    simpa [p, P, Category.assoc] using hh.symm

theorem indecomposable_representatives :
    SingleArrowObjectsSpec.IndecomposableRepresentatives.{w, d} := by
  intro k _ j
  cases j
  · change Indecomposable (Forms.vertexSimple.{0, 0, w, d} k (false : Vertex))
    let := Forms.vertexSimple_isSimple.{0, 0, w, d} k (false : Vertex)
    exact indecomposable_of_simple _
  · change Indecomposable (Forms.vertexSimple.{0, 0, w, d} k (true : Vertex))
    let := Forms.vertexSimple_isSimple.{0, 0, w, d} k (true : Vertex)
    exact indecomposable_of_simple _
  · exact indecomposable_identity

private def dimensions : Kind → Vertex → ℕ
  | .source, false | .target, true | .identity, _ => 1
  | _, _ => 0

private theorem finrank_representative (k : Type w) [Field k] (j : Kind) (i : Vertex) :
    Module.finrank k ((representative.{w, d} k j).vertex i) = dimensions j i := by
  cases j <;> cases i
  · rw [show (representative.{w, d} k .source).vertex false =
      ModuleCat.of k (ULift.{d} k) from Forms.vertexSimple_vertex_self k false]
    simp [dimensions]
  · rw [show (representative.{w, d} k .source).vertex true =
      ModuleCat.of k PUnit.{max w d + 1} from Forms.vertexSimple_vertex_of_ne k (by decide)]
    simp [dimensions, Module.finrank_zero_of_subsingleton]
  · rw [show (representative.{w, d} k .target).vertex false =
      ModuleCat.of k PUnit.{max w d + 1} from Forms.vertexSimple_vertex_of_ne k (by decide)]
    simp [dimensions, Module.finrank_zero_of_subsingleton]
  · rw [show (representative.{w, d} k .target).vertex true =
      ModuleCat.of k (ULift.{d} k) from Forms.vertexSimple_vertex_self k true]
    simp [dimensions]
  all_goals
    change Module.finrank k (ULift.{d} k) = 1
    simp

theorem distinct_representatives : SingleArrowObjectsSpec.DistinctRepresentatives.{w, d} := by
  rintro k _ i j ⟨e⟩
  have h (l : Vertex) : dimensions i l = dimensions j l := by
    rw [← finrank_representative.{w, d} k i l, ← finrank_representative.{w, d} k j l]
    exact (e.app (l : Paths Vertex)).toLinearEquiv.finrank_eq
  have h₁ := h false
  have h₂ := h true
  cases i <;> cases j <;> simp_all [dimensions]

section Decomposition

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- The product representation with the usual coordinate projections. -/
private def piRep {J : Type} (F : J → Rep.{w, d} k) : Rep.{w, d} k where
  obj i := ModuleCat.of k (∀ j, (F j).obj i)
  map p := ModuleCat.ofHom (LinearMap.pi fun j => ((F j).map p).hom.comp (LinearMap.proj j))
  map_id i := by
    apply ModuleCat.hom_ext
    ext x j
    change (F j).map (𝟙 i) (x j) = x j
    simp
  map_comp p q := by
    apply ModuleCat.hom_ext
    ext x j
    change (F j).map (p ≫ q) (x j) = (F j).map q ((F j).map p (x j))
    simp

private def piProjection {J : Type} (F : J → Rep.{w, d} k) (j : J) : piRep F ⟶ F j where
  app _ := ModuleCat.ofHom (LinearMap.proj j)
  naturality _ _ _ := rfl

private noncomputable def piRepIsoBiproduct {J : Type} [Finite J] (F : J → Rep.{w, d} k) :
    piRep F ≅ ⨁ F := by
  let c : Fan F := Fan.mk (piRep F) (piProjection F)
  have hc : IsLimit c := Fan.IsLimit.mk c
    (fun s =>
      { app := fun i => ModuleCat.ofHom (LinearMap.pi fun j => ((s.proj j).app i).hom)
        naturality := by
          intro i l p
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext j
          exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((s.proj j).naturality p)) x })
    (fun _ _ => rfl)
    (by
      intro s m hm
      apply RM03.QuiverRepresentation.hom_ext
      intro i
      apply LinearMap.ext
      intro x
      funext j
      exact LinearMap.congr_fun
        (congrArg (fun f => component f i) (hm j)) x)
  exact hc.conePointUniqueUpToIso (biproduct.isLimit F)

-- These presentations make the zero and one-dimensional coordinates reduce directly.
private abbrev standard (k : Type w) [Field k] : Kind → Rep.{w, d} k
  | .source => representation (0 : ULift.{d} k →ₗ[k] PUnit.{max w d + 1})
  | .target => representation (0 : PUnit.{max w d + 1} →ₗ[k] ULift.{d} k)
  | .identity => P₁ k

private def isoOfZeroArrows {V W : Rep.{w, d} k}
    (f : V.vertex false ≃ₗ[k] W.vertex false)
    (g : V.vertex true ≃ₗ[k] W.vertex true)
    (hV : V.arrow edge = 0) (hW : W.arrow edge = 0) : V ≅ W :=
  isoMk f g (fun x => by rw [hV, hW, LinearMap.zero_apply, LinearMap.zero_apply, g.map_zero])

private noncomputable def standardIso (j : Kind) :
    standard.{w, d} k j ≅ representative.{w, d} k j := by
  cases j
  · exact isoOfZeroArrows
      ((eqToIso (Forms.vertexSimple_vertex_self k false).symm).toLinearEquiv)
      ((eqToIso (Forms.vertexSimple_vertex_of_ne k (by decide : (true : Vertex) ≠ false)).symm).toLinearEquiv)
      (arrow_representation (0 : ULift.{d} k →ₗ[k] PUnit.{max w d + 1}))
      (Forms.vertexSimple_arrow k false edge)
  · exact isoOfZeroArrows
      ((eqToIso (Forms.vertexSimple_vertex_of_ne k (by decide : (false : Vertex) ≠ true)).symm).toLinearEquiv)
      ((eqToIso (Forms.vertexSimple_vertex_self k true).symm).toLinearEquiv)
      (arrow_representation (0 : PUnit.{max w d + 1} →ₗ[k] ULift.{d} k))
      (Forms.vertexSimple_arrow k true edge)
  · exact Iso.refl _

private abbrev family (k : Type w) [Field k] (n : Kind → ℕ) :
    (Σ j, Fin (n j)) → Rep.{w, d} k := fun j => standard k j.1

private def sourceCoordinates (n : Kind → ℕ) :
    (piRep (family.{w, d} k n)).vertex false ≃ₗ[k]
      (Fin (n .source) → ULift.{d} k) × (Fin (n .identity) → ULift.{d} k) where
  toFun x := (fun j => x ⟨.source, j⟩, fun j => x ⟨.identity, j⟩)
  invFun x j := match j with
    | ⟨.source, l⟩ => x.1 l
    | ⟨.target, _⟩ => PUnit.unit
    | ⟨.identity, l⟩ => x.2 l
  left_inv x := by
    funext j
    rcases j with ⟨j, l⟩
    cases j
    · rfl
    · change PUnit.unit = (x ⟨_, l⟩ : PUnit.{max w d + 1})
      exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def targetCoordinates (n : Kind → ℕ) :
    (piRep (family.{w, d} k n)).vertex true ≃ₗ[k]
      (Fin (n .identity) → ULift.{d} k) × (Fin (n .target) → ULift.{d} k) where
  toFun x := (fun j => x ⟨.identity, j⟩, fun j => x ⟨.target, j⟩)
  invFun x j := match j with
    | ⟨.source, _⟩ => PUnit.unit
    | ⟨.target, l⟩ => x.2 l
    | ⟨.identity, l⟩ => x.1 l
  left_inv x := by
    funext j
    rcases j with ⟨j, l⟩
    cases j
    · change PUnit.unit = (x ⟨_, l⟩ : PUnit.{max w d + 1})
      exact Subsingleton.elim _ _
    · rfl
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem targetCoordinates_arrow (n : Kind → ℕ)
    (x : (piRep (family.{w, d} k n)).vertex false) :
    targetCoordinates n ((piRep (family.{w, d} k n)).arrow edge x) =
      ((sourceCoordinates n x).2, 0) := by
  apply Prod.ext
  · funext j
    change (P₁.{w, d} k).arrow edge (x ⟨.identity, j⟩) = _
    rw [identity_arrow]
    rfl
  · funext j
    change (standard.{w, d} k .target).arrow edge (x ⟨.target, j⟩) = _
    rw [arrow_representation]
    rfl

private noncomputable def basisCoordinates (X : Type (max w d)) [AddCommGroup X] [Module k X]
    [Module.Finite k X] : X ≃ₗ[k] (Fin (Module.finrank k X) → ULift.{d} k) :=
  (Module.finBasis k X).equivFun.trans (LinearEquiv.piCongrRight fun _ => (ULift.moduleEquiv : ULift.{d} k ≃ₗ[k] k).symm)

/-- The restriction of an arrow to a complement of its kernel identifies that complement
with the image of the arrow. -/
private noncomputable def complementEquivRange {X Y : Type (max w d)}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (T : X →ₗ[k] Y) (L : Submodule k X) (hL : IsCompl T.ker L) : L ≃ₗ[k] T.range := by
  let f := T.rangeRestrict.comp L.subtype
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · apply (LinearMap.ker_eq_bot).1
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply Submodule.disjoint_def.mp hL.disjoint _ _ x.property
    change T x = 0
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  · rintro ⟨y, x, rfl⟩
    let e := T.ker.prodEquivOfIsCompl L hL
    let z := e.symm x
    refine ⟨z.2, Subtype.ext ?_⟩
    change T z.2 = T x
    conv_rhs => rw [← e.apply_symm_apply x]
    change T z.2 = T ((z.1 : X) + z.2)
    rw [map_add, LinearMap.mem_ker.mp z.1.property, zero_add]

theorem decomposition : SingleArrowObjectsSpec.Decomposition.{w, d} := by
  intro k _ V
  classical
  let W : Rep.{w, d} k := V.obj
  have h₁ : Module.Finite k (W.vertex false) := V.property false
  have h₂ : Module.Finite k (W.vertex true) := V.property true
  let T := W.arrow edge
  obtain ⟨L, hL⟩ := T.ker.exists_isCompl
  obtain ⟨C, hC⟩ := T.range.exists_isCompl
  let n : Kind → ℕ
    | .source => Module.finrank k T.ker
    | .target => Module.finrank k C
    | .identity => Module.finrank k T.range
  let eK := basisCoordinates.{w, d} (k := k) T.ker
  let eR := basisCoordinates.{w, d} (k := k) T.range
  let eC := basisCoordinates.{w, d} (k := k) C
  let eL := complementEquivRange T L hL
  let σ := T.ker.prodEquivOfIsCompl L hL
  let τ := T.range.prodEquivOfIsCompl C hC
  let f : (piRep (family.{w, d} k n)).vertex false ≃ₗ[k] W.vertex false :=
    (sourceCoordinates n).trans ((eK.symm.prodCongr (eR.symm.trans eL.symm)).trans σ)
  let g : (piRep (family.{w, d} k n)).vertex true ≃ₗ[k] W.vertex true :=
    (targetCoordinates n).trans ((eR.symm.prodCongr eC.symm).trans τ)
  have commutes (x : (piRep (family.{w, d} k n)).vertex false) :
      g ((piRep (family.{w, d} k n)).arrow edge x) = W.arrow edge (f x) := by
    let c := sourceCoordinates n x
    change τ (eR.symm (targetCoordinates n ((piRep (family.{w, d} k n)).arrow edge x)).1,
      eC.symm (targetCoordinates n ((piRep (family.{w, d} k n)).arrow edge x)).2) =
        T (σ (eK.symm c.1, eL.symm (eR.symm c.2)))
    rw [targetCoordinates_arrow]
    change (eR.symm c.2 : W.vertex true) + (eC.symm 0 : W.vertex true) =
      T ((eK.symm c.1 : W.vertex false) + (eL.symm (eR.symm c.2) : W.vertex false))
    rw [map_zero, Submodule.coe_zero, add_zero, map_add,
      LinearMap.mem_ker.mp (eK.symm c.1).property, zero_add]
    exact (congrArg Subtype.val (eL.apply_symm_apply (eR.symm c.2))).symm
  exact ⟨n, ⟨(isoMk f g commutes).symm ≪≫ piRepIsoBiproduct (family k n) ≪≫
    biproduct.mapIso (fun j => standardIso j.1)⟩⟩

end Decomposition

section Classification

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def splitBiproduct {A : Type*} [Category A] [Preadditive A]
    [HasBinaryBiproducts A] [HasFiniteBiproducts A]
    {J : Type} [Finite J] (F : J → A) (i : J) :
    (⨁ F) ≅ F i ⊞ (⨁ Subtype.restrict (fun j => j ≠ i) F) := by
  classical
  let b : BinaryBicone (F i) (⨁ Subtype.restrict (fun j => j ≠ i) F) :=
    { pt := ⨁ F
      fst := biproduct.π F i
      snd := biproduct.toSubtype F (fun j => j ≠ i)
      inl := biproduct.ι F i
      inr := biproduct.fromSubtype F (fun j => j ≠ i)
      inl_fst := by simp
      inl_snd := by simp
      inr_fst := by simp
      inr_snd := by simp }
  refine biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal b ?_)
  apply biproduct.hom_ext
  intro j
  change (biproduct.π F i ≫ biproduct.ι F i +
      biproduct.toSubtype F (fun l => l ≠ i) ≫ biproduct.fromSubtype F (fun l => l ≠ i)) ≫
        biproduct.π F j = 𝟙 (⨁ F) ≫ biproduct.π F j
  by_cases h : j = i
  · subst j
    simp [Preadditive.add_comp, Category.assoc]
  · simp [Preadditive.add_comp, Category.assoc, h, Ne.symm h]

private theorem indecomposable_of_iso {V W : Rep.{w, d} k} (e : V ≅ W)
    (h : Indecomposable W) : Indecomposable V :=
  ⟨fun z => h.1 (z.of_iso e.symm), fun Y Z f => h.2 Y Z (e.symm ≪≫ f)⟩

theorem classification : SingleArrowObjectsSpec.Classification.{w, d} := by
  intro k _ V
  constructor
  · intro h
    obtain ⟨n, ⟨e⟩⟩ := decomposition.{w, d} k V
    let J := Σ j, Fin (n j)
    let F : J → Rep.{w, d} k := fun j => representative k j.1
    have hJ : Nonempty J := by
      by_contra hn
      let : IsEmpty J := not_nonempty_iff.mp hn
      have hz : IsZero (⨁ F) := (IsZero.iff_id_eq_zero _).mpr
        (biproduct.hom_ext _ _ fun j => isEmptyElim j)
      exact h.1 (hz.of_iso e)
    obtain ⟨j⟩ := hJ
    let s := e ≪≫ splitBiproduct F j
    have hz := (h.2 _ _ s).resolve_left (indecomposable_representatives.{w, d} k j.1).1
    let := (Biprod.isIso_inl_iff_isZero (F j) _).mpr hz
    let f : V.obj ≅ F j := s ≪≫ (asIso biprod.inl).symm
    exact ⟨j.1, ⟨f⟩, fun l ⟨g⟩ => distinct_representatives k l j.1 ⟨g.symm ≪≫ f⟩⟩
  · rintro ⟨j, ⟨e⟩, _⟩
    exact indecomposable_of_iso e (indecomposable_representatives k j)

end Classification

section PathProjective

open scoped ModuleCat
open RM03 (Path PathAlgebra)
open RM03.ModuleVerticesSpec (vertexSpace arrowMap)

private noncomputable abbrev pathProjective (k : Type w) [Field k] :=
  ModuleCat.of (PathAlgebra k Vertex) (ULift.{d} (Forms.projectiveAt k (false : Vertex)))

private def generatingPath : (i : Vertex) → Quiver.Path (false : Vertex) i
  | false => .nil
  | true => edge.toPath

private theorem eq_generatingPath {i : Vertex} (p : Quiver.Path (false : Vertex) i) :
    p = generatingPath i := by
  cases p with
  | nil => rfl
  | cons p a =>
    rcases a with ⟨⟨⟩, rfl, rfl⟩
    cases p with
    | nil => rfl
    | cons p a => exact (Bool.noConfusion a.property.2)

private noncomputable abbrev pathVector (k : Type w) [Field k] (i : Vertex) : PathAlgebra k Vertex :=
  PathAlgebra.ofPath k (Path.ofPath (generatingPath i))

private noncomputable def generator (i : Vertex) : vertexSpace (pathProjective.{w, d} k) i := by
  let v : pathProjective.{w, d} k := ULift.up
    ⟨pathVector k i, (Forms.mem_projectiveAt k false _).mpr ⟨pathVector k i, by simp⟩⟩
  refine ⟨v, ⟨v, ?_⟩⟩
  apply ULift.ext
  apply Subtype.ext
  change PathAlgebra.vertex k i * pathVector k i = pathVector k i
  simp

private abbrev underlying {i : Vertex} (x : vertexSpace (pathProjective.{w, d} k) i) :
    PathAlgebra k Vertex := x.val.down.val

private theorem scalar_generator (i : Vertex)
    (x : vertexSpace (pathProjective.{w, d} k) i) :
    ∃ c : k, c • pathVector k i = underlying x := by
  obtain ⟨a, ha⟩ := (Forms.mem_projectiveAt k false _).mp x.val.down.property
  have hfix : PathAlgebra.vertex k i * underlying x = underlying x := by
    have h := RM03.ModuleVertices.vertex_smul_coe i i x
    rw [ite_eq_left rfl] at h
    exact congrArg (fun y : pathProjective.{w, d} k => y.down.val) h
  have hx := (PathAlgebra.mem_corner (k := k) false i (underlying x)).mpr
    ⟨a, by rw [mul_assoc, ha, hfix]⟩
  have hpaths : Set.range (fun p : Quiver.Path (false : Vertex) i =>
      PathAlgebra.ofPath k (Path.ofPath p)) = {pathVector k i} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      rw [eq_generatingPath p]
      rfl
    · intro h
      rw [Set.mem_singleton_iff] at h
      exact ⟨generatingPath i, h.symm⟩
  rw [PathAlgebra.corner_eq_span, hpaths] at hx
  exact Submodule.mem_span_singleton.mp hx

private theorem underlying_smul {i : Vertex} (c : k)
    (x : vertexSpace (pathProjective.{w, d} k) i) :
    underlying (c • x) = c • underlying x := by
  change algebraMap k (PathAlgebra k Vertex) c * underlying x = _
  exact (Algebra.smul_def _ _).symm

private noncomputable def projectiveCoordinates (i : Vertex) :
    ULift.{d} k ≃ₗ[k] vertexSpace (pathProjective.{w, d} k) i := by
  let f : ULift.{d} k →ₗ[k] vertexSpace (pathProjective.{w, d} k) i :=
    (LinearMap.toSpanSingleton k _ (generator (k := k) i)).comp
      (ULift.moduleEquiv : ULift.{d} k ≃ₗ[k] k).toLinearMap
  have hf (x : ULift.{d} k) : underlying (f x) = x.down • pathVector k i :=
    underlying_smul.{w, d} x.down (generator i)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    apply ULift.ext
    have hv : pathVector k i ≠ 0 := by
      exact fun hz => (PathAlgebra.basis k Vertex).ne_zero _
        ((PathAlgebra.basis_apply (Path.ofPath (generatingPath i))).trans hz)
    apply smul_left_injective k hv
    exact (hf a).symm.trans ((congrArg underlying.{w, d} h).trans (hf b))
  · intro x
    obtain ⟨c, hc⟩ := scalar_generator i x
    exact ⟨ULift.up c, Subtype.ext (ULift.ext (Subtype.ext ((hf _).trans hc)))⟩

private theorem projectiveCoordinates_apply (i : Vertex) (x : ULift.{d} k) :
    underlying (projectiveCoordinates i x) = x.down • pathVector k i :=
  underlying_smul.{w, d} x.down (generator i)

theorem projective_agreement : SingleArrowObjectsSpec.ProjectiveAgreement.{w, d} := by
  intro k _
  let M := pathProjective.{w, d} k
  let V : Rep.{w, d} k := RM03.ModuleVerticesSpec.representation M
  let f := projectiveCoordinates (k := k) false
  let g := projectiveCoordinates (k := k) true
  have h (x : ULift.{d} k) : g ((P₁.{w, d} k).arrow edge x) = V.arrow edge (f x) := by
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    change underlying (g ((P₁.{w, d} k).arrow edge x)) = underlying (V.arrow edge (f x))
    calc
      underlying (g ((P₁.{w, d} k).arrow edge x)) = x.down • pathVector k true := by
        rw [identity_arrow]
        exact projectiveCoordinates_apply true x
      _ = PathAlgebra.arrow k edge * (x.down • pathVector k false) := by
        rw [mul_smul_comm]
        congr 1
        change PathAlgebra.arrow k edge =
          PathAlgebra.arrow k edge * PathAlgebra.vertex k (false : Vertex)
        rw [PathAlgebra.arrow_eq_ofPath, PathAlgebra.ofPath_mul_vertex,
          ite_eq_left (show (Path.arrow edge).source = false from rfl)]
      _ = underlying (V.arrow edge (f x)) := by
        rw [← projectiveCoordinates_apply false x]
        rw [show V.arrow edge = arrowMap M edge from RM03.ModuleVertices.representation_arrow M edge]
        exact (congrArg (fun y : M => y.down.val) (RM03.ModuleVertices.coe_arrowMap edge (f x))).symm
  exact ⟨(isoMk (V := P₁ k) (W := V) f g h).symm⟩

end PathProjective

end RepTheorySurvey.Quiver.SingleArrowObjects
