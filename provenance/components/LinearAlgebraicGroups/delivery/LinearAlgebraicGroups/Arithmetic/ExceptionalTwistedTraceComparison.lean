import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
import LinearAlgebraicGroups.Arithmetic.ExceptionalSteinbergSection
import LinearAlgebraicGroups.Descent.RelativeFormComparison
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison

open LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AutomorphismSequence (AdjointQuotient RelativeAut groupSections relativePoints
  restrictIso innerAut scalarAut forgetPinning)
open Specs.ExceptionalSteinbergSection (IsGeometricImage geometricTestMap)
open Specs.ExceptionalTwistedTraceComparison
open Specs.GeometricRadicals (IsReductive)
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut automorphismAction IsInduced)
open Specs.SteinbergPinnedDescent (coefficientAction comparisonOnPoints pinnedAction pinnedPointMap
  diagramPermutation permuteParameters traceValue)
open Descent.NonabelianCohomology (Cocycle pointAction)
open private reductive_of_geometric_iso from LinearAlgebraicGroups.Descent.PinnedPairDescent
open private LinearAlgebraicGroups.SmoothOrbit.exists_rational_point
  from LinearAlgebraicGroups.Flag.SmoothOrbit

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

private theorem comparison_transports_action {G H : GroupScheme k}
    (e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (σ : Gal(S/k)) (y : GroupPoints G (CommAlgCat.of k S)) :
    comparisonOnPoints e (evalAut (transportedAut k S e σ) (coefficientAction S G σ y)) =
      coefficientAction S H σ (comparisonOnPoints e y) := by
  let U := Over.mk (𝟙 (fieldTest k S))
  let W := Over.mk (fieldMap k S σ)
  let v : W ⟶ U := Over.homMk (fieldMap k S σ) (Category.comp_id _)
  have hn :
      coefficientAction S H σ (comparisonOnPoints e y) =
        (e.hom.app (op W)).hom (coefficientAction S G σ y) :=
    (ConcreteCategory.congr_hom (e.hom.naturality v.op) y).symm
  rw [hn]
  change comparisonOnPoints e
    ((e.inv.app (op U)).hom ((e.hom.app (op W)).hom (coefficientAction S G σ y))) = _
  exact (comparisonOnPoints e).apply_symm_apply _

private def pushCocycle {Γ : Type u} {M : Type v} {N : Type w}
    [Group Γ] [TopologicalSpace Γ] [Group M] [TopologicalSpace M] [DiscreteTopology M]
    [Group N] [TopologicalSpace N] {r : Γ →* MulAut M} {s : Γ →* MulAut N}
    (p : M →* N) (hp : ∀ σ x, p (r σ x) = s σ (p x)) (a : Cocycle r) :
    Cocycle s :=
  ⟨p ∘ a.val, continuous_of_discreteTopology.comp a.property.1, fun σ τ ↦ by
    change p (a.val (σ * τ)) = p (a.val σ) * s σ (p (a.val τ))
    rw [a.property.2 σ τ, map_mul, hp]⟩

private theorem inner_conjugation {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    {inn : InnerMap Q} (hi : ActsByConjugation inn)
    (g y : GroupPoints G.val (CommAlgCat.of k S)) :
    adjointAction inn (projectionOnPoints Q g) y = g * y * g⁻¹ := by
  have h := hi (fieldTest k S) g
  change inn.app (op (fieldTest k S)) ⟨projectionOnPoints Q g⟩ = innerAut g at h
  unfold adjointAction
  rw [h]
  let g' : GroupPoints G.val (CommAlgCat.of k S) := 𝟙 (fieldTest k S) ≫ g
  change g' * y * g'⁻¹ = _
  rw [show g' = g from Category.id_comp _]

private theorem comparison_extends_points {K : Type u} [Field K] [Algebra k K]
    {G H : GroupScheme k} (a : CommAlgCat.of k S ⟶ CommAlgCat.of k K)
    (e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (x : GroupPoints G (CommAlgCat.of k S)) :
    comparisonOnPoints (restrictIso ((testSpec k).map a.op) e) (mapPoints a x) =
      mapPoints a (comparisonOnPoints e x) := by
  let U := Over.mk (𝟙 (fieldTest k S))
  let W := Over.mk ((testSpec k).map a.op)
  let v : W ⟶ U := Over.homMk ((testSpec k).map a.op) (Category.comp_id _)
  exact ConcreteCategory.congr_hom (e.hom.naturality v.op) x

private theorem reductive_of_relative_iso {G H : AffineAlgebraicGroup k} [Algebra.IsAlgebraic k S]
    (e : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S))
    (hG : IsReductive G) :
    IsReductive H := by
  let f : S →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let a := (testSpec k).map (CommAlgCat.ofHom f).op
  obtain ⟨c, _⟩ := Descent.RelativeFormComparison.schemeIsomorphismComparison
    (S := AlgebraicClosure k) G.val H.val
  exact reductive_of_geometric_iso (G := G) (H := H) (c.symm (restrictIso a e)) hG

theorem adjointTwisting : AdjointTwisting.{u} := by
  intro k S _ _ _ _ G hG Q a
  let : TopologicalSpace (GroupPoints Q.quotient.val (CommAlgCat.of k S)) := ⊥
  let : DiscreteTopology (GroupPoints Q.quotient.val (CommAlgCat.of k S)) := ⟨rfl⟩
  let : TopologicalSpace (RelativeAut G.val (fieldTest k S)) := ⊥
  let : TopologicalSpace (Gal(S/k)) := krullTopology k S
  obtain ⟨inn, hLift, hinj⟩ := Descent.AutomorphismSequence.adjointInner G Q
  let p : GroupPoints Q.quotient.val (CommAlgCat.of k S) →* RelativeAut G.val (fieldTest k S) :=
    (inn.app (op (fieldTest k S))).hom.comp
      { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hp (σ : Gal(S/k)) (z : GroupPoints Q.quotient.val (CommAlgCat.of k S)) :
      p (pointAction k S Q.quotient.val.X σ z) = automorphismAction k S G.val σ (p z) :=
    ConcreteCategory.congr_hom (inn.naturality (fieldMap k S σ).op)
      (ULift.up z : (groupSections Q.quotient.val).obj (op (fieldTest k S)))
  let b : Cocycle (automorphismAction k S G.val) := pushCocycle p hp a
  obtain ⟨C⟩ := Descent.RelativeFormComparison.relativeFormClassification (S := S) G
  obtain ⟨H, e, he, _⟩ := C.realizes b
  refine ⟨⟨H.val, reductive_of_relative_iso e hG, e, inn, hLift, hinj,
    fun σ ↦ (he σ).symm, ?_⟩⟩
  intro x σ
  let y := (comparisonOnPoints e).symm (extendPoint (S := S) x)
  have hy : comparisonOnPoints e y = extendPoint (S := S) x :=
    (comparisonOnPoints e).apply_symm_apply _
  have hx : coefficientAction S H.val.val σ (extendPoint x) = extendPoint x :=
    (SteinbergPinnedDescent.rationalPoints H.val (extendPoint x)).mpr ⟨x, rfl⟩ σ
  have h := comparison_transports_action e σ y
  rw [hy, hx, ← he σ] at h
  exact (comparisonOnPoints e).injective (h.trans hy.symm)

theorem simplyConnectedTwisting : SimplyConnectedTwisting.{u} := by
  intro k S _ _ _ _ G hG Q b
  let : TopologicalSpace (Gal(S/k)) := krullTopology k S
  let : TopologicalSpace (GroupPoints G.val (CommAlgCat.of k S)) := ⊥
  let : DiscreteTopology (GroupPoints G.val (CommAlgCat.of k S)) := ⟨rfl⟩
  let : TopologicalSpace (GroupPoints Q.quotient.val (CommAlgCat.of k S)) := ⊥
  have hp (σ : Gal(S/k)) (z : GroupPoints G.val (CommAlgCat.of k S)) :
      projectionOnPoints Q (pointAction k S G.val.X σ z) =
        pointAction k S Q.quotient.val.X σ (projectionOnPoints Q z) := by
    change (fieldMap k S σ ≫ z) ≫ Q.projection.hom.hom =
      fieldMap k S σ ≫ z ≫ Q.projection.hom.hom
    exact Category.assoc _ _ _
  let a : PointCocycle (S := S) Q.quotient.val := pushCocycle (projectionOnPoints Q) hp b
  obtain ⟨T⟩ := adjointTwisting G hG Q a
  refine ⟨a, T, fun _ ↦ rfl, ?_⟩
  intro x σ
  have h := T.fixed x σ
  dsimp only at h ⊢
  change adjointAction T.inner (projectionOnPoints Q (b.val σ)) _ = _ at h
  rwa [inner_conjugation T.onLift] at h

theorem pinnedActionComparison : PinnedActionComparison.{u} := by
  intro k S _ _ _ A P D l Q E ω V σ y
  have h := comparison_transports_action V.trivialization σ y
  have hs : QuasiSplitInnerForms.pinnedSection E (S := S) (ω σ) =
      scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l (ω σ))) (fieldTest k S) :=
    E.sectionOnConstants _ _
  rw [V.transport_eq, hs] at h
  exact h

private theorem adjoint_projection_surjective_over_closed_field {K : Type u}
    [Field K] [Algebra k K] [IsAlgClosed K]
    {G : AffineAlgebraicGroup k} (Q : AdjointQuotient G) :
    Function.Surjective (projectionOnPoints (S := K) Q) := by
  intro q
  let p := Q.projection.hom.hom
  let q' : fieldTest k K ⟶ Q.quotient.val.X := q
  let F : SchemeOver K := Over.mk (pullback.snd p.left q'.left)
  have pb := IsPullback.of_hasPullback p.left q'.left
  have hs : Surjective F.hom := MorphismProperty.of_isPullback pb Q.fppf.2.1
  let : LocallyOfFinitePresentation p.left := Q.fppf.2.2
  let : LocallyOfFiniteType F.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) pb inferInstance
  let : Surjective F.hom := hs
  let : Nonempty F.left := F.hom.surjective.nonempty
  obtain ⟨z⟩ := LinearAlgebraicGroups.SmoothOrbit.exists_rational_point F
  have hz : z.left ≫ pullback.snd p.left q'.left = 𝟙 _ := Over.w z
  have hq : (z.left ≫ pullback.fst p.left q'.left) ≫ p.left = q'.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hz, Category.id_comp]
  let g : fieldTest k K ⟶ G.val.X :=
    Over.homMk (z.left ≫ pullback.fst p.left q'.left) (by
      rw [← Over.w p, ← Category.assoc, hq]
      exact Over.w q')
  exact ⟨g, Over.OverMorphism.ext hq⟩

private theorem adjoint_action_extends_points {K : Type u} [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G} (inn : InnerMap Q)
    (a : CommAlgCat.of k S ⟶ CommAlgCat.of k K)
    (q : GroupPoints Q.quotient.val (CommAlgCat.of k S))
    (y : GroupPoints G.val (CommAlgCat.of k S)) :
    mapPoints a (adjointAction inn q y) =
      adjointAction inn (mapPoints a q) (mapPoints a y) := by
  let u := (testSpec k).map a.op
  have h := ConcreteCategory.congr_hom (inn.naturality u.op)
    (ULift.up q : (groupSections Q.quotient.val).obj (op (fieldTest k S)))
  change inn.app (op (fieldTest k K)) ⟨mapPoints a q⟩ =
    AutomorphismSequence.restrictAut u (inn.app (op (fieldTest k S)) ⟨q⟩) at h
  have h' := comparison_extends_points a
    (inn.app (op (fieldTest k S)) (ULift.up q : (groupSections Q.quotient.val).obj
      (op (fieldTest k S)))).asIso y
  exact h'.symm.trans (congrArg (fun b => evalAut b (mapPoints a y)) h.symm)

private theorem trace_extends_points {I : Type u} [Fintype I] [DecidableEq I]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    (ρ : RootWeightAction.Representation P.pair.G.val I)
    (f : S →ₐ[k] AlgebraicClosure k)
    (y : GroupPoints P.pair.G.val (CommAlgCat.of k S)) :
    traceValue ρ _ (mapPoints (CommAlgCat.ofHom f) y) = f (traceValue ρ _ y) := by
  have h := ConcreteCategory.congr_hom (ρ.naturality (CommAlgCat.ofHom f)) y
  have hm := congrArg (fun v : Matrix.GeneralLinearGroup I (AlgebraicClosure k) ↦ v.val) h
  change (ρ.app _ (mapPoints (CommAlgCat.ofHom f) y)).val =
    f.toRingHom.mapMatrix (ρ.app _ y).val at hm
  unfold traceValue
  rw [hm]
  exact (AddMonoidHom.map_trace f.toRingHom (ρ.app _ y).val).symm

theorem adjointTraceInvariant : AdjointTraceInvariant.{u} := by
  intro k S I _ _ _ _ _ _ A P G Q e inn hLift ρ q y
  let K := AlgebraicClosure k
  let f : S →ₐ[k] K := IsAlgClosed.lift
  let a := CommAlgCat.ofHom f
  let eK := comparisonOnPoints (restrictIso ((testSpec k).map a.op) e)
  let z := (comparisonOnPoints e).symm (adjointAction inn q (comparisonOnPoints e y))
  obtain ⟨g, hg⟩ := adjoint_projection_surjective_over_closed_field Q (mapPoints a q)
  let yK : GroupPoints P.pair.G.val (CommAlgCat.of k K) := mapPoints a y
  have h : eK (mapPoints a z) = eK (eK.symm g * yK * (eK.symm g)⁻¹) := by
    change comparisonOnPoints (restrictIso ((testSpec k).map a.op) e) (mapPoints a z) = _
    rw [comparison_extends_points, map_mul, map_mul, map_inv, eK.apply_symm_apply]
    have hz : comparisonOnPoints e z = adjointAction inn q (comparisonOnPoints e y) :=
      (comparisonOnPoints e).apply_symm_apply _
    rw [hz, adjoint_action_extends_points, ← hg, inner_conjugation hLift]
    rw [show eK yK = mapPoints a (comparisonOnPoints e y) from
      comparison_extends_points a e y]
  apply f.injective
  change f (traceValue ρ _ z) = f (traceValue ρ _ y)
  rw [← trace_extends_points ρ f z, ← trace_extends_points ρ f y]
  rw [eK.injective h]
  exact SteinbergPinnedDescent.traceConjugacy ρ _ _ _

theorem fixedTraceTuple : FixedTraceTuple.{u} := by
  intro k S _ _ _ _ A P D l Q₀ E ω V Q a T x I _ _ ρ
  dsimp only
  intro h σ
  let e := comparisonOnPoints V.trivialization
  let y := e.symm ((comparisonOnPoints T.trivialization).symm (extendPoint x))
  let yσ := pinnedAction S (l (ω σ)).asIso.hom σ y
  have hy : adjointAction T.inner (a.val σ) (e yσ) = e y := by
    change adjointAction T.inner (a.val σ)
      (comparisonOnPoints V.trivialization (pinnedAction S (l (ω σ)).asIso.hom σ y)) = e y
    rw [pinnedActionComparison V σ y]
    change adjointAction T.inner (a.val σ) (coefficientAction S V.model.val.val σ (e y)) = e y
    rw [e.apply_symm_apply]
    exact T.fixed x σ
  change permuteParameters (diagramPermutation D (ω σ)) σ (fun i ↦ traceValue (ρ i) _ y) =
    fun i ↦ traceValue (ρ i) _ y
  rw [← h σ y]
  funext i
  have hinv := adjointTraceInvariant V.trivialization T.inner T.onLift (ρ i) (a.val σ) yσ
  change traceValue (ρ i) _ (e.symm (adjointAction T.inner (a.val σ) (e yσ))) =
    traceValue (ρ i) _ yσ at hinv
  rw [hy, e.symm_apply_apply] at hinv
  exact hinv.symm

private theorem comparison_extension_square {G H : GroupScheme k}
    (f : S →ₐ[k] AlgebraicClosure k)
    (e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (i : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H)
    (j : (groupBaseChange k (AlgebraicClosure k)).obj G ≅
      (groupBaseChange k (AlgebraicClosure k)).obj H)
    (hi : IsInduced k S i e)
    (hj : IsInduced k (AlgebraicClosure k) j
      (restrictIso ((testSpec k).map (CommAlgCat.ofHom f).op) e)) :
    j.hom.hom.hom.left ≫ extensionProjection f H.X =
      extensionProjection f G.X ≫ i.hom.hom.hom.left := by
  let K := AlgebraicClosure k
  let a := (testSpec k).map (CommAlgCat.ofHom f).op
  let p₁ := pullback.fst G.X.hom (fieldSpecMap k K)
  let p₂ := pullback.snd G.X.hom (fieldSpecMap k K)
  let X : SchemeOver k := Over.mk (p₁ ≫ G.X.hom)
  let v : X ⟶ fieldTest k K := Over.homMk p₂ pullback.condition.symm
  let p : X ⟶ G.X := Over.homMk p₁ rfl
  let U := Over.mk v
  have hlift : pullback.lift p.left v.left ((Over.w p).trans (Over.w v).symm) =
      𝟙 _ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp]
      rfl
    · rw [pullback.lift_snd, Category.id_comp]
      rfl
  have hS := hi ((Over.map a).obj U) p
  have hK := hj U p
  have h₁ : j.hom.hom.hom.left ≫ pullback.fst H.X.hom (fieldSpecMap k K) =
      extensionProjection f G.X ≫ i.hom.hom.hom.left ≫
        pullback.fst H.X.hom (fieldSpecMap k S) := by
    have hS' : ((e.hom.app (op ((Over.map a).obj U))).hom p).left =
        extensionProjection f G.X ≫ i.hom.hom.hom.left ≫
          pullback.fst H.X.hom (fieldSpecMap k S) := hS
    have hK' : ((e.hom.app (op ((Over.map a).obj U))).hom p).left =
        pullback.lift p.left v.left ((Over.w p).trans (Over.w v).symm) ≫
          j.hom.hom.hom.left ≫ pullback.fst H.X.hom (fieldSpecMap k K) := hK
    rw [hlift, Category.id_comp] at hK'
    exact hK'.symm.trans hS'
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [show extensionProjection f H.X ≫ pullback.fst H.X.hom (fieldSpecMap k S) =
      pullback.fst H.X.hom (fieldSpecMap k K) from pullback.lift_fst ..]
    exact h₁
  · have hF (Y : SchemeOver k) : extensionProjection f Y ≫
        pullback.snd Y.hom (fieldSpecMap k S) =
          pullback.snd Y.hom (fieldSpecMap k K) ≫ a.left := pullback.lift_snd ..
    have hKbase : j.hom.hom.hom.left ≫ pullback.snd H.X.hom (fieldSpecMap k K) = p₂ :=
      Over.w j.hom.hom.hom
    have hSbase : i.hom.hom.hom.left ≫ pullback.snd H.X.hom (fieldSpecMap k S) =
        pullback.snd G.X.hom (fieldSpecMap k S) := Over.w i.hom.hom.hom
    rw [Category.assoc, hF H.X, ← Category.assoc, hKbase,
      Category.assoc, hSbase, hF G.X]

theorem geometricComparison : GeometricComparison.{u} := by
  intro k S _ _ _ G H f e
  dsimp only
  let K := AlgebraicClosure k
  let a := CommAlgCat.ofHom f
  let u := (testSpec k).map a.op
  obtain ⟨cS, hcS⟩ := Descent.RelativeFormComparison.schemeIsomorphismComparison (S := S) G H
  obtain ⟨cK, hcK⟩ := Descent.RelativeFormComparison.schemeIsomorphismComparison (S := K) G H
  let i := cS.symm e
  let j := cK.symm (restrictIso u e)
  have hi : IsInduced k S i e := (hcS _ _).mpr (cS.apply_symm_apply _)
  have hj : IsInduced k K j (restrictIso u e) := (hcK _ _).mpr (cK.apply_symm_apply _)
  refine ⟨i, j, hi, hj, comparison_extension_square f e i j hi hj, ?_⟩
  intro x x' hx
  let y : GroupPoints G (CommAlgCat.of k K) := mapPoints a x
  let U := Over.mk (𝟙 (fieldTest k K))
  have he := comparison_extends_points a e x
  have hx₁ := congrArg Over.Hom.left hx
  change x'.left ≫ pullback.fst G.X.hom (fieldSpecMap k K) =
    ((testSpec k).map (geometricTestMap f).op).left ≫ x.left at hx₁
  have hx₂ : x'.left ≫ pullback.snd G.X.hom (fieldSpecMap k K) = 𝟙 _ := by
    have hw := Over.w (show Points _ (CommAlgCat.of K K) from x')
    exact hw.trans (by simp [testSpec]; rfl)
  have hxLift : pullback.lift y.left U.hom.left
      ((Over.w y).trans (Over.w U.hom).symm) = x'.left := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hx₁.symm
    · rw [pullback.lift_snd]
      change 𝟙 _ = x'.left ≫ pullback.snd G.X.hom (fieldSpecMap k K)
      exact hx₂.symm
  have h : (comparisonOnPoints (restrictIso u e) y).left =
      pullback.lift y.left U.hom.left ((Over.w y).trans (Over.w U.hom).symm) ≫
        j.hom.hom.hom.left ≫ pullback.fst H.X.hom (fieldSpecMap k K) := hj U y
  have h' := h.trans (congrArg
    (fun p ↦ p ≫ j.hom.hom.hom.left ≫ pullback.fst H.X.hom (fieldSpecMap k K)) hxLift)
  have he' := congrArg (fun p : GroupPoints H (CommAlgCat.of k K) ↦
    (show fieldTest k K ⟶ H.X from p).left) he
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).trans (h'.symm.trans he')

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
