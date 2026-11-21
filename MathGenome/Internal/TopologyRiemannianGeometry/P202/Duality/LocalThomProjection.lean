import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LocalThomProjection
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.ThomClass

/-! The actual local projection expression of an ambient Thom class.
The proof first uses detection by fiber restrictions on the full normal chart,
then restricts to the tubular domain and transports along the tubular inverse. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
universe u v
namespace P202.LocalThomProjection
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.LocalThomProjection P202.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M} {i : P → M}
attribute [local instance] normalTopology
variable (R : Type v) [CommRing R]

lemma normalRegionProjection_eq (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) :
    normalRegionProjection N a U hU = (normalChartPairIso N a U hU).hom ≫
      secondProductProjection (TopCat.of U) (modelPair.{u} (n-m)) :=
  PairMap.ext _ _ rfl

/-- In degree zero, fiber restrictions detect a class just by evaluating at each
point of the total bundle. This does not require a positive-dimensional fiber. -/
lemma normalHasValues_zero_ext (N : NormalBundle T S i) (U : Set P)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) 0)
    (b c : relativeCohomology R R (normalOverPair N U) 0)
    (hb : NormalHasValues R N U 0 g b) (hc : NormalHasValues R N U 0 g c) : b = c := by
  apply relativeZeroValue_ext R R
  intro z
  have h := congrArg (fun x => relativeZeroValue R R (fiberPair N z.val.proj) x
      (⟨z.val, rfl⟩ : Fiber N z.val.proj))
    ((hb z.val.proj z.property).trans (hc z.val.proj z.property).symm)
  exact (relativeZeroValue_natural R R (fiberToNormalOver N U z.val.proj z.property)
    b ⟨z.val, rfl⟩).symm.trans (h.trans
      (relativeZeroValue_natural R R (fiberToNormalOver N U z.val.proj z.property)
        c ⟨z.val, rfl⟩))

lemma normalChart_class_eq_projection (N : NormalBundle T S i) (d : ℕ)
    (hd : n-m=d)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (a : P) (U : Set P) (hopen : IsOpen U) (hU : U ⊆ (normalBundle N).baseSet a)
    (cModel : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ))
    (hg : ∀ (p : P) (hp : p ∈ U),
      (relativeCohomologyFunctor R R (d : ℤ)).map (fiberCoordinates N a p (hU hp)).op cModel = g p)
    (c : relativeCohomology R R (normalOverPair N U) (d : ℤ))
    (hc : NormalHasValues R N U d g c) :
    c = (relativeCohomologyFunctor R R (d : ℤ)).map
      (normalRegionProjection N a U hU).op cModel := by
  let F := relativeCohomologyFunctor R R (d : ℤ)
  let b := F.map (normalRegionProjection N a U hU).op cModel
  have hb : NormalHasValues R N U d g b := by
    intro p hp
    change (F.map (normalRegionProjection N a U hU).op ≫
      F.map (fiberToNormalOver N U p hp).op) cModel = g p
    rw [← F.map_comp, ← op_comp, normalRegionProjection_eq, normalChart_projection_fiber]
    exact hg p hp
  cases d with
  | zero => exact normalHasValues_zero_ext R N U g c b hc hb
  | succ k =>
    obtain ⟨_, b', hb', hu⟩ := normalThomOn_of_chart R N (k+1) hd (Nat.zero_lt_succ k)
      g a U hU cModel hg U hopen Set.Subset.rfl
    exact (hu c hc).trans (hu b hb).symm

/-- Literal inclusion of the full normal chart in the full normal pair. -/
def normalRegionInclusion (N : NormalBundle T S i) (U : Set P) :
    normalRegionPair N U ⟶ normalPair N :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ hz => hz⟩

lemma normalRegion_expression [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d)
    (o : Orientation R N d)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) (hc : HasFiberValues R o c)
    (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (a : P) (U : Set P) (hopen : IsOpen U) (hU : U ⊆ (normalBundle N).baseSet a)
    (g : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ))
    (hg : ∀ (p : P) (hp : p ∈ U),
      (relativeCohomologyFunctor R R (d : ℤ)).map (fiberCoordinates N a p (hU hp)).op g = o.generator p) :
    (relativeCohomologyFunctor R R (d : ℤ)).map (normalRegionInclusion N U).op
        (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c) =
      (relativeCohomologyFunctor R R (d : ℤ)).map (normalRegionProjection N a U hU).op g := by
  apply normalChart_class_eq_projection R N d hd o.generator a U hopen hU g hg
  intro q hq
  let F := relativeCohomologyFunctor R R (d : ℤ)
  change (F.map (normalRegionInclusion N U).op ≫ F.map (fiberToNormalOver N U q hq).op)
    (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c) = _
  rw [← F.map_comp, ← op_comp]
  have hj : fiberToNormalOver N U q hq ≫ normalRegionInclusion N U = fiberToNormal N q :=
    PairMap.ext _ _ rfl
  rw [hj]
  exact (normal_fiber_values_iff_slice hi N K R d o c).mp (hc K hK) q

/-- The tube restriction of the ambient/normal comparison is its defining map. -/
lemma ambientNormal_restrict_domain [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (q : ℤ) (c : relativeCohomology R R (ambientPair i) q) :
    (relativeCohomologyFunctor R R q).map (domainToNormal N K).op
      (ambientNormalCohomologyEquiv hi N K R q c) =
      (relativeCohomologyFunctor R R q).map (domainToAmbient N K).op c := by
  change normalDomainCohomologyEquiv N K R q
    ((normalDomainCohomologyEquiv N K R q).symm (tubularCohomologyEquiv hi N K R q c)) = _
  exact (normalDomainCohomologyEquiv N K R q).apply_symm_apply _

def domainRegionToTube (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) :
    domainRegionPair N K U ⟶ tubularDomainPair N K :=
  ⟨TopCat.ofHom ⟨fun z => ⟨z.val, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩,
    fun _ hz => hz⟩

lemma ambientRegion_expression [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ) (hd : n-m=d)
    (o : Orientation R N d)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) (hc : HasFiberValues R o c)
    (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (a : P) (U : Set P) (hopen : IsOpen U) (hU : U ⊆ (normalBundle N).baseSet a)
    (g : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ))
    (hg : ∀ (p : P) (hp : p ∈ U),
      (relativeCohomologyFunctor R R (d : ℤ)).map (fiberCoordinates N a p (hU hp)).op g = o.generator p) :
    (relativeCohomologyFunctor R R (d : ℤ)).map (ambientRegionInclusion N K U).op c =
      (relativeCohomologyFunctor R R (d : ℤ)).map (ambientCoordinates N K a U hU).op g := by
  let F := relativeCohomologyFunctor R R (d : ℤ)
  let y := ambientNormalCohomologyEquiv hi N K R (d : ℤ) c
  have he := normalRegion_expression R hi N d hd o c hc K hK a U hopen hU g hg
  have he' := congrArg (fun z => F.map (domainRegionToNormal N K U).op z) he
  have hn : domainRegionToNormal N K U ≫ normalRegionInclusion N U =
      domainRegionToTube N K U ≫ domainToNormal N K := PairMap.ext _ _ rfl
  have ha : (regionPairIso N K U).hom ≫ ambientRegionInclusion N K U =
      domainRegionToTube N K U ≫ domainToAmbient N K := PairMap.ext _ _ rfl
  have hr : (regionPairIso N K U).hom ≫ ambientCoordinates N K a U hU =
      domainRegionToNormal N K U ≫ normalRegionProjection N a U hU := by
    simp [ambientCoordinates]
  apply (ModuleCat.mono_iff_injective (F.map (regionPairIso N K U).hom.op)).mp inferInstance
  change (F.map (ambientRegionInclusion N K U).op ≫ F.map (regionPairIso N K U).hom.op) c =
    (F.map (ambientCoordinates N K a U hU).op ≫ F.map (regionPairIso N K U).hom.op) g
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ha, hr]
  change (F.map (normalRegionInclusion N U).op ≫
    F.map (domainRegionToNormal N K U).op) y = _ at he'
  rw [← F.map_comp, ← op_comp, hn, op_comp, F.map_comp] at he'
  change F.map (domainRegionToTube N K U).op
    (F.map (domainToNormal N K).op y) = _ at he'
  rw [ambientNormal_restrict_domain R hi N K (d : ℤ) c] at he'
  simpa only [op_comp, F.map_comp, ModuleCat.comp_apply] using he'

lemma normalRegionProjection_zero_iff (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) (z : (normalRegionPair N U).space) :
    ((normalRegionProjection N a U hU).map z).down = 0 ↔
      z.val = normalZero N z.val.proj := by
  let e := fiberChart N a z.val.proj (hU z.property)
  change (e (⟨z.val, rfl⟩ : Fiber N z.val.proj)).down = 0 ↔ _
  have he : (e (fiberOrigin N z.val.proj)).down = 0 :=
    fiberChart_origin N a z.val.proj (hU z.property)
  constructor
  · intro hz
    exact congrArg Subtype.val (e.injective (ULift.ext (hz.trans he.symm)))
  · intro hz
    have hh : (⟨z.val, rfl⟩ : Fiber N z.val.proj) = fiberOrigin N z.val.proj := Subtype.ext hz
    rw [hh]
    exact he

lemma ambientCoordinates_zero_iff (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (a : P) (U : Set P) (hU : U ⊆ (normalBundle N).baseSet a) (x : imageRegion N K U) :
    ((ambientCoordinates N K a U hU).map x).down = 0 ↔ x.val ∈ Set.range i := by
  let z := (regionHomeomorph N K U).symm x
  change ((normalRegionProjection N a U hU).map ⟨z.val, z.property.2⟩).down = 0 ↔ _
  rw [normalRegionProjection_zero_iff]
  have hx : (K.homeomorph ⟨z.val, z.property.1⟩).val = x.val :=
    congrArg Subtype.val ((regionHomeomorph N K U).apply_symm_apply x)
  rw [← hx]
  exact (tubular_mem_range_iff N K z.val.proj ⟨z.val, rfl, z.property.1⟩).symm

lemma imageRegion_isOpen (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (U : Set P) (hU : IsOpen U) : IsOpen (imageRegion N K U) := by
  apply (K.isOpen_target.isOpenMap_subtype_val.comp K.homeomorph.isOpenMap)
  exact hU.preimage ((normalProjection_continuous N).comp continuous_subtype_val)

lemma imageRegion_contains (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (U : Set P) (p : P) (hp : p ∈ U) : i p ∈ imageRegion N K U :=
  ⟨⟨normalZero N p, K.zero_mem p⟩, hp, K.zero_eq p⟩

lemma model_generator_of_fiber_generator (N : NormalBundle T S i) (d : ℕ)
    (o : Orientation R N d) (a p : P) (hp : p ∈ (normalBundle N).baseSet a)
    (g : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ))
    (hg : (relativeCohomologyFunctor R R (d : ℤ)).map (fiberCoordinates N a p hp).op g =
      o.generator p) : Function.Bijective (fun r : R => r • g) := by
  let F := relativeCohomologyFunctor R R (d : ℤ)
  haveI : IsIso (F.map (fiberCoordinates N a p hp).op) := by
    change IsIso (F.map (fiberCoordinatesIso N a p hp).hom.op)
    infer_instance
  let e := (asIso (F.map (fiberCoordinates N a p hp).op)).toLinearEquiv
  have he : e g = o.generator p := hg
  constructor
  · intro r s h
    apply (o.generates p).injective
    simpa only [map_smul, he] using congrArg e h
  · intro x
    obtain ⟨r, hr⟩ := (o.generates p).surjective (e x)
    refine ⟨r, e.injective ?_⟩
    simpa only [map_smul, he] using hr

/-- Equality remains true on any further pair pullback, including any open
subpair. The maps and the equality are the actual contravariant functor maps. -/
lemma projection_formula_pullback (B C D : Pair.{u}) (f : B ⟶ C) (g : B ⟶ D)
    (q : ℤ) (c : relativeCohomology R R C q) (e : relativeCohomology R R D q)
    (h : (relativeCohomologyFunctor R R q).map f.op c =
      (relativeCohomologyFunctor R R q).map g.op e)
    (A : Pair.{u}) (j : A ⟶ B) :
    (relativeCohomologyFunctor R R q).map (j ≫ f).op c =
      (relativeCohomologyFunctor R R q).map (j ≫ g).op e := by
  simpa only [op_comp, Functor.map_comp, ModuleCat.comp_apply] using
    congrArg (fun z => (relativeCohomologyFunctor R R q).map j.op z) h

theorem localProjection :
  ∀ (R : Type v) [CommRing R] (m n d : ℕ)
    (P M : Type u) [TopologicalSpace P] [TopologicalSpace M] [CompactSpace P]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M), IsSmoothEmbedding T S i →
    ∀ (N : NormalBundle T S i), (∀ _ : P, d = n-m) →
    ∀ (o : Orientation R N d)
      (c : relativeCohomology R R (ambientPair i) (d : ℤ)), HasFiberValues R o c →
    ∀ (K : TubularNeighborhood N), NormalCompatible N K → ∀ p : P,
    ∃ (a : P) (U : Set P), IsOpen U ∧ p ∈ U ∧
    ∃ hU : U ⊆ (normalBundle N).baseSet a,
    ∃ g : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ),
      (∀ (q : P) (hq : q ∈ U),
        (relativeCohomologyFunctor R R (d : ℤ)).map
          (fiberCoordinates N a q (hU hq)).op g = o.generator q) ∧
      Function.Bijective (fun r : R => r • g) ∧
      IsOpen (imageRegion N K U) ∧ i p ∈ imageRegion N K U ∧
      (∀ x : imageRegion N K U,
        ((ambientCoordinates N K a U hU).map x).down = 0 ↔ x.val ∈ Set.range i) ∧
      (relativeCohomologyFunctor R R (d : ℤ)).map (ambientRegionInclusion N K U).op c =
        (relativeCohomologyFunctor R R (d : ℤ)).map (ambientCoordinates N K a U hU).op g ∧
      (∀ (B : Pair.{u}) (f : B ⟶ ambientRegionPair N K U),
        (relativeCohomologyFunctor R R (d : ℤ)).map (f ≫ ambientRegionInclusion N K U).op c =
        (relativeCohomologyFunctor R R (d : ℤ)).map (f ≫ ambientCoordinates N K a U hU).op g) := by
  intro R _ m n d P M _ _ _ T S i hi N hd o c hc K hK p
  obtain ⟨a, U, hopen, hp, hU, g, hg⟩ := o.locally_constant p
  have he := ambientRegion_expression R hi N d (hd p).symm o c hc K hK a U hopen hU g hg
  refine ⟨a, U, hopen, hp, hU, g, hg,
    model_generator_of_fiber_generator R N d o a p (hU hp) g (hg p hp),
    imageRegion_isOpen N K U hopen, imageRegion_contains N K U p hp,
    ambientCoordinates_zero_iff N K a U hU, he, ?_⟩
  intro B f
  exact projection_formula_pullback R _ _ _ _ _ (d : ℤ) c g he B f

end P202.LocalThomProjection
