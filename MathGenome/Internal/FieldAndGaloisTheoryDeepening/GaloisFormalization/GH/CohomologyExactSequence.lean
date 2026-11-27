import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.CohomologyExactSequence

namespace GaloisFormalization.GH.Model.ShortExactCoefficients

universe u v₁ v₂ v₃

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {A : Type v₁} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]
variable {B : Type v₂} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B]
variable {C : Type v₃} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

variable (S : ShortExactCoefficients G A B C)

omit [TopologicalSpace C] [DiscreteTopology C] in
theorem cochainI_injective (n : ℕ) : Function.Injective (S.cochainI n) := by
  intro a a' h
  apply Subtype.ext
  funext x
  exact S.i_injective (congrArg (fun b : continuousCochains G B n => b.val x) h)

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem cochainP_surjective (n : ℕ) : Function.Surjective (S.cochainP n) := by
  obtain ⟨s, hs⟩ := S.p_surjective.hasRightInverse
  intro c
  refine ⟨⟨s ∘ c.val, continuous_of_discreteTopology.comp c.property⟩, Subtype.ext ?_⟩
  exact funext fun x => hs (c.val x)

theorem cochain_exact (n : ℕ) : Function.Exact (S.cochainI n) (S.cochainP n) := by
  obtain ⟨r, hr⟩ := S.i_injective.hasLeftInverse
  intro b
  constructor
  · intro hb
    refine ⟨⟨r ∘ b.val, continuous_of_discreteTopology.comp b.property⟩, Subtype.ext ?_⟩
    funext x
    change S.i (r (b.val x)) = b.val x
    have hx : S.p (b.val x) = 0 :=
      congrArg (fun c : continuousCochains G C n => c.val x) hb
    obtain ⟨a, ha⟩ := (S.exact (b.val x)).mp hx
    rw [← ha, hr a]
  · rintro ⟨a, rfl⟩
    exact Subtype.ext (funext fun x => S.exact.apply_apply_eq_zero (a.val x))

variable [IsTopologicalGroup G] [ContinuousSMul G A] [ContinuousSMul G B] [ContinuousSMul G C]

omit [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul G C] in
private theorem cochainI_d (n : ℕ) (a : continuousCochains G A n) :
    S.cochainI (n + 1) (continuousDifferential G A n a) =
      continuousDifferential G B n (S.cochainI n a) :=
  continuousCochainMap_d (MonoidHom.id G) continuous_id S.i S.i_equivariant n a

omit [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A] in
private theorem cochainP_d (n : ℕ) (b : continuousCochains G B n) :
    S.cochainP (n + 1) (continuousDifferential G B n b) =
      continuousDifferential G C n (S.cochainP n b) :=
  continuousCochainMap_d (MonoidHom.id G) continuous_id S.p S.p_equivariant n b

omit [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A] in
private theorem cochainP_incoming (n : ℕ) (b : continuousCochains G B n.pred) :
    S.cochainP n (continuousIncoming G B n b) =
      continuousIncoming G C n (S.cochainP n.pred b) := by
  cases n with
  | zero => exact map_zero (S.cochainP 0)
  | succ n => exact S.cochainP_d n b

omit [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
    [ContinuousSMul G B] [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] in
private theorem class_eq_iff_incoming {n : ℕ} (a a' : continuousCocycles G A n) :
    continuousClass G A n a = continuousClass G A n a' ↔
      ∃ x : continuousCochains G A n.pred, continuousIncoming G A n x = a.val - a'.val := by
  rw [GH.continuousClass_eq_iff]
  change (∃ x, _ = a - a') ↔ _
  exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

omit [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
    [ContinuousSMul G B] [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] in
private theorem class_eq_zero_iff_incoming {n : ℕ} (a : continuousCocycles G A n) :
    continuousClass G A n a = 0 ↔
      ∃ x : continuousCochains G A n.pred, continuousIncoming G A n x = a.val := by
  simpa only [map_zero, ZeroMemClass.coe_zero, sub_zero] using
    (class_eq_iff_incoming a (0 : continuousCocycles G A n))

private theorem lift_differential {n : ℕ} (c : continuousCocycles G C n)
    (b : continuousCochains G B n) (hb : S.cochainP n b = c.val) :
    ∃ a : continuousCocycles G A (n + 1),
      S.cochainI (n + 1) a.val = continuousDifferential G B n b := by
  have hp : S.cochainP (n + 1) (continuousDifferential G B n b) = 0 := by
    rw [S.cochainP_d, hb]
    exact c.property
  obtain ⟨a, ha⟩ := (S.cochain_exact _ _).mp hp
  have hz : continuousDifferential G A (n + 1) a = 0 := by
    apply S.cochainI_injective (n + 2)
    rw [S.cochainI_d, ha, continuousDifferential_sq, map_zero]
  exact ⟨⟨a, hz⟩, ha⟩

private theorem lift_classes_eq {n : ℕ} {c : continuousCocycles G C n}
    {b b' : continuousCochains G B n} {a a' : continuousCocycles G A (n + 1)}
    (hb : S.cochainP n b = c.val) (hb' : S.cochainP n b' = c.val)
    (ha : S.cochainI (n + 1) a.val = continuousDifferential G B n b)
    (ha' : S.cochainI (n + 1) a'.val = continuousDifferential G B n b') :
    continuousClass G A (n + 1) a = continuousClass G A (n + 1) a' := by
  obtain ⟨x, hx⟩ := (S.cochain_exact n (b - b')).mp (by rw [map_sub, hb, hb', sub_self])
  apply (GH.continuousClass_succ_eq_iff a a').mpr
  refine ⟨x, S.cochainI_injective (n + 1) ?_⟩
  rw [S.cochainI_d, hx, map_sub, map_sub, ha, ha']

private theorem exists_connecting (n : ℕ) :
    ∃ δ : ContinuousH G C n →ₗ[ℤ] ContinuousH G A (n + 1),
      ∀ (c : continuousCocycles G C n) (b : continuousCochains G B n)
        (a : continuousCocycles G A (n + 1)),
        S.cochainP n b = c.val →
        S.cochainI (n + 1) a.val = continuousDifferential G B n b →
        δ (continuousClass G C n c) = continuousClass G A (n + 1) a := by
  classical
  choose b hb using fun c : continuousCocycles G C n => S.cochainP_surjective n c.val
  choose a ha using fun c : continuousCocycles G C n => S.lift_differential c (b c) (hb c)
  let f (c : continuousCocycles G C n) := continuousClass G A (n + 1) (a c)
  have hf (c : continuousCocycles G C n) (y : continuousCochains G B n)
      (z : continuousCocycles G A (n + 1)) (hy : S.cochainP n y = c.val)
      (hz : S.cochainI (n + 1) z.val = continuousDifferential G B n y) :
      f c = continuousClass G A (n + 1) z :=
    S.lift_classes_eq (hb c) hy (ha c) hz
  let F : continuousCocycles G C n →ₗ[ℤ] ContinuousH G A (n + 1) :=
    (AddMonoidHom.mk' f fun c c' => by
      rw [hf (c + c') (b c + b c') (a c + a c')]
      · exact map_add (continuousClass G A (n + 1)) _ _
      · change S.cochainP n (b c + b c') = c.val + c'.val
        rw [map_add, hb, hb]
      · change S.cochainI (n + 1) ((a c).val + (a c').val) =
          continuousDifferential G B n (b c + b c')
        rw [map_add, map_add, ha, ha]).toIntLinearMap
  have hF : continuousCoboundaries G C n ≤ LinearMap.ker F := by
    intro c hc
    obtain ⟨x, hx⟩ := (class_eq_zero_iff_incoming c).mp
      ((Submodule.Quotient.mk_eq_zero (continuousCoboundaries G C n)).mpr hc)
    obtain ⟨y, hy⟩ := S.cochainP_surjective n.pred x
    change f c = 0
    rw [hf c (continuousIncoming G B n y) 0]
    · exact map_zero (continuousClass G A (n + 1))
    · rw [S.cochainP_incoming, hy, hx]
    · change S.cochainI (n + 1) 0 = continuousDifferential G B n (continuousIncoming G B n y)
      rw [map_zero, continuousIncoming_d]
  exact ⟨(continuousCoboundaries G C n).liftQ F hF, hf⟩

private abbrev cocycleI (n : ℕ) :=
  continuousCocycleMap (MonoidHom.id G) continuous_id S.i S.i_equivariant n

private abbrev cocycleP (n : ℕ) :=
  continuousCocycleMap (MonoidHom.id G) continuous_id S.p S.p_equivariant n

omit [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul G C] in
private theorem cohomologyI_zero_injective : Function.Injective (S.cohomologyI 0) := by
  intro q q' h
  obtain ⟨a, rfl⟩ := GH.continuousClass_surjective 0 q
  obtain ⟨a', rfl⟩ := GH.continuousClass_surjective 0 q'
  change continuousClass G B 0 (S.cocycleI 0 a) =
    continuousClass G B 0 (S.cocycleI 0 a') at h
  apply congrArg (continuousClass G A 0)
  apply Subtype.ext
  apply S.cochainI_injective 0
  exact congrArg Subtype.val ((GH.continuousClass_zero_eq_iff _ _).mp h)

private theorem cohomology_exact_middle (n : ℕ) :
    Function.Exact (S.cohomologyI n) (S.cohomologyP n) := by
  intro q
  obtain ⟨z, rfl⟩ := GH.continuousClass_surjective n q
  constructor
  · intro hz
    change continuousClass G C n (S.cocycleP n z) = 0 at hz
    obtain ⟨x, hx⟩ := (class_eq_zero_iff_incoming _).mp hz
    change continuousIncoming G C n x = S.cochainP n z.val at hx
    obtain ⟨y, hy⟩ := S.cochainP_surjective n.pred x
    have hp : S.cochainP n (z.val - continuousIncoming G B n y) = 0 := by
      rw [map_sub, S.cochainP_incoming, hy, hx, sub_self]
    obtain ⟨a, ha⟩ := (S.cochain_exact _ _).mp hp
    have hdz : continuousDifferential G B n z.val = 0 := z.property
    have hd : continuousDifferential G A n a = 0 := by
      apply S.cochainI_injective (n + 1)
      rw [S.cochainI_d, ha, map_sub, hdz, continuousIncoming_d, sub_self, map_zero]
    refine ⟨continuousClass G A n ⟨a, hd⟩, ?_⟩
    change continuousClass G B n (S.cocycleI n ⟨a, hd⟩) = continuousClass G B n z
    refine (class_eq_iff_incoming _ _).mpr ⟨-y, ?_⟩
    change continuousIncoming G B n (-y) = S.cochainI n a - z.val
    rw [map_neg, ha]
    abel
  · rintro ⟨q, hq⟩
    obtain ⟨a, rfl⟩ := GH.continuousClass_surjective n q
    rw [← hq]
    change continuousClass G C n (S.cocycleP n (S.cocycleI n a)) = 0
    refine (class_eq_zero_iff_incoming _).mpr ⟨0, ?_⟩
    change continuousIncoming G C n 0 = S.cochainP n (S.cochainI n a.val)
    rw [map_zero, (S.cochain_exact n).apply_apply_eq_zero]

section

variable {δ : ConnectingFamily (G := G) (A := A) (C := C)} (hδ : S.ConnectingFormula δ)

include hδ in
private theorem connecting_class {n : ℕ} (c : continuousCocycles G C n)
    (b : continuousCochains G B n) (a : continuousCocycles G A (n + 1))
    (hb : S.cochainP n b = c.val)
    (ha : S.cochainI (n + 1) a.val = continuousDifferential G B n b) :
    δ n (continuousClass G C n c) = continuousClass G A (n + 1) a := by
  obtain ⟨a', _, heq, hu⟩ := hδ n c b hb
  exact heq.trans (congrArg (continuousClass G A (n + 1)) (Subtype.ext (hu a.val ha))).symm

include hδ in
private theorem cohomology_exact_right (n : ℕ) :
    Function.Exact (S.cohomologyP n) (δ n) := by
  intro q
  obtain ⟨c, rfl⟩ := GH.continuousClass_surjective n q
  constructor
  · intro hc
    obtain ⟨b, hb⟩ := S.cochainP_surjective n c.val
    obtain ⟨a, ha, heq, _⟩ := hδ n c b hb
    change δ n (continuousClass G C n c) = 0 at hc
    obtain ⟨x, hx⟩ := (class_eq_zero_iff_incoming a).mp (heq.symm.trans hc)
    change continuousDifferential G A n x = a.val at hx
    have hd : continuousDifferential G B n (b - S.cochainI n x) = 0 := by
      rw [map_sub, ← S.cochainI_d, hx, ha, sub_self]
    refine ⟨continuousClass G B n ⟨_, hd⟩, ?_⟩
    change continuousClass G C n (S.cocycleP n ⟨_, hd⟩) = continuousClass G C n c
    apply congrArg (continuousClass G C n)
    apply Subtype.ext
    change S.cochainP n (b - S.cochainI n x) = c.val
    rw [map_sub, (S.cochain_exact n).apply_apply_eq_zero, sub_zero, hb]
  · rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := GH.continuousClass_surjective n q
    rw [← hq]
    change δ n (continuousClass G C n (S.cocycleP n b)) = 0
    rw [S.connecting_class hδ (S.cocycleP n b) b.val 0 rfl]
    · exact map_zero (continuousClass G A (n + 1))
    · change S.cochainI (n + 1) 0 = continuousDifferential G B n b.val
      exact (map_zero _).trans (show continuousDifferential G B n b.val = 0 from b.property).symm

include hδ in
private theorem cohomology_exact_left (n : ℕ) :
    Function.Exact (δ n) (S.cohomologyI (n + 1)) := by
  intro q
  obtain ⟨a, rfl⟩ := GH.continuousClass_surjective (n + 1) q
  constructor
  · intro ha
    change continuousClass G B (n + 1) (S.cocycleI (n + 1) a) = 0 at ha
    obtain ⟨b, hb⟩ := (class_eq_zero_iff_incoming _).mp ha
    change continuousDifferential G B n b = S.cochainI (n + 1) a.val at hb
    have hc : continuousDifferential G C n (S.cochainP n b) = 0 := by
      rw [← S.cochainP_d, hb, (S.cochain_exact (n + 1)).apply_apply_eq_zero]
    let c : continuousCocycles G C n := ⟨_, hc⟩
    exact ⟨continuousClass G C n c, S.connecting_class hδ c b a rfl hb.symm⟩
  · rintro ⟨q, hq⟩
    obtain ⟨c, rfl⟩ := GH.continuousClass_surjective n q
    obtain ⟨b, hb⟩ := S.cochainP_surjective n c.val
    obtain ⟨a', ha', heq, _⟩ := hδ n c b hb
    rw [← hq, heq]
    change continuousClass G B (n + 1) (S.cocycleI (n + 1) a') = 0
    exact (class_eq_zero_iff_incoming _).mpr ⟨b, ha'.symm⟩

end

private theorem longExact :
    ∃ δ, S.IsLongExact δ := by
  classical
  choose δ hδ using S.exists_connecting
  have formula : S.ConnectingFormula δ := by
    intro n c b hb
    obtain ⟨a, ha⟩ := S.lift_differential c b hb
    refine ⟨a, ha, hδ n c b a hb ha, fun a' ha' => ?_⟩
    exact S.cochainI_injective (n + 1) (ha'.trans ha.symm)
  exact ⟨δ, ⟨S.cochainP_surjective, S.cohomologyI_zero_injective,
    S.cohomology_exact_middle, S.cohomology_exact_right formula,
    S.cohomology_exact_left formula, formula⟩⟩

end GaloisFormalization.GH.Model.ShortExactCoefficients

namespace GaloisFormalization.GH

/-- A short exact sequence of discrete continuous coefficients induces the long
exact sequence in continuous group cohomology. -/
theorem continuousCohomology_longExact : Specification.ContinuousCohomologyLongExact :=
  fun S => S.longExact

end GaloisFormalization.GH
