import MathGenome.Internal.D07.Ch15.ConstructibleDefinition
import MathGenome.Internal.Specs.D07.Ch15.GeometricFieldOperations
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

namespace D07.Ch15.StraightedgeCompass

lemma Construction.initial_subset {P : InitialData} {S : Set Point}
    (h : Construction P S) : P.points ⊆ S := by
  induction h with
  | initial => exact Set.Subset.rfl
  | step _ _ ih => exact ih.trans (Set.subset_insert _ _)

lemma Curve.Available.mono {S T : Set Point} (h : S ⊆ T) {c : Curve}
    (hc : c.Available S) : c.Available T := by
  cases c with
  | line a b => exact ⟨h hc.1, h hc.2.1, hc.2.2⟩
  | circle c a b => exact ⟨h hc.1, h hc.2.1, h hc.2.2⟩

lemma IntersectionStep.mono {S T : Set Point} (h : S ⊆ T) {p : Point}
    (hp : IntersectionStep S p) : IntersectionStep T p := by
  obtain ⟨c, d, hc, hd, hne, hfin, hp⟩ := hp
  exact ⟨c, d, hc.mono h, hd.mono h, hne, hfin, hp⟩

/-- Replay a second finite construction after the first. -/
lemma Construction.merge {P : InitialData} {S T : Set Point}
    (hS : Construction P S) (hT : Construction P T) :
    ∃ U, Construction P U ∧ S ⊆ U ∧ T ⊆ U := by
  induction hT with
  | initial => exact ⟨S, hS, Set.Subset.rfl, hS.initial_subset⟩
  | @step T p hT hp ih =>
    obtain ⟨U, hU, hSU, hTU⟩ := ih
    refine ⟨insert p U, hU.step (hp.mono hTU), ?_, ?_⟩
    · exact hSU.trans (Set.subset_insert _ _)
    · exact Set.insert_subset_insert hTU

lemma constructible_finite_available {P : InitialData} {A : Set Point}
    (hA : A.Finite) (h : ∀ p ∈ A, IsConstructible P p) :
    ∃ S, Construction P S ∧ A ⊆ S := by
  induction A, hA using Set.Finite.induction_on with
  | empty => exact ⟨P.points, .initial, Set.empty_subset _⟩
  | @insert p A hp hA ih =>
    obtain ⟨S, hS, hAS⟩ := ih (fun q hq => h q (Set.mem_insert_of_mem p hq))
    obtain ⟨T, hT, hpT⟩ := h p (Set.mem_insert p A)
    obtain ⟨U, hU, hSU, hTU⟩ := hS.merge hT
    exact ⟨U, hU, Set.insert_subset (hTU hpT) (hAS.trans hSU)⟩

/-- Curve availability, expressed using globally constructible points. -/
private def drawable (P : InitialData) : Curve → Prop
  | .line a b => IsConstructible P a ∧ IsConstructible P b ∧ a ≠ b
  | .circle c a b => IsConstructible P c ∧ IsConstructible P a ∧ IsConstructible P b

private def supports : Curve → Set Point
  | .line a b => {a, b}
  | .circle c a b => {c, a, b}

private lemma supports_finite (c : Curve) : (supports c).Finite := by
  cases c <;> simp [supports]

private lemma drawable_available {P : InitialData} {c : Curve}
    (hc : drawable P c) :
    (∀ p ∈ supports c, IsConstructible P p) ∧
      (∀ S, supports c ⊆ S → c.Available S) := by
  cases c with
  | line a b =>
    simp only [drawable, supports, Set.mem_insert_iff, Set.mem_singleton_iff] at *
    exact ⟨by rintro p (rfl | rfl) <;> tauto,
      fun S h => ⟨h (Or.inl rfl), h (Or.inr rfl), hc.2.2⟩⟩
  | circle c a b =>
    simp only [drawable, supports, Set.mem_insert_iff, Set.mem_singleton_iff] at *
    exact ⟨by rintro p (rfl | rfl | rfl) <;> tauto,
      fun S h => ⟨h (Or.inl rfl), h (Or.inr (Or.inl rfl)),
        h (Or.inr (Or.inr rfl))⟩⟩

private lemma constructible_intersection {P : InitialData} {c d : Curve} {p : Point}
    (hc : drawable P c) (hd : drawable P d) (hne : c.locus ≠ d.locus)
    (hf : (c.locus ∩ d.locus).Finite) (hp : p ∈ c.locus ∩ d.locus) :
    IsConstructible P p := by
  obtain ⟨hcs, hca⟩ := drawable_available hc
  obtain ⟨hds, hda⟩ := drawable_available hd
  obtain ⟨S, hS, hsub⟩ := constructible_finite_available
    ((supports_finite c).union (supports_finite d))
    (by rintro q (hq | hq); exact hcs q hq; exact hds q hq)
  have hs : IntersectionStep S p :=
    ⟨c, d, hca S (fun _ h => hsub (Or.inl h)),
      hda S (fun _ h => hsub (Or.inr h)), hne, hf, hp⟩
  exact ⟨insert p S, hS.step hs, Set.mem_insert _ _⟩

private lemma finite_pair_intersection {c d : Curve} {p q : Point}
    (h : ∀ r ∈ c.locus ∩ d.locus, r = p ∨ r = q) :
    (c.locus ∩ d.locus).Finite :=
  (Set.toFinite ({p, q} : Set Point)).subset (by
    intro r hr
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h r hr)

lemma constructible_origin (P : InitialData) : IsConstructible P origin :=
  isConstructible_of_mem P.origin_mem

lemma constructible_unitPoint (P : InitialData) : IsConstructible P unitPoint :=
  isConstructible_of_mem P.unitPoint_mem


private lemma line_locus_infinite {a b : Point} (hab : a ≠ b) :
    (Curve.line a b).locus.Infinite := by
  let f : ℝ → Point := fun t => (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))
  have hinj : Function.Injective f := by
    intro t u h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp [f] at hx hy
    by_cases h₁ : b.1 = a.1
    · have h₂ : b.2 ≠ a.2 := by
        intro h₂
        exact hab (Prod.ext h₁.symm h₂.symm)
      have : (t-u) * (b.2-a.2) = 0 := by nlinarith [hy]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h₂))
    · have : (t-u) * (b.1-a.1) = 0 := by nlinarith [hx]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h₁))
  apply (Set.infinite_range_of_injective hinj).mono
  rintro p ⟨t, rfl⟩
  change (b.1-a.1) * (a.2+t*(b.2-a.2)-a.2) =
    (b.2-a.2) * (a.1+t*(b.1-a.1)-a.1)
  ring

private lemma constructible_line_intersection {P : InitialData} {a b : Point}
    {d : Curve} {p : Point} (ha : IsConstructible P a) (hb : IsConstructible P b)
    (hab : a ≠ b) (hd : drawable P d)
    (hf : ((Curve.line a b).locus ∩ d.locus).Finite)
    (hp : p ∈ (Curve.line a b).locus ∩ d.locus) : IsConstructible P p := by
  apply constructible_intersection (c := .line a b) ⟨ha, hb, hab⟩ hd _ hf hp
  intro heq
  apply line_locus_infinite hab
  simpa only [heq, Set.inter_self] using hf

private lemma circle_locus_ne {c d a b e f : Point} (hcd : c ≠ d) :
    (Curve.circle c a b).locus ≠ (Curve.circle d e f).locus := by
  intro heq
  let p : Point := (c.1+(a.1-b.1), c.2+(a.2-b.2))
  let q : Point := (c.1-(a.1-b.1), c.2-(a.2-b.2))
  let u : Point := (d.1+(e.1-f.1), d.2+(e.2-f.2))
  let v : Point := (d.1-(e.1-f.1), d.2-(e.2-f.2))
  have hp : p ∈ (Curve.circle c a b).locus := by
    dsimp [Curve.locus, squaredDistance, p]; ring
  have hq : q ∈ (Curve.circle c a b).locus := by
    dsimp [Curve.locus, squaredDistance, q]; ring
  have hu : u ∈ (Curve.circle d e f).locus := by
    dsimp [Curve.locus, squaredDistance, u]; ring
  have hv : v ∈ (Curve.circle d e f).locus := by
    dsimp [Curve.locus, squaredDistance, v]; ring
  rw [heq] at hp hq
  rw [← heq] at hu hv
  dsimp [Curve.locus, squaredDistance, p, q, u, v] at hp hq hu hv
  have hx : c.1 = d.1 := by
    nlinarith [sq_nonneg (c.1-d.1), sq_nonneg (c.2-d.2)]
  have hy : c.2 = d.2 := by
    nlinarith [sq_nonneg (c.1-d.1), sq_nonneg (c.2-d.2)]
  exact hcd (Prod.ext hx hy)

/-- Select either signed horizontal intercept of any available circle. -/
private lemma horizontal_circle {P : InitialData} {c r s : Point} {x : ℝ}
    (hc : IsConstructible P c) (hr : IsConstructible P r) (hs : IsConstructible P s)
    (hx : squaredDistance (x, 0) c = squaredDistance r s) :
    IsConstructibleReal P x := by
  apply constructible_line_intersection (constructible_origin P) (constructible_unitPoint P)
    (by simp [origin, unitPoint]) (d := .circle c r s) ⟨hc, hr, hs⟩
  · apply finite_pair_intersection (p := (x,0)) (q := (2*c.1-x,0))
    intro z hz
    have hz₀ : z.2 = 0 := by simpa [Curve.locus, origin, unitPoint] using hz.1
    have hz₁ := hz.2
    dsimp [Curve.locus, squaredDistance] at hz₁ hx
    rw [hz₀] at hz₁
    have he : (z.1-c.1)^2 = (x-c.1)^2 := by nlinarith [hz₁, hx]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
    · left; exact Prod.ext (by linarith) hz₀
    · right; exact Prod.ext (by linarith) hz₀
  · exact ⟨by simp [Curve.locus, origin, unitPoint], hx⟩

theorem constructible_neg (P : InitialData) (a : ℝ)
    (ha : IsConstructibleReal P a) : IsConstructibleReal P (-a) := by
  apply horizontal_circle (constructible_origin P) (constructible_origin P) ha
  dsimp [squaredDistance, origin]; ring

theorem constructible_add (P : InitialData) (a b : ℝ)
    (ha : IsConstructibleReal P a) (hb : IsConstructibleReal P b) :
    IsConstructibleReal P (a+b) := by
  apply horizontal_circle ha (constructible_origin P) hb
  dsimp [squaredDistance, origin]; ring

lemma constructible_zero (P : InitialData) : IsConstructibleReal P 0 :=
  constructible_origin P

lemma constructible_one (P : InitialData) : IsConstructibleReal P 1 :=
  constructible_unitPoint P

lemma constructible_sub {P : InitialData} {a b : ℝ}
    (ha : IsConstructibleReal P a) (hb : IsConstructibleReal P b) :
    IsConstructibleReal P (a-b) := by
  simpa only [sub_eq_add_neg] using constructible_add P a (-b) ha (constructible_neg P b hb)


/-- Equal-radius circles at the endpoints of a horizontal segment give a
vertical direction. The radius is the distance between those endpoints. -/
private lemma vertical_pair {P : InitialData} {a t : ℝ}
    (hl : IsConstructibleReal P (a-1)) (hr : IsConstructibleReal P (a+1))
    (ht : t^2 = 3) : IsConstructible P (a,t) := by
  apply constructible_intersection
    (c := .circle (a-1,0) (a-1,0) (a+1,0))
    (d := .circle (a+1,0) (a-1,0) (a+1,0))
    ⟨hl, hl, hr⟩ ⟨hr, hl, hr⟩
    (circle_locus_ne (by intro h; have := congrArg Prod.fst h; dsimp at this; linarith))
  · apply finite_pair_intersection (p := (a,t)) (q := (a,-t))
    intro z hz
    obtain ⟨h₁,h₂⟩ := hz
    dsimp [Curve.locus, squaredDistance] at h₁ h₂
    have hx : z.1 = a := by nlinarith [h₁,h₂]
    have hy : z.2^2 = t^2 := by rw [hx] at h₁; nlinarith [h₁,ht]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
    · exact Or.inl (Prod.ext hx hy)
    · exact Or.inr (Prod.ext hx hy)
  · constructor <;> dsimp [Curve.locus, squaredDistance] <;> nlinarith [ht]

private noncomputable def auxiliaryHeight : ℝ := Real.sqrt 3
private lemma auxiliaryHeight_sq : auxiliaryHeight^2 = 3 := by
  exact Real.sq_sqrt (by norm_num)
private lemma auxiliaryHeight_ne : auxiliaryHeight ≠ 0 := by
  have := auxiliaryHeight_sq
  intro h
  rw [h] at this
  norm_num at this

private lemma vertical_direction (P : InitialData) :
    IsConstructible P (0,auxiliaryHeight) := by
  apply vertical_pair
  · exact constructible_sub (constructible_zero P) (constructible_one P)
  · exact constructible_add P 0 1 (constructible_zero P) (constructible_one P)
  · exact auxiliaryHeight_sq

/-- Selection on a vertical line which has itself been constructed. -/
private lemma vertical_circle {P : InitialData} {t y : ℝ} {c r s : Point}
    (hv : IsConstructible P (0,t)) (ht : t ≠ 0)
    (hc : IsConstructible P c) (hr : IsConstructible P r) (hs : IsConstructible P s)
    (hy : squaredDistance (0,y) c = squaredDistance r s) :
    IsConstructible P (0,y) := by
  apply constructible_line_intersection (constructible_origin P) hv
    (by intro h; exact ht (congrArg Prod.snd h).symm) (d := .circle c r s) ⟨hc,hr,hs⟩
  · apply finite_pair_intersection (p := (0,y)) (q := (0,2*c.2-y))
    intro z hz
    have hz₀ : z.1 = 0 := by
      have h : t*z.1 = 0 := by simpa [Curve.locus, origin] using hz.1.symm
      exact (mul_eq_zero.mp h).resolve_left ht
    have hz₁ := hz.2
    dsimp [Curve.locus, squaredDistance] at hz₁ hy
    rw [hz₀] at hz₁
    have he : (z.2-c.2)^2 = (y-c.2)^2 := by nlinarith [hz₁,hy]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
    · left; exact Prod.ext hz₀ (by linarith)
    · right; exact Prod.ext hz₀ (by linarith)
  · exact ⟨by simp [Curve.locus, origin], hy⟩

/-- Transfer a signed length between the axes by choosing the corresponding
intersection, including the tangent case of length zero. -/
lemma constructible_on_vertical {P : InitialData} {a : ℝ}
    (ha : IsConstructibleReal P a) : IsConstructible P (0,a) := by
  apply vertical_circle (vertical_direction P) auxiliaryHeight_ne
    (constructible_origin P) (constructible_origin P) ha
  dsimp [squaredDistance, origin]; ring

lemma constructible_of_on_vertical {P : InitialData} {a : ℝ}
    (ha : IsConstructible P (0,a)) : IsConstructibleReal P a := by
  apply horizontal_circle (constructible_origin P) (constructible_origin P) ha
  dsimp [squaredDistance, origin]; ring

private lemma horizontal_pair {P : InitialData} {b t : ℝ}
    (hl : IsConstructible P (0,b-1)) (hr : IsConstructible P (0,b+1))
    (ht : t^2 = 3) : IsConstructible P (t,b) := by
  apply constructible_intersection
    (c := .circle (0,b-1) (0,b-1) (0,b+1))
    (d := .circle (0,b+1) (0,b-1) (0,b+1))
    ⟨hl,hl,hr⟩ ⟨hr,hl,hr⟩
    (circle_locus_ne (by intro h; have := congrArg Prod.snd h; dsimp at this; linarith))
  · apply finite_pair_intersection (p := (t,b)) (q := (-t,b))
    intro z hz
    obtain ⟨h₁,h₂⟩ := hz
    dsimp [Curve.locus, squaredDistance] at h₁ h₂
    have hy : z.2 = b := by nlinarith [h₁,h₂]
    have hx : z.1^2 = t^2 := by rw [hy] at h₁; nlinarith [h₁,ht]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx with hx | hx
    · exact Or.inl (Prod.ext hx hy)
    · exact Or.inr (Prod.ext hx hy)
  · constructor <;> dsimp [Curve.locus, squaredDistance] <;> nlinarith [ht]

theorem constructible_combine (P : InitialData) (a b : ℝ)
    (ha : IsConstructibleReal P a) (hb : IsConstructibleReal P b) :
    IsConstructible P (a,b) := by
  have haLower := constructible_sub ha (constructible_one P)
  have haUpper := constructible_add P a 1 ha (constructible_one P)
  have hbLower := constructible_on_vertical (constructible_sub hb (constructible_one P))
  have hbUpper := constructible_on_vertical (constructible_add P b 1 hb (constructible_one P))
  have ht := auxiliaryHeight_sq
  have hnt : (-auxiliaryHeight)^2 = 3 := by nlinarith [ht]
  have hne : auxiliaryHeight ≠ -auxiliaryHeight := by
    intro h
    apply auxiliaryHeight_ne
    linarith
  have ha₁ := vertical_pair haLower haUpper ht
  have ha₂ := vertical_pair haLower haUpper hnt
  have hb₁ := horizontal_pair hbLower hbUpper ht
  have hb₂ := horizontal_pair hbLower hbUpper hnt
  have hane : (a,auxiliaryHeight) ≠ (a,-auxiliaryHeight) := by
    intro h; exact hne (congrArg Prod.snd h)
  have hbne : (auxiliaryHeight,b) ≠ (-auxiliaryHeight,b) := by
    intro h; exact hne (congrArg Prod.fst h)
  apply constructible_line_intersection ha₁ ha₂ hane
    (d := .line (auxiliaryHeight,b) (-auxiliaryHeight,b)) ⟨hb₁,hb₂,hbne⟩
  · apply finite_pair_intersection (p := (a,b)) (q := (a,b))
    intro z hz
    obtain ⟨hx,hy⟩ := hz
    dsimp [Curve.locus] at hx hy
    have hx' : z.1 = a := by
      have : (2*auxiliaryHeight)*(z.1-a) = 0 := by nlinarith [hx]
      rcases mul_eq_zero.mp this with h | h
      · exact (auxiliaryHeight_ne (by linarith)).elim
      · linarith
    have hy' : z.2 = b := by
      have : (2*auxiliaryHeight)*(z.2-b) = 0 := by nlinarith [hy]
      rcases mul_eq_zero.mp this with h | h
      · exact (auxiliaryHeight_ne (by linarith)).elim
      · linarith
    exact Or.inl (Prod.ext hx' hy')
  · constructor <;> dsimp [Curve.locus] <;> ring


theorem constructible_mul (P : InitialData) (a b : ℝ)
    (ha : IsConstructibleReal P a) (hb : IsConstructibleReal P b) :
    IsConstructibleReal P (a*b) := by
  have hb₀ := constructible_on_vertical hb
  have hab := constructible_combine P a (b-1) ha
    (constructible_sub hb (constructible_one P))
  have hne : (0,b) ≠ (a,b-1) := by
    intro h; have := congrArg Prod.snd h; dsimp at this; linarith
  apply constructible_line_intersection (constructible_origin P) (constructible_unitPoint P)
    (by simp [origin,unitPoint]) (d := .line (0,b) (a,b-1)) ⟨hb₀,hab,hne⟩
  · apply finite_pair_intersection (p := (a*b,0)) (q := (a*b,0))
    intro z hz
    have hy : z.2 = 0 := by simpa [Curve.locus,origin,unitPoint] using hz.1
    have hx := hz.2
    dsimp [Curve.locus] at hx
    rw [hy] at hx
    exact Or.inl (Prod.ext (by nlinarith [hx]) hy)
  · constructor
    · simp [Curve.locus,origin,unitPoint]
    · dsimp [Curve.locus]; ring

theorem constructible_div (P : InitialData) (a b : ℝ)
    (ha : IsConstructibleReal P a) (hb : IsConstructibleReal P b) (hbne : b ≠ 0) :
    IsConstructibleReal P (a/b) := by
  have hJ := constructible_on_vertical (constructible_one P)
  have hab := constructible_combine P a (1-b) ha
    (constructible_sub (constructible_one P) hb)
  have hne : (0,1) ≠ (a,1-b) := by
    intro h; have := congrArg Prod.snd h; dsimp at this; exact hbne (by linarith)
  have hdiv : b*(a/b) = a := by exact mul_div_cancel₀ a hbne
  apply constructible_line_intersection (constructible_origin P) (constructible_unitPoint P)
    (by simp [origin,unitPoint]) (d := .line (0,1) (a,1-b)) ⟨hJ,hab,hne⟩
  · apply finite_pair_intersection (p := (a/b,0)) (q := (a/b,0))
    intro z hz
    have hy : z.2 = 0 := by simpa [Curve.locus,origin,unitPoint] using hz.1
    have hx := hz.2
    dsimp [Curve.locus] at hx
    rw [hy] at hx
    exact Or.inl (Prod.ext ((eq_div_iff hbne).mpr (by nlinarith [hx])) hy)
  · constructor
    · simp [Curve.locus,origin,unitPoint]
    · dsimp [Curve.locus]; nlinarith [hdiv]

theorem constructible_sqrt (P : InitialData) (a : ℝ)
    (ha : IsConstructibleReal P a) (hnonneg : 0 ≤ a) :
    IsConstructibleReal P (Real.sqrt a) := by
  have htwo : IsConstructibleReal P 2 := by
    simpa only [one_add_one_eq_two] using constructible_add P 1 1 (constructible_one P) (constructible_one P)
  have hc := constructible_div P (a-1) 2
    (constructible_sub ha (constructible_one P)) htwo (by norm_num)
  have hr := constructible_div P (a+1) 2
    (constructible_add P a 1 ha (constructible_one P)) htwo (by norm_num)
  apply constructible_of_on_vertical
  apply vertical_circle (vertical_direction P) auxiliaryHeight_ne
    hc (constructible_origin P) hr
  dsimp [squaredDistance,origin]
  nlinarith [Real.sq_sqrt hnonneg]

/-- The two circles centered at the origin and unit point determine a point
and its reflection across the horizontal axis, without using projections. -/
lemma constructible_reflect_horizontal {P : InitialData} {p : Point}
    (hp : IsConstructible P p) : IsConstructible P (p.1,-p.2) := by
  apply constructible_intersection
    (c := .circle origin origin p) (d := .circle unitPoint unitPoint p)
    ⟨constructible_origin P,constructible_origin P,hp⟩
    ⟨constructible_unitPoint P,constructible_unitPoint P,hp⟩
    (circle_locus_ne (by simp [origin,unitPoint]))
  · apply finite_pair_intersection (p := p) (q := (p.1,-p.2))
    intro z hz
    obtain ⟨h₁,h₂⟩ := hz
    dsimp [Curve.locus,squaredDistance,origin,unitPoint] at h₁ h₂
    have hx : z.1 = p.1 := by nlinarith [h₁,h₂]
    have hy : z.2^2 = p.2^2 := by rw [hx] at h₁; nlinarith [h₁]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
    · exact Or.inl (Prod.ext hx hy)
    · exact Or.inr (Prod.ext hx hy)
  · constructor <;> dsimp [Curve.locus,squaredDistance,origin,unitPoint] <;> ring

theorem constructible_project_fst (P : InitialData) (p : Point)
    (hp : IsConstructible P p) : IsConstructible P (p.1,0) := by
  by_cases hy : p.2 = 0
  · have he : p = (p.1,0) := Prod.ext rfl hy
    rw [← he]; exact hp
  have hr := constructible_reflect_horizontal hp
  have hne : p ≠ (p.1,-p.2) := by
    intro h; have := congrArg Prod.snd h; dsimp at this; exact hy (by linarith)
  apply constructible_line_intersection (constructible_origin P) (constructible_unitPoint P)
    (by simp [origin,unitPoint]) (d := .line p (p.1,-p.2)) ⟨hp,hr,hne⟩
  · apply finite_pair_intersection (p := (p.1,0)) (q := (p.1,0))
    intro z hz
    have hz₀ : z.2 = 0 := by simpa [Curve.locus,origin,unitPoint] using hz.1
    have hx := hz.2
    dsimp [Curve.locus] at hx
    have he : (2*p.2)*(z.1-p.1) = 0 := by nlinarith [hx]
    have hx₀ : z.1 = p.1 := by
      rcases mul_eq_zero.mp he with h | h
      · exact (hy (by linarith)).elim
      · linarith
    exact Or.inl (Prod.ext hx₀ hz₀)
  · constructor
    · simp [Curve.locus,origin,unitPoint]
    · dsimp [Curve.locus]; ring

lemma constructible_snd_real {P : InitialData} {p : Point}
    (hp : IsConstructible P p) : IsConstructibleReal P p.2 := by
  have hx := constructible_project_fst P p hp
  apply horizontal_circle (constructible_origin P) hp hx
  dsimp [squaredDistance,origin]; ring

theorem constructible_project_snd (P : InitialData) (p : Point)
    (hp : IsConstructible P p) : IsConstructible P (0,p.2) :=
  constructible_on_vertical (constructible_snd_real hp)

lemma constructible_iff_coordinates {P : InitialData} {p : Point} :
    IsConstructible P p ↔ IsConstructibleReal P p.1 ∧ IsConstructibleReal P p.2 := by
  constructor
  · intro hp
    exact ⟨constructible_project_fst P p hp, constructible_snd_real hp⟩
  · rintro ⟨hx,hy⟩
    exact constructible_combine P p.1 p.2 hx hy

end D07.Ch15.StraightedgeCompass
