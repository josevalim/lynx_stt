namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-! Monotonicity of the maps of `map_update/5` for `:keep` and `:reject` of a value. -/

theorem old_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {κ : MKey} {o : Option V} (h : Old M₁ κ o) :
    Old M₂ κ o :=
  let ⟨u, hu, e⟩ := h; ⟨u, hM u hu, e⟩

theorem newF_mono {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {nopt : Bool} {md : String}
    {O₁ O₂ : Option V → Prop} (hO : ∀ o, O₁ o → O₂ o) {o : Option V} (h : NewF den nt₁ nopt md O₁ o) :
    NewF den nt₂ nopt md O₂ o := by
  unfold NewF at *
  rcases h with ⟨⟨x, hx⟩, h⟩ | ⟨h0, h⟩
  · refine Or.inl ⟨⟨x, hO _ hx⟩, ?_⟩
    rcases h with h | ⟨y, e, hy⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, e, hv y hy⟩
  · refine Or.inr ⟨hO _ h0, ?_⟩
    rcases h with ⟨hf, h | ⟨y, e, hy⟩⟩ | hk
    · exact Or.inl ⟨hf, Or.inl h⟩
    · exact Or.inl ⟨hf, Or.inr ⟨y, e, hv y hy⟩⟩
    · exact Or.inr hk

theorem kindHeld_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {d : String} (h : KindHeld M₁ d) :
    KindHeld M₂ d :=
  ⟨fun e F => let ⟨u, hu, s, ns, hs⟩ := h.1 e F; ⟨u, hM u hu, s, ns, hs⟩,
    fun e => let ⟨u, hu, hk⟩ := h.2 e; ⟨u, hM u hu, hk⟩⟩

theorem kindVal_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {d : String} {x : V} (h : KindVal M₁ d x) :
    KindVal M₂ d x :=
  let ⟨u, k, j, hu, e, hx⟩ := h; ⟨u, k, j, hM u hu, e, hx⟩

theorem newDomS_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x)
    {md d : String} {x : V} (h : NewDomS den M₁ nt₁ md d x) : NewDomS den M₂ nt₂ md d x :=
  ⟨hv x h.1, h.2.imp id (kindHeld_mono hM)⟩

theorem domNES_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x)
    {nopt : Bool} {md d : String} (h : DomNES den M₁ nt₁ nopt md d) : DomNES den M₂ nt₂ nopt md d :=
  h.imp id fun ⟨hf, hn⟩ => ⟨hf.imp id (kindHeld_mono hM), hn.imp id fun ⟨x, hx⟩ => ⟨x, hv x hx⟩⟩

theorem keyNES_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁)
    {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {nopt : Bool} {md s : String}
    (h : KeyNES den M₁ S₁ nt₁ nopt md s) : KeyNES den M₂ S₂ nt₂ nopt md s :=
  ⟨fun m => h.1 (hS s m), let ⟨o, ho⟩ := h.2; ⟨o, newF_mono hv (fun _ => old_mono hM) ho⟩⟩

theorem updHasS_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁)
    {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {nopt : Bool} {md : String} {Ds₁ Ds₂ : List String}
    (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {A₁ A₂ : Prop → Prop → Prop}
    (hA : ∀ (o₁ n₁ o₂ n₂ : Prop), (o₁ → o₂) → (n₁ → n₂) → A₁ o₁ n₁ → A₂ o₂ n₂)
    (h : UpdHasS den M₁ S₁ nt₁ nopt md Ds₁ A₁) : UpdHasS den M₂ S₂ nt₂ nopt md Ds₂ A₂ := by
  rcases h with ⟨s, hk, h⟩ | ⟨d, md', da, hne, h⟩
  · exact Or.inl ⟨s, keyNES_mono hM hS hv hk, hA _ _ _ _ (fun ⟨x, hx⟩ => ⟨x, old_mono hM hx⟩)
      (fun ⟨x, hx⟩ => ⟨x, newF_mono hv (fun _ => old_mono hM) hx⟩) h⟩
  · exact Or.inr ⟨d, hD d md', da, domNES_mono hM hv hne, hA _ _ _ _ (fun ⟨x, hx⟩ => ⟨x, kindVal_mono hM hx⟩)
      (fun ⟨x, hx⟩ => ⟨x, newDomS_mono hM hv hx⟩) h⟩

/-- Not keeping, with a value: some update gives a value as soon as some update is not empty. -/
theorem upd_present {M : MW V → Prop} {S : List String} {nt : Term} {md : String} {Ds : List String}
    (hmd : md = "force" ∨ md = "reject") (vne : ∃ x, den nt x)
    (h : UpdHasS den M S nt Bool.false md Ds (fun _ _ => True)) :
    UpdHasS den M S nt Bool.false md Ds (fun _ n => n) := by
  obtain ⟨x, hx⟩ := vne
  rcases h with ⟨s, hk, -⟩ | ⟨d, md', da, hne, -⟩
  · refine Or.inl ⟨s, hk, x, ?_⟩
    obtain ⟨o, ho⟩ := hk.2
    unfold NewF at ho ⊢
    rcases ho with ⟨ho, -⟩ | ⟨h0, h⟩
    · exact Or.inl ⟨ho, Or.inr ⟨x, rfl, hx⟩⟩
    · rcases h with ⟨hf, -⟩ | ⟨hk', -⟩
      · exact Or.inr ⟨h0, Or.inl ⟨hf, Or.inr ⟨x, rfl, hx⟩⟩⟩
      · rcases hmd with rfl | rfl <;> simp at hk'
  · refine Or.inr ⟨d, md', da, hne, x, hx, ?_⟩
    rcases hne with hk | ⟨hf, -⟩
    · rcases hmd with rfl | rfl <;> simp at hk
    · exact hf

/-- Keeping a value, no update removes the values of a key or a kind. -/
theorem keep_noLoss {M : MW V → Prop} {S : List String} {nt : Term} {Ds : List String} (vne : ∃ x, den nt x) :
    ¬UpdHasS den M S nt Bool.false "keep" Ds (fun o n => o ∧ ¬n) := by
  obtain ⟨x, hx⟩ := vne
  rintro (⟨s, -, ho, hn⟩ | ⟨d, -, da, -, ⟨y, u, k, j, hu, e, hy⟩, hn⟩)
  · obtain ⟨y, hy⟩ := ho
    exact hn ⟨x, Or.inl ⟨⟨y, hy⟩, Or.inr ⟨x, rfl, hx⟩⟩⟩
  · exact hn ⟨x, hx, Or.inr ⟨fun h => absurd h da, fun _ => ⟨u, hu, k, j, e, by rw [hy]; simp⟩⟩⟩

theorem outV_mono {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) {o : Option V} (h : OutV den nt₂ o) :
    OutV den nt₁ o :=
  h.imp id fun ⟨x, e, hx⟩ => ⟨x, e, fun h' => hx (hv x h')⟩

/-- The box is monotone in the type, the atoms of the key type, the kinds and the value. -/
theorem boxSem_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {S₁ S₂ : List String}
    (hS : ∀ s, s ∈ S₂ → s ∈ S₁) {nt₁ nt₂ : Term} (hv : ∀ x, den nt₁ x → den nt₂ x) (vne : ∃ x, den nt₁ x)
    {md : String} (hmd : Mode md) {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V}
    (h : BoxSem den M₁ S₁ nt₁ Bool.false md Ds₁ w) : BoxSem den M₂ S₂ nt₂ Bool.false md Ds₂ w := by
  obtain ⟨pre₁, hs₁, hn₁⟩ := h
  have pre₂ := updHasS_mono hM hS hv hD (A₁ := fun _ _ => True) (A₂ := fun _ _ => True) (fun _ _ _ _ _ _ h => h) pre₁
  have rs : ∀ s, RS den M₂ S₂ nt₂ Bool.false md Ds₂ s → RS den M₁ S₁ nt₁ Bool.false md Ds₁ s := by
    rintro s ⟨hr, nd, hk, uq⟩
    have nd₁ : ∀ d ∈ Ds₁, d ≠ "atom" → ¬DomNES den M₁ nt₁ Bool.false md d := fun d md' da h' =>
      nd d (hD d md') da (domNES_mono hM hv h')
    rcases pre₁ with ⟨s', hk', -⟩ | ⟨d, md', da, hne, -⟩
    · have := uq s' (keyNES_mono hM hS hv hk')
      subst this
      exact ⟨hr, nd₁, hk', fun s'' h'' => uq s'' (keyNES_mono hM hS hv h'')⟩
    · exact absurd hne (nd₁ d md' da)
  have fullD : (∀ d ∈ domainKinds, d ∈ Ds₁) → ∀ d ∈ domainKinds, d ∈ Ds₂ := fun h d m => hD d (h d m)
  have pres : md ≠ "keep" → PresentS den M₁ S₁ nt₁ Bool.false md Ds₁ := fun nk =>
    ⟨fun hk => absurd hk nk, fun _ => upd_present (by rcases hmd with h | h | h <;> simp_all) vne pre₁⟩
  refine ⟨pre₂, fun hs₂ => ?_, fun ns₂ => ?_⟩
  · have hs₁' : SameS den M₁ S₁ nt₁ Bool.false md Ds₁ := ⟨hs₂.1, fun h' => hs₂.2 (updHasS_mono hM hS hv hD
      (A₁ := fun o n => o ∨ n) (A₂ := fun o n => o ∨ n) (fun _ _ _ _ ho hn h => h.imp ho hn) h')⟩
    exact hM w (hs₁ hs₁')
  by_cases sm₁ : SameS den M₁ S₁ nt₁ Bool.false md Ds₁
  · have wM := hM w (hs₁ sm₁)
    have hk : md = "keep" := sm₁.1
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hk hc.2.1, fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S₂
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · refine Or.inr ⟨sS, Or.inl ⟨fun r => ?_, w, wM, rfl⟩⟩
        have := r.1; rw [hk] at this; simp at this
    · cases e : w (.dom k i) with
      | none => exact Or.inl rfl
      | some x => exact Or.inr ⟨x, rfl, Or.inl ⟨w, k, i, wM, rfl, e⟩⟩
    · rintro rfl; exact (hp.1 hk).2 wM
  obtain ⟨⟨ha, hd⟩, hq⟩ := hn₁ sm₁
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => ?_, fun nc => ?_⟩⟩
  · rcases ha s with ⟨sS1, h⟩ | ⟨nS1, ⟨nr, h⟩ | h⟩
    · by_cases sS : s ∈ S₂
      · exact Or.inl ⟨sS, old_mono hM h⟩
      · exact Or.inr ⟨sS, Or.inl ⟨fun r => (rs s r).2.2.1.1 sS1, old_mono hM h⟩⟩
    · exact Or.inr ⟨fun m => nS1 (hS s m), Or.inl ⟨fun r => nr (rs s r), old_mono hM h⟩⟩
    · exact Or.inr ⟨fun m => nS1 (hS s m), Or.inr (newF_mono hv (fun _ => old_mono hM) h)⟩
  · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h, Or.inl (kindVal_mono hM hx)⟩
    · exact Or.inr ⟨x, h, Or.inr ⟨hD _ dk, newDomS_mono hM hv hx⟩⟩
  · have hc₁ : Bool.false = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds₁ :=
      ⟨rfl, hc.2.1, fun f => hc.2.2 (fullD f)⟩
    intro hu
    exact (hq (pres hc.2.1)).1 hc₁ ⟨fun s nS1 => outV_mono hv (hu.1 s fun m => nS1 (hS s m)),
      fun k i dk => outV_mono hv (hu.2 k i (hD _ dk))⟩
  · by_cases hk : md = "keep"
    · subst hk
      have p₁ : PresentS den M₁ S₁ nt₁ Bool.false "keep" Ds₁ :=
        ⟨fun _ => ⟨keep_noLoss vne, fun h0 => (hp.1 rfl).2 (hM _ h0)⟩, fun h => absurd rfl h⟩
      exact (hq p₁).2 fun c => c.2.1 rfl
    · by_cases c₁ : Bool.false = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds₁
      · rintro rfl
        exact (hq (pres hk)).1 c₁ ⟨fun s _ => Or.inl rfl, fun k i _ => Or.inl rfl⟩
      · exact (hq (pres hk)).2 c₁

theorem keepSemM_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    {keep : Bool} {a : String} {w : MW V} (h : KeepSemM den M₁ v₁ keep a w) : KeepSemM den M₂ v₂ keep a w := by
  rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨hk, hn, hw⟩
  · exact Or.inl ⟨⟨x, e, hv x hx⟩, y, hM _ hy⟩
  · exact Or.inr ⟨hk, hn, hM _ hw⟩

theorem agreeP_mono {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {P₁ P₂ : String → V → Prop}
    (hP : ∀ d x, P₁ d x → P₂ d x) {F : List MKey} {w u : MW V} (h : AgreeP Ds₁ P₁ F w u) : AgreeP Ds₂ P₂ F w u := by
  refine ⟨h.1, fun k i nk => h.2.1 k i fun m => nk (hD _ m), fun k i mF dk => ?_⟩
  by_cases d₁ : domKind k ∈ Ds₁
  · rcases h.2.2 k i mF d₁ with e | e | ⟨x, e, hx⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨x, e, hP _ x hx⟩)
  · exact Or.inr (Or.inl (h.2.1 k i d₁))

theorem wres_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    (vne : ∃ x, den v₁ x) {md : String} {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V} (h : WRes den M₁ v₁ md Ds₁ w) :
    WRes den M₂ v₂ md Ds₂ w := by
  obtain ⟨hs, he⟩ := h
  refine ⟨fun F => ?_, fun _ => ⟨fun hk h0 => hM _ ((he vne).1 hk h0), (he vne).2⟩⟩
  obtain ⟨u, hu, hr, a⟩ := hs F
  exact ⟨u, hM u hu, fun r => let ⟨d, md', hk⟩ := hr r; ⟨d, hD d md', hk⟩,
    agreeP_mono hD (fun d x h => ⟨hv x h.1, h.2⟩) a⟩

/-- An update at a named atom of the key type gives maps of the box. -/
theorem keep_box {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    {keep : Bool} {S : List String} {Ds : List String} {a : String} (ha : a ∉ S) {w : MW V}
    (h : KeepSemM den M₁ v₁ keep a w) : BoxSem den M₂ S v₂ Bool.false (modeS keep) Ds w := by
  -- The key's old field and its update.
  have keyA : KeyNES den M₂ S v₂ Bool.false (modeS keep) a := by
    refine ⟨ha, ?_⟩
    rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨rfl, hn, hw⟩
    · exact ⟨some x, Or.inl ⟨⟨y, _, hM _ hy, by simp [setK]⟩, Or.inr ⟨x, rfl, hv x hx⟩⟩⟩
    · exact ⟨none, Or.inr ⟨⟨w, hM _ hw, hn⟩, Or.inr ⟨rfl, rfl⟩⟩⟩
  have notR : ∀ s, s ≠ a → ¬RS den M₂ S v₂ Bool.false (modeS keep) Ds s := fun s ne r => ne (r.2.2.2 a keyA).symm
  refine ⟨Or.inl ⟨a, keyA, trivial⟩, fun hs => ?_, fun ns => ?_⟩
  · rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨-, -, hw⟩
    · exact absurd (Or.inl ⟨a, keyA, Or.inl ⟨y, _, hM _ hy, by simp [setK]⟩⟩) hs.2
    · exact hM _ hw
  rcases h with ⟨⟨x, e, hx⟩, y, hy⟩ | ⟨hk, hn, hw⟩
  · -- The key holds a value of the type.
    have u₀ := hM _ hy
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun _ => ⟨fun _ hu => ?_, fun _ => ?_⟩⟩
    · by_cases sa : s = a
      · subst sa
        refine Or.inr ⟨ha, Or.inr ?_⟩
        rw [e]
        exact Or.inl ⟨⟨y, _, u₀, by simp [setK]⟩, Or.inr ⟨x, rfl, hv x hx⟩⟩
      · have ew : w (.atom s) = setK a (some y) w (.atom s) := by simp [setK, sa]
        by_cases sS : s ∈ S
        · exact Or.inl ⟨sS, _, u₀, ew.symm⟩
        · exact Or.inr ⟨sS, Or.inl ⟨notR s sa, _, u₀, ew.symm⟩⟩
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨_, k, i, u₀, rfl, by simp [setK, e']⟩⟩
    · rcases hu.1 a ha with h' | ⟨z, h', hz⟩
      · rw [e] at h'; cases h'
      · rw [e] at h'; cases h'; exact hz (hv x hx)
    · intro e0; rw [e0] at e; simp [wNone] at e
  · -- Keeping a map lacking the key.
    have wM := hM _ hw
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => ?_, fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · refine Or.inr ⟨sS, Or.inl ⟨fun r => ?_, w, wM, rfl⟩⟩
        have := r.1; rw [hk] at this; simp [modeS] at this
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨w, k, i, wM, rfl, e'⟩⟩
    · exact absurd (by rw [hk]; rfl) hc.2.1
    · rintro rfl
      exact (hp.1 (by rw [hk]; rfl)).2 wM

/-- Rejecting with every kind in the box: the widened kinds give maps of the box. -/
theorem widen_box {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    (vne : ∃ x, den v₁ x) {S Ws Ds : List String} (hA : "atom" ∉ Ws) (hD : ∀ d ∈ Ws, d ∈ Ds)
    (hfull : ∀ d ∈ domainKinds, d ∈ Ds) {w : MW V}
    (h : WRes den M₁ v₁ "reject" Ws w) : BoxSem den M₂ S v₂ Bool.false "reject" Ds w := by
  obtain ⟨hs, he⟩ := h
  obtain ⟨u₀, hu₀, hr₀, a₀⟩ := hs []
  obtain ⟨d₀, md₀, hk₀⟩ := hr₀ rfl
  have da : d₀ ≠ "atom" := fun e => hA (e ▸ md₀)
  obtain ⟨x₀, hx₀⟩ := vne
  have dne : DomNES den M₂ v₂ Bool.false "reject" d₀ :=
    Or.inr ⟨Or.inr ⟨fun e => absurd e da, fun _ => ⟨u₀, hM _ hu₀, hk₀⟩⟩, Or.inr ⟨x₀, hv x₀ hx₀⟩⟩
  refine ⟨Or.inr ⟨d₀, hD d₀ md₀, da, dne, trivial⟩, fun hs' => absurd hs'.1 (by simp), fun _ => ?_⟩
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun _ => ⟨fun hc _ => hc.2.2 hfull, fun _ => (he ⟨x₀, hx₀⟩).2 (by simp)⟩⟩
  · by_cases sS : s ∈ S
    · exact Or.inl ⟨sS, u₀, hM _ hu₀, (a₀.1 s).symm⟩
    · exact Or.inr ⟨sS, Or.inl ⟨fun r => r.2.1 d₀ (hD d₀ md₀) da dne, u₀, hM _ hu₀, (a₀.1 s).symm⟩⟩
  · obtain ⟨u, hu, -, a⟩ := hs [.dom k i]
    by_cases dk : domKind k ∈ Ws
    · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx, hK⟩
      · exact Or.inl e
      · cases e' : u (.dom k i) with
        | none => exact Or.inl (e.trans e')
        | some z => exact Or.inr ⟨z, e.trans e', Or.inl ⟨u, k, i, hM _ hu, rfl, e'⟩⟩
      · have hK' : HasKind u (domKind k) := hK.resolve_left (by simp)
        exact Or.inr ⟨x, e, Or.inr ⟨hD _ dk, hv x hx, Or.inr ⟨fun e => absurd e (domKind_ne_atom k), fun _ =>
          ⟨u, hM _ hu, hK'⟩⟩⟩⟩
    · rw [a.2.1 k i dk]
      cases e' : u (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨u, k, i, hM _ hu, rfl, e'⟩⟩

/-- `map_update/5` for `:keep` and `:reject` of a value is monotone in the type, the keys and the value. -/
theorem upd_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term} (hv : ∀ x, den v₁ x → den v₂ x)
    (vne : ∃ x, den v₁ x) {keep : Bool} {rs₁ rs₂ Ds₁ Ds₂ Dm₁ Dm₂ : List String} {neg₁ neg₂ : Term}
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom))
    (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (hK : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    (hDm₁ : ∀ d, d ∈ Dm₁ ↔ d ∈ Ds₁ ∧ (keep = Bool.true ∨ KindHeld M₁ d))
    (hDm₂ : ∀ d, d ∈ Dm₂ ↔ d ∈ Ds₂ ∧ (keep = Bool.true ∨ KindHeld M₂ d)) {w : MW V}
    (h : UpdSemKR den M₁ rs₁ neg₁ Dm₁ v₁ keep w) : UpdSemKR den M₂ rs₂ neg₂ Dm₂ v₂ keep w := by
  classical
  have hD₁ : ∀ s ∈ Ds₁, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok₁.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  -- The kinds of the small split are kinds of the large one.
  have dsub : ∀ d ∈ Ds₁, d ∈ Ds₂ := by
    intro d md
    by_cases da : d = "atom"
    · subst da
      obtain ⟨N₁, e₁⟩ := ok₁.hatom.mp (List.mem_map_of_mem md)
      subst e₁
      obtain ⟨c, hc⟩ := fresh_str (keyStrs N₁ ++ rs₂)
      have k₂ := hK (.atom c) (Or.inr ⟨N₁, rfl, lookup_fresh' fun m => hc (List.mem_append_left _ m)⟩)
      rcases k₂ with m | ⟨N₂, e₂, -⟩
      · obtain ⟨c', mc', e⟩ := List.mem_map.mp m
        cases e; exact absurd (List.mem_append_right _ mc') hc
      · have := ok₂.hatom.mpr ⟨N₂, e₂⟩
        obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    · obtain ⟨k, rfl⟩ := domKind_of (hD₁ _ md) da
      have := hK (.dom k 0) (List.mem_map_of_mem md)
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
  have dmsub : ∀ d ∈ Dm₁, d ∈ Dm₂ := fun d m => by
    obtain ⟨md, h'⟩ := (hDm₁ d).mp m
    exact (hDm₂ d).mpr ⟨dsub d md, h'.imp id (kindHeld_mono hM)⟩
  have fullM : FullK Dm₁ → FullK Dm₂ := fun f d m => dmsub d (f d m)
  have filt : ∀ (p : String → Bool) d, d ∈ Dm₁.filter p → d ∈ Dm₂.filter p := fun p d m => by
    rw [List.mem_filter] at m ⊢; exact ⟨dmsub d m.1, m.2⟩
  have rmode : keep = Bool.false → modeS keep = "reject" := fun e => by subst e; rfl
  -- The atoms of the small split are atoms of the large one.
  have named : ∀ a ∈ rs₁, (neg₂ = .atom "nil" → a ∈ rs₂) ∧ ∀ N₂, neg₂ = .map N₂ → a ∉ setStrs N₂ := by
    intro a ma
    have k₂ := hK (.atom a) (Or.inl (List.mem_map_of_mem ma))
    refine ⟨fun e => ?_, fun N₂ e => ?_⟩
    · rcases k₂ with m | ⟨N, e', -⟩
      · obtain ⟨a', ma', e⟩ := List.mem_map.mp m; cases e; exact ma'
      · rw [e] at e'; cases e'
    · rcases k₂ with m | ⟨N, e', hN⟩
      · rw [nr₂ N₂ e] at m; simp at m
      · rw [e] at e'; cases e'; exact fun m => setStrs_mem.mp m hN
  rcases h with ⟨rfl, hn | ⟨dne, hw⟩⟩ | ⟨N₁, rfl, h⟩
  · -- An atom of the small split.
    obtain ⟨a, ma, ha⟩ := hn
    rcases ok₂.hneg with rfl | ⟨N₂, rfl⟩
    · exact Or.inl ⟨rfl, Or.inl ⟨a, (named a ma).1 rfl, keepSemM_mono hM hv ha⟩⟩
    · have hb := fun Ds => keep_box (Ds := Ds) hM hv ((named a ma).2 N₂ rfl) ha
      by_cases f : keep = Bool.false ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, hb Dm₂⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (hb _)⟩⟩
  · -- The widened kinds of the small split.
    have nA : "atom" ∉ Dm₁ := fun m => by
      obtain ⟨N, e⟩ := ok₁.hatom.mp (List.mem_map_of_mem ((hDm₁ _).mp m).1); cases e
    rcases ok₂.hneg with rfl | ⟨N₂, rfl⟩
    · refine Or.inl ⟨rfl, Or.inr ⟨fun e => dne ?_, wres_mono hM hv vne dmsub hw⟩⟩
      cases Dm₁ with
      | nil => rfl
      | cons d _ => have := dmsub d List.mem_cons_self; rw [e] at this; cases this
    · by_cases f : keep = Bool.false ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        rw [rmode kf] at hw
        refine Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, ?_⟩⟩
        rw [rmode kf]
        exact widen_box hM hv vne nA dmsub full hw
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => dne ?_, wres_mono hM hv vne (fun d m => ?_) hw⟩⟩⟩
        · cases Dm₁ with
          | nil => rfl
          | cons d _ =>
            have := filt (fun x => decide (x ≠ "atom")) d (by
              simp only [List.mem_filter, List.mem_cons_self, true_and, decide_eq_true_eq]
              exact fun e' => nA (e' ▸ List.mem_cons_self))
            rw [e] at this; cases this
        · exact filt (fun x => decide (x ≠ "atom")) d (List.mem_filter.mpr ⟨m, by
            simp only [decide_eq_true_eq]; exact fun e' => nA (e' ▸ m)⟩)
  · -- The box and the widened kinds of a negated set.
    have at₁ : "atom" ∈ Ds₁ := by
      have := ok₁.hatom.mpr ⟨N₁, rfl⟩
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    obtain ⟨N₂, e₂⟩ : ∃ N₂, neg₂ = .map N₂ := ok₂.hatom.mp (List.mem_map_of_mem (dsub _ at₁))
    subst e₂
    have hS : ∀ s, s ∈ setStrs N₂ → s ∈ setStrs N₁ := fun s m => Classical.byContradiction fun nm => by
      have hN₁ : mapLookup N₁ (.atom s) = none := by
        cases e : mapLookup N₁ (.atom s) with
        | none => rfl
        | some _ => exact absurd (setStrs_mem.mpr (by rw [e]; simp)) nm
      have k₂ := hK (.atom s) (Or.inr ⟨N₁, rfl, hN₁⟩)
      rcases k₂ with m' | ⟨N, e, hN⟩
      · rw [nr₂ N₂ rfl] at m'; simp at m'
      · cases e; exact setStrs_mem.mp m hN
    have bm := fun {Ds₁' Ds₂' : List String} (hD : ∀ d ∈ Ds₁', d ∈ Ds₂') {w : MW V}
      (h : BoxSem den M₁ (setStrs N₁) v₁ Bool.false (modeS keep) Ds₁' w) =>
      boxSem_mono hM hS hv vne (mode_modeS keep) hD h
    rcases h with ⟨kf, full, hb⟩ | ⟨nf, hb | ⟨wne, hw⟩⟩
    · exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, fullM full, bm dmsub hb⟩⟩
    · by_cases f : keep = Bool.false ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, bm (fun d m => dmsub d (List.mem_filter.mp m).1) hb⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (bm (filt _) hb)⟩⟩
    · have nA : "atom" ∉ Dm₁.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
      by_cases f : keep = Bool.false ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        rw [rmode kf] at hw
        refine Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, ?_⟩⟩
        rw [rmode kf]
        exact widen_box hM hv vne nA (fun d m => dmsub d (List.mem_filter.mp m).1) full hw
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => wne ?_, wres_mono hM hv vne (filt _) hw⟩⟩⟩
        cases h' : Dm₁.filter (· ≠ "atom") with
        | nil => rfl
        | cons d _ =>
          have := filt _ d (by rw [h']; exact List.mem_cons_self)
          rw [e] at this; cases this

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Two successful `map_update/5` of static values at static key types, asking for the old values, on static maps of
the next level: a smaller type, smaller keys and a smaller non-empty value give fewer maps. -/
theorem upd_sub {XL XR : List (Term × Term)} (hXL : DE (level t n).E (.map XL)) (hXR : DE (level t n).E (.map XR))
    (maps : ∀ w, MT t n XL w → MT t n XR w) {k₁ k₂ : Term} {rs₁ rs₂ Ds₁ Ds₂ : List String} {neg₁ neg₂ : Term}
    {m : Nat}
    (rk₁ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₁ =
      .ok (splitT (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)))
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (nr₁ : ∀ N, neg₁ = .map N → rs₁ = [])
    (na₁ : ∀ N, neg₁ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (rk₂ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₂ =
      .ok (splitT (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom)))
    (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom)) (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (na₂ : ∀ N, neg₂ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (keys : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    {v₁ v₂ : Term} (hv₁ : (level t n).E v₁) (hv₂ : (level t n).E v₂)
    (sv₁ : v₁ = .atom "term" ∨ ∃ Z, v₁ = .map Z ∧ mapLookup Z (.atom "dynamic") = none)
    (sv₂ : v₂ = .atom "term" ∨ ∃ Z, v₂ = .map Z ∧ mapLookup Z (.atom "dynamic") = none)
    (vals : ∀ x, (level t n).den v₁ x → (level t n).den v₂ x) (vne : ∃ x, (level t n).den v₁ x) {mode : Term}
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject") (hm : (level t n).K + 26 ≤ m)
    {T₁ Y₁ e₁ T₂ Y₂ e₂ : Term}
    (run₁ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XL) k₁ v₁ mode (.atom "true") =
      .ok (.tuple #[T₁, Y₁, e₁]))
    (run₂ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XR) k₂ v₂ mode (.atom "true") =
      .ok (.tuple #[T₂, Y₂, e₂])) :
    ∃ YL YR, Y₁ = .map YL ∧ Y₂ = .map YR ∧ DE (level t n).E (.map YL) ∧ DE (level t n).E (.map YR) ∧
      SubN t n (.map YL) (.map YR) := by
  have sv₁' : v₁ = .atom "term" ∨ ∃ Z, v₁ = .map Z := sv₁.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  have sv₂' : v₂ = .atom "term" ∨ ∃ Z, v₂ = .map Z := sv₂.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  have vne₂ : ∃ x, (level t n).den v₂ x := let ⟨x, hx⟩ := vne; ⟨x, vals x hx⟩
  have nr₁' : ∀ N, neg₁ = .map N → rs₁.map Term.atom = [] := fun N e => by rw [nr₁ N e]; rfl
  have nr₂' : ∀ N, neg₂ = .map N → rs₂.map Term.atom = [] := fun N e => by rw [nr₂ N e]; rfl
  have side_kr : ∀ {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {k : Term} {rs Ds : List String}
      {neg : Term} (rk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k =
        .ok (splitT (rs.map Term.atom) neg (Ds.map Term.atom)))
      (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rs = [])
      (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {v : Term} (hv : (level t n).E v)
      (vne : ∃ x, (level t n).den v x)
      (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {T Y e : Term}
      (keep : Bool)
      (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k v (modeT keep) (.atom "true") =
        .ok (.tuple #[T, Y, e])),
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld (MT t n X) d)) ∧
          ∀ w, MT t n Y' w ↔ UpdSemKR (level t n).den (MT t n X) rs neg Dm v keep w := by
    intro X hX k rs Ds neg rk ok nr na v hv vne sv T Y e keep run
    obtain ⟨r, rr, rfl | ⟨er, rfl⟩ | ⟨T', Y', er, rfl, -, dY, oY, Dm, mDm, sY⟩⟩ :=
      kr_update hX rk ok nr na hv vne sv keep hm
    · rw [run] at rr; cases rr
    · rw [run] at rr; cases rr
    · rw [run] at rr
      obtain ⟨-, rfl, -⟩ := tuple3_inj (Except.ok.inj rr)
      exact ⟨Y', rfl, dY, oY, Dm, mDm, sY⟩
  rcases hmode with rfl | rfl | rfl
  · -- Forcing: the maps of `map_put/3`.
    have side : ∀ {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {k : Term} {rs Ds : List String}
        {neg : Term} (rk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k =
          .ok (splitT (rs.map Term.atom) neg (Ds.map Term.atom)))
        (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rs = [])
        (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {v : Term} (hv : (level t n).E v)
        (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {T Y e : Term}
        (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k v (.atom "force") (.atom "true") =
          .ok (.tuple #[T, Y, e])),
        ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
          ∀ w, MT t n Y' w ↔ PutSem (level t n).den (MT t n X) (rs.map Term.atom) neg (Ds.map Term.atom) v w := by
      intro X hX k rs Ds neg rk ok nr na v hv sv T Y e run
      obtain ⟨r₁, r₂, put₁, upd₂, ⟨-, rfl⟩ | ⟨-, ⟨er, rfl⟩, -⟩ | ⟨Y'', T', er, rfl, rfl, -⟩⟩ :=
        update_put_old hX rk ok nr na hv sv hm
      · rw [run] at upd₂; cases upd₂
      · rw [run] at upd₂; cases upd₂
      · rw [run] at upd₂
        obtain ⟨-, rfl, -⟩ := tuple3_inj (Except.ok.inj upd₂)
        obtain ⟨res, rres, ⟨rfl, -⟩ | ⟨Y', rfl, -, dY, oY, sY⟩⟩ :=
          dput hX rk ok (fun N e => by rw [nr N e]; rfl) na hv sv hm
        · rw [rres] at put₁; cases put₁
        · rw [rres] at put₁
          have := Except.ok.inj put₁
          simp only [Term.tuple.injEq, List.cons.injEq, Array.mk.injEq, true_and, and_true] at this
          exact ⟨Y', this.symm, dY, oY, sY⟩
    obtain ⟨YL, rfl, dL, oL, sL⟩ := side hXL rk₁ ok₁ nr₁ na₁ hv₁ sv₁ run₁
    obtain ⟨YR, rfl, dR, -, sR⟩ := side hXR rk₂ ok₂ nr₂ na₂ hv₂ sv₂ run₂
    refine ⟨YL, YR, rfl, rfl, dL, dR, fun q hq => ?_⟩
    obtain ⟨w, hw⟩ := pt_map q (oL q hq)
    rw [hw] at hq ⊢
    exact (sR w).mpr (put_mono maps vals ok₁ ok₂ nr₂' keys ((sL w).mp hq))
  all_goals
    first
    | rw [show Term.atom "keep" = modeT Bool.true from rfl] at run₁ run₂
    | rw [show Term.atom "reject" = modeT Bool.false from rfl] at run₁ run₂
    obtain ⟨YL, rfl, dL, oL, Dm₁, mDm₁, sL⟩ := side_kr hXL rk₁ ok₁ nr₁ na₁ hv₁ vne sv₁ _ run₁
    obtain ⟨YR, rfl, dR, -, Dm₂, mDm₂, sR⟩ := side_kr hXR rk₂ ok₂ nr₂ na₂ hv₂ vne₂ sv₂ _ run₂
    refine ⟨YL, YR, rfl, rfl, dL, dR, fun q hq => ?_⟩
    obtain ⟨w, hw⟩ := pt_map q (oL q hq)
    rw [hw] at hq ⊢
    exact (sR w).mpr (upd_mono maps vals vne ok₁ ok₂ nr₂ keys mDm₁ mDm₂ ((sL w).mp hq))

end

end Elixir.STTDescrProofsTest.Nest
