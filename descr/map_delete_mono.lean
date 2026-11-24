namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-! Monotonicity of the maps of `map_update/5` deleting a key. -/

/-- A deletion puts no value. -/
theorem newF_del_some (nn : ∀ x, ¬den (.map []) x) {md : String} {O : Option V → Prop} (x : V) :
    ¬NewF den (.map []) Bool.true md O (some x) := by
  unfold NewF
  intro h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · rcases h with ⟨h, -⟩ | ⟨y, e, hy⟩
    · cases h
    · cases e; exact nn _ hy
  · rcases h with ⟨-, ⟨h, -⟩ | ⟨y, e, hy⟩⟩ | ⟨-, h⟩
    · cases h
    · cases e; exact nn _ hy
    · cases h

theorem newDomS_del (nn : ∀ x, ¬den (.map []) x) {M : MW V → Prop} {md d : String} {x : V} :
    ¬NewDomS den M (.map []) md d x := fun h => nn x h.1

/-- Whether a deletion's updates hold old values or new ones only depends on the old ones. -/
theorem updHasS_del (nn : ∀ x, ¬den (.map []) x) {M : MW V → Prop} {S : List String} {md : String}
    {Ds : List String} {A : Prop → Prop → Prop} :
    UpdHasS den M S (.map []) Bool.true md Ds A ↔ UpdHasS den M S (.map []) Bool.true md Ds (fun o _ => A o False) := by
  have n₁ : ∀ s, (∃ x, NewF den (.map []) Bool.true md (Old M (.atom s)) (some x)) = False := fun s =>
    propext ⟨fun ⟨x, h⟩ => newF_del_some nn x h, False.elim⟩
  have n₂ : ∀ d, (∃ x, NewDomS den M (.map []) md d x) = False := fun d =>
    propext ⟨fun ⟨x, h⟩ => newDomS_del nn h, False.elim⟩
  unfold UpdHasS
  simp only [n₁, n₂]

/-- Not keeping, a deletion's box is never present. -/
theorem presentS_del (nn : ∀ x, ¬den (.map []) x) {M : MW V → Prop} {S : List String} {md : String}
    {Ds : List String} (hk : md ≠ "keep") : ¬PresentS den M S (.map []) Bool.true md Ds := by
  intro h
  have := (updHasS_del nn).mp (h.2 hk)
  rcases this with ⟨_, _, h'⟩ | ⟨_, _, _, _, h'⟩ <;> exact h'

theorem delAt_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md a : String} {w : MW V}
    (h : DelAt M₁ md a w) : DelAt M₂ md a w :=
  ⟨h.1, h.2.imp (fun ⟨x, hx⟩ => ⟨x, hM _ hx⟩) fun ⟨hr, hw⟩ => ⟨hr, hM _ hw⟩⟩

theorem wres_mono_del (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    {Ds₁ Ds₂ : List String} (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V} (h : WRes den M₁ (.map []) md Ds₁ w) :
    WRes den M₂ (.map []) md Ds₂ w := by
  obtain ⟨hs, -⟩ := h
  refine ⟨fun F => ?_, fun ⟨x, hx⟩ => absurd hx (nn x)⟩
  obtain ⟨u, hu, hr, a⟩ := hs F
  exact ⟨u, hM u hu, fun r => let ⟨d, md', hk⟩ := hr r; ⟨d, hD d md', hk⟩, agreeP_mono hD (fun d x h => h) a⟩

/-- The box of a deletion is monotone in the type, the atoms of the key type and the kinds. -/
theorem boxSem_mono_del (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u)
    {S₁ S₂ : List String} (hS : ∀ s, s ∈ S₂ → s ∈ S₁) {md : String} {Ds₁ Ds₂ : List String}
    (hD : ∀ d ∈ Ds₁, d ∈ Ds₂) {w : MW V}
    (h : BoxSem den M₁ S₁ (.map []) Bool.true md Ds₁ w) : BoxSem den M₂ S₂ (.map []) Bool.true md Ds₂ w := by
  have hv : ∀ x, den (.map []) x → den (.map []) x := fun _ h => h
  obtain ⟨pre₁, hs₁, hn₁⟩ := h
  have pre₂ := updHasS_mono hM hS hv hD (A₁ := fun _ _ => True) (A₂ := fun _ _ => True) (fun _ _ _ _ _ _ h => h) pre₁
  have rs : ∀ s, RS den M₂ S₂ (.map []) Bool.true md Ds₂ s → RS den M₁ S₁ (.map []) Bool.true md Ds₁ s := by
    rintro s ⟨hr, nd, hk, uq⟩
    have nd₁ : ∀ d ∈ Ds₁, d ≠ "atom" → ¬DomNES den M₁ (.map []) Bool.true md d := fun d md' da h' =>
      nd d (hD d md') da (domNES_mono hM hv h')
    rcases pre₁ with ⟨s', hk', -⟩ | ⟨d, md', da, hne, -⟩
    · have := uq s' (keyNES_mono hM hS hv hk')
      subst this
      exact ⟨hr, nd₁, hk', fun s'' h'' => uq s'' (keyNES_mono hM hS hv h'')⟩
    · exact absurd hne (nd₁ d md' da)
  -- Old values of a key or kind of the box.
  have olds : UpdHasS den M₁ S₁ (.map []) Bool.true md Ds₁ (fun o _ => o) →
      UpdHasS den M₂ S₂ (.map []) Bool.true md Ds₂ (fun o _ => o) := fun h =>
    updHasS_mono hM hS hv hD (A₁ := fun o _ => o) (A₂ := fun o _ => o) (fun _ _ _ _ ho _ h => ho h) h
  refine ⟨pre₂, fun hs₂ => ?_, fun ns₂ => ?_⟩
  · have hs₁' : SameS den M₁ S₁ (.map []) Bool.true md Ds₁ := ⟨hs₂.1, fun h' => hs₂.2 (updHasS_mono hM hS hv hD
      (A₁ := fun o n => o ∨ n) (A₂ := fun o n => o ∨ n) (fun _ _ _ _ ho hn h => h.imp ho hn) h')⟩
    exact hM w (hs₁ hs₁')
  -- A present box: only when keeping, and then the type lacks the empty map, as does the box of the smaller one.
  have pres : PresentS den M₂ S₂ (.map []) Bool.true md Ds₂ → md = "keep" ∧ ¬M₂ wNone ∧
      PresentS den M₁ S₁ (.map []) Bool.true md Ds₁ := fun hp => by
    by_cases hk : md = "keep"
    · obtain ⟨nl, n0⟩ := hp.1 hk
      refine ⟨hk, n0, fun _ => ⟨fun h' => nl ?_, fun h0 => n0 (hM _ h0)⟩, fun h' => absurd hk h'⟩
      exact (updHasS_del nn).mpr (by
        have := olds (by
          have := (updHasS_del nn).mp h'
          exact updHasS_mono (fun u h => h) (fun s h => h) hv (fun d h => h) (A₁ := fun o _ => o ∧ ¬False)
            (A₂ := fun o _ => o) (fun _ _ _ _ ho _ h => ho h.1) this)
        exact updHasS_mono (fun u h => h) (fun s h => h) hv (fun d h => h) (A₁ := fun o _ => o)
          (A₂ := fun o _ => o ∧ ¬False) (fun _ _ _ _ ho _ h => ⟨ho h, id⟩) this)
    · exact absurd hp (presentS_del nn hk)
  by_cases sm₁ : SameS den M₁ S₁ (.map []) Bool.true md Ds₁
  · have wM := hM w (hs₁ sm₁)
    have hk : md = "keep" := sm₁.1
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S₂
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · refine Or.inr ⟨sS, Or.inl ⟨fun r => ?_, w, wM, rfl⟩⟩
        have := r.1; rw [hk] at this; simp at this
    · cases e : w (.dom k i) with
      | none => exact Or.inl rfl
      | some x => exact Or.inr ⟨x, rfl, Or.inl ⟨w, k, i, wM, rfl, e⟩⟩
    · rintro rfl; exact (pres hp).2.1 wM
  obtain ⟨⟨ha, hd⟩, hq⟩ := hn₁ sm₁
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
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
  · exact (hq (pres hp).2.2).2 fun c => absurd c.1 (by simp)

/-- A deletion at a named atom of the key type gives maps of the box. -/
theorem del_box (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    (hmd : Mode md) {S : List String} {Ds : List String} {a : String} (ha : a ∉ S) {w : MW V}
    (h : DelAt M₁ md a w) : BoxSem den M₂ S (.map []) Bool.true md Ds w := by
  obtain ⟨wa, h⟩ := h
  -- The key's old field and its update.
  have keyA : KeyNES den M₂ S (.map []) Bool.true md a := by
    refine ⟨ha, none, ?_⟩
    rcases h with ⟨y, hy⟩ | ⟨hr, hw⟩
    · exact Or.inl ⟨⟨y, _, hM _ hy, by simp [setK]⟩, Or.inl ⟨rfl, rfl⟩⟩
    · refine Or.inr ⟨⟨w, hM _ hw, wa⟩, ?_⟩
      rcases hmd with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hr
  have notR : ∀ s, s ≠ a → ¬RS den M₂ S (.map []) Bool.true md Ds s := fun s ne r => ne (r.2.2.2 a keyA).symm
  refine ⟨Or.inl ⟨a, keyA, trivial⟩, fun hs => ?_, fun ns => ?_⟩
  · rcases h with ⟨y, hy⟩ | ⟨-, hw⟩
    · exact absurd (Or.inl ⟨a, keyA, Or.inl ⟨y, _, hM _ hy, by simp [setK]⟩⟩) hs.2
    · exact hM _ hw
  rcases h with ⟨y, hy⟩ | ⟨hr, hw⟩
  · -- The key held a value.
    have u₀ := hM _ hy
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
    · by_cases sa : s = a
      · subst sa
        refine Or.inr ⟨ha, Or.inr ?_⟩
        rw [wa]
        exact Or.inl ⟨⟨y, _, u₀, by simp [setK]⟩, Or.inl ⟨rfl, rfl⟩⟩
      · have ew : w (.atom s) = setK a (some y) w (.atom s) := by simp [setK, sa]
        by_cases sS : s ∈ S
        · exact Or.inl ⟨sS, _, u₀, ew.symm⟩
        · exact Or.inr ⟨sS, Or.inl ⟨notR s sa, _, u₀, ew.symm⟩⟩
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨_, k, i, u₀, rfl, by simp [setK, e']⟩⟩
    · -- A present box keeps no key with old values.
      by_cases hk : md = "keep"
      · exact absurd ((updHasS_del nn).mpr (Or.inl ⟨a, keyA, ⟨y, _, u₀, by simp [setK]⟩, id⟩)) (hp.1 hk).1
      · exact absurd hp (presentS_del nn hk)
  · -- Not rejecting, a map lacking the key.
    have wM := hM _ hw
    refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => ⟨fun hc => absurd hc.1 (by simp), fun _ => ?_⟩⟩
    · by_cases sS : s ∈ S
      · exact Or.inl ⟨sS, w, wM, rfl⟩
      · exact Or.inr ⟨sS, Or.inl ⟨fun r => hr r.1, w, wM, rfl⟩⟩
    · cases e' : w (.dom k i) with
      | none => exact Or.inl rfl
      | some z => exact Or.inr ⟨z, rfl, Or.inl ⟨w, k, i, wM, rfl, e'⟩⟩
    · by_cases hk : md = "keep"
      · rintro rfl; exact (hp.1 hk).2 wM
      · exact absurd hp (presentS_del nn hk)

/-- Not keeping, with every kind in the box: the widened kinds of a deletion give maps of the box. -/
theorem widen_box_del (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    (hmd : Mode md) (hk : md ≠ "keep") {S Ws Ds : List String} (hA : "atom" ∉ Ws) (neW : Ws ≠ [])
    (hD : ∀ d ∈ Ws, d ∈ Ds) {w : MW V}
    (h : WRes den M₁ (.map []) md Ws w) : BoxSem den M₂ S (.map []) Bool.true md Ds w := by
  obtain ⟨hs, -⟩ := h
  obtain ⟨u₀, hu₀, hr₀, a₀⟩ := hs []
  -- An updated kind other than atoms.
  obtain ⟨d₀, md₀, dne⟩ : ∃ d₀ ∈ Ws, DomNES den M₂ (.map []) Bool.true md d₀ := by
    rcases hmd with rfl | rfl | rfl
    · obtain ⟨d₀, md₀⟩ := List.exists_mem_of_ne_nil Ws neW
      exact ⟨d₀, md₀, Or.inr ⟨Or.inl rfl, Or.inl rfl⟩⟩
    · exact absurd rfl hk
    · obtain ⟨d₀, md₀, hk₀⟩ := hr₀ rfl
      have da : d₀ ≠ "atom" := fun e => hA (e ▸ md₀)
      exact ⟨d₀, md₀, Or.inr ⟨Or.inr ⟨fun e => absurd e da, fun _ => ⟨u₀, hM _ hu₀, hk₀⟩⟩, Or.inl rfl⟩⟩
  have da : d₀ ≠ "atom" := fun e => hA (e ▸ md₀)
  refine ⟨Or.inr ⟨d₀, hD d₀ md₀, da, dne, trivial⟩, fun hs' => absurd hs'.1 hk, fun _ => ?_⟩
  refine ⟨⟨fun s => ?_, fun k i => ?_⟩, fun hp => absurd hp (presentS_del nn hk)⟩
  · by_cases sS : s ∈ S
    · exact Or.inl ⟨sS, u₀, hM _ hu₀, (a₀.1 s).symm⟩
    · exact Or.inr ⟨sS, Or.inl ⟨fun r => r.2.1 d₀ (hD d₀ md₀) da dne, u₀, hM _ hu₀, (a₀.1 s).symm⟩⟩
  · obtain ⟨u, hu, -, a⟩ := hs [.dom k i]
    have kv : ∀ o, o = u (.dom k i) → w (.dom k i) = o → w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧
        (KindVal M₂ (domKind k) x ∨ (domKind k ∈ Ds ∧ NewDomS den M₂ (.map []) md (domKind k) x)) := by
      intro o eo ew
      subst eo
      cases e' : u (.dom k i) with
      | none => exact Or.inl (ew.trans e')
      | some z => exact Or.inr ⟨z, ew.trans e', Or.inl ⟨u, k, i, hM _ hu, rfl, e'⟩⟩
    by_cases dk : domKind k ∈ Ws
    · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx, -⟩
      · exact Or.inl e
      · exact kv _ rfl e
      · exact absurd hx (nn x)
    · exact kv _ rfl (a.2.1 k i dk)

/-- `map_update/5` deleting a key is monotone in the type and the keys. -/
theorem del_mono (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {md : String}
    (hmd : Mode md) {rs₁ rs₂ Ds₁ Ds₂ Dm₁ Dm₂ : List String} {neg₁ neg₂ : Term}
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom))
    (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (hK : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    (hDm₁ : ∀ d, d ∈ Dm₁ ↔ d ∈ Ds₁ ∧ (md ≠ "reject" ∨ KindHeld M₁ d))
    (hDm₂ : ∀ d, d ∈ Dm₂ ↔ d ∈ Ds₂ ∧ (md ≠ "reject" ∨ KindHeld M₂ d)) {w : MW V}
    (h : UpdSemD den M₁ rs₁ neg₁ Dm₁ md w) : UpdSemD den M₂ rs₂ neg₂ Dm₂ md w := by
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
    · exact Or.inl ⟨rfl, Or.inl ⟨a, (named a ma).1 rfl, delAt_mono hM ha⟩⟩
    · have hb := fun Ds => del_box (Ds := Ds) nn hM hmd ((named a ma).2 N₂ rfl) ha
      by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, hb Dm₂⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (hb _)⟩⟩
  · -- The widened kinds of the small split.
    have nA : "atom" ∉ Dm₁ := fun m => by
      obtain ⟨N, e⟩ := ok₁.hatom.mp (List.mem_map_of_mem ((hDm₁ _).mp m).1); cases e
    rcases ok₂.hneg with rfl | ⟨N₂, rfl⟩
    · refine Or.inl ⟨rfl, Or.inr ⟨fun e => dne ?_, wres_mono_del nn hM dmsub hw⟩⟩
      cases Dm₁ with
      | nil => rfl
      | cons d _ => have := dmsub d List.mem_cons_self; rw [e] at this; cases this
    · by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, widen_box_del nn hM hmd kf nA dne dmsub hw⟩⟩
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => dne ?_, wres_mono_del nn hM (fun d m => ?_) hw⟩⟩⟩
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
      (h : BoxSem den M₁ (setStrs N₁) (.map []) Bool.true md Ds₁' w) =>
      boxSem_mono_del nn hM hS hD h
    rcases h with ⟨kf, full, hb⟩ | ⟨nf, hb | ⟨wne, hw⟩⟩
    · exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, fullM full, bm dmsub hb⟩⟩
    · by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · exact Or.inr ⟨N₂, rfl, Or.inl ⟨f.1, f.2, bm (fun d m => dmsub d (List.mem_filter.mp m).1) hb⟩⟩
      · exact Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inl (bm (filt _) hb)⟩⟩
    · have nA : "atom" ∉ Dm₁.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
      by_cases f : md ≠ "keep" ∧ FullK Dm₂
      · obtain ⟨kf, full⟩ := f
        exact Or.inr ⟨N₂, rfl, Or.inl ⟨kf, full, widen_box_del nn hM hmd kf nA wne
          (fun d m => dmsub d (List.mem_filter.mp m).1) hw⟩⟩
      · refine Or.inr ⟨N₂, rfl, Or.inr ⟨f, Or.inr ⟨fun e => wne ?_, wres_mono_del nn hM (filt _) hw⟩⟩⟩
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

/-- Two successful `map_update/5` deleting static key types, asking for the old values, on static maps of the next
level: a smaller type and smaller keys give fewer maps. -/
theorem del_sub {XL XR : List (Term × Term)} (hXL : DE (level t n).E (.map XL)) (hXR : DE (level t n).E (.map XR))
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
    {md : String} (hmd : Mode md) (hm : (level t n).K + 26 ≤ m)
    {T₁ Y₁ e₁ T₂ Y₂ e₂ : Term}
    (run₁ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XL) k₁ (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T₁, Y₁, e₁]))
    (run₂ : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map XR) k₂ (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T₂, Y₂, e₂])) :
    ∃ YL YR, Y₁ = .map YL ∧ Y₂ = .map YR ∧ DE (level t n).E (.map YL) ∧ DE (level t n).E (.map YR) ∧
      SubN t n (.map YL) (.map YR) := by
  have side : ∀ {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {k : Term} {rs Ds : List String}
      {neg : Term} (rk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k =
        .ok (splitT (rs.map Term.atom) neg (Ds.map Term.atom)))
      (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rs = [])
      (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {T Y e : Term}
      (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k (.atom "delete") (.atom md) (.atom "true") =
        .ok (.tuple #[T, Y, e])),
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n X) d)) ∧
          ∀ w, MT t n Y' w ↔ UpdSemD (level t n).den (MT t n X) rs neg Dm md w := by
    intro X hX k rs Ds neg rk ok nr na T Y e run
    obtain ⟨r, rr, rfl | ⟨er, rfl⟩ | ⟨T', Y', er, rfl, -, dY, oY, Dm, mDm, sY⟩⟩ := del_update hX rk ok nr na hmd hm
    · rw [run] at rr; cases rr
    · rw [run] at rr; cases rr
    · rw [run] at rr
      obtain ⟨-, rfl, -⟩ := tuple3_inj (Except.ok.inj rr)
      exact ⟨Y', rfl, dY, oY, Dm, mDm, sY⟩
  obtain ⟨YL, rfl, dL, oL, Dm₁, mDm₁, sL⟩ := side hXL rk₁ ok₁ nr₁ na₁ run₁
  obtain ⟨YR, rfl, dR, -, Dm₂, mDm₂, sR⟩ := side hXR rk₂ ok₂ nr₂ na₂ run₂
  refine ⟨YL, YR, rfl, rfl, dL, dR, fun q hq => ?_⟩
  obtain ⟨w, hw⟩ := pt_map q (oL q hq)
  rw [hw] at hq ⊢
  exact (sR w).mpr (del_mono (fun x => (level t n).ef.den_none x) maps hmd ok₁ ok₂ nr₂ keys mDm₁ mDm₂ ((sL w).mp hq))

end

end Elixir.STTDescrProofsTest.Nest
