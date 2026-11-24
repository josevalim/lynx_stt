namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! The maps of `map_update_box/6`, described from the maps of a type rather than its lines. -/

/-- The maps hold atom keys outside every finite set. -/
def AtomsInf (M : MW V → Prop) : Prop := ∀ F : List String, ∃ u, M u ∧ ∃ s, s ∉ F ∧ u (.atom s) ≠ none

/-- The maps hold keys of a kind: atoms outside every finite set, or keys of another kind. -/
def KindHeld (M : MW V → Prop) (d : String) : Prop :=
  (d = "atom" → AtomsInf M) ∧ (d ≠ "atom" → ∃ u, M u ∧ HasKind u d)

/-- A value the maps hold at a key of a kind other than atoms. -/
def KindVal (M : MW V → Prop) (d : String) (x : V) : Prop := ∃ u k j, M u ∧ domKind k = d ∧ u (.dom k j) = some x

/-- The values an update puts at the keys of a kind. -/
def NewDomS (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (md : String) (d : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ KindHeld M d)

/-- Kinds whose update field is not empty. -/
def DomNES (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (nopt : Bool) (md : String) (d : String) : Prop :=
  md = "keep" ∨ ((md = "force" ∨ KindHeld M d) ∧ (nopt = Bool.true ∨ ∃ x, den nt x))

/-- Atom keys of the key type whose update field is not empty. -/
def KeyNES (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (s : String) : Prop :=
  s ∉ S ∧ ∃ o, NewF den nt nopt md (Old M (.atom s)) o

/-- Some updated key or kind of the key type has old values or new values as `A` asks. -/
def UpdHasS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (A : Prop → Prop → Prop) : Prop :=
  (∃ s, KeyNES den M S nt nopt md s ∧ A (∃ x, Old M (.atom s) (some x))
      (∃ x, NewF den nt nopt md (Old M (.atom s)) (some x))) ∨
    ∃ d ∈ Ds, d ≠ "atom" ∧ DomNES den M nt nopt md d ∧ A (∃ x, KindVal M d x) (∃ x, NewDomS den M nt md d x)

/-- Rejecting with a single key of the key type held and no other kind: that key is replaced. -/
def RS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (s : String) : Prop :=
  md = "reject" ∧ (∀ d ∈ Ds, d ≠ "atom" → ¬DomNES den M nt nopt md d) ∧ KeyNES den M S nt nopt md s ∧
    ∀ s', KeyNES den M S nt nopt md s' → s' = s

/-- The box: every key holds an old value, or, in the key type, a new one. -/
def SynS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (w : MW V) : Prop :=
  (∀ s, (s ∈ S ∧ Old M (.atom s) (w (.atom s))) ∨ (s ∉ S ∧ ((¬RS den M S nt nopt md Ds s ∧ Old M (.atom s) (w (.atom s))) ∨
      NewF den nt nopt md (Old M (.atom s)) (w (.atom s))))) ∧
    ∀ k i, w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧
      (KindVal M (domKind k) x ∨ (domKind k ∈ Ds ∧ NewDomS den M nt md (domKind k) x))

/-- No key of the key type holds a new value. -/
def UnsetS (den : Term → V → Prop) (S : List String) (Ds : List String) (nt : Term) (w : MW V) : Prop :=
  (∀ s, s ∉ S → OutV den nt (w (.atom s))) ∧ ∀ k i, domKind k ∈ Ds → OutV den nt (w (.dom k i))

/-- Whether the box is among the updated maps. -/
def PresentS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) : Prop :=
  (md = "keep" → ¬UpdHasS den M S nt nopt md Ds (fun o n => o ∧ ¬n) ∧ ¬M wNone) ∧
    (md ≠ "keep" → UpdHasS den M S nt nopt md Ds (fun _ n => n))

/-- Keeping absent keys, with no key of the key type holding old or new values. -/
def SameS (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) : Prop :=
  md = "keep" ∧ ¬UpdHasS den M S nt nopt md Ds (fun o n => o ∨ n)

/-- The maps of `map_update_box/6`, from the maps of a type, the atoms outside the key type, and the kinds updated. -/
def BoxSem (den : Term → V → Prop) (M : MW V → Prop) (S : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (w : MW V) : Prop :=
  UpdHasS den M S nt nopt md Ds (fun _ _ => True) ∧ (SameS den M S nt nopt md Ds → M w) ∧
    (¬SameS den M S nt nopt md Ds → SynS den M S nt nopt md Ds w ∧
      (PresentS den M S nt nopt md Ds →
        ((nopt = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds) → ¬UnsetS den S Ds nt w) ∧
        (¬(nopt = Bool.false ∧ md ≠ "keep" ∧ ¬∀ d ∈ domainKinds, d ∈ Ds) → w ≠ wNone)))

/-- The new field of a key some map lacks, holding a value. -/
theorem newF_some {nt : Term} {nopt : Bool} {md : String} {Old : Option V → Prop} (h0 : Old none) (x : V) :
    NewF den nt nopt md Old (some x) ↔ den nt x ∧ (md = "force" ∨ ∃ y, Old (some y)) := by
  unfold NewF
  constructor
  · rintro (⟨ho, (⟨h, -⟩ | ⟨z, h, hz⟩)⟩ | ⟨-, (⟨rfl, (⟨h, -⟩ | ⟨z, h, hz⟩)⟩ | ⟨-, h⟩)⟩)
    · cases h
    · cases h; exact ⟨hz, Or.inr ho⟩
    · cases h
    · cases h; exact ⟨hz, Or.inl rfl⟩
    · cases h
  · rintro ⟨hx, rfl | ho⟩
    · exact Or.inr ⟨h0, Or.inl ⟨rfl, Or.inr ⟨x, rfl, hx⟩⟩⟩
    · exact Or.inl ⟨ho, Or.inr ⟨x, rfl, hx⟩⟩

/-- Whether the new field of a key some map lacks is not empty. -/
theorem newF_ex {nt : Term} {nopt : Bool} {md : String} {Old : Option V → Prop} (h0 : Old none) :
    (∃ o, NewF den nt nopt md Old o) ↔
      md = "keep" ∨ ((md = "force" ∨ ∃ y, Old (some y)) ∧ (nopt = Bool.true ∨ ∃ x, den nt x)) := by
  unfold NewF
  constructor
  · rintro ⟨o, (⟨ho, (⟨-, hn⟩ | ⟨z, -, hz⟩)⟩ | ⟨-, (⟨rfl, (⟨-, hn⟩ | ⟨z, -, hz⟩)⟩ | ⟨hk, -⟩)⟩)⟩
    · exact Or.inr ⟨Or.inr ho, Or.inl hn⟩
    · exact Or.inr ⟨Or.inr ho, Or.inr ⟨z, hz⟩⟩
    · exact Or.inr ⟨Or.inl rfl, Or.inl hn⟩
    · exact Or.inr ⟨Or.inl rfl, Or.inr ⟨z, hz⟩⟩
    · exact Or.inl hk
  · rintro (hk | ⟨hf, hn⟩)
    · exact ⟨none, Or.inr ⟨h0, Or.inr ⟨hk, rfl⟩⟩⟩
    · have val : ∃ o, (o = none ∧ nopt = Bool.true) ∨ ∃ x, o = some x ∧ den nt x := by
        rcases hn with hn | ⟨x, hx⟩
        · exact ⟨none, Or.inl ⟨rfl, hn⟩⟩
        · exact ⟨some x, Or.inr ⟨x, rfl, hx⟩⟩
      obtain ⟨o, ho⟩ := val
      rcases hf with rfl | hy
      · exact ⟨o, Or.inr ⟨h0, Or.inl ⟨rfl, ho⟩⟩⟩
      · exact ⟨o, Or.inl ⟨hy, ho⟩⟩

section lines
variable (ef : EF nd E V den tl K) {lines : List Term} (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
include ef hl

/-- Atoms no line names hold absence or what the tags of the lines allow at atoms. -/
theorem unnamed_old (hne : lines ≠ []) {NK : List String} (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK)
    {s : String} (ns : s ∉ NK) (o : Option V) :
    Old (fun u => ∃ L ∈ lines, InMLine den L u) (.atom s) o ↔
      o = none ∨ ∃ x, o = some x ∧ ∃ L ∈ lines, LineTag den L "atom" x := by
  have notIn : ∀ L ∈ lines, ¬LineNames L s := fun L mL h => ns (lnNK L mL s h)
  constructor
  · rintro ⟨u, ⟨L, mL, hu⟩, rfl⟩
    cases ho : u (.atom s) with
    | none => exact Or.inl rfl
    | some x =>
      refine Or.inr ⟨x, rfl, L, mL, ?_⟩
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := (hl L mL).1
      have sl : s ∉ keyStrs l := fun m => notIn _ mL ⟨tag, l, negs, rfl, Or.inl m⟩
      have := (inMLine_iff.mp hu).1.atoms s
      simp only [FSem, lookup_fresh' sl, ho] at this
      exact ⟨tag, l, negs, rfl, (tagSem_some ef g "atom" x).mp this⟩
  · intro h
    obtain ⟨L, mL, hx⟩ : ∃ L ∈ lines, (o = none ∨ ∃ x, o = some x ∧ LineTag den L "atom" x) := by
      rcases h with rfl | ⟨x, rfl, L, mL, hL⟩
      · obtain ⟨L, mL⟩ := List.exists_mem_of_ne_nil lines hne
        exact ⟨L, mL, Or.inl rfl⟩
      · exact ⟨L, mL, Or.inr ⟨x, rfl, hL⟩⟩
    obtain ⟨⟨tag, l, negs, rfl, g, -, lits⟩, w₀, h₀⟩ := hl L mL
    have sl : s ∉ keyStrs l := fun m => notIn _ mL ⟨tag, l, negs, rfl, Or.inl m⟩
    have sn : s ∉ negStrs negs := fun m => by
      obtain ⟨N, mN, ms⟩ := List.mem_flatMap.mp m
      obtain ⟨k, t, l', rfl, -, -⟩ := lits N mN
      simp only [litStrs, domFields_fieldsTerm] at ms
      exact notIn _ mL ⟨tag, l, negs, rfl, Or.inr ⟨_, mN, k, t, l', rfl, ms⟩⟩
    have ho : TagSem den tag "atom" o := by
      rcases hx with rfl | ⟨x, rfl, tag', l', negs', e, hx⟩
      · exact tagSem_none tag "atom"
      · obtain ⟨rfl, -, -⟩ := tuple3_inj e
        exact (tagSem_some ef g "atom" x).mpr hx
    obtain ⟨u, hu, e⟩ := line_at h₀ lits sl sn ho
    exact ⟨u, ⟨_, mL, hu⟩, e⟩

/-- Keys of kinds other than atoms hold what the tags of the lines allow at their kind. -/
theorem dom_val (k : Fin 11) (x : V) :
    (∃ L ∈ lines, LineTag den L (domKind k) x) ↔ KindVal (fun u => ∃ L ∈ lines, InMLine den L u) (domKind k) x := by
  constructor
  · rintro ⟨L, mL, hx⟩
    obtain ⟨u, hu, κ, hκ, e⟩ := tag_witness ef (hl L mL).1 (hl L mL).2 (domKind_mem k) hx []
    rcases hκ with ⟨h, -⟩ | ⟨k', j, ek, rfl⟩
    · exact absurd h (domKind_ne_atom k)
    · exact ⟨u, k', j, ⟨L, mL, hu⟩, ek.symm, e⟩
  · rintro ⟨u, k', j, ⟨L, mL, hu⟩, ek, e⟩
    obtain rfl : k' = k := domKind_inj ek
    obtain ⟨tag, l, negs, rfl, g, -, -⟩ := (hl L mL).1
    have := (inMLine_iff.mp hu).1.doms k' j
    rw [e] at this
    exact ⟨_, mL, tag, l, negs, rfl, (tagSem_some ef g _ x).mp this⟩

/-- The kinds other than atoms whose keys the maps hold are those some line's tag allows. -/
theorem kind_held_ne {d : String} (hd : d ∈ domainKinds) (da : d ≠ "atom") :
    KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y := by
  obtain ⟨k, rfl⟩ := domKind_of hd da
  constructor
  · intro h
    obtain ⟨u, hu, k', i, ek, hi⟩ := h.2 da
    cases e : u (.dom k' i) with
    | none => exact absurd e hi
    | some x =>
      obtain rfl : k' = k := domKind_inj ek
      obtain ⟨L, mL, hL⟩ := (dom_val ef hl k' x).mpr ⟨u, k', i, hu, rfl, e⟩
      exact ⟨L, mL, x, hL⟩
  · rintro ⟨L, mL, y, hy⟩
    obtain ⟨u, k', j, hu, ek, e⟩ := (dom_val ef hl k y).mp ⟨L, mL, hy⟩
    exact ⟨fun h => absurd h da, fun _ => ⟨u, hu, k', j, ek, by rw [e]; simp⟩⟩

/-- The maps hold atom keys outside every finite set when some line's tag allows atoms. -/
theorem atoms_inf (hne : lines ≠ []) {NK : List String} (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) :
    AtomsInf (fun u => ∃ L ∈ lines, InMLine den L u) ↔ ∃ L ∈ lines, ∃ x, LineTag den L "atom" x := by
  constructor
  · intro h
    obtain ⟨u, hu, s, ns, hs⟩ := h NK
    cases e : u (.atom s) with
    | none => exact absurd e hs
    | some x =>
      rcases (unnamed_old ef hl hne lnNK ns (some x)).mp ⟨u, hu, e⟩ with h | ⟨y, h, L, mL, hy⟩
      · cases h
      · obtain rfl : x = y := Option.some.inj h
        exact ⟨L, mL, x, hy⟩
  · rintro ⟨L, mL, x, hx⟩ F
    obtain ⟨s, hs⟩ := fresh_str (F ++ NK)
    obtain ⟨u, hu, e⟩ := (unnamed_old ef hl hne lnNK (fun m => hs (List.mem_append_right _ m)) (some x)).mpr
      (Or.inr ⟨x, rfl, L, mL, hx⟩)
    exact ⟨u, hu, s, fun m => hs (List.mem_append_left _ m), by rw [e]; simp⟩

/-- The kinds whose keys the maps hold are those some line's tag allows. -/
theorem kind_held (hne : lines ≠ []) {NK : List String} (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK)
    {d : String} (hd : d ∈ domainKinds) :
    KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y := by
  by_cases da : d = "atom"
  · subst da
    rw [← atoms_inf ef hl hne lnNK]
    exact ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun h' => absurd rfl h'⟩⟩
  · obtain ⟨k, rfl⟩ := domKind_of hd da
    constructor
    · intro h
      obtain ⟨u, hu, k', i, ek, hi⟩ := h.2 da
      cases e : u (.dom k' i) with
      | none => exact absurd e hi
      | some x =>
        obtain rfl : k' = k := domKind_inj ek
        obtain ⟨L, mL, hL⟩ := (dom_val ef hl k' x).mpr ⟨u, k', i, hu, rfl, e⟩
        exact ⟨L, mL, x, hL⟩
    · rintro ⟨L, mL, y, hy⟩
      obtain ⟨u, k', j, hu, ek, e⟩ := (dom_val ef hl k y).mp ⟨L, mL, hy⟩
      exact ⟨fun h => absurd h da, fun _ => ⟨u, hu, k', j, ek, by rw [e]; simp⟩⟩

/-- `BoxRes` on the lines of a type is `BoxSem` on its maps. -/
theorem box_sem_iff (hne : lines ≠ []) {nt : Term} {nopt : Bool} {md : String}
    (S ks AK NK Ds : List String) (hD : ∀ d ∈ Ds, d ∈ domainKinds) (hks : ∀ s ∈ ks, s ∉ S)
    (hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ S) (akNK : ∀ s ∈ AK, s ∈ NK)
    (lnNK : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) (orNK : ∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ S ∨ s ∈ ks)
    (hAt : "atom" ∈ Ds ∨ (md = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x))
    (hlen : Ds.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Ds)
    {R : String → Prop} (hR : ∀ s, R s ↔ md = "reject" ∧ (∀ d ∈ Ds, ¬DomNE den lines nt nopt md d) ∧
      KeyNE den lines ks NK nt nopt md s ∧ ∀ s', KeyNE den lines ks NK nt nopt md s' → s' = s) (w : MW V) :
    BoxRes den lines ks AK NK R nt nopt md Ds w ↔
      BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) S nt nopt md Ds w := by
  classical
  let M : MW V → Prop := fun u => ∃ L ∈ lines, InMLine den L u
  have named : ∀ s o, (∃ L ∈ lines, LongM den L s o) ↔ Old M (.atom s) o := fun s o =>
    ⟨fun ⟨L, mL, u, hu, e⟩ => ⟨u, ⟨L, mL, hu⟩, e⟩, fun ⟨u, ⟨L, mL, hu⟩, e⟩ => ⟨L, mL, u, hu, e⟩⟩
  have eOld : ∀ s, (fun o => ∃ L ∈ lines, LongM den L s o) = Old M (.atom s) := fun s =>
    funext fun o => propext (named s o)
  have eSome : ∀ s, (∃ x, ∃ L ∈ lines, LongM den L s (some x)) = ∃ x, Old M (.atom s) (some x) := fun s =>
    propext (exists_congr fun x => named s (some x))
  have ksS : ∀ s ∈ NK, (s ∈ ks ↔ s ∉ S) := fun s ms => ⟨hks s, fun nS => by
    rcases orNK s ms with h | ⟨L, mL, hL⟩
    · exact ((hAK s).mp h).resolve_right nS
    · exact (lnKS L mL s hL).resolve_left nS⟩
  have SNK : ∀ s ∈ S, s ∈ NK := fun s m => akNK s ((hAK s).mpr (Or.inr m))
  have kh : ∀ d ∈ domainKinds, KindHeld M d ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y :=
    fun d hd => kind_held ef hl hne lnNK hd
  have newDom : ∀ d ∈ domainKinds, ∀ x, NewDom den lines nt md d x ↔ NewDomS den M nt md d x := by
    intro d hd x; simp only [NewDom, NewDomS, kh d hd]
  have domNE : ∀ d ∈ domainKinds, DomNE den lines nt nopt md d ↔ DomNES den M nt nopt md d := by
    intro d hd; simp only [DomNE, DomNES, kh d hd]
  have atomK : "atom" ∈ domainKinds := by simp [domainKinds]
  -- Atoms no line names.
  have un0 : ∀ s, s ∉ NK → Old M (.atom s) none := fun s ns =>
    (unnamed_old ef hl hne lnNK ns none).mpr (Or.inl rfl)
  have unNE : ∀ s, s ∉ NK → ((∃ x, Old M (.atom s) (some x)) ↔ ∃ L ∈ lines, ∃ x, LineTag den L "atom" x) := by
    intro s ns
    constructor
    · rintro ⟨x, h⟩
      rcases (unnamed_old ef hl hne lnNK ns (some x)).mp h with h | ⟨y, h, L, mL, hy⟩
      · cases h
      · exact ⟨L, mL, y, hy⟩
    · rintro ⟨L, mL, x, hx⟩
      exact ⟨x, (unnamed_old ef hl hne lnNK ns (some x)).mpr (Or.inr ⟨x, rfl, L, mL, hx⟩)⟩
  have unNew : ∀ s, s ∉ NK → ∀ x, NewF den nt nopt md (Old M (.atom s)) (some x) ↔ NewDom den lines nt md "atom" x := by
    intro s ns x
    rw [newF_some (un0 s ns), NewDom, unNE s ns]
  have unNewE : ∀ s, s ∉ NK → (∃ x, NewF den nt nopt md (Old M (.atom s)) (some x)) = ∃ x, NewDom den lines nt md "atom" x :=
    fun s ns => propext (exists_congr (unNew s ns))
  have unKey : ∀ s, s ∉ NK → (KeyNES den M S nt nopt md s ↔ "atom" ∈ Ds ∧ DomNE den lines nt nopt md "atom") := by
    intro s ns
    have nS : s ∉ S := fun m => ns (SNK s m)
    rw [KeyNES, newF_ex (un0 s ns), unNE s ns]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨?_, h⟩
      rcases hAt with h' | ⟨hr, nt'⟩
      · exact h'
      · exfalso
        rcases h with h | ⟨h | ⟨L, mL, y, hy⟩, -⟩
        · rw [hr] at h; simp at h
        · rw [hr] at h; simp at h
        · exact nt' L mL y hy
    · rintro ⟨-, h⟩
      exact ⟨nS, h⟩
  have nameKey : ∀ s ∈ NK, (KeyNE den lines ks NK nt nopt md s ↔ KeyNES den M S nt nopt md s) := by
    intro s ms
    rw [KeyNE, KeyNES, eOld s, ksS s ms]
    simp [ms]
  have two : ∃ s₁ s₂, s₁ ∉ NK ∧ s₂ ∉ NK ∧ s₁ ≠ s₂ := by
    obtain ⟨s₁, h₁⟩ := fresh_str NK
    obtain ⟨s₂, h₂⟩ := fresh_str (s₁ :: NK)
    exact ⟨s₁, s₂, h₁, fun m => h₂ (List.mem_cons_of_mem _ m), fun e => h₂ (e ▸ List.mem_cons_self)⟩
  have swapE : (∃ x, ∃ L ∈ lines, LineTag den L "atom" x) = (∃ L ∈ lines, ∃ x, LineTag den L "atom" x) :=
    propext ⟨fun ⟨x, L, mL, h⟩ => ⟨L, mL, x, h⟩, fun ⟨L, mL, x, h⟩ => ⟨x, L, mL, h⟩⟩
  -- The updated keys and kinds.
  have updHas : ∀ A, UpdHas den lines ks NK nt nopt md Ds A ↔ UpdHasS den M S nt nopt md Ds A := by
    intro A
    constructor
    · rintro (⟨s, hk, h⟩ | ⟨d, md', hne', h⟩)
      · rw [eSome s, eOld s] at h
        exact Or.inl ⟨s, (nameKey s hk.1).mp hk, h⟩
      · by_cases da : d = "atom"
        · subst da
          obtain ⟨s, ns⟩ := fresh_str NK
          rw [swapE, ← propext (unNE s ns), ← unNewE s ns] at h
          exact Or.inl ⟨s, (unKey s ns).mpr ⟨md', hne'⟩, h⟩
        · obtain ⟨k, rfl⟩ := domKind_of (hD _ md') da
          rw [propext (exists_congr (dom_val ef hl k)), propext (exists_congr (newDom _ (domKind_mem k)))] at h
          exact Or.inr ⟨_, md', da, (domNE _ (domKind_mem k)).mp hne', h⟩
    · rintro (⟨s, hk, h⟩ | ⟨d, md', da, hne', h⟩)
      · by_cases ms : s ∈ NK
        · rw [← eSome s, ← eOld s] at h
          exact Or.inl ⟨s, (nameKey s ms).mpr hk, h⟩
        · obtain ⟨ha, hd⟩ := (unKey s ms).mp hk
          rw [propext (unNE s ms), unNewE s ms, ← swapE] at h
          exact Or.inr ⟨"atom", ha, hd, h⟩
      · obtain ⟨k, rfl⟩ := domKind_of (hD _ md') da
        rw [← propext (exists_congr (dom_val ef hl k)), ← propext (exists_congr (newDom _ (domKind_mem k)))] at h
        exact Or.inr ⟨_, md', (domNE _ (domKind_mem k)).mpr hne', h⟩
  -- Replacing.
  have noA : ∀ {s}, RS den M S nt nopt md Ds s → ¬("atom" ∈ Ds ∧ DomNE den lines nt nopt md "atom") := by
    rintro s ⟨-, -, -, uq⟩ h
    obtain ⟨s₁, s₂, n₁, n₂, ne⟩ := two
    exact ne ((uq s₁ ((unKey s₁ n₁).mpr h)).trans (uq s₂ ((unKey s₂ n₂).mpr h)).symm)
  have rIff : ∀ s, R s ↔ RS den M S nt nopt md Ds s := by
    intro s
    rw [hR]
    constructor
    · rintro ⟨hr, nd, hk, uq⟩
      refine ⟨hr, fun d md' _ h => nd d md' ((domNE d (hD d md')).mpr h), (nameKey s hk.1).mp hk, fun s' hk' => ?_⟩
      by_cases ms' : s' ∈ NK
      · exact uq s' ((nameKey s' ms').mpr hk')
      · obtain ⟨ha, hd⟩ := (unKey s' ms').mp hk'
        exact absurd hd (nd _ ha)
    · intro h
      have nA := noA h
      obtain ⟨hr, nd, hk, uq⟩ := h
      have ms : s ∈ NK := Classical.byContradiction fun ns => nA ((unKey s ns).mp hk)
      refine ⟨hr, fun d md' hd => ?_, (nameKey s ms).mpr hk, fun s' hk' => uq s' ((nameKey s' hk'.1).mp hk')⟩
      by_cases da : d = "atom"
      · subst da; exact nA ⟨md', hd⟩
      · exact nd d md' da ((domNE d (hD d md')).mp hd)
  have unR : ∀ s, s ∉ NK → ¬RS den M S nt nopt md Ds s := fun s ns h =>
    noA h ((unKey s ns).mp h.2.2.1)
  have atomIn : ∀ x, NewDom den lines nt md "atom" x → "atom" ∈ Ds := fun x hx => by
    rcases hAt with h | ⟨hr, nt'⟩
    · exact h
    · exfalso
      rcases hx.2 with h | ⟨L, mL, y, hy⟩
      · rw [hr] at h; simp at h
      · exact nt' L mL y hy
  -- The box.
  have syn : BoxSynG den lines ks NK R nt nopt md Ds w ↔ SynS den M S nt nopt md Ds w := by
    constructor
    · rintro ⟨hn, hu, hd⟩
      refine ⟨fun s => ?_, fun k i => ?_⟩
      · by_cases ms : s ∈ NK
        · by_cases sS : s ∈ S
          · refine Or.inl ⟨sS, ?_⟩
            rcases hn s ms with ⟨-, h⟩ | ⟨sk, -⟩
            · exact (named s _).mp h
            · exact absurd sS (hks s sk)
          · refine Or.inr ⟨sS, ?_⟩
            rcases hn s ms with ⟨nr, h⟩ | ⟨-, h⟩
            · exact Or.inl ⟨fun h' => nr ((rIff s).mpr h'), (named s _).mp h⟩
            · rw [eOld s] at h; exact Or.inr h
        · have sS : s ∉ S := fun m => ms (SNK s m)
          refine Or.inr ⟨sS, ?_⟩
          rcases hu s ms with h | ⟨x, h, hx | ⟨-, hx⟩⟩
          · exact Or.inl ⟨unR s ms, by rw [h]; exact un0 s ms⟩
          · exact Or.inl ⟨unR s ms, (unnamed_old ef hl hne lnNK ms _).mpr (Or.inr ⟨x, h, hx⟩)⟩
          · rw [h]; exact Or.inr ((unNew s ms x).mpr hx)
      · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, h, Or.inl ((dom_val ef hl k x).mp hx)⟩
        · exact Or.inr ⟨x, h, Or.inr ⟨dk, (newDom _ (domKind_mem k) x).mp hx⟩⟩
    · rintro ⟨ha, hd⟩
      refine ⟨fun s ms => ?_, fun s ms => ?_, fun k i => ?_⟩
      · rcases ha s with ⟨sS, h⟩ | ⟨sS, ⟨nr, h⟩ | h⟩
        · refine Or.inl ⟨fun hr => ?_, (named s _).mpr h⟩
          obtain ⟨-, -, hk, -⟩ := (hR s).mp hr
          exact hks s hk.2.1 sS
        · exact Or.inl ⟨fun hr => nr ((rIff s).mp hr), (named s _).mpr h⟩
        · refine Or.inr ⟨(ksS s ms).mpr sS, ?_⟩
          rw [eOld s]; exact h
      · rcases ha s with ⟨sS, -⟩ | ⟨-, ⟨-, h⟩ | h⟩
        · exact absurd (SNK s sS) ms
        · rcases (unnamed_old ef hl hne lnNK ms _).mp h with h' | ⟨x, h', hx⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, h', Or.inl hx⟩
        · cases e : w (.atom s) with
          | none => exact Or.inl rfl
          | some x =>
            rw [e] at h
            have hx := (unNew s ms x).mp h
            exact Or.inr ⟨x, rfl, Or.inr ⟨atomIn x hx, hx⟩⟩
      · rcases hd k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, h, Or.inl ((dom_val ef hl k x).mpr hx)⟩
        · exact Or.inr ⟨x, h, Or.inr ⟨dk, (newDom _ (domKind_mem k) x).mpr hx⟩⟩
  have unset : SynS den M S nt nopt md Ds w → (UnsetSemD den ks AK Ds nt w ↔ UnsetS den S Ds nt w) := by
    intro hs
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun s sS => ?_, h2⟩
      by_cases sk : s ∈ ks
      · exact h1 s (Or.inl sk)
      have sAK : s ∉ AK := fun m => ((hAK s).mp m).elim sk sS
      by_cases ha : "atom" ∈ Ds
      · exact h1 s (Or.inr ⟨ha, sk, sAK⟩)
      have ms : s ∉ NK := fun ms => sk ((ksS s ms).mpr sS)
      obtain ⟨hr, nt'⟩ := hAt.resolve_left ha
      rcases hs.1 s with ⟨sS', -⟩ | ⟨-, ⟨-, h⟩ | h⟩
      · exact absurd sS' sS
      · rcases (unnamed_old ef hl hne lnNK ms _).mp h with h' | ⟨x, -, L, mL, hx⟩
        · exact Or.inl h'
        · exact absurd hx (nt' L mL x)
      · cases e : w (.atom s) with
        | none => exact Or.inl rfl
        | some x =>
          rw [e] at h
          exact absurd (atomIn x ((unNew s ms x).mp h)) ha
    · rintro ⟨h1, h2⟩
      refine ⟨fun s hs' => ?_, h2⟩
      rcases hs' with sk | ⟨-, -, sAK⟩
      · exact h1 s (hks s sk)
      · exact h1 s fun m => sAK ((hAK s).mpr (Or.inr m))
  have eM : (∀ L ∈ lines, ¬InMLine den L wNone) ↔ ¬M wNone :=
    ⟨fun h ⟨L, mL, hL⟩ => h L mL hL, fun h L mL hL => h ⟨L, mL, hL⟩⟩
  have present : BoxPresent den lines ks NK nt nopt md Ds ↔ PresentS den M S nt nopt md Ds := by
    unfold BoxPresent PresentS
    rw [updHas, updHas, eM]
  have same : BoxSame den lines ks NK nt nopt md Ds ↔ SameS den M S nt nopt md Ds := by
    unfold BoxSame SameS
    rw [updHas]
  have pre : ((∃ s, KeyNE den lines ks NK nt nopt md s) ∨ ∃ d ∈ Ds, DomNE den lines nt nopt md d) ↔
      UpdHasS den M S nt nopt md Ds (fun _ _ => True) := by
    rw [← updHas]
    simp [UpdHas]
  have hlen' : (Ds.length ≠ 12) ↔ ¬∀ d ∈ domainKinds, d ∈ Ds := not_congr hlen
  unfold BoxRes BoxSem
  rw [pre, same, present, hlen']
  constructor
  · rintro ⟨hp, hs, hn⟩
    refine ⟨hp, hs, fun ns => ?_⟩
    obtain ⟨hb, hq⟩ := hn ns
    have hb' := syn.mp hb
    exact ⟨hb', fun hpr => ⟨fun hc hu => (hq hpr).1 hc ((unset hb').mpr hu), (hq hpr).2⟩⟩
  · rintro ⟨hp, hs, hn⟩
    refine ⟨hp, hs, fun ns => ?_⟩
    obtain ⟨hb, hq⟩ := hn ns
    exact ⟨syn.mpr hb, fun hpr => ⟨fun hc hu => (hq hpr).1 hc ((unset hb).mp hu), (hq hpr).2⟩⟩

end lines

end

end Elixir.STTDescrProofsTest.Nest
