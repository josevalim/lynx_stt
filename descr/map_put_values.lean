namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The values of the maps `map_put/3` gives: at the selected keys, a value of the type or one an original map holds
at a selected key; at the other keys, what the original maps hold. Every original map with a selected key set to a
value of the type is one of them. -/

section
variable {V : Type} {den : Term → V → Prop}

/-- A map with a key set to a value. -/
def updK (κ : MKey) (x : V) (u : MW V) : MW V := fun κ' => if κ' = κ then some x else u κ'

theorem updK_same (κ : MKey) (x : V) (u : MW V) : updK κ x u κ = some x := by simp [updK]

theorem updK_other {κ κ' : MKey} (h : κ' ≠ κ) (x : V) (u : MW V) : updK κ x u κ' = u κ' := by simp [updK, h]

theorem splitKey_dom {rs ds : List Term} {neg : Term} {k : Fin 11} {i j : Nat} :
    SplitKey rs neg ds (.dom k i) ↔ SplitKey rs neg ds (.dom k j) := by
  simp [SplitKey]

/-- The values of the maps of a put at the selected keys are values of the type, or values of the original maps at
selected keys. -/
theorem put_upper {M : MW V → Prop} {rs ds : List Term} {neg v : Term} {w : MW V}
    (h : PutSem den M rs neg ds v w) {κ : MKey} (hκ : SplitKey rs neg ds κ) {x : V} (hw : w κ = some x) :
    den v x ∨ ∃ u κ', M u ∧ SplitKey rs neg ds κ' ∧ u κ' = some x := by
  -- The box: each key holds what some map holds at a key of its kind, or a value of the type.
  have box : ∀ {S : List String} {P : String → Prop}, BoxD den M S P v w →
      den v x ∨ ∃ u κ', M u ∧ SplitKey rs neg ds κ' ∧ u κ' = some x := by
    intro S P ⟨ba, bd⟩
    cases κ with
    | atom s =>
      rcases ba s with ⟨u, hu, e⟩ | ⟨-, y, e, hy⟩
      · exact Or.inr ⟨u, .atom s, hu, hκ, e.trans hw⟩
      · rw [hw] at e; cases e; exact Or.inl hy
    | dom k i =>
      rcases bd k i with e | ⟨y, e, (⟨u, j, hu, uj⟩ | ⟨-, hy⟩)⟩
      · rw [hw] at e; cases e
      · rw [hw] at e; cases e; exact Or.inr ⟨u, .dom k j, hu, splitKey_dom.mp hκ, uj⟩
      · rw [hw] at e; cases e; exact Or.inl hy
  -- The widened domains: on the key, some map agrees.
  have domc : ∀ {Ds : List String}, DomC den M Ds v w →
      den v x ∨ ∃ u κ', M u ∧ SplitKey rs neg ds κ' ∧ u κ' = some x := by
    intro Ds ⟨_, all⟩
    obtain ⟨u, hu, a₁, a₂, a₃⟩ := all [κ]
    cases κ with
    | atom s => exact Or.inr ⟨u, .atom s, hu, hκ, (a₁ s).symm.trans hw⟩
    | dom k i =>
      by_cases dk : domKind k ∈ Ds
      · rcases a₃ k i (by simp) dk with e | e | ⟨y, e, hy⟩
        · rw [hw] at e; cases e
        · exact Or.inr ⟨u, .dom k i, hu, hκ, e.symm.trans hw⟩
        · rw [hw] at e; cases e; exact Or.inl hy
      · exact Or.inr ⟨u, .dom k i, hu, hκ, (a₂ k i dk).symm.trans hw⟩
  rcases h with ⟨-, (⟨a, -, ⟨y, wa, hy⟩, o, hu⟩ | ⟨-, -, dc⟩)⟩ | ⟨N, -, (⟨-, -, bx, -⟩ | ⟨-, (⟨bx, -⟩ | ⟨-, -, dc⟩)⟩)⟩
  · by_cases e : κ = .atom a
    · subst e; rw [hw] at wa; cases wa; exact Or.inl hy
    · exact Or.inr ⟨_, κ, hu, hκ, by simp [setK, e, hw]⟩
  · exact domc dc
  · exact box bx
  · exact box bx
  · exact domc dc

/-- At an atom outside the selected keys, the maps of a put hold what some original map holds. -/
theorem put_other_atom {M : MW V → Prop} {rs ds : List Term} {neg v : Term} {w : MW V}
    (h : PutSem den M rs neg ds v w) {s : String} (hs : ¬SplitKey rs neg ds (.atom s)) :
    ∃ u, M u ∧ u (.atom s) = w (.atom s) := by
  rcases h with ⟨-, (⟨a, ha, -, o, hu⟩ | ⟨-, -, -, all⟩)⟩ | ⟨N, rfl, (⟨-, -, ⟨ba, -⟩, -⟩ | ⟨-, (⟨⟨ba, -⟩, -⟩ | ⟨-, -, -, all⟩)⟩)⟩
  · have : s ≠ a := fun e => hs (by subst e; exact Or.inl ha)
    exact ⟨_, hu, by simp [setK, this]⟩
  · obtain ⟨u, hu, a₁, -⟩ := all []
    exact ⟨u, hu, (a₁ s).symm⟩
  · rcases ba s with ⟨u, hu, e⟩ | ⟨ns, -⟩
    · exact ⟨u, hu, e⟩
    · exact absurd (Or.inr ⟨N, rfl, by simpa [setStrs_mem] using ns⟩) hs
  · rcases ba s with ⟨u, hu, e⟩ | ⟨ns, -⟩
    · exact ⟨u, hu, e⟩
    · exact absurd (Or.inr ⟨N, rfl, by simpa [setStrs_mem] using ns⟩) hs
  · obtain ⟨u, hu, a₁, -⟩ := all []
    exact ⟨u, hu, (a₁ s).symm⟩

/-- At a domain key of a kind outside the selected keys, the values of the maps of a put are values some original map
holds at a key of that kind. -/
theorem put_other_dom {M : MW V → Prop} {rs ds : List Term} {neg v : Term} {w : MW V}
    (h : PutSem den M rs neg ds v w) {k : Fin 11} (hk : .atom (domKind k) ∉ ds) {i : Nat} {x : V}
    (hw : w (.dom k i) = some x) : ∃ u j, M u ∧ u (.dom k j) = some x := by
  have box : ∀ {S : List String} {P : String → Prop}, (P (domKind k) → .atom (domKind k) ∈ ds) →
      BoxD den M S P v w → ∃ u j, M u ∧ u (.dom k j) = some x := by
    intro S P hP ⟨_, bd⟩
    rcases bd k i with e | ⟨y, e, (⟨u, j, hu, uj⟩ | ⟨p, -⟩)⟩
    · rw [hw] at e; cases e
    · rw [hw] at e; cases e; exact ⟨u, j, hu, uj⟩
    · exact absurd (hP p) hk
  rcases h with ⟨-, (⟨a, -, -, o, hu⟩ | ⟨-, -, -, all⟩)⟩ | ⟨N, -, (⟨-, -, bx, -⟩ | ⟨-, (⟨bx, -⟩ | ⟨-, -, -, all⟩)⟩)⟩
  · exact ⟨_, i, hu, by simp [setK, hw]⟩
  · obtain ⟨u, hu, -, a₂, -⟩ := all []
    exact ⟨u, i, hu, (a₂ k i fun m => hk (dsStrs_mem.mp m)).symm.trans hw⟩
  · exact box id bx
  · exact box False.elim bx
  · obtain ⟨u, hu, -, a₂, -⟩ := all []
    exact ⟨u, i, hu, (a₂ k i fun m => hk (dsStrs_mem.mp m)).symm.trans hw⟩

/-- The maps of a put select some key. -/
theorem put_selects {M : MW V → Prop} {rs ds : List Term} {neg v : Term} {w : MW V}
    (h : PutSem den M rs neg ds v w) : ∃ κ, SplitKey rs neg ds κ := by
  rcases h with ⟨-, (⟨a, ha, -⟩ | ⟨⟨k, hk⟩, -⟩)⟩ | ⟨N, rfl, -⟩
  · exact ⟨.atom a, Or.inl ha⟩
  · exact ⟨.dom k 0, hk⟩
  · obtain ⟨c, hc⟩ := fresh_str (setStrs N)
    exact ⟨.atom c, Or.inr ⟨N, rfl, by simpa [setStrs_mem] using hc⟩⟩

/-- The maps of a put hold a value of the type. -/
theorem put_value {M : MW V → Prop} {rs ds : List Term} {neg v : Term} {w : MW V}
    (h : PutSem den M rs neg ds v w) : ∃ x, den v x := by
  rcases h with ⟨-, (⟨-, -, ⟨x, -, hx⟩, -⟩ | ⟨-, hx, -⟩)⟩ | ⟨N, -, (⟨-, hx, -⟩ | ⟨-, (⟨-, un⟩ | ⟨-, hx, -⟩)⟩)⟩
  · exact ⟨x, hx⟩
  · exact hx
  · exact hx
  · refine Classical.byContradiction fun none => un ⟨fun s _ => ?_, fun k i f => f.elim⟩
    cases e : w (.atom s) with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl, fun hx => none ⟨x, hx⟩⟩
  · exact hx

/-- Every original map with a selected key set to a value of the type is a map of the put. -/
theorem put_witness {M : MW V → Prop} {rs ds : List Term} {neg v : Term} (ok : SplitOk rs neg ds)
    (nr : ∀ N, neg = .map N → rs = []) {u : MW V} (hu : M u) {κ : MKey} (hκ : SplitKey rs neg ds κ) {x : V}
    (hx : den v x) : PutSem den M rs neg ds v (updK κ x u) := by
  have ne : updK κ x u ≠ wNone := fun e => by have := congrFun e κ; simp [updK, wNone] at this
  -- The widened domains, at a domain key of a selected kind.
  have domc : ∀ k i, κ = .dom k i → .atom (domKind k) ∈ ds → DomC den M (dsStrs ds) v (updK κ x u) := by
    intro k i e dk
    subst e
    refine ⟨ne, fun F => ⟨u, hu, fun s => by simp [updK], fun k' i' nk => ?_, fun k' i' _ dk' => ?_⟩⟩
    · have : MKey.dom k' i' ≠ .dom k i := fun e => by
        simp only [MKey.dom.injEq] at e; obtain ⟨rfl, -⟩ := e; exact nk (dsStrs_mem.mpr dk)
      simp [updK, this]
    · by_cases e : MKey.dom k' i' = .dom k i
      · exact Or.inr (Or.inr ⟨x, by simp [updK, e], hx⟩)
      · exact Or.inr (Or.inl (by simp [updK, e]))
  -- The box at an atom outside the negated set, or at a domain key of a selected kind.
  have box : ∀ (S : List String) (P : String → Prop), (∀ s, κ = .atom s → s ∉ S) →
      (∀ k i, κ = .dom k i → P (domKind k)) → BoxD den M S P v (updK κ x u) := by
    intro S P hS hP
    refine ⟨fun s => ?_, fun k i => ?_⟩
    · by_cases e : MKey.atom s = κ
      · exact Or.inr ⟨hS s e.symm, x, by simp [updK, e], hx⟩
      · exact Or.inl ⟨u, hu, by simp [updK, e]⟩
    · by_cases e : MKey.dom k i = κ
      · exact Or.inr ⟨x, by simp [updK, e], Or.inr ⟨hP k i e.symm, hx⟩⟩
      · cases ui : u (.dom k i) with
        | none => exact Or.inl (by simp [updK, e, ui])
        | some y => exact Or.inr ⟨y, by simp [updK, e, ui], Or.inl ⟨u, i, hu, ui⟩⟩
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · cases κ with
    | atom s =>
      have hs : .atom s ∈ rs := by
        rcases hκ with h | ⟨N, e, -⟩
        · exact h
        · cases e
      refine Or.inl ⟨rfl, Or.inl ⟨s, hs, ⟨x, by simp [updK], hx⟩, u (.atom s), ?_⟩⟩
      have : setK s (u (.atom s)) (updK (.atom s) x u) = u := by
        funext κ'; by_cases e : κ' = .atom s <;> simp [setK, updK, e]
      rw [this]; exact hu
    | dom k i => exact Or.inl ⟨rfl, Or.inr ⟨⟨k, hκ⟩, ⟨x, hx⟩, domc k i rfl hκ⟩⟩
  · refine Or.inr ⟨N, rfl, ?_⟩
    have atomS : ∀ s, κ = .atom s → s ∉ setStrs N := fun s e => by
      subst e
      rcases hκ with h | ⟨N', e, hN⟩
      · rw [nr N rfl] at h; simp at h
      · simp only [Term.map.injEq] at e; subst e; simpa [setStrs_mem] using hN
    by_cases full : FullDs ds
    · exact Or.inl ⟨full, ⟨x, hx⟩, box _ _ atomS (fun k i e => by subst e; exact hκ), ne⟩
    · refine Or.inr ⟨full, ?_⟩
      cases κ with
      | atom s =>
        refine Or.inl ⟨box _ _ atomS (fun k i e => by cases e), fun ⟨un, _⟩ => ?_⟩
        rcases un s (atomS s rfl) with e | ⟨y, e, ny⟩
        · simp [updK] at e
        · simp [updK] at e; subst e; exact ny hx
      | dom k i => exact Or.inr ⟨⟨k, hκ⟩, ⟨x, hx⟩, domc k i rfl hκ⟩

end

section
variable {t : Term} {n : Nat}

/-- Non-empty static map types of the next level hold a map. -/
theorem nonempty_map {Y : List (Term × Term)} (dY : DE (level t n).E (.map Y))
    (onlyY : ∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (h : Elixir.Module.Types.Descr.«empty?/1» (D m) (.map Y) = .ok (.atom "false")) : ∃ w, MT t n Y w := by
  rw [next_empty dY hm] at h
  obtain ⟨q, hq⟩ : ∃ q : PN t n, denD (.map Y) q := by
    cases e : bp (∀ q : PN t n, ¬denD (.map Y) q)
    · exact Classical.byContradiction fun none => by
        have := bp_true.mpr fun q hq => none ⟨q, hq⟩
        rw [e] at this; cases this
    · rw [e] at h; simp [boolAtom] at h
  obtain ⟨w, hw⟩ := pt_map q (onlyY q hq)
  exact ⟨w, (hw Y).mp hq⟩

end

section
variable {t : Term} {n : Nat}

/-- The kind types of the laws hold every point of their kind. -/
theorem kind_full {d : String} (hd : d ∈ domainKinds) (na : d ≠ "atom") {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ T, Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom d) = .ok (.map T) ∧
      ∀ v : PN t n, ptKind v = d → denD (.map T) v := by
  have bit : ∀ i (hi : i < 8), i ≠ 2 → ∀ v : PN t n, ptKind v = bitKind i →
      denD (.map [(.atom "bitmap", .integer ((2 ^ i : Nat) : Int))]) v := fun i hi ni v hv =>
    (domT_bit (t := t) (n := n) i hi ni).kinds (by
      match i, hi, ni with
      | 0, _, _ | 1, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ | 7, _, _ => simp [bitKind]) v hv
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl na
  · exact ⟨_, rfl, fun v hv => by simpa using bit 0 (by omega) (by omega) v (by simpa [bitKind] using hv)⟩
  · exact ⟨_, rfl, fun v hv => by simpa using bit 1 (by omega) (by omega) v (by simpa [bitKind] using hv)⟩
  · exact ⟨_, rfl, fun v hv => by simpa using bit 4 (by omega) (by omega) v (by simpa [bitKind] using hv)⟩
  · refine ⟨_, rfl, fun v hv => (denD_single _ _ v).mpr ⟨ptKind_field hv (by simp), dn_funTop _⟩⟩
  · exact ⟨_, rfl, fun v hv => by simpa using bit 3 (by omega) (by omega) v (by simpa [bitKind] using hv)⟩
  · have b2 := kind_bit (t := t) (n := n) 2 (by omega)
    simp only [show ((2 ^ 2 : Nat) : Int) = 4 from rfl] at b2
    have dl : DE (level t n).E (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) :=
      single_de (by simp [names]) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Bdd.leaf_iff.mpr
        ⟨46675407, _, _, rfl, (level t n).ef.term, (level t n).ef.term⟩⟩))))
    obtain ⟨U, rU, -, sU⟩ := union_map b2.de dl hm
    refine ⟨U, ?_, fun v hv => (sU v).mpr ?_⟩
    · simp [Elixir.STTDescrProofsTest.«kind_type/1», Elixir.Module.Types.Descr.«empty_list/0»,
        Elixir.Module.Types.Descr.«term/0», non_empty_list_top, rU]
    · by_cases hb : v.1.1 = "bitmap"
      · have hp : v.1.2.1 < 8 := v.2.2.2.1 hb
        have e : v.1.2.1 = 2 := bitKind_inj hp (by omega) (by simpa [ptKind, hb, bitKind] using hv)
        refine Or.inl ((denD_single _ _ v).mpr ⟨hb, ?_⟩)
        simp only [dn_bitmap, bitOf, e]
        decide
      · have hl : v.1.1 = "list" := by simpa [ptKind, hb] using hv
        exact Or.inr ((denD_single _ _ v).mpr ⟨hl, by simp [dn_list, denL_top]⟩)
  · exact ⟨_, rfl, fun v hv => (mapTop_den v).mpr (ptKind_field hv (by simp))⟩
  · exact ⟨_, rfl, fun v hv => by simpa using bit 5 (by omega) (by omega) v (by simpa [bitKind] using hv)⟩
  · exact ⟨_, rfl, fun v hv => by simpa using bit 6 (by omega) (by omega) v (by simpa [bitKind] using hv)⟩
  · exact ⟨_, rfl, fun v hv => by simpa using bit 7 (by omega) (by omega) v (by simpa [bitKind] using hv)⟩
  · exact ⟨_, rfl, fun v hv => (tupleTop_den v).mpr (ptKind_field hv (by simp))⟩

end

end Elixir.STTDescrProofsTest.Nest
