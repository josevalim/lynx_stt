module

public import Erlang.program
public import MapSplitPairs
public import ListsSortCompare

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- `open_map/1` of one optional key is the open literal of that field. -/
theorem open_map_opt (a : String) {v : Term} (hv : Static v) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom a, .tuple #[v, .atom "true"]]]) =
      .ok (.map [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "true"])]])]) ∧
    KeyOk (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "true"])]]) := by
  obtain ⟨k, leaf, key⟩ := leaf_new_key "open" (Or.inl rfl) [.tuple #[.atom a, .tuple #[v, .atom "true"]]]
  refine ⟨k, ?_, key⟩
  simp only [Elixir.Module.Types.Descr.«open_map/1», Elixir.Module.Types.Descr.«map_descr/2»,
    Elixir.Module.Types.Descr.«map_descr_pairs/1»]
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure,
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_atom/1», Erlang.erlang.«is_boolean/1»,
    Elixir.Module.Types.Descr.«map_descr_pair/4», split_static hv, Lynx.Except.orElse, Lynx.Except.andAlso,
    ukeysort_one, Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2»]
  simp only [Term.list] at leaf
  simp [fieldsTerm, Term.list, leaf]

theorem fieldsV_opt {a : String} {e : Term} (he : (level t n).E e) :
    FieldsV (level t n).E [(.atom a, .tuple #[e, .atom "true"])] :=
  ⟨fun x mx => by simp at mx; subst mx; exact ⟨⟨a, rfl⟩, ⟨e, Bool.true, rfl, he⟩⟩, by simp⟩

/-- Values allowed at a key: absent, or of a type. -/
def OkAt (den : Term → V → Prop) (e : Term) (o : Option V) : Prop := o = none ∨ ∃ x, o = some x ∧ den e x

/-- The maps of an open literal of one optional key. -/
theorem mt_open_opt {e : Term} (he : (level t n).E e) (a : String) (k : Int) (w : MW (level t n).V) :
    MT t n [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[e, .atom "true"])]])] w ↔
      OkAt (level t n).den e (w (.atom a)) := by
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', equalExact_eq_decide]
  rw [denMF_leaf (level t n).ef (fieldsV_opt he) (Or.inl rfl), msem_at (level t n).ef (Or.inl rfl) _ a]
  have er : eraseKey a [(.atom a, .tuple #[e, .atom "true"])] = [] := by simp [eraseKey]
  rw [er]
  simp only [fieldAt, lookup_cons_atom, ite_true, Option.getD_some, msem_open_nil, and_true]
  rw [show Term.atom "true" = boolAtom Bool.true from rfl, fieldSem_mk]
  simp [OkAt]

/-- The domains an open map of one domain kind holds: values of a type at the kind, and any value at the others. -/
def domL (d : String) (v : Term) : List (Term × Term) :=
  domainKinds.map fun s => (.atom s, if s = d then v else .atom "term")

theorem map_put_domain_one (m : Nat) (k v : Term) :
    Elixir.Module.Types.Descr.«map_put_domain/4» (D m) .nil (Term.list [k]) v v = .ok (Term.list [.tuple #[k, v]]) := by
  rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
  simp only [Term.list]
  rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
  rfl

theorem pairs_domain (m : Nat) (d : String) {v : Term} (hv : Static v) (acc : Term) :
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[Term.list [.atom d], v]) acc =
      Elixir.Module.Types.Descr.«map_descr_domain/3» (D m) (Term.list [.atom d]) v acc := by
  rcases hv with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩ <;>
    simp [Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_list/1», Term.list]

/-- The domain kinds, as the domains of open maps list them. -/
def domKeysT : Term := Term.list (domainKinds.map Term.atom)

/-- `fields_put_all_new/3` fills the other domain kinds of a domain with `term()`. -/
theorem put_all_dom {d : String} (hd : d ∈ domainKinds) (v : Term) (m : Nat) :
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (Term.list [.tuple #[.atom d, v]]) domKeysT (.atom "term") =
      .ok (fieldsTerm (domL d v)) := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def, Term.list, domKeysT,
      domainKinds, domL, fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», Erlang.lists.«map/2»,
      Erlang.lists.«map_1/2».eq_def, Erlang.erlang.«is_function/2», Elixir.Module.Types.Descr.«-fields_put_all_new/3-fun-0-/2»,
      Erlang.program.«Elixir.Module.Types.Descr:-fields_put_all_new/3-fun-0-/1».pure]


theorem domsV_domL (d : String) {v : Term} (he : (level t n).E v) : DomsV (level t n).E (domL d v) := by
  refine ⟨fun e me => ?_, ?_⟩
  · obtain ⟨s, ms, rfl⟩ := List.mem_map.mp me
    refine ⟨⟨s, rfl, ms⟩, ?_⟩
    by_cases h : s = d
    · simp [h, he]
    · simp [h, (level t n).ef.term]
  · simp only [domL, domainKinds, List.map_cons, List.map_nil]
    simp (config := { decide := true }) [atoms_cmp, Ord.compare]

theorem usort_one (x : Term) : Erlang.lists.«usort/1» (Term.list [x]) = .ok (Term.list [x]) := by
  rw [Erlang.lists.«usort/1».eq_def]; rfl

theorem ukeysort_nil : Erlang.lists.«ukeysort/2» (.integer 1) .nil = .ok .nil := by
  rw [Erlang.lists.«ukeysort/2».eq_def]
  simp [Erlang.erlang.«>/2», cmp10, Erlang.erlang.«and/2»]

/-- `open_map/1` of one domain kind is the open literal of its domains. -/
theorem open_map_dom {d : String} (hd : d ∈ domainKinds) {v : Term} (hv : Static v) (he : (level t n).E v) (m : Nat) :
    ∃ k : Int, Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[Term.list [.atom d], v]]) =
      .ok (.map [(.atom "map", .tuple #[.integer k, fieldsTerm (domL d v), .nil])]) ∧
    KeyOk (.tuple #[.integer k, fieldsTerm (domL d v), .nil]) := by
  obtain ⟨k, leaf, key⟩ := leaf_new_keyM (E := (level t n).E) (Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)) []
  refine ⟨k, ?_, by simpa [Term.list] using key⟩
  have pa := put_all_dom hd v (m + 1)
  simp only [domKeysT, domainKinds, List.map_cons, List.map_nil] at pa
  simp only [Elixir.Module.Types.Descr.«open_map/1», Elixir.Module.Types.Descr.«map_descr/2»,
    Elixir.Module.Types.Descr.«map_descr_pairs/1»]
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure, pairs_domain _ d hv,
    Elixir.Module.Types.Descr.«map_descr_domain/3», split_static hv, Elixir.Module.Types.Descr.«map_put_domain/3»,
    Erlang.erlang.«is_list/1», ukeysort_nil, Lynx.Except.orElse,
    Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2»]
  rw [usort_one]
  simp only [Lynx.Except.ok_bind]
  rw [map_put_domain_one]
  simp only [Term.list] at pa leaf ⊢
  simp [pa, leaf]

theorem lookup_domL {kind : String} (hk : kind ∈ domainKinds) (d : String) (v : Term) :
    mapLookup (domL d v) (.atom kind) = some (if kind = d then v else .atom "term") := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [domL, domainKinds, lookup_cons_atom]

/-- The maps of an open literal of one domain kind. -/
theorem mt_dom {d : String} {v : Term} (he : (level t n).E v) (k : Int) (w : MW (level t n).V) :
    MT t n [(.atom "map", .tuple #[.integer k, fieldsTerm (domL d v), .nil])] w ↔
      (d = "atom" → ∀ s, OkAt (level t n).den v (w (.atom s))) ∧
        ∀ k' i, domKind k' = d → OkAt (level t n).den v (w (.dom k' i)) := by
  have g : TagV (level t n).E (fieldsTerm (domL d v)) := Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)
  have hn : ∀ x, ¬(level t n).den (.map []) x := fun x h => (level t n).ef.den_none x h
  have ts : ∀ kind ∈ domainKinds, ∀ o, TagSem (level t n).den (fieldsTerm (domL d v)) kind o ↔
      (kind = d → OkAt (level t n).den v o) := by
    intro kind mk o
    rw [tagSem_dom_iff hn, lookup_domL mk]
    by_cases e : kind = d
    · simp [e, OkAt]
    · simp only [e, ite_false, OkAt]
      cases o <;> simp [(level t n).ef.den_term]
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', equalExact_eq_decide]
  rw [show (Term.nil : Term) = fieldsTerm [] from rfl, denMF_leaf (level t n).ef ⟨by simp, by simp⟩ g]
  constructor
  · intro h
    refine ⟨fun e s => ?_, fun k' i e => ?_⟩
    · have := h.atoms s
      unfold FSem at this
      simp only [mapLookup, List.find?_nil, Option.map_none, equalExact_eq_decide] at this
      exact (ts "atom" (by simp [domainKinds]) _).mp this e.symm
    · exact (ts _ (domKind_mem k') _).mp (h.doms k' i) e
  · rintro ⟨ha, hd'⟩
    refine ⟨fun s => ?_, fun k' i => (ts _ (domKind_mem k') _).mpr (hd' k' i)⟩
    unfold FSem
    simp only [mapLookup, List.find?_nil, Option.map_none, equalExact_eq_decide]
    exact (ts "atom" (by simp [domainKinds]) _).mpr fun e => ha e.symm s

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- A point of the next level that is the map of some values. -/
def MapOf (p : PN t n) (w : MW (level t n).V) : Prop := ∀ (Y : List (Term × Term)), denD (.map Y) p ↔ MT t n Y w

theorem mapOf_mpt (w : MW (level t n).V) : MapOf (mpt (t := t) (n := n) w) w := fun _ => denD_mpt w

/-- Map types whose points are maps of values satisfying a condition. -/
def MapsOf (t : Term) (n : Nat) (H : Term) (Q : MW (level t n).V → Prop) : Prop :=
  DE (level t n).E H ∧ (∀ p : PN t n, denD H p → p.1.1 = "map") ∧ ∀ (p : PN t n) w, MapOf p w → (denD H p ↔ Q w)

theorem mapsOf_one (b : Term) (fb : MField (level t n).E b) :
    MapsOf t n (.map [(.atom "map", b)]) (fun w => MT t n [(.atom "map", b)] w) := by
  refine ⟨mfused_de fb, fun p hp => ?_, fun p w hw => hw _⟩
  rw [denD_map] at hp
  by_cases h : p.1.1 = "map"
  · exact h
  · simp [mapLookup, h, dn_none] at hp

theorem mapsOf_inter {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ C, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) A B = .ok C ∧ MapsOf t n C (fun w => QA w ∧ QB w) := by
  obtain ⟨c, hc, rc, sc, -⟩ := (ef_next t n).inter hA.1 hB.1
  exact ⟨c, rc m hm, hc, fun p hp => hA.2.1 p ((sc p).mp hp).1, fun p w hw => by rw [sc, hA.2.2 p w hw, hB.2.2 p w hw]⟩

/-- `atoms_hold/3` intersects maps holding values of a type at atom keys. -/
theorem atoms_hold_run {v : Term} (hv : Static v) (he : (level t n).E v) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∀ (atoms : List Term), (∀ a ∈ atoms, ∃ s, a = .atom s) → ∀ (acc : Term) (Q : MW (level t n).V → Prop),
      MapsOf t n acc Q → ∃ H, Elixir.STTDescrProofsTest.«atoms_hold/3» (D m) (Term.list atoms) v acc = .ok H ∧
        MapsOf t n H (fun w => Q w ∧ ∀ s, .atom s ∈ atoms → OkAt (level t n).den v (w (.atom s)))
  | [], _, acc, Q, h => ⟨acc, by simp [Elixir.STTDescrProofsTest.«atoms_hold/3»], by simpa using h⟩
  | a :: rest, ha, acc, Q, h => by
    obtain ⟨s, rfl⟩ := ha _ List.mem_cons_self
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k, rk, key⟩ := open_map_opt s hv m'
    have piece := mapsOf_one (t := t) (n := n) _ (mleaf_field (Or.inl rfl) (fieldsV_opt he) key)
    obtain ⟨C, rC, hC⟩ := mapsOf_inter h piece (m := m' + 1) (by omega)
    obtain ⟨H, rH, hH⟩ := atoms_hold_run hv he hm rest (fun a ma => ha a (List.mem_cons_of_mem _ ma)) C _ hC
    refine ⟨H, ?_, hH.1, hH.2.1, fun p w hw => ?_⟩
    · simp only [Term.list] at rk rH ⊢
      simp [Elixir.STTDescrProofsTest.«atoms_hold/3», rk, rC, rH]
    · rw [hH.2.2 p w hw]
      simp only [mt_open_opt he s k w]
      simp only [List.mem_cons, Term.atom.injEq]
      constructor
      · rintro ⟨⟨hq, hs⟩, hr⟩
        exact ⟨hq, fun s' hs' => hs'.elim (fun e => e ▸ hs) (hr s')⟩
      · rintro ⟨hq, hr⟩
        exact ⟨⟨hq, hr s (Or.inl rfl)⟩, fun s' m' => hr s' (Or.inr m')⟩

/-- `kinds_hold/3` intersects maps holding values of a type at the keys of kinds. -/
theorem kinds_hold_run {v : Term} (hv : Static v) (he : (level t n).E v) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∀ (kinds : List Term), (∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) → ∀ (acc : Term) (Q : MW (level t n).V → Prop),
      MapsOf t n acc Q → ∃ H, Elixir.STTDescrProofsTest.«kinds_hold/3» (D m) (Term.list kinds) v acc = .ok H ∧
        MapsOf t n H (fun w => Q w ∧ ∀ d, .atom d ∈ kinds →
          (d = "atom" → ∀ s, OkAt (level t n).den v (w (.atom s))) ∧
            ∀ k i, domKind k = d → OkAt (level t n).den v (w (.dom k i)))
  | [], _, acc, Q, h => ⟨acc, by simp [Elixir.STTDescrProofsTest.«kinds_hold/3»], by simpa using h⟩
  | a :: rest, hk, acc, Q, h => by
    obtain ⟨d, md, rfl⟩ := hk _ List.mem_cons_self
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k, rk, key⟩ := open_map_dom md hv he m'
    have fb : MField (level t n).E (.tuple #[.integer k, fieldsTerm (domL d v), .nil]) :=
      mleaf_field (Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)) (l := []) ⟨by simp, by simp⟩ key
    have piece := mapsOf_one (t := t) (n := n) _ fb
    obtain ⟨C, rC, hC⟩ := mapsOf_inter h piece (m := m' + 1) (by omega)
    obtain ⟨H, rH, hH⟩ := kinds_hold_run hv he hm rest (fun a ma => hk a (List.mem_cons_of_mem _ ma)) C _ hC
    refine ⟨H, ?_, hH.1, hH.2.1, fun p w hw => ?_⟩
    · simp only [Term.list] at rk rH ⊢
      simp [Elixir.STTDescrProofsTest.«kinds_hold/3», rk, rC, rH]
    · rw [hH.2.2 p w hw]
      simp only [mt_dom he k w, List.mem_cons, Term.atom.injEq]
      constructor
      · rintro ⟨⟨hq, hs⟩, hr⟩
        exact ⟨hq, fun d' hd' => hd'.elim (fun e => e ▸ hs) (hr d')⟩
      · rintro ⟨hq, hr⟩
        exact ⟨⟨hq, hr d (Or.inl rfl)⟩, fun d' m' => hr d' (Or.inr m')⟩

/-- `keys_hold/3`: maps holding values of a type at the keys of the given atoms and kinds. -/
theorem keys_hold_run (atoms kinds : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s)
    (hk : ∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) {v : Term} (hv : Static v) (he : (level t n).E v) {m : Nat}
    (hm : (level t n).K + 24 ≤ m) :
    ∃ H, Elixir.STTDescrProofsTest.«keys_hold/3» (D m) (Term.list atoms) (Term.list kinds) v = .ok H ∧
      MapsOf t n H (fun w => ∀ κ, KeysOf atoms kinds κ → OkAt (level t n).den v (w κ)) := by
  have top := mapsOf_one (t := t) (n := n) (.tuple #[.integer 61102469, .atom "open", .nil]) (Or.inl ⟨_, rfl⟩)
  obtain ⟨A, rA, hA⟩ := atoms_hold_run hv he hm atoms ha _ _ top
  obtain ⟨H, rH, hH⟩ := kinds_hold_run hv he hm kinds hk A _ hA
  refine ⟨H, by simp [Elixir.STTDescrProofsTest.«keys_hold/3», Elixir.Module.Types.Descr.«open_map/0», rA, rH],
    hH.1, hH.2.1, fun p w hw => ?_⟩
  rw [hH.2.2 p w hw]
  have tw : MT t n [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])] w := by
    simp [MT, mapLookup, denMF_top]
  constructor
  · rintro ⟨⟨-, has⟩, hks⟩ κ hκ
    cases κ with
    | atom s =>
      rcases hκ with h | h
      · exact has s h
      · exact (hks "atom" h).1 rfl s
    | dom k i => exact (hks _ hκ).2 k i rfl
  · intro h
    refine ⟨⟨tw, fun s hs => h (.atom s) (Or.inl hs)⟩, fun d hd => ⟨fun e s => ?_, fun k i e => ?_⟩⟩
    · subst e; exact h (.atom s) (Or.inr hd)
    · subst e; exact h (.dom k i) hd

end

end Elixir.STTDescrProofsTest.Nest
