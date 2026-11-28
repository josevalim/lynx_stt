module

public import Erlang.program
public import OptUnionNegation

@[expose] public section

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! The recursive node of the plain laws: its expansion is nil or a closed pair of a term and the node. -/

/-- The expansion literal of a node, with key `k`. -/
def litN (e : Term) (k : Int) : Term := .tuple #[.integer k, .atom "closed", Term.list [.atom "term", e]]

/-- The expansion of a node. -/
def expN (e : Term) (k : Int) : Term :=
  .map [(.atom "tuple", litN e k), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]

theorem tuple_node_run {r : List Nat} {e : Term} (h : NodeAt r e) {k : Int}
    (leaf : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list [.atom "term", e]) =
      .ok (.tuple #[.integer k, .atom "closed", Term.list [.atom "term", e]])) :
    Elixir.Module.Types.Descr.«tuple/1» (Term.list [.atom "term", e]) = .ok (.map [(.atom "tuple", litN e k)]) := by
  obtain ⟨S, rfl, -⟩ := h
  have c₁ : Term.compare (Term.fuel (Term.atom "term") (.map [])) (Term.atom "term") (.map []) ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  have c₂ : Term.compare (Term.fuel (Term.tuple ⟨[.reference r, .map S, gen]⟩) (.map [])) (Term.tuple ⟨[.reference r, .map S, gen]⟩) (.map []) ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  simp only [Term.list] at leaf ⊢
  simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₁, c₂, Elixir.Module.Types.Descr.«tuple/1»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_fields/5»,
    Elixir.Module.Types.Descr.«split_dynamic/1»,
    Elixir.Module.Types.Descr.«tuple_descr_static/2», Elixir.Module.Types.Descr.«tuple_new/2», leaf,
    Erlang.lists.«reverse/1», Term.list, litN]

/-- Nodes expand to nil or their expansion literal. -/
theorem expand_node_of {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (leaf : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list [.atom "term", e]) =
      .ok (.tuple #[.integer k, .atom "closed", Term.list [.atom "term", e]])) :
    Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k) := by
  have tup := tuple_node_run h leaf
  obtain ⟨S, rfl, hk⟩ := h
  have recur : Elixir.Module.Types.Descr.«-expand_node/1-fun-0-/2» (.map S) (.atom "t") =
      .ok (.tuple #[.reference r, .map S, gen]) := by
    obtain ⟨q, hq⟩ : ∃ q, S.find? (fun entry => decide (Term.compareExact (Term.fuel (Term.atom "t") entry.fst) (Term.atom "t") entry.fst = .eq)) =
        some (q, .tuple #[.reference r, gen]) := by
      simp only [getMapKeys, List.mapM_cons, List.mapM_nil, equalExact_eq_decide] at hk
      cases hf : S.find? (fun entry => decide (Term.compareExact (Term.fuel (Term.atom "t") entry.fst) (Term.atom "t") entry.fst = .eq)) with
      | none => simp [hf] at hk
      | some p => obtain ⟨q, v⟩ := p; simp [hf] at hk; exact ⟨q, by rw [hk]⟩
    simp [Elixir.Module.Types.Descr.«-expand_node/1-fun-0-/2», Erlang.erlang.«map_get/2», hq,
      Elixir.Module.Types.Descr.«make_node/3»]
  have atomNil : Elixir.Module.Types.Descr.«atom/1» (Term.list [.atom "nil"]) =
      .ok (.map [(.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]) := rfl
  have run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) (.tuple #[.reference r, .map S, gen]) =
      Elixir.Module.Types.Descr.«bare_union/2» (D m)
        (.map [(.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])])
        (.map [(.atom "tuple", litN (.tuple #[.reference r, .map S, gen]) k)]) := by
    unfold Elixir.Module.Types.Descr.«expand_node/1»
    simp only [gen, D, Erlang.program.«Elixir.STTDescrProofsTest:tuple_list/1».pure, pure, Except.pure,
      Lynx.Except.ok_bind]
    simp only [Elixir.STTDescrProofsTest.«Elixir.STTDescrProofsTest:tuple_list/1», Elixir.STTDescrProofsTest.«tuple_list/1»,
      atomNil, Lynx.Except.ok_bind, Erlang.program.«Elixir.Module.Types.Descr:-expand_node/1-fun-0-/1».pure, recur,
      Elixir.Module.Types.Descr.«term/0»]
    simp only [pure, Except.pure, Lynx.Except.ok_bind]
    rw [tup]
    simp only [Lynx.Except.ok_bind, gen]
  rw [run]
  unfold Elixir.Module.Types.Descr.«bare_union/2»
  simp [expN, Erlang.erlang.«==/2», Lynx.Term.getMapKeys, Elixir.Module.Types.Descr.«symmetrical_merge/3»,
    Erlang.maps.«merge_with/3», mapEntries_singleton, mapLookup]



theorem expand_node_run {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k) := by
  obtain ⟨k, leaf⟩ := leaf_closed [.atom "term", e]
  exact ⟨k, expand_node_of h m leaf⟩

/-! Plain operations compute on the expansion of a node. -/

theorem inter_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term") :
    Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (expN e k) b := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_intersection/2».eq_def, Elixir.Module.Types.Descr.«bare_intersection/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp [run, unfold_map, expN]
  all_goals simp [run, unfold_map, expN]


theorem inter_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) (ha : a ≠ .atom "term") :
    Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_intersection/2».eq_def, Elixir.Module.Types.Descr.«bare_intersection/2».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp [run, unfold_map, expN]
  all_goals simp [run, unfold_map, expN]

theorem sub_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) :
    Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) (expN e k) b := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«subtype?/2».eq_def, Elixir.Module.Types.Descr.«subtype?/2».eq_def]
  simp [run, unfold_map, expN]

theorem sub_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) :
    Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«subtype?/2».eq_def, Elixir.Module.Types.Descr.«subtype?/2».eq_def]
  simp [run, unfold_map, expN]


theorem node_ne_none {r : List Nat} {e : Term} (h : NodeAt r e) : Term.compare (Term.fuel e (.map [])) e (.map []) ≠ .eq := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Term.compare_step]; simp [Compare.compareStep]

theorem map_ne_none {B : List (Term × Term)} (ne : B ≠ []) : Term.compare (Term.fuel (Term.map B) (.map [])) (Term.map B) (.map []) ≠ .eq := by
  obtain ⟨e, xs, rfl⟩ : ∃ e xs, B = e :: xs := by
    cases B with
    | nil => exact absurd rfl ne
    | cons e xs => exact ⟨e, xs, rfl⟩
  have pos : ∀ (l : List (Term × Term)) (p : Term × Term),
      (Compare.mapViewInsert (fun a b => compareExact (fuel a b) a b) p l).length ≠ 0 := by
    intro l p
    cases l with
    | nil => simp [Compare.mapViewInsert]
    | cons q l => simp only [Compare.mapViewInsert]; split <;> simp
  intro h
  rw [Term.compare_step] at h
  simp [Compare.compareStep, Compare.compareMapViews, Compare.mapView] at h
  have h1 := h.1
  simp only [Compare.compareOn] at h1
  have := pos (Compare.mapView (fun a b => Term.compareExact (Term.fuel a b) a b) xs) e
  have z : (Compare.mapViewInsert (fun a b => compareExact (fuel a b) a b) e (Compare.mapView (fun a b => compareExact (fuel a b) a b) xs)).length = 0 := by
    simpa [Nat.compare_eq_eq] using h1
  exact this z


theorem expN_ne_none (e : Term) (k : Int) : Term.compare (Term.fuel (expN e k) (.map [])) (expN e k) (.map []) ≠ .eq :=
  map_ne_none (by simp)

theorem diff_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) :
    Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a (expN e k) := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_difference/2».eq_def, Elixir.Module.Types.Descr.«bare_difference/2».eq_def]
  simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem upper_expN (d : Dispatcher) (e : Term) (k : Int) :
    Elixir.Module.Types.Descr.«upper_bound/1» d (expN e k) = .ok (expN e k) := by
  unfold Elixir.Module.Types.Descr.«upper_bound/1»
  simp [expN, getMapKeys_single, mapLookup]

/-- The expansion of a node is not empty: it holds nil. -/
theorem empty_expN (d : Dispatcher) (e : Term) (k : Int) (S : Term) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d (expN e k) S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [expN, getMapKeys_single, Erlang.erlang.«==/2», Erlang.erlang.«is_map_key/2», mapLookup, Term.true,
    Term.false, Lynx.Except.andAlso]

/-- A node is empty only when seen: its expansion holds nil. -/
theorem empty_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D (m + 1)) e (.map S) =
      .ok (boolAtom (S.any fun p => decide (Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 = .eq))) := by
  obtain ⟨k, run⟩ := expand_node_run h m
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  cases hs : S.any fun p => decide (Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 = .eq) <;>
    simp [Erlang.erlang.«is_map_key/2», hs, Term.true, Term.false, Erlang.maps.«put/3», run, empty_expN, boolAtom]

theorem getMapKeys_tuple (ks : List Term) (xs : Array Term) : getMapKeys ks (.tuple xs) = [] := rfl

theorem disj_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term")
    (sb : ∀ X, b = .map X → mapLookup X (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) (expN e k) b := by
  obtain ⟨S, rfl, -⟩ := h
  have ue := upper_expN (D (m + 1)) (.tuple #[.reference r, .map S, gen]) k
  simp only [expN] at ue
  rw [Elixir.Module.Types.Descr.«disjoint?/2».eq_def, Elixir.Module.Types.Descr.«disjoint?/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp [run, unfold_map, expN, getMapKeys, ue]
  case map X =>
    have hE : mapLookup [(.atom "tuple", litN (.tuple #[.reference r, .map S, gen]) k),
        (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] (.atom "dynamic") = none := by
      simp [mapLookup]
    simp [run, unfold_map, expN, getMapKeys_single, getMapKeys_tuple, ue, sb X rfl, hE]
  all_goals simp [run, unfold_map, expN, getMapKeys, ue]


theorem disj_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) (ha : a ≠ .atom "term")
    (sa : ∀ X, a = .map X → mapLookup X (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) a (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  have ue := upper_expN (D (m + 1)) (.tuple #[.reference r, .map S, gen]) k
  simp only [expN] at ue
  have hE : mapLookup [(.atom "tuple", litN (.tuple #[.reference r, .map S, gen]) k),
      (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] (.atom "dynamic") = none := by
    simp [mapLookup]
  rw [Elixir.Module.Types.Descr.«disjoint?/2».eq_def, Elixir.Module.Types.Descr.«disjoint?/2».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp [run, unfold_map, expN, getMapKeys, ue]
  case map X => simp [run, unfold_map, expN, getMapKeys_single, getMapKeys_tuple, ue, sa X rfl, hE]
  all_goals simp [run, unfold_map, expN, getMapKeys, ue]

theorem tail_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) :
    Elixir.Module.Types.Descr.«list_tail_unfold/1» (D (m + 1)) e = .ok (expN e k) := by
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«list_tail_unfold/1».eq_def]
  simp [run, unfold_map, expN, Erlang.maps.«remove/2»]


/-! The emptiness of BDDs of the expansion literal: their elements are nodes, which hold nil, so they are not
empty unless seen. -/

/-- Whether a seen set holds the id of the node `r`. -/
def idIn (r : List Nat) (S : List (Term × Term)) : Bool := S.any fun p => decide (Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 = .eq)

theorem els_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D (m + 2)) (Term.list [.atom "term", e]) (.map S) =
      .ok (boolAtom (idIn r S)) := by
  have e₁ : Elixir.Module.Types.Descr.«empty_seen?/2» (D (m + 1)) (.atom "term") (.map S) = .ok (.atom "false") := by
    unfold Elixir.Module.Types.Descr.«empty_seen?/2»; rfl
  have e₂ := empty_node h m S
  simp [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», Erlang.lists.«any/2», Erlang.erlang.«is_function/2»,
    D, Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure,
    Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2», e₁, Term.list]
  rw [Erlang.lists.«any_1/2».eq_def]
  simp [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure,
    Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2», e₂]
  rw [Erlang.lists.«any_1/2».eq_def]
  simp only [idIn]
  cases hi : S.any (fun p => decide (Term.compareExact (Term.fuel (.reference r) p.1) (.reference r) p.1 = .eq)) <;> simp [boolAtom] <;> rfl


theorem walk_leaf_node {r : List Nat} {e : Term} (h : NodeAt r e) (k : Int) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (m + 2)) (.tuple #[.atom "open", .nil]) .nil (litN e k) (.map S) =
      .ok (boolAtom (idIn r S)) := by
  have els := els_node h m S
  simp only [Term.list] at els
  cases hb : idIn r S <;> rw [hb] at els <;>
    simp [litN, Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4», els,
      Term.list, boolAtom]

theorem walk_pos_node {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (m + 2))
      (.tuple #[.atom "closed", Term.list [.atom "term", e]]) .nil (.atom "bdd_top") (.map S) =
      .ok (boolAtom (idIn r S)) := by
  have els := els_node h m S
  cases hb : idIn r S <;> rw [hb] at els <;>
    simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4», els,
      Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, boolAtom]

theorem walk_neg_node (e : Term) (k : Int) (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) (.cons (litN e k) .nil)
      (.atom "bdd_top") S = .ok (.atom "false") := by
  simp [litN, Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil, Erlang.erlang.«==/2»,
    Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«/=/2», Lynx.Except.andAlso]


theorem tuple_walk_top (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil (.atom "bdd_top") S =
      .ok (.atom "false") := by
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]

theorem tuple_walk_bot (d : Dispatcher) (pos negs S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d pos negs (.atom "bdd_bot") S = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»]

/-- The top or empty BDD. -/
def bt (b : Bool) : Term := if b then .atom "bdd_top" else .atom "bdd_bot"

theorem walk_node_node {r : List Nat} {e : Term} (h : NodeAt r e) (k j : Int) (m : Nat) (S : List (Term × Term))
    (c u d : Bool) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (m + 2)) (.tuple #[.atom "open", .nil]) .nil
      (.tuple #[.integer j, litN e k, bt c, bt u, bt d]) (.map S) = .ok (boolAtom ((!c || idIn r S) && !u && !d)) := by
  have pt := walk_pos_node h m S
  have nt := walk_neg_node e k (D (m + 2)) (.map S)
  have tt := tuple_walk_top (D (m + 2)) (.map S)
  rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
  simp only [litN] at nt pt ⊢
  cases hb : idIn r S <;> rw [hb] at pt <;> cases c <;> cases u <;> cases d <;>
    simp [bt, tuple_walk_bot, pt, nt, tt, Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2», Term.list, boolAtom]

theorem diff_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term")
    (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) (expN e k) b := by
  have ne := node_ne_none h
  obtain ⟨S, rfl, -⟩ := h
  have tne : Term.compare (Term.fuel (Term.tuple #[.reference r, .map S, gen]) (.atom "term")) (Term.tuple #[.reference r, .map S, gen]) (.atom "term") ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  have ene : Term.compare (Term.fuel (expN (.tuple #[.reference r, .map S, gen]) k) (.atom "term")) (expN (.tuple #[.reference r, .map S, gen]) k) (.atom "term") ≠ .eq := by
    simp only [expN]; rw [Term.compare_step]; simp [Compare.compareStep]
  rw [Elixir.Module.Types.Descr.«bare_difference/2».eq_def, Elixir.Module.Types.Descr.«bare_difference/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem union_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b : Term) (hb : b ≠ .atom "term")
    (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) e b =
      Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) (expN e k) b := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def, Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem union_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a : Term) (ha : a ≠ .atom "term")
    (none : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) a e =
      Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) a (expN e k) := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def, Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

/-! The nodes the laws accept share the expansion literal of `t`, so BDDs of expansion literals hold a single
literal. -/

/-- The key of the expansion literal of the node `t`. -/
def keyOf (t : Term) : Int :=
  match Erlang.erlang.«phash2/1» (Term.list [.atom "term", t]) with
  | .ok (.integer h) => 268435456 + h - 288230376151711744
  | _ => 0

theorem leaf_isT {t e : Term} (h : IsT t e) :
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom "closed") (Term.list [.atom "term", e]) =
      .ok (.tuple #[.integer (keyOf t), .atom "closed", Term.list [.atom "term", e]]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (Term.list [.atom "term", t])
  have hk := h.hash
  rw [hrun] at hk
  simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hk, keyOf, hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2»,
    Erlang.erlang.«is_list/1», bsl27, Term.list, Erlang.erlang.«length/1», Erlang.erlang.«-/2_integers»] <;> decide

/-- Accepted nodes expand with the key of `t`. -/
theorem expand_isT {t e : Term} (h : IsT t e) (m : Nat) :
    Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e (keyOf t)) :=
  expand_node_of h.node m (leaf_isT h)

theorem lit_compare {t e e' : Term} (h₁ : IsT t e) (h₂ : IsT t e') (k : Int) :
    compare (fuel (litN e k) (litN e' k)) (litN e k) (litN e' k) = .eq := by
  have ce := compare_eq_of_compareExact_eq _ _ (isT_exact h₁ h₂)
  simp only [litN, Term.list]
  rw [Term.compare_step]
  simp [Compare.compareStep, List.compareLex_cons_cons, Ordering.then_eq_eq]
  rw [Term.compare_step]
  simp [Compare.compareStep]
  rw [Term.compare_step]
  simp [Compare.compareStep, ce, List.compareLex]

/-- The expansion literals of accepted nodes, with the key of `t`. -/
def PureLit (t l : Term) : Prop := ∃ e, IsT t e ∧ l = litN e (keyOf t)

theorem pureLit_not {t : Term} : ∀ l, PureLit t l → ¬IsTop l := by
  rintro l ⟨e, -, rfl⟩ ⟨k, h⟩
  simp [litN, Term.list] at h

theorem pure_inter {t x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_intersection/2» x y = .ok w ∧
      (kept (.atom "tuple", w) = Bool.true → OField (PureLit t) w) := by
  obtain ⟨w, run, k, -⟩ := open_inter_spec pureLit_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
    tuple_inter_shape.2.2 (.atom "tuple") fx fy
  exact ⟨w, run, fun kw => (k kw).1⟩

theorem pure_union {t x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok w ∧ OField (PureLit t) w := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl, Or.inl ⟨k, rfl⟩⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · refine ⟨_, ?_, Or.inl ⟨k, rfl⟩⟩
    have nx := not_top_of_ok wx pureLit_not
    unfold Elixir.Module.Types.Descr.«tuple_union/2»
    split
    · exact (nx _ rfl).elim
    · rename_i e; simp at e; subst e; rfl
    · rename_i h₁ h₂; exact (h₂ _ rfl).elim
  obtain ⟨r, hr, okr, -⟩ := union_ok wx wy
  exact ⟨r, by rw [tuple_union_bdd (not_top_of_ok wx pureLit_not) (not_top_of_ok wy pureLit_not), hr],
    Or.inr (okr _ wx wy)⟩

theorem pure_diff {t x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧
      (kept (.atom "tuple", w) = Bool.true → OField (PureLit t) w) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl,
      fun k => by simp [kept] at k⟩
  have ny := not_top_of_ok wy pureLit_not
  have special : ¬∃ k, y = .tuple #[k, .atom "closed", .nil] := by
    rintro ⟨k, rfl⟩
    unfold Bdd at wy
    split at wy <;> simp_all [PureLit, litN, Term.list]
    obtain ⟨e, -, -, h⟩ := wy
    cases h
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_top]
    · refine ⟨_, ?_, fun _ => Or.inl ⟨kt, rfl⟩⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    · obtain ⟨w, run, keep, -⟩ := neg_ok wy
      refine ⟨w, ?_, fun _ => Or.inr (keep _ wy)⟩
      rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
    · obtain ⟨w, run, keep, -⟩ := neg_ok wy
      refine ⟨w, ?_, fun _ => Or.inr (keep _ wy)⟩
      rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
  · obtain ⟨w, run, keep, -⟩ := diff_ok wx wy
    exact ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx pureLit_not) ny (fun ⟨_, h⟩ => special h), run],
      fun _ => Or.inr (keep _ wx wy)⟩

theorem pure_child {t lit c : Term} (hl : PureLit t lit) (wc : Bdd (fun s => PureLit t s ∧ compare (fuel lit s) lit s = .lt) c) :
    c = .atom "bdd_top" ∨ c = .atom "bdd_bot" := by
  obtain ⟨e, he, rfl⟩ := hl
  have no : ∀ s, PureLit t s → compare (fuel (litN e (keyOf t)) s) (litN e (keyOf t)) s ≠ .lt := by
    rintro s ⟨e', he', rfl⟩ h
    rw [lit_compare he he'] at h; cases h
  rcases wc.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, l, c', u, d, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · obtain ⟨p, q⟩ := Bdd.leaf_iff.mp wc
    exact absurd q (no _ p)
  · unfold Bdd at wc
    obtain ⟨-, ⟨p, q⟩, -⟩ := wc
    exact absurd q (no _ p)

/-- BDDs of expansion literals: the constants, a literal, or a node of a literal over constants. -/
theorem pure_shape {t x : Term} (wx : Bdd (PureLit t) x) :
    x = .atom "bdd_top" ∨ x = .atom "bdd_bot" ∨ (∃ e, IsT t e ∧ x = litN e (keyOf t)) ∨
      ∃ (j : Int) (e : Term) (c u d : Bool), IsT t e ∧
        x = .tuple #[.integer j, litN e (keyOf t), bt c, bt u, bt d] := by
  have btc : ∀ y : Term, y = .atom "bdd_top" ∨ y = .atom "bdd_bot" → ∃ b, y = bt b := by
    rintro y (rfl | rfl)
    · exact ⟨Bool.true, rfl⟩
    · exact ⟨Bool.false, rfl⟩
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · obtain ⟨e, he, h⟩ := Bdd.leaf_iff.mp wx
    exact Or.inr (Or.inr (Or.inl ⟨e, he, h⟩))
  · unfold Bdd at wx
    obtain ⟨-, hl, wc, wu, wd⟩ := wx
    obtain ⟨cb, rfl⟩ := btc c (pure_child hl wc)
    obtain ⟨ub, rfl⟩ := btc u (pure_child hl wu)
    obtain ⟨db, rfl⟩ := btc d (pure_child hl wd)
    obtain ⟨e, he, rfl⟩ := hl
    exact Or.inr (Or.inr (Or.inr ⟨h, e, cb, ub, db, he, rfl⟩))

theorem tuple_walk_top_leaf (d : Dispatcher) (k : Int) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil
      (.tuple #[.integer k, .atom "open", .nil]) S = .ok (.atom "false") := by
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
    Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil, Erlang.erlang.«>=/2»]

/-- The emptiness of the tuple field of a node expansion is decided, whatever was seen. -/
theorem pure_tuple_empty {t x : Term} (fx : OField (PureLit t) x) (S : List (Term × Term)) :
    ∃ b, ∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom b) := by
  by_cases seen : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 = .eq)) = Bool.true
  · refine ⟨Bool.true, fun m _ => ?_⟩
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true, boolAtom]
  have fresh : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 = .eq)) = Bool.false := by
    simpa using seen
  obtain ⟨S', put⟩ : ∃ S', Erlang.maps.«put/3» (.cons (.atom "tuple") x) (.atom "true") (.map S) = .ok (.map S') :=
    ⟨_, by simp [Erlang.maps.«put/3»]; rfl⟩
  have walk : ∀ m, Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) (.tuple #[.atom "open", .nil]) .nil x (.map S') := by
    intro m
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, put]
  have two : ∀ m, 2 ≤ m → ∃ m', m = m' + 2 := fun m hm => ⟨m - 2, by omega⟩
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨Bool.false, fun m _ => by rw [walk]; exact tuple_walk_top_leaf _ _ _⟩
  rcases pure_shape wx with rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · exact ⟨Bool.false, fun m _ => by rw [walk]; exact tuple_walk_top _ _⟩
  · exact ⟨Bool.true, fun m _ => by rw [walk]; exact tuple_walk_bot _ _ _ _⟩
  · exact ⟨idIn (refOf t) S', fun m hm => by
      obtain ⟨m', rfl⟩ := two m hm; rw [walk]; exact walk_leaf_node he.node _ m' S'⟩
  · exact ⟨(!c || idIn (refOf t) S') && !u && !d, fun m hm => by
      obtain ⟨m', rfl⟩ := two m hm; rw [walk]; exact walk_node_node he.node _ _ m' S' c u d⟩

/-! Node expansions and their combinations with basic types: plain operations keep them, and their emptiness is
decided. -/

/-- Fields of node expansions and their combinations with basic types: basic fields, or a tuple field of
expansion literals. -/
def FieldP (t : Term) (name : String) (w : Term) : Prop := FieldOk name w ∨ (name = "tuple" ∧ OField (PureLit t) w)

/-- Maps of fields of node expansions. -/
structure PureMap (t : Term) (M : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup M q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
    q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map"
  fields : ∀ name w, mapLookup M (.atom name) = some w → FieldP t name w

theorem PureMap.static {t : Term} {M : List (Term × Term)} (p : PureMap t M) :
    mapLookup M (.atom "dynamic") = Option.none := by
  cases h : mapLookup M (.atom "dynamic") with
  | none => rfl
  | some w => rcases p.keys _ (by rw [h]; rfl) with e | e | e | e | e | e <;> simp at e

theorem PureMap.atomKey {t : Term} {M : List (Term × Term)} (p : PureMap t M) {q w : Term}
    (h : mapLookup M q = some w) : ∃ name, q = .atom name := by
  rcases p.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem Basic.pure {t : Term} {M : List (Term × Term)} (b : Basic M) : PureMap t M :=
  ⟨b.keys, fun _ _ h => Or.inl (b.field h)⟩

theorem fieldP_tuple {t w : Term} (h : FieldP t "tuple" w) : OField (PureLit t) w := by
  rcases h with f | ⟨-, f⟩
  · rcases f with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · simp at e
    · simp at e
    · simp [topValue] at tv; subst tv; exact Or.inl ⟨_, rfl⟩
  · exact f

theorem fieldP_other {t w : Term} {name : String} (h : FieldP t name w) (nt : name ≠ "tuple") : FieldOk name w := by
  rcases h with f | ⟨e, -⟩
  · exact f
  · exact absurd e nt

theorem interP (t : Term) (name : String) (x y : Term) (hx : FieldP t name x) (hy : FieldP t name y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → FieldP t name r) := by
  by_cases nt : name = "tuple"
  · subst nt
    obtain ⟨w, run, k⟩ := pure_inter (fieldP_tuple hx) (fieldP_tuple hy)
    exact ⟨w, fun d => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun kw => Or.inr ⟨rfl, k kw⟩⟩
  · obtain ⟨r, run, ok, -⟩ := inter_key name x y (fieldP_other hx nt) (fieldP_other hy nt)
    exact ⟨r, run, fun kw => Or.inl (ok kw)⟩

theorem diffP (t : Term) (name : String) (x y : Term) (hx : FieldP t name x) (hy : FieldP t name y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → FieldP t name r) := by
  by_cases nt : name = "tuple"
  · subst nt
    obtain ⟨w, run, k⟩ := pure_diff (fieldP_tuple hx) (fieldP_tuple hy)
    exact ⟨w, fun d => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun kw => Or.inr ⟨rfl, k kw⟩⟩
  · obtain ⟨r, run, ok, -⟩ := diff_key name x y (fieldP_other hx nt) (fieldP_other hy nt)
    exact ⟨r, run, fun kw => Or.inl (ok kw)⟩

theorem unionP (t : Term) (name : String) (x y : Term) (hx : FieldP t name x) (hy : FieldP t name y) :
    ∃ r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y = .ok r) ∧ FieldP t name r := by
  by_cases nt : name = "tuple"
  · subst nt
    obtain ⟨w, run, k⟩ := pure_union (fieldP_tuple hx) (fieldP_tuple hy)
    exact ⟨w, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], Or.inr ⟨rfl, k⟩⟩
  · obtain ⟨r, run, ok⟩ := fieldok_union name (fieldP_other hx nt) (fieldP_other hy nt)
    exact ⟨r, run, Or.inl ok⟩

theorem inter_pure (t : Term) (A B : List (Term × Term)) (bA : PureMap t A) (bB : PureMap t B) :
    ∃ C, (∀ m, 0 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.map A) (.map B) =
      .ok (.map C)) ∧ PureMap t C := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (D 0) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have ik := fun name x y (hx : mapLookup A (.atom name) = some x) (hy : mapLookup B (.atom name) = some y) =>
    interP t name x y (bA.fields _ _ hx) (bB.fields _ _ hy)
  have gval : ∀ name x y r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom name) x y = .ok r) →
      g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  obtain ⟨I, C, run, lookI, lookC⟩ := inter_uniform 0 A B bA.static bB.static g (by
    intro q x y hx hy m _
    obtain ⟨name, key⟩ := bA.atomKey hx
    subst key
    obtain ⟨r, run, -⟩ := ik name x y hx hy
    rw [run, gval _ _ _ _ run])
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup A (.atom name), mapLookup B (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    intro name
    rw [lookC, find_atom, lookI, find_atom]
    cases mapLookup A (.atom name) <;> cases hR : mapLookup B (.atom name) <;> simp [hR]
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have hI := find_isSome I q hit
      rw [lookI] at hI
      split at hI
      · rename_i e' hit'
        exact find_isSome A q hit'
      · simp at hI
    · simp at some
  refine ⟨C, run, ⟨fun q h => bA.keys q (keys q h), fun name w h => ?_⟩⟩
  rw [look] at h
  cases hx : mapLookup A (.atom name) <;> cases hy : mapLookup B (.atom name) <;> rw [hx, hy] at h <;>
    try simp at h
  rename_i x y
  obtain ⟨r, run, ok⟩ := ik name x y hx hy
  simp only [gval _ _ _ _ run] at h
  obtain ⟨k, rfl⟩ := h
  exact ok k


/-- Folding the difference of maps of fields of node expansions gives such a map. -/
theorem fold_pure (t : Term) (A B C : List (Term × Term)) (bA : PureMap t A) (g : Term → Term → Term → Term)
    (lookC : ∀ q, mapLookup C q =
      match (mapEntries B).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | some e => (mapLookup A e.1).bind fun v₁ =>
          if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else Option.none
      | none => mapLookup A q)
    (dk : ∀ name x y, mapLookup A (.atom name) = some x → mapLookup B (.atom name) = some y →
      kept (.atom name, g (.atom name) x y) = Bool.true → FieldP t name (g (.atom name) x y)) :
    PureMap t C := by
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup B (.atom name) with
      | some y => (mapLookup A (.atom name)).bind fun x =>
          if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | none => mapLookup A (.atom name) := by
    intro name
    rw [lookC, find_atom]
    cases mapLookup B (.atom name) <;> rfl
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have same : compareExact (fuel q e.1) q e.1 = .eq := by simpa using List.find?_some hit
      rw [mapLookup_congr same]
      cases h : mapLookup A e.1 <;> simp_all
    · exact some
  refine ⟨fun q h => bA.keys q (keys q h), fun name w h => ?_⟩
  rw [look] at h
  cases hy : mapLookup B (.atom name) with
  | none => rw [hy] at h; exact bA.fields _ _ h
  | some y =>
    rw [hy] at h
    cases hx : mapLookup A (.atom name) with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Option.bind_some] at h
      split at h
      · rename_i k; cases h; exact dk name x y hx hy k
      · cases h

theorem diff_pure (t : Term) (left : Term) (A B : List (Term × Term)) (bA : PureMap t A) (bB : PureMap t B)
    (hleft : left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧
      Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) :
    ∃ C, (∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) left (.map B) = .ok (.map C)) ∧
      PureMap t C := by
  by_cases emptyB : B = []
  · subst emptyB
    rcases hleft with rfl | ⟨-, ne, -⟩
    rotate_left
    · exact absurd rfl ne
    refine ⟨A, fun m _ => ?_, bA⟩
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2»]
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (D 0) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have gval : ∀ name x y r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y = .ok r) →
      g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  have fold := fun depth => difference_fold depth (.function false "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries B) A (mapEntries_distinct B) (by
      intro e member v₁ found
      have hy := mapLookup_of_mem_mapEntries member
      obtain ⟨name, key⟩ := bA.atomKey found
      rw [key] at found hy ⊢
      obtain ⟨r, run, -⟩ := diffP t name v₁ e.2 (bA.fields _ _ found) (bB.fields _ _ hy)
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure, run, gval _ _ _ _ run])
  obtain ⟨C, -, lookC, eqC⟩ := fold 0
  refine ⟨C, fun m hm => ?_, fold_pure t A B C bA g lookC fun name x y hx hy k => by
    obtain ⟨r, run, ok⟩ := diffP t name x y (bA.fields _ _ hx) (bB.fields _ _ hy)
    rw [gval _ _ _ _ run] at k ⊢; exact ok k⟩
  obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 2 := ⟨m - 2, by omega⟩
  obtain ⟨C', fold', -, eq'⟩ := fold depth
  rw [eqC, ← eq']
  rcases hleft with rfl | ⟨rfl, -, term⟩
  · unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map bA.static, static_map bB.static, emptyB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3»]
    simpa using fold'
  · unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map bB.static, emptyB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3», term]
    simpa using fold'

theorem union_pure (t : Term) (A B : List (Term × Term)) (bA : PureMap t A) (bB : PureMap t B) :
    ∃ U, (∀ m, 1 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B) = .ok (.map U)) ∧
      PureMap t U := by
  let g : Term → Term → Term → Term := fun q x y =>
    match Elixir.Module.Types.Descr.«bare_union/3» (D 1) q x y with | .ok w => w | .error _ => .nil
  have gval : ∀ name x y r, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom name) x y =
      .ok r) → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h 0]
  have atomKey : ∀ {X : List (Term × Term)}, PureMap t X → ∀ {q w : Term}, mapLookup X q = some w →
      ∃ name, q = .atom name := fun bX q w h => by
    rcases bX.keys q (by rw [h]; rfl) with e | e | e | e | e | e <;> exact ⟨_, e⟩
  have calls : ∀ q x y, mapLookup A q = some x → mapLookup B q = some y → ∀ m, 1 ≤ m →
      Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y = .ok (g q x y) := by
    intro q x y hx hy m hm
    obtain ⟨name, rfl⟩ := atomKey bA hx
    obtain ⟨r, run, -⟩ := unionP t name x y (bA.fields _ _ hx) (bB.fields _ _ hy)
    obtain ⟨n, rfl, -⟩ := succ_of_le hm
    rw [run, gval _ _ _ _ run]
  obtain ⟨U, run, look⟩ := union_uniform 1 A B bA.static bB.static (fun q h => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h; exact atomKey bB hw) g calls
  refine ⟨U, run, ⟨fun q h => ?_, fun name w h => ?_⟩⟩
  · cases hb : mapLookup B q with
    | none => rw [(look q).1 hb] at h; exact bA.keys q h
    | some y => exact bB.keys q (by simp [hb])
  · cases hb : mapLookup B (.atom name) with
    | none => rw [(look _).1 hb] at h; exact bA.fields _ _ h
    | some y =>
      cases ha : mapLookup A (.atom name) with
      | none => rw [(look _).2.1 y hb ha] at h; rw [← Option.some.inj h]; exact bB.fields _ _ hb
      | some x =>
        rw [(look _).2.2 x y ha hb] at h
        rw [← Option.some.inj h]
        obtain ⟨r, run, ok⟩ := unionP t name x y (bA.fields _ _ ha) (bB.fields _ _ hb)
        rw [gval _ _ _ _ run]
        exact ok


theorem empty_pure {t : Term} {M : List (Term × Term)} (pM : PureMap t M) (S : List (Term × Term)) :
    ∃ b, ∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.map M) (.map S) = .ok (boolAtom b) := by
  by_cases nonempty : M = []
  · subst nonempty
    exact ⟨Bool.true, fun m _ => by simpa [boolAtom] using empty_none_seen (D m) (.map S)⟩
  obtain ⟨tb, ht⟩ : ∃ tb, ∀ m, 2 ≤ m → ∀ x, mapLookup M (.atom "tuple") = some x →
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom tb) := by
    cases hx : mapLookup M (.atom "tuple") with
    | none => exact ⟨Bool.false, fun m _ x h => by cases h⟩
    | some x =>
      obtain ⟨b, hb⟩ := pure_tuple_empty (fieldP_tuple (pM.fields _ _ hx)) S
      exact ⟨b, fun m hm x' h => by cases h; exact hb m hm⟩
  obtain ⟨mb, hm⟩ := map_top_bool S
  have static : mapLookup M (.atom "dynamic") = Option.none := pM.static
  have top : ∀ name, name ≠ "bitmap" → name ≠ "atom" → name ≠ "tuple" → ∀ w, mapLookup M (.atom name) = some w →
      topValue name = some w := fun name n₁ n₂ n₃ w h => by
    rcases fieldP_other (pM.fields _ _ h) n₃ with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, tv⟩
    · exact absurd e n₁
    · exact absurd e n₂
    · exact tv
  have mapV := top "map" (by decide) (by decide) (by decide)
  have listV := top "list" (by decide) (by decide) (by decide)
  have funV := top "fun" (by decide) (by decide) (by decide)
  simp only [topValue] at mapV listV funV
  refine ⟨!(mapLookup M (.atom "atom")).isSome && !(mapLookup M (.atom "bitmap")).isSome &&
    (!(mapLookup M (.atom "tuple")).isSome || tb) && (!(mapLookup M (.atom "map")).isSome || mb) &&
    !(mapLookup M (.atom "list")).isSome && !(mapLookup M (.atom "fun")).isSome, fun m hm' => ?_⟩
  have nL := list_top_nonempty (D m) (.map S)
  have nF := fun_top_nonempty (D m) (.map S)
  have mB := hm (D m)
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
  cases ha : mapLookup M (.atom "atom") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso, boolAtom]
  | none =>
  cases hb : mapLookup M (.atom "bitmap") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  | none =>
  have ab : ∀ x y : Bool,
      Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (boolAtom y)) Bool.true = .ok (boolAtom (x && y)) := by
    intro x y; cases x <;> cases y <;> rfl
  have abT : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "true")) Bool.true = .ok (boolAtom x) := by
    intro x; cases x <;> rfl
  have abF : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "false")) Bool.true = .ok (.atom "false") := by
    intro x; cases x <;> rfl
  have bt : boolAtom Bool.true = .atom "true" := rfl
  have bf : boolAtom Bool.false = .atom "false" := rfl
  have val : ∀ {key : String} {v : Term}, (∀ w, mapLookup M (.atom key) = some w → some v = some w) →
      mapLookup M (.atom key) = Option.none ∨ mapLookup M (.atom key) = some v := by
    intro key v h
    cases e : mapLookup M (.atom key) with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (by rw [Option.some.inj (h w e)])
  have tupleV : mapLookup M (.atom "tuple") = Option.none ∨ ∃ x, mapLookup M (.atom "tuple") = some x ∧
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom tb) := by
    cases hx : mapLookup M (.atom "tuple") with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl, ht m hm' x hx⟩
  rcases tupleV with htu | ⟨x, htu, tB⟩ <;> rcases val mapV with hma | hma <;>
    rcases val listV with hl | hl <;> rcases val funV with hf | hf <;>
    simp [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», abT, abF, bt, bf, ha, hb, htu, hma, hl, hf,
      mB, nL, nF]
  all_goals first
    | (cases tb <;> cases mb <;> simp [tB, boolAtom, Lynx.Except.andAlso] <;> rfl)
    | (apply nonempty
       apply nil_of_lookup_none
       intro q
       cases h : mapLookup M q with
       | none => rfl
       | some w =>
         rcases pM.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)

/-- The node `t`, its expansion, and their combinations with basic types. -/
def Pure (t a : Term) : Prop := a = .atom "term" ∨ IsT t a ∨ ∃ M, a = .map M ∧ PureMap t M

theorem expN_pure {t e : Term} (he : IsT t e) : PureMap t
    [(.atom "tuple", litN e (keyOf t)), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] := by
  refine ⟨fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?, equalExact_eq_decide] at h
    by_cases t₁ : Term.compareExact (Term.fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₁)))))
    · by_cases t₂ : Term.compareExact (Term.fuel q (.atom "atom")) q (.atom "atom") = .eq
      · exact Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₂))
      · simp [t₁, t₂] at h
  · by_cases t₁ : name = "tuple"
    · subst t₁
      simp [mapLookup] at h
      subst h
      exact Or.inr ⟨rfl, Or.inr (Bdd.leaf_iff.mpr ⟨e, he, rfl⟩)⟩
    · by_cases t₂ : name = "atom"
      · subst t₂
        simp [mapLookup] at h
        subst h
        exact Or.inl (Or.inr (Or.inl ⟨rfl, ⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil", by
          simp [amemV, mapLookup]⟩))
      · simp [mapLookup, t₁, t₂] at h

theorem node_ne_term {t e : Term} (he : IsT t e) : e ≠ .atom "term" := by
  obtain ⟨S, rfl, -⟩ := he.node; simp

theorem expN_ne_term (e : Term) (k : Int) : expN e k ≠ .atom "term" := by simp [expN]

theorem pure_none (t : Term) : Pure t (.map []) :=
  Or.inr (Or.inr ⟨[], rfl, ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩⟩)

/-- Intersections of maps of the class, with nodes replaced by their expansions. -/
theorem pure_inter_maps {t : Term} {a b : Term} (ha : IsT t a ∨ ∃ A, a = .map A ∧ PureMap t A)
    (hb : IsT t b ∨ ∃ B, b = .map B ∧ PureMap t B) :
    ∃ C, (∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok (.map C)) ∧ PureMap t C := by
  obtain ⟨A, pA, ea⟩ : ∃ A, PureMap t A ∧ ∀ m b, b ≠ .atom "term" →
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) b := by
    rcases ha with ha | ⟨A, rfl, pA⟩
    · exact ⟨_, expN_pure ha, fun m b hb => inter_node_l ha.node m (expand_isT ha m) b hb⟩
    · exact ⟨A, pA, fun _ _ _ => rfl⟩
  obtain ⟨B, pB, eb⟩ : ∃ B, PureMap t B ∧ ∀ m, b ≠ .atom "term" ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) b =
        Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) (.map B) := by
    rcases hb with hb | ⟨B, rfl, pB⟩
    · exact ⟨_, expN_pure hb, fun m => ⟨node_ne_term hb, inter_node_r hb.node m (expand_isT hb m) _ (by simp)⟩⟩
    · exact ⟨B, pB, fun _ => ⟨by simp, rfl⟩⟩
  obtain ⟨C, run, pC⟩ := inter_pure t A B pA pB
  refine ⟨C, fun m hm => ?_, pC⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [ea m b (eb m).1, (eb m).2, run _ (by omega)]

theorem pureOk (t : Term) : ElemOk (Pure t) 2 := by
  refine ⟨Or.inl rfl, fun {a b} ha hb => ?_, fun {a} ha S => ?_, pure_none t, by decide⟩
  · rcases ha with rfl | ha'
    · exact ⟨b, hb, fun _ _ => by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl⟩
    rcases hb with rfl | hb'
    · exact ⟨a, Or.inr ha', fun m _ => inter_term_right _ _⟩
    obtain ⟨C, run, pC⟩ := pure_inter_maps ha' hb'
    exact ⟨_, Or.inr (Or.inr ⟨C, rfl, pC⟩), run⟩
  · rcases ha with rfl | ha | ⟨M, rfl, pM⟩
    · exact ⟨Bool.false, fun m _ => by rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl⟩
    · exact ⟨_, fun m hm => by
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact empty_node ha.node m S⟩
    · exact empty_pure pM S

theorem pureDiff (t : Term) : ElemDiff (Pure t) 2 := by
  refine ⟨fun {a b} ha hb => ?_⟩
  rcases hb with rfl | hb'
  · exact ⟨_, pure_none t, fun m _ => diff_term_right _ _⟩
  -- The right type as a map.
  obtain ⟨B, pB, eb⟩ : ∃ B, PureMap t B ∧ ∀ m a,
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a (.map B) := by
    rcases hb' with hb | ⟨B, rfl, pB⟩
    · exact ⟨_, expN_pure hb, fun m a => diff_node_r hb.node m (expand_isT hb m) a⟩
    · exact ⟨B, pB, fun _ _ => rfl⟩
  have succ : ∀ m, 2 ≤ m → ∃ m', m = m' + 1 ∧ 1 ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  -- The left type as a map, or the result as the left type.
  have mapCase : ∀ {left : Term} (A : List (Term × Term)), PureMap t A →
      (left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧ Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) →
      ∃ c, Pure t c ∧ ∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) left (.map B) = .ok c :=
    fun A pA hl => let ⟨C, run, pC⟩ := diff_pure t _ A B pA pB hl; ⟨_, Or.inr (Or.inr ⟨C, rfl, pC⟩), run⟩
  obtain ⟨c, hc, run⟩ : ∃ c, Pure t c ∧ ∀ m, 2 ≤ m →
      Elixir.Module.Types.Descr.«bare_difference/2» (D m) a (.map B) = .ok c := by
    by_cases empty : B = []
    · subst empty
      refine ⟨a, ha, fun m _ => ?_⟩
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Erlang.erlang.«==/2»]
    rcases ha with rfl | ha | ⟨A, rfl, pA⟩
    · obtain ⟨T, term, -⟩ := unfolded_term_fields
      exact mapCase T (Basic.pure (term_basic term).1) (Or.inr ⟨rfl, empty, term⟩)
    · obtain ⟨c, hc, run⟩ := mapCase _ (expN_pure ha) (Or.inl rfl)
      refine ⟨c, hc, fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ m hm
      rw [diff_node_l ha.node m' (expand_isT ha m') (.map B) (by simp) (map_ne_none empty)]
      exact run _ (by omega)
    · exact mapCase A pA (Or.inl rfl)
  exact ⟨c, hc, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m hm; rw [eb]; exact run _ hm⟩

theorem union_any_term (d : Dispatcher) (a : Term) :
    Elixir.Module.Types.Descr.«bare_union/2» d a (.atom "term") = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»; split <;> simp_all

theorem empty_any_node {t e : Term} (he : IsT t e) (m : Nat) :
    Elixir.Module.Types.Descr.«empty?/1» (D (m + 1)) e = .ok (.atom "false") := by
  obtain ⟨S, rfl, -⟩ := he.node
  have := empty_node he.node m []
  unfold Elixir.Module.Types.Descr.«empty?/1»
  simpa [boolAtom] using this

/-- The maps of the class, with nodes replaced by their expansions, for `subtype?/2` and `disjoint?/2`. -/
def PureC (t a : Term) : Prop := a = .atom "term" ∨ ∃ M, a = .map M ∧ PureMap t M

theorem pure_sub_disj (t : Term) :
    (∀ {a b}, PureC t a → PureC t b → BoolAt 2 (fun m => Elixir.Module.Types.Descr.«subtype?/2» (D m) a b)) ∧
      (∀ {a b}, PureC t a → PureC t b → BoolAt (2 + 6) (fun m => Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b)) := by
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  exact class_sub_disj (PureC t) (FieldP t) (PureMap t) 2 (fun ha => ha) ⟨T, term, Basic.pure (term_basic term).1⟩
    (fun bA => bA.static) (fun bA => bA.keys) (fun bA _ _ h => bA.fields _ _ h)
    (fun name x y hx hy => by
      obtain ⟨r, run, ok⟩ := diffP t name x y hx hy
      exact ⟨r, fun m _ => run _, ok⟩)
    (fun name x y hx hy => by
      obtain ⟨r, run, ok⟩ := interP t name x y hx hy
      exact ⟨r, fun m _ => run _, ok⟩)
    (fun name x hx => by
      by_cases nt : name = "tuple"
      · subst nt
        obtain ⟨b, hb⟩ := pure_tuple_empty (fieldP_tuple hx) []
        exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using hb m hm⟩
      · exact ⟨Bool.false, fun m _ => fieldok_empty (D m) name (fieldP_other hx nt)⟩)
    (fun {a} ha => by
      rcases ha with rfl | ⟨A, rfl, pA⟩
      · exact ⟨Bool.false, fun m _ => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; rfl⟩
      · obtain ⟨b, hb⟩ := empty_pure pA []
        exact ⟨b, fun m hm => by dsimp only; unfold Elixir.Module.Types.Descr.«empty?/1»; exact hb m hm⟩)

theorem disj_term_l (d : Dispatcher) (b : Term) :
    Elixir.Module.Types.Descr.«disjoint?/2» d (.atom "term") b = Elixir.Module.Types.Descr.«empty?/1» d b := by
  unfold Elixir.Module.Types.Descr.«disjoint?/2»; rfl

theorem disj_term_r (d : Dispatcher) (a : Term) :
    Elixir.Module.Types.Descr.«disjoint?/2» d a (.atom "term") = Elixir.Module.Types.Descr.«empty?/1» d a := by
  unfold Elixir.Module.Types.Descr.«disjoint?/2»; split <;> simp_all

theorem pureFun (t : Term) : ElemFun (Pure t) 8 := by
  obtain ⟨sub, disj⟩ := pure_sub_disj t
  have succ : ∀ m, 2 ≤ m → ∃ m', m = m' + 1 ∧ 1 ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  have expC : ∀ {e}, IsT t e → PureC t (expN e (keyOf t)) := fun he => Or.inr ⟨_, rfl, expN_pure he⟩
  refine ⟨fun {a} ha => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_⟩
  · rcases ha with rfl | ha | ⟨A, rfl, pA⟩
    · exact Or.inl rfl
    · obtain ⟨S, rfl, -⟩ := ha.node; exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
    · exact Or.inr (Or.inl ⟨A, rfl, pA.static⟩)
  · -- Unions.
    rcases ha with rfl | ha' | ⟨A, rfl, pA⟩
    · exact ⟨_, Or.inl rfl, fun m _ => union_term_l _ _⟩
    rotate_left
    · rcases hb with rfl | hb' | ⟨B, rfl, pB⟩
      · exact ⟨_, Or.inl rfl, fun m _ => union_any_term _ _⟩
      · by_cases none : A = []
        · subst none
          refine ⟨b, Or.inr (Or.inl hb'), fun m _ => ?_⟩
          obtain ⟨S, rfl, -⟩ := hb'.node
          unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
        obtain ⟨U, run, pU⟩ := union_pure t A _ pA (expN_pure hb')
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => by
          obtain ⟨m', rfl, -⟩ := succ m (by omega)
          rw [union_node_r hb'.node m' (expand_isT hb' m') _ (by simp) (map_ne_none none)]; exact run _ (by omega)⟩
      · obtain ⟨U, run, pU⟩ := union_pure t A B pA pB
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => run m (by omega)⟩
    · rcases hb with rfl | hb' | ⟨B, rfl, pB⟩
      · exact ⟨_, Or.inl rfl, fun m _ => union_any_term _ _⟩
      · obtain ⟨U, run, pU⟩ := union_pure t _ _ (expN_pure ha') (expN_pure hb')
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => by
          obtain ⟨m', rfl, -⟩ := succ m (by omega)
          rw [union_node_l ha'.node m' (expand_isT ha' m') _ (node_ne_term hb') (node_ne_none hb'.node),
            union_node_r hb'.node m' (expand_isT hb' m') _ (expN_ne_term _ _) (expN_ne_none _ _)]
          exact run _ (by omega)⟩
      · by_cases none : B = []
        · subst none
          refine ⟨a, Or.inr (Or.inl ha'), fun m _ => ?_⟩
          have := node_ne_none ha'.node
          obtain ⟨S, rfl, -⟩ := ha'.node
          unfold Elixir.Module.Types.Descr.«bare_union/2»; simp_all [Erlang.erlang.«==/2»]
        obtain ⟨U, run, pU⟩ := union_pure t _ B (expN_pure ha') pB
        exact ⟨_, Or.inr (Or.inr ⟨U, rfl, pU⟩), fun m hm => by
          obtain ⟨m', rfl, -⟩ := succ m (by omega)
          rw [union_node_l ha'.node m' (expand_isT ha' m') _ (by simp) (map_ne_none none)]
          exact run _ (by omega)⟩
  · -- Inclusions: nodes behave as their expansions.
    obtain ⟨A', cA, ea⟩ : ∃ A', PureC t A' ∧ ∀ m' b, Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A' b := by
      rcases ha with rfl | ha | ⟨A, rfl, pA⟩
      · exact ⟨_, Or.inl rfl, fun _ _ => rfl⟩
      · exact ⟨_, expC ha, fun m' b => sub_node_l ha.node m' (expand_isT ha m') b⟩
      · exact ⟨_, Or.inr ⟨A, rfl, pA⟩, fun _ _ => rfl⟩
    obtain ⟨B', cB, eb⟩ : ∃ B', PureC t B' ∧ ∀ m' a, Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a B' := by
      rcases hb with rfl | hb | ⟨B, rfl, pB⟩
      · exact ⟨_, Or.inl rfl, fun _ _ => rfl⟩
      · exact ⟨_, expC hb, fun m' a => sub_node_r hb.node m' (expand_isT hb m') a⟩
      · exact ⟨_, Or.inr ⟨B, rfl, pB⟩, fun _ _ => rfl⟩
    obtain ⟨s, hs⟩ := sub cA cB
    exact ⟨s, fun m hm => by
      obtain ⟨m', rfl, -⟩ := succ m (by omega); dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩
  · -- Disjointness: the top type checks emptiness, and nodes behave as their expansions otherwise.
    have emptyOf : ∀ {a}, Pure t a → BoolAt 8 (fun m => Elixir.Module.Types.Descr.«empty?/1» (D m) a) := by
      intro a ha
      rcases ha with rfl | ha | ⟨A, rfl, pA⟩
      · exact ⟨Bool.false, fun m _ => by unfold Elixir.Module.Types.Descr.«empty?/1»; rfl⟩
      · exact ⟨Bool.false, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m (by omega); exact empty_any_node ha m'⟩
      · obtain ⟨b, hb⟩ := empty_pure pA []
        exact ⟨b, fun m hm => by unfold Elixir.Module.Types.Descr.«empty?/1»; exact hb m (by omega)⟩
    by_cases bt : b = .atom "term"
    · subst bt
      obtain ⟨s, hs⟩ := emptyOf ha
      exact ⟨s, fun m hm => by dsimp only; rw [disj_term_r]; exact hs m hm⟩
    by_cases at' : a = .atom "term"
    · subst at'
      obtain ⟨s, hs⟩ := emptyOf hb
      exact ⟨s, fun m hm => by dsimp only; rw [disj_term_l]; exact hs m hm⟩
    have stat : ∀ {x}, Pure t x → ∀ X, x = .map X → mapLookup X (.atom "dynamic") = none := by
      intro x hx X e
      rcases hx with rfl | hx | ⟨A, rfl, pA⟩
      · cases e
      · obtain ⟨S, rfl, -⟩ := hx.node; cases e
      · cases e; exact pA.static
    obtain ⟨A', cA, sA, nt, ea⟩ : ∃ A', PureC t A' ∧ (∀ X, A' = .map X → mapLookup X (.atom "dynamic") = none) ∧
        A' ≠ .atom "term" ∧ ∀ m', Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) a b =
          Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A' b := by
      rcases ha with rfl | ha | ⟨A, rfl, pA⟩
      · exact absurd rfl at'
      · exact ⟨_, expC ha, fun X e => by simp [expN] at e; subst e; simp [mapLookup], expN_ne_term _ _,
          fun m' => disj_node_l ha.node m' (expand_isT ha m') b bt (stat hb)⟩
      · exact ⟨_, Or.inr ⟨A, rfl, pA⟩, fun X e => by cases e; exact pA.static, by simp, fun _ => rfl⟩
    obtain ⟨B', cB, eb⟩ : ∃ B', PureC t B' ∧ ∀ m', Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A' b =
        Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A' B' := by
      rcases hb with rfl | hb | ⟨B, rfl, pB⟩
      · exact absurd rfl bt
      · exact ⟨_, expC hb, fun m' => disj_node_r hb.node m' (expand_isT hb m') A' nt sA⟩
      · exact ⟨_, Or.inr ⟨B, rfl, pB⟩, fun _ => rfl⟩
    obtain ⟨s, hs⟩ := disj cA cB
    exact ⟨s, fun m hm => by
      obtain ⟨m', rfl, -⟩ := succ m (by omega); dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩

/-- Fields of node expansions decide their emptiness under any `seen`. -/
theorem fieldP_empty {t x : Term} {name : String} (hx : FieldP t name x) (S : List (Term × Term)) :
    BoolAt 2 (fun m => Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S)) := by
  by_cases nt : name = "tuple"
  · subst nt
    obtain ⟨b, hb⟩ := pure_tuple_empty (fieldP_tuple hx) S
    exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using hb m hm⟩
  rcases fieldP_other hx nt with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨nb, na, tx⟩
  · exact ⟨Bool.false, fun m _ => by dsimp only; rw [Elixir.Module.Types.Descr.«empty_key?/3».eq_def]; rfl⟩
  · exact ⟨Bool.false, fun m _ => by dsimp only; rw [Elixir.Module.Types.Descr.«empty_key?/3».eq_def]; rfl⟩
  by_cases f : name = "fun"
  · subst f; simp [topValue] at tx; subst tx
    exact ⟨Bool.false, fun m _ => by
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using fun_top_nonempty (D m) (.map S)⟩
  by_cases l : name = "list"
  · subst l; simp [topValue] at tx; subst tx
    exact ⟨Bool.false, fun m _ => by
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using list_top_nonempty (D m) (.map S)⟩
  by_cases mp : name = "map"
  · subst mp; simp [topValue] at tx; subst tx
    obtain ⟨mb, hmb⟩ := map_top_bool S
    exact ⟨mb, fun m _ => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using hmb (D m)⟩
  · simp [topValue] at tx

theorem node_nonmap {t a : Term} (ha : IsT t a) : ∀ X, a ≠ .map X := by
  obtain ⟨S, rfl, -⟩ := ha.node
  intro X h; cases h

theorem pureDisj (t : Term) : ElemDisj (Pure t) 5 := by
  have pops := pureOk t
  have viaInter : ∀ {a b}, Pure t a → Pure t b → ∀ S : List (Term × Term), (∀ d,
      Elixir.Module.Types.Descr.«disjoint_seen?/3» d a b (.map S) =
        (Elixir.Module.Types.Descr.«bare_intersection/2» d a b).bind
          fun c => Elixir.Module.Types.Descr.«empty_seen?/2» d c (.map S)) →
      BoolAt (5 + 3) (fun m => Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) a b (.map S)) := by
    intro a b ha hb S eq
    obtain ⟨c, hc, rc⟩ := pops.inter ha hb
    obtain ⟨e, he⟩ := pops.empty hc S
    exact ⟨e, fun m hm => by dsimp only; rw [eq, rc m (by omega)]; exact he m (by omega)⟩
  refine ⟨fun {a b} ha hb S => ?_⟩
  rcases ha with rfl | ha' | ⟨A, rfl, pA⟩
  · exact viaInter (Or.inl rfl) hb S fun d => disj_seen_term_l d b _
  · exact viaInter (Or.inr (Or.inl ha')) hb S fun d => disj_seen_nonmap_l d b _ (node_nonmap ha')
  rcases hb with rfl | hb' | ⟨B, rfl, pB⟩
  · exact viaInter (Or.inr (Or.inr ⟨A, rfl, pA⟩)) (Or.inl rfl) S fun d => disj_seen_term_r d _ _
  · exact viaInter (Or.inr (Or.inr ⟨A, rfl, pA⟩)) (Or.inr (Or.inl hb')) S
      fun d => disj_seen_nonmap_r d _ _ (node_nonmap hb')
  obtain ⟨b, hb⟩ := nondisj_fields 2 (FieldP t) A B (.map S) pA.keys pB.keys (fun _ _ h => pA.fields _ _ h)
    (fun _ _ h => pB.fields _ _ h)
    (fun name x y hx hy => by
      obtain ⟨r, run, ok⟩ := interP t name x y hx hy
      exact ⟨r, fun m _ => run _, ok⟩)
    (fun name x hx => fieldP_empty hx S)
  refine ⟨!b, fun m hm => ?_⟩
  have e := hb m (by omega)
  dsimp only at e ⊢
  rw [disj_seen_maps _ _ _ _ pA.static pB.static, e]
  cases b <;> rfl

section
variable {t : Term} {C : Term → Prop} {K : Nat}

/-! Classes with the node: operations on the node compute on its expansion, which the class holds. -/

/-- A class of maps with the node `t`. -/
def WithNode (t : Term) (C : Term → Prop) (a : Term) : Prop := C a ∨ IsT t a

theorem addOk (_hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ X, a = .map X)
    (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (ops : ElemOk C K) : ElemOk (WithNode t C) (K + 1) := by
  have succ : ∀ m, K + 1 ≤ m → ∃ m', m = m' + 1 ∧ K ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  -- The left and right types as types of the class.
  refine ⟨Or.inl ops.term, fun {a b} ha hb => ?_, fun {a} ha S => ?_, Or.inl ops.none, by omega⟩
  · by_cases bt : b = .atom "term"
    · subst bt; exact ⟨a, ha, fun m _ => inter_term_right _ _⟩
    by_cases at' : a = .atom "term"
    · subst at'; exact ⟨b, hb, fun m _ => by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl⟩
    obtain ⟨A, cA, nA, ea⟩ : ∃ A, C A ∧ A ≠ .atom "term" ∧ ∀ m, Elixir.Module.Types.Descr.«bare_intersection/2»
        (D (m + 1)) a b = Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A b := by
      rcases ha with ha | ha
      · exact ⟨a, ha, at', fun _ => rfl⟩
      · exact ⟨_, hexp ha, expN_ne_term _ _, fun m => inter_node_l ha.node m (expand_isT ha m) b bt⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m, Elixir.Module.Types.Descr.«bare_intersection/2»
        (D (m + 1)) A b = Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ => rfl⟩
      · exact ⟨_, hexp hb, fun m => inter_node_r hb.node m (expand_isT hb m) A nA⟩
    obtain ⟨c, hc, run⟩ := ops.inter cA cB
    exact ⟨c, Or.inl hc, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; rw [ea, eb]; exact run _ (by omega)⟩
  · rcases ha with ha | ha
    · obtain ⟨b, run⟩ := ops.empty ha S
      exact ⟨b, fun m hm => run m (by omega)⟩
    · exact ⟨_, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m hm; exact empty_node ha.node m' S⟩

theorem addDisj (hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ X, a = .map X)
    (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (ops : ElemOk C K) (jops : ElemDisj C K) :
    ElemDisj (WithNode t C) (K + 1) := by
  have aops := addOk hC hexp ops
  have viaInter : ∀ {a b}, WithNode t C a → WithNode t C b → ∀ S : List (Term × Term), (∀ d,
      Elixir.Module.Types.Descr.«disjoint_seen?/3» d a b (.map S) =
        (Elixir.Module.Types.Descr.«bare_intersection/2» d a b).bind
          fun c => Elixir.Module.Types.Descr.«empty_seen?/2» d c (.map S)) →
      BoolAt (K + 1 + 3) (fun m => Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) a b (.map S)) := by
    intro a b ha hb S eq
    obtain ⟨c, hc, rc⟩ := aops.inter ha hb
    obtain ⟨e, he⟩ := aops.empty hc S
    exact ⟨e, fun m hm => by dsimp only; rw [eq, rc m (by omega)]; exact he m (by omega)⟩
  refine ⟨fun {a b} ha hb S => ?_⟩
  rcases ha with ha' | ha'
  · rcases hb with hb' | hb'
    · exact (jops.disj ha' hb' S).mono (by omega)
    · exact viaInter (Or.inl ha') (Or.inr hb') S fun d => disj_seen_nonmap_r d _ _ (node_nonmap hb')
  · exact viaInter (Or.inr ha') hb S fun d => disj_seen_nonmap_l d _ _ (node_nonmap ha')

theorem diff_none (d : Dispatcher) (a b : Term) (bt : b ≠ .atom "term") (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a b = .ok a := by
  rw [Elixir.Module.Types.Descr.«bare_difference/2».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) bt
    · simp_all [Erlang.erlang.«==/2»]
  all_goals simp_all [Erlang.erlang.«==/2»]

theorem addDiff (_hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ X, a = .map X)
    (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (hnone : C (.map [])) (dops : ElemDiff C K) :
    ElemDiff (WithNode t C) (K + 1) := by
  have succ : ∀ m, K + 1 ≤ m → ∃ m', m = m' + 1 ∧ K ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  refine ⟨fun {a b} ha hb => ?_⟩
  by_cases bt : b = .atom "term"
  · subst bt; exact ⟨_, Or.inl hnone, fun m _ => diff_term_right _ _⟩
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · exact ⟨a, ha, fun m _ => diff_none _ a b bt none⟩
  obtain ⟨B, cB, nB, sB, eb⟩ : ∃ B, C B ∧ B ≠ .atom "term" ∧ ¬Term.compare (Term.fuel B (.map [])) B (.map []) = .eq ∧
      ∀ m a, Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a B := by
    rcases hb with hb | hb
    · exact ⟨b, hb, bt, none, fun _ _ => rfl⟩
    · exact ⟨_, hexp hb, expN_ne_term _ _, expN_ne_none _ _, fun m a => diff_node_r hb.node m (expand_isT hb m) a⟩
  obtain ⟨A, cA, ea⟩ : ∃ A, C A ∧ ∀ m, Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a B =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) A B := by
    rcases ha with ha | ha
    · exact ⟨a, ha, fun _ => rfl⟩
    · exact ⟨_, hexp ha, fun m => diff_node_l ha.node m (expand_isT ha m) B nB sB⟩
  obtain ⟨c, hc, run⟩ := dops.diff cA cB
  exact ⟨c, Or.inl hc, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; rw [eb, ea]; exact run _ (by omega)⟩

theorem union_none (d : Dispatcher) (a b : Term) (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (none : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) : Elixir.Module.Types.Descr.«bare_union/2» d a b = .ok b := by
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem union_none_r (d : Dispatcher) (a b : Term) (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (na : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«bare_union/2» d a b = .ok a := by
  rw [Elixir.Module.Types.Descr.«bare_union/2».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem addFun (hC : ∀ {a}, C a → a = .atom "term" ∨ ∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = none)
    (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (ops : ElemOk C K) (fops : ElemFun C K) :
    ElemFun (WithNode t C) (K + 1) := by
  have succ : ∀ m, K + 1 ≤ m → ∃ m', m = m' + 1 ∧ K ≤ m' := fun m hm => ⟨m - 1, by omega, by omega⟩
  have static : ∀ {x}, WithNode t C x → ∀ X, x = .map X → mapLookup X (.atom "dynamic") = none := by
    intro x hx X e
    rcases hx with hx | hx
    · rcases hC hx with rfl | ⟨Y, rfl, sY⟩
      · cases e
      · cases e; exact sY
    · obtain ⟨S, rfl, -⟩ := hx.node; cases e
  refine ⟨fun {a} ha => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_⟩
  · rcases ha with ha | ha
    · exact fops.static ha
    · obtain ⟨S, rfl, -⟩ := ha.node; exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
  · -- Unions.
    by_cases at' : a = .atom "term"
    · subst at'; exact ⟨_, Or.inl ops.term, fun m _ => union_term_l _ _⟩
    by_cases bt : b = .atom "term"
    · subst bt; exact ⟨_, Or.inl ops.term, fun m _ => union_any_term _ _⟩
    by_cases na : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq
    · exact ⟨b, hb, fun m _ => union_none _ a b at' bt na⟩
    by_cases nb : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
    · exact ⟨a, ha, fun m _ => union_none_r _ a b at' bt na nb⟩
    obtain ⟨A, cA, nA, sA, ea⟩ : ∃ A, C A ∧ A ≠ .atom "term" ∧ ¬Term.compare (Term.fuel A (.map [])) A (.map []) = .eq ∧
        ∀ m, Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) a b =
          Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) A b := by
      rcases ha with ha | ha
      · exact ⟨a, ha, at', na, fun _ => rfl⟩
      · exact ⟨_, hexp ha, expN_ne_term _ _, expN_ne_none _ _,
          fun m => union_node_l ha.node m (expand_isT ha m) b bt nb⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m, Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) A b =
        Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) A B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ => rfl⟩
      · exact ⟨_, hexp hb, fun m => union_node_r hb.node m (expand_isT hb m) A nA sA⟩
    obtain ⟨c, hc, run⟩ := fops.union cA cB
    exact ⟨c, Or.inl hc, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; rw [ea, eb]; exact run _ (by omega)⟩
  · -- Inclusions.
    obtain ⟨A, cA, ea⟩ : ∃ A, C A ∧ ∀ m b, Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) A b := by
      rcases ha with ha | ha
      · exact ⟨a, ha, fun _ _ => rfl⟩
      · exact ⟨_, hexp ha, fun m b => sub_node_l ha.node m (expand_isT ha m) b⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m a, Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a b =
        Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) a B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ _ => rfl⟩
      · exact ⟨_, hexp hb, fun m a => sub_node_r hb.node m (expand_isT hb m) a⟩
    obtain ⟨s, hs⟩ := fops.sub cA cB
    exact ⟨s, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩
  · -- Disjointness: nodes are not empty, and behave as their expansions otherwise.
    have nodeEmpty : ∀ {e}, IsT t e → BoolAt (K + 1) (fun m => Elixir.Module.Types.Descr.«empty?/1» (D m) e) :=
      fun he => ⟨Bool.false, fun m hm => by obtain ⟨m', rfl, -⟩ := succ m hm; exact empty_any_node he m'⟩
    by_cases bt : b = .atom "term"
    · subst bt
      rcases ha with ha | ha
      · exact (fops.disj ha ops.term).mono (by omega)
      · obtain ⟨s, hs⟩ := nodeEmpty ha
        exact ⟨s, fun m hm => by dsimp only; rw [disj_term_r]; exact hs m hm⟩
    by_cases at' : a = .atom "term"
    · subst at'
      rcases hb with hb | hb
      · exact (fops.disj ops.term hb).mono (by omega)
      · obtain ⟨s, hs⟩ := nodeEmpty hb
        exact ⟨s, fun m hm => by dsimp only; rw [disj_term_l]; exact hs m hm⟩
    obtain ⟨A, cA, nA, sA, ea⟩ : ∃ A, C A ∧ A ≠ .atom "term" ∧
        (∀ X, A = .map X → mapLookup X (.atom "dynamic") = none) ∧
        ∀ m, Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) a b =
          Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) A b := by
      rcases ha with ha' | ha'
      · exact ⟨a, ha', at', static (Or.inl ha'), fun _ => rfl⟩
      · exact ⟨_, hexp ha', expN_ne_term _ _, fun X e => by simp [expN] at e; subst e; simp [mapLookup],
          fun m => disj_node_l ha'.node m (expand_isT ha' m) b bt (static hb)⟩
    obtain ⟨B, cB, eb⟩ : ∃ B, C B ∧ ∀ m, Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) A b =
        Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) A B := by
      rcases hb with hb | hb
      · exact ⟨b, hb, fun _ => rfl⟩
      · exact ⟨_, hexp hb, fun m => disj_node_r hb.node m (expand_isT hb m) A nA sA⟩
    obtain ⟨s, hs⟩ := fops.disj cA cB
    exact ⟨s, fun m hm => by obtain ⟨m', rfl, hm'⟩ := succ m hm; dsimp only; rw [ea, eb]; exact hs _ (by omega)⟩

end

theorem PureMap.noList {t : Term} {M : List (Term × Term)} (p : PureMap t M) : PureMap t (noList M) := by
  refine ⟨fun q h => p.keys q (by rw [← noList_lookup M q h]; exact h), fun name w h => ?_⟩
  have := noList_lookup M (.atom name) (by rw [h]; rfl)
  rw [this] at h
  exact p.fields _ _ h

theorem pureTail (t : Term) : TailOk (Pure t) := by
  intro e he
  rcases he with rfl | he | ⟨M, rfl, pM⟩
  · obtain ⟨T, run, bT⟩ := tail_term
    exact ⟨.map T, fun m _ => run (D m), Or.inr (Or.inr ⟨T, rfl, Basic.pure bT⟩)⟩
  · exact ⟨_, fun m hm => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact tail_node he.node m' (expand_isT he m'), Or.inr (Or.inr ⟨_, rfl, expN_pure he⟩)⟩
  · exact ⟨_, fun m _ => tail_map (D m) M, Or.inr (Or.inr ⟨_, rfl, pM.noList⟩)⟩

theorem addTail {t : Term} {C : Term → Prop} (hexp : ∀ {e}, IsT t e → C (expN e (keyOf t))) (tail : TailOk C) :
    TailOk (WithNode t C) := by
  intro e he
  rcases he with he | he
  · obtain ⟨e', run, he'⟩ := tail e he
    exact ⟨e', run, Or.inl he'⟩
  · exact ⟨_, fun m hm => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact tail_node he.node m' (expand_isT he m'), Or.inl (hexp he)⟩

/-- The expansion of a node nests its elements. -/
theorem expN_nest {E : Term → Prop} (hterm : E (.atom "term")) {e : Term} (he : E e) (k : Int) :
    NestC E (expN e k) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?, equalExact_eq_decide] at h
    by_cases t₁ : Term.compareExact (Term.fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₁)))))
    · by_cases t₂ : Term.compareExact (Term.fuel q (.atom "atom")) q (.atom "atom") = .eq
      · exact Or.inr (Or.inl ((compareExact_eq_atom _ _).mp t₂))
      · simp [t₁, t₂] at h
  · by_cases t₁ : name = "tuple"
    · subst t₁
      simp [mapLookup] at h
      subst h
      refine Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Bdd.leaf_iff.mpr ⟨⟨k, "closed", [.atom "term", e], rfl, Or.inr rfl,
        fun x mx => ?_⟩, fun ⟨_, h⟩ => by simp [Term.list] at h⟩)⟩))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mx
      rcases mx with rfl | rfl
      · exact hterm
      · exact he
    · by_cases t₂ : name = "atom"
      · subst t₂
        simp [mapLookup] at h
        subst h
        exact Or.inl ⟨by decide, by decide, by decide, by decide, Or.inr (Or.inl ⟨rfl,
          ⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil",
          by simp [amemV, mapLookup]⟩)⟩
      · simp [mapLookup, t₁, t₂] at h

/-- Nested element types of a depth with the recursive node `t`, closed under intersection and difference: at
depth 0, they nest the node, its expansion, and their combinations with basic types. -/
def Closed (t : Term) : Nat → Term → Prop
  | 0 => WithNode t (NestC (Pure t))
  | d + 1 => WithNode t (NestC (Closed t d))

theorem closed_node {t e : Term} (he : IsT t e) : ∀ d, Closed t d e
  | 0 => Or.inr he
  | _ + 1 => Or.inr he

/-- Adding the node to nested types of elements holding it. -/
theorem nest_node {t : Term} {E : Term → Prop} {K : Nat} (hterm : E (.atom "term")) (hnode : ∀ {e}, IsT t e → E e)
    (ops : ElemOk E K) (dops : ElemDiff E K) (fops : ElemFun E K) (hnone : E (.map [])) (tail : TailOk E)
    (jops : ElemDisj E (K + 3)) :
    ElemOk (WithNode t (NestC E)) (K + 15) ∧ ElemDiff (WithNode t (NestC E)) (K + 15) ∧
      ElemFun (WithNode t (NestC E)) (K + 15) ∧ WithNode t (NestC E) (.map []) ∧ TailOk (WithNode t (NestC E)) ∧
      ElemDisj (WithNode t (NestC E)) (K + 15) := by
  have hC : ∀ {a}, NestC E a → a = .atom "term" ∨ ∃ X, a = .map X := fun {a} ha => by
    rcases ha with rfl | ⟨X, rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, rfl⟩
  have hS : ∀ {a}, NestC E a → a = .atom "term" ∨ ∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = none :=
    fun {a} ha => by
      rcases ha with rfl | ⟨X, rfl, v⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, rfl, v.static⟩
  have hexp : ∀ {e}, IsT t e → NestC E (expN e (keyOf t)) := fun he => expN_nest hterm (hnode he) _
  have n₁ := (nestOk ops dops jops fops hnone tail).mono (show K + 8 ≤ K + 14 by omega)
  have n₂ := (nestDiff hterm K).mono (show K + 3 ≤ K + 14 by omega)
  have n₃ := nestFun ops dops jops fops hnone tail
  have n₄ := (nestDisj ops dops jops fops hnone tail).mono (show K + 8 + 3 ≤ K + 14 by omega)
  exact ⟨addOk hC hexp n₁, addDiff hC hexp nest_none n₂, addFun hS hexp n₁ n₃, Or.inl nest_none,
    addTail hexp (tail_nest hterm), addDisj hC hexp n₁ n₄⟩

theorem closed_ok (t : Term) : ∀ d, ElemOk (Closed t d) (23 + 15 * d) ∧ ElemDiff (Closed t d) (23 + 15 * d) ∧
    ElemFun (Closed t d) (23 + 15 * d) ∧ Closed t d (.map []) ∧ TailOk (Closed t d) ∧
      ElemDisj (Closed t d) (23 + 15 * d)
  | 0 => nest_node (Or.inl rfl) (fun he => Or.inr (Or.inl he)) ((pureOk t).mono (by omega))
      ((pureDiff t).mono (by omega)) (pureFun t) (pure_none t) (pureTail t) ((pureDisj t).mono (by omega))
  | d + 1 => by
    obtain ⟨ops, dops, fops, hnone, tail, jops⟩ := closed_ok t d
    have := nest_node ops.term (fun he => closed_node he d) ops dops fops hnone tail (jops.mono (by omega))
    rw [show 23 + 15 * (d + 1) = 23 + 15 * d + 15 by omega]
    exact this

theorem OField.mono {ok ok' : Term → Prop} (h : ∀ t, ok t → ok' t) {x : Term} (f : OField ok x) : OField ok' x := by
  rcases f with top | b
  · exact Or.inl top
  · exact Or.inr (b.mono h)

theorem FField.mono {E E' : Term → Prop} (h : ∀ t, E t → E' t) {w : Term} (f : FField E w) : FField E' w := by
  obtain ⟨p, R, rfl, b⟩ := f
  exact ⟨p, R, rfl, fun q v hv => (b q v hv).mono fun t ⟨n, e, k, args, ret, ht, len, ha, hr⟩ =>
    ⟨n, e, k, args, ret, ht, len, fun a ma => h a (ha a ma), h ret hr⟩⟩

/-- The nested types of the specification are closed nested types. -/
theorem nest_closed (t : Term) : ∀ d e, Nest t d e → Closed t d e
  | 0, _, h => by
    rcases h with h | h
    · rcases elem_lelem h with rfl | ⟨M, rfl, bM⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨M, rfl, Basic.nest (Or.inl rfl) bM⟩)
    · exact Or.inr h
  | d + 1, _, h => by
    rcases h with h | h
    rotate_left
    · exact Or.inr h
    rcases h with rfl | ⟨X, rfl, v⟩
    · exact Or.inl (Or.inl rfl)
    refine Or.inl (Or.inr ⟨X, rfl, ⟨v.keys, fun name w h => ?_⟩⟩)
    rcases v.keys (.atom name) (by rw [h]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨by decide, by decide, by decide, by decide, Or.inl ⟨rfl, v.bitmap w h⟩⟩
    · obtain ⟨p, S, rfl, set⟩ := v.atom w h
      refine Or.inl ⟨by decide, by decide, by decide, by decide, Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, ?_⟩)⟩
      exact atom_nonempty p S fun hp => v.atomUnion S (by subst hp; simpa using h)
    · exact Or.inr (Or.inl ⟨rfl, (v.funs w h).mono (nest_closed t d)⟩)
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))
      rcases v.lists w h with ⟨k, rfl⟩ | b
      · exact Bdd.leaf_iff.mpr ⟨k, _, _, rfl, (closed_ok t d).1.term, (closed_ok t d).1.term⟩
      · exact b.mono fun x ok => by
          obtain ⟨-, k, a, b, rfl, ha, hb⟩ := ok
          exact ⟨k, a, b, rfl, nest_closed t d a ha, nest_closed t d b hb⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, OField.mono (fun x ok => ok.mono (nest_closed t d)) (v.tuples w h)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, OField.mono (fun x ok => ok.mono (nest_closed t d)) (v.maps w h)⟩)))

/-! The law. -/

theorem Negatable.sem {X : List (Term × Term)} (v : Negatable E X) : Sem E X := by
  refine ⟨fun q h => ?_, fun name x hx => ?_⟩
  · rcases v.keys q h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
  · rcases v.keys (.atom name) (by simp [hx]) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨rfl, v.bitmap x hx⟩
    · obtain ⟨p, S, rfl, set⟩ := v.atom x hx
      refine Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, atom_nonempty p S fun hp => v.atomUnion S ?_⟩)
      subst hp
      simpa using hx
    · obtain ⟨pos, R, rfl⟩ := v.funs x hx
      exact Or.inr (Or.inr (Or.inl ⟨rfl, pos, R, rfl, fun q w h => v.arities _ hx _ R rfl q w h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (v.lists x hx).list⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, v.tuples x hx⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, v.maps x hx⟩))))

theorem negation_none_term (δ : Nat) : Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map []) = .ok (.atom "term") := by
  simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2»]

theorem equal_self (δ : Nat) (x : Term) : Elixir.Module.Types.Descr.«equal?/2» (D (δ + 100)) x x = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«equal?/2», Erlang.erlang.«==/2», Std.ReflCmp.compare_self, Lynx.Except.orElse,
    Term.true]

/-- De Morgan's law for any two types of bitmaps, atoms, functions, lists, tuples, and maps. -/
theorem de_morgan_union_law (δ : Nat) (ops : ElemOk E K) (dops : ElemDiff E K) (hK : K ≤ δ + 90) (L R : List (Term × Term)) (vL : Negatable E L) (vR : Negatable E R) :
    (do
      let u ← Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map L) (.map R)
      let a ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) u
      let nl ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map L)
      let nr ← Elixir.Module.Types.Descr.«bare_negation/1» (D (δ + 100)) (.map R)
      let b ← Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) nl nr
      Elixir.Module.Types.Descr.«equal?/2» (D (δ + 100)) a b) = .ok (.atom "true") := by
  by_cases eL : L = [] <;> by_cases eR : R = []
  · subst eL eR
    have union : Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map []) (.map []) = .ok (.map []) := by
      unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
    have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.atom "term") (.atom "term") =
        .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    simp [union, negation_none_term, inter, equal_self]
  · subst eL
    obtain ⟨N, neg, -⟩ := sem_neg δ ops.term R vR.sem eR
    have union : Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map []) (.map R) = .ok (.map R) := by
      unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]
    have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.atom "term") (.map N) = .ok (.map N) := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    simp [union, neg, negation_none_term, inter, equal_self]
  · subst eR
    obtain ⟨N, neg, -⟩ := sem_neg δ ops.term L vL.sem eL
    have union : Elixir.Module.Types.Descr.«bare_union/2» (D (δ + 100)) (.map L) (.map []) = .ok (.map L) := by
      unfold Elixir.Module.Types.Descr.«bare_union/2»
      cases L with
      | nil => exact absurd rfl eL
      | cons e rest => simp [Erlang.erlang.«==/2»]
    have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D (δ + 100)) (.map N) (.atom "term") = .ok (.map N) := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    simp [union, neg, negation_none_term, inter, equal_self]
  · obtain ⟨U, A, NL, NR, B, union, negU, negL, negR, inter, sub₁, sub₂⟩ := de_morgan_sem δ ops dops hK L R vL.sem vR.sem eL eR
    simp only [union, negU, negL, negR, inter, Lynx.Except.ok_bind]
    by_cases c : Term.compare (Term.fuel (.map A) (.map B)) (.map A) (.map B) = .eq <;>
      simp [Elixir.Module.Types.Descr.«equal?/2», sub₁, sub₂, Lynx.Except.orElse, Lynx.Except.andAlso,
        Erlang.erlang.«==/2», c, Term.true, Term.false]

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-- Element types denote sets of values `V`: they intersect and subtract as sets, and are empty exactly when
they denote nothing, at every call depth from `K`. -/
structure ElemSem (E : Term → Prop) (K : Nat) (V : Type) (den : Term → V → Prop) (Safe : List (Term × Term) → Prop) :
    Prop where
  term : ∀ v, den (.atom "term") v
  inter : ∀ {a b c : Term} {m : Nat}, E a → E b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c → ∀ v, den c v ↔ den a v ∧ den b v
  diff : ∀ {a b c : Term} {m : Nat}, E a → E b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c → ∀ v, den c v ↔ den a v ∧ ¬den b v
  empty : ∀ {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool}, E a → Safe S → K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b) → (b = Bool.true ↔ ∀ v, ¬den a v)
  inhabited : Nonempty V
  resp : ∀ {e e' : Term} {v : V}, E e → E e' → compare (fuel e e') e e' = .eq → den e' v → den e v

variable {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Tuples of values in the elements of a tuple literal: of the same size when closed, otherwise at least as large. -/
def InT (den : Term → V → Prop) (closed : Bool) : List Term → List V → Prop
  | [], [] => True
  | [], _ :: _ => closed = Bool.false
  | _ :: _, [] => False
  | e :: es, x :: xs => den e x ∧ InT den closed es xs

/-- Tuples of values in a tuple literal. -/
def LitSem (den : Term → V → Prop) (lit : Term) (v : List V) : Prop :=
  ∃ (k : Int) (tag : String) (l : List Term), lit = .tuple #[.integer k, .atom tag, Term.list l] ∧
    InT den (tag == "closed") l v

theorem InT.length_le {c : Bool} : ∀ {l : List Term} {v : List V}, InT den c l v → l.length ≤ v.length
  | [], _, _ => by simp
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => by simpa using InT.length_le h.2

theorem InT.closed_length : ∀ {l : List Term} {v : List V}, InT den Bool.true l v → v.length = l.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [InT] at h
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => by simpa using InT.closed_length h.2

/-- Splitting the values of a tuple at a prefix of its elements. -/
theorem InT.append {c : Bool} : ∀ (l₁ : List Term) {l₂ : List Term} {v : List V},
    InT den c (l₁ ++ l₂) v ↔ ∃ v₁ v₂, v = v₁ ++ v₂ ∧ InT den Bool.true l₁ v₁ ∧ InT den c l₂ v₂
  | [], l₂, v => ⟨fun h => ⟨[], v, rfl, trivial, h⟩, fun ⟨v₁, v₂, e, h₁, h₂⟩ => by
      cases v₁ with
      | nil => simpa [e] using h₂
      | cons _ _ => simp [InT] at h₁⟩
  | e :: l₁, l₂, [] => ⟨fun h => h.elim, fun ⟨v₁, v₂, ev, h₁, _⟩ => by
      cases v₁ with
      | nil => exact h₁.elim
      | cons _ _ => simp at ev⟩
  | e :: l₁, l₂, x :: v => by
      have ih := InT.append (c := c) l₁ (l₂ := l₂) (v := v)
      constructor
      · rintro ⟨hx, h⟩
        obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := ih.mp h
        exact ⟨x :: v₁, v₂, rfl, ⟨hx, h₁⟩, h₂⟩
      · rintro ⟨v₁, v₂, ev, h₁, h₂⟩
        cases v₁ with
        | nil => exact h₁.elim
        | cons y v₁ =>
          simp only [List.cons_append, List.cons.injEq] at ev
          obtain ⟨rfl, rfl⟩ := ev
          exact ⟨h₁.1, ih.mpr ⟨v₁, v₂, rfl, h₁.2, h₂⟩⟩

/-- Non-empty element types have values. -/
theorem full_witness (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S) {e : Term} (h : Full E K S e) :
    ∃ x, den e x := by
  have := (sem.empty (b := Bool.false) h.1 hS (Nat.le_refl K) (by simpa using h.2 K (Nat.le_refl K)))
  exact Classical.byContradiction fun none => by
    have := this.mpr (fun v hv => none ⟨v, hv⟩); cases this

/-- Tuples of non-empty element types have values of every size they allow. -/
theorem tuple_witness (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S) :
    ∀ (l : List Term), (∀ e ∈ l, Full E K S e) → ∀ (c : Bool) (extra : Nat), ∃ v : List V, InT den c l v ∧
      v.length = l.length + (if c then 0 else extra)
  | [], _, c, extra => by
    obtain ⟨x⟩ := sem.inhabited
    cases c with
    | true => exact ⟨[], trivial, rfl⟩
    | false =>
      cases extra with
      | zero => exact ⟨[], trivial, rfl⟩
      | succ k => exact ⟨List.replicate (k + 1) x, by simp [List.replicate, InT], by simp⟩
  | e :: l, hl, c, extra => by
    obtain ⟨x, hx⟩ := full_witness sem hS (hl e List.mem_cons_self)
    obtain ⟨v, hv, len⟩ := tuple_witness sem hS l (fun e m => hl e (List.mem_cons_of_mem _ m)) c extra
    exact ⟨x :: v, ⟨hx, hv⟩, by simp [len]; omega⟩

theorem list_inj : ∀ {l l' : List Term}, Term.list l = Term.list l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Term.list] at h
  | _ :: _, [], h => by simp [Term.list] at h
  | x :: l, y :: l', h => by
    simp only [Term.list, Term.cons.injEq] at h
    rw [h.1, list_inj h.2]

theorem InT.mid {c : Bool} (l₁ : List Term) (x : Term) (l₂ : List Term) {v : List V} :
    InT den c (l₁ ++ x :: l₂) v ↔ ∃ v₁ y v₂, v = v₁ ++ y :: v₂ ∧ InT den Bool.true l₁ v₁ ∧ den x y ∧ InT den c l₂ v₂ := by
  rw [InT.append]
  constructor
  · rintro ⟨v₁, w, rfl, h₁, h₂⟩
    cases w with
    | nil => exact h₂.elim
    | cons y v₂ => exact ⟨v₁, y, v₂, rfl, h₁, h₂.1, h₂.2⟩
  · rintro ⟨v₁, y, v₂, rfl, h₁, hx, h₂⟩
    exact ⟨v₁, y :: v₂, rfl, h₁, hx, h₂⟩

theorem InT.replace {c : Bool} {l₁ : List Term} {x x' : Term} {l₂ : List Term} {v : List V}
    (h : InT den c (l₁ ++ x :: l₂) v) (sub : ∀ y, den x y → den x' y) : InT den c (l₁ ++ x' :: l₂) v := by
  obtain ⟨v₁, y, v₂, rfl, h₁, hx, h₂⟩ := (InT.mid l₁ x l₂).mp h
  exact (InT.mid l₁ x' l₂).mpr ⟨v₁, y, v₂, rfl, h₁, sub y hx, h₂⟩

theorem InT.extend : ∀ {l : List Term} {v : List V} (w : List V), InT den Bool.true l v → InT den Bool.false l (v ++ w)
  | [], [], [], _ => trivial
  | [], [], _ :: _, _ => rfl
  | [], _ :: _, _, h => by simp [InT] at h
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, w, h => ⟨h.1, InT.extend w h.2⟩

theorem InT.open_prefix {l₁ l₂ : List Term} {v : List V} (h : InT den Bool.false (l₁ ++ l₂) v) :
    InT den Bool.false l₁ v := by
  obtain ⟨v₁, v₂, rfl, h₁, -⟩ := (InT.append l₁).mp h
  exact InT.extend v₂ h₁

/-- Values of a tuple literal hold, at each position of its elements, a value of that element. -/
theorem lit_at {k : Int} {ntag : String} {pre post : List Term} {nt : Term} {v₁ v₂ : List V} {y : V}
    (h : LitSem den (Term.tuple #[Term.integer k, Term.atom ntag, Term.list (pre ++ nt :: post)]) (v₁ ++ y :: v₂))
    (len : v₁.length = pre.length) : den nt y := by
  obtain ⟨k', tag', l, e, hl⟩ := h
  simp only [Term.tuple.injEq] at e
  have el : Term.list l = Term.list (pre ++ nt :: post) := by
    have := congrArg (fun a : Array Term => a[2]?) e
    simpa using this.symm
  rw [list_inj el] at hl
  obtain ⟨w₁, z, w₂, ew, h₁, hz, -⟩ := (InT.mid pre nt post).mp hl
  have := h₁.closed_length
  obtain ⟨-, e₂⟩ := List.append_inj ew (by omega)
  simp only [List.cons.injEq] at e₂
  rw [e₂.1]
  exact hz

/-- `tuple_elements_meets/4` answers `:disjoint` only when no tuple of the line is in the negated literal: some
element of the line meets the negated element at its position in nothing. -/
theorem meets_disj_sem (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) :
    ∀ (nl : List Term), (∀ e ∈ nl, E e) → ∀ (l acc : List Term), (∀ e ∈ l, Full E K S e) →
      Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m) (Term.list l) (Term.list nl) (Term.list acc)
        (.map S) = .ok (.atom "disjoint") →
      ∀ (c c' : Bool) (v : List V), InT den c l v → ¬InT den c' nl v := by
  intro nl
  induction nl with
  | nil =>
    intro _ l acc _ h
    rw [meets_done] at h
    generalize acc.reverse = r at h
    cases r <;> simp at h
  | cons nt nl ih =>
    intro hnl l acc hl h c c' v hv hn
    obtain ⟨ty, es, hshape, hty, hes⟩ : ∃ ty es, ((l = [] ∧ ty = .atom "term" ∧ es = []) ∨ l = ty :: es) ∧
        Full E K S ty ∧ ∀ e ∈ es, Full E K S e := by
      cases l with
      | nil => exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, full_term ops S, by simp⟩
      | cons x xs => exact ⟨x, xs, Or.inr rfl, hl x List.mem_cons_self, fun e m => hl e (List.mem_cons_of_mem _ m)⟩
    have hnt := hnl nt List.mem_cons_self
    have hnl' : ∀ e ∈ nl, E e := fun e m => hnl e (List.mem_cons_of_mem _ m)
    obtain ⟨y, vs, rfl⟩ : ∃ y vs, v = y :: vs := by
      cases v with
      | nil => exact absurd hn (by simp [InT])
      | cons y vs => exact ⟨y, vs, rfl⟩
    have ny : den nt y := hn.1
    have hy : den ty y ∧ InT den c es vs := by
      rcases hshape with ⟨rfl, rfl, rfl⟩ | rfl
      · refine ⟨sem.term y, ?_⟩
        cases c
        · cases vs <;> simp [InT]
        · simp [InT] at hv
      · exact hv
    obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty.1 hnt
    have dmeet := sem.inter hty.1 hnt hm (hmeet m hm)
    have step := meets_step (D m) acc l nt nl (.map S) ty es hshape meet (hmeet m hm)
    rw [list_cons] at h
    obtain ⟨bm, em⟩ := ops.empty lmeet S
    cases bm
    · rw [step.2 (by simpa [boolAtom] using em m hm)] at h
      exact ih hnl' es (meet :: acc) hes h c c' vs hy.2 hn.2
    · have none := (sem.empty lmeet hS hm (em m hm)).mp rfl
      exact none y ((dmeet y).mpr ⟨hy.1, ny⟩)

/-- The meets `tuple_elements_meets/4` computed for a line that meets the negated literal start with the meet of the
first element. -/
theorem meets_head (ops : ElemOk E K) (S : List (Term × Term)) {m : Nat} (hm : K ≤ m) {rest es nl : List Term}
    {ty nt : Term} (hshape : (rest = [] ∧ ty = .atom "term" ∧ es = []) ∨ rest = ty :: es) (hty : Full E K S ty)
    (hes : ∀ e ∈ es, Full E K S e) (hnt : E nt) (hnl : ∀ e ∈ nl, E e) {accM ms : List Term}
    (h : Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m) (Term.list rest) (.cons nt (Term.list nl))
      (Term.list accM) (.map S) = .ok (Term.list (accM.reverse ++ ms))) :
    ∃ meet ms', ms = meet :: ms' ∧ (∀ m', K ≤ m' → Elixir.Module.Types.Descr.«bare_intersection/2» (D m') ty nt =
      .ok meet) ∧ Full E K S meet ∧ Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m) (Term.list es)
        (Term.list nl) (Term.list (meet :: accM)) (.map S) = .ok (Term.list ((meet :: accM).reverse ++ ms')) := by
  obtain ⟨meet, lmeet, hmeet⟩ := ops.inter hty.1 hnt
  have mstep := meets_step (D m) accM rest nt nl (.map S) ty es hshape meet (hmeet m hm)
  obtain ⟨bm, em⟩ := ops.empty lmeet S
  cases bm
  case true =>
    rw [mstep.1 (by simpa [boolAtom] using em m hm)] at h
    cases h' : accM.reverse ++ ms <;> rw [h'] at h <;> simp [Term.list] at h
  have fullMeet : Full E K S meet := ⟨lmeet, fun m' h' => by simpa [boolAtom] using em m' h'⟩
  rw [mstep.2 (fullMeet.2 m hm)] at h
  rcases meets_cases ops S nl hnl (meet :: accM) es hes with dis | ⟨ms', -, -, run⟩
  · rw [dis m hm] at h
    cases h' : accM.reverse ++ ms <;> rw [h'] at h <;> simp [Term.list] at h
  · rw [run m hm] at h
    simp only [Except.ok.injEq, List.reverse_cons, List.append_assoc, List.singleton_append] at h
    refine ⟨meet, ms', (List.append_cancel_left (list_inj h)).symm, hmeet, fullMeet, ?_⟩
    simpa using run m hm

/-- `tuple_elements_empty?/7` finds the remaining values of a line, outside the negated literal, covered by the
remaining negations, given the meets `tuple_elements_meets/4` computed alongside. -/
theorem elements_complete (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (_hS : Safe S) (c : Bool) (negs : List Term)
    (line : ∀ l : List Term, (∀ e ∈ l, Full E K S e) → (∀ v, InT den c l v → ∃ N ∈ negs, LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "true"))
    (k : Int) (ntag : String) :
    ∀ (nrest pre acc rest accM ms : List Term), (∀ e ∈ nrest, E e) → pre.length = acc.length → (∀ e ∈ acc, Full E K S e) →
      (∀ e ∈ rest, Full E K S e) → (c = Bool.true → nrest.length ≤ rest.length) →
      Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m) (Term.list rest) (Term.list nrest) (Term.list accM)
        (.map S) = .ok (Term.list (accM.reverse ++ ms)) →
      (∀ v, InT den c (acc.reverse ++ rest) v →
        ¬LitSem den (Term.tuple #[Term.integer k, Term.atom ntag, Term.list (pre ++ nrest)]) v → ∃ N ∈ negs, LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_elements_empty?/7» (D m) (Term.list acc) (.atom (if c then "closed" else "open"))
        (Term.list rest) (Term.list nrest) (Term.list ms) (Term.list negs) (.map S) = .ok (.atom "true") := by
  intro nrest
  induction nrest with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _
    rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/7».eq_def]
    rfl
  | cons nt nl ih =>
    intro pre acc rest accM ms hn hpre hacc hrest hlen hmeets H
    have hnt := hn nt List.mem_cons_self
    have hnl : ∀ e ∈ nl, E e := fun e m => hn e (List.mem_cons_of_mem _ m)
    -- the next element of the line, `term` past the end of open lines
    obtain ⟨ty, es, hshape, hty, hes, back⟩ : ∃ ty es, ((rest = [] ∧ ty = .atom "term" ∧ es = []) ∨ rest = ty :: es) ∧
        Full E K S ty ∧ (∀ e ∈ es, Full E K S e) ∧
        ∀ v, InT den c (acc.reverse ++ ty :: es) v → InT den c (acc.reverse ++ rest) v := by
      cases rest with
      | nil =>
        have hc : c = Bool.false := by
          cases c
          · rfl
          · have := hlen rfl; simp at this
        subst hc
        exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, full_term ops S, by simp, fun v h => by
          simpa using InT.open_prefix (l₂ := [.atom "term"]) h⟩
      | cons x xs => exact ⟨x, xs, Or.inr rfl, hrest x List.mem_cons_self,
          fun e m => hrest e (List.mem_cons_of_mem _ m), fun v h => h⟩
    have notN : ∀ v₁ y v₂, List.length v₁ = acc.length → ¬den nt y →
        ¬LitSem den (Term.tuple #[Term.integer k, Term.atom ntag, Term.list (pre ++ nt :: nl)]) (v₁ ++ y :: v₂) :=
      fun v₁ y v₂ len ny h => ny (lit_at h (by omega))
    have allRev : ∀ x, Full E K S x → ∀ e ∈ acc.reverse ++ x :: es, Full E K S e := by
      intro x hx e m
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at m
      rcases m with m | rfl | m
      · exact hacc e m
      · exact hx
      · exact hes e m
    -- the meet of this element comes first in the meets
    rw [list_cons] at hmeets
    obtain ⟨meet, ms', rfl, hmeet, fullMeet, hmeets'⟩ := meets_head ops S hm hshape hty hes hnt hnl hmeets
    have dmeet := sem.inter hty.1 hnt hm (hmeet m hm)
    obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty.1 hnt
    have ddiff := sem.diff hty.1 hnt hm (hdiff m hm)
    have step := elements_step (D m) acc (.atom (if c then "closed" else "open")) rest nt nl meet (Term.list ms')
      (Term.list negs) (.map S) ty es hshape diff (hdiff m hm)
    obtain ⟨bd, ed⟩ := ops.empty ldiff S
    have pre' : (pre ++ [nt]).length = (ty :: acc).length := by simp [hpre]
    have assoc : pre ++ nt :: nl = (pre ++ [nt]) ++ nl := by simp
    rw [list_cons nt nl, list_cons meet ms']
    cases bd
    · have fullDiff : Full E K S diff := ⟨ldiff, fun m' h' => by simpa [boolAtom] using ed m' h'⟩
      rw [step.2 (fullDiff.2 m hm)]
      have l₁ := line _ (allRev diff fullDiff) (fun v hv => by
        obtain ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ := (InT.mid _ _ _).mp hv
        have hy' := (ddiff y).mp hy
        refine H _ (back _ ((InT.mid _ _ _).mpr ⟨v₁, y, v₂, rfl, h₁, hy'.1, h₂⟩)) (notN v₁ y v₂ ?_ hy'.2)
        rw [h₁.closed_length]; simp)
      have e₂ := ih (pre ++ [nt]) (meet :: acc) es (meet :: accM) ms' hnl pre' (fun e m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact fullMeet
          · exact hacc e m) hes (fun hc => by have h := hlen hc; rcases hshape with ⟨rfl, -, rfl⟩ | rfl <;> simp at h ⊢ <;> omega)
        hmeets' (fun v hv nN => by
          refine H _ (back _ ?_) (by rw [assoc]; exact nN)
          have := hv
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
          exact this.replace fun y hy => ((dmeet y).mp hy).1)
      rw [l₁, e₂]
      rfl
    · rw [step.1 (by simpa [boolAtom] using ed m hm)]
      exact ih (pre ++ [nt]) (ty :: acc) es (meet :: accM) ms' hnl pre' (fun e m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact hty
          · exact hacc e m) hes (fun hc => by have h := hlen hc; rcases hshape with ⟨rfl, -, rfl⟩ | rfl <;> simp at h ⊢ <;> omega)
        hmeets' (fun v hv nN => by
          refine H _ (back _ ?_) (by rw [assoc]; exact nN)
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hv)

theorem InT.fill {l : List Term} {j : Nat} {v : List V} (h : InT den Bool.true (l ++ List.replicate j (Term.atom "term")) v) :
    InT den Bool.false l v ∧ v.length = l.length + j := by
  obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := (InT.append l).mp h
  refine ⟨InT.extend v₂ h₁, ?_⟩
  simp [h₁.closed_length, h₂.closed_length]

theorem InT.fill_open {l : List Term} {j : Nat} {v : List V}
    (h : InT den Bool.false (l ++ List.replicate j (Term.atom "term")) v) : InT den Bool.false l v ∧ l.length + j ≤ v.length :=
  ⟨InT.open_prefix h, by have := h.length_le; simpa using this⟩

theorem lit_sem {k : Int} {ntag : String} {nl : List Term} {v : List V}
    (h : LitSem den (.tuple #[.integer k, .atom ntag, Term.list nl]) v) : InT den (ntag == "closed") nl v := by
  obtain ⟨k', tag', l, e, hl⟩ := h
  simp only [Term.tuple.injEq] at e
  have e₁ : Term.atom ntag = Term.atom tag' := by have := congrArg (fun a : Array Term => a[1]?) e; simpa using this
  have e₂ : Term.list nl = Term.list l := by have := congrArg (fun a : Array Term => a[2]?) e; simpa using this
  simp only [Term.atom.injEq] at e₁
  rw [e₁, list_inj e₂]
  exact hl

/-- Tuple lines of non-empty element types are empty when their negations cover their values. -/
theorem line_complete (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) :
    ∀ negs : List Term, (∀ t ∈ negs, TupleLit E t) → ∀ (c : Bool) (l : List Term), (∀ e ∈ l, Full E K S e) →
      (∀ v, InT den c l v → ∃ N ∈ negs, LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "true") := by
  intro negs
  induction negs with
  | nil =>
    intro _ c l hl H
    obtain ⟨v, hv, -⟩ := tuple_witness sem hS l hl c 0
    obtain ⟨N, mN, -⟩ := H v hv
    simp at mN
  | cons N rest ih =>
    intro lits c l hl H
    obtain ⟨k, ntag, nl, rfl, htag, hnl⟩ := lits N List.mem_cons_self
    have lits' : ∀ t ∈ rest, TupleLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    rw [list_cons]
    by_cases top : ntag = "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact line_top _ _ _ k _ (.map S)
    by_cases last : c = Bool.false ∧ ntag = "closed" ∧ rest = []
    · exfalso
      obtain ⟨rfl, rfl, rfl⟩ := last
      obtain ⟨v, hv, len⟩ := tuple_witness sem hS l hl Bool.false (nl.length + 1)
      obtain ⟨N', mN, hN⟩ := H v hv
      simp only [List.mem_singleton] at mN
      subst mN
      have := (lit_sem hN).closed_length
      simp at len; omega
    have notLast : ¬((if c then "closed" else "open") = "open" ∧ ntag = "closed" ∧ rest = []) := by
      rintro ⟨hc, h₁, h₂⟩
      cases c
      · exact last ⟨rfl, h₁, h₂⟩
      · simp at hc
    have covered : ∀ v, InT den c l v → ¬InT den (ntag == "closed") nl v → ∃ N ∈ rest, LitSem den N v := by
      intro v hv nN
      obtain ⟨N', mN, hN⟩ := H v hv
      rcases List.mem_cons.mp mN with rfl | mN
      · exact absurd (lit_sem hN) nN
      · exact ⟨N', mN, hN⟩
    by_cases skip : ((if c then "closed" else "open") = "closed" ∧ l.length < nl.length) ∨
        (ntag = "closed" ∧ nl.length < l.length)
    · rw [line_size (D m) _ l k ntag nl rest (.map S) top notLast skip]
      refine ih lits' c l hl fun v hv => covered v hv fun hN => ?_
      have le := hv.length_le
      have le' := hN.length_le
      cases c
      · rcases skip with ⟨h, -⟩ | ⟨hc, lt⟩
        · simp at h
        · subst hc; have := hN.closed_length; omega
      · rcases skip with ⟨-, lt⟩ | ⟨hc, lt⟩
        · have := hv.closed_length; omega
        · subst hc; have := hN.closed_length; omega
    · rcases meets_cases ops S nl hnl [] l hl with dis | ⟨ms, -, -, run⟩
      · rw [line_disjoint (D m) _ l k ntag nl rest (.map S) top notLast skip (by simpa using dis m hm)]
        exact ih lits' c l hl fun v hv => covered v hv
          (meets_disj_sem ops sem hm S hS nl hnl l [] hl (dis m hm) c _ v hv)
      have noLong : ntag = "closed" → l.length ≤ nl.length := fun hc => by
        have : ¬nl.length < l.length := fun h => skip (Or.inr ⟨hc, h⟩)
        omega
      have elems := elements_complete ops dops sem hm S hS c rest (fun l' hl' H' => ih lits' c l' hl' H') k ntag nl []
        [] l [] ms hnl rfl (by simp) hl (fun hc => by
          subst hc
          have : ¬l.length < nl.length := fun h => skip (Or.inl ⟨rfl, h⟩)
          simp; omega) (by simpa using run m hm)
        (fun v hv nN => covered v (by simpa using hv) fun hN => nN ⟨k, ntag, nl, by simp, hN⟩)
      have arity : Elixir.Module.Types.Descr.«tuple_empty_arity?/7» (D m) (.integer l.length) (.integer nl.length)
          (.atom (if c then "closed" else "open")) (Term.list l) (.atom ntag) (Term.list rest) (.map S) =
          .ok (.atom "true") := by
        apply arity_true
        cases c
        · right
          refine ⟨sizes_all (D m) l nl.length _ _ (fun i le lt => ?_) l.length (Nat.le_refl _), ?_⟩
          · refine ih lits' Bool.true _ (fun e me => ?_) fun v hv => covered v (InT.fill hv).1 fun hN => ?_
            · simp only [List.mem_append, List.mem_replicate] at me
              rcases me with me | ⟨-, rfl⟩
              · exact hl e me
              · exact full_term ops S
            · have := hN.length_le
              have := (InT.fill hv).2
              omega
          · by_cases o : ntag = "open"
            · exact Or.inl o
            · have hc : ntag = "closed" := by rcases htag with h | h <;> simp_all
              refine Or.inr ⟨by have := noLong hc; omega, ?_⟩
              refine ih lits' Bool.false _ (fun e me => ?_) fun v hv => covered v (InT.fill_open hv).1 fun hN => ?_
              · simp only [List.mem_append, List.mem_replicate] at me
                rcases me with me | ⟨-, rfl⟩
                · exact hl e me
                · exact full_term ops S
              · have := noLong hc
                subst hc
                have := hN.closed_length
                have := (InT.fill_open hv).2
                omega
        · left; rfl
      rw [line_meets (D m) _ l k ntag nl rest (.map S) top notLast skip _ (by simpa using run m hm)
        (by cases ms <;> simp), elems, arity]
      rfl

theorem InT.open_nil (v : List V) : InT den Bool.false [] v := by
  cases v <;> simp [InT]

theorem InT.iff_open {c : Bool} : ∀ {l : List Term} {v : List V},
    InT den c l v ↔ InT den Bool.false l v ∧ (c = Bool.true → v.length = l.length)
  | [], [] => by simp [InT]
  | [], _ :: _ => by cases c <;> simp [InT]
  | _ :: _, [] => by simp [InT]
  | e :: l, x :: v => by
    have ih := InT.iff_open (c := c) (l := l) (v := v)
    simp only [InT, List.length_cons, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨⟨hx, (ih.mp h).1⟩, (ih.mp h).2⟩
    · rintro ⟨⟨hx, h⟩, len⟩; exact ⟨hx, ih.mpr ⟨h, len⟩⟩

/-- Element-wise intersections of the elements of two tuples hold the values of both, past the shorter one too. -/
theorem zip_sem (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) :
    ∀ (l₁ : List Term), (∀ e ∈ l₁, E e) → ∀ (l₂ : List Term), (∀ e ∈ l₂, E e) → ∀ acc : List Term,
      ∃ r : List Term, Elixir.Module.Types.Descr.«zip_intersection/4» (D m) (Term.list l₁) (Term.list l₂)
          (Term.list acc) (.function false "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]) =
          .ok (Term.list (acc.reverse ++ r)) ∧ (∀ e ∈ r, E e) ∧ r.length = max l₁.length l₂.length ∧
        ∀ v, InT den Bool.false r v ↔ InT den Bool.false l₁ v ∧ InT den Bool.false l₂ v := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  intro l₁
  induction l₁ with
  | nil =>
    intro _ l₂ h₂ acc
    refine ⟨l₂, ?_, h₂, by simp, fun v => by simp [InT.open_nil]⟩
    unfold Elixir.Module.Types.Descr.«zip_intersection/4»
    exact reverse_list acc l₂
  | cons x xs ih =>
    intro h₁ l₂ h₂ acc
    cases l₂ with
    | nil =>
      refine ⟨x :: xs, ?_, h₁, by simp, fun v => by simp [InT.open_nil]⟩
      unfold Elixir.Module.Types.Descr.«zip_intersection/4»
      exact reverse_list acc (x :: xs)
    | cons y ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      obtain ⟨e, he, run⟩ := ops.inter hx hy
      obtain ⟨r, runr, hr, len, semr⟩ := ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys
        (fun e me => h₂ e (List.mem_cons_of_mem _ me)) (e :: acc)
      refine ⟨e :: r, ?_, fun e' me => ?_, by simp [len], fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«zip_intersection/4»
        simp [run n hn]
        simpa using runr
      · rcases List.mem_cons.mp me with rfl | me
        · exact he
        · exact hr e' me
      · have de := sem.inter hx hy hn (run n hn)
        cases v with
        | nil => simp [InT]
        | cons z v =>
          simp only [InT, semr v, de z]
          exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩

/-- The values of a tuple line. -/
def InPos (den : Term → V → Prop) (pos : Term) (v : List V) : Prop :=
  ∃ (tag : String) (l : List Term), pos = .tuple #[.atom tag, Term.list l] ∧ InT den (tag == "closed") l v

theorem inPos_iff {tag : String} {l : List Term} {v : List V} :
    InPos den (.tuple #[.atom tag, Term.list l]) v ↔ InT den (tag == "closed") l v := by
  constructor
  · rintro ⟨tag', l', e, h⟩
    simp only [Term.tuple.injEq] at e
    have e₁ : Term.atom tag = Term.atom tag' := by have := congrArg (fun a : Array Term => a[0]?) e; simpa using this
    have e₂ : Term.list l = Term.list l' := by have := congrArg (fun a : Array Term => a[1]?) e; simpa using this
    simp only [Term.atom.injEq] at e₁
    rw [e₁, list_inj e₂]
    exact h
  · intro h; exact ⟨tag, l, rfl, h⟩

/-- Intersecting a tuple line with a literal keeps the values of both. -/
theorem inter_sem (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) {pos lit : Term}
    (hp : TuplePos E pos) (hl : TupleOk E lit) :
    (Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok (.atom "empty") ∧
        ∀ v, InPos den pos v → ¬LitSem den lit v) ∨
      ∃ pos', Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok pos' ∧
        TuplePos E pos' ∧ ∀ v, InPos den pos' v ↔ InPos den pos v ∧ LitSem den lit v := by
  obtain ⟨t₁, l₁, rfl, g₁, e₁⟩ := hp
  obtain ⟨⟨k, t₂, l₂, rfl, g₂, e₂⟩, -⟩ := hl
  obtain ⟨v, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
  obtain ⟨r, zip, hr, len, semr⟩ := zip_sem ops sem hm l₁ e₁ l₂ e₂ []
  simp only [List.reverse_nil, List.nil_append] at zip
  have litIff : ∀ w, LitSem den (.tuple #[.integer k, .atom t₂, Term.list l₂]) w ↔ InT den (t₂ == "closed") l₂ w :=
    fun w => ⟨lit_sem, fun h => ⟨k, t₂, l₂, rfl, h⟩⟩
  unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
  simp only [length_list, Lynx.Except.ok_bind, hv]
  by_cases d : Disj t₁ t₂ l₁.length l₂.length
  · left
    refine ⟨by rw [disj.mpr d]; rfl, fun w hw hlw => ?_⟩
    rw [inPos_iff, InT.iff_open] at hw
    rw [litIff, InT.iff_open] at hlw
    rcases d with ⟨rfl, rfl, ne⟩ | ⟨rfl, rfl, lt⟩ | ⟨rfl, rfl, lt⟩
    · exact ne (by rw [← hw.2 rfl, hlw.2 rfl])
    · have := hlw.1.length_le; have := hw.2 rfl; omega
    · have := hw.1.length_le; have := hlw.2 rfl; omega
  right
  have nv : v ≠ .atom "disjoint" := fun e => d (disj.mp e)
  let tag : String := if t₁ = "open" ∧ t₂ = "open" then "open" else "closed"
  refine ⟨.tuple #[.atom tag, Term.list r], ?_, ⟨tag, r, rfl, by simp only [tag]; split <;> simp, hr⟩, fun w => ?_⟩
  · split
    · exact absurd rfl nv
    · simp only [Term.list] at zip
      by_cases o₁ : t₁ = "open" <;> by_cases o₂ : t₂ = "open" <;>
        simp [tag, o₁, o₂, Erlang.erlang.«==/2», Lynx.Except.andAlso, zip]
  rw [inPos_iff, inPos_iff, litIff, InT.iff_open, InT.iff_open (l := l₁), InT.iff_open (l := l₂), semr w]
  have nd : ¬Disj t₁ t₂ l₁.length l₂.length := d
  simp only [Disj, not_or, not_and] at nd
  rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> simp [tag, len] at nd ⊢
  all_goals first
    | (rw [Nat.max_eq_right nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩)
    | (rw [Nat.max_eq_left nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩)
    | (rw [nd, Nat.max_self]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b, c⟩, fun ⟨⟨a, c⟩, b, _⟩ => ⟨⟨a, b⟩, c⟩⟩)

theorem list_compare_inT {c : Bool} (sem : ElemSem E K V den Safe) : ∀ {l l' : List Term} {v : List V},
    (∀ e ∈ l, E e) → (∀ e ∈ l', E e) → compare (fuel (Term.list l) (Term.list l')) (Term.list l) (Term.list l') = .eq → InT den c l' v → InT den c l v
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, _, e, _ => by simp [Term.list] at e
  | _ :: _, [], _, _, _, e, _ => by simp [Term.list] at e
  | x :: l, y :: l', [], _, _, _, h => h.elim
  | x :: l, y :: l', z :: v, hl, hl', e, h => by
    simp only [Term.list, compare_cons, Ordering.then_eq_eq] at e
    exact ⟨sem.resp (hl x List.mem_cons_self) (hl' y List.mem_cons_self) e.1 h.1,
      list_compare_inT sem (fun e m => hl e (List.mem_cons_of_mem _ m)) (fun e m => hl' e (List.mem_cons_of_mem _ m))
        e.2 h.2⟩

open Classical in
/-- The valuation of tuple literals that a tuple of values induces, up to comparison. -/
noncomputable def valT (E : Term → Prop) (den : Term → V → Prop) (v : List V) (t : Term) : Bool :=
  decide (∃ t', compare (fuel t t') t t' = .eq ∧ TupleLit E t' ∧ LitSem den t' v)

theorem valT_resp (v : List V) : Resp (valT E den v) := by
  intro a b h
  simp only [valT]
  congr 1
  apply propext
  constructor
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans h e, rest⟩

theorem valT_true {v : List V} {t : Term} (ht : TupleLit E t) (h : LitSem den t v) : valT E den v t = Bool.true := by
  simp only [valT, decide_eq_true_eq]
  exact ⟨t, compare_self t, ht, h⟩

theorem valT_lit (sem : ElemSem E K V den Safe) {v : List V} {t : Term} (ht : TupleLit E t) (h : valT E den v t = Bool.true) :
    LitSem den t v := by
  simp only [valT, decide_eq_true_eq] at h
  obtain ⟨t', e, ⟨k', tag', l', rfl, -, hl'⟩, ⟨k'', tag'', l'', e', hv⟩⟩ := h
  obtain ⟨k, tag, l, rfl, -, hl⟩ := ht
  have e'' := e'
  simp only [Term.tuple.injEq] at e''
  have t₁ : Term.atom tag' = Term.atom tag'' := by have := congrArg (fun a : Array Term => a[1]?) e''; simpa using this
  have t₂ : Term.list l' = Term.list l'' := by have := congrArg (fun a : Array Term => a[2]?) e''; simpa using this
  simp only [Term.atom.injEq] at t₁
  rw [← t₁, ← list_inj t₂] at hv
  simp only [compare_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
    Ordering.then_eq_eq, List.compareLex_cons_cons] at e
  obtain ⟨-, -, et, el, -⟩ := e
  simp only [compare_eq_atom, Term.atom.injEq] at et
  subst et
  exact ⟨k, tag, l, rfl, list_compare_inT sem hl hl' el hv⟩

theorem valT_iff (sem : ElemSem E K V den Safe) {v : List V} {t : Term} (ht : TupleLit E t) :
    valT E den v t = Bool.true ↔ LitSem den t v := ⟨valT_lit sem ht, valT_true ht⟩

/-- A line whose values its negations cover is empty, whether some element is empty or not. -/
theorem top_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    (S : List (Term × Term)) (hS : Safe S) {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed") (el : ∀ e ∈ l, E e)
    {negs : List Term} (lits : ∀ t ∈ negs, TupleLit E t)
    (cover : ∀ v, InT den (tag == "closed") l v → ∃ N ∈ negs, LitSem den N v) :
    Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4» (D m) (.atom tag) (Term.list l) (Term.list negs) (.map S) =
      .ok (.atom "true") := by
  obtain ⟨b, check, full⟩ := elements_check ops S l el
  rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
  simp only [check m hm, Lynx.Except.ok_bind]
  cases b
  rotate_left
  · simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso]
  have full := full rfl
  have hm' : K ≤ m := by omega
  have nonempty : negs ≠ [] := by
    rintro rfl
    obtain ⟨v, hv, -⟩ := tuple_witness sem hS l full (tag == "closed") 0
    obtain ⟨N, mN, -⟩ := cover v hv
    simp at mN
  have notNil : Erlang.erlang.«==/2» (Term.list negs) .nil = .ok (.atom "false") := by
    cases negs with
    | nil => exact absurd rfl nonempty
    | cons x xs => simp [Erlang.erlang.«==/2», Term.list, Term.false]
  simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, notNil]
  have := line_complete ops dops sem hm' S hS negs lits (tag == "closed") l full cover
  rcases g with rfl | rfl <;> simpa using this

/-- No tuple value along the path, outside the negated literals, satisfies the BDD. -/
def ValUnsat (E : Term → Prop) (den : Term → V → Prop) (pos : Term) (negs : List Term) (r : Term) : Prop :=
  ∀ v, InPos den pos v → (∀ N ∈ negs, ¬LitSem den N v) → eval (valT E den v) r = Bool.false

theorem cover_of_unsat {pos : Term} {negs : List Term} {v : List V}
    (h : InPos den pos v → (∀ N ∈ negs, ¬LitSem den N v) → False) (hv : InPos den pos v) :
    ∃ N ∈ negs, LitSem den N v :=
  Classical.byContradiction fun none => h hv fun N mN hN => none ⟨N, mN, hN⟩

theorem tuple_bdd_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m)
    (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos → (∀ t ∈ negs, TupleLit E t) → ValUnsat E den pos negs r →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true") := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos →
    (∀ t ∈ negs, TupleLit E t) → ValUnsat E den pos negs r →
    Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits g
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    simp only
    exact top_val ops dops sem hm S hS gt el lits fun v hv =>
      cover_of_unsat (fun hv' nn => by have := g v hv' nn; simp at this) (inPos_iff.mpr hv)
  · intro ok _ pos negs _ _ _
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    split <;> simp_all
  · intro ok k x y okl okLit pos negs hp lits g
    have hl := okLit _ okl
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_sem ops sem hm hp hl with ⟨empty, -⟩ | ⟨pos', run, hp', sem'⟩
    · simp [empty]
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    simp [run]
    refine top_val ops dops sem hm S hS gt el lits fun v hv => ?_
    obtain ⟨hpos, hlit⟩ := (sem' v).mp (inPos_iff.mpr hv)
    refine cover_of_unsat (fun hv' nn => ?_) hpos
    have := g v hv' nn
    rw [eval_leaf, valT_true hl.1 hlit] at this
    cases this
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits g
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → TupleOk E t := fun t ht => okLit t ht.1
    have dPart : Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list (lit :: negs)) d (.map S) =
        .ok (.atom "true") := by
      refine idd okLit' pos (lit :: negs) hp (fun t m => ?_) fun v hv nn => ?_
      · rcases List.mem_cons.mp m with rfl | m
        · exact hl.1
        · exact lits t m
      have nl : valT E den v lit = Bool.false := by
        cases e : valT E den v lit
        · rfl
        · exact absurd (valT_lit sem hl.1 e) (nn lit List.mem_cons_self)
      have := g v hv fun N mN => nn N (List.mem_cons_of_mem _ mN)
      simp only [eval_node, nl] at this
      simp at this
      exact this.2
    have uPart := iu okLit' pos negs hp lits fun v hv nn => by
      have := g v hv nn
      simp only [eval_node] at this
      cases hu' : eval (valT E den v) u
      · rfl
      · simp [hu'] at this
    rw [list_cons] at dPart
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_sem ops sem hm ⟨tag, l, rfl, gt, el⟩ hl with ⟨empty, -⟩ | ⟨pos2, run, hp2, sem2⟩
    · simp [empty, dPart, uPart, Lynx.Except.andAlso]
    have cRes := ic okLit' pos2 negs hp2 lits fun v hv nn => by
      obtain ⟨hpos, hlit⟩ := (sem2 v).mp hv
      have := g v hpos nn
      simp only [eval_node, valT_true hl.1 hlit] at this
      simp at this
      exact this.1
    obtain ⟨tag2, l2, rfl, -⟩ := hp2
    simp [run, dPart, uPart, Lynx.Except.andAlso, cRes]

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Values of basic types: the bits of bitmaps, atoms, and the values of the top function, list, tuple, and
map types. -/

inductive FV where
  | bit (i : Fin 8)
  | atom (q : Term)
  | kind (k : Fin 4)

def kindName (k : Fin 4) : String :=
  match k.val with
  | 0 => "fun"
  | 1 => "list"
  | 2 => "tuple"
  | _ => "map"

theorem kindName_ne (k : Fin 4) : kindName k ≠ "bitmap" ∧ kindName k ≠ "atom" := by
  obtain ⟨k, lt⟩ := k
  simp only [kindName]
  match k, lt with
  | 0, _ | 1, _ | 2, _ | 3, _ => decide

/-- The top fields of basic types are named by kinds. -/
theorem kind_of {M : List (Term × Term)} (basic : Basic M) {name : String} (b : name ≠ "bitmap") (a : name ≠ "atom")
    (h : has M name = Bool.true) : ∃ k, kindName k = name := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  rcases basic.keys (.atom name) (by simp [hw]) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
    subst e
  · exact absurd rfl b
  · exact absurd rfl a
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The values of basic types, where the top type holds every value. -/
def denF (e : Term) (v : FV) : Prop :=
  match e with
  | .map M =>
    match v with
    | .bit i => (bits M).testBit i = Bool.true
    | .atom q => amem M q = Bool.true
    | .kind k => has M (kindName k) = Bool.true
  | _ => True

/-- Seen sets that keep the emptiness of basic types exact. -/
def SafeF (S : List (Term × Term)) : Prop := SeenOk (.map S)

theorem denF_none (v : FV) : ¬denF (.map []) v := by
  cases v <;> simp [denF, bits, amem, amemV, has, mapLookup]

/-- Basic types without values have no fields. -/
theorem basic_nil_of {M : List (Term × Term)} (basic : Basic M) (none : ∀ v, ¬denF (.map M) v) : M = [] := by
  refine basic_empty basic ?_ (fun q => ?_) fun name b a => ?_
  · have le := bits_le basic
    refine Nat.eq_of_testBit_eq fun i => ?_
    by_cases lt : i < 8
    · have := none (.bit ⟨i, lt⟩)
      simp only [denF] at this
      simpa using this
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt le (by
        have : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        omega))]
      simp
  · have := none (.atom q)
    simp only [denF] at this
    simpa using this
  · cases h : has M name with
    | false => rfl
    | true =>
      obtain ⟨k, rfl⟩ := kind_of basic b a h
      have := none (.kind k)
      simp only [denF] at this
      exact absurd h this

theorem lookup_rel {M M' : List (Term × Term)} (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) (q : Term) :
    Option.Rel (fun x y => compare (fuel x y) x y = .eq) (mapLookup M q) (mapLookup M' q) :=
  lookup_of_map_compare_eq M M' h q

theorem rel_isSome {a b : Option Term} (h : Option.Rel (fun x y => compare (fuel x y) x y = .eq) a b) : a.isSome = b.isSome := by
  cases h <;> rfl

theorem bits_resp {M M' : List (Term × Term)} (bM : Basic M) (bM' : Basic M') (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) :
    bits M = bits M' := by
  have r := lookup_rel h (.atom "bitmap")
  simp only [bits]
  cases hx : mapLookup M (.atom "bitmap") <;> cases hy : mapLookup M' (.atom "bitmap") <;> rw [hx, hy] at r <;>
    cases r <;> try rfl
  rename_i x y e
  obtain ⟨b, rfl, -⟩ := bM.bitmap x hx
  obtain ⟨b', rfl, -⟩ := bM'.bitmap y hy
  simp at e
  simp [e]

theorem amem_resp {M M' : List (Term × Term)} (bM : Basic M) (bM' : Basic M') (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq)
    (q : Term) : amem M q = amem M' q := by
  have r := lookup_rel h (.atom "atom")
  simp only [amem]
  cases hx : mapLookup M (.atom "atom") <;> cases hy : mapLookup M' (.atom "atom") <;> rw [hx, hy] at r <;>
    cases r <;> try rfl
  rename_i x y e
  obtain ⟨⟨p, S, rfl, -⟩, -⟩ := bM.atom x hx
  obtain ⟨⟨p', S', rfl, -⟩, -⟩ := bM'.atom y hy
  simp only [compare_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
    Ordering.then_eq_eq, List.compareLex_cons_cons] at e
  obtain ⟨-, et, es, -⟩ := e
  have same := rel_isSome (lookup_rel es q)
  cases p <;> cases p' <;> simp at et <;> simp [amemV, same]

theorem has_resp {M M' : List (Term × Term)} (h : compare (fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) (name : String) :
    has M name = has M' name :=
  rel_isSome (lookup_rel h (.atom name))

theorem denF_term (v : FV) : denF (.atom "term") v := trivial

theorem denF_inter {a b c : Term} {m : Nat} (ha : LElem a) (hb : LElem b) (hm : 2 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) (v : FV) :
    denF c v ↔ denF a v ∧ denF b v := by
  rcases ha with rfl | ⟨A, rfl, bA⟩
  · have : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.atom "term") b = .ok b := by
      unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
    rw [this] at run; cases run
    simp [denF_term]
  rcases hb with rfl | ⟨B, rfl, bB⟩
  · rw [inter_term_right] at run; cases run
    simp [denF_term]
  obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, run', -, hbits, hamem, hhas⟩ := inter_basic depth A B bA bB
  rw [run'] at run; cases run
  cases v with
  | bit i => simp [denF, hbits, Nat.testBit_and]
  | atom q => simp [denF, hamem]
  | kind k => simp [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2]

theorem term_bits {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) (v : FV) :
    denF (.map T) v := by
  obtain ⟨-, hbits, hamem, hhas⟩ := term_basic term
  cases v with
  | bit i =>
    obtain ⟨i, lt⟩ := i
    simp only [denF, hbits]
    match i, lt with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
  | atom q => simp [denF, hamem]
  | kind k =>
    simp only [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2]
    obtain ⟨k, lt⟩ := k
    simp only [kindName]
    match k, lt with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl

theorem denF_diff {a b c : Term} {m : Nat} (ha : LElem a) (hb : LElem b) (hm : 2 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) (v : FV) :
    denF c v ↔ denF a v ∧ ¬denF b v := by
  rcases hb with rfl | ⟨B, rfl, bB⟩
  · rw [diff_term_right] at run; cases run
    simp [denF_term, denF_none]
  by_cases empty : B = []
  · subst empty
    have : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a (.map []) = .ok a := by
      unfold Elixir.Module.Types.Descr.«bare_difference/2»
      rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]
    rw [this] at run; cases run
    simp [denF_none]
  obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, bA⟩
  · obtain ⟨T, term, -⟩ := unfolded_term_fields
    obtain ⟨C, run', -, hbits, hamem, hhas⟩ := diff_basic depth (.atom "term") T B (term_basic term).1 bB
      (Or.inr ⟨rfl, empty, term⟩)
    rw [run'] at run; cases run
    have all := term_bits term v
    cases v with
    | bit i => simp [denF, hbits, testBit_sub_and] at all ⊢; simp [all]
    | atom q => simp [denF, hamem] at all ⊢; simp [all]
    | kind k => simp [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2] at all ⊢; simp [all]
  · obtain ⟨C, run', -, hbits, hamem, hhas⟩ := diff_basic depth (.map A) A B bA bB (Or.inl rfl)
    rw [run'] at run; cases run
    cases v with
    | bit i => simp [denF, hbits, testBit_sub_and]
    | atom q => simp [denF, hamem]
    | kind k => simp [denF, hhas _ (kindName_ne k).1 (kindName_ne k).2]

theorem denF_empty {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool} (ha : LElem a) (hS : SafeF S)
    (run : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v, ¬denF a v := by
  rcases ha with rfl | ⟨M, rfl, bM⟩
  · have : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.atom "term") (.map S) = .ok (boolAtom Bool.false) := by
      rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl
    rw [this] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    simp only [Bool.false_eq_true, false_iff]
    exact fun none => none (.bit 0) trivial
  by_cases nil : M = []
  · subst nil
    rw [empty_none_seen] at run
    have : b = Bool.true := by cases b <;> simp_all [boolAtom]
    subst this
    simp [denF_none]
  · rw [empty_basic (D m) bM hS nil] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    simp only [Bool.false_eq_true, false_iff]
    exact fun none => nil (basic_nil_of bM none)

theorem denF_resp {e e' : Term} {v : FV} (he : LElem e) (he' : LElem e') (h : compare (fuel e e') e e' = .eq) (d : denF e' v) :
    denF e v := by
  rcases he with rfl | ⟨M, rfl, bM⟩
  · exact trivial
  rcases he' with rfl | ⟨M', rfl, bM'⟩
  · simp at h
  cases v with
  | bit i => simpa [denF, bits_resp bM bM' h] using d
  | atom q => simpa [denF, amem_resp bM bM' h] using d
  | kind k => simpa [denF, has_resp h] using d

theorem flatSem : ElemSem LElem 2 FV denF SafeF :=
  ⟨denF_term, fun ha hb hm run => denF_inter ha hb hm run, fun ha hb hm run => denF_diff ha hb hm run,
    fun ha hS _ run => denF_empty ha hS run, ⟨.bit 0⟩, fun he he' h d => denF_resp he he' h d⟩

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

theorem open_leaf_other (d : Dispatcher) (b : Term) (kL : Int) (fo sub : Term)
    (nb : b ≠ .atom "bdd_bot") (nt : b ≠ .atom "bdd_top")
    (nl : ∀ (k : Term) cl, b ≠ .tuple #[k, .atom "closed", cl])
    (nn : ∀ (h k : Term) cl c u d', b ≠ .tuple #[h, .tuple #[k, .atom "closed", cl], c, u, d']) :
    Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
      Elixir.Module.Types.Descr.«bdd_intersection/2» b (.tuple #[.integer kL, .atom "open", fo]) := by
  rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
  split
  · exact absurd rfl nb
  · exact absurd rfl nt
  · exact absurd rfl (nl _ _)
  · exact absurd rfl (nn _ _ _ _ _ _)
  · rfl

theorem open_leaf_inter {Val : (Term → Bool) → Prop} (resp : ∀ ρ, Val ρ → Resp ρ) {ok₁ : Term → Prop} {b L : Term}
    (wb : Bdd ok₁ b) (hL : Bdd ok₁ L) :
    ∃ r', Elixir.Module.Types.Descr.«bdd_intersection/2» b L = .ok r' ∧
      (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P L → Bdd P r') ∧ ∀ ρ, Val ρ → eval ρ r' = (eval ρ b && eval ρ L) := by
  obtain ⟨r', hr, okr, semr⟩ := inter_ok wb hL
  exact ⟨r', hr, fun P sub hP => okr P (wb.mono sub) (hL.mono fun t h => sub t h), fun ρ v => semr ρ (resp ρ v)⟩

theorem eq_cmp (a b : Term) [Decidable (Term.compare (Term.fuel a b) a b = .eq)] :
    Erlang.erlang.«==/2» a b = .ok (.atom (if Term.compare (Term.fuel a b) a b = .eq then "true" else "false")) := by
  by_cases h : Term.compare (Term.fuel a b) a b = .eq <;> simp [Erlang.erlang.«==/2», h, Term.true, Term.false]

theorem open_leaf_ok {Val : (Term → Bool) → Prop} (resp : ∀ ρ, Val ρ → Resp ρ) {ok : Term → Prop} {d : Dispatcher}
    {sub fo : Term} {kL : Int} (hL : ok (.tuple #[.integer kL, .atom "open", fo]))
    (order : ∀ (k : Int) cl, ok (.tuple #[.integer k, .atom "closed", cl]) →
      Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer kL, .atom "open", fo])) (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer kL, .atom "open", fo]) = .lt)
    (spec : ∀ (k : Int) cl, ok (.tuple #[.integer k, .atom "closed", cl]) → ∃ c : Bool,
      d.pure sub #[cl, fo] = .ok (boolAtom c) ∧ (c = Bool.true → ∀ ρ, Val ρ →
        ρ (.tuple #[.integer k, .atom "closed", cl]) = Bool.true → ρ (.tuple #[.integer kL, .atom "open", fo]) = Bool.true)) :
    ∀ ok₁ b, Bdd ok₁ b → (∀ t, ok₁ t → ok t) → ∃ r,
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        .ok r ∧ (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P r) ∧
      ∀ ρ, Val ρ → eval ρ r = (eval ρ b && ρ (.tuple #[.integer kL, .atom "open", fo])) := by
  have wL : ∀ {P : Term → Prop}, P (.tuple #[.integer kL, .atom "open", fo]) →
      Bdd P (.tuple #[.integer kL, .atom "open", fo]) := fun h => Bdd.leaf_iff.mpr h
  have fallback : ∀ {ok₁ : Term → Prop} {b : Term}, Bdd ok₁ b →
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        Elixir.Module.Types.Descr.«bdd_intersection/2» b (.tuple #[.integer kL, .atom "open", fo]) → ∃ r,
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        .ok r ∧ (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P r) ∧
      ∀ ρ, Val ρ → eval ρ r = (eval ρ b && ρ (.tuple #[.integer kL, .atom "open", fo])) := by
    intro ok₁ b wb e
    obtain ⟨r, hr, okr, semr⟩ := open_leaf_inter resp (ok₁ := fun t => ok₁ t ∨ t = .tuple #[.integer kL, .atom "open", fo])
      (wb.mono fun t h => Or.inl h) (wL (Or.inr rfl))
    refine ⟨r, by rw [e, hr], fun P sub hP => okr P (fun t h => h.elim (sub t) (fun e => e ▸ hP)) hP, fun ρ v => ?_⟩
    rw [semr ρ v, eval_leaf]
  refine Bdd.induction (P := fun ok₁ b => (∀ t, ok₁ t → ok t) → ∃ r,
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d b (.tuple #[.integer kL, .atom "open", fo]) sub =
        .ok r ∧ (∀ P : Term → Prop, (∀ t, ok₁ t → P t) → P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P r) ∧
      ∀ ρ, Val ρ → eval ρ r = (eval ρ b && ρ (.tuple #[.integer kL, .atom "open", fo]))) ?_ ?_ ?_ ?_
  · intro ok₁ _
    refine ⟨_, by rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]; rfl, fun P _ hP => wL hP,
      fun ρ _ => by simp [eval]⟩
  · intro ok₁ _
    refine ⟨_, by rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]; rfl, fun P _ _ => Bdd.bot,
      fun ρ _ => by simp⟩
  · intro ok₁ k x y okl sub₁
    by_cases hx : x = .atom "closed"
    · subst hx
      obtain ⟨c, run, sc⟩ := spec k y (sub₁ _ okl)
      cases c
      · refine fallback (Bdd.leaf_iff.mpr okl) ?_
        rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
        simp [run, isMember, boolAtom]
      · refine ⟨_, ?_, fun P sub _ => Bdd.leaf_iff.mpr (sub _ okl), fun ρ v => ?_⟩
        · rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
          simp [run, isMember, boolAtom]
        · have := sc rfl ρ v
          simp only [eval_leaf]
          revert this
          cases ρ (.tuple #[.integer k, .atom "closed", y]) <;> cases ρ (.tuple #[.integer kL, .atom "open", fo]) <;> simp
    · refine fallback (Bdd.leaf_iff.mpr okl) (open_leaf_other _ _ _ _ _ (by simp) (by simp) (fun k' cl e => ?_)
        (fun h k' cl c u d' e => by simp at e))
      simp at e
      exact hx e.2.1
  · intro ok₁ hh lit c u d' isLeaf okl hc hu hd ic iu id sub₁
    obtain ⟨k, x, y, rfl⟩ := isLeaf
    have w : Bdd ok₁ (.tuple #[.integer hh, .tuple #[.integer k, x, y], c, u, d']) :=
      Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, okl, hc, hu, hd⟩
    by_cases hx : x ≠ .atom "closed"
    · refine fallback w (open_leaf_other _ _ _ _ _ (by simp) (by simp) (fun k' cl e => by simp at e)
        (fun h k' cl c' u' d'' e => ?_))
      simp at e
      exact hx e.2.1.2.1
    have hx' : x = .atom "closed" := Classical.byContradiction hx
    subst hx'
    have sub' : ∀ t, Above ok₁ (.tuple #[.integer k, .atom "closed", y]) t → ok t := fun t ht => sub₁ t ht.1
    have below := order k y (sub₁ _ okl)
    obtain ⟨c₀, run, sc⟩ := spec k y (sub₁ _ okl)
    obtain ⟨nu, hnu, bnu, snu⟩ := iu sub'
    obtain ⟨nd, hnd, bnd, snd⟩ := id sub'
    obtain ⟨nc, hnc, bnc, snc⟩ : ∃ nc, (match c₀ with
        | Bool.true => (Except.ok c : Except Exception Term)
        | Bool.false => Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d c
            (.tuple #[.integer kL, .atom "open", fo]) sub) = .ok nc ∧
        (∀ P : Term → Prop, (∀ t, Above ok₁ (.tuple #[.integer k, .atom "closed", y]) t → P t) →
          P (.tuple #[.integer kL, .atom "open", fo]) → Bdd P nc) ∧
        ∀ ρ, Val ρ → (ρ (.tuple #[.integer k, .atom "closed", y]) && eval ρ nc) =
          (ρ (.tuple #[.integer k, .atom "closed", y]) && eval ρ c && ρ (.tuple #[.integer kL, .atom "open", fo])) := by
      cases c₀
      · obtain ⟨nc, hnc, bnc, snc⟩ := ic sub'
        exact ⟨nc, hnc, bnc, fun ρ v => by rw [snc ρ v, Bool.and_assoc]⟩
      · refine ⟨c, rfl, fun P sub _ => hc.mono sub, fun ρ v => ?_⟩
        have := sc rfl ρ v
        revert this
        cases ρ (.tuple #[.integer k, .atom "closed", y]) <;> cases ρ (.tuple #[.integer kL, .atom "open", fo]) <;>
          cases eval ρ c <;> simp
    have liftA : ∀ {P : Term → Prop}, (∀ t, ok₁ t → P t) →
        ∀ t, Above ok₁ (.tuple #[.integer k, .atom "closed", y]) t → Above P (.tuple #[.integer k, .atom "closed", y]) t :=
      fun sub t ht => ⟨sub t ht.1, ht.2⟩
    have ncOk := bnc (Above ok (.tuple #[.integer k, .atom "closed", y])) (liftA sub₁) ⟨hL, below⟩
    have nuOk := bnu (Above ok (.tuple #[.integer k, .atom "closed", y])) (liftA sub₁) ⟨hL, below⟩
    have ndOk := bnd (Above ok (.tuple #[.integer k, .atom "closed", y])) (liftA sub₁) ⟨hL, below⟩
    have semNode : ∀ ρ, Val ρ →
        eval ρ (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], nc, nu, nd]) =
          (eval ρ (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], c, u, d']) &&
            ρ (.tuple #[.integer kL, .atom "open", fo])) := by
      intro ρ v
      have hc' := snc ρ v
      simp only [eval_node, snu ρ v, snd ρ v]
      revert hc'
      cases ρ (.tuple #[.integer k, .atom "closed", y]) <;> cases ρ (.tuple #[.integer kL, .atom "open", fo]) <;>
        cases eval ρ c <;> cases eval ρ u <;> cases eval ρ d' <;> cases eval ρ nc <;> simp
    have runBlock : Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d
        (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], c, u, d']) (.tuple #[.integer kL, .atom "open", fo])
        sub = (do
          let r ← Lynx.Except.andAlso (Lynx.Except.andAlso (Erlang.erlang.«==/2» nc c) (Erlang.erlang.«==/2» nu u))
            (Erlang.erlang.«==/2» nd d')
          match r with
          | .atom "false" => Elixir.Module.Types.Descr.«bdd_node_new/4» (.tuple #[.integer k, .atom "closed", y]) nc nu nd
          | .atom "true" => pure (.tuple #[.integer hh, .tuple #[.integer k, .atom "closed", y], c, u, d'])
          | r => .error (.error (.tuple #[.atom "case_clause", r]))) := by
      rw [Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3».eq_def]
      cases c₀
      · simp only at hnc
        simp [run, isMember, boolAtom, hnc, hnu, hnd]
        rfl
      · simp only [Except.ok.injEq] at hnc
        subst hnc
        simp [run, isMember, boolAtom, hnu, hnd]
        rfl
    classical
    by_cases same : Term.compare (Term.fuel nc c) nc c = .eq ∧ Term.compare (Term.fuel nu u) nu u = .eq ∧ Term.compare (Term.fuel nd d') nd d' = .eq
    · obtain ⟨e₁, e₂, e₃⟩ := same
      refine ⟨_, ?_, fun P sub _ => w.mono sub, fun ρ v => ?_⟩
      · rw [runBlock]; simp [eq_cmp, e₁, e₂, e₃, Lynx.Except.andAlso]
      · rw [← semNode ρ v]
        simp only [eval_node, eval_congr_cmp ncOk (resp ρ v) e₁, eval_congr_cmp nuOk (resp ρ v) e₂,
          eval_congr_cmp ndOk (resp ρ v) e₃]
    · obtain ⟨hn, runn⟩ := node_new (.tuple #[.integer k, .atom "closed", y]) nc nu nd ⟨k, _, y, rfl⟩ ncOk nuOk ndOk
      refine ⟨.tuple #[.integer hn, .tuple #[.integer k, .atom "closed", y], nc, nu, nd], ?_,
        fun P sub hP => Bdd.node_iff.mpr ⟨⟨k, _, y, rfl⟩, sub _ okl, bnc _ (liftA sub)
        ⟨hP, below⟩, bnu _ (liftA sub) ⟨hP, below⟩, bnd _ (liftA sub) ⟨hP, below⟩⟩,
        fun ρ v => by simpa only [eval_node] using semNode ρ v⟩
      rw [runBlock, ← runn]
      by_cases e₁ : Term.compare (Term.fuel nc c) nc c = .eq <;> by_cases e₂ : Term.compare (Term.fuel nu u) nu u = .eq <;>
        by_cases e₃ : Term.compare (Term.fuel nd d') nd d' = .eq
      · exact absurd ⟨e₁, e₂, e₃⟩ same
      all_goals simp [eq_cmp, e₁, e₂, e₃, Lynx.Except.andAlso]

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of tuple literals. -/

/-- Lists related pairwise. -/
def Pairs (R : Term → Term → Prop) : List Term → List Term → Prop
  | [], [] => True
  | x :: xs, y :: ys => R x y ∧ Pairs R xs ys
  | _, _ => False

theorem Pairs.snoc {R : Term → Term → Prop} : ∀ {a b : List Term}, Pairs R a b → ∀ {x y : Term}, R x y →
    Pairs R (a ++ [x]) (b ++ [y])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, p, _, _, h => ⟨p.1, Pairs.snoc p.2 h⟩
  | [], _ :: _, p, _, _, _ => p.elim
  | _ :: _, [], p, _, _, _ => p.elim

theorem Pairs.mono {R R' : Term → Term → Prop} (h : ∀ x y, R x y → R' x y) : ∀ {a b : List Term}, Pairs R a b →
    Pairs R' a b
  | [], [], _ => trivial
  | _ :: _, _ :: _, p => ⟨h _ _ p.1, Pairs.mono h p.2⟩
  | [], _ :: _, p => p.elim
  | _ :: _, [], p => p.elim

theorem Pairs.swap {R R' : Term → Term → Prop} (h : ∀ x y, R x y → R' y x) : ∀ {a b : List Term}, Pairs R a b →
    Pairs R' b a
  | [], [], _ => trivial
  | _ :: _, _ :: _, p => ⟨h _ _ p.1, Pairs.swap h p.2⟩
  | [], _ :: _, p => p.elim
  | _ :: _, [], p => p.elim

theorem Pairs.append {R : Term → Term → Prop} : ∀ {a b : List Term}, Pairs R a b → ∀ {c d : List Term}, Pairs R c d →
    Pairs R (a ++ c) (b ++ d)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, p, _, _, h => ⟨p.1, Pairs.append p.2 h⟩
  | [], _ :: _, p, _, _, _ => p.elim
  | _ :: _, [], p, _, _, _ => p.elim

theorem plus_one (n : Nat) : Erlang.erlang.«+/2» (.integer (n : Int)) (.integer 1) = .ok (.integer ((n + 1 : Nat) : Int)) := by
  rw [Erlang.erlang.«+/2_integers»]; congr 2

theorem strategy_start (d : Dispatcher) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) :
    Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» d (.atom t₁) (Term.list l₁) (.atom t₂) (Term.list l₂) =
      if t₁ = t₂ ∧ l₁.length = l₂.length then
        Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l₁) (Term.list l₂) (.integer 0)
          (.atom "all_equal")
      else if t₁ = "open" ∧ l₁.length ≤ l₂.length then
        Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l₁) (Term.list l₂) (.integer 0)
          (.atom "right_subtype_of_left")
      else if t₂ = "open" ∧ l₂.length ≤ l₁.length then
        Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l₁) (Term.list l₂) (.integer 0)
          (.atom "left_subtype_of_right")
      else .ok (.atom "none") := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4»
  have le : (Ord.compare (l₁.length : Int) l₂.length).isLE = decide (l₁.length ≤ l₂.length) := by
    rcases Nat.lt_trichotomy l₁.length l₂.length with h | h | h
    · have : Ord.compare (l₁.length : Int) l₂.length = .lt := Int.compare_eq_lt.mpr (by omega)
      simp [this]; omega
    · simp [h]
    · have : Ord.compare (l₁.length : Int) l₂.length = .gt := Int.compare_eq_gt.mpr (by omega)
      simp [this]; omega
  have ge : (Ord.compare (l₁.length : Int) l₂.length).isGE = decide (l₂.length ≤ l₁.length) := by
    rcases Nat.lt_trichotomy l₁.length l₂.length with h | h | h
    · have : Ord.compare (l₁.length : Int) l₂.length = .lt := Int.compare_eq_lt.mpr (by omega)
      simp [this]; omega
    · simp [h]
    · have : Ord.compare (l₁.length : Int) l₂.length = .gt := Int.compare_eq_gt.mpr (by omega)
      simp [this]; omega
  have eqc : ((l₁.length : Int) = l₂.length) = (l₁.length = l₂.length) := by simp only [eq_iff_iff]; omega
  rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
    by_cases e : l₁.length = l₂.length <;> by_cases e' : l₁.length ≤ l₂.length <;>
    by_cases e'' : l₂.length ≤ l₁.length <;>
    simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», Erlang.erlang.«and/2»,
      Erlang.erlang.«=</2», Erlang.erlang.«>=/2», le, ge, eqc, e, e', e'',
      Term.true, Term.false] <;> omega

theorem split_full {c₁ s₁ c₂ s₂ : List Term} (lc : c₁.length = c₂.length) (sc : s₁ = [] ∨ s₂ = [])
    (le : (c₁ ++ s₁).length ≤ (c₂ ++ s₂).length) : s₁ = [] := by
  rcases sc with h | h
  · exact h
  · subst h; simp at le; cases s₁ with
    | nil => rfl
    | cons _ _ => simp at le; omega

theorem aob_bool (e : Term) : ∃ c : Bool, Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» e = .ok (boolAtom c) := by
  unfold Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1»
  cases e with
  | map X =>
    simp only
    split
    · simp [Erlang.erlang.«map_size/1»]; exact (Classical.em _).symm
    · split
      · simp [Erlang.erlang.«map_size/1»]; exact (Classical.em _).symm
      · split
        · simp [Erlang.erlang.«map_size/1»]; exact (Classical.em _).symm
        · exact ⟨Bool.false, rfl⟩
  | _ => exact ⟨Bool.false, by simp [getMapKeys]⟩

def StatusForm (res : Term) : Prop :=
  res = .atom "all_equal" ∨
    (∃ (j : Int) (d₁ d₂ : Term), res = .tuple #[.atom "one_index_difference", .integer j, d₁, d₂]) ∨
    res = .atom "left_subtype_of_right" ∨ res = .atom "right_subtype_of_left" ∨ res = .atom "none"

theorem set_mid : ∀ (a : List Term) (x u : Term) (b : List Term), (a ++ x :: b).set a.length u = a ++ u :: b
  | [], _, _, _ => rfl
  | _ :: a, x, u, b => by simp [set_mid a x u b]

theorem list_eq_nil {l : List Term} : Term.list l = .nil ↔ l = [] := by
  cases l <;> simp [Term.list]

/-- The status a strategy walk ends with: equal elements make either tuple a subtype of the other. -/
def endSt : Term → Term
  | .atom "all_equal" => .atom "left_subtype_of_right"
  | st => st

theorem endSt_ne (st : Term) : endSt st ≠ .atom "all_equal" := by
  unfold endSt; split <;> simp_all

theorem endSt_of_ne {st : Term} (h : st ≠ .atom "all_equal") : endSt st = st := by
  unfold endSt; split <;> simp_all

theorem index_nil_left (d : Dispatcher) (l : List Term) (i st : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list []) (Term.list l) i st = .ok (endSt st) := by
  rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
  cases l <;> simp only [Term.list] <;> unfold endSt <;> split <;> simp_all

theorem index_nil_right (d : Dispatcher) (l : List Term) (i st : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l) (Term.list []) i st = .ok (endSt st) := by
  rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
  cases l <;> simp only [Term.list] <;> unfold endSt <;> split <;> simp_all

/-- Uniting with all tuples never falls back to the plain union. -/
theorem strategy_top_none (d : Dispatcher) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) (top : (t₁ = "open" ∧ l₁ = []) ∨ (t₂ = "open" ∧ l₂ = []))
    (run : Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» d (.atom t₁) (Term.list l₁) (.atom t₂)
      (Term.list l₂) = .ok (.atom "none")) : False := by
  rw [strategy_start d t₁ t₂ g₁ g₂] at run
  rcases top with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · split at run
    · rw [index_nil_left] at run; simp [endSt] at run
    · split at run
      · rw [index_nil_left] at run; simp [endSt] at run
      · rename_i h₁ h₂; simp at h₂
  · split at run
    · rw [index_nil_right] at run; simp [endSt] at run
    · split at run
      · rw [index_nil_right] at run; simp [endSt] at run
      · split at run
        · rw [index_nil_right] at run; simp [endSt] at run
        · rename_i h₁ h₂ h₃; simp at h₃

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Fusing tuple literals of flat element types. -/

theorem Pairs.refl {R : Term → Term → Prop} (h : ∀ x, R x x) : ∀ l : List Term, Pairs R l l
  | [] => trivial
  | x :: l => ⟨h x, Pairs.refl h l⟩

/-- The number of literals in a BDD, regardless of hashes. -/
def bsize (t : Term) : Nat :=
  match t with
  | .tuple ⟨[_, _, c, u, d]⟩ => 1 + bsize c + bsize u + bsize d
  | .tuple ⟨[_, _, _]⟩ => 1
  | _ => 0
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem bsize_node (h lit c u d : Term) : bsize (.tuple #[h, lit, c, u, d]) = 1 + bsize c + bsize u + bsize d := by
  rw [bsize]

theorem bsize_leaf (k x y : Term) : bsize (.tuple #[k, x, y]) = 1 := by
  rw [bsize]

theorem bsize_atom (s : String) : bsize (.atom s) = 0 := by
  rw [bsize]
  all_goals intros; simp_all

theorem tuple_union_right {x : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) (k : Term) :
    Elixir.Module.Types.Descr.«tuple_union/2» x (.tuple #[k, .atom "open", .nil]) = .ok (.tuple #[k, .atom "open", .nil]) := by
  unfold Elixir.Module.Types.Descr.«tuple_union/2»
  split
  · exact (hx _ rfl).elim
  · rename_i e; simp at e; subst e; rfl
  · rename_i h; exact (h _ rfl).elim

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Negations of tuple types of flat element types. -/

theorem opt_bdd_seen_map (S : List (Term × Term)) (op a b : Term) :
    Elixir.Module.Types.Descr.«opt_bdd_seen/4» (.map S) op a b = .ok (.atom "seen") ∨
      ∃ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» (.map S) op a b = .ok (.tuple #[.atom "ok", .map S']) := by
  unfold Elixir.Module.Types.Descr.«opt_bdd_seen/4»
  cases h : mapLookup S (.tuple #[op, a, b]) with
  | none => exact Or.inr ⟨(.tuple #[op, a, b], .atom "true") :: S, by simp [getMapKeys_single, h, Erlang.maps.«put/3»]⟩
  | some w => exact Or.inl (by simp [getMapKeys_single, h])

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Fields of optimized operations, on points whose tuples are tuples of values. -/

theorem opt_union4_eq (d : Dispatcher) {name : String}
    (h : name = "bitmap" ∨ name = "atom" ∨ name = "fun" ∨ name = "list") (x y S : Term) :
    Elixir.Module.Types.Descr.«opt_union/4» d (.atom name) x y S =
      Elixir.Module.Types.Descr.«bare_union/3» d (.atom name) x y := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem opt_diff4_eq (n : Nat) {name t x : Term} (h : name = .atom "bitmap" ∨ name = .atom "atom" ∨ name = .atom "fun")
    (S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/4» (D n) name t x S =
      Elixir.Module.Types.Descr.«bare_difference/3» (D n) name t x := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem opt_inter4_eq (n : Nat) {name x y : Term} (h : name = .atom "bitmap" ∨ name = .atom "atom" ∨ name = .atom "fun")
    (S : Term) :
    Elixir.Module.Types.Descr.«opt_intersection/4» (D n) name x y S =
      Elixir.Module.Types.Descr.«bare_intersection/3» (D n) name x y := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- A type is a subtype of another when each field holds less on points of values. -/

theorem opt_inter_lookup (depth : Nat) (L R : List (Term × Term)) (seen : Term)
    (sL : mapLookup L (.atom "dynamic") = Option.none) (sR : mapLookup R (.atom "dynamic") = Option.none)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ w, Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) q x y seen = .ok w) :
    ∃ I, Elixir.Module.Types.Descr.«opt_intersection/3» (D (depth + 1)) (.map L) (.map R) seen = .ok (.map I) ∧
      (∀ name, (mapLookup L (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
        (mapLookup R (.atom name) = Option.none → mapLookup I (.atom name) = Option.none) ∧
        (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
          Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) (.atom name) x y seen = .ok w →
          mapLookup I (.atom name) = if kept (.atom name, w) then some w else Option.none)) ∧
      ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) k₀ v₁ v₂ seen with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y w, Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) q x y seen = .ok w → g q x y = w := by
    intro q x y w run; simp [g, run]
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (depth + 1)) false "Elixir.Module.Types.Descr"
    "-opt_intersection/3-anonymous-0-" #[seen] L R g (by
      intro e member y hy
      obtain ⟨w, run⟩ := calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_intersection/3-anonymous-0-/3».pure]
      simp only [Elixir.Module.Types.Descr.«-opt_intersection/3-anonymous-0-/4»]
      rw [run, value _ _ _ _ run])
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (depth + 1)) false "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  refine ⟨out, ?_, fun name => ?_, fun q h => ?_⟩
  · unfold Elixir.Module.Types.Descr.«opt_intersection/3»
    simp [getMapKeys_single, sL, sR]
    unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  rotate_left
  · rw [lookO] at h
    cases hit : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [hit] at h; cases h
    | some e =>
      obtain ⟨-, hI⟩ := find_entry hit
      rw [lookI] at hI
      cases hitL : (mapEntries L).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | none => rw [hitL] at hI; cases hI
      | some f => rw [(find_entry hitL).2]; rfl
  have look : mapLookup out (.atom name) =
      match mapLookup L (.atom name), mapLookup R (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    rw [lookO, find_atom, lookI, find_atom]
    rcases hL : mapLookup L (.atom name) with _ | x <;> rcases hR : mapLookup R (.atom name) with _ | y <;>
      simp [hR]
  refine ⟨fun hL => by rw [look, hL], fun hR => by rw [look, hR]; cases mapLookup L (.atom name) <;> rfl,
    fun x y w hL hR run => by rw [look, hL, hR]; simp only [value _ _ _ _ run]⟩

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Completeness of map line emptiness on values. -/

theorem cmp_lt_trans {x y z : Term} (h₁ : Term.compare (Term.fuel x y) x y = .lt) (h₂ : Term.compare (Term.fuel y z) y z = .lt) :
    Term.compare (Term.fuel x z) x z = .lt := Lynx.Term.compare_lt_trans h₁ h₂

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of map literals on value maps. -/

/-- Optimized unions of element types are their unions. -/
theorem opt_union_top (n : Nat) {name : String} {w : Term} (hn : topValue name = some w) (S : Term) :
    Elixir.Module.Types.Descr.«opt_union/4» (D (n + 1)) (.atom name) w w S = .ok w := by
  rcases top_cases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [opt_union4_eq _ (Or.inr (Or.inr (Or.inl rfl)))]; exact fun_top_union n
  · rfl
  · have st := strategy_start (D (n + 1)) "open" "open" (Or.inl rfl) (Or.inl rfl) [] []
    simp only [Term.list, List.length_nil, and_self, ite_true] at st
    rw [show Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D (n + 1)) .nil .nil (.integer 0)
      (.atom "all_equal") = .ok (.atom "left_subtype_of_right") from index_nil_left _ [] _ _] at st
    simp only [Elixir.Module.Types.Descr.«opt_union/4»]
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2»]
  · rfl

theorem opt_diff_top (d : Dispatcher) {name : String} {w : Term} (hn : topValue name = some w) (S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/4» d (.atom name) w w S =
      Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) w w := by
  rcases top_cases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> first
    | rfl
    | (simp only [Elixir.Module.Types.Descr.«opt_difference/4», Elixir.Module.Types.Descr.«bare_difference/3»]
       rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def, Elixir.Module.Types.Descr.«list_difference/2».eq_def]
       simp [Erlang.erlang.«=:=/2»])

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of map types on value maps. -/

theorem tuple3_eq {a b c a' b' c' : Term} (h : Term.tuple #[a, b, c] = .tuple #[a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun x : Array Term => x[0]?) h
  have e₁ := congrArg (fun x : Array Term => x[1]?) h
  have e₂ := congrArg (fun x : Array Term => x[2]?) h
  simp at e₀ e₁ e₂
  exact ⟨e₀, e₁, e₂⟩

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of basic types. -/

theorem opt_inter_key (depth : Nat) (name : String) (x y S : Term) (hx : FieldOk name x) (hy : FieldOk name y) :
    ∃ r, Elixir.Module.Types.Descr.«opt_intersection/4» (D depth) (.atom name) x y S = .ok r ∧
      (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
      (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a &&& b)) ∧
      (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
        (amemV (some x) q && amemV (some y) q)) ∧
      (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.true) := by
  by_cases bf : name = "bitmap" ∨ name = "atom" ∨ name = "fun"
  · obtain ⟨r, run, rest⟩ := inter_key name x y hx hy
    refine ⟨r, ?_, rest⟩
    rw [opt_inter4_eq depth (by rcases bf with rfl | rfl | rfl <;> simp) S]
    exact run _
  · have nb : name ≠ "bitmap" := fun e => bf (Or.inl e)
    have na : name ≠ "atom" := fun e => bf (Or.inr (Or.inl e))
    have nf : name ≠ "fun" := fun e => bf (Or.inr (Or.inr e))
    have tx : topValue name = some x := by
      rcases hx with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, t⟩
      · exact absurd e nb
      · exact absurd e na
      · exact t
    have ty : topValue name = some y := by
      rcases hy with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, t⟩
      · exact absurd e nb
      · exact absurd e na
      · exact t
    have xy : x = y := by rw [tx] at ty; cases ty; rfl
    subst xy
    have names : name = "list" ∨ name = "tuple" ∨ name = "map" := by
      unfold topValue at tx
      split at tx <;> simp_all
    refine ⟨x, ?_, fun _ => hx, fun e => absurd e nb, fun e => absurd e na, fun _ _ => ?_⟩
    · rcases names with rfl | rfl | rfl <;> simp only [topValue, Option.some.injEq] at tx <;> subst tx <;> rfl
    · rcases names with rfl | rfl | rfl <;> simp [topValue] at tx <;> subst tx <;> simp [kept]

theorem opt_inter_term_l (d : Dispatcher) (x S : Term) :
    Elixir.Module.Types.Descr.«opt_intersection/3» d (.atom "term") x S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/3»; rfl

/-- The intersection function of optimized map leaf intersections. -/
def optMapIFun (S : Term) : Term := .function false "Elixir.Module.Types.Descr" "-opt_map_leaf_intersection/3-fun-0-" 2 #[S]

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Lines of BDDs hold what their valuations satisfy. -/

/-- Lines whose positive literals a valuation holds and whose negative literals it does not. -/
def LineSat (ρ : Term → Bool) (line : Term) : Prop :=
  ∃ pos negs : List Term, line = .tuple #[Term.list pos, Term.list negs] ∧ (∀ t ∈ pos, ρ t = Bool.true) ∧
    ∀ t ∈ negs, ρ t = Bool.false

theorem line_inj {a b c d : List Term} (h : Term.tuple #[Term.list a, Term.list b] = .tuple #[Term.list c, Term.list d]) :
    a = c ∧ b = d := by
  simp only [Term.tuple.injEq] at h
  have e₁ : Term.list a = Term.list c := by have := congrArg (fun x : Array Term => x[0]?) h; simpa using this
  have e₂ : Term.list b = Term.list d := by have := congrArg (fun x : Array Term => x[1]?) h; simpa using this
  exact ⟨list_inj e₁, list_inj e₂⟩

/-- Valuations that satisfy a line of a BDD satisfy the BDD. -/
theorem dnf_sat {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧
      ∀ l ∈ lines, l ∈ acc ∨ ∀ ρ, LineSat ρ l → (∀ t ∈ pos, ρ t = Bool.true) ∧ (∀ t ∈ negs, ρ t = Bool.false) ∧
        eval ρ r = Bool.true := by
  refine Bdd.induction (P := fun ok r => ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧
      ∀ l ∈ lines, l ∈ acc ∨ ∀ ρ, LineSat ρ l → (∀ t ∈ pos, ρ t = Bool.true) ∧ (∀ t ∈ negs, ρ t = Bool.false) ∧
        eval ρ r = Bool.true) ?_ ?_ ?_ ?_ ok r wr
  · intro ok acc pos negs
    refine ⟨.tuple #[Term.list pos, Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l m => ?_⟩
    rcases List.mem_cons.mp m with rfl | m
    · refine Or.inr fun ρ ⟨P, N, e, hP, hN⟩ => ?_
      obtain ⟨rfl, rfl⟩ := line_inj e
      exact ⟨hP, hN, by simp⟩
    · exact Or.inl m
  · intro ok acc pos negs
    exact ⟨acc, by simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»], fun l m => Or.inl m⟩
  · intro ok k x y _ acc pos negs
    refine ⟨.tuple #[Term.list (.tuple #[.integer k, x, y] :: pos), Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l m => ?_⟩
    rcases List.mem_cons.mp m with rfl | m
    · refine Or.inr fun ρ ⟨P, N, e, hP, hN⟩ => ?_
      obtain ⟨rfl, rfl⟩ := line_inj e
      exact ⟨fun t mt => hP t (List.mem_cons_of_mem _ mt), hN, by simp [hP _ List.mem_cons_self]⟩
    · exact Or.inl m
  · intro ok h lit c u d _ _ hc hu hd ic iu id acc pos negs
    obtain ⟨l₁, r₁, h₁⟩ := iu acc pos negs
    obtain ⟨l₂, r₂, h₂⟩ := ic l₁ (lit :: pos) negs
    obtain ⟨l₃, r₃, h₃⟩ := id l₂ pos (lit :: negs)
    refine ⟨l₃, ?_, fun l m => ?_⟩
    · simp only [Term.list] at r₁ r₂ r₃ ⊢
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», r₁, r₂, r₃]
    rcases h₃ l m with m₂ | s₃
    · rcases h₂ l m₂ with m₁ | s₂
      · rcases h₁ l m₁ with m₀ | s₁
        · exact Or.inl m₀
        · refine Or.inr fun ρ sat => ?_
          obtain ⟨p, n, e⟩ := s₁ ρ sat
          exact ⟨p, n, by simp [e]⟩
      · refine Or.inr fun ρ sat => ?_
        obtain ⟨p, n, e⟩ := s₂ ρ sat
        exact ⟨fun t mt => p t (List.mem_cons_of_mem _ mt), n, by simp [p lit List.mem_cons_self, e]⟩
    · refine Or.inr fun ρ sat => ?_
      obtain ⟨p, n, e⟩ := s₃ ρ sat
      exact ⟨p, fun t mt => n t (List.mem_cons_of_mem _ mt), by simp [n lit List.mem_cons_self, e]⟩

/-! Non-empty lists of values: their elements and their tail, which is never a non-empty list. -/

structure LV (V : Type) where
  xs : List V
  last : V

variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Lists in a list literal. -/
def LLitSem (den : Term → V → Prop) (lit : Term) (v : LV V) : Prop :=
  ∃ (k : Int) (a b : Term), lit = .tuple #[.integer k, a, b] ∧ (∀ x ∈ v.xs, den a x) ∧ den b v.last

/-- Values that are non-empty lists, and the tail types without their non-empty lists. -/
structure TailSem (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) : Prop where
  unfold : ∀ {e : Term}, E e → ∃ e', (∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«list_tail_unfold/1» (D m) e = .ok e') ∧
    E e' ∧
    ∀ v, den e' v ↔ den e v ∧ ¬tl v
  witness : ∃ v, ¬tl v

theorem lit_shape {k k' : Int} {a b a' b' : Term} (h : Term.tuple #[.integer k, a, b] = .tuple #[.integer k', a', b']) :
    a = a' ∧ b = b' := by
  simp only [Term.tuple.injEq] at h
  have e₁ := congrArg (fun x : Array Term => x[1]?) h
  have e₂ := congrArg (fun x : Array Term => x[2]?) h
  simp at e₁ e₂
  exact ⟨e₁, e₂⟩

theorem llitSem_iff {k : Int} {a b : Term} {v : LV V} :
    LLitSem den (.tuple #[.integer k, a, b]) v ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last := by
  constructor
  · rintro ⟨k', a', b', e, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := lit_shape e
    exact ⟨h₁, h₂⟩
  · intro h; exact ⟨k, a, b, rfl, h⟩

open Classical in
/-- The valuation of list literals that a list induces, up to comparison. -/
noncomputable def valL (E : Term → Prop) (den : Term → V → Prop) (v : LV V) (t : Term) : Bool :=
  decide (∃ t', compare (fuel t t') t t' = .eq ∧ LLit E t' ∧ LLitSem den t' v)

theorem valL_resp (v : LV V) : Resp (valL E den v) := by
  intro a b h
  simp only [valL]
  congr 1
  apply propext
  constructor
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨t', e, rest⟩; exact ⟨t', Lynx.Term.compare_eq_trans h e, rest⟩

theorem valL_iff (sem : ElemSem E K V den Safe) {v : LV V} {t : Term} (ht : LLit E t) :
    valL E den v t = Bool.true ↔ LLitSem den t v := by
  simp only [valL, decide_eq_true_eq]
  constructor
  · rintro ⟨t', e, ⟨k', a', b', rfl, ha', hb'⟩, h⟩
    obtain ⟨k, a, b, rfl, ha, hb⟩ := ht
    rw [llitSem_iff] at h ⊢
    simp only [compare_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
      Ordering.then_eq_eq, List.compareLex_cons_cons] at e
    obtain ⟨-, -, ea, eb, -⟩ := e
    exact ⟨fun x mx => sem.resp ha ha' ea (h.1 x mx), sem.resp hb hb' eb h.2⟩
  · intro h; exact ⟨t, compare_self t, ht, h⟩

/-- Intersecting the positive literals of a line keeps the lists in all of them. -/
theorem lits_sem (ops : ElemOk E K) (sem : ElemSem E K V den Safe) :
    ∀ (l : List Term), (∀ t ∈ l, LLit E t) → ∀ a b, E a → E b →
      ∃ a' b', E a' ∧ E b' ∧ (∀ m, K + 1 ≤ m →
        Erlang.lists.«foldl_1/3» (D m) litsFun (.tuple #[a, b]) (Term.list l) = .ok (.tuple #[a', b'])) ∧
        ∀ v : LV V, ((∀ x ∈ v.xs, den a' x) ∧ den b' v.last) ↔
          ((∀ x ∈ v.xs, den a x) ∧ den b v.last) ∧ ∀ t ∈ l, LLitSem den t v := by
  intro l
  induction l with
  | nil =>
    intro _ a b ha hb
    exact ⟨a, b, ha, hb, fun m _ => by simp [Erlang.lists.«foldl_1/3»], fun v => by simp⟩
  | cons t rest ih =>
    intro lits a b ha hb
    obtain ⟨k, x, y, rfl, hx, hy⟩ := lits _ List.mem_cons_self
    obtain ⟨a₁, ha₁, ra⟩ := ops.inter ha hx
    obtain ⟨b₁, hb₁, rb⟩ := ops.inter hb hy
    obtain ⟨a', b', ha', hb', run, semr⟩ := ih (fun t m => lits t (List.mem_cons_of_mem _ m)) a₁ b₁ ha₁ hb₁
    have da := sem.inter ha hx (Nat.le_refl K) (ra K (Nat.le_refl K))
    have db := sem.inter hb hy (Nat.le_refl K) (rb K (Nat.le_refl K))
    refine ⟨a', b', ha', hb', fun m hm => ?_, fun v => ?_⟩
    · obtain ⟨n, rfl, hn⟩ := succ_of_le hm
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [litsFun,
        Erlang.program.«Elixir.Module.Types.Descr:-non_empty_list_literals_intersection/2-fun-0-/2».pure]
      simp only [Elixir.Module.Types.Descr.«-non_empty_list_literals_intersection/2-fun-0-/2», ra n hn, rb n hn,
        Lynx.Except.ok_bind, pure_bind]
      exact run (n + 1) hm
    · rw [semr v]
      simp only [List.forall_mem_cons, llitSem_iff, da, db]
      constructor
      · rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩
        exact ⟨⟨fun z mz => (h₁ z mz).1, h₂⟩, ⟨fun z mz => (h₁ z mz).2, h₃⟩, h₄⟩
      · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅⟩
        exact ⟨⟨fun z mz => ⟨h₁ z mz, h₃ z mz⟩, h₂, h₄⟩, h₅⟩

theorem TailSem.ok {tl : V → Prop} (tsem : TailSem E den tl) : TailOk E := fun _ he =>
  let ⟨e', run, he', _⟩ := tsem.unfold he
  ⟨e', run, he'⟩

theorem llitSem_tail {N : Term} {x : V} {xs : List V} {y : V} (h : LLitSem den N ⟨x :: xs, y⟩) :
    LLitSem den N ⟨xs, y⟩ := by
  obtain ⟨k, a, b, e, h₁, h₂⟩ := h
  exact ⟨k, a, b, e, fun z mz => h₁ z (List.mem_cons_of_mem _ mz), h₂⟩

/-- `list_line_negs_empty?/4` finds the lists of a line covered by its negations: negations whose element type
does not hold the line's are skipped, since longer lists escape them. -/
theorem negs_complete (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a : Term} (ha : Full E K S a) :
    ∀ negs : List Term, (∀ t ∈ negs, LLit E t) → ∀ t, Full E K S t → (∀ y, den t y → ¬tl y) →
      (∀ xs : List V, xs ≠ [] → (∀ x ∈ xs, den a x) → ∀ y, den t y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩) →
      ∀ m, K ≤ m → Elixir.Module.Types.Descr.«list_line_negs_empty?/4» (D m) (Term.list negs) a t (.map S) =
        .ok (.atom "true") := by
  intro negs
  induction negs with
  | nil =>
    intro _ t ht _ H m _
    exfalso
    obtain ⟨x, hx⟩ := full_witness sem hS ha
    obtain ⟨y, hy⟩ := full_witness sem hS ht
    obtain ⟨N, mN, -⟩ := H [x] (by simp) (by simpa using hx) y hy
    simp at mN
  | cons N rest ih =>
    intro lits t ht notl H m hm
    obtain ⟨k, nt, nl, rfl, hnt, hnl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, LLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    obtain ⟨sd, hsd, rsd⟩ := dops.diff ha.1 hnt
    have dsd := sem.diff ha.1 hnt hm (rsd m hm)
    obtain ⟨bs, hbs⟩ := ops.empty hsd S
    cases bs
    · have full : Full E K S sd := ⟨hsd, fun m' h' => by simpa using hbs m' h'⟩
      obtain ⟨w, hw⟩ := full_witness sem hS full
      have hw' := (dsd w).mp hw
      have rc := ih lits' t ht notl (fun xs ne hxs y hy => by
        obtain ⟨N', mN, hN⟩ := H (w :: xs) (by simp) (by simpa [hw'.1] using hxs) y hy
        rcases List.mem_cons.mp mN with rfl | mN
        · exact absurd ((llitSem_iff.mp hN).1 w List.mem_cons_self) hw'.2
        · exact ⟨N', mN, llitSem_tail hN⟩) m hm
      rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def]
      simp only [] at rc ⊢
      simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, isMember]
      exact rc
    · obtain ⟨t', ht', ht'E, dt'⟩ := tsem.unfold hnl
      obtain ⟨dd, hdd, rdd⟩ := dops.diff ht.1 ht'E
      have ddd := sem.diff ht.1 ht'E hm (rdd m hm)
      obtain ⟨be, hbe⟩ := ops.empty hdd S
      obtain ⟨b, hb⟩ := negs_total ops dops tsem.ok S ha.1 rest lits' dd hdd
      have h₁ := hb m hm
      dsimp only at h₁
      have last : be = Bool.true ∨ b = Bool.true := by
        cases be
        · right
          have full : Full E K S dd := ⟨hdd, fun m' h' => by simpa using hbe m' h'⟩
          have rc := ih lits' dd full (fun y hy => notl y ((ddd y).mp hy).1) (fun xs ne hxs y hy => by
            have hy' := (ddd y).mp hy
            obtain ⟨N', mN, hN⟩ := H xs ne hxs y hy'.1
            rcases List.mem_cons.mp mN with rfl | mN
            · exact absurd ((dt' y).mpr ⟨(llitSem_iff.mp hN).2, notl y hy'.1⟩) hy'.2
            · exact ⟨N', mN, hN⟩) m hm
          rw [h₁] at rc
          cases b <;> simp_all [boolAtom]
        · exact Or.inl rfl
      rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def]
      simp only [] at h₁ ⊢
      simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, isMember,
        ht' m (by have := ops.pos; omega), rdd m hm, hbe m hm, h₁]
      rcases last with rfl | rfl
      · simp
      · cases be <;> simp

/-- Lines of lists are empty when their negations cover them. -/
theorem list_line_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a b : Term} (ha : E a) (hb : E b)
    {negs : List Term} (lits : ∀ t ∈ negs, LLit E t)
    (H : ∀ xs : List V, xs ≠ [] → (∀ x ∈ xs, den a x) → ∀ y, den b y → ¬tl y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩)
    {m : Nat} (hm : K ≤ m) :
    Elixir.Module.Types.Descr.«list_line_empty?/4» (D m) a b (Term.list negs) (.map S) = .ok (.atom "true") := by
  obtain ⟨t, ht, htE, dt⟩ := tsem.unfold hb
  obtain ⟨b₁, h₁⟩ := ops.empty ha S
  obtain ⟨b₂, h₂⟩ := ops.empty htE S
  obtain ⟨b₃, h₃⟩ := negs_total ops dops tsem.ok S ha negs lits t htE
  have e₃ := h₃ m hm
  dsimp only at e₃
  have any : (b₁ || b₂ || b₃) = Bool.true := by
    cases b₁ <;> cases b₂ <;> simp only [Bool.true_or, Bool.or_true, Bool.false_or]
    have fa : Full E K S a := ⟨ha, fun m' h' => by simpa using h₁ m' h'⟩
    have ft : Full E K S t := ⟨htE, fun m' h' => by simpa using h₂ m' h'⟩
    have := negs_complete ops dops sem tsem S hS fa negs lits t ft (fun y hy => ((dt y).mp hy).2)
      (fun xs ne hxs y hy => H xs ne hxs y ((dt y).mp hy).1 ((dt y).mp hy).2) m hm
    rw [e₃] at this
    cases b₃ <;> simp_all [boolAtom]
  unfold Elixir.Module.Types.Descr.«list_line_empty?/4»
  simp only [ht m (by have := ops.pos; omega), Lynx.Except.ok_bind, h₁ m hm, h₂ m hm, e₃, Elixir.STTDescrProofsTest.orElse_bool, any]
  rfl

/-- `non_empty_list_literals_intersection/2` intersects the positive literals of a line, or finds them empty. -/
theorem literals_val (ops : ElemOk E K) (sem : ElemSem E K V den Safe) (S : List (Term × Term)) (pos : List Term)
    (lits : ∀ t ∈ pos, LLit E t) :
    (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m) (Term.list pos)
      (.map S) = .ok (.atom "empty")) ∨
    ∃ a b, E a ∧ E b ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m)
      (Term.list pos) (.map S) = .ok (.tuple #[a, b])) ∧
      ∀ v : LV V, ((∀ x ∈ v.xs, den a x) ∧ den b v.last) ↔ ∀ t ∈ pos, LLitSem den t v := by
  obtain ⟨a, b, ha, hb, fold, semf⟩ := lits_sem ops sem pos lits _ _ ops.term ops.term
  obtain ⟨ea, hea⟩ := ops.empty ha S
  obtain ⟨eb, heb⟩ := ops.empty hb S
  have foldEq : ∀ d, Erlang.lists.«foldl/3» d litsFun (.tuple #[.atom "term", .atom "term"]) (Term.list pos) =
      Erlang.lists.«foldl_1/3» d litsFun (.tuple #[.atom "term", .atom "term"]) (Term.list pos) := by
    intro d
    cases pos with
    | nil =>
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», litsFun]
    | cons t rest =>
      conv => rhs; rw [Erlang.lists.«foldl_1/3».eq_def]
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», litsFun]
  have unfold : ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m)
      (Term.list pos) (.map S) = if ea || eb then .ok (.atom "empty") else .ok (.tuple #[a, b]) := by
    intro m hm
    have f := fold m hm
    have e₁ := hea m (by omega)
    have e₂ := heb m (by omega)
    unfold Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2»
    have f' : Erlang.lists.«foldl/3» (D m) (.function false "Elixir.Module.Types.Descr"
        "-non_empty_list_literals_intersection/2-fun-0-" 2 #[]) (.tuple #[.atom "term", .atom "term"])
        (Term.list pos) = .ok (.tuple #[a, b]) := by rw [← litsFun, foldEq, f]
    simp only [pure_bind, f', Lynx.Except.ok_bind, e₁, e₂, Elixir.STTDescrProofsTest.orElse_bool]
    cases ea <;> cases eb <;> simp [boolAtom, isMember]
  by_cases e : (ea || eb) = Bool.true
  · exact Or.inl fun m hm => by rw [unfold m hm, ite_eq_left e]
  · refine Or.inr ⟨a, b, ha, hb, fun m hm => by rw [unfold m hm, ite_eq_right e], fun v => ?_⟩
    rw [semf v]
    exact ⟨fun h => h.2, fun h => ⟨⟨fun x _ => sem.term x, sem.term _⟩, h⟩⟩

/-- List BDDs that no list satisfies are empty. -/
theorem list_empty_val (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) {m : Nat} (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (LLit E) r) (S : List (Term × Term))
    (safe : ∀ S', Erlang.maps.«put/3» (.cons (.atom "list") r) (.atom "true") (.map S) = .ok (.map S') → Safe S')
    (unsat : ∀ v : LV V, v.xs ≠ [] → ¬tl v.last → eval (valL E den v) r = Bool.false) :
    Elixir.Module.Types.Descr.«list_empty?/2» (D m) r (.map S) = .ok (.atom "true") := by
  obtain ⟨x₀⟩ := sem.inhabited
  obtain ⟨y₀, hy₀⟩ := tsem.witness
  by_cases top : r = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  · subst top
    have := unsat ⟨[x₀], y₀⟩ (by simp) hy₀
    rw [eval_leaf, (valL_iff sem ⟨_, _, _, rfl, ops.term, ops.term⟩).mpr
      (llitSem_iff.mpr ⟨fun x _ => sem.term x, sem.term _⟩)] at this
    cases this
  by_cases seen : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 = .eq)) = Bool.true
  · unfold Elixir.Module.Types.Descr.«list_empty?/2»
    split
    · exact absurd rfl top
    · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
  have fresh : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 = .eq)) = Bool.false := by
    simpa using seen
  obtain ⟨S', put⟩ : ∃ S', Erlang.maps.«put/3» (.cons (.atom "list") r) (.atom "true") (.map S) = .ok (.map S') := by
    simp [Erlang.maps.«put/3»]
  have hS' := safe S' put
  obtain ⟨lines, dnf, hlines⟩ := dnf_lines wr (LLit E) (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  obtain ⟨lines', dnf', hsat⟩ := dnf_sat wr [] [] []
  have same : lines' = lines := list_inj (by rw [dnf] at dnf'; exact (Except.ok.inj dnf').symm)
  subst same
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
  have each : ∀ x ∈ lines', Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D n) (.map S') x =
      .ok (boolAtom Bool.true) := by
    intro x mx
    obtain ⟨pos, negs, rfl, hp, hn'⟩ := hlines x mx
    rcases literals_val ops sem S' pos hp with empty | ⟨a, b, ha, hb, run, semab⟩
    · simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», empty n hn, boolAtom]
    · have line := list_line_val ops dops sem tsem S' hS' ha hb hn' (m := n) (fun xs ne hxs y hy ny => ?_)
        (by omega)
      · simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», run n hn, line, boolAtom]
      · refine Classical.byContradiction fun none => ?_
        have sat : LineSat (valL E den ⟨xs, y⟩) (.tuple #[Term.list pos, Term.list negs]) :=
          ⟨pos, negs, rfl, fun t mt => (valL_iff sem (hp t mt)).mpr ((semab ⟨xs, y⟩).mp ⟨hxs, hy⟩ t mt),
            fun t mt => by
              cases e : valL E den ⟨xs, y⟩ t
              · rfl
              · exact absurd ⟨t, mt, (valL_iff sem (hn' t mt)).mp e⟩ none⟩
        rcases hsat _ mx with m₀ | s
        · simp at m₀
        · have := (s _ sat).2.2
          rw [unsat ⟨xs, y⟩ ne ny] at this
          cases this
  have all := all_list (D (n + 1)) _ _ _ (fun _ => Bool.true) lines' fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-list_empty?/2-fun-0-/1».pure]
    exact each x mx
  unfold Elixir.Module.Types.Descr.«list_empty?/2»
  split
  · exact absurd rfl top
  · simp only [Term.list] at dnf
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, put, Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf]
    rw [all]
    simp [List.all_eq_true, boolAtom]

/-! Lists of basic types. -/

theorem kindName_list {k : Fin 4} (h : k ≠ 1) : kindName k ≠ "list" := by
  obtain ⟨k, lt⟩ := k
  simp only [kindName]
  match k, lt, h with
  | 0, _, _ | 2, _, _ | 3, _, _ => decide
  | 1, _, h => exact absurd rfl h

theorem noList_den (M : List (Term × Term)) (v : FV) :
    denF (.map (noList M)) v ↔ denF (.map M) v ∧ v ≠ .kind 1 := by
  have look : ∀ name, name ≠ "list" → mapLookup (noList M) (.atom name) = mapLookup M (.atom name) := by
    intro name ne
    simp [noList, mapLookup_remove, ne]
  have lookL : mapLookup (noList M) (.atom "list") = Option.none := by simp [noList, mapLookup_remove]
  cases v with
  | bit i => simp [denF, bits, look "bitmap" (by decide)]
  | atom q => simp [denF, amem, look "atom" (by decide)]
  | kind k =>
    by_cases h : k = 1
    · subst h; simp [denF, has, kindName, lookL]
    · simp [denF, has, look _ (kindName_list h), h]

theorem testBit_255 : ∀ i : Fin 8, Nat.testBit 255 i = Bool.true := by decide

theorem tailTerm_den (v : FV) : denF (.map tailTerm) v ↔ v ≠ .kind 1 := by
  cases v with
  | bit i =>
    have b : bits tailTerm = 255 := by simp [bits, tailTerm, mapLookup]
    simp [denF, b, testBit_255]
  | atom q => simp [denF, amem, amemV, tailTerm, mapLookup]
  | kind k =>
    obtain ⟨k, lt⟩ := k
    simp only [denF, has, tailTerm, kindName]
    match k, lt with
    | 0, _ => simp [mapLookup, Fin.ext_iff]
    | 1, _ => simp [mapLookup]
    | 2, _ => simp [mapLookup, Fin.ext_iff]
    | 3, _ => simp [mapLookup, Fin.ext_iff]; decide

def tlF (v : FV) : Prop := v = .kind 1

/-- The top type without lists, whatever order its fields come in, with the lookups of `tailTerm`. -/
theorem tail_term_lookup : ∃ T, (∀ d, Elixir.Module.Types.Descr.«list_tail_unfold/1» d (.atom "term") = .ok (.map T)) ∧
    ∀ q, mapLookup T q = mapLookup tailTerm q := by
  refine ⟨_, fun d => by unfold Elixir.Module.Types.Descr.«list_tail_unfold/1»; rfl, ?_⟩
  refine lookup_tail_perm (fun name => ?_) fun q h => ?_
  · simp only [mapLookup, List.find?, tailTerm, compareExact_eq_atom, Term.atom.injEq, equalExact_eq_decide]
    all_goals by_cases b : name = "bitmap" <;> by_cases t : name = "tuple" <;> by_cases f : name = "fun" <;>
      by_cases m : name = "map" <;> by_cases a : name = "atom" <;> simp_all
  · by_cases a : ∃ name : String, q = .atom name
    · exact a
    · have na : ∀ k : String, ¬q = .atom k := fun k e => a ⟨k, e⟩
      simp [mapLookup, List.find?, compareExact_eq_atom, na] at h

theorem tailF : TailSem LElem denF tlF := by
  refine ⟨fun {e} he => ?_, ⟨.bit 0, by simp [tlF]⟩⟩
  rcases he with rfl | ⟨M, rfl, bM⟩
  · obtain ⟨T, run, look⟩ := tail_term_lookup
    have den : ∀ v, denF (.map T) v ↔ denF (.map tailTerm) v := fun v => by
      cases v <;> simp [denF, bits, amem, has, look]
    exact ⟨.map T, fun m _ => run (D m), Or.inr ⟨T, rfl, basic_of_lookup look⟩,
      fun v => by simp [denF_term, den, tailTerm_den, tlF]⟩
  · exact ⟨_, fun m _ => tail_map (D m) M, Or.inr ⟨_, rfl, bM.noList⟩, fun v => by simp [noList_den, tlF]⟩

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of tuple types on tuples of values. -/

/-- The intersection function of optimized tuple leaf intersections. -/
def optTupleIFun (S : Term) : Term :=
  .function false "Elixir.Module.Types.Descr" "-opt_tuple_leaf_intersection/3-fun-0-" 2 #[S]

theorem closed_lt_open' {k H : Int} (hk : k < 0) (hH : 0 ≤ H) (cl fo : Term) :
    Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer H, .atom "open", fo])) (.tuple #[.integer k, .atom "closed", cl]) (.tuple #[.integer H, .atom "open", fo]) = .lt := by
  rw [compare_tuple]
  have : Ord.compare k H = .lt := Int.compare_eq_lt.mpr (by omega)
  simp [List.compareLex_cons_cons, this]

theorem tupleLit_elems {E : Term → Prop} {k : Int} {t : String} {l : List Term}
    (h : TupleLit E (.tuple #[.integer k, .atom t, Term.list l])) : ∀ e ∈ l, E e := by
  obtain ⟨k', t', l', e, -, hl⟩ := h
  simp only [Term.tuple.injEq] at e
  have e₂ := congrArg (fun a : Array Term => a[2]?) e
  simp at e₂
  rw [list_inj e₂]
  exact hl

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Differences guided by comparing leaves, exact for the valuations that agree with the comparisons. -/

/-- Leaves of literals `ok`, or the empty BDD. -/
def LeafOrBot (ok : Term → Prop) (t : Term) : Prop :=
  t = .atom "bdd_bot" ∨ ∃ (k : Int) (x y : Term), t = .tuple #[.integer k, x, y] ∧ ok t

theorem LeafOrBot.bdd {ok : Term → Prop} {t : Term} (h : LeafOrBot ok t) : Bdd ok t := by
  rcases h with rfl | ⟨k, x, y, rfl, okt⟩
  · exact Bdd.bot
  · exact Bdd.leaf_iff.mpr okt

/-- What a leaf comparison answers about two literals, for the valuations `Val`. -/
def CmpOk (Val : (Term → Bool) → Prop) (ok : Term → Prop) (a₁ a₂ type res : Term) : Prop :=
  (res = .atom "disjoint" ∧ ∀ ρ, Val ρ → (ρ a₁ && ρ a₂) = Bool.false) ∨
  (res = .atom "subtype" ∧ ∀ ρ, Val ρ → ρ a₁ = Bool.true → ρ a₂ = Bool.true) ∨
  (∃ ad at', res = .tuple #[.atom "one_key_difference", ad, at'] ∧ LeafOrBot ok ad ∧ LeafOrBot ok at' ∧
    (∀ ρ, Val ρ → eval ρ ad = (ρ a₁ && !ρ a₂)) ∧
    (type = .atom "intersection" → ∀ ρ, Val ρ → eval ρ at' = (ρ a₁ && ρ a₂)) ∧
    (type = .atom "union" → ∀ ρ, Val ρ → eval ρ at' = (ρ a₁ || ρ a₂)) ∧
    (type = .atom "none" → at' = .atom "bdd_bot")) ∨
  res = .atom "none"

/-- The types of results `bdd_difference/3` asks leaf comparisons for. -/
def TypeOk (type : Term) : Prop := type = .atom "none" ∨ type = .atom "intersection" ∨ type = .atom "union"

/-- What `bdd_difference/3` guarantees. -/
def Diff3 (Val : (Term → Bool) → Prop) (ok : Term → Prop) (d : Dispatcher) (cmp a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_difference/3» d a b cmp = .ok r ∧ Bdd ok r ∧
    ∀ ρ, Val ρ → eval ρ r = (eval ρ a && !eval ρ b)

theorem diff3_plain {Val : (Term → Bool) → Prop} (resp : ∀ ρ, Val ρ → Resp ρ) {ok : Term → Prop} {d : Dispatcher}
    {cmp a b : Term} (wa : Bdd ok a) (wb : Bdd ok b)
    (run : Elixir.Module.Types.Descr.«bdd_difference/3» d a b cmp = Elixir.Module.Types.Descr.«bdd_difference/2» a b) :
    Diff3 Val ok d cmp a b := by
  obtain ⟨r, hr, okr, semr⟩ := diff_ok wa wb
  exact ⟨r, by rw [run, hr], okr ok wa wb, fun ρ v => semr ρ (resp ρ v)⟩

theorem d3_top_left (d : Dispatcher) (b cmp : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/3» d (.atom "bdd_top") b cmp =
      Elixir.Module.Types.Descr.«bdd_difference/2» (.atom "bdd_top") b := by
  rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]

theorem d3_bot_left (d : Dispatcher) (b cmp : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/3» d (.atom "bdd_bot") b cmp =
      Elixir.Module.Types.Descr.«bdd_difference/2» (.atom "bdd_bot") b := by
  rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]

theorem d3_atom_right {ok : Term → Prop} (d : Dispatcher) {a : Term} (wa : Bdd ok a) (s : String) (cmp : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/3» d a (.atom s) cmp =
      Elixir.Module.Types.Descr.«bdd_difference/2» a (.atom s) := by
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d', rfl⟩ <;>
    rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]

variable {Val : (Term → Bool) → Prop} {ok : Term → Prop} {d : Dispatcher} {cmp : Term}

/-- Leaves minus leaves. -/
theorem diff3_leaves (resp : ∀ ρ, Val ρ → Resp ρ)
    (spec : ∀ a₁ a₂ type, TypeOk type → ok a₁ → ok a₂ →
      ∃ res, d.pure cmp #[a₁, a₂, type] = .ok res ∧ CmpOk Val ok a₁ a₂ type res)
    (k₁ : Int) (x₁ y₁ : Term) (k₂ : Int) (x₂ y₂ : Term) (h₁ : ok (.tuple #[.integer k₁, x₁, y₁]))
    (h₂ : ok (.tuple #[.integer k₂, x₂, y₂])) :
    Diff3 Val ok d cmp (.tuple #[.integer k₁, x₁, y₁]) (.tuple #[.integer k₂, x₂, y₂]) := by
  obtain ⟨res, run, cmpOk⟩ := spec _ _ (.atom "none") (Or.inl rfl) h₁ h₂
  have w₁ : Bdd ok (.tuple #[.integer k₁, x₁, y₁]) := Bdd.leaf_iff.mpr h₁
  have w₂ : Bdd ok (.tuple #[.integer k₂, x₂, y₂]) := Bdd.leaf_iff.mpr h₂
  rcases cmpOk with ⟨rfl, disj⟩ | ⟨rfl, sub⟩ | ⟨ad, at', rfl, had, -, sad, -, -, -⟩ | rfl
  · refine ⟨_, ?_, w₁, fun ρ v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]; rfl
    · have := disj ρ v
      simp only [eval_leaf] at this ⊢
      revert this; cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> simp
  · refine ⟨_, ?_, Bdd.bot, fun ρ v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]; rfl
    · have := sub ρ v
      simp only [eval_leaf] at this ⊢
      revert this; cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> simp
  · refine ⟨ad, ?_, had.bdd, fun ρ v => by simp only [eval_leaf]; exact sad ρ v⟩
    rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]; rfl
  · refine diff3_plain resp w₁ w₂ ?_
    rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]; simp only [run, Lynx.Except.ok_bind]

theorem eq_bot_atom (x : Term) [Decidable (x = .atom "bdd_bot")] :
    Erlang.erlang.«==/2» x (.atom "bdd_bot") = .ok (.atom (if x = .atom "bdd_bot" then "true" else "false")) := by
  by_cases h : x = .atom "bdd_bot"
  · subst h; simp [Erlang.erlang.«==/2»]
  · simp [Erlang.erlang.«==/2», h]

/-- BDDs minus leaves. -/
theorem diff3_left (resp : ∀ ρ, Val ρ → Resp ρ)
    (spec : ∀ a₁ a₂ type, TypeOk type → ok a₁ → ok a₂ →
      ∃ res, d.pure cmp #[a₁, a₂, type] = .ok res ∧ CmpOk Val ok a₁ a₂ type res) :
    ∀ ok₁ b₁, Bdd ok₁ b₁ → (∀ t, ok₁ t → ok t) → ∀ (k : Int) x y, ok (.tuple #[.integer k, x, y]) →
      Diff3 Val ok d cmp b₁ (.tuple #[.integer k, x, y]) := by
  refine Bdd.induction (P := fun ok₁ b₁ => (∀ t, ok₁ t → ok t) → ∀ (k : Int) x y, ok (.tuple #[.integer k, x, y]) →
    Diff3 Val ok d cmp b₁ (.tuple #[.integer k, x, y])) ?_ ?_ ?_ ?_
  · intro ok₁ _ k x y h; exact diff3_plain resp Bdd.top (Bdd.leaf_iff.mpr h) (d3_top_left _ _ _)
  · intro ok₁ _ k x y h; exact diff3_plain resp Bdd.bot (Bdd.leaf_iff.mpr h) (d3_bot_left _ _ _)
  · intro ok₁ k₁ x₁ y₁ h₁ sub k x y h; exact diff3_leaves resp spec k₁ x₁ y₁ k x y (sub _ h₁) h
  · intro ok₁ hh a₁ c₁ u₁ d₁ isLeaf oka hc hu hd ic iu id sub k x y h₂
    have sub' : ∀ t, Above ok₁ a₁ t → ok t := fun t ht => sub t ht.1
    have lift : ∀ t, Above ok₁ a₁ t → Above ok a₁ t := fun t ht => ⟨sub t ht.1, ht.2⟩
    have w₁ : Bdd ok (.tuple #[.integer hh, a₁, c₁, u₁, d₁]) :=
      Bdd.node_iff.mpr ⟨isLeaf, sub _ oka, hc.mono lift, hu.mono lift, hd.mono lift⟩
    have w₂ : Bdd ok (.tuple #[.integer k, x, y]) := Bdd.leaf_iff.mpr h₂
    have wc : Bdd ok c₁ := hc.mono fun t ht => sub t ht.1
    have wu : Bdd ok u₁ := hu.mono fun t ht => sub t ht.1
    have wd : Bdd ok d₁ := hd.mono fun t ht => sub t ht.1
    obtain ⟨k₁, x₁, y₁, rfl⟩ := isLeaf
    classical
    let type : Term := .atom (if d₁ = .atom "bdd_bot" then "none" else "union")
    obtain ⟨res, run, cmpOk⟩ := spec _ _ type (by simp only [type]; split <;> simp [TypeOk]) (sub _ oka) h₂
    obtain ⟨ru, hru, okru, semru⟩ := iu sub' k x y h₂
    rcases cmpOk with ⟨rfl, -⟩ | ⟨rfl, sb⟩ | ⟨ad, au, rfl, had, hau, sad, -, sau, snone⟩ | rfl
    · obtain ⟨hn, runn⟩ := node_new (.tuple #[.integer k₁, x₁, y₁]) c₁ (.atom "bdd_bot") d₁ ⟨k₁, x₁, y₁, rfl⟩ hc
        (Bdd.bot (ok := ok₁)) hd
      have wn : Bdd ok (.tuple #[.integer hn, .tuple #[.integer k₁, x₁, y₁], c₁, .atom "bdd_bot", d₁]) :=
        Bdd.node_iff.mpr ⟨⟨k₁, x₁, y₁, rfl⟩, sub _ oka, hc.mono lift, Bdd.bot, hd.mono lift⟩
      obtain ⟨r₂, hr₂, okr₂, semr₂⟩ := diff_ok wn w₂
      obtain ⟨r, hr, okr, semr⟩ := union_ok (okru) (okr₂ ok wn w₂)
      refine ⟨r, ?_, okr ok okru (okr₂ ok wn w₂), fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_bot_atom]
        by_cases e : d₁ = .atom "bdd_bot"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hru, runn, hr₂, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hru, runn, hr₂, hr]
      · rw [semr ρ (resp ρ v), semru ρ v, semr₂ ρ (resp ρ v)]
        simp only [eval]
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
          cases eval ρ u₁ <;> cases eval ρ d₁ <;> rfl
    · obtain ⟨rd, hrd, okrd, semrd⟩ := id sub' k x y h₂
      obtain ⟨r, hr, okr, semr⟩ := union_ok okru okrd
      refine ⟨r, ?_, okr ok okru okrd, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_bot_atom]
        by_cases e : d₁ = .atom "bdd_bot"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hru, hrd, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hru, hrd, hr]
      · rw [semr ρ (resp ρ v), semru ρ v, semrd ρ v]
        have := sb ρ v
        simp only [eval_node, eval_leaf]
        revert this
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
          cases eval ρ u₁ <;> cases eval ρ d₁ <;> simp
    · obtain ⟨ri, hri, okri, semri⟩ := inter_ok had.bdd wc
      obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := union_ok (okri ok had.bdd wc) okru
      obtain ⟨rd, hrd, okrd, semrd⟩ : Diff3 Val ok d cmp d₁ au := by
        by_cases e : d₁ = .atom "bdd_bot"
        · subst e; exact diff3_plain resp Bdd.bot hau.bdd (d3_bot_left _ _ _)
        · rcases hau with rfl | ⟨k', x', y', rfl, okau⟩
          · exact diff3_plain resp wd Bdd.bot (d3_atom_right _ wd _ _)
          · exact id sub' k' x' y' okau
      obtain ⟨r, hr, okr, semr⟩ := union_ok (okr₁ ok (okri ok had.bdd wc) okru) okrd
      refine ⟨r, ?_, okr ok (okr₁ ok (okri ok had.bdd wc) okru) okrd, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_bot_atom]
        by_cases e : d₁ = .atom "bdd_bot"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hri, hru, hr₁, hrd, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hri, hru, hr₁, hrd, hr]
      · rw [semr ρ (resp ρ v), semr₁ ρ (resp ρ v), semri ρ (resp ρ v), semru ρ v, semrd ρ v, sad ρ v]
        simp only [eval_node, eval_leaf]
        by_cases e : d₁ = .atom "bdd_bot"
        · have := snone (by simp [type, e])
          subst this e
          try simp only [eval]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
            cases eval ρ u₁ <;> rfl
        · rw [sau (by simp [type, e]) ρ v]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k, x, y]) <;> cases eval ρ c₁ <;>
            cases eval ρ u₁ <;> cases eval ρ d₁ <;> rfl
    · refine diff3_plain resp w₁ w₂ ?_
      rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
      simp only [eq_bot_atom]
      by_cases e : d₁ = .atom "bdd_bot"
      · simp only [ite_eq_left e, type] at run ⊢; simp [run]
      · simp only [ite_eq_right e, type] at run ⊢; simp [run]

theorem eq_top_atom (x : Term) [Decidable (x = .atom "bdd_top")] :
    Erlang.erlang.«==/2» x (.atom "bdd_top") = .ok (.atom (if x = .atom "bdd_top" then "true" else "false")) := by
  by_cases h : x = .atom "bdd_top"
  · subst h; simp [Erlang.erlang.«==/2»]
  · simp [Erlang.erlang.«==/2», h]

/-- `bdd_difference/3` subtracts BDDs exactly, for the valuations its leaf comparisons are right about. -/
theorem diff3_ok (resp : ∀ ρ, Val ρ → Resp ρ)
    (spec : ∀ a₁ a₂ type, TypeOk type → ok a₁ → ok a₂ →
      ∃ res, d.pure cmp #[a₁, a₂, type] = .ok res ∧ CmpOk Val ok a₁ a₂ type res) :
    ∀ ok₂ b₂, Bdd ok₂ b₂ → (∀ t, ok₂ t → ok t) → ∀ b₁, Bdd ok b₁ → Diff3 Val ok d cmp b₁ b₂ := by
  refine Bdd.induction (P := fun ok₂ b₂ => (∀ t, ok₂ t → ok t) → ∀ b₁, Bdd ok b₁ → Diff3 Val ok d cmp b₁ b₂)
    ?_ ?_ ?_ ?_
  · intro ok₂ _ b₁ w₁; exact diff3_plain resp w₁ Bdd.top (d3_atom_right _ w₁ _ _)
  · intro ok₂ _ b₁ w₁; exact diff3_plain resp w₁ Bdd.bot (d3_atom_right _ w₁ _ _)
  · intro ok₂ k x y h sub b₁ w₁; exact diff3_left resp spec ok b₁ w₁ (fun _ h => h) k x y (sub _ h)
  · intro ok₂ hh a₂ c₂ u₂ d₂ isLeaf oka hc hu hd ic iu id sub b₁ w₁
    have sub' : ∀ t, Above ok₂ a₂ t → ok t := fun t ht => sub t ht.1
    have lift : ∀ t, Above ok₂ a₂ t → Above ok a₂ t := fun t ht => ⟨sub t ht.1, ht.2⟩
    have w₂ : Bdd ok (.tuple #[.integer hh, a₂, c₂, u₂, d₂]) :=
      Bdd.node_iff.mpr ⟨isLeaf, sub _ oka, hc.mono lift, hu.mono lift, hd.mono lift⟩
    obtain ⟨k₂, x₂, y₂, rfl⟩ := isLeaf
    rcases w₁.shape with rfl | rfl | ⟨k₁, x₁, y₁, rfl⟩ | ⟨h₁, l₁, c₁, u₁, d₁, rfl⟩
    · exact diff3_plain resp w₁ w₂ (d3_top_left _ _ _)
    · exact diff3_plain resp w₁ w₂ (d3_bot_left _ _ _)
    rotate_left
    · exact diff3_plain resp w₁ w₂ (by rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def])
    have h₁ : ok (.tuple #[.integer k₁, x₁, y₁]) := Bdd.leaf_iff.mp w₁
    classical
    let type : Term := .atom (if c₂ = .atom "bdd_top" then "none" else "intersection")
    obtain ⟨res, run, cmpOk⟩ := spec _ _ type (by simp only [type]; split <;> simp [TypeOk]) h₁ (sub _ oka)
    rcases cmpOk with ⟨rfl, dj⟩ | ⟨rfl, sb⟩ | ⟨ad, ai, rfl, had, hai, sad, sai, -, snone⟩ | rfl
    · obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := id sub' _ w₁
      obtain ⟨r, hr, okr, semr⟩ := iu sub' _ okr₁
      refine ⟨r, ?_, okr, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_top_atom]
        by_cases e : c₂ = .atom "bdd_top"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hr₁, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hr₁, hr]
      · rw [semr ρ v, semr₁ ρ v]
        have := dj ρ v
        simp only [eval_node, eval_leaf] at this ⊢
        revert this
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> cases eval ρ c₂ <;>
          cases eval ρ u₂ <;> cases eval ρ d₂ <;> simp
    · obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := ic sub' _ w₁
      obtain ⟨r, hr, okr, semr⟩ := iu sub' _ okr₁
      refine ⟨r, ?_, okr, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_top_atom]
        by_cases e : c₂ = .atom "bdd_top"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hr₁, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hr₁, hr]
      · rw [semr ρ v, semr₁ ρ v]
        have := sb ρ v
        simp only [eval_node, eval_leaf] at this ⊢
        revert this
        cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> cases eval ρ c₂ <;>
          cases eval ρ u₂ <;> cases eval ρ d₂ <;> simp
    · obtain ⟨r₁, hr₁, okr₁, semr₁⟩ := id sub' _ had.bdd
      obtain ⟨r₂, hr₂, okr₂, semr₂⟩ := iu sub' _ okr₁
      obtain ⟨r₃, hr₃, okr₃, semr₃⟩ := ic sub' _ hai.bdd
      obtain ⟨r₄, hr₄, okr₄, semr₄⟩ := iu sub' _ okr₃
      obtain ⟨r, hr, okr, semr⟩ := union_ok okr₂ okr₄
      refine ⟨r, ?_, okr ok okr₂ okr₄, fun ρ v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
        simp only [eq_top_atom]
        by_cases e : c₂ = .atom "bdd_top"
        · simp only [ite_eq_left e, type] at run ⊢; simp [run, hr₁, hr₂, hr₃, hr₄, hr]
        · simp only [ite_eq_right e, type] at run ⊢; simp [run, hr₁, hr₂, hr₃, hr₄, hr]
      · rw [semr ρ (resp ρ v), semr₂ ρ v, semr₁ ρ v, semr₄ ρ v, semr₃ ρ v, sad ρ v]
        simp only [eval_node, eval_leaf]
        by_cases e : c₂ = .atom "bdd_top"
        · have := snone (by simp [type, e])
          subst this e
          simp only [eval]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;>
            cases eval ρ u₂ <;> cases eval ρ d₂ <;> rfl
        · rw [sai (by simp [type, e]) ρ v]
          cases ρ (.tuple #[.integer k₁, x₁, y₁]) <;> cases ρ (.tuple #[.integer k₂, x₂, y₂]) <;> cases eval ρ c₂ <;>
            cases eval ρ u₂ <;> cases eval ρ d₂ <;> rfl
    · refine diff3_plain resp w₁ w₂ ?_
      rw [Elixir.Module.Types.Descr.«bdd_difference/3».eq_def]
      simp only [eq_top_atom]
      by_cases e : c₂ = .atom "bdd_top"
      · simp only [ite_eq_left e, type] at run ⊢; simp [run]
      · simp only [ite_eq_right e, type] at run ⊢; simp [run]

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! `disjoint?/2` on element types. -/

theorem not_true {c : Except Exception Term}
    (h : (do let w ← c; Erlang.erlang.«not/1» w) = .ok (.atom "true")) : c = .ok (.atom "false") := by
  cases c with
  | error e => simp at h
  | ok w =>
    change Erlang.erlang.«not/1» w = _ at h
    unfold Erlang.erlang.«not/1» at h
    split at h <;> simp_all

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Differences of list types on lists of values. -/

abbrev optListCmp : Term := .function false "Elixir.Module.Types.Descr" "opt_list_leaf_difference" 3 #[]

/-- The clause of `opt_list_difference/3` for two list literals. -/
theorem opt_list_leaves {d : Dispatcher} {S k₁ l₁ t₁ k₂ l₂ t₂ : Term}
    (nt : ¬(l₁ = .atom "term" ∧ t₁ = .atom "term"))
    (ne : compareExact (fuel (.tuple #[k₂, l₂, t₂]) (.tuple #[k₁, l₁, t₁])) (.tuple #[k₂, l₂, t₂]) (.tuple #[k₁, l₁, t₁]) ≠ .eq) :
    (Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "false") →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        Elixir.Module.Types.Descr.«bdd_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) optListCmp) ∧
    (Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«subtype?/2» d t₁ t₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        .ok (.atom "bdd_bot")) ∧
    (Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«subtype?/2» d t₁ t₂ = .ok (.atom "false") →
      Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_difference") (.tuple #[k₁, l₁, t₁])
        (.tuple #[k₂, l₂, t₂]) = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂])) ∧
    (∀ S', Elixir.Module.Types.Descr.«subtype?/2» d l₁ l₂ = .ok (.atom "true") →
      Elixir.Module.Types.Descr.«subtype?/2» d t₁ t₂ = .ok (.atom "false") →
      Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_difference") (.tuple #[k₁, l₁, t₁])
        (.tuple #[k₂, l₂, t₂]) = .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k₁, l₁, t₁]) (.tuple #[k₂, l₂, t₂]) S =
        (Elixir.Module.Types.Descr.«opt_difference/3» d t₁ t₂ S' >>=
          fun c => Elixir.Module.Types.Descr.«bdd_leaf_new/2» l₁ c)) := by
  refine ⟨fun h₁ => ?_, fun h₁ h₂ => ?_, fun h₁ h₂ h₃ => ?_, fun S' h₁ h₂ h₃ => ?_⟩ <;>
  · rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
    simp only [leaf_guard]
    rw [ite_eq_right (by simpa using ne)]
    split
    · exfalso; simp_all
    · rename_i heq₁ heq₂
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_eq heq₁
      obtain ⟨e₄, e₅, e₆⟩ := tuple3_eq heq₂
      subst e₁ e₂ e₃ e₄ e₅ e₆
      simp [*, Lynx.Except.andAlso, Erlang.erlang.«/=/2», optListCmp]
    · next h => exact (h _ _ _ _ _ _ rfl rfl).elim

theorem opt_list_same {d : Dispatcher} {S k a b y : Term} (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k, a, b]) y S = .ok (.atom "bdd_bot") := by
  rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
  simp only [leaf_guard]
  rw [ite_eq_left (by simpa using e)]
  rfl

/-- The top list leaf less a list field: the empty BDD when they are exactly equal, its negation otherwise. -/
theorem opt_list_top {d : Dispatcher} {S k y : Term} :
    Elixir.Module.Types.Descr.«opt_list_difference/3» d (.tuple #[k, .atom "term", .atom "term"]) y S =
      if compareExact (fuel y (.tuple #[k, .atom "term", .atom "term"])) y (.tuple #[k, .atom "term", .atom "term"]) = .eq then .ok (.atom "bdd_bot")
      else Elixir.Module.Types.Descr.«bdd_negation/1» y := by
  rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
  simp only [leaf_guard]
  split <;> simp_all

theorem opt_list_other {d : Dispatcher} {S x y : Term} (nt : ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"])
    (nl : ¬((∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b])) :
    Elixir.Module.Types.Descr.«opt_list_difference/3» d x y S =
      Elixir.Module.Types.Descr.«bdd_difference/3» d x y optListCmp := by
  rw [Elixir.Module.Types.Descr.«opt_list_difference/3».eq_def]
  simp only [leaf_guard]
  split
  · rw [ite_eq_right]
    · split
      · exfalso; simp_all
      · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
      · rfl
    · intro e
      obtain ⟨a, b, c, rfl, -⟩ := exact_tuple3 e
      exact nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩
  · split
    · exact (nt _ rfl).elim
    · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
    · rfl

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Differences of fields of flat types, on points of values. -/

/-- Differences of function types hold the arities of the first and not the second. -/
theorem fun_diff_spec (n : Nat) {x y : Term} (fx : FunF x) (fy : FunF y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 2)) (.atom "fun") x y = .ok w ∧
      (kept (.atom "fun", w) = Bool.true → FunF w ∧ ∀ a ρ, Resp ρ → arityOf w a ρ = (arityOf x a ρ && !arityOf y a ρ)) ∧
      (kept (.atom "fun", w) = Bool.false → ∀ a ρ, Resp ρ → (arityOf x a ρ && !arityOf y a ρ) = Bool.false) := by
  have size : ∀ M : List (Term × Term), M ≠ [] → ∃ s : Nat, s ≠ 0 ∧ Erlang.erlang.«map_size/1» (.map M) = .ok (.integer s) := by
    intro M ne; cases M with
    | nil => exact absurd rfl ne
    | cons e rest => exact size_cons e rest
  obtain ⟨p₁, R₁, rfl, b₁⟩ := fx
  obtain ⟨p₂, R₂, rfl, b₂⟩ := fy
  cases p₁ <;> cases p₂
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 2) b₂ b₁
    exact fun_finish Bool.true M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun h => by cases h) (fun _ hM => by
        subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»])
      (fun _ hM => by
        obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne])
  · obtain ⟨M, run, bM, sem, -⟩ := repr_union_sem (n + 1) b₁ b₂
    exact fun_finish Bool.false M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]
        cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun _ => by
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso])
      (fun h => by cases h) (fun h => by cases h)
  · obtain ⟨M, run, bM, sem, -⟩ := repr_inter_sem (n + 1) b₁ b₂
    exact fun_finish Bool.true M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]
        cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun h => by cases h) (fun _ hM => by
        subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»])
      (fun _ hM => by
        obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne])
  · obtain ⟨M, run, bM, sem, -⟩ := repr_diff_sem (n + 2) b₁ b₂
    exact fun_finish Bool.true M bM _ (fun a ρ resp => by
        rw [sem a ρ resp, arity_tag, arity_tag]; cases evalR R₁ a ρ <;> cases evalR R₂ a ρ <;> rfl) _
      (fun h => by cases h) (fun _ hM => by
        subst hM
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»])
      (fun _ hM => by
        obtain ⟨s, ne, sz⟩ := size M hM
        have : (s : Int) ≠ 0 := by omega
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne])

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

theorem lt_true {a b : Term} (h : Erlang.erlang.«</2» a b = .ok Term.true) : Term.compare (Term.fuel a b) a b = .lt := by
  refine Classical.byContradiction fun ne => ?_
  simp [Erlang.erlang.«</2», ne, Term.true] at h

theorem is_atom_true {a : Term} (h : Erlang.erlang.«is_atom/1» a = .ok Term.true) : ∃ s : String, a = .atom s := by
  cases a <;> simp_all [Erlang.erlang.«is_atom/1», Term.true]

/-- The keys `sorted_keys?/1` checks: atoms in increasing order. -/
theorem sorted_keys_spec : ∀ l : List (Term × Term), «sorted_keys?/1» (fieldsTerm l) = .ok Term.true →
    (∀ e ∈ l, ∃ s : String, e.1 = .atom s) ∧ l.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt)
  | [], _ => ⟨by simp, by simp⟩
  | [(k, v)], h => by
    rw [«sorted_keys?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    exact ⟨by simpa using is_atom_true h, by simp⟩
  | (k, v) :: (k', v') :: rest, h => by
    rw [«sorted_keys?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨ha, hlt⟩, hr⟩ := h
    obtain ⟨keys, pw⟩ := sorted_keys_spec ((k', v') :: rest) (by simpa [fieldsTerm, Term.list] using hr)
    have lt := lt_true (by simpa [Term.true] using hlt)
    refine ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨fun e me => ?_, pw⟩⟩
    · rcases List.mem_cons.mp me with rfl | me
      · exact is_atom_true (by simpa [Term.true] using ha)
      · exact keys e me
    · rcases List.mem_cons.mp me with rfl | me
      · exact lt
      · exact cmp_lt_trans lt ((List.pairwise_cons.mp pw).1 e me)

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Literal heights: how deep literals nest in a type, up to exact equality. -/

theorem sizeOf_entry_lt {X : List (Term × Term)} {e : Term × Term} (h : e ∈ mapEntries X) :
    sizeOf e.2 < sizeOf (Term.map X) := by
  have m := mem_of_mem_mapEntries h
  have := List.sizeOf_lt_of_mem m
  simp only [Term.map.sizeOf_spec]
  cases e with
  | mk a b => simp at this ⊢; omega

/-- The height of literals in a type: literals add one to the height of their parts, except the top leaf `{_, open, []}`
and the top list leaf, which have no height, and BDD nodes, lists, pairs, and maps take the largest height of their
parts. The top type has no height either: its literals are those top leaves. The top BDD counts as a literal, since
differences from it hold the literals they remove, and so does the empty BDD, since the difference of the top list
leaf and the empty BDD is the top BDD. The literal of the expansion of a recursive node,
`{_, closed, [term(), node]}`, is as high as the node, so unfolding a node keeps its height. -/
def lh : Term → Nat
  | .atom "bdd_top" => 1
  | .atom "bdd_bot" => 1
  | .tuple ⟨[_, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩ =>
    lh (.tuple ⟨[.reference r, .map a, b]⟩)
  | .tuple ⟨[_, .atom "open", .nil]⟩ => 0
  | .tuple ⟨[.integer 46675407, .atom "term", .atom "term"]⟩ => 0
  | .tuple ⟨[.reference _, .map _, _]⟩ => 1
  | .tuple ⟨[_, x, y]⟩ => max (lh x) (lh y) + 1
  | .tuple ⟨[_, .tuple ⟨[_, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩,
      c, u, d]⟩ => max (lh (.tuple ⟨[.reference r, .map a, b]⟩)) (max (lh c) (max (lh u) (lh d)))
  | .tuple ⟨[_, .tuple ⟨[_, x, y]⟩, c, u, d]⟩ => max (max (lh x) (lh y) + 1) (max (lh c) (max (lh u) (lh d)))
  | .tuple ⟨[a, b, c, d, e]⟩ => max (lh a) (max (lh b) (max (lh c) (max (lh d) (lh e))))
  | .tuple ⟨[a, b]⟩ => max (lh a) (lh b)
  | .cons h t => max (lh h) (lh t)
  | .map X => ((mapEntries X).attach.map fun ⟨e, _⟩ => lh e.2).foldr max 0
  | _ => 0
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | (rename_i h; have := sizeOf_entry_lt h; simp only [Term.map.sizeOf_spec] at this; simp_wf; omega)
    | (simp_wf; omega)

/-- Lists of exactly equal terms. -/
def ExactL : List Term → List Term → Prop
  | [], [] => True
  | a :: as, b :: bs => compareExact (fuel a b) a b = .eq ∧ ExactL as bs
  | _, _ => False

theorem exactL_of_lex : ∀ {xs ys : List Term}, List.compareLex (fun a b => compareExact (fuel a b) a b) xs ys = .eq → ExactL xs ys
  | [], [], _ => trivial
  | [], _ :: _, h => by simp [List.compareLex_nil_cons] at h
  | _ :: _, [], h => by simp [List.compareLex_cons_nil] at h
  | _ :: _, _ :: _, h => by
    simp only [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
    exact ⟨h.1, exactL_of_lex h.2⟩

theorem tuple_exact {xs : Array Term} {b : Term} (h : compareExact (fuel (.tuple xs) b) (.tuple xs) b = .eq) :
    ∃ ys : Array Term, b = .tuple ys ∧ ExactL xs.toList ys.toList := by
  cases b <;> rw [compareExact_step] at h <;> simp [Compare.compareStep] at h
  rename_i ys
  exact ⟨ys, rfl, exactL_of_lex h.2⟩

theorem cons_exact {x xs b : Term} (h : compareExact (fuel (.cons x xs) b) (.cons x xs) b = .eq) :
    ∃ y ys, b = .cons y ys ∧ compareExact (fuel x y) x y = .eq ∧ compareExact (fuel xs ys) xs ys = .eq := by
  obtain ⟨y, ys, rfl⟩ := cons_compareExact_eq x xs b h
  rw [compareExact_cons, Ordering.then_eq_eq] at h
  exact ⟨y, ys, rfl, h⟩

theorem map_exact {X : List (Term × Term)} {b : Term} (h : compareExact (fuel (.map X) b) (.map X) b = .eq) :
    ∃ Y, b = .map Y := by
  cases b <;> rw [compareExact_step] at h <;> simp [Compare.compareStep] at h
  exact ⟨_, rfl⟩

theorem foldr_max_le {l : List Nat} {n : Nat} : l.foldr max 0 ≤ n ↔ ∀ x ∈ l, x ≤ n := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.max_le]

theorem lh_map_le {X : List (Term × Term)} {n : Nat} : lh (.map X) ≤ n ↔ ∀ e ∈ mapEntries X, lh e.2 ≤ n := by
  rw [lh, foldr_max_le]
  constructor
  · intro h e me
    exact h _ (List.mem_map.mpr ⟨⟨e, me⟩, List.mem_attach _ _, rfl⟩)
  · intro h x mx
    obtain ⟨⟨e, me⟩, -, rfl⟩ := List.mem_map.mp mx
    exact h e me

theorem le_lh_map {X : List (Term × Term)} {e : Term × Term} (me : e ∈ mapEntries X) : lh e.2 ≤ lh (.map X) :=
  lh_map_le.mp (Nat.le_refl _) e me

theorem entry_of_lookup {X : List (Term × Term)} {q v : Term} (h : mapLookup X q = some v) :
    ∃ e ∈ mapEntries X, e.2 = v := by
  rw [← mapLookup_mapEntries] at h
  simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, rfl⟩

theorem lookup_exact {X Y : List (Term × Term)} (h : compareExact (fuel (.map X) (.map Y)) (.map X) (.map Y) = .eq) {q v : Term}
    (hv : mapLookup X q = some v) : ∃ w, mapLookup Y q = some w ∧ compareExact (fuel v w) v w = .eq := by
  have rel := lookup_of_map_compareExact_eq X Y h q
  rw [hv] at rel
  cases hw : mapLookup Y q with
  | none => rw [hw] at rel; cases rel
  | some w => rw [hw] at rel; cases rel; exact ⟨w, rfl, by assumption⟩

theorem lh_leaf_top (k : Term) : lh (.tuple ⟨[k, .atom "open", .nil]⟩) = 0 := by simp [lh]

theorem lh_leaf_list : lh (.tuple ⟨[.integer 46675407, .atom "term", .atom "term"]⟩) = 0 := by simp [lh]

/-- The literal of the expansion of a recursive node `{ref, state, generator}`, `{_, closed, [term(), node]}`. -/
def NodeLit (_k x y : Term) : Prop :=
  x = .atom "closed" ∧ ∃ r a b, y = .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)

theorem lh_nodeLit {k : Term} {r : List Nat} {a : List (Term × Term)} {b : Term} :
    lh (.tuple ⟨[k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩) =
      lh (.tuple ⟨[.reference r, .map a, b]⟩) := by
  rw [lh]

theorem lh_node_term {r : List Nat} {a : List (Term × Term)} {b : Term} :
    lh (.tuple ⟨[.reference r, .map a, b]⟩) = 1 := by
  rw [lh]

theorem lh_leaf (k x y : Term) (ho : ¬(x = .atom "open" ∧ y = .nil))
    (ht : ¬(k = .integer 46675407 ∧ x = .atom "term" ∧ y = .atom "term")) (hn : ¬NodeLit k x y)
    (hr : ¬∃ r a, k = .reference r ∧ x = .map a) :
    lh (.tuple ⟨[k, x, y]⟩) = max (lh x) (lh y) + 1 := by
  rw [lh]
  all_goals first
    | (intro r a h₁ h₂; exact hr ⟨r, a, h₁, h₂⟩)
    | (intro r a b h₁ h₂; subst h₁ h₂; exact hn ⟨rfl, r, a, b, rfl⟩)
    | (intro h₁ h₂; exact ho ⟨h₁, h₂⟩)
    | (rintro rfl rfl rfl; exact ht ⟨rfl, rfl, rfl⟩)

/-- Expansion literals of recursive nodes, which count as high as the node in BDD nodes. -/
def litZ : Term → Term → Bool
  | .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference _, .map _, _]⟩) .nil) => Bool.true
  | _, _ => Bool.false

theorem lh_node (h a x y c u d : Term) (hz : litZ x y = Bool.false) :
    lh (.tuple ⟨[h, .tuple ⟨[a, x, y]⟩, c, u, d]⟩) = max (max (lh x) (lh y) + 1) (max (lh c) (max (lh u) (lh d))) := by
  rw [lh]
  rintro r a b rfl rfl; simp [litZ] at hz

theorem lh_node_z (h a x y c u d : Term) (hz : litZ x y = Bool.true) :
    lh (.tuple ⟨[h, .tuple ⟨[a, x, y]⟩, c, u, d]⟩) = max (lh (.tuple ⟨[a, x, y]⟩)) (max (lh c) (max (lh u) (lh d))) := by
  unfold litZ at hz
  split at hz
  · conv => lhs; rw [lh]
    rw [lh_nodeLit]
  · cases hz

/-- BDD nodes of literals other than top leaves are as high as their literal and their branches. -/
theorem lh_node_lit (h k x y c u d : Term) (ho : ¬(x = .atom "open" ∧ y = .nil))
    (hl : ¬(k = .integer 46675407 ∧ x = .atom "term" ∧ y = .atom "term")) (hr : ¬∃ r a, k = .reference r ∧ x = .map a) :
    lh (.tuple ⟨[h, .tuple ⟨[k, x, y]⟩, c, u, d]⟩) = max (lh (.tuple ⟨[k, x, y]⟩)) (max (lh c) (max (lh u) (lh d))) := by
  cases hz : litZ x y
  · rw [lh_node _ _ _ _ _ _ _ hz, lh_leaf _ _ _ ho hl ?_ hr]
    rintro ⟨rfl, r, a, b, rfl⟩; simp [litZ] at hz
  · rw [lh_node_z _ _ _ _ _ _ _ hz]

theorem lh_five (a b c d e : Term) (hb : ∀ k x y, b ≠ .tuple ⟨[k, x, y]⟩) :
    lh (.tuple ⟨[a, b, c, d, e]⟩) = max (lh a) (max (lh b) (max (lh c) (max (lh d) (lh e)))) := by
  rw [lh]
  all_goals first
    | exact fun _ _ _ h => hb _ _ _ h
    | exact fun _ h => hb _ _ _ h
    | exact fun _ _ _ _ h => hb _ _ _ h

theorem nil_exact {y y' : Term} (h : compareExact (fuel y y') y y' = .eq) : y = .nil ↔ y' = .nil := by
  constructor
  · rintro rfl; exact (compareExact_eq_nil _).mp (Lynx.Term.compareExact_eq_symm h)
  · rintro rfl; exact (compareExact_eq_nil _).mp h

theorem atom_exact {y y' : Term} {s : String} (h : compareExact (fuel y y') y y' = .eq) : y = .atom s ↔ y' = .atom s := by
  constructor
  · rintro rfl; exact (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm h)
  · rintro rfl; exact (compareExact_eq_atom _ _).mp h

theorem int_exact {y y' : Term} {n : Int} (h : compareExact (fuel y y') y y' = .eq) : y = .integer n ↔ y' = .integer n := by
  constructor
  · rintro rfl; exact (integer_compareExact_eq _ _).mp h
  · rintro rfl; exact (compareExact_eq_integer _ _).mp h

theorem nodeLit_exact {k x y k' x' y' : Term} (_e₁ : compareExact (fuel k k') k k' = .eq) (e₂ : compareExact (fuel x x') x x' = .eq)
    (e₃ : compareExact (fuel y y') y y' = .eq) (h : NodeLit k x y) : NodeLit k' x' y' := by
  obtain ⟨rfl, r, a, b, rfl⟩ := h
  · refine ⟨(atom_compareExact_eq _ _).mp e₂ |>.symm ▸ rfl, ?_⟩
    obtain ⟨t, rest, rfl, et, er⟩ := cons_exact e₃
    obtain ⟨n, _, rfl, en, enil⟩ := cons_exact er
    obtain ⟨ys, rfl, ex⟩ := tuple_exact en
    obtain ⟨l⟩ := ys
    match l, ex with
    | [r', a', b'], ex =>
      obtain ⟨A', rfl⟩ := map_exact ex.2.1
      refine ⟨r, A', b', ?_⟩
      rw [(atom_compareExact_eq _ _).mp et, (nil_exact enil).mp rfl, (reference_compareExact_eq _ _).mp ex.1]

theorem litZ_exact {x y x' y' : Term} (e₂ : compareExact (fuel x x') x x' = .eq) (e₃ : compareExact (fuel y y') y y' = .eq) :
    litZ x y = litZ x' y' := by
  have one : ∀ {x y x' y' : Term}, compareExact (fuel x x') x x' = .eq → compareExact (fuel y y') y y' = .eq → litZ x y = Bool.true →
      litZ x' y' = Bool.true := by
    intro x y x' y' e₂ e₃ h
    unfold litZ at h
    split at h
    · rename_i r a b
      rw [(atom_compareExact_eq _ _).mp e₂]
      obtain ⟨t, rest, rfl, et, er⟩ := cons_exact e₃
      obtain ⟨n, _, rfl, en, enil⟩ := cons_exact er
      obtain ⟨ys, rfl, ex⟩ := tuple_exact en
      obtain ⟨l⟩ := ys
      match l, ex with
      | [r', a', b'], ex =>
        obtain ⟨A', rfl⟩ := map_exact ex.2.1
        rw [(atom_compareExact_eq _ _).mp et, (nil_exact enil).mp rfl, (reference_compareExact_eq _ _).mp ex.1]
        rfl
    · cases h
  cases h : litZ x y
  · cases h' : litZ x' y'
    · rfl
    · rw [one (Lynx.Term.compareExact_eq_symm e₂) (Lynx.Term.compareExact_eq_symm e₃) h'] at h; cases h
  · exact (one e₂ e₃ h).symm

/-- Literal heights do not change under exact equality. -/
theorem lh_exact : ∀ (n : Nat) (a b : Term), sizeOf a < n → compareExact (fuel a b) a b = .eq → lh a = lh b
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, b, size, h => by
    have ih := lh_exact n
    cases a with
    | tuple xs =>
      obtain ⟨ys, rfl, ex⟩ := tuple_exact h
      obtain ⟨l⟩ := xs
      obtain ⟨l'⟩ := ys
      simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec] at size
      simp only at ex
      match l, l', ex with
      | [], [], _ => rfl
      | [a₁], [b₁], ex => simp [lh]
      | [a₁, a₂], [b₁, b₂], ex =>
        simp only [List.cons.sizeOf_spec] at size
        simp only [lh]
        rw [ih a₁ b₁ (by omega) ex.1, ih a₂ b₂ (by omega) ex.2.1]
      | [a₁, a₂, a₃], [b₁, b₂, b₃], ex =>
        simp only [List.cons.sizeOf_spec] at size
        by_cases top : a₂ = .atom "open" ∧ a₃ = .nil
        · obtain ⟨rfl, rfl⟩ := top
          rw [(atom_exact ex.2.1).mp rfl, (nil_exact ex.2.2.1).mp rfl, lh_leaf_top, lh_leaf_top]
        have top' : ¬(b₂ = .atom "open" ∧ b₃ = .nil) := fun ⟨h₂, h₃⟩ =>
          top ⟨(atom_exact ex.2.1).mpr h₂, (nil_exact ex.2.2.1).mpr h₃⟩
        by_cases lt : a₁ = .integer 46675407 ∧ a₂ = .atom "term" ∧ a₃ = .atom "term"
        · obtain ⟨rfl, rfl, rfl⟩ := lt
          rw [(int_exact ex.1).mp rfl, (atom_exact ex.2.1).mp rfl, (atom_exact ex.2.2.1).mp rfl]
        have lt' : ¬(b₁ = .integer 46675407 ∧ b₂ = .atom "term" ∧ b₃ = .atom "term") := fun ⟨h₁, h₂, h₃⟩ =>
          lt ⟨(int_exact ex.1).mpr h₁, (atom_exact ex.2.1).mpr h₂, (atom_exact ex.2.2.1).mpr h₃⟩
        by_cases nd : ∃ r p, a₁ = .reference r ∧ a₂ = .map p
        · obtain ⟨r, p, rfl, rfl⟩ := nd
          have rr := (reference_compareExact_eq _ _).mp ex.1
          obtain ⟨Q, rfl⟩ := map_exact ex.2.1
          subst rr
          rw [lh_node_term, lh_node_term]
        have nd' : ¬∃ r p, b₁ = .reference r ∧ b₂ = .map p := by
          rintro ⟨r, p, rfl, rfl⟩
          have rr := (reference_compareExact_eq _ _).mp (Lynx.Term.compareExact_eq_symm ex.1)
          obtain ⟨Q, rfl⟩ := map_exact (Lynx.Term.compareExact_eq_symm ex.2.1)
          exact nd ⟨r, Q, rr, rfl⟩
        by_cases nl : NodeLit a₁ a₂ a₃
        · obtain ⟨rfl, r, p, q, rfl⟩ := nl
          obtain ⟨t, rest, e₃, et, er⟩ := cons_exact ex.2.2.1
          obtain ⟨n, _, rfl, en, enil⟩ := cons_exact er
          obtain ⟨ys, rfl, exn⟩ := tuple_exact en
          obtain ⟨l⟩ := ys
          match l, exn with
          | [r', p', q'], exn =>
            have rb := (atom_exact ex.2.1).mp rfl
            have rt := (atom_compareExact_eq _ _).mp et
            have rn := (nil_exact enil).mp rfl
            have rr := (reference_compareExact_eq _ _).mp exn.1
            obtain ⟨Q, rfl⟩ := map_exact exn.2.1
            subst rb rt rn rr e₃
            rw [lh_nodeLit, lh_nodeLit]
            exact ih _ _ (by simp at size ⊢; omega) en
        have nl' : ¬NodeLit b₁ b₂ b₃ := fun h => nl (nodeLit_exact (Lynx.Term.compareExact_eq_symm ex.1)
          (Lynx.Term.compareExact_eq_symm ex.2.1) (Lynx.Term.compareExact_eq_symm ex.2.2.1) h)
        rw [lh_leaf _ _ _ top lt nl nd, lh_leaf _ _ _ top' lt' nl' nd', ih a₂ b₂ (by omega) ex.2.1,
          ih a₃ b₃ (by omega) ex.2.2.1]
      | [a₁, a₂, a₃, a₄], [b₁, b₂, b₃, b₄], ex => simp [lh]
      | [a₁, a₂, a₃, a₄, a₅], [b₁, b₂, b₃, b₄, b₅], ex =>
        simp only [List.cons.sizeOf_spec] at size
        have i₃ := ih a₃ b₃ (by omega) ex.2.2.1
        have i₄ := ih a₄ b₄ (by omega) ex.2.2.2.1
        have i₅ := ih a₅ b₅ (by omega) ex.2.2.2.2.1
        by_cases three : ∃ k x y, a₂ = .tuple ⟨[k, x, y]⟩
        · obtain ⟨k, x, y, rfl⟩ := three
          obtain ⟨ys, rfl, exl⟩ := tuple_exact ex.2.1
          obtain ⟨l₂⟩ := ys
          simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec, List.cons.sizeOf_spec] at size
          simp only at exl
          match l₂, exl with
          | [k', x', y'], exl =>
            have z : litZ x y = litZ x' y' := litZ_exact exl.2.1 exl.2.2.1
            cases hz : litZ x y
            · rw [lh_node _ _ _ _ _ _ _ hz, lh_node _ _ _ _ _ _ _ (z ▸ hz), i₃, i₄, i₅, ih x x' (by omega) exl.2.1,
                ih y y' (by omega) exl.2.2.1]
            · rw [lh_node_z _ _ _ _ _ _ _ hz, lh_node_z _ _ _ _ _ _ _ (z ▸ hz), i₃, i₄, i₅,
                ih _ _ (by simp at size ⊢; omega) ex.2.1]
          | [], exl => exact exl.elim
          | [_], exl => exact exl.2.elim
          | [_, _], exl => exact exl.2.2.elim
          | _ :: _ :: _ :: _ :: _, exl => exact exl.2.2.2.elim
        · have three' : ∀ k x y, b₂ ≠ .tuple ⟨[k, x, y]⟩ := by
            rintro k x y rfl
            obtain ⟨ys, e, exl⟩ := tuple_exact (Lynx.Term.compareExact_eq_symm ex.2.1)
            subst e
            obtain ⟨l₂⟩ := ys
            simp only at exl
            match l₂, exl with
            | [k', x', y'], _ => exact three ⟨k', x', y', rfl⟩
            | [], exl => exact exl.elim
            | [_], exl => exact exl.2.elim
            | [_, _], exl => exact exl.2.2.elim
            | _ :: _ :: _ :: _ :: _, exl => exact exl.2.2.2.elim
          rw [lh_five _ _ _ _ _ fun k x y h' => three ⟨k, x, y, h'⟩, lh_five _ _ _ _ _ three', i₃, i₄, i₅,
            ih a₁ b₁ (by omega) ex.1, ih a₂ b₂ (by omega) ex.2.1]
      | _ :: _ :: _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _ :: _ :: _, ex => simp [lh]
      | [], _ :: _, ex => exact ex.elim
      | _ :: _, [], ex => exact ex.elim
      | [_], _ :: _ :: _, ex => exact ex.2.elim
      | _ :: _ :: _, [_], ex => exact ex.2.elim
      | [_, _], _ :: _ :: _ :: _, ex => exact ex.2.2.elim
      | _ :: _ :: _ :: _, [_, _], ex => exact ex.2.2.elim
      | [_, _, _], _ :: _ :: _ :: _ :: _, ex => exact ex.2.2.2.elim
      | _ :: _ :: _ :: _ :: _, [_, _, _], ex => exact ex.2.2.2.elim
      | [_, _, _, _], _ :: _ :: _ :: _ :: _ :: _, ex => exact ex.2.2.2.2.elim
      | _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _], ex => exact ex.2.2.2.2.elim
      | [_, _, _, _, _], _ :: _ :: _ :: _ :: _ :: _ :: _, ex => exact ex.2.2.2.2.2.elim
      | _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _], ex => exact ex.2.2.2.2.2.elim
    | cons x xs =>
      obtain ⟨y, ys, rfl, ex, exs⟩ := cons_exact h
      simp only [Term.cons.sizeOf_spec] at size
      simp only [lh]
      rw [ih x y (by omega) ex, ih xs ys (by omega) exs]
    | map X =>
      obtain ⟨Y, rfl⟩ := map_exact h
      have sym := Lynx.Term.compareExact_eq_symm h
      apply Nat.le_antisymm
      · refine lh_map_le.mpr fun e me => ?_
        obtain ⟨w, hw, ew⟩ := lookup_exact h (mapLookup_of_mem_mapEntries me)
        obtain ⟨e', me', rfl⟩ := entry_of_lookup hw
        rw [ih e.2 e'.2 (by have := sizeOf_entry_lt me; omega) ew]
        exact le_lh_map me'
      · refine lh_map_le.mpr fun e' me' => ?_
        obtain ⟨w, hw, ew⟩ := lookup_exact sym (mapLookup_of_mem_mapEntries me')
        obtain ⟨e, me, rfl⟩ := entry_of_lookup hw
        rw [← ih e.2 e'.2 (by have := sizeOf_entry_lt me; omega) (Lynx.Term.compareExact_eq_symm ew)]
        exact le_lh_map me
    | _ =>
      cases b <;> rw [compareExact_step] at h <;> simp [Compare.compareStep] at h <;>
        first | rfl | (subst_vars; rfl) | simp [lh]

/-! Element types of values: the interface each nesting level provides to the next. -/

/-- Seen sets of BDDs whose literals reach height `N`, and at least 1: their literals have elements. The BDDs are
keyed by their kind or arity. -/
def SafeN (N : Nat) (S : List (Term × Term)) : Prop :=
  ∀ e ∈ S, ∃ (h b : Term), e.1 = .cons h b ∧ 1 ≤ lh b ∧ N ≤ lh b

theorem safeN_nil (N : Nat) : SafeN N [] := fun _ h => by simp at h

/-- Seen sets as `SafeN`, except that BDDs keyed by an arity, which only function checks look up, may be one lower. -/
def SafeT (N : Nat) (S : List (Term × Term)) : Prop :=
  ∀ e ∈ S, ∃ (h b : Term), e.1 = .cons h b ∧ 1 ≤ lh b ∧ (N ≤ lh b ∨ (∃ i : Int, h = .integer i) ∧ N ≤ lh b + 1)

theorem SafeN.toT {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) : SafeT N S := fun e me =>
  let ⟨h, b, e₁, one, hb⟩ := hS e me
  ⟨h, b, e₁, one, Or.inl hb⟩

/-- Types that combine the node `nd` with types of height zero: their tuple field is a BDD of the expansion literal
of `nd`, and their other fields have height zero. -/
def Combo (nd a : Term) : Prop :=
  a = .atom "term" ∨ IsT nd a ∨ ∃ X, a = .map X ∧
    (∀ w, mapLookup X (.atom "tuple") = some w → OField (PureLit nd) w) ∧
    ∀ name w, name ≠ "tuple" → mapLookup X (.atom name) = some w → lh w = 0

/-- Seen sets of walks on tuple BDDs of height one: their keys are higher than zero and are not tuple BDDs of the
expansion literal of `nd`. -/
def Safe1 (nd : Term) (S : List (Term × Term)) : Prop :=
  SafeN 1 S ∧ ∀ e ∈ S, ∀ x, OField (PureLit nd) x → compareExact (fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 ≠ .eq

/-- Element types `E` of values `V`: closed under the plain and optimized operations, which hold the values `den`
says, with exact emptiness and sound subtyping and disjointness, at every call depth from `K`. Plain operations keep
literals, so they keep literal heights; emptiness is sound when the seen BDDs are higher than the type, and `tl`
holds of the values the tail of an improper list cannot be. -/
structure EF (nd : Term) (E : Term → Prop) (V : Type) (den : Term → V → Prop) (tl : V → Prop) (K : Nat) : Prop where
  term : E (.atom "term")
  den_term : ∀ v, den (.atom "term") v
  static : ∀ {a}, E a → Static a
  node : ∀ {a}, E a → IsNode a → IsT nd a
  low : ∀ {a}, E a → lh a = 0 → Combo nd a
  cinter : ∀ {a b c m}, E a → E b → Combo nd a → Combo nd b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c → Combo nd c
  cdiff : ∀ {a b c m}, E a → E b → Combo nd a → Combo nd b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c → Combo nd c
  cempty : ∀ {a S m b}, E a → Combo nd a → Safe1 nd S → K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b) → (b = Bool.true ↔ ∀ v, ¬den a v)
  inhabited : Nonempty V
  resp : ∀ {e e' : Term} {v : V}, E e → E e' → compare (fuel e e') e e' = .eq → den e' v → den e v
  union : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
    (∀ v, den c v ↔ den a v ∨ den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N
  inter : ∀ {a b}, E a → E b → ∃ c, E c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
    (∀ v, den c v ↔ den a v ∧ den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N
  diff : ∀ {a b}, E a → E b → ∃ c, E c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
    (∀ v, den c v ↔ den a v ∧ ¬den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N
  opt_union : ∀ {a b} (S : List (Term × Term)) {m}, E a → E b → K ≤ m → ∃ c, E c ∧
    Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧ ∀ v, den c v ↔ den a v ∨ den b v
  opt_inter : ∀ {a b} (S : List (Term × Term)) {m}, E a → E b → K ≤ m → ∃ c, E c ∧
    Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧ ∀ v, den c v ↔ den a v ∧ den b v
  opt_diff : ∀ {a b} (S : List (Term × Term)) {m}, E a → E b → K ≤ m → ∃ c, E c ∧
    Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧ ∀ v, den c v ↔ den a v ∧ ¬den b v
  empty : ∀ {a} (S : List (Term × Term)), E a → ∃ b : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) ∧
    ∀ N, lh a < N → SafeN N S → (b = Bool.true ↔ ∀ v, ¬den a v)
  sub : ∀ {a b}, E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s)) ∧
    (s = Bool.true → ∀ v, den a v → den b v)
  subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true")
  disj : ∀ {a b}, E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
    (s = Bool.true → ∀ v, den a v → den b v → False)
  sdisj : ∀ {a b} (S : List (Term × Term)), E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) a b (.map S) = .ok (boolAtom s)) ∧
    ∀ N, lh a < N → lh b < N → SafeN N S → (s = Bool.true ↔ ∀ v, den a v → den b v → False)
  fuse : ∀ {a b} (n : Int) {m}, E a → E b → compareExact (fuel a b) a b ≠ .eq → K ≤ m → ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
    (r = .atom "nil" ∨ (E r ∧ ∀ v, den r v ↔ den a v ∨ den b v))
  tail : ∀ {e}, E e → ∃ e', (∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«list_tail_unfold/1» (D m) e = .ok e') ∧ E e' ∧
    (∀ v, den e' v ↔ den e v ∧ ¬tl v) ∧ lh e' ≤ lh e
  tl_witness : ∃ v, ¬tl v
  none : E (.map [])
  pos : 1 ≤ K

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types below a literal height. -/
abbrev EB (E : Term → Prop) (N : Nat) (a : Term) : Prop := E a ∧ lh a < N

theorem lh_nil_map : lh (.map []) = 0 := by
  refine Nat.le_zero.mp (lh_map_le.mpr fun e me => ?_)
  have := mem_of_mem_mapEntries me
  simp at this

theorem EF.ops (ef : EF nd E V den tl K) (N : Nat) (hN : 0 < N) : ElemOk (EB E N) K :=
  ⟨⟨ef.term, by simpa [lh] using hN⟩,
    fun ha hb => let ⟨c, hc, run, _, h⟩ := ef.inter ha.1 hb.1; ⟨c, ⟨hc, h N ha.2 hb.2⟩, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha.1; ⟨b, run⟩, ⟨ef.none, by rw [lh_nil_map]; exact hN⟩, ef.pos⟩

theorem EF.dops (ef : EF nd E V den tl K) (N : Nat) : ElemDiff (EB E N) K :=
  ⟨fun ha hb => let ⟨c, hc, run, _, h⟩ := ef.diff ha.1 hb.1; ⟨c, ⟨hc, h N ha.2 hb.2⟩, run⟩⟩

theorem EF.jops (ef : EF nd E V den tl K) (N : Nat) : ElemDisj (EB E N) K :=
  ⟨fun ha hb S => let ⟨s, run, _⟩ := ef.sdisj S ha.1 hb.1; ⟨s, fun m hm => run m (by omega)⟩⟩

theorem EF.sem (ef : EF nd E V den tl K) (N : Nat) : ElemSem (EB E N) K V den (SafeN N) where
  term := ef.den_term
  inter := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.inter ha.1 hb.1
    rw [run' _ hm] at run; cases run; exact h v
  diff := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.diff ha.1 hb.1
    rw [run' _ hm] at run; cases run; exact h v
  empty := fun {a S m b} ha hS hm run => by
    obtain ⟨b', run', h⟩ := ef.empty S ha.1
    rw [run' _ hm] at run
    have : b' = b := by cases b <;> cases b' <;> simp_all [boolAtom]
    subst this
    exact h N ha.2 hS
  inhabited := ef.inhabited
  resp := fun he he' h d => ef.resp he.1 he'.1 h d

theorem EF.tsem (ef : EF nd E V den tl K) (N : Nat) : TailSem (EB E N) den tl :=
  ⟨fun he => let ⟨e', run, he', h, hl⟩ := ef.tail he.1; ⟨e', run, ⟨he', by have := he.2; omega⟩, h⟩, ef.tl_witness⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Flat element types: the bottom nesting level, whose values are bits, atoms, and the kinds of other values. -/

/-- Maps of size one hold a single key, up to exact equality. -/
theorem size_one_keys {A : List (Term × Term)} (h : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    {q q' x x' : Term} (hx : mapLookup A q = some x) (hx' : mapLookup A q' = some x') : compareExact (fuel q q') q q' = .eq := by
  simp only [Erlang.erlang.«map_size/1», Except.ok.injEq, Term.integer.injEq, equalExact_eq_decide] at h
  have mem : ∀ {q x}, mapLookup A q = some x → ∃ e ∈ A, compareExact (fuel q e.1) q e.1 = .eq := by
    intro q x hq
    simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hq
    obtain ⟨e, he, -⟩ := hq
    exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩
  obtain ⟨e, me, qe⟩ := mem hx
  obtain ⟨e', me', qe'⟩ := mem hx'
  cases A with
  | nil => simp at me
  | cons e₀ rest =>
    simp only [List.map_cons, List.eraseDupsBy_cons, List.length_cons] at h
    have none : List.filter (fun b => decide ((decide (compareExact (fuel b e₀.1) b e₀.1 = .eq)) = Bool.false)) (rest.map Prod.fst) = [] := by
      cases hf : List.filter (fun b => decide ((decide (compareExact (fuel b e₀.1) b e₀.1 = .eq)) = Bool.false)) (rest.map Prod.fst) with
      | nil => rfl
      | cons a as =>
        exfalso
        rw [hf, List.eraseDupsBy_cons] at h
        simp at h
        omega
    have all : ∀ f ∈ e₀ :: rest, compareExact (fuel f.1 e₀.1) f.1 e₀.1 = .eq := by
      intro f mf
      rcases List.mem_cons.mp mf with rfl | mf
      · simp
      · have := List.filter_eq_nil_iff.mp none f.1 (List.mem_map.mpr ⟨f, mf, rfl⟩)
        simpa using this
    exact Lynx.Term.compareExact_eq_trans (Lynx.Term.compareExact_eq_trans qe (all e me))
      (Lynx.Term.compareExact_eq_symm (Lynx.Term.compareExact_eq_trans qe' (all e' me')))

theorem lh_top61 : lh (.tuple #[.integer 61102469, .atom "open", .nil]) = 0 := lh_leaf_top _

theorem safeF_of {N : Nat} {S : List (Term × Term)} (h : SafeN N S) : SafeF S := by
  refine ⟨S, rfl, fun e me kind hit => ?_⟩
  obtain ⟨k, b, e₁, one, -⟩ := h e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
  rw [lh_top61] at this
  omega

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of tuple literals of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

def SameD (den : Term → V → Prop) (x y : Term) : Prop := ∀ v, den x v ↔ den y v
def SubD (den : Term → V → Prop) (x y : Term) : Prop := ∀ v, den x v → den y v

/-- What the status of a walk over the elements of two tuple literals says about the walked elements. -/
def StatusInv (den : Term → V → Prop) (status : Term) (p₁ p₂ : List Term) : Prop :=
  (status = .atom "all_equal" ∧ Pairs (SameD den) p₁ p₂) ∨
  (∃ (j : Nat) (d₁ d₂ : Term) (a₁ b₁ a₂ b₂ : List Term),
    status = Term.tuple #[Term.atom "one_index_difference", Term.integer j, d₁, d₂] ∧ p₁ = a₁ ++ d₁ :: b₁ ∧ p₂ = a₂ ++ d₂ :: b₂ ∧
    a₁.length = j ∧ Pairs (SameD den) a₁ a₂ ∧ Pairs (SameD den) b₁ b₂ ∧ compareExact (fuel d₁ d₂) d₁ d₂ ≠ .eq) ∨
  (status = .atom "left_subtype_of_right" ∧ Pairs (SubD den) p₁ p₂) ∨
  (status = .atom "right_subtype_of_left" ∧ Pairs (SubD den) p₂ p₁)

theorem StatusInv.endSt {st : Term} {p₁ p₂ : List Term} (h : StatusInv den st p₁ p₂) :
    StatusInv den (endSt st) p₁ p₂ := by
  rcases h with ⟨rfl, pr⟩ | h | h | h
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, pr.mono fun _ _ h v => (h v).mp⟩))
  · have h' := h
    obtain ⟨_, _, _, _, _, _, _, rfl, -⟩ := h'
    rw [endSt_of_ne (by simp)]; exact Or.inr (Or.inl h)
  · rw [endSt_of_ne (by rw [h.1]; simp)]; exact Or.inr (Or.inr (Or.inl h))
  · rw [endSt_of_ne (by rw [h.1]; simp)]; exact Or.inr (Or.inr (Or.inr h))

theorem same_of_exact (ef : EF nd E V den tl K) {x y : Term} (hx : E x) (hy : E y) (h : compareExact (fuel y x) y x = .eq) : (SameD den) x y := by
  have c := compare_eq_of_compareExact_eq _ _ h
  exact fun v => ⟨fun d => ef.resp hy hx c d, fun d => ef.resp hx hy (Lynx.Term.compare_eq_symm c) d⟩

theorem sub_bool (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {a b : Term} (ha : E a) (hb : E b) :
    ∃ s : Bool, Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧ (s = Bool.true → (SubD den) a b) := by
  obtain ⟨s, hs, sound⟩ := ef.sub ha hb
  exact ⟨s, hs m hm, sound⟩

/-- The walk of `opt_tuple_union_strategy_index/4` over the elements of two tuple literals. -/
theorem walk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (r₁ r₂ p₁ p₂ : List Term) (status : Term), (∀ e ∈ r₁, E e) →
    (∀ e ∈ r₂, E e) → (∀ e ∈ p₁, E e) → (∀ e ∈ p₂, E e) → p₁.length = p₂.length →
    StatusInv den status p₁ p₂ → ∃ res,
      Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m) (Term.list r₁) (Term.list r₂)
        (.integer (p₁.length : Int)) status = .ok res ∧
      (res = Term.atom "none" ∨ ∃ c₁ s₁ c₂ s₂, r₁ = c₁ ++ s₁ ∧ r₂ = c₂ ++ s₂ ∧ List.length c₁ = List.length c₂ ∧
        (s₁ = [] ∨ s₂ = []) ∧ StatusInv den res (p₁ ++ c₁) (p₂ ++ c₂)) ∧
      (status = .atom "left_subtype_of_right" ∨ status = .atom "right_subtype_of_left" →
        res = status ∨ res = .atom "none") ∧ res ≠ .atom "all_equal" := by
  intro r₁
  induction r₁ with
  | nil =>
    intro r₂ p₁ p₂ status _ _ _ _ _ inv
    refine ⟨endSt status, by simpa using index_nil_left (D m) r₂ _ status,
      Or.inr ⟨[], [], [], r₂, rfl, rfl, rfl, Or.inl rfl, by simpa using inv.endSt⟩,
      fun h => Or.inl (endSt_of_ne (by rcases h with h | h <;> rw [h] <;> simp)), endSt_ne status⟩
  | cons x xs ih =>
    intro r₂ p₁ p₂ status h₁ h₂ hp₁ hp₂ len inv
    cases r₂ with
    | nil =>
      refine ⟨endSt status, by simpa using index_nil_right (D m) (x :: xs) _ status,
        Or.inr ⟨[], x :: xs, [], [], rfl, rfl, rfl, Or.inr rfl, by simpa using inv.endSt⟩,
        fun h => Or.inl (endSt_of_ne (by rcases h with h | h <;> rw [h] <;> simp)), endSt_ne status⟩
    | cons y ys =>
      have hx : E x := h₁ x List.mem_cons_self
      have hy : E y := h₂ y List.mem_cons_self
      have h₁' : ∀ e ∈ xs, E e := fun e m => h₁ e (List.mem_cons_of_mem _ m)
      have h₂' : ∀ e ∈ ys, E e := fun e m => h₂ e (List.mem_cons_of_mem _ m)
      have hp₁' : ∀ e ∈ p₁ ++ [x], E e := fun e m => by
        rcases List.mem_append.mp m with m | m
        · exact hp₁ e m
        · simp at m; subst m; exact hx
      have hp₂' : ∀ e ∈ p₂ ++ [y], E e := fun e m => by
        rcases List.mem_append.mp m with m | m
        · exact hp₂ e m
        · simp at m; subst m; exact hy
      have len' : (p₁ ++ [x]).length = (p₂ ++ [y]).length := by simp [len]
      have lenS : ((p₁ ++ [x]).length : Int) = ((p₁.length + 1 : Nat) : Int) := by simp
      -- continuing the walk with a new status
      have cont : ∀ st, StatusInv den st (p₁ ++ [x]) (p₂ ++ [y]) → ∃ res,
          Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m) (Term.list xs) (Term.list ys)
            (.integer ((p₁.length + 1 : Nat) : Int)) st = .ok res ∧
          (res = Term.atom "none" ∨ ∃ c₁ s₁ c₂ s₂, x :: xs = c₁ ++ s₁ ∧ y :: ys = c₂ ++ s₂ ∧ List.length c₁ = List.length c₂ ∧
            (s₁ = [] ∨ s₂ = []) ∧ StatusInv den res (p₁ ++ c₁) (p₂ ++ c₂)) ∧
          (st = .atom "left_subtype_of_right" ∨ st = .atom "right_subtype_of_left" →
            res = st ∨ res = .atom "none") ∧ res ≠ .atom "all_equal" := by
        intro st inv'
        obtain ⟨res, run, out, keep, ne⟩ := ih ys (p₁ ++ [x]) (p₂ ++ [y]) st h₁' h₂' hp₁' hp₂' len' inv'
        rw [lenS] at run
        refine ⟨res, run, ?_, keep, ne⟩
        rcases out with e | ⟨c₁, s₁, c₂, s₂, e₁, e₂, lc, sc, inv''⟩
        · exact Or.inl e
        · refine Or.inr ⟨x :: c₁, s₁, y :: c₂, s₂, by simp [e₁], by simp [e₂], by simp [lc], sc, ?_⟩
          simpa using inv''
      by_cases same : compareExact (fuel y x) y x = .eq
      · have sd := same_of_exact ef hx hy same
        have inv' : StatusInv den status (p₁ ++ [x]) (p₂ ++ [y]) := by
          rcases inv with ⟨e, pr⟩ | ⟨j, d₁, d₂, a₁, b₁, a₂, b₂, e, rfl, rfl, lj, pa, pb, nd⟩ | ⟨e, pr⟩ | ⟨e, pr⟩
          · exact Or.inl ⟨e, pr.snoc sd⟩
          · exact Or.inr (Or.inl ⟨j, d₁, d₂, a₁, b₁ ++ [x], a₂, b₂ ++ [y], e, by simp, by simp, lj, pa, pb.snoc sd, nd⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨e, pr.snoc fun v h => (sd v).mp h⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨e, pr.snoc fun v h => (sd v).mpr h⟩))
        obtain ⟨res, run, out, keep, ne⟩ := cont status inv'
        refine ⟨res, ?_, out, keep, ne⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
        simp [Erlang.erlang.«=:=/2», same]
        simpa [Term.list] using run
      rcases inv with ⟨rfl, pr⟩ | ⟨j, d₁, d₂, a₁, b₁, a₂, b₂, rfl, rfl, rfl, lj, pa, pb, nd⟩ | ⟨rfl, pr⟩ | ⟨rfl, pr⟩
      · obtain ⟨res, run, out, -, ne⟩ := cont (.tuple #[.atom "one_index_difference", .integer (p₁.length : Int), x, y])
          (Or.inr (Or.inl ⟨p₁.length, x, y, p₁, [], p₂, [], rfl, rfl, rfl, rfl, pr, trivial,
            fun h => same (Lynx.Term.compareExact_eq_symm h)⟩))
        refine ⟨res, ?_, out, fun h => by simp at h, ne⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
        simp [Erlang.erlang.«=:=/2», same]
        simpa [Term.list] using run
      · have hd₁ : E d₁ := hp₁ d₁ (by simp)
        have hd₂ : E d₂ := hp₂ d₂ (by simp)
        obtain ⟨s₁, r₁, k₁⟩ := sub_bool ef hm hd₁ hd₂
        obtain ⟨s₂, r₂, k₂⟩ := sub_bool ef hm hx hy
        obtain ⟨s₃, r₃, k₃⟩ := sub_bool ef hm hd₂ hd₁
        obtain ⟨s₄, r₄, k₄⟩ := sub_bool ef hm hy hx
        by_cases l : (s₁ && s₂) = Bool.true
        · simp only [Bool.and_eq_true] at l
          obtain ⟨rfl, rfl⟩ := l
          have pr : Pairs (SubD den) (a₁ ++ d₁ :: b₁ ++ [x]) (a₂ ++ d₂ :: b₂ ++ [y]) :=
            ((pa.mono fun _ _ h v => (h v).mp).append (show Pairs (SubD den) (d₁ :: b₁) (d₂ :: b₂) from
              ⟨k₁ rfl, pb.mono fun _ _ h v => (h v).mp⟩)).snoc (k₂ rfl)
          obtain ⟨res, run, out, -, ne⟩ := cont (.atom "left_subtype_of_right") (Or.inr (Or.inr (Or.inl ⟨rfl, pr⟩)))
          refine ⟨res, ?_, out, fun h => by simp at h, ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, r₂,
            Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
          simpa [Term.list] using run
        by_cases rr : (s₃ && s₄) = Bool.true
        · simp only [Bool.and_eq_true] at rr
          obtain ⟨rfl, rfl⟩ := rr
          have pr : Pairs (SubD den) (a₂ ++ d₂ :: b₂ ++ [y]) (a₁ ++ d₁ :: b₁ ++ [x]) :=
            ((pa.swap fun _ _ h v => (h v).mpr).append (show Pairs (SubD den) (d₂ :: b₂) (d₁ :: b₁) from
              ⟨k₃ rfl, pb.swap fun _ _ h v => (h v).mpr⟩)).snoc (k₄ rfl)
          obtain ⟨res, run, out, -, ne⟩ := cont (.atom "right_subtype_of_left") (Or.inr (Or.inr (Or.inr ⟨rfl, pr⟩)))
          refine ⟨res, ?_, out, fun h => by simp at h, ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          cases s₁ <;> cases s₂ <;> simp at l <;>
            simp [Erlang.erlang.«=:=/2», same, r₁, r₂,
              r₃, r₄, Lynx.Except.andAlso, Erlang.erlang.«/=/2»] <;>
            simpa [Term.list] using run
        · refine ⟨.atom "none", ?_, Or.inl rfl, fun _ => Or.inr rfl, by simp⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          cases s₁ <;> cases s₂ <;> cases s₃ <;> cases s₄ <;> simp at l rr <;>
            simp [Erlang.erlang.«=:=/2», same, r₁, r₂,
              r₃, r₄, Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
      · obtain ⟨s₁, r₁, k₁⟩ := sub_bool ef hm hx hy
        cases s₁
        · refine ⟨.atom "none", ?_, Or.inl rfl, fun _ => Or.inr rfl, by simp⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
        · obtain ⟨res, run, out, keep, ne⟩ := cont (.atom "left_subtype_of_right")
            (Or.inr (Or.inr (Or.inl ⟨rfl, pr.snoc (k₁ rfl)⟩)))
          refine ⟨res, ?_, out, fun _ => keep (Or.inl rfl), ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
          simpa [Term.list] using run
      · obtain ⟨s₁, r₁, k₁⟩ := sub_bool ef hm hy hx
        cases s₁
        · refine ⟨.atom "none", ?_, Or.inl rfl, fun _ => Or.inr rfl, by simp⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
        · obtain ⟨res, run, out, keep, ne⟩ := cont (.atom "right_subtype_of_left")
            (Or.inr (Or.inr (Or.inr ⟨rfl, pr.snoc (k₁ rfl)⟩)))
          refine ⟨res, ?_, out, fun _ => keep (Or.inr rfl), ne⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same, r₁, isMember]
          simpa [Term.list] using run

theorem inT_sub {c : Bool} : ∀ {a b : List Term}, Pairs (SubD den) a b → ∀ {v : List V}, InT den c a v → InT den c b v
  | [], [], _, _, h => h
  | _ :: _, _ :: _, _, [], h => h.elim
  | _ :: _, _ :: _, p, _ :: _, h => ⟨p.1 _ h.1, inT_sub p.2 h.2⟩
  | [], _ :: _, p, _, _ => p.elim
  | _ :: _, [], p, _, _ => p.elim

theorem inT_same {c : Bool} {a b : List Term} (p : Pairs (SameD den) a b) {v : List V} :
    InT den c a v ↔ InT den c b v :=
  ⟨inT_sub (p.mono fun _ _ h v => (h v).mp), inT_sub (p.swap fun _ _ h v => (h v).mpr)⟩

theorem inT_sub_open {c : Bool} {a b s : List Term} (p : Pairs (SubD den) a b) {v : List V} (h : InT den c (a ++ s) v) :
    InT den Bool.false b v := by
  obtain ⟨v₁, v₂, rfl, h₁, -⟩ := (InT.append a).mp h
  exact InT.extend v₂ (inT_sub p h₁)

/-- What `opt_tuple_union_strategy/4` answers about two tuple literals. -/
def StratOk (den : Term → V → Prop) (t₁ : String) (l₁ : List Term) (t₂ : String) (l₂ : List Term) (res : Term) : Prop :=
  res ≠ .atom "all_equal" ∧
  (∀ (j : Int) d₁ d₂, res = .tuple #[.atom "one_index_difference", .integer j, d₁, d₂] → t₁ = t₂ ∧
    ∃ a₁ b₁ a₂ b₂, l₁ = a₁ ++ d₁ :: b₁ ∧ l₂ = a₂ ++ d₂ :: b₂ ∧ (List.length a₁ : Int) = j ∧ Pairs (SameD den) a₁ a₂ ∧
      Pairs (SameD den) b₁ b₂ ∧ compareExact (fuel d₁ d₂) d₁ d₂ ≠ .eq) ∧
  (res = .atom "left_subtype_of_right" → ∀ v, InT den (t₁ == "closed") l₁ v → InT den (t₂ == "closed") l₂ v) ∧
  (res = .atom "right_subtype_of_left" → ∀ v, InT den (t₂ == "closed") l₂ v → InT den (t₁ == "closed") l₁ v)

theorem stratOk_none (den : Term → V → Prop) (t₁ : String) (l₁ : List Term) (t₂ : String) (l₂ : List Term) :
    StratOk den t₁ l₁ t₂ l₂ (.atom "none") :=
  ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

/-- `opt_tuple_union_strategy/4` answers soundly about two tuple literals of element types. -/
theorem strategy_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e) :
    ∃ res, Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» (D m) (.atom t₁) (Term.list l₁) (.atom t₂)
      (Term.list l₂) = .ok res ∧ StratOk den t₁ l₁ t₂ l₂ res := by
  have nil₁ : ∀ e ∈ ([] : List Term), E e := by simp
  rw [strategy_start _ t₁ t₂ g₁ g₂]
  by_cases c₁ : t₁ = t₂ ∧ l₁.length = l₂.length
  · rw [ite_eq_left c₁]
    obtain ⟨res, run, out, -, ne⟩ := walk ef hm l₁ l₂ [] [] (.atom "all_equal") h₁ h₂ nil₁ nil₁ rfl
      (Or.inl ⟨rfl, trivial⟩)
    refine ⟨res, by simpa using run, ?_⟩
    rcases out with rfl | ⟨c₁', s₁, c₂', s₂, rfl, rfl, lc, sc, inv⟩
    · exact stratOk_none den _ _ _ _
    have e₁ := split_full lc sc (Nat.le_of_eq c₁.2)
    have e₂ := split_full lc.symm sc.symm (Nat.le_of_eq c₁.2.symm)
    subst e₁ e₂
    simp only [List.nil_append, List.append_nil] at inv ⊢
    obtain ⟨rfl, -⟩ := c₁
    rcases inv with ⟨rfl, pr⟩ | ⟨j, d₁, d₂, a₁, b₁, a₂, b₂, rfl, rfl, rfl, lj, pa, pb, nd⟩ | ⟨rfl, pr⟩ | ⟨rfl, pr⟩
    · exact absurd rfl ne
    · refine ⟨fun h => by simp at h, fun j' d₁' d₂' h => ?_, fun h => by simp at h, fun h => by simp at h⟩
      simp only [Term.tuple.injEq] at h
      have ej := congrArg (fun a : Array Term => a[1]?) h
      have ed₁ := congrArg (fun a : Array Term => a[2]?) h
      have ed₂ := congrArg (fun a : Array Term => a[3]?) h
      simp at ej ed₁ ed₂
      subst ed₁ ed₂
      exact ⟨rfl, a₁, b₁, a₂, b₂, rfl, rfl, by omega, pa, pb, nd⟩
    · exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun _ v hv => inT_sub pr hv,
        fun h => by simp at h⟩
    · exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun h => by simp at h,
        fun _ v hv => inT_sub pr hv⟩
  rw [ite_eq_right c₁]
  by_cases c₂ : t₁ = "open" ∧ l₁.length ≤ l₂.length
  · rw [ite_eq_left c₂]
    obtain ⟨res, run, out, keep, -⟩ := walk ef hm l₁ l₂ [] [] (.atom "right_subtype_of_left") h₁ h₂ nil₁ nil₁ rfl
      (Or.inr (Or.inr (Or.inr ⟨rfl, trivial⟩)))
    refine ⟨res, by simpa using run, ?_⟩
    rcases keep (Or.inr rfl) with rfl | rfl
    · rcases out with h | ⟨c₁', s₁, c₂', s₂, rfl, rfl, lc, sc, inv⟩
      · simp at h
      have e₁ := split_full lc sc c₂.2
      subst e₁
      simp only [List.nil_append] at inv
      rcases inv with ⟨h, -⟩ | ⟨_, _, _, _, _, _, _, h, -⟩ | ⟨h, -⟩ | ⟨-, pr⟩ <;> try simp at h
      obtain ⟨rfl, -⟩ := c₂
      exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun h => by simp at h,
        fun _ v hv => by simpa using inT_sub_open pr hv⟩
    · exact stratOk_none den _ _ _ _
  rw [ite_eq_right c₂]
  by_cases c₃ : t₂ = "open" ∧ l₂.length ≤ l₁.length
  · rw [ite_eq_left c₃]
    obtain ⟨res, run, out, keep, -⟩ := walk ef hm l₁ l₂ [] [] (.atom "left_subtype_of_right") h₁ h₂ nil₁ nil₁ rfl
      (Or.inr (Or.inr (Or.inl ⟨rfl, trivial⟩)))
    refine ⟨res, by simpa using run, ?_⟩
    rcases keep (Or.inl rfl) with rfl | rfl
    · rcases out with h | ⟨c₁', s₁, c₂', s₂, rfl, rfl, lc, sc, inv⟩
      · simp at h
      have e₂ := split_full lc.symm sc.symm c₃.2
      subst e₂
      simp only [List.nil_append] at inv
      rcases inv with ⟨h, -⟩ | ⟨_, _, _, _, _, _, _, h, -⟩ | ⟨-, pr⟩ | ⟨h, -⟩ <;> try simp at h
      obtain ⟨rfl, -⟩ := c₃
      exact ⟨fun h => by simp at h, fun _ _ _ h => by simp at h, fun _ v hv => by simpa using inT_sub_open pr hv,
        fun h => by simp at h⟩
    · exact stratOk_none den _ _ _ _
  · rw [ite_eq_right c₃]
    exact ⟨_, rfl, stratOk_none den _ _ _ _⟩

theorem StatusInv.form {res : Term} {p q : List Term} (h : StatusInv den res p q) : StatusForm res := by
  rcases h with ⟨rfl, -⟩ | ⟨j, d₁, d₂, -, -, -, -, rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨j, d₁, d₂, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem strategy_form (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e)
    {res : Term} (run : Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» (D m) (.atom t₁) (Term.list l₁) (.atom t₂)
      (Term.list l₂) = .ok res) : StatusForm res := by
  have nil₁ : ∀ e ∈ ([] : List Term), E e := by simp
  have fromWalk : ∀ st, StatusInv den st [] [] → Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m)
      (Term.list l₁) (Term.list l₂) (.integer 0) st = .ok res → StatusForm res := by
    intro st inv w
    obtain ⟨res', run', out, -, -⟩ := walk ef hm l₁ l₂ [] [] st h₁ h₂ nil₁ nil₁ rfl inv
    have run'' : Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» (D m) (Term.list l₁) (Term.list l₂)
        (.integer 0) st = .ok res' := by simpa using run'
    rw [w] at run''
    cases run''
    rcases out with rfl | ⟨_, _, _, _, -, -, -, -, inv'⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact inv'.form
  rw [strategy_start _ t₁ t₂ g₁ g₂] at run
  by_cases c₁ : t₁ = t₂ ∧ l₁.length = l₂.length
  · rw [ite_eq_left c₁] at run; exact fromWalk _ (Or.inl ⟨rfl, trivial⟩) run
  rw [ite_eq_right c₁] at run
  by_cases c₂ : t₁ = "open" ∧ l₁.length ≤ l₂.length
  · rw [ite_eq_left c₂] at run; exact fromWalk _ (Or.inr (Or.inr (Or.inr ⟨rfl, trivial⟩))) run
  rw [ite_eq_right c₂] at run
  by_cases c₃ : t₂ = "open" ∧ l₂.length ≤ l₁.length
  · rw [ite_eq_left c₃] at run; exact fromWalk _ (Or.inr (Or.inr (Or.inl ⟨rfl, trivial⟩))) run
  rw [ite_eq_right c₃] at run
  cases run
  exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem union_one_index {c : Bool} {a₁ b₁ a₂ b₂ : List Term} {d₁ d₂ u : Term} (pa : Pairs (SameD den) a₁ a₂)
    (pb : Pairs (SameD den) b₁ b₂) (su : ∀ v, den u v ↔ den d₁ v ∨ den d₂ v) (v : List V) :
    InT den c (a₁ ++ u :: b₁) v ↔ InT den c (a₁ ++ d₁ :: b₁) v ∨ InT den c (a₂ ++ d₂ :: b₂) v := by
  constructor
  · intro h
    obtain ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ := (InT.mid a₁ u b₁).mp h
    rcases (su y).mp hy with hy | hy
    · exact Or.inl ((InT.mid a₁ d₁ b₁).mpr ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩)
    · exact Or.inr ((InT.mid a₂ d₂ b₂).mpr ⟨v₁, y, v₂, rfl, (inT_same pa).mp h₁, hy, (inT_same pb).mp h₂⟩)
  · rintro (h | h)
    · exact h.replace fun y hy => (su y).mpr (Or.inl hy)
    · obtain ⟨v₁, y, v₂, rfl, h₁, hy, h₂⟩ := (InT.mid a₂ d₂ b₂).mp h
      exact (InT.mid a₁ u b₁).mpr ⟨v₁, y, v₂, rfl, (inT_same pa).mpr h₁, (su y).mpr (Or.inr hy), (inT_same pb).mpr h₂⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fusing tuple literals of element types. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types with only the facts that do not involve emptiness, for lemmas that only need comparisons. -/
theorem EF.semR (ef : EF nd E V den tl K) : ElemSem E K V den (fun _ => False) where
  term := ef.den_term
  inter := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.inter ha hb
    rw [run' _ hm] at run; cases run; exact h v
  diff := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.diff ha hb
    rw [run' _ hm] at run; cases run; exact h v
  empty := fun _ hS _ _ => hS.elim
  inhabited := ef.inhabited
  resp := fun he he' h d => ef.resp he he' h d

/-- Keys of tuple and map literals as Descr builds them: closed literals have negative keys and fewer than 2^31
elements or fields, and open ones other than the top literal have non-negative keys. -/
def KeyOk (t : Term) : Prop := ∀ (k : Int) (tag : String) (l : List Term), t = .tuple #[.integer k, .atom tag, Term.list l] →
  (tag = "closed" → k < 0) ∧ (tag = "open" → l ≠ [] → 0 ≤ k)

/-- Tuple literals of element types, keyed as Descr keys them. -/
def TLit (E : Term → Prop) (t : Term) : Prop := TupleOk E t ∧ KeyOk t

theorem tlit_not : ∀ t, TLit E t → ¬IsTop t := fun _ h => h.1.2

theorem leaf_key_val (l : List Term) (h : Int) :
    Elixir.Module.Types.Descr.«bdd_leaf_key/2» (Term.list l) (.integer h) =
      .ok (.integer (min (l.length : Int) 2147483647 * 134217728 + h)) := by
  have isList : Erlang.erlang.«is_list/1» (Term.list l) = .ok (.atom "true") := by
    cases l <;> simp [Erlang.erlang.«is_list/1», Term.true]
  unfold Elixir.Module.Types.Descr.«bdd_leaf_key/2»
  simp [isList, length_list, Erlang.erlang.«bsl/2», Int.shiftLeft_eq]

theorem tuple3_inj {a b c a' b' c' : Term} (h : Term.tuple #[a, b, c] = Term.tuple #[a', b', c']) :
    a = a' ∧ b = b' ∧ c = c' := by
  simp only [Term.tuple.injEq] at h
  have := congrArg Array.toList h
  simpa using this

/-- New leaves get the keys Descr gives them. -/
theorem leaf_new_key (t : String) (g : t = "open" ∨ t = "closed") (l : List Term) :
    ∃ k : Int, Elixir.Module.Types.Descr.«bdd_leaf_new/2» (.atom t) (Term.list l) =
      .ok (.tuple #[.integer k, .atom t, Term.list l]) ∧ KeyOk (.tuple #[.integer k, .atom t, Term.list l]) := by
  have key : ∀ (k : Int), (t = "closed" → k < 0) → (t = "open" → 0 ≤ k) →
      KeyOk (.tuple #[.integer k, .atom t, Term.list l]) := by
    intro k hc ho k' tag l' e
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    have := list_inj e₃
    subst this
    exact ⟨hc, fun o _ => ho o⟩
  rcases g with rfl | rfl
  · obtain ⟨hash, hrun, hlt⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list l))
    exact ⟨min (l.length : Int) 2147483647 * 134217728 + hash,
      by simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, leaf_key_val],
      key _ (fun h => by simp at h) (fun _ => by have := Int.le_min.mpr ⟨Int.natCast_nonneg l.length, (by decide : (0 : Int) ≤ 2147483647)⟩; omega)⟩
  · obtain ⟨hash, hrun, hlt⟩ := Erlang.erlang.phash2_range (Term.list l)
    refine ⟨min (l.length : Int) 2147483647 * 134217728 + hash - 288230376151711744, by
      simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun, leaf_key_val, Erlang.erlang.«-/2_integers»],
      key _ (fun _ => ?_) (fun h => by simp at h)⟩
    have := Int.min_le_right (l.length : Int) 2147483647
    omega

theorem sameD_refl (x : Term) : SameD den x x := fun _ => Iff.rfl

theorem exact_pairs (ef : EF nd E V den tl K) : ∀ {a b : List Term}, (∀ e ∈ a, E e) → (∀ e ∈ b, E e) →
    compareExact (fuel (Term.list b) (Term.list a)) (Term.list b) (Term.list a) = .eq → Pairs (SameD den) a b
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h => by simp [Term.list] at h
  | _ :: _, [], _, _, h => by
    have := Lynx.Term.compareExact_eq_symm h
    simp [Term.list] at this
  | x :: a, y :: b, ha, hb, h => by
    rw [Term.list, Term.list, compareExact_cons] at h
    simp only [Ordering.then_eq_eq] at h
    exact ⟨same_of_exact ef (ha x (by simp)) (hb y (by simp)) h.1,
      exact_pairs ef (fun e m => ha e (by simp [m])) (fun e m => hb e (by simp [m])) h.2⟩

/-- `opt_tuple_fuse_elements/4` fuses elements that differ at most at one position, or gives up. -/
theorem fuse_elements_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (n : Int) :
    ∀ (e₁ e₂ acc : List Term), (∀ e ∈ e₁, E e) →
    (∀ e ∈ e₂, E e) → (∀ e ∈ acc, E e) → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4» (D m) (Term.list e₁) (Term.list e₂) (Term.list acc)
        (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ ∃ l, r = Term.list l ∧ (∀ e ∈ l, E e) ∧ List.length l = acc.length + e₁.length ∧
        ∀ c v, InT den c l v ↔ InT den c (acc.reverse ++ e₁) v ∨ InT den c (acc.reverse ++ e₂) v) := by
  intro e₁
  induction e₁ with
  | nil =>
    intro e₂ acc _ _ ha
    cases e₂ with
    | nil =>
      refine ⟨Term.list acc.reverse, ?_, Or.inr ⟨acc.reverse, rfl, fun e m => ha e (by simpa using m),
        by simp, fun c v => by simp⟩⟩
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
      simpa [Term.list] using reverse1_list acc
    | cons y ys =>
      refine ⟨_, ?_, Or.inl rfl⟩
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
      simp
  | cons x xs ih =>
    intro e₂ acc h₁ h₂ ha
    cases e₂ with
    | nil =>
      refine ⟨_, ?_, Or.inl rfl⟩
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
      simp
    | cons y ys =>
      have hx : E x := h₁ x (by simp)
      have hy : E y := h₂ y (by simp)
      by_cases same : compareExact (fuel y x) y x = .eq
      · obtain ⟨r, run, out⟩ := ih ys (x :: acc) (fun e m => h₁ e (by simp [m])) (fun e m => h₂ e (by simp [m]))
          (fun e m => by rcases List.mem_cons.mp m with rfl | m; exact hx; exact ha e m)
        refine ⟨r, ?_, ?_⟩
        · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same]
          simpa [Term.list] using run
        · rcases out with rfl | ⟨l, rfl, hl, ll, sl⟩
          · exact Or.inl rfl
          refine Or.inr ⟨l, rfl, hl, by simp [ll]; omega, fun c v => ?_⟩
          rw [sl c v]
          have sd := same_of_exact ef hx hy same
          have pr : Pairs (SameD den) (acc.reverse ++ x :: ys) (acc.reverse ++ y :: ys) :=
            (Pairs.refl sameD_refl _).append ⟨sd, Pairs.refl sameD_refl _⟩
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          rw [inT_same pr]
      · by_cases tails : compareExact (fuel (Term.list ys) (Term.list xs)) (Term.list ys) (Term.list xs) = .eq
        · obtain ⟨f, rf, ef'⟩ := ef.fuse n hx hy (fun h => same (Lynx.Term.compareExact_eq_symm h)) hm
          rcases ef' with rfl | ⟨hu, su⟩
          · refine ⟨_, ?_, Or.inl rfl⟩
            rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
            simp [Erlang.erlang.«=:=/2», same]
            simp [tails, rf]
          · have rev := reverse_list acc (f :: xs)
            refine ⟨_, ?_, Or.inr ⟨acc.reverse ++ f :: xs, rfl, fun e m => ?_, by simp, fun c v => ?_⟩⟩
            · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
              simp [Erlang.erlang.«=:=/2», same]
              simp only [Term.list] at rev
              have nf : Term.compareExact (Term.fuel f (.atom "false")) f (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel f (.atom "nil")) f (.atom "nil") ≠ .eq := by
                rcases ef.static hu with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩ <;> simp
              simp [tails, rf, nf.1, nf.2, rev]
            · simp only [List.mem_append, List.mem_reverse, List.mem_cons] at m
              rcases m with m | rfl | m
              · exact ha e m
              · exact hu
              · exact h₁ e (by simp [m])
            · exact union_one_index (Pairs.refl sameD_refl _)
                (exact_pairs ef (fun e m => (h₁ e (by simp [m]))) (fun e m => (h₂ e (by simp [m])))
                  tails) su v
        · refine ⟨_, ?_, Or.inl rfl⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
          simp [Erlang.erlang.«=:=/2», same]
          simp [tails]

/-- A fused leaf, holding the values of both leaves. -/
def FusedLeaf (E : Term → Prop) (den : Term → V → Prop) (t₁ : String) (l₁ : List Term) (t₂ : String) (l₂ : List Term) (r : Term) : Prop :=
  r = .atom "nil" ∨ ∃ (k : Int) (l : List Term), r = .tuple #[.integer k, .atom t₁, Term.list l] ∧
    (∀ e ∈ l, E e) ∧ l.length = l₁.length ∧ KeyOk r ∧ ∀ v, InT den (t₁ == "closed") l v ↔
      InT den (t₁ == "closed") l₁ v ∨ InT den (t₂ == "closed") l₂ v

theorem fuse_leaf_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (k₁ k₂ : Int) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (l₁ l₂ : List Term) (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» (D m) (.tuple #[.integer k₁, .atom t₁, Term.list l₁])
      (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) = .ok r ∧ FusedLeaf E den t₁ l₁ t₂ l₂ r := by
  by_cases same : t₂ = t₁ ∧ l₁.length = l₂.length
  · obtain ⟨rfl, len⟩ := same
    obtain ⟨r, run, out⟩ := fuse_elements_sem ef hm 3 l₁ l₂ [] h₁ h₂ (by simp)
    rcases out with rfl | ⟨l, rfl, hl, ll, sl⟩
    · refine ⟨_, ?_, Or.inl rfl⟩
      unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
      simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», len, Erlang.erlang.«and/2»,
        Term.true]
      simp only [Term.list] at run
      simp [run]
    · obtain ⟨k, hk, key⟩ := leaf_new_key t₂ g₁ l
      have nf : Term.compareExact (Term.fuel (Term.list l) (.atom "false")) (Term.list l) (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel (Term.list l) (.atom "nil")) (Term.list l) (.atom "nil") ≠ .eq := by
        cases l <;> simp [Term.list]
      refine ⟨_, ?_, Or.inr ⟨k, l, rfl, hl, by simpa using ll, key, fun v => by simpa using sl (t₂ == "closed") v⟩⟩
      unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
      simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», len, Erlang.erlang.«and/2»,
        Term.true]
      simp only [Term.list] at run
      simp [run, nf.1, nf.2, hk]
  · refine ⟨_, ?_, Or.inl rfl⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
    by_cases tags : t₂ = t₁
    · subst tags
      have len : ¬(l₁.length : Int) = l₂.length := by simp at same; omega
      simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», len, Erlang.erlang.«and/2»,
        Term.true, Term.false]
    · simp [Lynx.Except.guard, Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», tags, Erlang.erlang.«and/2»,
        Lynx.Except.tryWith, Term.true, Term.false]
      by_cases len : (l₁.length : Int) = l₂.length <;> simp [len]

theorem vT_lit (ef : EF nd E V den tl K) {v : List V} {k : Int} {t : String} {l : List Term} (g : t = "open" ∨ t = "closed")
    (hl : ∀ e ∈ l, E e) :
    valT E den v (.tuple #[.integer k, .atom t, Term.list l]) = Bool.true ↔ InT den (t == "closed") l v := by
  rw [valT_iff ef.semR ⟨k, t, l, rfl, g, hl⟩]
  exact ⟨lit_sem, fun h => ⟨k, t, l, rfl, h⟩⟩

theorem vT_fused (ef : EF nd E V den tl K) {v : List V} {k₁ k₂ k : Int} {t₁ t₂ : String} {l₁ l₂ l : List Term}
    (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed") (h₁ : ∀ e ∈ l₁, E e)
    (h₂ : ∀ e ∈ l₂, E e) (hl : ∀ e ∈ l, E e)
    (sem : ∀ v, InT den (t₁ == "closed") l v ↔ InT den (t₁ == "closed") l₁ v ∨ InT den (t₂ == "closed") l₂ v) :
    valT E den v (.tuple #[.integer k, .atom t₁, Term.list l]) =
      (valT E den v (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) || valT E den v (.tuple #[.integer k₂, .atom t₂, Term.list l₂])) := by
  have e := vT_lit ef (v := v) (k := k) g₁ hl
  have e₁ := vT_lit ef (v := v) (k := k₁) g₁ h₁
  have e₂ := vT_lit ef (v := v) (k := k₂) g₂ h₂
  have s := sem v
  cases a : valT E den v (.tuple #[.integer k, .atom t₁, Term.list l]) <;>
    cases b : valT E den v (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) <;>
    cases c : valT E den v (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) <;> simp_all

/-- What a fusion chain finds: a leaf other than the top literal and the rest of the union. -/
def ChainOk (E : Term → Prop) (den : Term → V → Prop) (ok : Term → Prop) (b leaf r : Term) : Prop :=
  r = .atom "nil" ∨ ∃ fused rest, r = .tuple #[fused, rest] ∧ TLit E fused ∧ Bdd ok rest ∧
    bsize rest < bsize b ∧ ∀ v, (valT E den v fused || eval (valT E den v) rest) = (eval (valT E den v) b || valT E den v leaf)

theorem fuse_current (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {kL : Int} {tL : String} {lL : List Term} (gL : tL = "open" ∨ tL = "closed")
    (hL : ∀ e ∈ lL, E e) {cur : Term} (hc : TLit E cur) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» (D m) cur (.tuple #[.integer kL, .atom tL, Term.list lL]) =
      .ok r ∧ (r = .atom "nil" ∨ (TLit E r ∧ ∀ v, valT E den v r = (valT E den v cur || valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL])))) := by
  obtain ⟨⟨⟨k, t, l, rfl, g, hl⟩, nt⟩, kc⟩ := hc
  obtain ⟨r, run, out⟩ := fuse_leaf_sem ef hm k kL t tL g l lL hl hL
  refine ⟨r, run, ?_⟩
  rcases out with rfl | ⟨k', l', rfl, hl', len, key, sem⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨⟨⟨⟨k', t, l', rfl, g, hl'⟩, fun ⟨k'', e⟩ => nt ⟨.integer k, ?_⟩⟩, key⟩,
      fun v => vT_fused ef g gL hl hL hl' sem⟩
    simp only [Term.tuple.injEq] at e
    have e₁ := congrArg (fun a : Array Term => a[1]?) e
    have e₂ := congrArg (fun a : Array Term => a[2]?) e
    simp [list_eq_nil] at e₁ e₂
    subst e₁ e₂
    cases l with
    | nil => rfl
    | cons _ _ => simp at len

theorem fuse_chain_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {kL : Int} {tL : String} {lL : List Term}
    (gL : tL = "open" ∨ tL = "closed") (hL : ∀ e ∈ lL, E e) :
    ∀ (limit : Nat) (ok : Term → Prop) (b : Term), Bdd ok b → (∀ t, ok t → TLit E t) → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m) b (.tuple #[.integer kL, .atom tL, Term.list lL])
        (.integer (limit : Int)) = .ok r ∧ ChainOk E den ok b (.tuple #[.integer kL, .atom tL, Term.list lL]) r := by
  intro limit
  induction limit with
  | zero =>
    intro ok b _ _
    refine ⟨_, ?_, Or.inl rfl⟩
    rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
    simp
  | succ n ih =>
    intro ok b wb lits
    have nz : ((n + 1 : Nat) : Int) ≠ 0 := by omega
    have nz' : (n : Int) + 1 ≠ 0 := by omega
    have sub : Erlang.erlang.«-/2» (.integer ((n + 1 : Nat) : Int)) (.integer 1) = .ok (.integer (n : Int)) := by
      rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
    have atomCase : ∀ s : String, Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m) (.atom s)
        (.tuple #[.integer kL, .atom tL, Term.list lL]) (.integer ((n + 1 : Nat) : Int)) = .ok (.atom "nil") := by
      intro s
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
      split <;> first | rfl | simp_all
    rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact ⟨_, atomCase _, Or.inl rfl⟩
    · exact ⟨_, atomCase _, Or.inl rfl⟩
    · have hc := lits _ (Bdd.leaf_iff.mp wb)
      obtain ⟨r, run, out⟩ := fuse_current ef hm gL hL hc
      have run' : Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» (D m) (.tuple ⟨[.integer k, x, y]⟩)
          (.tuple #[.integer kL, .atom tL, Term.list lL]) = .ok r := run
      rcases out with rfl | ⟨okr, sr⟩
      · refine ⟨_, ?_, Or.inl rfl⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        simp [nz', run', isMember]
      · have nf : Term.compareExact (Term.fuel r (.atom "false")) r (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel r (.atom "nil")) r (.atom "nil") ≠ .eq := by
          obtain ⟨⟨⟨_, _, _, rfl, -⟩, -⟩, -⟩ := okr
          simp
        refine ⟨_, ?_, Or.inr ⟨r, .atom "bdd_bot", rfl, okr, Bdd.bot, by simp [bsize_atom, bsize_leaf],
          fun v => by simp [sr v, eval]⟩⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        simp [nz', run', isMember, nf.1, nf.2]
    · obtain ⟨isLeaf, okl, hc, hu, hd⟩ := Bdd.node_iff.mp wb
      by_cases shape : c = .atom "bdd_top" ∧ d = .atom "bdd_bot"
      · obtain ⟨rfl, rfl⟩ := shape
        have hlit := lits _ okl
        obtain ⟨r, run, out⟩ := fuse_current ef hm gL hL hlit
        rcases out with rfl | ⟨okr, sr⟩
        · obtain ⟨r', run', out'⟩ := ih (Above ok lit) u hu (fun t ht => lits t ht.1)
          rcases out' with rfl | ⟨fused, rest, rfl, okf, wrest, srest, semr⟩
          · refine ⟨_, ?_, Or.inl rfl⟩
            rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
            simp [nz']
            rw [run]
            simp [run']
          · by_cases bot : rest = .atom "bdd_bot"
            · subst bot
              refine ⟨_, ?_, Or.inr ⟨fused, lit, rfl, okf, ?_, ?_, fun v => ?_⟩⟩
              · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
                simp [nz']
                rw [run]
                simp [run']
              · obtain ⟨k', x', y', rfl⟩ := isLeaf
                exact Bdd.leaf_iff.mpr okl
              · obtain ⟨k', x', y', rfl⟩ := isLeaf
                simp [bsize_atom] at srest
                simp [bsize_node, bsize_leaf, bsize_atom]; omega
              · have := semr v
                obtain ⟨k', x', y', rfl⟩ := isLeaf
                simp only [eval] at this ⊢
                revert this
                cases valT E den v fused <;> cases valT E den v (.tuple #[.integer k', x', y']) <;> cases eval (valT E den v) u <;>
                  cases valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL]) <;> simp
            · obtain ⟨hn, runn⟩ := node_new lit (.atom "bdd_top") rest (.atom "bdd_bot") isLeaf (Bdd.top (ok := ok))
                wrest (Bdd.bot (ok := ok))
              refine ⟨_, ?_, Or.inr ⟨fused, .tuple #[.integer hn, lit, .atom "bdd_top", rest, .atom "bdd_bot"], rfl,
                okf, Bdd.node_iff.mpr ⟨isLeaf, okl, Bdd.top, wrest, Bdd.bot⟩, ?_, fun v => ?_⟩⟩
              · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
                simp [nz']
                rw [run]
                simp [run']
                rw [runn]
                rfl
              · simp [bsize_node, bsize_atom] at srest ⊢; omega
              · have := semr v
                simp only [eval] at this ⊢
                revert this
                cases valT E den v fused <;> cases valT E den v lit <;> cases eval (valT E den v) u <;> cases eval (valT E den v) rest <;>
                  cases valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL]) <;> simp
        · have nf : Term.compareExact (Term.fuel r (.atom "false")) r (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel r (.atom "nil")) r (.atom "nil") ≠ .eq := by
            obtain ⟨⟨⟨_, _, _, rfl, -⟩, -⟩, -⟩ := okr
            simp
          refine ⟨_, ?_, Or.inr ⟨r, u, rfl, okr, hu.mono fun t ht => ht.1, by simp [bsize_node, bsize_atom],
            fun v => ?_⟩⟩
          · rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
            simp [nz']
            rw [run]
            simp [nf.1, nf.2]
          · simp only [eval, sr v]
            cases valT E den v lit <;> cases eval (valT E den v) u <;> cases valT E den v (.tuple #[.integer kL, .atom tL, Term.list lL]) <;> rfl
      · refine ⟨_, ?_, Or.inl rfl⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        split
        · rename_i e; simp at e; omega
        · rename_i e₁ e₂; simp at e₁; exact absurd ⟨e₁.2.2.1, e₁.2.2.2.2⟩ shape
        · rename_i e₁ e₂; simp at e₁
        · rfl

/-! Optimized unions of tuple types of flat element types. -/

abbrev TField (E : Term → Prop) (x : Term) : Prop := OField (TLit E) x

noncomputable def denTF (E : Term → Prop) (den : Term → V → Prop) (x : Term) (v : List V) : Bool := denO x (valT E den v)

theorem denTF_bdd {x : Term} (wx : Bdd (TLit E) x) (v : List V) : denTF E den x v = eval (valT E den v) x :=
  denO_bdd tlit_not wx _

theorem vT_top (k : Int) (v : List V) : valT E den v (.tuple #[.integer k, .atom "open", .nil]) = Bool.true :=
  valT_true ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩ ⟨k, "open", [], rfl, InT.open_nil v⟩

theorem denTF_top (k : Term) (v : List V) : denTF E den (.tuple #[k, .atom "open", .nil]) v = Bool.true :=
  denO_top k _

theorem denTF_exact {x y : Term} (fx : TField E x) (fy : TField E y) (e : compareExact (fuel y x) y x = .eq) (v : List V) :
    denTF E den y v = denTF E den x v :=
  denO_exact tlit_not fx fy e (valT_resp v)

theorem tuple_union_field {x y : Term} (hx : TField E x) (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok r ∧ TField E r ∧ ∀ v, denTF E den r v = (denTF E den x v || denTF E den y v) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl, Or.inl ⟨k, rfl⟩,
      fun v => by simp [denTF_top]⟩
  rcases hy with ⟨k, rfl⟩ | wy
  · exact ⟨_, tuple_union_right (not_top_of_ok wx tlit_not) _, Or.inl ⟨k, rfl⟩, fun v => by simp [denTF_top]⟩
  obtain ⟨r, hr, okr, semr⟩ := union_ok wx wy
  refine ⟨r, by rw [tuple_union_bdd (not_top_of_ok wx tlit_not) (not_top_of_ok wy tlit_not), hr],
    Or.inr (okr _ wx wy), fun v => ?_⟩
  rw [denTF_bdd (okr _ wx wy), denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]

/-- Leaves of tuple types of element types, including the top literal. -/
def LeafT (E : Term → Prop) (leaf : Term) : Prop :=
  ∃ (k : Int) (t : String) (l : List Term), leaf = .tuple #[.integer k, .atom t, Term.list l] ∧
    (t = "open" ∨ t = "closed") ∧ (∀ e ∈ l, E e) ∧ KeyOk leaf

theorem LeafT.field {leaf : Term} (h : LeafT E leaf) : TField E leaf := by
  obtain ⟨k, t, l, rfl, g, hl, key⟩ := h
  by_cases top : t = "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨k, t, l, rfl, g, hl⟩, fun ⟨k', e⟩ => top ?_⟩, key⟩)
    obtain ⟨-, e₁, e₂⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₁
    exact ⟨e₁, list_eq_nil.mp e₂⟩

theorem LeafT.val {leaf : Term} (h : LeafT E leaf) (v : List V) : denTF E den leaf v = valT E den v leaf := by
  rcases h.field with ⟨k, rfl⟩ | w
  · rw [denTF_top, vT_top]
  · rw [denTF_bdd w]
    obtain ⟨k, t, l, rfl, -⟩ := h
    simp

theorem leafT_of_ok {t : Term} (h : TLit E t) : LeafT E t := by
  obtain ⟨⟨⟨k, tag, l, rfl, g, hl⟩, -⟩, key⟩ := h
  exact ⟨k, tag, l, rfl, g, hl, key⟩

theorem union_leaf_step (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (b leaf : Term) (wb : Bdd (TLit E) b)
    (hleaf : LeafT E leaf)
    (ih : ∀ b' leaf', bsize b' < bsize b → Bdd (TLit E) b' → LeafT E leaf' → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b' leaf' = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (eval (valT E den v) b' || valT E den v leaf')) : ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b leaf = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (eval (valT E den v) b || valT E den v leaf) := by
  have hleaf' := hleaf
  obtain ⟨k, t, l, rfl, g, hl, -⟩ := hleaf
  obtain ⟨c, runc, okc⟩ := fuse_chain_sem ef hm g hl 64 (TLit E) b wb (fun _ h => h)
  have runc' : Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m) b (.tuple #[.integer k, .atom t, Term.list l])
      (.integer 64) = .ok c := by simpa using runc
  rcases okc with rfl | ⟨fused, rest, rfl, okf, wrest, srest, semc⟩
  · obtain ⟨r, hr, fr, sr⟩ := tuple_union_field (Or.inr wb) hleaf'.field
    refine ⟨r, ?_, fr, fun v => by rw [sr v, denTF_bdd wb, hleaf'.val]⟩
    rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
    simp [runc', hr]
  · by_cases bot : rest = .atom "bdd_bot"
    · subst bot
      have wf : Bdd (TLit E) fused := by
        obtain ⟨⟨⟨kf, tf, lf, rfl, gf, hlf⟩, nt⟩, key⟩ := okf
        exact Bdd.leaf_iff.mpr ⟨⟨⟨kf, tf, lf, rfl, gf, hlf⟩, nt⟩, key⟩
      refine ⟨fused, ?_, Or.inr wf, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
        simp [runc']
      · have := semc v
        rw [denTF_bdd wf]
        obtain ⟨⟨⟨kf, _, _, rfl, -⟩, -⟩, -⟩ := okf
        simpa [eval] using this
    · obtain ⟨r, hr, fr, sr⟩ := ih rest fused srest wrest (leafT_of_ok okf)
      refine ⟨r, ?_, fr, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
        simp [runc', hr]
      · rw [sr v, ← semc v]
        cases valT E den v fused <;> cases eval (valT E den v) rest <;> rfl

/-- `opt_tuple_union_leaf/2` adds a leaf to a union, fusing it with the leaves it can. -/
theorem union_leaf_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (n : Nat) (b leaf : Term), bsize b ≤ n →
    Bdd (TLit E) b → LeafT E leaf → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b leaf = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (eval (valT E den v) b || valT E den v leaf) := by
  intro n
  induction n with
  | zero =>
    intro b leaf sz wb hl
    exact union_leaf_step ef hm b leaf wb hl fun b' _ lt => by omega
  | succ n ih =>
    intro b leaf sz wb hl
    exact union_leaf_step ef hm b leaf wb hl fun b' leaf' lt wb' hl' => ih b' leaf' (by omega) wb' hl'

theorem TField.shape {x : Term} (h : TField E x) :
    x = .atom "bdd_top" ∨ x = .atom "bdd_bot" ∨ LeafT E x ∨
      (∃ (hh : Int) (lit c u d : Term), x = .tuple #[.integer hh, lit, c, u, d] ∧ Bdd (TLit E) x) := by
  rcases h with ⟨k, rfl⟩ | w
  · refine Or.inr (Or.inr (Or.inl ⟨k, "open", [], rfl, Or.inl rfl, by simp, fun k' tag l' e => ?_⟩))
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₂
    subst e₂
    exact ⟨fun h => by simp at h, fun _ ne => absurd (list_eq_nil.mp e₃.symm) ne⟩
  rcases w.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨hh, lit, c, u, d, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl (leafT_of_ok (Bdd.leaf_iff.mp w))))
  · exact Or.inr (Or.inr (Or.inr ⟨hh, lit, c, u, d, rfl, w⟩))

theorem via_tuple_union {m : Nat} {x y : Term} (hx : TField E x) (hy : TField E y)
    (e : Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = Elixir.Module.Types.Descr.«tuple_union/2» x y) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v || denTF E den y v) := by
  obtain ⟨r, hr, fr, sr⟩ := tuple_union_field hx hy
  exact ⟨r, by rw [e, hr], fr, sr⟩

/-- Optimized unions of tuple types of element types hold the tuples of either. -/
theorem opt_tuple_union_sem (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {x y : Term} (hx : TField E x)
    (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v || denTF E den y v) := by
  have leafNode : ∀ {a b : Term}, LeafT E a → Bdd (TLit E) b → ∃ r,
      Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m) b a = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (denTF E den b v || denTF E den a v) := by
    intro a b ha wb
    obtain ⟨r, hr, fr, sr⟩ := union_leaf_sem ef (m := m) hm _ b a (Nat.le_refl _) wb ha
    exact ⟨r, hr, fr, fun v => by rw [sr v, denTF_bdd wb, ha.val]⟩
  rcases hx.shape with rfl | rfl | ⟨k₁, t₁, l₁, rfl, g₁, h₁, key₁⟩ | ⟨h₁, a₁, c₁, u₁, d₁, rfl, w₁⟩ <;>
    rcases hy.shape with rfl | rfl | ⟨k₂, t₂, l₂, rfl, g₂, h₂, key₂⟩ | ⟨h₂, a₂, c₂, u₂, d₂, rfl, w₂⟩
  all_goals first
    | exact via_tuple_union hx hy (by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; rfl)
    | (apply via_tuple_union hx hy
       unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
       simp only [leaf_guard, node_ne3, ite_false]
       done)
    | skip
  · by_cases same : compareExact (fuel (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) (.tuple #[.integer k₁, .atom t₁, Term.list l₁])) (.tuple #[.integer k₂, .atom t₂, Term.list l₂])
        (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) = .eq
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp only [leaf_guard, ite_eq_left same]; rfl,
        hx, fun v => by rw [denTF_exact hx hy same, Bool.or_self]⟩
    have lx : LeafT E (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) := ⟨k₁, t₁, l₁, rfl, g₁, h₁, key₁⟩
    have ly : LeafT E (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) := ⟨k₂, t₂, l₂, rfl, g₂, h₂, key₂⟩
    have e₁ := fun v => vT_lit ef (v := v) (k := k₁) g₁ h₁
    have e₂ := fun v => vT_lit ef (v := v) (k := k₂) g₂ h₂
    obtain ⟨res, run, sok⟩ := strategy_sem ef hm t₁ t₂ g₁ g₂ l₁ l₂ h₁ h₂
    have form := strategy_form ef hm t₁ t₂ g₁ g₂ l₁ l₂ h₁ h₂ run
    rcases form with rfl | ⟨j, d₁, d₂, rfl⟩ | rfl | rfl | rfl
    · exact absurd rfl sok.1
    · obtain ⟨rfl, a₁, b₁, a₂, b₂, rfl, rfl, rfl, pa, pb, nd⟩ := sok.2.1 _ _ _ rfl
      have hd₁ : E d₁ := h₁ d₁ (by simp)
      have hd₂ : E d₂ := h₂ d₂ (by simp)
      obtain ⟨u₀, hu₀, ru₀, su₀, -⟩ := ef.union hd₁ hd₂
      obtain ⟨f, rf, out⟩ := ef.fuse 3 hd₁ hd₂ nd hm
      -- the fused element, or the union when fusing fails
      obtain ⟨u, hu, su, hcase⟩ : ∃ u, E u ∧ (∀ v, den u v ↔ den d₁ v ∨ den d₂ v) ∧
          ((f = .atom "nil" ∧ u = u₀) ∨
            (u = f ∧ Term.compareExact (Term.fuel f (.atom "false")) f (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel f (.atom "nil")) f (.atom "nil") ≠ .eq)) := by
        rcases out with rfl | ⟨hf, sf⟩
        · exact ⟨u₀, hu₀, su₀, Or.inl ⟨rfl, rfl⟩⟩
        · have nf : Term.compareExact (Term.fuel f (.atom "false")) f (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel f (.atom "nil")) f (.atom "nil") ≠ .eq := by
            rcases ef.static hf with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩ <;> simp
          exact ⟨f, hf, sf, Or.inr ⟨rfl, nf⟩⟩
      have elems : ∀ e ∈ a₁ ++ u :: b₁, E e := by
        intro e me
        simp only [List.mem_append, List.mem_cons] at me
        rcases me with me | rfl | me
        · exact h₁ e (by simp [me])
        · exact hu
        · exact h₁ e (by simp [me])
      have rep := replace_list (a₁ ++ d₁ :: b₁) a₁.length u (by simp)
      rw [set_mid] at rep
      obtain ⟨k, hk, key⟩ := leaf_new_key t₁ g₁ (a₁ ++ u :: b₁)
      have hres : LeafT E (Term.tuple #[Term.integer k, Term.atom t₁, Term.list (a₁ ++ u :: b₁)]) := ⟨k, t₁, _, rfl, g₁, elems, key⟩
      refine ⟨_, ?_, hres.field, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
        simp only [run, Lynx.Except.ok_bind]
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, nf⟩
        · simp [isMember, rf, ru₀ m hm, rep, hk, Erlang.erlang.«=:=/2», same]
        · simp [isMember, rf, nf.1, nf.2, rep, hk, Erlang.erlang.«=:=/2», same]
      · apply Bool.eq_iff_iff.mpr
        rw [hres.val, lx.val, ly.val, vT_lit ef g₁ elems, Bool.or_eq_true, e₁ v, e₂ v]
        exact union_one_index pa pb su v
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp [Erlang.erlang.«=:=/2», same, run], ly.field, fun v => ?_⟩
      rw [lx.val, ly.val]
      by_cases hx' : valT E den v (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) = Bool.true
      · rw [hx', (e₂ v).mpr (sok.2.2.1 rfl v ((e₁ v).mp hx'))]; rfl
      · simp only [Bool.not_eq_true] at hx'; rw [hx']; rfl
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp [Erlang.erlang.«=:=/2», same, run], lx.field, fun v => ?_⟩
      rw [lx.val, ly.val]
      by_cases hy' : valT E den v (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) = Bool.true
      · rw [hy', (e₁ v).mpr (sok.2.2.2 rfl v ((e₂ v).mp hy'))]; rfl
      · simp only [Bool.not_eq_true] at hy'; rw [hy', Bool.or_false]
    · have o₁ : ¬(t₁ = "open" ∧ l₁ = []) := fun h => strategy_top_none (D m) t₁ t₂ g₁ g₂ l₁ l₂ (Or.inl h) run
      have o₂ : ¬(t₂ = "open" ∧ l₂ = []) := fun h => strategy_top_none (D m) t₁ t₂ g₁ g₂ l₁ l₂ (Or.inr h) run
      have notTop : ∀ {leaf : Term} {k : Int} {t : String} {l : List Term}, leaf = .tuple #[.integer k, .atom t, Term.list l] →
          ¬(t = "open" ∧ l = []) → LeafT E leaf → Bdd (TLit E) leaf := by
        intro leaf k t l e o hl
        rcases hl.field with ⟨k', e'⟩ | w
        · subst e
          obtain ⟨-, e₂, e₃⟩ := tuple3_inj e'
          simp only [Term.atom.injEq] at e₂
          exact absurd ⟨e₂, list_eq_nil.mp e₃⟩ o
        · exact w
      have w₁ := notTop rfl o₁ lx
      have w₂ := notTop rfl o₂ ly
      obtain ⟨r, hr, okr, semr⟩ := union_ok w₁ w₂
      refine ⟨r, ?_, Or.inr (okr _ w₁ w₂), fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, hr]
      · rw [denTF_bdd (okr _ w₁ w₂), denTF_bdd w₁, denTF_bdd w₂, semr _ (valT_resp v)]
  · obtain ⟨r, hr, fr, sr⟩ := leafNode ⟨k₁, t₁, l₁, rfl, g₁, h₁, key₁⟩ w₂
    refine ⟨r, ?_, fr, fun v => by rw [sr v, Bool.or_comm]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [leaf_guard, node_ne3, ite_false]
    exact hr
  · obtain ⟨r, hr, fr, sr⟩ := leafNode ⟨k₂, t₂, l₂, rfl, g₂, h₂, key₂⟩ w₁
    refine ⟨r, ?_, fr, sr⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only []
    exact hr

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized intersections of tuple types of element types on tuples of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Public emptiness checks of element types are exact. -/
theorem EF.empty_pub (ef : EF nd E V den tl K) {a : Term} (ha : E a) :
    ∃ b : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ ∀ v, ¬den a v) := by
  obtain ⟨b, run, ex⟩ := ef.empty [] ha
  have exact := ex (lh a + 1) (by omega) (safeN_nil _)
  rcases ef.static ha with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩
  · refine ⟨Bool.false, fun m _ => rfl, ?_⟩
    obtain ⟨v⟩ := ef.inhabited
    exact ⟨fun h => absurd h (by decide), fun h => absurd (ef.den_term v) (h v)⟩
  · exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm, exact⟩
  · exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm, exact⟩

theorem opt_tuple_funG (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) {a b : Term} (ha : E a) (hb : E b)
    (S : List (Term × Term)) :
    ∃ c, E c ∧ (∀ v, den c v ↔ den a v ∧ den b v) ∧
      Lynx.Dispatcher.pure (D (n + 2)) (optTupleIFun (.map S)) #[a, b] = .ok c := by
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S ha hb hn
  refine ⟨c, hc, sem, ?_⟩
  rw [optTupleIFun, Erlang.program.«Elixir.Module.Types.Descr:-opt_tuple_leaf_intersection/3-fun-0-/2».pure]
  simpa [Elixir.Module.Types.Descr.«-opt_tuple_leaf_intersection/3-fun-0-/3»] using run

/-- Element intersections that are never empty, or the `:empty` throw when one of them is. -/
theorem zip_ne_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) (S : List (Term × Term)) :
    ∀ (l₁ : List Term), (∀ e ∈ l₁, E e) → ∀ (l₂ : List Term), (∀ e ∈ l₂, E e) → ∀ acc : List Term,
      (∃ r : List Term, Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list l₁)
          (Term.list l₂) (Term.list acc) (optTupleIFun (Term.map S)) = .ok (Term.list (acc.reverse ++ r)) ∧
        (∀ e ∈ r, E e) ∧ r.length = max l₁.length l₂.length ∧
        ∀ v, InT den Bool.false r v ↔ InT den Bool.false l₁ v ∧ InT den Bool.false l₂ v) ∨
      (Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list l₁)
          (Term.list l₂) (Term.list acc) (optTupleIFun (.map S)) = .error (.throw (.atom "empty")) ∧
        ∀ v, InT den Bool.false l₁ v → InT den Bool.false l₂ v → False) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro _ l₂ h₂ acc
    refine Or.inl ⟨l₂, ?_, h₂, by simp, fun v => by simp [InT.open_nil]⟩
    unfold Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4»
    exact reverse_list acc l₂
  | cons x xs ih =>
    intro h₁ l₂ h₂ acc
    cases l₂ with
    | nil =>
      refine Or.inl ⟨x :: xs, ?_, h₁, by simp, fun v => by simp [InT.open_nil]⟩
      unfold Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4»
      exact reverse_list acc (x :: xs)
    | cons y ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      obtain ⟨e, he, sem, run⟩ := opt_tuple_funG ef hn hx hy S
      obtain ⟨b, runb', iffb⟩ := ef.empty_pub he
      have runb := runb' (n + 2) (by omega)
      have step : Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list (x :: xs))
          (Term.list (y :: ys)) (Term.list acc) (optTupleIFun (.map S)) =
          if b then .error (.throw (.atom "empty"))
          else Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4» (D (n + 2)) (Term.list xs) (Term.list ys)
            (Term.list (e :: acc)) (optTupleIFun (.map S)) := by
        rw [Elixir.Module.Types.Descr.«zip_non_empty_intersection!/4».eq_def]
        cases b <;> simp [Term.list, Elixir.Module.Types.Descr.«non_empty_intersection!/3», run, runb, boolAtom,
          isMember]
      cases b
      · rw [step]; simp only [Bool.false_eq_true, ite_false]
        rcases ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys (fun e me => h₂ e (List.mem_cons_of_mem _ me))
          (e :: acc) with ⟨r, runr, hr, len, semr⟩ | ⟨runr, empty⟩
        · refine Or.inl ⟨e :: r, by simpa using runr, fun e' me => ?_, by simp [len], fun v => ?_⟩
          · rcases List.mem_cons.mp me with rfl | me
            · exact he
            · exact hr e' me
          · cases v with
            | nil => simp [InT]
            | cons z v =>
              simp only [InT, semr v, sem z]
              exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
        · refine Or.inr ⟨runr, fun v i₁ i₂ => ?_⟩
          cases v with
          | nil => exact i₁
          | cons z v => exact empty v i₁.2 i₂.2
      · rw [step]
        refine Or.inr ⟨by simp, fun v i₁ i₂ => ?_⟩
        cases v with
        | nil => exact i₁
        | cons z v => exact (iffb.mp rfl) z ((sem z).mpr ⟨i₁.1, i₂.1⟩)

/-- Literal intersections of tuples of values: `:empty` when no tuple is in both, otherwise the tuples of both. -/
theorem tuple_lit_inter_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) {t₁ t₂ : String} (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") {l₁ l₂ : List Term} (h₁ : ∀ e ∈ l₁, E e) (h₂ : ∀ e ∈ l₂, E e)
    (S : List (Term × Term)) :
    (Elixir.Module.Types.Descr.«tuple_literal_intersection/5» (D (n + 2)) (.atom t₁) (Term.list l₁) (.atom t₂)
        (Term.list l₂) (optTupleIFun (.map S)) = .ok (.atom "empty") ∧
      ∀ v, InT den (t₁ == "closed") l₁ v → InT den (t₂ == "closed") l₂ v → False) ∨
    ∃ (t : String) (l : List Term), Elixir.Module.Types.Descr.«tuple_literal_intersection/5» (D (n + 2)) (.atom t₁)
        (Term.list l₁) (.atom t₂) (Term.list l₂) (optTupleIFun (.map S)) = .ok (.tuple #[.atom t, Term.list l]) ∧
      (t = "open" ↔ t₁ = "open" ∧ t₂ = "open") ∧ (t = "open" ∨ t = "closed") ∧ (∀ e ∈ l, E e) ∧
      l.length = max l₁.length l₂.length ∧ ¬Disj t₁ t₂ l₁.length l₂.length ∧
      ∀ v, InT den (t == "closed") l v ↔ InT den (t₁ == "closed") l₁ v ∧ InT den (t₂ == "closed") l₂ v := by
  obtain ⟨sv, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
  unfold Elixir.Module.Types.Descr.«tuple_literal_intersection/5»
  simp only [length_list, Lynx.Except.ok_bind, hv]
  by_cases d : Disj t₁ t₂ l₁.length l₂.length
  · left
    refine ⟨by rw [disj.mpr d]; rfl, fun w hw hlw => ?_⟩
    rw [InT.iff_open] at hw hlw
    rcases d with ⟨rfl, rfl, ne⟩ | ⟨rfl, rfl, lt⟩ | ⟨rfl, rfl, lt⟩
    · exact ne (by rw [← hw.2 rfl, hlw.2 rfl])
    · have := hlw.1.length_le; have := hw.2 rfl; omega
    · have := hw.1.length_le; have := hlw.2 rfl; omega
  have nv : sv ≠ .atom "disjoint" := fun e => d (disj.mp e)
  rcases zip_ne_sem ef hn S l₁ h₁ l₂ h₂ [] with ⟨r, zip, hr, len, semr⟩ | ⟨zip, empty⟩
  · right
    simp only [List.reverse_nil, List.nil_append] at zip
    let tag : String := if t₁ = "open" ∧ t₂ = "open" then "open" else "closed"
    refine ⟨tag, r, ?_, by simp only [tag]; split <;> simp_all, by simp only [tag]; split <;> simp, hr, len, d,
      fun w => ?_⟩
    · split
      · exact absurd rfl nv
      · simp only [Term.list] at zip
        by_cases o₁ : t₁ = "open" <;> by_cases o₂ : t₂ = "open" <;>
          simp [tag, o₁, o₂, Erlang.erlang.«==/2», Lynx.Except.andAlso, zip]
    rw [InT.iff_open, InT.iff_open (l := l₁), InT.iff_open (l := l₂), semr w]
    have nd : ¬Disj t₁ t₂ l₁.length l₂.length := d
    simp only [Disj, not_or, not_and] at nd
    rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> simp [tag, len] at nd ⊢
    all_goals first
      | (rw [Nat.max_eq_right nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩)
      | (rw [Nat.max_eq_left nd]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩)
      | (rw [nd, Nat.max_self]; exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b, c⟩, fun ⟨⟨a, c⟩, b, _⟩ => ⟨⟨a, b⟩, c⟩⟩)
  · left
    refine ⟨?_, fun w hw hlw => empty w (InT.iff_open.mp hw).1 (InT.iff_open.mp hlw).1⟩
    split
    · exact absurd rfl nv
    · simp [Term.list] at zip
      simp [zip, Lynx.Except.tryWith, Lynx.Exception.classTerm, Lynx.Exception.reason]

/-- `tuple_closed_subtype_of_open?/2` only answers true when every tuple of the closed literal is in the open one. -/
theorem tcso_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (cl l : List Term), (∀ e ∈ cl, E e) → (∀ e ∈ l, E e) →
    ∃ c : Bool, Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2» (D m) (Term.list cl) (Term.list l) =
        .ok (boolAtom c) ∧ (c = Bool.true → ∀ v, InT den Bool.true cl v → InT den Bool.false l v) := by
  intro cl
  induction cl with
  | nil =>
    intro l _ _
    cases l with
    | nil =>
      refine ⟨Bool.true, ?_, fun _ v _ => InT.open_nil v⟩
      rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def]; simp [boolAtom]
    | cons y ys =>
      refine ⟨Bool.false, ?_, fun h => by cases h⟩
      rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def]; simp [boolAtom]
  | cons x xs ih =>
    intro l h₁ h₂
    cases l with
    | nil =>
      refine ⟨Bool.true, ?_, fun _ v _ => InT.open_nil v⟩
      rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def]; simp [boolAtom]
    | cons y ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      obtain ⟨bs, hbs', sound'⟩ := ef.sub hx hy
      have hbs : Elixir.Module.Types.Descr.«subtype?/2» (D m) x y = .ok (boolAtom bs) := hbs' m hm
      obtain ⟨c, run, sound⟩ := ih ys (fun e me => h₁ e (List.mem_cons_of_mem _ me))
        (fun e me => h₂ e (List.mem_cons_of_mem _ me))
      refine ⟨bs && c, ?_, fun h v hv => ?_⟩
      · rw [Elixir.Module.Types.Descr.«tuple_closed_subtype_of_open?/2».eq_def, list_cons, list_cons]
        simp only
        rw [hbs, run, andAlso_bool]
      · simp only [Bool.and_eq_true] at h
        cases v with
        | nil => exact hv.elim
        | cons z v =>
          refine ⟨sound' h.1 z hv.1, sound h.2 v hv.2⟩

/-! Clauses of `opt_tuple_intersection/3`. -/

theorem opt_tuple_inter_top_eq {d : Dispatcher} {x S : Term} {k : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x (.tuple #[k, .atom "open", .nil]) S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  · exact (hx _ rfl).elim
  · rfl
  all_goals rename_i h
  all_goals first | exact (h _ rfl).elim | (exfalso; simp_all)

theorem opt_tuple_inter_plain_eq {d : Dispatcher} {x y S : Term} (tx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (ty : ∀ k, y ≠ .tuple #[k, .atom "open", .nil])
    (h3 : ∀ a b c a' b' c', x = .tuple #[a, b, c] → y = .tuple #[a', b', c'] → False)
    (h4 : ∀ k fo a b c u e, x = .tuple #[k, .atom "open", fo] → y = .tuple #[a, b, c, u, e] → False)
    (h5 : ∀ k fo a b c u e, y = .tuple #[k, .atom "open", fo] → x = .tuple #[a, b, c, u, e] → False) :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = Elixir.Module.Types.Descr.«tuple_intersection/2» x y := by
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := by
    rintro a b c rfl e
    obtain ⟨_, _, _, rfl, -⟩ := exact_tuple3 e
    exact h3 _ _ _ _ _ _ rfl rfl
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  · exact (tx _ rfl).elim
  · exact (ty _ rfl).elim
  · simp only [leaf_guard]
    split
    · rw [ite_eq_right (ne _ _ _ rfl)]
      split
      all_goals first
        | rfl
        | exact (h3 _ _ _ _ _ _ rfl rfl).elim
        | (exfalso; simp_all
           first
             | exact h4 _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
             | exact h5 _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl)
    · split
      all_goals first
        | rfl
        | exact (h3 _ _ _ _ _ _ rfl rfl).elim
        | exact (h4 _ _ _ _ _ _ _ rfl rfl).elim
        | exact (h5 _ _ _ _ _ _ _ rfl rfl).elim

/-- Exactly equal tuple leaves intersect to the first. -/
theorem opt_tuple_inter_same {d : Dispatcher} {S k a b y : Term} (nt : ¬IsTop (.tuple #[k, a, b]))
    (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d (.tuple #[k, a, b]) y S = .ok (.tuple #[k, a, b]) := by
  obtain ⟨a', b', c', rfl, e₁, e₂, e₃⟩ := exact_tuple3 e
  have ny : ∀ k', Term.tuple #[a', b', c'] ≠ .tuple #[k', .atom "open", .nil] := by
    intro k' h
    obtain ⟨-, rfl, rfl⟩ := tuple3_inj h
    have f₂ := Lynx.Term.compareExact_eq_symm e₂
    have f₃ := Lynx.Term.compareExact_eq_symm e₃
    simp only [compareExact_eq_atom, compareExact_eq_nil] at f₂ f₃
    subst f₂ f₃
    exact nt ⟨_, rfl⟩
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  · rename_i heq; exact absurd ⟨_, heq⟩ nt
  · rename_i h₁ h₂; first | exact (ny _ h₂).elim | exact (ny _ h₁).elim
  · simp only [leaf_guard]
    rw [ite_eq_left (by simpa using e)]
    rfl

theorem opt_tuple_inter_leaves {d : Dispatcher} {S : Term} {x y : Term} (hx : TupleOk E x)
    (hy : TupleOk E y) (ne : compareExact (fuel y x) y x ≠ .eq) :
    (Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "tuple_intersection") x y = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = Elixir.Module.Types.Descr.«tuple_intersection/2» x y) ∧
    (∀ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "tuple_intersection") x y = .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S =
        Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3» d x y S') := by
  obtain ⟨⟨k₁, t₁, l₁, rfl, -, -⟩, nt₁⟩ := hx
  obtain ⟨⟨k₂, t₂, l₂, rfl, -, -⟩, nt₂⟩ := hy
  constructor <;> intros <;>
  · unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
    split
    · rename_i heq; exact absurd ⟨_, heq⟩ nt₁
    · rename_i h₁ h₂; first | exact absurd ⟨_, h₁⟩ nt₂ | exact absurd ⟨_, h₂⟩ nt₂
    simp only [leaf_guard]
    rw [ite_eq_right (by simpa using ne)]
    simp_all

theorem opt_tuple_inter_push_l {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d (.tuple #[k, .atom "open", fo]) (.tuple #[h, lit, c, u, e]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function false "Elixir.Module.Types.Descr" "tuple_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

theorem opt_tuple_inter_push_r {d : Dispatcher} {S : Term} {k : Term} {fo : Term} (nt : fo ≠ .nil)
    {h lit c u e : Term} :
    Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo]) S =
      Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» d (.tuple #[h, lit, c, u, e]) (.tuple #[k, .atom "open", fo])
        (.function false "Elixir.Module.Types.Descr" "tuple_closed_subtype_of_open?" 2 #[]) := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»
  split
  all_goals first
    | rfl
    | (simp_all; done)
    | (simp only [leaf_guard, node_ne3, ite_false]
       first
         | rfl
         | (split <;> first | rfl | (simp_all; done)))

theorem tlit_closed_neg {k : Int} {cl : Term} (h : TLit E (.tuple #[.integer k, .atom "closed", cl])) : k < 0 := by
  obtain ⟨⟨⟨k', t, l, e, -, -⟩, -⟩, key⟩ := h
  obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
  simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
  subst e₁ e₂ e₃
  exact (key _ _ _ rfl).1 rfl

/-- Pushing an open literal below closed literals of negative keys keeps exactly the tuples of both. -/
theorem push_open (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {H : Int} (hH : 0 ≤ H) {l : List Term}
    (hL : TLit E (.tuple #[.integer H, .atom "open", Term.list l])) {b : Term} (wb : Bdd (TLit E) b) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_open_leaf_intersection/3» (D m) b (.tuple #[.integer H, .atom "open", Term.list l])
        (.function false "Elixir.Module.Types.Descr" "tuple_closed_subtype_of_open?" 2 #[]) = .ok r ∧
      TField E r ∧ ∀ v, denTF E den r v = (denTF E den b v && denTF E den (.tuple #[.integer H, .atom "open", Term.list l]) v) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  have hl₀ : ∀ e ∈ l, E e := tupleLit_elems hL.1.1
  obtain ⟨r, run, okr, semr⟩ := open_leaf_ok (Val := fun ρ => ∃ v, ρ = valT E den v) (fun ρ ⟨v, e⟩ => e ▸ valT_resp v)
    (ok := TLit E) (d := D (n + 1)) hL
    (fun k cl h => closed_lt_open' (tlit_closed_neg h) hH cl _)
    (fun k cl h => by
      have h₀ := h
      obtain ⟨⟨⟨k', tag, cls, e, -, -⟩, -⟩, -⟩ := h
      obtain ⟨-, -, e₂⟩ := tuple3_inj e
      subst e₂
      have hcl := tupleLit_elems h₀.1.1
      obtain ⟨c, hc, sound⟩ := tcso_val ef hn cls l hcl hl₀
      refine ⟨c, by
        rw [Erlang.program.«Elixir.Module.Types.Descr:tuple_closed_subtype_of_open?/2».pure (external := false)]
        exact hc, fun ct ρ ⟨v, hv⟩ hρ => ?_⟩
      subst hv
      exact (vT_lit ef (Or.inl rfl) hl₀).mpr (sound ct v ((vT_lit ef (Or.inr rfl) hcl).mp hρ)))
    (TLit E) b wb (fun _ h => h)
  have wr : Bdd (TLit E) r := okr (TLit E) (fun _ h => h) hL
  refine ⟨r, run, Or.inr wr, fun v => ?_⟩
  rw [denTF_bdd wr, semr _ ⟨v, rfl⟩, denTF_bdd wb, denTF_bdd (Bdd.leaf_iff.mpr hL), eval_leaf]

/-- Optimized intersections of tuple literals hold the tuples of both. -/
theorem opt_tuple_leaf_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n + 1) {x y : Term} (hx : TLit E x)
    (hy : TLit E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3» (D (n + 2)) x y (.map S) = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := by
  have hx₀ := hx
  have hy₀ := hy
  obtain ⟨⟨⟨k₁, t₁, l₁, rfl, g₁, h₁⟩, nt₁⟩, key₁⟩ := hx
  obtain ⟨⟨⟨k₂, t₂, l₂, rfl, g₂, h₂⟩, nt₂⟩, key₂⟩ := hy
  have wx : Bdd (TLit E) (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) := Bdd.leaf_iff.mpr hx₀
  have wy : Bdd (TLit E) (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) := Bdd.leaf_iff.mpr hy₀
  have dx : ∀ v, denTF E den (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) v = Bool.true ↔
      InT den (t₁ == "closed") l₁ v :=
    fun v => by rw [denTF_bdd wx, eval_leaf]; exact vT_lit ef g₁ h₁
  have dy : ∀ v, denTF E den (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) v = Bool.true ↔
      InT den (t₂ == "closed") l₂ v :=
    fun v => by rw [denTF_bdd wy, eval_leaf]; exact vT_lit ef g₂ h₂
  rcases tuple_lit_inter_val ef hn g₁ g₂ h₁ h₂ S with ⟨run, empty⟩ | ⟨t, l, run, iff, g, hl, len, nd, sem⟩
  · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
    · unfold Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3»
      simp only [optTupleIFun] at run
      simp [run]
    · rw [denTF_bdd Bdd.bot]
      cases e : denTF E den (.tuple #[.integer k₁, .atom t₁, Term.list l₁]) v
      · rfl
      · cases e' : denTF E den (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) v
        · rfl
        · exact (empty v ((dx v).mp e) ((dy v).mp e')).elim
  · obtain ⟨k, leaf, key⟩ := leaf_new_key t g l
    have okr : TLit E (.tuple #[.integer k, .atom t, Term.list l]) := by
      refine ⟨⟨⟨k, t, l, rfl, g, hl⟩, fun ⟨k', e⟩ => ?_⟩, key⟩
      obtain ⟨-, e₁, e₂⟩ := tuple3_inj e
      simp only [Term.atom.injEq] at e₁
      subst e₁
      obtain ⟨rfl, rfl⟩ := iff.mp rfl
      cases l with
      | cons _ _ => simp [Term.list] at e₂
      | nil =>
        cases l₁ with
        | cons a as => have := Nat.le_max_left (as.length + 1) l₂.length; simp at len; omega
        | nil => exact nt₁ ⟨_, rfl⟩
    have wr : Bdd (TLit E) (.tuple #[.integer k, .atom t, Term.list l]) := Bdd.leaf_iff.mpr okr
    refine ⟨_, ?_, Or.inr wr, fun v => ?_⟩
    · unfold Elixir.Module.Types.Descr.«opt_tuple_leaf_intersection/3»
      simp only [optTupleIFun] at run
      simp [run, leaf]
    · apply Bool.eq_iff_iff.mpr
      rw [denTF_bdd wr, eval_leaf, vT_lit ef g hl, sem v, Bool.and_eq_true, dx, dy]

theorem tlit_leaf {k : Int} {a b : Term} (h : TLit E (.tuple #[.integer k, a, b])) :
    ∃ (t : String) (l : List Term), a = .atom t ∧ b = Term.list l ∧ (t = "open" ∨ t = "closed") ∧
      (∀ e ∈ l, E e) ∧ (t = "open" → 0 ≤ k ∧ l ≠ []) := by
  obtain ⟨⟨⟨k', t, l, e, g, hl⟩, nt⟩, key⟩ := h
  obtain ⟨e₀, e₁, e₂⟩ := tuple3_inj e
  simp only [Term.integer.injEq] at e₀
  subst e₀ e₁ e₂
  have ne : t = "open" → l ≠ [] := fun o ne => nt ⟨_, by rw [o, ne]⟩
  exact ⟨t, l, rfl, rfl, g, hl, fun o => ⟨(key _ _ _ rfl).2 o (ne o), ne o⟩⟩

/-- Optimized intersections of tuple types hold the tuples of both. -/
theorem opt_tuple_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K + 2 ≤ m) {x y : Term} (fx : TField E x)
    (fy : TField E y) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) = .ok r ∧ TField E r ∧
      ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»; rfl, fy,
      fun v => by rw [denTF_top]; rfl⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨x, opt_tuple_inter_top_eq (not_top_of_ok wx tlit_not), Or.inr wx,
      fun v => by rw [denTF_top]; simp⟩
  have nx := not_top_of_ok wx tlit_not
  have ny := not_top_of_ok wy tlit_not
  have plain : Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) =
      Elixir.Module.Types.Descr.«tuple_intersection/2» x y →
      ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) = .ok r ∧ TField E r ∧
        ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := by
    intro e
    obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [e, tuple_intersection_bdd nx ny, hr], Or.inr wr, fun v => ?_⟩
    rw [denTF_bdd wr, denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]
  have plainEq := fun h3 h4 h5 => plain (opt_tuple_inter_plain_eq (d := D m) (S := .map S) nx ny h3 h4 h5)
  have xAtom : ∀ {s : String}, x = .atom s → ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) =
      .ok r ∧ TField E r ∧ ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ e _ => by cases e) (fun _ _ _ _ _ _ _ e _ => by cases e)
      (fun _ _ _ _ _ _ _ _ e => by cases e)
  have yAtom : ∀ {s : String}, y = .atom s →
      ∃ r, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» (D m) x y (.map S) =
      .ok r ∧ TField E r ∧ ∀ v, denTF E den r v = (denTF E den x v && denTF E den y v) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ _ e => by cases e) (fun _ _ _ _ _ _ _ _ e => by cases e)
      (fun _ _ _ _ _ _ _ e _ => by cases e)
  rcases wx.shape with ex | ex | ⟨k₁, a₁, b₁, rfl⟩ | ⟨h₁, lit₁, c₁, u₁, d₁, rfl⟩
  · exact xAtom ex
  · exact xAtom ex
  all_goals rcases wy.shape with ey | ey | ⟨k₂, a₂, b₂, rfl⟩ | ⟨h₂, lit₂, c₂, u₂, d₂, rfl⟩
  all_goals try exact yAtom ey
  -- two leaves
  · have ox := (Bdd.leaf_iff).mp wx
    have oy := (Bdd.leaf_iff).mp wy
    by_cases same : compareExact (fuel (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁])) (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁]) = .eq
    · exact ⟨_, opt_tuple_inter_same ox.1.2 same, Or.inr wx,
        fun v => by rw [denTF_exact (Or.inr wx) (Or.inr wy) same, Bool.and_self]⟩
    rcases opt_bdd_seen_map S (.atom "tuple_intersection") (.tuple #[.integer k₁, a₁, b₁])
      (.tuple #[.integer k₂, a₂, b₂]) with seen | ⟨S', okS⟩
    · exact plain ((opt_tuple_inter_leaves ox.1 oy.1 same).1 seen)
    · obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      obtain ⟨n', rfl, hn'⟩ := succ_of_le hn
      obtain ⟨r, run, fr, sr⟩ := opt_tuple_leaf_val ef (n := n') (by omega) ox oy S'
      exact ⟨r, by rw [(opt_tuple_inter_leaves ox.1 oy.1 same).2 _ okS, run], fr, sr⟩
  -- a leaf and a node
  · obtain ⟨t, l, rfl, rfl, g, -, op⟩ := tlit_leaf ((Bdd.leaf_iff).mp wx)
    rcases g with rfl | rfl
    · obtain ⟨hk, ne⟩ := op rfl
      obtain ⟨r, hr, fr, sr⟩ := push_open ef (m := m) (by omega) hk ((Bdd.leaf_iff).mp wx) wy
      refine ⟨r, ?_, fr, fun v => by rw [sr v, Bool.and_comm]⟩
      rw [opt_tuple_inter_push_l (by cases l <;> simp_all [Term.list])]
      exact hr
    · exact plainEq (fun _ _ _ _ _ _ _ e => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
        (fun _ _ _ _ _ _ _ _ e => by simp at e)
  -- a node and a leaf
  · obtain ⟨t, l, rfl, rfl, g, -, op⟩ := tlit_leaf ((Bdd.leaf_iff).mp wy)
    rcases g with rfl | rfl
    · obtain ⟨hk, ne⟩ := op rfl
      obtain ⟨r, hr, fr, sr⟩ := push_open ef (m := m) (by omega) hk ((Bdd.leaf_iff).mp wy) wx
      refine ⟨r, ?_, fr, sr⟩
      rw [opt_tuple_inter_push_r (by cases l <;> simp_all [Term.list])]
      exact hr
    · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
        (fun _ _ _ _ _ _ _ e _ => by simp at e)
  -- two nodes
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun _ _ _ _ _ _ _ e _ => by simp at e)

end Elixir.STTDescrProofsTest.Nest
