module

public import Erlang.program

@[expose] public section

-- Valid types hold a non-empty bitmap and atom types of version 2 sets.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-! Valid types: every field is a non-empty bitmap or an atom type. -/

/-- Removing a key's bindings, as `maps:remove/2` filters them, leaves the bindings of other keys. -/
theorem mapLookup_remove (entries : List (Term × Term)) (key query : Term) :
    mapLookup (entries.filter fun entry => !decide (compareExact (fuel key entry.1) key entry.1 = .eq)) query =
      if compareExact (fuel query key) query key = .eq then none else mapLookup entries query :=
  mapLookup_filter entries key query

/-- `min/2` on integers. -/
@[simp] theorem min_integers (a b : Int) :
    Erlang.erlang.«min/2» (.integer a) (.integer b) = .ok (.integer (min a b)) := by
  simp only [Erlang.erlang.«min/2», compare_integers]
  by_cases h : a ≤ b
  · have : (Ord.compare a b).isLE = Bool.true := Int.isLE_compare.mpr h
    simp [this, Int.min_def, h]
  · have : (Ord.compare a b).isLE = Bool.false := by
      cases e : (Ord.compare a b).isLE
      · rfl
      · exact absurd (Int.isLE_compare.mp e) h
    simp [this, Int.min_def, h]

/-- Atom types are unions (true) or negations (false) of version 2 sets of atoms. -/
abbrev AtomField (w : Term) : Prop :=
  ∃ (pos : Bool) (S : List (Term × Term)),
    w = .tuple #[.atom (if pos then "union" else "negation"), .map S] ∧
      Erlang.sets.elements? (.map S) = some S

/-- What `valid?/1` checks of a type. -/
structure Valid (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom"
  bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
  atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
  atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []

/-- Atom sets hold [] for each element, so they are version 2 sets. -/
theorem atom_keys_set (S : List (Term × Term))
    (atoms : «atom_keys?/1» (Term.list ((mapEntries S).map fun e => .tuple #[e.1, e.2])) =
      .ok Term.true) : Erlang.sets.elements? (.map S) = some S := by
  have empty : ∀ es : List (Term × Term),
      «atom_keys?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true →
      es.all (fun entry => entry.2 matches .nil) := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons e rest ih =>
      intro valid
      obtain ⟨k₀, w₀⟩ := e
      rw [«atom_keys?/1».eq_def] at valid
      split at valid
      · rename_i atom tail heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        simp [ih valid.2]
      · rename_i heq; simp at heq
      · simp at valid
  simp only [Erlang.sets.elements?]
  exact ite_eq_left (empty _ atoms)

/-- Every field of a valid type is a bitmap or an atom field. -/
theorem valid_fields (es : List (Term × Term))
    (valid : «valid_fields?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
    ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    have head : ((k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
        (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ [])) ∧
        «valid_fields?/1» (Term.list (rest.map fun e => .tuple #[e.1, e.2])) = .ok Term.true := by
      rw [«valid_fields?/1».eq_def] at valid
      split at valid
      · rename_i bits fields heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        cases w <;> simp [Erlang.erlang.«is_integer/1»] at valid
        rename_i n
        obtain ⟨⟨low, high⟩, tail⟩ := valid
        exact ⟨Or.inl ⟨rfl, n.toNat, by rw [Int.toNat_of_nonneg (by omega)], by omega, by omega⟩, tail⟩
      · rename_i set fields heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        cases set <;> simp [«atoms?/1»] at valid
        rename_i S
        refine ⟨Or.inr ⟨rfl, ⟨true, S, rfl, atom_keys_set S valid.1.1⟩, fun S' e => ?_⟩, valid.2⟩
        simp at e
        subst e
        rintro rfl
        simp [Erlang.erlang.«map_size/1»] at valid
      · rename_i set fields heq
        simp at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        simp [Lynx.Except.andAlso_eq_true] at valid
        cases set <;> simp [«atoms?/1»] at valid
        rename_i S
        exact ⟨Or.inr ⟨rfl, ⟨false, S, rfl, atom_keys_set S valid.1⟩, fun S' e => by simp at e⟩, valid.2⟩
      · rename_i heq
        simp at heq
      · simp at valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.1
    · exact ih head.2 p member

theorem lookup_found (E : List (Term × Term)) (q w : Term) (lookup : mapLookup E q = some w) :
    ∃ p ∈ E, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w := by
  simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at lookup
  obtain ⟨p, hp, rfl⟩ := lookup
  exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, rfl⟩

theorem valid_of (X : List (Term × Term)) (valid : «valid?/1» (.map X) = .ok Term.true) : Valid X := by
  simp only [«valid?/1», Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at valid
  have each := valid_fields (mapEntries X) valid
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  refine ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?_⟩
  · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
    obtain ⟨p, mp, qp, -⟩ := entry q w lookup
    rcases each p mp with ⟨key, -⟩ | ⟨key, -⟩ <;> rw [key] at qp <;> simp at qp <;> simp [qp]
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨key, field⟩ | ⟨key, -⟩
    · exact field
    · rw [key] at qp; simp at qp
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨key, -⟩ | ⟨key, field, -⟩
    · rw [key] at qp; simp at qp
    · exact field
  · obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
    rcases each p mp with ⟨key, -⟩ | ⟨key, -, union⟩
    · rw [key] at qp; simp at qp
    · exact union S e

theorem valid_map (descr : Term) (valid : «valid?/1» descr = .ok Term.true) :
    ∃ X, descr = .map X ∧ Valid X := by
  cases descr <;> simp [«valid?/1»] at valid
  exact ⟨_, rfl, valid_of _ (by simpa [«valid?/1»] using valid)⟩

end Elixir.STTDescrProofsTest

-- Unions merge fields with maps:merge_with/3.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-! Map fields. -/

/-- Atom keys are found exactly. -/
theorem find_atom (X : List (Term × Term)) (name : String) :
    (mapEntries X).find? (fun p => decide (compareExact (fuel (.atom name) p.1) (.atom name) p.1 = .eq)) =
      (mapLookup X (.atom name)).map fun v => (.atom name, v) := by
  rw [← mapLookup_mapEntries]
  simp only [mapLookup, equalExact_eq_decide]
  cases hit : (mapEntries X).find? (fun p => decide (compareExact (fuel (.atom name) p.1) (.atom name) p.1 = .eq)) with
  | none => rfl
  | some p =>
    have same : compareExact (fuel (.atom name) p.1) (.atom name) p.1 = .eq := by simpa using List.find?_some hit
    have key : p.1 = .atom name := (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm same)
    obtain ⟨k₀, v₀⟩ := p
    simp only at key
    subst key
    rfl

/-! Unions. -/

/-- The union of two atom types holds the atoms of either. -/
theorem atom_union (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
    (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
    (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
    ∃ (p : Bool) (E : List (Term × Term)),
      Elixir.Module.Types.Descr.«atom_union/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
        .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
      Erlang.sets.elements? (.map E) = some E ∧
      ∀ q, (p == (mapLookup E q).isSome) =
        ((p₁ == (mapLookup S₁ q).isSome) || (p₂ == (mapLookup S₂ q).isSome)) := by
  cases p₁ <;> cases p₂
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
    refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
    refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
    refine ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
    refine ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_union/2», hE], setE, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl

end Elixir.STTDescrProofsTest

-- Intersections intersect fields with maps:intersect_with/3 and drop empty ones.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-! Intersections. -/

/-- Unions of atoms are dropped when empty. -/
theorem union_or_empty (E : List (Term × Term)) :
    (∃ s : Nat, s ≠ 0 ∧ Erlang.sets.«size/1» (.map E) = .ok (.integer s)) ∨
      (Erlang.sets.«size/1» (.map E) = .ok (.integer 0) ∧ ∀ q, mapLookup E q = none) := by
  cases h : ((E.map Prod.fst).eraseDupsBy (fun a b => decide (compareExact (fuel a b) a b = .eq))).length with
  | zero =>
    have empty : Erlang.sets.«size/1» (.map E) = .ok (.integer 0) := by simp [Erlang.sets.«size/1», h]
    exact Or.inr ⟨empty, fun q => Erlang.sets.size_empty E q empty⟩
  | succ s => exact Or.inl ⟨s + 1, by omega, by simp [Erlang.sets.«size/1», h]⟩

/-- The intersection of two atom types holds the atoms of both, and is `0` when empty. -/
theorem atom_intersection (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
    (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
    (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
    (∃ (p : Bool) (E : List (Term × Term)),
      Elixir.Module.Types.Descr.«atom_intersection/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
        .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
      Erlang.sets.elements? (.map E) = some E ∧
      -- Intersections are unions unless both types are negations, and are not empty.
      p = (p₁ || p₂) ∧ (p = Bool.true → E ≠ []) ∧
      ∀ q, (p == (mapLookup E q).isSome) =
        ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome))) ∨
    (Elixir.Module.Types.Descr.«atom_intersection/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .ok (.integer 0) ∧
      ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) := by
  cases p₁ <;> cases p₂
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
    refine Or.inl ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE,
      Erlang.erlang.«==/2»], setE, rfl, fun negated => Bool.noConfusion negated, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_intersection/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp

/-- The intersection keeps the fields that are neither `0` nor `bdd_bot`. -/
def kept (entry : Term × Term) : Bool :=
  !decide (compareExact (fuel entry.2 (.integer 0)) entry.2 (.integer 0) = .eq) &&
    !decide (compareExact (fuel entry.2 (.atom "bdd_bot")) entry.2 (.atom "bdd_bot") = .eq)

theorem keep_field (key value : Term) :
    Elixir.Module.Types.Descr.«-symmetrical_intersection/3-fun-0-/2» key value =
      .ok (if kept (key, value) then Term.true else Term.false) := by
  by_cases zero : compareExact (fuel value (.integer 0)) value (.integer 0) = .eq <;>
    by_cases bot : compareExact (fuel value (.atom "bdd_bot")) value (.atom "bdd_bot") = .eq <;>
    simp [Elixir.Module.Types.Descr.«-symmetrical_intersection/3-fun-0-/2», kept, Erlang.erlang.«=:=/2»,
      Erlang.erlang.«=/=/2», zero, bot, Term.true, Term.false]

end Elixir.STTDescrProofsTest

-- Differences fold over the fields of the right type and drop empty ones.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-! Differences. -/

/-- The difference updates the fields of the left type that the right type also has,
dropping them when they become `0` or `bdd_bot`. -/
def differenceStep (g : Term → Term → Term → Term) (acc : List (Term × Term)) (entry : Term × Term) :
    List (Term × Term) :=
  match mapLookup acc entry.1 with
  | some v₁ =>
    if kept (entry.1, g entry.1 v₁ entry.2) then (entry.1, g entry.1 v₁ entry.2) :: acc
    else acc.filter fun e => !decide (compareExact (fuel entry.1 e.1) entry.1 e.1 = .eq)
  | none => acc

theorem member_dropped (key w : Term) :
    isMember w [.integer 0, .atom "bdd_bot"] = if kept (key, w) then .atom "false" else .atom "true" := by
  by_cases zero : compareExact (fuel w (.integer 0)) w (.integer 0) = .eq <;>
    by_cases bot : compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") = .eq <;>
    simp [isMember, kept, zero, bot]

theorem difference_step (depth : Nat) (fn : Term) (g : Term → Term → Term → Term) (acc : List (Term × Term))
    (key v₂ : Term)
    (calls : ∀ v₁, mapLookup acc key = some v₁ →
      Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[key, v₁, v₂] =
        .ok (g key v₁ v₂)) :
    Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        fn key v₂ (.map acc) = .ok (.map (differenceStep g acc (key, v₂))) := by
  unfold Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4»
  cases found : mapLookup acc key with
  | none => simp [getMapKeys_single, found, differenceStep]
  | some v₁ =>
    simp only [getMapKeys_single, found, Option.toList_some,
      calls v₁ found, Lynx.Except.ok_bind, member_dropped key, differenceStep]
    obtain ⟨e, member, same⟩ := (mapLookup_isSome acc key).mp (by simp [found])
    by_cases keep : kept (key, g key v₁ v₂) <;> simp [keep, Erlang.erlang.«is_map/1», Erlang.maps.«update/3»,
      Erlang.maps.«remove/2»]
    exact ⟨e.1, ⟨e.2, member⟩, same⟩

theorem step_other (g : Term → Term → Term → Term) (acc : List (Term × Term)) (e : Term × Term) (q : Term)
    (other : compareExact (fuel q e.1) q e.1 ≠ .eq) : mapLookup (differenceStep g acc e) q = mapLookup acc q := by
  unfold differenceStep
  cases mapLookup acc e.1 with
  | none => rfl
  | some v₁ =>
    by_cases keep : kept (e.1, g e.1 v₁ e.2)
    · simp [keep, mapLookup, other]
    · simp only [keep, Bool.false_eq_true, ite_false]
      rw [mapLookup_remove]
      simp [other]

theorem step_same (g : Term → Term → Term → Term) (acc : List (Term × Term)) (e : Term × Term) (q : Term)
    (same : compareExact (fuel q e.1) q e.1 = .eq) :
    mapLookup (differenceStep g acc e) q = (mapLookup acc e.1).bind fun v₁ =>
      if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none := by
  unfold differenceStep
  cases found : mapLookup acc e.1 with
  | none => simp only [Option.bind_none]; rw [mapLookup_congr same, found]
  | some v₁ =>
    by_cases keep : kept (e.1, g e.1 v₁ e.2)
    · simp [keep, mapLookup, same]
    · simp only [keep, Bool.false_eq_true, ite_false, Option.bind_some]
      rw [mapLookup_remove]
      simp [same]

/-- Folding the difference over the entries of the right type. -/
theorem difference_fold (depth : Nat) (fn : Term) (g : Term → Term → Term → Term) (es acc : List (Term × Term))
    (distinct : es.Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq))
    (calls : ∀ e ∈ es, ∀ v₁, mapLookup acc e.1 = some v₁ →
      Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[e.1, v₁, e.2] =
        .ok (g e.1 v₁ e.2)) :
    ∃ M, es.foldlM (fun acc entry =>
        (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
          (.function false "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3
          #[fn]) #[entry.1, entry.2, acc] : Except Exception Term))
        (.map acc) = .ok (.map M) ∧
      (∀ q, mapLookup M q =
        match es.find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => (mapLookup acc e.1).bind fun v₁ =>
            if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else none
        | none => mapLookup acc q) ∧ M = es.foldl (differenceStep g) acc := by
  induction es generalizing acc with
  | nil => exact ⟨acc, rfl, fun q => rfl, rfl⟩
  | cons e rest ih =>
    have apart := List.pairwise_cons.mp distinct
    have step : (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
        (.function false "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3
          #[fn]) #[e.1, e.2, .map acc] : Except Exception Term) =
        .ok (.map (differenceStep g acc e)) := by
      rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-dynamic_difference/3-fun-0-/3».pure,
        difference_step depth fn g acc e.1 e.2 (calls e (List.mem_cons_self ..))]
    obtain ⟨M, run, look, explicit⟩ := ih (differenceStep g acc e) apart.2 (by
      intro e' member v₁ found
      rw [step_other g acc e e'.1 (fun same => apart.1 e' member (Lynx.Term.compareExact_eq_symm same))] at found
      exact calls e' (List.mem_cons_of_mem _ member) v₁ found)
    refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_,
      by rw [explicit]; rfl⟩
    rw [look q]
    by_cases same : compareExact (fuel q e.1) q e.1 = .eq
    · have absent : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) = none := by
        rw [List.find?_eq_none]
        intro p member hit
        exact apart.1 p member
          (Lynx.Term.compareExact_eq_trans (Lynx.Term.compareExact_eq_symm same) (of_decide_eq_true hit))
      simp only [absent, List.find?_cons, same, decide_true]
      exact step_same g acc e q same
    · simp only [List.find?_cons, same, decide_false]
      cases hit : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) with
      | none => exact step_other g acc e q same
      | some e' =>
        have qe' : compareExact (fuel q e'.1) q e'.1 = .eq := by simpa using List.find?_some hit
        have other : compareExact (fuel e'.1 e.1) e'.1 e.1 ≠ .eq := fun same' =>
          same (Lynx.Term.compareExact_eq_trans qe' same')
        simp only
        rw [step_other g acc e e'.1 other]

/-! Bitmap differences remove the bits of the right bitmap. -/

theorem add_eq_or (x y : Nat) (disjoint : x &&& y = 0) : x + y = x ||| y := by
  let w := x + y + 1
  have small (n : Nat) (h : n ≤ x + y) : n < 2 ^ w :=
    Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega))
  have bv : BitVec.ofNat w x &&& BitVec.ofNat w y = 0#w := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (small x (by omega)), Nat.mod_eq_of_lt (small y (by omega)), disjoint]
  have := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ bv)
  simp only [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (small x (by omega)), Nat.mod_eq_of_lt (small y (by omega)),
    Nat.mod_eq_of_lt (small (x + y) (by omega))] at this
  exact this

theorem testBit_sub_and (a b i : Nat) :
    (a - (a &&& b)).testBit i = (a.testBit i && !b.testBit i) := by
  have disjoint : (a ^^^ (a &&& b)) &&& (a &&& b) = 0 := Nat.eq_of_testBit_eq fun j => by
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases a.testBit j <;> cases b.testBit j <;> rfl
  have whole : (a ^^^ (a &&& b)) ||| (a &&& b) = a := Nat.eq_of_testBit_eq fun j => by
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
    cases a.testBit j <;> cases b.testBit j <;> rfl
  have split := add_eq_or _ _ disjoint
  rw [whole] at split
  rw [show a - (a &&& b) = a ^^^ (a &&& b) by omega]
  simp only [Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

/-- The difference of two atom types holds the atoms of the first only, and is `0` when empty. -/
theorem atom_difference (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term))
    (set₁ : Erlang.sets.elements? (.map S₁) = some S₁)
    (set₂ : Erlang.sets.elements? (.map S₂) = some S₂) :
    (∃ (p : Bool) (E : List (Term × Term)),
      Elixir.Module.Types.Descr.«atom_difference/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) =
        .ok (.tuple #[.atom (if p then "union" else "negation"), .map E]) ∧
      Erlang.sets.elements? (.map E) = some E ∧
      -- Differences are unions unless a negation removes a union.
      p = (p₁ || !p₂) ∧ (p = Bool.true → E ≠ []) ∧
      ∀ q, (p == (mapLookup E q).isSome) =
        ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome))) ∨
    (Elixir.Module.Types.Descr.«atom_difference/2»
          (.tuple #[.atom (if p₁ then "union" else "negation"), .map S₁])
          (.tuple #[.atom (if p₂ then "union" else "negation"), .map S₂]) = .ok (.integer 0) ∧
      ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && !(p₂ == (mapLookup S₂ q).isSome)) = Bool.false) := by
  cases p₁ <;> cases p₂
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₂ set₁
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ set₁ set₂
    refine Or.inl ⟨false, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE,
      Erlang.erlang.«==/2»], setE, rfl, fun negated => Bool.noConfusion negated, fun q => ?_⟩
    rw [m]
    cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.intersection_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set₁ set₂
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine Or.inl ⟨true, E, by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2», nonzero], setE, rfl, fun _ nil => by
        subst nil; simp [Erlang.sets.«size/1»] at size; omega, fun q => ?_⟩
      rw [m]
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> rfl
    · refine Or.inr ⟨by simp [Elixir.Module.Types.Descr.«atom_difference/2», hE, size,
        Erlang.erlang.«==/2»], fun q => ?_⟩
      have := m q
      rw [empty q] at this
      revert this
      cases (mapLookup S₁ q).isSome <;> cases (mapLookup S₂ q).isSome <;> simp

theorem unfold_map (d : Dispatcher) (entries : List (Term × Term)) :
    Elixir.Module.Types.Descr.«unfold/1» d (.map entries) = .ok (.map entries) := by
  rw [Elixir.Module.Types.Descr.«unfold/1».eq_def]; rfl

theorem static_map {X : List (Term × Term)} (static : mapLookup X (.atom "dynamic") = none) :
    Erlang.erlang.«is_map_key/2» (.atom "dynamic") (.map X) = .ok (.atom "false") := by
  have absent : X.any (fun entry => decide (compareExact (fuel (.atom "dynamic") entry.1) (.atom "dynamic") entry.1 = .eq)) = Bool.false := by
    rw [Bool.eq_false_iff]
    intro present
    obtain ⟨entry, member, same⟩ := List.any_eq_true.mp present
    have := (mapLookup_isSome X (.atom "dynamic")).mpr ⟨entry, member, by simpa using same⟩
    rw [static] at this
    cases this
  simp [Erlang.erlang.«is_map_key/2», absent, Term.false]

end Elixir.STTDescrProofsTest

-- The empty type is the empty map, and intersecting with it empties a type.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-- Maps without visible keys hold no entries. -/
theorem nil_of_lookup_none (entries : List (Term × Term))
    (none : ∀ q, mapLookup entries q = Option.none) : entries = [] := by
  cases entries with
  | nil => rfl
  | cons entry rest =>
    have := none entry.1
    simp [mapLookup] at this

/-- Intersecting a map of fields with the empty type keeps no field. -/
theorem symmetrical_none (d : Dispatcher) (X : List (Term × Term)) :
    Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map X) (.map [])
      (.function false "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) = .ok (.map []) := by
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup d false "Elixir.Module.Types.Descr"
    "bare_intersection" #[] X [] (fun _ _ _ => .nil) (by intro e _ y hy; simp [mapLookup] at hy)
  obtain rfl : I = [] := nil_of_lookup_none I fun q => by
    rw [lookI]
    cases (mapEntries X).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) <;> simp [mapLookup]
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup d false "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] [] kept (by intro e member; simp at member)
  obtain rfl : out = [] := nil_of_lookup_none out fun q => by rw [lookO]; simp
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [runI, runO]

/-- The intersection of a static type with the empty type is empty, whatever its fields hold. -/
theorem intersection_none_static (depth : Nat) (X : List (Term × Term))
    (static : mapLookup X (.atom "dynamic") = Option.none) :
    Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map X) (.map []) = .ok (.map []) := by
  have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, static, absent, symmetrical_none]

/-- The intersection of a gradual type with the empty type is empty, when its dynamic
part is the top type or a map of fields. -/
theorem intersection_none_dynamic (depth : Nat) (X : List (Term × Term)) (Dy : Term)
    (dynamic : mapLookup X (.atom "dynamic") = some Dy)
    (inner : Dy = .atom "term" ∨ ∃ Y, Dy = .map Y) :
    Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map X) (.map []) = .ok (.map []) := by
  have part : Elixir.Module.Types.Descr.«bare_intersection/3»
      (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom "dynamic") Dy (.map []) =
        .ok (.integer 0) := by
    simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]
    unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»
    rcases inner with rfl | ⟨Y, rfl⟩
    · simp [Erlang.erlang.«==/2»]
    · simp [symmetrical_none, Erlang.erlang.«==/2»]
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) false "Elixir.Module.Types.Descr"
    "bare_intersection" #[] X [(.atom "dynamic", .map [])] (fun _ _ _ => .integer 0) (by
      intro e me y hy
      simp [mapLookup] at hy
      obtain ⟨key, rfl⟩ := hy
      have hx := mapLookup_of_mem_mapEntries me
      rw [key, dynamic] at hx
      cases hx
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, key, part])
  have zero : ∀ e ∈ mapEntries I, e.2 = .integer 0 := by
    intro e me
    have hx := mapLookup_of_mem_mapEntries me
    rw [lookI] at hx
    split at hx
    · simp at hx
      exact hx.2.symm
    · cases hx
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) false "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  obtain rfl : out = [] := nil_of_lookup_none out fun q => by
    rw [lookO]
    cases found : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rfl
    | some e => simp [kept, zero e (List.mem_of_find?_eq_some found)]
  have absent : mapLookup ([] : List (Term × Term)) (.atom "dynamic") = Option.none := rfl
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, dynamic, absent, Erlang.maps.«put/3»]
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [runI, runO]

/-- The empty type is empty. -/
theorem empty_none (d : Dispatcher) :
    Elixir.Module.Types.Descr.«empty?/1» d (.map []) = .ok Term.true := by
  simp only [Elixir.Module.Types.Descr.«empty?/1»]
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [getMapKeys_single, mapLookup, Erlang.erlang.«==/2», Term.true]

end Elixir.STTDescrProofsTest

-- A function type and its negation hold the same BDDs for each arity, whose
-- differences are bottom, so their intersection drops every arity.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

/-- Function types are unions (true) or negations (false) of maps from arities to BDDs. -/
abbrev FunField (w : Term) : Prop :=
  ∃ (pos : Bool) (R : List (Term × Term)), w = .tuple #[.atom (if pos then "union" else "negation"), .map R]

/-- A BDD without its own copy is bottom. -/
theorem bdd_difference_self (b : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/2» b b = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_difference/2»
  simp [Erlang.erlang.«=:=/2»]

/-- Each step of `fun_repr_difference/2` removes an arity whose BDD the accumulator holds as is. -/
theorem repr_step (acc : List (Term × Term)) (key bdd : Term)
    (same : ∀ v, mapLookup acc key = some v → v = bdd) :
    ∃ next, Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3» key bdd (.map acc) = .ok (.map next) ∧
      (∀ q, compareExact (fuel q key) q key ≠ .eq → mapLookup next q = mapLookup acc q) ∧
      (∀ q, compareExact (fuel q key) q key = .eq → mapLookup next q = Option.none) := by
  unfold Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3»
  cases found : mapLookup acc key with
  | none =>
    refine ⟨acc, by simp [getMapKeys_single, found], fun q _ => rfl, fun q eq => ?_⟩
    rw [mapLookup_congr eq]; exact found
  | some v =>
    obtain rfl := same v found
    refine ⟨acc.filter fun e => !decide (compareExact (fuel key e.1) key e.1 = .eq), ?_, fun q ne => ?_, fun q eq => ?_⟩
    · simp [getMapKeys_single, found, bdd_difference_self, isMember, Erlang.maps.«remove/2»]
    · rw [mapLookup_remove]; simp [ne]
    · rw [mapLookup_remove]; simp [eq]

/-- Folding `fun_repr_difference/2` over arities whose BDDs the accumulator holds as is
removes them. -/
theorem repr_fold (n : Nat) (es acc : List (Term × Term))
    (distinct : es.Pairwise (fun a b => compareExact (fuel a.1 b.1) a.1 b.1 ≠ .eq))
    (same : ∀ e ∈ es, ∀ v, mapLookup acc e.1 = some v → v = e.2) :
    ∃ M, es.foldlM (fun acc entry =>
        (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table n)
          (.function false "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
          #[entry.1, entry.2, acc] : Except Exception Term)) (.map acc) = .ok (.map M) ∧
      ∀ q, mapLookup M q =
        match es.find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some _ => Option.none
        | none => mapLookup acc q := by
  induction es generalizing acc with
  | nil => exact ⟨acc, rfl, fun q => rfl⟩
  | cons e rest ih =>
    have apart := List.pairwise_cons.mp distinct
    obtain ⟨next, run₁, other, gone⟩ := repr_step acc e.1 e.2 (same e (List.mem_cons_self ..))
    have step : (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table n)
        (.function false "Elixir.Module.Types.Descr" "-fun_repr_difference/2-fun-0-" 3 #[])
        #[e.1, e.2, .map acc] : Except Exception Term) = .ok (.map next) := by
      rw [dispatch_except, Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_difference/2-fun-0-/3».pure, run₁]
    obtain ⟨M, run, look⟩ := ih next apart.2 (by
      intro e' member v found
      rw [other e'.1 (fun s => apart.1 e' member (Lynx.Term.compareExact_eq_symm s))] at found
      exact same e' (List.mem_cons_of_mem _ member) v found)
    refine ⟨M, by simp only [List.foldlM_cons, step, Lynx.Except.ok_bind]; exact run, fun q => ?_⟩
    rw [look q]
    by_cases s : compareExact (fuel q e.1) q e.1 = .eq
    · have absent : rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) = Option.none := by
        rw [List.find?_eq_none]
        intro p member hit
        exact apart.1 p member
          (Lynx.Term.compareExact_eq_trans (Lynx.Term.compareExact_eq_symm s) (of_decide_eq_true hit))
      simp only [absent, List.find?_cons, s, decide_true]
      exact gone q s
    · simp only [List.find?_cons, s, decide_false]
      cases rest.find? (fun p => decide (compareExact (fuel q p.1) q p.1 = .eq)) with
      | none => exact other q s
      | some _ => rfl

/-- The difference of a map of arities to BDDs with a map of the same lookups is empty. -/
theorem repr_cancel (n : Nat) (R M : List (Term × Term)) (lookups : ∀ q, mapLookup M q = mapLookup R q) :
    Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
      (.map R) (.map M) = .ok (.map []) := by
  obtain ⟨D, run, look⟩ := repr_fold n (mapEntries M) R (mapEntries_distinct M) (by
    intro e member v found
    rw [← lookups, mapLookup_of_mem_mapEntries member] at found
    exact (Option.some.inj found).symm)
  obtain rfl : D = [] := nil_of_lookup_none D fun q => by
    rw [look q]
    cases hit : (mapEntries M).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | some _ => rfl
    | none =>
      have : mapLookup (mapEntries M) q = Option.none := by simp [mapLookup, hit]
      rw [mapLookup_mapEntries, lookups] at this
      exact this
  simp only [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
  simpa using run

/-- A function type does not intersect its negation. -/
theorem fun_negation (n : Nat) (w : Term) (field : FunField w) :
    ∃ y, Elixir.Module.Types.Descr.«fun_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
        (.tuple #[.atom "negation", .map []]) w = .ok y ∧
      (y = .integer 0 ∨ ∀ m, Elixir.Module.Types.Descr.«fun_intersection/2»
        (Dispatcher.ofTable Erlang.program.fun_table m) w y = .ok (.integer 0)) := by
  obtain ⟨pos, R, rfl⟩ := field
  cases pos with
  | true =>
    obtain ⟨out, merge, look⟩ := Erlang.maps.merge_with_lookup (Dispatcher.ofTable Erlang.program.fun_table n) false
      "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] R (fun _ _ _ => .nil)
      (by intro e _ v found; simp [mapLookup] at found)
    have same : ∀ q, mapLookup out q = mapLookup R q := by
      intro q
      rw [look q, ← mapLookup_mapEntries R]
      simp only [mapLookup, equalExact_eq_decide]
      cases (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) <;> simp
    refine ⟨.tuple #[.atom "negation", .map out], ?_, Or.inr fun m => ?_⟩
    · simp [Elixir.Module.Types.Descr.«fun_difference/2», Elixir.Module.Types.Descr.«fun_repr_union/2»,
        Elixir.Module.Types.Descr.«symmetrical_merge/3», merge, Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · simp [Elixir.Module.Types.Descr.«fun_intersection/2», repr_cancel m R out same, Erlang.erlang.«==/2»,
        Erlang.erlang.«map_size/1», Lynx.Except.andAlso]
  | false =>
    have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
        (.map R) (.map []) = .ok (.map R) := by
      simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
    by_cases empty : ((R.map Prod.fst).eraseDupsBy (fun a b => decide (compareExact (fuel a b) a b = .eq))).length = 0
    · refine ⟨.integer 0, ?_, Or.inl rfl⟩
      simp [Elixir.Module.Types.Descr.«fun_difference/2», keep, Erlang.erlang.«==/2»,
        Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
    · refine ⟨.tuple #[.atom "union", .map R], ?_, Or.inr fun m => ?_⟩
      · simp [Elixir.Module.Types.Descr.«fun_difference/2», keep, Erlang.erlang.«==/2»,
          Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
      · simp [Elixir.Module.Types.Descr.«fun_intersection/2», repr_cancel m R R (fun _ => rfl),
          Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]

end Elixir.STTDescrProofsTest

-- Lazy BDDs ordered by their literals: unions, removals, intersections,
-- negations, and differences terminate and compute the propositional
-- connectives, so a BDD that no assignment of its literals satisfies has no line.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

namespace BddProofs

/-- BDD literals are leaves: triples with an integer key. -/
def IsLeaf (t : Term) : Prop := ∃ (k : Int) (x y : Term), t = .tuple #[.integer k, x, y]

/-- Ordered BDDs whose literals satisfy `ok`. -/
def Bdd (ok : Term → Prop) : Term → Prop
  | .atom "bdd_top" => True
  | .atom "bdd_bot" => True
  | .tuple ⟨[.integer _, lit, c, u, d]⟩ => IsLeaf lit ∧ ok lit ∧
      Bdd (fun t => ok t ∧ compare (fuel lit t) lit t = .lt) c ∧ Bdd (fun t => ok t ∧ compare (fuel lit t) lit t = .lt) u ∧
      Bdd (fun t => ok t ∧ compare (fuel lit t) lit t = .lt) d
  | .tuple ⟨[.integer k, x, y]⟩ => ok (.tuple #[.integer k, x, y])
  | _ => False

/-- The propositional semantics of a BDD, given the truth of each literal. -/
def eval (ρ : Term → Bool) : Term → Bool
  | .atom "bdd_top" => true
  | .tuple ⟨[_, lit, c, u, d]⟩ => (ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)
  | .tuple ⟨[k, x, y]⟩ => ρ (.tuple #[k, x, y])
  | _ => false

theorem Bdd.shape {ok : Term → Prop} {b : Term} (wf : Bdd ok b) :
    b = .atom "bdd_top" ∨ b = .atom "bdd_bot" ∨ (∃ (k : Int) (x y : Term), b = .tuple #[.integer k, x, y]) ∨
      ∃ (h : Int) (lit c u d : Term), b = .tuple #[.integer h, lit, c, u, d] := by
  unfold Bdd at wf
  split at wf <;> simp_all

def bandI : Int → Int → Int
  | .ofNat x, .ofNat y => .ofNat (x &&& y)
  | .ofNat x, .negSucc y => .ofNat (x ^^^ (x &&& y))
  | .negSucc x, .ofNat y => .ofNat (y ^^^ (y &&& x))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)

def bxorI : Int → Int → Int
  | .ofNat x, .ofNat y => .ofNat (x ^^^ y)
  | .ofNat x, .negSucc y => .negSucc (x ^^^ y)
  | .negSucc x, .ofNat y => .negSucc (x ^^^ y)
  | .negSucc x, .negSucc y => .ofNat (x ^^^ y)

@[simp] theorem band_int (x y : Int) : Erlang.erlang.«band/2» (.integer x) (.integer y) = .ok (.integer (bandI x y)) := by
  cases x <;> cases y <;> rfl
@[simp] theorem bxor_int (x y : Int) : Erlang.erlang.«bxor/2» (.integer x) (.integer y) = .ok (.integer (bxorI x y)) := by
  cases x <;> cases y <;> rfl
@[simp] theorem bsl_six (x : Int) : Erlang.erlang.«bsl/2» (.integer x) (.integer 6) = .ok (.integer (x <<< 6)) := rfl
@[simp] theorem bsr_two (x : Int) : Erlang.erlang.«bsr/2» (.integer x) (.integer 2) = .ok (.integer (x >>> 2)) := rfl

/-- Computations that return an integer. -/
def IntOk (e : Except Exception Term) : Prop := ∃ z : Int, e = .ok (.integer z)

theorem IntOk.bind {m : Except Exception Term} {f : Term → Except Exception Term} (hm : IntOk m)
    (hf : ∀ a : Int, IntOk (f (.integer a))) : IntOk (m >>= f) := by
  obtain ⟨a, rfl⟩ := hm
  exact hf a

theorem hash_ok {ok : Term → Prop} {b : Term} (wf : Bdd ok b) {e : Except Exception Term}
    (top : b = .atom "bdd_top" → IntOk e) (bot : b = .atom "bdd_bot" → IntOk e)
    (leaf : ∀ (k : Int) (x y : Term), b = .tuple #[.integer k, x, y] → IntOk e)
    (node : ∀ (h : Int) (lit c u d : Term), b = .tuple #[.integer h, lit, c, u, d] → IntOk e) : IntOk e := by
  rcases wf.shape with h | h | ⟨k, x, y, h⟩ | ⟨n, lit, c, u, d, h⟩
  · exact top h
  · exact bot h
  · exact leaf k x y h
  · exact node n lit c u d h

theorem node_new {okc oku okd : Term → Prop} (lit c u d : Term) (leaf : IsLeaf lit) (hc : Bdd okc c) (hu : Bdd oku u) (hd : Bdd okd d) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_node_new/4» lit c u d = .ok (.tuple #[.integer h, lit, c, u, d]) := by
  obtain ⟨k, x, y, rfl⟩ := leaf
  have hash : IntOk (Elixir.Module.Types.Descr.«bdd_compute_hash/4» (.tuple #[.integer k, x, y]) c u d) := by
    unfold Elixir.Module.Types.Descr.«bdd_compute_hash/4»
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [band_int]
      try rfl
    refine IntOk.bind ?_ fun _ => ?_
    · refine hash_ok hc ?_ ?_ ?_ ?_ <;>
        (intros; subst_vars; apply Exists.intro
         simp only [band_int, pure, Except.pure]
         try rfl)
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [Erlang.erlang.«+/2_integers», bsl_six, bsr_two, bxor_int, Lynx.Except.ok_bind]
      try rfl
    refine IntOk.bind ?_ fun _ => ?_
    · refine hash_ok hu ?_ ?_ ?_ ?_ <;>
        (intros; subst_vars; apply Exists.intro
         simp only [band_int, pure, Except.pure]
         try rfl)
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [Erlang.erlang.«+/2_integers», bsl_six, bsr_two, bxor_int, Lynx.Except.ok_bind]
      try rfl
    refine IntOk.bind ?_ fun _ => ?_
    · refine hash_ok hd ?_ ?_ ?_ ?_ <;>
        (intros; subst_vars; apply Exists.intro
         simp only [band_int, pure, Except.pure]
         try rfl)
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [Erlang.erlang.«+/2_integers», bsl_six, bsr_two, bxor_int, Lynx.Except.ok_bind]
      try rfl
    apply Exists.intro
    simp only [band_int]
    try rfl
  obtain ⟨h, run⟩ := hash
  exact ⟨h, by simp [Elixir.Module.Types.Descr.«bdd_node_new/4», run]⟩

/-- The literals of a node's children are above the node's literal. -/
abbrev Above (ok : Term → Prop) (lit : Term) : Term → Prop := fun t => ok t ∧ Term.compare (Term.fuel lit t) lit t = .lt

theorem Bdd.node_iff {ok : Term → Prop} {h : Int} {lit c u d : Term} :
    Bdd ok (.tuple #[.integer h, lit, c, u, d]) ↔
      IsLeaf lit ∧ ok lit ∧ Bdd (Above ok lit) c ∧ Bdd (Above ok lit) u ∧ Bdd (Above ok lit) d := by
  simp [Bdd]

theorem Bdd.leaf_iff {ok : Term → Prop} {k : Int} {x y : Term} :
    Bdd ok (.tuple #[.integer k, x, y]) ↔ ok (.tuple #[.integer k, x, y]) := by
  simp [Bdd]

theorem sizeOf_children (h lit c u d : Term) :
    sizeOf c < sizeOf (Term.tuple #[h, lit, c, u, d]) ∧ sizeOf u < sizeOf (Term.tuple #[h, lit, c, u, d]) ∧
      sizeOf d < sizeOf (Term.tuple #[h, lit, c, u, d]) := by
  simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec, List.cons.sizeOf_spec,
    List.nil.sizeOf_spec]
  omega

/-- Induction over ordered BDDs. -/
theorem Bdd.induction {P : (Term → Prop) → Term → Prop}
    (top : ∀ ok, P ok (.atom "bdd_top")) (bot : ∀ ok, P ok (.atom "bdd_bot"))
    (leaf : ∀ ok (k : Int) x y, ok (.tuple #[.integer k, x, y]) → P ok (.tuple #[.integer k, x, y]))
    (node : ∀ ok (h : Int) lit c u d, IsLeaf lit → ok lit →
      Bdd (Above ok lit) c → Bdd (Above ok lit) u → Bdd (Above ok lit) d →
      P (Above ok lit) c → P (Above ok lit) u → P (Above ok lit) d →
      P ok (.tuple #[.integer h, lit, c, u, d])) :
    ∀ (ok : Term → Prop) (b : Term), Bdd ok b → P ok b := by
  suffices all : ∀ n, ∀ (ok : Term → Prop) (b : Term), sizeOf b ≤ n → Bdd ok b → P ok b from
    fun ok b => all _ ok b (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro ok b size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro ok b size wf
    rcases wf.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact top ok
    · exact bot ok
    · exact leaf ok k x y (Bdd.leaf_iff.mp wf)
    · obtain ⟨isLeaf, okLit, hc, hu, hd⟩ := Bdd.node_iff.mp wf
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h) lit c u d
      exact node ok h lit c u d isLeaf okLit hc hu hd (ih _ c (by omega) hc) (ih _ u (by omega) hu)
        (ih _ d (by omega) hd)

theorem Bdd.mono {ok ok' : Term → Prop} (h : ∀ t, ok t → ok' t) {b : Term} (wf : Bdd ok b) : Bdd ok' b := by
  revert ok'
  refine Bdd.induction (P := fun ok b => ∀ {ok'}, (∀ t, ok t → ok' t) → Bdd ok' b) ?_ ?_ ?_ ?_ ok b wf
  · intro ok ok' _; simp [Bdd]
  · intro ok ok' _; simp [Bdd]
  · intro ok k x y okb ok' h; exact Bdd.leaf_iff.mpr (h _ okb)
  · intro ok n lit c u d isLeaf okLit _ _ _ ihc ihu ihd ok' h
    have lift : ∀ t, Above ok lit t → Above ok' lit t := fun t ht => ⟨h t ht.1, ht.2⟩
    exact Bdd.node_iff.mpr ⟨isLeaf, h _ okLit, ihc lift, ihu lift, ihd lift⟩

/-- A BDD whose head is above `m` has all its literals above `m`. -/
def head : Term → Option Term
  | .tuple ⟨[_, lit, _, _, _]⟩ => some lit
  | .tuple ⟨[k, x, y]⟩ => some (.tuple #[k, x, y])
  | _ => none

theorem Bdd.raise {ok : Term → Prop} {b m : Term} (wf : Bdd ok b)
    (above : ∀ l, head b = some l → compare (fuel m l) m l = .lt) : Bdd (Above ok m) b := by
  rcases wf.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · simp [Bdd]
  · simp [Bdd]
  · exact Bdd.leaf_iff.mpr ⟨Bdd.leaf_iff.mp wf, above _ (by simp [head])⟩
  · obtain ⟨isLeaf, okLit, hc, hu, hd⟩ := Bdd.node_iff.mp wf
    have ml : compare (fuel m lit) m lit = .lt := above lit (by simp [head])
    have lift : ∀ t, Above ok lit t → Above (Above ok m) lit t :=
      fun t ht => ⟨⟨ht.1, Lynx.Term.compare_lt_trans ml ht.2⟩, ht.2⟩
    exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okLit, ml⟩, hc.mono lift, hu.mono lift, hd.mono lift⟩

/-- A non-trivial BDD seen as a node: leaves `l` are `(l and top) or bot or (not l and bot)`. -/
def Split (a lit c u d : Term) : Prop :=
  (∃ h : Int, a = .tuple #[.integer h, lit, c, u, d]) ∨
    (a = lit ∧ IsLeaf lit ∧ c = .atom "bdd_top" ∧ u = .atom "bdd_bot" ∧ d = .atom "bdd_bot")

theorem head_some {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) :
    (∃ (k : Int) (x y : Term), a = .tuple #[.integer k, x, y] ∧ l = a) ∨
      ∃ (h : Int) (c u d : Term), a = .tuple #[.integer h, l, c, u, d] := by
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · simp [head] at ha
  · simp [head] at ha
  · simp [head] at ha; exact Or.inl ⟨k, x, y, rfl, ha.symm⟩
  · simp [head] at ha; subst ha; exact Or.inr ⟨h, c, u, d, rfl⟩

theorem head_shape {a l : Term} (ha : head a = some l) :
    (∃ x y z : Term, a = .tuple #[x, y, z] ∧ l = a) ∨ ∃ h c u d : Term, a = .tuple #[h, l, c, u, d] := by
  unfold head at ha
  split at ha
  · cases ha; exact Or.inr ⟨_, _, _, _, rfl⟩
  · cases ha; exact Or.inl ⟨_, _, _, rfl, rfl⟩
  · cases ha

theorem compare_lt {ok : Term → Prop} {a b la lb : Term} (wa : Bdd ok a) (ha : head a = some la)
    (hb : head b = some lb) (lt : compare (fuel la lb) la lb = .lt) :
    ∃ (h : Int) (c u d : Term), Elixir.Module.Types.Descr.«bdd_compare/2» a b =
      .ok (.tuple #[.atom "lt", .tuple #[.integer h, la, c, u, d], b]) ∧ Split a la c u d := by
  have top : Bdd (fun _ => True) (.atom "bdd_top") := by simp [Bdd]
  have bot : Bdd (fun _ => True) (.atom "bdd_bot") := by simp [Bdd]
  unfold Elixir.Module.Types.Descr.«bdd_compare/2»
  rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨n, c, u, d, rfl⟩
  · obtain ⟨h, run⟩ := node_new (.tuple #[.integer k, x, y]) _ _ _ ⟨k, x, y, rfl⟩ top bot bot
    refine ⟨h, _, _, _, ?_, Or.inr ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩⟩
    rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», lt, run]
  · refine ⟨n, c, u, d, ?_, Or.inl ⟨n, rfl⟩⟩
    rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», lt]

theorem compare_gt {ok : Term → Prop} {a b la lb : Term} (wb : Bdd ok b) (ha : head a = some la)
    (hb : head b = some lb) (gt : compare (fuel la lb) la lb = .gt) :
    ∃ (h : Int) (c u d : Term), Elixir.Module.Types.Descr.«bdd_compare/2» a b =
      .ok (.tuple #[.atom "gt", a, .tuple #[.integer h, lb, c, u, d]]) ∧ Split b lb c u d := by
  have top : Bdd (fun _ => True) (.atom "bdd_top") := by simp [Bdd]
  have bot : Bdd (fun _ => True) (.atom "bdd_bot") := by simp [Bdd]
  unfold Elixir.Module.Types.Descr.«bdd_compare/2»
  rcases head_some wb hb with ⟨k, x, y, rfl, rfl⟩ | ⟨n, c, u, d, rfl⟩
  · obtain ⟨h, run⟩ := node_new (.tuple #[.integer k, x, y]) _ _ _ ⟨k, x, y, rfl⟩ top bot bot
    refine ⟨h, _, _, _, ?_, Or.inr ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩⟩
    rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», gt, run]
  · refine ⟨n, c, u, d, ?_, Or.inl ⟨n, rfl⟩⟩
    rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», gt]

/-- The literal `bdd_compare/2` reads of a BDD. -/
theorem compare_eq {a b la lb : Term} (ha : head a = some la) (hb : head b = some lb)
    (eq : compare (fuel la lb) la lb = .eq) :
    Elixir.Module.Types.Descr.«bdd_compare/2» a b = .ok (.tuple #[.atom "eq", a, b]) := by
  unfold Elixir.Module.Types.Descr.«bdd_compare/2»
  rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», eq]

/-! Semantics. -/

/-- Valuations give equal literals the same truth. -/
def Resp (ρ : Term → Bool) : Prop := ∀ a b, compare (fuel a b) a b = .eq → ρ a = ρ b

@[simp] theorem eval_top (ρ : Term → Bool) : eval ρ (.atom "bdd_top") = Bool.true := by simp [eval]
@[simp] theorem eval_bot (ρ : Term → Bool) : eval ρ (.atom "bdd_bot") = Bool.false := by simp [eval]
@[simp] theorem eval_node (ρ : Term → Bool) (h lit c u d : Term) :
    eval ρ (.tuple #[h, lit, c, u, d]) = ((ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)) := by
  simp [eval]
@[simp] theorem eval_leaf (ρ : Term → Bool) (k x y : Term) :
    eval ρ (.tuple #[k, x, y]) = ρ (.tuple #[k, x, y]) := by
  simp [eval]

theorem Split.eval {a lit c u d : Term} (split : Split a lit c u d) (ρ : Term → Bool) :
    eval ρ a = ((ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)) := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩
  · simp
  · cases h : ρ (.tuple #[.integer k, x, y]) <;> simp [h]

theorem tuple3_exact {a₀ a₁ a₂ b : Term} (e : compareExact (fuel (.tuple #[a₀, a₁, a₂]) b) (.tuple #[a₀, a₁, a₂]) b = .eq) :
    ∃ b₀ b₁ b₂, b = .tuple #[b₀, b₁, b₂] ∧ compareExact (fuel a₀ b₀) a₀ b₀ = .eq ∧ compareExact (fuel a₁ b₁) a₁ b₁ = .eq ∧
      compareExact (fuel a₂ b₂) a₂ b₂ = .eq := by
  rw [compareExact_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, rest⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, rfl, e.1, e.2.1, e.2.2⟩

theorem tuple5_exact {a₀ a₁ a₂ a₃ a₄ b : Term} (e : compareExact (fuel (.tuple #[a₀, a₁, a₂, a₃, a₄]) b) (.tuple #[a₀, a₁, a₂, a₃, a₄]) b = .eq) :
    ∃ b₀ b₁ b₂ b₃ b₄, b = .tuple #[b₀, b₁, b₂, b₃, b₄] ∧ compareExact (fuel a₁ b₁) a₁ b₁ = .eq ∧
      compareExact (fuel a₂ b₂) a₂ b₂ = .eq ∧ compareExact (fuel a₃ b₃) a₃ b₃ = .eq ∧ compareExact (fuel a₄ b₄) a₄ b₄ = .eq := by
  rw [compareExact_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, rest⟩⟩⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, b₃, b₄, rfl, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2⟩

/-- Exactly equal BDDs have the same semantics. -/
theorem eval_congr {ok : Term → Prop} {a : Term} (wa : Bdd ok a) {ρ : Term → Bool} (resp : Resp ρ) :
    ∀ {b}, compareExact (fuel a b) a b = .eq → eval ρ a = eval ρ b := by
  refine Bdd.induction (P := fun _ a => ∀ {b}, compareExact (fuel a b) a b = .eq → eval ρ a = eval ρ b)
    ?_ ?_ ?_ ?_ ok a wa
  · intro _ b e
    obtain rfl := (compareExact_eq_atom b "bdd_top").mp (Lynx.Term.compareExact_eq_symm e)
    rfl
  · intro _ b e
    obtain rfl := (compareExact_eq_atom b "bdd_bot").mp (Lynx.Term.compareExact_eq_symm e)
    rfl
  · intro _ k x y _ b e
    obtain ⟨b₀, b₁, b₂, rfl, -, -, -⟩ := tuple3_exact e
    simp only [eval_leaf]
    exact resp _ _ (compare_eq_of_compareExact_eq _ _ e)
  · intro _ h lit c u d _ _ _ _ _ ihc ihu ihd b e
    obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl, el, ec, eu, ed⟩ := tuple5_exact e
    simp only [eval_node]
    rw [resp _ _ (compare_eq_of_compareExact_eq _ _ el), ihc ec, ihu eu, ihd ed]

theorem head_ok {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) : ok l := by
  rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨h, c, u, d, rfl⟩
  · exact Bdd.leaf_iff.mp wa
  · exact (Bdd.node_iff.mp wa).2.1

theorem head_leaf {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) : IsLeaf l := by
  rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨h, c, u, d, rfl⟩
  · exact ⟨k, x, y, rfl⟩
  · exact (Bdd.node_iff.mp wa).1

/-- The children of a split BDD hold literals above its head. -/
theorem Split.children {ok : Term → Prop} {a lit c u d : Term} (split : Split a lit c u d) (wa : Bdd ok a) :
    Bdd (Above ok lit) c ∧ Bdd (Above ok lit) u ∧ Bdd (Above ok lit) d := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, _, rfl, rfl, rfl⟩
  · exact (Bdd.node_iff.mp wa).2.2
  · simp [Bdd]

/-! Termination: each recursive call raises the smallest literal of its arguments. -/

/-- All literals of `b` are above `m`. -/
abbrev High (m : Term) : Term → Prop := Bdd (fun t => Term.compare (Term.fuel m t) m t = .lt)

open Classical in
/-- The literals of the universe that some argument does not exceed. -/
noncomputable def μ (U : List Term) (a b : Term) : Nat :=
  (U.filter fun m => !decide (High m a ∧ High m b)).length

theorem filter_le {α} (U : List α) (p q : α → Bool) (h : ∀ x ∈ U, p x → q x) :
    (U.filter p).length ≤ (U.filter q).length := by
  induction U with
  | nil => simp
  | cons x xs ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases px : p x <;> by_cases qx : q x <;> simp [px, qx] <;>
      first | omega | (have := h x List.mem_cons_self px; simp_all)

theorem filter_lt {α} (U : List α) (p q : α → Bool) (h : ∀ x ∈ U, p x → q x) {l : α} (hl : l ∈ U)
    (hp : p l = Bool.false) (hq : q l = Bool.true) : (U.filter p).length < (U.filter q).length := by
  induction U with
  | nil => simp at hl
  | cons x xs ih =>
    have le := filter_le xs p q (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [hp, hq]; omega
    · have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hl
      by_cases px : p x <;> by_cases qx : q x <;> simp [px, qx] <;>
        first | omega | (have := h x List.mem_cons_self px; simp_all)

theorem μ_le {U : List Term} {a b a' b' : Term}
    (mono : ∀ m, High m a → High m b → High m a' ∧ High m b') : μ U a' b' ≤ μ U a b := by
  unfold μ
  apply filter_le
  intro m _ hm
  simp at hm ⊢
  intro ha hb
  exact hm (mono m ha hb).1 (mono m ha hb).2

theorem μ_lt {U : List Term} {a b a' b' l : Term}
    (mono : ∀ m, High m a → High m b → High m a' ∧ High m b') (hl : l ∈ U)
    (old : ¬(High l a ∧ High l b)) (new : High l a' ∧ High l b') : μ U a' b' < μ U a b := by
  unfold μ
  refine filter_lt _ _ _ ?_ hl ?_ ?_
  · intro m _ hm
    simp at hm ⊢
    intro ha hb
    exact hm (mono m ha hb).1 (mono m ha hb).2
  · simp [new]
  · simp
    exact fun ha hb => old ⟨ha, hb⟩

/-- A BDD is never above its own head. -/
theorem not_high_head {ok : Term → Prop} {a l : Term} (_wa : Bdd ok a) (ha : head a = some l) : ¬High l a :=
  fun high => by have := head_ok high ha; simp at this

/-! BDDs without leaves, whose literals all sit in nodes. -/

def NoLeaf : Term → Prop
  | .atom "bdd_top" => True
  | .atom "bdd_bot" => True
  | .tuple ⟨[_, _, c, u, d]⟩ => NoLeaf c ∧ NoLeaf u ∧ NoLeaf d
  | _ => False

theorem NoLeaf.top : NoLeaf (.atom "bdd_top") := by simp [NoLeaf]
theorem NoLeaf.bot : NoLeaf (.atom "bdd_bot") := by simp [NoLeaf]

theorem NoLeaf.node {h lit c u d : Term} : NoLeaf (.tuple #[h, lit, c, u, d]) ↔ NoLeaf c ∧ NoLeaf u ∧ NoLeaf d := by
  simp [NoLeaf]

theorem NoLeaf.leaf {k x y : Term} (n : NoLeaf (.tuple #[k, x, y])) : False := by
  simp [NoLeaf] at n

theorem Split.noLeaf {a lit c u d : Term} (split : Split a lit c u d) (n : NoLeaf a) :
    NoLeaf c ∧ NoLeaf u ∧ NoLeaf d := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, -⟩
  · exact NoLeaf.node.mp n
  · exact n.leaf.elim

/-! Unions. -/

def UnionOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_union/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a || eval ρ b)

/-- What unions and removals guarantee, including that they keep BDDs without leaves. -/
def UnionOkN (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_union/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → eval ρ r = (eval ρ a || eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

def RemoveOkN (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_remove/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

def RemoveBddOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_remove_bdd/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

/-- Every pair of BDDs over the universe below the measure `n` unites and removes. -/
def Below (U : List Term) (n : Nat) : Prop :=
  ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → UnionOkN a b ∧ RemoveOkN a b ∧ RemoveBddOk a b

theorem Bdd.top {ok : Term → Prop} : Bdd ok (.atom "bdd_top") := by simp [Bdd]
theorem Bdd.bot {ok : Term → Prop} : Bdd ok (.atom "bdd_bot") := by simp [Bdd]

theorem nontrivial_head {ok : Term → Prop} {a : Term} (wa : Bdd ok a) (t : a ≠ .atom "bdd_top")
    (f : a ≠ .atom "bdd_bot") : ∃ l, head a = some l := by
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact absurd rfl t
  · exact absurd rfl f
  · exact ⟨.tuple #[.integer k, x, y], by simp [head]⟩
  · exact ⟨lit, by simp [head]⟩

/-- Arguments above `m` keep the result above `m`. -/
theorem High.split {ok : Term → Prop} {a lit c u d m : Term} (split : Split a lit c u d) (_wa : Bdd ok a)
    (high : High m a) : High m c ∧ High m u ∧ High m d := by
  obtain ⟨hc, hu, hd⟩ := split.children high
  exact ⟨hc.mono fun _ h => h.1, hu.mono fun _ h => h.1, hd.mono fun _ h => h.1⟩

theorem Split.high {ok : Term → Prop} {a lit c u d : Term} (split : Split a lit c u d) (wa : Bdd ok a) :
    High lit c ∧ High lit u ∧ High lit d := by
  obtain ⟨hc, hu, hd⟩ := split.children wa
  exact ⟨hc.mono fun _ h => h.2, hu.mono fun _ h => h.2, hd.mono fun _ h => h.2⟩

theorem Split.head {a lit c u d : Term} (split : Split a lit c u d) : head a = some lit := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, -⟩ <;> simp [BddProofs.head]

theorem Bdd.congr {ok : Term → Prop} {x la lb : Term} (e : Term.compare (Term.fuel la lb) la lb = .eq)
    (w : Bdd (Above ok lb) x) : Bdd (Above ok la) x :=
  w.mono fun t h => ⟨h.1, by rw [Lynx.Term.compare_congr_left e]; exact h.2⟩

theorem High.congr {x la lb : Term} (e : Term.compare (Term.fuel la lb) la lb = .eq) (w : High lb x) : High la x :=
  w.mono fun t h => by rw [Lynx.Term.compare_congr_left e]; exact h

theorem union_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : Below U (μ U a b)) : UnionOkN a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_, fun na _ => na⟩
    · unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [← eval_congr wb resp same]; simp
  by_cases ta : a = .atom "bdd_top"
  · subst ta
    refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp, fun _ _ => NoLeaf.top⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases tb : b = .atom "bdd_top"
  · subst tb
    refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp, fun _ _ => NoLeaf.top⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fa : a = .atom "bdd_bot"
  · subst fa
    refine ⟨b, ?_, fun ok _ wb => wb, fun ρ _ => by simp, fun _ nb => nb⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fb : b = .atom "bdd_bot"
  · subst fb
    refine ⟨a, ?_, fun ok wa _ => wa, fun ρ _ => by simp, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
  obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt
    obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    obtain ⟨hc, hu, hd⟩ := split.children wa
    obtain ⟨Hc, Hu, Hd⟩ := split.high wa
    have HB : High la b := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ b (hc.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)).2.1
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ b (hu.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)).1
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ b (hd.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)).2.1
    obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc (raiseB wb))
      (keep₂ _ hu (raiseB wb)) (keep₃ _ hd (raiseB wb))
    have body : Elixir.Module.Types.Descr.«bdd_union/2» a b =
        if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
        else .ok (.tuple #[.integer h₁, la, r₁, r₂, r₃]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Erlang.erlang.«=:=/2», same]
      simp [run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
    · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wb)
        (keep₂ _ (hu.mono fun _ h => h.1) wb)
        (lower (fun m ha' hb' => ⟨keep₁ _ (High.split split wa ha').1 hb', keep₂ _ (High.split split wa ha').2.1 hb'⟩)
          ⟨keep₁ _ Hc HB, keep₂ _ Hu HB⟩)).1
      refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => nlr (nl₁ (split.noLeaf na).1 nb) (nl₂ (split.noLeaf na).2.1 nb)⟩
      · obtain ⟨oc, ou, -⟩ := split.children oka
        exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) okb) (keep₂ ok (ou.mono fun _ h => h.1) okb)
      · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wb) resp post
        have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [semr ρ resp, split.eval ρ, s₂]
        rw [← e₃] at s₁
        rw [← e₃]
        revert s₁ s₃
        generalize eval ρ r₃ = R
        generalize eval ρ c₁ = C
        generalize eval ρ u₁ = V
        generalize eval ρ d₁ = D
        generalize eval ρ b = B
        generalize ρ la = L
        revert R C V D B L
        decide
    · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => NoLeaf.node.mpr ⟨nl₁ (split.noLeaf na).1 nb, nl₂ (split.noLeaf na).2.1 nb,
          nl₃ (split.noLeaf na).2.2 nb⟩⟩
      · obtain ⟨oc, ou, od⟩ := split.children oka
        exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc (raiseB okb),
          keep₂ _ ou (raiseB okb), keep₃ _ od (raiseB okb)⟩
      · have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [eval_node, split.eval ρ, s₂]
        revert s₁ s₃
        generalize eval ρ r₁ = R₁
        generalize eval ρ r₃ = R₃
        generalize eval ρ c₁ = C
        generalize eval ρ u₁ = V
        generalize eval ρ d₁ = D
        generalize eval ρ b = B
        generalize ρ la = L
        revert R₁ R₃ C V D B L
        decide
  · -- eq
    have run := compare_eq ha hb order
    have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
        High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
      fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
    have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
    rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
      rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
    · -- two leaves
      refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
      · unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run]
      · simp [sameLit ρ resp]
    · -- a leaf below a node
      obtain ⟨-, -, hc, hu, hd⟩ := Bdd.node_iff.mp wb
      have Hu : High lb u₂ := hu.mono fun _ h => h.2
      have Hd : High lb d₂ := hd.mono fun _ h => h.2
      obtain ⟨h₃, node⟩ := node_new lb (.atom "bdd_top") u₂ d₂ (head_leaf wb hb) (Bdd.top (ok := fun _ => True)) hu hd
      have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k₁, x₁, y₁])
          (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
          if compareExact (fuel d₂ (.atom "bdd_top")) d₂ (.atom "bdd_top") = .eq then
            Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_top") u₂
          else .ok (.tuple #[.integer h₃, lb, .atom "bdd_top", u₂, d₂]) := by
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, node]
        by_cases post : compareExact (fuel d₂ (.atom "bdd_top")) d₂ (.atom "bdd_top") = .eq <;> simp [post]
      by_cases post : compareExact (fuel d₂ (.atom "bdd_top")) d₂ (.atom "bdd_top") = .eq
      · obtain rfl := (compareExact_eq_atom _ _).mp post
        obtain ⟨r, runr, keepr, semr, -⟩ := (ih (.atom "bdd_top") u₂ Bdd.top (hu.mono fun _ h => h.1)
          (lowerB (fun m _ hb' => ⟨Bdd.top, (High.split (Or.inl ⟨h₂, rfl⟩) wb hb').2.1⟩) ⟨Bdd.top, Hu⟩)).1
        refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok _ okb => ?_,
          fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
        · exact keepr ok Bdd.top ((Bdd.node_iff.mp okb).2.2.2.1.mono fun _ h => h.1)
        · rw [semr ρ resp]
          cases hl : ρ lb <;> simp [hl, sameLit ρ resp]
      · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok _ okb => ?_,
          fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
        · obtain ⟨leaf, okl, -, ou, od⟩ := Bdd.node_iff.mp okb
          exact Bdd.node_iff.mpr ⟨leaf, okl, Bdd.top, ou, od⟩
        · cases hl : ρ lb <;> simp [hl, sameLit ρ resp]
    · -- a node above a leaf
      obtain ⟨-, -, hc, hu, hd⟩ := Bdd.node_iff.mp wa
      have Hu : High la u₁ := hu.mono fun _ h => h.2
      obtain ⟨h₃, node⟩ := node_new la (.atom "bdd_top") u₁ d₁ (head_leaf wa ha) (Bdd.top (ok := fun _ => True)) hu hd
      have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer h₁, la, c₁, u₁, d₁])
          (.tuple #[.integer k₂, x₂, y₂]) =
          if compareExact (fuel d₁ (.atom "bdd_top")) d₁ (.atom "bdd_top") = .eq then
            Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_top") u₁
          else .ok (.tuple #[.integer h₃, la, .atom "bdd_top", u₁, d₁]) := by
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, node]
        by_cases post : compareExact (fuel d₁ (.atom "bdd_top")) d₁ (.atom "bdd_top") = .eq <;> simp [post]
      by_cases post : compareExact (fuel d₁ (.atom "bdd_top")) d₁ (.atom "bdd_top") = .eq
      · obtain rfl := (compareExact_eq_atom _ _).mp post
        obtain ⟨r, runr, keepr, semr, -⟩ := (ih (.atom "bdd_top") u₁ Bdd.top (hu.mono fun _ h => h.1)
          (lower (fun m ha' _ => ⟨Bdd.top, (High.split (Or.inl ⟨h₁, rfl⟩) wa ha').2.1⟩) ⟨Bdd.top, Hu⟩)).1
        refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka _ => ?_,
          fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
        · exact keepr ok Bdd.top ((Bdd.node_iff.mp oka).2.2.2.1.mono fun _ h => h.1)
        · rw [semr ρ resp]
          cases hl : ρ la <;> simp [hl, ← sameLit ρ resp]
      · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka _ => ?_,
          fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
        · obtain ⟨leaf, okl, -, ou, od⟩ := Bdd.node_iff.mp oka
          exact Bdd.node_iff.mpr ⟨leaf, okl, Bdd.top, ou, od⟩
        · cases hl : ρ la <;> simp [hl, ← sameLit ρ resp]
    · -- two nodes
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
      obtain ⟨hc₂, hu₂, hd₂⟩ := splitB.children wb
      obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
      obtain ⟨Hc₂, Hu₂, Hd₂⟩ := splitB.high wb
      obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
        (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
          ⟨Hc₁, Hc₂.congr order⟩)).1
      obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ u₂ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1)
        (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, (High.split splitB wb hb').2.1⟩)
          ⟨Hu₁, Hu₂.congr order⟩)).1
      obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
        (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, (High.split splitB wb hb').2.2⟩)
          ⟨Hd₁, Hd₂.congr order⟩)).1
      obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc₁ (hc₂.congr order))
        (keep₂ _ hu₁ (hu₂.congr order)) (keep₃ _ hd₁ (hd₂.congr order))
      have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer h₁, la, c₁, u₁, d₁])
          (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
          if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
          else .ok (.tuple #[.integer h₃, la, r₁, r₂, r₃]) := by
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
        by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
      · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
          (keep₂ _ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1))
          (lower (fun m ha' hb' => ⟨keep₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
            keep₂ _ (High.split splitA wa ha').2.1 (High.split splitB wb hb').2.1⟩)
            ⟨keep₁ _ Hc₁ (Hc₂.congr order), keep₂ _ Hu₁ (Hu₂.congr order)⟩)).1
        refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_,
          fun ρ resp => ?_, fun na nb => nlr (nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1)
            (nl₂ (NoLeaf.node.mp na).2.1 (NoLeaf.node.mp nb).2.1)⟩
        · obtain ⟨oc₁, ou₁, -⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, -⟩ := splitB.children okb
          exact keepr ok (keep₁ ok (oc₁.mono fun _ h => h.1) (oc₂.mono fun _ h => h.1))
            (keep₂ ok (ou₁.mono fun _ h => h.1) (ou₂.mono fun _ h => h.1))
        · have e₃ := eval_congr (keep₃ _ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)) resp post
          have s₁ := sem₁ ρ resp
          have s₂ := sem₂ ρ resp
          have s₃ := sem₃ ρ resp
          rw [semr ρ resp, eval_node, eval_node, s₁, s₂, ← sameLit ρ resp]
          rw [e₃, s₁] at s₃
          revert s₃
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          generalize eval ρ u₂ = U₂
          revert L C₁ C₂ D₁ D₂ U₁ U₂
          decide
      · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_,
          fun ρ resp => ?_, fun na nb => NoLeaf.node.mpr ⟨nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1,
            nl₂ (NoLeaf.node.mp na).2.1 (NoLeaf.node.mp nb).2.1, nl₃ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2⟩⟩
        · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
          exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc₁ (oc₂.congr order),
            keep₂ _ ou₁ (ou₂.congr order), keep₃ _ od₁ (od₂.congr order)⟩
        · rw [eval_node, eval_node, eval_node, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, ← sameLit ρ resp]
          cases ρ la <;> simp [Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  · -- gt
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
    have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
        High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
      fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    obtain ⟨hc, hu, hd⟩ := split.children wb
    obtain ⟨Hc, Hu, Hd⟩ := split.high wb
    have HA : High lb a := (raiseA wa).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₂ a (hc.mono fun _ h => h.1) wa
      (lowerB (fun m ha' hb' => ⟨(High.split split wb hb').1, ha'⟩) ⟨Hc, HA⟩)).2.1
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih a u₂ wa (hu.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)).1
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₂ a (hd.mono fun _ h => h.1) wa
      (lowerB (fun m ha' hb' => ⟨(High.split split wb hb').2.2, ha'⟩) ⟨Hd, HA⟩)).2.1
    obtain ⟨h₁, node⟩ := node_new lb r₁ r₂ r₃ (head_leaf wb hb) (keep₁ _ hc (raiseA wa))
      (keep₂ _ (raiseA wa) hu) (keep₃ _ hd (raiseA wa))
    have body : Elixir.Module.Types.Descr.«bdd_union/2» a b =
        if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
        else .ok (.tuple #[.integer h₁, lb, r₁, r₂, r₃]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Erlang.erlang.«=:=/2», same]
      simp [run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
    · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wa)
        (keep₂ _ wa (hu.mono fun _ h => h.1))
        (lowerB (fun m ha' hb' => ⟨keep₁ _ (High.split split wb hb').1 ha', keep₂ _ ha' (High.split split wb hb').2.1⟩)
          ⟨keep₁ _ Hc HA, keep₂ _ HA Hu⟩)).1
      refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => nlr (nl₁ (split.noLeaf nb).1 na) (nl₂ na (split.noLeaf nb).2.1)⟩
      · obtain ⟨oc, ou, -⟩ := split.children okb
        exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) oka) (keep₂ ok oka (ou.mono fun _ h => h.1))
      · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wa) resp post
        have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [semr ρ resp, split.eval ρ, s₂]
        rw [← e₃] at s₁
        rw [← e₃]
        revert s₁ s₃
        generalize eval ρ r₃ = R
        generalize eval ρ c₂ = C
        generalize eval ρ u₂ = V
        generalize eval ρ d₂ = D
        generalize eval ρ a = A
        generalize ρ lb = L
        revert R C V D A L
        decide
    · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => NoLeaf.node.mpr ⟨nl₁ (split.noLeaf nb).1 na, nl₂ na (split.noLeaf nb).2.1,
          nl₃ (split.noLeaf nb).2.2 na⟩⟩
      · obtain ⟨oc, ou, od⟩ := split.children okb
        exact Bdd.node_iff.mpr ⟨head_leaf wb hb, head_ok okb hb, keep₁ _ oc (raiseA oka),
          keep₂ _ (raiseA oka) ou, keep₃ _ od (raiseA oka)⟩
      · have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [eval_node, split.eval ρ, s₂]
        revert s₁ s₃
        generalize eval ρ r₁ = R₁
        generalize eval ρ r₃ = R₃
        generalize eval ρ c₂ = C
        generalize eval ρ u₂ = V
        generalize eval ρ d₂ = D
        generalize eval ρ a = A
        generalize ρ lb = L
        revert R₁ R₃ C V D A L
        decide

theorem Below.mono {U : List Term} {n m : Nat} (le : m ≤ n) (below : Below U n) : Below U m :=
  fun a b wa wb lt => below a b wa wb (by omega)

/-- Removing a BDD from another one that is not a node above it. -/
theorem remove_bdd_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : Below U (μ U a b)) : RemoveBddOk a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ resp => ?_, fun _ _ => NoLeaf.bot⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [eval_congr wb resp same]; simp
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₁, la, c₁, u₁, d₁, rfl⟩
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  have ha : head (.tuple #[.integer h₁, la, c₁, u₁, d₁]) = some la := by simp [head]
  have hb : head (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) = some lb := by simp [head]
  have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
  have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U (.tuple #[.integer h₁, la, c₁, u₁, d₁]) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  have lowerB : ∀ {a' b'}, (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) → High m a' ∧ High m b') →
      High lb a' ∧ High lb b' → μ U a' b' < μ U (.tuple #[.integer h₁, la, c₁, u₁, d₁]) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
    fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
  obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
  obtain ⟨hc₂, hu₂, hd₂⟩ := splitB.children wb
  obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
  obtain ⟨Hc₂, Hu₂, Hd₂⟩ := splitB.high wb
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt: remove the right BDD from each branch
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
        Bdd (Above ok la) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    have HB := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ _ (hc₁.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, hb'⟩) ⟨Hc₁, HB⟩)).2.2
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ _ (hu₁.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, hb'⟩) ⟨Hu₁, HB⟩)).2.2
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ _ (hd₁.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, hb'⟩) ⟨Hd₁, HB⟩)).2.2
    obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc₁ (raiseB wb))
      (keep₂ _ hu₁ (raiseB wb)) (keep₃ _ hd₁ (raiseB wb))
    refine ⟨.tuple #[.integer h₃, la, r₁, r₂, r₃], ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => NoLeaf.node.mpr ⟨nl₁ (NoLeaf.node.mp na).1 nb, nl₂ (NoLeaf.node.mp na).2.1 nb,
        nl₃ (NoLeaf.node.mp na).2.2 nb⟩⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      simp [Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», order, run₁, run₂, run₃, node]
    · obtain ⟨oc, ou, od⟩ := splitA.children oka
      exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc (raiseB okb),
        keep₂ _ ou (raiseB okb), keep₃ _ od (raiseB okb)⟩
    · have s₁ := sem₁ ρ resp
      have s₂ := sem₂ ρ resp
      have s₃ := sem₃ ρ resp
      simp only [eval_node] at s₁ s₂ s₃ ⊢
      revert s₁ s₂ s₃
      generalize ρ la = L
      generalize ρ lb = L'
      generalize eval ρ c₂ = C₂
      generalize eval ρ u₂ = U₂
      generalize eval ρ d₂ = D₂
      generalize eval ρ c₁ = C₁
      generalize eval ρ u₁ = U₁
      generalize eval ρ d₁ = D₁
      generalize eval ρ r₁ = R₁
      generalize eval ρ r₂ = R₂
      generalize eval ρ r₃ = R₃
      revert L L' C₂ U₂ D₂ C₁ U₁ D₁ R₁ R₂ R₃
      decide
  · -- eq: remove each branch, and the union branch of the right BDD
    obtain ⟨x₁, runx₁, keepx₁, semx₁, nlx₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
        ⟨Hc₁, Hc₂.congr order⟩)).2.1
    obtain ⟨x₂, runx₂, keepx₂, semx₂, nlx₂⟩ := (ih x₁ u₂ (keepx₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
      (hu₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨keepx₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
        (High.split splitB wb hb').2.1⟩) ⟨keepx₁ _ Hc₁ (Hc₂.congr order), Hu₂.congr order⟩)).2.1
    obtain ⟨y₁, runy₁, keepy₁, semy₁, nly₁⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, (High.split splitB wb hb').2.2⟩)
        ⟨Hd₁, Hd₂.congr order⟩)).2.1
    obtain ⟨y₂, runy₂, keepy₂, semy₂, nly₂⟩ := (ih y₁ u₂ (keepy₁ _ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1))
      (hu₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨keepy₁ _ (High.split splitA wa ha').2.2 (High.split splitB wb hb').2.2,
        (High.split splitB wb hb').2.1⟩) ⟨keepy₁ _ Hd₁ (Hd₂.congr order), Hu₂.congr order⟩)).2.1
    have bx := keepx₂ _ (keepx₁ _ hc₁ (hc₂.congr order)) (hu₂.congr order)
    have byy := keepy₂ _ (keepy₁ _ hd₁ (hd₂.congr order)) (hu₂.congr order)
    obtain ⟨h₃, node⟩ := node_new la x₂ u₁ y₂ (head_leaf wa ha) bx hu₁ byy
    refine ⟨.tuple #[.integer h₃, la, x₂, u₁, y₂], ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => NoLeaf.node.mpr ⟨nlx₂ (nlx₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1) (NoLeaf.node.mp nb).2.1,
        (NoLeaf.node.mp na).2.1, nly₂ (nly₁ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2) (NoLeaf.node.mp nb).2.1⟩⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      simp [Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», Erlang.erlang.«>/2», order,
        runx₁, runx₂, runy₁, runy₂, node]
    · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
      obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
      exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha,
        keepx₂ _ (keepx₁ _ oc₁ (oc₂.congr order)) (ou₂.congr order), ou₁,
        keepy₂ _ (keepy₁ _ od₁ (od₂.congr order)) (ou₂.congr order)⟩
    · have s₁ := semx₁ ρ resp
      have s₂ := semx₂ ρ resp
      have s₃ := semy₁ ρ resp
      have s₄ := semy₂ ρ resp
      have l := resp _ _ order
      simp only [eval_node]
      revert s₁ s₂ s₃ s₄ l
      generalize ρ la = L
      generalize ρ lb = L'
      generalize eval ρ c₂ = C₂
      generalize eval ρ u₂ = U₂
      generalize eval ρ d₂ = D₂
      generalize eval ρ c₁ = C₁
      generalize eval ρ u₁ = U₁
      generalize eval ρ d₁ = D₁
      generalize eval ρ x₁ = X₁
      generalize eval ρ x₂ = X₂
      generalize eval ρ y₁ = Y₁
      generalize eval ρ y₂ = Y₂
      revert L L' C₂ U₂ D₂ C₁ U₁ D₁ X₁ X₂ Y₁ Y₂
      decide
  · -- gt: what the right BDD always removes
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h₁, la, c₁, u₁, d₁]) →
        Bdd (Above ok lb) (.tuple #[.integer h₁, la, c₁, u₁, d₁]) :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    have HA := (raiseA wa).mono fun _ h => h.2
    obtain ⟨r, run, keep, sem, nl⟩ := (ih _ u₂ wa (hu₂.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split splitB wb hb').2.1⟩) ⟨HA, Hu₂⟩)).2.1
    refine ⟨r, ?_, fun ok oka okb => keep ok oka ((splitB.children okb).2.1.mono fun _ h => h.1),
      fun ρ resp => ?_, fun na nb => nl na (NoLeaf.node.mp nb).2.1⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      have notLt : Term.compare (Term.fuel la lb) la lb ≠ .lt := by rw [order]; decide
      simp [Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», Erlang.erlang.«>/2», order, run]
    · have s := sem ρ resp
      rw [eval_node]
      revert s
      generalize eval ρ (.tuple #[.integer h₁, la, c₁, u₁, d₁]) = A
      generalize ρ lb = L
      generalize eval ρ c₂ = C₂
      generalize eval ρ u₂ = U₂
      generalize eval ρ d₂ = D₂
      generalize eval ρ r = R
      revert A L C₂ U₂ D₂ R
      decide

/-- Removing a BDD from another one. -/
theorem remove_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : Below U (μ U a b)) : RemoveOkN a b := by
  rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
    simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
  · refine ⟨a, ?_, fun _ oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
  · -- removing a leaf
    have leafRun : Elixir.Module.Types.Descr.«bdd_remove/2» a (.tuple #[.integer k, x, y]) =
        Elixir.Module.Types.Descr.«bdd_remove_leaf/2» a (.tuple #[.integer k, x, y]) := by
      simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
    have fallback : ¬(∃ (h : Int) (la c u d : Term), a = .tuple #[.integer h, la, c, u, d] ∧
        compareExact (fuel (.tuple #[.integer k, x, y]) la) (.tuple #[.integer k, x, y]) la = .eq) → RemoveOkN a (.tuple #[.integer k, x, y]) := by
      intro notFirst
      have run : Elixir.Module.Types.Descr.«bdd_remove_leaf/2» a (.tuple #[.integer k, x, y]) =
          if compareExact (fuel (.tuple #[.integer k, x, y]) a) (.tuple #[.integer k, x, y]) a = .eq then .ok (.atom "bdd_bot") else .ok a := by
        unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
        rcases wa.shape with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨h, la, c, u, d, rfl⟩
        · by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.atom "bdd_top")) (.tuple #[.integer k, x, y]) (.atom "bdd_top") = .eq <;>
            simp [Erlang.erlang.«=:=/2», same]
        · by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.atom "bdd_bot")) (.tuple #[.integer k, x, y]) (.atom "bdd_bot") = .eq <;>
            simp [Erlang.erlang.«=:=/2», same]
        · rename_i k' x' y'
          by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.tuple #[.integer k', x', y'])) (.tuple #[.integer k, x, y]) (.tuple #[.integer k', x', y']) = .eq <;>
            simp [Erlang.erlang.«=:=/2», same]
        · have ne : ¬compareExact (fuel (.tuple #[.integer k, x, y]) la) (.tuple #[.integer k, x, y]) la = .eq := fun e => notFirst ⟨h, la, c, u, d, rfl, e⟩
          by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.tuple #[.integer h, la, c, u, d])) (.tuple #[.integer k, x, y]) (.tuple #[.integer h, la, c, u, d]) = .eq <;>
            simp [Erlang.erlang.«=:=/2», same, ne]
      by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) a) (.tuple #[.integer k, x, y]) a = .eq
      · refine ⟨.atom "bdd_bot", by rw [leafRun, run, ite_eq_left same], fun _ _ _ => Bdd.bot, fun ρ resp => ?_,
          fun _ _ => NoLeaf.bot⟩
        rw [eval_congr wb resp same]; simp
      · exact ⟨a, by rw [leafRun, run, ite_eq_right same], fun _ oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    by_cases first : ∃ (h : Int) (la c u d : Term), a = .tuple #[.integer h, la, c, u, d] ∧
        compareExact (fuel (.tuple #[.integer k, x, y]) la) (.tuple #[.integer k, x, y]) la = .eq
    · obtain ⟨h, la, c, u, d, rfl, e⟩ := first
      have ha : head (.tuple #[.integer h, la, c, u, d]) = some la := by simp [head]
      have splitA : Split _ la c u d := Or.inl ⟨h, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitA.children wa
      have wl : Bdd (· ∈ U) la := by
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        exact Bdd.leaf_iff.mpr (head_ok wa ha)
      have highLit : ∀ {m}, High m (.tuple #[.integer h, la, c, u, d]) → High m la := fun high => by
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        exact Bdd.leaf_iff.mpr (head_ok high ha)
      have okLit : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h, la, c, u, d]) → Bdd ok la := fun w => by
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        exact Bdd.leaf_iff.mpr (head_ok w ha)
      obtain ⟨r₁, run₁, keep₁, sem₁, -⟩ := union_step U la u wl (hu.mono fun _ h => h.1)
        (ih.mono (μ_le fun m ha' _ => ⟨highLit ha', (High.split splitA wa ha').2.1⟩))
      have wr₁ := keep₁ _ wl (hu.mono fun _ h => h.1)
      obtain ⟨r₂, run₂, keep₂, sem₂, -⟩ := union_step U r₁ d wr₁ (hd.mono fun _ h => h.1)
        (ih.mono (μ_le fun m ha' _ =>
          ⟨keep₁ _ (highLit ha') (High.split splitA wa ha').2.1, (High.split splitA wa ha').2.2⟩))
      refine ⟨r₂, ?_, fun ok oka _ => ?_, fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
      · rw [leafRun]
        unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
        simp [Erlang.erlang.«=:=/2», e, run₁, run₂]
      · obtain ⟨-, ou, od⟩ := splitA.children oka
        exact keep₂ ok (keep₁ ok (okLit oka) (ou.mono fun _ h => h.1)) (od.mono fun _ h => h.1)
      · have l : ρ (.tuple #[.integer k, x, y]) = ρ la := resp _ _ (compare_eq_of_compareExact_eq _ _ e)
        rw [sem₂ ρ resp, sem₁ ρ resp]
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        simp only [eval_node, eval_leaf, l]
        cases ρ (.tuple #[.integer k', x', y']) <;> simp [Bool.or_comm]
    · exact fallback first
  · have run : Elixir.Module.Types.Descr.«bdd_remove/2» a (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
        Elixir.Module.Types.Descr.«bdd_remove_bdd/2» a (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) := by
      simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
    obtain ⟨r, runr, keep, sem, nl⟩ := remove_bdd_step U a _ wa wb ih
    exact ⟨r, by rw [run, runr], keep, sem, nl⟩

/-- Every pair of BDDs over a universe unites and removes. -/
theorem below_all (U : List Term) : ∀ n, Below U n := by
  intro n
  induction n with
  | zero => intro a b _ _ lt; omega
  | succ n ih =>
    intro a b wa wb lt
    have ih' : Below U (μ U a b) := ih.mono (by omega)
    exact ⟨union_step U a b wa wb ih', remove_step U a b wa wb ih', remove_bdd_step U a b wa wb ih'⟩

theorem Bdd.and {p q : Term → Prop} {b : Term} (hp : Bdd p b) (hq : Bdd q b) :
    Bdd (fun t => p t ∧ q t) b := by
  revert hq
  refine Bdd.induction (P := fun p b => ∀ {q}, Bdd q b → Bdd (fun t => p t ∧ q t) b) ?_ ?_ ?_ ?_ p b hp
  · intro _ _ _; exact Bdd.top
  · intro _ _ _; exact Bdd.bot
  · intro _ k x y okp q hq; exact Bdd.leaf_iff.mpr ⟨okp, Bdd.leaf_iff.mp hq⟩
  · intro p h lit c u d leaf okp _ _ _ ic iu id q hq
    obtain ⟨-, okq, qc, qu, qd⟩ := Bdd.node_iff.mp hq
    refine Bdd.node_iff.mpr ⟨leaf, ⟨okp, okq⟩, ?_, ?_, ?_⟩
    · exact (ic qc).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩
    · exact (iu qu).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩
    · exact (id qd).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩

/-- The literals of a BDD. -/
def lits : Term → List Term
  | Term.tuple ⟨[_, lit, c, u, d]⟩ => lit :: (lits c ++ lits u ++ lits d)
  | .tuple ⟨[k, x, y]⟩ => [.tuple #[k, x, y]]
  | _ => []

-- Stated by `rfl`: the equation of the last clause of `lits` takes seconds to generate.
theorem lits_node (h lit c u d : Term) : lits (.tuple #[h, lit, c, u, d]) = lit :: (lits c ++ lits u ++ lits d) :=
  rfl

theorem lits_leaf (k x y : Term) : lits (.tuple #[k, x, y]) = [.tuple #[k, x, y]] := rfl

theorem Bdd.lits {ok : Term → Prop} {a : Term} (wa : Bdd ok a) : Bdd (· ∈ BddProofs.lits a) a := by
  refine Bdd.induction (P := fun _ a => Bdd (· ∈ BddProofs.lits a) a) ?_ ?_ ?_ ?_ ok a wa
  · intro _; exact Bdd.top
  · intro _; exact Bdd.bot
  · intro _ k x y _; exact Bdd.leaf_iff.mpr (by simp [lits_leaf])
  · intro _ h lit c u d leaf _ hc hu hd ic iu id
    refine Bdd.node_iff.mpr ⟨leaf, by simp [lits_node], ?_, ?_, ?_⟩
    · exact (Bdd.and ic hc).mono fun t ht => ⟨by simp [lits_node, ht.1], ht.2.2⟩
    · exact (Bdd.and iu hu).mono fun t ht => ⟨by simp [lits_node, ht.1], ht.2.2⟩
    · exact (Bdd.and id hd).mono fun t ht => ⟨by simp [lits_node, ht.1], ht.2.2⟩

theorem union_okN {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : UnionOkN a b :=
  let U := lits a ++ lits b
  (below_all U _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
    (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)).1

theorem union_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : UnionOk a b :=
  let ⟨r, run, keep, sem, _⟩ := union_okN wa wb
  ⟨r, run, keep, sem⟩

/-! Intersections. -/

/-- Nodes whose constrained and dual branches are equal collapse into a union. -/
theorem post_spec (lit r₁ r₂ r₃ : Term) (h : Int) {okU : Term → Prop}
    (w₁ : Bdd okU r₁) (w₂ : Bdd okU r₂) (w₃ : Bdd okU r₃) :
    ∃ r, (if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
        else .ok (.tuple #[.integer h, lit, r₁, r₂, r₃])) = .ok r ∧
      (∀ ok : Term → Prop, IsLeaf lit → ok lit → Bdd (Above ok lit) r₁ → Bdd (Above ok lit) r₂ →
        Bdd (Above ok lit) r₃ → Bdd ok r) ∧
      (∀ ρ, Resp ρ → eval ρ r = ((ρ lit && eval ρ r₁) || eval ρ r₂ || (!ρ lit && eval ρ r₃))) ∧
      (NoLeaf r₁ → NoLeaf r₂ → NoLeaf r₃ → NoLeaf r) := by
  by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
  · obtain ⟨r, run, keep, sem, nl⟩ := union_okN w₁ w₂
    refine ⟨r, by rw [ite_eq_left_of_eq_true _ _ (eq_true post), run], fun ok _ _ o₁ o₂ _ =>
      keep ok (o₁.mono fun _ h => h.1) (o₂.mono fun _ h => h.1), fun ρ resp => ?_, fun n₁ n₂ _ => nl n₁ n₂⟩
    rw [sem ρ resp, eval_congr w₃ resp post]
    cases ρ lit <;> cases eval ρ r₁ <;> simp
  · exact ⟨_, ite_eq_right_of_eq_false _ _ (eq_false post), fun ok leaf okl o₁ o₂ o₃ =>
      Bdd.node_iff.mpr ⟨leaf, okl, o₁, o₂, o₃⟩, fun ρ _ => eval_node ρ _ _ _ _ _,
      fun n₁ n₂ n₃ => NoLeaf.node.mpr ⟨n₁, n₂, n₃⟩⟩

theorem same_lit_bool (x y : Term) :
    Elixir.Module.Types.Descr.«same_lit?/2» x y = .ok (.atom "true") ∨
      Elixir.Module.Types.Descr.«same_lit?/2» x y = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«same_lit?/2»
  split
  · simp only [Lynx.Except.guard, Erlang.erlang.«=:=/2», Lynx.Except.tryWith, equalExact_eq_decide]
    split <;> simp
  · simp

theorem orElse_bool {x y : Except Exception Term}
    (hx : x = .ok (.atom "true") ∨ x = .ok (.atom "false")) (hy : y = .ok (.atom "true") ∨ y = .ok (.atom "false")) :
    Lynx.Except.orElse x y Bool.true = .ok (.atom "true") ∨ Lynx.Except.orElse x y Bool.true = .ok (.atom "false") := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [Lynx.Except.orElse]

def InterOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a && eval ρ b)

def InterOkN (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → eval ρ r = (eval ρ a && eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

theorem inter_eq_spec {okU : Term → Prop} (cd₁ cd₂ u₁ u₂ : Term) (w₁ : Bdd okU cd₁) (w₂ : Bdd okU cd₂)
    (w₃ : Bdd okU u₁) (w₄ : Bdd okU u₂) (i₁ : InterOkN cd₁ cd₂) (i₂ : InterOkN cd₁ u₂) (i₃ : InterOkN u₁ cd₂) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_intersection_eq/4» cd₁ cd₂ u₁ u₂ = .ok r ∧
      (∀ ok, Bdd ok cd₁ → Bdd ok cd₂ → Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
      (∀ ρ, Resp ρ → eval ρ r = ((eval ρ cd₁ && eval ρ cd₂) || (eval ρ cd₁ && eval ρ u₂) ||
        (eval ρ u₁ && eval ρ cd₂))) ∧ (NoLeaf cd₁ → NoLeaf cd₂ → NoLeaf u₁ → NoLeaf u₂ → NoLeaf r) := by
  obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := i₁
  obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := i₂
  obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := i₃
  by_cases top : r₁ = .atom "bdd_top"
  · subst top
    refine ⟨.atom "bdd_top", ?_, fun _ _ _ _ _ => Bdd.top, fun ρ resp => ?_, fun _ _ _ _ => NoLeaf.top⟩
    · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
      simp [run₁]
    · have := sem₁ ρ resp
      simp at this
      simp [this]
  · obtain ⟨r₄, run₄, keep₄, sem₄, nl₄⟩ := union_okN (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂)
    obtain ⟨r, runr, keepr, semr, nlr⟩ := union_okN (keep₁ _ w₁ w₂) (keep₄ _ (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂))
    refine ⟨r, ?_, fun ok o₁ o₂ o₃ o₄ => keepr ok (keep₁ ok o₁ o₂)
      (keep₄ ok (keep₂ ok o₁ o₄) (keep₃ ok o₃ o₂)), fun ρ resp => ?_,
      fun n₁ n₂ n₃ n₄ => nlr (nl₁ n₁ n₂) (nl₄ (nl₂ n₁ n₄) (nl₃ n₃ n₂))⟩
    · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
      simp only [run₁, Lynx.Except.ok_bind]
      simp [run₂, run₃, run₄, runr]
    · rw [semr ρ resp, sem₄ ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp]
      simp [Bool.or_assoc]

def BelowI (U : List Term) (n : Nat) : Prop :=
  ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → InterOkN a b

theorem inter_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : BelowI U (μ U a b)) : InterOkN a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_, fun na _ => na⟩
    · unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [← eval_congr wb resp same]; simp
  by_cases ta : a = .atom "bdd_top"
  · subst ta
    refine ⟨b, ?_, fun ok _ okb => okb, fun ρ _ => by simp, fun _ nb => nb⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases tb : b = .atom "bdd_top"
  · subst tb
    refine ⟨a, ?_, fun ok oka _ => oka, fun ρ _ => by simp, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fa : a = .atom "bdd_bot"
  · subst fa
    refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fb : b = .atom "bdd_bot"
  · subst fb
    refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
  obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt
    obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    obtain ⟨hc, hu, hd⟩ := split.children wa
    obtain ⟨Hc, Hu, Hd⟩ := split.high wa
    have HB : High la b := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := ih c₁ b (hc.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := ih u₁ b (hu.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := ih d₁ b (hd.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)
    have w₁ := keep₁ _ hc (raiseB wb)
    have w₂ := keep₂ _ hu (raiseB wb)
    have w₃ := keep₃ _ hd (raiseB wb)
    obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
    obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ r₂ r₃ h₁ w₁ w₂ w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => nl (nl₁ (split.noLeaf na).1 nb) (nl₂ (split.noLeaf na).2.1 nb) (nl₃ (split.noLeaf na).2.2 nb)⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children oka
      exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc (raiseB okb)) (keep₂ _ ou (raiseB okb))
        (keep₃ _ od (raiseB okb))
    · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
      cases ρ la <;> cases eval ρ b <;> simp
  · -- eq
    have run := compare_eq ha hb order
    have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
    rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
      rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
    · -- two leaves
      refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
      · unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Erlang.erlang.«=:=/2», same, run]
      · simp [sameLit ρ resp]
    · -- a leaf below a node
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitB.children wb
      obtain ⟨r₁, run₁, keep₁, sem₁⟩ := union_ok hc hu
      have w₁ := keep₁ _ hc hu
      obtain ⟨h₃, node⟩ := node_new lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wb hb) w₁
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, node]
        by_cases post : compareExact (fuel (.atom "bdd_bot") r₁) (.atom "bdd_bot") r₁ = .eq <;> simp [post]
      · obtain ⟨oc, ou, -⟩ := splitB.children okb
        exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ oc ou) Bdd.bot Bdd.bot
      · rw [sem ρ resp, sem₁ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, sameLit ρ resp]
        cases ρ lb <;> simp
    · -- a node above a leaf
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitA.children wa
      obtain ⟨r₁, run₁, keep₁, sem₁⟩ := union_ok hc hu
      have w₁ := keep₁ _ hc hu
      obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wa ha) w₁
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, node]
        by_cases post : compareExact (fuel (.atom "bdd_bot") r₁) (.atom "bdd_bot") r₁ = .eq <;> simp [post]
      · obtain ⟨oc, ou, -⟩ := splitA.children oka
        exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc ou) Bdd.bot Bdd.bot
      · rw [sem ρ resp, sem₁ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, ← sameLit ρ resp]
        cases ρ la <;> simp
    · -- two nodes
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
      obtain ⟨hc₂', hu₂', hd₂'⟩ := splitB.children wb
      have hc₂ := hc₂'.congr order
      have hu₂ := hu₂'.congr order
      have hd₂ := hd₂'.congr order
      obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
      have Hc₂ := (splitB.high wb).1.congr order
      have Hu₂ := (splitB.high wb).2.1.congr order
      have Hd₂ := (splitB.high wb).2.2.congr order
      have mA := fun m (ha' : High m _) => High.split splitA wa ha'
      have mB := fun m (hb' : High m _) => High.split splitB wb hb'
      have U' : ∀ {x : Term}, Bdd (Above (· ∈ U) la) x → Bdd (· ∈ U) x := fun w => w.mono fun _ h => h.1
      have pair : ∀ {x y : Term}, Bdd (Above (· ∈ U) la) x → Bdd (Above (· ∈ U) la) y → High la x → High la y →
          (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
            High m x ∧ High m y) → InterOkN x y :=
        fun wx wy hx hy mono => ih _ _ (U' wx) (U' wy) (lower mono ⟨hx, hy⟩)
      have bool : ∀ ρ, Resp ρ → ρ lb = ρ la := fun ρ resp => (sameLit ρ resp).symm
      by_cases su : compareExact (fuel u₂ u₁) u₂ u₁ = .eq
      · obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
        obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
        have w₁ := keep₁ _ hc₁ hc₂
        have w₃ := keep₃ _ hd₁ hd₂
        obtain ⟨h₃, node⟩ := node_new la r₁ u₁ r₃ (head_leaf wa ha) w₁ hu₁ w₃
        obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ u₁ r₃ h₃ w₁ hu₁ w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => nl
          (nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1) (NoLeaf.node.mp na).2.1
          (nl₃ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2)⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
          simp [Erlang.erlang.«=:=/2», same, run, su, run₁, run₃, node]
          by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, -, od₂⟩ := splitB.children okb
          exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc₁ (oc₂.congr order)) ou₁
            (keep₃ _ od₁ (od₂.congr order))
        · have eu := eval_congr (hu₂'.mono fun _ h => h.1) resp su
          rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp]
          simp only [eval_node, bool ρ resp, eu]
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          revert L C₁ C₂ D₁ D₂ U₁
          decide
      · rcases orElse_bool (same_lit_bool c₁ c₂) (same_lit_bool d₁ d₂) with so | so
        · -- equal literals below: intersect the branches with each other's unions
          obtain ⟨i₁, ri₁, ki₁, si₁, ni₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
          obtain ⟨i₂, ri₂, ki₂, si₂, ni₂⟩ := pair hc₁ hu₂ Hc₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').2.1⟩
          obtain ⟨i₃, ri₃, ki₃, si₃, ni₃⟩ := pair hu₁ hc₂ Hu₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').1⟩
          obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := inter_eq_spec c₁ c₂ u₁ u₂ hc₁ hc₂ hu₁ hu₂
            ⟨i₁, ri₁, ki₁, si₁, ni₁⟩ ⟨i₂, ri₂, ki₂, si₂, ni₂⟩ ⟨i₃, ri₃, ki₃, si₃, ni₃⟩
          obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := pair hu₁ hu₂ Hu₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.1⟩
          obtain ⟨j₁, rj₁, kj₁, sj₁, nj₁⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
          obtain ⟨j₂, rj₂, kj₂, sj₂, nj₂⟩ := pair hd₁ hu₂ Hd₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.1⟩
          obtain ⟨j₃, rj₃, kj₃, sj₃, nj₃⟩ := pair hu₁ hd₂ Hu₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.2⟩
          obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := inter_eq_spec d₁ d₂ u₁ u₂ hd₁ hd₂ hu₁ hu₂
            ⟨j₁, rj₁, kj₁, sj₁, nj₁⟩ ⟨j₂, rj₂, kj₂, sj₂, nj₂⟩ ⟨j₃, rj₃, kj₃, sj₃, nj₃⟩
          have w₁ := keep₁ _ hc₁ hc₂ hu₁ hu₂
          have w₂ := keep₂ _ hu₁ hu₂
          have w₃ := keep₃ _ hd₁ hd₂ hu₁ hu₂
          obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
          obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ r₂ r₃ h₃ w₁ w₂ w₃
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => by
            obtain ⟨c₁', u₁', d₁'⟩ := NoLeaf.node.mp na
            obtain ⟨c₂', u₂', d₂'⟩ := NoLeaf.node.mp nb
            exact nl (nl₁ c₁' c₂' u₁' u₂') (nl₂ u₁' u₂') (nl₃ d₁' d₂' u₁' u₂')⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
            simp [Erlang.erlang.«=:=/2», same, run, su, so, isMember, run₁, run₂, run₃, node]
            by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
          · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
            obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
            exact keep ok (head_leaf wa ha) (head_ok oka ha)
              (keep₁ _ oc₁ (oc₂.congr order) ou₁ (ou₂.congr order)) (keep₂ _ ou₁ (ou₂.congr order))
              (keep₃ _ od₁ (od₂.congr order) ou₁ (ou₂.congr order))
          · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp]
            simp only [eval_node, bool ρ resp]
            generalize ρ la = L
            generalize eval ρ c₁ = C₁
            generalize eval ρ c₂ = C₂
            generalize eval ρ d₁ = D₁
            generalize eval ρ d₂ = D₂
            generalize eval ρ u₁ = U₁
            generalize eval ρ u₂ = U₂
            revert L C₁ C₂ D₁ D₂ U₁ U₂
            decide
        · -- intersect the unions of each side
          obtain ⟨x, rx, kx, sx, nx⟩ := union_okN hc₁ hu₁
          obtain ⟨y, ry, ky, sy, ny⟩ := union_okN hc₂ hu₂
          obtain ⟨x', rx', kx', sx', nx'⟩ := union_okN hd₁ hu₁
          obtain ⟨y', ry', ky', sy', ny'⟩ := union_okN hd₂ hu₂
          obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := pair (kx _ hc₁ hu₁) (ky _ hc₂ hu₂) (kx _ Hc₁ Hu₁) (ky _ Hc₂ Hu₂)
            fun m ha' hb' => ⟨kx _ (mA m ha').1 (mA m ha').2.1, ky _ (mB m hb').1 (mB m hb').2.1⟩
          obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := pair (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂) (kx' _ Hd₁ Hu₁) (ky' _ Hd₂ Hu₂)
            fun m ha' hb' => ⟨kx' _ (mA m ha').2.2 (mA m ha').2.1, ky' _ (mB m hb').2.2 (mB m hb').2.1⟩
          have w₁ := keep₁ _ (kx _ hc₁ hu₁) (ky _ hc₂ hu₂)
          have w₃ := keep₃ _ (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂)
          obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
            (Bdd.bot (ok := fun _ => True)) w₃
          obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => by
            obtain ⟨c₁', u₁', d₁'⟩ := NoLeaf.node.mp na
            obtain ⟨c₂', u₂', d₂'⟩ := NoLeaf.node.mp nb
            exact nl (nl₁ (nx c₁' u₁') (ny c₂' u₂')) NoLeaf.bot (nl₃ (nx' d₁' u₁') (ny' d₂' u₂'))⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
            simp [Erlang.erlang.«=:=/2», same, run, su, so, isMember, rx, ry, rx', ry',
              run₁, run₃, node]
            by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
          · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
            obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
            exact keep ok (head_leaf wa ha) (head_ok oka ha)
              (keep₁ _ (kx _ oc₁ ou₁) (ky _ (oc₂.congr order) (ou₂.congr order))) Bdd.bot
              (keep₃ _ (kx' _ od₁ ou₁) (ky' _ (od₂.congr order) (ou₂.congr order)))
          · rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp, sx ρ resp, sy ρ resp, sx' ρ resp, sy' ρ resp]
            simp only [eval_node, eval_bot, bool ρ resp]
            generalize ρ la = L
            generalize eval ρ c₁ = C₁
            generalize eval ρ c₂ = C₂
            generalize eval ρ d₁ = D₁
            generalize eval ρ d₂ = D₂
            generalize eval ρ u₁ = U₁
            generalize eval ρ u₂ = U₂
            revert L C₁ C₂ D₁ D₂ U₁ U₂
            decide
  · -- gt
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    obtain ⟨hc, hu, hd⟩ := split.children wb
    obtain ⟨Hc, Hu, Hd⟩ := split.high wb
    have HA : High lb a := (raiseA wa).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := ih a c₂ wa (hc.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').1⟩) ⟨HA, Hc⟩)
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := ih a u₂ wa (hu.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := ih a d₂ wa (hd.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.2⟩) ⟨HA, Hd⟩)
    have w₁ := keep₁ _ (raiseA wa) hc
    have w₂ := keep₂ _ (raiseA wa) hu
    have w₃ := keep₃ _ (raiseA wa) hd
    obtain ⟨h₁, node⟩ := node_new lb r₁ r₂ r₃ (head_leaf wb hb) w₁ w₂ w₃
    obtain ⟨r, runr, keep, sem, nl⟩ := post_spec lb r₁ r₂ r₃ h₁ w₁ w₂ w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => nl (nl₁ na (split.noLeaf nb).1) (nl₂ na (split.noLeaf nb).2.1) (nl₃ na (split.noLeaf nb).2.2)⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children okb
      exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ (raiseA oka) oc) (keep₂ _ (raiseA oka) ou)
        (keep₃ _ (raiseA oka) od)
    · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
      cases ρ lb <;> cases eval ρ a <;> simp

theorem belowI_all (U : List Term) : ∀ n, BelowI U n := by
  intro n
  induction n with
  | zero => intro a b _ _ lt; omega
  | succ n ih =>
    intro a b wa wb lt
    exact inter_step U a b wa wb fun a' b' wa' wb' lt' => ih a' b' wa' wb' (by omega)

theorem inter_okN {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : InterOkN a b :=
  belowI_all (lits a ++ lits b) _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
    (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)

theorem inter_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : InterOk a b :=
  let ⟨r, run, keep, sem, _⟩ := inter_okN wa wb
  ⟨r, run, keep, sem⟩

/-! Negations. -/

def NegOk (b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok r ∧ (∀ ok, Bdd ok b → Bdd ok r) ∧
    ∀ ρ, Resp ρ → eval ρ r = !eval ρ b

/-- Negations, which never have leaves. -/
def NegOkN (b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok r ∧ (∀ ok, Bdd ok b → Bdd ok r) ∧
    (∀ ρ, Resp ρ → eval ρ r = !eval ρ b) ∧ NoLeaf r

theorem neg_okN {ok₀ : Term → Prop} {b : Term} (wb : Bdd ok₀ b) : NegOkN b := by
  refine Bdd.induction (P := fun _ b => NegOkN b) ?_ ?_ ?_ ?_ ok₀ b wb
  · intro _
    exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.bot,
      fun ρ _ => by simp, NoLeaf.bot⟩
  · intro _
    exact ⟨.atom "bdd_top", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.top,
      fun ρ _ => by simp, NoLeaf.top⟩
  · intro ok k x y okl
    obtain ⟨h, node⟩ := node_new (.tuple #[.integer k, x, y]) (.atom "bdd_bot") (.atom "bdd_bot")
      (.atom "bdd_top") ⟨k, x, y, rfl⟩ (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      (Bdd.top (ok := fun _ => True))
    refine ⟨.tuple #[.integer h, .tuple #[.integer k, x, y], .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"],
      by simp [Elixir.Module.Types.Descr.«bdd_negation/1», node], fun ok' w => ?_, fun ρ _ => ?_,
      NoLeaf.node.mpr ⟨NoLeaf.bot, NoLeaf.bot, NoLeaf.top⟩⟩
    · exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, Bdd.leaf_iff.mp w, Bdd.bot, Bdd.bot, Bdd.top⟩
    · cases ρ (.tuple #[.integer k, x, y]) <;> simp
  · intro ok h lit c u d leaf okl hc hu hd ⟨nc, runc, keepc, semc, nlc⟩ ⟨nu, runu, keepu, semu, nlu⟩
      ⟨nd, rund, keepd, semd, nld⟩
    have wnc := keepc _ hc
    have wnd := keepd _ hd
    obtain ⟨h₁, inner⟩ := node_new lit nc (.atom "bdd_bot") nd leaf wnc (Bdd.bot (ok := fun _ => True)) wnd
    have winner : Bdd ok (.tuple #[.integer h₁, lit, nc, .atom "bdd_bot", nd]) :=
      Bdd.node_iff.mpr ⟨leaf, okl, wnc, Bdd.bot, wnd⟩
    have wnu : Bdd ok nu := (keepu _ hu).mono fun _ h => h.1
    obtain ⟨i, runi, keepi, semi, nli⟩ := inter_okN winner wnu
    have wi := keepi _ winner wnu
    have ni : NoLeaf i := nli (NoLeaf.node.mpr ⟨nlc, NoLeaf.bot, nld⟩) nlu
    -- the result before and after the final simplification
    have final : ∃ r, (∀ ok', Bdd ok' (.tuple #[.integer h, lit, c, u, d]) → Bdd ok' r) ∧
        (∀ ρ, Resp ρ → eval ρ r = eval ρ i) ∧
        Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, lit, c, u, d]) = .ok r ∧ NoLeaf r := by
      have keepI : ∀ ok', Bdd ok' (.tuple #[.integer h, lit, c, u, d]) → Bdd ok' i := fun ok' w => by
        obtain ⟨-, okl', oc, ou, od⟩ := Bdd.node_iff.mp w
        exact keepi ok' (Bdd.node_iff.mpr ⟨leaf, okl', keepc _ oc, Bdd.bot, keepd _ od⟩)
          ((keepu _ ou).mono fun _ h => h.1)
      rcases wi.shape with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨hi, li, c', u', d', rfl⟩
      · refine ⟨_, keepI, fun _ _ => rfl, ?_, ni⟩
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
        rfl
      · refine ⟨_, keepI, fun _ _ => rfl, ?_, ni⟩
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
        rfl
      · refine ⟨_, keepI, fun _ _ => rfl, ?_, ni⟩
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
        rfl
      · have base : Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, lit, c, u, d]) =
            if compareExact (fuel d' c') d' c' = .eq then Elixir.Module.Types.Descr.«bdd_union/2» u' c'
            else .ok (.tuple #[.integer hi, li, c', u', d']) := by
          conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
          simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
          by_cases e : compareExact (fuel d' c') d' c' = .eq <;> simp [Erlang.erlang.«=:=/2», e]
        by_cases e : compareExact (fuel d' c') d' c' = .eq
        · obtain ⟨-, -, wc', wu', wd'⟩ := Bdd.node_iff.mp wi
          obtain ⟨r, runr, keepr, semr, nlr⟩ := union_okN wu' wc'
          refine ⟨r, fun ok' w => ?_, fun ρ resp => ?_, by rw [base, ite_eq_left e, runr],
            nlr (NoLeaf.node.mp ni).2.1 (NoLeaf.node.mp ni).1⟩
          · obtain ⟨-, -, oc', ou', -⟩ := Bdd.node_iff.mp (keepI ok' w)
            exact keepr ok' (ou'.mono fun _ h => h.1) (oc'.mono fun _ h => h.1)
          · rw [semr ρ resp, eval_node, eval_congr wd' resp e]
            cases ρ li <;> cases eval ρ c' <;> simp
        · exact ⟨_, keepI, fun _ _ => rfl, by rw [base, ite_eq_right e], ni⟩
    obtain ⟨r, keepr, semr, runr, nlr⟩ := final
    refine ⟨r, runr, keepr, fun ρ resp => ?_, nlr⟩
    rw [semr ρ resp, semi ρ resp, eval_node, eval_node, semc ρ resp, semd ρ resp, semu ρ resp]
    cases ρ lit <;> cases eval ρ c <;> cases eval ρ u <;> cases eval ρ d <;> simp

theorem neg_ok {ok₀ : Term → Prop} {b : Term} (wb : Bdd ok₀ b) : NegOk b :=
  let ⟨r, run, keep, sem, _⟩ := neg_okN wb
  ⟨r, run, keep, sem⟩

/-! Differences. -/

theorem tuple3_cmp {a₀ a₁ a₂ b : Term} (e : Term.compare (Term.fuel (.tuple #[a₀, a₁, a₂]) b) (.tuple #[a₀, a₁, a₂]) b = .eq) :
    ∃ b₀ b₁ b₂, b = .tuple #[b₀, b₁, b₂] ∧ Term.compare (Term.fuel a₀ b₀) a₀ b₀ = .eq ∧ Term.compare (Term.fuel a₁ b₁) a₁ b₁ = .eq ∧
      Term.compare (Term.fuel a₂ b₂) a₂ b₂ = .eq := by
  rw [compare_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, rest⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, rfl, e.1, e.2.1, e.2.2⟩

theorem tuple5_cmp {a₀ a₁ a₂ a₃ a₄ b : Term} (e : Term.compare (Term.fuel (.tuple #[a₀, a₁, a₂, a₃, a₄]) b) (.tuple #[a₀, a₁, a₂, a₃, a₄]) b = .eq) :
    ∃ b₀ b₁ b₂ b₃ b₄, b = .tuple #[b₀, b₁, b₂, b₃, b₄] ∧ Term.compare (Term.fuel a₁ b₁) a₁ b₁ = .eq ∧
      Term.compare (Term.fuel a₂ b₂) a₂ b₂ = .eq ∧ Term.compare (Term.fuel a₃ b₃) a₃ b₃ = .eq ∧ Term.compare (Term.fuel a₄ b₄) a₄ b₄ = .eq := by
  rw [compare_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, rest⟩⟩⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, b₃, b₄, rfl, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2⟩

/-- Equal BDDs have the same semantics. -/
theorem eval_congr_cmp {ok : Term → Prop} {a : Term} (wa : Bdd ok a) {ρ : Term → Bool} (resp : Resp ρ) :
    ∀ {b}, Term.compare (Term.fuel a b) a b = .eq → eval ρ a = eval ρ b := by
  refine Bdd.induction (P := fun _ a => ∀ {b}, Term.compare (Term.fuel a b) a b = .eq → eval ρ a = eval ρ b)
    ?_ ?_ ?_ ?_ ok a wa
  · intro _ b e
    obtain rfl := (compare_eq_atom b "bdd_top").mp (Lynx.Term.compare_eq_symm e)
    rfl
  · intro _ b e
    obtain rfl := (compare_eq_atom b "bdd_bot").mp (Lynx.Term.compare_eq_symm e)
    rfl
  · intro _ k x y _ b e
    obtain ⟨b₀, b₁, b₂, rfl, -, -, -⟩ := tuple3_cmp e
    simp only [eval_leaf]
    exact resp _ _ e
  · intro _ h lit c u d _ _ _ _ _ ihc ihu ihd b e
    obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl, el, ec, eu, ed⟩ := tuple5_cmp e
    simp only [eval_node]
    rw [resp _ _ el, ihc ec, ihu eu, ihd ed]

def DiffOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_difference/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a && !eval ρ b)

def BelowD (U : List Term) (n : Nat) : Prop :=
  ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → DiffOk a b

theorem diff_union_spec {okU : Term → Prop} {i u₁ u₂ : Term} (wu₁ : Bdd okU u₁) (wu₂ : Bdd okU u₂)
    (diff : ∀ u, Elixir.Module.Types.Descr.«bdd_union/2» u₁ u₂ = .ok u → DiffOk i u) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_difference_union/3» i u₁ u₂ = .ok r ∧
      (∀ ok, Bdd ok i → Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
      ∀ ρ, Resp ρ → eval ρ r = (eval ρ i && !(eval ρ u₁ || eval ρ u₂)) := by
  by_cases bot : i = .atom "bdd_bot"
  · subst bot
    exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«bdd_difference_union/3»; rfl,
      fun _ _ _ _ => Bdd.bot, fun _ _ => by simp⟩
  obtain ⟨u, runU, keepU, semU⟩ := union_ok wu₁ wu₂
  obtain ⟨r, run, keep, sem⟩ := diff u runU
  refine ⟨r, ?_, fun ok oi o₁ o₂ => keep ok oi (keepU ok o₁ o₂), fun ρ resp => by rw [sem ρ resp, semU ρ resp]⟩
  unfold Elixir.Module.Types.Descr.«bdd_difference_union/3»
  split
  · exact absurd rfl bot
  · simp [runU, run]

theorem neg_union_spec {okU : Term → Prop} {u₁ u₂ : Term} (wu₁ : Bdd okU u₁) (wu₂ : Bdd okU u₂) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_negation_union/2» u₁ u₂ = .ok r ∧
      (∀ ok, Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
      ∀ ρ, Resp ρ → eval ρ r = !(eval ρ u₁ || eval ρ u₂) := by
  obtain ⟨n₁, run₁, keep₁, sem₁⟩ := neg_ok wu₁
  obtain ⟨n₂, run₂, keep₂, sem₂⟩ := neg_ok wu₂
  obtain ⟨r, run, keep, sem⟩ := inter_ok (keep₁ _ wu₁) (keep₂ _ wu₂)
  refine ⟨r, by simp [Elixir.Module.Types.Descr.«bdd_negation_union/2», run₁, run₂, run],
    fun ok o₁ o₂ => keep ok (keep₁ ok o₁) (keep₂ ok o₂), fun ρ resp => ?_⟩
  rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp]
  cases eval ρ u₁ <;> cases eval ρ u₂ <;> rfl

theorem diff_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : BelowD U (μ U a b)) : DiffOk a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ resp => ?_⟩
    · unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [eval_congr wb resp same]; simp
  by_cases tb : b = .atom "bdd_top"
  · subst tb
    refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fa : a = .atom "bdd_bot"
  · subst fa
    refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fb : b = .atom "bdd_bot"
  · subst fb
    refine ⟨a, ?_, fun _ oka _ => oka, fun ρ _ => by simp⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases ta : a = .atom "bdd_top"
  · subst ta
    obtain ⟨r, run, keep, sem⟩ := neg_ok wb
    refine ⟨r, ?_, fun ok _ okb => keep ok okb, fun ρ resp => by simp [sem ρ resp]⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same, run]
  obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
  obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt
    obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    obtain ⟨hc, hu, hd⟩ := split.children wa
    obtain ⟨Hc, Hu, Hd⟩ := split.high wa
    have HB : High la b := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁⟩ := ih c₁ b (hc.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)
    obtain ⟨r₂, run₂, keep₂, sem₂⟩ := ih u₁ b (hu.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃⟩ := ih d₁ b (hd.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)
    have w₁ := keep₁ _ hc (raiseB wb)
    have w₂ := keep₂ _ hu (raiseB wb)
    have w₃ := keep₃ _ hd (raiseB wb)
    obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
    obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ r₂ r₃ h₁ w₁ w₂ w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children oka
      exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc (raiseB okb)) (keep₂ _ ou (raiseB okb))
        (keep₃ _ od (raiseB okb))
    · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
      cases ρ la <;> cases eval ρ b <;> simp
  · -- eq
    have run := compare_eq ha hb order
    have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
    rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
      rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
    · -- two leaves
      refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ resp => ?_⟩
      · unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2», same, run]
      · simp [sameLit ρ resp]
    · -- a leaf below a node
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitB.children wb
      obtain ⟨r₁, run₁, keep₁, sem₁⟩ := neg_union_spec hc hu
      have w₁ := keep₁ _ hc hu
      obtain ⟨h₃, node⟩ := node_new lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wb hb) w₁
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, node]
        by_cases post : compareExact (fuel (.atom "bdd_bot") r₁) (.atom "bdd_bot") r₁ = .eq <;> simp [post]
      · obtain ⟨oc, ou, -⟩ := splitB.children okb
        exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ oc ou) Bdd.bot Bdd.bot
      · rw [sem ρ resp, sem₁ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, sameLit ρ resp]
        cases ρ lb <;> simp
    · -- a node above a leaf
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitA.children wa
      obtain ⟨r₃, run₃, keep₃, sem₃⟩ := union_ok hd hu
      have w₃ := keep₃ _ hd hu
      obtain ⟨h₃, node⟩ := node_new la (.atom "bdd_bot") (.atom "bdd_bot") r₃ (head_leaf wa ha)
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) w₃
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec la (.atom "bdd_bot") (.atom "bdd_bot") r₃ h₃ Bdd.bot Bdd.bot w₃
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₃, node]
        by_cases post : compareExact (fuel r₃ (.atom "bdd_bot")) r₃ (.atom "bdd_bot") = .eq <;> simp [post]
      · obtain ⟨-, ou, od⟩ := splitA.children oka
        exact keep ok (head_leaf wa ha) (head_ok oka ha) Bdd.bot Bdd.bot (keep₃ _ od ou)
      · rw [sem ρ resp, sem₃ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, ← sameLit ρ resp]
        cases ρ la <;> cases eval ρ u₁ <;> cases eval ρ d₁ <;> simp
    · -- two nodes
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
      obtain ⟨hc₂', hu₂', hd₂'⟩ := splitB.children wb
      have hc₂ := hc₂'.congr order
      have hu₂ := hu₂'.congr order
      have hd₂ := hd₂'.congr order
      obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
      have Hc₂ := (splitB.high wb).1.congr order
      have Hu₂ := (splitB.high wb).2.1.congr order
      have Hd₂ := (splitB.high wb).2.2.congr order
      have mA := fun m (ha' : High m _) => High.split splitA wa ha'
      have mB := fun m (hb' : High m _) => High.split splitB wb hb'
      have U' : ∀ {x : Term}, Bdd (Above (· ∈ U) la) x → Bdd (· ∈ U) x := fun w => w.mono fun _ h => h.1
      have pair : ∀ {x y : Term}, Bdd (Above (· ∈ U) la) x → Bdd (Above (· ∈ U) la) y → High la x → High la y →
          (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
            High m x ∧ High m y) → DiffOk x y :=
        fun wx wy hx hy mono => ih _ _ (U' wx) (U' wy) (lower mono ⟨hx, hy⟩)
      have bool : ∀ ρ, Resp ρ → ρ lb = ρ la := fun ρ resp => (sameLit ρ resp).symm
      by_cases cond : Term.compare (Term.fuel u₁ (.atom "bdd_bot")) u₁ (.atom "bdd_bot") = .eq ∨ Term.compare (Term.fuel u₁ u₂) u₁ u₂ = .eq
      · obtain ⟨q₁, runQ₁, keepQ₁, semQ₁⟩ := union_ok hc₂ hu₂
        obtain ⟨q₃, runQ₃, keepQ₃, semQ₃⟩ := union_ok hd₂ hu₂
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := diff_union_spec (i := c₁) hc₂ hu₂ fun u ru => by
          rw [runQ₁] at ru; cases ru
          exact pair hc₁ (keepQ₁ _ hc₂ hu₂) Hc₁ (keepQ₁ _ Hc₂ Hu₂)
            fun m ha' hb' => ⟨(mA m ha').1, keepQ₁ _ (mB m hb').1 (mB m hb').2.1⟩
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := diff_union_spec (i := d₁) hd₂ hu₂ fun u ru => by
          rw [runQ₃] at ru; cases ru
          exact pair hd₁ (keepQ₃ _ hd₂ hu₂) Hd₁ (keepQ₃ _ Hd₂ Hu₂)
            fun m ha' hb' => ⟨(mA m ha').2.2, keepQ₃ _ (mB m hb').2.2 (mB m hb').2.1⟩
        have w₁ := keep₁ _ hc₁ hc₂ hu₂
        have w₃ := keep₃ _ hd₁ hd₂ hu₂
        obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
          (Bdd.bot (ok := fun _ => True)) w₃
        obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          have yes : Lynx.Except.orElse (Erlang.erlang.«==/2» u₁ (.atom "bdd_bot")) (Erlang.erlang.«==/2» u₁ u₂) =
              .ok (.atom "true") := by
            by_cases c₀ : Term.compare (Term.fuel u₁ (.atom "bdd_bot")) u₁ (.atom "bdd_bot") = .eq
            · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₀, Term.true]
            · have c := cond.resolve_left c₀
              simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₀, c, Term.true, Term.false]
          simp [Erlang.erlang.«=:=/2», same, run, yes, run₁, run₃, node]
          by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc₁, -, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
          exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc₁ (oc₂.congr order) (ou₂.congr order)) Bdd.bot
            (keep₃ _ od₁ (od₂.congr order) (ou₂.congr order))
        · have hU : eval ρ u₁ = Bool.false ∨ eval ρ u₁ = eval ρ u₂ := by
            rcases cond with c | c
            · left; rw [(compare_eq_atom _ _).mp c]; simp
            · right; exact eval_congr_cmp (hu₁.mono fun _ h => h.1) resp c
          rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp]
          simp only [eval_node, eval_bot, bool ρ resp]
          revert hU
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          generalize eval ρ u₂ = U₂
          revert L C₁ C₂ D₁ D₂ U₁ U₂
          decide
      · obtain ⟨p₁, runP₁, keepP₁, semP₁⟩ := union_ok hc₁ hu₁
        obtain ⟨q₁, runQ₁, keepQ₁, semQ₁⟩ := union_ok hc₂ hu₂
        obtain ⟨p₃, runP₃, keepP₃, semP₃⟩ := union_ok hd₁ hu₁
        obtain ⟨q₃, runQ₃, keepQ₃, semQ₃⟩ := union_ok hd₂ hu₂
        obtain ⟨r₁', run₁, keep₁, sem₁⟩ := pair (keepP₁ _ hc₁ hu₁) (keepQ₁ _ hc₂ hu₂) (keepP₁ _ Hc₁ Hu₁)
          (keepQ₁ _ Hc₂ Hu₂) fun m ha' hb' => ⟨keepP₁ _ (mA m ha').1 (mA m ha').2.1, keepQ₁ _ (mB m hb').1 (mB m hb').2.1⟩
        obtain ⟨r₃', run₃, keep₃, sem₃⟩ := pair (keepP₃ _ hd₁ hu₁) (keepQ₃ _ hd₂ hu₂) (keepP₃ _ Hd₁ Hu₁)
          (keepQ₃ _ Hd₂ Hu₂) fun m ha' hb' => ⟨keepP₃ _ (mA m ha').2.2 (mA m ha').2.1,
            keepQ₃ _ (mB m hb').2.2 (mB m hb').2.1⟩
        obtain ⟨r₁, wr₁, s₁, def₁⟩ : ∃ r₁, (∀ ok, Bdd (Above ok la) c₁ → Bdd (Above ok la) c₂ →
            Bdd (Above ok la) u₁ → Bdd (Above ok la) u₂ → Bdd (Above ok la) r₁) ∧
            (∀ ρ, Resp ρ → eval ρ r₁ = ((eval ρ c₁ || eval ρ u₁) && !(eval ρ c₂ || eval ρ u₂))) ∧
            ((c₂ = .atom "bdd_top" ∧ r₁ = .atom "bdd_bot") ∨ (¬c₂ = .atom "bdd_top" ∧ r₁ = r₁')) := by
          by_cases ct : c₂ = .atom "bdd_top"
          · exact ⟨.atom "bdd_bot", fun _ _ _ _ _ => Bdd.bot, fun ρ _ => by simp [ct], Or.inl ⟨ct, rfl⟩⟩
          · exact ⟨r₁', fun ok o₁ o₂ o₃ o₄ => keep₁ _ (keepP₁ _ o₁ o₃) (keepQ₁ _ o₂ o₄),
              fun ρ resp => by rw [sem₁ ρ resp, semP₁ ρ resp, semQ₁ ρ resp], Or.inr ⟨ct, rfl⟩⟩
        obtain ⟨r₃, wr₃, s₃, def₃⟩ : ∃ r₃, (∀ ok, Bdd (Above ok la) d₁ → Bdd (Above ok la) d₂ →
            Bdd (Above ok la) u₁ → Bdd (Above ok la) u₂ → Bdd (Above ok la) r₃) ∧
            (∀ ρ, Resp ρ → eval ρ r₃ = ((eval ρ d₁ || eval ρ u₁) && !(eval ρ d₂ || eval ρ u₂))) ∧
            ((d₂ = .atom "bdd_top" ∧ r₃ = .atom "bdd_bot") ∨ (¬d₂ = .atom "bdd_top" ∧ r₃ = r₃')) := by
          by_cases dt : d₂ = .atom "bdd_top"
          · exact ⟨.atom "bdd_bot", fun _ _ _ _ _ => Bdd.bot, fun ρ _ => by simp [dt], Or.inl ⟨dt, rfl⟩⟩
          · exact ⟨r₃', fun ok o₁ o₂ o₃ o₄ => keep₃ _ (keepP₃ _ o₁ o₃) (keepQ₃ _ o₂ o₄),
              fun ρ resp => by rw [sem₃ ρ resp, semP₃ ρ resp, semQ₃ ρ resp], Or.inr ⟨dt, rfl⟩⟩
        have w₁ := wr₁ _ hc₁ hc₂ hu₁ hu₂
        have w₃ := wr₃ _ hd₁ hd₂ hu₁ hu₂
        obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
          (Bdd.bot (ok := fun _ => True)) w₃
        obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          have no : Lynx.Except.orElse (Erlang.erlang.«==/2» u₁ (.atom "bdd_bot")) (Erlang.erlang.«==/2» u₁ u₂) =
              .ok (.atom "false") := by
            simp only [not_or] at cond
            simp [Erlang.erlang.«==/2», Lynx.Except.orElse, cond.1, cond.2, Term.false]
          simp [Erlang.erlang.«=:=/2», same, run, no]
          clear keep sem s₁ s₃ wr₁ wr₃ w₁ w₃ pair lower lowerB ih mA mB
          rcases def₁ with ⟨ct, rfl⟩ | ⟨ct, rfl⟩ <;> rcases def₃ with ⟨dt, rfl⟩ | ⟨dt, rfl⟩ <;>
            simp [Erlang.erlang.«==/2», ct, dt, Term.true, Term.false, runP₁, runQ₁, run₁, runP₃, runQ₃, run₃, node] <;>
            split <;> simp_all
        · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
          exact keep ok (head_leaf wa ha) (head_ok oka ha)
            (wr₁ _ oc₁ (oc₂.congr order) ou₁ (ou₂.congr order)) Bdd.bot
            (wr₃ _ od₁ (od₂.congr order) ou₁ (ou₂.congr order))
        · rw [sem ρ resp, s₁ ρ resp, s₃ ρ resp]
          simp only [eval_node, eval_bot, bool ρ resp]
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          generalize eval ρ u₂ = U₂
          revert L C₁ C₂ D₁ D₂ U₁ U₂
          decide
  · -- gt
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    obtain ⟨hc, hu, hd⟩ := split.children wb
    obtain ⟨Hc, Hu, Hd⟩ := split.high wb
    have HA : High lb a := (raiseA wa).mono fun _ h => h.2
    obtain ⟨m, runM, keepM, semM⟩ := ih a u₂ wa (hu.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)
    have wm := keepM _ (raiseA wa) hu
    have Hm : High lb m := keepM _ HA Hu
    obtain ⟨r₁, run₁, keep₁, sem₁⟩ := ih m c₂ (wm.mono fun _ h => h.1) (hc.mono fun _ h => h.1)
      (lowerB (fun m' ha' hb' => ⟨keepM _ ha' (High.split split wb hb').2.1, (High.split split wb hb').1⟩) ⟨Hm, Hc⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃⟩ := ih m d₂ (wm.mono fun _ h => h.1) (hd.mono fun _ h => h.1)
      (lowerB (fun m' ha' hb' => ⟨keepM _ ha' (High.split split wb hb').2.1, (High.split split wb hb').2.2⟩) ⟨Hm, Hd⟩)
    have w₁ := keep₁ _ wm hc
    have w₃ := keep₃ _ wm hd
    obtain ⟨h₁, node⟩ := node_new lb r₁ (.atom "bdd_bot") r₃ (head_leaf wb hb) w₁ (Bdd.bot (ok := fun _ => True)) w₃
    obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") r₃ h₁ w₁ Bdd.bot w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Erlang.erlang.«=:=/2», same, run, runM, run₁, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children okb
      have om := keepM _ (raiseA oka) ou
      exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ om oc) Bdd.bot (keep₃ _ om od)
    · rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp, semM ρ resp, split.eval ρ]
      cases ρ lb <;> cases eval ρ a <;> cases eval ρ u₂ <;> simp

theorem belowD_all (U : List Term) : ∀ n, BelowD U n := by
  intro n
  induction n with
  | zero => intro a b _ _ lt; omega
  | succ n ih =>
    intro a b wa wb lt
    exact diff_step U a b wa wb fun a' b' wa' wb' lt' => ih a' b' wa' wb' (by omega)

theorem diff_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : DiffOk a b :=
  belowD_all (lits a ++ lits b) _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
    (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)

/-! Unsatisfiable ordered BDDs have no lines. -/

/-- Valuations agreeing on the literals of a BDD agree on the BDD. -/
theorem eval_ext {ok : Term → Prop} {x : Term} (wx : Bdd ok x) {ρ ρ' : Term → Bool}
    (agree : ∀ t, ok t → ρ' t = ρ t) : eval ρ' x = eval ρ x := by
  revert agree
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → ρ' t = ρ t) → eval ρ' x = eval ρ x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _; simp
  · intro _ _; simp
  · intro _ k x y okl agree; simp [agree _ okl]
  · intro ok h lit c u d _ okl _ _ _ ic iu id agree
    have below : ∀ t, Above ok lit t → ρ' t = ρ t := fun t ht => agree t ht.1
    simp [agree _ okl, ic below, iu below, id below]

/-- Setting the truth of a literal. -/
def flip (ρ : Term → Bool) (l : Term) (v : Bool) : Term → Bool :=
  fun t => if Term.compare (Term.fuel t l) t l = .eq then v else ρ t

theorem Resp.flip {ρ : Term → Bool} (resp : Resp ρ) (l : Term) (v : Bool) : Resp (flip ρ l v) := by
  intro a b e
  simp only [BddProofs.flip]
  by_cases ha : Term.compare (Term.fuel a l) a l = .eq
  · have hb : Term.compare (Term.fuel b l) b l = .eq := Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm e) ha
    simp [ha, hb]
  · have hb : ¬Term.compare (Term.fuel b l) b l = .eq := fun hb => ha (Lynx.Term.compare_eq_trans e hb)
    simp [ha, hb, resp a b e]

def Unsat (r : Term) : Prop := ∀ ρ, Resp ρ → eval ρ r = Bool.false

theorem resp_const (v : Bool) : Resp (fun _ => v) := fun _ _ _ => rfl

theorem dnf_unsat {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (unsat : Unsat r) :
    ∀ acc pos neg, Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc pos neg r = .ok acc := by
  revert unsat
  refine Bdd.induction (P := fun _ r => Unsat r → ∀ acc pos neg,
    Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc pos neg r = .ok acc) ?_ ?_ ?_ ?_ ok r wr
  · intro _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro _ _ acc pos neg; simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»]
  · intro _ k x y _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro ok h lit c u d _ _ hc hu hd ic iu id unsat acc pos neg
    have above : ∀ v ρ t, Above ok lit t → flip ρ lit v t = ρ t := fun v ρ t ht => by
      have : Term.compare (Term.fuel t lit) t lit ≠ .eq := fun e => by
        have := ht.2; rw [Lynx.Term.compare_eq_symm e] at this; cases this
      simp [BddProofs.flip, this]
    have parts : ∀ ρ, Resp ρ → eval ρ c = Bool.false ∧ eval ρ u = Bool.false ∧ eval ρ d = Bool.false := by
      intro ρ resp
      have t := unsat _ (resp.flip lit Bool.true)
      have f := unsat _ (resp.flip lit Bool.false)
      simp only [eval_node, eval_ext hc (above Bool.true ρ), eval_ext hu (above Bool.true ρ),
        eval_ext hd (above Bool.true ρ)] at t
      simp only [eval_node, eval_ext hc (above Bool.false ρ), eval_ext hu (above Bool.false ρ),
        eval_ext hd (above Bool.false ρ)] at f
      simp [BddProofs.flip] at t f
      exact ⟨t.1, t.2, f.2⟩
    simp only [Elixir.Module.Types.Descr.«bdd_to_dnf/4»]
    rw [iu (fun ρ resp => (parts ρ resp).2.1), Lynx.Except.ok_bind, ic (fun ρ resp => (parts ρ resp).1),
      Lynx.Except.ok_bind, id (fun ρ resp => (parts ρ resp).2.2)]

/-- Unsatisfiable list BDDs are empty. -/
theorem list_empty_unsat (dsp : Dispatcher) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (unsat : Unsat r)
    (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«list_empty?/2» dsp r (.map S) = .ok (.atom "true") := by
  have dnf := dnf_unsat wr unsat .nil .nil .nil
  unfold Elixir.Module.Types.Descr.«list_empty?/2»
  split
  · have := unsat _ (resp_const Bool.true); simp at this
  · simp only [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf,
      Lynx.Except.ok_bind]
    by_cases seen : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 = .eq)) = Bool.true
    · simp [Erlang.erlang.«is_map_key/2», seen, Term.true]
    · simp [Erlang.erlang.«is_map_key/2», seen, Term.true, Term.false, Erlang.maps.«put/3»,
        Erlang.lists.«all/2», Erlang.erlang.«is_function/2»]

end BddProofs

end Elixir.STTDescrProofsTest

-- Tuple types are the top tuple literal or ordered BDDs of other tuple literals,
-- whose elements are types of bitmaps, atoms, tuples, and lists. Lines of
-- tuples intersect these elements, which stay such types, and what remains
-- of a tuple type and its negation has no line, except for the empty tuple,
-- whose negation holds tuples of other sizes.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term

open BddProofs

/-! Call depth: computations whose result does not depend on it, once it is deep enough. -/

abbrev D (n : Nat) : Dispatcher := Dispatcher.ofTable Erlang.program.fun_table n

def boolAtom (o : Bool) : Term := .atom (if o then "true" else "false")

theorem mapM_ok {α β : Type} (f : α → Except Exception β) (h : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f x = .ok (h x)) → xs.mapM f = .ok (xs.map h)
  | [], _ => rfl
  | x :: xs, all => by
    simp [List.mapM_cons, all x (by simp), mapM_ok f h xs (fun y my => all y (by simp [my]))]

/-- The entries `maps:intersect_with/3` returns with a combiner returning `g`. -/
def interList (g : Term → Term → Term → Term) (l r : List (Term × Term)) : List (Term × Term) :=
  ((mapEntries l).map fun e => ((mapLookup r e.1).map (g e.1 e.2)).map fun v => (e.1, v)).reduceOption

theorem intersect_with_eq (d : Dispatcher) (module name : String) (captures : Array Term)
    (l r : List (Term × Term)) (g : Term → Term → Term → Term)
    (calls : ∀ entry ∈ mapEntries l, ∀ value, mapLookup r entry.1 = some value →
      d.pure (.function false module name 3 captures) #[entry.1, entry.2, value] = .ok (g entry.1 entry.2 value)) :
    (Erlang.maps.«intersect_with/3» d (.function false module name 3 captures) (.map l) (.map r) :
      Except Exception Term) = .ok (.map (interList g l r)) := by
  simp only [Erlang.maps.«intersect_with/3», Dispatch.dispatch]
  rw [mapM_ok _ (fun e => ((mapLookup r e.1).map (g e.1 e.2)).map fun v => (e.1, v)) _ ?all]
  · rfl
  · intro e me
    cases hr : mapLookup r e.1 with
    | none => simp
    | some v => simp only [calls e me v hr]; rfl

/-- The entries `maps:merge_with/3` returns with a combiner returning `g`. -/
def mergeList (g : Term → Term → Term → Term) (l r : List (Term × Term)) : List (Term × Term) :=
  ((mapEntries r).map fun e => (e.1, match mapLookup l e.1 with | some v => g e.1 v e.2 | none => e.2)) ++ l

theorem merge_with_eq (d : Dispatcher) (module name : String) (captures : Array Term)
    (l r : List (Term × Term)) (g : Term → Term → Term → Term)
    (calls : ∀ entry ∈ mapEntries r, ∀ value, mapLookup l entry.1 = some value →
      d.pure (.function false module name 3 captures) #[entry.1, value, entry.2] = .ok (g entry.1 value entry.2)) :
    (Erlang.maps.«merge_with/3» d (.function false module name 3 captures) (.map l) (.map r) :
      Except Exception Term) = .ok (.map (mergeList g l r)) := by
  simp only [Erlang.maps.«merge_with/3», Dispatch.dispatch]
  rw [mapM_ok _ (fun e => (e.1, match mapLookup l e.1 with | some v => g e.1 v e.2 | none => e.2)) _ ?all]
  · rfl
  · intro e me
    cases hl : mapLookup l e.1 with
    | none => simp
    | some v => simp only [calls e me v hl]; rfl

/-- The entries `maps:filter/2` keeps with a predicate deciding by `keep`. -/
def filterList (keep : Term × Term → Bool) (es : List (Term × Term)) : List (Term × Term) :=
  ((mapEntries es).map fun e => (if keep e then some e.2 else none).map fun v => (e.1, v)).reduceOption

theorem filter_eq (d : Dispatcher) (module name : String) (captures : Array Term)
    (es : List (Term × Term)) (keep : Term × Term → Bool)
    (calls : ∀ entry ∈ mapEntries es, d.pure (.function false module name 2 captures) #[entry.1, entry.2] =
      .ok (if keep entry then Term.true else Term.false)) :
    (Erlang.maps.«filter/2» d (.function false module name 2 captures) (.map es) : Except Exception Term) =
      .ok (.map (filterList keep es)) := by
  simp only [Erlang.maps.«filter/2», Dispatch.dispatch]
  rw [mapM_ok _ (fun e => (if keep e then some e.2 else none).map fun v => (e.1, v)) _ ?all]
  · rfl
  · intro e me
    cases hk : keep e <;> simp [calls e me, hk, Term.true, Term.false]

/-- Element types `E` hold the top type, intersect into element types, and have their emptiness decided,
with the same results at every call depth from `K`. -/
structure ElemOk (E : Term → Prop) (K : Nat) : Prop where
  term : E (.atom "term")
  inter : ∀ {a b}, E a → E b → ∃ c, E c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c
  empty : ∀ {a}, E a → ∀ S : List (Term × Term), ∃ b : Bool, ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)
  none : E (.map [])
  pos : 1 ≤ K

/-- Element types that also subtract into element types. -/
structure ElemDiff (E : Term → Prop) (K : Nat) : Prop where
  diff : ∀ {a b}, E a → E b → ∃ c, E c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c

theorem ElemOk.mono {E : Term → Prop} {K K' : Nat} (ops : ElemOk E K) (le : K ≤ K') : ElemOk E K' := by
  refine ⟨ops.term, fun ha hb => ?_, fun ha S => ?_, ops.none, by have := ops.pos; omega⟩
  · obtain ⟨c, hc, run⟩ := ops.inter ha hb
    exact ⟨c, hc, fun m hm => run m (by omega)⟩
  · obtain ⟨b, run⟩ := ops.empty ha S
    exact ⟨b, fun m hm => run m (by omega)⟩

theorem ElemDiff.mono {E : Term → Prop} {K K' : Nat} (dops : ElemDiff E K) (le : K ≤ K') : ElemDiff E K' := by
  refine ⟨fun ha hb => ?_⟩
  obtain ⟨c, hc, run⟩ := dops.diff ha hb
  exact ⟨c, hc, fun m hm => run m (by omega)⟩

theorem succ_of_le {K m : Nat} (h : K + 1 ≤ m) : ∃ m', m = m' + 1 ∧ K ≤ m' := ⟨m - 1, by omega, by omega⟩

/-- Flat element types: valid types of bitmaps and atoms. -/
abbrev Elem (X : List (Term × Term)) : Prop := Valid X

def ElemTerm (e : Term) : Prop := e = .atom "term" ∨ ∃ X, e = .map X ∧ Elem X

theorem Elem.static {X : List (Term × Term)} (valid : Elem X) : mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w =>
    rcases valid.keys _ (by rw [h]; rfl) with bad | bad <;> simp only [Term.atom.injEq] at bad <;>
      exact absurd bad (by decide)

/-- The shape of a field of an element type. -/
def ElemField (q w : Term) : Prop :=
  (q = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
    (q = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ [])

theorem Elem.field {X : List (Term × Term)} (valid : Elem X) {q w : Term} (h : mapLookup X q = some w) :
    ElemField q w := by
  rcases valid.keys q (by simp [h]) with rfl | rfl
  · exact Or.inl ⟨rfl, valid.bitmap w h⟩
  · exact Or.inr ⟨rfl, valid.atom w h, fun S e => valid.atomUnion S (e ▸ h)⟩

/-- Intersections of static types whose common fields intersect the same way at every call depth. -/
theorem inter_uniform (K : Nat) (L R : List (Term × Term)) (sL : mapLookup L (.atom "dynamic") = Option.none)
    (sR : mapLookup R (.atom "dynamic") = Option.none) (g : Term → Term → Term → Term)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_intersection/3» (D m) q x y = .ok (g q x y)) :
    ∃ I out, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.map L) (.map R) =
        .ok (.map out)) ∧
      (∀ q, mapLookup I q = match (mapEntries L).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => (mapLookup R e.1).map (g e.1 e.2)
        | none => none) ∧
      ∀ q, mapLookup out q = match (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => if kept e then some e.2 else none
        | none => none := by
  have callsI : ∀ n, K ≤ n → ∀ e ∈ mapEntries L, ∀ y, mapLookup R e.1 = some y →
      (D (n + 1)).pure (.function false "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) #[e.1, e.2, y] =
        .ok (g e.1 e.2 y) := fun n hn e member y hy => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure]
    exact calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy n hn
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (K + 1)) false "Elixir.Module.Types.Descr"
    "bare_intersection" #[] L R g (callsI K (Nat.le_refl _))
  have eqI : I = interList g L R := by
    have := runI.symm.trans (intersect_with_eq _ _ _ _ L R g (callsI K (Nat.le_refl _)))
    simpa using this
  subst eqI
  have callsO : ∀ n, ∀ e ∈ mapEntries (interList g L R),
      (D (n + 1)).pure (.function false "Elixir.Module.Types.Descr" "-symmetrical_intersection/3-fun-0-" 2 #[])
        #[e.1, e.2] = .ok (if kept e then Term.true else Term.false) := fun n e _ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field]
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (K + 1)) false "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] (interList g L R) kept (callsO K)
  have eqO : out = filterList kept (interList g L R) := by
    have := runO.symm.trans (filter_eq _ _ _ _ _ kept (callsO K))
    simpa using this
  subst eqO
  refine ⟨interList g L R, filterList kept (interList g L R), fun m hm => ?_, lookI, lookO⟩
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, sL, sR]
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [intersect_with_eq _ _ _ _ L R g (callsI n hn), filter_eq _ _ _ _ _ kept (callsO n)]

/-- Lists of element types. -/
def AllElem (E : Term → Prop) (xs : Term) : Prop := ∃ l : List Term, xs = Term.list l ∧ ∀ e ∈ l, E e

theorem reverse_elems (l : List Term) (hl : ∀ e ∈ l, E e) :
    ∀ tail, AllElem E tail → ∃ r, Erlang.lists.«reverse/2» (Term.list l) tail = .ok r ∧ AllElem E r := by
  induction l with
  | nil => intro tail ht; exact ⟨tail, by simp [Erlang.lists.«reverse/2»], ht⟩
  | cons h t ih =>
    rintro tail ⟨lt, rfl, hlt⟩
    obtain ⟨r, run, hr⟩ := ih (fun e me => hl e (List.mem_cons_of_mem _ me)) (Term.list (h :: lt))
      ⟨h :: lt, rfl, fun e me => by
        rcases List.mem_cons.mp me with rfl | me
        · exact hl e List.mem_cons_self
        · exact hlt e me⟩
    exact ⟨r, by simpa [Term.list, Erlang.lists.«reverse/2»] using run, hr⟩

theorem zip_elems (ops : ElemOk E K) (l₁ : List Term) (h₁ : ∀ e ∈ l₁, E e) :
    ∀ (l₂ : List Term), (∀ e ∈ l₂, E e) → ∀ acc, AllElem E acc →
    ∃ r, AllElem E r ∧ ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«zip_intersection/4» (D m)
      (Term.list l₁) (Term.list l₂) acc (.function false "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]) =
        .ok r := by
  induction l₁ with
  | nil =>
    rintro l₂ h₂ acc ⟨la, rfl, hla⟩
    obtain ⟨r, run, hr⟩ := reverse_elems la hla (Term.list l₂) ⟨l₂, rfl, h₂⟩
    exact ⟨r, hr, fun _ _ => by unfold Elixir.Module.Types.Descr.«zip_intersection/4»; exact run⟩
  | cons x xs ih =>
    rintro l₂ h₂ acc ⟨la, rfl, hla⟩
    cases l₂ with
    | nil =>
      obtain ⟨r, run, hr⟩ := reverse_elems la hla (Term.list (x :: xs)) ⟨_, rfl, h₁⟩
      exact ⟨r, hr, fun _ _ => by unfold Elixir.Module.Types.Descr.«zip_intersection/4»; exact run⟩
    | cons y ys =>
      obtain ⟨e, he, run⟩ := ops.inter (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
      obtain ⟨r, hr, runr⟩ := ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys
        (fun e me => h₂ e (List.mem_cons_of_mem _ me)) (Term.list (e :: la))
        ⟨e :: la, rfl, fun e' me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact he
          · exact hla e' me⟩
      refine ⟨r, hr, fun m hm => ?_⟩
      obtain ⟨n, rfl, hn⟩ := succ_of_le hm
      unfold Elixir.Module.Types.Descr.«zip_intersection/4»
      simp only [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure, run n hn,
        Lynx.Except.ok_bind]
      exact runr _ hm

theorem length_list (l : List Term) : Erlang.erlang.«length/1» (Term.list l) = .ok (.integer l.length) := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [Erlang.erlang.«length/1»] at ih ⊢; simp [ih]

/-- Lines of tuples: a tag and element types. -/
def TuplePos (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ (tag = "open" ∨ tag = "closed") ∧
    ∀ e ∈ l, E e

/-- Tuple literals: a key, a tag, and element types. -/
def TupleLit (E : Term → Prop) (t : Term) : Prop :=
  ∃ (k : Int) (tag : String) (l : List Term), t = .tuple #[.integer k, .atom tag, Term.list l] ∧
    (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, E e

theorem sizes_ok (t₁ t₂ : String) (h₁ : t₁ = "open" ∨ t₁ = "closed") (h₂ : t₂ = "open" ∨ t₂ = "closed")
    (n₁ n₂ : Int) : ∃ v, Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» (.atom t₁) (.integer n₁) (.atom t₂)
      (.integer n₂) = .ok v := by
  unfold Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    simp [Erlang.erlang.«/=/2», Erlang.erlang.«==/2»]
  all_goals (repeat (first | exact ⟨_, rfl⟩ | split))

theorem line_ok (ops : ElemOk E K) {p t : Term} (hp : TuplePos E p) (ht : TupleLit E t) :
    (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) p t = .ok (.atom "empty")) ∨
      ∃ p', TuplePos E p' ∧
        ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) p t = .ok p' := by
  obtain ⟨t₁, l₁, rfl, g₁, e₁⟩ := hp
  obtain ⟨k, t₂, l₂, rfl, g₂, e₂⟩ := ht
  obtain ⟨v, strategy⟩ := sizes_ok t₁ t₂ g₁ g₂ l₁.length l₂.length
  obtain ⟨r, ⟨lr, rfl, hr⟩, zip⟩ := zip_elems ops l₁ e₁ l₂ e₂ .nil ⟨[], rfl, by simp⟩
  by_cases dis : v = .atom "disjoint"
  · subst dis
    left
    intro m _
    unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
    simp only [length_list, Lynx.Except.ok_bind, strategy]
    rfl
  · right
    have run : ∀ tag, tag = (if t₁ = "open" ∧ t₂ = "open" then "open" else "closed") → ∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) (.tuple #[.atom t₁, Term.list l₁])
          (.tuple #[.integer k, .atom t₂, Term.list l₂]) = .ok (.tuple #[.atom tag, Term.list lr]) := by
      intro tag htag m hm
      unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
      simp only [length_list, Lynx.Except.ok_bind, strategy]
      subst htag
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
        simp [Erlang.erlang.«==/2», Lynx.Except.andAlso, zip m hm]
    exact ⟨_, ⟨_, lr, rfl, by split <;> simp, hr⟩, run _ rfl⟩

/-- The branches of an unsatisfiable node are unsatisfiable. -/
theorem unsat_children {ok : Term → Prop} {h : Int} {lit c u d : Term}
    (hc : Bdd (Above ok lit) c) (hu : Bdd (Above ok lit) u) (hd : Bdd (Above ok lit) d)
    (unsat : Unsat (.tuple #[.integer h, lit, c, u, d])) : Unsat c ∧ Unsat u ∧ Unsat d := by
  have above : ∀ v ρ t, Above ok lit t → flip ρ lit v t = ρ t := fun v ρ t ht => by
    have : Term.compare (Term.fuel t lit) t lit ≠ .eq := fun e => by
      have := ht.2; rw [Lynx.Term.compare_eq_symm e] at this; cases this
    simp [BddProofs.flip, this]
  have parts : ∀ ρ, Resp ρ → eval ρ c = Bool.false ∧ eval ρ u = Bool.false ∧ eval ρ d = Bool.false := by
    intro ρ resp
    have t := unsat _ (resp.flip lit Bool.true)
    have f := unsat _ (resp.flip lit Bool.false)
    simp only [eval_node, eval_ext hc (above Bool.true ρ), eval_ext hu (above Bool.true ρ),
      eval_ext hd (above Bool.true ρ)] at t
    simp only [eval_node, eval_ext hc (above Bool.false ρ), eval_ext hu (above Bool.false ρ),
      eval_ext hd (above Bool.false ρ)] at f
    simp [BddProofs.flip] at t f
    exact ⟨t.1, t.2, f.2⟩
  exact ⟨fun ρ r => (parts ρ r).1, fun ρ r => (parts ρ r).2.1, fun ρ r => (parts ρ r).2.2⟩

/-- Unsatisfiable tuple BDDs have no line, whatever the elements of their literals. -/
theorem tuple_bdd_empty_unsat (ops : ElemOk E K) {m : Nat} (hm : K + 1 ≤ m) {ok : Term → Prop} {r : Term}
    (wr : Bdd ok r) (lits : ∀ t, ok t → TupleLit E t) (unsat : Unsat r) :
    ∀ pos negs seen, TuplePos E pos →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos negs r seen = .ok (.atom "true") := by
  revert lits unsat
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleLit E t) → Unsat r → ∀ pos negs seen, TuplePos E pos →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos negs r seen = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro _ _ _ pos negs seen _
    unfold Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
    rfl
  · intro _ k x y _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro ok h lit c u d _ okl hc hu hd ic iu id lits unsat pos negs seen hp
    obtain ⟨uc, uu, ud⟩ := unsat_children hc hu hd unsat
    have lits' : ∀ t, Above ok lit t → TupleLit E t := fun t ht => lits t ht.1
    have dTrue := id lits' ud pos (.cons lit negs) seen hp
    have uTrue := iu lits' uu pos negs seen hp
    unfold Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
    simp only [dTrue, uTrue, Lynx.Except.andAlso]
    rcases line_ok ops hp (lits lit okl) with line | ⟨p', hp', line⟩
    · simp [line m hm]
    · have cTrue := ic lits' uc p' negs seen hp'
      obtain ⟨tg, l, rfl, -, -⟩ := hp'
      simp [line m hm, cTrue]

/-! Reading the tuple specification. -/

theorem any_bdd_spec : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n → «any_bdd?/2» b lower = .ok Term.true →
    Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «any_bdd?/2» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · rename_i key _ _
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      cases key <;> simp [Erlang.erlang.«is_integer/1»] at h
      exact Bdd.leaf_iff.mpr (Lynx.Term.compare_lt_of_gt (by simpa [Erlang.erlang.«>/2»] using h))
    · rename_i hash key x y c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨⟨ih₁, ik⟩, gt⟩, hc⟩, hu⟩, hd⟩ := h
      cases hash <;> simp [Erlang.erlang.«is_integer/1»] at ih₁
      cases key <;> simp [Erlang.erlang.«is_integer/1»] at ik
      rename_i h' k
      have lt : Term.compare (Term.fuel lower (.tuple #[.integer k, x, y])) lower (.tuple #[.integer k, x, y]) = .lt :=
        Lynx.Term.compare_lt_of_gt (by simpa [Erlang.erlang.«>/2»] using gt)
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨Lynx.Term.compare_lt_trans lt ht, ht⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, lt,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

/-- Element types that `nested?/2` accepts at a depth. -/
abbrev NestedOk (E : Term → Prop) (depth : Term) : Prop := ∀ e, «nested?/2» e depth = .ok Term.true → E e

theorem elements_spec (hE : NestedOk E depth) : ∀ {xs : Term}, «elements?/2» xs depth = .ok Term.true → AllElem E xs
  | .nil, _ => ⟨[], rfl, by simp⟩
  | .cons x xs, h => by
    unfold «elements?/2» at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨l, rfl, hl⟩ := elements_spec hE h.2
    exact ⟨x :: l, rfl, fun e me => by
      rcases List.mem_cons.mp me with rfl | me
      · exact hE _ h.1
      · exact hl e me⟩
  | .atom _, h | .integer _, h | .float _, h | .reference _, h | .function _ _ _ _ _, h | .pid _, h
  | .tuple _, h | .map _, h | .bitstring _ _ _, h => by unfold «elements?/2» at h; simp [Term.true] at h

/-- The top tuple literal `{_, open, []}`, which tuple operations treat as the top type. -/
def IsTop (t : Term) : Prop := ∃ k : Term, t = .tuple #[k, .atom "open", .nil]

def TupleOk (E : Term → Prop) (t : Term) : Prop := TupleLit E t ∧ ¬IsTop t

theorem tuple_literal_spec (hE : NestedOk E depth) {lit lower : Term}
    (h : «tuple_literal?/3» lit lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ TupleOk E lit := by
  unfold «tuple_literal?/3» at h
  simp only at h
  split at h
  · rename_i key tag elements
    simp only [Lynx.Except.guard, Lynx.Except.tryWith] at h
    split at h
    · next member =>
      have tags : tag = .atom "open" ∨ tag = .atom "closed" := by
        by_cases o : tag = .atom "open"
        · exact Or.inl o
        · by_cases c : tag = .atom "closed"
          · exact Or.inr c
          · simp [isMember, o, c] at member
      cases key <;> simp [Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true] at h
      rename_i k
      by_cases gt : (Term.compare (Term.fuel (.tuple #[.integer k, tag, elements]) lower) (.tuple #[.integer k, tag, elements]) lower).isGT = Bool.true
      · have lt : Term.compare (Term.fuel lower (.tuple #[.integer k, tag, elements])) lower (.tuple #[.integer k, tag, elements]) = .lt :=
          Lynx.Term.compare_lt_of_gt (by simpa [Ordering.isGT_iff_eq_gt] using gt)
        rcases tags with rfl | rfl
        · by_cases en : elements = .nil
          · subst en
            simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2»] at h
          · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», en] at h
            obtain ⟨l, rfl, hl⟩ := elements_spec hE h
            refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "open", l, rfl, Or.inl rfl, hl⟩, ?_⟩
            rintro ⟨_, e⟩
            simp at e
            exact en e.2
        · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2»] at h
          obtain ⟨l, rfl, hl⟩ := elements_spec hE h
          refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "closed", l, rfl, Or.inr rfl, hl⟩, ?_⟩
          rintro ⟨_, e⟩
          simp at e
      · simp [Erlang.erlang.«>/2», gt] at h
    · simp [Term.true] at h
  · simp [Term.true] at h

theorem ordered_tuple_spec (hE : NestedOk E depth) : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
    «ordered_tuple_bdd?/3» b lower depth = .ok Term.true → Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ TupleOk E t) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «ordered_tuple_bdd?/3» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := tuple_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := tuple_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ TupleOk E t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ TupleOk E t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

/-- Tuple types are the top tuple literal or ordered BDDs of other tuple literals. -/
abbrev TupleField (E : Term → Prop) (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd (TupleOk E) w

theorem tuple_bdd_spec (hE : NestedOk E depth) {w : Term} (h : «tuple_bdd?/2» w depth = .ok Term.true) :
    TupleField E w := by
  unfold «tuple_bdd?/2» at h
  split at h
  · rename_i key
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ((ordered_tuple_spec hE _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)

/-! Differences of two leaves. -/

@[simp] theorem atom_compareExact_eq (name : String) (t : Term) :
    compareExact (fuel (.atom name) t) (.atom name) t = .eq ↔ t = .atom name :=
  ⟨fun e => (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm e),
    fun e => by subst e; exact compareExact_self _⟩

theorem diff_leaf_bot (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_difference/2»
  simp [Erlang.erlang.«=:=/2»]

theorem diff_leaf_top (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/2» (.tuple #[k, x, y]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_difference/2»
  simp [Erlang.erlang.«=:=/2»]

/-! The empty tuple and its negation. -/

def EmptyTuple (K : Nat) (r : Term) : Prop :=
  ∀ m S, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) r (.map S) = .ok (.atom "true")

theorem tuple_empty_of {K : Nat} {r : Term} (run : ∀ m S, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
    (D m) (.tuple #[.atom "open", .nil]) .nil r (.map S) = .ok (.atom "true")) : EmptyTuple K r := by
  intro n S hn
  have run' := fun S' => run n S' hn
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  by_cases seen : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "tuple") r) e.1) (.cons (.atom "tuple") r) e.1 = .eq)) = Bool.true
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen,
      Term.false, Erlang.maps.«put/3», run']

theorem tuple_empty_unsat (ops : ElemOk E K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
    (lits : ∀ t, ok t → TupleLit E t) (unsat : Unsat r) : EmptyTuple K r :=
  tuple_empty_of fun m S hm => tuple_bdd_empty_unsat ops hm wr lits unsat _ _ _ ⟨"open", [], rfl, Or.inl rfl, by simp⟩

theorem inter_top_leaf (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_top") (.tuple #[k, x, y]) = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

theorem inter_bot_leaf (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_bot") (.tuple #[k, x, y]) = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

theorem inter_leaf_top (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[k, x, y]) (.atom "bdd_top") = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

theorem inter_leaf_bot (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

/-- Two distinct leaves intersect into a node of the smaller one. -/
theorem leaf_intersection {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (same : ¬compareExact (fuel b a) b a = .eq)
    (order : Term.compare (Term.fuel a b) a b ≠ .eq) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok (.tuple #[.integer h, a, b, .atom "bdd_bot", .atom "bdd_bot"]) ∨
      Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok (.tuple #[.integer h, b, a, .atom "bdd_bot", .atom "bdd_bot"]) := by
  have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
  have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
  have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
  have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
  rcases cmp : Term.compare (Term.fuel a b) a b
  · obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt wa ha hb cmp
    rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rfl⟩ := la; simp at e
    obtain ⟨h₁, node⟩ := node_new a b (.atom "bdd_bot") (.atom "bdd_bot") la wb
      (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
    refine ⟨h₁, Or.inl ?_⟩
    obtain ⟨_, _, _, rfl⟩ := la
    obtain ⟨_, _, _, rfl⟩ := lb
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same, run, inter_top_leaf, inter_bot_leaf, node]
  · exact absurd cmp order
  · obtain ⟨h₀, c, u, d, run, split⟩ := compare_gt wb ha hb cmp
    rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rfl⟩ := lb; simp at e
    obtain ⟨h₁, node⟩ := node_new b a (.atom "bdd_bot") (.atom "bdd_bot") lb wa
      (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
    refine ⟨h₁, Or.inr ?_⟩
    obtain ⟨_, _, _, rfl⟩ := la
    obtain ⟨_, _, _, rfl⟩ := lb
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same, run, inter_leaf_top, inter_leaf_bot, node]

theorem empty_tuple_cancel (K : Nat) (k key : Int) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[.integer k, .atom "closed", .nil])
      (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) = .ok r ∧ EmptyTuple K r := by
  have same : ¬compareExact (fuel (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) (.tuple #[.integer k, .atom "closed", .nil])) (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]])
      (.tuple #[.integer k, .atom "closed", .nil]) = .eq := by
    intro e
    obtain ⟨_, _, _, e', -, t, -⟩ := tuple3_exact e
    simp at e'
    obtain ⟨rfl, rfl, rfl⟩ := e'
    simp at t
  have order : Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", .nil]) (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]])) (.tuple #[.integer k, .atom "closed", .nil])
      (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) ≠ .eq := by
    rw [compare_tuple]
    simp [List.compareLex_cons_cons]
  obtain ⟨h, run | run⟩ := leaf_intersection ⟨k, _, _, rfl⟩ ⟨key, _, _, rfl⟩ same order
  · refine ⟨_, run, tuple_empty_of fun n S _ => ?_⟩
    simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2»]
  · refine ⟨_, run, tuple_empty_of fun n S _ => ?_⟩
    simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2»]

/-- What survives of a tuple type and its negation is empty. -/
def TupleCancel (K : Nat) (x nb : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«tuple_intersection/2» x nb = .ok r ∧
    (kept (.atom "tuple", r) = Bool.true → EmptyTuple K r)

theorem TupleOk.lit {t : Term} (h : TupleOk E t) : TupleLit E t := h.1

/-- Intersections of tuple BDDs that are not the top literal themselves. -/
theorem tuple_intersection_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«tuple_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem not_top_of_ok {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (okNot : ∀ t, ok t → ¬IsTop t) :
    ∀ k, x ≠ .tuple #[k, .atom "open", .nil] := by
  intro k e
  subst e
  rcases wx.shape with h | h | ⟨k', x', y', h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact okNot _ (Bdd.leaf_iff.mp wx) ⟨_, rfl⟩

theorem tuple_cancel (ops : ElemOk E K) (x : Term) (field : TupleField E x) :
    ∃ nb, Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok nb ∧
      (kept (.atom "tuple", nb) = Bool.true → TupleCancel K x nb) := by
  rcases field with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«tuple_difference/2»], fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    simp [diff_leaf_top]
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun _ => ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩⟩
    · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    · unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
      rfl
  · obtain ⟨⟨k', tag, ls, e, tags, elems⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
    simp at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    by_cases special : tag = "closed" ∧ ls = []
    · obtain ⟨rfl, rfl⟩ := special
      obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
      refine ⟨.tuple #[.integer ((1 <<< 27) + hash), .atom "open", Term.list [.atom "term"]], ?_, fun _ => ?_⟩
      · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
          Elixir.Module.Types.Descr.«bdd_leaf_key/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»]
        rfl
      · obtain ⟨r, run, empty⟩ := empty_tuple_cancel K k ((1 <<< 27) + hash)
        refine ⟨r, ?_, fun _ => empty⟩
        rw [tuple_intersection_bdd notTop (by intro k e; simp at e)]
        exact run
    · have notSpecial : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠
          .tuple #[k₁, .atom "closed", .nil] := by
        intro k₁ e
        simp at e
        apply special
        refine ⟨e.2.1, ?_⟩
        cases ls <;> simp_all [Term.list]
      obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
      have wnb := keep _ wx
      refine ⟨nb, ?_, fun _ => ?_⟩
      · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        split
        · next _ _ e =>
          exfalso
          simp at e
          obtain ⟨-, rfl, hl⟩ := e
          exact notTopX ⟨_, by rw [hl]⟩
        · next _ _ e => exact (notSpecial _ e).elim
        · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact run
        · next h₁ => exact (h₁ _ _ rfl rfl).elim
      · have wl : Bdd (TupleLit E) (.tuple #[.integer k, .atom tag, Term.list ls]) := wx.mono fun _ h => h.1
        obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
        refine ⟨r, ?_, fun _ => tuple_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
          fun ρ resp => ?_⟩
        · rw [tuple_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
          exact rr
        · rw [sr ρ resp, sem ρ resp]
          cases eval ρ (.tuple #[.integer k, .atom tag, Term.list ls]) <;> rfl
  · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
    have wnb := keep _ wx
    refine ⟨nb, ?_, fun _ => ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [run]
    · have wl : Bdd (TupleLit E) (.tuple #[.integer h, lit, c, u, d]) := wx.mono fun _ h => h.1
      obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
      refine ⟨r, ?_, fun _ => tuple_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
        fun ρ resp => ?_⟩
      · rw [tuple_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
        exact rr
      · rw [sr ρ resp, sem ρ resp]
        cases eval ρ (.tuple #[.integer h, lit, c, u, d]) <;> rfl

end Elixir.STTDescrProofsTest

-- Map types are the top map literal or ordered BDDs of other map literals,
-- open or closed maps whose fields hold types of bitmaps and atoms. Lines of
-- maps intersect these fields, whose emptiness is immediate, and what remains
-- of a map type and its negation has no line.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term
open BddProofs

open BddProofs

def isNone : Term → Bool
  | .map [] => Bool.true
  | _ => Bool.false

/-- The emptiness of flat element types is decided without recursion. -/
theorem flat_empty {t : Term} (ht : ElemTerm t) (S : List (Term × Term)) (d : Dispatcher) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d t (.map S) = .ok (boolAtom (isNone t)) := by
  rcases ht with rfl | ⟨X, rfl, valid⟩
  · rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    rfl
  have absent : ∀ name, name ≠ "bitmap" → name ≠ "atom" → mapLookup X (.atom name) = Option.none := by
    intro name nb na
    cases h : mapLookup X (.atom name) with
    | none => rfl
    | some w =>
      rcases valid.keys (.atom name) (by rw [h]; rfl) with e | e
      · cases e; exact absurd rfl nb
      · cases e; exact absurd rfl na
  have anyKey : ∀ name, (X.any fun e => decide (compareExact (fuel (.atom name) e.1) (.atom name) e.1 = .eq)) =
      (mapLookup X (.atom name)).isSome := by
    intro name
    rw [Bool.eq_iff_iff, mapLookup_isSome]
    simp
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [getMapKeys_single, absent "dynamic" (by decide) (by decide), Erlang.erlang.«==/2»,
    Erlang.erlang.«is_map_key/2», anyKey, absent "tuple" (by decide) (by decide), absent "map" (by decide) (by decide),
    absent "list" (by decide) (by decide), absent "fun" (by decide) (by decide), Term.true, Term.false]
  by_cases empty : X = []
  · simp [empty, boolAtom, isNone]
  have nn : isNone (.map X) = Bool.false := by cases X <;> simp_all [isNone]
  rw [nn]
  obtain ⟨e, rest, hX⟩ := List.exists_cons_of_ne_nil empty
  have key : (mapLookup X e.1).isSome := (mapLookup_isSome _ _).mpr ⟨e, by simp [hX], compareExact_self _⟩
  simp only [empty, ite_false]
  cases ha : mapLookup X (.atom "atom") <;> cases hb : mapLookup X (.atom "bitmap") <;>
    simp [Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  rcases valid.keys _ key with k | k <;> rw [k] at key <;> simp_all

/-! Map literals. -/

/-- Results of literal intersections at every call depth from `K`, which throw `:empty` when a required
field is empty. -/
def Throws (K : Nat) (e : Nat → Except Exception Term) (P : Term → Prop) : Prop :=
  (∃ v, P v ∧ ∀ m, K ≤ m → e m = .ok v) ∨ ∀ m, K ≤ m → e m = .error (Exception.throw (.atom "empty"))

/-- Map fields: a type and whether it is optional. -/
def FieldValue (E : Term → Prop) (v : Term) : Prop :=
  ∃ (t : Term) (o : Bool), v = .tuple #[t, boolAtom o] ∧ E t

def bareIntersection : Term := .function false "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]

theorem merge_fun (ops : ElemOk E K) (S : List (Term × Term)) (key v₁ v₂ : Term) (h₁ : FieldValue E v₁)
    (h₂ : FieldValue E v₂) :
    Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» (D m)
      bareIntersection (.map S) key v₁ v₂) (FieldValue E) := by
  obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁
  obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂
  obtain ⟨e, fe, run⟩ := ops.inter f₁ f₂
  obtain ⟨b, empty⟩ := ops.empty fe S
  have dispatch : ∀ m, K + 1 ≤ m → Lynx.Dispatcher.pure (D m) bareIntersection #[t₁, t₂] = .ok e := by
    intro m hm
    obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
    exact run n hn
  by_cases thrown : (o₁ && o₂) = Bool.false ∧ b = Bool.true
  · obtain ⟨o, rfl⟩ := thrown
    refine Or.inr fun m hm => ?_
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> simp at o <;>
      simp [boolAtom, Lynx.Except.andAlso, dispatch m hm, empty m (by omega),
        isMember]
  · refine Or.inl ⟨_, ⟨e, o₁ && o₂, rfl, fe⟩, fun m hm => ?_⟩
    unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
    cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
      simp [boolAtom, Lynx.Except.andAlso, dispatch m hm, empty m (by omega),
        isMember]

def fieldsTerm (l : List (Term × Term)) : Term := Term.list (l.map fun e => .tuple #[e.1, e.2])

def Fields (E : Term → Prop) (v : Term) : Prop :=
  ∃ l : List (Term × Term), v = fieldsTerm l ∧ ∀ e ∈ l, FieldValue E e.2

def mergeFun (S : List (Term × Term)) : Term :=
  .function false "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-0-" 3 #[bareIntersection, .map S]

theorem fields_cons {x : Term × Term} {l : List (Term × Term)} (hx : FieldValue E x.2)
    (hl : ∀ e ∈ l, FieldValue E e.2) : ∀ e ∈ x :: l, FieldValue E e.2 := fun e me => by
  rcases List.mem_cons.mp me with rfl | me
  · exact hx
  · exact hl e me

theorem merge_fields (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 2) (fun m => Erlang.orddict.«merge/3» (D m) (mergeFun S) (fieldsTerm l₁) (fieldsTerm l₂))
      (Fields E) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    refine Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => ?_⟩
    unfold Erlang.orddict.«merge/3»
    simp [fieldsTerm, mergeFun, Erlang.erlang.«is_function/2»]
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ =>
      refine Or.inl ⟨fieldsTerm l₂, ⟨l₂, rfl, h₂⟩, fun m _ => ?_⟩
      unfold Erlang.orddict.«merge/3»
      cases l₂ <;> simp [fieldsTerm, mergeFun, Erlang.erlang.«is_function/2»]
    | x :: xs, [] =>
      refine Or.inl ⟨fieldsTerm (x :: xs), ⟨x :: xs, rfl, h₁⟩, fun m _ => ?_⟩
      unfold Erlang.orddict.«merge/3»
      simp [fieldsTerm, mergeFun, Erlang.erlang.«is_function/2»]
    | x :: xs, y :: ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel x.1 y.1) x.1 y.1
      · rcases ih xs (y :: ys) (by simp; omega) hxs h₂ with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
        · refine Or.inl ⟨fieldsTerm (x :: l), ⟨x :: l, rfl, fields_cons hx hl⟩, fun m hm => ?_⟩
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp] at this ⊢
          simp [this]
        · refine Or.inr fun m hm => ?_
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp] at this ⊢
          simp [this]
      · rcases merge_fun ops S x.1 x.2 y.2 hx hy with ⟨v, fv, hv⟩ | hv
        · rcases ih xs ys (by omega) hxs hys with ⟨r, ⟨l, rfl, hl⟩, run⟩ | run
          · refine Or.inl ⟨fieldsTerm ((x.1, v) :: l), ⟨(x.1, v) :: l, rfl, fields_cons fv hl⟩, fun m hm => ?_⟩
            obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
            have h1 := hv n hn
            have h2 := run (n + 1) hm
            unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, mergeFun,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at h2 ⊢
            simp [h1, h2]
          · refine Or.inr fun m hm => ?_
            obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
            have h1 := hv n hn
            have h2 := run (n + 1) hm
            unfold Erlang.orddict.«merge/3»
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, mergeFun,
              Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure] at h2 ⊢
            simp [h1, h2]
        · refine Or.inr fun m hm => ?_
          obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
          have h1 := hv n hn
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, mergeFun,
            Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-0-/3».pure]
          simp [h1]
      · rcases ih (x :: xs) ys (by simp; omega) h₁ hys with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
        · refine Or.inl ⟨fieldsTerm (y :: l), ⟨y :: l, rfl, fields_cons hy hl⟩, fun m hm => ?_⟩
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]
        · refine Or.inr fun m hm => ?_
          have := run m hm
          unfold Erlang.orddict.«merge/3»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]

theorem any1_list (d : Dispatcher) (f : Term) (res : Term → Bool) :
    ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (boolAtom (res x))) →
      Erlang.lists.«any_1/2» d f (Term.list l) = .ok (boolAtom (l.any res)) := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«any_1/2», boolAtom]
  | cons x xs ih =>
    intro hf
    rw [Erlang.lists.«any_1/2».eq_def]
    have hx := hf x List.mem_cons_self
    have tail := ih fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;> simp [hx, h, boolAtom, tail]

theorem any_list (d : Dispatcher) (m nm : String) (caps : Array Term) (res : Term → Bool) (l : List Term)
    (hf : ∀ x ∈ l, d.pure (.function false m nm 1 caps) #[x] = .ok (boolAtom (res x))) :
    Erlang.lists.«any/2» d (.function false m nm 1 caps) (Term.list l) = .ok (boolAtom (l.any res)) := by
  cases l with
  | nil => simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», boolAtom]
  | cons x xs =>
    have hx := hf x List.mem_cons_self
    have tail := any1_list d _ res xs fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;>
      simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», hx, h, boolAtom, tail]

theorem all1_list (d : Dispatcher) (f : Term) (res : Term → Bool) :
    ∀ l : List Term, (∀ x ∈ l, d.pure f #[x] = .ok (boolAtom (res x))) →
      Erlang.lists.«all_1/2» d f (Term.list l) = .ok (boolAtom (l.all res)) := by
  intro l
  induction l with
  | nil => intro _; simp [Erlang.lists.«all_1/2», boolAtom]
  | cons x xs ih =>
    intro hf
    rw [Erlang.lists.«all_1/2».eq_def]
    have hx := hf x List.mem_cons_self
    have tail := ih fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;> simp [hx, h, boolAtom, tail]

theorem all_list (d : Dispatcher) (m nm : String) (caps : Array Term) (res : Term → Bool) (l : List Term)
    (hf : ∀ x ∈ l, d.pure (.function false m nm 1 caps) #[x] = .ok (boolAtom (res x))) :
    Erlang.lists.«all/2» d (.function false m nm 1 caps) (Term.list l) = .ok (boolAtom (l.all res)) := by
  cases l with
  | nil => simp [Erlang.lists.«all/2», Erlang.erlang.«is_function/2», boolAtom]
  | cons x xs =>
    have hx := hf x List.mem_cons_self
    have tail := all1_list d _ res xs fun y m => hf y (List.mem_cons_of_mem _ m)
    cases h : res x <;>
      simp [Erlang.lists.«all/2», Erlang.erlang.«is_function/2», hx, h, boolAtom, tail]

/-- The optional flag of a field entry. -/
def optFlag (x : Term) : Bool :=
  match x with
  | .tuple #[_, .tuple #[_, .atom "true"]] => Bool.true
  | _ => Bool.false

theorem optFlag_entry (k t : Term) (o : Bool) : optFlag (.tuple #[k, .tuple #[t, boolAtom o]]) = o := by
  cases o <;> rfl

/-- Predicates on the optional flags of fields return Booleans. -/
theorem optional_list (d : Dispatcher) (f : Term) (lam : Term → Except Exception Term)
    (isF : ∀ x, d.pure f #[x] = lam x) (flag : Bool → Bool)
    (lamOk : ∀ k t o, lam (.tuple #[k, .tuple #[t, boolAtom o]]) = .ok (boolAtom (flag o)))
    (l : List (Term × Term)) (hl : ∀ e ∈ l, FieldValue E e.2) :
    ∀ x ∈ l.map (fun e => Term.tuple #[e.1, e.2]), d.pure f #[x] = .ok (boolAtom (flag (optFlag x))) := by
  intro x mx
  obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
  obtain ⟨t, o, ho, -⟩ := hl e me
  rw [isF, ho, lamOk, optFlag_entry]

theorem closed_fun₀ (k t : Term) (o : Bool) :
    Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-0-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
      .ok (boolAtom (!o)) := by
  cases o <;> simp [Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-0-/1», boolAtom,
    Erlang.erlang.«not/1»]

theorem closed_fun₁ (k t : Term) (o : Bool) :
    Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-1-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
      .ok (boolAtom (!o)) := by
  cases o <;> simp [Elixir.Module.Types.Descr.«-map_literal_intersection_closed/4-fun-1-/1», boolAtom,
    Erlang.erlang.«not/1»]

theorem closed_fields (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m)
      (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
  have tails : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
      ∃ b, ∀ m, Lynx.Except.orElse
        (Erlang.lists.«any/2» (D m)
          (.function false "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-0-" 1 #[]) (fieldsTerm l₁))
        (Erlang.lists.«any/2» (D m)
          (.function false "Elixir.Module.Types.Descr" "-map_literal_intersection_closed/4-fun-1-" 1 #[]) (fieldsTerm l₂))
        Bool.true = .ok (boolAtom b) := by
    intro l₁ l₂ h₁ h₂
    refine ⟨(l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) ||
      (l₂.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x), fun m => ?_⟩
    have r₁ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-0-/1».pure m) (fun o => !o)
      closed_fun₀ l₁ h₁)
    have r₂ := any_list (D m) _ _ _ (fun x => !optFlag x) _ (optional_list (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_closed/4-fun-1-/1».pure m) (fun o => !o)
      closed_fun₁ l₂ h₂)
    simp only [fieldsTerm] at r₁ r₂ ⊢
    rw [r₁, r₂]
    cases (l₁.map fun e => Term.tuple #[e.1, e.2]).any (fun x => !optFlag x) <;>
      simp [boolAtom, Lynx.Except.orElse] <;> rfl
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
      (l₁ = [] ∨ l₂ = []) →
      Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_closed/4» (D m)
        (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
    intro l₁ l₂ h₁ h₂ empty
    obtain ⟨b, hb⟩ := tails l₁ l₂ h₁ h₂
    cases b
    · refine Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => ?_⟩
      have hb := hb m
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
    · refine Or.inr fun m _ => ?_
      have hb := hb m
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
    | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁ _ List.mem_cons_self
      obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂ _ List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel k₁ k₂) k₁ k₂
      · cases o₁
        · refine Or.inr fun m _ => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs ((k₂, _) :: ys) (by simp; omega) hxs h₂ with ⟨v, hv, run⟩ | run
          · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
          · refine Or.inr fun m hm => ?_
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
      · obtain ⟨e, fe, run⟩ := ops.inter f₁ f₂
        obtain ⟨b, empty⟩ := ops.empty fe S
        have dispatch : ∀ m, K + 1 ≤ m → Lynx.Dispatcher.pure (D m) bareIntersection #[t₁, t₂] = .ok e := by
          intro m hm
          obtain ⟨n, rfl, hn⟩ := succ_of_le hm
          rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
          exact run n hn
        have value : FieldValue E (.tuple #[e, boolAtom (o₁ && o₂)]) := ⟨e, _, rfl, fe⟩
        have notLt : ¬(Term.compare (Term.fuel k₁ k₂) k₁ k₂).isLT = Bool.true := by simp [cmp]
        have notGt : ¬(Term.compare (Term.fuel k₁ k₂) k₁ k₂).isGT = Bool.true := by simp [cmp]
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ b = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          refine Or.inr fun m hm => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          cases o₁ <;> cases o₂ <;> simp at o <;>
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega)]
        · rcases ih xs ys (by omega) hxs hys with ⟨r, ⟨l, rfl, hl⟩, rest⟩ | rest
          · refine Or.inl ⟨fieldsTerm ((k₁, .tuple #[e, boolAtom (o₁ && o₂)]) :: l),
              ⟨_, rfl, fields_cons value hl⟩, fun m hm => ?_⟩
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
          · refine Or.inr fun m hm => ?_
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
      · have cmp' : Term.compare (Term.fuel k₂ k₁) k₂ k₁ = .lt := Lynx.Term.compare_lt_of_gt cmp
        cases o₂
        · refine Or.inr fun m _ => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom, isMember]
        · rcases ih ((k₁, _) :: xs) ys (by simp; omega) h₁ hys with ⟨v, hv, run⟩ | run
          · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember] using this
          · refine Or.inr fun m hm => ?_
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember] using this

theorem open_closed_fun (k t : Term) (o : Bool) :
    Elixir.Module.Types.Descr.«-map_literal_intersection_open_closed/4-fun-0-/1» (.tuple #[k, .tuple #[t, boolAtom o]]) =
      .ok (boolAtom o) := by
  simp [Elixir.Module.Types.Descr.«-map_literal_intersection_open_closed/4-fun-0-/1»]

theorem open_closed_fields (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m)
      (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
  have tailCase : ∀ (l₁ l₂ : List (Term × Term)), (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
      (l₁ = [] ∨ l₂ = []) →
      Throws (K + 1) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4» (D m)
        (fieldsTerm l₁) (fieldsTerm l₂) bareIntersection (.map S)) (Fields E) := by
    intro l₁ l₂ h₁ h₂ empty
    have hb := fun m => all_list (D m) _ _ _ (fun x => optFlag x) _ (optional_list (D m) _ _
      (Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection_open_closed/4-fun-0-/1».pure m)
      (fun o => o) open_closed_fun l₁ h₁)
    cases b : (l₁.map fun e => Term.tuple #[e.1, e.2]).all (fun x => optFlag x)
    · refine Or.inr fun m _ => ?_
      have hb := hb m
      rw [b] at hb
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
    · refine Or.inl ⟨fieldsTerm l₂, ⟨l₂, rfl, h₂⟩, fun m _ => ?_⟩
      have hb := hb m
      rw [b] at hb
      unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
      rcases empty with rfl | rfl
      · cases l₂ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
      · cases l₁ <;> simp [fieldsTerm] at hb ⊢ <;> simp [hb, boolAtom]
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    exact tailCase l₁ l₂ h₁ h₂ (Or.inl (List.eq_nil_of_length_eq_zero (by omega)))
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ => exact tailCase [] l₂ h₁ h₂ (Or.inl rfl)
    | x :: xs, [] => exact tailCase (x :: xs) [] h₁ h₂ (Or.inr rfl)
    | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      obtain ⟨t₁, o₁, rfl, f₁⟩ := h₁ _ List.mem_cons_self
      obtain ⟨t₂, o₂, rfl, f₂⟩ := h₂ _ List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel k₁ k₂) k₁ k₂
      · cases o₁
        · refine Or.inr fun m _ => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», cmp, boolAtom, isMember]
        · rcases ih xs ((k₂, _) :: ys) (by simp; omega) hxs h₂ with ⟨v, hv, run⟩ | run
          · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
          · refine Or.inr fun m hm => ?_
            have := run m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simpa [fieldsTerm, Lynx.Except.guard, Erlang.erlang.«</2», cmp, boolAtom, isMember] using this
      · obtain ⟨e, fe, run⟩ := ops.inter f₁ f₂
        obtain ⟨b, empty⟩ := ops.empty fe S
        have dispatch : ∀ m, K + 1 ≤ m → Lynx.Dispatcher.pure (D m) bareIntersection #[t₁, t₂] = .ok e := by
          intro m hm
          obtain ⟨n, rfl, hn⟩ := succ_of_le hm
          rw [bareIntersection, Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure]
          exact run n hn
        have value : FieldValue E (.tuple #[e, boolAtom (o₁ && o₂)]) := ⟨e, _, rfl, fe⟩
        by_cases thrown : (o₁ && o₂) = Bool.false ∧ b = Bool.true
        · obtain ⟨o, rfl⟩ := thrown
          refine Or.inr fun m hm => ?_
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          cases o₁ <;> cases o₂ <;> simp at o <;>
            simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
              isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega)]
        · rcases ih xs ys (by omega) hxs hys with ⟨r, ⟨l, rfl, hl⟩, rest⟩ | rest
          · refine Or.inl ⟨fieldsTerm ((k₁, .tuple #[e, boolAtom (o₁ && o₂)]) :: l),
              ⟨_, rfl, fields_cons value hl⟩, fun m hm => ?_⟩
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
          · refine Or.inr fun m hm => ?_
            have r := rest m hm
            unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
            simp only [fieldsTerm] at r
            cases o₁ <;> cases o₂ <;> cases b <;> simp at thrown <;>
              simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, boolAtom,
                isMember, Lynx.Except.andAlso, dispatch m hm, empty m (by omega), r]
      · rcases ih ((k₁, _) :: xs) ys (by simp; omega) h₁ hys with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
        · refine Or.inl ⟨fieldsTerm ((k₂, _) :: l), ⟨_, rfl, fields_cons (h₂ _ List.mem_cons_self) hl⟩,
            fun m hm => ?_⟩
          have := run m hm
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]
        · refine Or.inr fun m hm => ?_
          have := run m hm
          unfold Elixir.Module.Types.Descr.«map_literal_intersection_open_closed/4»
          simp [fieldsTerm, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp] at this ⊢
          simp [this]

/-- Map tags: open, closed, or domains, the types of the values of each kind of keys. -/
def MapTag (E : Term → Prop) (tag : Term) : Prop :=
  tag = .atom "open" ∨ tag = .atom "closed" ∨ ∃ dl : List (Term × Term), tag = fieldsTerm dl ∧ ∀ e ∈ dl, E e.2

/-- Lines of maps: a tag and fields. -/
def MapPos (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)), p = .tuple #[tag, fieldsTerm l] ∧ MapTag E tag ∧
    ∀ e ∈ l, FieldValue E e.2

/-- Map literals: a key, a tag, and fields. -/
def MapLit (E : Term → Prop) (t : Term) : Prop :=
  ∃ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] ∧
    MapTag E tag ∧ ∀ e ∈ l, FieldValue E e.2

theorem Throws.wrap {K : Nat} {e : Nat → Except Exception Term} (h : Throws K e (Fields E)) {tag : Term}
    (htag : MapTag E tag) :
    Throws K (fun m => e m >>= fun r => pure (Term.tuple #[tag, r])) (MapPos E) := by
  rcases h with ⟨v, ⟨l, rfl, hl⟩, run⟩ | run
  · exact Or.inl ⟨_, ⟨tag, l, rfl, htag, hl⟩, fun m hm => by simp [run m hm]⟩
  · exact Or.inr fun m hm => by simp [run m hm]

theorem Throws.mono {K K' : Nat} {e : Nat → Except Exception Term} {P : Term → Prop} (h : Throws K e P)
    (le : K ≤ K') : Throws K' e P := by
  rcases h with ⟨v, hv, run⟩ | run
  · exact Or.inl ⟨v, hv, fun m hm => run m (by omega)⟩
  · exact Or.inr fun m hm => run m (by omega)

theorem Throws.bind {K : Nat} {e : Nat → Except Exception Term} {P Q : Term → Prop} (h : Throws K e P)
    {f : Nat → Term → Except Exception Term} (hf : ∀ v, P v → Throws K (fun m => f m v) Q) :
    Throws K (fun m => e m >>= f m) Q := by
  rcases h with ⟨v, hv, run⟩ | run
  · rcases hf v hv with ⟨w, hw, run'⟩ | run'
    · exact Or.inl ⟨w, hw, fun m hm => by simp [run m hm, run' m hm]⟩
    · exact Or.inr fun m hm => by simp [run m hm, run' m hm]
  · exact Or.inr fun m hm => by simp [run m hm]

theorem MapTag.atom_open : MapTag E (.atom "open") := Or.inl rfl

theorem MapTag.atom_closed : MapTag E (.atom "closed") := Or.inr (Or.inl rfl)

theorem MapTag.of_string {tag : String} (g : tag = "open" ∨ tag = "closed") : MapTag E (.atom tag) := by
  rcases g with rfl | rfl
  · exact MapTag.atom_open
  · exact MapTag.atom_closed

theorem fieldsTerm_ne_atom (l : List (Term × Term)) (s : String) : fieldsTerm l ≠ .atom s := by
  cases l <;> simp [fieldsTerm, Term.list]

/-- `orddict:find/2` finds the value of an entry, or nothing. -/
theorem find_entry_or_error (k : Term) : ∀ l : List (Term × Term),
    Erlang.orddict.«find/2» k (fieldsTerm l) = .ok (.atom "error") ∨
      ∃ e ∈ l, Erlang.orddict.«find/2» k (fieldsTerm l) = .ok (.tuple #[.atom "ok", e.2])
  | [] => Or.inl (by rw [Erlang.orddict.«find/2».eq_def]; simp [fieldsTerm, Term.list])
  | (a, v) :: t => by
    rcases cmp : Term.compare (Term.fuel k a) k a
    · left
      rw [Erlang.orddict.«find/2».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
    · right
      refine ⟨(a, v), List.mem_cons_self, ?_⟩
      rw [Erlang.orddict.«find/2».eq_def]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
    · have step : Erlang.orddict.«find/2» k (fieldsTerm ((a, v) :: t)) = Erlang.orddict.«find/2» k (fieldsTerm t) := by
        conv => lhs; rw [Erlang.orddict.«find/2».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
      rw [step]
      rcases find_entry_or_error k t with h | ⟨e, me, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ me, h⟩

/-- The field of the atom keys outside the fields of a literal: `term()` when open, `none()` when closed, and
the atom domain, if any, otherwise. -/
theorem tag_field_ok (hterm : E (.atom "term")) (hnone : E (.map [])) {tag : Term} (g : MapTag E tag) :
    ∃ f, Elixir.Module.Types.Descr.«map_key_tag_to_field/1» tag = .ok f ∧ FieldValue E f := by
  rcases g with rfl | rfl | ⟨dl, rfl, hdl⟩
  · exact ⟨_, rfl, ⟨_, Bool.true, rfl, hterm⟩⟩
  · exact ⟨_, rfl, ⟨_, Bool.true, rfl, hnone⟩⟩
  · have ne := fieldsTerm_ne_atom dl
    rcases find_entry_or_error (.atom "atom") dl with h | ⟨e, me, h⟩
    · refine ⟨_, ?_, ⟨_, Bool.true, rfl, hnone⟩⟩
      generalize fieldsTerm dl = T at h ne
      rw [Elixir.Module.Types.Descr.«map_key_tag_to_field/1».eq_def]
      split
      · exact absurd rfl (ne "open")
      · exact absurd rfl (ne "closed")
      · simp [h, boolAtom]
    · refine ⟨_, ?_, ⟨_, Bool.true, rfl, hdl e me⟩⟩
      generalize fieldsTerm dl = T at h ne
      rw [Elixir.Module.Types.Descr.«map_key_tag_to_field/1».eq_def]
      split
      · exact absurd rfl (ne "open")
      · exact absurd rfl (ne "closed")
      · simp [h, boolAtom]

/-- Domains intersect kind by kind, dropping the empty intersections. -/
theorem domain_fields_ok (ops : ElemOk E K) (S : List (Term × Term)) : ∀ N (l₁ l₂ : List (Term × Term)),
    l₁.length + l₂.length ≤ N → (∀ e ∈ l₁, E e.2) → (∀ e ∈ l₂, E e.2) → ∃ l : List (Term × Term),
      (∀ e ∈ l, E e.2) ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«map_domain_intersection_fields/3» (D m)
        (fieldsTerm l₁) (fieldsTerm l₂) (.map S) = .ok (fieldsTerm l) := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size _ _
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨[], by simp, fun m _ => by
      rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list]⟩
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    match l₁, l₂ with
    | [], l₂ =>
      exact ⟨[], by simp, fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
        cases l₂ <;> simp [fieldsTerm, Term.list]⟩
    | x :: xs, [] =>
      exact ⟨[], by simp, fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]; simp [fieldsTerm, Term.list]⟩
    | x :: xs, y :: ys =>
      have hxs : ∀ e ∈ xs, E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel x.1 y.1) x.1 y.1
      · obtain ⟨l, hl, run⟩ := ih xs (y :: ys) (by simp; omega) hxs h₂
        refine ⟨l, hl, fun m hm => ?_⟩
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run m hm]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
      · obtain ⟨c, hc, inter⟩ := ops.inter (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
        obtain ⟨b, empty⟩ := ops.empty hc S
        obtain ⟨l, hl, run⟩ := ih xs ys (by omega) hxs hys
        cases b
        · refine ⟨(x.1, c) :: l, fun e me => ?_, fun m hm => ?_⟩
          · rcases List.mem_cons.mp me with rfl | me
            · exact hc
            · exact hl e me
          · have r := run m hm
            simp only [fieldsTerm] at r
            rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def]
            simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
              inter m hm, empty m hm, boolAtom, isMember, r]
        · refine ⟨l, hl, fun m hm => ?_⟩
          rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run m hm]
          simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp,
            inter m hm, empty m hm, boolAtom, isMember]
      · obtain ⟨l, hl, run⟩ := ih (x :: xs) ys (by simp; omega) h₁ hys
        refine ⟨l, hl, fun m hm => ?_⟩
        rw [Elixir.Module.Types.Descr.«map_domain_intersection_fields/3».eq_def, ← run m hm]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]

/-- The domains of intersections of map literals. -/
theorem domain_inter_ok (ops : ElemOk E K) (S : List (Term × Term)) {t₁ t₂ : Term} (g₁ : MapTag E t₁)
    (g₂ : MapTag E t₂) : ∃ t, MapTag E t ∧ ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) t₁ t₂ (.map S) = .ok t := by
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, h₁⟩
  · exact ⟨t₂, g₂, fun m _ => by
      rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]
      rcases g₂ with rfl | rfl | ⟨dl₂, rfl, _⟩ <;> simp [fieldsTerm_ne_atom]⟩
  · exact ⟨_, MapTag.atom_closed, fun m _ => by
      rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp⟩
  · rcases g₂ with rfl | rfl | ⟨dl₂, rfl, h₂⟩
    · exact ⟨_, Or.inr (Or.inr ⟨dl₁, rfl, h₁⟩), fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom]⟩
    · exact ⟨_, MapTag.atom_closed, fun m _ => by
        rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]; simp [fieldsTerm_ne_atom]⟩
    · obtain ⟨l, hl, run⟩ := domain_fields_ok ops S _ dl₁ dl₂ (Nat.le_refl _) h₁ h₂
      have step : ∀ m, K ≤ m → Elixir.Module.Types.Descr.«map_domain_intersection/3» (D m) (fieldsTerm dl₁)
          (fieldsTerm dl₂) (.map S) = (match fieldsTerm l with
            | .nil => Except.ok (Term.atom "closed")
            | t => Except.ok t) := by
        intro m hm
        have r := run m hm
        have ne₁ := fieldsTerm_ne_atom dl₁
        have ne₂ := fieldsTerm_ne_atom dl₂
        generalize fieldsTerm dl₁ = T₁ at r ne₁
        generalize fieldsTerm dl₂ = T₂ at r ne₂
        rw [Elixir.Module.Types.Descr.«map_domain_intersection/3».eq_def]
        split
        · exact absurd rfl (ne₁ "closed")
        · exact absurd rfl (ne₂ "closed")
        · exact absurd rfl (ne₁ "open")
        · exact absurd rfl (ne₂ "open")
        · simp only [r]
          cases fieldsTerm l <;> rfl
      cases l with
      | nil => exact ⟨_, MapTag.atom_closed, fun m hm => by rw [step m hm]; rfl⟩
      | cons x xs =>
        exact ⟨_, Or.inr (Or.inr ⟨x :: xs, rfl, hl⟩), fun m hm => by
          rw [step m hm]; simp [fieldsTerm, Term.list]⟩

def mergeFun₁ (S : List (Term × Term)) : Term :=
  .function false "Elixir.Module.Types.Descr" "-map_literal_intersection/6-fun-1-" 3 #[bareIntersection, .map S]

theorem merge_fun₁_eq (d : Dispatcher) (f s k a b : Term) :
    Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-1-/5» d f s k a b =
      Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5» d f s k a b := by
  unfold Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-1-/5»
    Elixir.Module.Types.Descr.«-map_literal_intersection/6-fun-0-/5»
  rfl

/-- Merging a field with a default field. -/
theorem merge_call₁ (ops : ElemOk E K) (S : List (Term × Term)) (key v₁ v₂ : Term) (h₁ : FieldValue E v₁)
    (h₂ : FieldValue E v₂) :
    Throws (K + 2) (fun m => Lynx.Dispatcher.pure (D m) (mergeFun₁ S) #[key, v₁, v₂]) (FieldValue E) := by
  rcases merge_fun ops S key v₁ v₂ h₁ h₂ with ⟨v, hv, run⟩ | run
  · refine Or.inl ⟨v, hv, fun m hm => ?_⟩
    obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
    simp [mergeFun₁, Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-1-/3».pure,
      merge_fun₁_eq, run n hn]
  · refine Or.inr fun m hm => ?_
    obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
    simp [mergeFun₁, Erlang.program.«Elixir.Module.Types.Descr:-map_literal_intersection/6-fun-1-/3».pure,
      merge_fun₁_eq, run n hn]

theorem Throws.congr {K : Nat} {e e' : Nat → Except Exception Term} {P : Term → Prop}
    (h : ∀ m, K ≤ m → e m = e' m) (h' : Throws K e' P) : Throws K e P := by
  rcases h' with ⟨v, hv, run⟩ | run
  · exact Or.inl ⟨v, hv, fun m hm => by rw [h m hm]; exact run m hm⟩
  · exact Or.inr fun m hm => by rw [h m hm]; exact run m hm

/-- Fields merged with defaults: keys of one side meet the default field of the other. -/
theorem merge_defaults (ops : ElemOk E K) (S : List (Term × Term)) {d₁ d₂ : Term} (fd₁ : FieldValue E d₁)
    (fd₂ : FieldValue E d₂) : ∀ N (l₁ l₂ : List (Term × Term)), l₁.length + l₂.length ≤ N →
    (∀ e ∈ l₁, FieldValue E e.2) → (∀ e ∈ l₂, FieldValue E e.2) →
    Throws (K + 2) (fun m => Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D m) (fieldsTerm l₁) d₁
      (fieldsTerm l₂) d₂ (mergeFun₁ S)) (Fields E) := by
  have call := merge_call₁ ops S
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ size h₁ h₂
    have : l₁ = [] ∧ l₂ = [] := by constructor <;> (apply List.eq_nil_of_length_eq_zero; omega)
    obtain ⟨rfl, rfl⟩ := this
    exact Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => by
      dsimp only; rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]⟩
  | succ N ih =>
    intro l₁ l₂ size h₁ h₂
    have step : ∀ (k : Term) {v₁ v₂ : Term} (l₁' l₂' : List (Term × Term)),
        FieldValue E v₁ → FieldValue E v₂ → l₁'.length + l₂'.length ≤ N →
        (∀ e ∈ l₁', FieldValue E e.2) → (∀ e ∈ l₂', FieldValue E e.2) →
        Throws (K + 2) (fun m => Lynx.Dispatcher.pure (D m) (mergeFun₁ S) #[k, v₁, v₂] >>= fun r =>
          Elixir.Module.Types.Descr.«fields_merge_with_defaults/5» (D m) (fieldsTerm l₁') d₁ (fieldsTerm l₂') d₂
            (mergeFun₁ S) >>= fun t => pure (Term.cons (.tuple #[k, r]) t)) (Fields E) := by
      intro k v₁ v₂ l₁' l₂' f₁ f₂ sz g₁ g₂
      refine Throws.bind (call k v₁ v₂ f₁ f₂) fun r hr => ?_
      refine Throws.bind (ih l₁' l₂' sz g₁ g₂) fun t ht => ?_
      obtain ⟨l, rfl, hl⟩ := ht
      exact Or.inl ⟨fieldsTerm ((k, r) :: l), ⟨_, rfl, fields_cons hr hl⟩, fun m _ => rfl⟩
    match l₁, l₂ with
    | [], [] =>
      exact Or.inl ⟨.nil, ⟨[], rfl, by simp⟩, fun m _ => by
        dsimp only; rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]; simp [fieldsTerm, Term.list]⟩
    | [], y :: ys =>
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      refine Throws.congr (fun m _ => ?_) (step y.1 [] ys fd₁ (h₂ y List.mem_cons_self) (by simp at size ⊢; omega)
        (by simp) hys)
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simp [fieldsTerm, Term.list]
    | x :: xs, [] =>
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      refine Throws.congr (fun m _ => ?_) (step x.1 xs [] (h₁ x List.mem_cons_self) fd₂ (by simp at size ⊢; omega)
        hxs (by simp))
      rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
      simp [fieldsTerm, Term.list]
    | x :: xs, y :: ys =>
      have hx := h₁ x List.mem_cons_self
      have hy := h₂ y List.mem_cons_self
      have hxs : ∀ e ∈ xs, FieldValue E e.2 := fun e me => h₁ e (List.mem_cons_of_mem _ me)
      have hys : ∀ e ∈ ys, FieldValue E e.2 := fun e me => h₂ e (List.mem_cons_of_mem _ me)
      simp only [List.length_cons] at size
      rcases cmp : Term.compare (Term.fuel x.1 y.1) x.1 y.1
      · refine Throws.congr (fun m _ => ?_) (step x.1 xs (y :: ys) hx fd₂ (by simp; omega) hxs h₂)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
      · refine Throws.congr (fun m _ => ?_) (step x.1 xs ys hx hy (by omega) hxs hys)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]
      · refine Throws.congr (fun m _ => ?_) (step y.1 (x :: xs) ys fd₁ hy (by simp; omega) h₁ hys)
        rw [Elixir.Module.Types.Descr.«fields_merge_with_defaults/5».eq_def]
        simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp]

/-- Intersections of map literals with domains merge their fields with the defaults of the other side. -/
theorem literal_domains_ok (ops : ElemOk E K) (S : List (Term × Term)) {t₁ t₂ : Term} (g₁ : MapTag E t₁)
    (g₂ : MapTag E t₂) (notAtoms : ∀ s₁ s₂, ¬(t₁ = .atom s₁ ∧ t₂ = .atom s₂)) (l₁ l₂ : List (Term × Term))
    (h₁ : ∀ e ∈ l₁, FieldValue E e.2) (h₂ : ∀ e ∈ l₂, FieldValue E e.2) :
    Throws (K + 2) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection/6» (D m)
      t₁ (fieldsTerm l₁) t₂ (fieldsTerm l₂) bareIntersection (.map S)) (MapPos E) := by
  obtain ⟨d₁, run₁, fd₁⟩ := tag_field_ok ops.term ops.none g₁
  obtain ⟨d₂, run₂, fd₂⟩ := tag_field_ok ops.term ops.none g₂
  obtain ⟨t, gt, runT⟩ := domain_inter_ok ops S g₁ g₂
  have merged := merge_defaults ops S fd₁ fd₂ _ l₁ l₂ (Nat.le_refl _) h₁ h₂
  refine Throws.congr (fun m hm => ?_) (merged.wrap gt)
  unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
  split <;> try (exfalso; exact notAtoms _ _ ⟨rfl, rfl⟩)
  simp [run₁, run₂, runT m (by omega), mergeFun₁]

theorem literal_ok (ops : ElemOk E K) (S : List (Term × Term)) {t₁ t₂ : Term} (g₁ : MapTag E t₁)
    (g₂ : MapTag E t₂) (l₁ l₂ : List (Term × Term)) (h₁ : ∀ e ∈ l₁, FieldValue E e.2)
    (h₂ : ∀ e ∈ l₂, FieldValue E e.2) :
    Throws (K + 2) (fun m => Elixir.Module.Types.Descr.«map_literal_intersection/6» (D m)
      t₁ (fieldsTerm l₁) t₂ (fieldsTerm l₂) bareIntersection (.map S)) (MapPos E) := by
  have size := Nat.le_refl (l₁.length + l₂.length)
  have size' : l₂.length + l₁.length ≤ l₁.length + l₂.length := by omega
  have general := literal_domains_ok ops S g₁ g₂
  rcases g₁ with rfl | rfl | ⟨dl₁, rfl, -⟩ <;> rcases g₂ with rfl | rfl | ⟨dl₂, rfl, -⟩ <;>
    try exact general (fun _ _ h => fieldsTerm_ne_atom _ _ (by first | exact h.1 | exact h.2)) l₁ l₂ h₁ h₂
  all_goals unfold Elixir.Module.Types.Descr.«map_literal_intersection/6»
  · have := (merge_fields ops S _ l₁ l₂ size h₁ h₂).wrap MapTag.atom_open
    simpa [mergeFun] using this.mono (by omega)
  · simpa using ((open_closed_fields ops S _ l₁ l₂ size h₁ h₂).wrap MapTag.atom_closed).mono (by omega)
  · simpa using ((open_closed_fields ops S _ l₂ l₁ size' h₂ h₁).wrap MapTag.atom_closed).mono (by omega)
  · simpa using ((closed_fields ops S _ l₁ l₂ size h₁ h₂).wrap MapTag.atom_closed).mono (by omega)

theorem map_line_ok (ops : ElemOk E K) (S : List (Term × Term)) {p t : Term} (hp : MapPos E p) (ht : MapLit E t) :
    (∀ m, K + 2 ≤ m → Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) p t (.map S) =
        .ok (.atom "empty")) ∨
      ∃ p', MapPos E p' ∧ ∀ m, K + 2 ≤ m →
        Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) p t (.map S) = .ok p' := by
  obtain ⟨t₁, l₁, rfl, g₁, h₁⟩ := hp
  obtain ⟨k, t₂, l₂, rfl, g₂, h₂⟩ := ht
  rcases literal_ok ops S g₁ g₂ l₁ l₂ h₁ h₂ with ⟨v, hv, run⟩ | run
  · right
    refine ⟨v, hv, fun m hm => ?_⟩
    have run := run m hm
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run]
  · left
    intro m hm
    have run := run m hm
    unfold Elixir.Module.Types.Descr.«map_line_intersection/3»
    simp [Lynx.Except.tryWith, bareIntersection] at run ⊢
    simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason]

theorem map_bdd_empty_unsat (ops : ElemOk E K) {m : Nat} (hm : K + 2 ≤ m) {ok : Term → Prop} {r : Term}
    (wr : Bdd ok r) (lits : ∀ t, ok t → MapLit E t) (unsat : Unsat r) :
    ∀ pos negs S, MapPos E pos →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos negs r (.map S) = .ok (.atom "true") := by
  revert lits unsat
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLit E t) → Unsat r → ∀ pos negs S, MapPos E pos →
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D m) pos negs r (.map S) = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro _ _ _ pos negs S _
    unfold Elixir.Module.Types.Descr.«map_bdd_empty?/4»
    rfl
  · intro _ k x y _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro ok h lit c u d _ okl hc hu hd ic iu id lits unsat pos negs S hp
    obtain ⟨uc, uu, ud⟩ := unsat_children hc hu hd unsat
    have lits' : ∀ t, Above ok lit t → MapLit E t := fun t ht => lits t ht.1
    have dTrue := id lits' ud pos (.cons lit negs) S hp
    have uTrue := iu lits' uu pos negs S hp
    unfold Elixir.Module.Types.Descr.«map_bdd_empty?/4»
    simp only [dTrue, uTrue, Lynx.Except.andAlso]
    rcases map_line_ok ops S hp (lits lit okl) with line | ⟨p', hp', line⟩
    · simp [line m hm]
    · have cTrue := ic lits' uc p' negs S hp'
      obtain ⟨tg, l, rfl, -, -⟩ := hp'
      simp [line m hm, cTrue]

def EmptyMap (K : Nat) (r : Term) : Prop :=
  ∀ m S, K + 2 ≤ m → Elixir.Module.Types.Descr.«map_empty?/2» (D m) r (.map S) = .ok (.atom "true")

theorem map_empty_unsat (ops : ElemOk E K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
    (lits : ∀ t, ok t → MapLit E t) (unsat : Unsat r) : EmptyMap K r := by
  intro m S hm
  have run := fun S' => map_bdd_empty_unsat ops hm wr lits unsat (.tuple #[.atom "open", .nil]) .nil S'
    ⟨.atom "open", [], rfl, MapTag.atom_open, by simp⟩
  unfold Elixir.Module.Types.Descr.«map_empty?/2»
  by_cases seen : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "map") r) e.1) (.cons (.atom "map") r) e.1 = .eq)) = Bool.true
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen,
      Term.false, Erlang.maps.«put/3», run]

def MapOk (E : Term → Prop) (t : Term) : Prop := MapLit E t ∧ ¬IsTop t

/-- Map types are the top map literal or ordered BDDs of other map literals. -/
abbrev MapField (E : Term → Prop) (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd (MapOk E) w

def MapCancel (K : Nat) (x nb : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«map_intersection/2» x nb = .ok r ∧
    (kept (.atom "map", r) = Bool.true → EmptyMap K r)

theorem map_intersection_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«map_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«map_intersection/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem map_cancel (ops : ElemOk E K) (x : Term) (field : MapField E x) :
    ∃ nb, Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok nb ∧
      (kept (.atom "map", nb) = Bool.true → MapCancel K x nb) := by
  rcases field with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«map_difference/2»], fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
    unfold Elixir.Module.Types.Descr.«map_difference/2»
    simp [diff_leaf_top]
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun _ => ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩⟩
    · unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_bot]
    · unfold Elixir.Module.Types.Descr.«map_intersection/2»
      rfl
  · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
    have wnb := keep _ wx
    refine ⟨nb, ?_, fun _ => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_difference/2»
      split
      · next _ _ e => exact (notTop _ e).elim
      · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact run
      · next h₁ => exact (h₁ _ _ rfl rfl).elim
    · have wl : Bdd (MapLit E) (.tuple #[.integer k, tg, l]) := wx.mono fun _ h => h.1
      obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
      refine ⟨r, ?_, fun _ => map_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
        fun ρ resp => ?_⟩
      · rw [map_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
        exact rr
      · rw [sr ρ resp, sem ρ resp]
        cases eval ρ (.tuple #[.integer k, tg, l]) <;> rfl
  · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
    have wnb := keep _ wx
    refine ⟨nb, ?_, fun _ => ?_⟩
    · unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [run]
    · have wl : Bdd (MapLit E) (.tuple #[.integer h, lit, c, u, d]) := wx.mono fun _ h => h.1
      obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
      refine ⟨r, ?_, fun _ => map_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
        fun ρ resp => ?_⟩
      · rw [map_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
        exact rr
      · rw [sr ρ resp, sem ρ resp]
        cases eval ρ (.tuple #[.integer h, lit, c, u, d]) <;> rfl

/-! Reading the map specification. -/

theorem map_fields_spec (hE : NestedOk E depth) (fs : Term) (h : «map_fields?/2» fs depth = .ok Term.true) :
    ∃ l : List (Term × Term), fs = fieldsTerm l ∧ ∀ e ∈ l, FieldValue E e.2 := by
  unfold «map_fields?/2» at h
  split at h
  · rename_i k t o rest
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨hb, ht⟩, hr⟩ := h
    obtain ⟨l, rfl, hl⟩ := map_fields_spec hE rest hr
    have ob : ∃ b, o = boolAtom b := by
      cases o <;> simp [Erlang.erlang.«is_boolean/1»] at hb
      rename_i name
      by_cases t : name = "true"
      · exact ⟨Bool.true, by simp [boolAtom, t]⟩
      · by_cases f : name = "false"
        · exact ⟨Bool.false, by simp [boolAtom, f]⟩
        · simp [t, f] at hb
    obtain ⟨b, rfl⟩ := ob
    refine ⟨(k, .tuple #[t, boolAtom b]) :: l, rfl, fun e me => ?_⟩
    rcases List.mem_cons.mp me with rfl | me
    · exact ⟨t, b, rfl, hE _ ht⟩
    · exact hl e me
  · exact ⟨[], rfl, by simp⟩
  · simp [Term.true] at h
termination_by sizeOf fs
decreasing_by all_goals (simp_wf; subst_vars; simp; omega)

theorem map_domains_spec (hE : NestedOk E depth) (ds : Term) (h : «map_domains?/2» ds depth = .ok Term.true) :
    ∃ dl : List (Term × Term), ds = fieldsTerm dl ∧ ∀ e ∈ dl, E e.2 := by
  unfold «map_domains?/2» at h
  split at h
  · rename_i k t rest
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨ht, hr⟩ := h
    obtain ⟨dl, rfl, hdl⟩ := map_domains_spec hE rest hr
    refine ⟨(k, t) :: dl, rfl, fun e me => ?_⟩
    rcases List.mem_cons.mp me with rfl | me
    · exact hE _ ht
    · exact hdl e me
  · exact ⟨[], rfl, by simp⟩
  · simp [Term.true] at h
termination_by sizeOf ds
decreasing_by all_goals (simp_wf; subst_vars; simp; omega)

theorem map_tag_spec (hE : NestedOk E depth) (tag : Term) (h : «map_tag?/2» tag depth = .ok Term.true) :
    MapTag E tag := by
  by_cases o : tag = .atom "open"
  · exact Or.inl o
  by_cases c : tag = .atom "closed"
  · exact Or.inr (Or.inl c)
  unfold «map_tag?/2» at h
  simp [isMember, o, c] at h
  obtain ⟨dl, rfl, hdl⟩ := map_domains_spec hE _ h
  exact Or.inr (Or.inr ⟨dl, rfl, hdl⟩)

theorem map_literal_spec (hE : NestedOk E depth) {lit lower : Term}
    (h : «map_literal?/3» lit lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ MapOk E lit := by
  unfold «map_literal?/3» at h
  split at h
  · rename_i key tag fields
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨⟨⟨hk, hlt⟩, htag⟩, hopen⟩, hfields⟩ := h
    cases key <;> simp [Erlang.erlang.«is_integer/1»] at hk
    rename_i k
    have lt : Term.compare (Term.fuel lower (.tuple #[.integer k, tag, fields])) lower (.tuple #[.integer k, tag, fields]) = .lt :=
      Lynx.Term.compare_lt_of_gt (by simpa [Erlang.erlang.«>/2», Ordering.isGT_iff_eq_gt, boolAtom] using hlt)
    have g := map_tag_spec hE tag htag
    obtain ⟨l, rfl, hl⟩ := map_fields_spec hE _ hfields
    refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, tag, l, rfl, g, hl⟩, ?_⟩
    rintro ⟨_, e⟩
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨-, rfl, hnil⟩ := e
    simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», hnil] at hopen
  · simp [Term.true] at h

theorem ordered_map_spec (hE : NestedOk E depth) : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
    «ordered_map_bdd?/3» b lower depth = .ok Term.true → Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ MapOk E t) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «ordered_map_bdd?/3» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := map_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := map_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ MapOk E t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ MapOk E t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

theorem map_bdd_spec (hE : NestedOk E depth) {w : Term} (h : «map_bdd?/2» w depth = .ok Term.true) :
    MapField E w := by
  unfold «map_bdd?/2» at h
  split at h
  · rename_i key
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ((ordered_map_spec hE _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)

end Elixir.STTDescrProofsTest

-- List types are the top list literal or ordered BDDs of other list literals,
-- so negations hold the same literals and the list intersection shortcuts
-- never apply. What remains of a list type and its negation has no line.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term
open BddProofs
open BddProofs

open BddProofs

/-- List literals other than the top literal `{_, term, term}`, which list operations treat as the top type. -/
def ListOk (t : Term) : Prop := ¬∃ k : Term, t = .tuple #[k, .atom "term", .atom "term"]

/-- List literals whose element and tail types are `E`. -/
def ListLit (E : Term → Prop) (t : Term) : Prop :=
  ListOk t ∧ ∃ (k : Int) (a b : Term), t = .tuple #[.integer k, a, b] ∧ E a ∧ E b

theorem bind_true {e : Except Exception Term} {f : Term → Except Exception Term}
    (h : (e >>= f) = .ok (.atom "true")) : ∃ v, e = .ok v ∧ f v = .ok (.atom "true") := by
  cases e with
  | error x => simp [bind, Except.bind] at h
  | ok v => exact ⟨v, rfl, by simpa [bind, Except.bind] using h⟩

theorem list_literal_spec (hE : NestedOk E depth) {lit lower : Term}
    (h : «list_literal?/3» lit lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ ListLit E lit := by
  unfold «list_literal?/3» at h
  split at h
  · rename_i key list last
    obtain ⟨v, hA, hrest⟩ := bind_true h
    obtain ⟨hm, hlast⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp hrest
    have hv : v = .atom "true" := by
      split at hm
      · simp at hm
      · rfl
      · simp at hm
    subst hv
    simp only at hm
    obtain ⟨⟨hint, hgt⟩, hnt⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp hA |>.imp_left
      (Lynx.Except.andAlso_eq_true _ _ _).mp
    cases key <;> simp [Erlang.erlang.«is_integer/1»] at hint
    rename_i k
    simp [Erlang.erlang.«>/2»] at hgt
    refine ⟨⟨k, list, last, rfl⟩, Lynx.Term.compare_lt_of_gt hgt, ?_, k, list, last, rfl, hE _ hm, hE _ hlast⟩
    rintro ⟨_, e⟩
    simp at e
    obtain ⟨-, rfl, rfl⟩ := e
    simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2»] at hnt
  · simp [Term.true] at h

theorem ordered_spec (hE : NestedOk E depth) : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
    «ordered_bdd?/3» b lower depth = .ok Term.true → Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ ListLit E t) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «ordered_bdd?/3» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := list_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := list_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ ListLit E t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ ListLit E t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

/-- List types are the top list literal or ordered BDDs of other list literals. -/
abbrev ListField (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "term", .atom "term"]) ∨ Bdd ListOk w

/-- List types whose literals have element and tail types `E`. -/
abbrev LField (E : Term → Prop) (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "term", .atom "term"]) ∨ Bdd (ListLit E) w

theorem LField.list {w : Term} (h : LField E w) : ListField w := by
  rcases h with top | b
  · exact Or.inl top
  · exact Or.inr (b.mono fun _ h => h.1)

theorem list_bdd_spec (hE : NestedOk E depth) {w : Term} (h : «list_bdd?/2» w depth = .ok Term.true) :
    LField E w := by
  unfold «list_bdd?/2» at h
  split at h
  · rename_i key
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ((ordered_spec hE _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)

/-- Function types map arities to BDDs. -/
def ArityBdds (w : Term) : Prop :=
  ∀ t R, w = .tuple #[t, .map R] → ∀ q v, mapLookup R q = some v → Bdd (fun _ => True) v

theorem arity_bdds_spec (es : List (Term × Term))
    (valid : «arity_bdds?/1» (Term.list (es.map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
    ∀ p ∈ es, Bdd (fun _ => True) p.2 := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons, Term.list, «arity_bdds?/1», Term.true, Lynx.Except.andAlso_eq_true] at valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact (any_bdd_spec _ _ _ (Nat.le_refl _) valid.1).mono fun _ _ => trivial
    · exact ih valid.2 p member

theorem arity_bdds_map (R : List (Term × Term))
    (valid : «arity_bdds?/1» (Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2])) = .ok Term.true) :
    ∀ q v, mapLookup R q = some v → Bdd (fun _ => True) v := by
  intro q v lookup
  obtain ⟨p, mp, -, rfl⟩ := lookup_found _ q v (by rw [mapLookup_mapEntries]; exact lookup)
  exact arity_bdds_spec _ valid p mp

/-- Function literals `{key, args, return}` with `n` arguments, whose argument and return types are `E`. -/
def FunLit (E : Term → Prop) (n : Int) (t : Term) : Prop :=
  ∃ (k : Int) (args : List Term) (ret : Term), t = .tuple #[.integer k, Term.list args, ret] ∧
    (args.length : Int) = n ∧ (∀ a ∈ args, E a) ∧ E ret

/-- The literals of the BDD of arity `q`. -/
def FunArity (E : Term → Prop) (q t : Term) : Prop := ∃ n : Int, q = .integer n ∧ FunLit E n t

/-- Nested function types: unions or negations of maps from arities to BDDs of literals of that arity. -/
def FField (E : Term → Prop) (w : Term) : Prop :=
  ∃ (pos : Bool) (R : List (Term × Term)), w = .tuple #[.atom (if pos then "union" else "negation"), .map R] ∧
    ∀ q v, mapLookup R q = some v → Bdd (FunArity E q) v

theorem fun_literal_spec (hE : NestedOk E depth) {lit lower : Term} {n : Int}
    (h : «fun_literal?/4» lit (.integer n) lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ FunLit E n lit := by
  unfold «fun_literal?/4» at h
  split at h
  · rename_i key args ret
    obtain ⟨h₁, hret⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
    obtain ⟨h₂, hlen⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h₁
    obtain ⟨h₃, hargs⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h₂
    obtain ⟨hint, hgt⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h₃
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at hint
    rename_i k
    obtain ⟨l, rfl, hl⟩ := elements_spec hE hargs
    simp [Erlang.erlang.«>/2»] at hgt
    simp [length_list, Erlang.erlang.«==/2», Term.true] at hlen
    exact ⟨⟨k, _, _, rfl⟩, Lynx.Term.compare_lt_of_gt hgt, k, l, ret, rfl, hlen, hl, hE _ hret⟩
  · simp [Term.true] at h

theorem ordered_fun_spec (hE : NestedOk E depth) (n : Int) : ∀ (s : Nat) (b lower : Term), sizeOf b ≤ s →
    «fun_bdd?/4» b (.integer n) lower depth = .ok Term.true →
      Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ FunLit E n t) b := by
  intro s
  induction s with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ s ih =>
    intro b lower size h
    unfold «fun_bdd?/4» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := fun_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := fun_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ FunLit E n t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ FunLit E n t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

theorem fun_arities_spec (hE : NestedOk E depth) (es : List (Term × Term))
    (valid : «fun_arities?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ p ∈ es, Bdd (FunArity E p.1) p.2 := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    simp only [List.map_cons, Term.list] at valid
    unfold «fun_arities?/2» at valid
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at valid
    obtain ⟨⟨int, bdd⟩, tail⟩ := valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨q, v⟩ := p
      cases q <;> simp [Erlang.erlang.«is_integer/1»] at int
      rename_i n
      exact (ordered_fun_spec hE n _ v _ (Nat.le_refl _) bdd).mono fun t h => ⟨n, rfl, h.2⟩
    · exact ih tail p member

theorem fun_arities_map (hE : NestedOk E depth) (R : List (Term × Term))
    (valid : «fun_arities?/2» (Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ q v, mapLookup R q = some v → Bdd (FunArity E q) v := by
  intro q v lookup
  obtain ⟨p, mp, qp, rfl⟩ := lookup_found _ q v (by rw [mapLookup_mapEntries]; exact lookup)
  exact (fun_arities_spec hE _ valid p mp).mono fun t ⟨n, e, lit⟩ => ⟨n, by rw [e] at qp; exact (compareExact_eq_integer _ _).mp qp, lit⟩

theorem FField.funField {w : Term} (h : FField E w) : FunField w ∧ ArityBdds w := by
  obtain ⟨pos, R, rfl, bdds⟩ := h
  refine ⟨⟨pos, R, rfl⟩, fun t R' e q v lookup => ?_⟩
  simp at e
  obtain ⟨-, rfl⟩ := e
  exact (bdds q v lookup).mono fun _ _ => trivial

/-- What `negatable?/2` checks of a type, whose tuple elements and map fields are `E`. -/
structure Negatable (E : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome →
    q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨ q = .atom "list" ∨ q = .atom "tuple" ∨
      q = .atom "map"
  bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
  atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
  atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []
  funs : ∀ w, mapLookup X (.atom "fun") = some w → FunField w
  arities : ∀ w, mapLookup X (.atom "fun") = some w → ArityBdds w
  lists : ∀ w, mapLookup X (.atom "list") = some w → LField E w
  tuples : ∀ w, mapLookup X (.atom "tuple") = some w → TupleField E w
  maps : ∀ w, mapLookup X (.atom "map") = some w → MapField E w

theorem Negatable.static {X : List (Term × Term)} (valid : Negatable E X) :
    mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w =>
    rcases valid.keys _ (by rw [h]; rfl) with bad | bad | bad | bad | bad | bad <;> simp only [Term.atom.injEq] at bad <;>
      exact absurd bad (by decide)

/-- What `nested?/2` checks of the fields of a nested type, whose tuple elements and map fields are `E`. -/
structure NestMap (E : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
    q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map"
  bitmap : ∀ w, mapLookup X (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
  atom : ∀ w, mapLookup X (.atom "atom") = some w → AtomField w
  atomUnion : ∀ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S]) → S ≠ []
  funs : ∀ w, mapLookup X (.atom "fun") = some w → FField E w
  lists : ∀ w, mapLookup X (.atom "list") = some w → LField E w
  tuples : ∀ w, mapLookup X (.atom "tuple") = some w → TupleField E w
  maps : ∀ w, mapLookup X (.atom "map") = some w → MapField E w

def NestOf (E : Term → Prop) (t : Term) : Prop := t = .atom "term" ∨ ∃ X, t = .map X ∧ NestMap E X

/-- The generator of the recursive node of the laws. -/
def gen : Term := .function true "Elixir.STTDescrProofsTest" "tuple_list" 1 #[]

/-- Recursive nodes of the reference `r`: their state maps `t` to the reference and the generator. -/
def NodeAt (r : List Nat) (e : Term) : Prop :=
  ∃ S, e = .tuple #[.reference r, .map S, gen] ∧ getMapKeys [.atom "t"] (.map S) = [.tuple #[.reference r, gen]]

theorem recursive_node_shape {e : Term} (h : «recursive_node?/1» e = .ok Term.true) : ∃ r, NodeAt r e := by
  unfold «recursive_node?/1» at h
  simp only at h
  split at h
  · rename_i _ r M g₄
    split at h
    · rename_i _ x g' hk
      simp only [Lynx.Except.guard, Erlang.erlang.«=:=/2», equalExact_eq_decide] at h
      by_cases h₁ : Term.compareExact (Term.fuel x (.reference r)) x (.reference r) = .eq <;> by_cases h₂ : Term.compareExact (Term.fuel g₄ g') g₄ g' = .eq <;>
        simp [h₁, h₂, Erlang.erlang.«and/2», Term.true] at h
      subst h
      rw [compareExact_eq_closed_function] at h₂
      rw [compareExact_eq_reference] at h₁
      subst h₁ h₂
      cases M with
      | map S => exact ⟨r, S, rfl, hk⟩
      | _ => simp [getMapKeys] at hk
    · simp at h
  · simp at h

/-- The reference of a node. -/
def refOf : Term → List Nat
  | .tuple ⟨[.reference r, _, _]⟩ => r
  | _ => []

/-- The recursive nodes the laws accept: those equal to their node `t`. -/
def IsT (t e : Term) : Prop :=
  compareExact (fuel e t) e t = .eq ∧ «recursive_node?/1» e = .ok Term.true

/-- Accepted nodes hash as `t` does in expansion literals. -/
theorem IsT.hash {t e : Term} (h : IsT t e) :
    Erlang.erlang.«phash2/1» (Term.list [.atom "term", e]) = Erlang.erlang.«phash2/1» (Term.list [.atom "term", t]) :=
  Erlang.erlang.phash2_congr (by simp [Term.list, compareExact_cons, h.1])

theorem IsT.node {t e : Term} (h : IsT t e) : NodeAt (refOf t) e := by
  obtain ⟨r, S, rfl, hk⟩ := recursive_node_shape h.2
  have same := h.1
  rw [compareExact_step] at same
  cases t <;> simp [Compare.compareStep] at same
  rename_i ts
  obtain ⟨l⟩ := ts
  match l, same with
  | [a, b, c], same =>
    simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at same
    obtain ⟨ha, -⟩ := same
    subst ha
    exact ⟨S, rfl, hk⟩
  | [], same => simp [List.compareLex] at same
  | [_], same => simp [List.compareLex] at same
  | [_, _], same => simp [List.compareLex] at same
  | _ :: _ :: _ :: _ :: _, same => simp [List.compareLex] at same

theorem isT_exact {t e e' : Term} (h₁ : IsT t e) (h₂ : IsT t e') : compareExact (fuel e e') e e' = .eq := by
  have b : compareExact (fuel t e') t e' = .eq := by
    rw [Lynx.Term.compareExact_swap, h₂.1]; rfl
  exact Lynx.Term.compareExact_eq_trans h₁.1 b

/-- Optimized laws hold no recursive node. -/
theorem not_isT_nil {e : Term} : ¬IsT (.atom "nil") e := fun ⟨same, h⟩ => by
  obtain ⟨r, S, rfl, -⟩ := recursive_node_shape h
  simp at same

/-- Nested types of a depth: flat element types at depth 0, and the recursive node `t` at every depth. -/
def Nest (t : Term) : Nat → Term → Prop
  | 0 => fun e => ElemTerm e ∨ IsT t e
  | d + 1 => fun e => NestOf (Nest t d) e ∨ IsT t e

theorem NestMap.negatable {X : List (Term × Term)} (v : NestMap E X) : Negatable E X := by
  exact ⟨v.keys, v.bitmap, v.atom, v.atomUnion, fun w h => (v.funs w h).funField.1,
    fun w h => (v.funs w h).funField.2, v.lists, v.tuples, v.maps⟩

/-- Each field `nested_field?/2` accepts. -/
theorem nested_field_spec (hE : NestedOk E depth) (k w : Term)
    (h : «nested_field?/2» (.tuple #[k, w]) depth = .ok Term.true) :
    (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
      (k = .atom "fun" ∧ FField E w) ∨ (k = .atom "list" ∧ LField E w) ∨ (k = .atom "tuple" ∧ TupleField E w) ∨
      (k = .atom "map" ∧ MapField E w) := by
  unfold «nested_field?/2» at h
  simp only at h
  split at h
  · rename_i tag arities shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    simp only [Lynx.Except.guard, Lynx.Except.tryWith] at h
    split at h
    · rename_i member
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      cases arities <;> simp [Erlang.erlang.«is_map/1», Lynx.Except.andAlso] at h
      rename_i R
      have bdds := fun_arities_map hE R (by simpa [Erlang.maps.«to_list/1»] using h)
      by_cases u : tag = .atom "union"
      · exact ⟨Bool.true, R, by simp [u], bdds⟩
      · by_cases n : tag = .atom "negation"
        · exact ⟨Bool.false, R, by simp [n], bdds⟩
        · simp [isMember, u, n] at member
    · exfalso
      split at h
      · simp_all
      · simp_all
      · simp_all
      · rcases valid_fields [(.atom "fun", .tuple #[tag, arities])] (by simpa [Term.list] using h) _
          List.mem_cons_self with h | h <;> simp at h
  split at h
  · rename_i bdd shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, list_bdd_spec hE h⟩)))
  · rename_i bdd shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tuple_bdd_spec hE h⟩))))
  · rename_i bdd shape
    simp at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, map_bdd_spec hE h⟩))))
  · rcases valid_fields [(k, w)] (by simpa [Term.list] using h) (k, w) (by simp) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem nested_fields_spec (hE : NestedOk E depth) (es : List (Term × Term))
    (valid : «nested_fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) ∨
      (p.1 = .atom "fun" ∧ FField E p.2) ∨ (p.1 = .atom "list" ∧ LField E p.2) ∨
      (p.1 = .atom "tuple" ∧ TupleField E p.2) ∨ (p.1 = .atom "map" ∧ MapField E p.2) := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    unfold «nested_fields?/2» at valid
    simp only [List.map_cons, Term.list, Term.true, Lynx.Except.andAlso_eq_true] at valid
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact nested_field_spec hE k w valid.1
    · exact ih valid.2 p member

theorem nest_map (hE : NestedOk E depth) (X : List (Term × Term))
    (valid : «nested_fields?/2» (Term.list ((mapEntries X).map fun e => .tuple #[e.1, e.2])) depth =
      .ok Term.true) : NestMap E X := by
  have each := nested_fields_spec hE (mapEntries X) valid
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  have key : ∀ {q : Term} {name : String}, compareExact (fuel q (.atom name)) q (.atom name) = .eq → q = .atom name :=
    fun e => (compareExact_eq_atom _ _).mp e
  refine ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?atomU,
    fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_⟩
  case atomU =>
    obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f.2 S e | (simp at qp)
  · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
    obtain ⟨p, mp, qp, -⟩ := entry q w lookup
    rcases each p mp with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> rw [k] at qp <;> simp [key qp]
  all_goals
    obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f | exact f.1 | exact f.2 | (simp at qp)

/-- The node clause of `nested?/2` accepts only the node of the depth. -/
theorem nested_node {e t : Term} {d : Nat} (h : «nested?/2» e (.tuple #[.integer d, t]) = .ok Term.true)
    (shape : ∃ a b c, e = .tuple #[a, b, c]) : IsT t e := by
  obtain ⟨a, b, c, rfl⟩ := shape
  unfold «nested?/2» at h
  simp only [Lynx.Except.guard, Erlang.erlang.«=:=/2», equalExact_eq_decide] at h
  by_cases hc : Term.compareExact (Term.fuel (Term.tuple #[a, b, c]) t) (Term.tuple #[a, b, c]) t = .eq
  · simp only [hc] at h
    exact ⟨hc, h⟩
  · simp [hc, Term.true, Term.false] at h
    split at h
    · simp [«valid?/1»] at h
    · rename_i heq _; cases heq
    · simp at h

/-- `nested?/2` accepts nested types of its depth. -/
theorem nested_spec (t : Term) : ∀ (d : Nat), NestedOk (Nest t d) (.tuple #[.integer d, t])
  | d, e, h => by
    by_cases shape : ∃ a b c, e = .tuple #[a, b, c]
    · cases d <;> exact Or.inr (nested_node h shape)
    have notNode : ∀ a b c, e ≠ .tuple #[a, b, c] := fun a b c he => shape ⟨a, b, c, he⟩
    cases d with
    | zero =>
      cases e
      case atom name =>
        by_cases top : name = "term"
        · subst top; exact Or.inl (Or.inl rfl)
        · simp [«nested?/2», top, «valid?/1»] at h
      case map X =>
        unfold «nested?/2» at h
        simp at h
        obtain ⟨X', e, valid⟩ := valid_map _ h
        exact Or.inl (Or.inr ⟨X', e, valid⟩)
      case tuple ts =>
        obtain ⟨l⟩ := ts
        match l, notNode with
        | [a, b, c], notNode => exact absurd rfl (notNode a b c)
        | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ =>
          unfold «nested?/2» at h; simp [«valid?/1»] at h
      all_goals (unfold «nested?/2» at h; simp [«valid?/1»] at h)
    | succ d =>
      have notMap : ∀ {e : Term}, (∀ X, e ≠ .map X) → (∀ a b c, e ≠ .tuple #[a, b, c]) → e ≠ .atom "term" →
          «nested?/2» e (.tuple #[.integer ↑(d + 1), t]) ≠ .ok Term.true := by
        intro e nm nn nt h
        unfold «nested?/2» at h
        split at h
        · exact nt rfl
        simp only [Lynx.Except.guard] at h
        split at h
        · rename_i heq _; cases heq; exact nn _ _ _ rfl
        split at h
        · first | (simp_all; omega) | simp_all
        · exact nm _ rfl
        · simp [Term.true] at h
      cases e
      case atom name =>
        by_cases top : name = "term"
        · subst top; exact Or.inl (Or.inl rfl)
        · exact absurd h (notMap (fun _ h => by cases h) (fun _ _ _ h => by cases h) (by simpa using top))
      case map X =>
        unfold «nested?/2» at h
        simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at h
        have sub : Erlang.erlang.«-/2» (.integer ↑(d + 1)) (.integer 1) = .ok (.integer ↑d) := by
          rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
        rw [sub, Lynx.Except.ok_bind] at h
        exact Or.inl (Or.inr ⟨X, rfl, nest_map (nested_spec t d) X h⟩)
      case tuple ts =>
        obtain ⟨l⟩ := ts
        exact absurd h (notMap (fun _ h => by cases h) notNode (fun h => by cases h))
      all_goals exact absurd h (notMap (fun _ h => by cases h) notNode (fun h => by cases h))

/-- Each field `negatable_fields?/2` accepts. -/
theorem negatable_fields_spec (hE : NestedOk E depth) (es : List (Term × Term))
    (valid : «negatable_fields?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true) :
    ∀ p ∈ es, (p.1 = .atom "bitmap" ∧ ∃ b : Nat, p.2 = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
      (p.1 = .atom "atom" ∧ AtomField p.2 ∧ ∀ S, p.2 = .tuple #[.atom "union", .map S] → S ≠ []) ∨
      (p.1 = .atom "fun" ∧ FunField p.2 ∧ ArityBdds p.2) ∨
      (p.1 = .atom "list" ∧ LField E p.2) ∨ (p.1 = .atom "tuple" ∧ TupleField E p.2) ∨
      (p.1 = .atom "map" ∧ MapField E p.2) := by
  induction es with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, w⟩ := e
    simp only [List.map_cons, Term.list, «negatable_fields?/2», Term.true, Lynx.Except.andAlso_eq_true] at valid
    have head : (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
        (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
        (k = .atom "fun" ∧ FunField w ∧ ArityBdds w) ∨
        (k = .atom "list" ∧ LField E w) ∨ (k = .atom "tuple" ∧ TupleField E w) ∨ (k = .atom "map" ∧ MapField E w) := by
      have field := valid.1
      have fallback : «nested_field?/2» (.tuple #[k, w]) depth = .ok Term.true →
          (k = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
            (k = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ []) ∨
            (k = .atom "fun" ∧ FunField w ∧ ArityBdds w) ∨ (k = .atom "list" ∧ LField E w) ∨
            (k = .atom "tuple" ∧ TupleField E w) ∨ (k = .atom "map" ∧ MapField E w) := fun h => by
        rcases nested_field_spec hE k w h with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.funField⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      unfold «negatable_field?/2» at field
      simp only at field
      split at field
      · rename_i tag arities shape
        simp at shape
        obtain ⟨rfl, rfl⟩ := shape
        simp only [Lynx.Except.guard, Lynx.Except.tryWith] at field
        split at field
        · rename_i member
          refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
          cases arities <;> simp [Erlang.erlang.«is_map/1», Lynx.Except.andAlso] at field
          rename_i R
          have bdds : ArityBdds (.tuple #[tag, .map R]) := by
            intro t R' e
            simp at e
            obtain ⟨-, rfl⟩ := e
            exact arity_bdds_map R (by simpa [Erlang.maps.«to_list/1»] using field)
          by_cases u : tag = .atom "union"
          · exact ⟨⟨Bool.true, R, by simp [u]⟩, bdds⟩
          · by_cases n : tag = .atom "negation"
            · exact ⟨⟨Bool.false, R, by simp [n]⟩, bdds⟩
            · simp [isMember, u, n] at member
        · exact fallback (by simpa using field)
      · exact fallback field
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih valid.2 p member

theorem negatable_map (t : Term) (depth : Nat) (descr : Term)
    (valid : «negatable?/2» descr (.tuple #[.integer depth, t]) = .ok Term.true) :
    descr = .atom "term" ∨ ∃ X, descr = .map X ∧ Negatable (Nest t depth) X := by
  cases descr
  case atom name =>
    by_cases top : name = "term"
    · exact Or.inl (by rw [top])
    · simp [«negatable?/2», top] at valid
  all_goals try (simp [«negatable?/2»] at valid; done)
  rename_i X
  refine Or.inr ?_
  simp [«negatable?/2», Term.true] at valid
  simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at valid
  have each := negatable_fields_spec (nested_spec t depth) (mapEntries X) valid
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  have key : ∀ {q : Term} {name : String}, compareExact (fuel q (.atom name)) q (.atom name) = .eq → q = .atom name :=
    fun e => (compareExact_eq_atom _ _).mp e
  refine ⟨X, rfl, ⟨fun q some => ?_, fun w lookup => ?_, fun w lookup => ?_, fun S lookup => ?atomU,
    fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_, fun w lookup => ?_⟩⟩
  case atomU =>
    obtain ⟨p, mp, qp, e⟩ := entry _ _ lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f.2 S e | (simp at qp)
  · obtain ⟨w, lookup⟩ := Option.isSome_iff_exists.mp some
    obtain ⟨p, mp, qp, -⟩ := entry q w lookup
    rcases each p mp with ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> rw [k] at qp <;> simp [key qp]
  all_goals
    obtain ⟨p, mp, qp, rfl⟩ := entry _ w lookup
    rcases each p mp with ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ | ⟨k, f⟩ <;> rw [k] at qp <;>
      first | exact f | exact f.1 | exact f.2 | (simp at qp)

/-- A list BDD of other literals is not a top literal itself. -/
theorem not_top_leaf {x : Term} (wx : Bdd ListOk x) : ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"] := by
  intro k e
  subst e
  rcases wx.shape with h | h | ⟨k', x', y', h⟩ | ⟨h', lit, c, u, d, h⟩ <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact Bdd.leaf_iff.mp wx ⟨_, rfl⟩

/-- The negation of a list type. -/
theorem list_negation (k : Int) (x : Term) (field : ListField x) :
    (Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer k, .atom "term", .atom "term"]) x =
      .ok (.atom "bdd_bot")) ∨
    (Bdd ListOk x ∧ ∃ y, Elixir.Module.Types.Descr.«list_difference/2»
        (.tuple #[.integer k, .atom "term", .atom "term"]) x = .ok y ∧
      Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x) := by
  rcases field with ⟨k', rfl⟩ | wx
  · left; simp [Elixir.Module.Types.Descr.«list_difference/2»]
  · right
    obtain ⟨y, run, keep, sem⟩ := neg_ok wx
    refine ⟨wx, y, ?_, keep _ wx, sem⟩
    have nt := not_top_leaf wx
    unfold Elixir.Module.Types.Descr.«list_difference/2»
    split
    · exact (nt _ rfl).elim
    · exact run
    · next h₁ h₂ => first | exact (h₁ _ rfl).elim | exact (h₁ _ _ rfl).elim | exact absurd rfl (h₁ _) | simp_all

/-- The intersection of list types of other literals. -/
theorem list_intersection_bdd {x y : Term} (wx : Bdd ListOk x) (wy : Bdd ListOk y) :
    Elixir.Module.Types.Descr.«list_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_intersection/2»
  split
  · exact (not_top_leaf wx _ rfl).elim
  · exact (not_top_leaf wy _ rfl).elim
  · rfl

/-- What remains of a list or tuple type and its negation. -/
def Gone (K : Nat) (q w : Term) : Prop :=
  (q = .atom "list" ∧ Bdd ListOk w ∧ Unsat w) ∨ (q = .atom "tuple" ∧ EmptyTuple K w) ∨
    (q = .atom "map" ∧ EmptyMap K w)

theorem Gone.congr {K : Nat} {q k w : Term} (e : compareExact (fuel q k) q k = .eq) (gone : Gone K k w) : Gone K q w := by
  rcases gone with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨(compareExact_eq_atom _ _).mp e, h⟩
  · exact Or.inr (Or.inl ⟨(compareExact_eq_atom _ _).mp e, h⟩)
  · exact Or.inr (Or.inr ⟨(compareExact_eq_atom _ _).mp e, h⟩)

/-- Types holding only what remains of list and tuple types and their negations are empty. -/
theorem empty_gone {K m : Nat} (hm : K + 2 ≤ m) (I : List (Term × Term))
    (only : ∀ q w, mapLookup I q = some w → Gone K q w) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) (.map I) = .ok Term.true := by
  have absent : ∀ name, name ≠ "list" → name ≠ "tuple" → name ≠ "map" →
      mapLookup I (.atom name) = Option.none := by
    intro name nl nt nm
    cases h : mapLookup I (.atom name) with
    | none => rfl
    | some w => rcases only _ w h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> simp at e <;> simp_all
  have none : ∀ name, name ≠ "list" → name ≠ "tuple" → name ≠ "map" →
      I.any (fun e => decide (compareExact (fuel (.atom name) e.1) (.atom name) e.1 = .eq)) = Bool.false := by
    intro name nl nt nm
    have := absent name nl nt nm
    rw [Bool.eq_false_iff]
    intro hany
    obtain ⟨e, me, he⟩ := List.any_eq_true.mp hany
    have := (mapLookup_isSome I (.atom name)).mpr ⟨e, me, by simpa using he⟩
    simp_all
  have anyKey : ∀ name, (I.any fun e => decide (compareExact (fuel (.atom name) e.1) (.atom name) e.1 = .eq)) =
      (mapLookup I (.atom name)).isSome := by
    intro name
    rw [Bool.eq_iff_iff, mapLookup_isSome]
    simp
  simp only [Elixir.Module.Types.Descr.«empty?/1»]
  rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
  simp [getMapKeys_single, absent "dynamic" (by decide) (by decide) (by decide), Erlang.erlang.«==/2»,
    Erlang.erlang.«is_map_key/2», none "atom" (by decide) (by decide) (by decide),
    none "bitmap" (by decide) (by decide) (by decide), none "fun" (by decide) (by decide) (by decide),
    Term.true, Term.false]
  by_cases empty : I = []
  · simp [empty]
  simp only [empty, ite_false, equalExact_eq_decide, anyKey]
  simp [Erlang.erlang.«not/1»]
  have tupleOk : ∀ r, mapLookup I (.atom "tuple") = some r →
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) r (.map []) = .ok (.atom "true") := fun r h => by
    rcases only _ r h with ⟨e, -⟩ | ⟨-, gone⟩ | ⟨e, -⟩
    · simp at e
    · exact gone m [] (by omega)
    · simp at e
  have mapOk : ∀ r, mapLookup I (.atom "map") = some r →
      Elixir.Module.Types.Descr.«map_empty?/2» (D m) r (.map []) = .ok (.atom "true") := fun r h => by
    rcases only _ r h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, gone⟩
    · simp at e
    · simp at e
    · exact gone m [] hm
  have listOk : ∀ r, mapLookup I (.atom "list") = some r →
      Elixir.Module.Types.Descr.«list_empty?/2» (D m) r (.map []) = .ok (.atom "true") := fun r h => by
    rcases only _ r h with ⟨-, wr, unsat⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact list_empty_unsat _ wr unsat []
    · simp at e
    · simp at e
  cases ht : mapLookup I (.atom "tuple") <;> cases hm : mapLookup I (.atom "map") <;>
    cases hl : mapLookup I (.atom "list") <;>
    first
      | (simp [tupleOk _ ht, mapOk _ hm, listOk _ hl]; done)
      | (simp [tupleOk _ ht, mapOk _ hm]; done)
      | (simp [tupleOk _ ht, listOk _ hl]; done)
      | (simp [mapOk _ hm, listOk _ hl]; done)
      | (simp [tupleOk _ ht]; done)
      | (simp [mapOk _ hm]; done)
      | (simp [listOk _ hl]; done)
      | (simp; done)

end Elixir.STTDescrProofsTest

-- Negations are differences from the top type, which no type intersects.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term
open BddProofs
open BddProofs
open BddProofs

/-- Symmetrical intersections whose common fields intersect to what remains of a type and its negation. -/
theorem symmetrical_gone (depth : Nat) (name : String) (captures : Array Term) (L R : List (Term × Term))
    (g : Term → Term → Term → Term)
    (common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        (.function false "Elixir.Module.Types.Descr" name 3 captures) #[q, x, y] = .ok (g q x y) ∧
      (kept (q, g q x y) = Bool.true → Gone K q (g q x y))) :
    ∃ I, Elixir.Module.Types.Descr.«symmetrical_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
      (.map L) (.map R) (.function false "Elixir.Module.Types.Descr" name 3 captures) = .ok (.map I) ∧
      ∀ q w, mapLookup I q = some w → Gone K q w := by
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) false "Elixir.Module.Types.Descr"
    name captures L R g (fun e member y hy => (common e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy).1)
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) false "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure,
        keep_field])
  refine ⟨out, ?_, fun q w hw => ?_⟩
  · unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  rw [lookO q] at hw
  cases hit : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
  | none => simp [hit] at hw
  | some e =>
    rw [hit] at hw
    have qe : compareExact (fuel q e.1) q e.1 = .eq := by simpa using List.find?_some hit
    have inI : mapLookup I e.1 = some e.2 :=
      mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hit)
    rw [lookI e.1] at inI
    cases hL : (mapEntries L).find? (fun f => decide (compareExact (fuel e.1 f.1) e.1 f.1 = .eq)) with
    | none => simp [hL] at inI
    | some f =>
      rw [hL] at inI
      obtain ⟨y, hy, value⟩ := Option.map_eq_some_iff.mp inI
      have hx := mapLookup_of_mem_mapEntries (List.mem_of_find?_eq_some hL)
      have ef : compareExact (fuel e.1 f.1) e.1 f.1 = .eq := by simpa using List.find?_some hL
      have keep : kept e = kept (f.1, g f.1 f.2 y) := by rw [value]; rfl
      by_cases k : kept e = Bool.true
      · simp [k] at hw
        subst hw
        have gone := (common f.1 f.2 y hx hy).2 (by rw [← keep]; exact k)
        rw [value] at gone
        exact gone.congr (Lynx.Term.compareExact_eq_trans qe ef)
      · simp [k] at hw

/-- Intersections keep at most an unsatisfiable list BDD when every common bitmap is
disjoint, every common atom field holds no atom, function types cancel out, and list
types are negations of each other. -/
theorem intersection_disjoint (depth : Nat) (L R : List (Term × Term)) (validL : Negatable E L)
    (staticR : mapLookup R (.atom "dynamic") = Option.none)
    (bitmaps : ∀ (b₁ : Nat) w, mapLookup L (.atom "bitmap") = some (.integer b₁) →
      mapLookup R (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0)
    (atoms : ∀ x y, mapLookup L (.atom "atom") = some x → mapLookup R (.atom "atom") = some y →
      ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
        x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
        y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
        Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
        (p₁ || p₂) = Bool.true ∧
        ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false)
    (funs : ∀ x y, mapLookup L (.atom "fun") = some x → mapLookup R (.atom "fun") = some y →
      Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table depth) x y =
        .ok (.integer 0))
    (lists : ∀ x y, mapLookup L (.atom "list") = some x → mapLookup R (.atom "list") = some y →
      Bdd ListOk x ∧ Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x)
    (tuples : ∀ x y, mapLookup L (.atom "tuple") = some x → mapLookup R (.atom "tuple") = some y →
      TupleCancel K x y)
    (maps : ∀ x y, mapLookup L (.atom "map") = some x → mapLookup R (.atom "map") = some y →
      MapCancel K x y) :
    ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map I) ∧
      ∀ q w, mapLookup I q = some w → Gone K q w := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
      k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  -- Each common field intersects to a value the filter drops.
  have common : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
        q x y = .ok (g q x y) ∧
        (kept (q, g q x y) = Bool.true → Gone K q (g q x y)) := by
    intro q x y hx hy
    rcases validL.keys q (by simp [hx]) with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨b₁, rfl, -⟩ := validL.bitmap x hx
      obtain ⟨b₂, rfl, disjoint⟩ := bitmaps b₁ y hx hy
      simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», Erlang.erlang.«band/2», kept, disjoint]
    · obtain ⟨p₁, S₁, p₂, S₂, rfl, rfl, set₁, set₂, union, none⟩ := atoms x y hx hy
      rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, -, tag, nonempty, mE⟩ | ⟨hE, -⟩
      · exfalso
        have positive : p = Bool.true := by rw [tag, union]
        apply nonempty positive
        apply nil_of_lookup_none
        intro q
        have := mE q
        rw [none q, positive] at this
        cases h : mapLookup E q with
        | none => rfl
        | some _ => simp [h] at this
      · simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», hE, kept]
    · simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», funs x y hx hy, kept]
    · obtain ⟨wx, wy, sem⟩ := lists x y hx hy
      obtain ⟨r, run, keep, semr⟩ := inter_ok wx wy
      have value : g (.atom "list") x y = r := by
        simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», list_intersection_bdd wx wy, run]
      refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», list_intersection_bdd wx wy, run, value],
        fun _ => Or.inl ⟨rfl, value ▸ keep _ wx wy, fun ρ resp => ?_⟩⟩
      rw [value, semr ρ resp, sem ρ resp]
      cases eval ρ x <;> rfl
    · obtain ⟨r, run, empty⟩ := tuples x y hx hy
      have value : g (.atom "tuple") x y = r := by
        simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», run]
      refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run, value], fun k => ?_⟩
      rw [value] at k ⊢
      exact Or.inr (Or.inl ⟨rfl, empty k⟩)
    · obtain ⟨r, run, empty⟩ := maps x y hx hy
      have value : g (.atom "map") x y = r := by
        simp [g, Elixir.Module.Types.Descr.«bare_intersection/3», run]
      refine ⟨by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run, value], fun k => ?_⟩
      rw [value] at k ⊢
      exact Or.inr (Or.inr ⟨rfl, empty k⟩)
  obtain ⟨I, run, only⟩ := symmetrical_gone depth "bare_intersection" #[] L R g fun q x y hx hy =>
    ⟨by rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure]; exact (common q x y hx hy).1,
      (common q x y hx hy).2⟩
  refine ⟨I, ?_, only⟩
  have absent : mapLookup R (.atom "dynamic") = Option.none := staticR
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, validL.static, absent, run]

/-- The top type holds every bitmap and the negations of no atoms and of no functions. -/
theorem unfolded_term_fields : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    mapLookup T (.atom "bitmap") = some (.integer 255) ∧
    mapLookup T (.atom "atom") = some (.tuple #[.atom "negation", .map []]) ∧
    mapLookup T (.atom "fun") = some (.tuple #[.atom "negation", .map []]) ∧
    mapLookup T (.atom "dynamic") = Option.none :=
  ⟨_, rfl, by simp [mapLookup], by simp [mapLookup], by simp [mapLookup], by simp [mapLookup]⟩

theorem negation_fields (ops : ElemOk E K) (depth : Nat) (X : List (Term × Term)) (valid : Negatable E X)
    (nonempty : X ≠ []) :
    ∃ N, Elixir.Module.Types.Descr.«bare_negation/1»
        (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map X) = .ok (.map N) ∧
      mapLookup N (.atom "dynamic") = Option.none ∧
      (∀ (b₁ : Nat) w, mapLookup X (.atom "bitmap") = some (.integer b₁) →
        mapLookup N (.atom "bitmap") = some w → ∃ b₂ : Nat, w = .integer b₂ ∧ b₁ &&& b₂ = 0) ∧
      (∀ x y, mapLookup X (.atom "atom") = some x → mapLookup N (.atom "atom") = some y →
        ∃ (p₁ : Bool) (S₁ : List (Term × Term)) (p₂ : Bool) (S₂ : List (Term × Term)),
          x = .tuple #[.atom (if p₁ then "union" else "negation"), .map S₁] ∧
          y = .tuple #[.atom (if p₂ then "union" else "negation"), .map S₂] ∧
          Erlang.sets.elements? (.map S₁) = some S₁ ∧ Erlang.sets.elements? (.map S₂) = some S₂ ∧
          (p₁ || p₂) = Bool.true ∧
          ∀ q, ((p₁ == (mapLookup S₁ q).isSome) && (p₂ == (mapLookup S₂ q).isSome)) = Bool.false) ∧
      (∀ x y, mapLookup X (.atom "fun") = some x → mapLookup N (.atom "fun") = some y → ∀ m,
        Elixir.Module.Types.Descr.«fun_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table m) x y =
          .ok (.integer 0)) ∧
      (∀ x y, mapLookup X (.atom "list") = some x → mapLookup N (.atom "list") = some y →
        Bdd ListOk x ∧ Bdd ListOk y ∧ ∀ ρ, Resp ρ → eval ρ y = !eval ρ x) ∧
      (∀ x y, mapLookup X (.atom "tuple") = some x → mapLookup N (.atom "tuple") = some y →
        TupleCancel K x y) ∧
      (∀ x y, mapLookup X (.atom "map") = some x → mapLookup N (.atom "map") = some y →
        MapCancel K x y) ∧
      (∀ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) → ∀ name t,
        mapLookup T (.atom name) = some t →
        (mapLookup X (.atom name) = Option.none → mapLookup N (.atom name) = some t) ∧
        ∀ x w, mapLookup X (.atom name) = some x →
          Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
            (.atom name) t x = .ok w →
          mapLookup N (.atom name) = if kept (.atom name, w) then some w else Option.none) := by
  obtain ⟨T, term, termBitmap, termAtom, termFun, termDynamic⟩ := unfolded_term_fields
  have termTuple : mapLookup T (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  have termMap : mapLookup T (.atom "map") = some (.tuple #[.integer 61102469, .atom "open", .nil]) := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  have termList : mapLookup T (.atom "list") =
      some (.tuple #[.integer 46675407, .atom "term", .atom "term"]) := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
      k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have noAtoms : Erlang.sets.elements? (.map []) = some [] := by simp [Erlang.sets.elements?]
  obtain ⟨N, fold, lookN, -⟩ := difference_fold depth (.function false "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries X) T (mapEntries_distinct X) (by
    intro e member v₁ found
    have hy := mapLookup_of_mem_mapEntries member
    rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure]
    rcases valid.keys e.1 (by simp [hy]) with key | key | key | key | key | key <;> rw [key] at found hy ⊢
    · rw [termBitmap] at found
      cases found
      obtain ⟨b, value, -⟩ := valid.bitmap e.2 hy
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», value]
    · rw [termAtom] at found
      cases found
      obtain ⟨p, S, value, set⟩ := valid.atom e.2 hy
      rw [value]
      rcases atom_difference false [] p S noAtoms set with ⟨_, _, hE, -⟩ | ⟨hE, -⟩ <;>
        simp only [Bool.false_eq_true, ite_false] at hE <;>
        simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
    · rw [termFun] at found
      cases found
      obtain ⟨y, run, -⟩ := fun_negation depth e.2 (valid.funs e.2 hy)
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    · rw [termList] at found
      cases found
      rcases list_negation 46675407 e.2 (valid.lists e.2 hy).list with run | ⟨-, y, run, -⟩ <;>
        simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    · rw [termTuple] at found
      cases found
      obtain ⟨y, run, -⟩ := tuple_cancel ops e.2 (valid.tuples e.2 hy)
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    · rw [termMap] at found
      cases found
      obtain ⟨y, run, -⟩ := map_cancel ops e.2 (valid.maps e.2 hy)
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run])
  have run : Elixir.Module.Types.Descr.«bare_negation/1»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 2)) (.map X) = .ok (.map N) := by
    simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map valid.static, nonempty]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», nonempty, term, Erlang.maps.«fold/3»]
    simpa using fold
  refine ⟨N, run, ?_, fun b₁ w hX hN => ?_, fun x y hX hN => ?_, fun x y hX hN m => ?_, fun x y hX hN => ?_,
    fun x y hX hN => ?_, fun x y hX hN => ?_, fun T' term' name t hT => ?_⟩
  · rw [lookN, find_atom, valid.static]
    exact termDynamic
  · rw [lookN, find_atom, hX] at hN
    have le : 255 &&& b₁ ≤ 255 := Nat.and_le_left
    have value : g (.atom "bitmap") (.integer 255) (.integer b₁) = .integer ↑(255 - (255 &&& b₁)) := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]
      omega
    simp only [Option.map_some, termBitmap, Option.bind_some, value] at hN
    refine ⟨255 - (255 &&& b₁), ?_, Nat.eq_of_testBit_eq fun i => ?_⟩
    · split at hN <;> simp_all
    · simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
      cases b₁.testBit i <;> simp
  · obtain ⟨pR, SR, rfl, setR⟩ := valid.atom x hX
    rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termAtom, Option.bind_some] at hN
    rcases atom_difference false [] pR SR noAtoms setR with ⟨p, E, hE, setE, tag, -, mE⟩ | ⟨hE, -⟩ <;>
      simp only [Bool.false_eq_true, ite_false] at hE
    · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
          (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) =
          .tuple #[.atom (if p then "union" else "negation"), .map E] := by
        simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
      have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) =
          Bool.true := by
        simp [kept]
      simp only [value, keep, ite_true, Option.some.injEq] at hN
      refine ⟨pR, SR, p, E, rfl, hN.symm, setR, setE, by rw [tag]; cases pR <;> rfl, fun q => ?_⟩
      rw [mE q]
      cases (mapLookup SR q).isSome <;> cases pR <;> simp [mapLookup]
    · have value : g (.atom "atom") (.tuple #[.atom "negation", .map []])
          (.tuple #[.atom (if pR then "union" else "negation"), .map SR]) = .integer 0 := by
        simp only [g, Elixir.Module.Types.Descr.«bare_difference/3», hE]
      have drop : kept (.atom "atom", .integer 0) = Bool.false := by simp [kept]
      simp [value, drop] at hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termFun, Option.bind_some] at hN
    obtain ⟨w, negation, either⟩ := fun_negation depth x (valid.funs x hX)
    have value : g (.atom "fun") (.tuple #[.atom "negation", .map []]) x = w := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», negation]
    rw [value] at hN
    rcases either with rfl | all
    · simp [kept] at hN
    · split at hN
      · cases hN; exact all m
      · cases hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termList, Option.bind_some] at hN
    rcases list_negation 46675407 x (valid.lists x hX).list with run | ⟨wx, w, run, wy, sem⟩
    · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x =
          .atom "bdd_bot" := by
        simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
      simp [value, kept] at hN
    · have value : g (.atom "list") (.tuple #[.integer 46675407, .atom "term", .atom "term"]) x = w := by
        simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
      rw [value] at hN
      split at hN
      · cases hN; exact ⟨wx, wy, sem⟩
      · cases hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termTuple, Option.bind_some] at hN
    obtain ⟨w, run, cancel⟩ := tuple_cancel ops x (valid.tuples x hX)
    have value : g (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    rw [value] at hN
    split at hN
    · rename_i k; cases hN; exact cancel k
    · cases hN
  · rw [lookN, find_atom, hX] at hN
    simp only [Option.map_some, termMap, Option.bind_some] at hN
    obtain ⟨w, run, cancel⟩ := map_cancel ops x (valid.maps x hX)
    have value : g (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil]) x = w := by
      simp [g, Elixir.Module.Types.Descr.«bare_difference/3», run]
    rw [value] at hN
    split at hN
    · rename_i k; cases hN; exact cancel k
    · cases hN
  · rw [term] at term'
    cases term'
    refine ⟨fun hX => ?_, fun x w hX run => ?_⟩
    · rw [lookN, find_atom, hX]
      exact hT
    · rw [lookN, find_atom, hX]
      have value : g (.atom name) t x = w := by simp [g, run]
      simp only [Option.map_some, hT, Option.bind_some, value]

end Elixir.STTDescrProofsTest

-- The optimized operations compute the same negations of bitmaps, atoms, functions,
-- lists, and tuples, while open maps of one field negate to open maps of one field.
-- Their intersections fall back to BDD intersections, since the negation of a BDD
-- node is never a leaf, or intersect literals whose fields do not meet.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term
open BddProofs
open BddProofs
open BddProofs

open BddProofs

theorem any_key (X : List (Term × Term)) (name : String) :
    (X.any fun e => decide (compareExact (fuel (.atom name) e.1) (.atom name) e.1 = .eq)) = (mapLookup X (.atom name)).isSome := by
  rw [Bool.eq_iff_iff, mapLookup_isSome]
  simp

theorem Valid.absent {V : List (Term × Term)} (valid : Valid V) (name : String) (nb : name ≠ "bitmap")
    (na : name ≠ "atom") : mapLookup V (.atom name) = Option.none := by
  cases h : mapLookup V (.atom name) with
  | none => rfl
  | some w =>
    rcases valid.keys (.atom name) (by rw [h]; rfl) with e | e
    · cases e; exact absurd rfl nb
    · cases e; exact absurd rfl na

theorem Valid.negatable {V : List (Term × Term)} (valid : Valid V) : Negatable E V := by
  refine ⟨fun q h => ?_, valid.bitmap, valid.atom, valid.atomUnion, fun w h => ?_, fun w h => ?_, fun w h => ?_,
    fun w h => ?_, fun w h => ?_⟩
  · rcases valid.keys q h with rfl | rfl <;> simp
  · simp [valid.absent "fun" (by decide) (by decide)] at h
  · simp [valid.absent "fun" (by decide) (by decide)] at h
  · simp [valid.absent "list" (by decide) (by decide)] at h
  · simp [valid.absent "tuple" (by decide) (by decide)] at h
  · simp [valid.absent "map" (by decide) (by decide)] at h

theorem difference_term_term (d : Dispatcher) (x S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» d x (.atom "term") S = .ok (.map []) := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  rfl

theorem difference_term_none (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» d (.atom "term") (.map []) S = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  simp [Erlang.erlang.«==/2»]

end Elixir.STTDescrProofsTest

-- The top type is a subtype of a type united with its negation: each field of the top
-- type, minus what the type and its negation unite into at that field, is empty.
-- Propositional BDD unions are tautologies, while `{}` and its negation `{term, ...}`
-- are checked as concrete tuple lines.
namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-- A field of the left type whose difference with the right type is empty. -/
def Covered (d : Dispatcher) (U : List (Term × Term)) (q t : Term) : Prop :=
  ∃ u w, mapLookup U q = some u ∧ Elixir.Module.Types.Descr.«bare_difference/3» d q t u = .ok w ∧
    (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
      Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))

theorem iterator_covered (d : Dispatcher) (U : List (Term × Term)) :
    ∀ es : List (Term × Term), (∀ e ∈ es, Covered d U e.1 e.2) →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» d it (.map U) (.map [])) =
        .ok (.atom "true") := by
  intro es
  induction es with
  | nil =>
    intro _
    simp [Term.list, Erlang.maps.«next/1»]
    unfold Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3»
    rfl
  | cons e rest ih =>
    intro all
    obtain ⟨u, w, hu, run, empty⟩ := all e (by simp)
    have tail := ih (fun e' m => all e' (by simp [m]))
    simp only [List.map, Term.list] at tail ⊢
    simp only [Erlang.maps.«next/1», Lynx.Except.ok_bind]
    rw [Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, hu, run]
    rcases empty with h | h | h
    · simpa [h] using tail
    · simpa [h] using tail
    · refine ⟨?_, tail⟩
      by_cases h₀ : w = .integer 0
      · simp [h₀]
      · by_cases h₁ : w = .atom "bdd_bot"
        · simp [h₁]
        · right
          simp [h₀, h₁, h]

/-- The top type is a subtype of static types covering each of its fields. -/
theorem subtype_term (d : Dispatcher) (T U : List (Term × Term))
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    (static : mapLookup U (.atom "dynamic") = Option.none)
    (covered : ∀ e ∈ mapEntries T, Covered d U e.1 e.2) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.atom "term") (.map U) = .ok (.atom "true") := by
  have walk := iterator_covered d U (mapEntries T) covered
  have staticT : mapLookup T (.atom "dynamic") = Option.none := by
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    simp [mapLookup]
  unfold Elixir.Module.Types.Descr.«subtype?/2»
  simp [term, unfold_map, Erlang.erlang.«is_map_key/2», static, staticT, any_key, Lynx.Except.andAlso,
    Erlang.erlang.«/=/2»]
  unfold Elixir.Module.Types.Descr.«subtype_static?/2»
  by_cases same : compareExact (fuel (.map U) (.map T)) (.map U) (.map T) = .eq
  · simp [Erlang.erlang.«=:=/2», same]
  · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, staticT, Erlang.maps.«iterator/1»]
    exact walk

/-- The difference of a field of the top type with a field type is empty. -/
def CoveredVal (d : Dispatcher) (q t u : Term) : Prop :=
  ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» d q t u = .ok w ∧
    (w = .integer 0 ∨ w = .atom "bdd_bot" ∨
      Elixir.Module.Types.Descr.«empty_key?/3» d q w (.map []) = .ok (.atom "true"))

/-- What a field type and its negation unite into covers the field of the top type. -/
def KeyOk (dn du dc : Dispatcher) (q t x : Term) : Prop :=
  ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» dn q t x = .ok w ∧
    (kept (q, w) = Bool.false → CoveredVal dc q t x) ∧
    (kept (q, w) = Bool.true → ∃ u, Elixir.Module.Types.Descr.«bare_union/3» du q x w = .ok u ∧ CoveredVal dc q t u)

theorem bitmap_absent (dc : Dispatcher) : CoveredVal dc (.atom "bitmap") (.integer 255) (.integer 255) :=
  ⟨.integer 0, by simp [Elixir.Module.Types.Descr.«bare_difference/3»]; rfl, Or.inl rfl⟩

theorem bitmap_key (dn du dc : Dispatcher) (b : Nat) (le : b ≤ 255) :
    KeyOk dn du dc (.atom "bitmap") (.integer 255) (.integer b) := by
  have band : (255 : Nat) &&& b = b := by
    rw [Nat.and_comm]
    have := Nat.and_two_pow_sub_one_eq_mod b 8
    simp at this
    omega
  refine ⟨.integer ↑(255 - b), ?_, fun k => ?_, fun _ => ?_⟩
  · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]
    omega
  · refine ⟨.integer ↑(255 - b), ?_, ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2», band]; omega
    · simp [kept] at k; left; simp [k]
  · refine ⟨.integer 255, ?_, .integer 0, ?_, Or.inl rfl⟩
    · have disjoint : b &&& (255 - b) = 0 := Nat.eq_of_testBit_eq fun i => by
        rw [← band]; simp only [Nat.testBit_and, testBit_sub_and, Nat.zero_testBit]
        cases b.testBit i <;> simp
      have := add_eq_or b (255 - b) disjoint
      simp [Elixir.Module.Types.Descr.«bare_union/3», Erlang.erlang.«bor/2»]
      omega
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]

theorem no_atoms : Erlang.sets.elements? (.map []) = some [] := by simp [Erlang.sets.elements?]

/-- Sets without members are empty. -/
theorem set_none {left right : Term} {f : Term → Term → Except Exception Term} {E : List (Term × Term)}
    (run : f left right = .ok (.map E)) (none : ∀ q, (mapLookup E q).isSome = Bool.false) :
    f left right = .ok (.map []) := by
  rw [run, nil_of_lookup_none E fun q => by simpa using none q]

theorem atom_absent (dc : Dispatcher) :
    CoveredVal dc (.atom "atom") (.tuple #[.atom "negation", .map []]) (.tuple #[.atom "negation", .map []]) := by
  obtain ⟨E, hE, -, m⟩ := Erlang.sets.subtract_member _ _ _ _ no_atoms no_atoms
  have run := set_none hE fun q => by rw [m]; simp [mapLookup]
  refine ⟨.integer 0, ?_, Or.inl rfl⟩
  simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», run,
    Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.sets.«size/1»]

theorem atom_key (dn du dc : Dispatcher) (p : Bool) (S : List (Term × Term))
    (set : Erlang.sets.elements? (.map S) = some S) :
    KeyOk dn du dc (.atom "atom") (.tuple #[.atom "negation", .map []])
      (.tuple #[.atom (if p then "union" else "negation"), .map S]) := by
  cases p
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.subtract_member _ _ _ _ set no_atoms
    rcases union_or_empty E with ⟨s, nonzero, size⟩ | ⟨size, empty⟩
    · refine ⟨.tuple #[.atom "union", .map E], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, size, nonzero]
      · obtain ⟨F, hF, -, mF⟩ := Erlang.sets.subtract_member _ _ _ _ set setE
        have run := set_none hF fun q => by rw [mF, m]; simp [mapLookup]
        exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«atom_union/2», run],
          atom_absent dc⟩
    · refine ⟨.integer 0, ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
          Erlang.erlang.«==/2», Lynx.Except.andAlso, size]
      · obtain rfl : S = [] := nil_of_lookup_none S fun q => by
          have := m q
          rw [empty q] at this
          simpa [mapLookup] using this
        exact atom_absent dc
  · obtain ⟨E, hE, setE, m⟩ := Erlang.sets.union_member _ _ _ _ no_atoms set
    refine ⟨.tuple #[.atom "negation", .map E], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«atom_difference/2», hE,
        Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · obtain ⟨F, hF, -, mF⟩ := Erlang.sets.subtract_member _ _ _ _ setE set
      have run := set_none hF fun q => by rw [mF, m]; simp [mapLookup]
      exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«atom_union/2», run],
        atom_absent dc⟩

theorem loop_ne_nil (f : Term → Term → Bool) :
    ∀ (l : List Term) (a : Term) (acc : List Term), List.eraseDupsBy.loop f l (a :: acc) ≠ [] := by
  intro l
  induction l with
  | nil => intro a acc; simp [List.eraseDupsBy.loop]
  | cons x xs ih =>
    intro a acc
    simp only [List.eraseDupsBy.loop]
    split
    · exact ih a acc
    · exact ih x (a :: acc)

theorem fun_absent (n : Nat) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "fun") (.tuple #[.atom "negation", .map []])
      (.tuple #[.atom "negation", .map []]) := by
  have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
      (.map []) (.map []) = .ok (.map []) := by
    simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
  refine ⟨.integer 0, ?_, Or.inl rfl⟩
  simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
    Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]

theorem fun_key (n m k : Nat) (x : Term) (field : FunField x) :
    KeyOk (Dispatcher.ofTable Erlang.program.fun_table n) (Dispatcher.ofTable Erlang.program.fun_table m)
      (Dispatcher.ofTable Erlang.program.fun_table k) (.atom "fun") (.tuple #[.atom "negation", .map []]) x := by
  obtain ⟨pos, R, rfl⟩ := field
  cases pos with
  | true =>
    obtain ⟨out, merge, look⟩ := Erlang.maps.merge_with_lookup (Dispatcher.ofTable Erlang.program.fun_table n) false
      "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] R (fun _ _ _ => .nil)
      (by intro e _ v found; simp [mapLookup] at found)
    have same : ∀ q, mapLookup R q = mapLookup out q := by
      intro q
      rw [look q, ← mapLookup_mapEntries R]
      simp only [mapLookup, equalExact_eq_decide]
      cases (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) <;> simp
    refine ⟨.tuple #[.atom "negation", .map out], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2»,
        Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», merge,
        Erlang.erlang.«==/2», Lynx.Except.andAlso]
    · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2»,
        repr_cancel m out R same], fun_absent k⟩
  | false =>
    have keep : Elixir.Module.Types.Descr.«fun_repr_difference/2» (Dispatcher.ofTable Erlang.program.fun_table n)
        (.map R) (.map []) = .ok (.map R) := by
      simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
    by_cases empty : ((R.map Prod.fst).eraseDupsBy (fun a b => decide (compareExact (fuel a b) a b = .eq))).length = 0
    · refine ⟨.integer 0, ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
          Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
      · obtain rfl : R = [] := by
          cases R with
          | nil => rfl
          | cons e rest =>
            simp [List.eraseDupsBy, List.eraseDupsBy.loop] at empty
            exact (loop_ne_nil _ _ _ [] empty).elim
        exact fun_absent k
    · refine ⟨.tuple #[.atom "union", .map R], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
          Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso, empty]
      · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2»,
          repr_cancel m R R (fun _ => rfl)], fun_absent k⟩

theorem list_absent (dc : Dispatcher) (k : Int) :
    CoveredVal dc (.atom "list") (.tuple #[.integer k, .atom "term", .atom "term"])
      (.tuple #[.integer k, .atom "term", .atom "term"]) :=
  ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
    Or.inr (Or.inl rfl)⟩

/-- The difference of all lists with a list BDD of other literals is its negation. -/
theorem list_difference_bdd (k : Int) {x : Term} (wx : Bdd ListOk x) :
    Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[.integer k, .atom "term", .atom "term"]) x =
      Elixir.Module.Types.Descr.«bdd_negation/1» x := by
  have nt := not_top_leaf wx
  unfold Elixir.Module.Types.Descr.«list_difference/2»
  split
  · exact (nt _ rfl).elim
  · rfl
  · next h₁ h₂ => first | exact (h₁ _ rfl).elim | exact (h₁ _ _ rfl).elim | exact absurd rfl (h₁ _) | simp_all

theorem list_key (dn du dc : Dispatcher) (k : Int) (x : Term) (field : ListField x) :
    KeyOk dn du dc (.atom "list") (.tuple #[.integer k, .atom "term", .atom "term"]) x := by
  rcases field with ⟨k', rfl⟩ | wx
  · refine ⟨.atom "bdd_bot", ?_, fun _ => ?_, fun k => by simp [kept] at k⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»]
    · exact ⟨.atom "bdd_bot", by
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
        Or.inr (Or.inl rfl)⟩
  obtain ⟨w, run, keep, sem⟩ := neg_ok wx
  have diff : Elixir.Module.Types.Descr.«bare_difference/3» dn (.atom "list")
      (.tuple #[.integer k, .atom "term", .atom "term"]) x = .ok w := by
    simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wx, run]
  have ww := keep _ wx
  refine ⟨w, diff, fun kw => ⟨w, by
      simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wx, run], ?_⟩, fun _ => ?_⟩
  · simp [kept] at kw
    by_cases e : w = .integer 0
    · exact Or.inl e
    · exact Or.inr (Or.inl (kw e))
  obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
  have wu := keepU _ wx ww
  have unionRun : Elixir.Module.Types.Descr.«list_union/2» x w = Elixir.Module.Types.Descr.«bdd_union/2» x w := by
    have nx := not_top_leaf wx
    have nw := not_top_leaf ww
    unfold Elixir.Module.Types.Descr.«list_union/2»
    split
    · exact (nx _ rfl).elim
    · exact (nw _ rfl).elim
    · rfl
  obtain ⟨w', runW, keepW, semW⟩ := neg_ok wu
  refine ⟨u, by simp [Elixir.Module.Types.Descr.«bare_union/3», unionRun, runU], w', ?_, Or.inr (Or.inr ?_)⟩
  · simp [Elixir.Module.Types.Descr.«bare_difference/3», list_difference_bdd k wu, runW]
  · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
    exact list_empty_unsat dc (keepW _ wu) (fun ρ resp => by
      rw [semW ρ resp, semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl) []

theorem remove_atom_leaf (s : String) (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_remove/2» (.atom s) (.tuple #[k, x, y]) = .ok (.atom s) := by
  unfold Elixir.Module.Types.Descr.«bdd_remove/2»
  unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
  simp [Erlang.erlang.«=:=/2»]

theorem union_bot_leaf (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_bot") (.tuple #[k, x, y]) = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2»]

theorem union_leaf_bot (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2»]

theorem union_two_leaves {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (lt : Term.compare (Term.fuel a b) a b = .lt) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_union/2» a b =
      .ok (.tuple #[.integer h, a, .atom "bdd_top", b, .atom "bdd_bot"]) := by
  have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
  have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
  have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
  have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
  have same : ¬compareExact (fuel a b) a b = .eq := fun e => by
    rw [compare_eq_of_compareExact_eq _ _ e] at lt; cases lt
  have same' : ¬compareExact (fuel b a) b a = .eq := fun e => same (Lynx.Term.compareExact_eq_symm e)
  obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt wa ha hb lt
  rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, rfl⟩ := la; simp at e
  obtain ⟨h₁, node⟩ := node_new a (.atom "bdd_top") b (.atom "bdd_bot") la (Bdd.top (ok := fun _ => True))
    wb (Bdd.bot (ok := fun _ => True))
  refine ⟨h₁, ?_⟩
  obtain ⟨_, _, _, rfl⟩ := la
  obtain ⟨_, _, _, rfl⟩ := lb
  conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2», run, remove_atom_leaf, union_bot_leaf, node, same']

theorem union_two_leaves_gt {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (gt : Term.compare (Term.fuel a b) a b = .gt) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_union/2» a b =
      .ok (.tuple #[.integer h, b, .atom "bdd_top", a, .atom "bdd_bot"]) := by
  have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
  have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
  have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
  have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
  have same : ¬compareExact (fuel a b) a b = .eq := fun e => by
    rw [compare_eq_of_compareExact_eq _ _ e] at gt; cases gt
  have same' : ¬compareExact (fuel b a) b a = .eq := fun e => same (Lynx.Term.compareExact_eq_symm e)
  obtain ⟨h₀, c, u, d, run, split⟩ := compare_gt wb ha hb gt
  rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, rfl⟩ := lb; simp at e
  obtain ⟨h₁, node⟩ := node_new b (.atom "bdd_top") a (.atom "bdd_bot") lb (Bdd.top (ok := fun _ => True))
    wa (Bdd.bot (ok := fun _ => True))
  refine ⟨h₁, ?_⟩
  obtain ⟨_, _, _, rfl⟩ := la
  obtain ⟨_, _, _, rfl⟩ := lb
  conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
  simp [Erlang.erlang.«=:=/2», run, remove_atom_leaf, union_leaf_bot, node, same']

theorem inter_bot_any (b : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_bot") b = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  by_cases e : compareExact (fuel b (.atom "bdd_bot")) b (.atom "bdd_bot") = .eq
  · simp [Erlang.erlang.«=:=/2», e]
  · simp [Erlang.erlang.«=:=/2», e]
    split <;> simp_all

theorem inter_top_any (b : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_top") b = .ok b := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  by_cases e : compareExact (fuel b (.atom "bdd_top")) b (.atom "bdd_top") = .eq
  · have := (compareExact_eq_atom _ _).mp e; subst this; simp [Erlang.erlang.«=:=/2»]
  · simp [Erlang.erlang.«=:=/2», e]

/-- The negation of the union of two leaves negates each in turn. -/
theorem neg_union_leaves {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (lt : Term.compare (Term.fuel a b) a b = .lt) (h : Int) :
    ∃ h₁ h₂ : Int, Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, a, .atom "bdd_top", b, .atom "bdd_bot"]) =
      .ok (.tuple #[.integer h₁, a, .atom "bdd_bot", .atom "bdd_bot",
        .tuple #[.integer h₂, b, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]]) := by
  obtain ⟨hA, nodeA⟩ := node_new a (.atom "bdd_bot") (.atom "bdd_bot") (.atom "bdd_top") la
    (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
  obtain ⟨hB, nodeB⟩ := node_new b (.atom "bdd_bot") (.atom "bdd_bot") (.atom "bdd_top") lb
    (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) (Bdd.top (ok := fun _ => True))
  let nB : Term := .tuple #[.integer hB, b, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]
  have wnB : Bdd (fun _ => True) nB := by
    obtain ⟨_, _, _, rfl⟩ := lb
    simp [nB, Bdd, IsLeaf]
  have wnA : Bdd (fun _ => True) (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) := by
    obtain ⟨_, _, _, rfl⟩ := la
    simp [Bdd, IsLeaf]
  obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt (b := nB) wnA (by simp [head]) (by simp [nB, head]) lt
  rcases split with ⟨_, e⟩ | ⟨e, -⟩
  · simp at e
    obtain ⟨-, rfl, rfl, rfl⟩ := e
    obtain ⟨h₃, node3⟩ := node_new a (.atom "bdd_bot") (.atom "bdd_bot") nB la
      (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) wnB
    refine ⟨h₃, hB, ?_⟩
    have notSame : ¬compareExact (fuel nB (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"])) nB (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) = .eq := by
      intro e
      obtain ⟨_, _, _, _, _, e', b₁, -⟩ := tuple5_exact e
      simp at e'
      obtain ⟨-, rfl, -⟩ := e'
      rw [compare_eq_of_compareExact_eq _ _ (Lynx.Term.compareExact_eq_symm b₁)] at lt
      cases lt
    have inter : Elixir.Module.Types.Descr.«bdd_intersection/2»
        (.tuple #[.integer hA, a, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) nB =
          .ok (.tuple #[.integer h₃, a, .atom "bdd_bot", .atom "bdd_bot", nB]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [nB, Erlang.erlang.«=:=/2», notSame, run, inter_bot_any, inter_top_any, node3]
    have negTop : Elixir.Module.Types.Descr.«bdd_negation/1» (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
      unfold Elixir.Module.Types.Descr.«bdd_negation/1»; rfl
    have negBot : Elixir.Module.Types.Descr.«bdd_negation/1» (.atom "bdd_bot") = .ok (.atom "bdd_top") := by
      unfold Elixir.Module.Types.Descr.«bdd_negation/1»; rfl
    have negB : Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok nB := by
      obtain ⟨_, _, _, rfl⟩ := lb
      unfold Elixir.Module.Types.Descr.«bdd_negation/1»
      simpa using nodeB
    conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
    simp [negTop, negBot, nodeA, negB, inter, Erlang.erlang.«=:=/2», nB]
  · obtain ⟨_, _, _, rfl⟩ := la
    simp at e

theorem inter_term (d : Dispatcher) :
    Elixir.Module.Types.Descr.«bare_intersection/2» d (.atom "term") (.atom "term") = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl

theorem meets_term (d : Dispatcher) (S e : Term) (he : e = .nil ∨ e = Term.list [.atom "term"]) :
    Elixir.Module.Types.Descr.«tuple_elements_meets/4» d e (Term.list [.atom "term"]) .nil S =
      .ok (Term.list [.atom "term"]) := by
  have seenTerm : Elixir.Module.Types.Descr.«empty_seen?/2» d (.atom "term") S = .ok (.atom "false") := by
    unfold Elixir.Module.Types.Descr.«empty_seen?/2»; rfl
  rcases he with rfl | rfl <;>
  · rw [Elixir.Module.Types.Descr.«tuple_elements_meets/4».eq_def]
    simp [Term.list, inter_term, seenTerm, isMember]
    rw [Elixir.Module.Types.Descr.«tuple_elements_meets/4».eq_def]
    rfl

theorem meets_nil (d : Dispatcher) (e S : Term) :
    Elixir.Module.Types.Descr.«tuple_elements_meets/4» d e .nil .nil S = .ok .nil := by
  rw [Elixir.Module.Types.Descr.«tuple_elements_meets/4».eq_def]; rfl

theorem elements_term (d : Dispatcher) (acc tag negs S e : Term) (he : e = .nil ∨ e = Term.list [.atom "term"]) :
    Elixir.Module.Types.Descr.«tuple_elements_empty?/7» d acc tag e (Term.list [.atom "term"])
      (Term.list [.atom "term"]) negs S = .ok (.atom "true") := by
  have diff : Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") (.atom "term") = .ok (.map []) := by
    unfold Elixir.Module.Types.Descr.«bare_difference/2»; rfl
  have seenNone : Elixir.Module.Types.Descr.«empty_seen?/2» d (.map []) S = .ok (.atom "true") := by
    unfold Elixir.Module.Types.Descr.«empty_seen?/2»
    simp [getMapKeys, Erlang.erlang.«==/2»]
  rcases he with rfl | rfl <;>
  · rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/7».eq_def]
    simp [Term.list, diff, seenNone, isMember]
    rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/7».eq_def]
    rfl

theorem elements_nil (d : Dispatcher) (acc tag e m negs S : Term) :
    Elixir.Module.Types.Descr.«tuple_elements_empty?/7» d acc tag e .nil m negs S = .ok (.atom "true") := by
  rw [Elixir.Module.Types.Descr.«tuple_elements_empty?/7».eq_def]; rfl

theorem cmp10 : Ord.compare (1 : Int) 0 = .gt := by decide
theorem cmp01 : Ord.compare (0 : Int) 1 = .lt := by decide
theorem cmp11 : Ord.compare (1 : Int) 1 = .eq := by decide

theorem dup_zero : Erlang.lists.«duplicate/2» (.integer 0) (.atom "term") = .ok .nil := by
  simp [Erlang.lists.«duplicate/2», Erlang.erlang.«>=/2», Erlang.erlang.«and/2»]
  rw [Erlang.lists.«duplicate/3».eq_def]
  simp

theorem dup_one : Erlang.lists.«duplicate/2» (.integer 1) (.atom "term") = .ok (Term.list [.atom "term"]) := by
  simp [Erlang.lists.«duplicate/2», Erlang.erlang.«>=/2», Erlang.erlang.«and/2», cmp10]
  rw [Erlang.lists.«duplicate/3».eq_def]
  simp
  rw [Erlang.lists.«duplicate/3».eq_def]
  simp [Term.list]

theorem fill_zero : Elixir.Module.Types.Descr.«tuple_fill/2» .nil (.integer 0) = .ok .nil := by
  simp [Elixir.Module.Types.Descr.«tuple_fill/2», Erlang.erlang.«length/1», Erlang.erlang.«</2»,
    dup_zero, Erlang.erlang.«++/2»]

theorem fill_one : Elixir.Module.Types.Descr.«tuple_fill/2» .nil (.integer 1) = .ok (Term.list [.atom "term"]) := by
  simp [Elixir.Module.Types.Descr.«tuple_fill/2», Erlang.erlang.«length/1», Erlang.erlang.«</2»,
    dup_one, Erlang.erlang.«++/2», cmp10]

theorem line_lt (d : Dispatcher) (k H : Int) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open") .nil
      (.cons (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]])
        (.cons (.tuple #[.integer k, .atom "closed", .nil]) .nil)) S = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«length/1», Lynx.Except.orElse,
    Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2»,
    meets_nil, meets_term d S _ (Or.inl rfl), elements_term d _ _ _ S _ (Or.inl rfl),
    Elixir.Module.Types.Descr.«tuple_empty_arity?/7»,
    Elixir.Module.Types.Descr.«tuple_empty_sizes?/5», fill_zero, cmp01,
    elements_nil]

theorem line_gt (d : Dispatcher) (k H : Int) (S : Term) :
    Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open") .nil
      (.cons (.tuple #[.integer k, .atom "closed", .nil])
        (.cons (.tuple #[.integer H, .atom "open", Term.list [.atom "term"]]) .nil)) S = .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«tuple_line_empty?/4», Erlang.erlang.«length/1», Lynx.Except.orElse,
    Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», elements_nil,
    Elixir.Module.Types.Descr.«tuple_empty_arity?/7»,
    Elixir.Module.Types.Descr.«tuple_empty_sizes?/5», fill_one,
    meets_nil, meets_term d S _ (Or.inr rfl), elements_nil, elements_term d _ _ _ S _ (Or.inr rfl)]

theorem any_nil (d : Dispatcher) (m n : String) (caps : Array Term) :
    Erlang.lists.«any/2» d (.function false m n 1 caps) .nil = .ok (.atom "false") := by
  simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2»]

theorem special_lt (d : Dispatcher) (h₁ h₂ k H : Int) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» d
      (.tuple #[.integer h₁, .tuple #[.integer k, .atom "closed", .nil], .atom "bdd_bot", .atom "bdd_bot",
        .tuple #[.integer h₂, .tuple #[.integer H, .atom "open", Term.list [.atom "term"]], .atom "bdd_bot",
          .atom "bdd_bot", .atom "bdd_top"]]) (.map []) = .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.false,
    Erlang.maps.«put/3»]
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
    Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]
  rw [line_lt]; rfl

theorem special_gt (d : Dispatcher) (h₁ h₂ k H : Int) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» d
      (.tuple #[.integer h₁, .tuple #[.integer H, .atom "open", Term.list [.atom "term"]], .atom "bdd_bot", .atom "bdd_bot",
        .tuple #[.integer h₂, .tuple #[.integer k, .atom "closed", .nil], .atom "bdd_bot",
          .atom "bdd_bot", .atom "bdd_top"]]) (.map []) = .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», Term.false,
    Erlang.maps.«put/3»]
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
    Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil]
  rw [line_gt]; rfl

theorem dropped {q w : Term} (k : kept (q, w) = Bool.false) : w = .integer 0 ∨ w = .atom "bdd_bot" := by
  simp [kept] at k
  by_cases e : w = .integer 0
  · exact Or.inl e
  · exact Or.inr (k e)

/-- The difference of all tuples with a tautology of tuple literals is empty. -/
theorem tuple_taut (ops : ElemOk E K) {m : Nat} (hm : K + 1 ≤ m) {u : Term} (wu : Bdd (TupleOk E) u) (taut : ∀ ρ, Resp ρ → eval ρ u = Bool.true) :
    CoveredVal (D m) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) u := by
  rcases wu.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, d, e, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
    simp [Elixir.Module.Types.Descr.«bare_difference/3»]
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    simp [diff_leaf_top]
  · have := taut _ (resp_const Bool.false); simp at this
  · have := taut _ (resp_const Bool.false); simp [eval] at this
  · obtain ⟨w, run, keep, sem⟩ := neg_ok wu
    refine ⟨w, ?_, Or.inr (Or.inr ?_)⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [run]
    · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
      exact tuple_empty_unsat ops (keep _ wu) (fun _ h => h.1) (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) m [] hm

theorem tuple_union_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«tuple_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
  unfold Elixir.Module.Types.Descr.«tuple_union/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem tuple_absent (n : Nat) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer 61102469, .atom "open", .nil]) :=
  ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»],
    Or.inr (Or.inl rfl)⟩

/-- A tuple BDD that is neither bottom, top, nor `{}` has its negation as difference. -/
theorem tuple_key_neg (ops : ElemOk E K) (dn du : Dispatcher) {m : Nat} (hm : K + 1 ≤ m) (x : Term) (wx : Bdd (TupleOk E) x)
    (run : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x =
      Elixir.Module.Types.Descr.«bdd_negation/1» x) :
    KeyOk dn du (D m) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
  have notTop := not_top_of_ok wx fun t h => h.2
  obtain ⟨w, neg, keep, sem⟩ := neg_ok wx
  have ww := keep _ wx
  have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w := by
    intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», run, neg]
  refine ⟨w, diff _, fun kw => ⟨w, diff _, ?_⟩, fun _ => ?_⟩
  · rcases dropped kw with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
  have wu := keepU _ wx ww
  refine ⟨u, ?_, tuple_taut ops hm wu fun ρ resp => ?_⟩
  · simp [Elixir.Module.Types.Descr.«bare_union/3», tuple_union_bdd notTop (not_top_of_ok ww fun t h => h.2), runU]
  · rw [semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl

theorem tuple_key (ops : ElemOk E K) (dn du : Dispatcher) {m : Nat} (hm : K + 1 ≤ m) (x : Term) (field : TupleField E x) :
    KeyOk dn du (D m) (.atom "tuple")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
  rcases field with ⟨k, rfl⟩ | wx
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by
      intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
      intro d
      simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_top]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«tuple_union/2»],
        tuple_absent _⟩
  · obtain ⟨⟨k', tag, ls, e, tags, elems⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
    simp at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    by_cases special : tag = "closed" ∧ ls = []
    · obtain ⟨rfl, rfl⟩ := special
      obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
      let W : Term := .tuple #[.integer ((1 <<< 27) + hash), .atom "open", Term.list [.atom "term"]]
      have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "tuple")
          (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "closed", Term.list []]) =
            .ok W := by
        intro d
        simp [Elixir.Module.Types.Descr.«bare_difference/3»]
        unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
          Elixir.Module.Types.Descr.«bdd_leaf_key/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«length/1», Erlang.erlang.«bsl/2», W]
        rfl
      refine ⟨W, diff _, fun k => by simp [kept, W] at k, fun _ => ?_⟩
      have lX : IsLeaf (.tuple #[.integer k, .atom "closed", Term.list []]) := ⟨_, _, _, rfl⟩
      have lW : IsLeaf W := ⟨_, _, _, rfl⟩
      have unionRun : ∀ u, Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k, .atom "closed", Term.list []]) W = .ok u →
          Elixir.Module.Types.Descr.«bare_union/3» du (.atom "tuple") (.tuple #[.integer k, .atom "closed", Term.list []]) W =
            .ok u := by
        intro u run
        simp [Elixir.Module.Types.Descr.«bare_union/3»]
        rw [tuple_union_bdd notTop (by intro k e; simp [W] at e)]
        exact run
      by_cases order : k ≤ (1 <<< 27) + hash
      · have lt : Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", Term.list []]) W) (.tuple #[.integer k, .atom "closed", Term.list []]) W = .lt := by
          have ca : Term.compare (Term.fuel (Term.atom "closed") (.atom "open")) (Term.atom "closed") (.atom "open") = .lt := by cbv
          simp [W, compare_tuple, List.compareLex_cons_cons, ca]
          have order' : k ≤ 134217728 + (hash : Int) := by simpa using order
          rcases Int.lt_or_eq_of_le order' with o | o
          · simp [Int.compare_eq_lt.mpr o]
          · rw [o]; simp
        obtain ⟨h, run⟩ := union_two_leaves lX lW lt
        obtain ⟨h₁, h₂, neg⟩ := neg_union_leaves lX lW lt h
        refine ⟨_, unionRun _ run, .tuple #[.integer h₁, (.tuple #[.integer k, .atom "closed", Term.list []]), .atom "bdd_bot", .atom "bdd_bot",
          .tuple #[.integer h₂, W, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]], ?_, Or.inr (Or.inr ?_)⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [neg]
        · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
          exact special_lt _ _ _ _ _
      · have lt : Term.compare (Term.fuel W (.tuple #[.integer k, .atom "closed", Term.list []])) W (.tuple #[.integer k, .atom "closed", Term.list []]) = .lt := by
          have o : 134217728 + (hash : Int) < k := by simp at order; omega
          simp [W, compare_tuple, List.compareLex_cons_cons, Int.compare_eq_lt.mpr o]
        have gt : Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", Term.list []]) W) (.tuple #[.integer k, .atom "closed", Term.list []]) W = .gt := by
          rw [Lynx.Term.compare_gt_iff_lt]; exact lt
        obtain ⟨h, run⟩ := union_two_leaves_gt lX lW gt
        obtain ⟨h₁, h₂, neg⟩ := neg_union_leaves lW lX lt h
        refine ⟨_, unionRun _ run, .tuple #[.integer h₁, W, .atom "bdd_bot", .atom "bdd_bot",
          .tuple #[.integer h₂, (.tuple #[.integer k, .atom "closed", Term.list []]), .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]], ?_, Or.inr (Or.inr ?_)⟩
        · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [neg]
        · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
          exact special_gt _ _ _ _ _
    · have notSpecial : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠
          .tuple #[k₁, .atom "closed", .nil] := by
        intro k₁ e
        simp at e
        apply special
        refine ⟨e.2.1, ?_⟩
        cases ls <;> simp_all [Term.list]
      refine tuple_key_neg ops dn du hm _ wx ?_
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split
      · next _ _ e =>
        exfalso
        simp at e
        obtain ⟨-, rfl, hl⟩ := e
        exact notTopX ⟨_, by rw [hl]⟩
      · next _ _ e => exact (notSpecial _ e).elim
      · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; rfl
      · next h₁ => exact (h₁ _ _ rfl rfl).elim
  · refine tuple_key_neg ops dn du hm _ wx ?_
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    simp

theorem map_taut (ops : ElemOk E K) {m : Nat} (hm : K + 2 ≤ m) {u : Term} (wu : Bdd (MapOk E) u) (taut : ∀ ρ, Resp ρ → eval ρ u = Bool.true) :
    CoveredVal (D m) (.atom "map")
      (.tuple #[.integer 61102469, .atom "open", .nil]) u := by
  rcases wu.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, d, e, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, Or.inr (Or.inl rfl)⟩
    simp [Elixir.Module.Types.Descr.«bare_difference/3»]
    unfold Elixir.Module.Types.Descr.«map_difference/2»
    simp [diff_leaf_top]
  · have := taut _ (resp_const Bool.false); simp at this
  · have := taut _ (resp_const Bool.false); simp [eval] at this
  · obtain ⟨w, run, keep, sem⟩ := neg_ok wu
    refine ⟨w, ?_, Or.inr (Or.inr ?_)⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [run]
    · simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
      exact map_empty_unsat ops (keep _ wu) (fun _ h => h.1) (fun ρ resp => by rw [sem ρ resp, taut ρ resp]; rfl) m [] hm

theorem map_union_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«map_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
  unfold Elixir.Module.Types.Descr.«map_union/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem map_absent (n : Nat) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table n) (.atom "map")
      (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer 61102469, .atom "open", .nil]) :=
  ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»],
    Or.inr (Or.inl rfl)⟩

theorem map_key (ops : ElemOk E K) (dn du : Dispatcher) {m : Nat} (hm : K + 2 ≤ m) (x : Term) (field : MapField E x) :
    KeyOk dn du (D m) (.atom "map")
      (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
  rcases field with ⟨k, rfl⟩ | wx
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by
      intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  have neg : (∃ h lit c u d, x = .tuple #[.integer h, lit, c, u, d]) ∨ (∃ k x₁ y₁, x = .tuple #[.integer k, x₁, y₁]) →
      KeyOk dn du (D m) (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) x := by
    intro shape
    obtain ⟨w, neg, keep, sem⟩ := neg_ok wx
    have ww := keep _ wx
    have run : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x =
        .ok w := by
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      rcases shape with ⟨h, lit, c, u, d, rfl⟩ | ⟨k, x₁, y₁, rfl⟩
      · simp [neg]
      · split
        · next _ _ e => exact (notTop _ e).elim
        · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact neg
        · next h₁ => exact (h₁ _ _ rfl rfl).elim
    have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok w := by
      intro d; simp [Elixir.Module.Types.Descr.«bare_difference/3», run]
    refine ⟨w, diff _, fun kw => ⟨w, diff _, ?_⟩, fun _ => ?_⟩
    · rcases dropped kw with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    obtain ⟨u, runU, keepU, semU⟩ := union_ok wx ww
    have wu := keepU _ wx ww
    refine ⟨u, ?_, map_taut ops hm wu fun ρ resp => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_union/3», map_union_bdd notTop (not_top_of_ok ww fun t h => h.2), runU]
    · rw [semU ρ resp, sem ρ resp]; cases eval ρ x <;> rfl
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · have diff : ∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "map")
        (.tuple #[.integer 61102469, .atom "open", .nil]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
      intro d
      simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_top]
    exact ⟨_, diff _, fun _ => ⟨_, diff _, Or.inr (Or.inl rfl)⟩, fun k => by simp [kept] at k⟩
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun k => by simp [kept] at k, fun _ => ?_⟩
    · simp [Elixir.Module.Types.Descr.«bare_difference/3»]
      unfold Elixir.Module.Types.Descr.«map_difference/2»
      simp [diff_leaf_bot]
    · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«map_union/2»],
        map_absent _⟩
  · exact neg (Or.inr ⟨_, _, _, rfl⟩)
  · exact neg (Or.inl ⟨_, _, _, _, _, rfl⟩)

/-- Unions of static types merge their fields, uniting those in both. -/
theorem union_lookup (depth : Nat) (L R : List (Term × Term))
    (staticL : mapLookup L (.atom "dynamic") = Option.none) (staticR : mapLookup R (.atom "dynamic") = Option.none)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ u, Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) q x y = .ok u) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        (.map L) (.map R) = .ok (.map U) ∧
      ∀ name, (mapLookup R (.atom name) = Option.none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
        (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = Option.none →
          mapLookup U (.atom name) = some y) ∧
        (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
          Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y =
            .ok u → mapLookup U (.atom name) = some u) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, Elixir.Module.Types.Descr.«bare_union/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
      q x y = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  obtain ⟨U, run, look⟩ : ∃ U, Elixir.Module.Types.Descr.«bare_union/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) = .ok (.map U) ∧
      ∀ name, mapLookup U (.atom name) =
        match mapLookup R (.atom name) with
        | some y => some (match mapLookup L (.atom name) with | some x => g (.atom name) x y | none => y)
        | none => mapLookup L (.atom name) := by
    unfold Elixir.Module.Types.Descr.«bare_union/2»
    simp [getMapKeys_single, Erlang.erlang.«==/2», staticL, staticR]
    by_cases emptyL : L = []
    · subst emptyL
      refine ⟨R, by simp, fun name => ?_⟩
      cases mapLookup R (.atom name) <;> simp [mapLookup]
    by_cases emptyR : R = []
    · subst emptyR
      exact ⟨L, by simp [emptyL], fun name => by simp [mapLookup]⟩
    simp only [emptyL, emptyR]
    unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
    obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) false "Elixir.Module.Types.Descr" "bare_union" #[] L R g (by
        intro e me x hx
        have hy := mapLookup_of_mem_mapEntries me
        obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
        rw [Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure, ru, value _ _ _ _ ru])
    refine ⟨out, by simpa using run, fun name => ?_⟩
    rw [look, find_atom]
    cases mapLookup R (.atom name) <;> rfl
  refine ⟨U, run, fun name => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩⟩
  · rw [look, hR]
  · rw [look, hR, hL]
  · rw [look, hR, hL]; simp only [value _ _ _ _ ru]

theorem term_keys {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {q t : Term} (hT : mapLookup T q = some t) :
    (q = .atom "bitmap" ∧ t = .integer 255) ∨ (q = .atom "atom" ∧ t = .tuple #[.atom "negation", .map []]) ∨
      (q = .atom "fun" ∧ t = .tuple #[.atom "negation", .map []]) ∨
      (q = .atom "list" ∧ t = .tuple #[.integer 46675407, .atom "term", .atom "term"]) ∨
      (q = .atom "tuple" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) ∨
      (q = .atom "map" ∧ t = .tuple #[.integer 61102469, .atom "open", .nil]) := by
  simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at term
  cases term
  simp only [mapLookup, List.find?, equalExact_eq_decide] at hT
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  split at hT
  · simp at hT; rename_i e; simp at e; simp [e, hT]
  · simp at hT

/-- Each field of the top type is covered by what a field type and its negation unite into. -/
theorem key_ok (δ : Nat) (ops : ElemOk E K) (hK : K ≤ δ + 90) (X : List (Term × Term)) (valid : Negatable E X) {T : List (Term × Term)}
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) {q t x : Term}
    (hT : mapLookup T q = some t) (hX : mapLookup X q = some x) :
    KeyOk (Dispatcher.ofTable Erlang.program.fun_table (δ + 98)) (Dispatcher.ofTable Erlang.program.fun_table (δ + 99))
      (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) q t x := by
  rcases term_keys term hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨b, rfl, -, le⟩ := valid.bitmap x hX
    exact bitmap_key _ _ _ b le
  · obtain ⟨p, S, rfl, set⟩ := valid.atom x hX
    exact atom_key _ _ _ p S set
  · exact fun_key (δ + 98) (δ + 99) (δ + 100) x (valid.funs x hX)
  · exact list_key _ _ _ _ x (valid.lists x hX).list
  · exact tuple_key ops _ _ (by omega) x (valid.tuples x hX)
  · exact map_key ops _ _ (by omega) x (valid.maps x hX)

/-- Fields of the top type are covered by themselves. -/
theorem key_absent (δ : Nat) {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {q t : Term} (hT : mapLookup T q = some t) :
    CoveredVal (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) q t t := by
  rcases term_keys term hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact bitmap_absent _
  · exact atom_absent _
  · exact fun_absent _
  · exact list_absent _ _
  · exact tuple_absent _
  · exact map_absent _

theorem atom_key_of {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    {q t : Term} (hT : mapLookup T q = some t) : ∃ name, q = .atom name := by
  rcases term_keys term hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨_, rfl⟩

/-- A type united with its negation covers the top type. -/
theorem union_negation_covers (δ : Nat) (ops : ElemOk E K) (hK : K ≤ δ + 90) (X : List (Term × Term)) (valid : Negatable E X)
    (nonempty : X ≠ []) :
    ∃ N U, Elixir.Module.Types.Descr.«bare_negation/1» (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) =
        .ok (.map N) ∧
      Elixir.Module.Types.Descr.«bare_union/2» (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.map N) =
        .ok (.map U) ∧ mapLookup U (.atom "dynamic") = Option.none ∧
      Elixir.Module.Types.Descr.«subtype?/2» (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.atom "term")
        (.map U) = .ok (.atom "true") := by
  obtain ⟨N, negation, staticN, -, -, -, -, -, -, lookups⟩ := negation_fields ops (δ + 98) X valid nonempty
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  have inT : ∀ q x, mapLookup X q = some x → ∃ t, mapLookup T q = some t := by
    intro q x hX
    have := term
    simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at this
    cases this
    rcases valid.keys q (by simp [hX]) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mapLookup]
  obtain ⟨U, union, lookU⟩ := union_lookup (δ + 99) X N valid.static staticN (by
    intro q x y hX hN
    obtain ⟨t, hT⟩ := inT q x hX
    obtain ⟨name, rfl⟩ := atom_key_of term hT
    obtain ⟨w, run, -, keep⟩ := key_ok δ ops hK X valid term hT hX
    have look := (lookups T term name t hT).2 x w hX run
    rw [hN] at look
    by_cases k : kept (.atom name, w) = Bool.true
    · simp only [k, ite_true, Option.some.injEq] at look
      obtain ⟨u, ru, -⟩ := keep k
      exact ⟨u, look ▸ ru⟩
    · simp [k] at look)
  have staticU : mapLookup U (.atom "dynamic") = Option.none := by
    rw [(lookU "dynamic").1 staticN]
    exact valid.static
  refine ⟨N, U, negation, union, staticU, subtype_term _ T U term staticU fun e member => ?_⟩
  have hT := mapLookup_of_mem_mapEntries member
  obtain ⟨name, key⟩ := atom_key_of term hT
  rw [key] at hT ⊢
  cases hX : mapLookup X (.atom name) with
  | none =>
    have hN := (lookups T term name e.2 hT).1 hX
    obtain ⟨w, run, empty⟩ := key_absent δ term hT
    exact ⟨e.2, w, (lookU name).2.1 _ hN hX, run, empty⟩
  | some x =>
    obtain ⟨w, run, drop, keep⟩ := key_ok δ ops hK X valid term hT hX
    have look := (lookups T term name e.2 hT).2 x w hX run
    by_cases k : kept (.atom name, w) = Bool.true
    · obtain ⟨u, ru, w', rw', empty⟩ := keep k
      simp only [k, ite_true] at look
      exact ⟨u, w', (lookU name).2.2 x w u hX look ru, rw', empty⟩
    · simp only [k, Bool.false_eq_true, ite_false] at look
      obtain ⟨w', rw', empty⟩ := drop (by simpa using k)
      exact ⟨x, w', by rw [(lookU name).1 look, hX], rw', empty⟩

end Elixir.STTDescrProofsTest
