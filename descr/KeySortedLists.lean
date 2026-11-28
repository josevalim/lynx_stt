module

public import Erlang.program
public import ListsRukeymerge
public import OpenMapDomain
public import OpenMapSubtype

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- Lists sorted strictly by their keys. -/
def SKL (dl : List (Term × Term)) : Prop := dl.Pairwise fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt

/-- Lists of atoms sorted strictly. -/
def SAK (ks : List Term) : Prop := ks.Pairwise fun a b => Term.compare (Term.fuel a b) a b = .lt

theorem map_pairs_val (m : Nat) (val : Term) : ∀ K : List Term,
    Erlang.lists.«map_1/2» (D m) (.function false "Elixir.Module.Types.Descr" "-fields_put_all_new/3-fun-0-" 1 #[val])
      (Term.list K) = .ok (fieldsTerm (K.map fun k => (k, val)))
  | [] => by simp [Erlang.lists.«map_1/2», fieldsTerm]
  | k :: K => by
    have := map_pairs_val m val K
    simp only [fieldsTerm] at this ⊢
    rw [Erlang.lists.«map_1/2».eq_def]
    simp [this, Elixir.Module.Types.Descr.«-fields_put_all_new/3-fun-0-/2»]

theorem fpa_nil_keys (m : Nat) (val : Term) (dl : List (Term × Term)) :
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (fieldsTerm dl) .nil val = .ok (fieldsTerm dl) := by
  rw [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def]
  cases dl <;> rfl

theorem fpa_nil_fields (m : Nat) (val k : Term) (K : List Term) :
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (fieldsTerm []) (Term.list (k :: K)) val =
      .ok (fieldsTerm ((k :: K).map fun k => (k, val))) := by
  rw [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def]
  have := map_pairs_val m val K
  simp only [fieldsTerm, List.map_nil] at this ⊢
  simp [Erlang.lists.«map/2», Erlang.erlang.«is_function/2», this,
    Elixir.Module.Types.Descr.«-fields_put_all_new/3-fun-0-/2»]

theorem skl_cons {x : Term × Term} {dl : List (Term × Term)} :
    SKL (x :: dl) ↔ (∀ y ∈ dl, Term.compare (Term.fuel x.1 y.1) x.1 y.1 = .lt) ∧ SKL dl := List.pairwise_cons

theorem sak_cons {k : Term} {K : List Term} :
    SAK (k :: K) ↔ (∀ y ∈ K, Term.compare (Term.fuel k y) k y = .lt) ∧ SAK K := List.pairwise_cons

theorem atom_cmp_eq {a b : String} : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b) = .eq ↔ a = b := by
  simp

theorem lookup_cons_ne {k1 k : Term} {v1 : Term} {dl : List (Term × Term)} (ne : compareExact (fuel k k1) k k1 ≠ .eq) :
    mapLookup ((k1, v1) :: dl) k = mapLookup dl k := by
  simp [mapLookup, ne]

theorem lookup_cons_eq {k1 k : Term} {v1 : Term} {dl : List (Term × Term)} (e : compareExact (fuel k k1) k k1 = .eq) :
    mapLookup ((k1, v1) :: dl) k = some v1 := by
  simp [mapLookup, e]

/-- `fields_put_all_new/3` over all the keys of a list that includes the keys of the fields gives each key its
field, or the value. -/
theorem fpa_run (m : Nat) (val : Term) : ∀ (K : List Term) (dl : List (Term × Term)),
    SAK K → (∀ k ∈ K, ∃ s, k = .atom s) → SKL dl → (∀ e ∈ dl, e.1 ∈ K) →
    Elixir.Module.Types.Descr.«fields_put_all_new/3» (D m) (fieldsTerm dl) (Term.list K) val =
      .ok (fieldsTerm (K.map fun k => (k, (mapLookup dl k).getD val)))
  | [], dl, _, _, _, hd => by
    have : dl = [] := List.eq_nil_iff_forall_not_mem.mpr fun e he => by simpa using hd e he
    subst this
    exact fpa_nil_keys m val []
  | k :: K, [], sk, ka, _, _ => by
    simpa [mapLookup] using fpa_nil_fields m val k K
  | k :: K, (k1, v1) :: dl, sk, ka, sd, hd => by
    have sd' := skl_cons.1 sd
    have sk' := sak_cons.1 sk
    obtain ⟨s, rfl⟩ := ka k (by simp)
    have hk1 := hd (k1, v1) (by simp)
    simp only [List.mem_cons] at hk1
    obtain ⟨s1, rfl⟩ : ∃ s1, k1 = .atom s1 := by
      rcases hk1 with h | h
      · exact ⟨s, h⟩
      · exact ka k1 (by simp [h])
    rw [Elixir.Module.Types.Descr.«fields_put_all_new/3».eq_def]
    simp only [fieldsTerm_cons, USort.lt_ok, USort.gt_ok, USort.g_if]
    -- the least key of the list is at most the first key of the fields
    have notlt : ¬Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s) = .lt := by
      intro l
      rcases hk1 with h | h
      · cases h; simp at l
      · have := sk'.1 _ h; rw [USort.c_swap, l] at this; simp at this
    have nl : ¬(Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s)).isLT = Bool.true := USort.not_islt notlt
    simp only [nl, Bool.false_eq_true, ↓reduceIte]
    by_cases g : (Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s)).isGT = Bool.true
    · simp only [g, ↓reduceIte]
      have g' := USort.isgt_lt g
      have rest := fpa_run m val K ((.atom s1, v1) :: dl) sk'.2 (fun k hk => ka k (by simp [hk])) sd (by
        intro e he
        have := hd e he
        simp only [List.mem_cons] at this
        rcases this with h | h
        · exfalso
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · simp only at h; rw [h] at g'; simp at g'
          · have := sd'.1 e he; rw [h] at this; rw [USort.c_swap, g'] at this; simp at this
        · exact h)
      have ne : compareExact (fuel (.atom s) (.atom s1)) (.atom s) (.atom s1) ≠ .eq := by
        intro e; simp at e; subst e; simp at g'
      have none : mapLookup dl (.atom s) = none := by
        simp only [mapLookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq, equalExact_eq_decide]
        intro e he c
        rw [atom_compareExact_eq] at c
        have := sd'.1 e he; rw [c] at this
        exact notlt this
      simp only [List.map_cons, lookup_cons_ne ne, fieldsTerm_cons, none, Option.getD_none]
      rw [show (Term.tuple ⟨[.atom s1, v1]⟩).cons (fieldsTerm dl) = fieldsTerm ((.atom s1, v1) :: dl) from rfl,
        rest]
      rfl
    · simp only [g, Bool.false_eq_true, ↓reduceIte]
      have e : s1 = s := by
        cases h : Term.compare (Term.fuel (.atom s1) (.atom s)) (.atom s1) (.atom s) with
        | lt => exact absurd h notlt
        | eq => simpa using h
        | gt => simp [h] at g
      subst e
      have rest := fpa_run m val K dl sk'.2 (fun k hk => ka k (by simp [hk])) sd'.2 (by
        intro e he
        rcases (List.mem_cons.mp (hd e (by simp [he]))) with h | h
        · have := sd'.1 e he; rw [h] at this; simp at this
        · exact h)
      simp only [rest, Lynx.Except.ok_bind, List.map_cons, fieldsTerm_cons,
        lookup_cons_eq (show compareExact (fuel (.atom s1) (.atom s1)) (.atom s1) (.atom s1) = .eq by simp), Option.getD_some]
      have congr : K.map (fun k => (k, (mapLookup ((.atom s1, v1) :: dl) k).getD val)) =
          K.map (fun k => (k, (mapLookup dl k).getD val)) := by
        refine List.map_congr_left fun k hk => ?_
        obtain ⟨s', rfl⟩ := ka k (by simp [hk])
        have ne : compareExact (fuel (.atom s') (.atom s1)) (.atom s') (.atom s1) ≠ .eq := by
          intro c; simp at c; subst c; have := sk'.1 _ hk; simp at this
        rw [lookup_cons_ne ne]
      rw [congr]
      rfl

theorem exact_ok (a b : Term) : Erlang.erlang.«=:=/2» a b =
    .ok (if compareExact (fuel a b) a b = .eq then Term.atom "true" else Term.atom "false") := by
  simp [Erlang.erlang.«=:=/2»]

theorem lookup_none_of {k : Term} {dl : List (Term × Term)} (h : ∀ e ∈ dl, compareExact (fuel k e.1) k e.1 ≠ .eq) :
    mapLookup dl k = none := by
  simp only [mapLookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq, equalExact_eq_decide]
  exact h

section
variable {t : Term} {n : Nat}

/-- Domains: sorted atom keys with element types of a level. -/
def DomL (t : Term) (n : Nat) (dl : List (Term × Term)) : Prop :=
  SKL dl ∧ ∀ e ∈ dl, (∃ s, e.1 = .atom s) ∧ (level t n).E e.2

/-- `map_put_domain/4` adds a value at sorted keys, joining it with the values already there. -/
theorem mpd_run {m : Nat} (hm : (level t n).K ≤ m) {v : Term} (hv : (level t n).E v) :
    ∀ (N : Nat) (dl : List (Term × Term)) (ks : List Term), dl.length + ks.length ≤ N → DomL t n dl → SAK ks →
      (∀ k ∈ ks, ∃ s, k = .atom s) →
      ∃ dl', Elixir.Module.Types.Descr.«map_put_domain/4» (D m) (fieldsTerm dl) (Term.list ks) v v =
        .ok (fieldsTerm dl') ∧ DomL t n dl' ∧ (∀ e ∈ dl', e.1 ∈ dl.map Prod.fst ∨ e.1 ∈ ks) ∧
        ∀ s, ((mapLookup dl' (.atom s)).isNone ↔ (mapLookup dl (.atom s)).isNone ∧ Term.atom s ∉ ks) ∧
          ∀ U', mapLookup dl' (.atom s) = some U' → ∀ x, (level t n).den U' x ↔
            ((∃ U, mapLookup dl (.atom s) = some U ∧ (level t n).den U x) ∨ (Term.atom s ∈ ks ∧ (level t n).den v x)) := by
  intro N
  induction N with
  | zero =>
    intro dl ks len hd sk ka
    have h1 : dl = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1 h2
    refine ⟨[], by rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]; rfl, hd, by simp, fun s => ?_⟩
    simp [mapLookup]
  | succ N ih =>
  intro dl ks len hd sk ka
  cases ks with
  | nil =>
    refine ⟨dl, ?_, hd, fun e he => Or.inl (List.mem_map.mpr ⟨e, he, rfl⟩), fun s => ⟨by simp, ?_⟩⟩
    · rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]; cases dl <;> rfl
    · intro U' h x; simp [h]
  | cons k ks =>
  have sk' := sak_cons.1 sk
  obtain ⟨s2, rfl⟩ := ka k (by simp)
  have ka' : ∀ k ∈ ks, ∃ s, k = .atom s := fun k hk => ka k (by simp [hk])
  have mem2 : ∀ s, (Term.atom s ∈ Term.atom s2 :: ks) ↔ (s = s2 ∨ Term.atom s ∈ ks) := by simp
  cases dl with
  | nil =>
    obtain ⟨dl', run, hd', keys, sem⟩ := ih [] ks (by simp at len ⊢; omega) hd sk'.2 ka'
    refine ⟨(.atom s2, v) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
      simp only [fieldsTerm, List.map_nil] at run ⊢
      simp [run]
    · rcases keys y hy with h | h
      · simp at h
      · exact sk'.1 _ h
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨⟨s2, rfl⟩, hv⟩
      · exact hd'.2 e he
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inr (by simp)
      · rcases keys e he with h | h
        · simp at h
        · exact Or.inr (by simp [h])
    · rw [lookup_cons_atom, mem2]
      by_cases e : s2 = s
      · subst e
        simp only [ite_true, Option.isNone_some, Bool.false_eq_true, true_or, not_true_eq_false, and_false,
          Option.some.injEq]
        refine ⟨trivial, fun U' h x => ?_⟩
        subst h; simp [mapLookup]
      · have ne : ¬s = s2 := fun h => e h.symm
        simp only [e, ite_false, ne, false_or]
        exact sem s
  | cons x dl =>
  obtain ⟨k1, v1⟩ := x
  have sd' := skl_cons.1 hd.1
  obtain ⟨⟨s1, hs1⟩, hv1⟩ := hd.2 (k1, v1) (by simp)
  simp only at hs1 hv1
  subst hs1
  have hdt : DomL t n dl := ⟨sd'.2, fun e he => hd.2 e (by simp [he])⟩
  -- keys of the tail are above the first key
  have tail_gt : ∀ e ∈ dl, Term.compare (Term.fuel (.atom s1) e.1) (.atom s1) e.1 = .lt := sd'.1
  rw [Elixir.Module.Types.Descr.«map_put_domain/4».eq_def]
  simp only [fieldsTerm_cons, USort.lt_ok, exact_ok, USort.g_if]
  by_cases l : (Term.compare (Term.fuel (.atom s1) (.atom s2)) (.atom s1) (.atom s2)).isLT = Bool.true
  · simp only [l, ↓reduceIte]
    have l' := USort.islt_lt l
    obtain ⟨dl', run, hd', keys, sem⟩ := ih dl (.atom s2 :: ks) (by simp at len ⊢; omega) hdt sk ka
    refine ⟨(.atom s1, v1) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
    · simp [run, fieldsTerm_cons]
    · rcases keys y hy with h | h
      · obtain ⟨e, he, hey⟩ := List.mem_map.mp h; rw [← hey]; exact tail_gt e he
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · rw [h]; exact l'
        · exact USort.c_lt_trans l' (sk'.1 _ h)
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨⟨s1, rfl⟩, hv1⟩
      · exact hd'.2 e he
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl (by simp)
      · rcases keys e he with h | h
        · exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)
        · exact Or.inr h
    · rw [lookup_cons_atom, lookup_cons_atom]
      by_cases e : s1 = s
      · subst e
        have nk : Term.atom s1 ∉ Term.atom s2 :: ks := by
          intro h; simp only [List.mem_cons] at h
          rcases h with h | h
          · rw [h] at l'; simp at l'
          · have := USort.c_lt_trans l' (sk'.1 _ h); simp at this
        simp only [ite_true, Option.isNone_some, Bool.false_eq_true, false_and, Option.some.injEq]
        refine ⟨trivial, fun U' h x => ?_⟩
        subst h; simp [nk]
      · simp only [e, ite_false]
        exact sem s
  simp only [l, Bool.false_eq_true, ↓reduceIte]
  by_cases q : compareExact (fuel (.atom s2) (.atom s1)) (.atom s2) (.atom s1) = .eq
  · simp only [q, ↓reduceIte]
    have e21 : s1 = s2 := by have := (atom_compareExact_eq _ _).mp q; simp at this; exact this
    subst e21
    obtain ⟨c, hc, rc, sc, -⟩ := (level t n).ef.union hv1 hv
    obtain ⟨dl', run, hd', keys, sem⟩ := ih dl ks (by simp at len ⊢; omega) hdt sk'.2 ka'
    refine ⟨(.atom s1, c) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
    · simp [rc m hm, run, fieldsTerm_cons]
    · rcases keys y hy with h | h
      · obtain ⟨e, he, hey⟩ := List.mem_map.mp h; rw [← hey]; exact tail_gt e he
      · exact sk'.1 _ h
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨⟨s1, rfl⟩, hc⟩
      · exact hd'.2 e he
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl (by simp)
      · rcases keys e he with h | h
        · exact Or.inl (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)
        · exact Or.inr (by simp [h])
    · rw [lookup_cons_atom, lookup_cons_atom, mem2]
      by_cases e : s1 = s
      · subst e
        simp only [ite_true, Option.isNone_some, Bool.false_eq_true, false_and, Option.some.injEq]
        refine ⟨trivial, fun U' h x => ?_⟩
        subst h; simp [sc x]
      · have ne : ¬s = s1 := fun h => e h.symm
        simp only [e, ite_false, ne, false_or]
        exact sem s
  simp only [q, ↓reduceIte]
  have l2 : Term.compare (Term.fuel (.atom s2) (.atom s1)) (.atom s2) (.atom s1) = .lt := by
    have nl := USort.not_islt' l
    have ne : ¬Term.compare (Term.fuel (.atom s1) (.atom s2)) (.atom s1) (.atom s2) = .eq := by
      intro c; simp at c; subst c; simp at q
    exact USort.gt_of_ne nl ne
  obtain ⟨dl', run, hd', keys, sem⟩ := ih ((.atom s1, v1) :: dl) ks (by simp at len ⊢; omega) hd sk'.2 ka'
  have none2 : mapLookup ((.atom s1, v1) :: dl) (.atom s2) = none := by
    apply lookup_none_of
    intro e he c
    rw [atom_compareExact_eq] at c
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp only at c; rw [c] at l2; simp at l2
    · have := USort.c_lt_trans l2 (tail_gt e he); rw [c] at this; simp at this
  refine ⟨(.atom s2, v) :: dl', ?_, ⟨skl_cons.2 ⟨fun y hy => ?_, hd'.1⟩, ?_⟩, ?_, fun s => ?_⟩
  · simp only [fieldsTerm_cons] at run
    rw [show (Term.tuple ⟨[.atom s1, v1]⟩).cons (fieldsTerm dl) = fieldsTerm ((.atom s1, v1) :: dl) from rfl]
    simp [run, fieldsTerm_cons]
  · rcases keys y hy with h | h
    · obtain ⟨e, he, hey⟩ := List.mem_map.mp h
      rw [← hey]
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact l2
      · exact USort.c_lt_trans l2 (tail_gt e he)
    · exact sk'.1 _ h
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨⟨s2, rfl⟩, hv⟩
    · exact hd'.2 e he
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact Or.inr (by simp)
    · rcases keys e he with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
  · rw [lookup_cons_atom, mem2]
    by_cases e : s2 = s
    · subst e
      simp only [ite_true, Option.isNone_some, Bool.false_eq_true, true_or, not_true_eq_false, and_false,
        Option.some.injEq, none2]
      refine ⟨trivial, fun U' h x => ?_⟩
      subst h; simp
    · have ne : ¬s = s2 := fun h => e h.symm
      simp only [e, ite_false, ne, false_or]
      exact sem s


end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem pairs_domain_list (m : Nat) (ks : List Term) {v : Term} (hv : Static v) (acc : Term) :
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[Term.list ks, v]) acc =
      Elixir.Module.Types.Descr.«map_descr_domain/3» (D m) (Term.list ks) v acc := by
  cases ks <;> rcases hv with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩ <;>
    simp [Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_list/1», Term.list]

theorem pairs_field (m : Nat) (a : String) (v : Term) (o : Bool) (acc : Term) :
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[.atom a, .tuple #[v, boolAtom o]]) acc =
      Elixir.Module.Types.Descr.«map_descr_pair/4» (.atom a) v (boolAtom o) acc := by
  cases o <;> simp [Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_atom/1»,
    Erlang.erlang.«is_boolean/1», boolAtom]

/-- The state of the fold over the pairs of a map constructor: the field pairs, newest first, and the domains. -/
def accT (F : List Term) (dl : List (Term × Term)) (b : Bool) : Term :=
  .tuple #[Term.list F, fieldsTerm dl, Term.list F, fieldsTerm dl, .atom "false", boolAtom b]

theorem em' (p : Prop) : ¬p ∨ p := (Classical.em p).symm

theorem step_field (m : Nat) (a : String) {v : Term} (hv : Static v) (o : Bool) (F : List Term)
    (dl : List (Term × Term)) (b : Bool) : ∃ b' : Bool,
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[.atom a, .tuple #[v, boolAtom o]])
      (accT F dl b) = .ok (accT (.tuple #[.atom a, .tuple #[v, boolAtom o]] :: F) dl b') := by
  rw [pairs_field]
  cases b <;> cases o <;>
    simp [Elixir.Module.Types.Descr.«map_descr_pair/4», accT, split_static hv, boolAtom, Lynx.Except.orElse,
      Erlang.erlang.«==/2»] <;>
    first
    | exact ⟨Bool.false, rfl⟩
    | exact ⟨Bool.true, rfl⟩
    | exact em' _
    | (split <;> first | exact ⟨Bool.true, rfl⟩ | exact ⟨Bool.false, rfl⟩)

theorem lk_spec {κ : Term → Term} {s z : Term} {A : List Term} (h : USort.lk κ s A = some z) :
    z ∈ A ∧ Term.compare (Term.fuel (κ z) s) (κ z) s = .eq := by
  induction A with
  | nil => simp at h
  | cons y ys ih =>
    by_cases e : Term.compare (Term.fuel (κ y) s) (κ y) s = .eq
    · simp [USort.lk_cons, e] at h; subst h; simp [e]
    · simp [USort.lk_cons, e] at h; have := ih h; exact ⟨by simp [this.1], this.2⟩

theorem atom_kdu (s : String) : USort.KdU (.atom s) := by
  intro a b e
  have := (Term.compare_eq_atom _ _).mp (USort.c_eq_symm e)
  cases this

/-- `lists:usort/1` of atoms sorts them strictly, keeping the same atoms. -/
theorem usort_atoms (ks : List Term) (ha : ∀ k ∈ ks, ∃ s, k = .atom s) :
    ∃ R, Erlang.lists.«usort/1» (Term.list ks) = .ok (Term.list R) ∧ SAK R ∧ ∀ k, k ∈ R ↔ k ∈ ks := by
  obtain ⟨R, run, sr, er⟩ := USort.usort_spec ks (fun x hx => by obtain ⟨s, rfl⟩ := ha x hx; exact atom_kdu s)
  refine ⟨R, run, sr, fun k => ⟨fun hk => USort.mem_of_eqv sr.ne er hk, fun hk => ?_⟩⟩
  obtain ⟨s, rfl⟩ := ha k hk
  obtain ⟨z, hz⟩ := USort.lk_some (κ := fun x => x) hk (Term.compare_self _)
  have hz' : USort.lk (fun x => x) (.atom s) R = some z := (er _).trans hz
  obtain ⟨mz, ez⟩ := lk_spec hz'
  have := (Term.compare_eq_atom _ _).mp ez
  subst this
  exact mz

section
variable {t : Term} {n : Nat}

theorem is_list_list (ks : List Term) : Erlang.erlang.«is_list/1» (Term.list ks) = .ok (.atom "true") := by
  cases ks <;> rfl

/-- A domain pair joins its value into the domains at its kinds. -/
theorem step_domain {m : Nat} (hm : (level t n).K ≤ m) (ks : List Term) (hks : ∀ k ∈ ks, ∃ s, k = .atom s)
    {v : Term} (hv : (level t n).E v) (F : List Term) (dl : List (Term × Term)) (hd : DomL t n dl) (b : Bool) :
    ∃ dl', Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[Term.list ks, v]) (accT F dl b) =
      .ok (accT F dl' b) ∧ DomL t n dl' ∧ (∀ e ∈ dl', e.1 ∈ dl.map Prod.fst ∨ e.1 ∈ ks) ∧
      ∀ s, ((mapLookup dl' (.atom s)).isNone ↔ (mapLookup dl (.atom s)).isNone ∧ Term.atom s ∉ ks) ∧
        ∀ U', mapLookup dl' (.atom s) = some U' → ∀ x, (level t n).den U' x ↔
          ((∃ U, mapLookup dl (.atom s) = some U ∧ (level t n).den U x) ∨ (Term.atom s ∈ ks ∧ (level t n).den v x)) := by
  have sv := (level t n).ef.static hv
  obtain ⟨R, ru, sr, mr⟩ := usort_atoms ks hks
  obtain ⟨dl', run, hd', keys, sem⟩ := mpd_run hm hv (dl.length + R.length) dl R (Nat.le_refl _) hd sr
    (fun k hk => hks k ((mr k).mp hk))
  refine ⟨dl', ?_, hd', fun e he => ?_, fun s => ?_⟩
  · rw [pairs_domain_list m ks sv]
    simp [Elixir.Module.Types.Descr.«map_descr_domain/3», accT, split_static sv,
      Elixir.Module.Types.Descr.«map_put_domain/3», is_list_list, ru, run, Lynx.Except.orElse]
  · rcases keys e he with h | h
    · exact Or.inl h
    · exact Or.inr ((mr _).mp h)
  · have := sem s
    simp only [mr] at this
    exact this

end

/-- The key of a pair of a map constructor. -/
def fk (x : Term) : Term :=
  match x with
  | .tuple es => es[0]?.getD .nil
  | _ => .nil

/-- Field pairs, with an atom key. -/
def isF (p : Term) : Bool :=
  match fk p with
  | .atom _ => Bool.true
  | _ => Bool.false

/-- The field pairs of a list of pairs, newest first. -/
def fieldsRev (P : List Term) : List Term := (P.filter isF).reverse

/-- Some domain pair names a kind. -/
def DomAny (P : List Term) (s : String) : Prop := ∃ ks v, Term.tuple #[Term.list ks, v] ∈ P ∧ Term.atom s ∈ ks

section
variable {t : Term} {n : Nat}

/-- Pairs of map constructors of a level: fields of atom keys and domains of kinds. -/
def CPair (t : Term) (n : Nat) (p : Term) : Prop :=
  (∃ (a : String) (v : Term) (o : Bool), p = .tuple #[.atom a, .tuple #[v, boolAtom o]] ∧ (level t n).E v) ∨
    ∃ ks v, p = .tuple #[Term.list ks, v] ∧ (∀ k ∈ ks, ∃ s ∈ domainKinds, k = .atom s) ∧ (level t n).E v

/-- A value of the types that some domain pair gives a kind. -/
def DomMem (P : List Term) (s : String) (x : (level t n).V) : Prop :=
  ∃ ks v, Term.tuple #[Term.list ks, v] ∈ P ∧ Term.atom s ∈ ks ∧ (level t n).den v x

/-- Domains holding, at each kind, the union of the types of the pairs naming it. -/
def DomSem (t : Term) (n : Nat) (P : List Term) (dl : List (Term × Term)) : Prop :=
  (∀ e ∈ dl, ∃ s ∈ domainKinds, e.1 = .atom s) ∧
  ∀ s, ((mapLookup dl (.atom s)).isNone ↔ ¬DomAny P s) ∧
    ∀ U, mapLookup dl (.atom s) = some U → ∀ x, (level t n).den U x ↔ DomMem (t := t) (n := n) P s x

theorem isF_field (a : String) (f : Term) : isF (.tuple #[.atom a, f]) = Bool.true := rfl

theorem isF_dom (ks : List Term) (v : Term) : isF (.tuple #[Term.list ks, v]) = Bool.false := by
  cases ks <;> rfl

theorem dom_tuple_inj {ks ks' : List Term} {v v' : Term}
    (h : Term.tuple #[Term.list ks', v'] = .tuple #[Term.list ks, v]) : ks' = ks ∧ v' = v := by
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun a : Array Term => a[0]?) h
  have e₁ := congrArg (fun a : Array Term => a[1]?) h
  simp at e₀ e₁
  exact ⟨list_inj e₀, e₁⟩

theorem field_ne_dom (a : String) (f : Term) (ks : List Term) (v : Term) :
    Term.tuple #[.atom a, f] ≠ .tuple #[Term.list ks, v] := by
  intro h
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun a : Array Term => a[0]?) h
  simp at e₀
  cases ks <;> simp [Term.list] at e₀

theorem fold_pairs {m : Nat} (hm : (level t n).K ≤ m) : ∀ (rest P : List Term), (∀ p ∈ rest, CPair t n p) →
    ∀ (dl : List (Term × Term)) (b : Bool), DomL t n dl → DomSem t n P dl →
    ∃ dl' b', Erlang.lists.«foldl_1/3» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-map_descr_pairs/1-fun-0-" 2 #[])
        (accT (fieldsRev P) dl b) (Term.list rest) = .ok (accT (fieldsRev (P ++ rest)) dl' b') ∧
      DomL t n dl' ∧ DomSem t n (P ++ rest) dl'
  | [], P, _, dl, b, hd, hs => ⟨dl, b, by simp [Erlang.lists.«foldl_1/3»], hd, by simpa using hs⟩
  | p :: rest, P, hr, dl, b, hd, hs => by
    rcases hr p (by simp) with ⟨a, v, o, rfl, hv⟩ | ⟨ks, v, rfl, hks, hv⟩
    · obtain ⟨b', st⟩ := step_field m a ((level t n).ef.static hv) o (fieldsRev P) dl b
      have e : fieldsRev (P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]]) =
          .tuple #[.atom a, .tuple #[v, boolAtom o]] :: fieldsRev P := by
        unfold fieldsRev
        rw [List.filter_append, List.filter_cons, isF_field]
        simp
      have hs' : DomSem t n (P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]]) dl := by
        refine ⟨hs.1, fun s => ?_⟩
        have nd : ∀ ks' v', Term.tuple #[Term.list ks', v'] ∈ P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]] ↔
            Term.tuple #[Term.list ks', v'] ∈ P := by
          intro ks' v'
          simp only [List.mem_append, List.mem_singleton, or_iff_left_iff_imp]
          intro h; exact absurd h.symm (field_ne_dom a _ ks' v')
        simp only [DomAny, DomMem, nd]
        exact hs.2 s
      obtain ⟨dl', b'', run, hd', hs''⟩ := fold_pairs hm rest _ (fun q hq => hr q (by simp [hq])) dl b' hd hs'
      refine ⟨dl', b'', ?_, hd', by simpa using hs''⟩
      rw [Term.list_cons, Erlang.lists.«foldl_1/3».eq_def]
      simp only [D, Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure]
      simp only [st, Lynx.Except.ok_bind]
      rw [← e]
      simpa using run
    · have hks' : ∀ k ∈ ks, ∃ s, k = .atom s := fun k hk => by obtain ⟨s, -, rfl⟩ := hks k hk; exact ⟨s, rfl⟩
      obtain ⟨dl', st, hd', keys, sem⟩ := step_domain hm ks hks' hv (fieldsRev P) dl hd b
      have e : fieldsRev (P ++ [Term.tuple #[Term.list ks, v]]) = fieldsRev P := by
        simp [fieldsRev, isF_dom]
      have hs' : DomSem t n (P ++ [Term.tuple #[Term.list ks, v]]) dl' := by
        refine ⟨fun e he => ?_, fun s => ⟨?_, fun U' hU' x => ?_⟩⟩
        · rcases keys e he with h | h
          · obtain ⟨e', he', hee⟩ := List.mem_map.mp h; rw [← hee]; exact hs.1 e' he'
          · obtain ⟨s, ms, hs⟩ := hks _ h; exact ⟨s, ms, hs⟩
        · rw [(sem s).1, (hs.2 s).1]
          simp only [DomAny, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩ ⟨ks', v', h3 | h3, h4⟩
            · exact h1 ⟨ks', v', h3, h4⟩
            · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h3; exact h2 h4
          · intro h
            exact ⟨fun ⟨ks', v', h3, h4⟩ => h ⟨ks', v', Or.inl h3, h4⟩, fun h4 => h ⟨ks, v, Or.inr rfl, h4⟩⟩
        · rw [(sem s).2 U' hU' x]
          simp only [DomMem, List.mem_append, List.mem_singleton]
          constructor
          · rintro (⟨U, hU, hx⟩ | ⟨h4, hx⟩)
            · obtain ⟨ks', v', h3, h4, h5⟩ := ((hs.2 s).2 U hU x).mp hx
              exact ⟨ks', v', Or.inl h3, h4, h5⟩
            · exact ⟨ks, v, Or.inr rfl, h4, hx⟩
          · rintro ⟨ks', v', h3 | h3, h4, h5⟩
            · left
              cases hl : mapLookup dl (.atom s) with
              | none =>
                exact absurd ⟨ks', v', h3, h4⟩ (((hs.2 s).1).mp (by simp [hl]))
              | some U => exact ⟨U, rfl, ((hs.2 s).2 U hl x).mpr ⟨ks', v', h3, h4, h5⟩⟩
            · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h3; exact Or.inr ⟨h4, h5⟩
      obtain ⟨dl'', b'', run, hd'', hs''⟩ := fold_pairs hm rest _ (fun q hq => hr q (by simp [hq])) dl' b hd' hs'
      refine ⟨dl'', b'', ?_, hd'', by simpa using hs''⟩
      rw [Term.list_cons, Erlang.lists.«foldl_1/3».eq_def]
      simp only [D, Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure]
      simp only [st, Lynx.Except.ok_bind]
      rw [← e]
      simpa using run

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem foldl_first (m : Nat) (f acc : Term) (fs : List Term) (hf : f = .function false "Elixir.Module.Types.Descr" "-map_descr_pairs/1-fun-0-" 2 #[]) :
    Erlang.lists.«foldl/3» (D m) f acc (Term.list fs) = Erlang.lists.«foldl_1/3» (D m) f acc (Term.list fs) := by
  subst hf
  cases fs with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»]
  | cons p rest =>
    rw [Term.list_cons, Erlang.lists.«foldl_1/3».eq_def]
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]

theorem kdk_field (a : String) (f : Term) : USort.KdK (.integer 1) fk (.tuple #[.atom a, f]) := by
  refine ⟨by simp [Erlang.erlang.«element/2», fk], fun x y e => ?_⟩
  have := (Term.compare_eq_atom _ _).mp (USort.c_eq_symm (show Term.compare (Term.fuel (.atom a) (.cons x y)) (.atom a) (.cons x y) = .eq from e))
  cases this

section
variable {t : Term} {n : Nat}

theorem fieldsRev_mem {fs : List Term} (h : ∀ p ∈ fs, CPair t n p) {x : Term} (hx : x ∈ fieldsRev fs) :
    ∃ (a : String) (v : Term) (o : Bool), x = .tuple #[.atom a, .tuple #[v, boolAtom o]] ∧ (level t n).E v := by
  simp only [fieldsRev, List.mem_reverse, List.mem_filter] at hx
  rcases h x hx.1 with h | ⟨ks, v, rfl, -, -⟩
  · exact h
  · simp [isF_dom] at hx

/-- `map_descr_pairs/1` of static pairs: the fields sorted by key, the last pair of each key first, and the
domains. -/
theorem descr_pairs_run {m : Nat} (hm : (level t n).K ≤ m) (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ R dl b, Elixir.Module.Types.Descr.«map_descr_pairs/1» (D (m + 1)) (Term.list fs) =
      .ok (.tuple #[Term.list R, fieldsTerm dl, Term.list R, fieldsTerm dl, .atom "false", boolAtom b]) ∧
      USort.SA fk R ∧ USort.Eqv fk R (fieldsRev fs) ∧ DomL t n dl ∧ DomSem t n fs dl := by
  obtain ⟨dl, b, run, hd, hs⟩ := fold_pairs hm fs [] h [] Bool.false ⟨by simp [SKL], by simp⟩
    ⟨by simp, fun s => ⟨by simp [mapLookup, DomAny], by simp [mapLookup]⟩⟩
  obtain ⟨R, rk, sr, er⟩ := USort.ukeysort_spec (κ := fk) 1 (by decide) (fieldsRev fs) (fun x hx => by
    obtain ⟨a, v, o, rfl, -⟩ := fieldsRev_mem h hx; exact kdk_field a _)
  refine ⟨R, dl, b, ?_, sr, er, hd, by simpa using hs⟩
  have init : Term.tuple #[.nil, .nil, .nil, .nil, .atom "false", .atom "false"] = accT (fieldsRev []) [] Bool.false := rfl
  simp only [List.nil_append] at run
  unfold Elixir.Module.Types.Descr.«map_descr_pairs/1»
  simp only [Lynx.Except.pure_eq_ok, Lynx.Except.ok_bind]
  rw [foldl_first _ _ _ _ rfl, init, run]
  simp only [accT, Lynx.Except.ok_bind, rk]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- The value of a pair of a map constructor. -/
def fv (x : Term) : Term :=
  match x with
  | .tuple es => es[1]?.getD .nil
  | _ => .nil

/-- The fields of sorted field pairs. -/
def toL (R : List Term) : List (Term × Term) := R.map fun x => (fk x, fv x)

theorem list_toL : ∀ (R : List Term), (∀ x ∈ R, ∃ (a : String) (f : Term), x = .tuple #[.atom a, f]) →
    Term.list R = fieldsTerm (toL R)
  | [], _ => rfl
  | x :: R, h => by
    obtain ⟨a, f, rfl⟩ := h x (by simp)
    have := list_toL R (fun y hy => h y (by simp [hy]))
    simp only [toL, List.map_cons, fieldsTerm_cons] at this ⊢
    rw [Term.list_cons, this]; rfl

theorem lookup_toL (s : String) : ∀ (R : List Term), (∀ x ∈ R, ∃ (a : String) (f : Term), x = .tuple #[.atom a, f]) →
    mapLookup (toL R) (.atom s) = (USort.lk fk (.atom s) R).map fv
  | [], _ => rfl
  | x :: R, h => by
    obtain ⟨a, f, rfl⟩ := h x (by simp)
    have ih := lookup_toL s R (fun y hy => h y (by simp [hy]))
    simp only [toL, List.map_cons] at ih ⊢
    rw [show fk (.tuple #[.atom a, f]) = .atom a from rfl, lookup_cons_atom, USort.lk_cons,
      show fk (.tuple #[.atom a, f]) = .atom a from rfl]
    by_cases e : a = s
    · subst e; simp
    · have ne : ¬Term.compare (Term.fuel (.atom a) (.atom s)) (.atom a) (.atom s) = .eq := by simpa using e
      simp only [e, ne, ite_false]
      exact ih

theorem static_closed (m : Nat) (x rest F : Term) :
    Elixir.Module.Types.Descr.«map_descr_static/3» (D m) (.atom "closed") F (.cons x rest) =
      (do let l ← Elixir.Module.Types.Descr.«map_new/2» (.cons x rest) F; pure (.map [(.atom "map", l)])) := by
  unfold Elixir.Module.Types.Descr.«map_descr_static/3»
  split <;> simp_all

theorem lookup_keys (f : Term → Term) (s : String) : ∀ (K : List Term), Term.atom s ∈ K →
    mapLookup (K.map fun k => (k, f k)) (.atom s) = some (f (.atom s))
  | [], h => by simp at h
  | k :: K, h => by
    by_cases e : compareExact (fuel (.atom s) k) (.atom s) k = .eq
    · rw [atom_compareExact_eq] at e; subst e; simp [mapLookup]
    · have h' : Term.atom s ∈ K := by
        rcases List.mem_cons.mp h with h | h
        · subst h; simp at e
        · exact h
      simp only [List.map_cons]
      rw [lookup_cons_ne e]
      exact lookup_keys f s K h'

/-- The domain kinds as atoms, in order. -/
theorem sak_kinds : SAK (domainKinds.map Term.atom) := by
  simp (config := { decide := true }) [SAK]

section
variable {t : Term} {n : Nat}

/-- The values a constructed map allows at the keys of a kind: those of the domain pairs naming it, or any value
for open maps and none for closed ones. -/
def CKind (tag : String) (fs : List Term) (s : String) (o : Option (level t n).V) : Prop :=
  o = none ∨ ∃ x, o = some x ∧
    ((DomAny fs s ∧ DomMem (t := t) (n := n) fs s x) ∨ (¬DomAny fs s ∧ tag = "open"))

/-- The values a constructed map allows at an atom key: those of the last field of the key, or of the atom
domain. -/
def CAtom (tag : String) (fs : List Term) (s : String) (o : Option (level t n).V) : Prop :=
  match USort.lk fk (.atom s) (fieldsRev fs) with
  | some x => FieldSem (level t n).den (fv x) o
  | none => CKind tag fs "atom" o

/-- The maps of a map constructor. -/
def CSem (tag : String) (fs : List Term) (w : MW (level t n).V) : Prop :=
  (∀ s, CAtom tag fs s (w (.atom s))) ∧ ∀ k i, CKind tag fs (domKind k) (w (.dom k i))

theorem domL_kinds {dl : List (Term × Term)} (hd : DomL t n dl) (hk : ∀ e ∈ dl, ∃ s ∈ domainKinds, e.1 = .atom s) :
    DomsV (level t n).E dl :=
  ⟨fun e he => ⟨by obtain ⟨s, ms, h⟩ := hk e he; exact ⟨s, h, ms⟩, (hd.2 e he).2⟩, hd.1⟩

/-- `map_descr/2` of static pairs is a map literal of the sorted last fields, under a tag of the domains. -/
theorem descr_leaf {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ (k : Int) (TAG : Term) (l : List (Term × Term)),
      Elixir.Module.Types.Descr.«map_descr/2» (D (m + 1)) (.atom tag) (Term.list fs) =
        .ok (.map [(.atom "map", .tuple #[.integer k, TAG, fieldsTerm l])]) ∧
      TagV (level t n).E TAG ∧ FieldsV (level t n).E l ∧ KeyOk (.tuple #[.integer k, TAG, fieldsTerm l]) ∧
      (∀ s, mapLookup l (.atom s) = (USort.lk fk (.atom s) (fieldsRev fs)).map fv) ∧
      ∀ kind ∈ domainKinds, ∀ o, TagSem (level t n).den TAG kind o ↔ CKind (t := t) (n := n) tag fs kind o := by
  obtain ⟨R, dl, b, rp, sr, er, hd, hs⟩ := descr_pairs_run hm fs h
  have memR : ∀ x ∈ R, ∃ (a : String) (v : Term) (o : Bool), x = .tuple #[.atom a, .tuple #[v, boolAtom o]] ∧
      (level t n).E v := fun x hx => fieldsRev_mem h (USort.mem_of_eqv sr.ne er hx)
  have shape : ∀ x ∈ R, ∃ (a : String) (f : Term), x = .tuple #[.atom a, f] := fun x hx => by
    obtain ⟨a, v, o, rfl, -⟩ := memR x hx; exact ⟨a, _, rfl⟩
  have lR := list_toL R shape
  have sl : FieldsV (level t n).E (toL R) := by
    refine ⟨fun e he => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      obtain ⟨a, v, o, rfl, hv⟩ := memR x hx
      exact ⟨⟨a, rfl⟩, ⟨v, o, rfl, hv⟩⟩
    · simp only [toL, List.pairwise_map]; exact sr
  have look : ∀ s, mapLookup (toL R) (.atom s) = (USort.lk fk (.atom s) (fieldsRev fs)).map fv := fun s => by
    rw [lookup_toL s R shape, er]
  have hnone : ∀ x, ¬(level t n).den (.map []) x := (level t n).ef.den_none
  unfold Elixir.Module.Types.Descr.«map_descr/2»
  simp only [rp, Lynx.Except.ok_bind]
  have hk : ∀ e ∈ dl, ∃ s ∈ domainKinds, e.1 = .atom s := hs.1
  cases dl with
  | nil =>
    have g : TagV (level t n).E (.atom tag) := by rcases ht with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)
    obtain ⟨k, rl, key⟩ := leaf_new_keyM g R
    rw [lR] at key
    have noAny : ∀ s, ¬DomAny fs s := fun s => ((hs.2 s).1).mp (by simp [mapLookup])
    refine ⟨k, .atom tag, toL R, ?_, g, sl, key, look, fun kind _ o => ?_⟩
    · rw [← lR]
      simp [Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2», rl,
        show fieldsTerm [] = .nil from rfl]
    · rw [tagSem_atom]
      cases o with
      | none => simp [CKind]
      | some x => simp [CKind, noAny]
  | cons d dl =>
  rcases ht with rfl | rfl
  · -- open maps fill the other kinds with `term()`
    have hK : ∀ e ∈ d :: dl, e.1 ∈ domainKinds.map Term.atom := fun e he => by
      obtain ⟨s, ms, h⟩ := hk e he; rw [h]; exact List.mem_map.mpr ⟨s, ms, rfl⟩
    have fp := fpa_run (m + 1) (.atom "term") (domainKinds.map Term.atom) (d :: dl) sak_kinds
      (fun k hk => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp hk; exact ⟨s, rfl⟩) hd.1 hK
    generalize hL : (domainKinds.map Term.atom).map (fun k => (k, (mapLookup (d :: dl) k).getD (.atom "term"))) = L
      at fp
    have lookL : ∀ kind ∈ domainKinds, mapLookup L (.atom kind) =
        some ((mapLookup (d :: dl) (.atom kind)).getD (.atom "term")) := fun kind mk => by
      rw [← hL]; exact lookup_keys _ kind _ (List.mem_map.mpr ⟨kind, mk, rfl⟩)
    have g : TagV (level t n).E (fieldsTerm L) := by
      refine Or.inr (Or.inr ⟨L, rfl, fun e he => ?_, ?_⟩)
      · rw [← hL] at he
        obtain ⟨k, hk', rfl⟩ := List.mem_map.mp he
        obtain ⟨s, ms, rfl⟩ := List.mem_map.mp hk'
        refine ⟨⟨s, rfl, ms⟩, ?_⟩
        cases hl : mapLookup (d :: dl) (.atom s) with
        | none => exact (level t n).ef.term
        | some U =>
          obtain ⟨e', he', rfl⟩ := lookup_mem hl
          exact (hd.2 e' he').2
      · rw [← hL, List.pairwise_map]; exact sak_kinds
    obtain ⟨k, rl, key⟩ := leaf_new_keyM g R
    rw [lR] at key
    refine ⟨k, fieldsTerm L, toL R, ?_, g, sl, key, look, fun kind mk o => ?_⟩
    · rw [← lR]
      have kl : Term.list [.atom "atom", .atom "binary", .atom "bitstring_no_binary", .atom "float", .atom "fun",
          .atom "integer", .atom "list", .atom "map", .atom "pid", .atom "port", .atom "reference", .atom "tuple"] =
          Term.list (domainKinds.map Term.atom) := rfl
      simp only [Elixir.Module.Types.Descr.«map_descr_static/3», fieldsTerm_cons, kl]
      simp only [← fieldsTerm_cons, fp, Lynx.Except.ok_bind, Elixir.Module.Types.Descr.«map_new/2», rl]
      rfl
    · rw [tagSem_dom_iff hnone, lookL kind mk]
      have sk := hs.2 kind
      cases hl : mapLookup (d :: dl) (.atom kind) with
      | none =>
        have na : ¬DomAny fs kind := sk.1.mp (by simp [hl])
        cases o <;> simp [CKind, na, (level t n).ef.den_term]
      | some U =>
        have da : DomAny fs kind := Classical.byContradiction fun h => by have := sk.1.mpr h; simp [hl] at this
        cases o with
        | none => simp [CKind]
        | some x => simp [CKind, da, sk.2 U hl x]
  · have g : TagV (level t n).E (fieldsTerm (d :: dl)) := Or.inr (Or.inr ⟨_, rfl, domL_kinds hd hk⟩)
    obtain ⟨k, rl, key⟩ := leaf_new_keyM g R
    rw [lR] at key
    refine ⟨k, fieldsTerm (d :: dl), toL R, ?_, g, sl, key, look, fun kind mk o => ?_⟩
    · rw [← lR, fieldsTerm_cons, static_closed, ← fieldsTerm_cons]
      simp [Elixir.Module.Types.Descr.«map_new/2», rl]
    · rw [tagSem_dom_iff hnone]
      have sk := hs.2 kind
      cases hl : mapLookup (d :: dl) (.atom kind) with
      | none =>
        have na : ¬DomAny fs kind := sk.1.mp (by simp [hl])
        cases o <;> simp [CKind, na]
      | some U =>
        have da : DomAny fs kind := Classical.byContradiction fun h => by have := sk.1.mpr h; simp [hl] at this
        cases o with
        | none => simp [CKind]
        | some x => simp [CKind, da, sk.2 U hl x]

theorem mapsOf_congr {H : Term} {Q Q' : MW (level t n).V → Prop} (h : MapsOf t n H Q) (e : ∀ w, Q w ↔ Q' w) :
    MapsOf t n H Q' := ⟨h.1, h.2.1, fun p w hw => (h.2.2 p w hw).trans (e w)⟩

/-- The maps of `map_descr/2` of static pairs. -/
theorem descr_maps {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ C, Elixir.Module.Types.Descr.«map_descr/2» (D (m + 1)) (.atom tag) (Term.list fs) = .ok C ∧
      MapsOf t n C (CSem (t := t) (n := n) tag fs) := by
  obtain ⟨k, TAG, l, run, g, sl, key, look, tags⟩ := descr_leaf hm tag ht fs h
  refine ⟨_, run, mapsOf_congr (mapsOf_one _ (mleaf_field g sl key)) fun w => ?_⟩
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', equalExact_eq_decide]
  rw [denMF_leaf (level t n).ef sl g]
  constructor
  · intro ms
    refine ⟨fun s => ?_, fun k i => (tags _ (domKind_mem k) _).mp (ms.doms k i)⟩
    have := ms.atoms s
    unfold FSem at this
    unfold CAtom
    rw [look] at this
    cases hx : USort.lk fk (.atom s) (fieldsRev fs) with
    | none => rw [hx] at this; exact (tags "atom" (by simp [domainKinds]) _).mp this
    | some x => rw [hx] at this; exact this
  · rintro ⟨ha, hd⟩
    refine ⟨fun s => ?_, fun k i => (tags _ (domKind_mem k) _).mpr (hd k i)⟩
    have := ha s
    unfold FSem
    unfold CAtom at this
    rw [look]
    cases hx : USort.lk fk (.atom s) (fieldsRev fs) with
    | none => rw [hx] at this; exact (tags "atom" (by simp [domainKinds]) _).mpr this
    | some x => rw [hx] at this; exact this

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem guard_true {g : Except Exception Term} {body next : Unit → Except Exception Term}
    (h : Lynx.Except.guard g body next = .ok (.atom "true")) :
    (g = .ok (.atom "true") ∧ body () = .ok (.atom "true")) ∨ next () = .ok (.atom "true") := by
  cases g with
  | error e =>
    simp only [Lynx.Except.guard_eq, Lynx.Except.tryWith] at h
    split at h <;> simp_all
  | ok v =>
    rw [Lynx.Except.guard_ok] at h
    split at h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr h

theorem is_atom_true {k : Term} (h : Erlang.erlang.«is_atom/1» k = .ok (.atom "true")) : ∃ s, k = .atom s := by
  cases k <;> simp [Erlang.erlang.«is_atom/1»] at h ⊢

theorem is_boolean_true {o : Term} (h : Erlang.erlang.«is_boolean/1» o = .ok (.atom "true")) :
    ∃ b, o = boolAtom b := by
  simp only [Erlang.erlang.«is_boolean/1»] at h
  split at h
  · exact ⟨Bool.true, rfl⟩
  · exact ⟨Bool.false, rfl⟩
  · simp at h

theorem cons_nil_false {a rest : Term} (h : Erlang.erlang.«==/2» (.cons a rest) .nil = .ok (.atom "true")) : False := by
  cases nil_of_eq h

/-- A pair checked by `map_pairs?/2`: a field of an atom key, or a domain of kinds, of static types. -/
def PairN (N a : Term) : Prop :=
  (∃ (s : String) (v : Term) (b : Bool), a = .tuple #[.atom s, .tuple #[v, boolAtom b]] ∧
    «arrows_static?/2» v N = .ok (.atom "true")) ∨
  ∃ ks v, a = .tuple #[Term.list ks, v] ∧ (∀ k ∈ ks, ∃ s ∈ domainKinds, k = .atom s) ∧
    «arrows_static?/2» v N = .ok (.atom "true")

theorem pair_step {a rest N : Term} (h : Elixir.STTDescrProofsTest.«map_pairs?/2» (.cons a rest) N = .ok (.atom "true")) :
    PairN N a ∧ Elixir.STTDescrProofsTest.«map_pairs?/2» rest N = .ok (.atom "true") := by
  rw [Elixir.STTDescrProofsTest.«map_pairs?/2».eq_def] at h
  simp only at h
  -- the domain clause, after the field clause fails
  have second : ∀ {kinds value : Term}, a = .tuple #[kinds, value] →
      Lynx.Except.guard (Erlang.erlang.«is_list/1» kinds)
        (fun _ => Lynx.Except.andAlso (Lynx.Except.andAlso (Elixir.STTDescrProofsTest.«kind_list?/1» kinds)
          («arrows_static?/2» value N) Bool.true) (Elixir.STTDescrProofsTest.«map_pairs?/2» rest N) Bool.true)
        (fun _ => Erlang.erlang.«==/2» (.cons a rest) .nil) = .ok (.atom "true") →
      PairN N a ∧ Elixir.STTDescrProofsTest.«map_pairs?/2» rest N = .ok (.atom "true") := by
    intro kinds value ha g
    rcases guard_true g with ⟨-, g⟩ | g
    · simp only [Lynx.Except.andAlso_eq_true] at g
      obtain ⟨ks, rfl, hks⟩ := kind_list_ok _ g.1.1
      exact ⟨Or.inr ⟨ks, value, ha, hks, g.1.2⟩, g.2⟩
    · exact (cons_nil_false g).elim
  split at h
  · rename_i k v o ps heq
    simp only [Term.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rcases guard_true h with ⟨g1, g2⟩ | h2
    · simp only [Lynx.Except.andAlso_eq_true] at g1 g2
      obtain ⟨s, rfl⟩ := is_atom_true g1.1
      obtain ⟨b, rfl⟩ := is_boolean_true g1.2
      exact ⟨Or.inl ⟨s, v, b, rfl, g2.1⟩, g2.2⟩
    · simp only at h2
      exact second rfl h2
  · split at h
    · rename_i kinds value ps heq
      simp only [Term.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact second rfl h
    · exact (cons_nil_false h).elim

section
variable {t : Term} {d : Nat}

/-- Pairs that `map_pairs?/2` accepts at a nesting are pairs of constructors one level up. -/
theorem map_pairs_ok : ∀ (P : Term), Elixir.STTDescrProofsTest.«map_pairs?/2» P (.tuple #[.integer d, t]) =
    .ok (.atom "true") → ∃ fs, P = Term.list fs ∧ ∀ p ∈ fs, CPair t (d + 1) p
  | .cons a rest, h => by
    obtain ⟨pa, hr⟩ := pair_step h
    obtain ⟨fs, rfl, hfs⟩ := map_pairs_ok rest hr
    refine ⟨a :: fs, rfl, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · rcases pa with ⟨s, v, b, rfl, hv⟩ | ⟨ks, v, rfl, hks, hv⟩
      · exact Or.inl ⟨s, v, b, rfl, Or.inl (arrows_static_ok hv)⟩
      · exact Or.inr ⟨ks, v, rfl, hks, Or.inl (arrows_static_ok hv)⟩
    · exact hfs p hp
  | .nil, _ => ⟨[], rfl, by simp⟩
  | .integer _, h | .float _, h | .atom _, h | .reference _, h | .function _ _ _ _ _, h | .pid _, h | .tuple _, h
  | .map _, h | .bitstring _ _ _, h => by
    rw [Elixir.STTDescrProofsTest.«map_pairs?/2».eq_def] at h
    cases nil_of_eq h

end

theorem kind_in_run (s : String) : ∀ ks : List Term, (∀ k ∈ ks, ∃ s', k = .atom s') →
    ∃ b : Bool, Elixir.STTDescrProofsTest.«kind_in?/2» (Term.list ks) (.atom s) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ Term.atom s ∈ ks)
  | [], _ => ⟨Bool.false, by simp [Elixir.STTDescrProofsTest.«kind_in?/2», boolAtom], by simp⟩
  | k :: ks, h => by
    obtain ⟨s', rfl⟩ := h k (by simp)
    obtain ⟨b, ih, hb⟩ := kind_in_run s ks (fun k hk => h k (by simp [hk]))
    rw [Term.list_cons, Elixir.STTDescrProofsTest.«kind_in?/2».eq_def]
    by_cases e : s' = s
    · subst e; exact ⟨Bool.true, by simp [Erlang.erlang.«==/2», boolAtom], by simp⟩
    · have ne : ¬Term.compare (Term.fuel (.atom s') (.atom s)) (.atom s') (.atom s) = .eq := by simpa using e
      refine ⟨b, by simp [Erlang.erlang.«==/2», ne, ih], ?_⟩
      rw [hb]
      simp only [List.mem_cons, Term.atom.injEq]
      exact ⟨Or.inr, fun h => h.resolve_left fun h' => e h'.symm⟩

/-- Elements of pair lists are pairs. -/
theorem keyfind_lk (k : Term) : ∀ L : List Term, (∀ x ∈ L, ∃ a b, x = .tuple #[a, b]) →
    Erlang.lists.«keyfind/3» k (.integer 1) (Term.list L) =
      .ok ((USort.lk fk k L).getD (.atom "false"))
  | [], _ => by simp [Erlang.lists.«keyfind/3»]
  | x :: L, h => by
    obtain ⟨a, b, rfl⟩ := h x (by simp)
    have ih := keyfind_lk k L (fun y hy => h y (by simp [hy]))
    rw [Term.list_cons]
    simp only [Erlang.lists.«keyfind/3», USort.lk_cons, show fk (.tuple #[a, b]) = a from rfl, equal_eq_decide]
    by_cases e : Term.compare (Term.fuel a k) a k = .eq
    · simp [e]
    · simp [e, ih]

section
variable {t : Term} {n : Nat}

/-- `domain_value/4` joins the values of the domain pairs naming a kind. -/
theorem dv_run {m : Nat} (hm : (level t n).K ≤ m) (s : String) : ∀ (rest P : List Term),
    (∀ p ∈ rest, CPair t n p) → ∀ (acc : Term) (found : Bool), (level t n).E acc → (found = Bool.true ↔ DomAny P s) →
    (found = Bool.true → ∀ x, (level t n).den acc x ↔ DomMem (t := t) (n := n) P s x) →
    ∃ U, Elixir.STTDescrProofsTest.«domain_value/4» (D m) (Term.list rest) (.atom s) acc (boolAtom found) = .ok U ∧
      (level t n).E U ∧ (DomAny (P ++ rest) s → ∀ x, (level t n).den U x ↔ DomMem (t := t) (n := n) (P ++ rest) s x) ∧
      (¬DomAny (P ++ rest) s → U = acc)
  | [], P, _, acc, found, he, hf, hd => ⟨acc, by simp [Elixir.STTDescrProofsTest.«domain_value/4»], he,
      fun a x => by simpa using hd (hf.mpr (by simpa using a)) x, fun _ => rfl⟩
  | p :: rest, P, hr, acc, found, he, hf, hd => by
    have hr' : ∀ q ∈ rest, CPair t n q := fun q hq => hr q (by simp [hq])
    have app : P ++ p :: rest = (P ++ [p]) ++ rest := by simp
    rcases hr p (by simp) with ⟨a, v, o, rfl, hv⟩ | ⟨ks, v, rfl, hks, hv⟩
    · -- fields are skipped
      have nd : ∀ ks' v', Term.tuple #[Term.list ks', v'] ∈ P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]] ↔
          Term.tuple #[Term.list ks', v'] ∈ P := by
        intro ks' v'
        simp only [List.mem_append, List.mem_singleton, or_iff_left_iff_imp]
        intro h; exact absurd h.symm (field_ne_dom a _ ks' v')
      obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]]) hr'
        acc found he
        (by simp only [DomAny, nd]; exact hf) (fun f x => by simp only [DomMem, nd]; exact hd f x)
      refine ⟨U, ?_, hU, by rw [app]; exact h1, by rw [app]; exact h2⟩
      rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
      simp [Erlang.erlang.«is_list/1», run]
    · have hks' : ∀ k ∈ ks, ∃ s', k = .atom s' := fun k hk => by
        obtain ⟨s', -, rfl⟩ := hks k hk; exact ⟨s', rfl⟩
      have ki := kind_in_run s ks hks'
      have anyP : ∀ s', DomAny (P ++ [Term.tuple #[Term.list ks, v]]) s' ↔ DomAny P s' ∨ Term.atom s' ∈ ks := by
        intro s'
        simp only [DomAny, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨ks', v', h1 | h1, h2⟩
          · exact Or.inl ⟨ks', v', h1, h2⟩
          · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h1; exact Or.inr h2
        · rintro (⟨ks', v', h1, h2⟩ | h2)
          · exact ⟨ks', v', Or.inl h1, h2⟩
          · exact ⟨ks, v, Or.inr rfl, h2⟩
      have memP : ∀ x, DomMem (t := t) (n := n) (P ++ [Term.tuple #[Term.list ks, v]]) s x ↔
          DomMem (t := t) (n := n) P s x ∨ (Term.atom s ∈ ks ∧ (level t n).den v x) := by
        intro x
        simp only [DomMem, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨ks', v', h1 | h1, h2, h3⟩
          · exact Or.inl ⟨ks', v', h1, h2, h3⟩
          · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h1; exact Or.inr ⟨h2, h3⟩
        · rintro (⟨ks', v', h1, h2, h3⟩ | ⟨h2, h3⟩)
          · exact ⟨ks', v', Or.inl h1, h2, h3⟩
          · exact ⟨ks, v, Or.inr rfl, h2, h3⟩
      obtain ⟨b, ki, hb⟩ := ki
      have nf : found = Bool.false → ¬DomAny P s := fun e h => by rw [e] at hf; simpa using hf.mpr h
      by_cases mem : Term.atom s ∈ ks
      · have bt : b = Bool.true := hb.mpr mem
        subst bt
        have anyAll : DomAny (P ++ Term.tuple #[Term.list ks, v] :: rest) s := ⟨ks, v, by simp, mem⟩
        cases found
        · obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[Term.list ks, v]]) hr' v Bool.true hv
            (by simp [anyP, mem]) (fun _ x => by
              rw [memP]
              have : ¬DomMem (t := t) (n := n) P s x := fun ⟨ks', v', h1, h2, _⟩ => nf rfl ⟨ks', v', h1, h2⟩
              simp [this, mem])
          refine ⟨U, ?_, hU, by rw [app]; exact h1, fun h => absurd anyAll h⟩
          rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
          simp only [boolAtom, ↓reduceIte] at run
          simp [is_list_list, ki, boolAtom, exact_ok, run]
        · obtain ⟨c, hc, rc, sc, -⟩ := (level t n).ef.union he hv
          obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[Term.list ks, v]]) hr' c Bool.true hc
            (by simp [anyP, mem]) (fun _ x => by rw [memP, sc x, hd rfl x]; simp [mem])
          refine ⟨U, ?_, hU, by rw [app]; exact h1, fun h => absurd anyAll h⟩
          rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
          simp only [boolAtom, ↓reduceIte] at run
          simp [is_list_list, ki, boolAtom, rc m hm, run]
      · have bf : b = Bool.false := by cases b <;> simp_all
        subst bf
        obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[Term.list ks, v]]) hr' acc found he
          (by rw [hf, anyP]; simp [mem]) (fun f x => by rw [memP, hd f x]; simp [mem])
        refine ⟨U, ?_, hU, by rw [app]; exact h1, by rw [app]; exact h2⟩
        rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
        cases found <;> simp only [boolAtom, ↓reduceIte, Bool.false_eq_true] at run ⊢ <;> simp [is_list_list, ki, boolAtom, run]

end

theorem lk_filter (k : Term) (s : String) (hk : k = .atom s) : ∀ L : List Term,
    (∀ x ∈ L, isF x = Bool.false → Term.compare (Term.fuel (fk x) k) (fk x) k ≠ .eq) → USort.lk fk k (L.filter isF) = USort.lk fk k L
  | [], _ => rfl
  | x :: L, h => by
    have ih := lk_filter k s hk L (fun y hy => h y (by simp [hy]))
    cases hx : isF x
    · have ne := h x (by simp) hx
      simp [hx, USort.lk_cons, ne, ih]
    · simp [hx, USort.lk_cons, ih]

section
variable {t : Term} {n : Nat}

/-- The values a tag gives the keys of a kind no pair names. -/
theorem tag_value_run (tag : String) (ht : tag = "open" ∨ tag = "closed") :
    ∃ T, Elixir.STTDescrProofsTest.«tag_value/1» (.atom tag) = .ok T ∧ (level t n).E T ∧
      ∀ x, ((level t n).den T x ↔ tag = "open") := by
  rcases ht with rfl | rfl
  · exact ⟨_, by simp [Elixir.STTDescrProofsTest.«tag_value/1», Elixir.Module.Types.Descr.«term/0»],
      (level t n).ef.term, fun x => by simp [(level t n).ef.den_term]⟩
  · exact ⟨_, by simp [Elixir.STTDescrProofsTest.«tag_value/1», Elixir.Module.Types.Descr.«none/0»],
      (level t n).ef.none, fun x => by simp [(level t n).ef.den_none]⟩

theorem domain_value_run {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (s : String) (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ U, Elixir.STTDescrProofsTest.«domain_value/3» (D m) (.atom tag) (Term.list fs) (.atom s) = .ok U ∧
      (level t n).E U ∧ ∀ x, (level t n).den U x ↔
        ((DomAny fs s ∧ DomMem (t := t) (n := n) fs s x) ∨ (¬DomAny fs s ∧ tag = "open")) := by
  obtain ⟨T, rT, eT, dT⟩ := tag_value_run (t := t) (n := n) tag ht
  obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s fs [] h T Bool.false eT (by simp [DomAny]) (by simp)
  simp only [boolAtom, ↓reduceIte, Bool.false_eq_true] at run
  refine ⟨U, by simp [Elixir.STTDescrProofsTest.«domain_value/3», rT, run], hU, fun x => ?_⟩
  simp only [List.nil_append] at h1 h2
  by_cases a : DomAny fs s
  · simp [a, h1 a x]
  · simp [a, h2 a, dT x]

/-- `atom_field/3`: the field of the last pair of a key, or the optional values of the atom domain. -/
theorem atom_field_run {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (s : String) (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ (T : Term) (b : Bool), Elixir.STTDescrProofsTest.«atom_field/3» (D m) (.atom tag) (Term.list fs) (.atom s) =
      .ok (.tuple #[T, boolAtom b]) ∧ (level t n).E T ∧ ∀ o,
        FieldSem (level t n).den (.tuple #[T, boolAtom b]) o ↔ CAtom (t := t) (n := n) tag fs s o := by
  have pairs : ∀ x ∈ fs.reverse, ∃ a b, x = .tuple #[a, b] := fun x hx => by
    rcases h x (List.mem_reverse.mp hx) with ⟨a, v, o, rfl, -⟩ | ⟨ks, v, rfl, -, -⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  have kf := keyfind_lk (.atom s) fs.reverse pairs
  have lkr : USort.lk fk (.atom s) (fieldsRev fs) = USort.lk fk (.atom s) fs.reverse := by
    rw [fieldsRev, ← List.filter_reverse]
    refine lk_filter _ s rfl _ fun x hx hf => ?_
    rcases h x (List.mem_reverse.mp hx) with ⟨a, v, o, rfl, -⟩ | ⟨ks, v, rfl, -, -⟩
    · simp [isF_field] at hf
    · intro e
      have := (Term.compare_eq_atom _ _).mp e
      cases ks <;> simp [fk, Term.list] at this
  unfold CAtom
  rw [lkr]
  cases hx : USort.lk fk (.atom s) fs.reverse with
  | none =>
    obtain ⟨U, rU, eU, dU⟩ := domain_value_run hm tag ht "atom" fs h
    refine ⟨U, Bool.true, ?_, eU, fun o => ?_⟩
    · simp [Elixir.STTDescrProofsTest.«atom_field/3», reverse1_list, kf, hx, rU, boolAtom]
    · rw [fieldSem_mk]
      cases o with
      | none => simp [CKind]
      | some x => simp [CKind, dU x]
  | some x =>
    obtain ⟨mx, ex⟩ := lk_spec hx
    rcases h x (List.mem_reverse.mp mx) with ⟨a, v, o, rfl, hv⟩ | ⟨ks, v, rfl, -, -⟩
    · have e : a = s := by simpa [fk] using ex
      subst e
      refine ⟨v, o, ?_, hv, fun o' => Iff.rfl⟩
      simp [Elixir.STTDescrProofsTest.«atom_field/3», reverse1_list, kf, hx]
    · have := (Term.compare_eq_atom _ _).mp ex
      cases ks <;> simp [fk, Term.list] at this

theorem construct_run {m : Nat} (tag : String) (ht : tag = "open" ∨ tag = "closed") (P : Term) :
    Elixir.STTDescrProofsTest.«construct/2» (D m) (.atom tag) P =
      Elixir.Module.Types.Descr.«map_descr/2» (D m) (.atom tag) P := by
  rcases ht with rfl | rfl
  · simp [Elixir.STTDescrProofsTest.«construct/2», Elixir.Module.Types.Descr.«open_map/1»]
  · simp [Elixir.STTDescrProofsTest.«construct/2», Elixir.Module.Types.Descr.«closed_map/1»]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

theorem sub_of_maps {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    (h : ∀ w, QA w → QB w) : SubN t n A B := fun p hp => by
  obtain ⟨w, hw⟩ := pt_map p (hA.2.1 p hp)
  exact (hB.2.2 p w hw).mpr (h w ((hA.2.2 p w hw).mp hp))

theorem maps_of_sub {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    (h : SubN t n A B) : ∀ w, QA w → QB w := fun w q =>
  (hB.2.2 _ w (mapOf_mpt w)).mp (h _ ((hA.2.2 _ w (mapOf_mpt w)).mpr q))

theorem some_map {C : Term} {Q : MW (level t n).V → Prop} (hC : MapsOf t n C Q)
    (ne : ¬∀ p : PN t n, ¬denD C p) : ∃ w, Q w := by
  obtain ⟨p, hp⟩ := Classical.not_forall.mp ne
  have hp := Classical.not_not.mp hp
  obtain ⟨w, hw⟩ := pt_map p (hC.2.1 p hp)
  exact ⟨w, (hC.2.2 p w hw).mp hp⟩

theorem sub_true {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    (h : ∀ w, QA w → QB w) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) A B = .ok (.atom "true") := by
  rw [next_sub hA.1 hB.1 hm, bp_true.mpr (sub_of_maps hA hB h)]; rfl

/-- `open_map/1` of one atom key with a field. -/
theorem single_atom (s : String) {T : Term} (b : Bool) (he : (level t n).E T) (m : Nat) :
    ∃ H, Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom s, .tuple #[T, boolAtom b]]]) =
      .ok H ∧ MapsOf t n H (fun w => FieldSem (level t n).den (.tuple #[T, boolAtom b]) (w (.atom s))) := by
  have hv := (level t n).ef.static he
  cases b
  · obtain ⟨k, run, key⟩ := open_map_run s hv m
    refine ⟨_, run, mapsOf_congr (mapsOf_one _ (mleaf_field (Or.inl rfl) (fieldsV_req he) key)) fun w => ?_⟩
    rw [mt_open_at he s k w, fieldSem_mk]
    simp
  · obtain ⟨k, run, key⟩ := open_map_opt s hv m
    refine ⟨_, run, mapsOf_congr (mapsOf_one _ (mleaf_field (Or.inl rfl) (fieldsV_opt he) key)) fun w => ?_⟩
    rw [mt_open_opt he s k w, fieldSem_mk]
    simp [OkAt]

/-- `open_map/1` of one domain kind. -/
theorem single_kind {d : String} (hd : d ∈ domainKinds) {U : Term} (he : (level t n).E U) (m : Nat) :
    ∃ H, Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[Term.list [.atom d], U]]) = .ok H ∧
      MapsOf t n H (fun w => (d = "atom" → ∀ s, OkAt (level t n).den U (w (.atom s))) ∧
        ∀ k i, domKind k = d → OkAt (level t n).den U (w (.dom k i))) := by
  obtain ⟨k, run, key⟩ := open_map_dom hd ((level t n).ef.static he) he m
  have fb : MField (level t n).E (.tuple #[.integer k, fieldsTerm (domL d U), .nil]) :=
    mleaf_field (Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)) (l := []) ⟨by simp, by simp⟩ key
  exact ⟨_, run, mapsOf_congr (mapsOf_one _ fb) fun w => mt_dom he k w⟩

theorem ckind_open {tag : String} {fs : List Term} {s : String} {o : Option (level t n).V}
    (h : CKind (t := t) (n := n) tag fs s o) : CKind (t := t) (n := n) "open" fs s o := by
  rcases h with h | ⟨x, rfl, (h | ⟨h, -⟩)⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, rfl, Or.inl h⟩
  · exact Or.inr ⟨x, rfl, Or.inr ⟨h, rfl⟩⟩

theorem csem_open {tag : String} {fs : List Term} {w : MW (level t n).V} (h : CSem (t := t) (n := n) tag fs w) :
    CSem (t := t) (n := n) "open" fs w := by
  refine ⟨fun s => ?_, fun k i => ckind_open (h.2 k i)⟩
  have := h.1 s
  unfold CAtom at this ⊢
  split at this
  · exact this
  · exact ckind_open this

theorem csem_set {tag : String} {fs : List Term} {w : MW (level t n).V} (h : CSem (t := t) (n := n) tag fs w)
    (s : String) {o : Option (level t n).V} (ho : CAtom (t := t) (n := n) tag fs s o) :
    CSem (t := t) (n := n) tag fs (setK s o w) := by
  refine ⟨fun s' => ?_, fun k i => by simpa [setK] using h.2 k i⟩
  by_cases e : s' = s
  · subst e; simpa [setK] using ho
  · have : (MKey.atom s' = MKey.atom s) ↔ False := by simp [e]
    simpa [setK, this] using h.1 s'

/-- A map of values with a key of a kind set. -/
def setD {V : Type} (k : Fin 11) (o : Option V) (w : MW V) : MW V := fun q => if q = .dom k 0 then o else w q

theorem csem_setD {tag : String} {fs : List Term} {w : MW (level t n).V} (h : CSem (t := t) (n := n) tag fs w)
    (k : Fin 11) {o : Option (level t n).V} (ho : CKind (t := t) (n := n) tag fs (domKind k) o) :
    CSem (t := t) (n := n) tag fs (setD k o w) := by
  refine ⟨fun s => by simpa [setD] using h.1 s, fun k' i => ?_⟩
  by_cases e : k' = k ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := e; simpa [setD] using ho
  · have : (MKey.dom k' i = MKey.dom k 0) ↔ False := by simp only [MKey.dom.injEq]; exact ⟨fun h => e h, False.elim⟩
    simpa [setD, this] using h.2 k' i

theorem exists_domKind {d : String} (hd : d ∈ domainKinds) (ne : d ≠ "atom") : ∃ k : Fin 11, domKind k = d := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl ne
  all_goals first
    | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩
    | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩ | exact ⟨9, rfl⟩ | exact ⟨10, rfl⟩

theorem ckind_iff {tag : String} {fs : List Term} {s : String} {U : Term}
    (dU : ∀ x, (level t n).den U x ↔ ((DomAny fs s ∧ DomMem (t := t) (n := n) fs s x) ∨ (¬DomAny fs s ∧ tag = "open")))
    (o : Option (level t n).V) : CKind (t := t) (n := n) tag fs s o ↔ OkAt (level t n).den U o := by
  cases o with
  | none => simp [CKind, OkAt]
  | some x => simp [CKind, OkAt, dU x]

end

section
variable {t : Term} {d : Nat}

theorem ctor_closed_open_core {fs : List Term} (h : ∀ p ∈ fs, CPair t (d + 1) p) {m : Nat}
    (hm : (level t (d + 1)).K + 24 ≤ m) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_closed_open:ensures/3» (D (m + 1)) (Term.list fs) depth node =
      .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) "closed" (Or.inr rfl) fs h
  obtain ⟨O, rO, hO⟩ := descr_maps (m := m) (by omega) "open" (Or.inl rfl) fs h
  simp [Elixir.STTDescrProofsTest.«map_constructor_closed_open:ensures/3», Elixir.Module.Types.Descr.«closed_map/1»,
    Elixir.Module.Types.Descr.«open_map/1», rC, rO, sub_true hC hO (fun w q => csem_open q) (m := m + 1) (by omega)]

theorem ctor_atom_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) (s : String) {m : Nat} (hm : (level t (d + 1)).K + 24 ≤ m) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_atom:ensures/5» (D (m + 1)) (.atom tag) (Term.list fs) (.atom s)
      depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨T, b, rA, eT, iA⟩ := atom_field_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht s fs h
  obtain ⟨H, rH, hH⟩ := single_atom (t := t) (n := d + 1) s b eT m
  simp [Elixir.STTDescrProofsTest.«map_constructor_atom:ensures/5», construct_run tag ht, rC, rA, rH,
    sub_true hC hH (fun w q => (iA _).mpr (q.1 s)) (m := m + 1) (by omega)]

theorem ctor_kind_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) {kind : String} (hk : kind ∈ domainKinds) (na : kind ≠ "atom") {m : Nat}
    (hm : (level t (d + 1)).K + 24 ≤ m) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_kind:ensures/5» (D (m + 1)) (.atom tag) (Term.list fs) (.atom kind)
      depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨U, rU, eU, dU⟩ := domain_value_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht kind fs h
  obtain ⟨H, rH, hH⟩ := single_kind (t := t) (n := d + 1) hk eU m
  simp [Elixir.STTDescrProofsTest.«map_constructor_kind:ensures/5», construct_run tag ht, rC, rU, rH,
    sub_true hC hH (fun w q => ⟨fun e => absurd e na, fun k i e => by
      subst e; exact (ckind_iff dU _).mp (q.2 k i)⟩) (m := m + 1) (by omega)]

theorem not_empty_of {C : Term} {Q : MW (level t (d + 1)).V → Prop} (hC : MapsOf t (d + 1) C Q) {M : Nat}
    (hM : (level t (d + 1)).K + 23 ≤ M)
    (r : (Elixir.Module.Types.Descr.«empty?/1» (D M) C >>= fun y => Erlang.erlang.«not/1» y) = .ok (.atom "true")) :
    ∃ w, Q w := by
  rw [next_empty hC.1 hM, Lynx.Except.ok_bind] at r
  refine some_map hC fun h => ?_
  rw [bp_true.mpr h] at r
  simp [boolAtom, Erlang.erlang.«not/1»] at r

theorem sub_of_true {A B : Term} {QA QB : MW (level t (d + 1)).V → Prop} (hA : MapsOf t (d + 1) A QA)
    (hB : MapsOf t (d + 1) B QB) {M : Nat} (hM : (level t (d + 1)).K + 23 ≤ M)
    (r : Elixir.Module.Types.Descr.«subtype?/2» (D M) A B = .ok (.atom "true")) : ∀ w, QA w → QB w := by
  rw [next_sub hA.1 hB.1 hM] at r
  exact maps_of_sub hA hB (bp_true.mp (boolAtom_inj (q := Bool.true) (Except.ok.inj r)))

theorem ctor_atom_least_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) (s : String) {v : Term} (ev : (level t (d + 1)).E v) (o : Bool) {m : Nat}
    (hm : (level t (d + 1)).K + 24 ≤ m)
    (r1 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«empty?/1» (D (m + 1)) x >>= fun y => Erlang.erlang.«not/1» y) = .ok (.atom "true"))
    (r2 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom s, .tuple #[v, boolAtom o]]]) >>=
        fun y => Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) x y) = .ok (.atom "true")) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_atom_least:ensures/7» (D (m + 1)) (.atom tag) (Term.list fs) (.atom s)
      v (boolAtom o) depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨T, b, rA, eT, iA⟩ := atom_field_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht s fs h
  obtain ⟨H, rH, hH⟩ := single_atom (t := t) (n := d + 1) s o ev m
  rw [construct_run tag ht, rC, Lynx.Except.ok_bind] at r1 r2
  rw [rH, Lynx.Except.ok_bind] at r2
  obtain ⟨w, hw⟩ := not_empty_of hC (by omega) r1
  have inc := sub_of_true hC hH (by omega) r2
  -- every value of the field is a value of the type
  have sem : ∀ x, (level t (d + 1)).den T x → (level t (d + 1)).den v x := by
    intro x hx
    have hs := inc _ (csem_set hw s ((iA (some x)).mp ((fieldSem_mk).mpr (Or.inr ⟨x, rfl, hx⟩))))
    rw [fieldSem_mk] at hs
    simp [setK] at hs
    exact hs
  -- an optional field allows no value, which only an optional field of the type allows
  have opt : o = Bool.true ∨ b = Bool.false := by
    cases b
    · exact Or.inr rfl
    · have hs := inc _ (csem_set hw s ((iA none).mp ((fieldSem_mk).mpr (Or.inl ⟨rfl, rfl⟩))))
      rw [fieldSem_mk] at hs
      simp [setK] at hs
      exact Or.inl hs
  have sub := (level t (d + 1)).ef.subc eT ev sem (m + 1) (by omega)
  simp only [Elixir.STTDescrProofsTest.«map_constructor_atom_least:ensures/7», rA, Lynx.Except.ok_bind]
  rcases opt with rfl | rfl
  · cases b <;> simp [Erlang.erlang.«element/2», sub, boolAtom, Lynx.Except.orElse]
  · cases o <;> simp [Erlang.erlang.«element/2», sub, boolAtom, Lynx.Except.orElse, Erlang.erlang.«not/1»]

theorem ctor_kind_least_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) {kind : String} (hk : kind ∈ domainKinds) (na : kind ≠ "atom") {v : Term}
    (ev : (level t (d + 1)).E v) {m : Nat} (hm : (level t (d + 1)).K + 24 ≤ m)
    (r1 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«empty?/1» (D (m + 1)) x >>= fun y => Erlang.erlang.«not/1» y) = .ok (.atom "true"))
    (r2 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[Term.list [.atom kind], v]]) >>=
        fun y => Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) x y) = .ok (.atom "true")) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_kind_least:ensures/6» (D (m + 1)) (.atom tag) (Term.list fs)
      (.atom kind) v depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨U, rU, eU, dU⟩ := domain_value_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht kind fs h
  obtain ⟨H, rH, hH⟩ := single_kind (t := t) (n := d + 1) hk ev m
  rw [construct_run tag ht, rC, Lynx.Except.ok_bind] at r1 r2
  rw [rH, Lynx.Except.ok_bind] at r2
  obtain ⟨w, hw⟩ := not_empty_of hC (by omega) r1
  have inc := sub_of_true hC hH (by omega) r2
  obtain ⟨k, hkd⟩ := exists_domKind hk na
  subst hkd
  have sem : ∀ x, (level t (d + 1)).den U x → (level t (d + 1)).den v x := by
    intro x hx
    have hs := (inc _ (csem_setD hw k ((ckind_iff dU _).mpr (Or.inr ⟨x, rfl, hx⟩)))).2 k 0 rfl
    simp [setD, OkAt] at hs
    exact hs
  simp [Elixir.STTDescrProofsTest.«map_constructor_kind_least:ensures/6», rU,
    (level t (d + 1)).ef.subc eU ev sem (m + 1) (by omega)]

end

section
variable {t : Term} {n : Nat}

/-- The maps of `empty_map/0`: no key holds a value. -/
theorem empty_map_maps : MapsOf t n (.map [(.atom "map", .tuple #[.integer (-288230376038284242), .atom "closed", .nil])])
    (CSem (t := t) (n := n) "closed" []) := by
  have key : KeyOk (.tuple #[.integer (-288230376038284242), .atom "closed", fieldsTerm []]) := by
    intro k tag l e
    obtain ⟨e₁, e₂, -⟩ := tuple3_inj e
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨fun _ => by decide, fun h => absurd h (by decide)⟩
  have g : TagV (level t n).E (.atom "closed") := Or.inr (Or.inl rfl)
  have sl : FieldsV (level t n).E [] := ⟨by simp, by simp⟩
  refine mapsOf_congr (mapsOf_one _ (mleaf_field g sl key)) fun w => ?_
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', equalExact_eq_decide]
  rw [show (Term.nil : Term) = fieldsTerm [] from rfl, denMF_leaf (level t n).ef sl g]
  have none : ∀ (s : String) (o : Option (level t n).V), CKind (t := t) (n := n) "closed" [] s o ↔ o = none := by
    intro s o; cases o <;> simp [CKind, DomAny]
  constructor
  · intro ms
    refine ⟨fun s => ?_, fun k i => (none _ _).mpr ?_⟩
    · have := ms.atoms s
      unfold FSem at this
      simp only [mapLookup, List.find?_nil, Option.map_none, tagSem_atom, equalExact_eq_decide] at this
      unfold CAtom
      simp only [fieldsRev, List.filter_nil, List.reverse_nil, USort.lk_nil]
      exact (none _ _).mpr (by simpa using this)
    · have := ms.doms k i; rw [tagSem_atom] at this; simpa using this
  · rintro ⟨ha, hd⟩
    refine ⟨fun s => ?_, fun k i => ?_⟩
    · have := ha s
      unfold CAtom at this
      simp only [fieldsRev, List.filter_nil, List.reverse_nil, USort.lk_nil] at this
      unfold FSem
      simp only [mapLookup, List.find?_nil, Option.map_none, tagSem_atom, equalExact_eq_decide]
      exact Or.inr ((none _ _).mp this)
    · rw [tagSem_atom]; exact Or.inr ((none _ _).mp (hd k i))

theorem ctor_empty_core {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    Elixir.STTDescrProofsTest.«map_constructor_empty:ensures/0» (D (m + 1)) = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (t := t) (n := n) (m := m) (by omega) "closed" (Or.inr rfl) [] (by simp)
  have hE := empty_map_maps (t := t) (n := n)
  have s1 := sub_true hE hC (fun w q => q) (m := m + 1) (by omega)
  have s2 := sub_true hC hE (fun w q => q) (m := m + 1) (by omega)
  simp [Elixir.STTDescrProofsTest.«map_constructor_empty:ensures/0», Elixir.Module.Types.Descr.«empty_map/0»,
    Elixir.Module.Types.Descr.«closed_map/1», rC, Elixir.Module.Types.Descr.«equal?/2», s1, s2,
    Erlang.erlang.«==/2»]

end

theorem tag_ok {tag : Term} (h : isMember tag [.atom "open", .atom "closed"] = .atom "true") :
    ∃ s, tag = .atom s ∧ (s = "open" ∨ s = "closed") := by
  obtain ⟨c, mc, e⟩ := isMember_true h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mc
  rcases mc with rfl | rfl
  · exact ⟨"open", (compareExact_eq_atom _ _).mp e, Or.inl rfl⟩
  · exact ⟨"closed", (compareExact_eq_atom _ _).mp e, Or.inr rfl⟩

theorem ne_atom_ok {k : String} (h : Erlang.erlang.«/=/2» (.atom k) (.atom "atom") = .ok (.atom "true")) :
    k ≠ "atom" := by
  intro e; subst e; simp [Erlang.erlang.«/=/2»] at h

end Elixir.STTDescrProofsTest.Nest
