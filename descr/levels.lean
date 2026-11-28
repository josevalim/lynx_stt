module

public import Erlang.program
public import MapKind

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- Element types at a nesting level, with their values. -/
structure Level : Type 1 where
  nd : Term
  E : Term → Prop
  V : Type
  den : Term → V → Prop
  tl : V → Prop
  K : Nat
  ef : EF nd E V den tl K
  none : E (.map [])
  hasT : ∀ {e}, IsT nd e → E e

theorem keyOf_neg (t : Term) : keyOf t < 0 := by
  obtain ⟨h, run, lt⟩ := Erlang.erlang.phash2_range (Term.list [.atom "term", t])
  simp only [keyOf, run]
  omega

theorem expN_descr {nd : Term} {TF LF MF : Term → Prop} {e : Term} (tf : TF (litN e (keyOf nd))) :
    DEG Fn TF LF MF (expN e (keyOf nd)) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w hw => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
    by_cases t : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp t⟩
    · by_cases a : compareExact (fuel q (.atom "atom")) q (.atom "atom") = .eq
      · exact ⟨"atom", by simp [names], (compareExact_eq_atom _ _).mp a⟩
      · simp [t, a] at h
  · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq, equalExact_eq_decide] at hw
    by_cases t : name = "tuple"
    · subst t; simp at hw; subst hw; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tf⟩))))
    · by_cases a : name = "atom"
      · subst a; simp at hw; subst hw
        exact Or.inr (Or.inl ⟨rfl, ⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩,
          .atom "nil", by simp [amemV, mapLookup]⟩)
      · simp [t, a] at hw

theorem DEG.notT {nd : Term} {TF LF MF : Term → Prop} {a : Term} (ha : DEG Fn TF LF MF a) : ¬IsT nd a := by
  rcases ha with rfl | ⟨X, rfl, -⟩
  · exact isT_term
  · exact isT_map

theorem nodeOk0 (nd : Term) : NodeOk nd (DEG FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map")) :=
  ⟨fun he => expN_descr (Or.inr (Bdd.leaf_iff.mpr ⟨_, he, rfl⟩)), DEG.notT⟩

theorem nodeOk_DE {nd : Term} {E : Term → Prop} (hterm : E (.atom "term")) (hasT : ∀ {e}, IsT nd e → E e) :
    NodeOk nd (DE E) := by
  refine ⟨fun {e} he => expN_descr (Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨keyOf nd, "closed", [.atom "term", e], rfl,
    Or.inr rfl, fun x mx => ?_⟩, fun ⟨k, h⟩ => by simp [Term.list] at h⟩, fun k tag l h => ?_⟩)), DEG.notT⟩
  · simp at mx; rcases mx with h | h <;> subst h; exact hterm; exact hasT he
  · obtain ⟨e₁, e₂, -⟩ := tuple3_inj h
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨fun _ => keyOf_neg nd, fun h => by simp at h⟩

/-- The element types of each level, with the node `t`. -/
def level (t : Term) : Nat → Level
  | 0 => ⟨t, DEN t (DEG FunTop (OField (PureLit t)) (FieldOk "list") (FieldOk "map")), PtG Resp Resp Resp FVT, denN t denD, tlD,
      23, addNode (ef_gen (step0 t) (fuse0 t)) (nodeOk0 t), Or.inl (Or.inr ⟨[], rfl, descrC_nil⟩), fun h => Or.inr h⟩
  | n + 1 =>
    let L := level t n
    ⟨L.nd, DEN L.nd (DE L.E), PtD L.E L.den L.tl (FVal L.E L.den), denN L.nd denD, tlD, L.K + 24,
      addNode (ef_step L.ef L.none)
      (nodeOk_DE L.ef.term L.hasT), Or.inl de_none, fun h => Or.inr h⟩

theorem level_nd (t : Term) : ∀ n, (level t n).nd = t
  | 0 => rfl
  | n + 1 => level_nd t n

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

/-- Types with no points are checked empty. -/
theorem descr_empty_none (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hS : FS []) {m : Nat} (hm : K ≤ m)
    {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X)
    (none : ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.map X) (.map []) = .ok (.atom "true") := by
  by_cases ne : X = []
  · subst ne
    simpa [boolAtom] using empty_none_seen (D m) (.map [])
  have key : ∀ name x, mapLookup X (.atom name) = some x →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map []) = .ok (.atom "true") :=
    fun name x h => fieldC_empty_none ks fc hm (sX.fields name x h) (fun _ => hS) fun p ok => by
      have := none name p ok; rwa [h] at this
  have run := descr_empty_run (D m) (S := .map []) (bt := Bool.true) (bm := Bool.true) (bl := Bool.true)
    (bf := Bool.true) sX.static ne
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "tuple" x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "map" x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "list" x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "fun" x h)
  have noA : (mapLookup X (.atom "atom")).isSome = Bool.false := by
    cases h : mapLookup X (.atom "atom") with
    | none => rfl
    | some x =>
      obtain ⟨p, ok, hp⟩ := atom_full sX h
      have := none "atom" p ok; rw [h, hp] at this; cases this
  have noB : (mapLookup X (.atom "bitmap")).isSome = Bool.false := by
    cases h : mapLookup X (.atom "bitmap") with
    | none => rfl
    | some x =>
      obtain ⟨p, ok, hp⟩ := bitmap_full sX h
      have := none "bitmap" p ok; rw [h, hp] at this; cases this
  rw [noA, noB] at run
  simpa [boolAtom] using run

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Top-level types over the element types of a level: the top type or types whose function fields are arrows
between element types. Their plain and optimized operations hold the expected points, and their emptiness and
subtyping checks are exact. -/

/-- Top-level types over the element types of a level. -/
def TC (L : Level) (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) X

abbrev TP (L : Level) : Type := PtD L.E L.den L.tl (FVal L.E L.den)

/-- Top-level types whose function types may hold any literals, as the specs accept them. -/
def TCF (L : Level) (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ DescrC FunF (TField L.E) (LF L.E) (MField L.E) X

theorem tks (L : Level) : Kinds (L.K + 11) (TField L.E) (LF L.E) (MField L.E) (ValT L.E L.den) (ValLN L.E L.den L.tl)
    (ValMN L.E L.den) := (kinds L.ef).mono (by omega)

theorem tfc (L : Level) : FunC (L.K + 11) (FunA L.E) (FVal L.E L.den) (fun _ => True) True := funAC L.ef L.ef.subc

theorem lookup_out' {Fn TF LF MF : Term → Prop} {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {name : String}
    (h : name ∉ names) : mapLookup X (.atom name) = none := by
  cases hx : mapLookup X (.atom name) with
  | none => rfl
  | some x =>
    obtain ⟨name', m, e⟩ := sX.keys _ (by rw [hx]; rfl)
    simp only [Term.atom.injEq] at e
    subst e; exact absurd m h

section
variable {L : Level}

theorem termT (L : Level) : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) T ∧ T ≠ [] ∧
    ∀ v : TP L, denD (.map T) v := by
  obtain ⟨T, term, sT, ne, -, all⟩ := termC (FV := FVal L.E L.den) (tks L) (Fn := FunA L.E) funA_top
  exact ⟨T, term, sT, ne, fun v => (denD_map v).mpr (all _ v.2.1 _ v.2.2)⟩

theorem tc_nil : TC L (.map []) := Or.inr ⟨[], rfl, descrC_nil (Fn := FunA L.E)⟩

theorem denD_nil (v : TP L) : ¬denD (.map []) v := by simp [denD_map, mapLookup, dn_none]

theorem tc_union {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, union_term_l _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, union_term_r _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem, -⟩ := descr_union (tks L) (tfc L) (m := n) (by omega) sA sB
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

theorem tc_inter {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, inter_term_left _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, inter_term_right _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem, -⟩ := descr_inter (tks L) (tfc L) (m := n) (by omega) sA sB
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

theorem diff_none_right' (d : Dispatcher) {a : Term} (ha : TC L a) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map []) = .ok a := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]

theorem tc_diff {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, tc_nil, diff_term_right _ _, fun v => by simp [denD_nil, denD_term]⟩
  by_cases nB : B = []
  · subst nB
    exact ⟨a, ha, diff_none_right' _ ha, fun v => by simp [denD_nil]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, all⟩ := termT L
    obtain ⟨U, run, sU, sem, -⟩ := descr_diff (tks L) (tfc L) (m := n) (by omega) sT sB
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, (diff_term_left _ term sT.static sB.static nB).trans run, fun v => ?_⟩
    have := (denD_map v).mp (all v)
    simp only [denD_map, sem _ _ v.2.2, this, denD_term, true_and, Bool.true_and]
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run, sU, sem, -⟩ := descr_diff (tks L) (tfc L) (m := n) (by omega) sA sB
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

theorem tc_opt_union {a b : Term} (ha : TC L a) (hb : TC L b) (S : List (Term × Term)) {m : Nat}
    (hm : L.K + 13 ≤ m) : ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_left _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_union (tks L) (tfc L) (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

theorem tc_opt_inter {a b : Term} (ha : TC L a) (hb : TC L b) (S : List (Term × Term)) {m : Nat}
    (hm : L.K + 13 ≤ m) : ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, opt_inter_term_l _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, opt_inter_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_inter (tks L) (tfc L) (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

theorem tc_opt_diff {a b : Term} (ha : TC L a) (hb : TC L b) (S : List (Term × Term)) {m : Nat}
    (hm : L.K + 15 ≤ m) : ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, tc_nil, difference_term_term _ _ _, fun v => by simp [denD_nil, denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · by_cases nB : B = []
    · subst nB
      exact ⟨_, Or.inl rfl, difference_term_none _ _, fun v => by simp [denD_nil, denD_term]⟩
    obtain ⟨T, term, sT, -, all⟩ := termT L
    obtain ⟨U, run, sU, sem⟩ := descr_opt_diff (tks L) (tfc L) (m := n) (by omega) sT sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, (opt_diff_term_left _ _ term sT.static sB.static nB).trans run, fun v => ?_⟩
    have := (denD_map v).mp (all v)
    simp only [denD_map, sem _ _ v.2.2, this, denD_term, true_and, Bool.true_and]
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run, sU, sem⟩ := descr_opt_diff (tks L) (tfc L) (m := n) (by omega) sA sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- Types without points are checked empty. -/
theorem tc_empty {a : Term} (ha : TC L a) {m : Nat} (hm : L.K + 11 ≤ m) (none : ∀ v : TP L, ¬denD a v) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (.atom "true") := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact absurd (denD_term ptWit) (none ptWit)
  rw [empty_map_seen]
  refine descr_empty_none (tks L) (tfc L) trivial hm sX fun name p ok => ?_
  by_cases mem : name ∈ names
  · have := none ⟨(name, p), mem, ok⟩
    simpa [denD] using this
  · rw [lookup_out' sX mem, dn_none]

/-- Subtyping of top-level types is complete. -/
theorem tc_sub {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (incl : ∀ v : TP L, denD a v → denD b v) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨T, term, sT, -, all⟩ := termT L
  have left : ∃ A, DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) A ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) b ∧
      ∀ v : TP L, denD a v ↔ denD (.map A) v := by
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · exact ⟨T, sT, subtype_term_l term _ _, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩⟩
    · exact ⟨A, sA, rfl, fun v => Iff.rfl⟩
  obtain ⟨A, sA, eA, dA⟩ := left
  have right : ∃ B, DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E) B ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) b =
        Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B) ∧
      ∀ v : TP L, denD b v ↔ denD (.map B) v := by
    rcases hb with rfl | ⟨B, rfl, sB⟩
    · exact ⟨T, sT, subtype_term_r term _ _, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩⟩
    · exact ⟨B, sB, rfl, fun v => Iff.rfl⟩
  obtain ⟨B, sB, eB, dB⟩ := right
  rw [eA, eB]
  refine descr_sub_complete (tks L) (tfc L) trivial (by omega) sA sB fun name p ok h => ?_
  by_cases mem : name ∈ names
  · have := (dB ⟨(name, p), mem, ok⟩).mp (incl _ ((dA _).mpr ((denD_map _).mpr h)))
    exact (denD_map _).mp this
  · rw [lookup_out' sA mem, dn_none] at h; cases h

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Nested types of the specification whose literals are keyed are element types of their level. -/

/-- All literals of a BDD satisfy `Q`. -/
def AllLits (Q : Term → Prop) : Term → Prop
  | .tuple ⟨[_, lit, c, u, d]⟩ => Q lit ∧ AllLits Q c ∧ AllLits Q u ∧ AllLits Q d
  | .tuple ⟨[k, x, y]⟩ => Q (.tuple #[k, x, y])
  | _ => True

theorem bdd_allLits {ok Q : Term → Prop} {w : Term} (wb : Bdd ok w) (all : AllLits Q w) :
    Bdd (fun t => ok t ∧ Q t) w := by
  revert all
  refine Bdd.induction (P := fun ok w => AllLits Q w → Bdd (fun t => ok t ∧ Q t) w) ?_ ?_ ?_ ?_ ok w wb
  · intro _ _; exact Bdd.top
  · intro _ _; exact Bdd.bot
  · intro ok k x y okl all
    exact Bdd.leaf_iff.mpr ⟨okl, by simpa [AllLits] using all⟩
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id all
    simp only [AllLits] at all
    obtain ⟨ql, ac, au, ad⟩ := all
    have mono : ∀ {x}, Bdd (fun t => Above ok lit t ∧ Q t) x → Bdd (Above (fun t => ok t ∧ Q t) lit) x :=
      fun hx => hx.mono fun t ⟨⟨o, l⟩, q⟩ => ⟨⟨o, q⟩, l⟩
    exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, ql⟩, mono (ic ac), mono (iu au), mono (id ad)⟩

/-- Keyed tuple literals whose elements satisfy `P`. -/
def TQ (P : Term → Prop) (t : Term) : Prop :=
  KeyOk t ∧ ∀ (k : Int) (tag : String) (l : List Term), t = .tuple #[.integer k, .atom tag, Term.list l] → ∀ e ∈ l, P e

/-- Keyed map literals with atom keys in order whose field types satisfy `P`. -/
def MQ (P : Term → Prop) (t : Term) : Prop :=
  KeyOk t ∧ ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    l.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt) ∧
    (∀ e ∈ l, (∃ s : String, e.1 = .atom s) ∧ ∀ u o, e.2 = .tuple #[u, boolAtom o] → P u) ∧
    ∀ dl, tag = fieldsTerm dl → DomsV P dl

/-- List literals whose element and tail types satisfy `P`. -/
def LQ (P : Term → Prop) (t : Term) : Prop := ∀ (k : Int) (a b : Term), t = .tuple #[.integer k, a, b] → P a ∧ P b

/-- Function literals whose argument and return types satisfy `P`. -/
def FLQ (P : Term → Prop) (t : Term) : Prop :=
  ∀ (k : Term) (args : List Term) (ret : Term), t = .tuple #[k, Term.list args, ret] → (∀ a ∈ args, P a) ∧ P ret

/-- Function types whose arities are natural numbers, at least one in unions, with literals of types `P`. -/
def FunK (P : Term → Prop) (w : Term) : Prop :=
  ∃ (tag : Term) (R : List (Term × Term)), w = .tuple #[tag, .map R] ∧ (tag = .atom "union" → R ≠ []) ∧
    NatKeys R ∧ ∀ q v, mapLookup R q = some v → AllLits (FLQ P) v

/-- The literal invariants the optimized operations expect of the fields of a type whose literals hold types `P`:
keyed tuple and map literals, map literals with atom keys in order, and, for element types, function types of
natural arities, at least one in unions. -/
structure KeyedF (P : Term → Prop) (el : Bool) (X : List (Term × Term)) : Prop where
  funs : el = Bool.true → ∀ w, mapLookup X (.atom "fun") = some w → FunK P w
  tuples : ∀ w, mapLookup X (.atom "tuple") = some w → AllLits (TQ P) w
  maps : ∀ w, mapLookup X (.atom "map") = some w → AllLits (MQ P) w
  lists : ∀ w, mapLookup X (.atom "list") = some w → AllLits (LQ P) w

/-- Keyed element types at each nesting depth. -/
def Keyed : Nat → Term → Prop
  | 0, _ => True
  | d + 1, e => e = .atom "term" ∨ (∃ a b c, e = .tuple #[a, b, c]) ∨ ∃ X, e = .map X ∧ KeyedF (Keyed d) Bool.true X

section
variable {E P E' : Term → Prop}

theorem tfield_of (conv : ∀ e, E e → P e → E' e) {w : Term} (tf : TupleField E w)
    (keys : AllLits (fun t => KeyOk t ∧ ∀ (k : Int) (tag : String) (l : List Term),
      t = .tuple #[.integer k, .atom tag, Term.list l] → ∀ e ∈ l, P e) w) : TField E' w := by
  rcases tf with top | b
  · exact Or.inl top
  refine Or.inr ((bdd_allLits b keys).mono fun t ⟨⟨⟨k, tag, l, e, g, els⟩, nt⟩, key, pe⟩ => ?_)
  subst e
  exact ⟨⟨⟨k, tag, l, rfl, g, fun x mx => conv x (els x mx) (pe k tag l rfl x mx)⟩, nt⟩, key⟩

/-- Nested function types with natural arities, at least one in unions, and literals of types `P`, are function
types of element types. -/
theorem funA_of (conv : ∀ e, E e → P e → E' e) {w : Term} (ff : FField E w) (fk : FunK P w) : FunA E' w := by
  obtain ⟨pos, R, rfl, bR⟩ := ff
  obtain ⟨tag, R', e, ne, nk, lits⟩ := fk
  have e₀ := congrArg (fun a : Term => match a with | .tuple ⟨[x, _]⟩ => x | _ => .nil) e
  have e₁ := congrArg (fun a : Term => match a with | .tuple ⟨[_, y]⟩ => y | _ => .nil) e
  simp only [Term.map.injEq] at e₀ e₁
  subst e₀ e₁
  refine ⟨pos, R, rfl, fun hp => ne (by subst hp; rfl), fun q v hv => ?_, nk⟩
  refine (bdd_allLits (bR q v hv) (lits q v hv)).mono fun t ⟨⟨n, hq, k, args, ret, et, len, ha, hr⟩, fl⟩ => ?_
  obtain ⟨pa, pr⟩ := fl _ _ _ et
  exact ⟨n.toNat, by rw [hq]; congr; omega, k, args, ret, et, by omega, fun a ma => conv a (ha a ma) (pa a ma),
    conv ret hr pr⟩

theorem lf_of (conv : ∀ e, E e → P e → E' e) (hterm : E' (.atom "term")) {w : Term} (lf : LField E w)
    (keys : AllLits (fun t => ∀ (k : Int) (a b : Term), t = .tuple #[.integer k, a, b] → P a ∧ P b) w) :
    LF E' w := by
  rcases lf with ⟨k, rfl⟩ | b
  · exact Bdd.leaf_iff.mpr ⟨k, _, _, rfl, hterm, hterm⟩
  refine (bdd_allLits b keys).mono fun t ⟨⟨_, k, a, c, e, ha, hc⟩, pe⟩ => ?_
  subst e
  obtain ⟨pa, pc⟩ := pe k a c rfl
  exact ⟨k, a, c, rfl, conv a ha pa, conv c hc pc⟩

theorem mfield_of (conv : ∀ e, E e → P e → E' e) {w : Term} (mf : MapField E w) (keys : AllLits (MQ P) w) :
    MField E' w := by
  rcases mf with top | b
  · exact Or.inl top
  refine Or.inr ((bdd_allLits b keys).mono fun t ⟨⟨⟨k, tag, l, e, g, fv⟩, nt⟩, key, pe⟩ => ?_)
  subst e
  obtain ⟨sorted, each, doms⟩ := pe k tag l rfl
  refine ⟨⟨k, tag, l, rfl, ?_, fun x mx => ⟨(each x mx).1, ?_⟩, sorted⟩, nt, key⟩
  · rcases g with rfl | rfl | ⟨dl, rfl, hdl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨dk, dp⟩ := doms dl rfl
      exact Or.inr (Or.inr ⟨dl, rfl, fun e me => ⟨(dk e me).1, conv _ (hdl e me) (dk e me).2⟩, dp⟩)
  · obtain ⟨u, o, eu, hu⟩ := fv x mx
    exact ⟨u, o, eu, conv u hu ((each x mx).2 u o eu)⟩

end

/-- Flat types are types of the bottom level. -/
theorem lelem_deg0 {t e : Term} (h : LElem e) :
    DEG FunTop (OField (PureLit t)) (FieldOk "list") (FieldOk "map") e := by
  rcases h with rfl | ⟨M, rfl, bM⟩
  · exact Or.inl rfl
  refine Or.inr ⟨M, rfl, fun q hq => ?_, fun name w hw => ?_⟩
  · rcases bM.keys q hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
  · rcases bM.keys (.atom name) (by rw [hw]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨rfl, bM.bitmap w hw⟩
    · exact Or.inr (Or.inl ⟨rfl, bM.atom w hw |>.1, by
        obtain ⟨q, hq⟩ := (bM.atom w hw).2; exact ⟨q, by simpa [amem, hw] using hq⟩⟩)
    · have := bM.top "fun" w (by decide) (by decide) hw
      simp [topValue] at this
      exact Or.inr (Or.inr (Or.inl ⟨rfl, this.symm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨by decide, by decide,
        bM.top "list" w (by decide) (by decide) hw⟩)⟩)))
    · have := bM.top "tuple" w (by decide) (by decide) hw
      simp [topValue] at this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨_, this.symm⟩⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨by decide, by decide,
        bM.top "map" w (by decide) (by decide) hw⟩)⟩))))

/-- Keyed nested types of the specification are element types of their level. -/
theorem nest_level (t : Term) : ∀ (d : Nat) (e : Term), Nest t d e → Keyed d e → (level t d).E e
  | 0, _, h, _ => by
    rcases h with h | h
    · exact Or.inl (lelem_deg0 (elem_lelem h))
    · exact Or.inr h
  | d + 1, _, h, k => by
    rcases h with h | h
    rotate_left
    · exact Or.inr (by rw [level_nd]; exact h)
    rcases h with rfl | ⟨X, rfl, v⟩
    · exact Or.inl (Or.inl rfl)
    obtain ⟨X', e, kf⟩ := (k.resolve_left (by simp)).resolve_left (by simp)
    simp only [Term.map.injEq] at e
    subst e
    have conv : ∀ e, Nest t d e → Keyed d e → (level t d).E e := nest_level t d
    refine Or.inl (Or.inr ⟨X, rfl, fun q hq => ?_, fun name w h => ?_⟩)
    · rcases v.keys q hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
    · rcases v.keys (.atom name) (by rw [h]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
        subst e
      · exact Or.inl ⟨rfl, v.bitmap w h⟩
      · obtain ⟨p, S, rfl, set⟩ := v.atom w h
        exact Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, atom_nonempty p S fun hp => v.atomUnion S (by subst hp; simpa using h)⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, funA_of conv (v.funs w h) (kf.funs rfl w h)⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, lf_of conv (level t d).ef.term (v.lists w h) (kf.lists w h)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tfield_of conv (v.tuples w h) (kf.tuples w h)⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, mfield_of conv (v.maps w h) (kf.maps w h)⟩))))

/-- Keyed negatable types are top-level types over the element types of their depth. -/
theorem negatable_tc (t : Term) (d : Nat) {X : List (Term × Term)} (v : Negatable (Nest t d) X)
    (kf : KeyedF (Keyed d) Bool.false X) : TCF (level t d) (.map X) := by
  have conv : ∀ e, Nest t d e → Keyed d e → (level t d).E e := nest_level t d
  refine Or.inr ⟨X, rfl, fun q hq => ?_, fun name w h => ?_⟩
  · rcases v.keys q hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp [names], rfl⟩
  · rcases v.keys (.atom name) (by rw [h]; rfl) with e | e | e | e | e | e <;> simp only [Term.atom.injEq] at e <;>
      subst e
    · exact Or.inl ⟨rfl, v.bitmap w h⟩
    · obtain ⟨p, S, rfl, set⟩ := v.atom w h
      exact Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩, atom_nonempty p S fun hp => v.atomUnion S (by subst hp; simpa using h)⟩)
    · obtain ⟨pos, R, rfl⟩ := v.funs w h
      exact Or.inr (Or.inr (Or.inl ⟨rfl, pos, R, rfl, fun q x hx => v.arities _ h _ R rfl q x hx⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, lf_of conv (level t d).ef.term (v.lists w h) (kf.lists w h)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tfield_of conv (v.tuples w h) (kf.tuples w h)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, mfield_of conv (v.maps w h) (kf.maps w h)⟩))))

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The top type is a top-level type at every level, and the laws use the level of their depth. -/

section
variable {L : Level} {m : Nat}

theorem tc_term : TC L (.atom "term") := Or.inl rfl

end

theorem level_K (t : Term) : ∀ n, (level t n).K = 23 + 24 * n
  | 0 => rfl
  | n + 1 => by
    show (level t n).K + 24 = _
    rw [level_K t n]
    omega

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! What the specification of the optimized laws checks: keyed literals at every depth. -/

theorem sizeOf_children5 (h lit c u d : Term) :
    sizeOf lit < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) ∧
    sizeOf c < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) ∧ sizeOf u < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) ∧
      sizeOf d < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) := by
  simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec, List.cons.sizeOf_spec,
    List.nil.sizeOf_spec]
  omega

theorem int_lt_true {a b : Int} (h : Erlang.erlang.«</2» (.integer a) (.integer b) = .ok Term.true) : a < b := by
  refine Classical.byContradiction fun hk => ?_
  have : Ord.compare a b ≠ .lt := fun e => hk (Int.compare_eq_lt.mp e)
  simp [Erlang.erlang.«</2», this, Term.true] at h

theorem int_ge_true {a b : Int} (h : Erlang.erlang.«>=/2» (.integer a) (.integer b) = .ok Term.true) : b ≤ a := by
  refine Classical.byContradiction fun hk => ?_
  have : Ord.compare a b = .lt := Int.compare_eq_lt.mpr (by omega)
  simp [Erlang.erlang.«>=/2», this, Term.true] at h

/-- Element checks of `keyed?/2` at a depth that ensure `P`. -/
def KeyedOk (P : Term → Prop) (depth : Term) : Prop := ∀ e, «keyed?/2» e depth = .ok Term.true → P e

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_elements_spec (hP : KeyedOk P depth) :
    ∀ l : List Term, «keyed_elements?/2» (Term.list l) depth = .ok Term.true → ∀ e ∈ l, P e
  | [], _ => by simp
  | x :: xs, h => by
    rw [«keyed_elements?/2».eq_def] at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact hP _ h.1
    · exact keyed_elements_spec hP xs h.2 e me

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_tuple_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_tuple_bdd?/2» t depth = .ok Term.true → TQ P t ∧ AllLits (TQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_tuple_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨⟨fun k tag l e => by simp at e, fun k tag l e => by simp at e⟩, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key elements
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨hk, he⟩ := h
      have tq : TQ P (.tuple ⟨[key, .atom "closed", elements]⟩) := by
        refine ⟨fun k tag l e => ?_, fun k tag l e => ?_⟩
        · obtain ⟨rfl, e₂, rfl⟩ := tuple3_eq e
          simp only [Term.atom.injEq] at e₂
          subst e₂
          exact ⟨fun _ => int_lt_true (by simpa using hk), fun h => by simp at h⟩
        · obtain ⟨rfl, -, rfl⟩ := tuple3_eq e
          exact keyed_elements_spec hP l he
      exact ⟨tq, tq⟩
    · rename_i key tag elements notClosed
      simp only [Term.true, Lynx.Except.andAlso_eq_true, Lynx.Except.orElse_eq_true] at h
      obtain ⟨hk, he⟩ := h
      have tq : TQ P (.tuple ⟨[key, tag, elements]⟩) := by
        refine ⟨fun k tag' l e => ?_, fun k tag' l e => ?_⟩
        · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
          refine ⟨fun c => by subst c; exact absurd rfl notClosed, fun _ ne => ?_⟩
          rcases hk with hk | ⟨-, hk⟩
          · cases l with
            | nil => exact absurd rfl ne
            | cons _ _ => simp [Erlang.erlang.«==/2», Term.list] at hk
          · exact int_ge_true (by simpa using hk)
        · obtain ⟨rfl, -, rfl⟩ := tuple3_eq e
          exact keyed_elements_spec hP l he
      exact ⟨tq, tq⟩
    · rename_i other notNode notClosed notLeaf
      refine ⟨⟨fun k tag l e => absurd e (notLeaf _ _ _), fun k tag l e => absurd e (notLeaf _ _ _)⟩, ?_⟩
      unfold AllLits
      split
      · exact (notNode _ _ _ _ _ rfl).elim
      · exact (notLeaf _ _ _ rfl).elim
      · trivial

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_values_spec (hP : KeyedOk P depth) :
    ∀ l : List (Term × Term), «keyed_values?/2» (fieldsTerm l) depth = .ok Term.true →
      ∀ e ∈ l, ∀ u o, e.2 = .tuple #[u, boolAtom o] → P u
  | [], _ => by simp
  | (k, v) :: rest, h => by
    rw [«keyed_values?/2».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    by_cases shape : ∃ a b, v = .tuple #[a, b]
    · obtain ⟨a, b, rfl⟩ := shape
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      intro e me u o hv
      rcases List.mem_cons.mp me with rfl | me'
      · simp only [Term.tuple.injEq] at hv
        have := congrArg (fun a : Array Term => a[0]?) hv
        simp at this
        subst this
        exact hP _ h.1
      · exact keyed_values_spec hP rest (by simpa [fieldsTerm, Term.list] using h.2) e me' u o hv
    · exfalso
      split at h
      · rename_i heq
        simp only [Term.cons.injEq, Term.tuple.injEq] at heq
        have := congrArg (fun a : Array Term => a[1]?) heq.1
        simp at this
        exact shape ⟨_, _, this⟩
      · rename_i heq; simp at heq
      · simp at h

theorem domain_kind_spec {k : Term} (h : «domain_kind?/1» k = .ok Term.true) : ∃ s, k = .atom s ∧ s ∈ domainKinds := by
  have mem : ∀ L : List String, isMember k (L.map Term.atom) = .atom "true" → ∃ s, k = .atom s ∧ s ∈ L := by
    intro L
    induction L with
    | nil => simp
    | cons x xs ih =>
      intro hm
      simp only [List.map, isMember_cons] at hm
      split at hm
      · rename_i e
        exact ⟨x, (compare_eq_atom _ _).mp (compare_eq_of_compareExact_eq _ _ e), List.mem_cons_self⟩
      · obtain ⟨s, rfl, ms⟩ := ih hm
        exact ⟨s, rfl, List.mem_cons_of_mem _ ms⟩
  apply mem domainKinds
  unfold «domain_kind?/1» at h
  simp only [domainKinds, List.map]
  refine Classical.byContradiction fun hm => ?_
  simp [Term.true, -isMember_cons] at h

theorem domain_kinds_spec : ∀ dl : List (Term × Term), «domain_kinds?/1» (fieldsTerm dl) = .ok Term.true →
    (∀ e ∈ dl, ∃ s, e.1 = .atom s ∧ s ∈ domainKinds) ∧ dl.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt)
  | [], _ => ⟨by simp, by simp⟩
  | [(k, v)], h => by
    rw [«domain_kinds?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    exact ⟨by simpa using domain_kind_spec h, by simp⟩
  | (k, v) :: (k', v') :: rest, h => by
    rw [«domain_kinds?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨ha, hlt⟩, hr⟩ := h
    obtain ⟨keys, pw⟩ := domain_kinds_spec ((k', v') :: rest) (by simpa [fieldsTerm, Term.list] using hr)
    have lt := lt_true (by simpa [Term.true] using hlt)
    refine ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨fun e me => ?_, pw⟩⟩
    · rcases List.mem_cons.mp me with rfl | me
      · exact domain_kind_spec (by simpa [Term.true] using ha)
      · exact keys e me
    · rcases List.mem_cons.mp me with rfl | me
      · exact lt
      · exact cmp_lt_trans lt ((List.pairwise_cons.mp pw).1 e me)

theorem keyed_domains_spec (hP : KeyedOk P depth) : ∀ n T, sizeOf T ≤ n →
    «keyed_domains?/2» T depth = .ok Term.true → ∃ dl : List (Term × Term), T = fieldsTerm dl ∧ ∀ e ∈ dl, P e.2 := by
  intro n
  induction n with
  | zero => intro T size; cases T <;> simp at size <;> omega
  | succ n ih =>
    intro T size h
    rw [«keyed_domains?/2».eq_def] at h
    split at h
    · rename_i kind type rest
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨dl, rfl, hdl⟩ := ih rest (by simp at size; omega) h.2
      refine ⟨(kind, type) :: dl, rfl, fun e me => ?_⟩
      rcases List.mem_cons.mp me with rfl | me
      · exact hP _ h.1
      · exact hdl e me
    · exact ⟨[], rfl, by simp⟩
    · simp [Term.true] at h

/-- Map leaves other than closed ones, read from the spec. -/
theorem mq_leaf (hP : KeyedOk P depth) {key tag fields : Term} (notClosed : tag ≠ .atom "closed")
    (hk : ∀ (k : Int) (l : List Term), key = .integer k → fields = Term.list l → l ≠ [] → 0 ≤ k)
    (hs : «sorted_keys?/1» fields = .ok Term.true) (hv : «keyed_values?/2» fields depth = .ok Term.true)
    (hd : ∀ dl, tag = fieldsTerm dl → DomsV P dl) : MQ P (.tuple ⟨[key, tag, fields]⟩) := by
  refine ⟨fun k tag' l e => ?_, fun k tag' l e => ?_⟩
  · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
    exact ⟨fun c => by subst c; exact absurd rfl notClosed, fun _ ne => hk k l rfl rfl ne⟩
  · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
    obtain ⟨keys, pw⟩ := sorted_keys_spec l hs
    exact ⟨pw, fun e me => ⟨keys e me, keyed_values_spec hP l hv e me⟩, hd⟩

theorem keyed_map_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_map_bdd?/2» t depth = .ok Term.true → MQ P t ∧ AllLits (MQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_map_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨⟨fun k tag l e => by simp at e, fun k tag l e => by simp at e⟩, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key fields
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨hk, hs⟩, hv⟩ := h
      have mq : MQ P (.tuple ⟨[key, .atom "closed", fields]⟩) := by
        refine ⟨fun k tag l e => ?_, fun k tag l e => ?_⟩
        · obtain ⟨rfl, e₂, rfl⟩ := tuple3_eq e
          simp only [Term.atom.injEq] at e₂
          subst e₂
          exact ⟨fun _ => int_lt_true (by simpa using hk), fun h => by simp at h⟩
        · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
          obtain ⟨keys, pw⟩ := sorted_keys_spec l hs
          exact ⟨pw, fun e me => ⟨keys e me, keyed_values_spec hP l hv e me⟩,
            fun dl e => absurd e.symm (fieldsTerm_ne_atom dl "closed")⟩
      exact ⟨mq, mq⟩
    · rename_i T notNode notClosed
      simp only at h
      split at h
      · rename_i key tag fields
        have nc : tag ≠ .atom "closed" := fun e => notClosed key fields (by rw [e])
        -- the leaf keys the tag clause reads
        have tagClause : ∀ {key fields : Term}, ((Erlang.erlang.«==/2» fields Term.nil = .ok (.atom "true") ∨
            Erlang.erlang.«==/2» fields Term.nil = .ok (.atom "false") ∧
              Erlang.erlang.«>=/2» key (Term.integer 0) = .ok (.atom "true")) ∧
            «sorted_keys?/1» fields = .ok (.atom "true")) ∧ «keyed_values?/2» fields depth = .ok (.atom "true") →
            (∀ dl, tag = fieldsTerm dl → DomsV P dl) → MQ P (.tuple ⟨[key, tag, fields]⟩) := by
          intro key fields h hd
          obtain ⟨⟨hk, hs⟩, hv⟩ := h
          refine mq_leaf hP nc (fun k l ek el ne => ?_) hs hv hd
          subst ek el
          rcases hk with hk | ⟨-, hk⟩
          · cases l with
            | nil => exact absurd rfl ne
            | cons _ _ => simp [Erlang.erlang.«==/2», Term.list] at hk
          · exact int_ge_true (by simpa using hk)
        have mq : MQ P (.tuple ⟨[key, tag, fields]⟩) := by
          cases tag with
          | nil =>
            simp [Erlang.erlang.«is_list/1», Term.true,
              Lynx.Except.andAlso_eq_true] at h
            obtain ⟨⟨⟨⟨hk, -⟩, -⟩, hs⟩, hv⟩ := h
            refine mq_leaf hP nc (fun k l ek _ _ => by subst ek; exact int_ge_true (by simpa using hk)) hs hv
              fun dl e => ?_
            have : dl = [] := fieldsTerm_eq_nil.mp e.symm
            subst this
            exact ⟨by simp, by simp⟩
          | cons a b =>
            simp [Erlang.erlang.«is_list/1», Term.true,
              Lynx.Except.andAlso_eq_true] at h
            obtain ⟨⟨⟨⟨hk, hkinds⟩, hdoms⟩, hs⟩, hv⟩ := h
            obtain ⟨dl, edl, hdl⟩ := keyed_domains_spec hP _ _ (Nat.le_refl _) hdoms
            refine mq_leaf hP nc (fun k l ek _ _ => by subst ek; exact int_ge_true (by simpa using hk)) hs hv
              fun dl' e => ?_
            rw [edl] at e hkinds
            obtain rfl := fieldsTerm_inj e
            obtain ⟨dk, dp⟩ := domain_kinds_spec dl hkinds
            exact ⟨fun e me => ⟨dk e me, hdl e me⟩, dp⟩
          | _ =>
            simp [Erlang.erlang.«is_list/1», Term.false] at h
            exact tagClause h fun dl e => absurd e (by cases dl <;> simp [fieldsTerm, Term.list])
        exact ⟨mq, mq⟩
      · rename_i notLeaf
        refine ⟨⟨fun k tag l e => absurd e (notLeaf _ _ _), fun k tag l e => absurd e (notLeaf _ _ _)⟩, ?_⟩
        unfold AllLits
        split
        · exact (notNode _ _ _ _ _ rfl).elim
        · exact (notLeaf _ _ _ rfl).elim
        · trivial

theorem keyed_list_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_list_bdd?/2» t depth = .ok Term.true → LQ P t ∧ AllLits (LQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_list_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨fun k a b e => by simp at e, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key list last
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      have lq : LQ P (.tuple ⟨[key, list, last]⟩) := fun k a b e => by
        obtain ⟨-, rfl, rfl⟩ := tuple3_eq e
        exact ⟨hP _ h.1, hP _ h.2⟩
      exact ⟨lq, lq⟩
    · rename_i other notNode notLeaf
      refine ⟨fun k a b e => absurd e (notLeaf _ _ _), ?_⟩
      unfold AllLits
      split
      · exact (notNode _ _ _ _ _ rfl).elim
      · exact (notLeaf _ _ _ rfl).elim
      · trivial

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_fun_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_fun_bdd?/2» t depth = .ok Term.true → FLQ P t ∧ AllLits (FLQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_fun_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨fun k a b e => by simp at e, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key args ret
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      have fq : FLQ P (.tuple ⟨[key, args, ret]⟩) := fun k as r e => by
        obtain ⟨-, rfl, rfl⟩ := tuple3_eq e
        exact ⟨keyed_elements_spec hP as h.1, hP _ h.2⟩
      exact ⟨fq, fq⟩
    · rename_i other notNode notLeaf
      refine ⟨fun k a b e => absurd e (notLeaf _ _ _), ?_⟩
      unfold AllLits
      split
      · exact (notNode _ _ _ _ _ rfl).elim
      · exact (notLeaf _ _ _ rfl).elim
      · trivial

theorem keyed_arities_spec (hP : KeyedOk P depth) : ∀ es : List (Term × Term),
    «keyed_arities?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true →
      ∀ e ∈ es, (∃ n : Nat, e.1 = .integer n) ∧ AllLits (FLQ P) e.2
  | [], _ => by simp
  | (k, v) :: rest, h => by
    rw [«keyed_arities?/2».eq_def] at h
    simp only [List.map_cons, Term.list, Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨⟨hi, hge⟩, hb⟩, hr⟩ := h
    have nat : ∃ n : Nat, k = .integer n := by
      cases k <;> simp [Erlang.erlang.«is_integer/1», Term.true] at hi
      rename_i z
      simp [Erlang.erlang.«>=/2», Int.isGE_compare, Term.true] at hge
      exact ⟨z.toNat, by simp only [Term.integer.injEq]; omega⟩
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact ⟨nat, (keyed_fun_spec hP _ _ (Nat.le_refl _) hb).2⟩
    · exact keyed_arities_spec hP rest hr e me

/-- What `keyed_fields?/3` checks of a field. -/
def FQ (P : Term → Prop) (el : Bool) (e : Term × Term) : Prop :=
  (e.1 = .atom "fun" → el = Bool.true → FunK P e.2) ∧ (e.1 = .atom "tuple" → AllLits (TQ P) e.2) ∧
    (e.1 = .atom "map" → AllLits (MQ P) e.2) ∧ (e.1 = .atom "list" → AllLits (LQ P) e.2)

/-- One field of `keyed_fields?/3`. -/
theorem keyed_fields_step (hP : KeyedOk P depth) (el : Bool) (k v rest : Term)
    (h : «keyed_fields?/3» (.cons (.tuple #[k, v]) rest) depth (boolAtom el) = .ok Term.true) :
    FQ P el (k, v) ∧ «keyed_fields?/3» rest depth (boolAtom el) = .ok Term.true := by
  rw [«keyed_fields?/3».eq_def] at h
  simp only [boolAtom] at h
  have elT : ∀ {el : Bool}, Term.atom (if el = Bool.true then "true" else "false") = .atom "true" → el = Bool.true := by
    intro el e; cases el <;> simp_all
  split at h
  · rename_i tag R fields heq₁ heq₂
    have e₀ := elT heq₂
    subst e₀
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq₁
    obtain ⟨e₁, rfl⟩ := heq₁
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨htag, har⟩, hr⟩ := h
    simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at har
    have each := keyed_arities_spec hP (mapEntries R) har
    refine ⟨⟨fun _ _ => ⟨tag, R, rfl, fun ht => ?_, fun q hq => ?_, fun q v hv => ?_⟩, fun e => by simp at e,
      fun e => by simp at e, fun e => by simp at e⟩, by simpa [boolAtom] using hr⟩
    · subst ht
      rintro rfl
      simp [Erlang.erlang.«==/2», Lynx.Except.orElse, Erlang.erlang.«map_size/1», Erlang.erlang.«>/2»] at htag
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
      obtain ⟨e, me, qe, -⟩ := lookup_entry hv
      obtain ⟨n, hn⟩ := (each e me).1
      rw [hn, compareExact_eq_integer] at qe
      exact ⟨n, qe⟩
    · obtain ⟨e, me, -, rfl⟩ := lookup_entry hv
      exact (each e me).2
  · simp at h
  · rename_i heq
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq
    obtain ⟨e₁, rfl⟩ := heq
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    exact ⟨⟨fun e => by simp at e, fun _ => (keyed_tuple_spec hP _ _ (Nat.le_refl _) h.1).2, fun e => by simp at e,
      fun e => by simp at e⟩, by simpa [boolAtom] using h.2⟩
  · rename_i heq
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq
    obtain ⟨e₁, rfl⟩ := heq
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    exact ⟨⟨fun e => by simp at e, fun e => by simp at e, fun _ => (keyed_map_spec hP _ _ (Nat.le_refl _) h.1).2,
      fun e => by simp at e⟩, by simpa [boolAtom] using h.2⟩
  · rename_i heq
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq
    obtain ⟨e₁, rfl⟩ := heq
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    exact ⟨⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e,
      fun _ => (keyed_list_spec hP _ _ (Nat.le_refl _) h.1).2⟩, by simpa [boolAtom] using h.2⟩
  · rename_i field fields notT notM notL heq notF₁ notF
    simp only [Term.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨⟨fun e et => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩, by simpa [boolAtom] using h⟩
    · simp only at e; subst e; subst et
      exact (notF v (by simp) rfl).elim
    · simp only at e; subst e; exact (notT v rfl).elim
    · simp only at e; subst e; exact (notM v rfl).elim
    · simp only at e; subst e; exact (notL v rfl).elim
  · rename_i heq; simp at heq
  · simp at h

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_fields_spec (hP : KeyedOk P depth) (el : Bool) :
    ∀ es : List (Term × Term), «keyed_fields?/3» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth (boolAtom el) =
      .ok Term.true → ∀ e ∈ es, FQ P el e
  | [], _ => by simp
  | (k, v) :: rest, h => by
    obtain ⟨fq, hr⟩ := keyed_fields_step hP el k v _ (by simpa [Term.list] using h)
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact fq
    · exact keyed_fields_spec hP el rest hr e me

/-- The fields of a map that `keyed_fields?/3` accepts. -/
theorem keyedF_of (hP : KeyedOk P depth) (el : Bool) (X : List (Term × Term))
    (h : (do
      let l ← Erlang.maps.«to_list/1» (.map X)
      «keyed_fields?/3» l depth (boolAtom el)) = .ok Term.true) : KeyedF P el X := by
  simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at h
  have each := keyed_fields_spec hP el (mapEntries X) h
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  refine ⟨fun et w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).1 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp)) et
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).2.1 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp))
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).2.2.1 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp))
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).2.2.2 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp))

end

/-- What `keyed?/2` checks at each depth. -/
theorem keyed_spec : ∀ d : Nat, KeyedOk (Keyed d) (.integer d)
  | 0, _, _ => trivial
  | d + 1, e, h => by
    rw [«keyed?/2».eq_def] at h
    split at h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    · rename_i _ _ heq; simp at heq; omega
    · rename_i e₀ _ _ _ _ _
      cases e₀ with
      | map X =>
        have sub : Erlang.erlang.«-/2» (.integer ((d + 1 : Nat) : Int)) (.integer 1) = .ok (.integer (d : Int)) := by
          rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
        refine Or.inr (Or.inr ⟨X, rfl, keyedF_of (keyed_spec d) Bool.true X ?_⟩)
        simpa [sub, boolAtom] using h
      | _ => simp [Erlang.maps.«to_list/1»] at h

/-- The depths of the laws are natural numbers. -/
theorem depth_nat {depth : Term} (h : «depth?/1» depth = .ok Term.true) : ∃ n : Nat, depth = .integer n := by
  cases depth <;> simp [«depth?/1», Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true, Erlang.erlang.«>=/2»,
    Int.isGE_compare] at h
  rename_i z
  exact ⟨z.toNat, by simp only [Term.integer.injEq]; omega⟩

theorem negatable_cases (t : Term) (n : Nat) (descr : Term)
    (h : «negatable?/2» descr (.tuple #[.integer n, t]) = .ok Term.true) :
    descr = .atom "term" ∨ ∃ X, descr = .map X ∧ Negatable (Nest t n) X :=
  negatable_map t n descr h

/-- The types of `opt_negatable?/2` are top-level types over the element types of their depth. -/
theorem opt_negatable_tc (t : Term) (n : Nat) (descr : Term)
    (h : «opt_negatable?/2» descr (.tuple #[.integer n, t]) = .ok Term.true) : TCF (level t n) descr := by
  unfold «opt_negatable?/2» at h
  split at h
  · exact Or.inl rfl
  · rename_i d nn notTerm heq
    obtain ⟨rfl, rfl⟩ : d = .integer n ∧ nn = t := by simp at heq; exact ⟨heq.1.symm, heq.2.symm⟩
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨hn, hk⟩ := h
    rcases negatable_cases _ n _ hn with rfl | ⟨X, rfl, v⟩
    · exact (notTerm rfl).elim
    · exact negatable_tc _ n v (keyedF_of (keyed_spec n) Bool.false X (by simpa [boolAtom] using hk))
  · simp at h

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Merging maps field by field, whatever their keys. -/

/-- The bindings of a map other than its dynamic part, as `maps:remove/2` and `maps:take/2` leave them. -/
def rmDyn (X : List (Term × Term)) : List (Term × Term) :=
  X.filter fun entry => !decide (compareExact (fuel (.atom "dynamic") entry.1) (.atom "dynamic") entry.1 = .eq)

theorem lookup_rmDyn (X : List (Term × Term)) (q : Term) :
    mapLookup (rmDyn X) q = if compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq then none else mapLookup X q := by
  simp only [rmDyn, mapLookup_remove]

theorem lookup_rmDyn_name (X : List (Term × Term)) {name : String} (h : name ≠ "dynamic") :
    mapLookup (rmDyn X) (.atom name) = mapLookup X (.atom name) := by
  simp [lookup_rmDyn, h]

theorem rmDyn_static {X : List (Term × Term)} (h : mapLookup X (.atom "dynamic") = none) : rmDyn X = X := by
  refine List.filter_eq_self.mpr fun e me => ?_
  by_cases c : compareExact (fuel (.atom "dynamic") e.1) (.atom "dynamic") e.1 = .eq <;> simp [c]
  have : (mapLookup X (.atom "dynamic")).isSome := (mapLookup_isSome X _).mpr ⟨e, me, c⟩
  rw [h] at this; cases this

theorem names_ne_dyn {name : String} (h : name ∈ names) : name ≠ "dynamic" := by
  simp [names] at h; rintro rfl; simp at h

/-- Merging maps with atom keys looks up the combined values of shared keys and the others' values. -/
theorem merge_gen (d : Dispatcher) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term)
    (call : ∀ q v₁ v₂, d.pure (.function false module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂)
    (L R : List (Term × Term)) (keysR : ∀ q, (mapLookup R q).isSome → ∃ n, q = .atom n)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∃ u, f q x y = .ok u) :
    ∃ U, Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map L) (.map R) (.function false module name 3 caps) =
        .ok (.map U) ∧
      ∀ q, (mapLookup R q = none → mapLookup U q = mapLookup L q) ∧
        (∀ y, mapLookup R q = some y → mapLookup L q = none → mapLookup U q = some y) ∧
        (∀ x y u, mapLookup L q = some x → mapLookup R q = some y → f q x y = .ok u → mapLookup U q = some u) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match f k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, f q x y = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
  obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup d false module name caps L R g (by
    intro e me x hx
    have hy := mapLookup_of_mem_mapEntries me
    obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
    rw [call, ru, value _ _ _ _ ru])
  refine ⟨out, by simpa using run, fun q => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩⟩
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rfl
    | some e => rw [(find_entry hit).2] at hR; cases hR
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit] at hR; cases hR
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [h] at hR; cases hR
      simp [← mapLookup_congr qe, hL]
  · rw [look q]
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit] at hR; cases hR
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [h] at hR; cases hR
      obtain ⟨n, hn⟩ := keysR e.1 (by rw [← mapLookup_congr qe, h]; rfl)
      rw [hn] at qe
      obtain rfl := (compareExact_eq_atom q n).mp qe
      simp [hn, hL, value _ _ _ _ ru]

/-- Intersecting maps looks up the kept combined values of shared keys. -/
theorem intersect_gen (n : Nat) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term)
    (call : ∀ q v₁ v₂, (D (n + 1)).pure (.function false module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂)
    (L R : List (Term × Term)) (keysL : ∀ q, (mapLookup L q).isSome → ∃ n, q = .atom n)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∃ u, f q x y = .ok u) :
    ∃ I, Elixir.Module.Types.Descr.«symmetrical_intersection/3» (D (n + 1)) (.map L) (.map R) (.function false module name 3 caps) =
        .ok (.map I) ∧
      ∀ q, (mapLookup L q = none → mapLookup I q = none) ∧ (mapLookup R q = none → mapLookup I q = none) ∧
        (∀ x y u, mapLookup L q = some x → mapLookup R q = some y → f q x y = .ok u →
          mapLookup I q = if kept (q, u) then some u else none) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match f k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, f q x y = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (n + 1)) false module name caps L R g (by
    intro e member y hy
    obtain ⟨w, run⟩ := calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy
    rw [call, run, value _ _ _ _ run])
  have lookI' : ∀ q, mapLookup I q =
      match mapLookup L q, mapLookup R q with
      | some x, some y => some (g q x y)
      | _, _ => none := by
    intro q
    rw [lookI]
    cases hit : (mapEntries L).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [find_none hit]
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      obtain ⟨n, hn⟩ := keysL e.1 (by rw [← mapLookup_congr qe, h]; rfl)
      rw [hn] at qe
      obtain rfl := (compareExact_eq_atom q n).mp qe
      rw [h, ← hn]
      dsimp only
      cases mapLookup R e.1 <;> rfl
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (n + 1)) false "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  refine ⟨out, ?_, fun q => ?_⟩
  · unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runO]
  have look : mapLookup out q =
      match mapLookup L q, mapLookup R q with
      | some x, some y => if kept (q, g q x y) then some (g q x y) else none
      | _, _ => none := by
    rw [lookO]
    cases hit : (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none =>
      have := find_none hit
      rw [lookI'] at this
      revert this
      cases mapLookup L q <;> cases mapLookup R q <;> simp
    | some e =>
      obtain ⟨qe, h⟩ := find_entry hit
      rw [lookI'] at h
      revert h
      cases mapLookup L q <;> cases mapLookup R q <;> simp
      intro h
      simp only [kept]
      rw [h]
      rfl
  refine ⟨fun hL => by rw [look, hL], fun hR => by rw [look, hR]; cases mapLookup L q <;> rfl,
    fun x y w hL hR run => by rw [look, hL, hR]; simp only [value _ _ _ _ run]⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Gradual top-level types: a static part and a dynamic part that includes it. -/

section
variable {L : Level}

abbrev DC (L : Level) := DescrC (FunA L.E) (TField L.E) (LF L.E) (MField L.E)
abbrev FC (L : Level) := FieldC (FunA L.E) (TField L.E) (LF L.E) (MField L.E)

theorem denD_rmDyn (X : List (Term × Term)) (v : TP L) : denD (.map (rmDyn X)) v ↔ denD (.map X) v := by
  simp only [denD_map, lookup_rmDyn_name X (names_ne_dyn v.2.1)]

/-- Field operations a union merges fields with: they unite the points of their fields. -/
structure UnionOp (L : Level) (d : Dispatcher) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term) : Prop where
  call : ∀ q v₁ v₂, d.pure (.function false module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂
  spec : ∀ name x y, FC L name x → FC L name y → ∃ u, f (.atom name) x y = .ok u ∧ FC L name u ∧
    ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (some u) p = (dn name (some x) p || dn name (some y) p)

theorem DC.atoms {X : List (Term × Term)} (sX : DC L X) : ∀ q, (mapLookup X q).isSome → ∃ n, q = .atom n :=
  fun q h => let ⟨n, _, e⟩ := sX.keys q h; ⟨n, e⟩

/-- Maps whose bindings other than the dynamic one are fields have atom keys. -/
theorem rmDyn_atoms {X : List (Term × Term)} (sX : DC L (rmDyn X)) : ∀ q, (mapLookup X q).isSome → ∃ n, q = .atom n := by
  intro q h
  by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
  · exact ⟨"dynamic", (compareExact_eq_atom q _).mp e⟩
  · exact sX.atoms q (by rw [lookup_rmDyn, ite_eq_right e]; exact h)

/-- Merging static types unites them. -/
theorem merge_descr {d : Dispatcher} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    {A B : List (Term × Term)} (sA : DC L A) (sB : DC L B) :
    ∃ U, Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map A) (.map B) (.function false module name 3 caps) =
        .ok (.map U) ∧ DC L U ∧ ∀ v : TP L, denD (.map U) v ↔ denD (.map A) v ∨ denD (.map B) v := by
  obtain ⟨U, run, look⟩ := merge_gen d module name caps f op.call A B sB.atoms (fun q x y hx hy => by
    obtain ⟨n, -, rfl⟩ := sA.keys q (by simp [hx])
    obtain ⟨u, ru, -⟩ := op.spec n x y (sA.fields n x hx) (sB.fields n y hy)
    exact ⟨u, ru⟩)
  have keysU : ∀ q, (mapLookup U q).isSome → (mapLookup A q).isSome ∨ (mapLookup B q).isSome := by
    intro q h
    cases hB : mapLookup B q with
    | none => rw [(look q).1 hB] at h; exact Or.inl h
    | some y => exact Or.inr (by simp)
  obtain ⟨cU, sem, -⟩ := union_gen (slh := False) sA sB f
    (fun n => ⟨(look _).1, (look _).2.1, (look _).2.2⟩) keysU
    (fun n x y fx fy => let ⟨u, ru, fu, su⟩ := op.spec n x y fx fy; ⟨u, ru, fu, su, False.elim⟩)
  exact ⟨U, run, cU, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

/-- Unions of dynamic parts: top-level types merged field by field. -/
theorem dyn_union_tc {d : Dispatcher} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    {a b : Term} (ha : TC L a) (hb : TC L b) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«dynamic_union/3» d a b (.function false module name 3 caps) = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, by unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, by unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl, fun v => by simp [denD_term]⟩
  obtain ⟨U, run, sU, sem⟩ := merge_descr op sA sB
  refine ⟨_, Or.inr ⟨U, rfl, sU⟩, ?_, sem⟩
  unfold Elixir.Module.Types.Descr.«dynamic_union/3»
  simpa [unfold_map] using run

/-- The upper bound of a type: its dynamic part, or the type itself when it is static. -/
def upper (a : Term) : Term :=
  match a with
  | .map X => (mapLookup X (.atom "dynamic")).getD a
  | _ => a

/-- Gradual top-level types: top-level types, or maps of fields with a dynamic part, a top-level type that holds
every point of the fields, as Descr maintains. -/
def GC (L : Level) (a : Term) : Prop :=
  TC L a ∨ ∃ X Dy, a = .map X ∧ mapLookup X (.atom "dynamic") = some Dy ∧ TC L Dy ∧ DC L (rmDyn X) ∧
    ∀ v : TP L, denD a v → denD Dy v

theorem upper_tc {a : Term} (ha : TC L a) : upper a = a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · rfl
  · simp [upper, sX.static]

theorem upper_dyn {X : List (Term × Term)} {Dy : Term} (h : mapLookup X (.atom "dynamic") = some Dy) :
    upper (.map X) = Dy := by
  simp [upper, h]

theorem GC.tc {a : Term} (ha : TC L a) : GC L a := Or.inl ha

theorem GC.up_tc {a : Term} (ha : GC L a) : TC L (upper a) := by
  rcases ha with ha | ⟨X, Dy, rfl, hD, tD, -, -⟩
  · rwa [upper_tc ha]
  · rwa [upper_dyn hD]

theorem GC.inv {a : Term} (ha : GC L a) (v : TP L) (h : denD a v) : denD (upper a) v := by
  rcases ha with ha | ⟨X, Dy, rfl, hD, -, -, inv⟩
  · rwa [upper_tc ha]
  · rw [upper_dyn hD]; exact inv v h

/-- A static operand meets a gradual one as its own dynamic part. -/
def alignT (X : List (Term × Term)) : List (Term × Term) :=
  match mapLookup X (.atom "dynamic") with
  | some _ => X
  | none => (.atom "dynamic", .map X) :: X

theorem rmDyn_cons_dyn (X : List (Term × Term)) (w : Term) : rmDyn ((.atom "dynamic", w) :: X) = rmDyn X := by
  simp [rmDyn]

/-- Aligned maps of gradual types: their dynamic part is the upper bound, and their fields those of the type. -/
theorem align_gc {X : List (Term × Term)} (hX : GC L (.map X)) :
    mapLookup (alignT X) (.atom "dynamic") = some (upper (.map X)) ∧ DC L (rmDyn (alignT X)) ∧
      ∀ v : TP L, denD (.map (alignT X)) v ↔ denD (.map X) v := by
  rcases hX with (h | ⟨X', e, sX⟩) | ⟨X', Dy, e, hD, -, sX, -⟩
  · cases h
  · simp only [Term.map.injEq] at e; subst e
    have st := sX.static
    refine ⟨by rw [alignT, st, upper_tc (Or.inr ⟨X, rfl, sX⟩)]; simp [mapLookup], ?_, fun v => ?_⟩
    · rw [alignT, st]; simp only; rw [rmDyn_cons_dyn, rmDyn_static st]; exact sX
    · rw [alignT, st]; simp only
      rw [← denD_rmDyn, rmDyn_cons_dyn, denD_rmDyn]
  · simp only [Term.map.injEq] at e; subst e
    refine ⟨by simp [alignT, hD, upper], by simpa [alignT, hD] using sX, fun v => by simp [alignT, hD]⟩

/-- The fields of `U` merge those of `L` and `R` with `f`. -/
def MergeL (f : Term → Term → Term → Except Exception Term) (L R U : List (Term × Term)) : Prop :=
  (∀ name, (mapLookup R (.atom name) = none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
    (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = none → mapLookup U (.atom name) = some y) ∧
    (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok u →
      mapLookup U (.atom name) = some u)) ∧
  ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome

/-- The fields of `I` intersect those of `L` and `R` with `f`. -/
def InterL (f : Term → Term → Term → Except Exception Term) (L R I : List (Term × Term)) : Prop :=
  (∀ name, (mapLookup L (.atom name) = none → mapLookup I (.atom name) = none) ∧
    (mapLookup R (.atom name) = none → mapLookup I (.atom name) = none) ∧
    (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok w →
      mapLookup I (.atom name) = keptO name w)) ∧
  ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome

theorem rmDyn_alignT (X : List (Term × Term)) : rmDyn (alignT X) = rmDyn X := by
  unfold alignT
  cases mapLookup X (.atom "dynamic") <;> simp [rmDyn_cons_dyn]

/-- Merging maps with dynamic parts merges their fields and their dynamic parts. -/
theorem merge_grad {d : Dispatcher} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    {X Y : List (Term × Term)} {Dx Dy Du : Term} (hX : mapLookup X (.atom "dynamic") = some Dx)
    (hY : mapLookup Y (.atom "dynamic") = some Dy) (sX : DC L (rmDyn X)) (sY : DC L (rmDyn Y))
    (du : f (.atom "dynamic") Dx Dy = .ok Du) :
    ∃ U, Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map X) (.map Y) (.function false module name 3 caps) =
        .ok (.map U) ∧ mapLookup U (.atom "dynamic") = some Du ∧ DC L (rmDyn U) ∧
        (∀ v : TP L, denD (.map U) v ↔ denD (.map X) v ∨ denD (.map Y) v) ∧ MergeL f (rmDyn X) (rmDyn Y) (rmDyn U) := by
  obtain ⟨U, run, look⟩ := merge_gen d module name caps f op.call X Y (rmDyn_atoms sY) (fun q x y hx hy => by
    by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
    · obtain rfl := (compareExact_eq_atom q _).mp e
      rw [hX] at hx; rw [hY] at hy; cases hx; cases hy
      exact ⟨Du, du⟩
    · have hx' : mapLookup (rmDyn X) q = some x := by rw [lookup_rmDyn, ite_eq_right e]; exact hx
      have hy' : mapLookup (rmDyn Y) q = some y := by rw [lookup_rmDyn, ite_eq_right e]; exact hy
      obtain ⟨n, -, rfl⟩ := sX.keys q (by simp [hx'])
      obtain ⟨u, ru, -⟩ := op.spec n x y (sX.fields n x hx') (sY.fields n y hy')
      exact ⟨u, ru⟩)
  have lookR : ∀ q, (mapLookup (rmDyn Y) q = none → mapLookup (rmDyn U) q = mapLookup (rmDyn X) q) ∧
      (∀ y, mapLookup (rmDyn Y) q = some y → mapLookup (rmDyn X) q = none → mapLookup (rmDyn U) q = some y) ∧
      (∀ x y u, mapLookup (rmDyn X) q = some x → mapLookup (rmDyn Y) q = some y → f q x y = .ok u →
        mapLookup (rmDyn U) q = some u) := by
    intro q
    simp only [lookup_rmDyn]
    by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
    · simp [e]
    · simp only [e, ite_false]; exact look q
  have keysU : ∀ q, (mapLookup (rmDyn U) q).isSome → (mapLookup (rmDyn X) q).isSome ∨ (mapLookup (rmDyn Y) q).isSome := by
    intro q h
    cases hB : mapLookup (rmDyn Y) q with
    | none => rw [(lookR q).1 hB] at h; exact Or.inl h
    | some y => exact Or.inr (by simp)
  obtain ⟨cU, sem, -⟩ := union_gen (slh := False) sX sY f
    (fun n => ⟨(lookR _).1, (lookR _).2.1, (lookR _).2.2⟩) keysU
    (fun n x y fx fy => let ⟨u, ru, fu, su⟩ := op.spec n x y fx fy; ⟨u, ru, fu, su, False.elim⟩)
  refine ⟨U, run, (look _).2.2 Dx Dy Du hX hY du, cU, fun v => ?_, fun n => ⟨(lookR _).1, (lookR _).2.1, (lookR _).2.2⟩,
    keysU⟩
  rw [← denD_rmDyn U, ← denD_rmDyn X, ← denD_rmDyn Y]
  simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]

/-- Merging aligned gradual types unites their fields and their upper bounds. -/
theorem merge_aligned {d d' : Dispatcher} {module name module' name' : String} {caps caps' : Array Term}
    {f f' : Term → Term → Term → Except Exception Term} (op : UnionOp L d module name caps f)
    (op' : UnionOp L d' module' name' caps' f')
    (dyn : ∀ x y, f (.atom "dynamic") x y =
      Elixir.Module.Types.Descr.«dynamic_union/3» d' x y (.function false module' name' 3 caps'))
    {X Y : List (Term × Term)} (hX : GC L (.map X)) (hY : GC L (.map Y)) :
    ∃ c, GC L c ∧
      Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map (alignT X)) (.map (alignT Y))
        (.function false module name 3 caps) = .ok c ∧
      (∀ v : TP L, denD c v ↔ denD (.map X) v ∨ denD (.map Y) v) ∧
      (∀ v : TP L, denD (upper c) v ↔ denD (upper (.map X)) v ∨ denD (upper (.map Y)) v) ∧
      ∃ U, c = .map U ∧ MergeL f (rmDyn X) (rmDyn Y) (rmDyn U) ∧
        Elixir.Module.Types.Descr.«dynamic_union/3» d' (upper (.map X)) (upper (.map Y))
          (.function false module' name' 3 caps') = .ok (upper c) := by
  obtain ⟨dX, sX, eX⟩ := align_gc hX
  obtain ⟨dY, sY, eY⟩ := align_gc hY
  obtain ⟨Du, tu, ru, su⟩ := dyn_union_tc op' hX.up_tc hY.up_tc
  obtain ⟨U, run, dU, sU, sem, look⟩ := merge_grad op dX dY sX sY (by rw [dyn]; exact ru)
  rw [rmDyn_alignT, rmDyn_alignT] at look
  have lo : ∀ v : TP L, denD (.map U) v ↔ denD (.map X) v ∨ denD (.map Y) v := fun v => by
    rw [sem, eX, eY]
  refine ⟨_, Or.inr ⟨U, Du, rfl, dU, tu, sU, fun v h => ?_⟩, run, lo, fun v => by rw [upper_dyn dU, su],
    U, rfl, look, by rw [upper_dyn dU]; exact ru⟩
  rw [su]
  rcases (lo v).mp h with h | h
  · exact Or.inl (hX.inv v h)
  · exact Or.inr (hY.inv v h)

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Unions of gradual types. -/

section
variable {L : Level}

theorem bare_union_op {n : Nat} (hm : L.K + 12 ≤ n) :
    UnionOp L (D (n + 1)) "Elixir.Module.Types.Descr" "bare_union" #[]
      (Elixir.Module.Types.Descr.«bare_union/3» (D n)) where
  call := fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure n q v₁ v₂
  spec := fun _ _ _ fx fy =>
    let ⟨u, ru, fu, su, _⟩ := fieldC_union (tks L) (tfc L) (by omega) fx fy; ⟨u, ru, fu, su⟩

theorem opt_union_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    UnionOp L (D (n + 1)) "Elixir.Module.Types.Descr" "-opt_union/3-anonymous-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_union/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_union/3-anonymous-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_union (tks L) (tfc L) (by omega) fx fy S

theorem opt_union_dyn_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    UnionOp L (D (n + 1)) "Elixir.Module.Types.Descr" "-opt_union/4-fun-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_union/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_union/4-fun-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_union (tks L) (tfc L) (by omega) fx fy S

theorem bare_union_dyn (d : Dispatcher) (x y : Term) :
    Elixir.Module.Types.Descr.«bare_union/3» d (.atom "dynamic") x y =
      Elixir.Module.Types.Descr.«dynamic_union/3» d x y (.function false "Elixir.Module.Types.Descr" "bare_union" 3 #[]) := by
  unfold Elixir.Module.Types.Descr.«bare_union/3»; rfl

theorem opt_union_dyn (d : Dispatcher) (x y S : Term) :
    Elixir.Module.Types.Descr.«opt_union/4» d (.atom "dynamic") x y S =
      Elixir.Module.Types.Descr.«dynamic_union/3» d x y (.function false "Elixir.Module.Types.Descr" "-opt_union/4-fun-0-" 3 #[S]) := by
  unfold Elixir.Module.Types.Descr.«opt_union/4»; rfl

theorem union_run_grad (d : Dispatcher) {X Y : List (Term × Term)} (nX : X ≠ []) (nY : Y ≠ [])
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.map X) (.map Y) =
      Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map (alignT X)) (.map (alignT Y))
        (.function false "Elixir.Module.Types.Descr" "bare_union" 3 #[]) := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, Erlang.erlang.«==/2», hX, hY, nX, nY, Erlang.maps.«put/3», alignT]

theorem opt_union_run_grad (d : Dispatcher) {X Y : List (Term × Term)} (S : Term) (nX : X ≠ []) (nY : Y ≠ [])
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«opt_union/3» d (.map X) (.map Y) S =
      Elixir.Module.Types.Descr.«symmetrical_merge/3» d (.map (alignT X)) (.map (alignT Y))
        (.function false "Elixir.Module.Types.Descr" "-opt_union/3-anonymous-0-" 3 #[S]) := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, Erlang.erlang.«==/2», hX, hY, nX, nY, Erlang.maps.«put/3», alignT]

theorem GC.shape {a : Term} (ha : GC L a) : a = .atom "term" ∨ ∃ X, a = .map X := by
  rcases ha with (h | ⟨X, rfl, -⟩) | ⟨X, -, rfl, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨X, rfl⟩
  · exact Or.inr ⟨X, rfl⟩

theorem GC.static {X : List (Term × Term)} (hX : GC L (.map X)) (st : mapLookup X (.atom "dynamic") = none) :
    TC L (.map X) := by
  rcases hX with h | ⟨X', Dy, e, hD, -⟩
  · exact h
  · simp only [Term.map.injEq] at e; subst e; rw [st] at hD; cases hD

theorem upper_term : upper (.atom "term") = .atom "term" := rfl

theorem upper_nil : upper (.map []) = .map [] := rfl

/-- Unions hold the points of either type, at both bounds. -/
def USem (L : Level) (a b c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ denD a v ∨ denD b v) ∧ ∀ v : TP L, denD (upper c) v ↔ denD (upper a) v ∨ denD (upper b) v

theorem usem_term_l (a : Term) : USem L (.atom "term") a (.atom "term") :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem usem_term_r (a : Term) : USem L a (.atom "term") (.atom "term") :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem usem_nil_l (a : Term) : USem L (.map []) a a :=
  ⟨fun v => by simp [denD_nil], fun v => by simp [upper_nil, denD_nil]⟩

theorem usem_nil_r (a : Term) : USem L a (.map []) a :=
  ⟨fun v => by simp [denD_nil], fun v => by simp [upper_nil, denD_nil]⟩

theorem usem_tc {a b c : Term} (ha : TC L a) (hb : TC L b) (hc : TC L c)
    (sem : ∀ v : TP L, denD c v ↔ denD a v ∨ denD b v) : USem L a b c :=
  ⟨sem, by rw [upper_tc ha, upper_tc hb, upper_tc hc]; exact sem⟩

theorem union_nil_l (d : Dispatcher) (Y : List (Term × Term)) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.map []) (.map Y) = .ok (.map Y) := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»; simp [Erlang.erlang.«==/2»]

theorem union_nil_r (d : Dispatcher) (X : List (Term × Term)) :
    Elixir.Module.Types.Descr.«bare_union/2» d (.map X) (.map []) = .ok (.map X) := by
  unfold Elixir.Module.Types.Descr.«bare_union/2»
  by_cases h : X = [] <;> simp [Erlang.erlang.«==/2», h]

theorem opt_union_nil_l (d : Dispatcher) (Y : List (Term × Term)) (S : Term) :
    Elixir.Module.Types.Descr.«opt_union/3» d (.map []) (.map Y) S = .ok (.map Y) := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»; simp [Erlang.erlang.«==/2»]

theorem opt_union_nil_r (d : Dispatcher) (X : List (Term × Term)) (S : Term) :
    Elixir.Module.Types.Descr.«opt_union/3» d (.map X) (.map []) S = .ok (.map X) := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»
  by_cases h : X = [] <;> simp [Erlang.erlang.«==/2», h]

theorem dyn_isSome {X : List (Term × Term)} (st : ¬TC L (.map X)) (hX : GC L (.map X)) :
    (mapLookup X (.atom "dynamic")).isSome := by
  cases h : mapLookup X (.atom "dynamic")
  · exact absurd (hX.static h) st
  · rfl

theorem gc_union {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧ USem L a b c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, GC.tc tc_term, union_term_l _ _, usem_term_l _⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_term, union_term_r _ _, usem_term_r _⟩
  by_cases nX : X = []
  · subst nX; exact ⟨_, hb, union_nil_l _ _, usem_nil_l _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨_, ha, union_nil_r _ _, usem_nil_r _⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_union st.1 st.2 (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, usem_tc st.1 st.2 hc sem⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, lo, up, -⟩ := merge_aligned (bare_union_op (n := k + 1) (by omega))
    (bare_union_op (n := k) (by omega)) (bare_union_dyn _) ha hb
  exact ⟨c, hc, (union_run_grad _ nX nY g).trans run, lo, up⟩

theorem gc_opt_union {a b : Term} (ha : GC L a) (hb : GC L b) (S : List (Term × Term)) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧ USem L a b c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, GC.tc tc_term, opt_union_term_left _ _ _, usem_term_l _⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_term, opt_union_term_r _ _ _, usem_term_r _⟩
  by_cases nX : X = []
  · subst nX; exact ⟨_, hb, opt_union_nil_l _ _ _, usem_nil_l _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨_, ha, opt_union_nil_r _ _ _, usem_nil_r _⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_opt_union st.1 st.2 S (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, usem_tc st.1 st.2 hc sem⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, lo, up, -⟩ := merge_aligned (opt_union_op (n := k + 1) (by omega) S)
    (opt_union_dyn_op (n := k) (by omega) S) (fun x y => opt_union_dyn _ x y _) ha hb
  exact ⟨c, hc, (opt_union_run_grad _ _ nX nY g).trans run, lo, up⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Intersections of gradual types. -/

section
variable {L : Level}

/-- Field operations an intersection combines fields with: they keep the common points of their fields. -/
structure InterOp (L : Level) (n : Nat) (module name : String) (caps : Array Term)
    (f : Term → Term → Term → Except Exception Term) : Prop where
  call : ∀ q v₁ v₂, (D (n + 1)).pure (.function false module name 3 caps) #[q, v₁, v₂] = f q v₁ v₂
  spec : ∀ name x y, FC L name x → FC L name y → ∃ w, f (.atom name) x y = .ok w ∧
    (kept (.atom name, w) = Bool.true → FC L name w) ∧
    ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)

/-- Intersecting static types keeps their common points. -/
theorem inter_descr {n : Nat} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : InterOp L n module name caps f)
    {A B : List (Term × Term)} (sA : DC L A) (sB : DC L B) :
    ∃ I, Elixir.Module.Types.Descr.«symmetrical_intersection/3» (D (n + 1)) (.map A) (.map B)
        (.function false module name 3 caps) = .ok (.map I) ∧ DC L I ∧
      ∀ v : TP L, denD (.map I) v ↔ denD (.map A) v ∧ denD (.map B) v := by
  obtain ⟨I, run, look⟩ := intersect_gen n module name caps f op.call A B sA.atoms (fun q x y hx hy => by
    obtain ⟨k, -, rfl⟩ := sA.keys q (by simp [hx])
    obtain ⟨w, rw', -⟩ := op.spec k x y (sA.fields k x hx) (sB.fields k y hy)
    exact ⟨w, rw'⟩)
  have keysI : ∀ q, (mapLookup I q).isSome → (mapLookup A q).isSome := by
    intro q h
    cases hA : mapLookup A q with
    | none => rw [(look q).1 hA] at h; cases h
    | some _ => rfl
  obtain ⟨cI, sem, -⟩ := inter_gen (slh := False) sA sB f
    (fun k => ⟨(look _).1, (look _).2.1, fun x y w hx hy rw' => (look _).2.2 x y w hx hy rw'⟩) keysI
    (fun k x y fx fy => let ⟨w, rw', kw, sw⟩ := op.spec k x y fx fy; ⟨w, rw', fun h => ⟨kw h, False.elim⟩, sw⟩)
  exact ⟨I, run, cI, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

/-- Intersections of dynamic parts. -/
theorem dyn_inter_tc {n : Nat} {module name : String} {caps : Array Term}
    {f : Term → Term → Term → Except Exception Term} (op : InterOp L n module name caps f)
    {a b : Term} (ha : TC L a) (hb : TC L b) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«dynamic_intersection/3» (D (n + 1)) a b (.function false module name 3 caps) =
      .ok c ∧ ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, by unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, by unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl,
      fun v => by simp [denD_term]⟩
  obtain ⟨I, run, sI, sem⟩ := inter_descr op sA sB
  refine ⟨_, Or.inr ⟨I, rfl, sI⟩, ?_, sem⟩
  unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»
  simpa [unfold_map] using run

/-- The dynamic field of an intersection: dropped when empty. -/
def dynZero : Term → Term
  | .map [] => .integer 0
  | c => c

theorem bare_inter_dyn (d : Dispatcher) {x y c : Term}
    (run : Elixir.Module.Types.Descr.«dynamic_intersection/3» d x y
      (.function false "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) = .ok c) (hc : TC L c) :
    Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "dynamic") x y = .ok (dynZero c) := by
  unfold Elixir.Module.Types.Descr.«bare_intersection/3»
  rcases hc with rfl | ⟨C, rfl, -⟩
  · have c : Term.compare (Term.fuel (.atom "term") (.map [])) (.atom "term") (.map []) ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    simp [run, Erlang.erlang.«==/2», dynZero, c]
  · cases C <;> simp [run, Erlang.erlang.«==/2», dynZero]

theorem opt_inter_dyn (d : Dispatcher) {x y c S : Term}
    (run : Elixir.Module.Types.Descr.«dynamic_intersection/3» d x y
      (.function false "Elixir.Module.Types.Descr" "-opt_intersection/4-fun-0-" 3 #[S]) = .ok c) (hc : TC L c) :
    Elixir.Module.Types.Descr.«opt_intersection/4» d (.atom "dynamic") x y S = .ok (dynZero c) := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/4»
  rcases hc with rfl | ⟨C, rfl, -⟩
  · have c : Term.compare (Term.fuel (.atom "term") (.map [])) (.atom "term") (.map []) ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    simp [run, Erlang.erlang.«==/2», dynZero, c]
  · cases C <;> simp [run, Erlang.erlang.«==/2», dynZero]

/-- Intersections hold the common points of the types, at both bounds. -/
def ISem (L : Level) (a b c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ denD a v ∧ denD b v) ∧ ∀ v : TP L, denD (upper c) v ↔ denD (upper a) v ∧ denD (upper b) v

/-- Intersecting aligned gradual types intersects their fields and their upper bounds. When the upper bounds do not
meet, the dynamic part is dropped, and so are the points of the fields, which the upper bounds include. -/
theorem inter_aligned {n : Nat} {module name module' name' : String} {caps caps' : Array Term}
    {f f' : Term → Term → Term → Except Exception Term} (op : InterOp L (n + 1) module name caps f)
    (op' : InterOp L n module' name' caps' f')
    (dyn : ∀ x y c, Elixir.Module.Types.Descr.«dynamic_intersection/3» (D (n + 1)) x y
      (.function false module' name' 3 caps') = .ok c → TC L c → f (.atom "dynamic") x y = .ok (dynZero c))
    {X Y : List (Term × Term)} (hX : GC L (.map X)) (hY : GC L (.map Y)) :
    ∃ c, GC L c ∧
      Elixir.Module.Types.Descr.«symmetrical_intersection/3» (D (n + 2)) (.map (alignT X)) (.map (alignT Y))
        (.function false module name 3 caps) = .ok c ∧ ISem L (.map X) (.map Y) c ∧
      ∃ I, c = .map I ∧ InterL f (rmDyn X) (rmDyn Y) (rmDyn I) ∧
        ((mapLookup I (.atom "dynamic") = none ∧ ∀ v : TP L, ¬denD (upper c) v) ∨
          Elixir.Module.Types.Descr.«dynamic_intersection/3» (D (n + 1))
            (upper (.map X)) (upper (.map Y)) (.function false module' name' 3 caps') = .ok (upper c)) := by
  obtain ⟨dX, sX, eX⟩ := align_gc hX
  obtain ⟨dY, sY, eY⟩ := align_gc hY
  obtain ⟨Di, ti, ri, si⟩ := dyn_inter_tc op' hX.up_tc hY.up_tc
  have rD := dyn _ _ _ ri ti
  obtain ⟨I, run, look⟩ := intersect_gen (n + 1) module name caps f op.call (alignT X) (alignT Y)
    (rmDyn_atoms sX) (fun q x y hx hy => by
      by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
      · obtain rfl := (compareExact_eq_atom q _).mp e
        rw [dX] at hx; rw [dY] at hy; cases hx; cases hy
        exact ⟨_, rD⟩
      · have hx' : mapLookup (rmDyn (alignT X)) q = some x := by rw [lookup_rmDyn, ite_eq_right e]; exact hx
        have hy' : mapLookup (rmDyn (alignT Y)) q = some y := by rw [lookup_rmDyn, ite_eq_right e]; exact hy
        obtain ⟨k, -, rfl⟩ := sX.keys q (by simp [hx'])
        obtain ⟨w, rw', -⟩ := op.spec k x y (sX.fields k x hx') (sY.fields k y hy')
        exact ⟨w, rw'⟩)
  have lookR : ∀ k, (mapLookup (rmDyn (alignT X)) (.atom k) = none → mapLookup (rmDyn I) (.atom k) = none) ∧
      (mapLookup (rmDyn (alignT Y)) (.atom k) = none → mapLookup (rmDyn I) (.atom k) = none) ∧
      (∀ x y w, mapLookup (rmDyn (alignT X)) (.atom k) = some x → mapLookup (rmDyn (alignT Y)) (.atom k) = some y →
        f (.atom k) x y = .ok w → mapLookup (rmDyn I) (.atom k) = keptO k w) := by
    intro k
    simp only [lookup_rmDyn]
    by_cases e : compareExact (fuel (.atom k) (.atom "dynamic")) (.atom k) (.atom "dynamic") = .eq
    · simp [e]
    · simp only [e, ite_false]; exact ⟨(look _).1, (look _).2.1, fun x y w hx hy rw' => (look _).2.2 x y w hx hy rw'⟩
  have keysI : ∀ q, (mapLookup (rmDyn I) q).isSome → (mapLookup (rmDyn (alignT X)) q).isSome := by
    intro q h
    simp only [lookup_rmDyn] at h ⊢
    by_cases e : compareExact (fuel q (.atom "dynamic")) q (.atom "dynamic") = .eq
    · simp [e] at h
    · simp only [e, ite_false] at h ⊢
      cases hA : mapLookup (alignT X) q with
      | none => rw [(look q).1 hA] at h; cases h
      | some _ => rfl
  have interL : InterL f (rmDyn X) (rmDyn Y) (rmDyn I) := by
    rw [← rmDyn_alignT X, ← rmDyn_alignT Y]; exact ⟨lookR, keysI⟩
  obtain ⟨cI, sem, -⟩ := inter_gen (slh := False) sX sY f lookR keysI
    (fun k x y fx fy => let ⟨w, rw', kw, sw⟩ := op.spec k x y fx fy; ⟨w, rw', fun h => ⟨kw h, False.elim⟩, sw⟩)
  have lo : ∀ v : TP L, denD (.map I) v ↔ denD (.map X) v ∧ denD (.map Y) v := fun v => by
    rw [← denD_rmDyn I, ← eX, ← eY, ← denD_rmDyn (alignT X), ← denD_rmDyn (alignT Y)]
    simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]
  have dI := (look _).2.2 _ _ _ dX dY rD
  -- The upper bounds meet unless their intersection is the empty map.
  by_cases z : Di = .map []
  · subst z
    have none : mapLookup I (.atom "dynamic") = none := by rw [dI]; simp [dynZero, kept]
    have tI : TC L (.map I) := Or.inr ⟨I, rfl, by rw [← rmDyn_static none]; exact cI⟩
    have empty : ∀ v : TP L, ¬(denD (upper (.map X)) v ∧ denD (upper (.map Y)) v) := fun v h =>
      denD_nil v ((si v).mpr h)
    refine ⟨_, GC.tc tI, run, ⟨lo, fun v => ?_⟩, I, rfl, interL, Or.inl ⟨none, fun v h => ?_⟩⟩
    · rw [upper_tc tI, lo]
      exact ⟨fun h => absurd ⟨hX.inv v h.1, hY.inv v h.2⟩ (empty v), fun h => absurd h (empty v)⟩
    · rw [upper_tc tI, lo] at h
      exact empty v ⟨hX.inv v h.1, hY.inv v h.2⟩
  · have kD : dynZero Di = Di := by
      rcases ti with rfl | ⟨C, rfl, -⟩
      · rfl
      · cases C
        · exact absurd rfl z
        · rfl
    have keep : kept (.atom "dynamic", Di) = Bool.true := by
      rcases ti with rfl | ⟨C, rfl, -⟩
      · simp [kept]
      · simp [kept]
    have hD : mapLookup I (.atom "dynamic") = some Di := by rw [dI, kD]; simp [keep]
    refine ⟨_, Or.inr ⟨I, Di, rfl, hD, ti, cI, fun v h => ?_⟩, run, ⟨lo, fun v => by rw [upper_dyn hD, si]⟩,
      I, rfl, interL, Or.inr (by rw [upper_dyn hD]; exact ri)⟩
    rw [si]
    obtain ⟨h₁, h₂⟩ := (lo v).mp h
    exact ⟨hX.inv v h₁, hY.inv v h₂⟩

theorem bare_inter_op {n : Nat} (hm : L.K + 12 ≤ n) :
    InterOp L n "Elixir.Module.Types.Descr" "bare_intersection" #[]
      (Elixir.Module.Types.Descr.«bare_intersection/3» (D n)) where
  call := fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure n q v₁ v₂
  spec := fun _ _ _ fx fy =>
    let ⟨w, rw', k, sw⟩ := fieldC_inter (tks L) (tfc L) (by omega) fx fy; ⟨w, rw', fun h => (k h).1, sw⟩

theorem opt_inter_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    InterOp L n "Elixir.Module.Types.Descr" "-opt_intersection/3-anonymous-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_intersection/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_intersection/3-anonymous-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_inter (tks L) (tfc L) (by omega) fx fy S

theorem opt_inter_dyn_op {n : Nat} (hm : L.K + 12 ≤ n) (S : List (Term × Term)) :
    InterOp L n "Elixir.Module.Types.Descr" "-opt_intersection/4-fun-0-" #[.map S]
      (fun q x y => Elixir.Module.Types.Descr.«opt_intersection/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_intersection/4-fun-0-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_inter (tks L) (tfc L) (by omega) fx fy S

theorem inter_run_grad (d : Dispatcher) {X Y : List (Term × Term)}
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«bare_intersection/2» d (.map X) (.map Y) =
      Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map (alignT X)) (.map (alignT Y))
        (.function false "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) := by
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, hX, hY, Erlang.maps.«put/3», alignT]

theorem opt_inter_run_grad (d : Dispatcher) {X Y : List (Term × Term)} (S : Term)
    (g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«opt_intersection/3» d (.map X) (.map Y) S =
      Elixir.Module.Types.Descr.«symmetrical_intersection/3» d (.map (alignT X)) (.map (alignT Y))
        (.function false "Elixir.Module.Types.Descr" "-opt_intersection/3-anonymous-0-" 3 #[S]) := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/3»
  cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> rw [hX, hY] at g <;>
    simp at g <;>
    simp [getMapKeys_single, hX, hY, Erlang.maps.«put/3», alignT]

theorem isem_term_l (a : Term) : ISem L (.atom "term") a a :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem isem_term_r (a : Term) : ISem L a (.atom "term") a :=
  ⟨fun v => by simp [denD_term], fun v => by simp [upper_term, denD_term]⟩

theorem isem_tc {a b c : Term} (ha : TC L a) (hb : TC L b) (hc : TC L c)
    (sem : ∀ v : TP L, denD c v ↔ denD a v ∧ denD b v) : ISem L a b c :=
  ⟨sem, by rw [upper_tc ha, upper_tc hb, upper_tc hc]; exact sem⟩

/-- Intersections of the dynamic parts of gradual types intersect them as static types. -/
theorem dyn_inter_bare (d : Dispatcher) {a b : Term} (ha : TC L a) (hb : TC L b) :
    Elixir.Module.Types.Descr.«dynamic_intersection/3» d a b
      (.function false "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) =
        Elixir.Module.Types.Descr.«bare_intersection/2» d a b := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [inter_term_left]; unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [inter_term_right]; unfold Elixir.Module.Types.Descr.«dynamic_intersection/3»; rfl
  unfold Elixir.Module.Types.Descr.«dynamic_intersection/3» Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, sA.static, sB.static]

/-- Intersections of gradual types, whose upper bound is empty or the intersection of the upper bounds. -/
theorem gc_inter {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧ ISem L a b c ∧
      ((∀ v : TP L, ¬denD (upper c) v) ∨ ∃ j, m ≤ j + 1 ∧
        Elixir.Module.Types.Descr.«bare_intersection/2» (D j) (upper a) (upper b) = .ok (upper c)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, hb, inter_term_left _ _, isem_term_l _, Or.inr ⟨k + 2, by omega, by rw [upper_term]; exact inter_term_left _ _⟩⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, ha, inter_term_right _ _, isem_term_r _, Or.inr ⟨k + 2, by omega, by rw [upper_term]; exact inter_term_right _ _⟩⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_inter st.1 st.2 (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, isem_tc st.1 st.2 hc sem,
      Or.inr ⟨k + 2, by omega, by rw [upper_tc st.1, upper_tc st.2, upper_tc hc]; exact run⟩⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, sem, up⟩ := inter_aligned (bare_inter_op (n := k + 1) (by omega))
    (bare_inter_op (n := k) (by omega)) (fun _ _ _ r t => bare_inter_dyn _ r t) ha hb
  obtain ⟨I, rfl, -, up⟩ := up
  refine ⟨_, hc, (inter_run_grad _ g).trans run, sem, ?_⟩
  rcases up with ⟨-, up⟩ | up
  · exact Or.inl up
  · exact Or.inr ⟨k + 1, by omega, by rw [← dyn_inter_bare _ ha.up_tc hb.up_tc]; exact up⟩

theorem gc_opt_inter {a b : Term} (ha : GC L a) (hb : GC L b) (S : List (Term × Term)) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧ ISem L a b c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, hb, opt_inter_term_l _ _ _, isem_term_l _⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, ha, opt_inter_term_r _ _ _, isem_term_r _⟩
  by_cases st : TC L (.map X) ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_opt_inter st.1 st.2 S (m := k + 2) (by omega)
    exact ⟨c, GC.tc hc, run, isem_tc st.1 st.2 hc sem⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sX : TC L (.map X)
    · exact Or.inr (dyn_isSome (fun h => st ⟨sX, h⟩) hb)
    · exact Or.inl (dyn_isSome sX ha)
  obtain ⟨c, hc, run, sem, -⟩ := inter_aligned (opt_inter_op (n := k + 1) (by omega) S)
    (opt_inter_dyn_op (n := k) (by omega) S) (fun _ _ _ r t => opt_inter_dyn _ r t) ha hb
  exact ⟨c, hc, (opt_inter_run_grad _ _ g).trans run, sem⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Differences of gradual types. -/

section
variable {L : Level}

/-- Field operations a difference removes fields with: they keep the points of the first field outside the second. -/
structure DiffOp (L : Level) (n : Nat) (fn : Term) (f : Term → Term → Term → Except Exception Term) : Prop where
  call : ∀ q v₁ v₂, (D (n + 1)).pure fn #[q, v₁, v₂] = f q v₁ v₂
  spec : ∀ name x y, FC L name x → FC L name y → ∃ w, f (.atom name) x y = .ok w ∧
    (kept (.atom name, w) = Bool.true → FC L name w) ∧
    ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)

/-- Differences of static parts. -/
theorem dyn_diff_tc {n : Nat} {fn : Term} {f : Term → Term → Term → Except Exception Term} (op : DiffOp L n fn f)
    {a b : Term} (ha : TC L a) (hb : TC L b) :
    ∃ c, TC L c ∧ Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) a b fn = .ok c ∧
      ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · have c : Term.compare (Term.fuel (.atom "term") (.map [])) (.atom "term") (.map []) ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    refine ⟨_, tc_nil, ?_, fun v => by simp [denD_nil, denD_term]⟩
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», c]
  by_cases nB : B = []
  · subst nB
    refine ⟨a, ha, ?_, fun v => by simp [denD_nil]⟩
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2»]
  have left : ∃ A, DC L A ∧ (∀ v : TP L, denD a v ↔ denD (.map A) v) ∧
      Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) a (.map B) fn =
        Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) (.map A) (.map B) fn := by
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · obtain ⟨T, term, sT, -, all⟩ := termT L
      refine ⟨T, sT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩, ?_⟩
      unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
      simp [Erlang.erlang.«==/2», nB, term]
    · exact ⟨A, sA, fun v => Iff.rfl, rfl⟩
  obtain ⟨A, sA, eA, rA⟩ := left
  obtain ⟨O, fold, sO, dO, -⟩ := diff_gen (slh := False) n fn f sA sB op.call
    (fun k x y fx fy => let ⟨w, rw', kw, sw⟩ := op.spec k x y fx fy; ⟨w, rw', fun h => ⟨kw h, False.elim⟩, sw⟩)
  refine ⟨_, Or.inr ⟨O, rfl, sO⟩, ?_, fun v => ?_⟩
  · rw [rA]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», nB, Erlang.maps.«fold/3»]
    simpa using fold
  · rw [eA]
    simp only [denD_map, dO _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- The static part of a type, as `pop_dynamic/1` takes it. -/
def lower (a : Term) : Term :=
  match a with
  | .map X => .map (rmDyn X)
  | _ => a

theorem GC.low_tc {a : Term} (ha : GC L a) : TC L (lower a) := by
  rcases ha with (rfl | ⟨X, rfl, sX⟩) | ⟨X, -, rfl, -, -, sX, -⟩
  · exact tc_term
  · exact Or.inr ⟨_, rfl, by rw [rmDyn_static sX.static]; exact sX⟩
  · exact Or.inr ⟨_, rfl, sX⟩

theorem denD_lower (a : Term) (v : TP L) : denD (lower a) v ↔ denD a v := by
  cases a <;> simp [lower, denD_rmDyn]

theorem pop_dyn (Y : List (Term × Term)) :
    Elixir.Map.«pop/3» (.map Y) (.atom "dynamic") (.map Y) = .ok (.tuple #[upper (.map Y), lower (.map Y)]) := by
  cases h : mapLookup Y (.atom "dynamic") <;>
    simp [Elixir.Map.«pop/3», Erlang.maps.«take/2», h, upper, lower, rmDyn]
  rw [← rmDyn, rmDyn_static h]

/-- Differences with a gradual type subtract the upper bound from the static part, and the static part from the
upper bound. -/
theorem diff_run_grad (d : Dispatcher) {a : Term} {Y : List (Term × Term)} (nY : Y ≠ [])
    (ha : a = .atom "term" ∨ ∃ X, a = .map X)
    (g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map Y) = (do
      let dp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (upper a) (lower (.map Y))
        (.function false "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
      let sp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (lower a) (upper (.map Y))
        (.function false "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
      Elixir.Module.Types.Descr.«put_dynamic/2» sp dp) := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  rcases ha with rfl | ⟨X, rfl⟩
  · cases hY : mapLookup Y (.atom "dynamic") <;> simp [hY] at g
    simp [Erlang.erlang.«==/2», nY, unfold_map, hY, Erlang.erlang.«is_map_key/2», any_key, pop_dyn]
    rfl
  · have c : Term.compare (Term.fuel (.map X) (.atom "term")) (.map X) (.atom "term") ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    have gr : ((mapLookup X (.atom "dynamic")).isSome || (mapLookup Y (.atom "dynamic")).isSome) = Bool.true := by
      rcases g with ⟨X', e, h⟩ | h
      · simp only [Term.map.injEq] at e; subst e; simp [h]
      · simp [h]
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp [hX, hY] at gr <;>
      simp [Erlang.erlang.«==/2», nY, c, unfold_map, hX, hY, Erlang.erlang.«is_map_key/2», any_key,
        pop_dyn, Lynx.Except.orElse]

theorem opt_diff_run_grad (d : Dispatcher) {a : Term} {Y : List (Term × Term)} (S : Term) (nY : Y ≠ [])
    (ha : a = .atom "term" ∨ ∃ X, a = .map X)
    (g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome) :
    Elixir.Module.Types.Descr.«opt_difference/3» d a (.map Y) S = (do
      let dp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (upper a) (lower (.map Y))
        (.function false "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-1-" 3 #[S])
      let sp ← Elixir.Module.Types.Descr.«dynamic_difference/3» d (lower a) (upper (.map Y))
        (.function false "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-2-" 3 #[S])
      Elixir.Module.Types.Descr.«put_dynamic/2» sp dp) := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  rcases ha with rfl | ⟨X, rfl⟩
  · cases hY : mapLookup Y (.atom "dynamic") <;> simp [hY] at g
    simp [Erlang.erlang.«==/2», nY, unfold_map, hY, Erlang.erlang.«is_map_key/2», any_key, pop_dyn]
    rfl
  · have c : Term.compare (Term.fuel (.map X) (.atom "term")) (.map X) (.atom "term") ≠ .eq := by rw [compare_step]; simp [Compare.compareStep]
    have gr : ((mapLookup X (.atom "dynamic")).isSome || (mapLookup Y (.atom "dynamic")).isSome) = Bool.true := by
      rcases g with ⟨X', e, h⟩ | h
      · simp only [Term.map.injEq] at e; subst e; simp [h]
      · simp [h]
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp [hX, hY] at gr <;>
      simp [Erlang.erlang.«==/2», nY, c, unfold_map, hX, hY, Erlang.erlang.«is_map_key/2», any_key,
        pop_dyn, Lynx.Except.orElse]

/-- Top-level types equal by comparison hold the same points. -/
theorem tc_congr {a b : Term} (ha : TC L a) (hb : TC L b) (e : Term.compare (Term.fuel a b) a b = .eq) (v : TP L) :
    denD a v ↔ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩ <;> rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact Iff.rfl
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · simp only [denD_map, descr_congr (tks L) (tfc L) sA sB e v.1.1 v.1.2 v.2.2]

/-- Putting a dynamic part that includes the static one: a gradual type with these bounds. -/
theorem put_dyn_sem {sp dp : Term} (hs : TC L sp) (hd : TC L dp) (inv : ∀ v : TP L, denD sp v → denD dp v) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«put_dynamic/2» sp dp = .ok c ∧
      (∀ v : TP L, denD c v ↔ denD sp v) ∧ ∀ v : TP L, denD (upper c) v ↔ denD dp v := by
  rcases hs with rfl | ⟨S, rfl, sS⟩
  · exact ⟨_, GC.tc tc_term, by unfold Elixir.Module.Types.Descr.«put_dynamic/2»; rfl, fun v => Iff.rfl,
      fun v => ⟨fun _ => inv v (denD_term v), fun _ => denD_term v⟩⟩
  have tS : TC L (.map S) := Or.inr ⟨S, rfl, sS⟩
  by_cases e₁ : Term.compare (Term.fuel (.map S) dp) (.map S) dp = .eq
  · refine ⟨_, GC.tc tS, ?_, fun v => Iff.rfl, fun v => by rw [upper_tc tS]; exact tc_congr tS hd e₁ v⟩
    unfold Elixir.Module.Types.Descr.«put_dynamic/2»
    simp [Erlang.erlang.«==/2», e₁]
  by_cases e₂ : Term.compare (Term.fuel dp (.map [])) dp (.map []) = .eq
  · have none : ∀ v : TP L, ¬denD dp v := fun v h => denD_nil v ((tc_congr hd tc_nil e₂ v).mp h)
    refine ⟨_, GC.tc tc_nil, ?_, fun v => ⟨fun h => absurd h (denD_nil v), fun h => absurd (inv v h) (none v)⟩,
      fun v => ⟨fun h => absurd h (denD_nil v), fun h => absurd h (none v)⟩⟩
    unfold Elixir.Module.Types.Descr.«put_dynamic/2»
    simp [Erlang.erlang.«==/2», e₁, e₂]
  have st := sS.static
  have hD : mapLookup ((.atom "dynamic", dp) :: S) (.atom "dynamic") = some dp := by simp [mapLookup]
  have same : ∀ v : TP L, denD (.map ((.atom "dynamic", dp) :: S)) v ↔ denD (.map S) v := fun v => by
    rw [← denD_rmDyn, rmDyn_cons_dyn, rmDyn_static st]
  refine ⟨_, Or.inr ⟨_, dp, rfl, hD, hd, by rw [rmDyn_cons_dyn, rmDyn_static st]; exact sS,
    fun v h => inv v ((same v).mp h)⟩, ?_, same, fun v => by rw [upper_dyn hD]⟩
  unfold Elixir.Module.Types.Descr.«put_dynamic/2»
  simp [Erlang.erlang.«==/2», e₁, e₂, Erlang.maps.«put/3»]

/-- Differences hold the points of the first type outside the second, crossing the bounds. -/
def DSem (L : Level) (a b c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD (upper b) v) ∧
    ∀ v : TP L, denD (upper c) v ↔ denD (upper a) v ∧ ¬denD b v

theorem bare_diff_op {n : Nat} (hm : L.K + 13 ≤ n) :
    DiffOp L n (.function false "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
      (Elixir.Module.Types.Descr.«bare_difference/3» (D n)) where
  call := fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure n q v₁ v₂
  spec := fun _ _ _ fx fy =>
    let ⟨w, rw', k, sw⟩ := fieldC_diff (tks L) (tfc L) (by omega) fx fy; ⟨w, rw', fun h => (k h).1, sw⟩

theorem opt_diff_op₁ {n : Nat} (hm : L.K + 13 ≤ n) (S : List (Term × Term)) :
    DiffOp L n (.function false "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-1-" 3 #[.map S])
      (fun q x y => Elixir.Module.Types.Descr.«opt_difference/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-1-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_diff (tks L) (tfc L) (by omega) fx fy S

theorem opt_diff_op₂ {n : Nat} (hm : L.K + 13 ≤ n) (S : List (Term × Term)) :
    DiffOp L n (.function false "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-2-" 3 #[.map S])
      (fun q x y => Elixir.Module.Types.Descr.«opt_difference/4» (D n) q x y (.map S)) where
  call := fun q v₁ v₂ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-2-/3».pure]; rfl
  spec := fun _ _ _ fx fy => fieldC_opt_diff (tks L) (tfc L) (by omega) fx fy S

/-- The gradual difference: the dynamic part and the static part, put together. -/
theorem diff_grad {n : Nat} {fn₁ fn₂ : Term} {f₁ f₂ : Term → Term → Term → Except Exception Term}
    (op₁ : DiffOp L n fn₁ f₁) (op₂ : DiffOp L n fn₂ f₂) {a b : Term} (ha : GC L a) (hb : GC L b) :
    ∃ c, GC L c ∧ (do
      let dp ← Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) (upper a) (lower b) fn₁
      let sp ← Elixir.Module.Types.Descr.«dynamic_difference/3» (D (n + 2)) (lower a) (upper b) fn₂
      Elixir.Module.Types.Descr.«put_dynamic/2» sp dp) = .ok c ∧ DSem L a b c := by
  obtain ⟨dp, tdp, rdp, sdp⟩ := dyn_diff_tc op₁ ha.up_tc hb.low_tc
  obtain ⟨sp, tsp, rsp, ssp⟩ := dyn_diff_tc op₂ ha.low_tc hb.up_tc
  obtain ⟨c, hc, rc, lo, up⟩ := put_dyn_sem tsp tdp fun v h => by
    rw [ssp, denD_lower] at h
    rw [sdp, denD_lower]
    exact ⟨ha.inv v h.1, fun h' => h.2 (hb.inv v h')⟩
  refine ⟨c, hc, by simp [rdp, rsp, rc], fun v => ?_, fun v => ?_⟩
  · rw [lo, ssp, denD_lower]
  · rw [up, sdp, denD_lower]

theorem diff_nil_r (d : Dispatcher) (a : Term) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map []) = .ok a := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»; simp [Erlang.erlang.«==/2»]

theorem opt_diff_nil_r (d : Dispatcher) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» d a (.map []) S = .ok a := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»; simp [Erlang.erlang.«==/2»]

theorem dsem_term_r (a : Term) : DSem L a (.atom "term") (.map []) :=
  ⟨fun v => by simp [denD_nil, upper_term, denD_term], fun v => by simp [upper_nil, denD_nil, denD_term]⟩

theorem dsem_nil_r (a : Term) : DSem L a (.map []) a :=
  ⟨fun v => by simp [denD_nil, upper_nil], fun v => by simp [denD_nil]⟩

theorem dsem_tc {a b c : Term} (ha : TC L a) (hb : TC L b) (hc : TC L c)
    (sem : ∀ v : TP L, denD c v ↔ denD a v ∧ ¬denD b v) : DSem L a b c :=
  ⟨by rw [upper_tc hb]; exact sem, by rw [upper_tc ha, upper_tc hc]; exact sem⟩

theorem gc_diff {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c ∧ DSem L a b c := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_nil, diff_term_right _ _, dsem_term_r _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨a, ha, diff_nil_r _ _, dsem_nil_r _⟩
  by_cases st : TC L a ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_diff st.1 st.2 (m := n + 2) (by omega)
    exact ⟨c, GC.tc hc, run, dsem_tc st.1 st.2 hc sem⟩
  have g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sY : TC L (.map Y)
    · rcases ha.shape with rfl | ⟨X, rfl⟩
      · exact absurd ⟨tc_term, sY⟩ st
      · exact Or.inl ⟨X, rfl, dyn_isSome (fun h => st ⟨h, sY⟩) ha⟩
    · exact Or.inr (dyn_isSome sY hb)
  obtain ⟨c, hc, run, sem⟩ := diff_grad (bare_diff_op (n := n) (by omega)) (bare_diff_op (n := n) (by omega)) ha hb
  exact ⟨c, hc, (diff_run_grad _ nY ha.shape g).trans run, sem⟩

theorem gc_opt_diff {a b : Term} (ha : GC L a) (hb : GC L b) (S : List (Term × Term)) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧ DSem L a b c := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, GC.tc tc_nil, difference_term_term _ _ _, dsem_term_r _⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨a, ha, opt_diff_nil_r _ _ _, dsem_nil_r _⟩
  by_cases st : TC L a ∧ TC L (.map Y)
  · obtain ⟨c, hc, run, sem⟩ := tc_opt_diff st.1 st.2 S (m := n + 2) (by omega)
    exact ⟨c, GC.tc hc, run, dsem_tc st.1 st.2 hc sem⟩
  have g : (∃ X, a = .map X ∧ (mapLookup X (.atom "dynamic")).isSome) ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    by_cases sY : TC L (.map Y)
    · rcases ha.shape with rfl | ⟨X, rfl⟩
      · exact absurd ⟨tc_term, sY⟩ st
      · exact Or.inl ⟨X, rfl, dyn_isSome (fun h => st ⟨h, sY⟩) ha⟩
    · exact Or.inr (dyn_isSome sY hb)
  obtain ⟨c, hc, run, sem⟩ := diff_grad (opt_diff_op₁ (n := n) (by omega) S) (opt_diff_op₂ (n := n) (by omega) S) ha hb
  exact ⟨c, hc, (opt_diff_run_grad _ _ nY ha.shape g).trans run, sem⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Negations of gradual types, and subtyping of gradual types by both bounds. -/

section
variable {L : Level}

/-- Negations swap the bounds. -/
def GNSem (L : Level) (a c : Term) : Prop :=
  (∀ v : TP L, denD c v ↔ ¬denD (upper a) v) ∧ ∀ v : TP L, denD (upper c) v ↔ ¬denD a v

theorem nsem_of_dsem {a c : Term} (h : DSem L (.atom "term") a c) : GNSem L a c :=
  ⟨fun v => by simp [h.1 v, denD_term], fun v => by simp [h.2 v, upper_term, denD_term]⟩

theorem nsem_term : GNSem L (.atom "term") (.map []) :=
  ⟨fun v => by simp [denD_nil, upper_term, denD_term], fun v => by simp [upper_nil, denD_nil, denD_term]⟩

theorem gc_neg {a : Term} (ha : GC L a) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c ∧ GNSem L a c := by
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, GC.tc tc_nil, by simp [Elixir.Module.Types.Descr.«bare_negation/1»],
      nsem_term⟩
  obtain ⟨c, hc, run, sem⟩ := gc_diff (GC.tc tc_term) ha hm
  exact ⟨c, hc, by simpa [Elixir.Module.Types.Descr.«bare_negation/1», Elixir.Module.Types.Descr.«term/0»] using run,
    nsem_of_dsem sem⟩

theorem gc_opt_neg {a : Term} (ha : GC L a) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok c ∧ GNSem L a c := by
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · refine ⟨_, GC.tc tc_nil, ?_, nsem_term⟩
    rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
    simp
  obtain ⟨c, hc, run, sem⟩ := gc_opt_diff (GC.tc tc_term) ha [] hm
  refine ⟨c, hc, ?_, nsem_of_dsem sem⟩
  rw [Elixir.Module.Types.Descr.«opt_negation/1».eq_def]
  simpa [Elixir.Module.Types.Descr.«opt_difference/2», Elixir.Module.Types.Descr.«term/0», unfold_map] using run

theorem gc_opt_union2 {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok c ∧ USem L a b c := by
  simpa [Elixir.Module.Types.Descr.«opt_union/2»] using gc_opt_union ha hb [] hm

theorem gc_opt_inter2 {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 14 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok c ∧ ISem L a b c := by
  simpa [Elixir.Module.Types.Descr.«opt_intersection/2»] using gc_opt_inter ha hb [] hm

theorem gc_opt_diff2 {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 15 ≤ m) :
    ∃ c, GC L c ∧ Elixir.Module.Types.Descr.«opt_difference/2» (D m) a b = .ok c ∧ DSem L a b c := by
  simpa [Elixir.Module.Types.Descr.«opt_difference/2»] using gc_opt_diff ha hb [] hm

/-- Each field of an included static type is covered by the other type. -/
theorem keysub_complete {m : Nat} (hm : L.K + 13 ≤ m) {A B : List (Term × Term)} (sA : DC L A) (sB : DC L B)
    (incl : ∀ v : TP L, denD (.map A) v → denD (.map B) v) : ∀ e ∈ mapEntries A, KeySub (D m) B e.1 e.2 := by
  intro e me
  have hx := mapLookup_of_mem_mapEntries me
  obtain ⟨name, mem, key⟩ := sA.keys e.1 (by simp [hx])
  rw [key] at hx ⊢
  have fx := sA.fields name e.2 hx
  have none : ∀ w, FC L name w → (∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (some w) p = Bool.false) →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) w (.map []) = .ok (.atom "true") :=
    fun w fw empty => fieldC_empty_none (tks L) (tfc L) (show L.K + 11 ≤ m by omega) fw (fun _ => trivial) empty
  have inc : ∀ p, PtOkD L.E L.den L.tl (FVal L.E L.den) name p → dn name (some e.2) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true := fun p ok h =>
    (denD_map ⟨(name, p), mem, ok⟩).mp (incl ⟨(name, p), mem, ok⟩ ((denD_map _).mpr (by rw [hx]; exact h)))
  cases hy : mapLookup B (.atom name) with
  | none =>
    refine Or.inr ⟨hy, none _ fx fun p ok => ?_⟩
    cases h : dn name (some e.2) p
    · rfl
    · have := inc p ok h; rw [hy, dn_none] at this; cases this
  | some y =>
    obtain ⟨w, run, k, sem⟩ := fieldC_diff (tks L) (tfc L) (show L.K + 11 + 2 ≤ m by omega) fx (sB.fields name y hy)
    refine Or.inl ⟨y, w, hy, run, ?_⟩
    cases kw : kept (.atom name, w)
    · rcases kept_of_ne kw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (none w (k kw).1 fun p ok => ?_))
      have := sem p ok
      rw [keptO_true kw] at this
      rw [this]
      cases h : dn name (some e.2) p
      · rfl
      · have := inc p ok h; rw [hy] at this; simp [this]

/-- The subtraction check of `subtype?/2` is complete on top-level types. -/
theorem esub_complete {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (incl : ∀ v : TP L, denD a v → denD b v) :
    Elixir.Module.Types.Descr.«empty_difference_subtype?/3» (D m) a b (.map []) = .ok (.atom "true") := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · simp [getMapKeys]
    · simp [getMapKeys_single, sA.static]
  have left : ∃ A, DC L A ∧ (∀ v : TP L, denD a v ↔ denD (.map A) v) ∧
      Elixir.Module.Types.Descr.«empty_difference_subtype?/3» (D m) a (.map B) (.map []) =
        (do
          let it ← Erlang.maps.«next/1» (Term.list ((mapEntries A).map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_empty_difference_subtype?/3» (D m) it (.map B) (.map [])) := by
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · obtain ⟨T, term, sT, -, all⟩ := termT L
      refine ⟨T, sT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩, ?_⟩
      simp [getMapKeys, term, Erlang.maps.«iterator/1»]
    · exact ⟨A, sA, fun v => Iff.rfl, by simp [getMapKeys_single, sA.static, Erlang.maps.«iterator/1»]⟩
  obtain ⟨A, sA, eA, rA⟩ := left
  rw [rA]
  exact iterator_sub (D m) B (mapEntries A) (keysub_complete hm sA sB fun v h => incl v ((eA v).mpr h))

theorem sstatic_complete {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (incl : ∀ v : TP L, denD a v → denD b v) :
    Elixir.Module.Types.Descr.«subtype_static?/2» (D m) a b = .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«subtype_static?/2»
  by_cases same : compareExact (fuel b a) b a = .eq
  · simp [Erlang.erlang.«=:=/2», same]
  · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»,
      esub_complete ha hb hm incl]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Subtyping and equality of gradual types are complete for both bounds. -/

section
variable {L : Level}

theorem map_get_dyn {X : List (Term × Term)} {Dx : Term} (h : mapLookup X (.atom "dynamic") = some Dx) :
    Elixir.Map.«get/2» (.map X) (.atom "dynamic") = .ok Dx := by
  simp [Elixir.Map.«get/2», Elixir.Map.«get/3», getMapKeys_single, h]

theorem tc_rmDyn {X : List (Term × Term)} (hX : GC L (.map X)) : TC L (.map (rmDyn X)) := hX.low_tc

/-- Gradual subtyping on maps: compares the bounds. -/
theorem gc_sub_maps {X Y : List (Term × Term)} (hX : GC L (.map X)) (hY : GC L (.map Y)) {m : Nat} (hm : L.K + 13 ≤ m)
    (lo : ∀ v : TP L, denD (.map X) v → denD (.map Y) v)
    (up : ∀ v : TP L, denD (upper (.map X)) v → denD (upper (.map Y)) v) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) = .ok (.atom "true") := by
  have lo' : ∀ v : TP L, denD (.map (rmDyn X)) v → denD (.map (rmDyn Y)) v := fun v h =>
    (denD_rmDyn Y v).mpr (lo v ((denD_rmDyn X v).mp h))
  cases hx : mapLookup X (.atom "dynamic") with
  | none =>
    have tX := hX.static hx
    cases hy : mapLookup Y (.atom "dynamic") with
    | none => exact tc_sub tX (hY.static hy) hm lo
    | some Dy =>
      have run := sstatic_complete tX (tc_rmDyn hY) hm fun v h => by
        have := lo' v; rw [rmDyn_static hx] at this; exact this h
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», Erlang.maps.«remove/2»]
      simpa [rmDyn] using run
  | some Dx =>
    cases hy : mapLookup Y (.atom "dynamic") with
    | none =>
      have tY := hY.static hy
      have run := sstatic_complete hX.up_tc tY hm fun v h => by
        have := up v; rw [upper_tc tY] at this; exact this h
      rw [upper_dyn hx] at run
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», map_get_dyn hx, run]
    | some Dy =>
      have tX := hX.up_tc; have tY := hY.up_tc
      rw [upper_dyn hx] at tX; rw [upper_dyn hy] at tY
      have r₁ := esub_complete tX tY hm fun v h => by
        have := up v; rw [upper_dyn hx, upper_dyn hy] at this; exact this h
      have r₂ := esub_complete (tc_rmDyn hX) (tc_rmDyn hY) hm lo'
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2»]
      unfold Elixir.Module.Types.Descr.«subtype_static?/2»
      by_cases same : compareExact (fuel (.map Y) (.map X)) (.map Y) (.map X) = .eq
      · simp [Erlang.erlang.«=:=/2», same]
      · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, hx, hy, r₁, Erlang.maps.«remove/2», Lynx.Except.andAlso]
        simpa [rmDyn] using r₂

/-- Gradual subtyping is complete for both bounds. -/
theorem gc_sub {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (lo : ∀ v : TP L, denD a v → denD b v) (up : ∀ v : TP L, denD (upper a) v → denD (upper b) v) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨T, term, sT, -, all⟩ := termT L
  have tT : GC L (.map T) := GC.tc (Or.inr ⟨T, rfl, sT⟩)
  have uT : upper (.map T) = .map T := upper_tc (Or.inr ⟨T, rfl, sT⟩)
  have left : ∃ X, GC L (.map X) ∧ (∀ v : TP L, denD a v ↔ denD (.map X) v) ∧
      (∀ v : TP L, denD (upper a) v ↔ denD (upper (.map X)) v) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) b := by
    rcases ha.shape with rfl | ⟨X, rfl⟩
    · exact ⟨T, tT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩,
        fun v => by rw [upper_term, uT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩, subtype_term_l term _ _⟩
    · exact ⟨X, ha, fun v => Iff.rfl, fun v => Iff.rfl, rfl⟩
  obtain ⟨X, hX, eX, uX, rX⟩ := left
  have right : ∃ Y, GC L (.map Y) ∧ (∀ v : TP L, denD b v ↔ denD (.map Y) v) ∧
      (∀ v : TP L, denD (upper b) v ↔ denD (upper (.map Y)) v) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) b =
        Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) := by
    rcases hb.shape with rfl | ⟨Y, rfl⟩
    · exact ⟨T, tT, fun v => ⟨fun _ => all v, fun _ => denD_term v⟩,
        fun v => by rw [upper_term, uT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩, subtype_term_r term _ _⟩
    · exact ⟨Y, hb, fun v => Iff.rfl, fun v => Iff.rfl, rfl⟩
  obtain ⟨Y, hY, eY, uY, rY⟩ := right
  rw [rX, rY]
  exact gc_sub_maps hX hY hm (fun v h => (eY v).mp (lo v ((eX v).mpr h)))
    (fun v h => (uY v).mp (up v ((uX v).mpr h)))

/-- Gradual equality is complete for both bounds. -/
theorem gc_equal {a b : Term} (ha : GC L a) (hb : GC L b) {m : Nat} (hm : L.K + 13 ≤ m)
    (lo : ∀ v : TP L, denD a v ↔ denD b v) (up : ∀ v : TP L, denD (upper a) v ↔ denD (upper b) v) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  have s₁ := gc_sub ha hb hm (fun v => (lo v).mp) (fun v => (up v).mp)
  have s₂ := gc_sub hb ha hm (fun v => (lo v).mpr) (fun v => (up v).mpr)
  by_cases c : Term.compare (Term.fuel a b) a b = .eq <;>
    simp [Elixir.Module.Types.Descr.«equal?/2», s₁, s₂, Lynx.Except.orElse, Lynx.Except.andAlso,
      Erlang.erlang.«==/2», c, Term.true, Term.false]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The laws on gradual types, at both bounds. -/

section
variable {L : Level} {m : Nat}

theorem gd_opt_de_morgan_union {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ u x nl nr y, Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) u = .ok x ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok nl ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) b = .ok nr ∧
      Elixir.Module.Types.Descr.«opt_intersection/2» (D m) nl nr = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_opt_union2 ha hb (m := m) (by omega)
  obtain ⟨x, hx, rx, sx⟩ := gc_opt_neg hu hm
  obtain ⟨nl, hnl, rnl, snl⟩ := gc_opt_neg ha hm
  obtain ⟨nr, hnr, rnr, snr⟩ := gc_opt_neg hb hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_inter2 hnl hnr (m := m) (by omega)
  exact ⟨u, x, nl, nr, y, ru, rx, rnl, rnr, ry, gc_equal hx hy (by omega)
    (fun v => by rw [sx.1, su.2, sy.1, snl.1, snr.1]; exact not_or)
    (fun v => by rw [sx.2, su.1, sy.2, snl.2, snr.2]; exact not_or)⟩

theorem gd_opt_de_morgan_inter {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ i x nl nr y, Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) i = .ok x ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok nl ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) b = .ok nr ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D m) nl nr = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si⟩ := gc_opt_inter2 ha hb (m := m) (by omega)
  obtain ⟨x, hx, rx, sx⟩ := gc_opt_neg hi hm
  obtain ⟨nl, hnl, rnl, snl⟩ := gc_opt_neg ha hm
  obtain ⟨nr, hnr, rnr, snr⟩ := gc_opt_neg hb hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_union2 hnl hnr (m := m) (by omega)
  exact ⟨i, x, nl, nr, y, ri, rx, rnl, rnr, ry, gc_equal hx hy (by omega)
    (fun v => by rw [sx.1, si.2, sy.1, snl.1, snr.1]; exact Classical.not_and_iff_not_or_not)
    (fun v => by rw [sx.2, si.1, sy.2, snl.2, snr.2]; exact Classical.not_and_iff_not_or_not)⟩

theorem gd_opt_inter_sub {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ i, Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i a = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i b = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si⟩ := gc_opt_inter2 ha hb hm
  exact ⟨i, ri, gc_sub hi ha (by omega) (fun v h => ((si.1 v).mp h).1) (fun v h => ((si.2 v).mp h).1),
    gc_sub hi hb (by omega) (fun v h => ((si.1 v).mp h).2) (fun v h => ((si.2 v).mp h).2)⟩

theorem gd_opt_union_sup {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u, Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a u = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) b u = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_opt_union2 ha hb hm
  exact ⟨u, ru, gc_sub ha hu (by omega) (fun v h => (su.1 v).mpr (Or.inl h)) (fun v h => (su.2 v).mpr (Or.inl h)),
    gc_sub hb hu (by omega) (fun v h => (su.1 v).mpr (Or.inr h)) (fun v h => (su.2 v).mpr (Or.inr h))⟩

theorem gd_inter_sub {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ i, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i a = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i b = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si, -⟩ := gc_inter ha hb hm
  exact ⟨i, ri, gc_sub hi ha (by omega) (fun v h => ((si.1 v).mp h).1) (fun v h => ((si.2 v).mp h).1),
    gc_sub hi hb (by omega) (fun v h => ((si.1 v).mp h).2) (fun v h => ((si.2 v).mp h).2)⟩

theorem gd_union_sup {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a u = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) b u = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb hm
  exact ⟨u, ru, gc_sub ha hu (by omega) (fun v h => (su.1 v).mpr (Or.inl h)) (fun v h => (su.2 v).mpr (Or.inl h)),
    gc_sub hb hu (by omega) (fun v h => (su.1 v).mpr (Or.inr h)) (fun v h => (su.2 v).mpr (Or.inr h))⟩

theorem gd_union_equal {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u w, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok w ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) u w = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb hm
  obtain ⟨w, hw, rw', sw⟩ := gc_opt_union2 ha hb hm
  exact ⟨u, w, ru, rw', gc_equal hu hw (by omega) (fun v => by rw [su.1, sw.1]) (fun v => by rw [su.2, sw.2])⟩

theorem gd_inter_equal {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ i j, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok j ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) i j = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si, -⟩ := gc_inter ha hb hm
  obtain ⟨j, hj, rj, sj⟩ := gc_opt_inter2 ha hb hm
  exact ⟨i, j, ri, rj, gc_equal hi hj (by omega) (fun v => by rw [si.1, sj.1]) (fun v => by rw [si.2, sj.2])⟩

theorem gd_distrib {t a b : Term} (ht : GC L t) (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u x y z w, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) t u = .ok x ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) t a = .ok y ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) t b = .ok z ∧
      Elixir.Module.Types.Descr.«bare_union/2» (D m) y z = .ok w ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x w = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb hm
  obtain ⟨x, hx, rx, sx, -⟩ := gc_inter ht hu hm
  obtain ⟨y, hy, ry, sy, -⟩ := gc_inter ht ha hm
  obtain ⟨z, hz, rz, sz, -⟩ := gc_inter ht hb hm
  obtain ⟨w, hw, rw', sw⟩ := gc_union hy hz hm
  exact ⟨u, x, y, z, w, ru, rx, ry, rz, rw', gc_equal hx hw (by omega)
    (fun v => by rw [sx.1, su.1, sw.1, sy.1, sz.1]; exact and_or_left)
    (fun v => by rw [sx.2, su.2, sw.2, sy.2, sz.2]; exact and_or_left)⟩

theorem gd_neg_equal {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ x y, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok x ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨x, hx, rx, sx⟩ := gc_neg ha hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_neg ha hm
  exact ⟨x, y, rx, ry, gc_equal hx hy (by omega) (fun v => by rw [sx.1, sy.1]) (fun v => by rw [sx.2, sy.2])⟩

theorem gd_diff_equal {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ x y, Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok x ∧
      Elixir.Module.Types.Descr.«opt_difference/2» (D m) a b = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨x, hx, rx, sx⟩ := gc_diff ha hb hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_diff2 ha hb hm
  exact ⟨x, y, rx, ry, gc_equal hx hy (by omega) (fun v => by rw [sx.1, sy.1]) (fun v => by rw [sx.2, sy.2])⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Types without function fields checked empty hold no points. -/

section
variable {L : Level}

/-- Emptiness is sound on top-level types, whose function types are arrows. -/
theorem tc_empty_sound {C : List (Term × Term)} (sC : DC L C) {m : Nat} (hm : L.K + 11 ≤ m)
    (h : Elixir.Module.Types.Descr.«empty?/1» (D m) (.map C) = .ok (.atom "true")) :
    ∀ v : TP L, ¬denD (.map C) v := by
  obtain ⟨b, run, ex⟩ := descr_empty (tks L) (tfc L) trivial hm sC [] trivial
  rw [empty_map_seen, run] at h
  have hb : b = Bool.true := by cases b <;> simp_all [boolAtom]
  have none := (ex (lh (.map C) + 1) (by omega) (safeN_nil _)).2 hb
  intro v hv
  have := none v.1.1 v.1.2 v.2.2
  rw [(denD_map v).mp hv] at this
  cases this

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! A gradual type meets its negation only in its dynamic part, which `lower_bound/1` removes, and united with its
negation it covers every value in its dynamic part, which `upper_bound/1` returns. -/

theorem lower_bound_run {d : Dispatcher} {a : Term} (h : a = .atom "term" ∨ ∃ X, a = .map X) :
    Elixir.Module.Types.Descr.«lower_bound/1» d a = .ok (lower a) := by
  rcases h with rfl | ⟨X, rfl⟩
  · unfold Elixir.Module.Types.Descr.«lower_bound/1»; rfl
  · unfold Elixir.Module.Types.Descr.«lower_bound/1»
    simp [Erlang.maps.«remove/2», lower, rmDyn]

/-- Types whose dynamic part, if any, is the top type or a map. -/
def UB (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ ∀ Dy, mapLookup X (.atom "dynamic") = some Dy → Dy = .atom "term" ∨ ∃ Y, Dy = .map Y

theorem upper_bound_run {d : Dispatcher} {a : Term} (h : UB a) :
    Elixir.Module.Types.Descr.«upper_bound/1» d a = .ok (upper a) := by
  rcases h with rfl | ⟨X, rfl, hd⟩
  · unfold Elixir.Module.Types.Descr.«upper_bound/1»; rfl
  · unfold Elixir.Module.Types.Descr.«upper_bound/1»
    cases e : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, e, upper]
    | some Dy =>
      rcases hd Dy e with rfl | ⟨Y, rfl⟩ <;> simp [getMapKeys_single, e, upper]

@[simp] theorem upper_bound_term (d : Dispatcher) :
    Elixir.Module.Types.Descr.«upper_bound/1» d (.atom "term") = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«upper_bound/1»; rfl

theorem upper_bound_static {d : Dispatcher} {X : List (Term × Term)} (h : mapLookup X (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«upper_bound/1» d (.map X) = .ok (.map X) := by
  rw [upper_bound_run (Or.inr ⟨X, rfl, fun Dy e => by rw [h] at e; cases e⟩)]
  simp [upper, h]

section
variable {L : Level} {m : Nat}

theorem GC.ub {a : Term} (ha : GC L a) : UB a := by
  rcases ha with (h | ⟨X, rfl, sX⟩) | ⟨X, Dy, rfl, e, tc, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨X, rfl, fun Dy e' => by rw [sX.static] at e'; cases e'⟩
  · refine Or.inr ⟨X, rfl, fun Dy' e' => ?_⟩
    rw [e] at e'; cases e'
    rcases tc with h | ⟨Y, rfl, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨Y, rfl⟩

theorem gd_inter_neg_lower {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n i, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a n = .ok i ∧
      Elixir.Module.Types.Descr.«lower_bound/1» (D m) i = .ok (lower i) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) (lower i) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_neg ha hm
  obtain ⟨i, hi, ri, si, -⟩ := gc_inter ha hn (m := m) (by omega)
  exact ⟨n, i, rn, ri, lower_bound_run hi.shape, tc_empty hi.low_tc (by omega) fun v h => by
    obtain ⟨h₁, h₂⟩ := (si.1 v).mp ((denD_lower i v).mp h)
    exact (sn.1 v).mp h₂ (ha.inv v h₁)⟩

theorem gd_opt_inter_neg_lower {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n i, Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a n = .ok i ∧
      Elixir.Module.Types.Descr.«lower_bound/1» (D m) i = .ok (lower i) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) (lower i) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_opt_neg ha hm
  obtain ⟨i, hi, ri, si⟩ := gc_opt_inter2 ha hn (m := m) (by omega)
  exact ⟨n, i, rn, ri, lower_bound_run hi.shape, tc_empty hi.low_tc (by omega) fun v h => by
    obtain ⟨h₁, h₂⟩ := (si.1 v).mp ((denD_lower i v).mp h)
    exact (sn.1 v).mp h₂ (ha.inv v h₁)⟩

theorem gd_union_neg_upper {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n u, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«bare_union/2» (D m) a n = .ok u ∧
      Elixir.Module.Types.Descr.«upper_bound/1» (D m) u = .ok (upper u) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.atom "term") (upper u) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_neg ha hm
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hn (m := m) (by omega)
  refine ⟨n, u, rn, ru, upper_bound_run hu.ub, tc_sub tc_term hu.up_tc (by omega) fun v _ => (su.2 v).mpr ?_⟩
  by_cases h : denD a v
  · exact Or.inl (ha.inv v h)
  · exact Or.inr ((sn.2 v).mpr h)

theorem gd_opt_union_neg_upper {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ n u, Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok n ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D m) a n = .ok u ∧
      Elixir.Module.Types.Descr.«upper_bound/1» (D m) u = .ok (upper u) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.atom "term") (upper u) = .ok (.atom "true") := by
  obtain ⟨n, hn, rn, sn⟩ := gc_opt_neg ha hm
  obtain ⟨u, hu, ru, su⟩ := gc_opt_union2 ha hn (m := m) (by omega)
  refine ⟨n, u, rn, ru, upper_bound_run hu.ub, tc_sub tc_term hu.up_tc (by omega) fun v _ => (su.2 v).mpr ?_⟩
  by_cases h : denD a v
  · exact Or.inl (ha.inv v h)
  · exact Or.inr ((sn.2 v).mpr h)

theorem gd_de_morgan_union {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ u x nl nr y, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D m) u = .ok x ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok nl ∧
      Elixir.Module.Types.Descr.«bare_negation/1» (D m) b = .ok nr ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) nl nr = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb (m := m) (by omega)
  obtain ⟨x, hx, rx, sx⟩ := gc_neg hu hm
  obtain ⟨nl, hnl, rnl, snl⟩ := gc_neg ha hm
  obtain ⟨nr, hnr, rnr, snr⟩ := gc_neg hb hm
  obtain ⟨y, hy, ry, sy, -⟩ := gc_inter hnl hnr (m := m) (by omega)
  exact ⟨u, x, nl, nr, y, ru, rx, rnl, rnr, ry, gc_equal hx hy (by omega)
    (fun v => by rw [sx.1, su.2, sy.1, snl.1, snr.1]; exact not_or)
    (fun v => by rw [sx.2, su.1, sy.2, snl.2, snr.2]; exact not_or)⟩

end

end Elixir.STTDescrProofsTest.Nest

-- Compatibility only checks emptiness, inclusion, and disjointness of the bounds of gradual types, which are
-- exact on the element types of the next level, whose function types are the top one.
namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Compatibility of gradual types whose function types are the top one. -/

section
variable {L : Level}

/-- Static types whose function types are function types of element types are element types of the next level. -/
theorem de_of_tc {a : Term} (ha : TCF L a)
    (top : ∀ X x, a = .map X → mapLookup X (.atom "fun") = some x → FunA L.E x) : DE L.E a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨X, rfl, sX.keys, fun name x h => ?_⟩
    rcases sX.fields name x h with h' | h' | ⟨e, -⟩ | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · subst e; exact Or.inr (Or.inr (Or.inl ⟨rfl, top X x rfl h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))

theorem de_tc {a : Term} (ha : DE L.E a) : TC L a := ha

/-- The shapes of gradual types: the top type, static maps, maps whose dynamic part is the top type, and maps whose
dynamic part is a static map. -/
theorem GC.cases {a : Term} (ha : GC L a) :
    a = .atom "term" ∨ (∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = none) ∨
      (∃ X, a = .map X ∧ mapLookup X (.atom "dynamic") = some (.atom "term")) ∨
      ∃ X Y, a = .map X ∧ mapLookup X (.atom "dynamic") = some (.map Y) ∧ mapLookup Y (.atom "dynamic") = none := by
  rcases ha with (rfl | ⟨X, rfl, sX⟩) | ⟨X, Dy, rfl, hD, tD, -, -⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨X, rfl, sX.static⟩)
  · rcases tD with rfl | ⟨Y, rfl, sY⟩
    · exact Or.inr (Or.inr (Or.inl ⟨X, rfl, hD⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨X, Y, rfl, hD, sY.static⟩))

/-- Emptiness of a gradual type checks its dynamic part. -/
theorem empty_upper (d : Dispatcher) {a : Term} (ha : GC L a) :
    Elixir.Module.Types.Descr.«empty?/1» d a = Elixir.Module.Types.Descr.«empty?/1» d (upper a) := by
  rcases ha.cases with rfl | ⟨X, rfl, h⟩ | ⟨X, rfl, h⟩ | ⟨X, Y, rfl, h, hY⟩
  · rfl
  · simp [upper, h]
  · simp only [upper, h, Option.getD_some, empty_map_seen]
    rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, h, Elixir.Module.Types.Descr.«empty?/1»]
  · simp only [upper, h, Option.getD_some, empty_map_seen]
    conv => lhs; rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    conv => rhs; rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, h, hY]

/-- Disjointness of gradual types checks their dynamic parts. -/
theorem disj_upper (d : Dispatcher) {a b : Term} (ha : GC L a) (hb : GC L b) :
    Elixir.Module.Types.Descr.«disjoint?/2» d a b = Elixir.Module.Types.Descr.«disjoint?/2» d (upper a) (upper b) := by
  have ea := empty_upper d ha
  have eb := empty_upper d hb
  rcases ha.cases with rfl | ⟨X, rfl, h⟩ | ⟨X, rfl, h⟩ | ⟨X, X', rfl, h, h'⟩ <;>
    rcases hb.cases with rfl | ⟨Y, rfl, k⟩ | ⟨Y, rfl, k⟩ | ⟨Y, Y', rfl, k, k'⟩ <;>
    simp only [upper, Option.getD_some, Option.getD_none, *] at ea eb ⊢ <;>
    unfold Elixir.Module.Types.Descr.«disjoint?/2» <;>
    simp [getMapKeys_single, upper_term, *]

/-- On static types, `subtype_static?/2` answers as `subtype?/2`. -/
theorem sstatic_sub {a b : Term} (ha : TC L a) (hb : TC L b) {m : Nat} (hm : L.K + 13 ≤ m) :
    Elixir.Module.Types.Descr.«subtype_static?/2» (D m) a b = Elixir.Module.Types.Descr.«subtype?/2» (D m) a b := by
  by_cases incl : ∀ v : TP L, denD a v → denD b v
  · rw [sstatic_complete ha hb hm incl, tc_sub ha hb hm incl]
  obtain ⟨T, term, sT, -, all⟩ := termT L
  have static : ∀ {X : List (Term × Term)}, DC L X → ∀ {Y : List (Term × Term)}, DC L Y →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) =
        Elixir.Module.Types.Descr.«subtype_static?/2» (D m) (.map X) (.map Y) := by
    intro X sX Y sY
    unfold Elixir.Module.Types.Descr.«subtype?/2»
    simp [unfold_map, Erlang.erlang.«is_map_key/2», sX.static, sY.static, any_key,
      Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact absurd (fun v _ => denD_term v) incl
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [subtype_term_l term, static sT sB]
    have ne : compareExact (fuel (.map B) (.map T)) (.map B) (.map T) ≠ .eq := fun e => incl fun v _ =>
      (tc_congr (Or.inr ⟨B, rfl, sB⟩) (Or.inr ⟨T, rfl, sT⟩) (compare_eq_of_compareExact_eq _ _ e) v).mpr (all v)
    unfold Elixir.Module.Types.Descr.«subtype_static?/2»
    simp [Erlang.erlang.«=:=/2», ne, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
    conv => lhs; rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    conv => rhs; rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
    simp [getMapKeys_single, sT.static, sB.static, term]
    split <;> rfl
  · exact (static sA sB).symm

end

/-- Static types whose function types `arrows?/2` accepts, arrows between nested types, are element types of the
next level. -/
theorem arrows_de {t : Term} {n : Nat} {b : Term} (hb : TCF (level t n) b)
    (h : «arrows?/2» b (.tuple #[.integer n, t]) = .ok (.atom "true")) : DE (level t n).E b := by
  refine de_of_tc hb fun X x e hx => ?_
  subst e
  unfold «arrows?/2» at h
  simp only [getMapKeys_single, hx] at h
  obtain ⟨hn, hk⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
  have ff : FField (Nest t n) x := by
    rcases nested_field_spec (nested_spec t n) _ _ hn with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, ff⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    all_goals first | exact ff | simp at e
  have fq := keyed_fields_spec (keyed_spec n) Bool.true [(.atom "fun", x)] (by simpa [Term.list, boolAtom] using hk)
    _ (List.mem_singleton_self _)
  rw [← level_nd t n] at ff
  exact funA_of (nest_level t n) (by rw [level_nd] at ff; exact ff) (fq.1 rfl rfl)

/-- `compatible?/2` checks the dynamic parts when the static part of the left type is empty, and inclusion of the
static part otherwise. -/
theorem compat_run (d : Dispatcher) {l r : Term} (hl : l = .atom "term" ∨ ∃ X, l = .map X)
    (hr : UB r) {e s j : Bool}
    (eE : Elixir.Module.Types.Descr.«empty?/1» d (lower l) = .ok (boolAtom e))
    (eS : Elixir.Module.Types.Descr.«subtype_static?/2» d (lower l) (upper r) = .ok (boolAtom s))
    (eJ : Elixir.Module.Types.Descr.«disjoint?/2» d (upper l) (upper r) = .ok (boolAtom j)) :
    Elixir.Module.Types.Descr.«compatible?/2» d l r = .ok (boolAtom (if e then !j else s)) := by
  have finish : ∀ {lo up up' : Term}, Elixir.Module.Types.Descr.«empty?/1» d lo = .ok (boolAtom e) →
      Elixir.Module.Types.Descr.«subtype_static?/2» d lo up' = .ok (boolAtom s) →
      Elixir.Module.Types.Descr.«disjoint?/2» d up up' = .ok (boolAtom j) →
      (do
        let x ← Elixir.Module.Types.Descr.«empty?/1» d lo
        Lynx.Except.guard (.ok (x.isMember [.atom "false", .atom "nil"]))
          (fun _ => Elixir.Module.Types.Descr.«subtype_static?/2» d lo up')
          fun _ => do
            let y ← Elixir.Module.Types.Descr.«disjoint?/2» d up up'
            Erlang.erlang.«not/1» y) = .ok (boolAtom (if e then !j else s)) := by
    intro lo up up' h₁ h₂ h₃
    cases e <;> cases j <;> simp [h₁, h₂, h₃, boolAtom, isMember, Erlang.erlang.«not/1»]
  rcases hl with rfl | ⟨X, rfl⟩ <;> rcases hr with rfl | ⟨Y, rfl, hd⟩
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    simp [-isMember_cons]
    exact finish eE eS eJ
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    cases hY : mapLookup Y (.atom "dynamic") with
    | none =>
      simp only [upper, hY, Option.getD_none] at eS eJ
      simp [-isMember_cons, getMapKeys_single, hY]
      exact finish eE eS eJ
    | some Dy =>
      simp only [upper, hY, Option.getD_some] at eS eJ
      rcases hd Dy hY with rfl | ⟨Z, rfl⟩ <;> simp [-isMember_cons, getMapKeys_single, hY] <;> exact finish eE eS eJ
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    simp [-isMember_cons, unfold_map, pop_dyn]
    exact finish eE eS eJ
  · unfold Elixir.Module.Types.Descr.«compatible?/2»
    cases hY : mapLookup Y (.atom "dynamic") with
    | none =>
      simp only [upper, hY, Option.getD_none] at eS eJ
      simp [-isMember_cons, unfold_map, pop_dyn, getMapKeys_single, hY]
      exact finish eE eS eJ
    | some Dy =>
      simp only [upper, hY, Option.getD_some] at eS eJ
      rcases hd Dy hY with rfl | ⟨Z, rfl⟩ <;> simp [-isMember_cons, unfold_map, pop_dyn, getMapKeys_single, hY] <;>
        exact finish eE eS eJ

/-- `compatible?/2` checks that the static part of the left type is included in the dynamic part of the right one and
that the two meet, as the law states it. -/
theorem gd_compatible {t : Term} {n : Nat} {l r : Term} (gl : GC (level t n) l) (gr : GC (level t n) r) (ll : DE (level t n).E (lower l))
    (ul : DE (level t n).E (upper l)) (ur : DE (level t n).E (upper r)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«compatible?/2» (D m) l r = .ok (boolAtom b) ∧
      Lynx.Except.andAlso (Elixir.Module.Types.Descr.«subtype?/2» (D m) (lower l) (upper r))
        (do
          let j ← Elixir.Module.Types.Descr.«disjoint?/2» (D m) l r
          Erlang.erlang.«not/1» j) true = .ok (boolAtom b) := by
  have ef3 : EF (level t n).nd (DE (level t n).E)
      (PtD (level t n).E (level t n).den (level t n).tl (FVal (level t n).E (level t n).den)) denD tlD
      ((level t n).K + 23) := ef_step (level t n).ef (level t n).none
  let toTP : PtD (level t n).E (level t n).den (level t n).tl (FVal (level t n).E (level t n).den) → TP (level t n) :=
    fun v => v
  obtain ⟨bE, rE, semE⟩ := ef3.empty [] ll
  replace semE := semE (lh (lower l) + 1) (by omega) (safeN_nil _)
  obtain ⟨s, rS, semS⟩ := ef3.sub ll ur
  obtain ⟨dj, rJ, semJ⟩ := ef3.disj ul ur
  have tl := de_tc ll
  have tr := de_tc ur
  have eS : Elixir.Module.Types.Descr.«subtype_static?/2» (D m) (lower l) (upper r) = .ok (boolAtom s) := by
    rw [sstatic_sub tl tr (by omega), rS m hm]
  have eE : Elixir.Module.Types.Descr.«empty?/1» (D m) (lower l) = .ok (boolAtom bE) := by
    rcases tl with e | ⟨X, e, -⟩ <;> rw [e] at rE semE ⊢
    · have : bE = Bool.false := by
        cases bE
        · rfl
        · exact absurd (denD_term ptWit) ((semE.mp rfl) ptWit)
      subst this; rfl
    · rw [empty_map_seen]; exact rE m hm
  have eJ : Elixir.Module.Types.Descr.«disjoint?/2» (D m) l r = .ok (boolAtom dj) := by
    rw [disj_upper (D m) gl gr]; exact rJ m hm
  have eJ' : Elixir.Module.Types.Descr.«disjoint?/2» (D m) (upper l) (upper r) = .ok (boolAtom dj) := rJ m hm
  have hc := compat_run (D m) gl.shape gr.ub eE eS eJ'
  rw [hc]
  simp only [eJ, rS m hm, Lynx.Except.ok_bind]
  cases bE
  · -- The static part is not empty: it must be included and then the types meet.
    refine ⟨s, by simp, ?_⟩
    cases s
    · simp [boolAtom, Lynx.Except.andAlso]
    · have meet : dj = Bool.false := by
        cases dj
        · rfl
        · obtain ⟨v, hv⟩ : ∃ v, denD (lower l) v := by
            apply Classical.byContradiction; intro h
            exact absurd (semE.mpr fun v hv => h ⟨v, hv⟩) (by simp)
          exact (semJ rfl v (gl.inv (toTP v) ((denD_lower l (toTP v)).mp hv)) (semS rfl v hv)).elim
      subst meet
      simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
  · -- The static part is empty, so it is included.
    have sub : s = Bool.true := by
      have := ef3.subc ll ur (fun v hv => absurd hv ((semE.mp rfl) v)) m hm
      rw [rS m hm] at this
      cases s <;> simp_all [boolAtom]
    subst sub
    refine ⟨!dj, by simp, ?_⟩
    cases dj <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Subtyping is an order, and disjointness is exact, on types whose function types are arrows. -/

section
variable {L : Level}

/-- The fields of a gradual map other than its dynamic part are those of its lower bound. -/
theorem gc_fields {X : List (Term × Term)} (hX : GC L (.map X)) {name : String} (h : name ≠ "dynamic") {x : Term}
    (hx : mapLookup X (.atom name) = some x) : FC L name x := by
  have t := hX.low_tc
  rcases t with e | ⟨X', e, sX⟩
  · simp [lower] at e
  · simp only [lower, Term.map.injEq] at e
    subst e
    exact sX.fields name x (by rw [lookup_rmDyn_name X h]; exact hx)

/-- Gradual types equal by comparison hold the same points, at both bounds. -/
theorem gc_congr {a b : Term} (ha : GC L a) (hb : GC L b) (e : Term.compare (Term.fuel a b) a b = .eq) (v : TP L) :
    (denD a v ↔ denD b v) ∧ (denD (upper a) v ↔ denD (upper b) v) := by
  rcases ha.shape with rfl | ⟨X, rfl⟩ <;> rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨Iff.rfl, Iff.rfl⟩
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · rw [compare_step] at e; simp [Compare.compareStep] at e
  · have fields : denD (.map X) v ↔ denD (.map Y) v := by
      rw [denD_map, denD_map]
      have ne := names_ne_dyn v.2.1
      have rel := lookup_rel_cmp e (.atom v.1.1)
      cases hx : mapLookup X (.atom v.1.1) <;> cases hy : mapLookup Y (.atom v.1.1) <;> rw [hx, hy] at rel <;>
        cases rel
      rename_i x y cmp
      rw [fieldC_congr (tks L) (tfc L) (gc_fields ha ne hx) (gc_fields hb ne hy) cmp v.1.2 v.2.2]
    refine ⟨fields, ?_⟩
    have rel := lookup_rel_cmp e (.atom "dynamic")
    cases hx : mapLookup X (.atom "dynamic") <;> cases hy : mapLookup Y (.atom "dynamic") <;> rw [hx, hy] at rel <;>
      cases rel
    · simp only [upper, hx, hy, Option.getD_none]
      exact fields
    rename_i x y cmp
    have tx := ha.up_tc; have ty := hb.up_tc
    rw [upper_dyn hx] at tx ⊢; rw [upper_dyn hy] at ty ⊢
    exact tc_congr tx ty cmp v

end

section
variable {t : Term} {n : Nat}

/-- Points of the next level, whose function fields hold sets of functions. -/
abbrev PN (t : Term) (n : Nat) : Type :=
  PtD (level t n).E (level t n).den (level t n).tl (FVal (level t n).E (level t n).den)

/-- A point of the next level, as a point of the top-level types. -/
def toTPN (v : PN t n) : TP (level t n) := v

theorem denD_toTPN (a : Term) (v : PN t n) : denD a (toTPN v) ↔ denD a v := Iff.rfl

/-- Inclusion of types over the points of the next level. -/
def SubN (t : Term) (n : Nat) (a b : Term) : Prop := ∀ v : PN t n, denD a v → denD b v

theorem ef_next (t : Term) (n : Nat) : EF (level t n).nd (DE (level t n).E) (PN t n) denD tlD ((level t n).K + 23) :=
  ef_step (level t n).ef (level t n).none

/-- Subtyping of types whose function types are arrows is exact. -/
theorem next_sub {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom (bp (SubN t n a b))) := by
  have ef3 := ef_next t n
  obtain ⟨s, rs, ss⟩ := ef3.sub ha hb
  by_cases h : SubN t n a b
  · rw [ef3.subc ha hb h m hm, bp_true.mpr h]; rfl
  · rw [rs m hm, bp_false.mpr h]
    cases s
    · rfl
    · exact absurd (ss rfl) h

/-- The subtraction check of `subtype?/2` is exact on types whose function types are arrows. -/
theorem next_esub {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«empty_difference_subtype?/3» (D m) a b (.map []) =
      .ok (boolAtom (bp (SubN t n a b))) := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · have e := compare_eq_of_compareExact_eq _ _ same
    have incl : ∀ v : TP (level t n), denD a v → denD b v := fun v h =>
      (tc_congr (de_tc hb) (de_tc ha) e v).mpr h
    rw [esub_complete (de_tc ha) (de_tc hb) (by omega) incl, bp_true.mpr (show SubN t n a b from fun v h => incl (toTPN v) h)]
    rfl
  · have run := sstatic_sub (de_tc ha) (de_tc hb) (m := m) (by omega)
    unfold Elixir.Module.Types.Descr.«subtype_static?/2» at run
    simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»] at run
    rw [run, next_sub ha hb hm]

/-- The lower bound of a gradual type is included in its upper bound. -/
theorem gc_inv_n {a : Term} (ga : GC (level t n) a) : SubN t n (lower a) (upper a) := fun v h =>
  ga.inv (toTPN v) ((denD_lower a (toTPN v)).mp h)

theorem bp_and (p q : Prop) : (bp p && bp q) = bp (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Gradual subtyping on maps compares both bounds exactly. -/
theorem gd_sub_maps {X Y : List (Term × Term)} (ga : GC (level t n) (.map X)) (gb : GC (level t n) (.map Y))
    (la : DE (level t n).E (lower (.map X))) (ua : DE (level t n).E (upper (.map X)))
    (lb : DE (level t n).E (lower (.map Y))) (ub : DE (level t n).E (upper (.map Y))) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map X) (.map Y) =
      .ok (boolAtom (bp (SubN t n (lower (.map X)) (lower (.map Y)) ∧ SubN t n (upper (.map X)) (upper (.map Y))))) := by
  have iX := gc_inv_n ga
  have iY := gc_inv_n gb
  cases hx : mapLookup X (.atom "dynamic") with
  | none =>
    have eX : lower (.map X) = .map X := by simp [lower, rmDyn_static hx]
    have uX : upper (.map X) = .map X := by simp [upper, hx]
    rw [eX] at la iX ⊢; rw [uX] at iX ⊢
    cases hy : mapLookup Y (.atom "dynamic") with
    | none =>
      have eY : lower (.map Y) = .map Y := by simp [lower, rmDyn_static hy]
      have uY : upper (.map Y) = .map Y := by simp [upper, hy]
      rw [eY] at lb ⊢; rw [uY]
      rw [next_sub la lb hm, bp_congr (and_self_iff (a := SubN t n (.map X) (.map Y))).symm]
    | some Dy =>
      have run := sstatic_sub (de_tc la) (de_tc lb) (m := m) (by omega)
      rw [next_sub la lb hm] at run
      have e : SubN t n (.map X) (lower (.map Y)) ∧ SubN t n (.map X) (upper (.map Y)) ↔
          SubN t n (.map X) (lower (.map Y)) := ⟨fun h => h.1, fun h => ⟨h, fun v hv => iY v (h v hv)⟩⟩
      rw [bp_congr e]
      simp only [lower] at run ⊢
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», Erlang.maps.«remove/2»]
      simpa [rmDyn] using run
  | some Dx =>
    cases hy : mapLookup Y (.atom "dynamic") with
    | none =>
      have eY : lower (.map Y) = .map Y := by simp [lower, rmDyn_static hy]
      have uY : upper (.map Y) = .map Y := by simp [upper, hy]
      rw [eY] at lb ⊢; rw [uY]
      have run := sstatic_sub (de_tc ua) (de_tc lb) (m := m) (by omega)
      rw [next_sub ua lb hm, upper_dyn hx] at run
      have e : SubN t n (lower (.map X)) (.map Y) ∧ SubN t n (upper (.map X)) (.map Y) ↔
          SubN t n (upper (.map X)) (.map Y) := ⟨fun h => h.2, fun h => ⟨fun v hv => h v (iX v hv), h⟩⟩
      rw [bp_congr e, upper_dyn hx]
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2», map_get_dyn hx, run]
    | some Dy =>
      have r₁ := next_esub ua ub hm
      have r₂ := next_esub la lb hm
      rw [upper_dyn hx, upper_dyn hy] at r₁
      rw [upper_dyn hx, upper_dyn hy]
      simp only [lower] at r₂ ⊢
      unfold Elixir.Module.Types.Descr.«subtype?/2»
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, hy, any_key, Lynx.Except.andAlso,
        Erlang.erlang.«not/1», Erlang.erlang.«/=/2»]
      unfold Elixir.Module.Types.Descr.«subtype_static?/2»
      by_cases same : compareExact (fuel (.map Y) (.map X)) (.map Y) (.map X) = .eq
      · have cg := fun v => gc_congr gb ga (compare_eq_of_compareExact_eq _ _ same) (toTPN v)
        have P : SubN t n (.map (rmDyn X)) (.map (rmDyn Y)) ∧ SubN t n Dx Dy := by
          refine ⟨fun v h => ?_, fun v h => ?_⟩
          · have := (cg v).1.mpr ((denD_rmDyn X (toTPN v)).mp h)
            exact (denD_rmDyn Y (toTPN v)).mpr this
          · have := (cg v).2.mpr (by rw [upper_dyn hx]; exact h)
            rw [upper_dyn hy] at this; exact this
        simp [Erlang.erlang.«=:=/2», same, bp_true.mpr P]
      · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»]
        rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def]
        simp [getMapKeys_single, hx, hy, r₁, Erlang.maps.«remove/2», Lynx.Except.andAlso]
        rw [← rmDyn, ← rmDyn, r₂]
        by_cases h₁ : SubN t n Dx Dy <;> by_cases h₂ : SubN t n (.map (rmDyn X)) (.map (rmDyn Y)) <;>
          simp [h₁, h₂, boolAtom]

/-- The unfolded top type is a static map holding every point of the next level. -/
theorem termN (t : Term) (n : Nat) : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    GC (level t n) (.map T) ∧ DE (level t n).E (.map T) ∧ lower (.map T) = .map T ∧ upper (.map T) = .map T ∧
    ∀ v : PN t n, denD (.map T) v := by
  obtain ⟨T, term, sT, -, -⟩ := termT (level t n)
  obtain ⟨T', term', sT', -, -, all⟩ := termC (FV := FVal (level t n).E (level t n).den) (kinds (level t n).ef)
    (Fn := FunA (level t n).E) funA_top
  rw [term] at term'
  cases term'
  exact ⟨T, term, GC.tc (Or.inr ⟨T, rfl, sT⟩), Or.inr ⟨T, rfl, sT'⟩, by simp [lower, rmDyn_static sT.static],
    upper_tc (Or.inr ⟨T, rfl, sT⟩), fun v => (denD_map v).mpr (all _ v.2.1 _ v.2.2)⟩

/-- A gradual type, with the top type as its unfolded map. -/
theorem gc_map {a : Term} (ga : GC (level t n) a) (la : DE (level t n).E (lower a)) (ua : DE (level t n).E (upper a)) :
    ∃ X, GC (level t n) (.map X) ∧ DE (level t n).E (lower (.map X)) ∧ DE (level t n).E (upper (.map X)) ∧
      (∀ v : PN t n, denD (lower a) v ↔ denD (lower (.map X)) v) ∧
      (∀ v : PN t n, denD (upper a) v ↔ denD (upper (.map X)) v) ∧
      (a = .atom "term" ∧ Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map X) ∨ a = .map X) := by
  rcases ga.shape with rfl | ⟨X, rfl⟩
  · obtain ⟨T, term, gT, dT, lT, uT, all⟩ := termN t n
    refine ⟨T, gT, by rw [lT]; exact dT, by rw [uT]; exact dT, fun v => ?_, fun v => ?_, Or.inl ⟨rfl, term⟩⟩
    · rw [lT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩
    · rw [uT]; exact ⟨fun _ => all v, fun _ => denD_term v⟩
  · exact ⟨X, ga, la, ua, fun v => Iff.rfl, fun v => Iff.rfl, Or.inr rfl⟩

/-- Gradual subtyping compares both bounds exactly, on types whose function types are arrows. -/
theorem gd_sub {a b : Term} (ga : GC (level t n) a) (gb : GC (level t n) b)
    (la : DE (level t n).E (lower a)) (ua : DE (level t n).E (upper a))
    (lb : DE (level t n).E (lower b)) (ub : DE (level t n).E (upper b)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b =
      .ok (boolAtom (bp (SubN t n (lower a) (lower b) ∧ SubN t n (upper a) (upper b)))) := by
  obtain ⟨X, gX, lX, uX, elX, euX, sa⟩ := gc_map ga la ua
  obtain ⟨Y, gY, lY, uY, elY, euY, sb⟩ := gc_map gb lb ub
  have e : SubN t n (lower a) (lower b) ∧ SubN t n (upper a) (upper b) ↔
      SubN t n (lower (.map X)) (lower (.map Y)) ∧ SubN t n (upper (.map X)) (upper (.map Y)) := by
    simp only [SubN]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun v h => (elY v).mp (h₁ v ((elX v).mpr h)), fun v h => (euY v).mp (h₂ v ((euX v).mpr h))⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun v h => (elY v).mpr (h₁ v ((elX v).mp h)), fun v h => (euY v).mpr (h₂ v ((euX v).mp h))⟩
  rw [bp_congr e, ← gd_sub_maps gX gY lX uX lY uY hm]
  rcases sa with ⟨rfl, term⟩ | rfl <;> rcases sb with ⟨rfl, term'⟩ | rfl
  · rw [subtype_term_l term, subtype_term_r term']
  · rw [subtype_term_l term]
  · rw [subtype_term_r term']
  · rfl

/-- Walks whose common fields all intersect into dropped or empty fields find no common field. -/
theorem iter_disj_false (K' : Nat) (B : List (Term × Term)) :
    ∀ es : List (Term × Term), (∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∀ d', K' ≤ d' → ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map []) = .ok (.atom "true"))) →
    ∀ m, K' + es.length ≤ m →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) (.map [])) = .ok (.atom "false") := by
  intro es
  induction es with
  | nil =>
    intro _ m _
    simp [Term.list, Erlang.maps.«next/1»]
    rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
    simp
  | cons e rest ih =>
    intro calls m hm
    have calls' := fun e' (me' : e' ∈ rest) => calls e' (List.mem_cons_of_mem _ me')
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    have hm' : K' + rest.length ≤ m := by simp at hm; omega
    have cont : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-iterator_non_disjoint_intersection?/3-fun-0-" 1
        #[Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]), .map B, .map []]) #[x] =
        (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) (.map [])) := by
      intro x
      rw [Erlang.program.«Elixir.Module.Types.Descr:-iterator_non_disjoint_intersection?/3-fun-0-/1».pure]
      simp [Elixir.Module.Types.Descr.«-iterator_non_disjoint_intersection?/3-fun-0-/4»]
    refine Eq.trans ?_ (ih calls' m hm')
    simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
    rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
    cases hb : mapLookup B e.1 with
    | none => simp [getMapKeys_single, hb, cont]
    | some y₀ =>
      obtain ⟨w, rw', k₀⟩ := calls e List.mem_cons_self y₀ hb (m + 1) (by simp at hm; omega)
      rcases k₀ with k | hb'
      · rcases dropped k with e₀ | e₀ <;> rw [e₀] at rw' <;>
          simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember]
      · by_cases dz : (compareExact (fuel w (.integer 0)) w (.integer 0) = .eq ∨ compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") = .eq)
        · rcases dz with dz | dz <;>
            simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember, dz]
        · simp only [not_or] at dz
          simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont, isMember, dz.1, dz.2, hb']

end

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop} {H : Prop}

/-- `disjoint?/2` answers `true` on types without common points. -/
theorem descr_disj_complete (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hS : FS [])
    {m : Nat} (hm : K + 7 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (disj : ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D m) (.map A) (.map B) = .ok (.atom "true") := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y →
      (∀ name p, PtOkC TV LV MV FV name p →
        (dn name (mapLookup X (.atom name)) p && dn name (mapLookup Y (.atom name)) p) = Bool.false) →
      ∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∀ d', K + 1 ≤ d' → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
          (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map []) = .ok (.atom "true")) := by
    intro X Y sX sY dXY e me y hy d' hd
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, ?_⟩
    cases kw : kept (.atom name, w)
    · exact Or.inl rfl
    · refine Or.inr ?_
      have rb := fieldC_empty_none ks fc (show K ≤ d' by omega) (k kw).1 (fun _ => hS) fun p ok => by
        have := sem p ok
        rw [keptO_true kw] at this
        rw [this, ← hx, ← hy]
        exact dXY name p ok
      simpa using rb
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  unfold Elixir.Module.Types.Descr.«disjoint?/2»
  simp [getMapKeys_single, stA, stB]
  unfold Elixir.Module.Types.Descr.«non_disjoint_intersection?/2»
  rw [Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def]
  by_cases g : sa > sb
  · have walk := iter_disj_false (K + 1) A (mapEntries B)
      (calls sB sA fun name p ok => by rw [Bool.and_comm]; exact disj name p ok) m (by have := descrC_six sB; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [← bind_assoc, walk]
    simp [Erlang.erlang.«not/1»]
  · have walk := iter_disj_false (K + 1) B (mapEntries A) (calls sA sB disj) m (by have := descrC_six sA; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [← bind_assoc, walk]
    simp [Erlang.erlang.«not/1»]

end

section
variable {t : Term} {n : Nat}

/-- Emptiness of types whose function types are arrows is exact. -/
theorem next_empty {a : Term} (ha : DE (level t n).E a) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom (bp (∀ v : PN t n, ¬denD a v))) := by
  have ef3 := ef_next t n
  obtain ⟨b, run, sem⟩ := ef3.empty [] ha
  replace sem := sem (lh a + 1) (by omega) (safeN_nil _)
  have e : b = bp (∀ v : PN t n, ¬denD a v) := by
    cases b
    · exact (bp_false.mpr fun h => absurd (sem.mpr h) (by simp)).symm
    · exact (bp_true.mpr (sem.mp rfl)).symm
  subst e
  rcases ha with rfl | ⟨X, rfl, -⟩
  · rw [empty_term_false, bp_false.mpr fun h => h ptWit (denD_term ptWit)]
  · rw [empty_map_seen]; exact run m hm

/-- Disjointness of types whose function types are arrows is exact. -/
theorem next_disj {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b =
      .ok (boolAtom (bp (∀ v : PN t n, denD a v → denD b v → False))) := by
  have ef3 := ef_next t n
  by_cases h : ∀ v : PN t n, denD a v → denD b v → False
  · rw [bp_true.mpr h]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · rw [disjoint_term_l, next_empty hb hm, bp_true.mpr fun v hv => h v (denD_term v) hv]
    rcases hb with rfl | ⟨B, rfl, sB⟩
    · rw [disjoint_term_r, next_empty (Or.inr ⟨A, rfl, sA⟩) hm, bp_true.mpr fun v hv => h v hv (denD_term v)]
    have st := stepOf (level t n).ef (level t n).none
    refine descr_disj_complete st.ks st.fc trivial (by omega) sA sB fun name p ok => ?_
    by_cases mem : name ∈ names
    · have := h ⟨(name, p), mem, ok⟩
      simp only [denD_map] at this
      cases h₁ : dn name (mapLookup A (.atom name)) p <;> cases h₂ : dn name (mapLookup B (.atom name)) p <;>
        simp_all
    · have : mapLookup A (.atom name) = none := by
        cases hx : mapLookup A (.atom name)
        · rfl
        · obtain ⟨name', m', e⟩ := sA.keys (.atom name) (by simp [hx])
          simp only [Term.atom.injEq] at e; subst e; exact absurd m' mem
      simp [this, dn_none]
  · obtain ⟨s, run, sound⟩ := ef3.disj ha hb
    rw [run m hm, bp_false.mpr h]
    cases s
    · rfl
    · exact absurd (sound rfl) h

/-- Disjointness of gradual types is the emptiness of their intersection. -/
theorem gd_disj_empty {a b : Term} (ga : GC (level t n) a) (gb : GC (level t n) b)
    (ua : DE (level t n).E (upper a)) (ub : DE (level t n).E (upper b)) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) c = .ok (boolAtom s) := by
  obtain ⟨c, gc, run, sem, up⟩ := gc_inter ga gb (m := m) (by omega)
  refine ⟨c, bp (∀ v : PN t n, denD (upper a) v → denD (upper b) v → False), run, ?_, ?_⟩
  · rw [disj_upper _ ga gb]; exact next_disj ua ub (by omega)
  · rw [empty_upper _ gc]
    rcases up with up | ⟨j, hj, rj⟩
    · have dis : ∀ v : PN t n, denD (upper a) v → denD (upper b) v → False := fun v h₁ h₂ =>
        up (toTPN v) ((sem.2 (toTPN v)).mpr ⟨h₁, h₂⟩)
      rw [bp_true.mpr dis, tc_empty gc.up_tc (by omega) up]
      rfl
    · obtain ⟨c', dc', rc', sc', -⟩ := (ef_next t n).inter ua ub
      have e := (rc' j (by omega)).symm.trans rj
      cases e
      rw [next_empty dc' (by omega)]
      refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
      exact ⟨fun h v h₁ h₂ => h v ((sc' v).mpr ⟨h₁, h₂⟩), fun h v hv => h v ((sc' v).mp hv).1 ((sc' v).mp hv).2⟩

/-- `equal?/2` checks subtyping both ways, as gradual types equal by comparison are subtypes of each other. -/
theorem gd_equal {a b : Term} (ga : GC (level t n) a) (gb : GC (level t n) b)
    (la : DE (level t n).E (lower a)) (ua : DE (level t n).E (upper a))
    (lb : DE (level t n).E (lower b)) (ub : DE (level t n).E (upper b)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ s₁ s₂, Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s₁) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) b a = .ok (boolAtom s₂) ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (boolAtom (s₁ && s₂)) := by
  have r₁ := gd_sub ga gb la ua lb ub hm
  have r₂ := gd_sub gb ga lb ub la ua hm
  refine ⟨_, _, r₁, r₂, ?_⟩
  by_cases c : Term.compare (Term.fuel a b) a b = .eq
  · have cg := fun v => gc_congr ga gb c (toTPN v)
    have lo : ∀ v : PN t n, denD (lower a) v ↔ denD (lower b) v := fun v => by
      rw [← denD_toTPN, ← denD_toTPN (lower b), denD_lower, denD_lower]; exact (cg v).1
    have up : ∀ v : PN t n, denD (upper a) v ↔ denD (upper b) v := fun v => (cg v).2
    rw [bp_true.mpr ⟨fun v => (lo v).mp, fun v => (up v).mp⟩, bp_true.mpr ⟨fun v => (lo v).mpr, fun v => (up v).mpr⟩]
    simp [Elixir.Module.Types.Descr.«equal?/2», Lynx.Except.orElse, Erlang.erlang.«==/2», c, Term.true]
  · simp [Elixir.Module.Types.Descr.«equal?/2», Lynx.Except.orElse, Lynx.Except.andAlso, Erlang.erlang.«==/2», c,
      Term.false, r₁, r₂]
    cases bp (SubN t n (lower a) (lower b) ∧ SubN t n (upper a) (upper b)) <;> rfl

end

/-- Every type is a subtype of itself. -/
theorem subtype_refl (d : Dispatcher) {a : Term} (h : a = .atom "term" ∨ ∃ X, a = .map X) :
    Elixir.Module.Types.Descr.«subtype?/2» d a a = .ok (.atom "true") := by
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  have maps : ∀ X : List (Term × Term), Elixir.Module.Types.Descr.«subtype?/2» d (.map X) (.map X) = .ok (.atom "true") := by
    intro X
    unfold Elixir.Module.Types.Descr.«subtype?/2»
    cases hx : mapLookup X (.atom "dynamic") <;>
      simp [unfold_map, Erlang.erlang.«is_map_key/2», hx, any_key, Lynx.Except.andAlso, Erlang.erlang.«not/1»,
        Erlang.erlang.«/=/2», Elixir.Module.Types.Descr.«subtype_static?/2», Erlang.erlang.«=:=/2»]
  rcases h with rfl | ⟨X, rfl⟩
  · rw [subtype_term_l term, subtype_term_r term]; exact maps T
  · exact maps X

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Unions and intersections of gradual types whose function types are arrows. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop} {H : Prop}

/-- Merging fields keeps them in their classes. -/
theorem mergeL_descr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {k : Nat} (hk : K + 1 ≤ k)
    {A B U : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : MergeL (Elixir.Module.Types.Descr.«bare_union/3» (D k)) A B U) : DescrC Fn TF LF MF U :=
  (union_gen (slh := False) (TV := TV) (LV := LV) (MV := MV) (FV := FV) sA sB _ h.1 h.2 fun _ _ _ fx fy =>
    let ⟨u, ru, fu, su, _⟩ := fieldC_union ks fc hk fx fy; ⟨u, ru, fu, su, False.elim⟩).1

/-- Intersecting fields keeps them in their classes. -/
theorem interL_descr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {k : Nat} (hk : K + 1 ≤ k)
    {A B I : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : InterL (Elixir.Module.Types.Descr.«bare_intersection/3» (D k)) A B I) : DescrC Fn TF LF MF I :=
  (inter_gen (slh := False) (TV := TV) (LV := LV) (MV := MV) (FV := FV) sA sB _ h.1 h.2 fun _ _ _ fx fy =>
    let ⟨w, rw', kw, sw⟩ := fieldC_inter ks fc hk fx fy; ⟨w, rw', fun h => ⟨(kw h).1, False.elim⟩, sw⟩).1

end

section
variable {t : Term} {n : Nat}

/-- Gradual types whose bounds are element types of the next level, so their function types are arrows. -/
def GD (t : Term) (n : Nat) (a : Term) : Prop :=
  GC (level t n) a ∧ DE (level t n).E (lower a) ∧ DE (level t n).E (upper a)

theorem de_map {X : List (Term × Term)} (h : DE (level t n).E (.map X)) :
    DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E) (MField (level t n).E) X := by
  rcases h with h | ⟨X', e, sX⟩
  · cases h
  · simp only [Term.map.injEq] at e; subst e; exact sX

/-- Element types of the next level are their own bounds. -/
theorem de_gd {a : Term} (ha : DE (level t n).E a) : GD t n a ∧ lower a = a ∧ upper a = a := by
  have tc := de_tc ha
  have e : lower a = a ∧ upper a = a := by
    rcases ha with rfl | ⟨X, rfl, sX⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨by simp [lower, rmDyn_static sX.static], upper_tc tc⟩
  exact ⟨⟨GC.tc tc, by rw [e.1]; exact ha, by rw [e.2]; exact ha⟩, e⟩

/-- Unions of dynamic parts keep arrows. -/
theorem dyn_union_de {k : Nat} (hk : (level t n).K + 12 ≤ k) {a b c : Term} (ha : DE (level t n).E a)
    (hb : DE (level t n).E b)
    (run : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) a b
      (.function false "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok c) : DE (level t n).E c := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · have e : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) (.atom "term") b
        (.function false "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl
    rw [e] at run; cases run; exact Or.inl rfl
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · have e : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) (.map A) (.atom "term")
        (.function false "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok (.atom "term") := by
      unfold Elixir.Module.Types.Descr.«dynamic_union/3»; rfl
    rw [e] at run; cases run; exact Or.inl rfl
  have st := stepOf (level t n).ef (level t n).none
  obtain ⟨U, rU, look⟩ := merge_gen (D (k + 1)) "Elixir.Module.Types.Descr" "bare_union" #[] _
    (fun q v₁ v₂ => Erlang.program.«Elixir.Module.Types.Descr:bare_union/3».pure k q v₁ v₂) A B
    (fun q h => let ⟨n', _, e⟩ := sB.keys q h; ⟨n', e⟩) (fun q x y hx hy => by
      obtain ⟨name, -, rfl⟩ := sA.keys q (by simp [hx])
      obtain ⟨u, ru, -⟩ := fieldC_union st.ks st.fc (by omega) (sA.fields name x hx) (sB.fields name y hy)
      exact ⟨u, ru⟩)
  have e : Elixir.Module.Types.Descr.«dynamic_union/3» (D (k + 1)) (.map A) (.map B)
      (.function false "Elixir.Module.Types.Descr" "bare_union" 3 #[]) = .ok (.map U) := by
    unfold Elixir.Module.Types.Descr.«dynamic_union/3»; simpa [unfold_map] using rU
  rw [e] at run; cases run
  refine Or.inr ⟨U, rfl, mergeL_descr st.ks st.fc (by omega) sA sB ⟨fun name => look _, fun q h => ?_⟩⟩
  cases hB : mapLookup B q with
  | none => rw [(look q).1 hB] at h; exact Or.inl h
  | some _ => exact Or.inr rfl

/-- Unions of gradual types whose function types are arrows unite both bounds and keep arrows. -/
theorem gd_union {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧ GD t n c ∧
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∨ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∨ denD (upper b) v) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ha, la, ua⟩ := ga
  obtain ⟨hb, lb, ub⟩ := gb
  have bounds : ∀ c, USem (level t n) a b c →
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∨ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∨ denD (upper b) v) := fun c sem =>
    ⟨fun v => (denD_lower c (toTPN v)).trans ((sem.1 _).trans
      (or_congr (denD_lower a (toTPN v)).symm (denD_lower b (toTPN v)).symm)), fun v => sem.2 (toTPN v)⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, union_term_l _ _, ⟨GC.tc tc_term, Or.inl rfl, Or.inl rfl⟩, bounds _ (usem_term_l _)⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, union_term_r _ _, ⟨GC.tc tc_term, Or.inl rfl, Or.inl rfl⟩, bounds _ (usem_term_r _)⟩
  by_cases nX : X = []
  · subst nX; exact ⟨_, union_nil_l _ _, ⟨hb, lb, ub⟩, bounds _ (usem_nil_l _)⟩
  by_cases nY : Y = []
  · subst nY; exact ⟨_, union_nil_r _ _, ⟨ha, la, ua⟩, bounds _ (usem_nil_r _)⟩
  by_cases st : mapLookup X (.atom "dynamic") = none ∧ mapLookup Y (.atom "dynamic") = none
  · have eX : lower (.map X) = .map X ∧ upper (.map X) = .map X := by simp [lower, upper, rmDyn_static st.1, st.1]
    have eY : lower (.map Y) = .map Y ∧ upper (.map Y) = .map Y := by simp [lower, upper, rmDyn_static st.2, st.2]
    rw [eX.1] at la; rw [eY.1] at lb
    obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).union la lb
    obtain ⟨gc, lc, uc⟩ := de_gd dc
    exact ⟨c, run _ (by omega), gc, fun v => by rw [lc, eX.1, eY.1]; exact sem v,
      fun v => by rw [uc, eX.2, eY.2]; exact sem v⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp_all
  obtain ⟨c, hc, run, lo, up, U, rfl, look, rD⟩ := merge_aligned (bare_union_op (L := level t n) (n := k + 1) (by omega))
    (bare_union_op (n := k) (by omega)) (bare_union_dyn _) ha hb
  have st := stepOf (level t n).ef (level t n).none
  have dl : DE (level t n).E (lower (.map U)) :=
    Or.inr ⟨_, rfl, mergeL_descr st.ks st.fc (by omega) (de_map la) (de_map lb) look⟩
  exact ⟨_, (union_run_grad _ nX nY g).trans run, ⟨hc, dl, dyn_union_de (by omega) ua ub rD⟩, bounds _ ⟨lo, up⟩⟩

/-- Intersections of gradual types whose function types are arrows intersect both bounds and keep arrows. -/
theorem gd_inter {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧ GD t n c ∧
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∧ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∧ denD (upper b) v) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ha, la, ua⟩ := ga
  obtain ⟨hb, lb, ub⟩ := gb
  have bounds : ∀ c, ISem (level t n) a b c →
      (∀ v : PN t n, denD (lower c) v ↔ denD (lower a) v ∧ denD (lower b) v) ∧
      (∀ v : PN t n, denD (upper c) v ↔ denD (upper a) v ∧ denD (upper b) v) := fun c sem =>
    ⟨fun v => (denD_lower c (toTPN v)).trans ((sem.1 _).trans
      (and_congr (denD_lower a (toTPN v)).symm (denD_lower b (toTPN v)).symm)), fun v => sem.2 (toTPN v)⟩
  rcases ha.shape with rfl | ⟨X, rfl⟩
  · exact ⟨_, inter_term_left _ _, ⟨hb, lb, ub⟩, bounds _ (isem_term_l _)⟩
  rcases hb.shape with rfl | ⟨Y, rfl⟩
  · exact ⟨_, inter_term_right _ _, ⟨ha, la, ua⟩, bounds _ (isem_term_r _)⟩
  by_cases st : mapLookup X (.atom "dynamic") = none ∧ mapLookup Y (.atom "dynamic") = none
  · have eX : lower (.map X) = .map X ∧ upper (.map X) = .map X := by simp [lower, upper, rmDyn_static st.1, st.1]
    have eY : lower (.map Y) = .map Y ∧ upper (.map Y) = .map Y := by simp [lower, upper, rmDyn_static st.2, st.2]
    rw [eX.1] at la; rw [eY.1] at lb
    obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).inter la lb
    obtain ⟨gc, lc, uc⟩ := de_gd dc
    exact ⟨c, run _ (by omega), gc, fun v => by rw [lc, eX.1, eY.1]; exact sem v,
      fun v => by rw [uc, eX.2, eY.2]; exact sem v⟩
  have g : (mapLookup X (.atom "dynamic")).isSome ∨ (mapLookup Y (.atom "dynamic")).isSome := by
    cases hX : mapLookup X (.atom "dynamic") <;> cases hY : mapLookup Y (.atom "dynamic") <;> simp_all
  obtain ⟨c, hc, run, sem, I, rfl, look, up⟩ := inter_aligned (bare_inter_op (L := level t n) (n := k + 1) (by omega))
    (bare_inter_op (n := k) (by omega)) (fun _ _ _ r t => bare_inter_dyn _ r t) ha hb
  have st := stepOf (level t n).ef (level t n).none
  have dl : DE (level t n).E (lower (.map I)) :=
    Or.inr ⟨_, rfl, interL_descr st.ks st.fc (by omega) (de_map la) (de_map lb) look⟩
  have du : DE (level t n).E (upper (.map I)) := by
    rcases up with ⟨none, -⟩ | run'
    · rw [show upper (.map I) = lower (.map I) by simp [upper, lower, none, rmDyn_static none]]; exact dl
    · rw [dyn_inter_bare _ ha.up_tc hb.up_tc] at run'
      obtain ⟨c', dc', rc', -⟩ := (ef_next t n).inter ua ub
      have e := (rc' (k + 1) (by omega)).symm.trans run'
      simp only [Except.ok.injEq] at e
      rw [← e]; exact dc'
  exact ⟨_, (inter_run_grad _ g).trans run, ⟨hc, dl, du⟩, bounds _ sem⟩

theorem boolAtom_inj {p q : Bool} (h : boolAtom p = boolAtom q) : p = q := by
  cases p <;> cases q <;> simp_all [boolAtom]

/-- Equality of gradual types whose function types are arrows compares both bounds exactly. -/
theorem gd_eq {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (boolAtom (bp (∀ v : PN t n,
      (denD (lower a) v ↔ denD (lower b) v) ∧ (denD (upper a) v ↔ denD (upper b) v)))) := by
  obtain ⟨s₁, s₂, r₁, r₂, r₃⟩ := gd_equal ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 hm
  rw [gd_sub ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 hm, Except.ok.injEq] at r₁
  rw [gd_sub gb.1 ga.1 gb.2.1 gb.2.2 ga.2.1 ga.2.2 hm, Except.ok.injEq] at r₂
  rw [r₃, ← boolAtom_inj r₁, ← boolAtom_inj r₂, bp_and]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
  simp only [SubN]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ v
    exact ⟨⟨h₁ v, h₃ v⟩, ⟨h₂ v, h₄ v⟩⟩
  · intro h
    exact ⟨⟨fun v => (h v).1.1, fun v => (h v).2.1⟩, fun v => (h v).1.2, fun v => (h v).2.2⟩

theorem gd_eq_true {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (lo : ∀ v : PN t n, denD (lower a) v ↔ denD (lower b) v) (up : ∀ v : PN t n, denD (upper a) v ↔ denD (upper b) v) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  rw [gd_eq ga gb hm, bp_true.mpr fun v => ⟨lo v, up v⟩]; rfl

/-- A type is a subtype of another exactly when their union is the other. -/
theorem gd_sub_union {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) c b = .ok (boolAtom s) := by
  obtain ⟨c, run, gc, lc, uc⟩ := gd_union ga gb hm
  refine ⟨c, _, run, gd_sub ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 (by omega), ?_⟩
  rw [gd_eq gc gb (by omega)]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
  simp only [SubN, lc, uc]
  constructor
  · intro h; exact ⟨fun v hv => (h v).1.mp (Or.inl hv), fun v hv => (h v).2.mp (Or.inl hv)⟩
  · intro h v; exact ⟨⟨fun h' => h'.elim (h.1 v) id, Or.inr⟩, ⟨fun h' => h'.elim (h.2 v) id, Or.inr⟩⟩

/-- A type is a subtype of another exactly when their intersection is the first. -/
theorem gd_sub_inter {a b : Term} (ga : GD t n a) (gb : GD t n b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) c a = .ok (boolAtom s) := by
  obtain ⟨c, run, gc, lc, uc⟩ := gd_inter ga gb hm
  refine ⟨c, _, run, gd_sub ga.1 gb.1 ga.2.1 ga.2.2 gb.2.1 gb.2.2 (by omega), ?_⟩
  rw [gd_eq gc ga (by omega)]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ?_)
  simp only [SubN, lc, uc]
  constructor
  · intro h; exact ⟨fun v hv => ((h v).1.mpr hv).2, fun v hv => ((h v).2.mpr hv).2⟩
  · intro h v; exact ⟨⟨And.left, fun h' => ⟨h', h.1 v h'⟩⟩, ⟨And.left, fun h' => ⟨h', h.2 v h'⟩⟩⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Differences and negations of static types whose function types are arrows. -/

section
variable {t : Term} {n : Nat}

/-- The static types of the laws are element types of the next level. -/
theorem arrows_static_ok {a : Term} (h : «arrows_static?/2» a (.tuple #[.integer n, t]) = .ok (.atom "true")) :
    DE (level t n).E a := by
  unfold «arrows_static?/2» at h
  simp only [Lynx.Except.andAlso_eq_true] at h
  exact arrows_de (opt_negatable_tc t n a (by simpa [Term.true] using h.1)) h.2

/-- Gradual types whose parts' function types are arrows between nested types, the dynamic part including the
static one. -/
theorem arrows_gradual_gc {m : Nat} (hm : (level t n).K + 15 ≤ m) (descr : Term)
    (h : «arrows_gradual?/2» (D m) descr (.tuple #[.integer n, t]) = .ok Term.true) : GC (level t n) descr := by
  have static : «arrows_static?/2» descr (.tuple #[.integer n, t]) = .ok Term.true → GC (level t n) descr := fun h =>
    GC.tc (arrows_static_ok (by simpa [Term.true] using h))
  unfold «arrows_gradual?/2» at h
  cases descr with
  | map X =>
    cases hD : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, hD] at h; exact static h
    | some Dy =>
      simp only [getMapKeys_single, hD, Option.toList, Erlang.maps.«remove/2», Lynx.Except.ok_bind, Term.true,
        Lynx.Except.andAlso_eq_true, equalExact_eq_decide] at h
      obtain ⟨⟨hS, hDy⟩, hI⟩ := h
      have tS : TC (level t n) (.map (rmDyn X)) := arrows_static_ok hS
      have tD : TC (level t n) Dy := arrows_static_ok hDy
      have sS : DC (level t n) (rmDyn X) := by
        rcases tS with e | ⟨S, e, sS⟩
        · cases e
        · simp only [Term.map.injEq] at e; rw [e]; exact sS
      obtain ⟨c, tc, run, sem⟩ := tc_diff tS tD (m := m) hm
      rw [← rmDyn, run, Lynx.Except.ok_bind] at hI
      have none : ∀ v : TP (level t n), ¬denD c v := by
        rcases tc with rfl | ⟨C, rfl, sC⟩
        · simp [Elixir.Module.Types.Descr.«empty?/1»] at hI
        · exact tc_empty_sound sC (by omega) hI
      refine Or.inr ⟨X, Dy, rfl, hD, tD, sS, fun v hv => ?_⟩
      exact Classical.byContradiction fun hn => none v ((sem v).mpr ⟨(denD_rmDyn X v).mpr hv, hn⟩)
  | _ => simp at h; exact static h

/-- Gradual types whose parts' function types are arrows between nested types: the parts are element types of
the next level. -/
theorem arrows_gradual_ok {m : Nat} (hm : (level t n).K + 15 ≤ m) {a : Term}
    (h : «arrows_gradual?/2» (D m) a (.tuple #[.integer n, t]) = .ok (.atom "true")) :
    GC (level t n) a ∧ DE (level t n).E (lower a) ∧ DE (level t n).E (upper a) :=
  let ga := arrows_gradual_gc hm a h
  ⟨ga, ga.low_tc, ga.up_tc⟩

theorem denN_nil (v : PN t n) : ¬denD (.map []) v := by simp [denD_map, mapLookup, dn_none]

/-- Negations of element types of the next level. -/
theorem next_neg {a : Term} (ha : DE (level t n).E a) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ c, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c ∧ DE (level t n).E c ∧
      ∀ v : PN t n, denD c v ↔ ¬denD a v := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact ⟨_, by simp [Elixir.Module.Types.Descr.«bare_negation/1»], (ef_next t n).none,
      fun v => by simp [denN_nil, denD_term]⟩
  obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).diff (ef_next t n).term (Or.inr ⟨X, rfl, sX⟩)
  exact ⟨c, by simpa [Elixir.Module.Types.Descr.«bare_negation/1», Elixir.Module.Types.Descr.«term/0»] using run m hm,
    dc, fun v => by rw [sem]; simp [denD_term]⟩

/-- Equality of element types of the next level is exact. -/
theorem next_eq_true {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) (h : ∀ v : PN t n, denD a v ↔ denD b v) :
    Elixir.Module.Types.Descr.«equal?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨ga, la, ua⟩ := de_gd ha
  obtain ⟨gb, lb, ub⟩ := de_gd hb
  exact gd_eq_true ga gb hm (fun v => by rw [la, lb]; exact h v) (fun v => by rw [ua, ub]; exact h v)

/-- A static type is a subtype of another exactly when their difference is empty. -/
theorem next_sub_diff {a b : Term} (ha : DE (level t n).E a) (hb : DE (level t n).E b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    ∃ c s, Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s) ∧
      Elixir.Module.Types.Descr.«empty?/1» (D m) c = .ok (boolAtom s) := by
  obtain ⟨c, dc, run, sem, -⟩ := (ef_next t n).diff ha hb
  refine ⟨c, _, run m hm, next_sub ha hb hm, ?_⟩
  rw [next_empty dc hm]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ⟨fun h v h₁ => ?_, fun h v hc => ?_⟩)
  · exact Classical.byContradiction fun h₂ => h v ((sem v).mpr ⟨h₁, h₂⟩)
  · exact ((sem v).mp hc).2 (h v ((sem v).mp hc).1)

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple_fetch_element/3` takes the element at an index, or the top or empty type past the elements. -/
theorem fetch_element (tag : String) (g : tag = "open" ∨ tag = "closed") :
    ∀ (l : List Term) (i : Nat), Elixir.Module.Types.Descr.«tuple_fetch_element/3» (Term.list l) (.integer i) (.atom tag) =
      .ok (if h : i < l.length then .tuple #[l[i], .atom "false"]
        else if tag = "open" then .tuple #[.atom "term", .atom "true"] else .tuple #[.map [], .atom "true"])
  | [], i => by
    rcases g with rfl | rfl <;> simp [Elixir.Module.Types.Descr.«tuple_fetch_element/3», Term.list]
  | x :: l, 0 => by simp [Elixir.Module.Types.Descr.«tuple_fetch_element/3», Term.list]
  | x :: l, j + 1 => by
    have ih := fetch_element tag g l j
    have ne : ((j + 1 : Nat) : Int) ≠ 0 := by omega
    rw [Elixir.Module.Types.Descr.«tuple_fetch_element/3».eq_def]
    simp only [Term.list] at ih ⊢
    by_cases h : j < l.length <;> simp_all
    intro h'; omega

theorem do_take : ∀ (l₁ : List Term) (x : Term) (l₂ acc : List Term),
    Elixir.Module.Types.Descr.«do_tuple_take_element/3» (Term.list (l₁ ++ x :: l₂)) (.integer l₁.length) (Term.list acc) =
      .ok (.tuple #[x, Term.list (acc.reverse ++ l₁ ++ l₂)])
  | [], x, l₂, acc => by
    simp [Elixir.Module.Types.Descr.«do_tuple_take_element/3», Term.list, reverse_list]
  | h :: l₁, x, l₂, acc => by
    have ih := do_take l₁ x l₂ (h :: acc)
    have ne : ((l₁.length + 1 : Nat) : Int) ≠ 0 := by omega
    rw [Elixir.Module.Types.Descr.«do_tuple_take_element/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp_all

theorem do_take_short : ∀ (l acc : List Term) (i : Nat), l.length ≤ i →
    Elixir.Module.Types.Descr.«do_tuple_take_element/3» (Term.list l) (.integer i) (Term.list acc) = .ok (.atom "error")
  | [], acc, i, _ => by simp [Elixir.Module.Types.Descr.«do_tuple_take_element/3»]
  | h :: l, acc, 0, le => by simp at le
  | h :: l, acc, j + 1, le => by
    have ih := do_take_short l (h :: acc) j (by simp at le; omega)
    have ne : ((j + 1 : Nat) : Int) ≠ 0 := by omega
    rw [Elixir.Module.Types.Descr.«do_tuple_take_element/3».eq_def]
    simp only [Term.list] at ih ⊢
    simp_all

/-- `tuple_take_element/3` splits a literal at an index into the element there and a literal of the others. -/
theorem take_mid (tag : String) (g : tag = "open" ∨ tag = "closed") (l₁ : List Term) (x : Term) (l₂ : List Term) :
    ∃ k : Int, Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list (l₁ ++ x :: l₂)) (.integer l₁.length)
      (.atom tag) = .ok (.tuple #[x, .tuple #[.integer k, .atom tag, Term.list (l₁ ++ l₂)]]) ∧
      KeyOk (.tuple #[.integer k, .atom tag, Term.list (l₁ ++ l₂)]) := by
  obtain ⟨k, run, key⟩ := leaf_new_key tag g (l₁ ++ l₂)
  refine ⟨k, ?_, key⟩
  have := do_take l₁ x l₂ []
  simp only [List.reverse_nil, List.nil_append] at this
  simp [Elixir.Module.Types.Descr.«tuple_take_element/3», this, Elixir.Module.Types.Descr.«tuple_new/2», run]

theorem take_closed_short (l : List Term) (i : Nat) (h : l.length ≤ i) :
    Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i) (.atom "closed") = .ok (.atom "empty") := by
  have := do_take_short l [] i h
  simp [Elixir.Module.Types.Descr.«tuple_take_element/3», Term.list] at this ⊢
  simp [this]

theorem take_open_short (l : List Term) (i : Nat) (h : l.length ≤ i) :
    ∃ k : Int, Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i) (.atom "open") =
      .ok (.tuple #[.atom "term", .tuple #[.integer k, .atom "open",
        Term.list (l ++ List.replicate (i - l.length) (Term.atom "term"))]]) ∧
      KeyOk (.tuple #[.integer k, .atom "open", Term.list (l ++ List.replicate (i - l.length) (Term.atom "term"))]) := by
  obtain ⟨k, run, key⟩ := leaf_new_key "open" (Or.inl rfl) (l ++ List.replicate (i - l.length) (.atom "term"))
  refine ⟨k, ?_, key⟩
  have := do_take_short l [] i h
  simp [Elixir.Module.Types.Descr.«tuple_take_element/3», Term.list] at this ⊢
  simp [this, Erlang.erlang.«==/2», fill_list l i h, Elixir.Module.Types.Descr.«tuple_new/2», run]

section
variable {V : Type} {den : Term → V → Prop}

/-- Values of a literal, split at one of its elements. -/
theorem InT.split {c : Bool} : ∀ (l₁ : List Term) (x : Term) (l₂ : List Term) (v₁ : List V) (y : V) (v₂ : List V),
    l₁.length = v₁.length →
    (InT den c (l₁ ++ x :: l₂) (v₁ ++ y :: v₂) ↔ den x y ∧ InT den c (l₁ ++ l₂) (v₁ ++ v₂))
  | [], x, l₂, [], y, v₂, _ => Iff.rfl
  | [], _, _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, _, [], _, _, h => by simp at h
  | e :: l₁, x, l₂, z :: v₁, y, v₂, h => by
    have ih : InT den c (l₁ ++ x :: l₂) (v₁ ++ y :: v₂) ↔ den x y ∧ InT den c (l₁ ++ l₂) (v₁ ++ v₂) :=
      InT.split l₁ x l₂ v₁ y v₂ (by simpa using h)
    simp only [List.cons_append, InT, ih]
    exact ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨b, a, c⟩ => ⟨a, b, c⟩⟩

theorem InT.terms (hterm : ∀ y, den (.atom "term") y) {c : Bool} :
    ∀ (n : Nat) (w : List V), n = w.length → InT den c (List.replicate n (.atom "term")) w
  | 0, [], _ => trivial
  | n + 1, y :: w, h => ⟨hterm y, InT.terms hterm n w (by simpa using h)⟩
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h

theorem InT.open_any (hterm : ∀ y, den (.atom "term") y) :
    ∀ (n : Nat) (w : List V), n ≤ w.length → InT den Bool.false (List.replicate n (.atom "term")) w
  | 0, [], _ => trivial
  | 0, _ :: _, _ => rfl
  | n + 1, y :: w, h => ⟨hterm y, InT.open_any hterm n w (by simp at h; omega)⟩
  | _ + 1, [], h => by simp at h

/-- Values of an open literal shorter than an index, split at that index. -/
theorem InT.split_short (hterm : ∀ y, den (.atom "term") y) :
    ∀ (l : List Term) (v₁ : List V) (y : V) (v₂ : List V), l.length ≤ v₁.length →
      (InT den Bool.false l (v₁ ++ y :: v₂) ↔
        InT den Bool.false (l ++ List.replicate (v₁.length - l.length) (.atom "term")) (v₁ ++ v₂))
  | [], v₁, y, v₂, _ => by
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    refine ⟨fun _ => InT.open_any hterm _ _ (by simp), fun _ => ?_⟩
    cases v₁ <;> exact rfl
  | e :: l, [], y, v₂, h => by simp at h
  | e :: l, z :: v₁, y, v₂, h => by
    have ih := InT.split_short hterm l v₁ y v₂ (by simpa using h)
    simp only [List.cons_append, InT, List.length_cons, Nat.add_sub_add_right, ih]

theorem InT.split_closed : ∀ {l : List Term} {v₁ : List V} {y : V} {v₂ : List V}, l.length ≤ v₁.length →
    ¬InT den Bool.true l (v₁ ++ y :: v₂) := by
  intro l v₁ y v₂ h h'
  have := h'.closed_length
  simp at this; omega

end

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Lines of tuple BDDs: a tag, element types, and negated literals. -/
def TLine (E : Term → Prop) (L : Term) : Prop :=
  ∃ (tag : String) (l negs : List Term), L = .tuple #[.atom tag, Term.list l, Term.list negs] ∧
    (tag = "open" ∨ tag = "closed") ∧ (∀ e ∈ l, E e) ∧ ∀ t ∈ negs, TupleLit E t

/-- Tuples of values in a line. -/
def InLine (den : Term → V → Prop) (L : Term) (v : List V) : Prop :=
  ∃ (tag : String) (l negs : List Term), L = .tuple #[.atom tag, Term.list l, Term.list negs] ∧
    InT den (tag == "closed") l v ∧ ∀ N ∈ negs, ¬LitSem den N v

theorem inLine_iff {tag : String} {l negs : List Term} {v : List V} :
    InLine den (.tuple #[.atom tag, Term.list l, Term.list negs]) v ↔
      InT den (tag == "closed") l v ∧ ∀ N ∈ negs, ¬LitSem den N v := by
  constructor
  · rintro ⟨tag', l', negs', e, h, hn⟩
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₁
    rw [e₁, list_inj e₂, list_inj e₃]
    exact ⟨h, hn⟩
  · intro h; exact ⟨tag, l, negs, rfl, h⟩

/-- `tuple_bdd_to_dnf/4` lists the lines of a BDD: the values of the path through it, outside its negations. -/
theorem dnf_tuple (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 1 ≤ m) {ok : Term → Prop}
    {r : Term} (wr : Bdd ok r) (okT : ∀ t, ok t → TupleOk E t) :
    ∀ (acc : List Term) (pos : Term) (negs : List Term), TuplePos E pos → (∀ t ∈ negs, TupleLit E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) (Term.list acc) pos (Term.list negs) r =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, TLine E L) ∧
        ∀ v, (∃ L ∈ lines, InLine den L v) ↔
          (InPos den pos v ∧ (∀ N ∈ negs, ¬LitSem den N v) ∧ eval (valT E den v) r = Bool.true) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) →
    ∀ (acc : List Term) (pos : Term) (negs : List Term), TuplePos E pos → (∀ t ∈ negs, TupleLit E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) (Term.list acc) pos (Term.list negs) r =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, TLine E L) ∧
        ∀ v, (∃ L ∈ lines, InLine den L v) ↔
          (InPos den pos v ∧ (∀ N ∈ negs, ¬LitSem den N v) ∧ eval (valT E den v) r = Bool.true))
    ?_ ?_ ?_ ?_ ok r wr okT
  · intro ok _ acc pos negs hp lits
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    refine ⟨[.tuple #[.atom tag, Term.list l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp [Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp [inLine_iff, inPos_iff]
  · intro ok _ acc pos negs _ _
    refine ⟨[], ?_, by simp, fun v => by simp⟩
    rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp
  · intro ok k x y okl okLit acc pos negs hp lits
    have hl := okLit _ okl
    rcases inter_sem ops sem hm hp hl with ⟨empty, none⟩ | ⟨pos', run, hp', sem'⟩
    · refine ⟨[], ?_, by simp, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp [empty]
      · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and, eval_leaf]
        intro hv _ e
        exact none v hv (valT_lit sem hl.1 e)
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    refine ⟨[.tuple #[.atom tag, Term.list l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]; simp [run, Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp only [List.mem_singleton, exists_eq_left, inLine_iff, eval_leaf, valT_iff sem hl.1]
      rw [← inPos_iff, sem' v]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit acc pos negs hp lits
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → TupleOk E t := fun t ht => okLit t ht.1
    obtain ⟨Lu, ru, tu, su⟩ := iu okLit' acc pos negs hp lits
    have lits' : ∀ t ∈ lit :: negs, TupleLit E t := fun t mt => by
      rcases List.mem_cons.mp mt with rfl | mt
      · exact hl.1
      · exact lits t mt
    obtain ⟨Lc, runC, tc, sc⟩ : ∃ Lc,
        ((Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit = .ok (.atom "empty") ∧ Lc = []) ∨
          ∃ tag2 l2, Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) pos lit =
              .ok (.tuple #[.atom tag2, Term.list l2]) ∧
            Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) (Term.list (Lu ++ acc)) (.tuple #[.atom tag2, Term.list l2])
              (Term.list negs) c = .ok (Term.list (Lc ++ (Lu ++ acc)))) ∧ (∀ L ∈ Lc, TLine E L) ∧
          ∀ v, (∃ L ∈ Lc, InLine den L v) ↔
            (InPos den pos v ∧ LitSem den lit v ∧ (∀ N ∈ negs, ¬LitSem den N v) ∧ eval (valT E den v) c = Bool.true) := by
      rcases inter_sem ops sem hm hp hl with ⟨empty, none⟩ | ⟨pos2, run, hp2, sem2⟩
      · exact ⟨[], Or.inl ⟨empty, rfl⟩, by simp, fun v => by
          simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
          exact fun hv hlit => absurd hlit (none v hv)⟩
      obtain ⟨Lc, rc, tc, sc⟩ := ic okLit' (Lu ++ acc) pos2 negs hp2 lits
      obtain ⟨tag2, l2, rfl, -⟩ := hp2
      refine ⟨Lc, Or.inr ⟨tag2, l2, run, rc⟩, tc, fun v => ?_⟩
      rw [sc v, sem2 v]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    obtain ⟨Ld, rd, td, sd⟩ := idd okLit' (Lc ++ (Lu ++ acc)) pos (lit :: negs) hp lits'
    rw [list_cons] at rd
    refine ⟨Ld ++ Lc ++ Lu, ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4».eq_def]
      obtain ⟨tag, l, rfl, -⟩ := hp
      rcases runC with ⟨e, rfl⟩ | ⟨tag2, l2, e, rc⟩
      · simp only [List.nil_append] at rd
        simp [ru, e, rd]
      · simp [ru, e, rc, rd]
    · intro L mL
      simp only [List.mem_append] at mL
      rcases mL with (mL | mL) | mL
      · exact td L mL
      · exact tc L mL
      · exact tu L mL
    · have split : (∃ L ∈ Ld ++ Lc ++ Lu, InLine den L v) ↔
          (∃ L ∈ Ld, InLine den L v) ∨ (∃ L ∈ Lc, InLine den L v) ∨ (∃ L ∈ Lu, InLine den L v) := by
        constructor
        · rintro ⟨L, mL, hL⟩
          simp only [List.mem_append] at mL
          rcases mL with (mL | mL) | mL
          · exact Or.inl ⟨L, mL, hL⟩
          · exact Or.inr (Or.inl ⟨L, mL, hL⟩)
          · exact Or.inr (Or.inr ⟨L, mL, hL⟩)
        · rintro (⟨L, mL, hL⟩ | ⟨L, mL, hL⟩ | ⟨L, mL, hL⟩) <;> exact ⟨L, by simp [mL], hL⟩
      rw [split, sd v, sc v, su v, eval_node]
      by_cases hlit : LitSem den lit v
      · have e : valT E den v lit = Bool.true := valT_true hl.1 hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inl ⟨a, b, c⟩) (fun c => Or.inr ⟨a, b, c⟩)⟩
      · have e : valT E den v lit = Bool.false := by
          cases h' : valT E den v lit
          · rfl
          · exact absurd (valT_lit sem hl.1 h') hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inr ⟨a, b, c⟩) (fun c => Or.inl ⟨a, b, c⟩)⟩

/-- `tuple_line_elements_empty?/2` finds an empty element, when there is one. -/
theorem elements_exact (ops : ElemOk E K) (sem : ElemSem E K V den Safe) (hS : Safe []) (l : List Term)
    (hl : ∀ e ∈ l, E e) : ∃ b, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D m)
      (Term.list l) (.map []) = .ok (boolAtom b)) ∧ (b = Bool.false → ∀ e ∈ l, Full E K [] e) ∧
      (b = Bool.true → ∃ e ∈ l, ∀ y, ¬den e y) := by
  have each : ∀ e ∈ l, ∃ b, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map []) = .ok (boolAtom b) :=
    fun e me => ops.empty (hl e me) []
  classical
  let res : Term → Bool := fun e => if h : e ∈ l then Classical.choose (each e h) else Bool.false
  have hres : ∀ e ∈ l, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map []) = .ok (boolAtom (res e)) := by
    intro e me m' h
    simp only [res, dite_eq_left me]
    exact Classical.choose_spec (each e me) m' h
  refine ⟨l.any res, fun m hm => ?_, fun no e me => ⟨hl e me, fun m' h => ?_⟩, fun yes => ?_⟩
  · obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    simp only [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2»]
    refine any_list _ _ _ _ res l fun x mx => ?_
    rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2»]
    exact hres x mx n hn
  · have := List.any_eq_false.mp no e me
    rw [hres e me m' h]
    simp_all [boolAtom]
  · obtain ⟨e, me, he⟩ := List.any_eq_true.mp yes
    refine ⟨e, me, fun y hy => ?_⟩
    have := (sem.empty (hl e me) hS (Nat.le_refl K) (hres e me K (Nat.le_refl K))).mp he
    exact this y hy

/-- Lines either hold a tuple of values or are empty. -/
theorem line_keep (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (hS : Safe []) {L : Term}
    (hL : TLine E L) : ∃ keep : Bool, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ v, InLine den L v) := by
  obtain ⟨tag, l, negs, rfl, gt, el, lits⟩ := hL
  obtain ⟨b, check, full, empty⟩ := elements_exact ops sem hS l el
  cases b
  · have full := full rfl
    by_cases ex : ∃ v, InLine den (.tuple #[.atom tag, Term.list l, Term.list negs]) v
    · refine ⟨Bool.true, fun m acc hm => ?_, by simp [ex]⟩
      obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      obtain ⟨v, hvL⟩ := ex
      obtain ⟨hv, hn'⟩ := inLine_iff.mp hvL
      have f := line_false ops dops sem (m := n) (by omega) [] hS negs lits (tag == "closed") l el v hv hn'
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_with_negations/1-fun-0-/2».pure]
      rcases gt with rfl | rfl <;>
        simp_all [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_with_negations/1-fun-0-/2»,
          Elixir.Module.Types.Descr.«tuple_line_empty?/3», check n (by omega), Lynx.Except.orElse, Lynx.Term.isMember]
    · refine ⟨Bool.false, fun m acc hm => ?_, by simp [ex]⟩
      obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      have t := line_complete ops dops sem (m := n) (by omega) [] hS negs lits (tag == "closed") l full
        fun v hv => Classical.byContradiction fun none => ex ⟨v, inLine_iff.mpr ⟨hv, fun N mN hN => none ⟨N, mN, hN⟩⟩⟩
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_with_negations/1-fun-0-/2».pure]
      rcases gt with rfl | rfl <;>
        simp_all [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_with_negations/1-fun-0-/2»,
          Elixir.Module.Types.Descr.«tuple_line_empty?/3», check n (by omega), Lynx.Except.orElse, Lynx.Term.isMember]
  · obtain ⟨e, me, he⟩ := empty rfl
    refine ⟨Bool.false, fun m acc hm => ?_, ?_⟩
    · obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
      rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_to_dnf_with_negations/1-fun-0-/2».pure]
      simp [Elixir.Module.Types.Descr.«-tuple_bdd_to_dnf_with_negations/1-fun-0-/2», check n (by omega),
        Lynx.Except.orElse, Lynx.Term.isMember]
    · simp only [Bool.false_eq_true, false_iff, not_exists]
      intro v hv
      obtain ⟨hv, -⟩ := inLine_iff.mp hv
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem me
      obtain ⟨v₁, y, v₂, -, -, hy, -⟩ := (InT.mid l₁ e l₂).mp hv
      exact he y hy

/-- Folds whose steps compute a function of the element and the accumulator. -/
theorem foldl1_det {K : Nat} (f : Term) (g : Term → Term → Term) :
    ∀ l : List Term, (∀ x ∈ l, ∀ a m, K ≤ m → (D m).pure f #[x, a] = .ok (g x a)) →
      ∀ acc m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list l) = .ok (l.foldl (fun a x => g x a) acc) := by
  intro l
  induction l with
  | nil => intro _ acc m _; simp [Erlang.lists.«foldl_1/3»]
  | cons x xs ih =>
    intro step acc m hm
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only at ih ⊢
    simp only [step x List.mem_cons_self acc m hm, Lynx.Except.ok_bind, List.foldl_cons]
    exact ih (fun y my => step y (List.mem_cons_of_mem _ my)) _ m hm

theorem foldl_det {K : Nat} (mo nm : String) (caps : Array Term) (g : Term → Term → Term) (l : List Term)
    (step : ∀ x ∈ l, ∀ a m, K ≤ m → (D m).pure (.function false mo nm 2 caps) #[x, a] = .ok (g x a)) (acc : Term) {m : Nat}
    (hm : K ≤ m) : Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) =
      .ok (l.foldl (fun a x => g x a) acc) := by
  have := foldl1_det (.function false mo nm 2 caps) g l step acc m hm
  cases l with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem foldl_filter (keep : Term → Bool) : ∀ (l acc : List Term),
    l.foldl (fun a x => if keep x then Term.cons x a else a) (Term.list acc) = Term.list ((l.filter keep).reverse ++ acc)
  | [], acc => by simp
  | x :: l, acc => by
    have ih := foldl_filter keep l
    cases h : keep x
    · simp [h, ih]
    · have := ih (x :: acc)
      simp only [Term.list] at this
      simp [h, this]

/-- `tuple_bdd_to_dnf_with_negations/1` lists the non-empty lines of a BDD. -/
theorem dnf_neg (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (hS : Safe []) {m : Nat}
    (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (TLit E) r) :
    ∃ lines : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_with_negations/1» (D m) r =
        .ok (Term.list lines) ∧ (∀ L ∈ lines, TLine E L ∧ ∃ v, InLine den L v) ∧
      ∀ v, eval (valT E den v) r = Bool.true ↔ ∃ L ∈ lines, InLine den L v := by
  obtain ⟨all, run, tl, sl⟩ := dnf_tuple ops sem (m := m) (by omega) wr (fun t h => h.1) [] (.tuple #[.atom "open", .nil]) []
    ⟨"open", [], rfl, Or.inl rfl, by simp⟩ (by simp)
  have keeps : ∀ L ∈ all, ∃ keep : Bool, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ v, InLine den L v) :=
    fun L mL => line_keep ops dops sem hS (tl L mL)
  classical
  let keep : Term → Bool := fun L => if h : L ∈ all then Classical.choose (keeps L h) else Bool.false
  have hk : ∀ L ∈ all, (∀ m acc, K + 2 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep L then .cons L acc else acc)) ∧ (keep L = Bool.true ↔ ∃ v, InLine den L v) := by
    intro L mL
    simp only [keep, dite_eq_left mL]
    exact Classical.choose_spec (keeps L mL)
  have fold := foldl_det (K := K + 2) "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" #[]
    (fun x a => if keep x then .cons x a else a) all (fun x mx a m hm => (hk x mx).1 m a hm) .nil hm
  have e := foldl_filter keep all []
  simp only [List.append_nil] at e
  simp only [Term.list] at e
  refine ⟨(all.filter keep).reverse, ?_, fun L mL => ?_, fun v => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_with_negations/1»]
    have run' : Elixir.Module.Types.Descr.«tuple_bdd_to_dnf/4» (D m) .nil (.tuple #[.atom "open", .nil]) .nil r =
        .ok (Term.list all) := by simpa using run
    simp only [run', Lynx.Except.ok_bind]
    rw [show (do
        let f ← (pure (Term.function false "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[]) :
          Except Exception Term)
        Erlang.lists.«foldl/3» (D m) f .nil (Term.list all)) =
        Erlang.lists.«foldl/3» (D m) (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_to_dnf_with_negations/1-fun-0-" 2 #[])
          .nil (Term.list all) from rfl, fold, e]
  · simp only [List.mem_reverse, List.mem_filter] at mL
    exact ⟨tl L mL.1, (hk L mL.1).2.mp mL.2⟩
  · have hp : InPos den (.tuple #[.atom "open", .nil]) v := ⟨"open", [], rfl, InT.open_nil v⟩
    rw [← (by simpa [hp] using sl v : (∃ L ∈ all, InLine den L v) ↔ eval (valT E den v) r = Bool.true)]
    constructor
    · rintro ⟨L, mL, hL⟩
      exact ⟨L, by simp [mL, (hk L mL).2.mpr ⟨v, hL⟩], hL⟩
    · rintro ⟨L, mL, hL⟩
      simp only [List.mem_reverse, List.mem_filter] at mL
      exact ⟨L, mL.1, hL⟩

/-- Folds whose steps keep a relation between the elements folded so far and the accumulator. -/
theorem foldl1_rel {K : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧ ∀ m, K ≤ m → (D m).pure f #[x, a] = .ok a') :
    ∀ (rest pre : List Term) acc, (∀ x ∈ rest, x ∈ l) → R pre acc →
      ∃ r, R (pre ++ rest) r ∧ ∀ m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r := by
  intro rest
  induction rest with
  | nil => intro pre acc _ h; exact ⟨acc, by simpa using h, fun m _ => by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro pre acc sub h
    obtain ⟨a', h', run⟩ := step pre x acc (sub x List.mem_cons_self) h
    obtain ⟨r, hr, rest⟩ := ih (pre ++ [x]) a' (fun y my => sub y (List.mem_cons_of_mem _ my)) h'
    refine ⟨r, by simpa using hr, fun m hm => ?_⟩
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only at rest ⊢
    simp only [run m hm, Lynx.Except.ok_bind]
    exact rest m hm

theorem foldl_rel {K : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧ ∀ m, K ≤ m →
      (D m).pure (.function false mo nm 2 caps) #[x, a] = .ok a') (acc : Term) (h : R [] acc) :
    ∃ r, R l r ∧ ∀ m, K ≤ m → Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) = .ok r := by
  obtain ⟨r, hr, run⟩ := foldl1_rel (.function false mo nm 2 caps) R l step l [] acc (fun _ h => h) h
  refine ⟨r, by simpa using hr, fun m hm => ?_⟩
  have := run m hm
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using this
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem foldl1_rel_at {m : Nat} (f : Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧ (D m).pure f #[x, a] = .ok a') :
    ∀ (rest pre : List Term) acc, (∀ x ∈ rest, x ∈ l) → R pre acc →
      ∃ r, R (pre ++ rest) r ∧ Erlang.lists.«foldl_1/3» (D m) f acc (Term.list rest) = .ok r := by
  intro rest
  induction rest with
  | nil => intro pre acc _ h; exact ⟨acc, by simpa using h, by simp [Erlang.lists.«foldl_1/3»]⟩
  | cons x xs ih =>
    intro pre acc sub h
    obtain ⟨a', h', run⟩ := step pre x acc (sub x List.mem_cons_self) h
    obtain ⟨r, hr, rest⟩ := ih (pre ++ [x]) a' (fun y my => sub y (List.mem_cons_of_mem _ my)) h'
    refine ⟨r, by simpa using hr, ?_⟩
    rw [Erlang.lists.«foldl_1/3».eq_def]
    simp only at rest ⊢
    simp only [run, Lynx.Except.ok_bind]
    exact rest

/-- Folds at a call depth whose steps keep a relation between the elements folded so far and the accumulator. -/
theorem foldl_rel_at {m : Nat} (mo nm : String) (caps : Array Term) (R : List Term → Term → Prop) (l : List Term)
    (step : ∀ pre x a, x ∈ l → R pre a → ∃ a', R (pre ++ [x]) a' ∧
      (D m).pure (.function false mo nm 2 caps) #[x, a] = .ok a') (acc : Term) (h : R [] acc) :
    ∃ r, R l r ∧ Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) = .ok r := by
  obtain ⟨r, hr, run⟩ := foldl1_rel_at (.function false mo nm 2 caps) R l step l [] acc (fun _ h => h) h
  refine ⟨r, by simpa using hr, ?_⟩
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using run
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at run
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using run

theorem foldl1_lists_at {m : Nat} (f : Term) (h : Term → List Term) :
    ∀ l : List Term, (∀ x ∈ l, ∀ (A : List Term), (D m).pure f #[x, Term.list A] = .ok (Term.list (h x ++ A))) →
      ∀ A, Erlang.lists.«foldl_1/3» (D m) f (Term.list A) (Term.list l) =
        .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  intro l
  induction l with
  | nil => intro _ A; simp [Erlang.lists.«foldl_1/3»]
  | cons x xs ih =>
    intro step A
    rw [Erlang.lists.«foldl_1/3».eq_def]
    have tail := ih (fun y my => step y (List.mem_cons_of_mem _ my)) (h x ++ A)
    simp only at tail step ⊢
    simp only [step x List.mem_cons_self A, Lynx.Except.ok_bind]
    simpa using tail

/-- Folds at a call depth whose steps prepend a list to the accumulator. -/
theorem foldl_lists_at {m : Nat} (mo nm : String) (caps : Array Term) (h : Term → List Term) (l : List Term)
    (step : ∀ x ∈ l, ∀ (A : List Term),
      (D m).pure (.function false mo nm 2 caps) #[x, Term.list A] = .ok (Term.list (h x ++ A))) (A : List Term) :
    Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) (Term.list A) (Term.list l) =
      .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  have := foldl1_lists_at (.function false mo nm 2 caps) h l step A
  cases l with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

/-- Folds whose steps prepend a list to the accumulator. -/
theorem foldl1_lists {K : Nat} (f : Term) (h : Term → List Term) :
    ∀ l : List Term, (∀ x ∈ l, ∀ (A : List Term) m, K ≤ m → (D m).pure f #[x, Term.list A] = .ok (Term.list (h x ++ A))) →
      ∀ A m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f (Term.list A) (Term.list l) =
        .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  intro l
  induction l with
  | nil => intro _ A m _; simp [Erlang.lists.«foldl_1/3»]
  | cons x xs ih =>
    intro step A m hm
    rw [Erlang.lists.«foldl_1/3».eq_def]
    have tail := ih (fun y my => step y (List.mem_cons_of_mem _ my)) (h x ++ A) m hm
    simp only at tail step ⊢
    simp only [step x List.mem_cons_self A m hm, Lynx.Except.ok_bind]
    simpa using tail

theorem foldl_lists {K : Nat} (mo nm : String) (caps : Array Term) (h : Term → List Term) (l : List Term)
    (step : ∀ x ∈ l, ∀ (A : List Term) m, K ≤ m →
      (D m).pure (.function false mo nm 2 caps) #[x, Term.list A] = .ok (Term.list (h x ++ A))) (A : List Term) {m : Nat}
    (hm : K ≤ m) : Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) (Term.list A) (Term.list l) =
      .ok (Term.list (l.reverse.flatMap h ++ A)) := by
  have := foldl1_lists (.function false mo nm 2 caps) h l step A m hm
  cases l with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Pairs of an element type and a tuple type, as tuples split at an index. -/
def PairOk (E : Term → Prop) (p : Term) : Prop := ∃ f b, p = .tuple #[f, b] ∧ E f ∧ TField E b

/-- A value and the remaining tuple of values in a pair. -/
def PairIn (E : Term → Prop) (den : Term → V → Prop) (p : Term) (y : V) (w : List V) : Prop :=
  ∃ f b, p = .tuple #[f, b] ∧ den f y ∧ denTF E den b w = Bool.true

theorem pairIn_iff {f b : Term} {y : V} {w : List V} :
    PairIn E den (.tuple #[f, b]) y w ↔ den f y ∧ denTF E den b w = Bool.true := by
  constructor
  · rintro ⟨f', b', e, h₁, h₂⟩
    simp only [Term.tuple.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact ⟨h₁, h₂⟩
  · intro h; exact ⟨f, b, rfl, h⟩

theorem tleaf_field {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e)
    (key : KeyOk (.tuple #[.integer k, .atom tag, Term.list l])) : TField E (.tuple #[.integer k, .atom tag, Term.list l]) := by
  by_cases top : tag = "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨k, tag, l, rfl, g, hl⟩, ?_⟩, key⟩)
    rintro ⟨k', e⟩
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₂
    cases l with
    | nil => exact top ⟨e₂, rfl⟩
    | cons _ _ => simp [Term.list] at e₃

/-- `tuple_take_element/3` splits a literal at an index into a pair, or finds no tuple long enough. -/
theorem take_pair (ef : EF nd E V den tl K) {tag : String} (g : tag = "open" ∨ tag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) (i : Nat) : ∃ res, Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i)
      (.atom tag) = .ok res ∧
      ((res = .atom "empty" ∧ ∀ (v₁ : List V) y v₂, v₁.length = i → ¬InT den (tag == "closed") l (v₁ ++ y :: v₂)) ∨
        (PairOk E res ∧ res ≠ .atom "empty" ∧ (∀ y (w : List V), PairIn E den res y w → i ≤ w.length) ∧
          ∀ (v₁ : List V) y v₂, v₁.length = i →
          (InT den (tag == "closed") l (v₁ ++ y :: v₂) ↔ PairIn E den res y (v₁ ++ v₂)))) := by
  by_cases short : l.length ≤ i
  · rcases g with rfl | rfl
    · obtain ⟨k, run, key⟩ := take_open_short l i short
      have hl' : ∀ e ∈ l ++ List.replicate (i - l.length) (.atom "term"), E e := by
        intro e me
        rcases List.mem_append.mp me with me | me
        · exact hl e me
        · rw [List.eq_of_mem_replicate me]; exact ef.term
      refine ⟨_, run, Or.inr ⟨⟨_, _, rfl, ef.term, tleaf_field (Or.inl rfl) hl' key⟩, by simp, fun y w hw => ?_,
        fun v₁ y v₂ len => ?_⟩⟩
      · rw [pairIn_iff, denTF_leaf ef (Or.inl rfl) hl', vT_lit ef (Or.inl rfl) hl'] at hw
        have := hw.2.length_le
        simp at this; omega
      rw [pairIn_iff, denTF_leaf ef (Or.inl rfl) hl', vT_lit ef (Or.inl rfl) hl']
      have := InT.split_short (den := den) ef.den_term l v₁ y v₂ (by omega)
      rw [len] at this
      simpa [ef.den_term y] using this
    · exact ⟨_, take_closed_short l i short, Or.inl ⟨rfl, fun v₁ y v₂ len h => InT.split_closed (by omega) h⟩⟩
  · obtain ⟨l₁, x, l₂, rfl, len₁⟩ : ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ List.length l₁ = i := by
      refine ⟨l.take i, l[i]'(by omega), l.drop (i + 1), ?_, by simp; omega⟩
      simp
    obtain ⟨k, run, key⟩ := take_mid tag g l₁ x l₂
    rw [len₁] at run
    have hx : E x := hl x (by simp)
    have hl' : ∀ e ∈ l₁ ++ l₂, E e := fun e me => hl e (by
      rcases List.mem_append.mp me with me | me <;> simp [me])
    refine ⟨_, run, Or.inr ⟨⟨_, _, rfl, hx, tleaf_field g hl' key⟩, by simp, fun y w hw => ?_, fun v₁ y v₂ len => ?_⟩⟩
    · rw [pairIn_iff, denTF_leaf ef g hl', vT_lit ef g hl'] at hw
      have := hw.2.length_le
      simp at this; omega
    rw [pairIn_iff, denTF_leaf ef g hl', vT_lit ef g hl']
    exact InT.split l₁ x l₂ v₁ y v₂ (by omega)

open Classical in
/-- The pair a negated literal splits into at an index, if any. -/
noncomputable def splitH (i : Nat) (N : Term) : List Term :=
  match N with
  | .tuple ⟨[_, tag, els]⟩ =>
    match Elixir.Module.Types.Descr.«tuple_take_element/3» els (.integer i) tag with
    | .ok r => if r = .atom "empty" then [] else [r]
    | .error _ => []
  | _ => []

/-- `tuple_split_negative_pairs/2` splits the negated literals of a line at an index. -/
theorem split_pairs (ef : EF nd E V den tl K) (negs : List Term) (lits : ∀ N ∈ negs, TupleLit E N) (i : Nat) {m : Nat} :
    ∃ P, Elixir.Module.Types.Descr.«tuple_split_negative_pairs/2» (D m) (Term.list negs) (.integer i) = .ok (Term.list P) ∧
      (∀ p ∈ P, PairOk E p) ∧ ∀ (v₁ : List V) y v₂, v₁.length = i →
        ((∃ N ∈ negs, LitSem den N (v₁ ++ y :: v₂)) ↔ ∃ p ∈ P, PairIn E den p y (v₁ ++ v₂)) := by
  have each : ∀ N ∈ negs, (∀ (A : List Term) m', 0 ≤ m' →
      (D m').pure (.function false "Elixir.Module.Types.Descr" "-tuple_split_negative_pairs/2-fun-0-" 2 #[.integer i])
        #[N, Term.list A] = .ok (Term.list (splitH i N ++ A))) ∧ (∀ p ∈ splitH i N, PairOk E p) ∧
      ∀ (v₁ : List V) y v₂, v₁.length = i →
        (LitSem den N (v₁ ++ y :: v₂) ↔ ∃ p ∈ splitH i N, PairIn E den p y (v₁ ++ v₂)) := by
    intro N mN
    obtain ⟨k, tag, l, rfl, g, hl⟩ := lits N mN
    obtain ⟨res, run, ⟨rfl, none⟩ | ⟨ok, ne, -, sem⟩⟩ := take_pair ef g hl i
    · have h : splitH i (.tuple #[.integer k, .atom tag, Term.list l]) = [] := by simp [splitH, run]
      refine ⟨fun A m' _ => ?_, by simp [h], fun v₁ y v₂ len => ?_⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_split_negative_pairs/2-fun-0-/2».pure, h]
        simp [Elixir.Module.Types.Descr.«-tuple_split_negative_pairs/2-fun-0-/3», run]
      · simp only [h, List.not_mem_nil, false_and, exists_false, iff_false]
        exact fun hN => none v₁ y v₂ len (lit_sem hN)
    · have h : splitH i (.tuple #[.integer k, .atom tag, Term.list l]) = [res] := by simp [splitH, run, ne]
      refine ⟨fun A m' _ => ?_, by simp [h, ok], fun v₁ y v₂ len => ?_⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_split_negative_pairs/2-fun-0-/2».pure, h]
        simp only [Elixir.Module.Types.Descr.«-tuple_split_negative_pairs/2-fun-0-/3», run, Lynx.Except.ok_bind]
        rfl
      · simp only [h, List.mem_singleton, exists_eq_left]
        rw [← sem v₁ y v₂ len]
        exact ⟨lit_sem, fun hv => ⟨k, tag, l, rfl, hv⟩⟩
  have fold := foldl_lists (K := 0) "Elixir.Module.Types.Descr" "-tuple_split_negative_pairs/2-fun-0-" #[.integer i]
    (splitH i) negs (fun N mN A m' h => (each N mN).1 A m' h) [] (m := m) (Nat.zero_le _)
  refine ⟨negs.reverse.flatMap (splitH i), ?_, fun p mp => ?_, fun v₁ y v₂ len => ?_⟩
  · simpa [Elixir.Module.Types.Descr.«tuple_split_negative_pairs/2»] using fold
  · simp only [List.mem_flatMap, List.mem_reverse] at mp
    obtain ⟨N, mN, mp⟩ := mp
    exact (each N mN).2.1 p mp
  · simp only [List.mem_flatMap, List.mem_reverse]
    constructor
    · rintro ⟨N, mN, hN⟩
      obtain ⟨p, mp, hp⟩ := ((each N mN).2.2 v₁ y v₂ len).mp hN
      exact ⟨p, ⟨N, mN, mp⟩, hp⟩
    · rintro ⟨p, ⟨N, mN, mp⟩, hp⟩
      exact ⟨N, mN, ((each N mN).2.2 v₁ y v₂ len).mpr ⟨p, mp, hp⟩⟩

/-- The union of the tuple types of pairs. -/
theorem union_pairs (P : List Term) (hP : ∀ p ∈ P, PairOk E p) :
    ∃ u, TField E u ∧ (∀ w, denTF E den u w = Bool.true ↔ ∃ p ∈ P, ∃ f b, p = .tuple #[f, b] ∧ denTF E den b w = Bool.true) ∧
      ∀ m, Erlang.lists.«foldl/3» (D m)
        (.function false "Elixir.Module.Types.Descr" "-tuple_pair_projection_keeps_full_fst?/2-fun-0-" 2 #[])
        (.atom "bdd_bot") (Term.list P) = .ok u := by
  obtain ⟨u, ⟨tu, su⟩, run⟩ := foldl_rel (K := 0) "Elixir.Module.Types.Descr" "-tuple_pair_projection_keeps_full_fst?/2-fun-0-" #[]
    (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔
      ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ denTF E den b w = Bool.true) P
    (fun pre x a mx ⟨ta, sa⟩ => by
      obtain ⟨f, b, rfl, -, fb⟩ := hP x mx
      obtain ⟨r, run, tr, sr, -⟩ := tuple_union_lh (den := den) fb ta
      refine ⟨r, ⟨tr, fun w => ?_⟩, fun m _ => ?_⟩
      · rw [sr, Bool.or_eq_true, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_pair_projection_keeps_full_fst?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_pair_projection_keeps_full_fst?/2-fun-0-/2»] using run)
    (.atom "bdd_bot") ⟨Or.inr Bdd.bot, fun w => by simp [denTF_bot]⟩
  exact ⟨u, tu, su, fun m => run m (Nat.zero_le _)⟩

/-- `tuple_pair_projection_keeps_full_fst?/2` checks for a remaining tuple outside every negated pair. -/
theorem keeps_full (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {b : Term} (hb : TField E b) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2» (D m) (Term.list P) b = .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ w, denTF E den b w = Bool.true ∧
        ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → denTF E den nb w = Bool.false) := by
  obtain ⟨u, tu, su, run⟩ := union_pairs (den := den) P hP
  obtain ⟨d, rd, td, sd, -⟩ := tuple_diff_lh ef hb tu
  obtain ⟨e, re, se⟩ := tuple_empty_exact ef td []
  have se := se (lh d + 1) (by omega) (safeT_nil _)
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2», run m, rd, re m hm,
      Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [sd] at hw
      simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true'] at hw
      refine ⟨w, hw.1, fun p mp f nb e => ?_⟩
      cases h : denTF E den nb w
      · rfl
      · exact absurd ((su w).mpr ⟨p, mp, f, nb, e, h⟩) (by rw [hw.2]; simp)
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro w hw none
      have := (se.mp rfl) w
      rw [sd, hw] at this
      simp only [Bool.true_and, Bool.not_eq_false'] at this
      obtain ⟨p, mp, f, nb, e, h⟩ := (su w).mp this
      rw [none p mp f nb e] at h
      cases h

/-- Lists of pairs whose tuple types are not empty. -/
def QOk (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) : Prop :=
  ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ E f ∧ TField E b ∧ ∃ w, denTF E den b w = Bool.true

/-- A value and a remaining tuple of values in some pair. -/
def InPairs (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) (y : V) (w : List V) : Prop :=
  ∃ p ∈ Q, PairIn E den p y w

/-- Lists of pairs whose element types have values. -/
def QF (den : Term → V → Prop) (Q : List Term) : Prop := ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ ∃ y, den f y

theorem empty_bool (ef : EF nd E V den tl K) {a : Term} (ha : E a) {m : Nat} (hm : K ≤ m) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ v, ¬den a v) :=
  let ⟨b, run, sem⟩ := ef.empty_pub ha; ⟨b, run m hm, sem⟩

/-- `prepend_tuple_pair_unless_empty_diff/4` keeps the pair of the difference, unless it is empty. -/
theorem prepend_pair (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f nv b : Term} (hf : E f) (hnv : E nv)
    (hb : TField E b) (nb : ∃ w, denTF E den b w = Bool.true) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«prepend_tuple_pair_unless_empty_diff/4» (D m) f nv b (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ QOk E den new ∧
      (∀ y w, InPairs E den new y w ↔ (den f y ∧ ¬den nv y) ∧ denTF E den b w = Bool.true) ∧ QF den new := by
  obtain ⟨d, hd, rd, sd⟩ := ef.opt_diff [] hf hnv hm
  obtain ⟨e, re, se⟩ := empty_bool ef hd hm
  cases e
  · refine ⟨[.tuple #[d, b]], fun A => ?_, ?_, fun y w => ?_, fun p mp => ?_⟩
    · simp [Elixir.Module.Types.Descr.«prepend_tuple_pair_unless_empty_diff/4»,
        Elixir.Module.Types.Descr.«opt_difference/2», rd, re, Lynx.Term.isMember, Term.list]
    · intro p mp; simp at mp; subst mp; exact ⟨d, b, rfl, hd, hb, nb⟩
    · simp [InPairs, pairIn_iff, sd]
    · simp at mp; subst mp
      exact ⟨d, b, rfl, Classical.byContradiction fun none => by
        have := se.mpr fun v hv => none ⟨v, hv⟩
        cases this⟩
  · refine ⟨[], fun A => ?_, by simp [QOk], fun y w => ?_, by simp [QF]⟩
    · simp [Elixir.Module.Types.Descr.«prepend_tuple_pair_unless_empty_diff/4»,
        Elixir.Module.Types.Descr.«opt_difference/2», rd, re, Lynx.Term.isMember]
    · simp only [InPairs, List.not_mem_nil, false_and, exists_false, false_iff, not_and]
      intro h₁ _
      exact se.mp rfl y ((sd y).mpr h₁)

/-- One step of `tuple_project_negative_pairs/3`: a pair minus a negated pair, as pairs of non-empty tuple types. -/
theorem project_step (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {nv nb x : Term} (hnv : E nv)
    (hnb : TField E nb) (hx : QOk E den [x]) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4» (D m) nb nv x (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ QOk E den new ∧
      (∀ y w, InPairs E den new y w ↔ PairIn E den x y w ∧ ¬(den nv y ∧ denTF E den nb w = Bool.true)) ∧
        (QF den [x] → QF den new) := by
  obtain ⟨f, b, rfl, hf, hb, nbw⟩ := hx _ List.mem_cons_self
  obtain ⟨ib, rib, tib, sib, -⟩ := tuple_inter_lh (den := den) hb hnb
  obtain ⟨eib, reib, seib⟩ := tuple_empty_exact ef tib []
  have seib := seib (lh ib + 1) (by omega) (safeT_nil _)
  obtain ⟨i_f, hif, rif, sif⟩ := ef.opt_inter [] hf hnv (show K ≤ m by omega)
  obtain ⟨e1, re1, se1⟩ := empty_bool ef hif (show K ≤ m by omega)
  obtain ⟨db, rdb, tdb, sdb, -⟩ := tuple_diff_lh ef hb hnb
  obtain ⟨e2, re2, se2⟩ := tuple_empty_exact ef tdb []
  have se2 := se2 (lh db + 1) (by omega) (safeT_nil _)
  obtain ⟨pnew, rp, qp, sp, fp⟩ := prepend_pair ef (m := m) (by omega) hf hnv hb nbw
  have keepSem : ∀ y w, InPairs E den [.tuple #[f, b]] y w ↔ PairIn E den (.tuple #[f, b]) y w := fun y w => by
    simp [InPairs]
  by_cases keep : (∃ k r, nb = .tuple #[k, .atom "closed", r]) ∧ eib = Bool.true
  · obtain ⟨⟨k, r, rfl⟩, rfl⟩ := keep
    refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun y w => ?_, id⟩
    · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
      simp [rib, reib m hm, Lynx.Term.isMember, Term.list]
    · rw [keepSem, pairIn_iff]
      refine ⟨fun h => ⟨h, fun ⟨_, h'⟩ => ?_⟩, fun h => h.1⟩
      have := seib.mp rfl w
      rw [sib, h.2, h'] at this
      cases this
  -- The pair meets the negated pair: the intersection of the remaining tuples is not known to be empty.
  cases e1
  · cases e2
    · refine ⟨pnew ++ [.tuple #[i_f, db]], fun A => ?_, ?_, fun y w => ?_, fun _ p mp => ?_⟩
      · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
        have rp' := rp (.tuple #[i_f, db] :: A)
        simp only [Term.list] at rp'
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb,
            re2 m hm, rp']
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb, re2 m hm, rp']
      · intro p mp
        rcases List.mem_append.mp mp with mp | mp
        · exact qp p mp
        · simp at mp; subst mp
          refine ⟨i_f, db, rfl, hif, tdb, ?_⟩
          exact Classical.byContradiction fun none => by
            have := se2.mpr fun v => by
              cases h : denTF E den db v
              · rfl
              · exact absurd ⟨v, h⟩ none
            cases this
      · simp only [InPairs, List.mem_append, List.mem_singleton] at sp ⊢
        rw [pairIn_iff]
        constructor
        · rintro ⟨p, mp | rfl, hp⟩
          · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (sp y w).mp ⟨p, mp, hp⟩
            exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
          · rw [pairIn_iff, sif, sdb] at hp
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
            refine ⟨⟨hp.1.1, hp.2.1⟩, fun h => ?_⟩
            rw [h.2] at hp; cases hp.2.2
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩
          by_cases hn : den nv y
          · refine ⟨_, Or.inr rfl, ?_⟩
            rw [pairIn_iff, sif, sdb, h₂]
            cases h : denTF E den nb w
            · exact ⟨⟨h₁, hn⟩, rfl⟩
            · exact absurd ⟨hn, h⟩ h₃
          · obtain ⟨p, mp, hp⟩ := (sp y w).mpr ⟨⟨h₁, hn⟩, h₂⟩
            exact ⟨p, Or.inl mp, hp⟩
      · rcases List.mem_append.mp mp with mp | mp
        · exact fp p mp
        · simp at mp; subst mp
          exact ⟨i_f, db, rfl, Classical.byContradiction fun none => by
            have := se1.mpr fun v hv => none ⟨v, hv⟩
            cases this⟩
    · refine ⟨pnew, fun A => ?_, qp, fun y w => ?_, fun _ => fp⟩
      · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb, re2 m hm, rp A]
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, rdb, re2 m hm, rp A]
      · rw [sp, pairIn_iff]
        have cover : ∀ w, denTF E den b w = Bool.true → denTF E den nb w = Bool.true := fun w h => by
          have := se2.mp rfl w
          rw [sdb, h] at this
          simpa using this
        constructor
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, fun hn => h₃ ⟨hn, cover w h₂⟩⟩, h₂⟩
  · refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun y w => ?_, id⟩
    · rw [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4».eq_def]
      by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
      · obtain ⟨k, r, rfl⟩ := hc
        have : eib = Bool.false := by
          cases eib
          · rfl
          · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
        subst this
        simp [rib, reib m hm, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, Term.list]
      · simp only
        split
        · exact absurd ⟨_, _, rfl⟩ hc
        · simp [Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_intersection/2», rif, re1, Term.list]
    · rw [keepSem, pairIn_iff]
      refine ⟨fun h => ⟨h, fun h' => (se1.mp rfl) y ((sif y).mpr ⟨h.1, h'.1⟩)⟩, fun h => h.1⟩

/-- `tuple_project_negative_pairs/3` splits a pair minus negated pairs into pairs of non-empty tuple types. -/
theorem project_pairs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {value rest : Term} (hv : E value) (hr : TField E rest) (nr : ∃ w, denTF E den rest w = Bool.true) :
    ∃ Q, Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» (D (n + 2)) (Term.list P) value rest =
        .ok (Term.list Q) ∧ QOk E den Q ∧
      (∀ y w, InPairs E den Q y w ↔ den value y ∧ denTF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬PairIn E den p y w) ∧
        ((∃ y, den value y) → QF den Q) := by
  obtain ⟨r, ⟨Q, rfl, qQ, sQ, fQ⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr"
    "-tuple_project_negative_pairs/3-fun-1-" #[]
    (fun pre a => ∃ Q, a = Term.list Q ∧ QOk E den Q ∧ (∀ y w, InPairs E den Q y w ↔
      den value y ∧ denTF E den rest w = Bool.true ∧ ∀ p ∈ pre, ¬PairIn E den p y w) ∧
      ((∃ y, den value y) → QF den Q)) P
    (fun pre x a mx ⟨Q, ea, qQ, sQ, fQ⟩ => by
      subst ea
      obtain ⟨nv, nb, rfl, hnv, hnb⟩ := hP x mx
      have each : ∀ p ∈ Q, ∃ new, (∀ A, Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (new ++ A))) ∧ QOk E den new ∧
          (∀ y w, InPairs E den new y w ↔ PairIn E den p y w ∧ ¬(den nv y ∧ denTF E den nb w = Bool.true)) ∧
          (QF den [p] → QF den new) :=
        fun p mp => project_step ef hn hnv hnb fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact qQ p mp
      classical
      let h : Term → List Term := fun p => if hp : p ∈ Q then Classical.choose (each p hp) else []
      have hh : ∀ p ∈ Q, (∀ A, Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (h p ++ A))) ∧ QOk E den (h p) ∧
          (∀ y w, InPairs E den (h p) y w ↔ PairIn E den p y w ∧ ¬(den nv y ∧ denTF E den nb w = Bool.true)) ∧
          (QF den [p] → QF den (h p)) := by
        intro p mp
        simp only [h, dite_eq_left mp]
        exact Classical.choose_spec (each p mp)
      have inner := foldl_lists_at (m := n + 1) "Elixir.Module.Types.Descr" "-tuple_project_negative_pairs/3-fun-0-"
        #[nb, nv] h Q (fun p mp A => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_project_negative_pairs/3-fun-0-/2».pure]
          exact (hh p mp).1 A) []
      refine ⟨Term.list (Q.reverse.flatMap h), ⟨Q.reverse.flatMap h, rfl, fun p mp => ?_, fun y w => ?_, fun nv p mp => ?_⟩,
        ?_⟩
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        exact (hh q mq).2.1 p mp
      · simp only [InPairs, List.mem_flatMap, List.mem_reverse, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨p, ⟨q, mq, mp⟩, hp⟩
          obtain ⟨hq, hn'⟩ := ((hh q mq).2.2.1 y w).mp ⟨p, mp, hp⟩
          obtain ⟨h₁, h₂, h₃⟩ := (sQ y w).mp ⟨q, mq, hq⟩
          refine ⟨h₁, h₂, fun p' mp' hp' => ?_⟩
          rcases mp' with mp' | rfl
          · exact h₃ p' mp' hp'
          · exact hn' (pairIn_iff.mp hp')
        · rintro ⟨h₁, h₂, h₃⟩
          obtain ⟨q, mq, hq⟩ := (sQ y w).mpr ⟨h₁, h₂, fun p' mp' => h₃ p' (Or.inl mp')⟩
          obtain ⟨p, mp, hp⟩ := ((hh q mq).2.2.1 y w).mpr ⟨hq, fun h => h₃ _ (Or.inr rfl) (pairIn_iff.mpr h)⟩
          exact ⟨p, ⟨q, mq, mp⟩, hp⟩
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        exact (hh q mq).2.2.2 (fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact fQ nv q mq) p mp
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_project_negative_pairs/3-fun-1-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_project_negative_pairs/3-fun-1-/2»] using inner)
    (Term.list [.tuple #[value, rest]]) ⟨[.tuple #[value, rest]], rfl, fun p mp => by
      simp at mp; subst mp; exact ⟨value, rest, rfl, hv, hr, nr⟩, fun y w => by simp [InPairs, pairIn_iff],
      fun ⟨y, hy⟩ p mp => by simp at mp; subst mp; exact ⟨value, rest, rfl, y, hy⟩⟩
  exact ⟨Q, by simpa [Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3»] using run, qQ, sQ, fQ⟩

/-- The final fold of `tuple_bdd_fetch_lines/3` unites the element types of the pairs. -/
theorem union_fields (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (Q : List Term)
    (hQ : ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ E f) :
    ∃ u, E u ∧ Erlang.lists.«foldl/3» (D (n + 1)) (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[])
        (.map []) (Term.list Q) = .ok u ∧
      ∀ y, den u y ↔ ∃ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ den f y := by
  obtain ⟨u, ⟨hu, su⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" #[]
    (fun pre a => E a ∧ ∀ y, den a y ↔ ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ den f y) Q
    (fun pre x a mx ⟨ha, sa⟩ => by
      obtain ⟨f, b, rfl, hf⟩ := hQ x mx
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hf ha hn
      refine ⟨c, ⟨hc, fun y => ?_⟩, ?_⟩
      · rw [sc, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_bdd_fetch_lines/3-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-tuple_bdd_fetch_lines/3-fun-0-/2», Elixir.Module.Types.Descr.«opt_union/2»] using rc)
    (.map []) ⟨ef.none, fun y => by simp [ef.den_none y]⟩
  exact ⟨u, hu, run, su⟩

/-- The element type a line with negations projects to: the values of its pair outside the negated pairs. -/
theorem proj_value (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (P : List Term) (hP : ∀ p ∈ P, PairOk E p)
    {value rest : Term} (hv : E value) (hr : TField E rest) (nr : ∃ w, denTF E den rest w = Bool.true) :
    ∃ (s : Bool) (value' : Term), Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2» (D (n + 2)) (Term.list P) rest =
        .ok (boolAtom s) ∧ (s = Bool.true → value' = value) ∧
      (s = Bool.false → ∃ Q, Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» (D (n + 2)) (Term.list P) value rest =
        .ok (Term.list Q) ∧ Erlang.lists.«foldl/3» (D (n + 2))
          (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[]) (.map []) (Term.list Q) =
            .ok value') ∧ E value' ∧
      ∀ y, den value' y ↔ ∃ w, den value y ∧ denTF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬PairIn E den p y w := by
  obtain ⟨s, rs, ss⟩ := keeps_full (den := den) ef (m := n + 2) (by omega) P hP hr
  cases s
  · obtain ⟨Q, rQ, qQ, sQ, -⟩ := project_pairs ef hn P hP hv hr nr
    obtain ⟨u, hu, ru, su⟩ := union_fields ef (n := n + 1) (by omega) Q fun p mp => by
      obtain ⟨f, b, e, hf, -⟩ := qQ p mp
      exact ⟨f, b, e, hf⟩
    refine ⟨Bool.false, u, rs, by simp, fun _ => ⟨Q, rQ, ru⟩, hu, fun y => ?_⟩
    rw [su]
    constructor
    · rintro ⟨p, mp, f, b, rfl, hy⟩
      obtain ⟨f', b', e, -, -, w, hw⟩ := qQ _ mp
      simp only [Term.tuple.injEq] at e
      obtain ⟨rfl, rfl, -⟩ := e
      exact ⟨w, (sQ y w).mp ⟨_, mp, pairIn_iff.mpr ⟨hy, hw⟩⟩⟩
    · rintro ⟨w, h⟩
      obtain ⟨p, mp, hp⟩ := (sQ y w).mpr h
      obtain ⟨f, b, rfl, hy, -⟩ := hp
      exact ⟨_, mp, f, b, rfl, hy⟩
  · obtain ⟨w₀, hw₀, out⟩ := ss.mp rfl
    refine ⟨Bool.true, value, rs, fun _ => rfl, by simp, hv, fun y => ⟨fun hy => ⟨w₀, hy, hw₀, fun p mp hp => ?_⟩,
      fun ⟨_, hy, _⟩ => hy⟩⟩
    obtain ⟨f, nb, rfl, -, hnb⟩ := hp
    rw [out _ mp f nb rfl] at hnb
    cases hnb

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem fetch_step_pos (d : Dispatcher) (tag : String) (l lines : List Term) (i : Nat) (ea : Term) (ob : Bool)
    (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) {descr u : Term} {o : Bool}
    (hfe : Elixir.Module.Types.Descr.«tuple_fetch_element/3» (Term.list l) (.integer i) (.atom tag) =
      .ok (.tuple #[descr, boolAtom o]))
    (hu : Elixir.Module.Types.Descr.«opt_union/2» d descr ea = .ok u) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list (.tuple #[.atom tag, Term.list l, Term.list []] :: lines))
      (.integer i) (.tuple #[ea, boolAtom ob]) =
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list lines) (.integer i) (.tuple #[u, boolAtom (o || ob)]) := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  simp only [Term.list]
  split
  all_goals first
    | (exfalso; simp_all [boolAtom]; done)
    | skip
  · rename_i hx heq₁ heq₂
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq₁ heq₂
    obtain ⟨⟨rfl, rfl, -⟩, rfl⟩ := heq₁
    obtain ⟨rfl, rfl⟩ := heq₂
    cases o <;> cases ob <;> simp [hfe, hu, Lynx.Except.orElse, boolAtom]
  · rename_i h₁ h₂ h₃ h₄
    exact (h₃ _ _ _ _ _ rfl rfl).elim

theorem fetch_step_negs (d : Dispatcher) (tag : String) (l negs lines : List Term) (i : Nat) (ea : Term) (ob : Bool)
    (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) (nn : negs ≠ []) {res next : Term}
    (ht : Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i) (.atom tag) = .ok res)
    (hn : (res = .atom "empty" ∧ next = .tuple #[ea, boolAtom ob]) ∨
      ∃ value rest P s value' u, res = .tuple #[value, rest] ∧
        Elixir.Module.Types.Descr.«tuple_split_negative_pairs/2» d (Term.list negs) (.integer i) = .ok (Term.list P) ∧
        Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2» d (Term.list P) rest = .ok (boolAtom s) ∧
        ((s = Bool.true ∧ value' = value) ∨ (s = Bool.false ∧ ∃ Q,
          Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» d (Term.list P) value rest = .ok (Term.list Q) ∧
          Erlang.lists.«foldl/3» d (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[])
            (.map []) (Term.list Q) = .ok value')) ∧
        Elixir.Module.Types.Descr.«opt_union/2» d value' ea = .ok u ∧ next = .tuple #[u, boolAtom ob]) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list (.tuple #[.atom tag, Term.list l, Term.list negs] :: lines))
      (.integer i) (.tuple #[ea, boolAtom ob]) =
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list lines) (.integer i) next := by
  have nnil : Term.list negs ≠ .nil := by cases negs <;> simp_all [Term.list]
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  simp only [Term.list] at nnil ⊢
  split
  all_goals first
    | (exfalso; simp_all [boolAtom]; done)
    | skip
  · rename_i hx hneg heq₁ heq₂
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq₁ heq₂
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq₁
    obtain ⟨rfl, rfl⟩ := heq₂
    rcases hn with ⟨rfl, rfl⟩ | ⟨value, rest, P, s, value', u, rfl, hs, hk, hv, hu, rfl⟩
    · simp [ht]
    · rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, Q, hq, hf⟩
      · simp [ht, hs, hk, hu, Lynx.Term.isMember, boolAtom]
      · simp [ht, hs, hk, hq, hf, hu, Lynx.Term.isMember, boolAtom]
  · rename_i h₁ h₂ h₃ h₄
    exact (h₄ _ _ _ _ _ _ rfl rfl).elim

section
variable {V : Type} {den : Term → V → Prop}

theorem InT.open_append : ∀ {l : List Term} {v : List V} (w : List V), InT den Bool.false l v →
    InT den Bool.false l (v ++ w)
  | [], [], [], _ => trivial
  | [], [], _ :: _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, w, h => ⟨h.1, InT.open_append w h.2⟩

theorem InT.open_ext : ∀ {l : List Term} {v : List V} (extra : List V), InT den Bool.false l v →
    InT den Bool.false l (v ++ extra)
  | [], _, _, _ => InT.open_nil _
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, extra, h => ⟨h.1, InT.open_ext extra h.2⟩

theorem InT.open_length : ∀ {l : List Term} {v : List V}, InT den Bool.false l v → l.length ≤ v.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => Nat.succ_le_succ (InT.open_length h.2)

theorem InT.open_take : ∀ {l : List Term} {v : List V}, InT den Bool.false l v → InT den Bool.false l (v.take l.length)
  | [], [], _ => trivial
  | [], _ :: _, _ => trivial
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => ⟨h.1, InT.open_take h.2⟩

/-- Values at an index of the tuples of a line. -/
def LongIn (den : Term → V → Prop) (L : Term) (i : Nat) (y : V) : Prop :=
  ∃ v₁ v₂, List.length v₁ = i ∧ InLine den L (v₁ ++ y :: v₂)

/-- Lines holding tuples without an index. -/
def ShortIn (den : Term → V → Prop) (L : Term) (i : Nat) : Prop := ∃ v, InLine den L v ∧ List.length v ≤ i

end

theorem fetch_nil (d : Dispatcher) (i : Nat) (acc : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list []) (.integer i) acc = .ok acc := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  simp only [Term.list]
  split <;> simp_all

theorem fetch_halt (d : Dispatcher) (lines : Term) (i : Nat) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d lines (.integer i) (.tuple #[.atom "term", .atom "true"]) =
      .ok (.tuple #[.atom "term", .atom "true"]) := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  rfl

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- A line without negations, at an index: its element there, or the top or empty type past its elements. -/
theorem line_pos (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (i : Nat) {tag : String} {l : List Term}
    (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e) (ne : ∃ v, InT den (tag == "closed") l v)
    (lines : List Term) {ea : Term} (hea : E ea) (ob : Bool) (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) :
    ∃ ea' ob', Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D m)
        (Term.list (.tuple #[.atom tag, Term.list l, Term.list []] :: lines)) (.integer i) (.tuple #[ea, boolAtom ob]) =
      Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D m) (Term.list lines) (.integer i)
        (.tuple #[ea', boolAtom ob']) ∧ E ea' ∧ (∀ y, den ea y → den ea' y) ∧
      (∀ y, LongIn den (.tuple #[.atom tag, Term.list l, Term.list []]) i y → den ea' y) ∧
      (ob = Bool.true → ob' = Bool.true) ∧
      (ob' = Bool.true → ob = Bool.true ∨ ShortIn den (.tuple #[.atom tag, Term.list l, Term.list []]) i) ∧
      (ob' = Bool.false → ob = Bool.false ∧ ∀ y, den ea' y →
        den ea y ∨ LongIn den (.tuple #[.atom tag, Term.list l, Term.list []]) i y) ∧
      (∀ y, den ea' y → den ea y ∨ LongIn den (.tuple #[.atom tag, Term.list l, Term.list []]) i y) := by
  obtain ⟨v₀, hv₀⟩ := ne
  have inl : ∀ v, InLine den (.tuple #[.atom tag, Term.list l, Term.list []]) v ↔ InT den (tag == "closed") l v :=
    fun v => by rw [inLine_iff]; simp
  have hfe := fetch_element tag g l i
  by_cases short : i < l.length
  · obtain ⟨l₁, x, l₂, rfl, len₁⟩ : ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ List.length l₁ = i := by
      refine ⟨l.take i, l[i]'short, l.drop (i + 1), ?_, by simp; omega⟩
      simp
    have hx : E x := hl x (by simp)
    obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hx hea hm
    have long : ∀ y, LongIn den (.tuple #[.atom tag, Term.list (l₁ ++ x :: l₂), Term.list []]) i y ↔ den x y := by
      intro y
      constructor
      · rintro ⟨v₁, v₂, len, hv⟩
        exact ((InT.split l₁ x l₂ v₁ y v₂ (by omega)).mp ((inl _).mp hv)).1
      · intro hy
        obtain ⟨w₁, y₀, w₂, rfl, h₁, -, h₂⟩ := (InT.mid l₁ x l₂).mp hv₀
        have lw := h₁.closed_length
        have rest := ((InT.split l₁ x l₂ w₁ y₀ w₂ (by omega)).mp hv₀).2
        exact ⟨w₁, w₂, by omega, (inl _).mpr ((InT.split l₁ x l₂ w₁ y w₂ (by omega)).mpr ⟨hy, rest⟩)⟩
    have e : (l₁ ++ x :: l₂)[i]'(by simp; omega) = x := by subst len₁; simp
    refine ⟨u, Bool.false || ob, fetch_step_pos (D m) tag _ lines i ea ob nh (descr := x) (o := Bool.false) (by rw [hfe, dite_eq_left short, e]; rfl)
      (by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru), hu, fun y h => (su y).mpr (Or.inr h),
      fun y h => (su y).mpr (Or.inl ((long y).mp h)), fun h => by simp [h], fun h => Or.inl (by simpa using h),
      fun h => ⟨by simpa using h,
        fun y hy => ((su y).mp hy).elim (fun h => Or.inr ((long y).mpr h)) Or.inl⟩,
      fun y hy => ((su y).mp hy).elim (fun h => Or.inr ((long y).mpr h)) Or.inl⟩
  · rcases g with rfl | rfl
    · obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ef.term hea hm
      refine ⟨u, Bool.true || ob, fetch_step_pos (D m) "open" _ lines i ea ob nh (descr := .atom "term") (o := Bool.true) (by rw [hfe]; simp [short])
        (by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru), hu, fun y h => (su y).mpr (Or.inr h),
        fun y _ => (su y).mpr (Or.inl (ef.den_term y)), fun _ => by simp, fun _ => Or.inr ⟨v₀.take l.length, (inl _).mpr ?_, ?_⟩,
        fun h => by simp at h, fun y hy => ((su y).mp hy).elim (fun _ => Or.inr ?_) Or.inl⟩
      · exact InT.open_take (by simpa using hv₀)
      · simp; omega
      · -- An open literal shorter than the index holds tuples with any value there.
        have h₀ : InT den Bool.false l v₀ := by simpa using hv₀
        have lv := InT.open_length h₀
        let p := v₀.take l.length
        have hp : InT den Bool.false l p := InT.open_take h₀
        have lp : p.length = l.length := by simp [p]; omega
        let pad := List.replicate (i - l.length) (Classical.choice ef.inhabited)
        refine ⟨p ++ pad, [], by simp [pad, lp]; omega, (inl _).mpr ?_⟩
        simpa using InT.open_ext (pad ++ [y]) hp
    · obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ef.none hea hm
      have nolong : ∀ y, ¬LongIn den (.tuple #[.atom "closed", Term.list l, Term.list []]) i y := by
        rintro y ⟨v₁, v₂, len, hv⟩
        exact InT.split_closed (l := l) (v₁ := v₁) (by omega) (by simpa using (inl _).mp hv)
      refine ⟨u, Bool.true || ob, fetch_step_pos (D m) "closed" _ lines i ea ob nh (descr := .map []) (o := Bool.true) (by rw [hfe]; simp [short])
        (by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru), hu, fun y h => (su y).mpr (Or.inr h),
        fun y h => absurd h (nolong y), fun _ => by simp, fun _ => Or.inr ⟨v₀, (inl _).mpr hv₀, ?_⟩, fun h => by simp at h,
        fun y hy => ((su y).mp hy).elim (fun h => absurd h (ef.den_none y)) Or.inl⟩
      have := (by simpa using hv₀ : InT den Bool.true l v₀).closed_length
      omega

/-- A line with negations, at an index: the values there of its tuples, projected outside the negated pairs. -/
theorem line_negs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (i : Nat) {tag : String} {l negs : List Term}
    (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e) (lits : ∀ t ∈ negs, TupleLit E t) (nn : negs ≠ [])
    (ne : ∃ v, InLine den (.tuple #[.atom tag, Term.list l, Term.list negs]) v)
    (lines : List Term) {ea : Term} (hea : E ea) (ob : Bool) (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) :
    ∃ ea', Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D (n + 2))
        (Term.list (.tuple #[.atom tag, Term.list l, Term.list negs] :: lines)) (.integer i) (.tuple #[ea, boolAtom ob]) =
      Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D (n + 2)) (Term.list lines) (.integer i)
        (.tuple #[ea', boolAtom ob]) ∧ E ea' ∧ (∀ y, den ea y → den ea' y) ∧
      (∀ y, LongIn den (.tuple #[.atom tag, Term.list l, Term.list negs]) i y → den ea' y) ∧
      (∀ y, den ea' y → den ea y ∨ LongIn den (.tuple #[.atom tag, Term.list l, Term.list negs]) i y) := by
  obtain ⟨v₀, hv₀⟩ := ne
  obtain ⟨hv₀, -⟩ := inLine_iff.mp hv₀
  obtain ⟨res, ht, ⟨rfl, none⟩ | ⟨⟨value, rest, rfl, hval, hr⟩, nr, lenR, sem⟩⟩ := take_pair ef g hl i
  · refine ⟨ea, fetch_step_negs (D (n + 2)) tag l negs lines i ea ob nh nn ht (Or.inl ⟨rfl, rfl⟩), hea, fun y h => h,
      fun y ⟨v₁, v₂, len, hv⟩ => absurd (inLine_iff.mp hv).1 (none v₁ y v₂ len), fun y h => Or.inl h⟩
  obtain ⟨P, rP, hP, sP⟩ := split_pairs (den := den) ef negs lits i (m := n + 2)
  -- The pair holds a tuple long enough, so its remaining tuples are not empty.
  obtain ⟨v, hv, long⟩ : ∃ v, InT den (tag == "closed") l v ∧ i < List.length v := by
    rcases g with rfl | rfl
    · obtain ⟨y₀⟩ := ef.inhabited
      exact ⟨v₀ ++ List.replicate (i + 1) y₀, InT.open_append _ (by simpa using hv₀), by simp; omega⟩
    · by_cases short : l.length ≤ i
      · have := take_closed_short l i short
        rw [this] at ht; cases ht
      · have := (by simpa using hv₀ : InT den Bool.true l v₀).closed_length
        exact ⟨v₀, hv₀, by omega⟩
  have split : v = v.take i ++ v[i] :: v.drop (i + 1) := by simp
  have restNe : ∃ w, denTF E den rest w = Bool.true := by
    rw [split] at hv
    have := (sem (v.take i) v[i] (v.drop (i + 1)) (by simp; omega)).mp hv
    exact ⟨_, (pairIn_iff.mp this).2⟩
  obtain ⟨s, value', rk, hs₁, hs₂, hv', sv'⟩ := proj_value ef hn P hP hval hr restNe
  obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hv' hea (show K ≤ n + 2 by omega)
  have hsv : (s = Bool.true ∧ value' = value) ∨ (s = Bool.false ∧ ∃ Q,
      Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» (D (n + 2)) (Term.list P) value rest = .ok (Term.list Q) ∧
      Erlang.lists.«foldl/3» (D (n + 2)) (.function false "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[])
        (.map []) (Term.list Q) = .ok value') := by
    cases s
    · exact Or.inr ⟨rfl, hs₂ rfl⟩
    · exact Or.inl ⟨rfl, hs₁ rfl⟩
  have run := fetch_step_negs (D (n + 2)) tag l negs lines i ea ob nh nn ht (Or.inr ⟨value, rest, P, s, value', u, rfl, rP,
    rk, hsv, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru, rfl⟩)
  have longIff : ∀ y, LongIn den (.tuple #[.atom tag, Term.list l, Term.list negs]) i y ↔ den value' y := by
    intro y
    rw [sv']
    constructor
    · rintro ⟨v₁, v₂, len, hvl⟩
      obtain ⟨hin, hneg⟩ := inLine_iff.mp hvl
      obtain ⟨hy, hw⟩ := pairIn_iff.mp ((sem v₁ y v₂ len).mp hin)
      exact ⟨v₁ ++ v₂, hy, hw, fun p mp hp => (sP v₁ y v₂ len).mpr ⟨p, mp, hp⟩ |>.elim fun N ⟨mN, hN⟩ => hneg N mN hN⟩
    · rintro ⟨w, hy, hw, hno⟩
      have lw := lenR y w (pairIn_iff.mpr ⟨hy, hw⟩)
      have ew : w = w.take i ++ w.drop i := by simp
      refine ⟨w.take i, w.drop i, by simp; omega, inLine_iff.mpr ⟨?_, fun N mN hN => ?_⟩⟩
      · rw [sem _ y _ (by simp; omega), ← ew]
        exact pairIn_iff.mpr ⟨hy, hw⟩
      · obtain ⟨p, mp, hp⟩ := (sP _ y _ (by simp; omega)).mp ⟨N, mN, hN⟩
        rw [← ew] at hp
        exact hno p mp hp
  exact ⟨u, run, hu, fun y h => (su y).mpr (Or.inr h), fun y h => (su y).mpr (Or.inl ((longIff y).mp h)),
    fun y h => ((su y).mp h).elim (fun h => Or.inr ((longIff y).mpr h)) Or.inl⟩

/-- `tuple_bdd_fetch_lines/3` unites the values at an index of the tuples of non-empty lines, and flags lines holding
tuples without that index, unless it reaches the top type, flagged. -/
theorem fetch_lines_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (i : Nat) :
    ∀ (lines : List Term), (∀ L ∈ lines, TLine E L ∧ ∃ v, InLine den L v) → ∀ (ea : Term) (ob : Bool), E ea →
      ∃ e o, Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D (n + 2)) (Term.list lines) (.integer i)
          (.tuple #[ea, boolAtom ob]) = .ok (.tuple #[e, boolAtom o]) ∧ E e ∧ (∀ y, den ea y → den e y) ∧
        (∀ L ∈ lines, ∀ y, LongIn den L i y → den e y) ∧ (ob = Bool.true → o = Bool.true) ∧
        (o = Bool.true → ob = Bool.true ∨ ∃ L ∈ lines, ShortIn den L i) ∧
        (∀ y, den e y → den ea y ∨ ∃ L ∈ lines, LongIn den L i y)
  | lines, hlines, ea, ob, hea => by
    by_cases halt : ea = .atom "term" ∧ ob = Bool.true
    · obtain ⟨rfl, rfl⟩ := halt
      exact ⟨_, Bool.true, fetch_halt _ _ _, ef.term, fun y _ => ef.den_term y, fun _ _ y _ => ef.den_term y,
        fun _ => rfl, fun _ => Or.inl rfl, fun y h => Or.inl h⟩
    cases lines with
    | nil =>
      exact ⟨ea, ob, fetch_nil _ _ _, hea, fun y h => h, by simp, id, fun h => Or.inl h, fun y h => Or.inl h⟩
    | cons L rest =>
      obtain ⟨⟨tag, l, negs, rfl, g, hl, lits⟩, ne⟩ := hlines _ List.mem_cons_self
      have hrest := fun L' (m : L' ∈ rest) => hlines L' (List.mem_cons_of_mem _ m)
      by_cases nn : negs = []
      · subst nn
        obtain ⟨v, hv⟩ := ne
        obtain ⟨ea', ob', run, hea', sub, long, mono, short, -, back⟩ := line_pos ef (m := n + 2) (by omega) i g hl
          ⟨v, (inLine_iff.mp hv).1⟩ rest hea ob halt
        obtain ⟨e, o, run', he, sub', long', mono', short', back'⟩ := fetch_lines_sem ef hn i rest hrest ea' ob' hea'
        refine ⟨e, o, run.trans run', he, fun y h => sub' y (sub y h), fun L' mL' y h => ?_, fun h => mono' (mono h),
          fun h => ?_, fun y hy => ?_⟩
        · rcases List.mem_cons.mp mL' with rfl | mL'
          · exact sub' y (long y h)
          · exact long' L' mL' y h
        · rcases short' h with h | ⟨L', mL', h⟩
          · rcases short h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨_, List.mem_cons_self, h⟩
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h⟩
        · rcases back' y hy with h' | ⟨L', mL', h'⟩
          · rcases back y h' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr ⟨_, List.mem_cons_self, h''⟩
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h'⟩
      · obtain ⟨ea', run, hea', sub, long, back⟩ := line_negs ef hn i g hl lits nn ne rest hea ob halt
        obtain ⟨e, o, run', he, sub', long', mono', short', back'⟩ := fetch_lines_sem ef hn i rest hrest ea' ob hea'
        refine ⟨e, o, run.trans run', he, fun y h => sub' y (sub y h), fun L' mL' y h => ?_, mono', fun h => ?_,
          fun y hy => ?_⟩
        · rcases List.mem_cons.mp mL' with rfl | mL'
          · exact sub' y (long y h)
          · exact long' L' mL' y h
        · rcases short' h with h | ⟨L', mL', h⟩
          · exact Or.inl h
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h⟩
        · rcases back' y hy with h' | ⟨L', mL', h'⟩
          · rcases back y h' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr ⟨_, List.mem_cons_self, h''⟩
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h'⟩

theorem ge_ints (a b : Nat) : Erlang.erlang.«>=/2» (.integer (a : Int)) (.integer (b : Int)) =
    .ok (boolAtom (decide (b ≤ a))) := by
  by_cases h : b ≤ a <;> simp [Erlang.erlang.«>=/2», h, boolAtom, Int.isGE_compare] <;> omega

/-- `tuple_bdd_positive_size_at_least?/3` finds a lower bound of the sizes of the tuples of a BDD from its literals. -/
theorem pos_size (ef : EF nd E V den tl K) (n : Nat) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
    (okT : ∀ t, ok t → TupleOk E t) : ∀ g : Bool, ∃ b : Bool,
      Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3» r (.integer n) (boolAtom g) = .ok (boolAtom b) ∧
      (b = Bool.true → ∀ v, eval (valT E den v) r = Bool.true → (g = Bool.true → n ≤ List.length v) → n ≤ List.length v) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) → ∀ g : Bool, ∃ b : Bool,
      Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3» r (.integer n) (boolAtom g) = .ok (boolAtom b) ∧
      (b = Bool.true → ∀ v, eval (valT E den v) r = Bool.true → (g = Bool.true → n ≤ List.length v) → n ≤ List.length v))
    ?_ ?_ ?_ ?_ ok r wr okT
  · intro ok _ g
    refine ⟨g, ?_, fun h v _ hg => hg h⟩
    cases g <;> rfl
  · intro ok _ g
    refine ⟨Bool.true, ?_, fun _ v h => by simp at h⟩
    cases g <;> rfl
  · intro ok k x y okl okLit g
    obtain ⟨⟨k', tag, l, e, gt, el⟩, -⟩ := okLit _ okl
    cases g
    · refine ⟨decide (n ≤ l.length), ?_, fun h v hv _ => ?_⟩
      · rw [e]
        unfold Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3»
        by_cases h : n ≤ l.length <;> simp [length_list, boolAtom, h]
      · simp only [decide_eq_true_eq] at h
        rw [eval_leaf, e] at hv
        have := (lit_sem (valT_lit ef.semR ⟨k', tag, l, rfl, gt, el⟩ hv)).length_le
        omega
    · exact ⟨Bool.true, by rfl, fun _ v _ hg => hg rfl⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit g
    have hl := okLit _ okl
    obtain ⟨k', tag, l, rfl, gt, el⟩ := hl.1
    have okLit' : ∀ t, Above ok (.tuple #[.integer k', .atom tag, Term.list l]) t → TupleOk E t := fun t ht => okLit t ht.1
    cases g
    · obtain ⟨bu, ru, su⟩ := iu okLit' Bool.false
      obtain ⟨bc, rc, sc⟩ := ic okLit' (decide (n ≤ l.length))
      obtain ⟨bd, rd, sd⟩ := idd okLit' Bool.false
      refine ⟨bu && bc && bd, ?_, fun hb v hv _ => ?_⟩
      · unfold Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3»
        simp only [boolAtom_false] at ru rd
        have rc' := rc
        by_cases hn : n ≤ l.length <;> simp only [hn, decide_true, decide_false, boolAtom_true, boolAtom_false] at rc' <;>
          cases bu <;> cases bc <;> cases bd <;>
          simp [length_list, ru, rc', rd, Lynx.Except.andAlso, boolAtom, hn]
      · simp only [Bool.and_eq_true] at hb
        rw [eval_node] at hv
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hv
        rcases hv with (⟨hlit, hcv⟩ | huv) | ⟨-, hdv⟩
        · refine sc hb.1.2 v hcv fun hg => ?_
          simp only [decide_eq_true_eq] at hg
          have := (lit_sem (valT_lit ef.semR ⟨k', tag, l, rfl, gt, el⟩ hlit)).length_le
          omega
        · exact su hb.1.1 v huv (by simp)
        · exact sd hb.2 v hdv (by simp)
    · exact ⟨Bool.true, by rfl, fun _ v _ hg => hg rfl⟩

theorem pos2_ne (b : Term) {n : Nat} (hn : 1 ≤ n) :
    Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/2» b (.integer n) =
      Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3» b (.integer n) (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/2»
  split
  · rename_i h; simp at h; omega
  · rfl

theorem inT_terms_iff (hterm : ∀ y, den (.atom "term") y) (n : Nat) (v : List V) :
    InT den Bool.false (List.replicate n (.atom "term")) v ↔ n ≤ v.length :=
  ⟨fun h => by simpa using h.length_le, InT.open_any hterm n v⟩

/-- `tuple_of_size_at_least_static?/2` decides whether every tuple of a tuple type has a size. -/
theorem size_at_least (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {b : Term} (hb : TField E b) (n : Nat)
    (hn : 1 ≤ n) : ∃ sz : Bool, Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m)
      (.map [(.atom "tuple", b)]) (.integer n) = .ok (boolAtom sz) ∧
      (sz = Bool.true ↔ ∀ v, denTF E den b v = Bool.true → n ≤ List.length v) := by
  -- The positive check, sound.
  obtain ⟨p, rp, sp⟩ : ∃ p : Bool, Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/2» b (.integer n) =
      .ok (boolAtom p) ∧ (p = Bool.true → ∀ v, denTF E den b v = Bool.true → n ≤ List.length v) := by
    rw [pos2_ne b hn]
    rcases hb with ⟨k, rfl⟩ | wb
    · refine ⟨Bool.false, ?_, by simp⟩
      have := ge_ints 0 n
      have nn : decide (n ≤ 0) = Bool.false := by simp; omega
      rw [nn] at this
      simpa [Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3», Erlang.erlang.«length/1»] using this
    · obtain ⟨p, rp, sp⟩ := pos_size ef n wb (fun t h => h.1) Bool.false
      exact ⟨p, rp, fun h v hv => sp h v (by rwa [denTF_bdd wb] at hv) (by simp)⟩
  obtain ⟨k, rk, key⟩ := leaf_new_key "open" (Or.inl rfl) (List.replicate n (.atom "term"))
  have hl : ∀ e ∈ List.replicate n (.atom "term"), E e := fun e me => by rw [List.eq_of_mem_replicate me]; exact ef.term
  obtain ⟨d, rd, td, sd, -⟩ := tuple_diff_lh ef hb (tleaf_field (Or.inl rfl) hl key)
  obtain ⟨e, re, se⟩ := tuple_empty_exact ef td []
  have se := se (lh d + 1) (by omega) (safeT_nil _)
  have leafSem : ∀ v, denTF E den (.tuple #[.integer k, .atom "open", Term.list (List.replicate n (.atom "term"))]) v =
      Bool.true ↔ n ≤ List.length v := fun v => by
    rw [denTF_leaf ef (Or.inl rfl) hl, vT_lit ef (Or.inl rfl) hl]
    exact inT_terms_iff ef.den_term n v
  cases p
  · refine ⟨e, ?_, ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
      simp [getMapKeys_single, mapLookup, rp, dup_nat, Elixir.Module.Types.Descr.«tuple_new/2», rk, rd, re m hm,
        Lynx.Except.orElse, boolAtom]
    · rw [se]
      constructor
      · intro h v hv
        have := h v
        rw [sd, hv] at this
        simp only [Bool.true_and, Bool.not_eq_false'] at this
        exact (leafSem v).mp this
      · intro h v
        rw [sd]
        cases hv : denTF E den b v
        · rfl
        · simp [(leafSem v).mpr (h v hv)]
  · refine ⟨Bool.true, ?_, ⟨fun _ => sp rfl, fun _ => rfl⟩⟩
    unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
    simp [getMapKeys_single, mapLookup, rp, Lynx.Except.orElse, boolAtom]

/-- `tuple_bdd_fetch_static/2` finds the values at an index of the tuples of a BDD, and whether some tuple has no such
index. -/
theorem bdd_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) {r : Term} (wr : Bdd (TLit E) r) (i : Nat) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_bdd_fetch_static/2» (D (n + 2)) r (.integer i) =
        .ok (.tuple #[e, boolAtom o]) ∧ E e ∧
      (∀ v₁ y v₂, List.length v₁ = i → denTF E den r (v₁ ++ y :: v₂) = Bool.true → den e y) ∧
      (o = Bool.true ↔ ∃ v, denTF E den r v = Bool.true ∧ List.length v ≤ i) ∧
      (∀ y, den e y → ∃ v₁ v₂, List.length v₁ = i ∧ denTF E den r (v₁ ++ y :: v₂) = Bool.true) := by
  obtain ⟨lines, rl, tl', sl⟩ := dnf_neg (den := den) ef.opsU ef.dopsU ef.msemZ rfl (m := n + 2) (by omega) wr
  have inR : ∀ v, denTF E den r v = Bool.true ↔ ∃ L ∈ lines, InLine den L v := fun v => by rw [denTF_bdd wr]; exact sl v
  obtain ⟨e, o, rf, he, -, long, -, short, back⟩ := fetch_lines_sem ef hn i lines tl' (.map []) Bool.false ef.none
  obtain ⟨sz, rs, ss⟩ := size_at_least ef (m := n + 2) (by omega) (Or.inr wr) (i + 1) (by omega)
  have shortIff : (∃ v, denTF E den r v = Bool.true ∧ List.length v ≤ i) ↔ sz = Bool.false := by
    rw [← Bool.not_eq_true, ss]
    constructor
    · rintro ⟨v, hv, len⟩ h; have := h v hv; omega
    · intro h
      obtain ⟨v, hv⟩ := Classical.not_forall.mp h
      obtain ⟨hv, len⟩ := Classical.not_imp.mp hv
      exact ⟨v, hv, by omega⟩
  refine ⟨e, o || !sz, ?_, he, fun v₁ y v₂ len hv => ?_, ?_, fun y hy => ?_⟩
  · unfold Elixir.Module.Types.Descr.«tuple_bdd_fetch_static/2»
    have rs' : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (n + 2)) (.map [(.atom "tuple", r)])
        (.integer ((i : Int) + 1)) = .ok (boolAtom sz) := by simpa using rs
    simp only [rl, rf, Lynx.Except.ok_bind, plus_one, boolAtom_false] at rf ⊢
    cases o <;> cases sz <;> simp [rs', Lynx.Except.orElse, Erlang.erlang.«not/1», boolAtom]
  · obtain ⟨L, mL, hL⟩ := (inR _).mp hv
    exact long L mL y ⟨v₁, v₂, len, hL⟩
  · rw [shortIff]
    cases o <;> cases sz <;> simp
    obtain h | ⟨L, mL, v, hv, len⟩ := short rfl
    · cases h
    · have := (shortIff.mp ⟨v, (inR v).mpr ⟨L, mL, hv⟩, len⟩); cases this
  · rcases back y hy with h' | ⟨L, mL, v₁, v₂, len, hL⟩
    · exact absurd h' (ef.den_none y)
    · exact ⟨v₁, v₂, len, (inR _).mpr ⟨L, mL, hL⟩⟩

/-- `tuple_fetch_element/3` on a non-empty literal: the values at an index of its tuples, and whether one is shorter. -/
theorem leaf_fetch (ef : EF nd E V den tl K) {tag : String} (g : tag = "open" ∨ tag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) (ne : ∃ v, InT den (tag == "closed") l v) (i : Nat) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_fetch_element/3» (Term.list l) (.integer i) (.atom tag) =
        .ok (.tuple #[e, boolAtom o]) ∧ E e ∧
      (∀ v₁ y v₂, List.length v₁ = i → InT den (tag == "closed") l (v₁ ++ y :: v₂) → den e y) ∧
      (o = Bool.true ↔ ∃ v, InT den (tag == "closed") l v ∧ List.length v ≤ i) ∧
      (∀ y, den e y → ∃ v₁ v₂, List.length v₁ = i ∧ InT den (tag == "closed") l (v₁ ++ y :: v₂)) := by
  obtain ⟨v₀, hv₀⟩ := ne
  have hfe := fetch_element tag g l i
  by_cases short : i < l.length
  · obtain ⟨l₁, x, l₂, rfl, len₁⟩ : ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ List.length l₁ = i := by
      refine ⟨l.take i, l[i]'short, l.drop (i + 1), ?_, by simp; omega⟩
      simp
    have e : (l₁ ++ x :: l₂)[i]'(by simp; omega) = x := by subst len₁; simp
    refine ⟨x, Bool.false, by rw [hfe, dite_eq_left short, e]; rfl, hl x (by simp),
      fun v₁ y v₂ len h => ((InT.split l₁ x l₂ v₁ y v₂ (by omega)).mp h).1, ⟨fun h => (by cases h), ?_⟩, fun y hy => ?_⟩
    · rintro ⟨v, hv, len⟩
      have := hv.length_le
      simp at this; omega
    · obtain ⟨w₁, y₀, w₂, rfl, h₁, -, h₂⟩ := (InT.mid l₁ x l₂).mp hv₀
      have lw := h₁.closed_length
      have rest := ((InT.split l₁ x l₂ w₁ y₀ w₂ (by omega)).mp hv₀).2
      exact ⟨w₁, w₂, by omega, (InT.split l₁ x l₂ w₁ y w₂ (by omega)).mpr ⟨hy, rest⟩⟩
  · rcases g with rfl | rfl
    · refine ⟨.atom "term", Bool.true, by rw [hfe]; simp [short], ef.term, fun _ y _ _ _ => ef.den_term y,
        ⟨fun _ => ⟨v₀.take l.length, InT.open_take (by simpa using hv₀), by simp; omega⟩, fun _ => rfl⟩,
        fun y _ => ?_⟩
      have h₀ : InT den Bool.false l v₀ := by simpa using hv₀
      have lv := InT.open_length h₀
      let p := v₀.take l.length
      have hp : InT den Bool.false l p := InT.open_take h₀
      have lp : p.length = l.length := by simp [p]; omega
      let pad := List.replicate (i - l.length) (Classical.choice ef.inhabited)
      refine ⟨p ++ pad, [], by simp [pad, lp]; omega, ?_⟩
      simpa using InT.open_ext (pad ++ [y]) hp
    · refine ⟨.map [], Bool.true, by rw [hfe]; simp [short], ef.none,
        fun v₁ y v₂ len h => absurd h (InT.split_closed (l := l) (v₁ := v₁) (by omega)), ⟨fun _ => ⟨v₀, hv₀, ?_⟩, fun _ => rfl⟩,
        fun y hy => absurd hy (ef.den_none y)⟩
      have := (by simpa using hv₀ : InT den Bool.true l v₀).closed_length
      omega

theorem inT_nonempty {c : Bool} : ∀ {l : List Term} {v : List V}, InT den c l v → ∀ e ∈ l, ∃ y, den e y
  | [], _, _, e, me => by simp at me
  | _ :: _, [], h, _, _ => by simp [InT] at h
  | x :: l, y :: v, h, e, me => by
    simp only [InT] at h
    rcases List.mem_cons.mp me with rfl | me
    · exact ⟨y, h.1⟩
    · exact inT_nonempty h.2 e me

/-- `tuple_fetch_static/2` on a static type with a non-empty tuple field. -/
theorem static_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) (fb : TField E b) (ne : ∃ v, denTF E den b v = Bool.true) (i : Nat) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_fetch_static/2» (D (n + 2)) (.map X) (.integer i) =
        .ok (.tuple #[e, boolAtom o]) ∧ E e ∧
      (∀ v₁ y v₂, List.length v₁ = i → denTF E den b (v₁ ++ y :: v₂) = Bool.true → den e y) ∧
      (o = Bool.true ↔ ∃ v, denTF E den b v = Bool.true ∧ List.length v ≤ i) ∧
      (∀ y, den e y → ∃ v₁ v₂, List.length v₁ = i ∧ denTF E den b (v₁ ++ y :: v₂) = Bool.true) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, hl⟩ := tfield_three fb e₀
    have sem : ∀ v, denTF E den (.tuple #[.integer k, .atom tag, Term.list l]) v = Bool.true ↔
        InT den (tag == "closed") l v := fun v => by rw [denTF_leaf ef g hl, vT_lit ef g hl]
    obtain ⟨v₀, hv₀⟩ := ne
    obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ := leaf_fetch ef g hl ⟨v₀, (sem v₀).mp hv₀⟩ i
    -- The literal holds tuples, so none of its elements is empty.
    obtain ⟨c, check, -, empty⟩ := elements_exact ef.opsU ef.msemZ rfl l hl
    have c_false : c = Bool.false := by
      cases c
      · rfl
      · obtain ⟨x, mx, hx⟩ := empty rfl
        obtain ⟨y, hy⟩ := inT_nonempty ((sem v₀).mp hv₀) x mx
        exact absurd hy (hx y)
    subst c_false
    refine ⟨e, o, ?_, he, fun v₁ y v₂ len h => s₁ v₁ y v₂ len ((sem _).mp h), ?_, fun y hy => ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«tuple_fetch_leaf/3», check (n + 2) (by omega), boolAtom, run]
    · rw [s₂]; simp only [sem]
    · obtain ⟨v₁, v₂, len, h⟩ := s₃ y hy
      exact ⟨v₁, v₂, len, (sem _).mpr h⟩
  · have wb : Bdd (TLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ := bdd_fetch (den := den) ef hn wb i
    refine ⟨e, o, ?_, he, s₁, s₂, s₃⟩
    unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»
    rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · simp [getMapKeys_single, hb, run]
    · simp [getMapKeys_single, hb, run]
    · exact absurd ⟨_, _, _, rfl⟩ three
    · simp [getMapKeys_single, hb, run]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Tuples of values in the tuple field of a map. -/
def TT (t : Term) (n : Nat) (X : List (Term × Term)) (w : List (level t n).V) : Prop :=
  ∃ b, mapLookup X (.atom "tuple") = some b ∧ denTF (level t n).E (level t n).den b w = Bool.true

/-- Maps of tuple types only, with some tuple. -/
def TOnly (t : Term) (n : Nat) (X : List (Term × Term)) : Prop :=
  (∀ v : PN t n, denD (.map X) v → v.1.1 = "tuple") ∧ ∃ w, TT t n X w

/-- The point of the next level of a tuple of values. -/
noncomputable def tpt (w : List (level t n).V) : PN t n :=
  ⟨("tuple", (0, .nil, valT (level t n).E (level t n).den w)), by simp [names],
    ⟨valT_resp w, fun h => by simp at h, fun h => by simp at h, fun _ => ⟨w, rfl⟩,
      fun h => by simp at h, fun h => by simp at h⟩⟩

theorem denD_tpt {X : List (Term × Term)} (w : List (level t n).V) : denD (.map X) (tpt (t := t) (n := n) w) ↔ TT t n X w := by
  rw [denD_map]
  simp only [tpt]
  cases h : mapLookup X (.atom "tuple") with
  | none => simp [TT, h, dn_none]
  | some b => simp [TT, h, dn_tupleT (E := (level t n).E) (den := (level t n).den) (p := (0, .nil, valT _ _ w)) rfl]

theorem pt_tuple (v : PN t n) (h : v.1.1 = "tuple") :
    ∃ w, ∀ X : List (Term × Term), (denD (.map X) v ↔ TT t n X w) := by
  obtain ⟨⟨name, p⟩, mem, ok⟩ := v
  simp only at h
  subst h
  obtain ⟨w, hw⟩ := ok.2.2.2.1 rfl
  refine ⟨w, fun X => ?_⟩
  rw [denD_map]
  simp only
  cases hb : mapLookup X (.atom "tuple") with
  | none => simp [TT, hb, dn_none]
  | some b => simp [TT, hb, dn_tupleT (E := (level t n).E) (den := (level t n).den) hw]


/-- A map without its tuple field. -/
def rmT (X : List (Term × Term)) : List (Term × Term) :=
  X.filter fun entry => !decide (compareExact (fuel (.atom "tuple") entry.1) (.atom "tuple") entry.1 = .eq)

theorem lookup_rmT (X : List (Term × Term)) (name : String) :
    mapLookup (rmT X) (.atom name) = if name = "tuple" then none else mapLookup X (.atom name) := by
  simp only [rmT, mapLookup_remove]
  by_cases h : name = "tuple" <;> simp [h]

theorem rest_tuple {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) :
    DE (level t n).E (.map (rmT X)) ∧ ∀ v : PN t n, denD (.map (rmT X)) v ↔ denD (.map X) v ∧ v.1.1 ≠ "tuple" := by
  have sX := de_map hX
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name x h => ?_⟩, fun v => ?_⟩
  · have : (mapLookup X q).isSome := by
      simp only [rmT, mapLookup_remove] at h
      split at h
      · simp at h
      · exact h
    exact sX.keys q this
  · rw [lookup_rmT] at h
    split at h
    · cases h
    · exact sX.fields name x h
  · rw [denD_map, denD_map, lookup_rmT]
    by_cases h : v.1.1 = "tuple"
    · simp [h, dn_none]
    · simp [h]

/-- `open_tuple/1` of static element types is the open tuple literal of them. -/
theorem open_tuple_run (l : List Term) (hl : ∀ e ∈ l, Static e) : ∃ k : Int,
    Elixir.Module.Types.Descr.«open_tuple/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list l])]) ∧
    KeyOk (.tuple #[.integer k, .atom "open", Term.list l]) := by
  obtain ⟨se, run⟩ := descr_fields l hl [] [] Bool.false
  obtain ⟨k, leaf, key⟩ := leaf_new_key "open" (Or.inl rfl) l
  refine ⟨k, ?_, key⟩
  have rev : Erlang.lists.«reverse/1» (Term.list l.reverse) = .ok (Term.list l) := by
    simpa using reverse1_list l.reverse
  simp only [Term.list, List.append_nil, boolAtom_false] at run
  simp_all [Elixir.Module.Types.Descr.«open_tuple/1», Elixir.Module.Types.Descr.«open_tuple/2»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_static/2»,
    Elixir.Module.Types.Descr.«tuple_new/2»]

theorem inT_rep_true (hterm : ∀ y, (level t n).den (.atom "term") y) (i : Nat) (v : List (level t n).V) :
    InT (level t n).den Bool.true (List.replicate i (.atom "term")) v ↔ v.length = i :=
  ⟨fun h => by simpa using h.closed_length, fun h => InT.terms hterm i v h.symm⟩

/-- The tuples of an open literal of top types and an element type at an index. -/
theorem tt_open_at {e : Term} (he : (level t n).E e) (i : Nat) (k : Int) (w : List (level t n).V) :
    TT t n [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list (List.replicate i (.atom "term") ++ [e])])] w ↔
      ∃ v₁ y v₂, w = v₁ ++ y :: v₂ ∧ List.length v₁ = i ∧ (level t n).den e y := by
  have hl : ∀ x ∈ List.replicate i (.atom "term") ++ [e], (level t n).E x := by
    intro x mx
    rcases List.mem_append.mp mx with mx | mx
    · rw [List.eq_of_mem_replicate mx]; exact (level t n).ef.term
    · simp at mx; subst mx; exact he
  simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', denTF_leaf (level t n).ef (Or.inl rfl) hl, vT_lit (level t n).ef (Or.inl rfl) hl, equalExact_eq_decide]
  rw [show ("open" == "closed") = Bool.false from rfl, InT.mid]
  constructor
  · rintro ⟨v₁, y, v₂, rfl, h₁, hy, -⟩
    exact ⟨v₁, y, v₂, rfl, (inT_rep_true (level t n).ef.den_term i v₁).mp h₁, hy⟩
  · rintro ⟨v₁, y, v₂, rfl, len, hy⟩
    exact ⟨v₁, y, v₂, rfl, (inT_rep_true (level t n).ef.den_term i v₁).mpr len, hy, InT.open_nil v₂⟩

/-- The tuples of an open literal of top types. -/
theorem tt_open (i : Nat) (k : Int) (w : List (level t n).V) :
    TT t n [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list (List.replicate i (.atom "term"))])] w ↔
      i ≤ w.length := by
  have hl : ∀ x ∈ List.replicate i (.atom "term"), (level t n).E x := by
    intro x mx; rw [List.eq_of_mem_replicate mx]; exact (level t n).ef.term
  simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', denTF_leaf (level t n).ef (Or.inl rfl) hl, vT_lit (level t n).ef (Or.inl rfl) hl, equalExact_eq_decide]
  exact inT_terms_iff (level t n).ef.den_term i w

/-- The top tuple type, as `tuple/0` builds it. -/
theorem tupleTop_de : DE (level t n).E (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) :=
  fused_de (l := []) (Or.inl rfl) (by simp) fun k tag l e => by
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.atom.injEq] at e₂
    subst e₂
    have : l = [] := by cases l <;> simp_all [Term.list]
    exact ⟨fun h => by simp at h, fun _ h => absurd this h⟩

theorem tupleTop_den (v : PN t n) :
    denD (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) v ↔ v.1.1 = "tuple" := by
  rw [denD_map]
  by_cases h : v.1.1 = "tuple"
  · simp [mapLookup, h, dn_tuple, denO_top]
  · simp [mapLookup, h, dn_none]

/-- A point of the next level outside every tuple type. -/
def bitPt : PN t n := ⟨("bitmap", (0, .nil, fun _ => Bool.false)), by simp [names],
  ⟨resp_const _, fun _ => by simp, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h⟩⟩

theorem lt_zero_false (i : Nat) : Erlang.erlang.«</2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
  have : ¬(i : Int) < 0 := by omega
  simp [Erlang.erlang.«</2», Int.compare_eq_lt, this]

/-- `tuple_fetch/2` on static types of the next level: types holding only tuples, all of them long enough, give the
type of their values at the index; types holding a shorter tuple give `:badindex`, and others `:badtuple`. -/
theorem fetch_tuple {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok res ∧
      ((res = .atom "badtuple" ∧ ¬TOnly t n X) ∨ (res = .atom "badindex" ∧ TOnly t n X ∧ ∃ w, TT t n X w ∧ List.length w ≤ i) ∨
        ∃ e, res = .tuple #[.atom "false", e] ∧ (level t n).E e ∧ TOnly t n X ∧ (∀ w, TT t n X w → i < List.length w) ∧
          (∀ v₁ y v₂, List.length v₁ = i → TT t n X (v₁ ++ y :: v₂) → (level t n).den e y) ∧
          (∀ y, (level t n).den e y → ∃ v₁ v₂, List.length v₁ = i ∧ TT t n X (v₁ ++ y :: v₂))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have sX := de_map hX
  have ef := (level t n).ef
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def]
  simp only [Erlang.maps.«take/2», sX.static, lt_zero_false]
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Lynx.Term.isMember]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    obtain ⟨dR, sR⟩ := rest_tuple hX
    have rE := next_empty dR (m := k + 2) (by omega)
    obtain ⟨eb, reb, seb⟩ := tuple_empty_exact (level t n).ef fb []
    have seb := seb (lh b + 1) (by omega) (safeT_nil _)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have only : TOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmT X)) v) ∧ eb = Bool.false := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        refine ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), ?_⟩
        cases eb
        · rfl
        · have := seb.mp rfl w; rw [(tt w).mp hw] at this; cases this
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), ?_⟩
        obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt seb.mpr (by simp [h₂]))
        exact ⟨w, (tt w).mpr (by simpa using hw)⟩
    have nonEmpty : Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 2)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb)) := by
      simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb, equalExact_eq_decide]
      rw [show (List.filter (fun entry => !decide (compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst = .eq)) X) = rmT X from rfl]
      simp only [Lynx.Except.ok_bind, rE, reb (k + 2) (by omega)]
      cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
        simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    by_cases ok : TOnly t n X
    · have r : (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb) = Bool.true := by
        obtain ⟨h₁, h₂⟩ := only.mp ok
        rw [bp_true.mpr h₁, h₂]; rfl
      rw [r] at nonEmpty
      obtain ⟨w₀, hw₀⟩ := ok.2
      obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ := static_fetch (level t n).ef (n := k) (by omega) hb fb
        ⟨w₀, (tt w₀).mp hw₀⟩ i
      obtain ⟨eb₂, re₂, se₂⟩ := (level t n).ef.empty_pub he
      cases o
      · have long : ∀ w, TT t n X w → i < List.length w := fun w hw => by
          by_cases h : List.length w ≤ i
          · exact absurd (s₂.mpr ⟨w, (tt w).mp hw, h⟩) (by simp)
          · omega
        cases eb₂
        · refine ⟨_, ?_, Or.inr (Or.inr ⟨e, rfl, he, ok, long, fun v₁ y v₂ len h => s₁ v₁ y v₂ len ((tt _).mp h),
            fun y hy => ?_⟩)⟩
          · simp [key, nonEmpty, run, re₂ (k + 2) (by omega), Lynx.Except.andAlso, Lynx.Term.isMember,
              Lynx.Except.orElse, boolAtom]
          · obtain ⟨v₁, v₂, len, h⟩ := s₃ y hy
            exact ⟨v₁, v₂, len, (tt _).mpr h⟩
        · exfalso
          have lw := long w₀ hw₀
          have split : w₀ = w₀.take i ++ w₀[i] :: w₀.drop (i + 1) := by simp
          have hw' := (tt w₀).mp hw₀
          rw [split] at hw'
          exact se₂.mp rfl _ (s₁ _ _ _ (by simp; omega) hw')
      · refine ⟨.atom "badindex", ?_, Or.inr (Or.inl ⟨rfl, ok, ?_⟩)⟩
        · simp [key, nonEmpty, run, Lynx.Except.andAlso, Lynx.Term.isMember, Lynx.Except.orElse, boolAtom]
        · obtain ⟨w, hw, len⟩ := s₂.mp rfl
          exact ⟨w, (tt w).mpr hw, len⟩
    · have r : (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb) = Bool.false := by
        cases h : (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb)
        · rfl
        · simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true'] at h
          exact absurd (only.mpr h) ok
      rw [r] at nonEmpty
      refine ⟨.atom "badtuple", ?_, Or.inl ⟨rfl, ok⟩⟩
      simp [key, nonEmpty, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]


theorem fetch_neg (d : Dispatcher) (a : Term) {z : Int} (h : z < 0) :
    Elixir.Module.Types.Descr.«tuple_fetch/2» d a (.integer z) = .ok (.atom "badindex") := by
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def]
  simp [Erlang.erlang.«</2», Int.compare_eq_lt, h]

theorem fetch_term (d : Dispatcher) (i : Nat) :
    Elixir.Module.Types.Descr.«tuple_fetch/2» d (.atom "term") (.integer i) = .ok (.atom "badtuple") := by
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def]
  simp

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fetching keys of map types: map literals split at a key. -/

/-- Fields without a key. -/
def eraseKey (a : String) (l : List (Term × Term)) : List (Term × Term) :=
  l.filter fun e => !decide (compareExact (fuel (.atom a) e.1) (.atom a) e.1 = .eq)

theorem lookup_eraseKey (a s : String) (l : List (Term × Term)) :
    mapLookup (eraseKey a l) (.atom s) = if s = a then none else mapLookup l (.atom s) := by
  simp only [eraseKey, mapLookup_remove]
  by_cases h : s = a <;> simp [h]

theorem eraseKey_of_absent {a : String} {l : List (Term × Term)} (h : ∀ e ∈ l, e.1 ≠ .atom a) : eraseKey a l = l :=
  List.filter_eq_self.mpr fun e me => by
    have : ¬compareExact (fuel (.atom a) e.1) (.atom a) e.1 = .eq := fun c => h e me ((atom_compareExact_eq a e.1).mp c)
    simp [this]

section
variable {E : Term → Prop}

theorem fieldsV_eraseKey {a : String} {l : List (Term × Term)} (sl : FieldsV E l) : FieldsV E (eraseKey a l) :=
  ⟨fun e me => sl.1 e (List.mem_filter.mp me).1, sl.2.filter _⟩

/-- `orddict:take/2` on the fields of value maps. -/
theorem take_val (a : String) : ∀ {l : List (Term × Term)}, FieldsV E l → ∀ (acc : List (Term × Term)),
    Erlang.orddict.«take_1/3» (.atom a) (fieldsTerm l) (fieldsTerm acc) =
      match mapLookup l (.atom a) with
      | some f => .ok (.tuple #[f, fieldsTerm (acc.reverse ++ eraseKey a l)])
      | none => .ok (.atom "error")
  | [], _, acc => by rw [Erlang.orddict.«take_1/3».eq_def]; simp [fieldsTerm, Term.list, mapLookup]
  | (k, v) :: t, sl, acc => by
    obtain ⟨b, rfl⟩ := (sl.1 _ List.mem_cons_self).1
    have st := fieldsV_tail sl
    have hd := fieldsV_head sl
    rcases cmp : Term.compare (Term.fuel (.atom a) (.atom b)) (.atom a) (.atom b)
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have none : mapLookup t (.atom a) = Option.none := lookup_none fun e me eq => by
        have := cmp_lt_trans cmp (hd e me)
        rw [eq, compare_self] at this; cases this
      rw [Erlang.orddict.«take_1/3».eq_def, lookup_cons_atom, ite_eq_right ne, none]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», cmp]
    · have ab : a = b := Std.compare_eq_iff_eq.mp (by rw [← atoms_cmp]; exact cmp)
      subst ab
      have absent : ∀ e ∈ t, e.1 ≠ .atom a := fun e me eq => by
        have := hd e me; rw [eq, compare_self] at this; cases this
      have er : eraseKey a ((.atom a, v) :: t) = t := by
        have := eraseKey_of_absent absent
        simp only [eraseKey, List.filter_cons] at this ⊢
        simp [this]
      rw [Erlang.orddict.«take_1/3».eq_def, lookup_cons_atom, ite_eq_left rfl, er]
      simp [fieldsTerm, Term.list, Erlang.erlang.«</2», Erlang.erlang.«>/2», reverse_list]
    · have ne : b ≠ a := by
        rintro rfl; rw [compare_self] at cmp; cases cmp
      have ih := take_val a st ((.atom b, v) :: acc)
      have er : eraseKey a ((.atom b, v) :: t) = (.atom b, v) :: eraseKey a t := by
        simp [eraseKey, List.filter_cons]
        exact fun h => ne h.symm
      rw [Erlang.orddict.«take_1/3».eq_def, lookup_cons_atom, ite_eq_right ne, er]
      simp only [fieldsTerm, List.map_cons, Term.list] at ih ⊢
      simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», cmp, ih]

end

theorem eraseKey_none {a : String} {l : List (Term × Term)} (h : mapLookup l (.atom a) = none) : eraseKey a l = l :=
  List.filter_eq_self.mpr fun e me => by
    have : ¬compareExact (fuel (.atom a) e.1) (.atom a) e.1 = .eq := fun c => by
      have := (mapLookup_isSome l (.atom a)).mpr ⟨e, me, c⟩
      rw [h] at this; cases this
    simp [this]

/-- The field a map literal gives a key. -/
def fieldAt (tag : Term) (l : List (Term × Term)) (a : String) : Term := (mapLookup l (.atom a)).getD (tagField tag)

/-- A map of values without a key. -/
def eraseK {V : Type} (a : String) (w : MW V) : MW V := fun k => if k = .atom a then none else w k

/-- A map of values with a key set. -/
def setK {V : Type} (a : String) (o : Option V) (w : MW V) : MW V := fun k => if k = .atom a then o else w k

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_pop_key_bdd/3` splits a literal into the field of a key and a literal of the other fields. -/
theorem pop_val {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l) (a : String) :
    ∃ k : Int, Elixir.Module.Types.Descr.«map_pop_key_bdd/3» tag (fieldsTerm l) (.atom a) =
      .ok (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]]) ∧
      KeyOk (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) := by
  obtain ⟨k, run, key⟩ := leaf_new_keyM g ((eraseKey a l).map fun e => .tuple #[e.1, e.2])
  refine ⟨k, ?_, key⟩
  have tk := take_val a sl []
  simp only [List.reverse_nil, List.nil_append] at tk
  have tk' : Erlang.orddict.«take/2» (.atom a) (fieldsTerm l) =
      match mapLookup l (.atom a) with
      | some f => .ok (.tuple #[f, fieldsTerm (eraseKey a l)])
      | none => .ok (.atom "error") := by
    unfold Erlang.orddict.«take/2»; exact tk
  unfold Elixir.Module.Types.Descr.«map_pop_key_bdd/3»
  rw [tk']
  cases h : mapLookup l (.atom a) with
  | none =>
    rw [eraseKey_none h] at run ⊢
    simp only [Lynx.Except.ok_bind, key_tag_field g, Elixir.Module.Types.Descr.«map_new/2»]
    rw [show fieldsTerm l = Term.list (l.map fun e => .tuple #[e.1, e.2]) from rfl, run]
    simp [fieldAt, h]
  | some f =>
    simp only [Lynx.Except.ok_bind, Elixir.Module.Types.Descr.«map_new/2»]
    rw [show fieldsTerm (eraseKey a l) = Term.list ((eraseKey a l).map fun e => .tuple #[e.1, e.2]) from rfl, run]
    simp [fieldAt, h]

theorem tagSem_field (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) (o : Option V) :
    TagSem den tag "atom" o ↔ FieldSem den (tagField tag) o := by
  rcases g with rfl | rfl | ⟨dl, rfl, -⟩
  · rw [fieldSem_tag ef.mopsE ef.mdopsE ef.semR (Or.inl rfl)]; rfl
  · rw [fieldSem_tag ef.mopsE ef.mdopsE ef.semR (Or.inr rfl)]; rfl
  · rw [tagSem_dom]
    simp only [tagField, tagType_dom]

/-- A map literal holds the maps whose key holds a value of its field there, and whose other keys hold what the
literal of its other fields holds. -/
theorem msem_at (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) (l : List (Term × Term)) (a : String)
    (w : MW V) : MSem den tag l w ↔
      FieldSem den (fieldAt tag l a) (w (.atom a)) ∧ MSem den tag (eraseKey a l) (eraseK a w) := by
  constructor
  · intro h
    refine ⟨?_, ⟨fun s => ?_, fun k i => by simpa [eraseK] using h.doms k i⟩⟩
    · have := h.atoms a
      unfold FSem at this
      unfold fieldAt
      cases hl : mapLookup l (.atom a) with
      | none => rw [hl] at this; exact (tagSem_field ef g _).mp this
      | some f => rw [hl] at this; exact this
    · unfold FSem
      rw [lookup_eraseKey]
      by_cases hs : s = a
      · subst hs; simp [eraseK, tagSem_none]
      · have := h.atoms s
        unfold FSem at this
        simpa [eraseK, hs] using this
  · rintro ⟨hf, hm⟩
    refine ⟨fun s => ?_, fun k i => by simpa [eraseK] using hm.doms k i⟩
    by_cases hs : s = a
    · subst hs
      unfold FSem
      unfold fieldAt at hf
      cases hl : mapLookup l (.atom s) with
      | none => rw [hl] at hf; exact (tagSem_field ef g _).mpr hf
      | some f => rw [hl] at hf; exact hf
    · have := hm.atoms s
      unfold FSem at this ⊢
      rw [lookup_eraseKey] at this
      simpa [eraseK, hs] using this

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-- A map of values with the value of one key moved to another, and the first key absent. -/
def mvK (a c : String) (w : MW V) : MW V :=
  fun k => if k = .atom a then none else if k = .atom c then w (.atom a) else w k

theorem mvK_in {a c : String} (ne : a ≠ c) {tag : Term} {l : List (Term × Term)} (ha : mapLookup l (.atom a) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} (h : MSem den tag l w) : MSem den tag l (mvK a c w) := by
  refine ⟨fun s => ?_, fun k i => by simpa [mvK] using h.doms k i⟩
  by_cases hs : s = a
  · subst hs; unfold FSem; rw [ha]; simp [mvK, tagSem_none]
  · by_cases hs' : s = c
    · subst hs'
      have := h.atoms a
      unfold FSem at this ⊢
      rw [ha] at this; rw [hc]
      simpa [mvK, Ne.symm ne] using this
    · simpa [mvK, hs, hs'] using h.atoms s

theorem mvK_back {a c : String} (ne : a ≠ c) {tag : Term} {l : List (Term × Term)} (ha : mapLookup l (.atom a) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} (h : MSem den tag l (mvK a c w))
    (tc : TagSem den tag "atom" (w (.atom c))) : MSem den tag l w := by
  refine ⟨fun s => ?_, fun k i => by simpa [mvK] using h.doms k i⟩
  by_cases hs : s = a
  · subst hs
    have := h.atoms c
    unfold FSem at this ⊢
    rw [hc] at this; rw [ha]
    simpa [mvK, Ne.symm ne] using this
  · by_cases hs' : s = c
    · subst hs'; unfold FSem; rw [hc]; exact tc
    · simpa [mvK, hs, hs'] using h.atoms s

/-- Keys of fields. -/
def keyStrs (l : List (Term × Term)) : List String := l.filterMap fun e => match e.1 with
  | .atom s => some s
  | _ => none

theorem lookup_fresh' {l : List (Term × Term)} {c : String} (h : c ∉ keyStrs l) : mapLookup l (.atom c) = none :=
  lookup_none fun e me eq => h (List.mem_filterMap.mpr ⟨e, me, by rw [eq]⟩)

/-- Strings longer than a bound, of distinct lengths. -/
def freshStrs (M n : Nat) : List String := (List.range n).map fun k => String.ofList (List.replicate (M + k + 1) 'x')

theorem freshStrs_len {M n : Nat} {c : String} (h : c ∈ freshStrs M n) : M < c.length := by
  simp only [freshStrs, List.mem_map, List.mem_range] at h
  obtain ⟨k, -, rfl⟩ := h
  simp; omega

theorem freshStrs_nodup (M n : Nat) : (freshStrs M n).Nodup := by
  unfold freshStrs List.Nodup
  rw [List.pairwise_map]
  refine (List.nodup_range).imp fun {x y} h e => h ?_
  have := congrArg String.length e
  simp at this; omega

theorem freshStrs_length (M n : Nat) : (freshStrs M n).length = n := by simp [freshStrs]

/-- Literals that do not hold maps whose key has been moved to a fresh key, for one of a list of fresh keys. -/
theorem survive (a : String) {w : MW V} (Ns : List (Term × List (Term × Term)))
    (hN : ∀ N ∈ Ns, mapLookup N.2 (.atom a) = none) (out : ∀ N ∈ Ns, ¬MSem den N.1 N.2 w) :
    ∀ (C : List String), C.Nodup → (∀ c ∈ C, c ≠ a ∧ ∀ N ∈ Ns, mapLookup N.2 (.atom c) = none) →
      Ns.length < C.length → ∃ c ∈ C, ∀ N ∈ Ns, ¬MSem den N.1 N.2 (mvK a c w) := by
  induction Ns with
  | nil =>
    intro C _ _ len
    cases C with
    | nil => simp at len
    | cons c _ => exact ⟨c, List.mem_cons_self, by simp⟩
  | cons N rest ih =>
    intro C nd fr len
    have hN' := fun N' (m : N' ∈ rest) => hN N' (List.mem_cons_of_mem _ m)
    have out' := fun N' (m : N' ∈ rest) => out N' (List.mem_cons_of_mem _ m)
    have fr' : ∀ c ∈ C, c ≠ a ∧ ∀ N' ∈ rest, mapLookup N'.2 (.atom c) = none :=
      fun c mc => ⟨(fr c mc).1, fun N' m => (fr c mc).2 N' (List.mem_cons_of_mem _ m)⟩
    by_cases killed : ∃ c₀ ∈ C, MSem den N.1 N.2 (mvK a c₀ w)
    · obtain ⟨c₀, mc₀, h₀⟩ := killed
      -- Only that key: another one would show the literal holds the map itself.
      have only : ∀ c ∈ C, c ≠ c₀ → ¬MSem den N.1 N.2 (mvK a c w) := by
        intro c mc ne hc
        have na₀ := (fr c₀ mc₀).1
        have hc₀ := (fr c₀ mc₀).2 N List.mem_cons_self
        have tc : TagSem den N.1 "atom" (w (.atom c₀)) := by
          have := hc.atoms c₀
          unfold FSem at this
          rw [hc₀] at this
          simpa [mvK, na₀, Ne.symm ne] using this
        exact out N List.mem_cons_self
          (mvK_back (Ne.symm na₀) (hN N List.mem_cons_self) hc₀ h₀ tc)
      obtain ⟨c, mc, hc⟩ := ih hN' out' (C.erase c₀) (nd.erase c₀)
        (fun c m => fr' c (List.mem_of_mem_erase m)) (by rw [List.length_erase_of_mem mc₀]; simp at len; omega)
      have ne : c ≠ c₀ := fun e => by subst e; exact (List.Nodup.not_mem_erase nd) mc
      refine ⟨c, List.mem_of_mem_erase mc, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact only c (List.mem_of_mem_erase mc) ne
      · exact hc N' m
    · obtain ⟨c, mc, hc⟩ := ih hN' out' C nd fr' (by simp at len; omega)
      refine ⟨c, mc, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact fun h => killed ⟨c, mc, h⟩
      · exact hc N' m

theorem le_maxLen : ∀ (L : List String), ∀ s ∈ L, s.length ≤ (L.map String.length).foldr max 0
  | [], _, h => by simp at h
  | x :: L, s, h => by
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxLen L s h) (Nat.le_max_right _ _)

/-- A map in a literal and outside others, none of which mention a key, can do without the key. -/
theorem aless (a : String) {tag : Term} {l : List (Term × Term)} (hB : mapLookup l (.atom a) = none)
    (Ns : List (Term × List (Term × Term))) (hN : ∀ N ∈ Ns, mapLookup N.2 (.atom a) = none) {w : MW V}
    (hb : MSem den tag l w) (out : ∀ N ∈ Ns, ¬MSem den N.1 N.2 w) :
    ∃ u : MW V, u (.atom a) = none ∧ MSem den tag l u ∧ ∀ N ∈ Ns, ¬MSem den N.1 N.2 u := by
  let L : List String := a :: keyStrs l ++ Ns.flatMap fun N => keyStrs N.2
  let M := (L.map String.length).foldr max 0
  have fresh : ∀ c ∈ freshStrs M (Ns.length + 1), c ∉ L := fun c mc mL => by
    have := le_maxLen L c mL; have := freshStrs_len mc; omega
  obtain ⟨c, mc, hc⟩ := survive a Ns hN out (freshStrs M (Ns.length + 1)) (freshStrs_nodup M _)
    (fun c mc => ⟨fun e => fresh c mc (by simp [L, e]), fun N mN => lookup_fresh' fun m =>
      fresh c mc (by simp only [L, List.mem_cons, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨N, mN, m⟩)⟩)
    (by rw [freshStrs_length]; omega)
  have na : a ≠ c := fun e => fresh c mc (by simp [L, e])
  refine ⟨mvK a c w, by simp [mvK], mvK_in na hB (lookup_fresh' fun m => fresh c mc (by simp [L, m])) hb, hc⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- Lines of map BDDs: a tag, fields, and negated literals. -/
def MLine (E : Term → Prop) (L : Term) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    TagV E tag ∧ FieldsV E l ∧ ∀ t ∈ negs, MapLitV E t

/-- Maps of values in a line. -/
def InMLine (den : Term → V → Prop) (L : Term) (w : MW V) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    MSem den tag l w ∧ ∀ N ∈ negs, ¬NSem den N w

theorem inMLine_iff {tag : Term} {l : List (Term × Term)} {negs : List Term} {w : MW V} :
    InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w ↔ MSem den tag l w ∧ ∀ N ∈ negs, ¬NSem den N w := by
  constructor
  · rintro ⟨tag', l', negs', e, h, hn⟩
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    rw [e₁, fieldsTerm_inj e₂, list_inj e₃]
    exact ⟨h, hn⟩
  · intro h; exact ⟨tag, l, negs, rfl, h⟩

/-- `map_bdd_to_dnf/5` lists the lines of a map BDD. -/
theorem dnf_map (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K + 2 ≤ m)
    {S : List (Term × Term)} (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (okT : ∀ t, ok t → MapLitV E t) :
    ∀ (acc : List Term) (pos : Term) (negs : List Term), MapPosV E pos → (∀ t ∈ negs, MapLitV E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list acc) pos (Term.list negs) r (.map S) =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, MLine E L) ∧
        ∀ v, (∃ L ∈ lines, InMLine den L v) ↔
          (InPosM den pos v ∧ (∀ N ∈ negs, ¬NSem den N v) ∧ eval (valM E den v) r = Bool.true) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → MapLitV E t) →
    ∀ (acc : List Term) (pos : Term) (negs : List Term), MapPosV E pos → (∀ t ∈ negs, MapLitV E t) →
      ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list acc) pos (Term.list negs) r (.map S) =
          .ok (Term.list (lines ++ acc)) ∧ (∀ L ∈ lines, MLine E L) ∧
        ∀ v, (∃ L ∈ lines, InMLine den L v) ↔
          (InPosM den pos v ∧ (∀ N ∈ negs, ¬NSem den N v) ∧ eval (valM E den v) r = Bool.true))
    ?_ ?_ ?_ ?_ ok r wr okT
  · intro ok _ acc pos negs hp lits
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    refine ⟨[.tuple #[tag, fieldsTerm l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp [inMLine_iff, inPosM_iff]
  · intro ok _ acc pos negs _ _
    refine ⟨[], ?_, by simp, fun v => by simp⟩
    rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp
  · intro ok k x y okl okLit acc pos negs hp lits
    have hl := okLit _ okl
    rcases inter_val ops dops sem hm hS hp hl with ⟨empty, none⟩ | ⟨pos', run, hp', sem'⟩
    · refine ⟨[], ?_, by simp, fun v => ?_⟩
      · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [empty]
      · simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and, eval_leaf]
        intro hv _ e
        exact none v hv ((valM_iff ops dops sem hl).mp e)
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    refine ⟨[.tuple #[tag, fieldsTerm l, Term.list negs]], ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]; simp [run, Term.list]
    · intro L mL; simp at mL; subst mL; exact ⟨tag, l, negs, rfl, gt, el, lits⟩
    · simp only [List.mem_singleton, exists_eq_left, inMLine_iff, eval_leaf, valM_iff ops dops sem hl]
      rw [← inPosM_iff, sem' v]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit acc pos negs hp lits
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → MapLitV E t := fun t ht => okLit t ht.1
    obtain ⟨Lu, ru, tu, su⟩ := iu okLit' acc pos negs hp lits
    have lits' : ∀ t ∈ lit :: negs, MapLitV E t := fun t mt => by
      rcases List.mem_cons.mp mt with rfl | mt
      · exact hl
      · exact lits t mt
    obtain ⟨Lc, runC, tc, sc⟩ : ∃ Lc,
        ((Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) = .ok (.atom "empty") ∧ Lc = []) ∨
          ∃ tag2 l2, Elixir.Module.Types.Descr.«map_line_intersection/3» (D m) pos lit (.map S) =
              .ok (.tuple #[tag2, fieldsTerm l2]) ∧
            Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) (Term.list (Lu ++ acc)) (.tuple #[tag2, fieldsTerm l2])
              (Term.list negs) c (.map S) = .ok (Term.list (Lc ++ (Lu ++ acc)))) ∧ (∀ L ∈ Lc, MLine E L) ∧
          ∀ v, (∃ L ∈ Lc, InMLine den L v) ↔
            (InPosM den pos v ∧ NSem den lit v ∧ (∀ N ∈ negs, ¬NSem den N v) ∧ eval (valM E den v) c = Bool.true) := by
      rcases inter_val ops dops sem hm hS hp hl with ⟨empty, none⟩ | ⟨pos2, run, hp2, sem2⟩
      · exact ⟨[], Or.inl ⟨empty, rfl⟩, by simp, fun v => by
          simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_and]
          exact fun hv hlit => absurd hlit (none v hv)⟩
      obtain ⟨Lc, rc, tc, sc⟩ := ic okLit' (Lu ++ acc) pos2 negs hp2 lits
      obtain ⟨tag2, l2, rfl, -⟩ := hp2
      refine ⟨Lc, Or.inr ⟨tag2, l2, run, rc⟩, tc, fun v => ?_⟩
      rw [sc v, sem2 v]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    obtain ⟨Ld, rd, td, sd⟩ := idd okLit' (Lc ++ (Lu ++ acc)) pos (lit :: negs) hp lits'
    rw [list_cons] at rd
    refine ⟨Ld ++ Lc ++ Lu, ?_, ?_, fun v => ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_bdd_to_dnf/5».eq_def]
      obtain ⟨tag, l, rfl, -⟩ := hp
      rcases runC with ⟨e, rfl⟩ | ⟨tag2, l2, e, rc⟩
      · simp only [List.nil_append] at rd
        simp [ru, e, rd]
      · simp [ru, e, rc, rd]
    · intro L mL
      simp only [List.mem_append] at mL
      rcases mL with (mL | mL) | mL
      · exact td L mL
      · exact tc L mL
      · exact tu L mL
    · have split : (∃ L ∈ Ld ++ Lc ++ Lu, InMLine den L v) ↔
          (∃ L ∈ Ld, InMLine den L v) ∨ (∃ L ∈ Lc, InMLine den L v) ∨ (∃ L ∈ Lu, InMLine den L v) := by
        constructor
        · rintro ⟨L, mL, hL⟩
          simp only [List.mem_append] at mL
          rcases mL with (mL | mL) | mL
          · exact Or.inl ⟨L, mL, hL⟩
          · exact Or.inr (Or.inl ⟨L, mL, hL⟩)
          · exact Or.inr (Or.inr ⟨L, mL, hL⟩)
        · rintro (⟨L, mL, hL⟩ | ⟨L, mL, hL⟩ | ⟨L, mL, hL⟩) <;> exact ⟨L, by simp [mL], hL⟩
      rw [split, sd v, sc v, su v, eval_node]
      by_cases hlit : NSem den lit v
      · have e : valM E den v lit = Bool.true := (valM_iff ops dops sem hl).mpr hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inl ⟨a, b, c⟩) (fun c => Or.inr ⟨a, b, c⟩)⟩
      · have e : valM E den v lit = Bool.false := by
          cases h' : valM E den v lit
          · rfl
          · exact absurd ((valM_iff ops dops sem hl).mp h') hlit
        simp [e, hlit]
        exact ⟨fun h => h.elim (fun ⟨a, b, c⟩ => ⟨a, b, Or.inr c⟩) (fun ⟨a, b, c⟩ => ⟨a, b, Or.inl c⟩),
          fun ⟨a, b, c⟩ => c.elim (fun c => Or.inr ⟨a, b, c⟩) (fun c => Or.inl ⟨a, b, c⟩)⟩

/-- Map lines either hold a map of values or are empty. -/
theorem mline_keep (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    (jsem : ElemDisjSem E K V den Safe) (hS : Safe []) {L : Term}
    (hL : MLine E L) : ∃ keep : Bool, (∀ m acc, K + 4 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ w, InMLine den L w) := by
  obtain ⟨tag, l, negs, rfl, gt, sl, lits⟩ := hL
  obtain ⟨b, run⟩ := init_total ops dops jops [] gt.plain (fun e me => (sl.1 e me).2) (fun t m => (lits t m).plain)
  have sem' : b = Bool.true ↔ ∀ w, MSem den tag l w → CovM den negs w := by
    constructor
    · rintro rfl; exact init_sound ops dops sem jops (m := K + 4) (by omega) hS gt sl lits (run (K + 4) (by omega))
    · intro h
      have := (run (K + 4) (by omega)).symm.trans (init_val ops dops sem jops jsem (m := K + 4) (by omega) hS gt sl lits h)
      cases b
      · simp [boolAtom] at this
      · rfl
  refine ⟨!b, fun m acc hm => ?_, ?_⟩
  · obtain ⟨n, rfl, hn⟩ := succ_of_le (show 1 ≤ m by omega)
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_bdd_to_dnf_remove_empty/1-fun-0-/2».pure]
    cases b <;> simp [Elixir.Module.Types.Descr.«-map_bdd_to_dnf_remove_empty/1-fun-0-/2»,
      Elixir.Module.Types.Descr.«init_map_line_empty?/3», run n (by omega), Lynx.Term.isMember, boolAtom]
  · rw [Bool.not_eq_true', ← Bool.not_eq_true, sem']
    constructor
    · intro h
      obtain ⟨w, hw⟩ := Classical.not_forall.mp h
      obtain ⟨hm, hc⟩ := Classical.not_imp.mp hw
      exact ⟨w, inMLine_iff.mpr ⟨hm, fun N mN hN => hc ⟨N, mN, hN⟩⟩⟩
    · rintro ⟨w, hw⟩ h
      obtain ⟨hm, hn⟩ := inMLine_iff.mp hw
      obtain ⟨N, mN, hN⟩ := h w hm
      exact hn N mN hN

/-- `map_bdd_to_dnf_remove_empty/1` lists the non-empty lines of a map BDD. -/
theorem dnf_neg_map (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) (jops : ElemDisj E K)
    (jsem : ElemDisjSem E K V den Safe) (hS : Safe []) {m : Nat}
    (hm : K + 4 ≤ m) {r : Term} (wr : Bdd (MLit E) r) :
    ∃ lines : List Term, Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1» (D m) r =
        .ok (Term.list lines) ∧ (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) ∧
      ∀ w, eval (valM E den w) r = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := by
  obtain ⟨all, run, tl, sl⟩ := dnf_map (den := den) ops dops sem (m := m) (by omega) hS wr (fun t h => h.1) []
    (.tuple #[.atom "open", .nil]) [] ⟨.atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩ (by simp)
  have keeps : ∀ L ∈ all, ∃ keep : Bool, (∀ m acc, K + 4 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep then .cons L acc else acc)) ∧ (keep = Bool.true ↔ ∃ w, InMLine den L w) :=
    fun L mL => mline_keep ops dops sem jops jsem hS (tl L mL)
  classical
  let keep : Term → Bool := fun L => if h : L ∈ all then Classical.choose (keeps L h) else Bool.false
  have hk : ∀ L ∈ all, (∀ m acc, K + 4 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) #[L, acc] =
        .ok (if keep L then .cons L acc else acc)) ∧ (keep L = Bool.true ↔ ∃ w, InMLine den L w) := by
    intro L mL
    simp only [keep, dite_eq_left mL]
    exact Classical.choose_spec (keeps L mL)
  have fold := foldl_det (K := K + 4) "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" #[]
    (fun x a => if keep x then .cons x a else a) all (fun x mx a m hm => (hk x mx).1 m a hm) .nil hm
  have e := foldl_filter keep all []
  simp only [List.append_nil] at e
  simp only [Term.list] at e
  refine ⟨(all.filter keep).reverse, ?_, fun L mL => ?_, fun w => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_bdd_to_dnf_remove_empty/1»
    have run' : Elixir.Module.Types.Descr.«map_bdd_to_dnf/5» (D m) .nil (.tuple #[.atom "open", .nil]) .nil r (.map []) =
        .ok (Term.list all) := by simpa using run
    simp only [run', Lynx.Except.ok_bind]
    rw [show (do
        let f ← (pure (Term.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[]) :
          Except Exception Term)
        Erlang.lists.«foldl/3» (D m) f .nil (Term.list all)) =
        Erlang.lists.«foldl/3» (D m) (.function false "Elixir.Module.Types.Descr" "-map_bdd_to_dnf_remove_empty/1-fun-0-" 2 #[])
          .nil (Term.list all) from rfl, fold, e]
  · simp only [List.mem_reverse, List.mem_filter] at mL
    exact ⟨tl L mL.1, (hk L mL.1).2.mp mL.2⟩
  · have hp : InPosM den (.tuple #[.atom "open", .nil]) w := ⟨.atom "open", [], rfl, ⟨fun s => by
      simp [FSem, TagSem, mapLookup], fun k i => by simp [TagSem]⟩⟩
    rw [← (by simpa [hp] using sl w : (∃ L ∈ all, InMLine den L w) ↔ eval (valM E den w) r = Bool.true)]
    constructor
    · rintro ⟨L, mL, hL⟩
      exact ⟨L, by simp [mL, (hk L mL).2.mpr ⟨w, hL⟩], hL⟩
    · rintro ⟨L, mL, hL⟩
      simp only [List.mem_reverse, List.mem_filter] at mL
      exact ⟨L, mL.1, hL⟩

end

end Elixir.STTDescrProofsTest.Nest
