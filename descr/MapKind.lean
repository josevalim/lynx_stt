module

public import Erlang.program
public import MapLiteralIntersections

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Maps are a structural kind, and the three kinds together. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Valuations of map literals that maps of values induce. -/
def ValMN (E : Term → Prop) (den : Term → V → Prop) (ρ : Term → Bool) : Prop := ∃ w : MW V, ρ = valM E den w

theorem dn_mapW {x : Term} {p : Point} {w : MW V} (e : p.2.2 = valM E den w) :
    dn "map" (some x) p = denMF E den x w := by
  rw [dn_map, e]; rfl

theorem mfield_nz {w : Term} (fw : MField E w) : w ≠ .integer 0 := by
  rcases fw with ⟨k, rfl⟩ | ww
  · simp
  · exact bdd_ne_zero ww

theorem denMF_bot (w : MW V) : denMF E den (.atom "bdd_bot") w = Bool.false := by
  simp [denMF, denO, isOpenTop]

theorem mapKind (ef : EF nd E V den tl K) : KindOk (K + 4) "map" (MField E) (ValMN E den) where
  resp := fun _ ⟨w, e⟩ => e ▸ valM_resp w
  wit := ⟨_, fun _ => none, rfl⟩
  top := fun t ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ <;> try simp at h
    exact ⟨Or.inl ⟨_, rfl⟩, lh_top_leaf _, fun p _ => by rw [dn_map, denO_top]⟩
  congr := fun fx fx' e p ⟨w, hw⟩ => by
    rw [dn_mapW hw, dn_mapW hw]
    exact denMF_resp fx fx' e w
  union := fun fx fy => by
    obtain ⟨r, run, fr, sem, le⟩ := map_field_union (den := den) fx fy
    exact ⟨r, fun m _ => run _, fr, fun p ⟨w, hw⟩ => by rw [dn_mapW hw, dn_mapW hw, dn_mapW hw, sem], le⟩
  inter := fun fx fy => by
    obtain ⟨r, run, fr, sem, le⟩ := map_field_inter (den := den) fx fy
    refine ⟨r, fun m _ => run _, fun _ => ⟨fr, le⟩, fun p ⟨w, hw⟩ => ?_⟩
    cases k : kept (.atom "map", r)
    · rw [keptO_false k, dn_none, dn_mapW hw, dn_mapW hw, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (mfield_nz fr), denMF_bot]
    · rw [keptO_true k, dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]
  diff := fun fx fy => by
    obtain ⟨r, run, fr, sem, le⟩ := map_field_diff (den := den) fx fy
    refine ⟨r, fun m _ => run _, fun k => ⟨fr, le (kept_ne_bot k)⟩, fun p ⟨w, hw⟩ => ?_⟩
    cases k : kept (.atom "map", r)
    · rw [keptO_false k, dn_none, dn_mapW hw, dn_mapW hw, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (mfield_nz fr), denMF_bot]
    · rw [keptO_true k, dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]
  opt_union := by
    intro x y S m fx fy hm
    obtain ⟨r, run, fr, sem⟩ := map_field_opt_union ef (m := m) (by omega) fx fy S
    exact ⟨r, run, fr, fun p ⟨w, hw⟩ => by rw [dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]⟩
  opt_inter := by
    intro x y S m fx fy hm
    obtain ⟨r, run, fr, sem⟩ := map_field_opt_inter ef (m := m) (by omega) fx fy S
    refine ⟨r, run, fun _ => fr, fun p ⟨w, hw⟩ => ?_⟩
    cases k : kept (.atom "map", r)
    · rw [keptO_false k, dn_none, dn_mapW hw, dn_mapW hw, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (mfield_nz fr), denMF_bot]
    · rw [keptO_true k, dn_mapW hw, dn_mapW hw, dn_mapW hw, sem]
  opt_diff := by
    intro x y S m fx fy hm
    obtain ⟨r, run, k, d⟩ := map_field_opt_diff ef (m := m) (by omega) fx fy S
    refine ⟨r, run, fun kw => (k kw).1, fun p ⟨w, hw⟩ => ?_⟩
    cases kw : kept (.atom "map", r)
    · rw [keptO_false kw, dn_none, dn_mapW hw, dn_mapW hw, d kw]
    · rw [keptO_true kw, dn_mapW hw, dn_mapW hw, dn_mapW hw, (k kw).2]
  empty := fun S fx => by
    obtain ⟨b, run, ex⟩ := map_field_empty ef fx S
    refine ⟨b, run, fun N hx hS => (ex N hx hS).trans ⟨fun h p ⟨w, hw⟩ => by rw [dn_mapW hw]; exact h w,
      fun h w => by have := h (0, .nil, valM E den w) ⟨w, rfl⟩; rwa [dn_mapW rfl] at this⟩⟩

theorem KindOk.mono {K K' : Nat} {name : String} {F : Term → Prop} {Val : (Term → Bool) → Prop}
    (k : KindOk K name F Val) (le : K ≤ K') : KindOk K' name F Val where
  resp := k.resp
  wit := k.wit
  top := k.top
  congr := k.congr
  union := fun fx fy => let ⟨w, run, h⟩ := k.union fx fy; ⟨w, fun m hm => run m (by omega), h⟩
  inter := fun fx fy => let ⟨w, run, h⟩ := k.inter fx fy; ⟨w, fun m hm => run m (by omega), h⟩
  diff := fun fx fy => let ⟨w, run, h⟩ := k.diff fx fy; ⟨w, fun m hm => run m (by omega), h⟩
  opt_union := fun {_ _} S {_} fx fy hm => k.opt_union S fx fy (by omega)
  opt_inter := fun {_ _} S {_} fx fy hm => k.opt_inter S fx fy (by omega)
  opt_diff := fun {_ _} S {_} fx fy hm => k.opt_diff S fx fy (by omega)
  empty := fun S fx => let ⟨b, run, h⟩ := k.empty S fx; ⟨b, fun m hm => run m (by omega), h⟩

/-- The structural kinds over element types. -/
theorem kinds (ef : EF nd E V den tl K) : Kinds (K + 4) (TField E) (LF E) (MField E) (ValT E den) (ValLN E den tl)
    (ValMN E den) := ⟨(tupleKind ef).mono (by omega), (listKind ef).mono (by omega), mapKind ef⟩

theorem Kinds.mono {K K' : Nat} {TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
    (ks : Kinds K TF LF MF TV LV MV) (le : K ≤ K') : Kinds K' TF LF MF TV LV MV :=
  ⟨ks.t.mono le, ks.l.mono le, ks.m.mono le⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The bottom level: top list and map fields, and tuple fields of the expansion literal of the node `t`. -/

theorem sub_term_term (d : Dispatcher) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.atom "term") (.atom "term") = .ok (.atom "true") := by
  obtain ⟨T, term, -, -, -, staticT⟩ := unfolded_term_fields
  unfold Elixir.Module.Types.Descr.«subtype?/2»
  simp [term, unfold_map, Erlang.erlang.«is_map_key/2», staticT, any_key, Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
  unfold Elixir.Module.Types.Descr.«subtype_static?/2»
  simp [Erlang.erlang.«=:=/2»]

theorem empty_term_false (d : Dispatcher) :
    Elixir.Module.Types.Descr.«empty?/1» d (.atom "term") = .ok (boolAtom Bool.false) := by
  unfold Elixir.Module.Types.Descr.«empty?/1»; rfl

theorem topF_lh {name : String} {x : Term} (h : topValue name = some x) : lh x = 0 := by
  rcases top_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [lh, lh_nil_map]

theorem topF_dn {name : String} {x : Term} (hn : name = "list" ∨ name = "map") (h : topValue name = some x)
    (p : Point) : dn name (some x) p = Bool.true := by
  rcases hn with rfl | rfl <;> rcases top_cases h with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;>
    simp at e <;> simp [dn_list, dn_map, denL_top, denO_top]

/-- Top list and map fields: their operations keep the top value, and they are not empty. -/
theorem topF_of {name : String} (hn : name = "list" ∨ name = "map") {x : Term} (h : FieldOk name x) :
    topValue name = some x := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tx⟩ <;> first | exact tx | (rcases hn with h | h <;> simp at h)

theorem topKind (name : String) (hn : name = "list" ∨ name = "map") {K : Nat} (hK : 1 ≤ K) :
    KindOk K name (FieldOk name) Resp where
  resp := fun _ h => h
  wit := ⟨_, resp_const Bool.true⟩
  top := fun t ht => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    have tv : topValue name = some t := by
      rcases hn with rfl | rfl <;>
        rcases ht with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all [topValue]
    exact ⟨Or.inr (Or.inr ⟨nb, na, tv⟩), topF_lh tv, fun p _ => topF_dn hn tv p⟩
  congr := fun fx fx' _ p _ => by
    rcases fx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tx⟩ <;> try (rcases hn with h | h <;> simp at h)
    rcases fx' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tx'⟩ <;> try (rcases hn with h | h <;> simp at h)
    rw [topF_dn hn tx, topF_dn hn tx']
  union := fun {x y} fx fy => by
    obtain ⟨r, run, fr⟩ := fieldok_union name fx fy
    have tr : topValue name = some r := by
      rcases fr with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, tr⟩ <;> first | exact tr | (rcases hn with h | h <;> simp at h)
    refine ⟨r, fun m hm => ?_, fr, fun p _ => by rw [topF_dn hn tr, topF_dn hn (topF_of hn fx)]; rfl,
      by rw [topF_lh tr]; omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact run n
  inter := fun {x y} fx fy => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    obtain ⟨r, run, fr, -, -, kr⟩ := inter_key name x y fx fy
    have k := kr nb na
    have tr := topF_of hn (fr k)
    refine ⟨r, fun m _ => run _, fun _ => ⟨fr k, by rw [topF_lh tr]; omega⟩, fun p _ => ?_⟩
    rw [keptO_true k, topF_dn hn tr, topF_dn hn (topF_of hn fx), topF_dn hn (topF_of hn fy)]
    rfl
  diff := fun {x y} fx fy => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    obtain ⟨r, run, -, -, -, kr⟩ := diff_key name x y fx fy
    have k := kr nb na
    refine ⟨r, fun m _ => run _, fun h => absurd (h.symm.trans k) (by decide), fun p _ => ?_⟩
    rw [keptO_false k, dn_none, topF_dn hn (topF_of hn fy)]
    simp
  opt_union := fun {x y} S {m} fx fy hm => by
    have tx := topF_of hn fx
    have ty := topF_of hn fy
    rw [tx] at ty
    cases ty
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact ⟨x, opt_union_top n tx _, fx, fun p _ => by rw [topF_dn hn tx]; rfl⟩
  opt_inter := fun {x y} S {m} fx fy hm => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    obtain ⟨r, run, fr, -, -, kr⟩ := opt_inter_key m name x y (.map S) fx fy
    have k := kr nb na
    have tr := topF_of hn (fr k)
    refine ⟨r, run, fun _ => fr k, fun p _ => ?_⟩
    rw [keptO_true k, topF_dn hn tr, topF_dn hn (topF_of hn fx), topF_dn hn (topF_of hn fy)]
    rfl
  opt_diff := fun {x y} S {m} fx fy hm => by
    have nb : name ≠ "bitmap" := by rcases hn with rfl | rfl <;> decide
    have na : name ≠ "atom" := by rcases hn with rfl | rfl <;> decide
    have tx := topF_of hn fx
    have ty := topF_of hn fy
    rw [tx] at ty
    cases ty
    obtain ⟨r, run, -, -, -, kr⟩ := diff_key name x x fx fx
    have k := kr nb na
    refine ⟨r, by rw [opt_diff_top _ tx, run], fun h => absurd (h.symm.trans k) (by decide), fun p _ => ?_⟩
    rw [keptO_false k, dn_none, topF_dn hn tx]
    rfl
  empty := fun {x} S fx => by
    have tx := topF_of hn fx
    obtain ⟨b, run⟩ : ∃ b, ∀ d, Elixir.Module.Types.Descr.«empty_key?/3» d (.atom name) x (.map S) = .ok (boolAtom b) := by
      rcases hn with rfl | rfl <;> rcases top_cases tx with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> simp at e
      · refine ⟨Bool.false, fun d => ?_⟩
        simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using list_top_nonempty d (.map S)
      · obtain ⟨b, h⟩ := map_top_bool S
        exact ⟨b, fun d => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using h d⟩
    refine ⟨b, fun m _ => run _, fun N _ hS => ?_⟩
    have e : b = Bool.false := by
      rcases hn with rfl | rfl <;> rcases top_cases tx with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> simp at e
      · have r₀ := list_top_nonempty (D 0) (.map S)
        have r₁ := run (D 0)
        simp only [Elixir.Module.Types.Descr.«empty_key?/3»] at r₁
        rw [r₀] at r₁
        cases b <;> simp_all [boolAtom]
      · have r₀ := map_top_nonempty (D 0) (safeF_of hS)
        have r₁ := run (D 0)
        simp only [Elixir.Module.Types.Descr.«empty_key?/3»] at r₁
        rw [r₀] at r₁
        cases b <;> simp_all [boolAtom]
    subst e
    refine ⟨fun h => by simp at h, fun h => ?_⟩
    have := h (0, .nil, fun _ => Bool.true) (resp_const _)
    rw [topF_dn hn tx] at this
    cases this

/-! Tuple fields of the bottom level: BDDs of the expansion literal of `t`. -/

section
variable {t : Term}

theorem pure_diff_sem {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && !denO y ρ) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, Or.inr Bdd.bot,
      fun ρ _ => by simp [denO, isOpenTop, eval]⟩
  have ny := not_top_of_ok wy pureLit_not
  have special : ¬∃ k, y = .tuple #[k, .atom "closed", .nil] := by
    rintro ⟨k, rfl⟩
    unfold Bdd at wy
    split at wy <;> simp_all [PureLit, litN, Term.list]
    obtain ⟨e, -, -, h⟩ := wy
    cases h
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun ρ _ => by simp [denO, isOpenTop, eval]⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_top]
    · refine ⟨_, ?_, Or.inl ⟨kt, rfl⟩, fun ρ _ => by simp [denO, isOpenTop, eval]⟩
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    all_goals
      obtain ⟨w, run, keep, sem⟩ := neg_ok wy
      refine ⟨w, ?_, Or.inr (keep _ wy), fun ρ r => ?_⟩
      · rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run]
      · rw [denO_top, denO_bdd pureLit_not (keep _ wy), denO_bdd pureLit_not wy, sem ρ r]; rfl
  · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
    refine ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx pureLit_not) ny (fun ⟨_, h⟩ => special h), run],
      Or.inr (keep _ wx wy), fun ρ r => ?_⟩
    rw [denO_bdd pureLit_not (keep _ wx wy), denO_bdd pureLit_not wx, denO_bdd pureLit_not wy, sem ρ r]

end

section
variable {t : Term}

/-- Optimized intersections of pure tuple fields are their plain ones. -/
theorem pure_opt_inter {d : Dispatcher} {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) (S : Term) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«opt_tuple_intersection/3»; rfl, fy, fun ρ _ => by rw [denO_top]; rfl⟩
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨x, opt_tuple_inter_top_eq (not_top_of_ok wx pureLit_not), Or.inr wx, fun ρ _ => by rw [denO_top]; simp⟩
  have nx := not_top_of_ok wx pureLit_not
  have ny := not_top_of_ok wy pureLit_not
  have plain : Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S =
      Elixir.Module.Types.Descr.«tuple_intersection/2» x y →
      ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧ OField (PureLit t) w ∧
        ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := by
    intro e
    obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [e, tuple_intersection_bdd nx ny, hr], Or.inr wr, fun ρ hρ => ?_⟩
    rw [denO_bdd pureLit_not wr, denO_bdd pureLit_not wx, denO_bdd pureLit_not wy, semr _ hρ]
  have plainEq := fun h3 h4 h5 => plain (opt_tuple_inter_plain_eq (d := d) (S := S) nx ny h3 h4 h5)
  have closed : ∀ {k fo}, PureLit t (.tuple #[k, .atom "open", fo]) → False := by
    rintro k fo ⟨e, -, h⟩
    simp [litN] at h
  have xAtom : ∀ {s : String}, x = .atom s → ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧
      OField (PureLit t) w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ e _ => by cases e) (fun _ _ _ _ _ _ _ e _ => by cases e)
      (fun _ _ _ _ _ _ _ _ e => by cases e)
  have yAtom : ∀ {s : String}, y = .atom s → ∃ w, Elixir.Module.Types.Descr.«opt_tuple_intersection/3» d x y S = .ok w ∧
      OField (PureLit t) w ∧ ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && denO y ρ) := fun e => by
    subst e
    exact plainEq (fun _ _ _ _ _ _ _ e => by cases e) (fun _ _ _ _ _ _ _ _ e => by cases e)
      (fun _ _ _ _ _ _ _ e _ => by cases e)
  rcases wx.shape with ex | ex | ⟨k₁, a₁, b₁, rfl⟩ | ⟨h₁, lit₁, c₁, u₁, d₁, rfl⟩
  · exact xAtom ex
  · exact xAtom ex
  all_goals rcases wy.shape with ey | ey | ⟨k₂, a₂, b₂, rfl⟩ | ⟨h₂, lit₂, c₂, u₂, d₂, rfl⟩
  all_goals try exact yAtom ey
  · have same := pureLit_exact (Bdd.leaf_iff.mp wx) (Bdd.leaf_iff.mp wy)
    exact ⟨_, opt_tuple_inter_same (pureLit_not _ (Bdd.leaf_iff.mp wx)) same, Or.inr wx,
      fun ρ hρ => by rw [denO_congr pureLit_not (Or.inr wy) (Or.inr wx) (compare_eq_of_compareExact_eq _ _ same) hρ,
        Bool.and_self]⟩
  · exact plainEq (fun _ _ _ _ _ _ _ e => by simp at e) (fun k fo _ _ _ _ _ e _ => closed (e ▸ Bdd.leaf_iff.mp wx))
      (fun _ _ _ _ _ _ _ e => by simp at e)
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun k fo _ _ _ _ _ e _ => closed (e ▸ Bdd.leaf_iff.mp wy))
  · exact plainEq (fun _ _ _ _ _ _ e _ => by simp at e) (fun _ _ _ _ _ _ _ e _ => by simp at e)
      (fun _ _ _ _ _ _ _ e _ => by simp at e)

end

section
variable {t : Term}

/-- Expansions of accepted nodes meet: both hold nil. -/
theorem disj_expN {e e' : Term} (he : IsT t e) (he' : IsT t e') {m : Nat} (hm : 8 ≤ m) :
    Elixir.Module.Types.Descr.«disjoint?/2» (D m) (expN e (keyOf t)) (expN e' (keyOf t)) = .ok (.atom "false") := by
  obtain ⟨s, run⟩ := (pure_sub_disj t).2 (Or.inr ⟨_, rfl, expN_pure he⟩) (Or.inr ⟨_, rfl, expN_pure he'⟩)
  have r := run m (by omega)
  cases s
  · simpa [boolAtom, expN] using r
  exfalso
  have pA := expN_pure he
  have pB := expN_pure he'
  have calls : ∀ {X Y : List (Term × Term)}, PureMap t X → PureMap t Y → ∀ e ∈ mapEntries X,
      ∀ y d', 2 ≤ d' → mapLookup Y e.1 = some y → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
          ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map []) = .ok (boolAtom b)) := by
    intro X Y sX sY x mx y d' hd hy
    have hx := mapLookup_of_mem_mapEntries mx
    obtain ⟨name, key⟩ := sX.atomKey hx
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k⟩ := interP t name x.2 y (sX.fields name x.2 hx) (sY.fields name y hy)
    refine ⟨w, run _, fun kw => ?_⟩
    by_cases nt : name = "tuple"
    · subst nt
      obtain ⟨b, hb⟩ := pure_tuple_empty (fieldP_tuple (k kw)) []
      exact ⟨b, by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using hb d' hd⟩
    · have h := fieldok_empty (D d') name (fieldP_other (k kw) nt)
      exact ⟨Bool.false, by simpa using h⟩
  -- the walk finds the atom field, whose intersection holds nil
  have stA := pA.static
  have stB := pB.static
  have hit : ∀ {X Y : List (Term × Term)}, PureMap t X → PureMap t Y →
      mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) →
      mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) →
      (∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∃ d', 2 ≤ d' ∧ ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map []) = .ok (.atom "true"))) →
      False := by
    intro X Y sX sY hX hY walk
    obtain ⟨x, mx, qx, -⟩ : ∃ x ∈ mapEntries X, compareExact (fuel (.atom "atom") x.1) (.atom "atom") x.1 = .eq ∧ True := by
      have : (mapLookup (mapEntries X) (.atom "atom")).isSome := by rw [mapLookup_mapEntries, hX]; rfl
      obtain ⟨x, mx, qx⟩ := (mapLookup_isSome _ _).mp this
      exact ⟨x, mx, qx, trivial⟩
    have key : x.1 = .atom "atom" := ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qx))
    have hx := mapLookup_of_mem_mapEntries mx
    rw [key, hX] at hx
    obtain ⟨d', -, w, run, out⟩ := walk x mx _ (by rw [key]; exact hY)
    rw [key] at run out
    have hx' : x.2 = .tuple #[.atom "union", .map [(.atom "nil", .nil)]] := (Option.some.inj hx).symm
    rw [hx'] at run
    have fa : FieldOk "atom" (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) :=
      fieldP_other (sX.fields "atom" _ hX) (by decide)
    obtain ⟨r₀, rr, -, -, am, -⟩ := inter_key "atom" _ _ fa fa
    have e₀ : r₀ = w := by have := (rr (D d')).symm.trans run; simpa using this
    subst e₀
    have kr : kept (.atom "atom", r₀) = Bool.true := by
      have := am rfl (.atom "nil")
      cases k : kept (.atom "atom", r₀)
      · simp [k, amemV, mapLookup] at this
      · rfl
    rcases out with k | em
    · rw [k] at kr; cases kr
    · simp [Elixir.Module.Types.Descr.«empty_key?/3»] at em
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (expN e (keyOf t)) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (expN e' (keyOf t)) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  simp only [expN] at hsa hsb
  have ue := upper_expN (D m) e (keyOf t)
  have ue' := upper_expN (D m) e' (keyOf t)
  simp only [expN] at ue ue'
  have h := r
  simp only at h
  unfold Elixir.Module.Types.Descr.«disjoint?/2» at h
  simp [getMapKeys_single, mapLookup, boolAtom] at h
  unfold Elixir.Module.Types.Descr.«non_disjoint_intersection?/2» at h
  rw [Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def] at h
  have hA : mapLookup [(.atom "tuple", litN e (keyOf t)), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]
      (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) := by simp [mapLookup]
  have hB : mapLookup [(.atom "tuple", litN e' (keyOf t)), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])]
      (.atom "atom") = some (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) := by simp [mapLookup]
  by_cases g : sa > sb
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen 2 _ (.map []) (mapEntries _) (calls pB pA) m
      (by have := entries_le_six pB.keys; omega) (not_true (by rw [bind_assoc]; exact h))
    exact hit pB pA hB hA walk
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen 2 _ (.map []) (mapEntries _) (calls pA pB) m
      (by have := entries_le_six pA.keys; omega) (not_true (by rw [bind_assoc]; exact h))
    exact hit pA pB hA hB walk
end

section
variable {t : Term}

/-- `opt_tuple_leaf_difference/3` finds expansion literals in each other. -/
theorem pure_cmp {n : Nat} (hn : 8 ≤ n) (a₁ a₂ type : Term) (h₁ : PureLit t a₁) (h₂ : PureLit t a₂) :
    ∃ res, (D (n + 1)).pure (.function false "Elixir.Module.Types.Descr" "opt_tuple_leaf_difference" 3 #[])
      #[a₁, a₂, type] = .ok res ∧ CmpOk Resp (PureLit t) a₁ a₂ type res := by
  obtain ⟨e₁, he₁, rfl⟩ := h₁
  obtain ⟨e₂, he₂, rfl⟩ := h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:opt_tuple_leaf_difference/3».pure]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have dtt : Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) (.atom "term") (.atom "term") = .ok (.atom "false") := by
    rw [disj_term_l, empty_term_false]; rfl
  have stt := sub_term_term (D (m + 1))
  have dee : Elixir.Module.Types.Descr.«disjoint?/2» (D (m + 1)) e₁ e₂ = .ok (.atom "false") := by
    rw [disj_node_l he₁.node m (expand_isT he₁ m) _ (node_ne_term he₂) (fun X h => by obtain ⟨S, rfl, -⟩ := he₂.node; cases h),
      disj_node_r he₂.node m (expand_isT he₂ m) _ (expN_ne_term _ _) (fun X h => by simp [expN] at h; subst h; simp [mapLookup])]
    exact disj_expN he₁ he₂ (by omega)
  obtain ⟨s, hs⟩ := (pure_sub_disj t).1 (Or.inr ⟨_, rfl, expN_pure he₁⟩) (Or.inr ⟨_, rfl, expN_pure he₂⟩)
  have see : Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) e₁ e₂ = .ok (boolAtom s) := by
    rw [sub_node_l he₁.node m (expand_isT he₁ m), sub_node_r he₂.node m (expand_isT he₂ m)]
    exact hs _ (by omega)
  refine ⟨if s then .atom "subtype" else .atom "none", ?_, ?_⟩
  · simp only [litN, Term.list]
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp [Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«/=/2», Erlang.erlang.«==/2»]
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp [dtt, stt, Erlang.erlang.«/=/2», Lynx.Except.andAlso]
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp [dee, see, Lynx.Except.guard, Erlang.erlang.«/=/2», Lynx.Except.andAlso]
    cases s
    · simp [boolAtom]
    · simp [boolAtom]
      rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
      simp [isMember]
  · cases s
    · exact Or.inr (Or.inr (Or.inr rfl))
    · refine Or.inr (Or.inl ⟨rfl, fun ρ hρ h => ?_⟩)
      rw [← hρ _ _ (compare_eq_of_compareExact_eq _ _ (pureLit_exact ⟨e₂, he₂, rfl⟩ ⟨e₁, he₁, rfl⟩))]
      exact h

/-- Optimized differences of pure tuple fields. -/
theorem pure_opt_diff {n : Nat} (hn : 8 ≤ n) {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_difference/2» (D (n + 1)) x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ && !denO y ρ) := by
  obtain ⟨w, run, fw, sem⟩ := pure_diff_sem fx fy
  rcases opt_tuple_split (D (n + 1)) x y with e | ⟨e, eb, ny, nx⟩ | ⟨k, a, b, rfl, same, e⟩
  · exact ⟨w, by rw [e, run], fw, sem⟩
  rotate_left
  · refine ⟨_, e, Or.inr Bdd.bot, fun ρ hρ => ?_⟩
    rw [denO_congr pureLit_not fy fx (compare_eq_of_compareExact_eq _ _ same) hρ,
      show denO (.atom "bdd_bot") ρ = Bool.false by simp [denO, isOpenTop]]
    cases denO (.tuple #[k, a, b]) ρ <;> rfl
  rw [e]
  have wy : Bdd (PureLit t) y := by
    rcases fy with ⟨k, rfl⟩ | wy
    · exact absurd rfl (ny _)
    · exact wy
  rcases fx with ⟨k, rfl⟩ | wx
  · rcases nx with nx | nx
    · exact absurd rfl (nx _)
    have wx : Bdd (fun l => l = .tuple #[.integer k, .atom "open", .nil]) (.tuple #[.integer k, .atom "open", .nil]) :=
      Bdd.leaf_iff.mpr rfl
    rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
  obtain ⟨r, hr, okr, semr⟩ := diff3_ok (Val := Resp) (fun _ h => h)
    (fun a₁ a₂ type _ h₁ h₂ => pure_cmp hn a₁ a₂ type h₁ h₂) _ y wy (fun _ h => h) x wx
  refine ⟨r, hr, Or.inr okr, fun ρ hρ => ?_⟩
  rw [denO_bdd pureLit_not okr, denO_bdd pureLit_not wx, denO_bdd pureLit_not wy, semr _ hρ]

/-- Expansion literals fuse into themselves. -/
theorem pure_fuse_leaf (d : Dispatcher) {e e' : Term} (he : IsT t e) (he' : IsT t e') :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» d (litN e (keyOf t)) (litN e' (keyOf t)) = .ok (litN e (keyOf t)) := by
  have ee := isT_exact he' he
  have leaf := leaf_isT he
  simp only [litN, Term.list] at leaf ⊢
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
  simp [Erlang.erlang.«=:=/2», Erlang.erlang.«length/1», Erlang.erlang.«==/2», Erlang.erlang.«and/2»,
    Term.true]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
  simp [Erlang.erlang.«=:=/2»]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
  simp [Erlang.erlang.«=:=/2», ee]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
  simp [Erlang.lists.«reverse/1», leaf]
  done

theorem pure_union {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) :=
  open_union_spec pureLit_not _ tuple_union_shape.1 tuple_union_shape.2.1 tuple_union_shape.2.2 fx fy

theorem chain_atom (d : Dispatcher) (s : String) (leaf z : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» d (.atom s) leaf z = .ok (.atom "nil") := by
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
  split <;> first | rfl | simp_all

theorem fuse_leaf_top (d : Dispatcher) (e : Term) (k k' : Int) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2» d (litN e k) (.tuple #[.integer k', .atom "open", .nil]) =
      .ok (.atom "nil") := by
  simp only [litN, Term.list]
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_leaf/2»
  simp [Erlang.erlang.«=:=/2», Erlang.erlang.«and/2», Term.false,
    Erlang.erlang.«length/1», Erlang.erlang.«==/2»]

theorem hρ_same {e e' : Term} (he : IsT t e) (he' : IsT t e') (ρ : Term → Bool) (hρ : Resp ρ) :
    ρ (litN e' (keyOf t)) = ρ (litN e (keyOf t)) :=
  hρ _ _ (compare_eq_of_compareExact_eq _ _ (pureLit_exact ⟨e, he, rfl⟩ ⟨e', he', rfl⟩))

/-- Adding a leaf to a node of expansion literals. -/
theorem pure_union_leaf (m : Nat) {j : Int} {e₀ : Term} (h₀ : IsT t e₀) (c u d : Bool)
    (fb : OField (PureLit t) (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d])) {leaf : Term}
    (fl : OField (PureLit t) leaf) (lf : (∃ k, leaf = .tuple #[.integer k, .atom "open", .nil]) ∨ PureLit t leaf) :
    ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m)
      (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) leaf = .ok r ∧ OField (PureLit t) r ∧
      ∀ ρ, Resp ρ → denO r ρ = (denO (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) ρ || denO leaf ρ) := by
  obtain ⟨w, run, fw, sem⟩ := pure_union fb fl
  have plain : Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m)
      (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) leaf (.integer 64) = .ok (.atom "nil") →
      ∃ r, Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2» (D m)
        (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) leaf = .ok r ∧ OField (PureLit t) r ∧
        ∀ ρ, Resp ρ → denO r ρ = (denO (.tuple #[.integer j, litN e₀ (keyOf t), bt c, bt u, bt d]) ρ || denO leaf ρ) := by
    intro ch
    refine ⟨w, ?_, fw, sem⟩
    rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
    simp [ch, run]
  by_cases shape : c = Bool.true ∧ d = Bool.false
  · obtain ⟨rfl, rfl⟩ := shape
    rcases lf with ⟨k, rfl⟩ | ⟨e', he', rfl⟩
    · apply plain
      rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
      cases u <;> simp [bt, fuse_leaf_top, isMember, chain_atom]
    · have fl' : Bdd (PureLit t) (litN e₀ (keyOf t)) := Bdd.leaf_iff.mpr ⟨e₀, h₀, rfl⟩
      have fl'' : Bdd (PureLit t) (litN e' (keyOf t)) := Bdd.leaf_iff.mpr ⟨e', he', rfl⟩
      have wb : Bdd (PureLit t) (.tuple #[.integer j, litN e₀ (keyOf t), bt Bool.true, bt u, bt Bool.false]) := by
        rcases fb with ⟨k, h⟩ | w
        · simp at h
        · exact w
      have same := hρ_same (t := t) h₀ he'
      have ch : ∀ uu : Term, Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3» (D m)
          (.tuple #[.integer j, litN e₀ (keyOf t), bt Bool.true, uu, bt Bool.false]) (litN e' (keyOf t)) (.integer 64) =
          .ok (.tuple #[litN e₀ (keyOf t), uu]) := by
        intro uu
        rw [show bt Bool.true = .atom "bdd_top" from rfl, show bt Bool.false = .atom "bdd_bot" from rfl,
          Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
        simp only [pure_fuse_leaf (D m) h₀ he']
        simp [isMember, litN, Term.list]
      cases u
      · refine ⟨_, ?_, Or.inr fl', fun ρ hρ => ?_⟩
        · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def, ch]
          rfl
        · rw [denO_bdd pureLit_not fl', denO_bdd pureLit_not fl'', denO_bdd pureLit_not wb]
          have s' := same ρ hρ
          simp only [litN, Term.list] at s' ⊢
          simp [eval, bt, s']
      · obtain ⟨w', run', fw', sem'⟩ := pure_union (Or.inr (Bdd.top (ok := PureLit t))) (Or.inr fl')
        refine ⟨w', ?_, fw', fun ρ hρ => ?_⟩
        · rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def, ch]
          simp only [bt]
          simp
          rw [Elixir.Module.Types.Descr.«opt_tuple_union_leaf/2».eq_def]
          simp [chain_atom, run']
        · rw [sem' ρ hρ, denO_bdd pureLit_not (Bdd.top (ok := PureLit t)), denO_bdd pureLit_not wb]
          simp [eval, bt]
  · apply plain
    rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_chain/3».eq_def]
    cases c <;> cases d <;> simp_all [bt]
    all_goals done

theorem via_pure_union {m : Nat} {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y)
    (e : Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = Elixir.Module.Types.Descr.«tuple_union/2» x y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) := by
  obtain ⟨w, run, fw, sem⟩ := pure_union fx fy
  exact ⟨w, by rw [e, run], fw, sem⟩

/-- Optimized unions of pure tuple fields. -/
theorem pure_opt_union (m : Nat) {x y : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_union/2» (D m) x y = .ok w ∧ OField (PureLit t) w ∧
      ∀ ρ, Resp ρ → denO w ρ = (denO x ρ || denO y ρ) := by
  have fx' := fx
  have fy' := fy
  rcases pure_cases fx with ⟨k₁, rfl⟩ | rfl | rfl | ⟨e₁, h₁, rfl⟩ | ⟨j₁, e₁, c₁, u₁, d₁, h₁, rfl⟩ <;>
    rcases pure_cases fy with ⟨k₂, rfl⟩ | rfl | rfl | ⟨e₂, h₂, rfl⟩ | ⟨j₂, e₂, c₂, u₂, d₂, h₂, rfl⟩
  all_goals first
    | exact via_pure_union fx' fy' (by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; rfl)
    | (apply via_pure_union fx' fy'
       unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
       simp only [leaf_guard, node_ne3, ite_false, litN, Term.list]
       done)
    | skip
  -- two top leaves
  · by_cases same : compareExact (fuel (.tuple #[.integer k₂, .atom "open", .nil]) (.tuple #[.integer k₁, .atom "open", .nil])) (.tuple #[.integer k₂, .atom "open", .nil]) (.tuple #[.integer k₁, .atom "open", .nil]) = .eq
    · refine ⟨_, by unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»; simp only [leaf_guard, ite_eq_left same]; rfl,
        fx', fun ρ _ => by simp [denO_top]⟩
    have st := strategy_start (D m) "open" "open" (Or.inl rfl) (Or.inl rfl) [] []
    simp only [Term.list, List.length_nil, and_self, ite_true] at st
    rw [show Term.nil = Term.list [] from rfl, index_nil_left] at st
    refine ⟨_, ?_, fy', fun ρ _ => by simp [denO_top]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2», same, st, endSt]
  -- the top leaf and a literal
  · have same : ¬compareExact (fuel (litN e₂ (keyOf t)) (.tuple #[.integer k₁, .atom "open", .nil])) (litN e₂ (keyOf t)) (.tuple #[.integer k₁, .atom "open", .nil]) = .eq := by
      simp [litN, Term.list, compareExact_tuple, List.compareLex_cons_cons]
    have st := strategy_start (D m) "open" "closed" (Or.inl rfl) (Or.inr rfl) [] [.atom "term", e₂]
    simp only [List.length_nil, List.length_cons, String.reduceEq, false_and, ite_false, true_and] at st
    rw [index_nil_left] at st
    refine ⟨_, ?_, fx', fun ρ _ => by simp [denO_top]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2», litN, Term.list, compareExact_tuple, List.compareLex_cons_cons] at st ⊢
    simp [st, endSt]
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₂ c₂ u₂ d₂ fy' fx' (Or.inl ⟨k₁, rfl⟩)
    refine ⟨r, ?_, fr, fun ρ hρ => by rw [sr ρ hρ, Bool.or_comm]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [leaf_guard, node_ne3, ite_false]
    exact hr
  · have same : ¬compareExact (fuel (.tuple #[.integer k₂, .atom "open", .nil]) (litN e₁ (keyOf t))) (.tuple #[.integer k₂, .atom "open", .nil]) (litN e₁ (keyOf t)) = .eq := by
      simp [litN, Term.list, compareExact_tuple, List.compareLex_cons_cons]
    have st := strategy_start (D m) "closed" "open" (Or.inr rfl) (Or.inl rfl) [.atom "term", e₁] []
    simp only [List.length_nil, List.length_cons, String.reduceEq, false_and, ite_false, true_and] at st
    rw [index_nil_right] at st
    refine ⟨_, ?_, fy', fun ρ _ => by simp [denO_top]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp [Erlang.erlang.«=:=/2», litN, Term.list, compareExact_tuple, List.compareLex_cons_cons] at st ⊢
    simp [st, endSt]
  · have same := pureLit_exact ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
    refine ⟨_, ?_, fx', fun ρ hρ => by rw [denO_congr pureLit_not fy' fx' (compare_eq_of_compareExact_eq _ _ same) hρ,
      Bool.or_self]⟩
    have same' := same
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [litN, Term.list] at same' ⊢
    simp only [leaf_guard, ite_eq_left same']
    rfl
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₂ c₂ u₂ d₂ fy' fx' (Or.inr ⟨e₁, h₁, rfl⟩)
    refine ⟨r, ?_, fr, fun ρ hρ => by rw [sr ρ hρ, Bool.or_comm]⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [leaf_guard, node_ne3, ite_false, litN, Term.list]
    exact hr
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₁ c₁ u₁ d₁ fx' fy' (Or.inl ⟨k₂, rfl⟩)
    refine ⟨r, ?_, fr, sr⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only []
    exact hr
  · obtain ⟨r, hr, fr, sr⟩ := pure_union_leaf m h₁ c₁ u₁ d₁ fx' fy' (Or.inr ⟨e₂, h₂, rfl⟩)
    refine ⟨r, ?_, fr, sr⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_union/2»
    simp only [litN, Term.list]
    exact hr

theorem pure_lh_bound {x y w : Term} (fx : OField (PureLit t) x) (fy : OField (PureLit t) y) (fw : OField (PureLit t) w)
    (tops : (∃ k, x = .tuple #[.integer k, .atom "open", .nil]) → (∃ k, y = .tuple #[.integer k, .atom "open", .nil]) →
      lh w = 0) : lh w ≤ max (lh x) (lh y) := by
  by_cases tx : ∃ k, x = .tuple #[.integer k, .atom "open", .nil]
  · by_cases ty : ∃ k, y = .tuple #[.integer k, .atom "open", .nil]
    · rw [tops tx ty]; omega
    · have := pure_one fy fun k h => ty ⟨k, h⟩
      have := pure_le fw
      omega
  · have := pure_one fx fun k h => tx ⟨k, h⟩
    have := pure_le fw
    omega

theorem pure_nz {w : Term} (fw : OField (PureLit t) w) : w ≠ .integer 0 := by
  rcases fw with ⟨k, rfl⟩ | ww
  · simp
  · exact bdd_ne_zero ww

/-- Tuple fields of expansion literals of the node `t`, at the bottom level. -/
theorem pureKind {K : Nat} (hK : 10 ≤ K) : KindOk K "tuple" (OField (PureLit t)) Resp where
  resp := fun _ h => h
  wit := ⟨_, resp_const Bool.true⟩
  top := fun t' ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ | ⟨h, _⟩ <;> try simp at h
    exact ⟨Or.inl ⟨_, rfl⟩, lh_top_leaf _, fun p _ => by rw [dn_tuple, denO_top]⟩
  congr := fun fx fx' e p hp => by
    rw [dn_tuple, dn_tuple]
    exact denO_congr pureLit_not fx fx' e hp
  union := fun {x y} fx fy => by
    obtain ⟨w, run, fw, sem⟩ := pure_union fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], fw,
      fun p hp => by rw [dn_tuple, dn_tuple, dn_tuple, sem _ hp], pure_lh_bound fx fy fw fun ⟨k, ex⟩ _ => ?_⟩
    subst ex
    rw [tuple_union_shape.1] at run
    cases run
    exact lh_top_leaf _
  inter := fun {x y} fx fy => by
    obtain ⟨w, run, k, d⟩ := open_inter_spec pureLit_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
      tuple_inter_shape.2.2 (.atom "tuple") fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run],
      fun kw => ⟨(k kw).1, pure_lh_bound fx fy (k kw).1 fun ⟨k₁, ex⟩ ⟨k₂, ey⟩ => ?_⟩, fun p hp => ?_⟩
    · subst ex ey
      rw [tuple_inter_shape.1] at run
      cases run
      exact lh_top_leaf _
    · cases kk : kept (.atom "tuple", w)
      · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, d kk _ hp]
      · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, (k kk).2 _ hp]
  diff := fun {x y} fx fy => by
    obtain ⟨w, run, fw, sem⟩ := pure_diff_sem fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run],
      fun kw => ⟨fw, pure_lh_bound fx fy fw fun ⟨k₁, ex⟩ ⟨k₂, ey⟩ => ?_⟩, fun p hp => ?_⟩
    · subst ex ey
      have : w = .atom "bdd_bot" := by
        unfold Elixir.Module.Types.Descr.«tuple_difference/2» at run
        simp at run
        exact run.symm
      subst this
      simp [kept] at kw
    · cases kk : kept (.atom "tuple", w)
      · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, ← sem _ hp,
          dropped_bdd (by rw [kept_name]; exact kk) (pure_nz fw)]
        simp [denO, isOpenTop]
      · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, sem _ hp]
  opt_union := fun {x y} S {m} fx fy hm => by
    obtain ⟨w, run, fw, sem⟩ := pure_opt_union m fx fy
    exact ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_union/4»] using run, fw,
      fun p hp => by rw [dn_tuple, dn_tuple, dn_tuple, sem _ hp]⟩
  opt_inter := fun {x y} S {m} fx fy hm => by
    obtain ⟨w, run, fw, sem⟩ := pure_opt_inter (d := D m) fx fy (.map S)
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_intersection/4»] using run, fun _ => fw, fun p hp => ?_⟩
    cases kk : kept (.atom "tuple", w)
    · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, ← sem _ hp,
        dropped_bdd (by rw [kept_name]; exact kk) (pure_nz fw)]
      simp [denO, isOpenTop]
    · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, sem _ hp]
  opt_diff := fun {x y} S {m} fx fy hm => by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    obtain ⟨w, run, fw, sem⟩ := pure_opt_diff (n := n) (by omega) fx fy
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_difference/4»] using run, fun _ => fw, fun p hp => ?_⟩
    cases kk : kept (.atom "tuple", w)
    · rw [keptO_false kk, dn_none, dn_tuple, dn_tuple, ← sem _ hp,
        dropped_bdd (by rw [kept_name]; exact kk) (pure_nz fw)]
      simp [denO, isOpenTop]
    · rw [keptO_true kk, dn_tuple, dn_tuple, dn_tuple, sem _ hp]
  empty := fun {x} S fx => by
    obtain ⟨b, run⟩ := pure_tuple_empty fx S
    refine ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m (by omega),
      fun N hx hS => ?_⟩
    have v := pure_empty_val fx (not_seen hS hx "tuple") (safeN_noid hS _) (m := 2) (by omega)
    rw [run 2 (by omega)] at v
    have hb : b = (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)) := by
      cases b <;> cases h : (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)) <;> simp_all [boolAtom]
    subst hb
    constructor
    · intro h p hp
      rw [dn_tuple]
      obtain ⟨c, hc⟩ := pure_val fx hp
      rw [hc]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      cases c
      · exact h.2
      · exact h.1
    · intro h
      have h₁ := h (0, .nil, fun _ => Bool.true) (resp_const _)
      have h₂ := h (0, .nil, fun _ => Bool.false) (resp_const _)
      rw [dn_tuple] at h₁ h₂
      simp [h₁, h₂]

end

/-- The kinds of the bottom level. -/
theorem kinds0 (t : Term) {K : Nat} (hK : 10 ≤ K) :
    Kinds K (OField (PureLit t)) (FieldOk "list") (FieldOk "map") Resp Resp Resp :=
  ⟨pureKind hK, topKind "list" (Or.inl rfl) (by omega), topKind "map" (Or.inr rfl) (by omega)⟩

end Elixir.STTDescrProofsTest.Nest

/-! Function values of arity n are finite graphs of rows (x, y): each argument x_j is a value or the probe ★
(`none`), and the result y is a value or the error Ω (`none`). The row (★ⁿ, Ω) is not allowed, so the top
function of arity n is the arrow (none, …, none) → term. A function belongs to an arrow when every row whose
arguments are ★ or in the arrow's arguments returns a value in the arrow's return. -/

namespace Elixir.STTDescrProofsTest.FunSem

variable {V : Type}

abbrev Row (V : Type) := List (Option V) × Option V
abbrev Arrow (V : Type) := List (V → Prop) × (V → Prop)

/-- An argument or a result: a value of the set, or, when not flagged, ★ or Ω. -/
def Opt (flag : Bool) (a : V → Prop) : Option V → Prop
  | none => flag = false
  | some v => a v

/-- The arguments a row passes to an arrow: ★ or members of the arrow's argument types. -/
def InDom : List (V → Prop) → List (Option V) → Prop
  | [], [] => True
  | t :: ts, o :: os => Opt false t o ∧ InDom ts os
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- A row an arrow allows: when the arrow applies, the row returns a value of its return type. -/
def Allows (a : Arrow V) (r : Row V) : Prop :=
  InDom a.1 r.1 → ∃ y, r.2 = some y ∧ a.2 y

/-- The flagged arguments of `phi`: each one is a value of its set, or ★ when not flagged. -/
def Args : List (Bool × (V → Prop)) → List (Option V) → Prop
  | [], [] => True
  | (b, a) :: as, o :: os => Opt b a o ∧ Args as os
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- No row with these arguments and result is allowed by all the arrows. -/
def NoRow (args : List (Bool × (V → Prop))) (ret : Bool × (V → Prop)) (P : List (Arrow V)) : Prop :=
  ∀ x y, Args args x → Opt ret.1 ret.2 y → ¬∀ p ∈ P, Allows p (x, y)

/-- The arguments of the recursive calls that skip an arrow through each of its arguments. -/
def Skips : List (V → Prop) → List (Bool × (V → Prop)) → List (List (Bool × (V → Prop)))
  | u :: us, (b, a) :: as => ((true, fun v => a v ∧ ¬u v) :: as) :: (Skips us as).map ((b, a) :: ·)
  | [], _ => []
  | _ :: _, [] => []

/-- The `phi` recursion over sets, without its shortcuts. -/
def phiS (args : List (Bool × (V → Prop))) (ret : Bool × (V → Prop)) : List (Arrow V) → Prop
  | [] => (∃ p ∈ args, p.1 = true ∧ ∀ v, ¬p.2 v) ∨ (ret.1 = true ∧ ∀ v, ¬ret.2 v)
  | (us, s) :: P => phiS args (true, fun v => ret.2 v ∧ s v) P ∧ ∀ a ∈ Skips us args, phiS a ret P

theorem opt_exists (b : Bool) (a : V → Prop) : (∃ o, Opt b a o) ↔ (b = true → ∃ v, a v) := by
  constructor
  · rintro ⟨o, h⟩ hb
    cases o with
    | none => simp [Opt] at h; simp_all
    | some v => exact ⟨v, h⟩
  · intro h
    cases b
    · exact ⟨none, rfl⟩
    · obtain ⟨v, hv⟩ := h rfl; exact ⟨some v, hv⟩

theorem args_exists : ∀ (args : List (Bool × (V → Prop))),
    (∃ x, Args args x) ↔ ∀ p ∈ args, p.1 = true → ∃ v, p.2 v
  | [] => ⟨fun _ => by simp, fun _ => ⟨[], trivial⟩⟩
  | (b, a) :: as => by
    constructor
    · rintro ⟨x, h⟩
      cases x with
      | nil => cases h
      | cons o os =>
        obtain ⟨ho, hs⟩ := h
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact (opt_exists b a).mp ⟨o, ho⟩
        · exact (args_exists as).mp ⟨os, hs⟩ p hp
    · intro h
      obtain ⟨o, ho⟩ := (opt_exists b a).mpr (h (b, a) (by simp))
      obtain ⟨os, hs⟩ := (args_exists as).mpr fun p hp => h p (by simp [hp])
      exact ⟨o :: os, ho, hs⟩

/-- Arguments outside an arrow's domain are those of a call that skips the arrow through one argument. -/
theorem args_skips : ∀ (us : List (V → Prop)) (args : List (Bool × (V → Prop))) (x : List (Option V)),
    us.length = args.length → ((Args args x ∧ ¬InDom us x) ↔ ∃ a ∈ Skips us args, Args a x)
  | [], [], x, _ => by
    cases x <;> simp [Args, InDom, Skips]
  | u :: us, (b, a) :: as, x, len => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at len
    cases x with
    | nil => simp [Args, Skips]
    | cons o os =>
      have ih := args_skips us as os len
      simp only [Args, InDom, Skips, List.mem_cons, List.mem_map]
      constructor
      · rintro ⟨⟨ho, hs⟩, hn⟩
        by_cases hu : Opt false u o
        · have : ¬InDom us os := fun h => hn ⟨hu, h⟩
          obtain ⟨a', ma, ha⟩ := ih.mp ⟨hs, this⟩
          exact ⟨_, Or.inr ⟨a', ma, rfl⟩, ho, ha⟩
        · cases o with
          | none => exact absurd rfl hu
          | some v => exact ⟨_, Or.inl rfl, ⟨ho, hu⟩, hs⟩
      · rintro ⟨a', ha' | ⟨a'', ma, rfl⟩, hx⟩
        · subst ha'
          obtain ⟨ho, hs⟩ := hx
          cases o with
          | none => cases ho
          | some v => exact ⟨⟨ho.1, hs⟩, fun h => ho.2 h.1⟩
        · obtain ⟨ho, hs⟩ := hx
          obtain ⟨hs', hn⟩ := ih.mpr ⟨a'', ma, hs⟩
          exact ⟨⟨ho, hs'⟩, fun h => hn h.2⟩
  | [], _ :: _, _, len => by simp at len
  | _ :: _, [], _, len => by simp at len

theorem skips_length : ∀ (us : List (V → Prop)) (args : List (Bool × (V → Prop))), ∀ a ∈ Skips us args,
    a.length = args.length
  | u :: us, (b, a) :: as, a', ma => by
    simp only [Skips, List.mem_cons, List.mem_map] at ma
    rcases ma with rfl | ⟨a'', ma, rfl⟩
    · rfl
    · simp [skips_length us as a'' ma]
  | [], _, _, ma => by simp [Skips] at ma
  | _ :: _, [], _, ma => by simp [Skips] at ma

/-- `phi` holds exactly when no row with its arguments and result is allowed by all the arrows. -/
theorem phiS_iff (args : List (Bool × (V → Prop))) (ret : Bool × (V → Prop)) (P : List (Arrow V))
    (len : ∀ p ∈ P, p.1.length = args.length) : phiS args ret P ↔ NoRow args ret P := by
  induction P generalizing args ret with
  | nil =>
    simp only [phiS, NoRow, List.not_mem_nil, false_implies, implies_true, not_true_eq_false, imp_false]
    constructor
    · rintro (⟨p, mp, hb, he⟩ | ⟨hb, he⟩) x y hx hy
      · obtain ⟨v, hv⟩ := (args_exists args).mp ⟨x, hx⟩ p mp hb
        exact he v hv
      · obtain ⟨v, hv⟩ := (opt_exists ret.1 ret.2).mp ⟨y, hy⟩ hb
        exact he v hv
    · intro h
      apply Classical.byContradiction
      intro hn
      simp only [not_or, not_exists, not_and, Classical.not_forall, Classical.not_not] at hn
      obtain ⟨x, hx⟩ := (args_exists args).mpr fun p mp hb => by
        obtain ⟨v, hv⟩ := hn.1 p mp hb; exact ⟨v, hv⟩
      obtain ⟨y, hy⟩ := (opt_exists ret.1 ret.2).mpr fun hb => by
        obtain ⟨v, hv⟩ := hn.2 hb; exact ⟨v, hv⟩
      exact h x y hx hy
  | cons p P ih =>
    obtain ⟨us, s⟩ := p
    have lu : us.length = args.length := len (us, s) (by simp)
    have lP : ∀ p ∈ P, p.1.length = args.length := fun p mp => len p (by simp [mp])
    simp only [phiS]
    rw [ih args _ lP]
    have skips : (∀ a ∈ Skips us args, phiS a ret P) ↔ ∀ a ∈ Skips us args, NoRow a ret P := by
      refine forall₂_congr fun a ma => ih a ret fun p mp => ?_
      rw [skips_length us args a ma]; exact lP p mp
    rw [skips]
    constructor
    · rintro ⟨hu, hs⟩ x y hx hy hall
      by_cases hd : InDom us x
      · obtain ⟨v, rfl, hv⟩ := hall (us, s) (by simp) hd
        exact hu x (some v) hx ⟨hy, hv⟩ fun p mp => hall p (by simp [mp])
      · obtain ⟨a, ma, ha⟩ := (args_skips us args x lu).mp ⟨hx, hd⟩
        exact hs a ma x y ha hy fun p mp => hall p (by simp [mp])
    · intro h
      refine ⟨fun x y hx hy hall => ?_, fun a ma x y ha hy hall => ?_⟩
      · cases y with
        | none => cases hy
        | some v =>
          refine h x (some v) hx hy.1 fun p mp => ?_
          rcases List.mem_cons.mp mp with rfl | mp
          · exact fun _ => ⟨v, rfl, hy.2⟩
          · exact hall p mp
      · have hx := (args_skips us args x lu).mpr ⟨a, ma, ha⟩
        refine h x y hx.1 hy fun p mp => ?_
        rcases List.mem_cons.mp mp with rfl | mp
        · exact fun hd => absurd hd hx.2
        · exact hall p mp

/-! Functions and lines of arrows. -/

/-- Rows of a function of arity n: n arguments, and never the probe input with the error. -/
def ValidRow (n : Nat) (r : Row V) : Prop :=
  r.1.length = n ∧ ¬(r.1 = List.replicate n none ∧ r.2 = none)

/-- A line of arrows is empty when every function of arity n in its positive arrows is in one of its negative ones. -/
def LineEmpty (n : Nat) (P N : List (Arrow V)) : Prop :=
  ∀ g : List (Row V), (∀ r ∈ g, ValidRow n r) → (∀ p ∈ P, ∀ r ∈ g, Allows p r) → ∃ q ∈ N, ∀ r ∈ g, Allows q r

/-- The rows the positive arrows allow, one per negative arrow, that this negative arrow does not allow. -/
theorem witness_rows (n : Nat) (P : List (Arrow V)) : ∀ N : List (Arrow V),
    (∀ q ∈ N, ∃ r, ValidRow n r ∧ (∀ p ∈ P, Allows p r) ∧ ¬Allows q r) →
    ∃ g : List (Row V), (∀ r ∈ g, ValidRow n r ∧ ∀ p ∈ P, Allows p r) ∧ ∀ q ∈ N, ∃ r ∈ g, ¬Allows q r
  | [], _ => ⟨[], by simp, by simp⟩
  | q :: N, h => by
    obtain ⟨r, vr, ar, nr⟩ := h q (by simp)
    obtain ⟨g, hg, ng⟩ := witness_rows n P N fun q' mq => h q' (by simp [mq])
    refine ⟨r :: g, fun r' mr => ?_, fun q' mq => ?_⟩
    · rcases List.mem_cons.mp mr with rfl | mr
      · exact ⟨vr, ar⟩
      · exact hg r' mr
    · rcases List.mem_cons.mp mq with rfl | mq
      · exact ⟨r, by simp, nr⟩
      · obtain ⟨r', mr, nr'⟩ := ng q' mq; exact ⟨r', by simp [mr], nr'⟩

/-- A line is empty exactly when one negative arrow contains the positive arrows on every row. -/
theorem lineEmpty_iff (n : Nat) (P N : List (Arrow V)) :
    LineEmpty n P N ↔ ∃ q ∈ N, ∀ r, ValidRow n r → (∀ p ∈ P, Allows p r) → Allows q r := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    simp only [not_exists, not_and, Classical.not_forall] at hn
    obtain ⟨g, hg, ng⟩ := witness_rows n P N fun q mq => by
      obtain ⟨r, hr⟩ := hn q mq
      exact ⟨r, hr.1, hr.2.1, hr.2.2⟩
    obtain ⟨q, mq, hq⟩ := h g (fun r mr => (hg r mr).1) (fun p mp r mr => (hg r mr).2 p mp)
    obtain ⟨r, mr, nr⟩ := ng q mq
    exact nr (hq r mr)
  · rintro ⟨q, mq, hq⟩ g vg pg
    exact ⟨q, mq, fun r mr => hq r (vg r mr) fun p mp => pg p mp r mr⟩

theorem inDom_args : ∀ (ts : List (V → Prop)) (x : List (Option V)), InDom ts x ↔ Args (ts.map (false, ·)) x
  | [], [] => Iff.rfl
  | t :: ts, o :: os => by simp only [InDom, List.map, Args, inDom_args ts os]
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl

theorem inDom_probe : ∀ (ts : List (V → Prop)), InDom ts (List.replicate ts.length none)
  | [] => trivial
  | _ :: ts => ⟨rfl, inDom_probe ts⟩

theorem inDom_length : ∀ {ts : List (V → Prop)} {x : List (Option V)}, InDom ts x → x.length = ts.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [inDom_length h.2]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- With some positive arrow of arity n, a negative arrow contains them on every row exactly when `phi` holds,
starting from its arguments and the complement of its return. -/
theorem neg_iff_phi (n : Nat) (P : List (Arrow V)) (ne : P ≠ []) (lP : ∀ p ∈ P, p.1.length = n)
    (t : List (V → Prop)) (s : V → Prop) (lt : t.length = n) :
    (∀ r, ValidRow n r → (∀ p ∈ P, Allows p r) → Allows (t, s) r) ↔
      phiS (t.map (false, ·)) (false, fun v => ¬s v) P := by
  rw [phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [lt])]
  constructor
  · intro h x y hx hy hall
    have hd : InDom t x := (inDom_args t x).mpr hx
    have lx : x.length = n := by rw [inDom_length hd, lt]
    have valid : ValidRow n (x, y) := by
      refine ⟨lx, fun ⟨ex, ey⟩ => ?_⟩
      dsimp only at ex ey
      obtain ⟨p, mp⟩ := List.exists_mem_of_ne_nil P ne
      have : InDom p.1 x := by rw [ex, ← lP p mp]; exact inDom_probe p.1
      obtain ⟨v, hv, -⟩ := hall p mp this
      rw [ey] at hv; cases hv
    obtain ⟨v, rfl, hv⟩ := h (x, y) valid hall hd
    exact hy hv
  · intro h r vr hall hd
    apply Classical.byContradiction
    intro hn
    refine h r.1 r.2 ((inDom_args t r.1).mp hd) ?_ hall
    cases hr : r.2 with
    | none => rfl
    | some v => exact fun hv => hn ⟨v, hr, hv⟩

/-- The top arrow of arity n allows every row of a function of arity n. -/
def top (n : Nat) : Arrow V := (List.replicate n (fun _ => False), fun _ => True)

theorem inDom_none : ∀ (n : Nat) (x : List (Option V)), InDom (List.replicate n (fun _ : V => False)) x →
    x = List.replicate n none
  | 0, [], _ => rfl
  | n + 1, o :: os, h => by
    obtain ⟨ho, hs⟩ := h
    cases o with
    | none => simp [inDom_none n os hs, List.replicate_succ]
    | some v => exact ho.elim
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h

theorem allows_top {n : Nat} {r : Row V} (vr : ValidRow n r) : Allows (top n) r := by
  intro hd
  have ex := inDom_none n r.1 hd
  cases hr : r.2 with
  | none => exact absurd ⟨ex, hr⟩ vr.2
  | some v => exact ⟨v, rfl, trivial⟩

/-- Lines without positive arrows are the lines with the top arrow as their only positive one. -/
theorem lineEmpty_top (n : Nat) (N : List (Arrow V)) : LineEmpty n [] N ↔ LineEmpty n [top n] N := by
  rw [lineEmpty_iff, lineEmpty_iff]
  refine exists_congr fun q => and_congr_right fun _ => forall_congr' fun r => ?_
  constructor
  · intro h vr _; exact h vr (by simp)
  · intro h vr _; exact h vr fun p mp => by simp at mp; subst mp; exact allows_top vr

theorem lineEmpty_nil (n : Nat) : ¬LineEmpty n ([] : List (Arrow V)) [] := by
  intro h
  obtain ⟨q, mq, -⟩ := h [] (by simp) (by simp)
  cases mq

end Elixir.STTDescrProofsTest.FunSem

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Lists of terms: positions and replacements. -/

theorem nth1_cons {k : Int} (hk : k ≠ 1) (h t : Term) :
    Erlang.lists.«nth_1/2» (.integer k) (.cons h t) = Erlang.lists.«nth_1/2» (.integer (k - 1)) t := by
  conv => lhs; rw [Erlang.lists.«nth_1/2».eq_def]
  split
  · rename_i h₁ _; simp only [Term.integer.injEq] at h₁; omega
  · rename_i h₁ _; simp only [Term.cons.injEq] at h₁; obtain ⟨rfl, rfl⟩ := h₁; simp
  · exfalso; simp_all

theorem nth1_list : ∀ (xs : List Term) (j : Nat) (h : j < xs.length),
    Erlang.lists.«nth_1/2» (.integer ((j : Int) + 1)) (Term.list xs) = .ok xs[j]
  | x :: xs, 0, _ => by
    rw [Erlang.lists.«nth_1/2».eq_def]; rfl
  | x :: xs, j + 1, h => by
    have ih := nth1_list xs j (by simp at h; omega)
    rw [show Term.list (x :: xs) = .cons x (Term.list xs) from rfl, nth1_cons (by omega)]
    rw [show ((j + 1 : Nat) : Int) + 1 - 1 = (j : Int) + 1 by omega]
    exact ih

theorem nth_list (xs : List Term) (j : Nat) (h : j < xs.length) :
    Erlang.lists.«nth/2» (.integer ((j : Int) + 1)) (Term.list xs) = .ok xs[j] := by
  match xs, j, h with
  | x :: xs, 0, _ => rfl
  | x :: xs, j + 1, h =>
    have := nth1_list (x :: xs) (j + 1) h
    unfold Erlang.lists.«nth/2»
    split
    · rename_i h₁ _; simp only [Term.integer.injEq] at h₁; omega
    · have gt : ((j + 1 : Nat) : Int) + 1 > 1 := by omega
      have c : Ord.compare ((j : Int) + 1 + 1) 1 = Ordering.gt := by
        first
          | exact Int.compare_eq_gt.mpr (by omega)
          | (simp only [compare, compareOfLessAndEq]; split <;> first | omega | (split <;> first | rfl | omega))
      simp [Term.list, Erlang.erlang.«>/2», Erlang.erlang.«and/2», c] at this ⊢
      exact this

theorem replace_cons {k : Int} (hk : k ≠ 0) (h t v : Term) :
    Elixir.List.«do_replace_at/3» (.cons h t) (.integer k) v = (do
      let r ← Elixir.List.«do_replace_at/3» t (.integer (k - 1)) v
      pure (.cons h r)) := by
  conv => lhs; rw [Elixir.List.«do_replace_at/3».eq_def]
  split
  · rename_i h₁; simp at h₁
  · rename_i h₁; simp only [Term.integer.injEq] at h₁; omega
  · rename_i heq _; simp only [Term.cons.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
    rw [Erlang.erlang.«-/2_integers», Lynx.Except.ok_bind]
  · exfalso; simp_all

theorem do_replace_list : ∀ (xs : List Term) (j : Nat) (v : Term), j < xs.length →
    Elixir.List.«do_replace_at/3» (Term.list xs) (.integer j) v = .ok (Term.list (xs.set j v))
  | x :: xs, 0, v, _ => by rw [Elixir.List.«do_replace_at/3».eq_def]; rfl
  | x :: xs, j + 1, v, h => by
    have ih := do_replace_list xs j v (by simp at h; omega)
    rw [show Term.list (x :: xs) = .cons x (Term.list xs) from rfl, replace_cons (by omega)]
    rw [show ((j + 1 : Nat) : Int) - 1 = (j : Int) by omega, ih]
    rfl

theorem replace_list (xs : List Term) (j : Nat) (v : Term) (h : j < xs.length) :
    Elixir.List.«replace_at/3» (Term.list xs) (.integer j) v = .ok (Term.list (xs.set j v)) := by
  have c : Ord.compare (j : Int) 0 ≠ Ordering.lt := by
    first
      | exact fun e => absurd (Int.compare_eq_lt.mp e) (by omega)
      | (simp only [compare, compareOfLessAndEq]; split <;> first | omega | (split <;> simp))
  have run := do_replace_list xs j v h
  unfold Elixir.List.«replace_at/3»
  cases xs with
  | nil => simp at h
  | cons x xs =>
    simp [Erlang.erlang.«is_list/1», Erlang.erlang.«is_integer/1», Erlang.erlang.«</2», c,
      Term.list, Lynx.Except.andAlso] at run ⊢
    exact run

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The terms `phi/5` works on, and the sets they stand for. -/

section
variable {V : Type} (den : Term → V → Prop)

/-- Flagged arguments, as `phi/5` keeps them: a list of `{flag, type}`. -/
def encA (args : List (Bool × Term)) : Term := Term.list (args.map fun p => .tuple #[boolAtom p.1, p.2])

/-- The flagged return, `{flag, type}`. -/
def encR (r : Bool × Term) : Term := .tuple #[boolAtom r.1, r.2]

/-- Positive arrows, as BDD leaves `{key, arguments, return}`. -/
def encP (P : List (Term × List Term × Term)) : Term :=
  Term.list (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2])

def semA (args : List (Bool × Term)) : List (Bool × (V → Prop)) := args.map fun p => (p.1, den p.2)
def semR (r : Bool × Term) : Bool × (V → Prop) := (r.1, den r.2)
def semP (P : List (Term × List Term × Term)) : List (FunSem.Arrow V) := P.map fun p => (p.2.1.map den, den p.2.2)

end

/-- Lists whose elements are equal by comparison, pairwise. -/
inductive CmpEq : List Term → List Term → Prop
  | nil : CmpEq [] []
  | cons {a b : Term} {as bs : List Term} : Term.compare (Term.fuel a b) a b = .eq → CmpEq as bs → CmpEq (a :: as) (b :: bs)

theorem list_cmp : ∀ (xs ys : List Term), Term.compare (Term.fuel (Term.list xs) (Term.list ys)) (Term.list xs) (Term.list ys) = .eq → CmpEq xs ys
  | [], [], _ => .nil
  | x :: xs, ys, e => by
    obtain ⟨y, ys', h, ex, es⟩ := cons_cmp e
    cases ys with
    | nil => simp [Term.list] at h
    | cons y' ys =>
      simp only [Term.list, Term.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .cons ex (list_cmp xs ys es)
  | [], y :: ys, e => by
    have := (nil_compare_eq (Term.list (y :: ys))).mp e
    simp [Term.list] at this

theorem boolAtom_cmp {b b' : Bool} (e : Term.compare (Term.fuel (boolAtom b) (boolAtom b')) (boolAtom b) (boolAtom b') = .eq) : b = b' := by
  have := atom_cmp e
  cases b <;> cases b' <;> simp_all [boolAtom]

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- Element types equal by comparison stand for the same set. -/
def DenCongr (E : Term → Prop) (den : Term → V → Prop) : Prop :=
  ∀ {a a'}, E a → E a' → Term.compare (Term.fuel a a') a a' = .eq → den a = den a'

theorem semA_f2 (cg : DenCongr E den) : ∀ {args args' : List (Bool × Term)}, (∀ p ∈ args, E p.2) →
    (∀ p ∈ args', E p.2) →
    CmpEq (args.map fun p => .tuple #[boolAtom p.1, p.2]) (args'.map fun p => .tuple #[boolAtom p.1, p.2]) →
      semA den args = semA den args'
  | [], [], _, _, _ => rfl
  | p :: args, p' :: args', h, h', f => by
    simp only [List.map] at f
    obtain _ | ⟨e₀, f⟩ := f
    obtain ⟨eb, ea⟩ := tuple2_cmp e₀
    have tail := semA_f2 cg (fun q mq => h q (by simp [mq])) (fun q mq => h' q (by simp [mq])) f
    simp only [semA, List.map_cons] at tail ⊢
    rw [boolAtom_cmp eb, cg (h p (by simp)) (h' p' (by simp)) ea, tail]
  | [], _ :: _, _, _, f => by simp only [List.map] at f; cases f
  | _ :: _, [], _, _, f => by simp only [List.map] at f; cases f

theorem semA_cmp (cg : DenCongr E den) {args args' : List (Bool × Term)} (h : ∀ p ∈ args, E p.2)
    (h' : ∀ p ∈ args', E p.2) (e : Term.compare (Term.fuel (encA args) (encA args')) (encA args) (encA args') = .eq) : semA den args = semA den args' :=
  semA_f2 cg h h' (list_cmp _ _ e)

theorem map_den_f2 (cg : DenCongr E den) : ∀ {us us' : List Term}, (∀ u ∈ us, E u) → (∀ u ∈ us', E u) →
    CmpEq us us' → us.map den = us'.map den
  | [], [], _, _, _ => rfl
  | u :: us, u' :: us', h, h', .cons e f => by
    simp only [List.map_cons]
    rw [cg (h u (by simp)) (h' u' (by simp)) e,
      map_den_f2 cg (fun q mq => h q (by simp [mq])) (fun q mq => h' q (by simp [mq])) f]

theorem semP_f2 (cg : DenCongr E den) : ∀ {P P' : List (Term × List Term × Term)},
    (∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2) → (∀ p ∈ P', (∀ u ∈ p.2.1, E u) ∧ E p.2.2) →
    CmpEq (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (P'.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) →
      semP den P = semP den P'
  | [], [], _, _, _ => rfl
  | p :: P, p' :: P', h, h', f => by
    simp only [List.map] at f
    obtain _ | ⟨e₀, f⟩ := f
    obtain ⟨b₀, b₁, b₂, eq, -, e₁, e₂⟩ := tuple3_cmp e₀
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eq
    obtain ⟨-, rfl, rfl, -⟩ := eq
    have tail := semP_f2 cg (fun q mq => h q (by simp [mq])) (fun q mq => h' q (by simp [mq])) f
    simp only [semP, List.map_cons] at tail ⊢
    rw [map_den_f2 cg (h p (by simp)).1 (h' p' (by simp)).1 (list_cmp _ _ e₁),
      cg (h p (by simp)).2 (h' p' (by simp)).2 e₂, tail]
  | [], _ :: _, _, _, f => by simp only [List.map] at f; cases f
  | _ :: _, [], _, _, f => by simp only [List.map] at f; cases f

theorem semP_cmp (cg : DenCongr E den) {P P' : List (Term × List Term × Term)}
    (h : ∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2) (h' : ∀ p ∈ P', (∀ u ∈ p.2.1, E u) ∧ E p.2.2)
    (e : Term.compare (Term.fuel (encP P) (encP P')) (encP P) (encP P') = .eq) : semP den P = semP den P' :=
  semP_f2 cg h h' (list_cmp _ _ e)

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The cache of `phi/5` and the context it runs in. -/

section
variable {V : Type} (E : Term → Prop) (den : Term → V → Prop)

/-- Whether a set is empty, as a Boolean. -/
noncomputable def isEmpty (a : Term) : Bool := @decide (∀ v, ¬den a v) (Classical.propDecidable _)

theorem isEmpty_iff (a : Term) : isEmpty den a = Bool.true ↔ ∀ v, ¬den a v := by
  simp [isEmpty]

/-- Element types, closed under the operations `phi/5` performs, whose emptiness is decided under `seen`,
from call depth `K`. -/
structure PhiCtx (K : Nat) (seen : Term) : Prop where
  inter : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
    ∀ v, den c v ↔ den a v ∧ den b v
  diff : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
    ∀ v, den c v ↔ den a v ∧ ¬den b v
  empty : ∀ {a}, E a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a seen = .ok (boolAtom (isEmpty den a))
  congr : DenCongr E den

/-- Arguments, return, and positive arrows of arity `n`, of element types. -/
def PhiOk (n : Nat) (args : List (Bool × Term)) (ret : Bool × Term) (P : List (Term × List Term × Term)) : Prop :=
  (∀ p ∈ args, E p.2) ∧ args.length = n ∧ E ret.2 ∧ ∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2 ∧ p.2.1.length = n

/-- Cached answers of `phi/5` are its answers. -/
def CacheOk (n : Nat) (cache : Term) : Prop :=
  ∃ M, cache = .map M ∧ ∀ e ∈ M, ∃ args ret P b, PhiOk E n args ret P ∧
    e.1 = .tuple #[encA args, encR ret, encP P] ∧ e.2 = boolAtom b ∧
    (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P))

theorem cacheOk_nil (n : Nat) : CacheOk E den n (.map []) := ⟨[], rfl, by simp⟩

end

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n : Nat}

theorem semR_cmp (cg : DenCongr E den) {r r' : Bool × Term} (h : E r.2) (h' : E r'.2)
    (e : Term.compare (Term.fuel (encR r) (encR r')) (encR r) (encR r') = .eq) : semR den r = semR den r' := by
  obtain ⟨eb, ea⟩ := tuple2_cmp e
  simp only [semR, boolAtom_cmp eb, cg h h' ea]

/-- Storing an answer keeps the cache correct. -/
theorem cache_put {cache : Term} (ok : CacheOk E den n cache) {args : List (Bool × Term)} {ret : Bool × Term}
    {P : List (Term × List Term × Term)} (v : PhiOk E n args ret P) {b : Bool}
    (sem : b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P)) :
    ∃ c, Erlang.maps.«put/3» (.tuple #[encA args, encR ret, encP P]) (boolAtom b) cache = .ok c ∧ CacheOk E den n c := by
  obtain ⟨M, rfl, hM⟩ := ok
  refine ⟨_, rfl, _, rfl, fun e me => ?_⟩
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨args, ret, P, b, v, rfl, rfl, sem⟩
  · exact hM e me

/-- A cached answer is the answer. -/
theorem cache_get (cg : DenCongr E den) {cache : Term} (ok : CacheOk E den n cache) {args : List (Bool × Term)}
    {ret : Bool × Term} {P : List (Term × List Term × Term)} (v : PhiOk E n args ret P) {w : Term}
    (h : getMapKeys [.tuple #[encA args, encR ret, encP P]] cache = [w]) :
    ∃ b, w = boolAtom b ∧ (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P)) := by
  obtain ⟨M, rfl, hM⟩ := ok
  rw [getMapKeys_single] at h
  cases hl : mapLookup M (.tuple #[encA args, encR ret, encP P]) with
  | none => rw [hl] at h; cases h
  | some w' =>
    rw [hl] at h; simp at h; subst h
    simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at hl
    obtain ⟨e, he, rfl⟩ := hl
    have me := List.mem_of_find?_eq_some he
    have qe : compareExact (fuel (.tuple #[encA args, encR ret, encP P]) e.1) (.tuple #[encA args, encR ret, encP P]) e.1 = .eq := by simpa using List.find?_some he
    obtain ⟨args', ret', P', b, v', e1, e2, sem⟩ := hM e me
    rw [e1] at qe
    have ce := compare_eq_of_compareExact_eq _ _ qe
    obtain ⟨b₀, b₁, b₂, eq, c₀, c₁, c₂⟩ := tuple3_cmp ce
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eq
    obtain ⟨rfl, rfl, rfl, -⟩ := eq
    refine ⟨b, e2, ?_⟩
    rw [semA_cmp cg v.1 v'.1 c₀, semR_cmp cg v.2.2.1 v'.2.2.1 c₁,
      semP_cmp cg (fun p mp => ⟨(v.2.2.2 p mp).1, (v.2.2.2 p mp).2.1⟩)
        (fun p mp => ⟨(v'.2.2.2 p mp).1, (v'.2.2.2 p mp).2.1⟩) c₂]
    exact sem

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.FunSem
variable {V : Type}

/-- Skipping an arrow through argument `i`. -/
def skipAt (args : List (Bool × (V → Prop))) (i : Nat) (u : V → Prop) : List (Bool × (V → Prop)) :=
  args.set i (true, fun v => ((args[i]?.map Prod.snd).getD fun _ => False) v ∧ ¬u v)

theorem mem_skips : ∀ (us : List (V → Prop)) (args : List (Bool × (V → Prop))), us.length = args.length →
    ∀ a, a ∈ Skips us args ↔ ∃ i, ∃ h : i < us.length, a = skipAt args i us[i]
  | [], [], _, a => by simp [Skips]
  | u :: us, (b, x) :: as, len, a => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at len
    simp only [Skips, List.mem_cons, List.mem_map, mem_skips us as len]
    constructor
    · rintro (rfl | ⟨a', ⟨i, hi, rfl⟩, rfl⟩)
      · exact ⟨0, by simp, by simp [skipAt]⟩
      · exact ⟨i + 1, by simp; omega, by simp [skipAt]⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => left; simp [skipAt]
      | succ i =>
        have hi' : i < us.length := by simp at hi; omega
        right; exact ⟨skipAt as i us[i], ⟨i, hi', rfl⟩, by simp [skipAt]⟩
  | [], _ :: _, len, _ => by simp at len
  | _ :: _, [], len, _ => by simp at len

end Elixir.STTDescrProofsTest.FunSem

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

theorem any_congr_mem {α : Type} {f g : α → Bool} : ∀ (l : List α), (∀ p ∈ l, f p = g p) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a (by simp), any_congr_mem l fun p mp => h p (by simp [mp])]

theorem semA_set (args : List (Bool × Term)) (i : Nat) (p : Bool × Term) :
    semA den (args.set i p) = (semA den args).set i (p.1, den p.2) := by
  simp [semA, List.map_set]

/-- The answer of `phi/5` when no positive arrow is left. -/
theorem phi_base (ctx : PhiCtx E den K seen) {args : List (Bool × Term)} {ret : Bool × Term}
    (v : PhiOk E n args ret []) {cache : Term} (ok : CacheOk E den n cache) {m : Nat} (hm : K + 1 ≤ m) :
    ∃ b c, Elixir.Module.Types.Descr.«phi/5» (D m) (encA args) (encR ret) (encP []) cache seen =
        .ok (.tuple #[boolAtom b, c]) ∧
      (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den [])) ∧ CacheOk E den n c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨vA, vL, vR, -⟩ := v
  let res : Term → Bool := fun x => match x with
    | .tuple ⟨[.atom "true", a]⟩ => isEmpty den a
    | _ => Bool.false
  have hres : ∀ p ∈ args, res (.tuple #[boolAtom p.1, p.2]) = (p.1 && isEmpty den p.2) := by
    intro p _; cases p.1 <;> rfl
  have any := any_list (D (k + 1)) "Elixir.Module.Types.Descr" "-phi/5-fun-0-" #[seen] res
    (args.map fun p => .tuple #[boolAtom p.1, p.2]) (by
      intro x mx
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mx
      rw [Erlang.program.«Elixir.Module.Types.Descr:-phi/5-fun-0-/1».pure, hres p mp]
      have e := ctx.empty (vA p mp) k (by omega)
      cases hb : p.1 <;> simp [Elixir.Module.Types.Descr.«-phi/5-fun-0-/2», Lynx.Except.andAlso, boolAtom, e])
  have hany : (args.map fun p => Term.tuple #[boolAtom p.1, p.2]).any res =
      args.any (fun p => p.1 && isEmpty den p.2) := by
    rw [List.any_map]; exact any_congr_mem args fun p mp => hres p mp
  rw [hany] at any
  let r : Bool := args.any (fun p => p.1 && isEmpty den p.2) || (ret.1 && isEmpty den ret.2)
  have sem : r = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den []) := by
    simp only [r, semR, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, isEmpty_iff]
    constructor
    · rintro (⟨p, mp, hb, he⟩ | ⟨hb, he⟩)
      · exact Or.inl ⟨(p.1, den p.2), List.mem_map.mpr ⟨p, mp, rfl⟩, hb, he⟩
      · exact Or.inr ⟨hb, he⟩
    · rintro (⟨q, mq, hb, he⟩ | ⟨hb, he⟩)
      · obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mq
        exact Or.inl ⟨p, mp, hb, he⟩
      · exact Or.inr ⟨hb, he⟩
  obtain ⟨c, put, okc⟩ := cache_put ok ⟨vA, vL, vR, by simp⟩ sem
  refine ⟨r, c, ?_, sem, okc⟩
  have er := ctx.empty vR (k + 1) (by omega)
  have v11 : Lynx.Except.orElse (Erlang.lists.«any/2» (D (k + 1))
      (.function false "Elixir.Module.Types.Descr" "-phi/5-fun-0-" 1 #[seen]) (encA args))
      (Lynx.Except.andAlso (pure (boolAtom ret.1)) (Elixir.Module.Types.Descr.«empty_seen?/2» (D (k + 1)) ret.2 seen)
        Bool.true) Bool.true = .ok (boolAtom r) := by
    simp only [encA]; rw [any, er]; simp only [r]
    cases h1 : ret.1 <;> cases h2 : args.any (fun p => p.1 && isEmpty den p.2) <;>
      cases h3 : isEmpty den ret.2 <;> simp [Lynx.Except.orElse, Lynx.Except.andAlso, boolAtom]
  rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
  simp only [encR, encP, List.map_nil, Term.list]
  simp only [pure_bind, v11, Lynx.Except.ok_bind]
  rw [show Term.tuple ⟨[boolAtom ret.1, ret.2]⟩ = encR ret from rfl, show Term.nil = encP [] from rfl, put]
  rfl

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.FunSem
variable {V : Type}

theorem args_set_empty : ∀ (args : List (Bool × (V → Prop))) (j : Nat) (e : V → Prop) (x : List (Option V)),
    j < args.length → (∀ v, ¬e v) → ¬Args (args.set j (true, e)) x
  | (b, a) :: as, 0, e, o :: os, _, he, h => by
    obtain ⟨ho, -⟩ := h
    cases o with
    | none => cases ho
    | some v => exact he v ho
  | (b, a) :: as, j + 1, e, o :: os, hj, he, h =>
    args_set_empty as j e os (by simp at hj; omega) he h.2
  | (b, a) :: as, j, e, [], _, _, h => by
    cases j <;> simp [List.set, Args] at h
  | [], _, _, _, hj, _, _ => by simp at hj

/-- `phi` holds when the return set is flagged and empty. -/
theorem phiS_empty_ret (args : List (Bool × (V → Prop))) (r : V → Prop) (P : List (Arrow V))
    (len : ∀ p ∈ P, p.1.length = args.length) (he : ∀ v, ¬r v) : phiS args (true, r) P := by
  rw [phiS_iff _ _ _ len]
  intro x y _ hy _
  cases y with
  | none => cases hy
  | some v => exact he v hy

/-- `phi` holds when an argument is flagged and empty. -/
theorem phiS_empty_arg (args : List (Bool × (V → Prop))) (j : Nat) (hj : j < args.length) (e : V → Prop)
    (ret : Bool × (V → Prop)) (P : List (Arrow V)) (len : ∀ p ∈ P, p.1.length = args.length) (he : ∀ v, ¬e v) :
    phiS (args.set j (true, e)) ret P := by
  rw [phiS_iff _ _ _ (by simpa using len)]
  intro x y hx
  exact absurd hx (args_set_empty args j e x hj he)

end Elixir.STTDescrProofsTest.FunSem

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

theorem encA_set (args : List (Bool × Term)) (j : Nat) (p : Bool × Term) :
    Term.list ((args.map fun p => Term.tuple #[boolAtom p.1, p.2]).set j (.tuple #[boolAtom p.1, p.2])) =
      encA (args.set j p) := by
  simp [encA, List.map_set]

theorem guard_member (b : Bool) {α : Type} (f g : Unit → Except Exception α) :
    Lynx.Except.guard (.ok ((boolAtom b).isMember [.atom "false", .atom "nil"])) f g = if b then g () else f () := by
  cases b <;> simp [boolAtom, Term.isMember]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

/-- Positive arrows of arity `n` with element types. -/
def PosOk (E : Term → Prop) (n : Nat) (P : List (Term × List Term × Term)) : Prop :=
  ∀ p ∈ P, (∀ u ∈ p.2.1, E u) ∧ E p.2.2 ∧ p.2.1.length = n

theorem semP_len {P : List (Term × List Term × Term)} (hP : PosOk E n P) {args : List (Bool × Term)}
    (len : args.length = n) : ∀ p ∈ semP den P, p.1.length = (semA den args).length := by
  intro p mp
  obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
  simp [semA, (hP q mq).2.2, len]

theorem phiArgs_nil (d : Dispatcher) (j args ret P cache seen : Term) :
    Elixir.Module.Types.Descr.«phi_arguments/7» d .nil j args ret P cache seen = .ok (.tuple #[.atom "true", cache]) := by
  rw [Elixir.Module.Types.Descr.«phi_arguments/7».eq_def]; rfl

/-- `phi_arguments/7` checks the skips of an arrow through its remaining arguments, given that `phi/5` answers
for the remaining arrows. -/
theorem phiArgs_run (ctx : PhiCtx E den K seen) {m : Nat} (hm : K ≤ m) {args : List (Bool × Term)}
    (hA : ∀ p ∈ args, E p.2) (lA : args.length = n) {ret : Bool × Term} (hR : E ret.2)
    {P : List (Term × List Term × Term)} (hP : PosOk E n P)
    (ih : ∀ args' cache, (∀ p ∈ args', E p.2) → List.length args' = n → CacheOk E den n cache →
      ∃ b c, Elixir.Module.Types.Descr.«phi/5» (D m) (encA args') (encR ret) (encP P) cache seen =
          .ok (.tuple #[boolAtom b, c]) ∧
        (b = Bool.true ↔ FunSem.phiS (semA den args') (semR den ret) (semP den P)) ∧ CacheOk E den n c) :
    ∀ (suf : List Term) (j : Nat), j + suf.length = n → (∀ u ∈ suf, E u) → ∀ cache, CacheOk E den n cache →
      ∃ b c, Elixir.Module.Types.Descr.«phi_arguments/7» (D m) (Term.list suf) (.integer j) (encA args) (encR ret)
          (encP P) cache seen = .ok (.tuple #[boolAtom b, c]) ∧
        (b = Bool.true ↔ ∀ i (h : i < suf.length),
          FunSem.phiS (FunSem.skipAt (semA den args) (j + i) (den suf[i])) (semR den ret) (semP den P)) ∧
        CacheOk E den n c
  | [], j, _, _, cache, ok => ⟨Bool.true, cache, by simpa [Term.list, boolAtom] using phiArgs_nil _ _ _ _ _ cache seen,
      by simp, ok⟩
  | u :: suf, j, hj, hu, cache, ok => by
    have jn : j < args.length := by simp at hj; omega
    have hu₀ : E u := hu u (by simp)
    obtain ⟨c, hc, rc, sc⟩ := ctx.diff (hA _ (List.getElem_mem jn)) hu₀
    have ec := ctx.empty hc m hm
    -- The first skip.
    have first : ∃ b₁ c₁, (do
          let x ← Elixir.Module.Types.Descr.«empty_seen?/2» (D m) c seen
          Lynx.Except.guard (.ok (x.isMember [.atom "false", .atom "nil"]))
            (fun _ => do
              let a ← Elixir.List.«replace_at/3» (encA args) (.integer j) (.tuple #[.atom "true", c])
              Elixir.Module.Types.Descr.«phi/5» (D m) a (encR ret) (encP P) cache seen)
            fun _ => pure (.tuple #[.atom "true", cache])) = .ok (.tuple #[boolAtom b₁, c₁]) ∧
        (b₁ = Bool.true ↔ FunSem.phiS (FunSem.skipAt (semA den args) j (den u)) (semR den ret) (semP den P)) ∧
        CacheOk E den n c₁ := by
      have skip : FunSem.skipAt (semA den args) j (den u) = semA den (args.set j (Bool.true, c)) := by
        rw [semA_set]
        simp only [FunSem.skipAt]
        congr 2
        funext v
        simp only [semA, List.getElem?_map, jn, List.getElem?_eq_getElem, Option.map_some, Option.getD_some]
        exact propext (sc v).symm
      rw [ec]
      cases he : isEmpty den c
      · have rep := replace_list (args.map fun p => Term.tuple #[boolAtom p.1, p.2]) j (.tuple #[boolAtom Bool.true, c])
          (by simp [jn])
        replace rep : Elixir.List.«replace_at/3» (encA args) (.integer j) (.tuple #[boolAtom Bool.true, c]) =
            .ok (encA (args.set j (Bool.true, c))) := by
          rw [← encA_set]; exact rep
        obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := ih (args.set j (Bool.true, c)) cache
          (fun p mp => by
            rcases List.mem_or_eq_of_mem_set mp with mp | rfl
            · exact hA p mp
            · exact hc)
          (by simp [lA]) ok
        refine ⟨b₁, c₁, ?_, by rw [skip]; exact s₁, o₁⟩
        simp only [guard_member, Bool.false_eq_true, ite_false, Lynx.Except.ok_bind]
        rw [show Term.tuple #[.atom "true", c] = .tuple #[boolAtom Bool.true, c] from rfl, rep, Lynx.Except.ok_bind]
        exact r₁
      · refine ⟨Bool.true, cache, by simp [boolAtom], ?_, ok⟩
        simp only [true_iff]
        rw [skip, semA_set]
        exact FunSem.phiS_empty_arg _ j (by simp [semA, jn]) (den c) _ _ (semP_len hP lA) ((isEmpty_iff den c).mp he)
    obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := first
    obtain ⟨b₂, c₂, r₂, s₂, o₂⟩ := phiArgs_run ctx hm hA lA hR hP ih suf (j + 1) (by simp at hj; omega)
      (fun u' mu => hu u' (by simp [mu])) c₁ o₁
    have nth := nth_list (args.map fun p => Term.tuple #[boolAtom p.1, p.2]) j (by simp [jn])
    simp only [List.getElem_map] at nth
    refine ⟨b₁ && b₂, if b₁ then c₂ else c₁, ?_, ?_, ?_⟩
    · rw [Elixir.Module.Types.Descr.«phi_arguments/7».eq_def]
      simp only [Erlang.erlang.«+/2_integers»]
      simp only [encA] at nth r₁ r₂ ⊢
      rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega] at r₂
      simp only [Lynx.Except.ok_bind]
      rw [nth]
      simp only [rc m hm, Lynx.Except.ok_bind]
      rw [r₁]
      cases b₁ <;> simp [r₂]
    · rw [Bool.and_eq_true, s₁, s₂]
      constructor
      · rintro ⟨h₀, hs⟩ i hi
        cases i with
        | zero => simpa using h₀
        | succ i =>
          have := hs i (by simp at hi; omega)
          rw [show j + 1 + i = j + (i + 1) by omega] at this
          simpa using this
      · intro h
        refine ⟨h 0 (by simp), fun i hi => ?_⟩
        have := h (i + 1) (by simp; omega)
        rw [show j + (i + 1) = j + 1 + i by omega] at this
        simpa using this
    · cases b₁ <;> simp [o₁, o₂]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {n K : Nat} {seen : Term}

/-- `phi/5` answers whether no row with its arguments and result is allowed by all its arrows. -/
theorem phi_run (ctx : PhiCtx E den K seen) {m : Nat} (hm : K + 1 ≤ m) :
    ∀ (P : List (Term × List Term × Term)), PosOk E n P → ∀ (args : List (Bool × Term)) (ret : Bool × Term) cache,
      (∀ p ∈ args, E p.2) → args.length = n → E ret.2 → CacheOk E den n cache →
      ∃ b c, Elixir.Module.Types.Descr.«phi/5» (D m) (encA args) (encR ret) (encP P) cache seen =
          .ok (.tuple #[boolAtom b, c]) ∧
        (b = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den P)) ∧ CacheOk E den n c
  | [], _, args, ret, cache, hA, lA, hR, ok => phi_base ctx ⟨hA, lA, hR, by simp⟩ ok hm
  | (key, us, s) :: P, hP, args, ret, cache, hA, lA, hR, ok => by
    have hP' : PosOk E n P := fun p mp => hP p (by simp [mp])
    obtain ⟨hU, hS, lU⟩ := hP (key, us, s) (by simp)
    have valid : PhiOk E n args ret ((key, us, s) :: P) := ⟨hA, lA, hR, hP⟩
    have ih := phi_run ctx hm P hP'
    have ok2 := ok
    obtain ⟨M, eM, hM⟩ := ok2
    subst eM
    -- What the arrow means.
    have unfoldS : FunSem.phiS (semA den args) (semR den ret) (semP den ((key, us, s) :: P)) ↔
        FunSem.phiS (semA den args) (Bool.true, fun v => den ret.2 v ∧ den s v) (semP den P) ∧
          ∀ i (h : i < us.length), FunSem.phiS (FunSem.skipAt (semA den args) (0 + i) (den us[i])) (semR den ret)
            (semP den P) := by
      simp only [semP, List.map_cons, FunSem.phiS, semR]
      refine and_congr_right fun _ => ?_
      rw [show (P.map fun p => (p.2.1.map den, den p.2.2)) = semP den P from rfl]
      constructor
      · intro h i hi
        exact h _ ((FunSem.mem_skips _ _ (by simp [semA, lU, lA]) _).mpr ⟨i, by simpa using hi, by simp⟩)
      · intro h a ma
        obtain ⟨i, hi, rfl⟩ := (FunSem.mem_skips _ _ (by simp [semA, lU, lA]) _).mp ma
        simpa using h i (by simpa using hi)
    have key_eq : Term.tuple #[encA args, encR ret, encP ((key, us, s) :: P)] =
        .tuple #[encA args, .tuple #[boolAtom ret.1, ret.2], .cons (.tuple #[key, Term.list us, s]) (encP P)] := rfl
    cases hl : mapLookup M (.tuple #[encA args, encR ret, encP ((key, us, s) :: P)]) with
    | some w =>
      obtain ⟨b, rfl, sem⟩ := cache_get ctx.congr ⟨M, rfl, hM⟩ valid (w := w) (by rw [getMapKeys_single, hl]; rfl)
      refine ⟨b, .map M, ?_, sem, ⟨M, rfl, hM⟩⟩
      rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
      rw [key_eq] at hl
      simp only [encR, encP, List.map_cons, Term.list] at hl ⊢
      simp [getMapKeys_single, hl]
    | none =>
      obtain ⟨c, hc, rc, sc⟩ := ctx.inter hR hS
      have ec := ctx.empty hc m (by omega)
      have denc : den c = fun v => den ret.2 v ∧ den s v := funext fun v => propext (sc v)
      -- The arrow used: the return meets the arrow's return.
      have first : ∃ b₁ c₁, (do
            let x ← Elixir.Module.Types.Descr.«empty_seen?/2» (D m) c seen
            Lynx.Except.guard (.ok (x.isMember [.atom "false", .atom "nil"]))
              (fun _ => Elixir.Module.Types.Descr.«phi/5» (D m) (encA args) (.tuple #[.atom "true", c]) (encP P)
                (.map M) seen)
              fun _ => pure (.tuple #[.atom "true", .map M])) = .ok (.tuple #[boolAtom b₁, c₁]) ∧
          (b₁ = Bool.true ↔ FunSem.phiS (semA den args) (Bool.true, fun v => den ret.2 v ∧ den s v) (semP den P)) ∧
          CacheOk E den n c₁ := by
        rw [ec]
        cases he : isEmpty den c
        · obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := ih args (Bool.true, c) (.map M) hA lA hc ok
          refine ⟨b₁, c₁, ?_, ?_, o₁⟩
          · simp only [Lynx.Except.ok_bind, guard_member, Bool.false_eq_true, ite_false]; exact r₁
          · rw [s₁]; simp [semR, denc]
        · refine ⟨Bool.true, .map M, by simp [boolAtom], ?_, ok⟩
          simp only [true_iff]
          exact FunSem.phiS_empty_ret _ _ _ (semP_len hP' lA) fun v hv =>
            (isEmpty_iff den c).mp he v ((sc v).mpr hv)
      obtain ⟨b₁, c₁, r₁, s₁, o₁⟩ := first
      have miss : getMapKeys [.tuple #[encA args, encR ret, encP ((key, us, s) :: P)]] (.map M) = [] := by
        rw [getMapKeys_single, hl]; rfl
      rw [key_eq] at miss
      cases b₁
      · -- The arrow used is not covered: the answer is false.
        obtain ⟨c', put, o'⟩ := cache_put o₁ valid (b := Bool.false)
          (by simp only [Bool.false_eq_true, false_iff, unfoldS, not_and]; intro h; exact absurd h (by simpa using s₁))
        refine ⟨Bool.false, c', ?_, ?_, o'⟩
        · rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
          rw [key_eq] at put
          simp only [encR, encP, List.map_cons, Term.list] at miss put ⊢
          simp only [pure_bind, miss]
          simp only [encP] at r₁
          rw [rc m (by omega), Lynx.Except.ok_bind, r₁, Lynx.Except.ok_bind]
          simp only [boolAtom_false]
          rw [show Term.atom "false" = boolAtom Bool.false from rfl, put]
          rfl
        · simp only [Bool.false_eq_true, false_iff, unfoldS, not_and]; intro h; exact absurd h (by simpa using s₁)
      · obtain ⟨b₂, c₂, r₂, s₂, o₂⟩ := phiArgs_run ctx (by omega) hA lA hR hP'
          (fun args' cache h l o => ih args' ret cache h l hR o) us 0 (by simp [lU]) hU c₁ o₁
        have sem : b₂ = Bool.true ↔ FunSem.phiS (semA den args) (semR den ret) (semP den ((key, us, s) :: P)) := by
          rw [unfoldS, s₂]; simp only [s₁.mp rfl, true_and]
        obtain ⟨c', put, o'⟩ := cache_put o₂ valid sem
        refine ⟨b₂, c', ?_, sem, o'⟩
        rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
        rw [key_eq] at put
        simp only [encR, encP, List.map_cons, Term.list] at miss put ⊢
        simp only [pure_bind, miss]
        simp only [encP] at r₁ r₂
        rw [rc m (by omega), Lynx.Except.ok_bind, r₁, Lynx.Except.ok_bind]
        simp only [boolAtom_true]
        rw [show ((0 : Nat) : Int) = 0 from rfl] at r₂
        rw [show Term.tuple ⟨[boolAtom ret.1, ret.2]⟩ = encR ret from rfl, r₂, Lynx.Except.ok_bind]
        dsimp only
        rw [show encR ret = Term.tuple #[boolAtom ret.1, ret.2] from rfl, put]
        rfl

end

end Elixir.STTDescrProofsTest.Nest

/-! Application of an intersection of arrows to real argument tuples, and the fast paths of `phi_starter`. -/

namespace Elixir.STTDescrProofsTest.FunSem
variable {V : Type}

/-- Real arguments in an arrow's domain. -/
def InDomR : List (V → Prop) → List V → Prop
  | [], [] => True
  | t :: ts, v :: vs => t v ∧ InDomR ts vs
  | [], _ :: _ => False
  | _ :: _, [] => False

theorem inDom_real : ∀ (ts : List (V → Prop)) (x : List V), InDom ts (x.map some) ↔ InDomR ts x
  | [], [] => Iff.rfl
  | t :: ts, v :: vs => by simp only [List.map, InDom, InDomR, Opt, inDom_real ts vs]
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl

/-- Probes replaced by real values. -/
def fill : List (Option V) → List V → List V
  | o :: os, w :: ws => o.getD w :: fill os ws
  | _, _ => []

theorem fill_args : ∀ (t : List (V → Prop)) (x : List (Option V)) (w : List V), InDomR t w →
    Args (t.map (false, ·)) x → InDomR t (fill x w)
  | [], [], [], _, _ => trivial
  | t :: ts, o :: os, w :: ws, ⟨hw, hws⟩, ⟨ho, hos⟩ => by
    refine ⟨?_, fill_args ts os ws hws hos⟩
    cases o with
    | none => exact hw
    | some v => exact ho
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | [], [], _ :: _, h, _ => h.elim
  | _ :: _, _ :: _, [], h, _ => h.elim

/-- Filling probes keeps a row in every domain it was in only through its real values: domains that contain the
filled row contain the row with probes. -/
theorem inDom_fill : ∀ (us : List (V → Prop)) (x : List (Option V)) (w : List V), x.length = w.length →
    InDom us ((fill x w).map some) → InDom us x
  | [], [], [], _, _ => trivial
  | u :: us, o :: os, w :: ws, len, ⟨ho, hos⟩ => by
    refine ⟨?_, inDom_fill us os ws (by simpa using len) hos⟩
    cases o with
    | none => rfl
    | some v => exact ho
  | [], _ :: _, _ :: _, _, h => by simp [fill, InDom] at h
  | _ :: _, [], _, _, h => by simp [fill, InDom] at h
  | _ :: _, _ :: _, [], len, _ => by simp at len
  | [], [], _ :: _, len, _ => by simp at len
  | [], _ :: _, [], len, _ => by simp at len

theorem inDomR_length : ∀ {t : List (V → Prop)} {x : List V}, InDomR t x → x.length = t.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [inDomR_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- When every argument has a value, rows with probes can be filled with real arguments: no row exists exactly when
no real row exists. -/
theorem noRow_real (P : List (Arrow V)) (t : List (V → Prop)) (s : V → Prop) (w : List V) (hw : InDomR t w) :
    NoRow (t.map (false, ·)) (false, fun v => ¬s v) P ↔
      ∀ x, InDomR t x → ∀ y, (∀ p ∈ P, Allows p (x.map some, y)) → ∃ v, y = some v ∧ s v := by
  constructor
  · intro h x hx y hall
    apply Classical.byContradiction
    intro hn
    refine h (x.map some) y ((inDom_args t _).mp ((inDom_real t x).mpr hx)) ?_ hall
    cases y with
    | none => rfl
    | some v => exact fun hv => hn ⟨v, rfl, hv⟩
  · intro h x y hx hy hall
    have lx : x.length = w.length := by
      rw [inDom_length ((inDom_args t x).mpr hx), inDomR_length hw]
    have hf := fill_args t x w hw hx
    obtain ⟨v, rfl, hv⟩ := h (fill x w) hf y fun p mp hd => hall p mp (inDom_fill p.1 x w lx hd)
    exact hy hv

/-- The results of applying arrows to arguments in `I`, refined by `r`, as `aux_apply/4` builds them: either an
arrow's domain does not cover the remaining arguments, which are applied to the other arrows, or the arrow applies
and refines the result. -/
def App (I : List V → Prop) (r : V → Prop) : List (Arrow V) → V → Prop
  | [] => r
  | (us, s) :: P => fun v => ((∃ x, I x ∧ ¬InDomR us x) ∧ App (fun x => I x ∧ ¬InDomR us x) r P v) ∨
      App I (fun v => r v ∧ s v) P v

theorem app_iff : ∀ (P : List (Arrow V)) (I : List V → Prop) (r : V → Prop), (∃ x, I x) →
    ∀ v, App I r P v ↔ ∃ x, I x ∧ r v ∧ ∀ p ∈ P, InDomR p.1 x → p.2 v
  | [], I, r, ⟨x, hx⟩, v => ⟨fun h => ⟨x, hx, h, by simp⟩, fun ⟨_, _, h, _⟩ => h⟩
  | (us, s) :: P, I, r, ne, v => by
    simp only [App]
    rw [app_iff P I _ ne]
    constructor
    · rintro (⟨ne', h⟩ | ⟨x, hx, ⟨hr, hs⟩, hall⟩)
      · obtain ⟨x, ⟨hx, hd⟩, hr, hall⟩ := (app_iff P _ r ne' v).mp h
        refine ⟨x, hx, hr, fun p mp hp => ?_⟩
        rcases List.mem_cons.mp mp with rfl | mp
        · exact absurd hp hd
        · exact hall p mp hp
      · refine ⟨x, hx, hr, fun p mp hp => ?_⟩
        rcases List.mem_cons.mp mp with rfl | mp
        · exact hs
        · exact hall p mp hp
    · rintro ⟨x, hx, hr, hall⟩
      by_cases hd : InDomR us x
      · exact Or.inr ⟨x, hx, ⟨hr, hall (us, s) (by simp) hd⟩, fun p mp => hall p (by simp [mp])⟩
      · exact Or.inl ⟨⟨x, hx, hd⟩, (app_iff P _ r ⟨x, hx, hd⟩ v).mpr
          ⟨x, ⟨hx, hd⟩, hr, fun p mp => hall p (by simp [mp])⟩⟩

/-- With non-empty arguments covered by the domains of the positive arrows, a negative arrow contains them exactly
when applying them to its arguments gives results in its return. -/
theorem noRow_app (P : List (Arrow V)) (t : List (V → Prop)) (s : V → Prop) (w : List V) (hw : InDomR t w)
    (cover : ∀ x, InDomR t x → ∃ p ∈ P, InDomR p.1 x) :
    NoRow (t.map (false, ·)) (false, fun v => ¬s v) P ↔ ∀ v, App (InDomR t) (fun _ => True) P v → s v := by
  rw [noRow_real P t s w hw]
  constructor
  · intro h v hv
    obtain ⟨x, hx, -, hall⟩ := (app_iff P _ _ ⟨w, hw⟩ v).mp hv
    obtain ⟨v', e, hs⟩ := h x hx (some v) fun p mp hd => ⟨v, rfl, hall p mp ((inDom_real p.1 x).mp hd)⟩
    cases e; exact hs
  · intro h x hx y hall
    obtain ⟨p, mp, hp⟩ := cover x hx
    obtain ⟨v, rfl, -⟩ := hall p mp ((inDom_real p.1 x).mpr hp)
    refine ⟨v, rfl, h v ((app_iff P _ _ ⟨w, hw⟩ v).mpr ⟨x, hx, trivial, fun q mq hq => ?_⟩)⟩
    obtain ⟨v', e, hv'⟩ := hall q mq ((inDom_real q.1 x).mpr hq)
    cases e; exact hv'

/-- With pairwise disjoint domains, the results are the returns of the arrows whose domain meets the arguments. -/
theorem app_disjoint (P : List (Arrow V)) (I : List V → Prop) (ne : ∃ x, I x)
    (disj : ∀ i j (hi : i < P.length) (hj : j < P.length), i ≠ j → ∀ x, InDomR P[i].1 x → ¬InDomR P[j].1 x)
    (cover : ∀ x, I x → ∃ p ∈ P, InDomR p.1 x) (s : V → Prop) :
    (∀ v, App I (fun _ => True) P v → s v) ↔ ∀ p ∈ P, (∃ x, I x ∧ InDomR p.1 x) → ∀ v, p.2 v → s v := by
  constructor
  · intro h p mp ⟨x, hx, hd⟩ v hv
    refine h v ((app_iff P I _ ne v).mpr ⟨x, hx, trivial, fun q mq hq => ?_⟩)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem mq
    by_cases e : i = j
    · subst e; exact hv
    · exact absurd hq (disj i j hi hj e x hd)
  · intro h v hv
    obtain ⟨x, hx, -, hall⟩ := (app_iff P I _ ne v).mp hv
    obtain ⟨p, mp, hp⟩ := cover x hx
    exact h p mp ⟨x, hx, hp⟩ v (hall p mp hp)

end Elixir.STTDescrProofsTest.FunSem

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! What the function checks compute: applications of arrows to domains, and the shortcuts of `phi_starter/4`. -/

/-- A proposition as a Boolean. -/
noncomputable def bp (p : Prop) : Bool := @decide p (Classical.propDecidable p)

@[simp] theorem bp_true {p : Prop} : bp p = Bool.true ↔ p := by simp [bp]
@[simp] theorem bp_false {p : Prop} : bp p = Bool.false ↔ ¬p := by simp [bp]

theorem bp_congr {p q : Prop} (h : p ↔ q) : bp p = bp q := by
  rw [propext h]

section
variable {V : Type}

/-- Element types for the function checks under the seen set `seen`: closed under the operations the checks
perform, with exact emptiness under `seen` and exact subtyping, and sound disjointness, from call depth `K`. -/
structure FunElem (E : Term → Prop) (den : Term → V → Prop) (K : Nat) (seen : Term) : Prop where
  phi : PhiCtx E den K seen
  union : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
    ∀ v, den c v ↔ den a v ∨ den b v
  neg : ∀ {a}, E a → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c) ∧
    ∀ v, den c v ↔ ¬den a v
  sub : ∀ {a b}, E a → E b → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom (bp (∀ v, den a v → den b v)))
  disj : ∀ {a b}, E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
    (s = Bool.true → ∀ v, den a v → den b v → False)
  term : E (.atom "term") ∧ ∀ v, den (.atom "term") v
  none : E (.map []) ∧ ∀ v, ¬den (.map []) v
  empty0 : ∀ {a}, E a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map []) = .ok (boolAtom (isEmpty den a))
  empty1 : ∀ {a}, E a → ∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom (isEmpty den a))

/-- Domains of arrows, tuple types of their arguments standing for lists of values `dden`: closed under the
operations the checks perform, with exact emptiness with no seen set and under `seen`, from call depth `K`. -/
structure FunDom (Dm E : Term → Prop) (den : Term → V → Prop) (dden : Term → List V → Prop) (K : Nat)
    (seen : Term) : Prop where
  dom : ∀ l : List Term, (∀ a ∈ l, E a) → ∃ t, Dm t ∧ Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) = .ok t ∧
    ∀ x, dden t x ↔ FunSem.InDomR (l.map den) x
  none : Dm (.map []) ∧ ∀ x, ¬dden (.map []) x
  isMap : ∀ {a}, Dm a → ∃ X, a = .map X
  union : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧ ∀ x, dden c x ↔ dden a x ∨ dden b x
  inter : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
    ∀ x, dden c x ↔ dden a x ∧ dden b x
  diff : ∀ {a b}, Dm a → Dm b → ∃ c, Dm c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
    ∀ x, dden c x ↔ dden a x ∧ ¬dden b x
  empty : ∀ {a}, Dm a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map []) = .ok (boolAtom (bp (∀ x, ¬dden a x)))
  emptySeen : ∀ {a}, Dm a → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a seen = .ok (boolAtom (bp (∀ x, ¬dden a x)))

variable {E Dm : Term → Prop} {den : Term → V → Prop} {dden : Term → List V → Prop} {K : Nat} {seen : Term}

theorem FunDom.empty1 (fd : FunDom Dm E den dden K seen) {a : Term} (ha : Dm a) (m : Nat) (hm : K ≤ m) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) a = .ok (boolAtom (bp (∀ x, ¬dden a x))) := by
  obtain ⟨X, rfl⟩ := fd.isMap ha
  simp only [Elixir.Module.Types.Descr.«empty?/1»]
  exact fd.empty ha m hm

theorem app_congr_I {I I' : List V → Prop} (h : ∀ x, I x ↔ I' x) (r : V → Prop) (P : List (FunSem.Arrow V)) (v : V) :
    FunSem.App I r P v ↔ FunSem.App I' r P v := by
  have : I = I' := funext fun x => propext (h x)
  rw [this]

theorem app_congr_r (I : List V → Prop) {r r' : V → Prop} (h : ∀ v, r v ↔ r' v) (P : List (FunSem.Arrow V)) (v : V) :
    FunSem.App I r P v ↔ FunSem.App I r' P v := by
  have : r = r' := funext fun x => propext (h x)
  rw [this]

theorem inDomR_exists : ∀ (ts : List (V → Prop)), (∀ t ∈ ts, ∃ v, t v) → ∃ w, FunSem.InDomR ts w
  | [], _ => ⟨[], trivial⟩
  | t :: ts, h => by
    obtain ⟨v, hv⟩ := h t List.mem_cons_self
    obtain ⟨w, hw⟩ := inDomR_exists ts fun u mu => h u (List.mem_cons_of_mem _ mu)
    exact ⟨v :: w, hv, hw⟩

theorem inDomR_nil_iff {xs : List V} : FunSem.InDomR [] xs ↔ xs = [] := by
  cases xs <;> simp [FunSem.InDomR]

theorem inDomR_cons_iff {t : V → Prop} {B : List (V → Prop)} {zs : List V} :
    FunSem.InDomR (t :: B) zs ↔ ∃ z zs', zs = z :: zs' ∧ t z ∧ FunSem.InDomR B zs' := by
  cases zs with
  | nil => simp [FunSem.InDomR]
  | cons z zs =>
    simp only [FunSem.InDomR]
    exact ⟨fun h => ⟨z, zs, rfl, h⟩, fun ⟨z', zs', e, h⟩ => by
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact h⟩

theorem inDomR_append : ∀ (A B : List (V → Prop)) (xs : List V),
    FunSem.InDomR (A ++ B) xs ↔ ∃ ys zs, xs = ys ++ zs ∧ FunSem.InDomR A ys ∧ FunSem.InDomR B zs
  | [], B, xs => by
    constructor
    · intro h; exact ⟨[], xs, rfl, trivial, h⟩
    · rintro ⟨ys, zs, rfl, hy, hz⟩
      obtain rfl := inDomR_nil_iff.mp hy
      simpa using hz
  | t :: A, B, xs => by
    rw [List.cons_append, inDomR_cons_iff]
    constructor
    · rintro ⟨x, xs', rfl, hx, h⟩
      obtain ⟨ys, zs, rfl, hy, hz⟩ := (inDomR_append A B xs').mp h
      exact ⟨x :: ys, zs, rfl, inDomR_cons_iff.mpr ⟨x, ys, rfl, hx, hy⟩, hz⟩
    · rintro ⟨ys, zs, rfl, hy, hz⟩
      obtain ⟨y, ys', rfl, hx, hy'⟩ := inDomR_cons_iff.mp hy
      exact ⟨y, ys' ++ zs, rfl, hx, (inDomR_append A B _).mpr ⟨ys', zs, rfl, hy', hz⟩⟩

/-- Lists of values with a prefix in `A`, followed by a value and a rest that satisfy `Q`. -/
def Split (A : List (V → Prop)) (Q : V → List V → Prop) (x : List V) : Prop :=
  ∃ ys z zs, x = ys ++ z :: zs ∧ FunSem.InDomR A ys ∧ Q z zs

theorem split_congr {A : List (V → Prop)} {Q Q' : V → List V → Prop} (h : ∀ z zs, Q z zs ↔ Q' z zs) (x : List V) :
    Split A Q x ↔ Split A Q' x := by
  constructor
  · rintro ⟨ys, z, zs, e, a, q⟩; exact ⟨ys, z, zs, e, a, (h z zs).mp q⟩
  · rintro ⟨ys, z, zs, e, a, q⟩; exact ⟨ys, z, zs, e, a, (h z zs).mpr q⟩

theorem split_or {A : List (V → Prop)} {Q Q' : V → List V → Prop} (x : List V) :
    (Split A Q x ∨ Split A Q' x) ↔ Split A (fun z zs => Q z zs ∨ Q' z zs) x := by
  constructor
  · rintro (⟨ys, z, zs, e, a, q⟩ | ⟨ys, z, zs, e, a, q⟩)
    · exact ⟨ys, z, zs, e, a, Or.inl q⟩
    · exact ⟨ys, z, zs, e, a, Or.inr q⟩
  · rintro ⟨ys, z, zs, e, a, q | q⟩
    · exact Or.inl ⟨ys, z, zs, e, a, q⟩
    · exact Or.inr ⟨ys, z, zs, e, a, q⟩

theorem split_cons {A : List (V → Prop)} {d : V → Prop} {B : List (V → Prop)} (x : List V) :
    FunSem.InDomR (A ++ d :: B) x ↔ Split A (fun z zs => d z ∧ FunSem.InDomR B zs) x := by
  rw [inDomR_append]
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz⟩
    obtain ⟨z, zs', rfl, hd, hb⟩ := inDomR_cons_iff.mp hz
    exact ⟨ys, z, zs', rfl, hy, hd, hb⟩
  · rintro ⟨ys, z, zs, rfl, hy, hd, hb⟩
    exact ⟨ys, z :: zs, rfl, hy, inDomR_cons_iff.mpr ⟨z, zs, rfl, hd, hb⟩⟩

/-- Lists of values in the products of `accm` reversed, followed by values of `types` that are not values of
`args`, position by position. -/
def RestSem (den : Term → V → Prop) (accm types args : List Term) (x : List V) : Prop :=
  ∃ ys zs, x = ys ++ zs ∧ FunSem.InDomR (accm.reverse.map den) ys ∧ FunSem.InDomR (types.map den) zs ∧
    ¬FunSem.InDomR (args.map den) zs

theorem rest_cons (accm types args : List Term) (t a : Term) (x : List V) :
    RestSem den accm (t :: types) (a :: args) x ↔ Split (accm.reverse.map den)
      (fun z zs => den t z ∧ FunSem.InDomR (types.map den) zs ∧ ¬(den a z ∧ FunSem.InDomR (args.map den) zs)) x := by
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz, hn⟩
    obtain ⟨z, zs', rfl, ht, hb⟩ := inDomR_cons_iff.mp (by simpa using hz)
    exact ⟨ys, z, zs', rfl, hy, ht, hb, fun ⟨h₁, h₂⟩ => hn (by simpa using inDomR_cons_iff.mpr ⟨z, zs', rfl, h₁, h₂⟩)⟩
  · rintro ⟨ys, z, zs, rfl, hy, ht, hb, hn⟩
    refine ⟨ys, z :: zs, rfl, hy, by simpa using inDomR_cons_iff.mpr ⟨z, zs, rfl, ht, hb⟩, fun h => hn ?_⟩
    obtain ⟨z', zs', e, h₁, h₂⟩ := inDomR_cons_iff.mp (by simpa using h)
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨h₁, h₂⟩

theorem rest_snoc (m : Term) (accm types args : List Term) (x : List V) :
    RestSem den (m :: accm) types args x ↔ Split (accm.reverse.map den)
      (fun z zs => den m z ∧ FunSem.InDomR (types.map den) zs ∧ ¬FunSem.InDomR (args.map den) zs) x := by
  have e : (m :: accm).reverse.map den = accm.reverse.map den ++ [den m] := by simp
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz, hn⟩
    rw [e] at hy
    obtain ⟨ys₁, ys₂, rfl, h₁, h₂⟩ := (inDomR_append _ _ ys).mp hy
    obtain ⟨z, zs', rfl, hd, hn'⟩ := inDomR_cons_iff.mp h₂
    obtain rfl := inDomR_nil_iff.mp hn'
    exact ⟨ys₁, z, zs, by simp, h₁, hd, hz, hn⟩
  · rintro ⟨ys, z, zs, rfl, hy, hd, hz, hn⟩
    refine ⟨ys ++ [z], zs, by simp, ?_, hz, hn⟩
    rw [e]
    exact (inDomR_append _ _ _).mpr ⟨ys, [z], rfl, hy, inDomR_cons_iff.mpr ⟨z, [], rfl, hd, trivial⟩⟩

theorem rest_nil (types args : List Term) (x : List V) :
    RestSem den [] types args x ↔ FunSem.InDomR (types.map den) x ∧ ¬FunSem.InDomR (args.map den) x := by
  constructor
  · rintro ⟨ys, zs, rfl, hy, hz, hn⟩
    obtain rfl := inDomR_nil_iff.mp (by simpa using hy)
    exact ⟨by simpa using hz, by simpa using hn⟩
  · rintro ⟨hz, hn⟩
    exact ⟨[], x, rfl, by simp [FunSem.InDomR], hz, hn⟩

/-- Products of arguments: lists of `n` element types, each with some value. -/
def ProdOk (E : Term → Prop) (den : Term → V → Prop) (n : Nat) (p : List Term) : Prop :=
  p.length = n ∧ ∀ e ∈ p, E e ∧ ∃ v, den e v

/-- The lists of values of a list of products. -/
def ProdSem (den : Term → V → Prop) (ps : List (List Term)) (x : List V) : Prop :=
  ∃ p ∈ ps, FunSem.InDomR (p.map den) x

theorem prodSem_cons (p : List Term) (ps : List (List Term)) (x : List V) :
    ProdSem den (p :: ps) x ↔ FunSem.InDomR (p.map den) x ∨ ProdSem den ps x := by
  simp [ProdSem]

theorem prodSem_ne {n : Nat} {ps : List (List Term)} (h : ∀ p ∈ ps, ProdOk E den n p) (ne : ps ≠ []) :
    ∃ x, ProdSem den ps x := by
  obtain ⟨p, mp⟩ : ∃ p, p ∈ ps := by
    cases ps with
    | nil => exact absurd rfl ne
    | cons p _ => exact ⟨p, List.mem_cons_self⟩
  obtain ⟨x, hx⟩ := inDomR_exists (p.map den) fun t mt => by
    obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt
    exact ((h p mp).2 a ma).2
  exact ⟨x, p, mp, hx⟩

/-- Meets of elements with negated elements, position by position, each with some value. -/
def Meets (E : Term → Prop) (den : Term → V → Prop) : List Term → List Term → List Term → Prop
  | [], ts, as => ts = [] ∧ as = []
  | m :: ms, ts, as => ∃ t ts' a as', ts = t :: ts' ∧ as = a :: as' ∧ E m ∧ (∀ v, den m v ↔ den t v ∧ den a v) ∧
      (∃ v, den m v) ∧ Meets E den ms ts' as'

/-- `tuple_elements_meets/4` with no seen set meets a product with the arguments of an arrow, or finds them
disjoint. -/
theorem meets_sem (fe : FunElem E den K seen) : ∀ (nl l acc : List Term), l.length = nl.length →
    (∀ e ∈ l, E e) → (∀ e ∈ nl, E e) →
    ((∀ m, K ≤ m → Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m) (Term.list l) (Term.list nl)
        (Term.list acc) (.map []) = .ok (.atom "disjoint")) ∧
      ∀ x, FunSem.InDomR (l.map den) x → ¬FunSem.InDomR (nl.map den) x) ∨
    ∃ ms, Meets E den ms l nl ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m)
      (Term.list l) (Term.list nl) (Term.list acc) (.map []) = .ok (Term.list (acc.reverse ++ ms))
  | [], l, acc, hlen, _, _ => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact Or.inr ⟨[], ⟨rfl, rfl⟩, fun m _ => by simpa using meets_done (D m) _ _ acc⟩
  | nt :: nl, l, acc, hlen, hl, hnl => by
    obtain ⟨ty, es, rfl⟩ : ∃ ty es, l = ty :: es := by
      cases l with
      | nil => simp at hlen
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hty := hl ty List.mem_cons_self
    have hes : ∀ e ∈ es, E e := fun e m => hl e (List.mem_cons_of_mem _ m)
    have hnt := hnl nt List.mem_cons_self
    have hnl' : ∀ e ∈ nl, E e := fun e m => hnl e (List.mem_cons_of_mem _ m)
    obtain ⟨meet, lmeet, hmeet, smeet⟩ := fe.phi.inter hty hnt
    have step := fun m (hm : K ≤ m) => meets_step (D m) acc (ty :: es) nt nl (.map []) ty es (Or.inr rfl) meet
      (hmeet m hm)
    have em := fe.empty0 lmeet
    rw [list_cons nt nl]
    by_cases ne : ∃ v, den meet v
    · have hb : isEmpty den meet = Bool.false := by
        cases h : isEmpty den meet
        · rfl
        · obtain ⟨v, hv⟩ := ne; exact absurd hv ((isEmpty_iff den meet).mp h v)
      rcases meets_sem fe nl es (meet :: acc) (by simpa using hlen) hes hnl' with ⟨dis, sem⟩ | ⟨ms, hms, run⟩
      · refine Or.inl ⟨fun m hm => by rw [(step m hm).2 (by simpa [hb, boolAtom] using em m hm)]; exact dis m hm, ?_⟩
        intro x h₁ h₂
        cases x with
        | nil => simp [FunSem.InDomR] at h₁
        | cons y ys => exact sem ys h₁.2 h₂.2
      · refine Or.inr ⟨meet :: ms, ⟨ty, es, nt, nl, rfl, rfl, lmeet, smeet, ne, hms⟩, fun m hm => ?_⟩
        rw [(step m hm).2 (by simpa [hb, boolAtom] using em m hm), run m hm]
        simp
    · have hb : isEmpty den meet = Bool.true := (isEmpty_iff den meet).mpr fun v hv => ne ⟨v, hv⟩
      refine Or.inl ⟨fun m hm => (step m hm).1 (by simpa [hb, boolAtom] using em m hm), ?_⟩
      intro x h₁ h₂
      cases x with
      | nil => simp [FunSem.InDomR] at h₁
      | cons y ys => exact ne ⟨y, (smeet y).mpr ⟨h₁.1, h₂.1⟩⟩

/-- `product_difference/5` splits a product minus the arguments of an arrow into products, after the products `acc`
already found. -/
theorem prod_diff_sem (fe : FunElem E den K seen) (n : Nat) :
    ∀ types args meets : List Term, Meets E den meets types args → (∀ e ∈ types, E e ∧ ∃ v, den e v) →
      (∀ e ∈ args, E e) → ∀ accm : List Term, accm.length + types.length = n → (∀ e ∈ accm, E e ∧ ∃ v, den e v) →
      ∀ acc : List (List Term), (∀ p ∈ acc, ProdOk E den n p) →
      ∃ out : List (List Term), (∀ p ∈ out, ProdOk E den n p) ∧ (∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«product_difference/5» (D m) (Term.list types) (Term.list args)
          (Term.list meets) (Term.list accm) (Term.list (acc.map Term.list)) = .ok (Term.list (out.map Term.list))) ∧
        ∀ x, ProdSem den out x ↔ ProdSem den acc x ∨ RestSem den accm types args x
  | [], args, meets, hM, _, _, accm, _, _, acc, hacc => by
    have hm : meets = [] ∧ args = [] := by
      cases meets with
      | nil => exact ⟨rfl, hM.2⟩
      | cons _ _ => obtain ⟨_, _, _, _, h, -⟩ := hM; cases h
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨acc, hacc, fun m _ => by rw [Elixir.Module.Types.Descr.«product_difference/5».eq_def]; rfl,
      fun x => ⟨Or.inl, ?_⟩⟩
    rintro (h | ⟨ys, zs, -, -, hz, hn⟩)
    · exact h
    · exact absurd (by simpa using hz) hn
  | ty :: types, args, meets, hM, ht, hargs, accm, hn, haccm, acc, hacc => by
    obtain ⟨mt, meets, rfl⟩ : ∃ mt ms, meets = mt :: ms := by
      cases meets with
      | nil => obtain ⟨h, -⟩ := hM; cases h
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨t', ts', a, args', e₁, rfl, lmt, smt, nmt, hM'⟩ := hM
    simp only [List.cons.injEq] at e₁
    obtain ⟨rfl, rfl⟩ := e₁
    have hty := ht ty List.mem_cons_self
    have ht' : ∀ e ∈ types, E e ∧ ∃ v, den e v := fun e m => ht e (List.mem_cons_of_mem _ m)
    have ha := hargs a List.mem_cons_self
    have ha' : ∀ e ∈ args', E e := fun e m => hargs e (List.mem_cons_of_mem _ m)
    obtain ⟨diff, ldiff, hdiff, sdiff⟩ := fe.phi.diff hty.1 ha
    have e1 := fe.empty1 ldiff
    simp only [List.length_cons] at hn
    by_cases ne : ∃ v, den diff v
    · have hb : isEmpty den diff = Bool.false := by
        cases h : isEmpty den diff
        · rfl
        · obtain ⟨v, hv⟩ := ne; exact absurd hv ((isEmpty_iff den diff).mp h v)
      obtain ⟨out, hout, run, sem⟩ := prod_diff_sem fe n types args' meets hM' ht' ha' (mt :: accm) (by simp; omega)
        (fun e me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact ⟨lmt, nmt⟩
          · exact haccm e me)
        ((accm.reverse ++ diff :: types) :: acc) (fun p mp => by
          rcases List.mem_cons.mp mp with rfl | mp
          · refine ⟨by simp; omega, fun e me => ?_⟩
            simp only [List.mem_append, List.mem_reverse, List.mem_cons] at me
            rcases me with me | rfl | me
            · exact haccm e me
            · exact ⟨ldiff, ne⟩
            · exact ht' e me
          · exact hacc p mp)
      refine ⟨out, hout, fun m hm => ?_, fun x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«product_difference/5».eq_def]
        simp only [Term.list] at run ⊢
        have rev := reverse_list accm (diff :: types)
        simp only [Term.list] at rev
        simp [hdiff m hm, e1 m hm, hb, boolAtom, isMember, rev]
        simpa using run m hm
      · rw [sem x, prodSem_cons, rest_cons, rest_snoc, List.map_append, List.map_cons, split_cons]
        have key : Split (accm.reverse.map den) (fun z zs => den diff z ∧ FunSem.InDomR (types.map den) zs) x ∨
              Split (accm.reverse.map den) (fun z zs => den mt z ∧ FunSem.InDomR (types.map den) zs ∧
                ¬FunSem.InDomR (args'.map den) zs) x ↔
            Split (accm.reverse.map den) (fun z zs => den ty z ∧ FunSem.InDomR (types.map den) zs ∧
              ¬(den a z ∧ FunSem.InDomR (args'.map den) zs)) x := by
          rw [split_or]
          refine split_congr (fun z zs => ?_) x
          rw [sdiff z, smt z]
          constructor
          · rintro (⟨⟨h₁, h₂⟩, h₃⟩ | ⟨⟨h₁, h₂⟩, h₃, h₄⟩)
            · exact ⟨h₁, h₃, fun h => h₂ h.1⟩
            · exact ⟨h₁, h₃, fun h => h₄ h.2⟩
          · rintro ⟨h₁, h₂, h₃⟩
            by_cases h : den a z
            · exact Or.inr ⟨⟨h₁, h⟩, h₂, fun h' => h₃ ⟨h, h'⟩⟩
            · exact Or.inl ⟨⟨h₁, h⟩, h₂⟩
        rw [← key]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
    · have hb : isEmpty den diff = Bool.true := (isEmpty_iff den diff).mpr fun v hv => ne ⟨v, hv⟩
      obtain ⟨out, hout, run, sem⟩ := prod_diff_sem fe n types args' meets hM' ht' ha' (ty :: accm) (by simp; omega)
        (fun e me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact hty
          · exact haccm e me) acc hacc
      refine ⟨out, hout, fun m hm => ?_, fun x => ?_⟩
      · rw [Elixir.Module.Types.Descr.«product_difference/5».eq_def]
        simp only [Term.list] at run ⊢
        simp [hdiff m hm, e1 m hm, hb, boolAtom, isMember]
        simpa using run m hm
      · rw [sem x, rest_cons, rest_snoc]
        refine or_congr Iff.rfl (split_congr (fun z zs => ?_) x)
        constructor
        · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, fun h => h₃ h.2⟩
        · rintro ⟨h₁, h₂, h₃⟩
          refine ⟨h₁, h₂, fun h => h₃ ⟨?_, h⟩⟩
          exact Classical.byContradiction fun na => ne ⟨z, (sdiff z).mpr ⟨h₁, na⟩⟩

/-- `args_difference/4` subtracts the arguments of an arrow from products: all of them are disjoint from the
arguments, or the products of what remains are found, after the products `acc` already found. -/
theorem args_diff_sem (fe : FunElem E den K seen) (args : List Term) (hargs : ∀ e ∈ args, E e) :
    ∀ products : List (List Term), (∀ p ∈ products, ProdOk E den args.length p) →
      ∀ acc : List (List Term), (∀ p ∈ acc, ProdOk E den args.length p) → ∀ dj : Bool,
      ∃ out : Term, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«args_difference/4» (D m)
          (Term.list (products.map Term.list)) (Term.list args) (Term.list (acc.map Term.list)) (boolAtom dj) =
            .ok out) ∧
        ((out = .atom "disjoint" ∧ dj = Bool.true ∧ ∀ x, ProdSem den products x → ¬FunSem.InDomR (args.map den) x) ∨
          ∃ ps, out = Term.list (ps.map Term.list) ∧ (∀ p ∈ ps, ProdOk E den args.length p) ∧
            ∀ x, ProdSem den ps x ↔ ProdSem den acc x ∨ (ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x)) := by
  intro products
  induction products with
  | nil =>
    intro _ acc hacc dj
    cases dj
    · refine ⟨_, fun m _ => by rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]; rfl,
        Or.inr ⟨acc, rfl, hacc, fun x => ?_⟩⟩
      simp [ProdSem]
    · exact ⟨_, fun m _ => by rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]; rfl,
        Or.inl ⟨rfl, rfl, fun x h => by simp [ProdSem] at h⟩⟩
  | cons p products ih =>
    intro hps acc hacc dj
    obtain ⟨hpl, hp⟩ := hps p List.mem_cons_self
    have hps' : ∀ q ∈ products, ProdOk E den args.length q := fun q m => hps q (List.mem_cons_of_mem _ m)
    rcases meets_sem fe args p [] hpl (fun e me => (hp e me).1) hargs with ⟨dis, sem⟩ | ⟨ms, hms, run⟩
    · obtain ⟨out, rout, hout⟩ := ih hps' (p :: acc) (fun q mq => by
        rcases List.mem_cons.mp mq with rfl | mq
        · exact ⟨hpl, hp⟩
        · exact hacc q mq) dj
      refine ⟨out, fun m hm => ?_, ?_⟩
      · have d := dis m hm
        rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]
        simp [d]
        simpa using rout m hm
      · rcases hout with ⟨e, edj, h⟩ | ⟨ps, e, hps'', h⟩
        · refine Or.inl ⟨e, edj, fun x hx => ?_⟩
          rcases (prodSem_cons p products x).mp hx with hx | hx
          · exact sem x hx
          · exact h x hx
        · refine Or.inr ⟨ps, e, hps'', fun x => ?_⟩
          rw [h x, prodSem_cons, prodSem_cons]
          constructor
          · rintro ((h | h) | ⟨h, n⟩)
            · exact Or.inr ⟨Or.inl h, sem x h⟩
            · exact Or.inl h
            · exact Or.inr ⟨Or.inr h, n⟩
          · rintro (h | ⟨h | h, n⟩)
            · exact Or.inl (Or.inr h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr ⟨h, n⟩
    · obtain ⟨acc', hacc', rpd, spd⟩ := prod_diff_sem fe args.length p args ms hms hp hargs [] (by simp [hpl])
        (by simp) acc hacc
      obtain ⟨out, rout, hout⟩ := ih hps' acc' hacc' Bool.false
      refine ⟨out, fun m hm => ?_, ?_⟩
      · have d := run m hm
        simp only [List.reverse_nil, List.nil_append] at d
        have pd := rpd m hm
        rw [Elixir.Module.Types.Descr.«args_difference/4».eq_def]
        cases ms with
        | nil => simp [d, pd]; simpa [boolAtom] using rout m hm
        | cons x xs => simp [d] at pd ⊢; simp [pd]; simpa [boolAtom] using rout m hm
      · rcases hout with ⟨-, h, -⟩ | ⟨ps, e, hps'', h⟩
        · cases h
        · refine Or.inr ⟨ps, e, hps'', fun x => ?_⟩
          rw [h x, spd x, rest_nil, prodSem_cons]
          constructor
          · rintro ((h | ⟨h, n⟩) | ⟨h, n⟩)
            · exact Or.inl h
            · exact Or.inr ⟨Or.inl h, n⟩
            · exact Or.inr ⟨Or.inr h, n⟩
          · rintro (h | ⟨h | h, n⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨h, n⟩)
            · exact Or.inr ⟨h, n⟩

theorem app_mono_r : ∀ (P : List (FunSem.Arrow V)) (I : List V → Prop) (r r' : V → Prop), (∀ v, r v → r' v) →
    ∀ v, FunSem.App I r P v → FunSem.App I r' P v
  | [], _, _, _, h, v, a => h v a
  | (us, s) :: P, I, r, r', h, v, a => by
    simp only [FunSem.App] at a ⊢
    rcases a with ⟨ne, a⟩ | a
    · exact Or.inl ⟨ne, app_mono_r P _ r r' h v a⟩
    · exact Or.inr (app_mono_r P I _ _ (fun v ⟨x, y⟩ => ⟨h v x, y⟩) v a)

/-- Applications return values of the returns reached. -/
theorem app_sub_r : ∀ (P : List (FunSem.Arrow V)) (I : List V → Prop) (r : V → Prop) (v : V),
    FunSem.App I r P v → r v
  | [], _, _, _, a => a
  | (us, s) :: P, I, r, v, a => by
    simp only [FunSem.App] at a
    rcases a with ⟨-, a⟩ | a
    · exact app_sub_r P _ r v a
    · exact (app_sub_r P I _ v a).1

/-- `aux_apply/4` unites its result with the application of the arrows to the products, refined by the returns
reached so far. -/
theorem aux_apply_sem (fe : FunElem E den K seen) (n : Nat) :
    ∀ P : List (Term × List Term × Term), PosOk E n P → ∀ result rets (products : List (List Term)), E result →
      E rets → (∀ p ∈ products, ProdOk E den n p) → products ≠ [] →
      ∃ r, E r ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«aux_apply/4» (D m) result
          (Term.list (products.map Term.list)) rets (encP P) = .ok r) ∧
        ∀ v, den r v ↔ den result v ∨ FunSem.App (ProdSem den products) (den rets) (semP den P) v := by
  intro P
  induction P with
  | nil =>
    intro _ result rets products hres hrets _ _
    obtain ⟨u, hu, ru, su⟩ := fe.union hres hrets
    by_cases hs : ∀ v, den rets v → den result v
    · refine ⟨result, hres, fun m hm => ?_, fun v => ?_⟩
      · have h := fe.sub hrets hres m hm
        have hb : bp (∀ v, den rets v → den result v) = Bool.true := bp_true.mpr hs
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [encP, Term.list, h, hb, isMember]
      · simp only [semP, List.map_nil, FunSem.App]
        exact ⟨Or.inl, fun h => h.elim id (hs v)⟩
    · refine ⟨u, hu, fun m hm => ?_, fun v => ?_⟩
      · have h := fe.sub hrets hres m hm
        have hb : bp (∀ v, den rets v → den result v) = Bool.false := bp_false.mpr hs
        unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp [encP, Term.list, h, hb, isMember, ru m hm]
      · simp only [semP, List.map_nil, FunSem.App]
        exact su v
  | cons p rest ih =>
    intro hP result rets products hres hrets hps nep
    obtain ⟨key, args, ret⟩ := p
    obtain ⟨hargs, hret, hlen⟩ := hP _ List.mem_cons_self
    have ih' := ih fun q mq => hP q (List.mem_cons_of_mem _ mq)
    have hps' : ∀ q ∈ products, ProdOk E den args.length q := fun q mq => ⟨by rw [(hps q mq).1, hlen], (hps q mq).2⟩
    obtain ⟨refine, hrefine, rrefine, srefine⟩ := fe.phi.inter hrets hret
    obtain ⟨x₀, hx₀⟩ := prodSem_ne hps nep
    have app : ∀ v, FunSem.App (ProdSem den products) (den rets) (semP den ((key, args, ret) :: rest)) v ↔
        ((∃ x, ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) ∧
          FunSem.App (fun x => ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) (den rets) (semP den rest) v) ∨
          FunSem.App (ProdSem den products) (den refine) (semP den rest) v := by
      intro v
      simp only [semP, List.map_cons, FunSem.App]
      exact or_congr Iff.rfl (app_congr_r _ (fun v => (srefine v).symm) _ v)
    obtain ⟨out, rout, hout⟩ := args_diff_sem fe args hargs products hps' [] (by simp) Bool.true
    have runs : ∀ m, K ≤ m → Elixir.Module.Types.Descr.«args_difference/4» (D m) (Term.list (products.map Term.list))
        (Term.list args) .nil (.atom "true") = .ok out := fun m hm => by simpa [boolAtom] using rout m hm
    rcases hout with ⟨rfl, -, dis⟩ | ⟨ps, rfl, hps'', sps⟩
    · -- the products are disjoint from the domain of the arrow, which is skipped
      obtain ⟨r, hr, run, s⟩ := ih' result rets products hres hrets hps nep
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp only [encP, List.map_cons, Term.list] at run ⊢
        simp [runs m hm]
        exact run m hm
      · rw [s, app]
        have same : ∀ x, ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x ↔ ProdSem den products x :=
          fun x => ⟨And.left, fun h => ⟨h, dis x h⟩⟩
        rw [app_congr_I same]
        refine or_congr Iff.rfl ⟨fun h => Or.inl ⟨⟨x₀, hx₀, dis x₀ hx₀⟩, h⟩, ?_⟩
        rintro (⟨-, h⟩ | h)
        · exact h
        · exact app_mono_r _ _ _ _ (fun v h => ((srefine v).mp h).1) v h
    cases ps with
    | nil =>
      -- the domain of the arrow covers the products: the return is refined
      obtain ⟨r, hr, run, s⟩ := ih' result refine products hres hrefine hps nep
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · unfold Elixir.Module.Types.Descr.«aux_apply/4»
        simp only [encP, List.map_cons, Term.list] at run ⊢
        simp [runs m hm, rrefine m hm]
        exact run m hm
      · rw [s, app]
        refine or_congr Iff.rfl ⟨Or.inr, ?_⟩
        rintro (⟨⟨x, hx, hn⟩, -⟩ | h)
        · exact absurd ((sps x).mpr (Or.inr ⟨hx, hn⟩)) (by simp [ProdSem])
        · exact h
    | cons q qs =>
      -- the products are split: the uncovered ones go on, and the return is refined on all of them
      have uncovered : ∀ x, ProdSem den (q :: qs) x ↔ ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x :=
        fun x => by rw [sps x]; simp [ProdSem]
      have hq : ∀ x ∈ q :: qs, ProdOk E den n x := fun x mx => ⟨by rw [(hps'' x mx).1, hlen], (hps'' x mx).2⟩
      obtain ⟨r₁, hr₁, run₁, s₁⟩ := ih' result rets (q :: qs) hres hrets hq (by simp)
      obtain ⟨r₂, hr₂, run₂, s₂⟩ := ih' r₁ refine products hr₁ hrefine hps nep
      obtain ⟨y₀, hy₀⟩ := prodSem_ne hq (by simp)
      have first : ∀ v, den r₁ v ↔ den result v ∨
          ((∃ x, ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) ∧
            FunSem.App (fun x => ProdSem den products x ∧ ¬FunSem.InDomR (args.map den) x) (den rets)
              (semP den rest) v) := fun v => by
        rw [s₁, app_congr_I uncovered]
        exact or_congr Iff.rfl ⟨fun h => ⟨⟨y₀, (uncovered y₀).mp hy₀⟩, h⟩, And.right⟩
      by_cases sb : ∀ v, den refine v → den r₁ v
      · refine ⟨r₁, hr₁, fun m hm => ?_, fun v => ?_⟩
        · have h := fe.sub hrefine hr₁ m hm
          have hb : bp (∀ v, den refine v → den r₁ v) = Bool.true := bp_true.mpr sb
          have r1 := run₁ m hm
          simp only [List.map_cons] at r1
          unfold Elixir.Module.Types.Descr.«aux_apply/4»
          simp only [encP, List.map_cons, Term.list] at r1 ⊢
          simp [runs m hm, rrefine m hm, r1, h, hb, isMember]
        · rw [first, app]
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rintro (h | h | h)
            · exact Or.inl h
            · exact Or.inr h
            · exact (first v).mp (sb v (app_sub_r _ _ _ v h))
      · refine ⟨r₂, hr₂, fun m hm => ?_, fun v => ?_⟩
        · have h := fe.sub hrefine hr₁ m hm
          have hb : bp (∀ v, den refine v → den r₁ v) = Bool.false := bp_false.mpr sb
          have r1 := run₁ m hm
          simp only [List.map_cons] at r1
          unfold Elixir.Module.Types.Descr.«aux_apply/4»
          simp only [encP, List.map_cons, Term.list] at r1 run₂ ⊢
          simp [runs m hm, rrefine m hm, r1, h, hb, isMember, run₂ m hm]
        · rw [s₂, first, app]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · rintro (h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr h

/-- Folds that unite into their accumulator, at every call depth from `K`. -/
theorem foldl1_or {W : Type} (K : Nat) (f : Term) (Inv : Term → Prop) (sem : Term → W → Prop) (G : Term → W → Prop) :
    ∀ l : List Term, (∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ (∀ m, K ≤ m → (D m).pure f #[x, a] = .ok a') ∧
      ∀ w, sem a' w ↔ sem a w ∨ G x w) →
      ∀ acc, Inv acc → ∃ r, Inv r ∧ (∀ m, K ≤ m → Erlang.lists.«foldl_1/3» (D m) f acc (Term.list l) = .ok r) ∧
        ∀ w, sem r w ↔ sem acc w ∨ ∃ x ∈ l, G x w := by
  intro l
  induction l with
  | nil => exact fun _ acc h => ⟨acc, h, fun m _ => by simp [Erlang.lists.«foldl_1/3»], fun w => by simp⟩
  | cons x xs ih =>
    intro step acc hacc
    obtain ⟨a', ha', run, s'⟩ := step x List.mem_cons_self acc hacc
    obtain ⟨r, hr, rest, s⟩ := ih (fun y my => step y (List.mem_cons_of_mem _ my)) a' ha'
    refine ⟨r, hr, fun m hm => ?_, fun w => ?_⟩
    · rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [run m hm, Lynx.Except.ok_bind]
      exact rest m hm
    · rw [s, s']
      constructor
      · rintro ((h | h) | ⟨y, my, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self, h⟩
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ my, h⟩
      · rintro (h | ⟨y, my, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp my with rfl | my
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨y, my, h⟩

theorem foldl_or {W : Type} (K : Nat) (mo nm : String) (caps : Array Term) (Inv : Term → Prop) (sem : Term → W → Prop)
    (G : Term → W → Prop) (l : List Term)
    (step : ∀ x ∈ l, ∀ a, Inv a → ∃ a', Inv a' ∧ (∀ m, K ≤ m → (D m).pure (.function false mo nm 2 caps) #[x, a] = .ok a') ∧
      ∀ w, sem a' w ↔ sem a w ∨ G x w) (acc : Term) (hacc : Inv acc) :
    ∃ r, Inv r ∧ (∀ m, K ≤ m →
      Erlang.lists.«foldl/3» (D m) (.function false mo nm 2 caps) acc (Term.list l) = .ok r) ∧
      ∀ w, sem r w ↔ sem acc w ∨ ∃ x ∈ l, G x w := by
  obtain ⟨r, hr, run, s⟩ := foldl1_or K _ Inv sem G l step acc hacc
  refine ⟨r, hr, fun m hm => ?_, s⟩
  have := run m hm
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using this
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at this
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using this

theorem enc_inj {a b a' b' : Term} {l l' : List Term}
    (e : Term.tuple #[a, Term.list l, b] = .tuple #[a', Term.list l', b']) : a = a' ∧ l = l' ∧ b = b' := by
  simp only [Term.tuple.injEq] at e
  have e₀ := congrArg (fun a : Array Term => a[0]?) e
  have e₁ := congrArg (fun a : Array Term => a[1]?) e
  have e₂ := congrArg (fun a : Array Term => a[2]?) e
  simp at e₀ e₁ e₂
  exact ⟨e₀, list_inj e₁, e₂⟩

/-- `fetch_domain/1` unites the domains of the positive arrows. -/
theorem fetch_domain_sem (fd : FunDom Dm E den dden K seen) (n : Nat) (P : List (Term × List Term × Term))
    (hP : PosOk E n P) :
    ∃ fdom, Dm fdom ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«fetch_domain/1» (D m) (encP P) = .ok fdom) ∧
      ∀ x, dden fdom x ↔ ∃ p ∈ semP den P, FunSem.InDomR p.1 x := by
  let G : Term → List V → Prop := fun t x => ∃ p ∈ P, t = .tuple #[p.1, Term.list p.2.1, p.2.2] ∧
    FunSem.InDomR (p.2.1.map den) x
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-fetch_domain/1-fun-0-" #[] Dm dden G
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (by
      intro t mt a ha
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs, -, -⟩ := hP p mp
      obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom p.2.1 hargs
      obtain ⟨u, hu, ru, su⟩ := fd.union ha hdom
      refine ⟨u, hu, fun m hm => ?_, fun x => ?_⟩
      · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fetch_domain/1-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-fetch_domain/1-fun-0-/2», rdom, ru m' hm']
      · rw [su, sdom]
        refine or_congr Iff.rfl ⟨fun h => ⟨p, mp, rfl, h⟩, fun ⟨q, mq, e, h⟩ => ?_⟩
        obtain ⟨-, el, -⟩ := enc_inj e
        rw [el]; exact h) (.map []) fd.none.1
  refine ⟨r, hr, fun m hm => by unfold Elixir.Module.Types.Descr.«fetch_domain/1»; exact run m hm, fun x => ?_⟩
  rw [s]
  simp only [fd.none.2, false_or, List.mem_map, semP, G]
  constructor
  · rintro ⟨_, ⟨p, mp, rfl⟩, q, mq, e, h⟩
    exact ⟨_, ⟨q, mq, rfl⟩, h⟩
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, p, mp, rfl, h⟩

/-- `fun_apply_static/2` applies the positive arrows to nonempty arguments. -/
theorem apply_static_sem (fe : FunElem E den K seen) (n : Nat) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (ne : ∀ a ∈ args, ∃ v, den a v) (len : args.length = n) (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ r, E r ∧ (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«fun_apply_static/2» (D m) (Term.list args) (Term.list [encP P]) = .ok r) ∧
      ∀ v, den r v ↔ FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den P) v := by
  let G : Term → V → Prop := fun t v => t = encP P ∧ FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den P) v
  have prod : ∀ x, ProdSem den [args] x ↔ FunSem.InDomR (args.map den) x := fun x => by simp [ProdSem]
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-fun_apply_static/2-fun-0-"
    #[Term.list args] E den G [encP P] (by
      intro t mt a ha
      rw [List.mem_singleton.mp mt]
      obtain ⟨r, hr, run, s⟩ := aux_apply_sem fe n P hP a (.atom "term") [args] ha fe.term.1
        (fun p mp => by
          rw [List.mem_singleton.mp mp]
          exact ⟨len, fun e me => ⟨hargs e me, ne e me⟩⟩) (by simp)
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_static/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-fun_apply_static/2-fun-0-/3»] using run m' hm'
      · rw [s, app_congr_I prod, app_congr_r _ (fun v => iff_true_intro (fe.term.2 v))]
        simp [G]) (.map []) fe.none.1
  refine ⟨r, hr, fun m hm => by unfold Elixir.Module.Types.Descr.«fun_apply_static/2»; simpa using run m hm,
    fun v => ?_⟩
  rw [s]
  simp [fe.none.2, G]

/-- `apply_disjoint/2` unites the returns of the positive arrows whose domain meets the arguments. -/
theorem apply_disjoint_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) (args : List Term)
    (hargs : ∀ a ∈ args, E a) (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ r, E r ∧ (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«apply_disjoint/2» (D m) (Term.list args) (encP P) = .ok r) ∧
      ∀ v, den r v ↔ ∃ p ∈ semP den P, (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR p.1 x) ∧ p.2 v := by
  obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom args hargs
  let G : Term → V → Prop := fun t v => ∃ p ∈ P, t = .tuple #[p.1, Term.list p.2.1, p.2.2] ∧
    (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x) ∧ den p.2.2 v
  have G_enc : ∀ p ∈ P, ∀ v, G (.tuple #[p.1, Term.list p.2.1, p.2.2]) v ↔
      (∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x) ∧ den p.2.2 v := by
    intro p mp v
    constructor
    · rintro ⟨q, mq, e, h⟩
      obtain ⟨-, el, er⟩ := enc_inj e
      rw [el, er]; exact h
    · exact fun h => ⟨p, mp, rfl, h⟩
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-apply_disjoint/2-fun-0-" #[dom] E den G
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (by
      intro t mt a ha
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs', hret', -⟩ := hP p mp
      obtain ⟨dom', hdom', rdom', sdom'⟩ := fd.dom p.2.1 hargs'
      obtain ⟨i, hi, ri, si⟩ := fd.inter hdom' hdom
      have ei := fd.empty1 hi
      obtain ⟨u, hu, ru, su⟩ := fe.union ha hret'
      by_cases meet : ∃ x, FunSem.InDomR (args.map den) x ∧ FunSem.InDomR (p.2.1.map den) x
      · have hb : bp (∀ x, ¬dden i x) = Bool.false := bp_false.mpr fun h => by
          obtain ⟨x, h₁, h₂⟩ := meet
          exact h x ((si x).mpr ⟨(sdom' x).mpr h₂, (sdom x).mpr h₁⟩)
        refine ⟨u, hu, fun m hm => ?_, fun v => ?_⟩
        · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
          simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm', ei m' hm', hb,
            isMember, ru m' hm']
        · rw [su, G_enc p mp]
          exact or_congr Iff.rfl ⟨fun h => ⟨meet, h⟩, fun h => h.2⟩
      · have hb : bp (∀ x, ¬dden i x) = Bool.true := bp_true.mpr fun x hx => by
          rw [si, sdom, sdom'] at hx
          exact meet ⟨x, hx.2, hx.1⟩
        refine ⟨a, ha, fun m hm => ?_, fun v => ?_⟩
        · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          rw [Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure]
          simp [Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», rdom', ri m' hm', ei m' hm', hb,
            isMember]
        · rw [G_enc p mp]
          exact ⟨Or.inl, fun h => h.elim id fun h => absurd h.1 meet⟩) (.map []) fe.none.1
  refine ⟨r, hr, fun m hm => by
    unfold Elixir.Module.Types.Descr.«apply_disjoint/2»; simp [rdom, encP, run m hm], fun v => ?_⟩
  rw [s]
  simp only [fe.none.2, false_or, List.mem_map, semP]
  constructor
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, (G_enc p mp v).mp h⟩
  · rintro ⟨_, ⟨p, mp, rfl⟩, h⟩
    exact ⟨_, ⟨p, mp, rfl⟩, (G_enc p mp v).mpr h⟩

/-- Arguments with no row are covered by the domains of the positive arrows. -/
theorem noRow_cover (P : List (FunSem.Arrow V)) (t : List (V → Prop)) (s : V → Prop)
    (h : FunSem.NoRow (t.map (false, ·)) (false, fun v => ¬s v) P) :
    ∀ x, FunSem.InDomR t x → ∃ p ∈ P, FunSem.InDomR p.1 x := by
  intro x hx
  apply Classical.byContradiction
  intro hn
  refine h (x.map some) none ((FunSem.inDom_args t _).mp ((FunSem.inDom_real t x).mpr hx)) rfl fun p mp hd => ?_
  exact absurd ⟨p, mp, (FunSem.inDom_real p.1 x).mp hd⟩ hn

/-- Arguments in disjoint domains, position by position. -/
def DisjDom (a b : FunSem.Arrow V) : Prop := ∀ x, FunSem.InDomR a.1 x → FunSem.InDomR b.1 x → False

theorem disjoint_args_sem (fe : FunElem E den K seen) : ∀ (l₁ l₂ : List Term), (∀ a ∈ l₁, E a) → (∀ a ∈ l₂, E a) →
    l₁.length = l₂.length → ∃ b : Bool,
      (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m) (Term.list l₁) (Term.list l₂) =
        .ok (boolAtom b)) ∧
      (b = Bool.true → ∀ x, FunSem.InDomR (l₁.map den) x → FunSem.InDomR (l₂.map den) x → False)
  | [], [], _, _, _ => ⟨Bool.false, fun m _ => by
      unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»; simp, by simp⟩
  | a :: l₁, b :: l₂, h₁, h₂, len => by
    obtain ⟨d, hd, sd⟩ := fe.disj (h₁ a List.mem_cons_self) (h₂ b List.mem_cons_self)
    obtain ⟨r, hr, sr⟩ := disjoint_args_sem fe l₁ l₂ (fun x m => h₁ x (List.mem_cons_of_mem _ m))
      (fun x m => h₂ x (List.mem_cons_of_mem _ m)) (by simpa using len)
    refine ⟨d || r, fun m hm => ?_, fun hb x hx hy => ?_⟩
    · unfold Elixir.Module.Types.Descr.«disjoint_arguments?/2»
      rw [hd m hm, hr m hm]
      cases d <;> cases r <;> simp [Lynx.Except.orElse, boolAtom]
    · cases x with
      | nil => exact hx.elim
      | cons v x =>
        obtain ⟨hv₁, hx₁⟩ := hx
        obtain ⟨hv₂, hx₂⟩ := hy
        rcases Bool.or_eq_true _ _ |>.mp hb with h | h
        · exact sd h v hv₁ hv₂
        · exact sr h x hx₁ hx₂
  | [], _ :: _, _, _, len => by simp at len
  | _ :: _, [], _, _, len => by simp at len

theorem all_disjoint_sem (fe : FunElem E den K seen) (n : Nat) : ∀ P : List (Term × List Term × Term), PosOk E n P →
    ∃ b : Bool, (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«all_disjoint_arguments?/1» (D m) (encP P) = .ok (boolAtom b)) ∧
      (b = Bool.true → List.Pairwise DisjDom (semP den P))
  | [], _ => ⟨Bool.true, fun m _ => by
      unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»; simp [encP, Term.list], fun _ => by simp [semP]⟩
  | p :: rest, hP => by
    obtain ⟨hargs, -, plen⟩ := hP p List.mem_cons_self
    have hrest : PosOk E n rest := fun q mq => hP q (List.mem_cons_of_mem _ mq)
    obtain ⟨b₂, r₂, s₂⟩ := all_disjoint_sem fe n rest hrest
    let res : Term → Bool := fun t => bp (∃ q ∈ rest, t = .tuple #[q.1, Term.list q.2.1, q.2.2] ∧
      ∃ b : Bool, b = Bool.true ∧ ∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m)
        (Term.list p.2.1) (Term.list q.2.1) = .ok (boolAtom b))
    have each : ∀ q ∈ rest, ∃ b : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint_arguments?/2» (D m)
        (Term.list p.2.1) (Term.list q.2.1) = .ok (boolAtom b)) ∧ res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = b ∧
        (b = Bool.true → DisjDom (p.2.1.map den, den p.2.2) (q.2.1.map den, den q.2.2)) := by
      intro q mq
      obtain ⟨hargs', -, qlen⟩ := hrest q mq
      obtain ⟨b, hb, sb⟩ := disjoint_args_sem fe p.2.1 q.2.1 hargs hargs' (by omega)
      refine ⟨b, hb, ?_, fun h x hx hy => sb h x hx hy⟩
      cases b
      · refine bp_false.mpr fun ⟨q', mq', e, b', hb', run⟩ => ?_
        obtain ⟨-, el, -⟩ := enc_inj e
        rw [← el] at run
        have := (run K (Nat.le_refl _)).symm.trans (hb K (Nat.le_refl _))
        subst hb'
        simp [boolAtom] at this
      · exact bp_true.mpr ⟨q, mq, rfl, Bool.true, rfl, hb⟩
    let b₁ := (rest.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).all res
    refine ⟨b₁ && b₂, fun m hm => ?_, fun hb => ?_⟩
    · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      have run₁ := all_list (D (m' + 1)) "Elixir.Module.Types.Descr" "-all_disjoint_arguments?/1-fun-0-"
        #[Term.list p.2.1] res (rest.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]) (by
          intro t mt
          obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
          obtain ⟨b, hb, rb, -⟩ := each q mq
          rw [Erlang.program.«Elixir.Module.Types.Descr:-all_disjoint_arguments?/1-fun-0-/1».pure, rb]
          simp only [Elixir.Module.Types.Descr.«-all_disjoint_arguments?/1-fun-0-/2»]
          exact hb m' hm')
      unfold Elixir.Module.Types.Descr.«all_disjoint_arguments?/1»
      simp only [encP, List.map_cons, Term.list] at run₁ r₂ ⊢
      simp only [pure_bind, run₁, r₂ (m' + 1) hm, andAlso_bool]; rfl
    · obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hb
      simp only [semP, List.map_cons, List.pairwise_cons]
      refine ⟨fun a ma => ?_, s₂ h₂⟩
      obtain ⟨q, mq, rfl⟩ := List.mem_map.mp ma
      obtain ⟨b, -, rb, sb⟩ := each q mq
      have : res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = Bool.true :=
        List.all_eq_true.mp h₁ _ (List.mem_map.mpr ⟨q, mq, rfl⟩)
      rw [rb] at this
      exact sb this

theorem nonempty_args_sem (fe : FunElem E den K seen) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (name : String) (lam : ∀ d a, (D (d + 1)).pure (.function false "Elixir.Module.Types.Descr" name 1 #[seen]) #[a] =
      (do let e ← Elixir.Module.Types.Descr.«empty_seen?/2» (D d) a seen; Erlang.erlang.«not/1» e))
    {m : Nat} (hm : K + 1 ≤ m) :
    Erlang.lists.«all/2» (D m) (.function false "Elixir.Module.Types.Descr" name 1 #[seen]) (Term.list args) =
      .ok (boolAtom (bp (∀ a ∈ args, ∃ v, den a v))) := by
  obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
  have run := all_list (D (m' + 1)) "Elixir.Module.Types.Descr" name #[seen] (fun a => !isEmpty den a) args
    (fun a ma => by
      rw [lam, fe.phi.empty (hargs a ma) m' hm']
      cases isEmpty den a <;> rfl)
  rw [run]
  congr 2
  cases h : args.all (fun a => !isEmpty den a)
  · symm; refine bp_false.mpr fun hall => ?_
    obtain ⟨a, ma, ha⟩ := List.all_eq_false.mp h
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at ha
    obtain ⟨v, hv⟩ := hall a ma
    exact absurd hv ((isEmpty_iff den a).mp (by simpa using ha) v)
  · symm; refine bp_true.mpr fun a ma => ?_
    have := List.all_eq_true.mp h a ma
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
    apply Classical.byContradiction
    intro hn
    have : isEmpty den a = Bool.true := (isEmpty_iff den a).mpr fun v hv => hn ⟨v, hv⟩
    simp_all

/-- `disjoint_non_empty_domains?/3` takes a shortcut only when the arguments are not empty, and the disjoint one
only when the domains of the positive arrows are disjoint. -/
theorem domains_sem (fe : FunElem E den K seen) (n : Nat) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (P : List (Term × List Term × Term)) (hP : PosOk E n P) :
    ∃ v, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3» (D m) (Term.list args) (encP P) seen = .ok v) ∧
      (v = .atom "nil" ∨ ((∀ a ∈ args, ∃ x, den a x) ∧
        (v = .atom "non_empty" ∨ (v = .atom "disjoint_non_empty" ∧ List.Pairwise DisjDom (semP den P))))) := by
  let a₁ := bp (∀ a ∈ args, ∃ v, den a v)
  have h₁ : ∀ m, K + 1 ≤ m → Erlang.lists.«all/2» (D m)
      (.function false "Elixir.Module.Types.Descr" "-disjoint_non_empty_domains?/3-fun-0-" 1 #[seen]) (Term.list args) =
      .ok (boolAtom a₁) := fun m hm => nonempty_args_sem fe args hargs _ (fun d a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-disjoint_non_empty_domains?/3-fun-0-/1».pure]; rfl) hm
  obtain ⟨a₂, h₂⟩ := all_uni (K + 2) "Elixir.Module.Types.Descr" "-all_non_empty_arguments?/2-fun-1-" #[seen]
    (P.map fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) (fun t mt => by
      obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      obtain ⟨hargs', -, -⟩ := hP p mp
      refine ⟨bp (∀ a ∈ p.2.1, ∃ v, den a v), fun m hm => ?_⟩
      obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      dsimp only
      rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-1-/1».pure]
      simp only [Elixir.Module.Types.Descr.«-all_non_empty_arguments?/2-fun-1-/2»]
      exact nonempty_args_sem fe p.2.1 hargs' _ (fun d a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-0-/1».pure]; rfl) (by omega))
  obtain ⟨dj, hdj, sdj⟩ := all_disjoint_sem fe n P hP
  refine ⟨if a₁ && a₂ then (if dj then .atom "disjoint_non_empty" else .atom "non_empty") else .atom "nil",
    fun m hm => ?_, ?_⟩
  · have e₁ := h₁ m (by omega)
    have e₂ := h₂ m hm
    have e₃ := hdj m (by omega)
    dsimp only at e₂
    unfold Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3»
    simp only [Elixir.Module.Types.Descr.«all_non_empty_arguments?/2», pure_bind, e₁, encP, e₂, andAlso_bool]
    simp only [encP] at e₃
    cases a₁ <;> cases a₂ <;> cases dj <;>
      simp [e₃, Lynx.Except.andAlso, Erlang.erlang.«/=/2», boolAtom]
  · by_cases ha : (a₁ && a₂) = Bool.true
    · have ne : ∀ a ∈ args, ∃ x, den a x := bp_true.mp (Bool.and_eq_true _ _ |>.mp ha).1
      rw [ite_eq_left ha]
      cases dj
      · exact Or.inr ⟨ne, Or.inl rfl⟩
      · exact Or.inr ⟨ne, Or.inr ⟨rfl, sdj rfl⟩⟩
    · have ha' : (a₁ && a₂) = Bool.false := by simpa using ha
      simp [ha']

/-- `phi_starter/4` decides whether the positive arrows are in the arrow from `args` to `ret`, when the domains of
the positive arrows cover the arguments: by `phi/5`, or by its shortcuts. -/
theorem phi_starter_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat) (args : List Term)
    (hargs : ∀ a ∈ args, E a) (len : args.length = n) {ret : Term} (hret : E ret) (P : List (Term × List Term × Term))
    (hP : PosOk E n P) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«phi_starter/4» (D m) (Term.list args) ret (encP P) seen = .ok (boolAtom b)) ∧
      ((∀ x, FunSem.InDomR (args.map den) x → ∃ p ∈ semP den P, FunSem.InDomR p.1 x) →
        (b = Bool.true ↔ FunSem.NoRow ((args.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den ret v) (semP den P))) := by
  obtain ⟨v, rv, hv⟩ := domains_sem fe n args hargs P hP
  have lP : ∀ p ∈ semP den P, p.1.length = ((args.map den).map (Bool.false, ·)).length := by
    intro p mp
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
    simp [(hP q mq).2.2, len]
  rcases hv with rfl | ⟨ne, rfl | ⟨rfl, disj⟩⟩
  · obtain ⟨neg, hneg, rneg, sneg⟩ := fe.neg hret
    have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function false "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" 1 #[])
        (Term.list args) = .ok (encA (args.map fun x => (Bool.false, x))) := fun m => by
      have := map_list (D m) "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" #[]
        (fun x => .tuple #[boolAtom Bool.false, x]) args fun x _ => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-phi_starter/4-fun-0-/1».pure]; rfl
      rw [this]; simp only [encA, List.map_map]; rfl
    obtain ⟨b, c, run, sb, -⟩ := phi_run fe.phi (m := K + 2) (by omega) P hP (args.map fun x => (Bool.false, x))
      (Bool.false, neg) (.map []) (by simpa using hargs) (by simpa using len) hneg (cacheOk_nil E den n)
    have dneg : den neg = fun v => ¬den ret v := funext fun v => propext (sneg v)
    have sem : FunSem.phiS (semA den (args.map fun x => (Bool.false, x))) (semR den (Bool.false, neg)) (semP den P) ↔
        FunSem.NoRow ((args.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den ret v) (semP den P) := by
      have e : semA den (args.map fun x => (Bool.false, x)) = (args.map den).map (Bool.false, ·) := by simp [semA]
      rw [e, semR, dneg]
      exact FunSem.phiS_iff _ _ _ lP
    refine ⟨b, fun m hm => ?_, fun _ => sb.trans sem⟩
    obtain ⟨b', c', run', sb', -⟩ := phi_run fe.phi (m := m) (by omega) P hP (args.map fun x => (Bool.false, x))
      (Bool.false, neg) (.map []) (by simpa using hargs) (by simpa using len) hneg (cacheOk_nil E den n)
    have bb : b' = b := by
      cases b <;> cases b' <;> simp_all
    subst bb
    unfold Elixir.Module.Types.Descr.«phi_starter/4»
    simp only [encR, boolAtom_false] at run'
    simp [rv m hm, margs, rneg m (by omega), run']
  · obtain ⟨w, hw⟩ := inDomR_exists (args.map den) fun t mt => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt; exact ne a ma
    obtain ⟨r, hr, ra, sr⟩ := apply_static_sem fe n args hargs ne len P hP
    refine ⟨bp (∀ v, den r v → den ret v), fun m hm => ?_, fun cover => ?_⟩
    · unfold Elixir.Module.Types.Descr.«phi_starter/4»
      simp [rv m hm, ra m (by omega), fe.sub hr hret m (by omega)]
    · rw [bp_true, FunSem.noRow_app _ _ _ w hw cover]
      exact forall_congr' fun v => imp_congr_left (sr v)
  · obtain ⟨w, hw⟩ := inDomR_exists (args.map den) fun t mt => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mt; exact ne a ma
    obtain ⟨r, hr, ra, sr⟩ := apply_disjoint_sem fe fd n args hargs P hP
    refine ⟨bp (∀ v, den r v → den ret v), fun m hm => ?_, fun cover => ?_⟩
    · unfold Elixir.Module.Types.Descr.«phi_starter/4»
      simp [rv m hm, ra m (by omega), fe.sub hr hret m (by omega)]
    · have dj : ∀ i j (hi : i < (semP den P).length) (hj : j < (semP den P).length), i ≠ j →
          ∀ x, FunSem.InDomR (semP den P)[i].1 x → ¬FunSem.InDomR (semP den P)[j].1 x := by
        intro i j hi hj ne x h₁ h₂
        have pw := List.pairwise_iff_getElem.mp disj
        rcases Nat.lt_or_gt_of_ne ne with lt | lt
        · exact pw i j hi hj lt x h₁ h₂
        · exact pw j i hj hi lt x h₂ h₁
      rw [bp_true, FunSem.noRow_app _ _ _ w hw cover,
        FunSem.app_disjoint _ _ ⟨w, hw⟩ dj cover]
      constructor
      · intro h p mp hx v hv
        exact h v ((sr v).mpr ⟨p, mp, hx, hv⟩)
      · intro h v hv
        obtain ⟨p, mp, hx, hp⟩ := (sr v).mp hv
        exact h p mp hx v hp

/-- The negative arrows a line of positive arrows `P` is contained in, as `phi` sees them. -/
def NegIn (_n : Nat) (den : Term → V → Prop) (P : List (Term × List Term × Term)) (q : Term × List Term × Term) : Prop :=
  FunSem.NoRow ((q.2.1.map den).map (Bool.false, ·)) (Bool.false, fun v => ¬den q.2.2 v) (semP den P)

/-- Lines with positive arrows: the line is empty exactly when some negative arrow contains the positive ones. -/
theorem fun_line_pos_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat)
    (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N) (ne : P ≠ []) :
    ∃ b : Bool, (∀ m, K + 3 ≤ m →
      Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N) seen = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ ∃ q ∈ N, NegIn n den P q) := by
  obtain ⟨fdom, hfdom, rfdom, sfdom⟩ := fetch_domain_sem fd n P hP
  let res : Term → Bool := fun t => bp (∃ q ∈ N, t = .tuple #[q.1, Term.list q.2.1, q.2.2] ∧ NegIn n den P q)
  have each : ∀ q ∈ N, res (.tuple #[q.1, Term.list q.2.1, q.2.2]) = bp (NegIn n den P q) ∧ ∀ m, K + 2 ≤ m →
      (Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3» (D m) (encP P) seen
        (.tuple #[q.1, Term.list q.2.1, q.2.2])) = .ok (boolAtom (bp (NegIn n den P q))) := by
    intro q mq
    refine ⟨bp_congr ⟨fun ⟨q', mq', e, h⟩ => ?_, fun h => ⟨q, mq, rfl, h⟩⟩, fun m hm => ?_⟩
    · obtain ⟨-, el, er⟩ := enc_inj e
      simp only [NegIn] at h ⊢
      rw [el, er]; exact h
    obtain ⟨hargs, hret, len⟩ := hN q mq
    obtain ⟨dom, hdom, rdom, sdom⟩ := fd.dom q.2.1 hargs
    obtain ⟨c, hc, rc, sc⟩ := fd.diff hdom hfdom
    obtain ⟨b, rb, sb⟩ := phi_starter_sem fe fd n q.2.1 hargs len hret P hP
    have cover : bp (∀ x, ¬dden c x) = Bool.true ↔
        ∀ x, FunSem.InDomR (q.2.1.map den) x → ∃ p ∈ semP den P, FunSem.InDomR p.1 x := by
      rw [bp_true]
      refine forall_congr' fun x => ?_
      rw [sc, sdom, sfdom]
      constructor
      · intro h hx; apply Classical.byContradiction; exact fun hn => h ⟨hx, hn⟩
      · exact fun h ⟨hx, hn⟩ => hn (h hx)
    simp only [Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3», rdom, rfdom m (by omega),
      Elixir.Module.Types.Descr.«subtype_seen?/3», rc m (by omega), fd.emptySeen hc m (by omega), rb m hm,
      Lynx.Except.ok_bind, andAlso_bool]
    congr 2
    cases hcv : bp (∀ x, ¬dden c x)
    · symm; refine bp_false.mpr fun h => ?_
      have := cover.mpr (noRow_cover _ _ _ h)
      rw [hcv] at this; cases this
    · have cv := cover.mp hcv
      cases hb : b
      · symm; exact bp_false.mpr fun h => by have := (sb cv).mpr h; rw [hb] at this; cases this
      · symm; exact bp_true.mpr ((sb cv).mp hb)
  have run : ∀ m, K + 3 ≤ m → Erlang.lists.«any/2» (D m)
      (.function false "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-1-" 1 #[encP P, seen])
      (Term.list (N.map fun q => .tuple #[q.1, Term.list q.2.1, q.2.2])) =
      .ok (boolAtom ((N.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).any res)) := fun m hm => by
    obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    refine any_list _ _ _ _ res _ fun t mt => ?_
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
    rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-1-/1».pure, (each q mq).2 m' hm',
      (each q mq).1]
  refine ⟨(N.map fun q => Term.tuple #[q.1, Term.list q.2.1, q.2.2]).any res, fun m hm => ?_, ?_⟩
  · obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil ne
    rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
    have r := run m hm
    simp only [encP, List.map_cons, Term.list] at r ⊢
    simp only [pure_bind]
    exact r
  · rw [List.any_eq_true]
    constructor
    · rintro ⟨t, mt, ht⟩
      obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
      rw [(each q mq).1, bp_true] at ht
      exact ⟨q, mq, ht⟩
    · rintro ⟨q, mq, h⟩
      exact ⟨_, List.mem_map.mpr ⟨q, mq, rfl⟩, by rw [(each q mq).1, bp_true]; exact h⟩

theorem lineEmpty_negIn (n : Nat) (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N)
    (ne : P ≠ []) : FunSem.LineEmpty n (semP den P) (semP den N) ↔ ∃ q ∈ N, NegIn n den P q := by
  have lP : ∀ p ∈ semP den P, p.1.length = n := by
    intro p mp
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
    simp [(hP q mq).2.2]
  rw [FunSem.lineEmpty_iff]
  constructor
  · rintro ⟨q', mq', h⟩
    obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mq'
    have lt : (q.2.1.map den).length = n := by simp [(hN q mq).2.2]
    refine ⟨q, mq, ?_⟩
    have := (FunSem.neg_iff_phi n _ (by simpa [semP] using ne) lP _ _ lt).mp h
    exact (FunSem.phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [(hN q mq).2.2])).mp this
  · rintro ⟨q, mq, h⟩
    have lt : (q.2.1.map den).length = n := by simp [(hN q mq).2.2]
    refine ⟨_, List.mem_map.mpr ⟨q, mq, rfl⟩, ?_⟩
    refine (FunSem.neg_iff_phi n _ (by simpa [semP] using ne) lP _ _ lt).mpr ?_
    exact (FunSem.phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [(hN q mq).2.2])).mpr h

/-- `fun_line_empty?/3` decides whether a line of arrows of arity `n` is empty, from call depth `K + 3`. -/
theorem fun_line_sem (fe : FunElem E den K seen) (fd : FunDom Dm E den dden K seen) (n : Nat)
    (P N : List (Term × List Term × Term)) (hP : PosOk E n P) (hN : PosOk E n N) :
    ∃ b : Bool, (∀ m, K + 3 ≤ m →
      Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N) seen = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ FunSem.LineEmpty n (semP den P) (semP den N)) := by
  by_cases ne : P ≠ []
  · obtain ⟨b, rb, sb⟩ := fun_line_pos_sem fe fd n P N hP hN ne
    exact ⟨b, rb, sb.trans (lineEmpty_negIn n P N hP hN ne).symm⟩
  simp only [ne_eq, Decidable.not_not] at ne
  subst ne
  cases N with
  | nil =>
    refine ⟨Bool.false, fun m _ => ?_, ?_⟩
    · rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]; simp [encP, Term.list]
    · simp only [semP, List.map_nil]
      exact ⟨fun h => (by cases h), fun h => absurd h (FunSem.lineEmpty_nil n)⟩
  | cons q qs =>
    obtain ⟨hargs, -, len⟩ := hN q List.mem_cons_self
    obtain ⟨kt, leaf⟩ := leaf_fun (q.2.1.map fun _ => .map [])
    let top : Term × List Term × Term := (.integer kt, q.2.1.map fun _ => .map [], .atom "term")
    have hT : PosOk E n [top] := fun t mt => by
      rw [List.mem_singleton.mp mt]
      exact ⟨fun a ma => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ma; exact fe.none.1, fe.term.1, by simp [top, len]⟩
    obtain ⟨b, rb, sb⟩ := fun_line_pos_sem fe fd n [top] (q :: qs) hT hN (by simp)
    have margs : ∀ m, Erlang.lists.«map/2» (D m) (.function false "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-0-" 1 #[])
        (Term.list q.2.1) = .ok (Term.list (q.2.1.map fun _ => .map [])) := fun m =>
      map_list (D m) _ _ _ _ _ fun x _ => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-0-/1».pure]; rfl
    have semT : semP den [top] = [FunSem.top n] := by
      simp only [semP, List.map_cons, List.map_nil, List.map_map, FunSem.top, top]
      have e₁ : (den ∘ fun _ : Term => Term.map []) = fun _ => fun _ => False :=
        funext fun _ => funext fun v => propext (iff_false_intro (fe.none.2 v))
      have e₂ : den (.atom "term") = fun _ => True := funext fun v => propext (iff_true_intro (fe.term.2 v))
      rw [e₁, e₂, List.map_const', len]
    refine ⟨b, fun m hm => ?_, ?_⟩
    · have r := rb m hm
      rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
      simp only [encP, List.map_cons, List.map_nil, Term.list, top] at r ⊢
      simp [margs, leaf]
      exact r
    · rw [sb, ← lineEmpty_negIn n [top] (q :: qs) hT hN (by simp), semT]
      simp only [semP, List.map_nil]
      exact (FunSem.lineEmpty_top n _).symm

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Function types hold function values: the valuation of arrows a function induces, and the emptiness of a BDD of
arrows of one arity. -/

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- The valuation of function literals that a function `g` induces, up to comparison: a literal holds when every
row of `g` is one its arrow allows. -/
noncomputable def valF (E : Term → Prop) (den : Term → V → Prop) (g : List (FunSem.Row V)) (t : Term) : Bool :=
  bp (∃ (k : Term) (args : List Term) (ret : Term), Term.compare (Term.fuel t (.tuple #[k, Term.list args, ret])) t (.tuple #[k, Term.list args, ret]) = .eq ∧
    (∀ a ∈ args, E a) ∧ E ret ∧ ∀ r ∈ g, FunSem.Allows (args.map den, den ret) r)

theorem valF_resp (g : List (FunSem.Row V)) : Resp (valF E den g) := by
  intro a b h
  simp only [valF]
  congr 1
  apply propext
  constructor
  · rintro ⟨k, args, ret, e, rest⟩; exact ⟨k, args, ret, Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨k, args, ret, e, rest⟩; exact ⟨k, args, ret, Lynx.Term.compare_eq_trans h e, rest⟩

theorem valF_iff (cg : DenCongr E den) (g : List (FunSem.Row V)) {k : Term} {args : List Term} {ret : Term}
    (hargs : ∀ a ∈ args, E a) (hret : E ret) :
    valF E den g (.tuple #[k, Term.list args, ret]) = Bool.true ↔ ∀ r ∈ g, FunSem.Allows (args.map den, den ret) r := by
  simp only [valF, bp_true]
  constructor
  · rintro ⟨k', args', ret', e, hargs', hret', h⟩
    obtain ⟨b₀, b₁, b₂, eq, -, e₁, e₂⟩ := tuple3_cmp e
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eq
    obtain ⟨-, rfl, rfl, -⟩ := eq
    rw [map_den_f2 cg hargs hargs' (list_cmp _ _ e₁), cg hret hret' e₂]
    exact h
  · exact fun h => ⟨k, args, ret, compare_self _, hargs, hret, h⟩

/-- Literals of arity `n` as `phi/5` and the line checks take them. -/
theorem lits_enc {n : Nat} : ∀ (pos : List Term), (∀ t ∈ pos, FunLit E n t) →
    ∃ P : List (Term × List Term × Term), pos = P.map (fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) ∧ PosOk E n P
  | [], _ => ⟨[], rfl, by simp [PosOk]⟩
  | t :: pos, h => by
    obtain ⟨k, args, ret, rfl, len, hargs, hret⟩ := h t List.mem_cons_self
    obtain ⟨P, rfl, hP⟩ := lits_enc pos fun u mu => h u (List.mem_cons_of_mem _ mu)
    refine ⟨(.integer k, args, ret) :: P, rfl, fun p mp => ?_⟩
    rcases List.mem_cons.mp mp with rfl | mp
    · exact ⟨hargs, hret, by simp only; omega⟩
    · exact hP p mp

/-- A function satisfies a line exactly when the positive arrows allow its rows and no negative arrow does. -/
theorem lineSat_valF (cg : DenCongr E den) (g : List (FunSem.Row V)) {n : Nat} (P N : List (Term × List Term × Term))
    (hP : PosOk E n P) (hN : PosOk E n N) :
    LineSat (valF E den g) (.tuple #[encP P, encP N]) ↔
      (∀ p ∈ semP den P, ∀ r ∈ g, FunSem.Allows p r) ∧ ∀ q ∈ semP den N, ¬∀ r ∈ g, FunSem.Allows q r := by
  constructor
  · rintro ⟨pos, negs, e, hp, hn⟩
    obtain ⟨el, er⟩ := line_inj e
    subst el; subst er
    refine ⟨fun p mp => ?_, fun q mq => ?_⟩
    · obtain ⟨p', mp', rfl⟩ := List.mem_map.mp mp
      exact (valF_iff cg g (hP p' mp').1 (hP p' mp').2.1).mp (hp _ (List.mem_map.mpr ⟨p', mp', rfl⟩))
    · obtain ⟨q', mq', rfl⟩ := List.mem_map.mp mq
      intro h
      have := hn _ (List.mem_map.mpr ⟨q', mq', rfl⟩)
      rw [(valF_iff cg g (hN q' mq').1 (hN q' mq').2.1).mpr h] at this
      cases this
  · rintro ⟨hp, hn⟩
    refine ⟨_, _, rfl, fun t mt => ?_, fun t mt => ?_⟩
    · obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      exact (valF_iff cg g (hP p mp).1 (hP p mp).2.1).mpr (hp _ (List.mem_map.mpr ⟨p, mp, rfl⟩))
    · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
      cases h : valF E den g (.tuple #[q.1, Term.list q.2.1, q.2.2])
      · rfl
      · exact absurd ((valF_iff cg g (hN q mq).1 (hN q mq).2.1).mp h) (hn _ (List.mem_map.mpr ⟨q, mq, rfl⟩))

/-- Lines of literals `L` of arity `n`, as `phi/5` and the line checks take them. -/
theorem lines_enc {n : Nat} {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t) : ∀ (lines : List Term),
    (∀ l ∈ lines, LineOk L l) → ∃ ls : List (List (Term × List Term × Term) × List (Term × List Term × Term)),
      lines = ls.map (fun l => .tuple #[encP l.1, encP l.2]) ∧
      ∀ l ∈ ls, PosOk E n l.1 ∧ PosOk E n l.2 ∧ (∀ p ∈ l.1, L (.tuple #[p.1, Term.list p.2.1, p.2.2])) ∧
        ∀ p ∈ l.2, L (.tuple #[p.1, Term.list p.2.1, p.2.2])
  | [], _ => ⟨[], rfl, by simp⟩
  | l :: lines, h => by
    obtain ⟨pos, negs, rfl, hp, hn⟩ := h l List.mem_cons_self
    obtain ⟨P, rfl, hP⟩ := lits_enc (E := E) pos fun t mt => hL t (hp t mt)
    obtain ⟨N, rfl, hN⟩ := lits_enc (E := E) negs fun t mt => hL t (hn t mt)
    obtain ⟨ls, rfl, hls⟩ := lines_enc hL lines fun l ml => h l (List.mem_cons_of_mem _ ml)
    refine ⟨(P, N) :: ls, rfl, fun l ml => ?_⟩
    rcases List.mem_cons.mp ml with rfl | ml
    · exact ⟨hP, hN, fun p mp => hp _ (List.mem_map.mpr ⟨p, mp, rfl⟩),
        fun p mp => hn _ (List.mem_map.mpr ⟨p, mp, rfl⟩)⟩
    · exact hls l ml

/-- A BDD of arrows of arity `n` holds no function of arity `n` exactly when each of its lines is empty. -/
theorem bdd_empty_lines (cg : DenCongr E den) {n : Nat} {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t) {b : Term}
    (wb : Bdd L b) :
    ∃ ls : List (List (Term × List Term × Term) × List (Term × List Term × Term)),
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list []) (Term.list []) (Term.list []) b =
        .ok (Term.list (ls.map (fun l => .tuple #[encP l.1, encP l.2]))) ∧
      (∀ l ∈ ls, PosOk E n l.1 ∧ PosOk E n l.2 ∧ (∀ p ∈ l.1, L (.tuple #[p.1, Term.list p.2.1, p.2.2])) ∧
        ∀ p ∈ l.2, L (.tuple #[p.1, Term.list p.2.1, p.2.2])) ∧
      ((∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → eval (valF E den g) b = Bool.false) ↔
        ∀ l ∈ ls, FunSem.LineEmpty n (semP den l.1) (semP den l.2)) := by
  obtain ⟨lines, run, hlines⟩ := dnf_lines wb L (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  obtain ⟨ls, rfl, hls⟩ := lines_enc (E := E) hL lines hlines
  obtain ⟨lines₁, run₁, sat⟩ := dnf_sat wb [] [] []
  obtain ⟨lines₂, run₂, -, cover⟩ := nl_dnf_cover wb [] [] []
  rw [run] at run₁ run₂
  have e₁ := list_inj (Except.ok.inj run₁)
  have e₂ := list_inj (Except.ok.inj run₂)
  rw [← e₁] at sat
  rw [← e₂] at cover
  refine ⟨ls, run, hls, ⟨fun h l ml g vg allP => ?_, fun h g vg => ?_⟩⟩
  · apply Classical.byContradiction
    intro hn
    simp only [not_exists, not_and] at hn
    have ls₁ : LineSat (valF E den g) (.tuple #[encP l.1, encP l.2]) :=
      (lineSat_valF cg g l.1 l.2 (hls l ml).1 (hls l ml).2.1).mpr ⟨allP, fun q mq hq => hn q mq hq⟩
    rcases sat _ (List.mem_map.mpr ⟨l, ml, rfl⟩) with m | sat
    · simp at m
    · have := (sat _ ls₁).2.2
      rw [h g vg] at this; cases this
  · cases he : eval (valF E den g) b
    · rfl
    · obtain ⟨t, mt, lt⟩ := cover _ (by simp) (by simp) he
      obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mt
      obtain ⟨allP, noN⟩ := (lineSat_valF cg g l.1 l.2 (hls l ml).1 (hls l ml).2.1).mp lt
      obtain ⟨q, mq, hq⟩ := h l ml g vg allP
      exact absurd hq (noN q mq)

theorem encP_inj : ∀ {P P' : List (Term × List Term × Term)}, encP P = encP P' → P = P'
  | [], [], _ => rfl
  | p :: P, p' :: P', h => by
    simp only [encP, List.map_cons, Term.list, Term.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨e₁, e₂, e₃⟩ := enc_inj h₁
    rw [encP_inj (P := P) (P' := P') h₂]
    obtain ⟨a, b, c⟩ := p
    obtain ⟨a', b', c'⟩ := p'
    simp_all
  | [], _ :: _, h => by simp [encP, Term.list] at h
  | _ :: _, [], h => by simp [encP, Term.list] at h

theorem lookup_entry {R : List (Term × Term)} {q b : Term} (h : mapLookup R q = some b) :
    ∃ e ∈ mapEntries R, compareExact (fuel q e.1) q e.1 = .eq ∧ e.2 = b := by
  rw [← mapLookup_mapEntries] at h
  simp only [mapLookup, Option.map_eq_some_iff, equalExact_eq_decide] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩

/-- `fun_empty?/2` on a union of arities: no function of any arity is in it, when the seen set does not hold its
BDDs and the lines of each BDD are decided under the seen set with that BDD, from call depth `K`. -/
theorem fun_union_sem (cg : DenCongr E den) {K : Nat} (R S : List (Term × Term)) (L : Term → Nat → Term → Prop)
    (hL : ∀ b n t, L b n t → FunLit E n t)
    (hR : ∀ e ∈ mapEntries R, ∃ n : Nat, e.1 = .integer n ∧ Bdd (L e.2 n) e.2)
    (fresh : ∀ e ∈ mapEntries R, S.any (fun s => decide (Term.compareExact (Term.fuel (.cons e.1 e.2) s.1) (.cons e.1 e.2) s.1 = .eq)) = Bool.false)
    (lines : ∀ e ∈ mapEntries R, ∀ n : Nat, e.1 = .integer n → ∀ P N, PosOk E n P → PosOk E n N →
      (∀ p ∈ P, L e.2 n (.tuple #[p.1, Term.list p.2.1, p.2.2])) →
      (∀ p ∈ N, L e.2 n (.tuple #[p.1, Term.list p.2.1, p.2.2])) →
      ∃ b : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N)
        (.map ((.cons e.1 e.2, .atom "true") :: S)) = .ok (boolAtom b)) ∧
        (b = Bool.true ↔ FunSem.LineEmpty n (semP den P) (semP den N))) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«fun_empty?/2» (D m) (.tuple #[.atom "union", .map R]) (.map S) = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ ∀ (n : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow n r) →
        evalR R (.integer n) (valF E den g) = Bool.false) := by
  -- What each entry answers.
  let ES : Term × Term → Prop := fun e => ∀ (n : Nat), e.1 = .integer n → ∀ g : List (FunSem.Row V),
    (∀ r ∈ g, FunSem.ValidRow n r) → eval (valF E den g) e.2 = Bool.false
  let res : Term → Bool := fun t => bp (∃ e ∈ mapEntries R, t = .tuple #[e.1, e.2] ∧ ES e)
  have each : ∀ e ∈ mapEntries R, res (.tuple #[e.1, e.2]) = bp (ES e) ∧ ∀ m, K + 2 ≤ m →
      (D m).pure (.function false "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-1-" 1 #[.map S]) #[.tuple #[e.1, e.2]] =
        .ok (boolAtom (bp (ES e))) := by
    intro e me
    refine ⟨bp_congr ⟨fun ⟨e', me', h, es⟩ => ?_, fun h => ⟨e, me, rfl, h⟩⟩, fun m hm => ?_⟩
    · have h₀ := congrArg (fun a : Term => match a with | .tuple ⟨[x, _]⟩ => x | _ => .nil) h
      have h₁ := congrArg (fun a : Term => match a with | .tuple ⟨[_, y]⟩ => y | _ => .nil) h
      simp only at h₀ h₁
      intro n hn g vg
      rw [h₁]; exact es n (h₀ ▸ hn) g vg
    obtain ⟨n, hn, wb⟩ := hR e me
    obtain ⟨ls, dnf, hls, sem⟩ := bdd_empty_lines (E := E) cg (hL e.2 n) wb
    have ES_iff : ES e ↔ ∀ l ∈ ls, FunSem.LineEmpty n (semP den l.1) (semP den l.2) := by
      rw [← sem]
      constructor
      · exact fun h => h n hn
      · intro h n' hn' g vg
        rw [hn] at hn'
        simp only [Term.integer.injEq] at hn'
        obtain rfl : n' = n := by omega
        exact h g vg
    let resL : Term → Bool := fun t => bp (∃ l ∈ ls, t = .tuple #[encP l.1, encP l.2] ∧
      FunSem.LineEmpty n (semP den l.1) (semP den l.2))
    obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    have all := all_list (D m') "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-0-"
      #[.map ((.cons e.1 e.2, .atom "true") :: S)] resL (ls.map fun l => .tuple #[encP l.1, encP l.2]) (by
        intro t mt
        obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mt
        obtain ⟨hP, hN, LP, LN⟩ := hls l ml
        obtain ⟨b, rb, sb⟩ := lines e me n hn l.1 l.2 hP hN LP LN
        obtain ⟨m'', rfl, hm''⟩ := succ_of_le hm'
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-0-/1».pure]
        simp only [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-0-/2»]
        rw [rb m'' hm'']
        congr 2
        cases b
        · symm; refine bp_false.mpr fun ⟨l', ml', e', h⟩ => ?_
          have e'' := congrArg (fun a : Term => match a with | .tuple ⟨[x, y]⟩ => (x, y) | _ => (.nil, .nil)) e'
          simp only [Prod.mk.injEq] at e''
          rw [← encP_inj e''.1, ← encP_inj e''.2] at h
          exact absurd (sb.mpr h) (by simp)
        · symm; exact bp_true.mpr ⟨l, ml, rfl, sb.mp rfl⟩)
    have allIff : (ls.map fun l => Term.tuple #[encP l.1, encP l.2]).all resL = bp (ES e) := by
      rw [bp_congr ES_iff]
      cases h : (ls.map fun l => Term.tuple #[encP l.1, encP l.2]).all resL
      · symm; refine bp_false.mpr fun hall => ?_
        obtain ⟨t, mt, ht⟩ := List.all_eq_false.mp h
        obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mt
        have : resL (.tuple #[encP l.1, encP l.2]) = Bool.true := bp_true.mpr ⟨l, ml, rfl, hall l ml⟩
        simp_all
      · symm; refine bp_true.mpr fun l ml => ?_
        have := List.all_eq_true.mp h _ (List.mem_map.mpr ⟨l, ml, rfl⟩)
        obtain ⟨l', ml', e', h'⟩ := bp_true.mp this
        have e'' := congrArg (fun a : Term => match a with | .tuple ⟨[x, y]⟩ => (x, y) | _ => (.nil, .nil)) e'
        simp only [Prod.mk.injEq] at e''
        rw [encP_inj e''.1, encP_inj e''.2]; exact h'
    simp only [Term.list] at dnf
    rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-1-/1».pure]
    simp [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-1-/2», Elixir.Module.Types.Descr.«empty_bdd_seen_key/2»,
      Erlang.erlang.«is_map_key/2», fresh e me, Term.false, Erlang.maps.«put/3»,
      Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf, all, allIff]
  have run : ∀ m, K + 2 ≤ m → Erlang.lists.«all/2» (D m)
      (.function false "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-1-" 1 #[.map S])
      (Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2])) =
      .ok (boolAtom (((mapEntries R).map fun e => Term.tuple #[e.1, e.2]).all res)) := fun m hm =>
    all_list _ _ _ _ res _ fun t mt => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mt
      rw [(each e me).2 m hm, (each e me).1]
  refine ⟨((mapEntries R).map fun e => Term.tuple #[e.1, e.2]).all res, fun m hm => ?_, ?_⟩
  · unfold Elixir.Module.Types.Descr.«fun_empty?/2»
    simpa [Erlang.maps.«to_list/1»] using run m hm
  · rw [List.all_eq_true]
    constructor
    · intro h n g vg
      cases hl : mapLookup R (.integer n) with
      | none => simp [evalR, hl]
      | some b =>
        obtain ⟨e, me, ek, rfl⟩ := lookup_entry hl
        have := h _ (List.mem_map.mpr ⟨e, me, rfl⟩)
        rw [(each e me).1, bp_true] at this
        simp only [evalR, hl, Option.elim]
        exact this n ((integer_compareExact_eq n e.1).mp ek) g vg
    · intro h t mt
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mt
      rw [(each e me).1, bp_true]
      intro n hn g vg
      have := h n g vg
      simp only [evalR, ← hn, mapLookup_of_mem_mapEntries me, Option.elim] at this
      exact this

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types hold only the top function type in their function fields. -/

def funTopT : Term := .tuple #[.atom "negation", .map []]

def FunTop (x : Term) : Prop := x = funTopT

theorem fun_top_inter (n : Nat) :
    Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom "fun") funTopT funTopT = .ok funTopT := by
  have mrun := merge_with_eq (D (n + 1)) "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] []
    (fun _ _ _ => .nil) (by intro e me; simp at me)
  simp only [mergeList, mapEntries_nil] at mrun
  simp [funTopT, Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2»,
    Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», mrun, Erlang.erlang.«==/2»]

theorem fun_top_diff (n : Nat) :
    Elixir.Module.Types.Descr.«bare_difference/3» (D n) (.atom "fun") funTopT funTopT = .ok (.integer 0) := by
  simp [funTopT, Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2»,
    Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»,
    Erlang.erlang.«==/2», Erlang.erlang.«map_size/1»]

theorem fun_top_ne (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«empty_key?/3» d (.atom "fun") funTopT S = .ok (.atom "false") := by
  simp [funTopT, Elixir.Module.Types.Descr.«empty_key?/3», Elixir.Module.Types.Descr.«fun_empty?/2»]

theorem funF_top : FunF funTopT := ⟨Bool.false, [], rfl, fun q v h => by simp [mapLookup] at h⟩

theorem lh_funTop : lh funTopT = 0 := by
  have := lh_nil_map
  simp [funTopT, lh] at this ⊢
  exact this

theorem dn_funTop (p : Point) : dn "fun" (some funTopT) p = Bool.true := by
  simp [dn, funTopT, arityOf, mapLookup]

theorem funTopC {K : Nat} {FV : Term → (Term → Bool) → Prop} (hK : 1 ≤ K) (wit : ∃ a ρ, Resp ρ ∧ FV a ρ) :
    FunC K FunTop FV (fun _ => True) True where
  funF := fun h => h ▸ funF_top
  union := fun {x y} hx hy m w hm run => by
    subst hx; subst hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [funTopT, fun_top_union] at run
    cases run
    exact ⟨rfl, fun _ => by rw [← funTopT, lh_funTop]; simp⟩
  inter := fun {x y} hx hy m w hm run _ => by
    subst hx; subst hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [fun_top_inter] at run
    cases run
    exact ⟨rfl, fun _ => by simp [lh_funTop]⟩
  diff := fun {x y} hx hy m w hm run k => by
    subst hx; subst hy
    rw [fun_top_diff] at run
    cases run
    simp [kept] at k
  empty := fun {x} S {m} hx _ _ => by
    subst hx
    refine ⟨fun N _ _ h => ?_, fun _ => ⟨Bool.false, by simpa [boolAtom] using fun_top_ne (D m) (.map S),
      fun _ _ _ h => by cases h⟩⟩
    obtain ⟨a, ρ, r, f⟩ := wit
    have := h (0, a, ρ) r f
    rw [dn_funTop] at this
    cases this

/-! Element types are nested types of the plain laws, below their height. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem tfield_nest {x : Term} (fx : TField E x) {N : Nat} (h : lh x < N) : OField (TupleOk (EB E N)) x := by
  rcases fx with top | wx
  · exact Or.inl top
  refine Or.inr ((bdd_lh_le wx (fun _ h => h) (lh x) (Nat.le_refl _)).mono fun t ⟨ht, le⟩ => ?_)
  obtain ⟨-, below⟩ := tlit_lh ht
  obtain ⟨⟨⟨k, tag, l, rfl, g, els⟩, nt⟩, -⟩ := ht
  exact ⟨⟨k, tag, l, rfl, g, fun e me => ⟨els e me, by have := (below k tag l rfl e me).1; omega⟩⟩, nt⟩

theorem mfield_nest {x : Term} (fx : MField E x) {N : Nat} (h : lh x < N) : OField (MapOk (EB E N)) x := by
  rcases fx with top | wx
  · exact Or.inl top
  refine Or.inr ((mbdd_lh_le wx (fun _ h => h) (lh x) (Nat.le_refl _)).mono fun t ⟨ht, le⟩ => ?_)
  obtain ⟨-, below⟩ := mlit_lh ht
  obtain ⟨⟨k, tag, l, rfl, g, ⟨fs, -⟩⟩, nt, -⟩ := ht
  obtain ⟨bf, bd⟩ := below k tag l rfl
  refine ⟨⟨k, tag, l, rfl, ?_, fun e me => ?_⟩, nt⟩
  · rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
    · exact MapTag.atom_open
    · exact MapTag.atom_closed
    · refine Or.inr (Or.inr ⟨dl, rfl, fun e me => ⟨(dv.1 e me).2, ?_⟩⟩)
      have := bd e (by rw [domFields_fieldsTerm]; exact me); omega
  · obtain ⟨u, o, eu, hu⟩ := (fs e me).2
    exact ⟨u, o, eu, hu, by have := bf e me u o eu; omega⟩

theorem lf_nest (ef : EF nd E V den tl K) {x : Term} (fx : LF E x) {N : Nat} (hN : 0 < N) (h : lh x < N) :
    Bdd (LLit (EB E N)) x := by
  refine (nl_lit_le ef fx (fun _ h => h) (max (lh x) 1) (by omega) (fun _ => by omega)).mono fun t ⟨ht, le⟩ => ?_
  obtain ⟨k, a, b, rfl, ha, hb⟩ := ht
  rw [litH_eq] at le
  exact ⟨k, a, b, rfl, ⟨ha, by omega⟩, ⟨hb, by omega⟩⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Function types of element types: arrows between element types, whose points are functions. -/

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- Literals of the BDD of the arity `q`: arrows with that many arguments, for arities that are natural numbers. -/
def FunArityN (E : Term → Prop) (q t : Term) : Prop := ∃ n : Nat, q = .integer n ∧ FunLit E n t

/-- Arities: maps whose keys are natural numbers. -/
def NatKeys (R : List (Term × Term)) : Prop := ∀ q, (mapLookup R q).isSome → ∃ n : Nat, q = .integer n

/-- Function types of element types: unions of some arities, or negations, of maps from arities to BDDs of arrows. -/
def FunA (E : Term → Prop) (x : Term) : Prop :=
  ∃ (pos : Bool) (R : List (Term × Term)), x = .tuple #[.atom (if pos then "union" else "negation"), .map R] ∧
    (pos = Bool.true → R ≠ []) ∧ AllBddP (FunArityN E) R ∧ NatKeys R

/-- Points of function types of element types: an arity and the valuation of arrows a function of that arity
induces. -/
def FVal (E : Term → Prop) (den : Term → V → Prop) (a : Term) (ρ : Term → Bool) : Prop :=
  ∃ (n : Nat) (g : List (FunSem.Row V)), a = .integer n ∧ (∀ r ∈ g, FunSem.ValidRow n r) ∧ ρ = valF E den g

theorem fVal_wit : ∃ a ρ, Resp ρ ∧ FVal E den a ρ :=
  ⟨.integer 0, valF E den [], valF_resp [], 0, [], rfl, by simp, rfl⟩

theorem FunA.funF {x : Term} (h : FunA E x) : FunF x :=
  let ⟨p, R, e, _, b, _⟩ := h
  ⟨p, R, e, fun q v h => (b q v h).mono fun _ _ => trivial⟩

theorem funA_top : FunA E funTopT :=
  ⟨Bool.false, [], rfl, by simp, fun q v h => by simp [mapLookup] at h, fun q h => by simp [mapLookup] at h⟩

theorem funLit_mono {E' : Term → Prop} (h : ∀ a, E a → E' a) {n : Int} {t : Term} (ht : FunLit E n t) :
    FunLit E' n t :=
  let ⟨k, args, ret, e, len, ha, hr⟩ := ht
  ⟨k, args, ret, e, len, fun a ma => h a (ha a ma), h ret hr⟩

/-! Heights of function literals and BDDs. -/

theorem lh_flit (k : Int) (args : List Term) (ret : Term) :
    lh (.tuple #[.integer k, Term.list args, ret]) = max (lh (Term.list args)) (lh ret) + 1 := by
  refine lh_leaf _ _ _ ?_ ?_ ?_ ?_
  · rintro ⟨h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨-, h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨r, a, h, -⟩; cases h

theorem flit_node_lh (h k : Int) (args : List Term) (ret c u d : Term) :
    lh (.tuple #[.integer h, .tuple #[.integer k, Term.list args, ret], c, u, d]) =
      max (lh (.tuple #[.integer k, Term.list args, ret])) (max (lh c) (max (lh u) (lh d))) := by
  refine lh_node_lit _ _ _ _ _ _ _ ?_ ?_ ?_
  · rintro ⟨h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨-, h, -⟩; cases args <;> simp [Term.list] at h
  · rintro ⟨r, a, h, -⟩; cases h

theorem lh_list_le : ∀ (l : List Term) {M : Nat}, (∀ a ∈ l, lh a ≤ M) → lh (Term.list l) ≤ M
  | [], _, _ => by simp [Term.list, lh]
  | a :: l, M, h => by
    simp only [Term.list, lh]
    have := lh_list_le l fun b mb => h b (List.mem_cons_of_mem _ mb)
    have := h a List.mem_cons_self
    omega

theorem le_lh_list : ∀ {l : List Term} {a : Term}, a ∈ l → lh a ≤ lh (Term.list l)
  | b :: l, a, m => by
    simp only [Term.list, lh]
    rcases List.mem_cons.mp m with rfl | m
    · omega
    · have := le_lh_list m; omega

/-- Function literals. -/
def FShape (t : Term) : Prop := ∃ (k : Int) (args : List Term) (ret : Term), t = .tuple #[.integer k, Term.list args, ret]

theorem FunLit.shape {n : Int} {t : Term} (h : FunLit E n t) : FShape t :=
  let ⟨k, args, ret, e, _⟩ := h
  ⟨k, args, ret, e⟩

/-- Literals of function BDDs are no higher than the BDD. -/
theorem fbdd_lh_le {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (lits : ∀ t, ok t → FShape t) :
    ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x := by
  revert lits
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → FShape t) → ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _ _ _; exact Bdd.top
  · intro _ _ _ _; exact Bdd.bot
  · intro ok k x y okl _ M le
    exact Bdd.leaf_iff.mpr ⟨okl, le⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd lits M le
    obtain ⟨k', args, ret, rfl⟩ := lits _ okl
    rw [flit_node_lh] at le
    have hlit : lh (.tuple #[.integer k', Term.list args, ret]) ≤ M := by omega
    have hc' : lh c ≤ M ∧ lh u ≤ M ∧ lh d ≤ M := by omega
    have lits' : ∀ t, Above ok (.tuple #[.integer k', Term.list args, ret]) t → FShape t := fun t ht => lits t ht.1
    obtain ⟨isLeaf, -⟩ := Bdd.node_iff.mp (show Bdd ok (.tuple #[.integer h, .tuple #[.integer k', Term.list args, ret], c, u, d])
      from Bdd.node_iff.mpr ⟨⟨_, _, _, rfl⟩, okl, hc, hu, hd⟩)
    refine Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, hlit⟩, ?_, ?_, ?_⟩
    · exact (ic lits' M hc'.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (iu lits' M hc'.2.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (idd lits' M hc'.2.2).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩

/-- Function BDDs whose literals are below a positive height are below it. -/
theorem fbdd_lh_bound {ok : Term → Prop} {r : Term} (wr : Bdd ok r) {M : Nat}
    (lits : ∀ t, ok t → FShape t ∧ lh t ≤ M) (top : 1 ≤ M) : lh r ≤ M := by
  revert lits top
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → FShape t ∧ lh t ≤ M) → 1 ≤ M → lh r ≤ M)
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ top; simpa [lh] using top
  · intro _ _ top; simpa [lh] using top
  · intro ok k x y okl lits _
    exact (lits _ okl).2
  · intro ok h lit c u d leaf okl _ _ _ ic iu idd lits one
    obtain ⟨⟨k', args, ret, rfl⟩, le⟩ := lits _ okl
    have lits' : ∀ t, Above ok (.tuple #[.integer k', Term.list args, ret]) t → FShape t ∧ lh t ≤ M :=
      fun t ht => lits t ht.1
    have hc := ic lits' one
    have hu := iu lits' one
    have hd := idd lits' one
    rw [flit_node_lh]
    omega

/-- Function BDDs have a height. -/
theorem fbdd_pos {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (lits : ∀ t, ok t → FShape t) :
    1 ≤ lh r := by
  revert lits
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → FShape t) → 1 ≤ lh r) ?_ ?_ ?_ ?_ ok r wr
  · intro _ _; simp [lh]
  · intro _ _; simp [lh]
  · intro ok k x y okl lits
    obtain ⟨k', args, ret, e⟩ := lits _ okl
    rw [e, lh_flit]; omega
  · intro ok h lit c u d leaf okl _ _ _ _ _ _ lits
    obtain ⟨k', args, ret, rfl⟩ := lits _ okl
    rw [flit_node_lh, lh_flit]; omega

/-! Plain operations on function types of element types. -/

/-- Literals of arity `q` below the height `L`. -/
abbrev FunArityL (E : Term → Prop) (L : Nat) (q t : Term) : Prop := FunArityN E q t ∧ lh t ≤ L

theorem lh_tag (p : Bool) (M : List (Term × Term)) :
    lh (.tuple #[.atom (if p then "union" else "negation"), .map M]) = lh (.map M) := by
  have : lh (.atom (if p then "union" else "negation")) = 0 := by cases p <;> simp [lh]
  simp [lh, this]

theorem lh_union (M : List (Term × Term)) : lh (.tuple #[.atom "union", .map M]) = lh (.map M) := lh_tag Bool.true M
theorem lh_negation (M : List (Term × Term)) : lh (.tuple #[.atom "negation", .map M]) = lh (.map M) :=
  lh_tag Bool.false M

theorem funArity_shape {q t : Term} (h : FunArityN E q t) : FShape t :=
  let ⟨_, _, lit⟩ := h
  FunLit.shape lit

theorem lookup_lh {R : List (Term × Term)} {q v : Term} (h : mapLookup R q = some v) : lh v ≤ lh (.map R) := by
  obtain ⟨e, me, -, rfl⟩ := lookup_entry h
  exact le_lh_map me

/-- Maps of BDDs of literals below a positive height are below it. -/
theorem allBdd_lh {R : List (Term × Term)} {L : Nat} (b : AllBddP (FunArityL E L) R) (one : 1 ≤ L) :
    lh (.map R) ≤ L :=
  lh_map_le.mpr fun _e me =>
    fbdd_lh_bound (b _ _ (mapLookup_of_mem_mapEntries me)) (fun _t ht => ⟨funArity_shape ht.1, ht.2⟩) one

theorem allBdd_bound {R : List (Term × Term)} (b : AllBddP (FunArityN E) R) {L : Nat} (le : lh (.map R) ≤ L) :
    AllBddP (FunArityL E L) R := fun q v h =>
  fbdd_lh_le (b q v h) (fun _ ht => funArity_shape ht) L (by have := lookup_lh h; omega)

theorem allBdd_unbound {R : List (Term × Term)} {L : Nat} (b : AllBddP (FunArityL E L) R) : AllBddP (FunArityN E) R :=
  fun q v h => (b q v h).mono fun _ ht => ht.1

/-- Function types of element types of height zero are the top function type. -/
theorem funA_lh0 {x : Term} (fx : FunA E x) (h : lh x = 0) : x = funTopT := by
  obtain ⟨p, R, rfl, ne, b, -⟩ := fx
  rw [lh_tag] at h
  have nil : R = [] := by
    cases R with
    | nil => rfl
    | cons e rest =>
      exfalso
      have hl : mapLookup (e :: rest) e.1 = some e.2 := by simp [mapLookup]
      have := lookup_lh hl
      have := fbdd_pos (b _ _ hl) (fun _ ht => funArity_shape ht)
      omega
  subst nil
  cases p
  · rfl
  · exact absurd rfl (ne rfl)

theorem funA_ne {R : List (Term × Term)} (h : R ≠ []) : ∃ a, (mapLookup R a).isSome := by
  cases R with
  | nil => exact absurd rfl h
  | cons e rest => exact ⟨e.1, by simp [mapLookup]⟩

theorem ne_of_some {M : List (Term × Term)} {a : Term} (h : (mapLookup M a).isSome) : M ≠ [] := by
  rintro rfl; simp [mapLookup] at h

/-- Function results whose unions have no arities become `0`. -/
theorem funA_result {pos : Bool} {M : List (Term × Term)} {L : Nat} (bM : AllBddP (FunArityL E L) M) (kM : NatKeys M)
    (one : 1 ≤ L)
    (e : Nat → Except Exception Term)
    (h₁ : pos = Bool.false → ∀ n, e n = .ok (.tuple #[.atom "negation", .map M]))
    (h₂ : pos = Bool.true → M = [] → ∀ n, e n = .ok (.integer 0))
    (h₃ : pos = Bool.true → M ≠ [] → ∀ n, e n = .ok (.tuple #[.atom "union", .map M])) :
    ∃ r, (∀ n, e n = .ok r) ∧ (kept (.atom "fun", r) = Bool.true → FunA E r ∧ lh r ≤ L) := by
  cases pos
  · exact ⟨_, h₁ rfl, fun _ => ⟨⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, kM⟩, by
      rw [lh_negation]; exact allBdd_lh bM one⟩⟩
  · by_cases hM : M = []
    · exact ⟨_, h₂ rfl hM, fun k => by simp [kept] at k⟩
    · exact ⟨_, h₃ rfl hM, fun _ => ⟨⟨Bool.true, M, rfl, fun _ => hM, allBdd_unbound bM, kM⟩, by
        rw [lh_union]; exact allBdd_lh bM one⟩⟩

theorem funA_bounded {x : Term} (fx : FunA E x) {L : Nat} (le : lh x ≤ L) :
    ∃ (p : Bool) (R : List (Term × Term)), x = .tuple #[.atom (if p then "union" else "negation"), .map R] ∧
      (p = Bool.true → R ≠ []) ∧ AllBddP (FunArityL E L) R ∧ NatKeys R := by
  obtain ⟨p, R, rfl, ne, b, k⟩ := fx
  rw [lh_tag] at le
  exact ⟨p, R, rfl, ne, allBdd_bound b le, k⟩

theorem natKeys_of {M R : List (Term × Term)} (k : NatKeys R) (h : ∀ a, (mapLookup M a).isSome → (mapLookup R a).isSome) :
    NatKeys M := fun q hq => k q (h q hq)

theorem natKeys_or {M R₁ R₂ : List (Term × Term)} (k₁ : NatKeys R₁) (k₂ : NatKeys R₂)
    (h : ∀ a, (mapLookup M a).isSome → (mapLookup R₁ a).isSome ∨ (mapLookup R₂ a).isSome) : NatKeys M :=
  fun q hq => (h q hq).elim (k₁ q) (k₂ q)

theorem funA_union {x y : Term} (fx : FunA E x) (fy : FunA E y) :
    ∃ w, (∀ n, Elixir.Module.Types.Descr.«bare_union/3» (D (n + 1)) (.atom "fun") x y = .ok w) ∧ FunA E w ∧
      lh w ≤ max (lh x) (lh y) := by
  by_cases z : max (lh x) (lh y) = 0
  · rw [funA_lh0 fx (by omega), funA_lh0 fy (by omega)]
    exact ⟨funTopT, fun n => fun_top_union n, funA_top, by rw [lh_funTop]; omega⟩
  have one : 1 ≤ max (lh x) (lh y) := by omega
  obtain ⟨p₁, R₁, rfl, n₁, b₁, k₁⟩ := funA_bounded fx (Nat.le_max_left _ (lh y))
  obtain ⟨p₂, R₂, rfl, n₂, b₂, k₂⟩ := funA_bounded fy (Nat.le_max_right (lh (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])) _)
  generalize max (lh (Term.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁]))
    (lh (Term.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂])) = L at one b₁ b₂ ⊢
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, keys⟩ := repr_inter_uniform b₁ b₂
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, natKeys_of k₁ keys⟩, by rw [lh_tag]; exact allBdd_lh bM one⟩
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₁ b₂
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, natKeys_of k₁ keys⟩, by rw [lh_tag]; exact allBdd_lh bM one⟩
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₂ b₁
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.false, M, rfl, by simp, allBdd_unbound bM, natKeys_of k₂ keys⟩, by rw [lh_tag]; exact allBdd_lh bM one⟩
  · obtain ⟨M, bM, run, keys, keys'⟩ := repr_union_uniform b₁ b₂
    obtain ⟨a, ha⟩ := funA_ne (n₁ rfl)
    exact ⟨_, fun n => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«fun_union/2», run],
      ⟨Bool.true, M, rfl, fun _ => ne_of_some (keys a ha), allBdd_unbound bM, natKeys_or k₁ k₂ keys'⟩,
      by rw [lh_tag]; exact allBdd_lh bM one⟩

theorem funA_inter {x y : Term} (fx : FunA E x) (fy : FunA E y) :
    ∃ w, (∀ n, Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom "fun") x y = .ok w) ∧
      (kept (.atom "fun", w) = Bool.true → FunA E w ∧ lh w ≤ max (lh x) (lh y)) := by
  by_cases z : max (lh x) (lh y) = 0
  · rw [funA_lh0 fx (by omega), funA_lh0 fy (by omega)]
    exact ⟨funTopT, fun n => fun_top_inter n, fun _ => ⟨funA_top, by rw [lh_funTop]; omega⟩⟩
  have one : 1 ≤ max (lh x) (lh y) := by omega
  obtain ⟨p₁, R₁, rfl, n₁, b₁, k₁⟩ := funA_bounded fx (Nat.le_max_left _ (lh y))
  obtain ⟨p₂, R₂, rfl, n₂, b₂, k₂⟩ := funA_bounded fy (Nat.le_max_right (lh (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])) _)
  generalize max (lh (Term.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁]))
    (lh (Term.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂])) = L at one b₁ b₂ ⊢
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, -, keys⟩ := repr_union_uniform b₁ b₂
    refine funA_result (pos := Bool.false) bM (natKeys_or k₁ k₂ keys) one _ (fun _ n => ?_) (fun h => by cases h) (fun h => by cases h)
    simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
      Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₂ b₁
    refine funA_result (pos := Bool.true) bM (natKeys_of k₂ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, keys⟩ := repr_inter_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]

theorem funA_diff {x y : Term} (fx : FunA E x) (fy : FunA E y) :
    ∃ w, (∀ n, Elixir.Module.Types.Descr.«bare_difference/3» (D (n + 1)) (.atom "fun") x y = .ok w) ∧
      (kept (.atom "fun", w) = Bool.true → FunA E w ∧ lh w ≤ max (lh x) (lh y)) := by
  by_cases z : max (lh x) (lh y) = 0
  · rw [funA_lh0 fx (by omega), funA_lh0 fy (by omega)]
    exact ⟨.integer 0, fun n => fun_top_diff (n + 1), fun k => by simp [kept] at k⟩
  have one : 1 ≤ max (lh x) (lh y) := by omega
  obtain ⟨p₁, R₁, rfl, n₁, b₁, k₁⟩ := funA_bounded fx (Nat.le_max_left _ (lh y))
  obtain ⟨p₂, R₂, rfl, n₂, b₂, k₂⟩ := funA_bounded fy (Nat.le_max_right (lh (.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁])) _)
  generalize max (lh (Term.tuple #[.atom (if p₁ then "union" else "negation"), .map R₁]))
    (lh (Term.tuple #[.atom (if p₂ then "union" else "negation"), .map R₂])) = L at one b₁ b₂ ⊢
  cases p₁ <;> cases p₂
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₂ b₁
    refine funA_result (pos := Bool.true) bM (natKeys_of k₂ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, -, keys⟩ := repr_union_uniform b₁ b₂
    refine funA_result (pos := Bool.false) bM (natKeys_or k₁ k₂ keys) one _ (fun _ n => ?_) (fun h => by cases h) (fun h => by cases h)
    simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
      Erlang.erlang.«==/2», Lynx.Except.andAlso]
  · obtain ⟨M, bM, run, keys⟩ := repr_inter_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]
  · obtain ⟨M, bM, run, keys⟩ := repr_diff_uniform b₁ b₂
    refine funA_result (pos := Bool.true) bM (natKeys_of k₁ keys) one _ (fun h => by cases h) (fun _ hM n => ?_) (fun _ hM n => ?_)
    · subst hM
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, Erlang.erlang.«map_size/1»]
    · obtain ⟨s, ne, sz⟩ := map_size_ne hM
      have : (s : Int) ≠ 0 := by omega
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», run,
        Erlang.erlang.«==/2», Lynx.Except.andAlso, sz, ne]

/-- Literals of arity `n` of the function BDD `b`, whose types are below `b`. -/
abbrev LitB (E : Term → Prop) (b : Term) (n : Nat) (t : Term) : Prop := FunLit (EB E (lh b)) n t

theorem litB_of {q b : Term} (wb : Bdd (FunArityN E q) b) {n : Nat} (hq : q = .integer n) : Bdd (LitB E b n) b := by
  refine (fbdd_lh_le wb (fun _ ht => funArity_shape ht) (lh b) (Nat.le_refl _)).mono fun t ⟨⟨n', e', lit⟩, le⟩ => ?_
  rw [hq] at e'
  simp only [Term.integer.injEq] at e'
  obtain rfl : n' = n := by omega
  obtain ⟨k, args, ret, rfl, len, ha, hr⟩ := lit
  rw [lh_flit] at le
  refine ⟨k, args, ret, rfl, len, fun a ma => ⟨ha a ma, ?_⟩, hr, ?_⟩
  · have := le_lh_list ma; omega
  · omega

/-- Function types of element types below a height are nested function types of element types below it. -/
theorem funA_ffield {x : Term} (fx : FunA E x) {N : Nat} (h : lh x < N) : FField (EB E N) x := by
  obtain ⟨p, R, rfl, -, bR, kR⟩ := fx
  refine ⟨p, R, rfl, fun q v hv => ?_⟩
  obtain ⟨n, hn⟩ := kR q (by rw [hv]; rfl)
  have le : lh v ≤ lh (.tuple #[.atom (if p then "union" else "negation"), .map R]) := by
    rw [lh_tag]; exact lookup_lh hv
  exact (litB_of (bR q v hv) hn).mono fun t ht =>
    ⟨n, hn, funLit_mono (fun a ha => ⟨ha.1, by have := ha.2; omega⟩) ht⟩


/-- The element types of the next level, below a height. -/
theorem descr_nest (ef : EF nd E V den tl K) {X : List (Term × Term)}
    (sX : DescrC (FunA E) (TField E) (LF E) (MField E) X) {N : Nat} (h : lh (.map X) < N) : NestFields (EB E N) X := by
  refine ⟨fun q hq => ?_, fun name w hw => ?_⟩
  · obtain ⟨name, m, rfl⟩ := sX.keys q hq
    simp [names] at m
    rcases m with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · have le := lh_field_le hw
    rcases sX.fields name w hw with ⟨rfl, b⟩ | ⟨rfl, a⟩ | ⟨rfl, f⟩ | ⟨rfl, l⟩ | ⟨rfl, t⟩ | ⟨rfl, m⟩
    · exact Or.inl ⟨by simp, by simp, by simp, by simp, Or.inl ⟨rfl, b⟩⟩
    · exact Or.inl ⟨by simp, by simp, by simp, by simp, Or.inr (Or.inl ⟨rfl, a⟩)⟩
    · exact Or.inr (Or.inl ⟨rfl, funA_ffield f (by omega)⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lf_nest ef l (by omega) (by omega)⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, tfield_nest t (by omega)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, mfield_nest m (by omega)⟩)))

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The top type and `:term` operands, for types over the structural kinds. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}

theorem topAt_fieldC (ks : Kinds K TF LF MF TV LV MV) (ftop : Fn funTopT) {name : String} {t : Term}
    (ht : TopAt name t) :
    FieldC Fn TF LF MF name t ∧ lh t = 0 ∧ ∀ p, PtOkC TV LV MV FV name p → dn name (some t) p = Bool.true := by
  have plain : name = "bitmap" ∨ name = "atom" ∨ name = "fun" →
      ∀ p, PtOkC TV LV MV FV name p → dn name (some t) p = Bool.true := fun h p ok =>
    (top_field (E := fun _ => True) ht).2.1 p ⟨ok.1, ok.2.1, fun e => by rcases h with rfl | rfl | rfl <;> simp at e⟩
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩
  · exact ⟨Or.inl ⟨rfl, 255, rfl, by decide, by decide⟩, lh_int _, plain (Or.inl rfl)⟩
  · refine ⟨Or.inr (Or.inl ⟨rfl, ⟨⟨Bool.false, [], rfl, no_atoms⟩, .nil, by simp [amemV, mapLookup]⟩⟩), ?_,
      plain (Or.inr (Or.inl rfl))⟩
    have := lh_nil_map
    simp [lh] at this ⊢; exact this
  · exact ⟨Or.inr (Or.inr (Or.inl ⟨rfl, ftop⟩)), lh_funTop, plain (Or.inr (Or.inr rfl))⟩
  · obtain ⟨f, l, d⟩ := ks.l.top t (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, e⟩))))
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, f⟩))), l, fun p ok => d p (ok.2.2.1 rfl)⟩
  · obtain ⟨f, l, d⟩ := ks.t.top t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, e⟩)))))
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, f⟩)))), l, fun p ok => d p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨f, l, d⟩ := ks.m.top t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, e⟩)))))
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, f⟩)))), l, fun p ok => d p (ok.2.2.2.2.1 rfl)⟩

/-- The unfolded top type holds every point, at no height. -/
theorem termC (ks : Kinds K TF LF MF TV LV MV) (ftop : Fn funTopT) :
    ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    DescrC Fn TF LF MF T ∧ T ≠ [] ∧ lh (.map T) = 0 ∧
    ∀ name ∈ names, ∀ p, PtOkC TV LV MV FV name p → dn name (mapLookup T (.atom name)) p = Bool.true := by
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  have keys : ∀ q, (mapLookup T q).isSome → ∃ name ∈ names, q = .atom name := fun q h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨name, m, e, -⟩ := term_top term ht
    exact ⟨name, m, e⟩
  have fields : ∀ name t, mapLookup T (.atom name) = some t → TopAt name t := fun name t h => by
    obtain ⟨name', -, e, ht⟩ := term_top term h
    simp only [Term.atom.injEq] at e
    subst e; exact ht
  refine ⟨T, term, ⟨keys, fun name t h => (topAt_fieldC (FV := FV) ks ftop (fields name t h)).1⟩, term_ne_nil term,
    Nat.le_zero.mp (lh_descr_le keys fun name t h => by rw [(topAt_fieldC (FV := FV) ks ftop (fields name t h)).2.1]; omega),
    fun name m p ok => ?_⟩
  obtain ⟨t, ht, top⟩ := term_at term m
  rw [ht]
  exact (topAt_fieldC ks ftop top).2.2 p ok

end

theorem diff_term_left (d : Dispatcher) {T B : List (Term × Term)}
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) (sT : mapLookup T (.atom "dynamic") = none)
    (sB : mapLookup B (.atom "dynamic") = none) (ne : B ≠ []) :
    Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") (.map B) =
      Elixir.Module.Types.Descr.«bare_difference/2» d (.map T) (.map B) := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sT, static_map sB, ne]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», ne, term]

theorem opt_diff_term_left (d : Dispatcher) {T B : List (Term × Term)} (S : Term)
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) (sT : mapLookup T (.atom "dynamic") = none)
    (sB : mapLookup B (.atom "dynamic") = none) (ne : B ≠ []) :
    Elixir.Module.Types.Descr.«opt_difference/3» d (.atom "term") (.map B) S =
      Elixir.Module.Types.Descr.«opt_difference/3» d (.map T) (.map B) S := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sT, static_map sB, ne]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», ne, term]

theorem opt_union_term_r (d : Dispatcher) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_union/3» d a (.atom "term") S = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»; split <;> simp_all

theorem opt_inter_term_r (d : Dispatcher) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_intersection/3» d a (.atom "term") S = .ok a := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/3»; split <;> simp_all

theorem fuse_term_l (d : Dispatcher) (b n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d (.atom "term") b n = .ok (.atom "nil") := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3»
  simp [Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1», getMapKeys]

theorem fuse_term_r (d : Dispatcher) (A : List (Term × Term)) (n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d (.map A) (.atom "term") n = .ok (.atom "nil") := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3»
  simp only [Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1», getMapKeys, equalExact_eq_decide]
  repeat' split
  all_goals simp_all [Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«map_size/1»]
  all_goals (repeat' split) <;> simp_all

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The element types of the next level: the top type and types over the structural kinds of element types. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem EF.funB (ef : EF nd E V den tl K) (N : Nat) : ElemFun (EB E N) K where
  static := fun ha => ef.static ha.1
  union := fun ha hb => let ⟨c, hc, run, _, h⟩ := ef.union ha.1 hb.1; ⟨c, ⟨hc, h N ha.2 hb.2⟩, run⟩
  sub := fun ha hb => let ⟨s, run, _⟩ := ef.sub ha.1 hb.1; ⟨s, run⟩
  disj := fun ha hb => let ⟨s, run, _⟩ := ef.disj ha.1 hb.1; ⟨s, run⟩

theorem EF.tailB (ef : EF nd E V den tl K) (N : Nat) : TailOk (EB E N) := fun _ he =>
  let ⟨e', run, he', _, hl⟩ := ef.tail he.1
  ⟨e', run, he', by have := he.2; omega⟩

/-- Types over function fields `Fn` and fields `TF`, `LF`, and `MF`. -/
def DEG (Fn TF LF MF : Term → Prop) (a : Term) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ DescrC Fn TF LF MF X

/-- Element types of the next level. -/
abbrev DE (E : Term → Prop) : Term → Prop := DEG (FunA E) (TField E) (LF E) (MField E)

/-- Points of types: a field name and a point valid there. -/
abbrev PtG (TV LV MV : (Term → Bool) → Prop) (FV : Term → (Term → Bool) → Prop) : Type :=
  {q : String × Point // q.1 ∈ names ∧ PtOkC TV LV MV FV q.1 q.2}

/-- Points of the next level. -/
abbrev PtOkD (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (FV : Term → (Term → Bool) → Prop)
    (name : String) (p : Point) : Prop :=
  PtOkC (ValT E den) (ValLN E den tl) (ValMN E den) FV name p

abbrev PtD (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (FV : Term → (Term → Bool) → Prop) : Type :=
  PtG (ValT E den) (ValLN E den tl) (ValMN E den) FV

section
variable {C : Nat → Term → Prop} {TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

def denD (a : Term) (q : PtG TV LV MV FV) : Prop :=
  a = .atom "term" ∨ ∃ X, a = .map X ∧ dn q.1.1 (mapLookup X (.atom q.1.1)) q.1.2 = Bool.true

def tlD (q : PtG TV LV MV FV) : Prop := q.1.1 = "list"

theorem denD_term (q : PtG TV LV MV FV) : denD (.atom "term") q := Or.inl rfl

theorem denD_map {X : List (Term × Term)} (q : PtG TV LV MV FV) :
    denD (.map X) q ↔ dn q.1.1 (mapLookup X (.atom q.1.1)) q.1.2 = Bool.true := by
  simp [denD]

end

theorem de_nest (ef : EF nd E V den tl K) {a : Term} (ha : DE E a) {N : Nat} (h : lh a < N) : NestC (EB E N) a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨X, rfl, descr_nest ef sX h⟩

/-- The plain operations on element types of the next level, below a height, at every call depth. -/
theorem nest_ops (ef : EF nd E V den tl K) (hnone : E (.map [])) {N : Nat} (hN : 0 < N) :
    ElemOk (NestC (EB E N)) (K + 8) ∧ ElemDiff (NestC (EB E N)) (K + 3) ∧ ElemFun (NestC (EB E N)) (K + 14) := by
  have none : EB E N (.map []) := ⟨hnone, by rw [lh_nil_map]; exact hN⟩
  have term : EB E N (.atom "term") := ⟨ef.term, by simp [lh]; exact hN⟩
  exact ⟨nestOk (ef.ops N hN) (ef.dops N) ((ef.jops N).mono (by omega)) (ef.funB N) none (ef.tailB N), nestDiff term K,
    nestFun (ef.ops N hN) (ef.dops N) ((ef.jops N).mono (by omega)) (ef.funB N) none (ef.tailB N)⟩

/-- Disjointness on element types of the next level, below a height, is a Boolean at every call depth. -/
theorem nest_disj (ef : EF nd E V den tl K) (hnone : E (.map [])) {N : Nat} (hN : 0 < N) :
    ElemDisj (NestC (EB E N)) (K + 8 + 3) :=
  nestDisj (ef.ops N hN) (ef.dops N) ((ef.jops N).mono (by omega)) (ef.funB N) ⟨hnone, by rw [lh_nil_map]; exact hN⟩
    (ef.tailB N)

theorem lh_term_zero : lh (.atom "term") = 0 := by simp [lh]

theorem fcOf (K : Nat) : FunC (K + 2) FunTop FVT (fun _ => True) True :=
  funTopC (by omega) ⟨.nil, fun _ => Bool.true, resp_const _, trivial⟩

/-- What the step to the next level needs: kinds of fields, function fields `Fn` whose points `FV` allows, holding
the top function type as their only fields of height zero, and the plain operations on a class `C N` of types
holding the types over those fields below each height `N`. -/
structure StepOk (nd : Term) (C : Nat → Term → Prop) (K : Nat) (Fn TF LF MF : Term → Prop)
    (TV LV MV : (Term → Bool) → Prop) (FV : Term → (Term → Bool) → Prop) : Prop where
  ks : Kinds (K + 2) TF LF MF TV LV MV
  fc : FunC (K + 2) Fn FV (fun _ => True) True
  ftop : Fn funTopT
  fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT
  fvw : ∃ a ρ, Resp ρ ∧ FV a ρ
  nest : ∀ {a N}, DEG Fn TF LF MF a → lh a < N → C N a
  ops : ∀ {N}, 0 < N → ElemOk (C N) (K + 8) ∧ ElemDiff (C N) (K + 3) ∧ ElemFun (C N) (K + 14)
  jops : ∀ {N}, 0 < N → ElemDisj (C N) (K + 11)
  tz : ∀ {x}, TF x → lh x = 0 → ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]
  lz : ∀ {x}, LF x → lh x = 0 → x = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  mz : ∀ {x}, MF x → lh x = 0 → ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]
  treal : ∀ (c : Bool) {x}, TF x → OField (PureLit nd) x → ∃ ρ, TV ρ ∧ denO x ρ = denO x (fun _ => c)

theorem tz_of {x : Term} (fx : TField E x) (z : lh x = 0) : ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil] := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, rfl⟩
  · have := tbdd_pos wx; omega

theorem mz_of {x : Term} (fx : MField E x) (z : lh x = 0) : ∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil] := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, rfl⟩
  · have := mbdd_pos wx; omega

theorem lz_of (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (z : lh x = 0) :
    x = .tuple #[.integer 46675407, .atom "term", .atom "term"] := by
  rcases wx.shape with rfl | rfl | ⟨k, a, c, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · simp [lh] at z
  · simp [lh] at z
  · obtain ⟨k', a', c', e, ha, hc⟩ := Bdd.leaf_iff.mp wx
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    by_cases nt : k = 46675407 ∧ a = .atom "term" ∧ c = .atom "term"
    · obtain ⟨rfl, rfl, rfl⟩ := nt; rfl
    · rw [nl_lh_leaf (ef.shape hc) nt] at z; omega
  · obtain ⟨-, okl, -⟩ := Bdd.node_iff.mp wx
    obtain ⟨k', a', c', rfl, ha', -⟩ := okl
    rw [nl_lh_node (ef.shape ha')] at z
    omega

/-- Tuple valuations of element types hold or leave out the expansion literal of the node, as wanted. -/
theorem treal_of (ef : EF nd E V den tl K) (c : Bool) {x : Term} (fx : TField E x) (px : OField (PureLit nd) x) :
    ∃ ρ, ValT E den ρ ∧ denO x ρ = denO x (fun _ => c) := by
  rcases pure_cases px with ⟨k, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c', u, d, he, rfl⟩
  · exact ⟨_, ⟨[], rfl⟩, by simp [denO_top]⟩
  · exact ⟨_, ⟨[], rfl⟩, rfl⟩
  · exact ⟨_, ⟨[], rfl⟩, rfl⟩
  · have hl : TLit E (litN e (keyOf nd)) := by
      rcases fx with ⟨k, h⟩ | wx
      · simp [litN, Term.list] at h
      · exact Bdd.leaf_iff.mp wx
    obtain ⟨⟨v₁, h₁⟩, ⟨v₀, h₀⟩⟩ := ef.litN_vals (litN_el hl) he (keyOf nd)
    cases c
    · exact ⟨_, ⟨v₀, rfl⟩, by simp [denO, isOpenTop, litN, Term.list] at h₀ ⊢; exact h₀⟩
    · exact ⟨_, ⟨v₁, rfl⟩, by simp [denO, isOpenTop, litN, Term.list] at h₁ ⊢; exact h₁⟩
  · have hl : TLit E (litN e (keyOf nd)) := by
      rcases fx with ⟨k, h⟩ | wx
      · simp at h
      · exact (Bdd.node_iff.mp wx).2.1
    obtain ⟨⟨v₁, h₁⟩, ⟨v₀, h₀⟩⟩ := ef.litN_vals (litN_el hl) he (keyOf nd)
    cases c
    · refine ⟨_, ⟨v₀, rfl⟩, ?_⟩
      simp only [litN, Term.list] at h₀
      cases c' <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list, h₀]
    · refine ⟨_, ⟨v₁, rfl⟩, ?_⟩
      simp only [litN, Term.list] at h₁
      cases c' <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list, h₁]

end

section
variable {nd : Term} {C : Nat → Term → Prop} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

/-- Unions of element types of the next level. -/
theorem de_union (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ c, DEG Fn TF LF MF c ∧ (∀ m, K + 14 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
      (∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∨ denD b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, fun m _ => union_term_l _ _, fun v => by simp [denD_term],
      fun N h _ => h⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, fun m _ => union_term_r _ _, fun v => by simp [denD_term],
      fun N _ h => h⟩
  have hN : 0 < max (lh (.map A)) (lh (.map B)) + 1 := by omega
  obtain ⟨c, -, run⟩ := (st.ops hN).2.2.union (st.nest (Or.inr ⟨A, rfl, sA⟩) (by omega))
    (st.nest (Or.inr ⟨B, rfl, sB⟩) (by omega))
  obtain ⟨U, run', sU, sem, le'⟩ := descr_union st.ks st.fc (m := K + 14) (by omega) sA sB
  have le := le' trivial
  have e := (run (K + 15) (by omega)).symm.trans run'
  simp only [Except.ok.injEq] at e
  subst e
  refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_, fun N h₁ h₂ => by omega⟩
  simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]

/-- Intersections of element types of the next level. -/
theorem de_inter (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ c, DEG Fn TF LF MF c ∧ (∀ m, K + 8 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
      (∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ denD b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, fun m _ => inter_term_left _ _, fun v => by simp [denD_term], fun N _ h => h⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, fun m _ => inter_term_right _ _, fun v => by simp [denD_term],
      fun N h _ => h⟩
  have hN : 0 < max (lh (.map A)) (lh (.map B)) + 1 := by omega
  obtain ⟨c, -, run⟩ := (st.ops hN).1.inter (st.nest (Or.inr ⟨A, rfl, sA⟩) (by omega))
    (st.nest (Or.inr ⟨B, rfl, sB⟩) (by omega))
  obtain ⟨U, run', sU, sem, le'⟩ := descr_inter st.ks st.fc (m := K + 8) (by omega) sA sB
  have le := le' trivial
  have e := (run (K + 9) (by omega)).symm.trans run'
  simp only [Except.ok.injEq] at e
  subst e
  refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_, fun N h₁ h₂ => by omega⟩
  simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]

theorem descrC_nil : DescrC Fn TF LF MF [] :=
  ⟨fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩

theorem lookup_out {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {name : String}
    (h : name ∉ names) : mapLookup X (.atom name) = none := by
  cases hx : mapLookup X (.atom name) with
  | none => rfl
  | some x =>
    obtain ⟨name', m, e⟩ := sX.keys _ (by rw [hx]; rfl)
    simp only [Term.atom.injEq] at e
    subst e; exact absurd m h

def ptWit : PtG TV LV MV FV := ⟨("atom", (0, .nil, fun _ => Bool.true)), by simp [names],
  ⟨resp_const _, by simp, by simp, by simp, by simp⟩⟩

theorem diff_none_right (d : Dispatcher) {a : Term} (ha : DEG Fn TF LF MF a) :
    Elixir.Module.Types.Descr.«bare_difference/2» d a (.map []) = .ok a := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]

/-- Differences of element types of the next level. -/
theorem de_diff (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ c, DEG Fn TF LF MF c ∧ (∀ m, K + 6 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
      (∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ ¬denD b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · refine ⟨_, Or.inr ⟨[], rfl, descrC_nil⟩, fun m _ => diff_term_right _ _, fun v => ?_,
      fun N _ _ => by rw [lh_nil_map]; omega⟩
    simp [denD_map, mapLookup, dn_none, denD_term]
  by_cases nB : B = []
  · subst nB
    exact ⟨a, ha, fun m _ => diff_none_right _ ha, fun v => by simp [denD_map, mapLookup, dn_none],
      fun N h _ => h⟩
  have hN : 0 < max (lh a) (lh (.map B)) + 1 := by omega
  obtain ⟨c, -, run⟩ := (st.ops hN).2.1.diff (st.nest ha (by omega))
    (st.nest (Or.inr ⟨B, rfl, sB⟩) (by omega))
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, lT, all⟩ := termC (FV := FV) st.ks st.ftop
    obtain ⟨U, run', sU, sem, le'⟩ := descr_diff st.ks st.fc (m := K + 4) (by omega) sT sB
    have le := le' trivial
    have e := (run (K + 6) (by omega)).symm.trans
      ((diff_term_left _ term sT.static sB.static nB).trans run')
    simp only [Except.ok.injEq] at e
    subst e
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, fun m hm => run m (by omega), fun v => ?_, fun N h₁ h₂ => by omega⟩
    simp only [denD_map, sem _ _ v.2.2, all _ v.2.1 _ v.2.2, denD_term, true_and, Bool.true_and,
      Bool.not_eq_true']
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run', sU, sem, le'⟩ := descr_diff st.ks st.fc (m := K + 4) (by omega) sA sB
    have le := le' trivial
    have e := (run (K + 6) (by omega)).symm.trans run'
    simp only [Except.ok.injEq] at e
    subst e
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, fun m hm => run m (by omega), fun v => ?_, fun N h₁ h₂ => by omega⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- Emptiness of element types of the next level, exact under safe seen sets. -/
theorem de_empty (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a : Term} (S : List (Term × Term)) (ha : DEG Fn TF LF MF a) :
    ∃ b : Bool, (∀ m, K + 8 ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh a < N → SafeN N S → (b = Bool.true ↔ ∀ v : PtG TV LV MV FV, ¬denD a v) := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · refine ⟨Bool.false, fun m _ => by simpa [boolAtom] using empty_term _ _, fun N _ _ => ?_⟩
    refine ⟨fun h => absurd h (by simp), fun h => absurd (denD_term ptWit) (h ptWit)⟩
  have hN : 0 < lh (.map X) + 1 := by omega
  obtain ⟨b, run⟩ := (st.ops hN).1.empty (st.nest (Or.inr ⟨X, rfl, sX⟩) (by omega)) S
  obtain ⟨b', run', ex⟩ := descr_empty st.ks st.fc trivial (m := K + 8) (by omega) sX S trivial
  have e := (run (K + 8) (by omega)).symm.trans run'
  have : b = b' := by cases b <;> cases b' <;> simp_all [boolAtom]
  subst this
  refine ⟨b, run, fun N hl hS => ?_⟩
  obtain ⟨comp, sound⟩ := ex N hl hS
  constructor
  · intro bt v hv
    have := sound bt v.1.1 v.1.2 v.2.2
    rw [denD_map, this] at hv
    cases hv
  · intro none
    refine comp fun name p ok => ?_
    by_cases m : name ∈ names
    · have := none ⟨(name, p), m, ok⟩
      simpa [denD] using this
    · rw [lookup_out sX m, dn_none]

theorem empty_map_seen (d : Dispatcher) (A : List (Term × Term)) :
    Elixir.Module.Types.Descr.«empty?/1» d (.map A) = Elixir.Module.Types.Descr.«empty_seen?/2» d (.map A) (.map []) := by
  unfold Elixir.Module.Types.Descr.«empty?/1»; rfl

theorem bool_run {r : Except Exception Term} {s b : Bool} (h₁ : r = .ok (boolAtom s)) (h₂ : r = .ok (boolAtom b)) :
    s = b := by
  have := h₁.symm.trans h₂
  cases s <;> cases b <;> simp_all [boolAtom]

/-- Optimized unions of element types of the next level. -/
theorem de_opt_union (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (S : List (Term × Term)) {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (hm : K + 4 ≤ m) : ∃ c, DEG Fn TF LF MF c ∧
      Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∨ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_left _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inl rfl, opt_union_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_union st.ks st.fc (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.or_eq_true]⟩

/-- Optimized intersections of element types of the next level. -/
theorem de_opt_inter (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (S : List (Term × Term)) {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (hm : K + 4 ≤ m) : ∃ c, DEG Fn TF LF MF c ∧
      Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ denD b v := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨b, hb, opt_inter_term_l _ _ _, fun v => by simp [denD_term]⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, Or.inr ⟨A, rfl, sA⟩, opt_inter_term_r _ _ _, fun v => by simp [denD_term]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨U, run, sU, sem⟩ := descr_opt_inter st.ks st.fc (m := n) (by omega) sA sB S
  exact ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => by simp only [denD_map, sem _ _ v.2.2, Bool.and_eq_true]⟩

/-- Optimized differences of element types of the next level. -/
theorem de_opt_diff (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (S : List (Term × Term)) {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (hm : K + 6 ≤ m) : ∃ c, DEG Fn TF LF MF c ∧
      Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧
      ∀ v : PtG TV LV MV FV, denD c v ↔ denD a v ∧ ¬denD b v := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · refine ⟨_, Or.inr ⟨[], rfl, descrC_nil⟩, difference_term_term _ _ _, fun v => ?_⟩
    simp [denD_map, mapLookup, dn_none, denD_term]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · by_cases nB : B = []
    · subst nB
      exact ⟨_, Or.inl rfl, difference_term_none _ _, fun v => by simp [denD_map, mapLookup, dn_none, denD_term]⟩
    obtain ⟨T, term, sT, -, -, all⟩ := termC (FV := FV) st.ks st.ftop
    obtain ⟨U, run, sU, sem⟩ := descr_opt_diff st.ks st.fc (m := n) (by omega) sT sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, (opt_diff_term_left _ _ term sT.static sB.static nB).trans run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2, all _ v.2.1 _ v.2.2, denD_term, true_and, Bool.true_and]
    cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp
  · obtain ⟨U, run, sU, sem⟩ := descr_opt_diff st.ks st.fc (m := n) (by omega) sA sB S
    refine ⟨_, Or.inr ⟨U, rfl, sU⟩, run, fun v => ?_⟩
    simp only [denD_map, sem _ _ v.2.2]
    cases dn v.1.1 (mapLookup A (.atom v.1.1)) v.1.2 <;> cases dn v.1.1 (mapLookup B (.atom v.1.1)) v.1.2 <;> simp

/-- Subtyping of element types of the next level: a uniform answer, sound. -/
theorem de_sub (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ s : Bool, (∀ m, K + 14 ≤ m → Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v : PtG TV LV MV FV, denD a v → denD b v) := by
  have hN : 0 < max (lh a) (lh b) + 1 := by omega
  obtain ⟨s, run⟩ := (st.ops hN).2.2.sub (st.nest ha (by omega)) (st.nest hb (by omega))
  refine ⟨s, run, fun st v hv => ?_⟩
  subst st
  have h : Elixir.Module.Types.Descr.«subtype?/2» (D (K + 14)) a b = .ok (boolAtom Bool.true) := run (K + 14) (by omega)
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact denD_term v
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, -, all⟩ := termC (FV := FV) st.ks st.ftop
    rw [subtype_term_l term] at h
    have := descr_sub_sound st.ks st.fc trivial trivial (by omega) sT sB h v.1.1 v.1.2 v.2.2
      (all _ v.2.1 _ v.2.2)
    exact (denD_map v).mpr this
  · exact (denD_map v).mpr (descr_sub_sound st.ks st.fc trivial trivial (by omega) sA sB h v.1.1 v.1.2 v.2.2
      ((denD_map v).mp hv))

theorem descr_incl {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A)
    (h : ∀ v : PtG TV LV MV FV, denD (.map A) v → denD (.map B) v) :
    ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup A (.atom name)) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true := by
  intro name p ok hx
  by_cases mn : name ∈ names
  · exact (denD_map ⟨(name, p), mn, ok⟩).mp (h _ ((denD_map _).mpr hx))
  · cases ha : mapLookup A (.atom name) with
    | none => rw [ha, dn_none] at hx; cases hx
    | some x =>
      obtain ⟨name', m', e⟩ := sA.keys _ (by rw [ha]; rfl)
      simp only [Term.atom.injEq] at e
      subst e; exact absurd m' mn

/-- Subtyping of element types of the next level is complete. -/
theorem de_subc (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (incl : ∀ v : PtG TV LV MV FV, denD a v → denD b v) {m : Nat} (hm : K + 14 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨T, term, sT, -, -, all⟩ := termC (FV := FV) st.ks st.ftop
  have toT : ∀ v : PtG TV LV MV FV, denD (.map T) v := fun v => (denD_map v).mpr (all _ v.2.1 _ v.2.2)
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [subtype_term_r term]
    rcases ha with rfl | ⟨A, rfl, sA⟩
    · rw [subtype_term_l term]
      exact descr_sub_complete st.ks st.fc trivial (by omega) sT sT fun _ _ _ h => h
    · exact descr_sub_complete st.ks st.fc trivial (by omega) sA sT (descr_incl sA fun v _ => toT v)
  · rcases ha with rfl | ⟨A, rfl, sA⟩
    · rw [subtype_term_l term]
      exact descr_sub_complete st.ks st.fc trivial (by omega) sT sB (descr_incl sT fun v _ => incl v (denD_term v))
    · exact descr_sub_complete st.ks st.fc trivial (by omega) sA sB (descr_incl sA incl)

theorem de_empty_sound (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {B : List (Term × Term)}
    (sB : DescrC Fn TF LF MF B) {m : Nat} (hm : K + 8 ≤ m)
    (h : Elixir.Module.Types.Descr.«empty?/1» (D m) (.map B) = .ok (boolAtom Bool.true)) :
    ∀ v : PtG TV LV MV FV, ¬denD (.map B) v := by
  obtain ⟨b, run, ex⟩ := de_empty st [] (Or.inr ⟨B, rfl, sB⟩)
  rw [empty_map_seen] at h
  have := bool_run (run m hm) h
  subst this
  exact (ex _ (Nat.lt_succ_self _) (safeN_nil _)).mp rfl

/-- Disjointness of element types of the next level: a uniform answer, sound. -/
theorem de_disj (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ s : Bool, (∀ m, K + 14 ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v : PtG TV LV MV FV, denD a v → denD b v → False) := by
  have hN : 0 < max (lh a) (lh b) + 1 := by omega
  obtain ⟨s, run⟩ := (st.ops hN).2.2.disj (st.nest ha (by omega)) (st.nest hb (by omega))
  refine ⟨s, run, fun st v hva hvb => ?_⟩
  subst st
  have h : Elixir.Module.Types.Descr.«disjoint?/2» (D (K + 14)) a b = .ok (boolAtom Bool.true) := run (K + 14) (by omega)
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [disjoint_term_l] at h
    rcases hb with rfl | ⟨B, rfl, sB⟩
    · rw [empty_term_false] at h; simp [boolAtom] at h
    · exact de_empty_sound st sB (by omega) h v hvb
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [disjoint_term_r] at h
    exact de_empty_sound st sA (by omega) h v hva
  have := descr_disj_sound st.ks st.fc trivial trivial (by omega) sA sB h v.1.1 v.1.2 v.2.2
  rw [(denD_map v).mp hva, (denD_map v).mp hvb] at this
  cases this

theorem de_resp (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {e e' : Term} {v : PtG TV LV MV FV} (he : DEG Fn TF LF MF e) (he' : DEG Fn TF LF MF e')
    (h : Term.compare (Term.fuel e e') e e' = .eq) (d : denD e' v) : denD e v := by
  rcases he with rfl | ⟨A, rfl, sA⟩
  · exact denD_term v
  rcases he' with rfl | ⟨B, rfl, sB⟩
  · obtain ⟨Y, e⟩ := map_cmp_shape h; cases e
  rw [denD_map] at d ⊢
  rw [descr_congr st.ks st.fc sA sB h v.1.1 v.1.2 v.2.2, d]

theorem noList_atom (M : List (Term × Term)) (name : String) :
    mapLookup (noList M) (.atom name) = if name = "list" then none else mapLookup M (.atom name) := by
  simp only [noList, mapLookup_remove, compareExact_eq_atom, Term.atom.injEq]

/-- Types without their list field. -/
theorem descr_noList {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) :
    DescrC Fn TF LF MF (noList X) ∧ lh (.map (noList X)) ≤ lh (.map X) ∧
      ∀ v : PtG TV LV MV FV, denD (.map (noList X)) v ↔ denD (.map X) v ∧ ¬tlD v := by
  have keys : ∀ q, (mapLookup (noList X) q).isSome → ∃ name ∈ names, q = .atom name := fun q h =>
    sX.keys q (by rw [← noList_lookup X q h]; exact h)
  refine ⟨⟨keys, fun name w h => ?_⟩, lh_descr_le keys fun name w h => ?_, fun v => ?_⟩
  · rw [noList_lookup X _ (by rw [h]; rfl)] at h; exact sX.fields name w h
  · rw [noList_lookup X _ (by rw [h]; rfl)] at h; exact lh_field_le h
  · rw [denD_map, denD_map, noList_atom]
    unfold tlD
    split <;> simp_all [dn_none]

theorem tailTerm_noList {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T))
    (name : String) : mapLookup tailTerm (.atom name) = mapLookup (noList T) (.atom name) := by
  simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at term
  cases term
  rw [noList_atom]
  simp only [mapLookup, List.find?, tailTerm, compareExact_eq_atom, Term.atom.injEq, equalExact_eq_decide]
  by_cases b : name = "bitmap" <;> by_cases t : name = "tuple" <;> by_cases f : name = "fun" <;>
    by_cases m : name = "map" <;> by_cases a : name = "atom" <;> by_cases l : name = "list" <;> simp_all

/-- `list_tail_unfold/1` of element types of the next level. -/
theorem de_tail (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {e : Term} (he : DEG Fn TF LF MF e) :
    ∃ e', (∀ d, Elixir.Module.Types.Descr.«list_tail_unfold/1» d e = .ok e') ∧ DEG Fn TF LF MF e' ∧
      (∀ v : PtG TV LV MV FV, denD e' v ↔ denD e v ∧ ¬tlD v) ∧ lh e' ≤ lh e := by
  rcases he with rfl | ⟨X, rfl, sX⟩
  · obtain ⟨T', run, look⟩ := tail_term_lookup
    obtain ⟨T, term, sT, -, lT, all⟩ := termC (FV := FV) st.ks st.ftop
    obtain ⟨sN, lN, semN⟩ := descr_noList (TV := TV) (LV := LV) (MV := MV) sT
    have eq : ∀ name, mapLookup T' (.atom name) = mapLookup (noList T) (.atom name) := fun name =>
      (look _).trans (tailTerm_noList term name)
    have keys : ∀ q, (mapLookup T' q).isSome → ∃ name ∈ names, q = .atom name := fun q h => by
      rw [look] at h
      rcases tailTerm_basic.keys q h with e | e | e | e | e | e <;> exact ⟨_, by simp [names], e⟩
    refine ⟨_, run, Or.inr ⟨T', rfl, keys, fun name w h => sN.fields name w (by rw [← eq]; exact h)⟩, fun v => ?_,
      lh_descr_le keys fun name w h => ?_⟩
    · rw [denD_map, eq, ← denD_map, semN v, denD_map, all _ v.2.1 _ v.2.2]
      simp [denD_term]
    · rw [eq] at h; have := lh_field_le h; rw [lh_term_zero]; omega
  · obtain ⟨sN, lN, semN⟩ := descr_noList (TV := TV) (LV := LV) (MV := MV) sX
    exact ⟨_, fun d => tail_map d X, Or.inr ⟨_, rfl, sN⟩, semN, lN⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fusing element types of the next level. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Tuple fields that are 3-tuples are leaves: the top leaf or tuple literals. -/
theorem tfield_three {x a b c : Term} (fx : TField E x) (h : x = .tuple ⟨[a, b, c]⟩) :
    ∃ (k : Int) (tag : String) (l : List Term), x = .tuple #[.integer k, .atom tag, Term.list l] ∧
      (tag = "open" ∨ tag = "closed") ∧ (∀ e ∈ l, E e) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
  rcases wx.shape with rfl | rfl | ⟨k, y, z, rfl⟩ | ⟨h', lit, c', u, d, rfl⟩
  · cases h
  · cases h
  · obtain ⟨⟨⟨k', tag, l, e, g, els⟩, -⟩, key⟩ := Bdd.leaf_iff.mp wx
    exact ⟨k', tag, l, e, g, els⟩
  · simp at h

theorem denTF_leaf (ef : EF nd E V den tl K) {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (hl : ∀ e ∈ l, E e) (v : List V) :
    denTF E den (.tuple #[.integer k, .atom tag, Term.list l]) v = valT E den v (.tuple #[.integer k, .atom tag, Term.list l]) := by
  by_cases top : tag = "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    have : valT E den v (.tuple #[.integer k, .atom "open", Term.list []]) = Bool.true := by
      rw [vT_lit ef g hl]
      cases v <;> simp [InT]
    rw [this]; exact denTF_top _ _
  · have nt : isOpenTop (.tuple #[.integer k, .atom tag, Term.list l]) = Bool.false := by
      cases l with
      | nil =>
        have : tag ≠ "open" := fun e => top ⟨e, rfl⟩
        simp only [Term.list]
        unfold isOpenTop
        split
        · rename_i heq; simp at heq; exact absurd heq.2 this
        · rfl
      | cons _ _ => simp [isOpenTop, Term.list]
    simp [denTF, denO, nt]

/-- A single tuple leaf, as a type of the next level. -/
theorem fused_de {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e)
    (key : KeyOk (.tuple #[.integer k, .atom tag, Term.list l])) :
    DE E (.map [(.atom "tuple", .tuple #[.integer k, .atom tag, Term.list l])]) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
    by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [e] at h
  · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq, equalExact_eq_decide] at h
    by_cases e : name = "tuple"
    · subst e
      simp at h
      subst h
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))))
      by_cases top : tag = "open" ∧ l = []
      · obtain ⟨rfl, rfl⟩ := top; exact Or.inl ⟨k, rfl⟩
      · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨k, tag, l, rfl, g, hl⟩, fun ⟨k', e⟩ => top ?_⟩, key⟩)
        simp only [Term.tuple.injEq] at e
        have e₁ := congrArg (fun a : Array Term => a[1]?) e
        have e₂ := congrArg (fun a : Array Term => a[2]?) e
        simp [list_eq_nil] at e₁ e₂
        exact ⟨e₁, e₂⟩
    · simp [e] at h

theorem single_other {A : List (Term × Term)} {x : Term} (size : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    (hx : mapLookup A (.atom "tuple") = some x) {name : String} (hn : name ≠ "tuple") : mapLookup A (.atom name) = none := by
  cases h : mapLookup A (.atom name) with
  | none => rfl
  | some y => exact absurd ((compareExact_eq_atom _ _).mp (size_one_keys size h hx)) (by simpa using hn)

/-- The fused single tuple leaf holds the values of both single tuple leaves. -/
theorem fused_sem (ef : EF nd E V den tl K) {A B : List (Term × Term)} {kA kB k : Int} {t : String} {lA lB l : List Term}
    (g : t = "open" ∨ t = "closed") (hA : ∀ e ∈ lA, E e) (hB : ∀ e ∈ lB, E e) (hl : ∀ e ∈ l, E e)
    (tA : mapLookup A (.atom "tuple") = some (.tuple #[.integer kA, .atom t, Term.list lA]))
    (sA : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    (tB : mapLookup B (.atom "tuple") = some (.tuple #[.integer kB, .atom t, Term.list lB]))
    (sB : Erlang.erlang.«map_size/1» (.map B) = .ok (.integer 1))
    (sem : ∀ w, InT den (t == "closed") l w ↔ InT den (t == "closed") lA w ∨ InT den (t == "closed") lB w)
    (v : PtD E den tl (FVal E den)) :
    denD (.map [(.atom "tuple", .tuple #[.integer k, .atom t, Term.list l])]) v ↔ denD (.map A) v ∨ denD (.map B) v := by
  obtain ⟨⟨name, p⟩, m, ok⟩ := v
  simp only [denD_map]
  by_cases hn : name = "tuple"
  · subst hn
    obtain ⟨w, hw⟩ := ok.2.2.2.1 rfl
    have one : mapLookup [(.atom "tuple", .tuple #[.integer k, .atom t, Term.list l])] (.atom "tuple") =
        some (.tuple #[.integer k, .atom t, Term.list l]) := by simp [mapLookup]
    rw [one, tA, tB, dn_tupleT hw, dn_tupleT hw, dn_tupleT hw, denTF_leaf ef g hl, denTF_leaf ef g hA,
      denTF_leaf ef g hB, vT_fused ef (k₁ := kA) (k₂ := kB) g g hA hB hl sem, Bool.or_eq_true]
  · have none : mapLookup [(.atom "tuple", .tuple #[.integer k, .atom t, Term.list l])] (.atom name) = none := by
      simp [mapLookup, hn]
    rw [none, single_other sA tA hn, single_other sB tB hn]
    simp [dn_none]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types as the function checks use them, under seen sets above them. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem EF.den_none (ef : EF nd E V den tl K) (v : V) : ¬den (.map []) v := by
  obtain ⟨b, run, ex⟩ := ef.empty [] ef.none
  have r := run K (Nat.le_refl _)
  rw [empty_none_seen] at r
  have : b = Bool.true := by cases b <;> simp_all [boolAtom]
  subst this
  exact (ex 1 (by rw [lh_nil_map]; omega) (safeN_nil _)).mp rfl v

theorem EF.den_none' (ef : EF nd E V den tl K) {a : Term} (ha : E a) (none : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) (v : V) :
    ¬den a v := fun d => ef.den_none v (ef.resp ef.none ha (Lynx.Term.compare_eq_symm none) d)

theorem EF.congr (ef : EF nd E V den tl K) {N : Nat} : DenCongr (EB E N) den := by
  intro a a' ha ha' e
  funext v
  exact propext ⟨fun d => ef.resp ha'.1 ha.1 (Lynx.Term.compare_eq_symm e) d, fun d => ef.resp ha.1 ha'.1 e d⟩

/-- Emptiness of element types below a height, with no seen set, is exact. -/
theorem EF.empty0 (ef : EF nd E V den tl K) {H : Nat} {a : Term} (ha : EB E H a) {m : Nat} (hm : K ≤ m) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map []) = .ok (boolAtom (isEmpty den a)) := by
  obtain ⟨b, run, ex⟩ := ef.empty [] ha.1
  rw [run m hm]
  congr 2
  cases b
  · symm; exact Bool.eq_false_iff.mpr fun h => by
      have := (ex H ha.2 (safeN_nil H)).mpr ((isEmpty_iff den a).mp h); cases this
  · symm; exact (isEmpty_iff den a).mpr ((ex H ha.2 (safeN_nil H)).mp rfl)

/-- Element types below the height `H` are element types of the function checks under seen sets above them, given
complete subtyping. -/
theorem felem (ef : EF nd E V den tl K)
    (subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true"))
    {H : Nat} (one : 1 ≤ H) {S : List (Term × Term)} (hS : SafeN H S) : FunElem (EB E H) den K (.map S) where
  phi := {
    inter := fun ha hb => let ⟨c, hc, run, sem, h⟩ := ef.inter ha.1 hb.1; ⟨c, ⟨hc, h H ha.2 hb.2⟩, run, sem⟩
    diff := fun ha hb => let ⟨c, hc, run, sem, h⟩ := ef.diff ha.1 hb.1; ⟨c, ⟨hc, h H ha.2 hb.2⟩, run, sem⟩
    empty := fun {a} ha m hm => by
      obtain ⟨b, run, ex⟩ := ef.empty S ha.1
      rw [run m hm]
      congr 2
      cases b
      · symm; exact Bool.eq_false_iff.mpr fun h => by
          have := (ex H ha.2 hS).mpr ((isEmpty_iff den a).mp h); cases this
      · symm; exact (isEmpty_iff den a).mpr ((ex H ha.2 hS).mp rfl)
    congr := ef.congr }
  empty0 := fun ha m hm => ef.empty0 ha hm
  empty1 := fun ha m hm => by rw [empty1_static (ef.static ha.1)]; exact ef.empty0 ha hm
  union := fun ha hb => let ⟨c, hc, run, sem, h⟩ := ef.union ha.1 hb.1; ⟨c, ⟨hc, h H ha.2 hb.2⟩, run, sem⟩
  neg := fun {a} ha => by
    rcases ef.static ha.1 with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩
    · refine ⟨.map [], ⟨ef.none, by rw [lh_nil_map]; omega⟩, fun m _ => by
        unfold Elixir.Module.Types.Descr.«bare_negation/1»; rfl, fun v => ?_⟩
      exact ⟨fun d => absurd d (ef.den_none v), fun d => absurd (ef.den_term v) d⟩
    all_goals
      obtain ⟨c, hc, run, sem, h⟩ := ef.diff ef.term ha.1
      exact ⟨c, ⟨hc, h H (by simp [lh]; omega) ha.2⟩, fun m hm => by
        unfold Elixir.Module.Types.Descr.«bare_negation/1»; exact run m hm,
        fun v => by rw [sem]; exact ⟨fun h => h.2, fun h => ⟨ef.den_term v, h⟩⟩⟩
  sub := fun {a b} ha hb m hm => by
    obtain ⟨s, run, sound⟩ := ef.sub ha.1 hb.1
    rw [run m hm]
    congr 2
    cases s
    · symm; refine bp_false.mpr fun incl => ?_
      have := (run m hm).symm.trans (subc ha.1 hb.1 incl m hm)
      simp [boolAtom] at this
    · symm; exact bp_true.mpr (sound rfl)
  disj := fun ha hb => let ⟨s, run, sound⟩ := ef.disj ha.1 hb.1; ⟨s, run, sound⟩
  term := ⟨⟨ef.term, by simp [lh]; omega⟩, ef.den_term⟩
  none := ⟨⟨ef.none, by rw [lh_nil_map]; omega⟩, ef.den_none⟩

end

/-! Domains of arrows of element types: tuple types of them, standing for the lists of values they hold. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Domains of arrows of element types below the height `H`: tuple types of the next level, no higher than `H`. -/
def DomA (E : Term → Prop) (H : Nat) (t : Term) : Prop :=
  TupC (EB E H) t ∧ ∃ X, t = .map X ∧ DescrC FunTop (TField E) (LF E) (MField E) X ∧ lh (.map X) ≤ H

/-- The lists of values a domain holds. -/
def ddenA (E : Term → Prop) (den : Term → V → Prop) (t : Term) (x : List V) : Prop :=
  ∃ X, t = .map X ∧ dn "tuple" (mapLookup X (.atom "tuple")) (0, .nil, valT E den x) = Bool.true

theorem inT_dom : ∀ (l : List Term) (x : List V), InT den Bool.true l x ↔ FunSem.InDomR (l.map den) x
  | [], [] => by simp [InT, FunSem.InDomR]
  | [], _ :: _ => by simp [InT, FunSem.InDomR]
  | _ :: _, [] => by simp [InT, FunSem.InDomR]
  | e :: l, v :: x => by simp only [InT, List.map_cons, FunSem.InDomR, inT_dom l x]

/-- The domain of arguments: the closed tuple of them, keyed as Descr keys closed literals. -/
theorem args_domain_key (l : List Term) (hl : ∀ e ∈ l, Static e) : ∃ k : Int,
    Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list l) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", Term.list l])]) ∧
    KeyOk (.tuple #[.integer k, .atom "closed", Term.list l]) := by
  obtain ⟨se, run⟩ := descr_fields l hl [] [] Bool.false
  obtain ⟨k, leaf, key⟩ := leaf_new_key "closed" (Or.inr rfl) l
  refine ⟨k, ?_, key⟩
  have rev : Erlang.lists.«reverse/1» (Term.list l.reverse) = .ok (Term.list l) := by
    simpa using reverse1_list l.reverse
  simp only [Term.list, List.append_nil, boolAtom_false] at run
  unfold Elixir.Module.Types.Descr.«args_to_domain/1»
  cases l <;> simp_all [Erlang.erlang.«is_list/1», Elixir.Module.Types.Descr.«tuple/1»,
    Elixir.Module.Types.Descr.«tuple_descr/2», Elixir.Module.Types.Descr.«tuple_descr_static/2»,
    Elixir.Module.Types.Descr.«tuple_new/2», Term.list]

theorem lh_closed_le {k : Int} {l : List Term} {H : Nat} (one : 1 ≤ H) (hl : ∀ e ∈ l, lh e < H) :
    lh (.tuple #[.integer k, .atom "closed", Term.list l]) ≤ H := by
  by_cases ne : ExpEls "closed" l
  · obtain ⟨-, r, a, b, rfl⟩ := ne
    have : lh (.tuple ⟨[.reference r, .map a, b]⟩) = 1 := by rw [lh]
    simp only [Term.list]
    rw [show (#[Term.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple #[.reference r, .map a, b]) .nil)] :
      Array Term) = ⟨[Term.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩
      from rfl, lh_nodeLit, this]
    exact one
  · rw [lh_lit (Or.inr rfl) (by simp) ne]
    have := lh_list_le l (M := H - 1) fun e me => by have := hl e me; omega
    omega

theorem tupC_keys {H : Nat} {X : List (Term × Term)} (h : TupC (EB E H) (.map X)) {name : String} (ne : name ≠ "tuple") :
    mapLookup X (.atom name) = Option.none := by
  obtain ⟨X', e, -, keys⟩ := h
  simp only [Term.map.injEq] at e
  subst e
  cases hx : mapLookup X (.atom name) with
  | none => rfl
  | some x =>
    have := keys _ (by rw [hx]; rfl)
    simp only [Term.atom.injEq] at this
    exact absurd this ne

/-- Emptiness of domains: exact under seen sets above them, or keyed by an arity, as high. -/
theorem domA_empty (ef : EF nd E V den tl K) {H : Nat} {a : Term} (ha : DomA E H a) (S : List (Term × Term))
    (hS : SafeT (H + 1) S) {m : Nat} (hm : K + 1 ≤ m) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom (bp (∀ x, ¬ddenA E den a x))) := by
  obtain ⟨tc, X, rfl, sX, lX⟩ := ha
  by_cases ne : X = []
  · subst ne
    rw [empty_none_seen]
    have : bp (∀ x, ¬ddenA E den (.map []) x) = Bool.true := bp_true.mpr fun x ⟨Y, e, d⟩ => by
      simp only [Term.map.injEq] at e; subst e; simp [mapLookup, dn_none] at d
    rw [this]; rfl
  obtain ⟨xt, hxt⟩ : ∃ xt, mapLookup X (.atom "tuple") = some xt := by
    cases X with
    | nil => exact absurd rfl ne
    | cons e rest =>
      obtain ⟨X', eX, -, keys⟩ := tc
      simp only [Term.map.injEq] at eX
      have h1 : (mapLookup (e :: rest) e.1).isSome := by simp [mapLookup]
      have q := keys e.1 (by rw [← eX]; exact h1)
      rw [q] at h1
      exact Option.isSome_iff_exists.mp h1
  have fx : TField E xt := fieldC_tuple (sX.fields "tuple" xt hxt)
  obtain ⟨bt, run, ex⟩ := tuple_empty_exact ef fx S
  have lt : lh xt < H + 1 := by have := lh_field_le hxt; omega
  have r := descr_empty_run (D m) (S := .map S) (bt := bt) (bm := Bool.true) (bl := Bool.true) (bf := Bool.true)
    sX.static ne (fun x h => by rw [hxt] at h; cases h; exact run m hm)
    (fun x h => by rw [tupC_keys (name := "map") tc (by decide)] at h; cases h)
    (fun x h => by rw [tupC_keys (name := "list") tc (by decide)] at h; cases h)
    (fun x h => by rw [tupC_keys (name := "fun") tc (by decide)] at h; cases h)
  rw [r, tupC_keys (name := "atom") tc (by decide), tupC_keys (name := "bitmap") tc (by decide),
    tupC_keys (name := "map") tc (by decide), tupC_keys (name := "list") tc (by decide),
    tupC_keys (name := "fun") tc (by decide), hxt]
  simp only [Option.isSome_none, Bool.not_false, Bool.true_and, Option.isNone_some, Bool.false_or, Option.isNone_none,
    Bool.true_or, Bool.and_true]
  congr 2
  have sem : (∀ x, ¬ddenA E den (.map X) x) ↔ ∀ v, denTF E den xt v = Bool.false := by
    constructor
    · intro h v
      cases hv : denTF E den xt v
      · rfl
      · exact absurd ⟨X, rfl, by rw [hxt, dn_tupleT rfl]; exact hv⟩ (h v)
    · rintro h x ⟨Y, e, d⟩
      simp only [Term.map.injEq] at e; subst e
      rw [hxt, dn_tupleT rfl, h x] at d; cases d
  cases bt
  · symm; refine bp_false.mpr fun h => ?_
    have := (ex (H + 1) lt hS).mpr (sem.mp h); cases this
  · symm; exact bp_true.mpr (sem.mpr ((ex (H + 1) lt hS).mp rfl))

theorem safeT_nil (N : Nat) : SafeT N [] := fun _ h => by simp at h

/-- Points of tuple fields at the values `x`. -/
theorem ptTup (ef : EF nd E V den tl K) (x : List V) :
    PtOkC (ValT E den) (ValLN E den tl) (ValMN E den) FVT "tuple" (0, .nil, valT E den x) :=
  ptOk_tuple (kinds ef) ⟨x, rfl⟩

/-- Domains of arrows of element types below the height `H` are domains of the function checks under seen sets
above them, or keyed by an arity, as high. -/
theorem fdom (ef : EF nd E V den tl K) {H : Nat} (one : 1 ≤ H) {S : List (Term × Term)} (hS : SafeT (H + 1) S) :
    FunDom (DomA E H) (EB E H) den (ddenA E den) (K + 6) (.map S) := by
  have hnone : EB E H (.map []) := ⟨ef.none, by rw [lh_nil_map]; omega⟩
  have dm := domOk (ef.ops H (by omega)) (ef.dops H) (ef.funB H) hnone (ef.tailB H)
  have sem2 : ∀ {X Y : List (Term × Term)} {U : List (Term × Term)} (f : Bool → Bool → Bool),
      (∀ name p, PtOkC (ValT E den) (ValLN E den tl) (ValMN E den) FVT name p →
        dn name (mapLookup U (.atom name)) p = f (dn name (mapLookup X (.atom name)) p) (dn name (mapLookup Y (.atom name)) p)) →
      ∀ x, ddenA E den (.map U) x ↔ f (dn "tuple" (mapLookup X (.atom "tuple")) (0, .nil, valT E den x))
        (dn "tuple" (mapLookup Y (.atom "tuple")) (0, .nil, valT E den x)) = Bool.true := by
    intro X Y U f sem x
    constructor
    · rintro ⟨U', e, d⟩
      simp only [Term.map.injEq] at e; subst e
      rw [← sem _ _ (ptTup ef x)]; exact d
    · intro h; exact ⟨U, rfl, by rw [sem _ _ (ptTup ef x)]; exact h⟩
  have ddenM : ∀ {X : List (Term × Term)} (x : List V), ddenA E den (.map X) x ↔
      dn "tuple" (mapLookup X (.atom "tuple")) (0, .nil, valT E den x) = Bool.true := by
    intro X x
    constructor
    · rintro ⟨U', e, d⟩; simp only [Term.map.injEq] at e; subst e; exact d
    · intro h; exact ⟨X, rfl, h⟩
  refine ⟨fun l hl => ?_, ⟨⟨dm.none, [], rfl, descrC_nil, by rw [lh_nil_map]; omega⟩, fun x ⟨Y, e, d⟩ => ?_⟩,
    fun ha => dm.isMap ha.1, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_, fun {a b} ha hb => ?_,
    fun ha m hm => domA_empty ef ha [] (safeT_nil _) (by omega), fun ha m hm => domA_empty ef ha S hS (by omega)⟩
  · obtain ⟨k, run, key⟩ := args_domain_key l fun e me => ef.static (hl e me).1
    obtain ⟨t, tc, run'⟩ := dm.dom l hl
    rw [run] at run'; cases run'
    have look : ∀ q, mapLookup [(Term.atom "tuple", Term.tuple #[.integer k, .atom "closed", Term.list l])] q =
        if compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq then some (.tuple #[.integer k, .atom "closed", Term.list l])
        else Option.none := by
      intro q; by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq <;> simp [mapLookup, e]
    have lit : TLit E (.tuple #[.integer k, .atom "closed", Term.list l]) :=
      ⟨⟨⟨k, "closed", l, rfl, Or.inr rfl, fun e me => (hl e me).1⟩, fun ⟨_, e⟩ => by simp at e⟩, key⟩
    refine ⟨_, ⟨tc, _, rfl, ⟨fun q h => ?_, fun name w h => ?_⟩, ?_⟩, run, fun x => ?_⟩
    · rw [look] at h; split at h
      · rename_i e; exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
      · simp at h
    · rw [look] at h; split at h
      · rename_i e
        simp only [atom_compareExact_eq, Term.atom.injEq] at e
        subst e
        simp at h; subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Bdd.leaf_iff.mpr lit)⟩))))
      · simp at h
    · refine lh_map_le.mpr fun e me => ?_
      simp only [mapEntries_singleton, List.mem_singleton] at me
      subst me
      exact lh_closed_le one fun e me => (hl e me).2
    · rw [ddenM, show mapLookup [(Term.atom "tuple", Term.tuple #[.integer k, .atom "closed", Term.list l])] (.atom "tuple") =
          some (.tuple #[.integer k, .atom "closed", Term.list l]) by simp [mapLookup], dn_tupleT rfl,
        denTF_leaf ef (Or.inr rfl) (fun e me => (hl e me).1), vT_lit ef (Or.inr rfl) (fun e me => (hl e me).1)]
      exact inT_dom l x
  · simp only [Term.map.injEq] at e; subst e; simp [mapLookup, dn_none] at d
  · obtain ⟨c, tc, run⟩ := dm.union ha.1 hb.1
    obtain ⟨-, A, rfl, sA, lA⟩ := ha
    obtain ⟨-, B, rfl, sB, lB⟩ := hb
    obtain ⟨U, run', sU, sem, le⟩ := descr_union (kinds ef) (fcOf (K + 2)) (m := K + 7) (by omega) sA sB
    rw [run (K + 8) (by omega)] at run'; cases run'
    refine ⟨_, ⟨tc, U, rfl, sU, by have := le trivial; omega⟩, fun m hm => run m (by omega), fun x => ?_⟩
    rw [sem2 (· || ·) sem x, ddenM, ddenM, Bool.or_eq_true]
  · obtain ⟨c, tc, run⟩ := dm.inter ha.1 hb.1
    obtain ⟨-, A, rfl, sA, lA⟩ := ha
    obtain ⟨-, B, rfl, sB, lB⟩ := hb
    obtain ⟨U, run', sU, sem, le⟩ := descr_inter (kinds ef) (fcOf (K + 2)) (m := K + 7) (by omega) sA sB
    rw [run (K + 8) (by omega)] at run'; cases run'
    refine ⟨_, ⟨tc, U, rfl, sU, by have := le trivial; omega⟩, fun m hm => run m (by omega), fun x => ?_⟩
    rw [sem2 (· && ·) sem x, ddenM, ddenM, Bool.and_eq_true]
  · obtain ⟨c, tc, run⟩ := dm.diff ha.1 hb.1
    obtain ⟨-, A, rfl, sA, lA⟩ := ha
    obtain ⟨-, B, rfl, sB, lB⟩ := hb
    obtain ⟨U, run', sU, sem, le⟩ := descr_diff (kinds ef) (fcOf (K + 2)) (m := K + 6) (by omega) sA sB
    rw [run (K + 8) (by omega)] at run'; cases run'
    refine ⟨_, ⟨tc, U, rfl, sU, by have := le trivial; omega⟩, fun m hm => run m (by omega), fun x => ?_⟩
    rw [sem2 (fun a b => a && !b) sem x, ddenM, ddenM]
    simp

end

/-! Emptiness of function types of element types: exact on functions, under seen sets above them. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem FunElem.mono {E : Term → Prop} {den : Term → V → Prop} {K K' : Nat} {seen : Term}
    (fe : FunElem E den K seen) (le : K ≤ K') : FunElem E den K' seen where
  phi := {
    inter := fun ha hb => let ⟨c, hc, run, sem⟩ := fe.phi.inter ha hb; ⟨c, hc, fun m hm => run m (by omega), sem⟩
    diff := fun ha hb => let ⟨c, hc, run, sem⟩ := fe.phi.diff ha hb; ⟨c, hc, fun m hm => run m (by omega), sem⟩
    empty := fun ha m hm => fe.phi.empty ha m (by omega)
    congr := fe.phi.congr }
  union := fun ha hb => let ⟨c, hc, run, sem⟩ := fe.union ha hb; ⟨c, hc, fun m hm => run m (by omega), sem⟩
  neg := fun ha => let ⟨c, hc, run, sem⟩ := fe.neg ha; ⟨c, hc, fun m hm => run m (by omega), sem⟩
  sub := fun ha hb m hm => fe.sub ha hb m (by omega)
  disj := fun ha hb => let ⟨s, run, sem⟩ := fe.disj ha hb; ⟨s, fun m hm => run m (by omega), sem⟩
  term := fe.term
  none := fe.none
  empty0 := fun ha m hm => fe.empty0 ha m (by omega)
  empty1 := fun ha m hm => fe.empty1 ha m (by omega)

theorem EF.congrE (ef : EF nd E V den tl K) : DenCongr E den := by
  intro a a' ha ha' e
  funext v
  exact propext ⟨fun d => ef.resp ha' ha (Lynx.Term.compare_eq_symm e) d, fun d => ef.resp ha ha' e d⟩

theorem fresh_arities : ∀ (R : List (Term × Term)), ∃ n : Nat, ∀ m, n ≤ m → mapLookup R (.integer m) = Option.none
  | [] => ⟨0, fun _ _ => rfl⟩
  | e :: R => by
    obtain ⟨n, hn⟩ := fresh_arities R
    obtain ⟨j, hj⟩ : ∃ j : Nat, ∀ m : Nat, j ≤ m → e.1 ≠ .integer m := by
      cases h : e.1 with
      | integer i => exact ⟨i.toNat + 1, fun m hm e' => by simp only [Term.integer.injEq] at e'; omega⟩
      | _ => exact ⟨0, fun m _ e' => by cases e'⟩
    refine ⟨max n j, fun m hm => ?_⟩
    have ne : ¬compareExact (fuel (.integer (m : Int)) e.1) (.integer (m : Int)) e.1 = .eq := by
      rw [integer_compareExact_eq]; exact hj m (by omega)
    simpa [mapLookup, List.find?_cons, ne] using hn m (by omega)

theorem posOk_of {E' : Term → Prop} {n : Nat} {P : List (Term × List Term × Term)}
    (h : ∀ p ∈ P, FunLit E' n (.tuple #[p.1, Term.list p.2.1, p.2.2])) : PosOk E' n P := by
  intro p mp
  obtain ⟨k, args, ret, e, len, ha, hr⟩ := h p mp
  obtain ⟨-, el, er⟩ := enc_inj e
  rw [el, er]
  exact ⟨ha, hr, by omega⟩

theorem not_seen_any {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {h x : Term} (hx : lh x < N) :
    S.any (fun e => decide (Term.compareExact (Term.fuel (.cons h x) e.1) (.cons h x) e.1 = .eq)) = Bool.false := by
  simp only [List.any_eq_false, decide_eq_true_eq]
  intro e me hit
  obtain ⟨h', b, e₁, one, hb⟩ := hS e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
  omega

/-- Function types of element types decide whether they hold functions, under seen sets above them, given
complete subtyping of element types. -/
theorem funA_empty (ef : EF nd E V den tl K)
    (subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true"))
    {x : Term} (fx : FunA E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 11 ≤ m → Elixir.Module.Types.Descr.«fun_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ (n : Nat) (g : List (FunSem.Row V)),
        (∀ r ∈ g, FunSem.ValidRow n r) → arityOf x (.integer n) (valF E den g) = Bool.false) := by
  have fx' := fx
  obtain ⟨p, R, rfl, ne, bR, kR⟩ := fx'
  -- Totality, for any seen set.
  generalize hH0 : lh (.tuple #[.atom (if p then "union" else "negation"), .map R]) + 1 = H0
  have hnone : EB E H0 (.map []) := ⟨ef.none, by rw [lh_nil_map]; omega⟩
  have ff : FField (EB E H0) (.tuple #[.atom (if p then "union" else "negation"), .map R]) := by
    refine ⟨p, R, rfl, fun q v h => ?_⟩
    obtain ⟨n, hn⟩ := kR q (by rw [h]; rfl)
    have le : lh v ≤ lh (.tuple #[.atom (if p then "union" else "negation"), .map R]) := by
      rw [lh_tag]; exact lookup_lh h
    refine (litB_of (bR q v h) hn).mono fun t ht => ⟨n, hn, funLit_mono (fun a ha => ⟨ha.1, ?_⟩) ht⟩
    have := ha.2; omega
  obtain ⟨b₀, run₀⟩ := fun_total ((ef.ops H0 (by omega)).mono (by omega : K ≤ K + 3)) ((ef.dops H0).mono (by omega))
    ((ef.funB H0).mono (by omega)) (domOk (ef.ops H0 (by omega)) (ef.dops H0) (ef.funB H0) hnone (ef.tailB H0)) hnone ff S
  refine ⟨b₀, fun m hm => run₀ m (by omega), fun N hx hS => ?_⟩
  cases p
  · have : b₀ = Bool.false := by
      have := run₀ (K + 8) (Nat.le_refl _)
      unfold Elixir.Module.Types.Descr.«fun_empty?/2» at this
      cases b₀ <;> simp_all [boolAtom]
    subst this
    obtain ⟨n₀, hn₀⟩ := fresh_arities R
    refine ⟨fun h => (by cases h), fun h => ?_⟩
    have := h n₀ [] (by simp)
    simp [arityOf, hn₀ n₀ (Nat.le_refl _)] at this
  · have hl : ∀ b n t, LitB E b n t → FunLit E n t := fun _ _ _ h => funLit_mono (fun a ha => ha.1) h
    have hR : ∀ e ∈ mapEntries R, ∃ n : Nat, e.1 = .integer n ∧ Bdd (LitB E e.2 n) e.2 := by
      intro e me
      have h := mapLookup_of_mem_mapEntries me
      obtain ⟨n, hn⟩ := kR e.1 (by rw [h]; rfl)
      exact ⟨n, hn, litB_of (bR _ _ h) hn⟩
    have below : ∀ e ∈ mapEntries R, lh e.2 < N := by
      intro e me
      have := le_lh_map me
      rw [lh_tag] at hx
      omega
    obtain ⟨b₁, run₁, sem₁⟩ := fun_union_sem (K := K + 9) ef.congrE R S (LitB E) hl hR
      (fun e me => not_seen_any hS (below e me)) (by
        intro e me n hn P N' hP hN LP LN
        have one : 1 ≤ lh e.2 := fbdd_pos (bR _ _ (mapLookup_of_mem_mapEntries me)) fun _ ht => funArity_shape ht
        have hS' : SafeN (lh e.2) ((.cons e.1 e.2, .atom "true") :: S) := by
          intro s ms
          rcases List.mem_cons.mp ms with rfl | ms
          · exact ⟨e.1, e.2, rfl, one, Nat.le_refl _⟩
          · obtain ⟨h', b', e₁, one', hb'⟩ := hS s ms
            exact ⟨h', b', e₁, one', by have := below e me; omega⟩
        have hT : SafeT (lh e.2 + 1) ((.cons e.1 e.2, .atom "true") :: S) := by
          intro s ms
          rcases List.mem_cons.mp ms with rfl | ms
          · exact ⟨e.1, e.2, rfl, one, Or.inr ⟨⟨n, hn⟩, Nat.le_refl _⟩⟩
          · obtain ⟨h', b', e₁, one', hb'⟩ := hS s ms
            exact ⟨h', b', e₁, one', Or.inl (by have := below e me; omega)⟩
        exact fun_line_sem ((felem ef subc one hS').mono (by omega : K ≤ K + 6)) (fdom ef one hT) n P N'
          (posOk_of LP) (posOk_of LN))
    have : b₀ = b₁ := by
      have := (run₀ (K + 11) (by omega)).symm.trans (run₁ (K + 11) (by omega))
      cases b₀ <;> cases b₁ <;> simp_all [boolAtom]
    subst this
    rw [sem₁]
    exact forall_congr' fun n => forall_congr' fun g => imp_congr_right fun _ => by rw [arity_tag]; simp

/-- Function types of element types, whose points are functions: closed under plain operations, which keep literal
heights, with exact emptiness under seen sets above them, given complete subtyping of element types. -/
theorem funAC (ef : EF nd E V den tl K)
    (subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true")) :
    FunC (K + 11) (FunA E) (FVal E den) (fun _ => True) True where
  funF := FunA.funF
  union := fun {x y} hx hy m w hm run => by
    obtain ⟨w', run', fw, le⟩ := funA_union hx hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [run'] at run; cases run
    exact ⟨fw, fun _ => le⟩
  inter := fun {x y} hx hy m w hm run kw => by
    obtain ⟨w', run', k⟩ := funA_inter hx hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [run'] at run; cases run
    exact ⟨(k kw).1, fun _ => (k kw).2⟩
  diff := fun {x y} hx hy m w hm run kw => by
    obtain ⟨w', run', k⟩ := funA_diff hx hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [run'] at run; cases run
    exact ⟨(k kw).1, fun _ => (k kw).2⟩
  empty := fun {x} S {m} hx _ hm => by
    obtain ⟨b, run, ex⟩ := funA_empty ef subc hx S
    have key : Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "fun") x (.map S) = .ok (boolAtom b) := by
      simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m hm
    refine ⟨fun N hN hS none => ?_, fun _ => ⟨b, key, fun N hN hS hb p r f => ?_⟩⟩
    · have : b = Bool.true := (ex N hN hS).mpr fun n g vg => by
        have := none (0, .integer n, valF E den g) (valF_resp g) ⟨n, g, rfl, vg, rfl⟩
        rwa [dn_fun] at this
      rw [key, this]; rfl
    · obtain ⟨n, g, ha, vg, hρ⟩ := f
      rw [dn_fun, ha, hρ]
      exact (ex N hN hS).mp hb n g vg

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types of one level give element types of the next. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem de_none : DE E (.map []) := Or.inr ⟨[], rfl, descrC_nil⟩

end

section
variable {nd : Term} {C : Nat → Term → Prop} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

/-- Maps that combine the node with types of height zero: a tuple field of the expansion literal of `nd`, and
other fields of height zero. -/
def ComboMap (nd : Term) (X : List (Term × Term)) : Prop :=
  (∀ w, mapLookup X (.atom "tuple") = some w → OField (PureLit nd) w) ∧
    ∀ name w, name ≠ "tuple" → mapLookup X (.atom name) = some w → lh w = 0

theorem isT_map {nd : Term} {X : List (Term × Term)} : ¬IsT nd (.map X) := by
  rintro ⟨-, h⟩
  unfold «recursive_node?/1» at h
  simp at h

theorem combo_map {nd : Term} {X : List (Term × Term)} : Combo nd (.map X) ↔ ComboMap nd X := by
  constructor
  · rintro (h | h | ⟨Y, h, ct, co⟩)
    · cases h
    · exact absurd h isT_map
    · cases h; exact ⟨ct, co⟩
  · exact fun ⟨ct, co⟩ => Or.inr (Or.inr ⟨X, rfl, ct, co⟩)

/-- Pure tuple fields of `TF`. -/
abbrev TFc (nd : Term) (TF : Term → Prop) (x : Term) : Prop := TF x ∧ OField (PureLit nd) x

/-- Fields of height zero of `F`. -/
abbrev ZF (F : Term → Prop) (x : Term) : Prop := F x ∧ lh x = 0

theorem comboMap_descr {nd : Term} {Fn TF LF MF : Term → Prop} {X : List (Term × Term)}
    (fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT)
    (sX : DescrC Fn TF LF MF X) (c : ComboMap nd X) : DescrC FunTop (TFc nd TF) (ZF LF) (ZF MF) X := by
  refine ⟨sX.keys, fun name x hx => ?_⟩
  have f := sX.fields name x hx
  by_cases nt : name = "tuple"
  · subst nt; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fieldC_tuple f, c.1 x hx⟩))))
  have z := c.2 name x nt hx
  rcases f with ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩
  · exact Or.inl ⟨h, f⟩
  · exact Or.inr (Or.inl ⟨h, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, fz f z⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f, z⟩)))
  · exact absurd h nt
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, f, z⟩))))

theorem descr_comboMap {nd : Term} {TF LF MF : Term → Prop} {X : List (Term × Term)}
    (sX : DescrC FunTop (TFc nd TF) (ZF LF) (ZF MF) X) : ComboMap nd X := by
  refine ⟨fun w hw => (fieldC_tuple (sX.fields _ w hw)).2, fun name w nt hw => ?_⟩
  rcases sX.fields name w hw with ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨-, f⟩ | ⟨h, -⟩ | ⟨-, f⟩
  · exact lh_bitF f
  · exact lh_atomF f
  · rw [show w = funTopT from f]; exact lh_funTop
  · exact f.2
  · exact absurd h nt
  · exact f.2

theorem descr_unrestrict' {nd : Term} {TF LF MF : Term → Prop} {name : String} {x : Term}
    (f : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name x) : FieldC FunTop TF LF MF name x := by
  rcases f with ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩
  · exact Or.inl ⟨h, f⟩
  · exact Or.inr (Or.inl ⟨h, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, f⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f.1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, f.1⟩))))

/-- Plain operations on fields keep pure tuple fields pure and fields of height zero at height zero. -/
theorem restrict_field {nd : Term} {TF LF MF : Term → Prop} {name : String} {x y w : Term}
    (fx : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name x) (fy : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name y)
    (fw : FieldC FunTop TF LF MF name w) (lw : lh w ≤ max (lh x) (lh y))
    (pw : name = "tuple" → OField (PureLit nd) w) : FieldC FunTop (TFc nd TF) (ZF LF) (ZF MF) name w := by
  rcases fw with ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩ | ⟨h, f⟩
  · exact Or.inl ⟨h, f⟩
  · exact Or.inr (Or.inl ⟨h, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, f⟩))
  · subst h
    have := (fieldC_list fx).2
    have := (fieldC_list fy).2
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, f, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, f, pw h⟩))))
  · subst h
    have := (fieldC_map fx).2
    have := (fieldC_map fy).2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, f, by omega⟩))))

/-- Plain intersections of combinations of the node with types of height zero are such combinations. -/
theorem combo_inter {nd : Term} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
    (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K FunTop FVT (fun _ => True) True)
    (fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT) {m : Nat} (hm : K + 1 ≤ m)
    {A B I : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (cA : ComboMap nd A) (cB : ComboMap nd B)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map A) (.map B) = .ok (.map I)) :
    ComboMap nd I := by
  have sA' := comboMap_descr fz sA cA
  have sB' := comboMap_descr fz sB cB
  obtain ⟨I', run', look, keysI⟩ := inter_lookup m A B sA.static sB.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sA.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := fieldC_inter ks fc hm (descr_unrestrict' (sA'.fields name x hx))
      (descr_unrestrict' (sB'.fields name y hy))
    exact ⟨w, run⟩
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Term.map.injEq] at e
  subst e
  obtain ⟨cI, -, -⟩ := inter_gen (slh := True) (TV := TV) (LV := LV) (MV := MV) sA' sB'
    (fun q x y => Elixir.Module.Types.Descr.«bare_intersection/3» (D m) q x y)
    (fun name => ⟨(look name).1, (look name).2.1, fun x y w hx hy r => by rw [(look name).2.2 x y w hx hy r]; rfl⟩)
    keysI (fun name x y fx fy => by
      obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm (descr_unrestrict' fx) (descr_unrestrict' fy)
      refine ⟨w, run, fun kw => ⟨restrict_field fx fy (k kw).1 ((k kw).2 trivial) fun h => ?_, fun _ => (k kw).2 trivial⟩,
        sem⟩
      subst h
      obtain ⟨w', run'', kk, -⟩ := open_inter_spec pureLit_not _ tuple_inter_shape.1 tuple_inter_shape.2.1
        tuple_inter_shape.2.2 (.atom "tuple") (fieldC_tuple fx).2 (fieldC_tuple fy).2
      have : w = w' := by
        have := run.symm.trans (by simpa [Elixir.Module.Types.Descr.«bare_intersection/3»] using run'')
        simpa using this
      subst this
      exact (kk kw).1)
  exact descr_comboMap cI

/-- Plain differences of combinations of the node with types of height zero are such combinations. -/
theorem combo_diff {nd : Term} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
    (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K FunTop FVT (fun _ => True) True)
    (fz : ∀ {x}, Fn x → lh x = 0 → x = funTopT) {m : Nat} (hm : K + 2 ≤ m)
    {A B O : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (cA : ComboMap nd A) (cB : ComboMap nd B)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map A) (.map B) = .ok (.map O)) :
    ComboMap nd O := by
  by_cases nB : B = []
  · subst nB
    have : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map A) (.map []) = .ok (.map A) := by
      unfold Elixir.Module.Types.Descr.«bare_difference/2»; simp [Erlang.erlang.«==/2»]
    rw [this] at run
    simp only [Except.ok.injEq, Term.map.injEq] at run
    subst run
    exact cA
  have sA' := comboMap_descr fz sA cA
  have sB' := comboMap_descr fz sB cB
  obtain ⟨O', fold, sO, -, -⟩ := diff_gen (slh := True) (TV := TV) (LV := LV) (MV := MV) m
    (.function false "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    (fun q x y => Elixir.Module.Types.Descr.«bare_difference/3» (D m) q x y) sA' sB'
    (fun q x y => by rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure])
    (fun name x y fx fy => by
      obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm (descr_unrestrict' fx) (descr_unrestrict' fy)
      refine ⟨w, run, fun kw => ⟨restrict_field fx fy (k kw).1 ((k kw).2 trivial) fun h => ?_, fun _ => (k kw).2 trivial⟩,
        sem⟩
      subst h
      obtain ⟨w', run'', fw', -⟩ := pure_diff_sem (fieldC_tuple fx).2 (fieldC_tuple fy).2
      have : w = w' := by
        have := run.symm.trans (by simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run'')
        simpa using this
      subst this
      exact fw')
  have run' : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map A) (.map B) = .ok (.map O') := by
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map sA.static, static_map sB.static, nB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», nB, Erlang.maps.«fold/3»]
    simpa using fold
  have e := run.symm.trans run'
  simp only [Except.ok.injEq, Term.map.injEq] at e
  subst e
  exact descr_comboMap sO

section
variable {nd : Term} {C : Nat → Term → Prop} {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop}
  {FV : Term → (Term → Bool) → Prop}

theorem dg_low (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a : Term} (ha : DEG Fn TF LF MF a) (z : lh a = 0) : Combo nd a := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · exact Or.inl rfl
  refine combo_map.mpr ⟨fun w hw => ?_, fun name w _ hw => ?_⟩
  · obtain ⟨k, rfl⟩ := st.tz (fieldC_tuple (sX.fields _ w hw)) (by have := lh_field_le hw; omega)
    exact Or.inl ⟨k, rfl⟩
  · have := lh_field_le hw; omega

theorem dg_cinter (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b c : Term} {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 14 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) : Combo nd c := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · rw [inter_term_left] at run; cases run; exact cb
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [inter_term_right] at run; cases run; exact ca
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨I, runI, -, -, -⟩ := descr_inter st.ks st.fc (m := m') (by omega) sA sB
  rw [runI] at run; cases run
  exact combo_map.mpr (combo_inter st.ks (fcOf K) st.fz (by omega) sA sB (combo_map.mp ca) (combo_map.mp cb) runI)

theorem dg_cdiff (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b c : Term} {m : Nat} (ha : DEG Fn TF LF MF a)
    (hb : DEG Fn TF LF MF b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 14 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) : Combo nd c := by
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · rw [diff_term_right] at run; cases run; exact combo_none nd
  by_cases nB : B = []
  · subst nB
    rw [diff_none_right _ ha] at run; cases run; exact ca
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · obtain ⟨T, term, sT, -, lT, -⟩ := termC (FV := FV) st.ks st.ftop
    rw [diff_term_left _ term sT.static sB.static nB] at run
    obtain ⟨O, runO, -, -, -⟩ := descr_diff st.ks st.fc (m := m') (by omega) sT sB
    rw [runO] at run; cases run
    have cT : ComboMap nd T := ⟨fun w hw => by
        obtain ⟨k, rfl⟩ := st.tz (fieldC_tuple (sT.fields _ w hw)) (by have := lh_field_le hw; omega)
        exact Or.inl ⟨k, rfl⟩,
      fun name w _ hw => by have := lh_field_le hw; omega⟩
    exact combo_map.mpr (combo_diff st.ks (fcOf K) st.fz (by omega) sT sB cT (combo_map.mp cb) runO)
  · obtain ⟨O, runO, -, -, -⟩ := descr_diff st.ks st.fc (m := m') (by omega) sA sB
    rw [runO] at run; cases run
    exact combo_map.mpr (combo_diff st.ks (fcOf K) st.fz (by omega) sA sB (combo_map.mp ca) (combo_map.mp cb) runO)

theorem map_topk_nonempty (d : Dispatcher) (k : Int) {S : List (Term × Term)}
    (fresh : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "map") (.tuple #[.integer k, .atom "open", .nil])) e.1) (.cons (.atom "map") (.tuple #[.integer k, .atom "open", .nil])) e.1 = .eq)) =
      Bool.false) :
    Elixir.Module.Types.Descr.«map_empty?/2» d (.tuple #[.integer k, .atom "open", .nil]) (.map S) = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«map_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]
  rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
  have line := line_inter_open d k .nil
  simp [line, Elixir.Module.Types.Descr.«init_map_line_empty?/4», any_nil]
  rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
  simp

/-- Combinations of the node with types of height zero decide their emptiness exactly, when no seen BDD is a tuple
BDD of the expansion literal. -/
theorem dg_cempty (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool}
    (ha : DEG Fn TF LF MF a) (ca : Combo nd a) (hS : Safe1 nd S) (hm : K + 14 ≤ m)
    (run : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v : PtG TV LV MV FV, ¬denD a v := by
  rcases ha with rfl | ⟨X, rfl, sX⟩
  · rw [empty_term] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    exact ⟨fun h => absurd h (by decide), fun h => absurd (denD_term ptWit) (h ptWit)⟩
  have cX := combo_map.mp ca
  by_cases ne : X = []
  · subst ne
    rw [empty_none_seen] at run
    have : b = Bool.true := by cases b <;> simp_all [boolAtom]
    subst this
    exact ⟨fun _ v => by simp [denD_map, mapLookup, dn_none], fun _ => rfl⟩
  have fresh : ∀ x, OField (PureLit nd) x →
      S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 = .eq)) = Bool.false := by
    intro x px
    simp only [List.any_eq_false, decide_eq_true_eq]
    exact fun e me => hS.2 e me x px
  have ht : ∀ x, mapLookup X (.atom "tuple") = some x → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      .ok (boolAtom (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false))) := fun x hx =>
    pure_empty_val (cX.1 x hx) (fresh x (cX.1 x hx)) (safeN_noid hS.1 _) (by omega)
  have hmf : ∀ x, mapLookup X (.atom "map") = some x → Elixir.Module.Types.Descr.«map_empty?/2» (D m) x (.map S) =
      .ok (boolAtom Bool.false) := fun x hx => by
    obtain ⟨k, rfl⟩ := st.mz (fieldC_map (sX.fields _ x hx)) (cX.2 "map" x (by decide) hx)
    exact map_topk_nonempty _ k (not_seen hS.1 (by simp [lh]) "map")
  have hl : ∀ x, mapLookup X (.atom "list") = some x → Elixir.Module.Types.Descr.«list_empty?/2» (D m) x (.map S) =
      .ok (boolAtom Bool.false) := fun x hx => by
    rw [st.lz (fieldC_list (sX.fields _ x hx)) (cX.2 "list" x (by decide) hx)]
    exact list_top_nonempty _ _
  have hf : ∀ x, mapLookup X (.atom "fun") = some x → Elixir.Module.Types.Descr.«fun_empty?/2» (D m) x (.map S) =
      .ok (boolAtom Bool.false) := fun x hx => by
    have hx' : FunTop x := st.fz (fieldC_fun (sX.fields _ x hx)) (cX.2 "fun" x (by decide) hx)
    rw [hx']
    exact fun_top_nonempty _ _
  obtain ⟨bt, ht', hbt⟩ : ∃ bt : Bool, (∀ x, mapLookup X (.atom "tuple") = some x →
      Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom bt)) ∧
      ∀ x, mapLookup X (.atom "tuple") = some x → bt = (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)) := by
    cases h : mapLookup X (.atom "tuple") with
    | none => exact ⟨Bool.true, fun x hx => by simp at hx, fun x hx => by simp at hx⟩
    | some x =>
      refine ⟨(!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false)), fun x' hx' => ?_, fun x' hx' => ?_⟩
      · simp only [Option.some.injEq] at hx'; subst hx'; exact ht x h
      · simp only [Option.some.injEq] at hx'; subst hx'; rfl
  rw [descr_empty_run (D m) sX.static ne ht' hmf hl hf] at run
  have hb : b = (!(mapLookup X (.atom "atom")).isSome && !(mapLookup X (.atom "bitmap")).isSome &&
      ((mapLookup X (.atom "tuple")).isNone || bt) && (mapLookup X (.atom "map")).isNone &&
      (mapLookup X (.atom "list")).isNone && (mapLookup X (.atom "fun")).isNone) := by
    simp only [boolAtom, Except.ok.injEq] at run
    cases b <;> cases h : (!(mapLookup X (.atom "atom")).isSome && !(mapLookup X (.atom "bitmap")).isSome &&
      ((mapLookup X (.atom "tuple")).isNone || bt) && (mapLookup X (.atom "map")).isNone &&
      (mapLookup X (.atom "list")).isNone && (mapLookup X (.atom "fun")).isNone) <;> simp_all
  subst hb
  have pt : ∀ (name : String) (p : Point), name ∈ names → PtOkC TV LV MV FV name p →
      dn name (mapLookup X (.atom name)) p = Bool.true → ∃ v : PtG TV LV MV FV, denD (.map X) v :=
    fun name p mn ok h => ⟨⟨(name, p), mn, ok⟩, (denD_map _).mpr h⟩
  constructor
  · intro h v hv
    rw [denD_map] at hv
    obtain ⟨⟨name, p⟩, mn, ok⟩ := v
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hbm⟩, htp⟩, hmp⟩, hlp⟩, hfp⟩ := h
    rcases names_mem mn with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [hbm, dn_none] at hv
    · simp [ha, dn_none] at hv
    · simp [hfp, dn_none] at hv
    · simp [hlp, dn_none] at hv
    · cases hx : mapLookup X (.atom "tuple") with
      | none => simp [hx, dn_none] at hv
      | some x =>
        rw [hx] at htp hv
        simp only [reduceCtorEq, false_or] at htp
        rw [hbt x hx] at htp
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at htp
        rw [dn_tuple] at hv
        obtain ⟨c, hc⟩ := pure_val (cX.1 x hx) (st.ks.t.resp _ (ok.2.2.2.1 rfl))
        rw [hc] at hv
        cases c
        · rw [htp.2] at hv; cases hv
        · rw [htp.1] at hv; cases hv
    · simp [hmp, dn_none] at hv
  · intro h
    have no : ∀ (name : String) (p : Point), name ∈ names → PtOkC TV LV MV FV name p →
        dn name (mapLookup X (.atom name)) p = Bool.true → False := fun name p mn ok d => by
      obtain ⟨v, hv⟩ := pt name p mn ok d
      exact h v hv
    have atomN : mapLookup X (.atom "atom") = none := by
      cases hx : mapLookup X (.atom "atom") with
      | none => rfl
      | some x =>
        obtain ⟨p, ok, d⟩ := atom_full (TV := TV) (LV := LV) (MV := MV) sX hx
        exact (no "atom" p (by simp [names]) ok (by rw [hx]; exact d)).elim
    have bitN : mapLookup X (.atom "bitmap") = none := by
      cases hx : mapLookup X (.atom "bitmap") with
      | none => rfl
      | some x =>
        obtain ⟨p, ok, d⟩ := bitmap_full (TV := TV) (LV := LV) (MV := MV) sX hx
        exact (no "bitmap" p (by simp [names]) ok (by rw [hx]; exact d)).elim
    have funN : mapLookup X (.atom "fun") = none := by
      cases hx : mapLookup X (.atom "fun") with
      | none => rfl
      | some x =>
        have hx' : FunTop x := st.fz (fieldC_fun (sX.fields _ x hx)) (cX.2 "fun" x (by decide) hx)
        obtain ⟨a, ρ, r, f⟩ := st.fvw
        refine (no "fun" (0, a, ρ) (by simp [names]) (ptOk_fun r f) ?_).elim
        rw [hx, hx', dn_fun]
        simp [funTopT, arityOf, mapLookup]
    have listN : mapLookup X (.atom "list") = none := by
      cases hx : mapLookup X (.atom "list") with
      | none => rfl
      | some x =>
        rw [st.lz (fieldC_list (sX.fields _ x hx)) (cX.2 "list" x (by decide) hx)] at hx
        obtain ⟨ρ, hρ⟩ := st.ks.l.wit
        refine (no "list" (0, .nil, ρ) (by simp [names])
          ⟨st.ks.l.resp ρ hρ, by simp, fun _ => hρ, by simp, by simp⟩ ?_).elim
        rw [hx, dn_list, denL_top]
    have mapN : mapLookup X (.atom "map") = none := by
      cases hx : mapLookup X (.atom "map") with
      | none => rfl
      | some x =>
        obtain ⟨k, rfl⟩ := st.mz (fieldC_map (sX.fields _ x hx)) (cX.2 "map" x (by decide) hx)
        obtain ⟨ρ, hρ⟩ := st.ks.m.wit
        refine (no "map" (0, .nil, ρ) (by simp [names])
          ⟨st.ks.m.resp ρ hρ, by simp, by simp, by simp, fun _ => hρ, by simp⟩ ?_).elim
        rw [hx, dn_map, denO_top]
    have tupB : (mapLookup X (.atom "tuple")).isNone || bt := by
      cases hx : mapLookup X (.atom "tuple") with
      | none => rfl
      | some x =>
        rw [hbt x hx]
        have fx := fieldC_tuple (sX.fields _ x hx)
        have none : ∀ c : Bool, denO x (fun _ => c) = Bool.false := by
          intro c
          cases hc : denO x (fun _ => c)
          · rfl
          · obtain ⟨ρ, hρ, e⟩ := st.treal c fx (cX.1 x hx)
            refine (no "tuple" (0, .nil, ρ) (by simp [names])
              ⟨st.ks.t.resp ρ hρ, by simp, by simp, fun _ => hρ, by simp⟩ ?_).elim
            rw [hx, dn_tuple, e, hc]
        simp [none]
    simp [atomN, bitN, funN, listN, mapN, tupB]

end

/-- Disjointness of element types of the next level under seen sets: a uniform answer, exact when the seen BDDs are
higher than the types. -/
theorem de_sdisj (st : StepOk nd C K Fn TF LF MF TV LV MV FV) {a b : Term} (S : List (Term × Term))
    (ha : DEG Fn TF LF MF a) (hb : DEG Fn TF LF MF b) :
    ∃ s : Bool, (∀ m, K + 14 ≤ m →
        Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) a b (.map S) = .ok (boolAtom s)) ∧
      ∀ N, lh a < N → lh b < N → SafeN N S →
        (s = Bool.true ↔ ∀ v : PtG TV LV MV FV, denD a v → denD b v → False) := by
  have hN : 0 < max (lh a) (lh b) + 1 := by omega
  obtain ⟨s, run⟩ := (st.jops hN).disj (st.nest ha (by omega)) (st.nest hb (by omega)) S
  refine ⟨s, run, fun N la lb safe => ?_⟩
  have r := run (K + 14) (by omega)
  dsimp only at r
  -- with the top type, `disjoint_seen?/3` checks the emptiness of the intersection
  have viaInter : Elixir.Module.Types.Descr.«disjoint_seen?/3» (D (K + 14)) a b (.map S) =
      (Elixir.Module.Types.Descr.«bare_intersection/2» (D (K + 14)) a b).bind
        (fun c => Elixir.Module.Types.Descr.«empty_seen?/2» (D (K + 14)) c (.map S)) →
      (s = Bool.true ↔ ∀ v : PtG TV LV MV FV, denD a v → denD b v → False) := by
    intro e
    obtain ⟨c, hc, rc, sc, lc⟩ := de_inter st ha hb
    obtain ⟨be, re, ee⟩ := de_empty st S hc
    rw [e, rc (K + 14) (by omega)] at r
    have r' : Elixir.Module.Types.Descr.«empty_seen?/2» (D (K + 14)) c (.map S) = .ok (boolAtom s) := r
    rw [re (K + 14) (by omega)] at r'
    have : be = s := by cases be <;> cases s <;> simp_all [boolAtom]
    subst this
    rw [ee N (lc N la lb) safe]
    exact ⟨fun h v h₁ h₂ => h v ((sc v).mpr ⟨h₁, h₂⟩), fun h v hv => h v ((sc v).mp hv).1 ((sc v).mp hv).2⟩
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact viaInter (disj_seen_term_l _ _ _)
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact viaInter (disj_seen_term_r _ _ _)
  constructor
  · intro hs v hva hvb
    subst hs
    have := descr_sdisj_sound st.ks st.fc trivial trivial safe (m := K + 14) (by omega) sA sB la lb r v.1.1 v.1.2 v.2.2
    rw [(denD_map v).mp hva, (denD_map v).mp hvb] at this
    cases this
  · intro h
    have c := descr_sdisj_complete st.ks st.fc trivial trivial safe (m := K + 14) (by omega) sA sB la lb
      fun name p ok => by
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
    rw [c] at r
    cases s <;> simp_all [boolAtom]

/-- Fusing types over fields `TF`, `LF`, and `MF`. -/
def FuseOk (K : Nat) (Fn TF LF MF : Term → Prop) (TV LV MV : (Term → Bool) → Prop)
    (FV : Term → (Term → Bool) → Prop) : Prop :=
  ∀ {a b : Term} (n : Int) {m : Nat}, DEG Fn TF LF MF a → DEG Fn TF LF MF b → compareExact (fuel a b) a b ≠ .eq → K + 14 ≤ m → ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ (DEG Fn TF LF MF r ∧ ∀ v : PtG TV LV MV FV, denD r v ↔ denD a v ∨ denD b v))

/-- Types over the fields of a step are element types. -/
theorem ef_gen (st : StepOk nd C K Fn TF LF MF TV LV MV FV) (fu : FuseOk K Fn TF LF MF TV LV MV FV) :
    EF nd (DEG Fn TF LF MF) (PtG TV LV MV FV) denD tlD (K + 14) where
  pos := by omega
  term := Or.inl rfl
  none := Or.inr ⟨[], rfl, descrC_nil⟩
  den_term := denD_term
  static := fun {a} ha => by
    rcases ha with rfl | ⟨X, rfl, sX⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, rfl, sX.static⟩)
  node := fun {a} ha hn => by
    rcases ha with rfl | ⟨X, rfl, -⟩ <;> obtain ⟨r, st, g, h⟩ := hn <;> simp at h
  low := fun ha z => dg_low st ha z
  cinter := fun ha hb ca cb hm run => dg_cinter st ha hb ca cb hm run
  cdiff := fun ha hb ca cb hm run => dg_cdiff st ha hb ca cb hm run
  cempty := fun ha ca hS hm run => dg_cempty st ha ca hS (by omega) run
  inhabited := ⟨ptWit⟩
  resp := fun he he' h d => de_resp st he he' h d
  union := fun ha hb => de_union st ha hb
  inter := fun ha hb =>
    let ⟨c, hc, run, sem, l⟩ := de_inter st ha hb
    ⟨c, hc, fun m hm => run m (by omega), sem, l⟩
  diff := fun ha hb =>
    let ⟨c, hc, run, sem, l⟩ := de_diff st ha hb
    ⟨c, hc, fun m hm => run m (by omega), sem, l⟩
  opt_union := by intro a b S m ha hb hm; exact de_opt_union st S ha hb (by omega)
  opt_inter := by intro a b S m ha hb hm; exact de_opt_inter st S ha hb (by omega)
  opt_diff := by intro a b S m ha hb hm; exact de_opt_diff st S ha hb (by omega)
  empty := fun S ha =>
    let ⟨b, run, ex⟩ := de_empty st S ha
    ⟨b, fun m hm => run m (by omega), ex⟩
  sub := fun ha hb => de_sub st ha hb
  subc := fun ha hb incl m hm => de_subc st ha hb incl hm
  disj := fun ha hb => de_disj st ha hb
  sdisj := fun S ha hb => de_sdisj st S ha hb
  fuse := by intro a b n m ha hb ne hm; exact fu n ha hb ne hm
  tail := fun he => let ⟨e', run, he', sem, l⟩ := de_tail st he; ⟨e', fun m _ => run (D m), he', sem, l⟩
  tl_witness := ⟨ptWit, by simp [tlD, ptWit]⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem stepOf (ef : EF nd E V den tl K) (hnone : E (.map [])) :
    StepOk nd (fun N => NestC (EB E N)) (K + 9) (FunA E) (TField E) (LF E) (MField E) (ValT E den) (ValLN E den tl)
      (ValMN E den) (FVal E den) :=
  ⟨(kinds ef).mono (by omega), funAC ef ef.subc, funA_top, fun hx z => funA_lh0 hx z, fVal_wit,
    fun ha h => de_nest ef ha h,
    fun hN => let ⟨o, d, f⟩ := nest_ops ef hnone hN; ⟨o.mono (by omega), d.mono (by omega), f.mono (by omega)⟩,
    fun hN => (nest_disj ef hnone hN).mono (by omega),
    tz_of, lz_of ef, mz_of, fun c _ fx px => treal_of ef c fx px⟩

theorem de_fuse (ef : EF nd E V den tl K) (hnone : E (.map [])) {a b : Term} (n : Int) {m : Nat} (ha : DE E a)
    (hb : DE E b) (ne : compareExact (fuel a b) a b ≠ .eq) (hm : K + 23 ≤ m) : ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ (DE E r ∧ ∀ v : PtD E den tl (FVal E den), denD r v ↔ denD a v ∨ denD b v)) := by
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, fuse_term_l _ _ _, Or.inl rfl⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, fuse_term_r _ _ _, Or.inl rfl⟩
  obtain ⟨u, hu, urun, usem, -⟩ := de_union (stepOf ef hnone) (Or.inr ⟨A, rfl, sA⟩) (Or.inr ⟨B, rfl, sB⟩)
  have run := urun m hm
  obtain ⟨c₁, r₁⟩ := aob_bool (.map A)
  obtain ⟨c₂, r₂⟩ := aob_bool (.map B)
  have second : ∃ r, (do
      let _19 ← Lynx.Except.andAlso (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A))
        (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B)) Bool.true
      Lynx.Except.guard (Except.ok (_19.isMember [Term.atom "false", Term.atom "nil"]))
        (fun _ => pure (Term.atom "nil")) fun _ => Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B)) = .ok r ∧
      (r = .atom "nil" ∨ (DE E r ∧ ∀ v : PtD E den tl (FVal E den), denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
    rw [r₁, r₂]
    cases c₁ <;> cases c₂ <;>
      simp [Lynx.Except.andAlso, boolAtom, isMember, run, hu, usem]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3».eq_def]
  simp only [getMapKeys_single]
  split
  · rename_i k₀ tag e₁ hA
    have hxA : mapLookup A (.atom "tuple") = some (.tuple ⟨[k₀, tag, e₁]⟩) := by
      cases h : mapLookup A (.atom "tuple") <;> simp_all
    obtain ⟨kA, tA, lA, eA, gA, elA⟩ := tfield_three (fieldC_tuple (sA.fields _ _ hxA)) rfl
    obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj eA
    split
    · rename_i k₁ tag₂ e₂ hB
      have hxB : mapLookup B (.atom "tuple") = some (.tuple ⟨[k₁, tag₂, e₂]⟩) := by
        cases h : mapLookup B (.atom "tuple") <;> simp_all
      obtain ⟨kB, tB, lB, eB, gB, elB⟩ := tfield_three (fieldC_tuple (sB.fields _ _ hxB)) rfl
      obtain ⟨rfl, rfl, rfl⟩ := tuple3_inj eB
      obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      have fallback : ∀ (x : Except Exception Term),
          (∀ c₁ c₂ : Bool, Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A) = .ok (boolAtom c₁) →
            Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B) = .ok (boolAtom c₂) →
            x = .ok (if c₁ && c₂ then u else .atom "nil")) →
          ∃ r, x = .ok r ∧ (r = .atom "nil" ∨ (DE E r ∧ ∀ v : PtD E den tl (FVal E den), denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
        intro x hx
        refine ⟨_, hx c₁ c₂ r₁ r₂, ?_⟩
        cases c₁ <;> cases c₂ <;> simp [hu, usem]
      by_cases G : tB = tA ∧ sa = 1 ∧ sb = 1 ∧ 0 < n
      · obtain ⟨rfl, rfl, rfl, pos⟩ := G
        have sub : Erlang.erlang.«-/2» (.integer n) (.integer 1) = .ok (.integer (n - 1)) := by
          rw [Erlang.erlang.«-/2_integers»]
        have pc : compare n 0 = Ordering.gt := by exact Int.compare_eq_gt.mpr pos
        obtain ⟨r, rr, out⟩ := fuse_elements_sem ef (m := m) (by omega) (n - 1) lA lB [] elA elB (by simp)
        rcases out with rfl | ⟨l, rfl, hl, ll, sl⟩
        · refine ⟨_, ?_, Or.inl rfl⟩
          simp only [Term.list] at rr
          simp [hsa, hsb, Erlang.erlang.«=:=/2», Lynx.Except.andAlso,
            Erlang.erlang.«and/2», Erlang.erlang.«==/2», Erlang.erlang.«>/2», pc, rr, isMember]
        · obtain ⟨k, hk, key⟩ := leaf_new_key tB gA l
          have nf : Term.compareExact (Term.fuel (Term.list l) (.atom "false")) (Term.list l) (.atom "false") ≠ .eq ∧ Term.compareExact (Term.fuel (Term.list l) (.atom "nil")) (Term.list l) (.atom "nil") ≠ .eq := by
            cases l <;> simp [Term.list]
          refine ⟨_, ?_, Or.inr ⟨fused_de gA hl key,
            fused_sem ef gA elA elB hl hxA hsa hxB hsb fun w => by simpa using sl (tB == "closed") w⟩⟩
          simp [hsa, hsb, Erlang.erlang.«=:=/2», Lynx.Except.andAlso,
            Erlang.erlang.«and/2», Erlang.erlang.«==/2», Erlang.erlang.«>/2», pc, rr, isMember, hk, nf.1, nf.2]
      · refine fallback _ fun c₁ c₂ r₁ r₂ => ?_
        have pc : compare n 0 = Ordering.gt ↔ 0 < n := Int.compare_eq_gt
        by_cases e₁ : tB = tA <;> by_cases e₂ : sa = 1 <;> by_cases e₃ : sb = 1 <;> by_cases e₄ : 0 < n <;>
          simp only [e₁, e₂, e₃, e₄, and_self, not_true_eq_false] at G <;>
          cases c₁ <;> cases c₂ <;>
          simp [hsa, hsb, e₁, e₂, e₃, e₄, pc, r₁, r₂, run, Erlang.erlang.«=:=/2»,
            Lynx.Except.andAlso, Erlang.erlang.«and/2», Erlang.erlang.«==/2»,
            Erlang.erlang.«>/2», isMember, boolAtom]
    · exact second
  · exact second

/-- The step from element types to types over them. -/
theorem ef_step (ef : EF nd E V den tl K) (hnone : E (.map [])) :
    EF nd (DE E) (PtD E den tl (FVal E den)) denD tlD (K + 23) :=
  ef_gen (stepOf ef hnone) fun {_ _} n {_} ha hb ne hm => de_fuse ef hnone n ha hb ne hm

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types with the node: operations on the node compute on its expansion. -/

theorem opt_union_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b S : Term)
    (hb : b ≠ .atom "term") (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) e b S =
      Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) (expN e k) b S := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def, Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem opt_union_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a S : Term)
    (ha : a ≠ .atom "term") (none : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) a e S =
      Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) a (expN e k) S := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def, Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem opt_inter_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b S : Term)
    (hb : b ≠ .atom "term") :
    Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) e b S =
      Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) (expN e k) b S := by
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_intersection/3».eq_def, Elixir.Module.Types.Descr.«opt_intersection/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [unfold_map, expN]
  all_goals simp_all [unfold_map, expN]

theorem opt_inter_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a S : Term)
    (ha : a ≠ .atom "term") :
    Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) a e S =
      Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) a (expN e k) S := by
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_intersection/3».eq_def, Elixir.Module.Types.Descr.«opt_intersection/3».eq_def]
  cases a
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) ha
    · simp_all [unfold_map, expN]
  all_goals simp_all [unfold_map, expN]

theorem opt_diff_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (b S : Term)
    (hb : b ≠ .atom "term") (none : ¬Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) e b S =
      Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) (expN e k) b S := by
  obtain ⟨S₀, rfl, -⟩ := h
  have tne : Term.compare (Term.fuel (Term.tuple #[.reference r, .map S₀, gen]) (.atom "term")) (Term.tuple #[.reference r, .map S₀, gen]) (.atom "term") ≠ .eq := by
    rw [Term.compare_step]; simp [Compare.compareStep]
  have ene : Term.compare (Term.fuel (expN (.tuple #[.reference r, .map S₀, gen]) k) (.atom "term")) (expN (.tuple #[.reference r, .map S₀, gen]) k) (.atom "term") ≠ .eq := by
    simp only [expN]; rw [Term.compare_step]; simp [Compare.compareStep]
  rw [Elixir.Module.Types.Descr.«opt_difference/3».eq_def, Elixir.Module.Types.Descr.«opt_difference/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) hb
    · simp_all [Erlang.erlang.«==/2», unfold_map, expN, Elixir.Module.Types.Descr.«unfold/1»]
  all_goals simp_all [Erlang.erlang.«==/2», unfold_map, expN, Elixir.Module.Types.Descr.«unfold/1»]

theorem opt_diff_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (m : Nat) {k : Int}
    (run : Elixir.Module.Types.Descr.«expand_node/1» (D (m + 1)) e = .ok (expN e k)) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) a e S =
      Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 1)) a (expN e k) S := by
  have ne := node_ne_none h
  have ne' := expN_ne_none e k
  obtain ⟨S₀, rfl, -⟩ := h
  rw [Elixir.Module.Types.Descr.«opt_difference/3».eq_def, Elixir.Module.Types.Descr.«opt_difference/3».eq_def]
  simp_all [Erlang.erlang.«==/2», unfold_map, expN]

theorem opt_union_none_l (d : Dispatcher) {a b S : Term} (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (none : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) : Elixir.Module.Types.Descr.«opt_union/3» d a b S = .ok b := by
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem opt_union_none_r (d : Dispatcher) {a b S : Term} (at' : a ≠ .atom "term") (bt : b ≠ .atom "term")
    (na : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_union/3» d a b S = .ok a := by
  rw [Elixir.Module.Types.Descr.«opt_union/3».eq_def]
  split
  · exact absurd rfl at'
  · exact absurd rfl bt
  · simp_all [Erlang.erlang.«==/2»]

theorem opt_diff_none_r (d : Dispatcher) {a b S : Term} (bt : b ≠ .atom "term") (none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq) :
    Elixir.Module.Types.Descr.«opt_difference/3» d a b S = .ok a := by
  rw [Elixir.Module.Types.Descr.«opt_difference/3».eq_def]
  cases b
  case atom name =>
    by_cases ht : name = "term"
    · exact absurd (by rw [ht]) bt
    · simp_all [Erlang.erlang.«==/2»]
  all_goals simp_all [Erlang.erlang.«==/2»]

theorem fuse_node_l {r : List Nat} {e : Term} (h : NodeAt r e) (d : Dispatcher) (b n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d e b n = .ok (.atom "nil") := by
  obtain ⟨S, rfl, -⟩ := h
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3»
  simp [Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1», getMapKeys]
  repeat' split
  all_goals simp_all [Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«map_size/1»]

theorem aob_node {r : List Nat} {S : List (Term × Term)} {g : Term} :
    Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.tuple #[.reference r, .map S, g]) = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1»
  simp [getMapKeys]

theorem fuse_node_r {r : List Nat} {e : Term} (h : NodeAt r e) (d : Dispatcher) (a n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d a e n = .ok (.atom "nil") := by
  obtain ⟨S, rfl, -⟩ := h
  obtain ⟨c, rc⟩ := aob_bool a
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3».eq_def]
  simp only [getMapKeys_tuple]
  split <;> cases c <;> simp [rc, aob_node, Lynx.Except.andAlso, boolAtom, isMember]

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types and the node `nd`. -/
def DEN (nd : Term) (E : Term → Prop) (a : Term) : Prop := E a ∨ IsT nd a

/-- The node holds the values of its expansion. -/
def denN (nd : Term) (den : Term → V → Prop) (a : Term) (v : V) : Prop :=
  (IsT nd a ∧ den (expN a (keyOf nd)) v) ∨ (¬IsT nd a ∧ den a v)

/-- Classes that hold the expansions of the node `nd`, and no node. -/
structure NodeOk (nd : Term) (E : Term → Prop) : Prop where
  exp : ∀ {e}, IsT nd e → E (expN e (keyOf nd))
  notN : ∀ {a}, E a → ¬IsT nd a

theorem isT_term : ¬IsT nd (.atom "term") := fun he => node_ne_term he rfl

theorem lh_expN {e : Term} (he : IsT nd e) : lh (expN e (keyOf nd)) = 1 := by
  apply Nat.le_antisymm
  · refine lh_map_le.mpr fun x mx => ?_
    have := mem_of_mem_mapEntries mx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
    have la : lh (.tuple #[.atom "union", .map [(.atom "nil", .nil)]]) = 0 :=
      lh_atomF ⟨⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil",
        by simp [amemV, mapLookup]⟩
    rcases this with rfl | rfl
    · exact Nat.le_of_eq (lh_litN he _)
    · simp only [la]; omega
  · have := lh_field_le (X := [(.atom "tuple", litN e (keyOf nd)), (.atom "atom", .tuple #[.atom "union",
      .map [(.atom "nil", .nil)]])]) (q := .atom "tuple") (x := litN e (keyOf nd)) (by simp [mapLookup])
    rw [lh_litN he _] at this
    exact this

theorem combo_expN {e : Term} (he : IsT nd e) : Combo nd (expN e (keyOf nd)) := by
  refine combo_map.mpr ⟨fun w hw => ?_, fun name w nt hw => ?_⟩
  · simp [mapLookup] at hw
    subst hw
    exact Or.inr (Bdd.leaf_iff.mpr ⟨e, he, rfl⟩)
  · simp only [mapLookup, List.find?_cons, compareExact_eq_atom, Term.atom.injEq, equalExact_eq_decide] at hw
    by_cases t : name = "tuple"
    · exact absurd t nt
    · by_cases a : name = "atom"
      · subst a; simp at hw; subst hw
        exact lh_atomF ⟨⟨Bool.true, [(.atom "nil", .nil)], rfl, by simp [Erlang.sets.elements?]⟩, .atom "nil",
          by simp [amemV, mapLookup]⟩
      · simp [t, a] at hw

theorem denN_of {a : Term} {v : V} (hn : ¬IsT nd a) : denN nd den a v ↔ den a v := by
  simp [denN, hn]

theorem denN_node {a : Term} {v : V} (hn : IsT nd a) : denN nd den a v ↔ den (expN a (keyOf nd)) v := by
  simp [denN, hn]

/-- A type of the class with the node, as a type of the class: the node as its expansion. -/
theorem NodeOk.red (h : NodeOk nd E) {a : Term} (ha : DEN nd E a) : ∃ A, E A ∧ (∀ v, denN nd den a v ↔ den A v) ∧
    lh A = lh a ∧ (Combo nd a → Combo nd A) ∧ (a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd))) := by
  rcases ha with ha | ha
  · exact ⟨a, ha, fun v => denN_of (h.notN ha), rfl, id, Or.inl rfl⟩
  · exact ⟨_, h.exp ha, fun v => denN_node ha, by rw [lh_expN ha, lh_isT ha], fun _ => combo_expN ha, Or.inr ⟨ha, rfl⟩⟩

theorem DEN.ne_term {a A : Term} (r : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd))) (at' : a ≠ .atom "term") :
    A ≠ .atom "term" := by
  rcases r with rfl | ⟨-, rfl⟩
  · exact at'
  · exact expN_ne_term _ _

theorem DEN.ne_none {a A : Term} (r : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd)))
    (na : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq) : ¬Term.compare (Term.fuel A (.map [])) A (.map []) = .eq := by
  rcases r with rfl | ⟨-, rfl⟩
  · exact na
  · exact expN_ne_none _ _

theorem isT_ne_none {a : Term} (ha : IsT nd a) : ¬Term.compare (Term.fuel a (.map [])) a (.map []) = .eq := node_ne_none ha.node

theorem red_inter {a b A B : Term} (ra : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd)))
    (rb : b = B ∨ (IsT nd b ∧ B = expN b (keyOf nd))) (bt : b ≠ .atom "term") (nA : A ≠ .atom "term") (m : Nat) :
    Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A B := by
  have e₁ : Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) A b := by
    rcases ra with rfl | ⟨t, rfl⟩
    · rfl
    · exact inter_node_l t.node m (expand_isT t m) b bt
  rw [e₁]
  rcases rb with rfl | ⟨t, rfl⟩
  · rfl
  · exact inter_node_r t.node m (expand_isT t m) A nA

theorem red_diff {a b A B : Term} (ra : a = A ∨ (IsT nd a ∧ A = expN a (keyOf nd)))
    (rb : b = B ∨ (IsT nd b ∧ B = expN b (keyOf nd))) (nB : B ≠ .atom "term") (eB : ¬Term.compare (Term.fuel B (.map [])) B (.map []) = .eq)
    (m : Nat) :
    Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) A B := by
  have e₁ : Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a b =
      Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 1)) a B := by
    rcases rb with rfl | ⟨t, rfl⟩
    · rfl
    · exact diff_node_r t.node m (expand_isT t m) a
  rw [e₁]
  rcases ra with rfl | ⟨t, rfl⟩
  · rfl
  · exact diff_node_l t.node m (expand_isT t m) B nB eB

theorem an_inter (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ c, DEN nd E c ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
      (∀ v, denN nd den c v ↔ denN nd den a v ∧ denN nd den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨a, ha, fun m _ => inter_term_right _ _, fun v => ⟨fun x => ⟨x, dt v⟩, fun x => x.1⟩, fun N h₁ _ => h₁⟩
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨b, hb, fun m _ => inter_term_left _ _, fun v => ⟨fun x => ⟨dt v, x⟩, fun x => x.2⟩, fun N _ h₂ => h₂⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  obtain ⟨c, hc, run, sem, lc⟩ := ef.inter eA eB
  refine ⟨c, Or.inl hc, fun m hm => ?_, fun v => ?_, fun N h₁ h₂ => lc N (by omega) (by omega)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [red_inter rA rB bt (DEN.ne_term rA at') m']
    exact run _ (by omega)
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_diff (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ c, DEN nd E c ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
      (∀ v, denN nd den c v ↔ denN nd den a v ∧ ¬denN nd den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  have dn0 : ∀ v, ¬denN nd den (.map []) v := fun v d =>
    ef.den_none v ((denN_of (fun t => isT_map t)).mp d)
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.none, fun m _ => diff_term_right _ _, fun v => ⟨fun x => absurd x (dn0 v),
      fun x => absurd (dt v) x.2⟩, fun N _ _ => by rw [lh_nil_map]; omega⟩
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · have nb : ∀ v, ¬denN nd den b v := by
      rcases rB with rfl | ⟨t, -⟩
      · exact fun v d => ef.den_none' eB none v ((sB v).mp d)
      · exact absurd none (isT_ne_none t)
    exact ⟨a, ha, fun m _ => diff_none _ a b bt none, fun v => ⟨fun x => ⟨x, nb v⟩, fun x => x.1⟩, fun N h₁ _ => h₁⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨c, hc, run, sem, lc⟩ := ef.diff eA eB
  refine ⟨c, Or.inl hc, fun m hm => ?_, fun v => ?_, fun N h₁ h₂ => lc N (by omega) (by omega)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [red_diff rA rB (DEN.ne_term rB bt) (DEN.ne_none rB none) m']
    exact run _ (by omega)
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_union (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ c, DEN nd E c ∧ (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
      (∀ v, denN nd den c v ↔ denN nd den a v ∨ denN nd den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨_, Or.inl ef.term, fun m _ => union_term_l _ _, fun v => ⟨fun _ => Or.inl (dt v), fun _ => dt v⟩,
      fun N h₁ _ => h₁⟩
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.term, fun m _ => union_any_term _ _, fun v => ⟨fun _ => Or.inr (dt v), fun _ => dt v⟩,
      fun N _ h₂ => h₂⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  have nemp : ∀ {x X}, DEN nd E x → Term.compare (Term.fuel x (.map [])) x (.map []) = .eq → (x = X ∨ (IsT nd x ∧ X = expN x (keyOf nd))) →
      E X → (∀ v, denN nd den x v ↔ den X v) → ∀ v, ¬denN nd den x v := by
    intro x X _ none r eX s v d
    rcases r with rfl | ⟨t, -⟩
    · exact ef.den_none' eX none v ((s v).mp d)
    · exact absurd none (isT_ne_none t)
  by_cases na : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq
  · exact ⟨b, hb, fun m _ => union_none _ a b at' bt na,
      fun v => ⟨Or.inr, fun x => x.elim (fun d => absurd d (nemp ha na rA eA sA v)) id⟩, fun N _ h₂ => h₂⟩
  by_cases nb : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · exact ⟨a, ha, fun m _ => union_none_r _ a b at' bt na nb,
      fun v => ⟨Or.inl, fun x => x.elim id (fun d => absurd d (nemp hb nb rB eB sB v))⟩, fun N h₁ _ => h₁⟩
  obtain ⟨c, hc, run, sem, lc⟩ := ef.union eA eB
  refine ⟨c, Or.inl hc, fun m hm => ?_, fun v => ?_, fun N h₁ h₂ => lc N (by omega) (by omega)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) a b =
        Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) A b := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact union_node_l t.node m' (expand_isT t m') b bt nb
    have e₂ : Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) A b =
        Elixir.Module.Types.Descr.«bare_union/2» (D (m' + 1)) A B := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact union_node_r t.node m' (expand_isT t m') A (DEN.ne_term rA at') (DEN.ne_none rA na)
    rw [e₁, e₂]
    exact run _ (by omega)
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_opt_union (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (S : List (Term × Term)) {m : Nat}
    (ha : DEN nd E a) (hb : DEN nd E b) (hm : K + 1 ≤ m) : ∃ c, DEN nd E c ∧
      Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧
      ∀ v, denN nd den c v ↔ denN nd den a v ∨ denN nd den b v := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨_, Or.inl ef.term, opt_union_term_left _ _ _, fun v => ⟨fun _ => Or.inl (dt v), fun _ => dt v⟩⟩
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.term, opt_union_term_r _ _ _, fun v => ⟨fun _ => Or.inr (dt v), fun _ => dt v⟩⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  have nemp : ∀ {x X}, DEN nd E x → Term.compare (Term.fuel x (.map [])) x (.map []) = .eq → (x = X ∨ (IsT nd x ∧ X = expN x (keyOf nd))) →
      E X → (∀ v, denN nd den x v ↔ den X v) → ∀ v, ¬denN nd den x v := by
    intro x X _ none r eX s v d
    rcases r with rfl | ⟨t, -⟩
    · exact ef.den_none' eX none v ((s v).mp d)
    · exact absurd none (isT_ne_none t)
  by_cases na : Term.compare (Term.fuel a (.map [])) a (.map []) = .eq
  · exact ⟨b, hb, opt_union_none_l _ at' bt na,
      fun v => ⟨Or.inr, fun x => x.elim (fun d => absurd d (nemp ha na rA eA sA v)) id⟩⟩
  by_cases nb : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · exact ⟨a, ha, opt_union_none_r _ at' bt na nb,
      fun v => ⟨Or.inl, fun x => x.elim id (fun d => absurd d (nemp hb nb rB eB sB v))⟩⟩
  obtain ⟨c, hc, run, sem⟩ := ef.opt_union S eA eB (show K ≤ m by omega)
  refine ⟨c, Or.inl hc, ?_, fun v => ?_⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) a b (.map S) =
        Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) A b (.map S) := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_union_node_l t.node m' (expand_isT t m') b _ bt nb
    have e₂ : Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) A b (.map S) =
        Elixir.Module.Types.Descr.«opt_union/3» (D (m' + 1)) A B (.map S) := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_union_node_r t.node m' (expand_isT t m') A _ (DEN.ne_term rA at') (DEN.ne_none rA na)
    rw [e₁, e₂, run]
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_opt_inter (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (S : List (Term × Term)) {m : Nat}
    (ha : DEN nd E a) (hb : DEN nd E b) (hm : K + 1 ≤ m) : ∃ c, DEN nd E c ∧
      Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧
      ∀ v, denN nd den c v ↔ denN nd den a v ∧ denN nd den b v := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  by_cases at' : a = .atom "term"
  · subst at'
    exact ⟨b, hb, opt_inter_term_l _ _ _, fun v => ⟨fun x => ⟨dt v, x⟩, fun x => x.2⟩⟩
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨a, ha, opt_inter_term_r _ _ _, fun v => ⟨fun x => ⟨x, dt v⟩, fun x => x.1⟩⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  obtain ⟨c, hc, run, sem⟩ := ef.opt_inter S eA eB (show K ≤ m by omega)
  refine ⟨c, Or.inl hc, ?_, fun v => ?_⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) a b (.map S) =
        Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) A b (.map S) := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_inter_node_l t.node m' (expand_isT t m') b _ bt
    have e₂ : Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) A b (.map S) =
        Elixir.Module.Types.Descr.«opt_intersection/3» (D (m' + 1)) A B (.map S) := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_inter_node_r t.node m' (expand_isT t m') A _ (DEN.ne_term rA at')
    rw [e₁, e₂, run]
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_opt_diff (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (S : List (Term × Term)) {m : Nat}
    (ha : DEN nd E a) (hb : DEN nd E b) (hm : K + 1 ≤ m) : ∃ c, DEN nd E c ∧
      Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧
      ∀ v, denN nd den c v ↔ denN nd den a v ∧ ¬denN nd den b v := by
  have dt := fun v => (denN_of (nd := nd) (den := den) isT_term (v := v)).mpr (ef.den_term v)
  have dn0 : ∀ v, ¬denN nd den (.map []) v := fun v d =>
    ef.den_none v ((denN_of (fun t => isT_map t)).mp d)
  by_cases bt : b = .atom "term"
  · subst bt
    exact ⟨_, Or.inl ef.none, difference_term_term _ _ _, fun v => ⟨fun x => absurd x (dn0 v),
      fun x => absurd (dt v) x.2⟩⟩
  obtain ⟨B, eB, sB, lB, -, rB⟩ := h.red (den := den) hb
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · have nb : ∀ v, ¬denN nd den b v := by
      rcases rB with rfl | ⟨t, -⟩
      · exact fun v d => ef.den_none' eB none v ((sB v).mp d)
      · exact absurd none (isT_ne_none t)
    exact ⟨a, ha, opt_diff_none_r _ bt none, fun v => ⟨fun x => ⟨x, nb v⟩, fun x => x.1⟩⟩
  obtain ⟨A, eA, sA, lA, -, rA⟩ := h.red (den := den) ha
  obtain ⟨c, hc, run, sem⟩ := ef.opt_diff S eA eB (show K ≤ m by omega)
  refine ⟨c, Or.inl hc, ?_, fun v => ?_⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e₁ : Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) a b (.map S) =
        Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) a B (.map S) := by
      rcases rB with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_diff_node_r t.node m' (expand_isT t m') a _
    have e₂ : Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) a B (.map S) =
        Elixir.Module.Types.Descr.«opt_difference/3» (D (m' + 1)) A B (.map S) := by
      rcases rA with rfl | ⟨t, rfl⟩
      · rfl
      · exact opt_diff_node_l t.node m' (expand_isT t m') B _ (DEN.ne_term rB bt) (DEN.ne_none rB none)
    rw [e₁, e₂, run]
  · rw [denN_of (h.notN hc), sA, sB]; exact sem v

theorem an_cinter (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b c : Term} {m : Nat} (ha : DEN nd E a)
    (hb : DEN nd E b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 1 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) : Combo nd c := by
  by_cases bt : b = .atom "term"
  · subst bt; rw [inter_term_right] at run; cases run; exact ca
  by_cases at' : a = .atom "term"
  · subst at'; rw [inter_term_left] at run; cases run; exact cb
  obtain ⟨A, eA, -, -, cA, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, -, -, cB, rB⟩ := h.red (den := den) hb
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [red_inter rA rB bt (DEN.ne_term rA at') m'] at run
  exact ef.cinter eA eB (cA ca) (cB cb) (by omega) run

theorem an_cdiff (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b c : Term} {m : Nat} (ha : DEN nd E a)
    (hb : DEN nd E b) (ca : Combo nd a) (cb : Combo nd b) (hm : K + 1 ≤ m)
    (run : Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) : Combo nd c := by
  by_cases bt : b = .atom "term"
  · subst bt; rw [diff_term_right] at run; cases run; exact combo_none nd
  by_cases none : Term.compare (Term.fuel b (.map [])) b (.map []) = .eq
  · rw [diff_none _ a b bt none] at run; cases run; exact ca
  obtain ⟨A, eA, -, -, cA, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, -, -, cB, rB⟩ := h.red (den := den) hb
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [red_diff rA rB (DEN.ne_term rB bt) (DEN.ne_none rB none) m'] at run
  exact ef.cdiff eA eB (cA ca) (cB cb) (by omega) run

/-- Expansions of the node hold values: nil. -/
theorem EF.expN_inh (ef : EF nd E V den tl K) {e : Term} (he : E (expN e (keyOf nd))) :
    ∃ v, den (expN e (keyOf nd)) v := by
  obtain ⟨b, run, ex⟩ := ef.empty [] he
  have r := run K (Nat.le_refl _)
  rw [empty_expN] at r
  have : b = Bool.false := by cases b <;> simp_all [boolAtom]
  subst this
  have hx := ex (lh (expN e (keyOf nd)) + 1) (Nat.lt_succ_self _) (safeN_nil _)
  exact Classical.byContradiction fun hn => absurd (hx.mpr fun w hw => hn ⟨w, hw⟩) (by decide)

theorem an_empty (ef : EF nd E V den tl K) (h : NodeOk nd E) {a : Term} (S : List (Term × Term)) (ha : DEN nd E a) :
    ∃ b : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh a < N → SafeN N S → (b = Bool.true ↔ ∀ v, ¬denN nd den a v) := by
  rcases ha with ha | ha
  · obtain ⟨b, run, ex⟩ := ef.empty S ha
    refine ⟨b, fun m hm => run m (by omega), fun N hN hS => ?_⟩
    rw [ex N hN hS]
    exact ⟨fun x v d => x v ((denN_of (h.notN ha)).mp d), fun x v d => x v ((denN_of (h.notN ha)).mpr d)⟩
  · refine ⟨idIn (refOf nd) S, fun m hm => ?_, fun N _ hS => ?_⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact empty_node ha.node m' S
    · rw [safeN_noid hS]
      obtain ⟨v, hv⟩ := ef.expN_inh (h.exp ha)
      exact ⟨fun x => absurd x (by decide), fun x => absurd ((denN_node ha).mpr hv) (x v)⟩

theorem an_cempty (ef : EF nd E V den tl K) (h : NodeOk nd E) {a : Term} {S : List (Term × Term)} {m : Nat} {b : Bool}
    (ha : DEN nd E a) (ca : Combo nd a) (hS : Safe1 nd S) (hm : K + 1 ≤ m)
    (run : Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v, ¬denN nd den a v := by
  rcases ha with ha | ha
  · rw [ef.cempty ha ca hS (by omega) run]
    exact ⟨fun x v d => x v ((denN_of (h.notN ha)).mp d), fun x v d => x v ((denN_of (h.notN ha)).mpr d)⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [empty_node ha.node m' S] at run
    have := safeN_noid hS.1 (refOf nd)
    simp only [idIn] at this
    rw [this] at run
    have : b = Bool.false := by cases b <;> simp_all [boolAtom]
    subst this
    obtain ⟨v, hv⟩ := ef.expN_inh (h.exp ha)
    exact ⟨fun x => absurd x (by decide), fun x => absurd ((denN_node ha).mpr hv) (x v)⟩

theorem an_sub (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ s : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v, denN nd den a v → denN nd den b v) := by
  obtain ⟨A, eA, sA, -, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, -, -, rB⟩ := h.red (den := den) hb
  obtain ⟨s, run, sound⟩ := ef.sub eA eB
  refine ⟨s, fun m hm => ?_, fun st v d => (sB v).mpr (sound st v ((sA v).mp d))⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e₁ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b := by
    rcases rA with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_l t.node m' (expand_isT t m') b
  have e₂ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A B := by
    rcases rB with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_r t.node m' (expand_isT t m') A
  rw [e₁, e₂]
  exact run _ (by omega)

theorem an_subc (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b)
    (incl : ∀ v, denN nd den a v → denN nd den b v) {m : Nat} (hm : K + 1 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true") := by
  obtain ⟨A, eA, sA, -, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, -, -, rB⟩ := h.red (den := den) hb
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e₁ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) a b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b := by
    rcases rA with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_l t.node m' (expand_isT t m') b
  have e₂ : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A b =
      Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) A B := by
    rcases rB with rfl | ⟨t, rfl⟩
    · rfl
    · exact sub_node_r t.node m' (expand_isT t m') A
  rw [e₁, e₂]
  exact ef.subc eA eB (fun v d => (sB v).mp (incl v ((sA v).mpr d))) _ (by omega)

theorem static_map_of (ef : EF nd E V den tl K) {b : Term} (hb : DEN nd E b) :
    ∀ X, b = .map X → mapLookup X (.atom "dynamic") = none := by
  intro X e
  subst e
  rcases hb with hb | hb
  · rcases ef.static hb with h | ⟨Y, h, sY⟩ | ⟨r, st, g, h⟩
    · cases h
    · cases h; exact sY
    · cases h
  · exact absurd hb isT_map

theorem an_disj (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ s : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
      (s = Bool.true → ∀ v, denN nd den a v → denN nd den b v → False) := by
  -- the top type and the node: `disjoint?/2` checks the emptiness of the node, which holds nil
  by_cases ct : (a = .atom "term" ∧ IsT nd b) ∨ (IsT nd a ∧ b = .atom "term")
  · refine ⟨Bool.false, fun m hm => ?_, fun st => by cases st⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases ct with ⟨rfl, hb⟩ | ⟨ha, rfl⟩
    · rw [disjoint_term_l, empty_any_node hb m']; rfl
    · rw [disj_term_r, empty_any_node ha m']; rfl
  obtain ⟨A, eA, sA, -, -, rA⟩ := h.red (den := den) ha
  obtain ⟨B, eB, sB, -, -, rB⟩ := h.red (den := den) hb
  obtain ⟨s, run, sound⟩ := ef.disj eA eB
  refine ⟨s, fun m hm => ?_, fun st v da db => sound st v ((sA v).mp da) ((sB v).mp db)⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [← run (m' + 1) (by omega)]
  by_cases at' : a = .atom "term"
  · subst at'
    rcases rA with rfl | ⟨t, -⟩
    · rcases rB with rfl | ⟨t, -⟩
      · rfl
      · exact absurd (Or.inl ⟨rfl, t⟩) ct
    · exact absurd t isT_term
  by_cases bt : b = .atom "term"
  · subst bt
    rcases rB with rfl | ⟨t, -⟩
    · rcases rA with rfl | ⟨t, -⟩
      · rfl
      · exact absurd (Or.inr ⟨t, rfl⟩) ct
    · exact absurd t isT_term
  have e₁ : Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) a b =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A b := by
    rcases rA with rfl | ⟨t, rfl⟩
    · rfl
    · exact disj_node_l t.node m' (expand_isT t m') b bt (static_map_of ef hb)
  have e₂ : Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A b =
      Elixir.Module.Types.Descr.«disjoint?/2» (D (m' + 1)) A B := by
    rcases rB with rfl | ⟨t, rfl⟩
    · rfl
    · refine disj_node_r t.node m' (expand_isT t m') A (DEN.ne_term rA at') fun X e => ?_
      rcases rA with rfl | ⟨t', rfl⟩
      · exact static_map_of ef ha X e
      · simp [expN] at e; subst e; simp [mapLookup]
  rw [e₁, e₂]

/-- Disjointness under seen sets: on element types as before, and with the node, the emptiness of the
intersection, which computes on its expansion. -/
theorem an_sdisj (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (S : List (Term × Term))
    (ha : DEN nd E a) (hb : DEN nd E b) :
    ∃ s : Bool, (∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) a b (.map S) = .ok (boolAtom s)) ∧
      ∀ N, lh a < N → lh b < N → SafeN N S → (s = Bool.true ↔ ∀ v, denN nd den a v → denN nd den b v → False) := by
  -- with the node, `disjoint_seen?/3` checks the emptiness of the intersection
  have viaInter : (∀ m, Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) a b (.map S) =
      (Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b).bind
        (fun c => Elixir.Module.Types.Descr.«empty_seen?/2» (D m) c (.map S))) →
      ∃ s : Bool, (∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) a b (.map S) = .ok (boolAtom s)) ∧
      ∀ N, lh a < N → lh b < N → SafeN N S →
        (s = Bool.true ↔ ∀ v, denN nd den a v → denN nd den b v → False) := by
    intro e
    obtain ⟨c, hc, rc, sc, lc⟩ := an_inter ef h ha hb
    obtain ⟨be, re, ee⟩ := an_empty ef h S hc
    refine ⟨be, fun m hm => ?_, fun N la lb safe => ?_⟩
    · rw [e, rc m hm]; exact re m hm
    · rw [ee N (lc N la lb) safe]
      exact ⟨fun h' v h₁ h₂ => h' v ((sc v).mpr ⟨h₁, h₂⟩), fun h' v hv => h' v ((sc v).mp hv).1 ((sc v).mp hv).2⟩
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · obtain ⟨s, run, ex⟩ := ef.sdisj S ha hb
      refine ⟨s, fun m hm => run m (by omega), fun N la lb safe => ?_⟩
      rw [ex N la lb safe]
      exact ⟨fun h' v h₁ h₂ => h' v ((denN_of (h.notN ha)).mp h₁) ((denN_of (h.notN hb)).mp h₂),
        fun h' v h₁ h₂ => h' v ((denN_of (h.notN ha)).mpr h₁) ((denN_of (h.notN hb)).mpr h₂)⟩
    · exact viaInter fun m => disj_seen_nonmap_r (D m) a (.map S) (node_nonmap hb)
  · exact viaInter fun m => disj_seen_nonmap_l (D m) b (.map S) (node_nonmap ha)

theorem an_fuse (ef : EF nd E V den tl K) (h : NodeOk nd E) {a b : Term} (n : Int) {m : Nat} (ha : DEN nd E a)
    (hb : DEN nd E b) (ne : compareExact (fuel a b) a b ≠ .eq) (hm : K + 1 ≤ m) : ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
      (r = .atom "nil" ∨ (DEN nd E r ∧ ∀ v, denN nd den r v ↔ denN nd den a v ∨ denN nd den b v)) := by
  rcases ha with ha | ha
  rotate_left
  · exact ⟨_, fuse_node_l ha.node _ _ _, Or.inl rfl⟩
  rcases hb with hb | hb
  rotate_left
  · exact ⟨_, fuse_node_r hb.node _ _ _, Or.inl rfl⟩
  obtain ⟨r, run, out⟩ := ef.fuse n ha hb ne (show K ≤ m by omega)
  refine ⟨r, run, out.imp id fun ⟨hr, sem⟩ => ⟨Or.inl hr, fun v => ?_⟩⟩
  rw [denN_of (h.notN hr), denN_of (h.notN ha), denN_of (h.notN hb)]
  exact sem v

theorem noList_expN (e : Term) (k : Int) :
    noList [(.atom "tuple", litN e k), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] =
      [(.atom "tuple", litN e k), (.atom "atom", .tuple #[.atom "union", .map [(.atom "nil", .nil)]])] := by
  simp [noList]

theorem an_tail (ef : EF nd E V den tl K) (h : NodeOk nd E) {e : Term} (he : DEN nd E e) :
    ∃ e', (∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«list_tail_unfold/1» (D m) e = .ok e') ∧ DEN nd E e' ∧
      (∀ v, denN nd den e' v ↔ denN nd den e v ∧ ¬tl v) ∧ lh e' ≤ lh e := by
  rcases he with he | he
  · obtain ⟨e', run, he', sem, l⟩ := ef.tail he
    refine ⟨e', run, Or.inl he', fun v => ?_, l⟩
    rw [denN_of (h.notN he'), denN_of (h.notN he)]
    exact sem v
  · obtain ⟨e'', run'', -, sem'', -⟩ := ef.tail (h.exp he)
    have r := run'' 1 (Nat.le_refl _)
    simp only [expN] at r
    rw [tail_map, noList_expN] at r
    simp only [Except.ok.injEq] at r
    subst r
    refine ⟨_, fun m hm => ?_, Or.inl (h.exp he), fun v => ?_, Nat.le_of_eq (by rw [lh_expN he, lh_isT he])⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact tail_node he.node m' (expand_isT he m')
    · rw [denN_of (h.notN (h.exp he)), denN_node he]
      simp only [expN] at sem'' ⊢
      exact ⟨fun d => ⟨d, ((sem'' v).mp d).2⟩, fun d => d.1⟩

theorem node_cmp {r : List Nat} {S : List (Term × Term)} {g x : Term}
    (h : Term.compare (Term.fuel (.tuple #[.reference r, .map S, g]) x) (.tuple #[.reference r, .map S, g]) x = .eq) : IsNode x := by
  cases x <;> rw [compare_step] at h <;> simp [Compare.compareStep] at h
  rename_i ys
  obtain ⟨l⟩ := ys
  match l, h with
  | [a, b, c], h =>
    simp only [List.compareLex_cons_cons, Ordering.then_eq_eq, List.size_toArray, List.length_cons,
      List.length_nil] at h
    obtain ⟨-, ha, hb, -⟩ := h
    cases a <;> rw [compare_step] at ha <;> simp [Compare.compareStep] at ha
    obtain ⟨Y, rfl⟩ := map_cmp_shape hb
    exact ⟨_, _, _, rfl⟩
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | _ :: _ :: _ :: _ :: _, h => simp at h

theorem expN_exact {e e' : Term} (he : IsT nd e) (he' : IsT nd e') (k : Int) :
    compareExact (fuel (expN e k) (expN e' k)) (expN e k) (expN e' k) = .eq := by
  have ee := isT_exact he he'
  apply map_compareExact_eq_of_lookup
  intro q
  simp only [mapLookup, equalExact_eq_decide, List.find?_cons, List.find?_nil]
  by_cases t : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
  · simp [t, litN, Term.list, compareExact_tuple, List.compareLex_cons_cons, compareExact_cons, ee,
      List.compareLex_nil_nil]
  by_cases a : compareExact (fuel q (.atom "atom")) q (.atom "atom") = .eq
  · simp [t, a]
  · simp [t, a]

theorem an_resp (ef : EF nd E V den tl K) (h : NodeOk nd E) {e e' : Term} {v : V} (he : DEN nd E e)
    (he' : DEN nd E e') (c : Term.compare (Term.fuel e e') e e' = .eq) (d : denN nd den e' v) : denN nd den e v := by
  rcases he with he | he <;> rcases he' with he' | he'
  · rw [denN_of (h.notN he')] at d
    rw [denN_of (h.notN he)]
    exact ef.resp he he' c d
  · obtain ⟨S, rfl, -⟩ := he'.node
    exact absurd (ef.node he (node_cmp (Lynx.Term.compare_eq_symm c))) (h.notN he)
  · obtain ⟨S, rfl, -⟩ := he.node
    exact absurd (ef.node he' (node_cmp c)) (h.notN he')
  · rw [denN_node he'] at d
    rw [denN_node he]
    exact ef.resp (h.exp he) (h.exp he') (compare_eq_of_compareExact_eq _ _ (expN_exact he he' _)) d

/-- Element types with the node: operations on the node compute on its expansion. -/
theorem addNode (ef : EF nd E V den tl K) (h : NodeOk nd E) :
    EF nd (DEN nd E) V (denN nd den) tl (K + 1) where
  pos := by omega
  term := Or.inl ef.term
  none := Or.inl ef.none
  den_term := fun v => (denN_of isT_term).mpr (ef.den_term v)
  static := fun {a} ha => by
    rcases ha with ha | ha
    · exact ef.static ha
    · obtain ⟨S, rfl, -⟩ := ha.node; exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
  node := fun {a} ha hn => by
    rcases ha with ha | ha
    · exact ef.node ha hn
    · exact ha
  low := fun {a} ha z => by
    rcases ha with ha | ha
    · exact ef.low ha z
    · rw [lh_isT ha] at z; cases z
  cinter := fun ha hb ca cb hm run => an_cinter ef h ha hb ca cb hm run
  cdiff := fun ha hb ca cb hm run => an_cdiff ef h ha hb ca cb hm run
  cempty := fun ha ca hS hm run => an_cempty ef h ha ca hS hm run
  inhabited := ef.inhabited
  resp := fun he he' c d => an_resp ef h he he' c d
  union := fun ha hb => an_union ef h ha hb
  inter := fun ha hb => an_inter ef h ha hb
  diff := fun ha hb => an_diff ef h ha hb
  opt_union := by intro a b S m ha hb hm; exact an_opt_union ef h S ha hb hm
  opt_inter := by intro a b S m ha hb hm; exact an_opt_inter ef h S ha hb hm
  opt_diff := by intro a b S m ha hb hm; exact an_opt_diff ef h S ha hb hm
  empty := fun S ha => an_empty ef h S ha
  sub := fun ha hb => an_sub ef h ha hb
  subc := fun ha hb incl m hm => an_subc ef h ha hb incl (by omega)
  disj := fun ha hb => an_disj ef h ha hb
  sdisj := fun S ha hb => an_sdisj ef h S ha hb
  fuse := by intro a b n m ha hb ne hm; exact an_fuse ef h n ha hb ne hm
  tail := fun he => an_tail ef h he
  tl_witness := ef.tl_witness

end


/-! The bottom level: types over pure tuple fields, top list and map fields, and the node. -/

theorem pure_of_descr {nd : Term} {X : List (Term × Term)}
    (sX : DescrC FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") X) : PureMap nd X := by
  refine ⟨fun q h => ?_, fun name w hw => ?_⟩
  · obtain ⟨name, m, rfl⟩ := sX.keys q h
    rcases names_mem m with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rcases sX.fields name w hw with ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩ | ⟨rfl, f⟩
    · obtain ⟨b, rfl, h₁, h₂⟩ := f
      exact Or.inl (Or.inl ⟨rfl, b, rfl, h₁, h₂⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, f.1, f.2⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨by decide, by decide, by rw [show w = funTopT from f]; rfl⟩))
    · exact Or.inl f
    · exact Or.inr ⟨rfl, f⟩
    · exact Or.inl f

/-- The step to the bottom level. -/
theorem step0 (nd : Term) : StepOk nd (fun _ => Pure nd) 8 FunTop (OField (PureLit nd)) (FieldOk "list")
    (FieldOk "map") Resp Resp Resp FVT where
  ks := kinds0 nd (by omega)
  fc := fcOf 8
  ftop := rfl
  fz := fun hx _ => hx
  fvw := ⟨.nil, fun _ => Bool.true, resp_const _, trivial⟩
  nest := fun {a N} ha _ => by
    rcases ha with rfl | ⟨X, rfl, sX⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨X, rfl, pure_of_descr sX⟩)
  ops := fun _ => ⟨(pureOk nd).mono (by omega), (pureDiff nd).mono (by omega), (pureFun nd).mono (by omega)⟩
  jops := fun _ => (pureDisj nd).mono (by omega)
  tz := fun {x} fx z => by
    rcases fx with ⟨k, rfl⟩ | wx
    · exact ⟨k, rfl⟩
    · have := pure_one (Or.inr wx) (fun k h => by subst h; exact absurd (Bdd.leaf_iff.mp wx) (pureLit_not _ · ⟨_, rfl⟩))
      omega
  lz := fun {x} fx _ => by
    have := topF_of (Or.inl rfl) fx
    simp [topValue] at this
    exact this.symm
  mz := fun {x} fx _ => by
    have := topF_of (Or.inr rfl) fx
    simp [topValue] at this
    exact ⟨_, this.symm⟩
  treal := fun c {x} _ _ => ⟨fun _ => c, resp_const c, rfl⟩

/-- Maps of a single tuple field are exactly equal when their fields are. -/
theorem single_exact {A B : List (Term × Term)} {x y : Term}
    (tA : mapLookup A (.atom "tuple") = some x) (tB : mapLookup B (.atom "tuple") = some y)
    (sA : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    (sB : Erlang.erlang.«map_size/1» (.map B) = .ok (.integer 1)) (e : compareExact (fuel x y) x y = .eq) :
    compareExact (fuel (.map A) (.map B)) (.map A) (.map B) = .eq := by
  apply map_compareExact_eq_of_lookup
  intro q
  by_cases hq : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
  · rw [mapLookup_congr hq, mapLookup_congr hq, tA, tB]
    exact Option.Rel.some e
  · have nA : mapLookup A q = none := by
      cases h : mapLookup A q with
      | none => rfl
      | some x => exact absurd (size_one_keys sA h tA) hq
    have nB : mapLookup B q = none := by
      cases h : mapLookup B q with
      | none => rfl
      | some x => exact absurd (size_one_keys sB h tB) hq
    rw [nA, nB]; exact Option.Rel.none

/-- Maps of a single top tuple field hold exactly the tuples. -/
theorem den_single_top {A : List (Term × Term)} {k : Term}
    (tA : mapLookup A (.atom "tuple") = some (.tuple #[k, .atom "open", .nil]))
    (sA : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1)) (v : PtG Resp Resp Resp FVT) :
    denD (.map A) v ↔ v.1.1 = "tuple" := by
  obtain ⟨⟨name, p⟩, -, -⟩ := v
  rw [denD_map]
  by_cases hn : name = "tuple"
  · subst hn; simp [tA, dn_tuple, denO_top]
  · simp [single_other sA tA hn, dn_none, hn]

/-- Leaves of pure tuple fields: the top leaf or the expansion literal. -/
theorem pure3 {nd k tag e : Term} (h : OField (PureLit nd) (.tuple ⟨[k, tag, e]⟩)) :
    (tag = .atom "open" ∧ e = .nil) ∨
      ∃ e₀, IsT nd e₀ ∧ k = .integer (keyOf nd) ∧ tag = .atom "closed" ∧ e = Term.list [.atom "term", e₀] := by
  rcases pure_cases h with ⟨k', ex⟩ | ex | ex | ⟨e₀, h₀, ex⟩ | ⟨j, e₀, c, u, d, h₀, ex⟩
  · simp at ex; exact Or.inl ⟨ex.2.1, ex.2.2⟩
  · cases ex
  · cases ex
  · simp [litN] at ex; exact Or.inr ⟨e₀, h₀, ex.1, ex.2.1, ex.2.2⟩
  · simp at ex

/-- Fusing types of the bottom level. -/
theorem fuse0 (nd : Term) : FuseOk 8 FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") Resp Resp Resp FVT := by
  intro a b n m ha hb ne hm
  rcases ha with rfl | ⟨A, rfl, sA⟩
  · exact ⟨_, fuse_term_l _ _ _, Or.inl rfl⟩
  rcases hb with rfl | ⟨B, rfl, sB⟩
  · exact ⟨_, fuse_term_r _ _ _, Or.inl rfl⟩
  obtain ⟨u, hu, urun, usem, -⟩ := de_union (step0 nd) (Or.inr ⟨A, rfl, sA⟩) (Or.inr ⟨B, rfl, sB⟩)
  have run := urun m hm
  obtain ⟨c₁, r₁⟩ := aob_bool (.map A)
  obtain ⟨c₂, r₂⟩ := aob_bool (.map B)
  have second : ∃ r, (do
      let _19 ← Lynx.Except.andAlso (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A))
        (Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B)) Bool.true
      Lynx.Except.guard (Except.ok (_19.isMember [Term.atom "false", Term.atom "nil"]))
        (fun _ => pure (Term.atom "nil")) fun _ => Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B)) = .ok r ∧
      (r = .atom "nil" ∨ (DEG FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") r ∧
        ∀ v : PtG Resp Resp Resp FVT, denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
    rw [r₁, r₂]
    cases c₁ <;> cases c₂ <;>
      simp [Lynx.Except.andAlso, boolAtom, isMember, run, hu, usem]
  rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3».eq_def]
  simp only [getMapKeys_single]
  split
  · rename_i k₀ tag e₁ hA
    have hxA : mapLookup A (.atom "tuple") = some (.tuple ⟨[k₀, tag, e₁]⟩) := by
      cases h : mapLookup A (.atom "tuple") <;> simp_all
    split
    · rename_i k₁ tag₂ e₂ hB
      have hxB : mapLookup B (.atom "tuple") = some (.tuple ⟨[k₁, tag₂, e₂]⟩) := by
        cases h : mapLookup B (.atom "tuple") <;> simp_all
      obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
        ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
      have pA := fieldC_tuple (sA.fields _ _ hxA)
      have pB := fieldC_tuple (sB.fields _ _ hxB)
      have fallback : ∀ (x : Except Exception Term),
          (∀ c₁ c₂ : Bool, Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map A) = .ok (boolAtom c₁) →
            Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» (.map B) = .ok (boolAtom c₂) →
            x = .ok (if c₁ && c₂ then u else .atom "nil")) →
          ∃ r, x = .ok r ∧ (r = .atom "nil" ∨ (DEG FunTop (OField (PureLit nd)) (FieldOk "list") (FieldOk "map") r ∧
            ∀ v : PtG Resp Resp Resp FVT, denD r v ↔ denD (.map A) v ∨ denD (.map B) v)) := by
        intro x hx
        refine ⟨_, hx c₁ c₂ r₁ r₂, ?_⟩
        cases c₁ <;> cases c₂ <;> simp [hu, usem]
      by_cases G : compareExact (fuel tag₂ tag) tag₂ tag = .eq ∧ sa = 1 ∧ sb = 1 ∧ 0 < n
      · obtain ⟨et, rfl, rfl, pos⟩ := G
        have sub : Erlang.erlang.«-/2» (.integer n) (.integer 1) = .ok (.integer (n - 1)) := by
          rw [Erlang.erlang.«-/2_integers»]
        have pc : compare n 0 = Ordering.gt := by exact Int.compare_eq_gt.mpr pos
        rcases pure3 pA with ⟨rfl, rfl⟩ | ⟨eA₀, hA₀, rfl, rfl, rfl⟩ <;>
          rcases pure3 pB with ⟨rfl, rfl⟩ | ⟨eB₀, hB₀, rfl, rfl, rfl⟩ <;> simp at et
        · obtain ⟨kf, hk, -⟩ := leaf_new_key "open" (Or.inl rfl) []
          simp only [Term.list] at hk
          refine ⟨_, ?_, Or.inr ⟨Or.inr ⟨[(.atom "tuple", .tuple #[.integer kf, .atom "open", .nil])], rfl,
            ⟨fun q h => ?_, fun name w h => ?_⟩⟩, fun v => ?_⟩⟩
          · simp [hsa, hsb, Erlang.erlang.«=:=/2», Lynx.Except.andAlso,
              Erlang.erlang.«and/2», Erlang.erlang.«==/2», Erlang.erlang.«>/2», pc, isMember]
            rw [Elixir.Module.Types.Descr.«opt_tuple_fuse_elements/4».eq_def]
            simp [Erlang.lists.«reverse/1», hk]
          · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
            by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
            · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
            · simp [e] at h
          · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq, equalExact_eq_decide] at h
            by_cases e : name = "tuple"
            · subst e; simp at h; subst h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨kf, rfl⟩⟩))))
            · simp [e] at h
          · have one : mapLookup [(.atom "tuple", .tuple #[.integer kf, .atom "open", .nil])] (.atom "tuple") =
                some (.tuple #[.integer kf, .atom "open", .nil]) := by simp [mapLookup]
            rw [den_single_top one (by simp [Erlang.erlang.«map_size/1»]; rfl), den_single_top hxA hsa,
              den_single_top hxB hsb, or_self]
        · exfalso
          apply ne
          refine single_exact hxA hxB hsa hsb ?_
          have := pureLit_exact ⟨eB₀, hB₀, rfl⟩ ⟨eA₀, hA₀, rfl⟩
          simpa [litN, Term.list] using this
      · refine fallback _ fun c₁ c₂ r₁ r₂ => ?_
        have pc : compare n 0 = Ordering.gt ↔ 0 < n := Int.compare_eq_gt
        by_cases e₁ : compareExact (fuel tag₂ tag) tag₂ tag = .eq <;> by_cases e₂ : sa = 1 <;> by_cases e₃ : sb = 1 <;> by_cases e₄ : 0 < n <;>
          simp only [e₁, e₂, e₃, e₄, and_self, not_true_eq_false] at G <;>
          cases c₁ <;> cases c₂ <;>
          simp [hsa, hsb, e₁, e₂, e₃, e₄, pc, r₁, r₂, run, Erlang.erlang.«=:=/2»,
            Lynx.Except.andAlso, Erlang.erlang.«and/2», Erlang.erlang.«==/2»,
            Erlang.erlang.«>/2», isMember, boolAtom]
    · exact second
  · exact second

end Elixir.STTDescrProofsTest.Nest
