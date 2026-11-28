module

public import Erlang.program
public import RecursiveNode
public import BasicSubtypeSound
public import FlatDifferences

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem vT_closed_nil (ef : EF nd E V den tl K) (v : List V) (k : Int) :
    valT E den v (.tuple #[.integer k, .atom "closed", .nil]) = decide (v = []) := by
  have := vT_lit ef (v := v) (k := k) (t := "closed") (l := []) (Or.inr rfl) (by simp)
  simp only [Term.list] at this
  cases h : valT E den v (.tuple #[.integer k, .atom "closed", .nil]) <;> cases v <;> simp_all [InT]

theorem vT_open_term (ef : EF nd E V den tl K) (v : List V) (k : Int) :
    valT E den v (.tuple #[.integer k, .atom "open", Term.list [.atom "term"]]) = !decide (v = []) := by
  have := vT_lit ef (v := v) (k := k) (t := "open") (l := [.atom "term"]) (Or.inl rfl)
    (by simpa using ef.term)
  cases h : valT E den v (.tuple #[.integer k, .atom "open", Term.list [.atom "term"]]) <;> cases v <;>
    simp_all [InT, ef.den_term, InT.open_nil]

/-! Optimized differences of tuple types on tuples of values. -/

/-- Element types that include, position by position, those of another list, as far as both go. -/
def ZipSub (den : Term → V → Prop) : List Term → List Term → Prop
  | a :: as, b :: bs => (∀ x, den a x → den b x) ∧ ZipSub den as bs
  | _, _ => True

/-- Element types that share no value at some position of both lists. -/
def ZipDisj (den : Term → V → Prop) : List Term → List Term → Prop
  | a :: as, b :: bs => (∀ x, den a x → den b x → False) ∨ ZipDisj den as bs
  | _, _ => False

theorem zipDisj_sem {c₁ c₂ : Bool} : ∀ {l₁ l₂ : List Term} {v : List V}, ZipDisj den l₁ l₂ →
    InT den c₁ l₁ v → InT den c₂ l₂ v → False
  | a :: as, b :: bs, x :: xs, h, h₁, h₂ => by
    rcases h with h | h
    · exact h x h₁.1 h₂.1
    · exact zipDisj_sem h h₁.2 h₂.2
  | [], _, _, h, _, _ => by cases h
  | _ :: _, [], _, h, _, _ => by cases h
  | _ :: _, _ :: _, [], _, h₁, _ => h₁.elim

theorem zipSub_sem : ∀ {l₁ l₂ : List Term} {v : List V}, ZipSub den l₁ l₂ → l₂.length ≤ l₁.length →
    InT den Bool.false l₁ v → InT den Bool.false l₂ v
  | _, [], _, _, _, _ => InT.open_nil _
  | a :: as, b :: bs, x :: xs, h, le, h₁ => ⟨h.1 x h₁.1, zipSub_sem h.2 (by simp at le; omega) h₁.2⟩
  | [], _ :: _, _, _, le, _ => by simp at le
  | _ :: _, _ :: _, [], _, _, h₁ => h₁.elim

/-- The walk of `opt_tuple_leaf_difference/3` over elements. -/
theorem tld_walk (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) : ∀ (l₁ : List Term), (∀ e ∈ l₁, E e) → ∀ (l₂ : List Term),
    (∀ e ∈ l₂, E e) → ∀ s : Bool, ∃ res,
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D m) (Term.list l₁) (Term.list l₂) (boolAtom s) =
        .ok res ∧ ((res = .atom "disjoint" ∧ ZipDisj den l₁ l₂) ∨
          (res = .atom "subtype" ∧ s = Bool.true ∧ ZipSub den l₁ l₂) ∨
        res = .atom "none") := by
  have last : ∀ l₁ l₂ : List Term, (l₁ = [] ∨ l₂ = []) → ∀ s : Bool, ∃ res,
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D m) (Term.list l₁) (Term.list l₂) (boolAtom s) =
        .ok res ∧ ((res = .atom "disjoint" ∧ ZipDisj den l₁ l₂) ∨
          (res = .atom "subtype" ∧ s = Bool.true ∧ ZipSub den l₁ l₂) ∨
        res = .atom "none") := by
    intro l₁ l₂ e s
    have zs : ZipSub den l₁ l₂ := by cases l₁ <;> cases l₂ <;> simp_all [ZipSub]
    cases s
    · refine ⟨.atom "none", ?_, Or.inr (Or.inr rfl)⟩
      rcases e with rfl | rfl
      · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
        simp [boolAtom, isMember]
      · cases l₁ <;> rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def] <;>
          simp [boolAtom, isMember]
    · refine ⟨.atom "subtype", ?_, Or.inr (Or.inl ⟨rfl, rfl, zs⟩)⟩
      rcases e with rfl | rfl
      · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
        simp [boolAtom, isMember]
      · cases l₁ <;> rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def] <;>
          simp [boolAtom, isMember]
  intro l₁
  induction l₁ with
  | nil => intro _ l₂ _ s; exact last [] l₂ (Or.inl rfl) s
  | cons a as ih =>
    intro h₁ l₂ h₂ s
    cases l₂ with
    | nil => exact last _ [] (Or.inr rfl) s
    | cons b bs =>
      have ha := h₁ a List.mem_cons_self
      have hb := h₂ b List.mem_cons_self
      obtain ⟨bd, hd, sd⟩ := ef.disj ha hb
      obtain ⟨bs', hs, ss⟩ := ef.sub ha hb
      have rd := hd m hm
      have rs := hs m hm
      cases bd
      · cases s
        · refine ⟨.atom "none", ?_, Or.inr (Or.inr rfl)⟩
          rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
          simp [boolAtom, Lynx.Except.andAlso, rd, Erlang.erlang.«/=/2»]
        · cases bs'
          · refine ⟨.atom "none", ?_, Or.inr (Or.inr rfl)⟩
            rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
            simp [boolAtom, Lynx.Except.andAlso, rd, rs, Erlang.erlang.«/=/2»]
          · obtain ⟨res, run, sem⟩ := ih (fun e m' => h₁ e (List.mem_cons_of_mem _ m')) bs
              (fun e m' => h₂ e (List.mem_cons_of_mem _ m')) Bool.true
            refine ⟨res, ?_, ?_⟩
            · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
              simp [boolAtom] at run
              simp [boolAtom, Lynx.Except.andAlso, rd, rs, Erlang.erlang.«/=/2», run]
            · rcases sem with ⟨e, d⟩ | ⟨e, -, sb⟩ | e
              · exact Or.inl ⟨e, Or.inr d⟩
              · exact Or.inr (Or.inl ⟨e, rfl, ss rfl, sb⟩)
              · exact Or.inr (Or.inr e)
      · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, Or.inl (sd rfl)⟩⟩
        rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
        simp [boolAtom, Lynx.Except.andAlso, rd, Erlang.erlang.«/=/2»]

theorem strategy_lsr (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed") (g₂ : t₂ = "open" ∨ t₂ = "closed")
    (n₁ n₂ : Nat) (h : Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» (.atom t₁) (.integer n₁) (.atom t₂)
      (.integer n₂) = .ok (.atom "left_subtype_of_right")) :
    (t₂ = "closed" → t₁ = "closed" ∧ n₁ = n₂) ∧ n₂ ≤ n₁ := by
  unfold Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» at h
  rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;> rcases Nat.lt_trichotomy n₁ n₂ with c | c | c <;>
    simp [Erlang.erlang.«/=/2», Erlang.erlang.«==/2», c, Int.compare_eq_lt,
      Int.compare_eq_gt, Erlang.erlang.«>=/2», Erlang.erlang.«</2», Erlang.erlang.«>/2», Int.isGE_compare] at h ⊢ <;>
    first
      | omega
      | (have h3 : (n₁ : Int) ≠ n₂ := by omega
         simp [h3] at h)
      | (have h1 : ¬n₂ < n₁ := by omega
         simp [h1] at h)

/-- Tuple values. -/
def ValT (E : Term → Prop) (den : Term → V → Prop) (ρ : Term → Bool) : Prop := ∃ v, ρ = valT E den v

theorem valT_respT : ∀ ρ, ValT E den ρ → Resp ρ := fun _ ⟨v, e⟩ => e ▸ valT_resp v

/-- `opt_tuple_leaf_difference/3` compares tuple literals soundly. -/
theorem tuple_cmp (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a₁ a₂ type : Term) (h₁ : TLit E a₁) (h₂ : TLit E a₂) :
    ∃ res, (D (n + 1)).pure (.function false "Elixir.Module.Types.Descr" "opt_tuple_leaf_difference" 3 #[])
      #[a₁, a₂, type] = .ok res ∧ CmpOk (ValT E den) (TLit E) a₁ a₂ type res := by
  obtain ⟨⟨⟨k₁, t₁, l₁, rfl, g₁, e₁⟩, -⟩, -⟩ := h₁
  obtain ⟨⟨⟨k₂, t₂, l₂, rfl, g₂, e₂⟩, -⟩, -⟩ := h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:opt_tuple_leaf_difference/3».pure]
  obtain ⟨sv, hv, disj⟩ := strategy_spec t₁ t₂ g₁ g₂ l₁.length l₂.length
  by_cases d : Disj t₁ t₂ l₁.length l₂.length
  · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨v, e⟩ => ?_⟩⟩
    · rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
      simp [length_list, hv, disj.mpr d]
    · subst e
      apply Bool.eq_false_iff.mpr
      intro h
      rw [Bool.and_eq_true, vT_lit ef g₁ e₁, vT_lit ef g₂ e₂] at h
      obtain ⟨hw, hlw⟩ := h
      rw [InT.iff_open] at hw hlw
      rcases d with ⟨rfl, rfl, ne⟩ | ⟨rfl, rfl, lt⟩ | ⟨rfl, rfl, lt⟩
      · exact ne (by rw [← hw.2 rfl, hlw.2 rfl])
      · have := hlw.1.length_le; have := hw.2 rfl; omega
      · have := hw.1.length_le; have := hlw.2 rfl; omega
  have nv : sv ≠ .atom "disjoint" := fun e => d (disj.mp e)
  have step : ∀ s : Bool, (s = Bool.true ↔ sv = .atom "left_subtype_of_right") →
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D n) (.tuple #[.integer k₁, .atom t₁, Term.list l₁])
        (.tuple #[.integer k₂, .atom t₂, Term.list l₂]) type =
      Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3» (D n) (Term.list l₁) (Term.list l₂) (boolAtom s) := by
    intro s hs
    rw [Elixir.Module.Types.Descr.«opt_tuple_leaf_difference/3».eq_def]
    simp only [length_list, Lynx.Except.ok_bind, hv]
    cases s
    · have : sv ≠ .atom "left_subtype_of_right" := fun e => by simpa using hs.mpr e
      have eq : Erlang.erlang.«==/2» sv (.atom "left_subtype_of_right") = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2», this]
      rw [eq]; rfl
    · have := hs.mp rfl
      subst this
      have eq : Erlang.erlang.«==/2» (.atom "left_subtype_of_right") (.atom "left_subtype_of_right") =
          .ok (.atom "true") := by simp [Erlang.erlang.«==/2»]
      rw [eq]; rfl
  classical
  obtain ⟨res, run, sem⟩ := tld_walk ef hn l₁ e₁ l₂ e₂ (decide (sv = .atom "left_subtype_of_right"))
  refine ⟨res, by rw [step _ decide_eq_true_iff, run], ?_⟩
  rcases sem with ⟨rfl, zd⟩ | ⟨rfl, ls, zs⟩ | rfl
  · refine Or.inl ⟨rfl, fun ρ ⟨v, e⟩ => ?_⟩
    subst e
    apply Bool.eq_false_iff.mpr
    intro h
    rw [Bool.and_eq_true, vT_lit ef g₁ e₁, vT_lit ef g₂ e₂] at h
    exact zipDisj_sem zd h.1 h.2
  · simp only [decide_eq_true_eq] at ls
    subst ls
    obtain ⟨cl, le⟩ := strategy_lsr t₁ t₂ g₁ g₂ _ _ hv
    refine Or.inr (Or.inl ⟨rfl, fun ρ ⟨v, e⟩ h => ?_⟩)
    subst e
    rw [vT_lit ef g₁ e₁] at h
    rw [vT_lit ef g₂ e₂, InT.iff_open]
    rw [InT.iff_open] at h
    refine ⟨zipSub_sem zs le h.1, fun c => ?_⟩
    obtain ⟨c₁, len⟩ := cl (by simpa using c)
    rw [h.2 (by simp [c₁]), len]
  · exact Or.inr (Or.inr (Or.inr rfl))

/-! Differences of tuple types on tuples of values. -/

theorem denTF_bot (v : List V) : denTF E den (.atom "bdd_bot") v = Bool.false := by
  rw [denTF_bdd (Bdd.bot (ok := TLit E))]; rfl

/-- Open leaves other than the top tuple hold no empty tuple. -/
theorem open_leaf_ne (ef : EF nd E V den tl K) {kx e : Term} (wx : Bdd (TLit E) (.tuple #[kx, .atom "open", e])) (v : List V)
    (h : denTF E den (.tuple #[kx, .atom "open", e]) v = Bool.true) : v ≠ [] := by
  obtain ⟨kx, rfl⟩ := leaf_int wx
  have okx := Bdd.leaf_iff.mp wx
  obtain ⟨⟨⟨k, t, l, eq, g, hl⟩, nt⟩, -⟩ := okx
  obtain ⟨e₀, e₁, e₂⟩ := tuple3_inj eq
  simp only [Term.atom.injEq, Term.integer.injEq] at e₀ e₁
  subst e₀ e₁ e₂
  rw [denTF_bdd wx, eval_leaf, vT_lit ef g hl] at h
  have ne : l ≠ [] := fun h => nt ⟨_, by rw [h]⟩
  intro hv
  subst hv
  cases l with
  | nil => exact ne rfl
  | cons _ _ => exact h.elim

/-- Plain differences of tuple types hold the tuples of the first and not the second. -/
theorem tuple_diff_val (ef : EF nd E V den tl K) {x y : Term} (fx : TField E x) (fy : TField E y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧ TField E w ∧
      ∀ v, denTF E den w v = (denTF E den x v && !denTF E den y v) := by
  rcases fy with ⟨k, rfl⟩ | wy
  · exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl, Or.inr Bdd.bot,
      fun v => by rw [denTF_bot, denTF_top]; simp⟩
  have ny := not_top_of_ok wy tlit_not
  by_cases special : ∃ k, y = .tuple #[k, .atom "closed", .nil]
  · obtain ⟨k, rfl⟩ := special
    rcases fx with ⟨kt, rfl⟩ | wx
    · obtain ⟨h, run, key⟩ := leaf_new_key "open" (Or.inl rfl) [.atom "term"]
      have lit : LeafT E (.tuple #[.integer h, .atom "open", Term.list [.atom "term"]]) :=
        ⟨h, "open", [.atom "term"], rfl, Or.inl rfl, fun e me => by rw [List.mem_singleton.mp me]; exact ef.term, key⟩
      obtain ⟨k, rfl⟩ := leaf_int wy
      refine ⟨_, by simp [Elixir.Module.Types.Descr.«tuple_difference/2», Erlang.erlang.«==/2», run], lit.field,
        fun v => ?_⟩
      rw [lit.val, denTF_top, denTF_bdd wy, eval_leaf, vT_open_term ef, vT_closed_nil ef]
      simp
    · by_cases openLeaf : ∃ kx e, x = .tuple #[kx, .atom "open", e]
      · obtain ⟨kx, e, rfl⟩ := openLeaf
        have ne : e ≠ .nil := fun h => not_top_of_ok wx tlit_not _ (by rw [h])
        refine ⟨_, ?_, Or.inr wx, fun v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          cases e <;> simp_all [Erlang.erlang.«==/2»]
        · obtain ⟨k, rfl⟩ := leaf_int wy
          cases hx : denTF E den (.tuple #[kx, .atom "open", e]) v
          · rfl
          · have := open_leaf_ne ef wx v hx
            rw [denTF_bdd wy, eval_leaf, vT_closed_nil ef]
            simp [this]
      · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
        have ww := keep _ wx wy
        refine ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨h, _⟩ => openLeaf h), run],
          Or.inr ww, fun v => ?_⟩
        rw [denTF_bdd ww, denTF_bdd wx, denTF_bdd wy, sem _ (valT_resp v)]
  · rcases fx with ⟨kt, rfl⟩ | wx
    · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · refine ⟨.atom "bdd_bot", ?_, Or.inr Bdd.bot, fun v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [diff_leaf_top]
        · rw [denTF_bot, denTF_bdd wy]; rfl
      · refine ⟨_, ?_, Or.inl ⟨kt, rfl⟩, fun v => ?_⟩
        · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          simp [diff_leaf_bot]
        · rw [denTF_bdd wy]; simp
      all_goals
        obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        have ww := keep _ wy
        refine ⟨w, by rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run], Or.inr ww, fun v => ?_⟩
        rw [denTF_bdd ww, denTF_bdd wy, denTF_top, sem _ (valT_resp v)]
        simp
    · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
      have ww := keep _ wx wy
      refine ⟨w, by rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨_, h⟩ => special h), run],
        Or.inr ww, fun v => ?_⟩
      rw [denTF_bdd ww, denTF_bdd wx, denTF_bdd wy, sem _ (valT_resp v)]

/-- `opt_tuple_difference/2` is `tuple_difference/2`, but on the leaves it compares, and exactly equal leaves leave
nothing. -/
theorem opt_tuple_split (d : Dispatcher) (x y : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_difference/2» d x y = Elixir.Module.Types.Descr.«tuple_difference/2» x y ∨
    (Elixir.Module.Types.Descr.«opt_tuple_difference/2» d x y = Elixir.Module.Types.Descr.«bdd_difference/3» d x y
        (.function false "Elixir.Module.Types.Descr" "opt_tuple_leaf_difference" 3 #[]) ∧
      Elixir.Module.Types.Descr.«tuple_difference/2» x y = Elixir.Module.Types.Descr.«bdd_difference/2» x y ∧
      (∀ k, y ≠ .tuple #[k, .atom "open", .nil]) ∧
      ((∀ k, x ≠ .tuple #[k, .atom "open", .nil]) ∨ ∀ arr, y ≠ .tuple arr)) ∨
    (∃ k a b, x = .tuple #[k, a, b] ∧ compareExact (fuel y x) y x = .eq ∧
      Elixir.Module.Types.Descr.«opt_tuple_difference/2» d x y = .ok (.atom "bdd_bot")) := by
  by_cases same : (∃ k a b, x = .tuple #[k, a, b] ∧ compareExact (fuel y x) y x = .eq) ∧ ∀ k, y ≠ .tuple #[k, .atom "open", .nil]
  · obtain ⟨⟨k, a, b, rfl, e⟩, ny⟩ := same
    right; right
    refine ⟨k, a, b, rfl, e, ?_⟩
    unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2»
    split
    all_goals first
      | rfl
      | exact (ny _ rfl).elim
      | (simp only [leaf_guard]; rw [ite_eq_left (by simpa using e)]; rfl)
  unfold Elixir.Module.Types.Descr.«opt_tuple_difference/2»
  split
  · left; unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl
  rename_i h₁
  simp only [leaf_guard]
  have xopen : ∀ (h₃ : ∀ k arr, x = .tuple #[k, .atom "open", .nil] → y = .tuple arr → False),
      (∀ k, x ≠ .tuple #[k, .atom "open", .nil]) ∨ ∀ arr, y ≠ .tuple arr := by
    intro h₃
    by_cases hx : ∃ k, x = .tuple #[k, .atom "open", .nil]
    · obtain ⟨k, e⟩ := hx
      exact Or.inr fun arr e' => h₃ _ _ e e'
    · exact Or.inl fun k e => hx ⟨k, e⟩
  split
  · rw [ite_eq_right (fun e => same ⟨⟨_, _, _, rfl, e⟩, fun k e' => h₁ k e'⟩)]
    split
    · left; rename_i heq; rw [heq]; unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      first | rfl | (split <;> simp_all)
    · left; rename_i heq; rw [heq]; unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      first | rfl | (split <;> simp_all)
    · rename_i h₂ h₃
      refine Or.inr (Or.inl ⟨rfl, ?_, fun k e => h₁ _ e, xopen fun k arr e e' => h₃ _ _ e e'⟩)
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split <;> simp_all
  · split
    · left; unfold Elixir.Module.Types.Descr.«tuple_difference/2»; first | rfl | (split <;> simp_all)
    · left; unfold Elixir.Module.Types.Descr.«tuple_difference/2»; first | rfl | (split <;> simp_all)
    · rename_i h₂ h₃
      refine Or.inr (Or.inl ⟨rfl, ?_, fun k e => h₁ _ e, xopen fun k arr e e' => h₃ _ _ e e'⟩)
      unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      split <;> simp_all

/-- Optimized differences of tuple types hold the tuples of the first and not the second. -/
theorem opt_tuple_diff_val (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {x y : Term} (fx : TField E x) (fy : TField E y) :
    ∃ w, Elixir.Module.Types.Descr.«opt_tuple_difference/2» (D (n + 1)) x y = .ok w ∧ TField E w ∧
      ∀ v, denTF E den w v = (denTF E den x v && !denTF E den y v) := by
  obtain ⟨w, run, fw, sem⟩ := tuple_diff_val ef fx fy
  rcases opt_tuple_split (D (n + 1)) x y with e | ⟨e, eb, ny, nx⟩ | ⟨k, a, b, rfl, same, e⟩
  · exact ⟨w, by rw [e, run], fw, sem⟩
  rotate_left
  · exact ⟨_, e, Or.inr Bdd.bot, fun v => by rw [denTF_exact fx fy same, Bool.and_not_self, denTF_bot]⟩
  rw [e]
  have wy : Bdd (TLit E) y := by
    rcases fy with ⟨k, rfl⟩ | wy
    · exact absurd rfl (ny _)
    · exact wy
  rcases fx with ⟨k, rfl⟩ | wx
  · rcases nx with nx | nx
    · exact absurd rfl (nx _)
    have wx : Bdd (TupleLit E) (.tuple #[.integer k, .atom "open", .nil]) :=
      Bdd.leaf_iff.mpr ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
    rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact ⟨w, by rw [d3_atom_right _ wx, ← eb, run], fw, sem⟩
    · exact absurd rfl (nx _)
    · exact absurd rfl (nx _)
  obtain ⟨r, hr, okr, semr⟩ := diff3_ok valT_respT (fun a₁ a₂ type _ h₁ h₂ => tuple_cmp ef hn a₁ a₂ type h₁ h₂)
    _ y wy (fun _ h => h) x wx
  refine ⟨r, hr, Or.inr okr, fun v => ?_⟩
  rw [denTF_bdd okr, denTF_bdd wx, denTF_bdd wy, semr _ ⟨v, rfl⟩]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple emptiness is sound: a tuple of values in a line makes its emptiness check answer `false`. -/

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

theorem full_of_val (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S)
    {e : Term} (he : E e) {y : V} (hy : den e y) : Full E K S e := by
  obtain ⟨b, run⟩ := ops.empty he S
  refine ⟨he, fun m hm => ?_⟩
  cases b
  · simpa [boolAtom] using run m hm
  · exact absurd hy ((sem.empty he hS hm (run m hm)).mp rfl y)

theorem full_of_inT (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S)
    {c : Bool} : ∀ {l : List Term} {v : List V}, (∀ e ∈ l, E e) → InT den c l v → ∀ e ∈ l, Full E K S e
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => h.elim
  | x :: l, y :: v, hl, h => by
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact full_of_val ops sem hS (hl _ List.mem_cons_self) h.1
    · exact full_of_inT ops sem hS (fun e m => hl e (List.mem_cons_of_mem _ m)) h.2 e me

theorem inT_fill_closed : ∀ {l : List Term} {v : List V}, InT den Bool.false l v →
    (∀ y, den (Term.atom "term") y) → InT den Bool.true (l ++ List.replicate (v.length - l.length) (Term.atom "term")) v
  | [], [], _, _ => trivial
  | [], y :: v, _, t => by
    have := inT_fill_closed (l := []) (v := v) (InT.open_nil v) t
    simp only [List.nil_append, List.length_cons, List.length_nil, Nat.sub_zero] at this ⊢
    rw [List.replicate_succ]
    exact ⟨t y, this⟩
  | _ :: _, [], h, _ => h.elim
  | e :: l, y :: v, h, t => by
    have len : (y :: v).length - (e :: l).length = v.length - l.length := by simp
    rw [len, List.cons_append]
    exact ⟨h.1, inT_fill_closed h.2 t⟩

theorem inT_fill_open : ∀ {l : List Term} {v : List V} (j : Nat), InT den Bool.false l v → l.length + j ≤ v.length →
    (∀ y, den (Term.atom "term") y) → InT den Bool.false (l ++ List.replicate j (Term.atom "term")) v
  | [], v, j, _, le, t => by
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at le ⊢
    induction j generalizing v with
    | zero => exact InT.open_nil v
    | succ j ih =>
      cases v with
      | nil => simp at le
      | cons y v => exact ⟨t y, ih v (InT.open_nil v) (by simp at le; omega)⟩
  | _ :: _, [], _, h, _, _ => h.elim
  | e :: l, y :: v, j, h, le, t => ⟨h.1, inT_fill_open j h.2 (by simp at le ⊢; omega) t⟩

/-- `tuple_empty_sizes?/5` answers false when a closed line of a size it checks answers false. -/
theorem sizes_false (d : Dispatcher) (l : List Term) (m' : Nat) (rest S : Term)
    (lines : ∀ i, l.length ≤ i → i < m' → ∃ b : Bool, Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed")
      (Term.list (l ++ List.replicate (i - l.length) (Term.atom "term"))) rest S = .ok (boolAtom b))
    (j : Nat) (lj : l.length ≤ j) (jm : j < m')
    (hj : Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "closed")
      (Term.list (l ++ List.replicate (j - l.length) (Term.atom "term"))) rest S = .ok (Term.atom "false")) :
    ∀ i, l.length ≤ i → i ≤ j → Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer i) (.integer m')
      (Term.list l) rest S = .ok (.atom "false") := by
  intro i le ij
  induction h : j - i generalizing i with
  | zero =>
    have : i = j := by omega
    subst this
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    have lt : (i : Int) < m' := by omega
    simp [lt, fill_list l i le, hj, Lynx.Except.andAlso]
  | succ k ih =>
    rw [Elixir.Module.Types.Descr.«tuple_empty_sizes?/5».eq_def]
    have lt : (i : Int) < m' := by omega
    have next := ih (i + 1) (by omega) (by omega) (by omega)
    simp only [Int.natCast_add, Int.natCast_one] at next
    obtain ⟨b, hb⟩ := lines i le (by omega)
    simp only [Lynx.Except.guard, Erlang.erlang.«</2»]
    simp [Int.compare_eq_lt, lt, fill_list l i le, hb, next]
    cases b <;> rfl

theorem empty_false_of_val (ops : ElemOk E K) (sem : ElemSem E K V den Safe) {S : List (Term × Term)} (hS : Safe S)
    {m : Nat} (hm : K ≤ m) {e : Term} (he : E e) {y : V} (hy : den e y) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) e (.map S) = .ok (.atom "false") :=
  (full_of_val ops sem hS he hy).2 m hm

/-- `tuple_elements_empty?/7` answers false when a tuple of the line, outside the remaining negations, escapes the
negated literal at one of the positions it checks, given the meets `tuple_elements_meets/4` computed alongside. -/
theorem elements_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) (c : Bool) (negs : List Term)
    (line : ∀ l : List Term, (∀ e ∈ l, E e) → ∀ v, InT den c l v → (∀ N ∈ negs, ¬LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "false"))
    (lineBool : ∀ l : List Term, (∀ e ∈ l, Full E K S e) → ∃ b : Bool,
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (boolAtom b)) :
    ∀ (nrest acc rest accM ms : List Term), (∀ e ∈ nrest, E e) → (∀ e ∈ acc, E e) → (∀ e ∈ rest, E e) →
      (c = Bool.true → nrest.length ≤ rest.length) → ∀ (v₁ w : List V), InT den Bool.true acc.reverse v₁ →
      InT den c rest w → (∀ N ∈ negs, ¬LitSem den N (v₁ ++ w)) → ¬InT den Bool.false nrest w →
      nrest.length ≤ w.length →
      Elixir.Module.Types.Descr.«tuple_elements_meets/4» (D m) (Term.list rest) (Term.list nrest) (Term.list accM)
        (.map S) = .ok (Term.list (accM.reverse ++ ms)) →
      Elixir.Module.Types.Descr.«tuple_elements_empty?/7» (D m) (Term.list acc) (.atom (if c then "closed" else "open"))
        (Term.list rest) (Term.list nrest) (Term.list ms) (Term.list negs) (.map S) = .ok (.atom "false") := by
  intro nrest
  induction nrest with
  | nil => intro _ _ _ _ _ _ _ _ v₁ w _ _ _ nI _ _; exact absurd (InT.open_nil w) nI
  | cons nt nl ih =>
    intro acc rest accM ms hn hacc hrest hlen v₁ w h₁ hw hneg nI wlen hmeets
    have hnt := hn nt List.mem_cons_self
    have hnl : ∀ e ∈ nl, E e := fun e m => hn e (List.mem_cons_of_mem _ m)
    obtain ⟨y, w', rfl⟩ : ∃ y w', w = y :: w' := by
      cases w with
      | nil => simp at wlen
      | cons y w' => exact ⟨y, w', rfl⟩
    obtain ⟨ty, es, hshape, hty, hes, hy, hw'⟩ : ∃ ty es, ((rest = [] ∧ ty = .atom "term" ∧ es = []) ∨ rest = ty :: es) ∧
        E ty ∧ (∀ e ∈ es, E e) ∧ den ty y ∧ InT den c es w' := by
      cases rest with
      | nil =>
        have hc : c = Bool.false := by
          cases c
          · rfl
          · have := hlen rfl; simp at this
        subst hc
        exact ⟨_, _, Or.inl ⟨rfl, rfl, rfl⟩, ops.term, by simp, sem.term y, InT.open_nil w'⟩
      | cons x xs =>
        exact ⟨x, xs, Or.inr rfl, hrest x List.mem_cons_self, fun e m => hrest e (List.mem_cons_of_mem _ m), hw.1, hw.2⟩
    have hlen' : c = Bool.true → nl.length ≤ es.length := fun hc => by
      have := hlen hc
      rcases hshape with ⟨rfl, -, rfl⟩ | rfl <;> simp at this ⊢ <;> omega
    have accFull : ∀ e ∈ acc.reverse, Full E K S e :=
      full_of_inT ops sem hS (fun e me => hacc e (List.mem_reverse.mp me)) h₁
    have esFull : ∀ e ∈ es, Full E K S e := full_of_inT ops sem hS hes hw'
    have elemsLine : ∀ x, E x → ∀ e ∈ acc.reverse ++ x :: es, E e := by
      intro x hx e me
      simp only [List.mem_append, List.mem_reverse, List.mem_cons] at me
      rcases me with me | rfl | me
      · exact hacc e me
      · exact hx
      · exact hes e me
    rw [list_cons] at hmeets
    obtain ⟨meet, ms', rfl, hmeet, fullMeet, hmeets'⟩ :=
      meets_head ops S hm hshape (full_of_val ops sem hS hty hy) esFull hnt hnl hmeets
    have dmeet := sem.inter hty hnt hm (hmeet m hm)
    obtain ⟨diff, ldiff, hdiff⟩ := dops.diff hty hnt
    have ddiff := sem.diff hty hnt hm (hdiff m hm)
    have step := elements_step (D m) acc (.atom (if c then "closed" else "open")) rest nt nl meet (Term.list ms')
      (Term.list negs) (.map S) ty es hshape diff (hdiff m hm)
    obtain ⟨bd, ed⟩ := ops.empty ldiff S
    rw [list_cons nt nl, list_cons meet ms']
    by_cases inN : den nt y
    · -- the tuple escapes later
      have nI' : ¬InT den Bool.false nl w' := fun h => nI ⟨inN, h⟩
      cases bd
      · have r := ih (meet :: acc) es (meet :: accM) ms' hnl (fun e me => by
            rcases List.mem_cons.mp me with rfl | me
            · exact fullMeet.1
            · exact hacc e me) hes hlen' (v₁ ++ [y]) w' (by
            simp only [List.reverse_cons]
            exact (InT.append _).mpr ⟨v₁, [y], rfl, h₁, (dmeet y).mpr ⟨hy, inN⟩, trivial⟩) hw'
          (by simpa using hneg) nI' (by simp at wlen; omega) hmeets'
        obtain ⟨bl, hl⟩ := lineBool (acc.reverse ++ diff :: es) fun e me => by
          simp only [List.mem_append, List.mem_cons] at me
          rcases me with me | rfl | me
          · exact accFull e me
          · exact ⟨ldiff, fun m' h' => by simpa [boolAtom] using ed m' h'⟩
          · exact esFull e me
        rw [step.2 (by simpa [boolAtom] using ed m hm), hl, r]
        cases bl <;> rfl
      · rw [step.1 (by simpa [boolAtom] using ed m hm)]
        exact ih (ty :: acc) es (meet :: accM) ms' hnl (fun e me => by
            rcases List.mem_cons.mp me with rfl | me
            · exact hty
            · exact hacc e me) hes hlen' (v₁ ++ [y]) w' (by
            simp only [List.reverse_cons]
            exact (InT.append _).mpr ⟨v₁, [y], rfl, h₁, hy, trivial⟩) hw'
          (by simpa using hneg) nI' (by simp at wlen; omega) hmeets'
    · -- the tuple escapes here
      have diffFalse := empty_false_of_val ops sem hS hm ldiff ((ddiff y).mpr ⟨hy, inN⟩)
      rw [step.2 diffFalse]
      rw [line (acc.reverse ++ diff :: es) (elemsLine diff ldiff) (v₁ ++ y :: w')
        ((InT.append _).mpr ⟨v₁, y :: w', rfl, h₁, (ddiff y).mpr ⟨hy, inN⟩, hw'⟩) hneg]
      rfl

/-- `tuple_empty_arity?/7` answers false on open lines when a size it checks answers false. -/
theorem arity_false (d : Dispatcher) (n m' : Nat) (l : List Term) (ntag : String) (rest S : Term)
    (ok : (Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer n) (.integer m') (Term.list l) rest S =
        .ok (.atom "false")) ∨
      (∃ b : Bool, Elixir.Module.Types.Descr.«tuple_empty_sizes?/5» d (.integer n) (.integer m') (Term.list l) rest S =
        .ok (boolAtom b)) ∧ ntag = "closed" ∧ l.length ≤ m' + 1 ∧
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» d (.atom "open")
          (Term.list (l ++ List.replicate (m' + 1 - l.length) (Term.atom "term"))) rest S = .ok (Term.atom "false")) :
    Elixir.Module.Types.Descr.«tuple_empty_arity?/7» d (.integer n) (.integer m') (.atom "open") (Term.list l)
      (.atom ntag) rest S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«tuple_empty_arity?/7».eq_def]
  rcases ok with sizes | ⟨⟨b, sizes⟩, rfl, le, line⟩
  · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, sizes, Lynx.Except.andAlso]
  · have fill := fill_list l (m' + 1) le
    simp only [Int.natCast_add, Int.natCast_one] at fill
    cases b <;> simp [Erlang.erlang.«==/2», Lynx.Except.orElse, sizes, Lynx.Except.andAlso, fill, line, boolAtom]

/-- Tuple lines answer false when a tuple of values of the line escapes their negations. -/
theorem line_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat} (hm : K ≤ m)
    (S : List (Term × Term)) (hS : Safe S) :
    ∀ negs : List Term, (∀ t ∈ negs, TupleLit E t) → ∀ (c : Bool) (l : List Term), (∀ e ∈ l, E e) →
      ∀ v, InT den c l v → (∀ N ∈ negs, ¬LitSem den N v) →
      Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c then "closed" else "open")) (Term.list l)
        (Term.list negs) (.map S) = .ok (.atom "false") := by
  intro negs
  induction negs with
  | nil => intro _ c l _ v _ _; exact line_nil (D m) _ _ _
  | cons N rest ih =>
    intro lits c l hl v hv hneg
    obtain ⟨k, ntag, nl, rfl, htag, hnl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, TupleLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    have hneg' : ∀ N ∈ rest, ¬LitSem den N v := fun N m => hneg N (List.mem_cons_of_mem _ m)
    have nN : ¬InT den (ntag == "closed") nl v := fun h => hneg _ List.mem_cons_self ⟨k, ntag, nl, rfl, h⟩
    have full := full_of_inT ops sem hS hl hv
    have bools : ∀ (c' : Bool) (l' : List Term), (∀ e ∈ l', Full E K S e) → ∃ b : Bool,
        Elixir.Module.Types.Descr.«tuple_line_empty?/4» (D m) (.atom (if c' then "closed" else "open")) (Term.list l')
          (Term.list rest) (.map S) = .ok (boolAtom b) := fun c' l' hl' => by
      obtain ⟨b, hb⟩ := line_total ops dops S rest lits' (if c' then "closed" else "open") l' hl'
      exact ⟨b, hb m hm⟩
    rw [list_cons]
    by_cases top : ntag = "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      exact absurd (InT.open_nil v) nN
    by_cases last : c = Bool.false ∧ ntag = "closed" ∧ rest = []
    · obtain ⟨rfl, rfl, rfl⟩ := last
      exact line_last (D m) _ k _ _
    have notLast : ¬((if c then "closed" else "open") = "open" ∧ ntag = "closed" ∧ rest = []) := by
      rintro ⟨hc, h₁, h₂⟩
      cases c
      · exact last ⟨rfl, h₁, h₂⟩
      · simp at hc
    by_cases skip : ((if c then "closed" else "open") = "closed" ∧ l.length < nl.length) ∨
        (ntag = "closed" ∧ nl.length < l.length)
    · rw [line_size (D m) _ l k ntag nl rest (.map S) top notLast skip]
      exact ih lits' c l hl v hv hneg'
    rcases meets_cases ops S nl hnl [] l full with dis | ⟨ms, mlen, hms, run⟩
    · rw [line_disjoint (D m) _ l k ntag nl rest (.map S) top notLast skip (by simpa using dis m hm)]
      exact ih lits' c l hl v hv hneg'
    rw [line_meets (D m) _ l k ntag nl rest (.map S) top notLast skip _ (by simpa using run m hm)
      (by cases ms <;> simp)]
    have lineFalse := fun (c' : Bool) l' hl' v' hv' hn' => ih lits' c' l' hl' v' hv' hn'
    obtain ⟨be, he⟩ := elements_total ops dops S (.atom (if c then "closed" else "open")) (Term.list rest)
      (fun l' hl' => line_total ops dops S rest lits' _ l' hl') nl hnl ms mlen hms [] l (by simp) full
    have heM := he m hm
    -- how the tuple escapes the negated literal
    rw [InT.iff_open] at nN
    by_cases short : v.length < nl.length
    · -- a shorter tuple: only open lines hold it
      have hc : c = Bool.false := by
        cases c
        · rfl
        · have := hv.closed_length
          exact absurd (Or.inl ⟨rfl, by omega⟩) skip
      subst hc
      have lv := hv.length_le
      have ar := arity_false (D m) l.length nl.length l ntag (Term.list rest) (.map S) (Or.inl
        (sizes_false (D m) l nl.length _ _ (fun i _ _ => bools Bool.true _ (fun e me => by
            simp only [List.mem_append, List.mem_replicate] at me
            rcases me with me | ⟨-, rfl⟩
            · exact full e me
            · exact full_term ops S))
          v.length lv short
          (lineFalse Bool.true _ (fun e me => by
            simp only [List.mem_append, List.mem_replicate] at me
            rcases me with me | ⟨-, rfl⟩
            · exact hl e me
            · exact ops.term) v (inT_fill_closed hv sem.term) hneg') l.length (Nat.le_refl _) lv))
      simp only [Bool.false_eq_true, ite_false] at heM ⊢
      rw [heM, ar]
      cases be <;> rfl
    by_cases escape : InT den Bool.false nl v
    · -- a longer tuple than a closed literal
      have hn : ntag = "closed" := by
        rcases htag with ho | hc
        · exact absurd ⟨escape, fun h => by simp [ho] at h⟩ nN
        · exact hc
      subst hn
      have long : nl.length < v.length := by
        rcases Nat.lt_or_ge nl.length v.length with h | h
        · exact h
        · exact absurd ⟨escape, fun _ => by have := escape.length_le; omega⟩ nN
      have hc : c = Bool.false := by
        cases c
        · rfl
        · have := hv.closed_length
          exact absurd (Or.inr ⟨rfl, by omega⟩) skip
      subst hc
      have le : l.length ≤ nl.length := by
        have : ¬nl.length < l.length := fun h => skip (Or.inr ⟨rfl, h⟩)
        omega
      obtain ⟨bs, hbs⟩ := sizes_total (K := K) S l nl.length (Term.list rest) (fun i _ _ => line_total ops dops S rest
        lits' "closed" _ (fun e me => by
          simp only [List.mem_append, List.mem_replicate] at me
          rcases me with me | ⟨-, rfl⟩
          · exact full e me
          · exact full_term ops S)) l.length (Nat.le_refl _)
      have ar := arity_false (D m) l.length nl.length l "closed" (Term.list rest) (.map S) (Or.inr
        ⟨⟨bs, hbs m hm⟩, rfl, by omega, lineFalse Bool.false _ (fun e me => by
          simp only [List.mem_append, List.mem_replicate] at me
          rcases me with me | ⟨-, rfl⟩
          · exact hl e me
          · exact ops.term) v (inT_fill_open _ hv (by have := hv.length_le; omega) sem.term) hneg'⟩)
      simp only [Bool.false_eq_true, ite_false] at heM ⊢
      rw [heM, ar]
      cases be <;> rfl
    · -- a position where the tuple escapes
      have ef := elements_false ops dops sem hm S hS c rest (fun l' hl' v' hv' hn' => ih lits' c l' hl' v' hv' hn')
        (fun l' hl' => bools c l' hl') nl [] l [] ms hnl (by simp) hl (fun hc => by
          subst hc
          have := hv.closed_length
          have : ¬l.length < nl.length := fun h => skip (Or.inl ⟨rfl, h⟩)
          omega) [] v trivial hv (by simpa using hneg') escape (by omega) (by simpa using run m hm)
      have ef' : Elixir.Module.Types.Descr.«tuple_elements_empty?/7» (D m) .nil
          (.atom (if c then "closed" else "open")) (Term.list l) (Term.list nl) (Term.list ms) (Term.list rest)
          (.map S) = .ok (.atom "false") := ef
      rw [ef']
      rfl

theorem elements_check2 (ops : ElemOk E K) (S : List (Term × Term)) (l : List Term) (hl : ∀ e ∈ l, E e) :
    ∃ b, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2» (D m) (Term.list l) (.map S) =
      .ok (boolAtom b)) ∧ (b = Bool.true → ∃ e ∈ l, ∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«empty_seen?/2» (D m) e (.map S) = .ok (.atom "true")) := by
  have each : ∀ e ∈ l, ∃ b, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map S) = .ok (boolAtom b) :=
    fun e me => ops.empty (hl e me) S
  classical
  let res : Term → Bool := fun e => if h : e ∈ l then Classical.choose (each e h) else Bool.false
  have hres : ∀ e ∈ l, ∀ m', K ≤ m' →
      Elixir.Module.Types.Descr.«empty_seen?/2» (D m') e (.map S) = .ok (boolAtom (res e)) := by
    intro e me m' h
    simp only [res, dite_eq_left me]
    exact Classical.choose_spec (each e me) m' h
  refine ⟨l.any res, fun m hm => ?_, fun yes => ?_⟩
  · obtain ⟨n, rfl, hn⟩ := succ_of_le hm
    simp only [Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2»]
    refine any_list _ _ _ _ res l fun x mx => ?_
    rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_line_elements_empty?/2-fun-0-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-tuple_line_elements_empty?/2-fun-0-/2»]
    exact hres x mx n hn
  · obtain ⟨e, me, he⟩ := List.any_eq_true.mp yes
    exact ⟨e, me, fun m' h => by rw [hres e me m' h, he]; rfl⟩

/-- Checked tuple lines answer false when a tuple of values of the line escapes their negations. -/
theorem line_seen_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) (S : List (Term × Term)) (hS : Safe S) {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (el : ∀ e ∈ l, E e) {negs : List Term} (lits : ∀ t ∈ negs, TupleLit E t) (v : List V)
    (hv : InT den (tag == "closed") l v) (hneg : ∀ N ∈ negs, ¬LitSem den N v) :
    Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4» (D m) (.atom tag) (Term.list l) (Term.list negs) (.map S) =
      .ok (.atom "false") := by
  obtain ⟨b, check, some⟩ := elements_check2 ops S l el
  have full := full_of_inT ops sem hS el hv
  have hb : b = Bool.false := by
    cases b
    · rfl
    · obtain ⟨e, me, he⟩ := some rfl
      have := (full e me).2 m (by omega)
      rw [he m (by omega)] at this
      simp at this
  subst hb
  rw [Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4».eq_def]
  simp only [check m hm, Lynx.Except.ok_bind]
  cases negs with
  | nil => simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, Erlang.erlang.«==/2», Term.list]
  | cons N rest =>
    have notNil : Erlang.erlang.«==/2» (Term.list (N :: rest)) .nil = .ok (.atom "false") := by
      simp [Erlang.erlang.«==/2», Term.list, Term.false]
    simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.andAlso, notNil]
    have := line_false ops dops sem (by omega : K ≤ m) S hS (N :: rest) lits (tag == "closed") l el v hv hneg
    rcases g with rfl | rfl <;> simpa using this

/-- Tuple BDD walks answer false when a tuple of values along the path, outside the negations, satisfies the BDD. -/
theorem tuple_bdd_false (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {m : Nat}
    (hm : K + 1 ≤ m) (S : List (Term × Term)) (hS : Safe S) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos → (∀ t ∈ negs, TupleLit E t) → ∀ v, InPos den pos v →
      (∀ N ∈ negs, ¬LitSem den N v) → eval (valT E den v) r = Bool.true →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "false") := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) → ∀ pos negs, TuplePos E pos →
    (∀ t ∈ negs, TupleLit E t) → ∀ v, InPos den pos v → (∀ N ∈ negs, ¬LitSem den N v) →
      eval (valT E den v) r = Bool.true →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos (Term.list negs) r (.map S) = .ok (.atom "false"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro ok _ pos negs hp lits v hv hneg _
    obtain ⟨tag, l, rfl, gt, el⟩ := hp
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    exact line_seen_false ops dops sem hm S hS gt el lits v (inPos_iff.mp hv) hneg
  · intro ok _ pos negs _ _ v _ _ h
    simp at h
  · intro ok k x y okl okLit pos negs hp lits v hv hneg h
    have hl := okLit _ okl
    rw [eval_leaf] at h
    have hlit := (valT_iff sem hl.1).mp h
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    rcases inter_sem ops sem hm hp hl with ⟨_, empty⟩ | ⟨pos', run, hp', sem'⟩
    · exact absurd hlit (empty v hv)
    obtain ⟨tag, l, rfl, gt, el⟩ := hp'
    simp [run]
    exact line_seen_false ops dops sem hm S hS gt el lits v (inPos_iff.mp ((sem' v).mpr ⟨hv, hlit⟩)) hneg
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit pos negs hp lits v hv hneg hev
    have hl := okLit _ okl
    have okLit' : ∀ t, Above ok lit t → TupleOk E t := fun t ht => okLit t ht.1
    have lits' : ∀ t ∈ lit :: negs, TupleLit E t := fun t m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact hl.1
      · exact lits t m
    obtain ⟨bd, hbd⟩ := tuple_bdd_total ops dops S hd (fun t ht => (okLit' t ht).1) pos (lit :: negs) hp lits'
    obtain ⟨bu, hbu⟩ := tuple_bdd_total ops dops S hu (fun t ht => (okLit' t ht).1) pos negs hp lits
    have dPart := hbd m hm
    rw [list_cons] at dPart
    rw [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4».eq_def]
    simp only [eval_node] at hev
    rcases inter_sem ops sem hm hp hl with ⟨empty, notLit⟩ | ⟨pos2, run, hp2, sem2⟩
    · -- the literal meets nothing on the path
      have nl : valT E den v lit = Bool.false := by
        cases e : valT E den v lit
        · rfl
        · exact absurd ((valT_iff sem hl.1).mp e) (notLit v hv)
      simp only [nl, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and] at hev
      rcases Bool.or_eq_true_iff.mp hev with hu' | hd'
      · have r := iu okLit' pos negs hp lits v hv hneg hu'
        cases bd <;> simp [empty, dPart, r, Lynx.Except.andAlso, boolAtom]
      · have r := idd okLit' pos (lit :: negs) hp lits' v hv (fun N m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact fun h => by rw [(valT_iff sem hl.1).mpr h] at nl; cases nl
          · exact hneg N m) hd'
        rw [list_cons] at r
        simp [r, Lynx.Except.andAlso]
    obtain ⟨tag2, l2, rfl, gt2, el2⟩ := id hp2
    obtain ⟨bc, hbc⟩ := tuple_bdd_total ops dops S hc (fun t ht => (okLit' t ht).1) _ negs hp2 lits
    have uPart := hbu m hm
    have cPart := hbc m hm
    by_cases hlv : valT E den v lit = Bool.true
    · simp only [hlv, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false] at hev
      rcases Bool.or_eq_true_iff.mp hev with hc' | hu'
      · have r := ic okLit' _ negs hp2 lits v ((sem2 v).mpr ⟨hv, (valT_iff sem hl.1).mp hlv⟩) hneg hc'
        cases bd <;> cases bu <;> simp [run, dPart, r, Lynx.Except.andAlso, boolAtom]
      · have r := iu okLit' pos negs hp lits v hv hneg hu'
        cases bd <;> cases bc <;> simp [run, dPart, cPart, r, Lynx.Except.andAlso, boolAtom]
    · simp only [Bool.not_eq_true] at hlv
      simp only [hlv, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and] at hev
      rcases Bool.or_eq_true_iff.mp hev with hu' | hd'
      · have r := iu okLit' pos negs hp lits v hv hneg hu'
        cases bd <;> cases bc <;> simp [run, dPart, cPart, r, Lynx.Except.andAlso, boolAtom]
      · have r := idd okLit' pos (lit :: negs) hp lits' v hv (fun N m => by
          rcases List.mem_cons.mp m with rfl | m
          · exact fun h => by rw [(valT_iff sem hl.1).mpr h] at hlv; cases hlv
          · exact hneg N m) hd'
        rw [list_cons] at r
        simp [r, Lynx.Except.andAlso]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple fields of the expansion literal of the node `t`: their heights, meaning, and emptiness. -/

section
variable {t : Term}

theorem lh_isT {e : Term} (h : IsT t e) : lh e = 1 := by
  obtain ⟨S, rfl, -⟩ := h.node
  exact lh_node_term

theorem lh_litN {e : Term} (h : IsT t e) (k : Int) : lh (litN e k) = 1 := by
  obtain ⟨S, rfl, -⟩ := h.node
  simp only [litN, Term.list]
  rw [show (#[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple #[.reference (refOf t), .map S, gen]) .nil)] :
      Array Term) = ⟨[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference (refOf t), .map S, gen]⟩) .nil)]⟩
      from rfl, lh_nodeLit]
  exact lh_node_term

theorem lh_bt (b : Bool) : lh (bt b) = 1 := by cases b <;> simp [bt, lh]

theorem pure_one {x : Term} (fx : OField (PureLit t) x) (nt : ∀ k, x ≠ .tuple #[.integer k, .atom "open", .nil]) :
    lh x = 1 := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact absurd rfl (nt k)
  rcases pure_shape wx with rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · simp [lh]
  · simp [lh]
  · exact lh_litN he _
  · obtain ⟨S, rfl, -⟩ := he.node
    simp only [litN, Term.list]
    rw [show (#[.integer j, .tuple #[.integer (keyOf t), .atom "closed", .cons (.atom "term")
        (.cons (.tuple #[.reference (refOf t), .map S, gen]) .nil)], bt c, bt u, bt d] : Array Term) =
        ⟨[.integer j, .tuple ⟨[.integer (keyOf t), .atom "closed", .cons (.atom "term")
        (.cons (.tuple ⟨[.reference (refOf t), .map S, gen]⟩) .nil)]⟩, bt c, bt u, bt d]⟩ from rfl,
      lh_node_z _ _ _ _ _ _ _ (by simp [litZ]), lh_nodeLit, lh_node_term]
    simp [lh_bt]

theorem pure_le {x : Term} (fx : OField (PureLit t) x) : lh x ≤ 1 := by
  by_cases nt : ∃ k, x = .tuple #[.integer k, .atom "open", .nil]
  · obtain ⟨k, rfl⟩ := nt
    simp [lh]
  · exact Nat.le_of_eq (pure_one fx fun k h => nt ⟨k, h⟩)

theorem pureLit_exact {a b : Term} (ha : PureLit t a) (hb : PureLit t b) : compareExact (fuel b a) b a = .eq := by
  obtain ⟨e, he, rfl⟩ := ha
  obtain ⟨e', he', rfl⟩ := hb
  simp [litN, Term.list, compareExact_tuple, List.compareLex_cons_cons, compareExact_cons, isT_exact he' he,
    List.compareLex_nil_nil]

theorem pure_cases {x : Term} (fx : OField (PureLit t) x) :
    (∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]) ∨ x = .atom "bdd_top" ∨ x = .atom "bdd_bot" ∨
      (∃ e, IsT t e ∧ x = litN e (keyOf t)) ∨
      ∃ (j : Int) (e : Term) (c u d : Bool), IsT t e ∧ x = .tuple #[.integer j, litN e (keyOf t), bt c, bt u, bt d] := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr (pure_shape wx)

/-- Pure tuple fields mean the same under a valuation and under the constant valuation of its literal. -/
theorem pure_val {x : Term} (fx : OField (PureLit t) x) {ρ : Term → Bool} (_hρ : Resp ρ) :
    ∃ b, denO x ρ = denO x (fun _ => b) := by
  rcases pure_cases fx with ⟨k, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · exact ⟨Bool.true, by simp [denO_top]⟩
  · exact ⟨Bool.true, rfl⟩
  · exact ⟨Bool.true, rfl⟩
  · refine ⟨ρ (litN e (keyOf t)), ?_⟩
    simp [denO, isOpenTop, litN, Term.list]
  · refine ⟨ρ (litN e (keyOf t)), ?_⟩
    cases c <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list]

/-- The emptiness of pure tuple fields, when neither the field nor the node was seen. -/
theorem pure_empty_val {x : Term} (fx : OField (PureLit t) x) {S : List (Term × Term)}
    (fresh : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 = .eq)) = Bool.false)
    (noid : idIn (refOf t) S = Bool.false) {m : Nat} (hm : 2 ≤ m) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      .ok (boolAtom (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false))) := by
  have walk : Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) (.tuple #[.atom "open", .nil]) .nil x
        (.map ((.cons (.atom "tuple") x, .atom "true") :: S)) := by
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, Erlang.maps.«put/3»]
  have noid' : idIn (refOf t) ((.cons (.atom "tuple") x, .atom "true") :: S) = Bool.false := by
    simp [idIn] at noid ⊢
    exact noid
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  rw [walk]
  rcases pure_cases fx with ⟨k, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · rw [tuple_walk_top_leaf]; simp [denO_top, boolAtom]
  · rw [tuple_walk_top]; simp [denO, isOpenTop, boolAtom]
  · rw [tuple_walk_bot]; simp [denO, isOpenTop, boolAtom]
  · rw [walk_leaf_node he.node _ m', noid']; simp [denO, isOpenTop, litN, Term.list, boolAtom]
  · rw [walk_node_node he.node _ _ m', noid']
    cases c <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list, boolAtom]

theorem safeN_noid {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) (r : List Nat) : idIn r S = Bool.false := by
  simp only [idIn, List.any_eq_false, decide_eq_true_eq]
  intro e me h
  obtain ⟨kind, b, e₁, -⟩ := hS e me
  rw [e₁] at h
  simp at h

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple emptiness is exact under seen sets of higher BDDs. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem lh_atom {s : String} (h : s ≠ "bdd_top") (h' : s ≠ "bdd_bot") : lh (.atom s) = 0 := by
  unfold lh; split <;> simp_all

theorem lh_list_mem : ∀ {l : List Term} {e : Term}, e ∈ l → lh e ≤ lh (Term.list l)
  | x :: l, e, h => by
    rw [Term.list, lh]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := lh_list_mem h; omega

/-- Expansion literals of recursive nodes, `{_, closed, [term(), node]}`. -/
def ExpLit (t : Term) : Prop :=
  ∃ (k : Int) (r : List Nat) (a : List (Term × Term)) (b : Term),
    t = .tuple #[.integer k, .atom "closed", Term.list [.atom "term", .tuple #[.reference r, .map a, b]]]

/-- Whether the elements of a tuple literal are those of an expansion literal. -/
def ExpEls (tag : String) (l : List Term) : Prop :=
  tag = "closed" ∧ ∃ (r : List Nat) (a : List (Term × Term)) (b : Term), l = [.atom "term", .tuple #[.reference r, .map a, b]]

theorem lh_lit {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (top : ¬(tag = "open" ∧ l = [])) (ne : ¬ExpEls tag l) :
    lh (.tuple #[.integer k, .atom tag, Term.list l]) = lh (Term.list l) + 1 := by
  rw [show (#[.integer k, .atom tag, Term.list l] : Array Term) = ⟨[.integer k, .atom tag, Term.list l]⟩ from rfl,
    lh_leaf _ _ _ (fun ⟨h₁, h₂⟩ => top ⟨by simpa using h₁, list_eq_nil.mp h₂⟩)
      (fun ⟨_, _, h⟩ => by cases l <;> simp [Term.list] at h) ?_ (by simp),
    lh_atom (by rintro rfl; simp at g) (by rintro rfl; simp at g)]
  · omega
  · rintro ⟨h, r, a, b, e⟩
    simp only [Term.atom.injEq] at h
    match l, e with
    | [x, y], e =>
      simp only [Term.list, Term.cons.injEq] at e
      obtain ⟨rfl, rfl, -⟩ := e
      exact ne ⟨h, r, a, b, rfl⟩

theorem lh_lit_exp {k : Int} {tag : String} {l : List Term} (ex : ExpEls tag l) :
    1 ≤ lh (.tuple #[.integer k, .atom tag, Term.list l]) ∧ ∀ e ∈ l, lh e ≤ lh (.tuple #[.integer k, .atom tag, Term.list l]) := by
  obtain ⟨rfl, r, a, b, rfl⟩ := ex
  have e : lh (.tuple #[.integer k, .atom "closed", Term.list [.atom "term", .tuple #[.reference r, .map a, b]]]) =
      lh (.tuple ⟨[.reference r, .map a, b]⟩) := lh_nodeLit
  rw [e, lh_node_term]
  refine ⟨by omega, fun x mx => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at mx
  rcases mx with rfl | rfl
  · simp [lh]
  · rw [show (#[.reference r, .map a, b] : Array Term) = ⟨[.reference r, .map a, b]⟩ from rfl, lh_node_term]
    exact Nat.le_refl _

theorem tlit_lh {t : Term} (h : TLit E t) : 1 ≤ lh t ∧ ∀ (k : Int) (tag : String) (l : List Term),
    t = .tuple #[.integer k, .atom tag, Term.list l] → ∀ e ∈ l, lh e ≤ lh t ∧ (lh e < lh t ∨ ExpLit t) := by
  obtain ⟨⟨⟨k, tag, l, rfl, g, -⟩, nt⟩, -⟩ := h
  have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [h₁, h₂]⟩
  by_cases ex : ExpEls tag l
  · obtain ⟨one, els⟩ := lh_lit_exp (k := k) ex
    refine ⟨one, fun k' tag' l' e x mx => ?_⟩
    obtain ⟨-, -, e₃⟩ := tuple3_inj e
    have := list_inj e₃
    subst this
    refine ⟨els x mx, Or.inr ?_⟩
    obtain ⟨rfl, r, a, b, rfl⟩ := ex
    exact ⟨k, r, a, b, rfl⟩
  refine ⟨by rw [lh_lit g top ex]; omega, fun k' tag' l' e => ?_⟩
  obtain ⟨-, -, e₃⟩ := tuple3_inj e
  have := list_inj e₃
  subst this
  intro x mx
  have := lh_list_mem mx
  rw [lh_lit g top ex]; omega

theorem tlit_node_lh {h k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (top : ¬(tag = "open" ∧ l = [])) (c u d : Term) :
    lh (.tuple #[.integer h, .tuple #[.integer k, .atom tag, Term.list l], c, u, d]) =
      max (lh (.tuple #[.integer k, .atom tag, Term.list l])) (max (lh c) (max (lh u) (lh d))) :=
  lh_node_lit (.integer h) (.integer k) (.atom tag) (Term.list l) c u d
    (fun ⟨h₁, h₂⟩ => top ⟨by simpa using h₁, list_eq_nil.mp h₂⟩)
    (fun ⟨_, e, _⟩ => by rcases g with rfl | rfl <;> simp at e) (by simp)

/-- Literals of tuple BDDs are no higher than the BDD. -/
theorem bdd_lh_le {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (lits : ∀ t, ok t → TLit E t) :
    ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x := by
  revert lits
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → TLit E t) → ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _ _ _; exact Bdd.top
  · intro _ _ _ _; exact Bdd.bot
  · intro ok k x y okl _ M le
    exact Bdd.leaf_iff.mpr ⟨okl, le⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd lits M le
    obtain ⟨k, a, b, rfl⟩ := leaf
    have tl := lits _ okl
    obtain ⟨⟨⟨k', tag, l, e, g, -⟩, nt⟩, -⟩ := tl
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [h₁, h₂]⟩
    rw [tlit_node_lh (h := h) g top c u d] at le
    have hlit : lh (.tuple #[.integer k, .atom tag, Term.list l]) ≤ M := by omega
    have hc' : lh c ≤ M ∧ lh u ≤ M ∧ lh d ≤ M := by omega
    have lits' : ∀ t, Above ok (.tuple #[.integer k, .atom tag, Term.list l]) t → TLit E t := fun t ht => lits t ht.1
    refine Bdd.node_iff.mpr ⟨⟨k, _, _, rfl⟩, ⟨okl, hlit⟩, ?_, ?_, ?_⟩
    · exact (ic lits' M hc'.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (iu lits' M hc'.2.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (idd lits' M hc'.2.2).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩

theorem EF.opsU (ef : EF nd E V den tl K) : ElemOk E K :=
  ⟨ef.term, fun ha hb => let ⟨c, hc, run, _⟩ := ef.inter ha hb; ⟨c, hc, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha; ⟨b, run⟩, ef.none, ef.pos⟩

theorem EF.dopsU (ef : EF nd E V den tl K) : ElemDiff E K :=
  ⟨fun ha hb => let ⟨c, hc, run, _⟩ := ef.diff ha hb; ⟨c, hc, run⟩⟩

/-- Types below the seen BDDs are not seen. -/
theorem not_seen {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {x : Term} (hx : lh x < N) (kind : String) :
    S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom kind) x) e.1) (.cons (.atom kind) x) e.1 = .eq)) = Bool.false := by
  simp only [List.any_eq_false, decide_eq_true_eq]
  intro e me hit
  obtain ⟨kind', b, e₁, one, hb⟩ := hS e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
  omega

/-- Seeing a BDD with literals keeps the seen set safe below it. -/
theorem safe_put {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {x : Term} (hx : lh x < N) (one : 1 ≤ lh x)
    (kind : String) : SafeN (lh x) ((.cons (.atom kind) x, .atom "true") :: S) := by
  intro e me
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨.atom kind, x, rfl, one, Nat.le_refl _⟩
  · obtain ⟨kind', b, e₁, one', hb⟩ := hS e me
    exact ⟨kind', b, e₁, one', by omega⟩

theorem not_seenT {N : Nat} {S : List (Term × Term)} (hS : SafeT N S) {x : Term} (hx : lh x < N) (kind : String) :
    S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom kind) x) e.1) (.cons (.atom kind) x) e.1 = .eq)) = Bool.false := by
  simp only [List.any_eq_false, decide_eq_true_eq]
  intro e me hit
  obtain ⟨h, b, e₁, one, hb⟩ := hS e me
  rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
  rcases hb with hb | ⟨⟨i, rfl⟩, -⟩
  · have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
    omega
  · simp at hit

theorem safe_putT {N : Nat} {S : List (Term × Term)} (hS : SafeT N S) {x : Term} (hx : lh x < N) (one : 1 ≤ lh x)
    (kind : String) : SafeN (lh x) ((.cons (.atom kind) x, .atom "true") :: S) := by
  intro e me
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨.atom kind, x, rfl, one, Nat.le_refl _⟩
  · obtain ⟨h, b, e₁, one', hb⟩ := hS e me
    exact ⟨h, b, e₁, one', by omega⟩

theorem tuple_empty_step {d : Dispatcher} {x : Term} {S : List (Term × Term)}
    (fresh : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 = .eq)) = Bool.false) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» d x (.map S) =
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil x
        (.map ((.cons (.atom "tuple") x, .atom "true") :: S)) := by
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]

theorem tlit_bdd_lh {x : Term} (wx : Bdd (TLit E) x) (nt : x ≠ .atom "bdd_top") (nb : x ≠ .atom "bdd_bot") :
    1 ≤ lh x := by
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact absurd rfl nt
  · exact absurd rfl nb
  · exact (tlit_lh (Bdd.leaf_iff.mp wx)).1
  · obtain ⟨⟨k, a, b, rfl⟩, okl, -⟩ := Bdd.node_iff.mp wx
    have := (tlit_lh okl).1
    obtain ⟨⟨⟨k', tag, l, e, g, -⟩, nt'⟩, -⟩ := okl
    obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e
    simp only [Term.integer.injEq] at e₁
    subst e₁ e₂ e₃
    have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt' ⟨_, by rw [h₁, h₂]⟩
    rw [tlit_node_lh (h := h) g top c u d]
    omega

/-- Element types that combine the node with types of height zero. -/
abbrev EC (nd : Term) (E : Term → Prop) (a : Term) : Prop := E a ∧ Combo nd a

theorem combo_term (nd : Term) : Combo nd (.atom "term") := Or.inl rfl

theorem combo_none (nd : Term) : Combo nd (.map []) :=
  Or.inr (Or.inr ⟨[], rfl, fun w h => by simp [mapLookup] at h, fun _ w _ h => by simp [mapLookup] at h⟩)

theorem EF.ops1 (ef : EF nd E V den tl K) : ElemOk (EC nd E) K := by
  refine ⟨⟨ef.term, combo_term nd⟩, fun ha hb => ?_, fun ha S => ?_, ⟨ef.none, combo_none nd⟩, ef.pos⟩
  · obtain ⟨c, hc, run, -, -⟩ := ef.inter ha.1 hb.1
    exact ⟨c, ⟨hc, ef.cinter ha.1 hb.1 ha.2 hb.2 (Nat.le_refl _) (run K (Nat.le_refl _))⟩, run⟩
  · obtain ⟨b, run, -⟩ := ef.empty S ha.1
    exact ⟨b, run⟩

theorem EF.dops1 (ef : EF nd E V den tl K) : ElemDiff (EC nd E) K := by
  refine ⟨fun ha hb => ?_⟩
  obtain ⟨c, hc, run, -, -⟩ := ef.diff ha.1 hb.1
  exact ⟨c, ⟨hc, ef.cdiff ha.1 hb.1 ha.2 hb.2 (Nat.le_refl _) (run K (Nat.le_refl _))⟩, run⟩

theorem EF.sem1 (ef : EF nd E V den tl K) : ElemSem (EC nd E) K V den (Safe1 nd) where
  term := ef.den_term
  inter := fun ha hb hm run v => ef.semR.inter ha.1 hb.1 hm run v
  diff := fun ha hb hm run v => ef.semR.diff ha.1 hb.1 hm run v
  empty := fun ha hS hm run => ef.cempty ha.1 ha.2 hS hm run
  inhabited := ef.inhabited
  resp := fun he he' h d => ef.resp he.1 he'.1 h d

/-- The node holds values: its expansion holds nil. -/
theorem EF.node_inh (ef : EF nd E V den tl K) {e : Term} (he : E e) (ht : IsT nd e) : ∃ w, den e w := by
  obtain ⟨b, run, ex⟩ := ef.empty [] he
  obtain ⟨m, hm⟩ : ∃ m, K = m + 1 := ⟨K - 1, by have := ef.pos; omega⟩
  have r := run (m + 1) (by omega)
  rw [empty_node ht.node m] at r
  have : b = Bool.false := by cases b <;> simp_all [boolAtom]
  subst this
  have h := ex (lh e + 1) (Nat.lt_succ_self _) (safeN_nil _)
  exact Classical.byContradiction fun hn => absurd (h.mpr fun w hw => hn ⟨w, hw⟩) (by decide)

theorem litN_el {e : Term} {k : Int} (ht : TLit E (litN e k)) : E e := by
  obtain ⟨⟨⟨k', tag, l, eq, -, el⟩, -⟩, -⟩ := ht
  obtain ⟨-, -, e₃⟩ := tuple3_inj eq
  have := list_inj e₃
  exact el e (by rw [← this]; simp)

/-- Values of the expansion literal of the node, and values outside it. -/
theorem EF.litN_vals (ef : EF nd E V den tl K) {e : Term} (he : E e) (ht : IsT nd e) (k : Int) :
    (∃ v, valT E den v (litN e k) = Bool.true) ∧ ∃ v, valT E den v (litN e k) = Bool.false := by
  have hl : ∀ x ∈ [Term.atom "term", e], E x := by
    intro x mx; simp at mx; rcases mx with rfl | rfl; exact ef.term; exact he
  obtain ⟨w₁, hw₁⟩ := ef.node_inh he ht
  obtain ⟨w₀⟩ := ef.inhabited
  refine ⟨⟨[w₀, w₁], (vT_lit ef (Or.inr rfl) hl).mpr ?_⟩, ⟨[], ?_⟩⟩
  · simp [InT, ef.den_term, hw₁]
  · cases h : valT E den [] (litN e k)
    · rfl
    · have := (vT_lit ef (Or.inr rfl) hl).mp h
      simp [InT] at this

/-- A walk over a tuple BDD with literals over element types `C` decides the emptiness of the BDD. -/
theorem walk_exact {C : Term → Prop} {Safe : List (Term × Term) → Prop} (ef : EF nd E V den tl K)
    (ops : ElemOk C K) (dops : ElemDiff C K) (sem : ElemSem C K V den Safe) {x : Term} (wx : Bdd (TLit E) x)
    {M : Nat} (le : lh x ≤ M) (okLit : ∀ t, (TLit E t ∧ lh t ≤ M) → TupleOk C t) {S' : List (Term × Term)}
    (hS' : Safe S') {b : Bool}
    (run : Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D (K + 1)) (.tuple #[.atom "open", .nil]) .nil x
      (.map S') = .ok (boolAtom b)) :
    b = Bool.true ↔ ∀ v, denTF E den x v = Bool.false := by
  have wx' := bdd_lh_le wx (fun _ h => h) M le
  have agree : ∀ v, eval (valT C den v) x = eval (valT E den v) x := fun v =>
    eval_ext wx' fun t ht => by
      have h₁ := valT_iff sem (okLit t ht).1 (v := v)
      have h₂ := valT_iff ef.semR ht.1.1.1 (v := v)
      cases e₁ : valT C den v t <;> cases e₂ : valT E den v t <;> simp_all
  have pos : TuplePos C (.tuple #[.atom "open", .nil]) := ⟨"open", [], rfl, Or.inl rfl, by simp⟩
  constructor
  · intro hbt v
    subst hbt
    cases e : denTF E den x v
    · rfl
    · exfalso
      have f := tuple_bdd_false ops dops sem (Nat.le_refl _) _ hS' wx' okLit _ [] pos (by simp) v
        ⟨"open", [], rfl, InT.open_nil v⟩ (by simp) (by rw [agree, ← denTF_bdd wx]; exact e)
      simp only [Term.list] at f
      rw [f] at run
      simp [boolAtom] at run
  · intro unsat
    have t := tuple_bdd_val ops dops sem (Nat.le_refl _) _ hS' wx' okLit _ [] pos (by simp)
      fun v _ _ => by rw [agree, ← denTF_bdd wx]; exact unsat v
    simp only [Term.list] at t
    rw [t] at run
    cases b <;> simp_all [boolAtom]

theorem lh_explit {t : Term} (ex : ExpLit t) : lh t = 1 := by
  obtain ⟨k, r, a, b, rfl⟩ := ex
  simp only [Term.list]
  rw [show (#[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple #[.reference r, .map a, b]) .nil)] :
      Array Term) = ⟨[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩
      from rfl, lh_nodeLit]
  exact lh_node_term

/-- Tuple literals of element types: their elements are below them, or are the node and `term()`. -/
theorem tlit_els (ef : EF nd E V den tl K) {t : Term} (ht : TLit E t) {k : Int} {tag : String} {l : List Term}
    (e : t = .tuple #[.integer k, .atom tag, Term.list l]) {x : Term} (mx : x ∈ l) :
    E x ∧ (lh x < lh t ∨ (lh t = 1 ∧ (x = .atom "term" ∨ IsT nd x))) := by
  have hx : E x := by
    obtain ⟨⟨⟨k', tag', l', e', -, el⟩, -⟩, -⟩ := ht
    rw [e'] at e
    obtain ⟨-, -, e₃⟩ := tuple3_inj e
    exact el x (list_inj e₃ ▸ mx)
  refine ⟨hx, ?_⟩
  rcases ((tlit_lh ht).2 k tag l e x mx).2 with lt | ex
  · exact Or.inl lt
  · refine Or.inr ⟨lh_explit ex, ?_⟩
    obtain ⟨k', r, a, b, rfl⟩ := ex
    obtain ⟨-, -, e₃⟩ := tuple3_inj e
    have := list_inj e₃
    subst this
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at mx
    rcases mx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (ef.node hx ⟨r, a, b, rfl⟩)

/-- Literals of element types exactly equal to an expansion literal of `nd` are expansion literals of `nd`. -/
theorem lit_of_exact (ef : EF nd E V den tl K) {l l' : Term} (hl : PureLit nd l) (hl' : TLit E l')
    (ex : compareExact (fuel l l') l l' = .eq) : PureLit nd l' := by
  obtain ⟨e₀, h₀, rfl⟩ := hl
  obtain ⟨⟨⟨k, tag, l, rfl, -, el⟩, -⟩, -⟩ := hl'
  obtain ⟨S, he₀, -⟩ := h₀.node
  simp only [litN, Term.list, compareExact_tuple, List.size_toArray, List.length_cons, List.length_nil,
    Std.ReflCmp.compare_self, Ordering.then_eq_eq, true_and, List.compareLex_cons_cons, List.compareLex_nil_nil,
    and_true] at ex
  obtain ⟨ek, et, el'⟩ := ex
  have hk := (int_exact ek).mp rfl
  have ht := (atom_exact et).mp rfl
  simp only [Term.integer.injEq, Term.atom.injEq] at hk ht
  subst hk ht
  obtain ⟨y₁, r₁, e₁, ey₁, er₁⟩ := cons_exact el'
  obtain ⟨y₂, r₂, e₂, ey₂, er₂⟩ := cons_exact er₁
  have := (nil_exact er₂).mp rfl
  subst this
  have := (atom_exact ey₁).mp rfl
  subst this
  have ll : l = [.atom "term", y₂] := list_inj (by rw [e₁, e₂])
  subst ll
  subst he₀
  obtain ⟨ys, rfl, ex⟩ := tuple_exact ey₂
  obtain ⟨ys⟩ := ys
  match ys, ex with
  | [r', m', g'], ex =>
    have rr := (reference_compareExact_eq _ _).mp ex.1
    obtain ⟨S', rfl⟩ := map_exact ex.2.1
    subst rr
    exact ⟨_, ef.node (el _ (by simp)) ⟨_, _, _, rfl⟩, rfl⟩

/-- Pure tuple fields are exactly equal only to pure tuple fields, among tuple fields of element types. -/
theorem pure_of_exact (ef : EF nd E V den tl K) {p x : Term} (fp : OField (PureLit nd) p) (wx : Bdd (TLit E) x)
    (e : compareExact (fuel p x) p x = .eq) : Bdd (PureLit nd) x := by
  rcases pure_cases fp with ⟨k, rfl⟩ | rfl | rfl | ⟨e₀, h₀, rfl⟩ | ⟨j, e₀, c, u, d, h₀, rfl⟩
  · obtain ⟨a', b', c', rfl, ea, eb, ec⟩ := exact_tuple3 (Lynx.Term.compareExact_eq_symm e)
    have := (atom_exact eb).mpr rfl
    have := (nil_exact ec).mpr rfl
    have := (int_exact ea).mpr rfl
    subst_vars
    exact absurd ⟨_, rfl⟩ (Bdd.leaf_iff.mp wx).1.2
  · have := (atom_exact (Lynx.Term.compareExact_eq_symm e)).mpr rfl
    subst this; exact Bdd.top
  · have := (atom_exact (Lynx.Term.compareExact_eq_symm e)).mpr rfl
    subst this; exact Bdd.bot
  · rcases wx.shape with rfl | rfl | ⟨k', a', b', rfl⟩ | ⟨hh, lit, c', u', d', rfl⟩
    · simp [litN] at e
    · simp [litN] at e
    rotate_left
    · simp [litN, Term.list, compareExact_tuple] at e
    exact Bdd.leaf_iff.mpr (lit_of_exact ef ⟨e₀, h₀, rfl⟩ (Bdd.leaf_iff.mp wx) e)
  · rcases wx.shape with rfl | rfl | ⟨k', a', b', rfl⟩ | ⟨hh, lit, c', u', d', rfl⟩
    · simp at e
    · simp at e
    · simp [compareExact_tuple] at e
    obtain ⟨isLeaf, okl, -, -, -⟩ := Bdd.node_iff.mp wx
    simp only [compareExact_tuple, List.size_toArray, List.length_cons, List.length_nil, Std.ReflCmp.compare_self,
      Ordering.then_eq_eq, true_and, List.compareLex_cons_cons, List.compareLex_nil_nil,
      and_true] at e
    obtain ⟨-, el, ec, eu, ed⟩ := e
    have btE : ∀ (b : Bool) {y : Term}, compareExact (fuel (bt b) y) (bt b) y = .eq → y = bt b := by
      intro b y h; cases b <;> exact (atom_exact h).mp rfl
    rw [btE c ec, btE u eu, btE d ed]
    have btB : ∀ (ok : Term → Prop) (b : Bool), Bdd ok (bt b) := by
      intro ok b; cases b
      · exact Bdd.bot
      · exact Bdd.top
    exact Bdd.node_iff.mpr ⟨isLeaf, lit_of_exact ef ⟨e₀, h₀, rfl⟩ okl el, btB _ _, btB _ _, btB _ _⟩

/-- Tuple types decide their emptiness exactly, when the seen BDDs are higher than them, or, keyed by an arity,
as high. -/
theorem tuple_empty_exact (ef : EF nd E V den tl K) {x : Term} (fx : TField E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeT N S → (b = Bool.true ↔ ∀ v, denTF E den x v = Bool.false) := by
  have field : TupleField E x := fx.imp id fun w => w.mono fun _ h => h.1
  obtain ⟨b, hb⟩ := tuple_total ef.opsU ef.dopsU S field
  refine ⟨b, hb, fun N hx hS => ?_⟩
  have step := tuple_empty_step (d := D (K + 1)) (not_seenT hS hx "tuple")
  have run := hb (K + 1) (Nat.le_refl _)
  dsimp only at run
  rw [step] at run
  rcases fx with ⟨k, rfl⟩ | wx
  · rw [tuple_walk_top_leaf] at run
    have : b = Bool.false := by
      cases b
      · rfl
      · simp [boolAtom] at run
    subst this
    exact ⟨fun h => absurd h (by decide), fun h => absurd (h []) (by rw [denTF_top]; simp)⟩
  by_cases top : x = .atom "bdd_top"
  · subst top
    rw [tuple_walk_top] at run
    have : b = Bool.false := by
      cases b
      · rfl
      · simp [boolAtom] at run
    subst this
    exact ⟨fun h => absurd h (by decide), fun h => absurd (h []) (by rw [denTF_bdd wx]; simp)⟩
  by_cases bot : x = .atom "bdd_bot"
  · subst bot
    rw [tuple_walk_bot] at run
    have : b = Bool.true := by
      cases b
      · simp [boolAtom] at run
      · rfl
    subst this
    exact ⟨fun _ v => by rw [denTF_bdd wx]; rfl, fun _ => rfl⟩
  have one := tlit_bdd_lh wx top bot
  by_cases pure : Bdd (PureLit nd) x
  · have noid := safeN_noid (safe_putT hS hx one "tuple") (refOf nd)
    obtain ⟨m', hm'⟩ : ∃ m', K + 1 = m' + 2 := ⟨K - 1, by have := ef.pos; omega⟩
    rw [hm'] at run
    rcases pure_shape pure with rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
    · exact absurd rfl top
    · exact absurd rfl bot
    · rw [walk_leaf_node he.node _ m', noid] at run
      have : b = Bool.false := by
        simp only [boolAtom] at run
        cases b <;> simp at run ⊢
      subst this
      obtain ⟨⟨v, hv⟩, -⟩ := ef.litN_vals (litN_el (Bdd.leaf_iff.mp wx)) he (keyOf nd)
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      have := h v
      rw [denTF_bdd wx, show eval (valT E den v) (litN e (keyOf nd)) = valT E den v (litN e (keyOf nd)) by
        simp [litN, Term.list, eval_leaf], hv] at this
      cases this
    · rw [walk_node_node he.node _ _ m', noid] at run
      have hb' : b = (!c && !u && !d) := by
        simp only [boolAtom] at run
        cases b <;> cases c <;> cases u <;> cases d <;> simp at run ⊢
      subst hb'
      obtain ⟨isLeaf, okl, -⟩ := Bdd.node_iff.mp wx
      obtain ⟨⟨v₁, h₁⟩, ⟨v₀, h₀⟩⟩ := ef.litN_vals (litN_el okl) he (keyOf nd)
      have ev : ∀ v, denTF E den (.tuple #[.integer j, litN e (keyOf nd), bt c, bt u, bt d]) v =
          (valT E den v (litN e (keyOf nd)) && c || u || (!valT E den v (litN e (keyOf nd)) && d)) := by
        intro v
        rw [denTF_bdd wx]
        cases c <;> cases u <;> cases d <;> simp [eval, bt]
      constructor
      · intro h v
        rw [ev]
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        obtain ⟨⟨hc, hu⟩, hd⟩ := h
        subst hc hu hd
        simp
      · intro h
        have a₁ := h v₁
        have a₀ := h v₀
        rw [ev, h₁] at a₁
        rw [ev, h₀] at a₀
        cases c <;> cases u <;> cases d <;> simp at a₁ a₀ ⊢
  by_cases two : 2 ≤ lh x
  · refine walk_exact ef (ef.ops (lh x) (by omega)) (ef.dops (lh x)) (ef.sem (lh x)) wx (Nat.le_refl _)
      (fun t ⟨ht, le⟩ => ?_) (safe_putT hS hx one "tuple") run
    obtain ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ := ht
    refine ⟨⟨k, tag, l, rfl, g, fun e me => ?_⟩, nt⟩
    obtain ⟨he, lt | ⟨l1, -⟩⟩ := tlit_els ef ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ rfl me
    · exact ⟨he, by omega⟩
    · have := ((tlit_lh ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩).2 k tag l rfl e me).1
      exact ⟨he, by omega⟩
  · have l1 : lh x = 1 := by omega
    have hS1 : Safe1 nd ((.cons (.atom "tuple") x, .atom "true") :: S) := by
      refine ⟨by have := safe_putT hS hx one "tuple"; rwa [l1] at this, fun e me p fp hit => ?_⟩
      rcases List.mem_cons.mp me with rfl | me
      · rw [compareExact_cons, Ordering.then_eq_eq] at hit
        exact pure (pure_of_exact ef fp wx hit.2)
      · obtain ⟨h', b', e₁, -, hb'⟩ := hS e me
        rw [e₁, compareExact_cons, Ordering.then_eq_eq] at hit
        rcases hb' with hb' | ⟨⟨i, rfl⟩, -⟩
        · have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
          have := pure_le fp
          omega
        · simp at hit
    refine walk_exact ef ef.ops1 ef.dops1 ef.sem1 wx (Nat.le_of_eq l1) (fun t ⟨ht, le⟩ => ?_) hS1 run
    obtain ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ := ht
    refine ⟨⟨k, tag, l, rfl, g, fun e me => ?_⟩, nt⟩
    obtain ⟨he, lt | ⟨-, c⟩⟩ := tlit_els ef ⟨⟨⟨k, tag, l, rfl, g, el⟩, nt⟩, key⟩ rfl me
    · exact ⟨he, ef.low he (by omega)⟩
    · rcases c with rfl | c
      · exact ⟨he, combo_term nd⟩
      · exact ⟨he, Or.inr (Or.inl c)⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Plain operations on tuple types keep literal heights. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- BDDs of tuple literals below a positive height are below it. -/
theorem bdd_lh_bound {ok : Term → Prop} {r : Term} (wr : Bdd ok r) {M : Nat}
    (lits : ∀ t, ok t → TLit E t ∧ lh t ≤ M) (top : 1 ≤ M) : lh r ≤ M := by
  revert lits top
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TLit E t ∧ lh t ≤ M) → 1 ≤ M → lh r ≤ M)
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ top; simpa [lh] using top
  · intro _ _ top; simpa [lh] using top
  · intro ok k x y okl lits _
    exact (lits _ okl).2
  · intro ok h lit c u d leaf okl _ _ _ ic iu idd lits one
    obtain ⟨k, a, b, rfl⟩ := leaf
    have ⟨tl', le⟩ := lits _ okl
    obtain ⟨⟨⟨k', tag, l, e, g, -⟩, nt⟩, -⟩ := tl'
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    have top : ¬(tag = "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [h₁, h₂]⟩
    have lits' : ∀ t, Above ok (.tuple #[.integer k, .atom tag, Term.list l]) t → TLit E t ∧ lh t ≤ M :=
      fun t ht => lits t ht.1
    have hc := ic lits' one
    have hu := iu lits' one
    have hd := idd lits' one
    rw [tlit_node_lh (h := h) g top c u d]
    omega

theorem tfield_mono {x : Term} (wx : Bdd (TLit E) x) {M : Nat} (le : lh x ≤ M) :
    Bdd (fun t => TLit E t ∧ lh t ≤ M) x :=
  (bdd_lh_le wx (fun _ h => h) M le).mono fun _ h => h

/-- BDDs of tuple literals have a height. -/
theorem tbdd_pos {x : Term} (wx : Bdd (TLit E) x) : 1 ≤ lh x := by
  by_cases t : x = .atom "bdd_top"
  · subst t; simp [lh]
  by_cases b : x = .atom "bdd_bot"
  · subst b; simp [lh]
  · exact tlit_bdd_lh wx t b

theorem lh_top_leaf (k : Term) : lh (.tuple #[k, .atom "open", .nil]) = 0 := lh_leaf_top k

/-- Plain unions of tuple types. -/
theorem tuple_union_lh {x y : Term} (hx : TField E x) (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_union/2» x y = .ok r ∧ TField E r ∧
      (∀ v, denTF E den r v = (denTF E den x v || denTF E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨_, by unfold Elixir.Module.Types.Descr.«tuple_union/2»; rfl, Or.inl ⟨k, rfl⟩,
      fun v => by simp [denTF_top], by rw [lh_top_leaf]; omega⟩
  rcases hy with ⟨k, rfl⟩ | wy
  · exact ⟨_, tuple_union_right (not_top_of_ok wx tlit_not) _, Or.inl ⟨k, rfl⟩, fun v => by simp [denTF_top],
      by rw [lh_top_leaf]; omega⟩
  obtain ⟨r, hr, okr, semr⟩ := union_ok wx wy
  have wr := okr _ wx wy
  refine ⟨r, by rw [tuple_union_bdd (not_top_of_ok wx tlit_not) (not_top_of_ok wy tlit_not), hr],
    Or.inr wr, fun v => ?_, ?_⟩
  · rw [denTF_bdd wr, denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]
  · exact bdd_lh_bound (okr _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
      (fun _ h => h) (by have := tbdd_pos wx; omega)

/-- Plain intersections of tuple types. -/
theorem tuple_inter_lh {x y : Term} (hx : TField E x) (hy : TField E y) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_intersection/2» x y = .ok r ∧ TField E r ∧
      (∀ v, denTF E den r v = (denTF E den x v && denTF E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  rcases hx with ⟨k, rfl⟩ | wx
  · exact ⟨y, by unfold Elixir.Module.Types.Descr.«tuple_intersection/2»; rfl, hy, fun v => by simp [denTF_top],
      by omega⟩
  have nx := not_top_of_ok wx tlit_not
  rcases hy with ⟨k, rfl⟩ | wy
  · refine ⟨x, ?_, Or.inr wx, fun v => by simp [denTF_top], by omega⟩
    unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
    split
    · exact (nx _ rfl).elim
    · simp_all
    · rename_i h₁ h₂; exact (h₂ _ rfl).elim
  · obtain ⟨r, hr, okr, semr⟩ := inter_ok wx wy
    have wr := okr _ wx wy
    refine ⟨r, by rw [tuple_intersection_bdd nx (not_top_of_ok wy tlit_not), hr], Or.inr wr, fun v => ?_, ?_⟩
    · rw [denTF_bdd wr, denTF_bdd wx, denTF_bdd wy, semr _ (valT_resp v)]
    · exact bdd_lh_bound (okr _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
        (fun _ h => h) (by have := tbdd_pos wx; omega)

theorem lh_closed_nil (k : Int) : lh (.tuple #[.integer k, .atom "closed", .nil]) = 1 := by
  simp [lh]

theorem lh_open_term (k : Int) : lh (.tuple #[.integer k, .atom "open", Term.list [.atom "term"]]) = 1 := by
  have := lh_lit (k := k) (tag := "open") (l := [.atom "term"]) (Or.inl rfl) (by simp) (by simp [ExpEls])
  rw [this]
  simp [Term.list, lh]

/-- Plain differences of tuple types: non-empty results keep heights. -/
theorem tuple_diff_lh (ef : EF nd E V den tl K) {x y : Term} (fx : TField E x) (fy : TField E y) :
    ∃ w, Elixir.Module.Types.Descr.«tuple_difference/2» x y = .ok w ∧ TField E w ∧
      (∀ v, denTF E den w v = (denTF E den x v && !denTF E den y v)) ∧
      (w ≠ .atom "bdd_bot" → lh w ≤ max (lh x) (lh y)) := by
  obtain ⟨w₀, run₀, fw₀, sem₀⟩ := tuple_diff_val ef fx fy
  refine ⟨w₀, run₀, fw₀, sem₀, fun nb => ?_⟩
  -- the bound, by the cases of the difference
  rcases fy with ⟨k, rfl⟩ | wy
  · have : w₀ = .atom "bdd_bot" := by
      have e : Elixir.Module.Types.Descr.«tuple_difference/2» x (.tuple #[.integer k, .atom "open", .nil]) =
          .ok (.atom "bdd_bot") := by unfold Elixir.Module.Types.Descr.«tuple_difference/2»; rfl
      rw [e] at run₀; cases run₀; rfl
    exact absurd this nb
  have ny := not_top_of_ok wy tlit_not
  by_cases special : ∃ k, y = .tuple #[k, .atom "closed", .nil]
  · obtain ⟨k, rfl⟩ := special
    obtain ⟨k, rfl⟩ := leaf_int wy
    rcases fx with ⟨kt, rfl⟩ | wx
    · obtain ⟨h, run, -⟩ := leaf_new_key "open" (Or.inl rfl) [.atom "term"]
      have e : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.tuple #[.integer k, .atom "closed", .nil]) = .ok (.tuple #[.integer h, .atom "open", Term.list [.atom "term"]]) := by
        simp [Elixir.Module.Types.Descr.«tuple_difference/2», Erlang.erlang.«==/2», run]
      rw [e] at run₀; cases run₀
      rw [lh_open_term, lh_closed_nil]; omega
    · by_cases openLeaf : ∃ kx e, x = .tuple #[kx, .atom "open", e]
      · obtain ⟨kx, e, rfl⟩ := openLeaf
        have ne : e ≠ .nil := fun h => not_top_of_ok wx tlit_not _ (by rw [h])
        have e' : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[kx, .atom "open", e])
            (.tuple #[.integer k, .atom "closed", .nil]) = .ok (.tuple #[kx, .atom "open", e]) := by
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»
          cases e <;> simp_all [Erlang.erlang.«==/2»]
        rw [e'] at run₀; cases run₀; omega
      · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
        rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨h, _⟩ => openLeaf h), run] at run₀
        cases run₀
        exact bdd_lh_bound (keep _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
          (fun _ h => h) (by rw [lh_closed_nil]; omega)
  · rcases fx with ⟨kt, rfl⟩ | wx
    · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · have e : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
            (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»; simp [diff_leaf_top]
        rw [e] at run₀; cases run₀; exact absurd rfl nb
      · have e : Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
            (.atom "bdd_bot") = .ok (.tuple #[.integer kt, .atom "open", .nil]) := by
          unfold Elixir.Module.Types.Descr.«tuple_difference/2»; simp [diff_leaf_bot]
        rw [e] at run₀; cases run₀; omega
      all_goals
        obtain ⟨w, run, keep, sem⟩ := neg_ok wy
        rw [tuple_difference_neg ny (fun k e => special ⟨k, e⟩) _ rfl, run] at run₀
        cases run₀
        exact bdd_lh_bound (keep _ (tfield_mono wy (Nat.le_max_right _ _))) (fun _ h => h)
          (by have := tlit_bdd_lh wy (by simp) (by simp); omega)
    · obtain ⟨w, run, keep, sem⟩ := diff_ok wx wy
      rw [tuple_difference_bdd (not_top_of_ok wx tlit_not) ny (fun ⟨_, h⟩ => special h), run] at run₀
      cases run₀
      exact bdd_lh_bound (keep _ (tfield_mono wx (Nat.le_max_left _ _)) (tfield_mono wy (Nat.le_max_right _ _)))
        (fun _ h => h) (by have := tbdd_pos wx; omega)

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The structural kinds of types (lists, tuples, maps): what each provides to the types holding them. -/

/-- A field, when an operation keeps it. -/
def keptO (name : String) (w : Term) : Option Term := if kept (.atom name, w) then some w else none

/-- A structural kind `name`, with fields `F` and points whose valuations `Val` come from values: plain and optimized
operations hold the points they should, and emptiness is exact under seen sets of higher BDDs, at call depths from
`K`. Plain operations keep literal heights, except differences by the empty field. -/
structure KindOk (K : Nat) (name : String) (F : Term → Prop) (Val : (Term → Bool) → Prop) : Prop where
  resp : ∀ ρ, Val ρ → Resp ρ
  wit : ∃ ρ, Val ρ
  top : ∀ t, TopAt name t → F t ∧ lh t = 0 ∧ ∀ p : Point, Val p.2.2 → dn name (some t) p = Bool.true
  congr : ∀ {x x'}, F x → F x' → Term.compare (Term.fuel x x') x x' = .eq → ∀ p : Point, Val p.2.2 →
    dn name (some x) p = dn name (some x') p
  union : ∀ {x y}, F x → F y → ∃ w, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/3» (D m) (.atom name) x y = .ok w) ∧
    F w ∧ (∀ p : Point, Val p.2.2 → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
    lh w ≤ max (lh x) (lh y)
  inter : ∀ {x y}, F x → F y → ∃ w,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom name) x y = .ok w) ∧
    (kept (.atom name, w) = Bool.true → F w ∧ lh w ≤ max (lh x) (lh y)) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)
  diff : ∀ {x y}, F x → F y → ∃ w,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom name) x y = .ok w) ∧
    (kept (.atom name, w) = Bool.true → F w ∧ lh w ≤ max (lh x) (lh y)) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)
  opt_union : ∀ {x y} (S : List (Term × Term)) {m}, F x → F y → K ≤ m → ∃ w,
    Elixir.Module.Types.Descr.«opt_union/4» (D m) (.atom name) x y (.map S) = .ok w ∧ F w ∧
    ∀ p : Point, Val p.2.2 → dn name (some w) p = (dn name (some x) p || dn name (some y) p)
  opt_inter : ∀ {x y} (S : List (Term × Term)) {m}, F x → F y → K ≤ m → ∃ w,
    Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom name) x y (.map S) = .ok w ∧
    (kept (.atom name, w) = Bool.true → F w) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)
  opt_diff : ∀ {x y} (S : List (Term × Term)) {m}, F x → F y → K ≤ m → ∃ w,
    Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom name) x y (.map S) = .ok w ∧
    (kept (.atom name, w) = Bool.true → F w) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)
  empty : ∀ {x} (S : List (Term × Term)), F x → ∃ b : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S) = .ok (boolAtom b)) ∧
    ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ p : Point, Val p.2.2 → dn name (some x) p = Bool.false)

theorem keptO_true {name : String} {w : Term} (h : kept (.atom name, w) = Bool.true) : keptO name w = some w := by
  simp [keptO, h]

theorem keptO_false {name : String} {w : Term} (h : kept (.atom name, w) = Bool.false) : keptO name w = none := by
  simp [keptO, h]

/-- Fields dropped from BDD kinds are the empty BDD. -/
theorem dropped_bdd {w : Term} (h : kept (.atom "x", w) = Bool.false) (nz : w ≠ .integer 0) : w = .atom "bdd_bot" := by
  simp only [kept, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd ((compareExact_eq_integer _ _).mp h) nz
  · exact (compareExact_eq_atom _ _).mp h

theorem kept_name {name name' : String} (w : Term) : kept (.atom name, w) = kept (.atom name', w) := rfl

theorem kept_ne_bot {name : String} {w : Term} (h : kept (.atom name, w) = Bool.true) : w ≠ .atom "bdd_bot" := by
  rintro rfl; simp [kept] at h

theorem tuple_cmp_top {k b : Term} (h : Term.compare (Term.fuel (.tuple #[k, .atom "open", .nil]) b) (.tuple #[k, .atom "open", .nil]) b = .eq) :
    ∃ k', b = .tuple #[k', .atom "open", .nil] := by
  cases b <;> rw [compare_step] at h <;> simp [Compare.compareStep] at h
  rename_i ys
  obtain ⟨l⟩ := ys
  match l, h with
  | [k', x, y], h =>
    simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
    obtain ⟨-, hx, hy, -⟩ := h
    subst hy
    have hx' := (compare_eq_atom _ _).mp (Lynx.Term.compare_eq_symm hx)
    subst hx'
    exact ⟨k', rfl⟩
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | _ :: _ :: _ :: _ :: _, h => simp at h

/-- Open fields mean the same up to comparison. -/
theorem denO_congr {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) {x x' : Term} (fx : OField ok x)
    (fx' : OField ok x') (e : Term.compare (Term.fuel x x') x x' = .eq) {ρ : Term → Bool} (resp : Resp ρ) : denO x ρ = denO x' ρ := by
  rcases fx with ⟨k, rfl⟩ | wx
  · obtain ⟨k', rfl⟩ := tuple_cmp_top e
    rw [denO_top, denO_top]
  rcases fx' with ⟨k', rfl⟩ | wx'
  · obtain ⟨k, rfl⟩ := tuple_cmp_top (Lynx.Term.compare_eq_symm e)
    obtain ⟨k'', rfl⟩ := leaf_int wx
    exact absurd ⟨_, rfl⟩ (okNot _ (Bdd.leaf_iff.mp wx))
  rw [denO_bdd okNot wx, denO_bdd okNot wx', eval_congr_cmp wx resp e]

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem dn_tupleT {x : Term} {p : Point} {v : List V} (e : p.2.2 = valT E den v) :
    dn "tuple" (some x) p = denTF E den x v := by
  rw [dn_tuple, e]; rfl

theorem tfield_nz {w : Term} (fw : TField E w) : w ≠ .integer 0 := by
  rcases fw with ⟨k, rfl⟩ | ww
  · simp
  · exact bdd_ne_zero ww

/-- Tuples are a structural kind. -/
theorem tupleKind (ef : EF nd E V den tl K) : KindOk (K + 2) "tuple" (TField E) (ValT E den) where
  resp := valT_respT
  wit := ⟨_, [], rfl⟩
  top := fun t ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ | ⟨h, _⟩ <;> try simp at h
    exact ⟨Or.inl ⟨_, rfl⟩, lh_top_leaf _, fun p _ => by rw [dn_tuple, denO_top]⟩
  congr := fun fx fx' e p ⟨v, hv⟩ => by
    rw [dn_tuple, dn_tuple, hv]
    exact denO_congr tlit_not fx fx' e (valT_resp v)
  union := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := tuple_union_lh (den := den) fx fy
    exact ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], fw,
      fun p ⟨v, hv⟩ => by rw [dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem], le⟩
  inter := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := tuple_inter_lh (den := den) fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun _ => ⟨fw, le⟩,
      fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  diff := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := tuple_diff_lh ef (den := den) fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun k => ⟨fw, le (kept_ne_bot k)⟩,
      fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  opt_union := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := opt_tuple_union_sem ef (m := m) (by omega) fx fy
    exact ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_union/4»] using run, fw,
      fun p ⟨v, hv⟩ => by rw [dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]⟩
  opt_inter := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := opt_tuple_inter_val ef hm fx fy S
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_intersection/4»] using run, fun _ => fw, fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  opt_diff := by
    intro x y S m fx fy hm
    obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 ≤ m by omega)
    obtain ⟨w, run, fw, sem⟩ := opt_tuple_diff_val ef hn fx fy
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_difference/4»] using run, fun _ => fw, fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  empty := fun S fx => by
    obtain ⟨b, run, ex⟩ := tuple_empty_exact ef fx S
    refine ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m (by omega),
      fun N hx hS => (ex N hx hS.toT).trans ⟨fun h p ⟨v, hv⟩ => by rw [dn_tupleT hv]; exact h v,
        fun h v => by have := h (0, .nil, valT E den v) ⟨v, rfl⟩; rwa [dn_tupleT rfl] at this⟩⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Soundness of list emptiness: `list_empty?/2` answers `true` only for list types without lists of values. -/

/-- A valuation satisfying a BDD satisfies one of its lines. -/
theorem nl_dnf_cover {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧ (∀ l ∈ acc, l ∈ lines) ∧
      ∀ ρ, (∀ t ∈ pos, ρ t = Bool.true) → (∀ t ∈ negs, ρ t = Bool.false) → eval ρ r = Bool.true →
        ∃ l ∈ lines, LineSat ρ l := by
  refine Bdd.induction (P := fun ok r => ∀ (acc pos negs : List Term), ∃ lines : List Term,
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list acc) (Term.list pos) (Term.list negs) r =
        .ok (Term.list lines) ∧ (∀ l ∈ acc, l ∈ lines) ∧
      ∀ ρ, (∀ t ∈ pos, ρ t = Bool.true) → (∀ t ∈ negs, ρ t = Bool.false) → eval ρ r = Bool.true →
        ∃ l ∈ lines, LineSat ρ l) ?_ ?_ ?_ ?_ ok r wr
  · intro ok acc pos negs
    refine ⟨.tuple #[Term.list pos, Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l ml => List.mem_cons_of_mem _ ml,
      fun ρ hp hn _ => ?_⟩
    exact ⟨_, List.mem_cons_self, pos, negs, rfl, hp, hn⟩
  · intro ok acc pos negs
    exact ⟨acc, by simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»], fun l ml => ml, fun ρ _ _ h => by simp at h⟩
  · intro ok k x y _ acc pos negs
    refine ⟨.tuple #[Term.list (.tuple #[.integer k, x, y] :: pos), Term.list negs] :: acc, by
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», Term.list], fun l ml => List.mem_cons_of_mem _ ml,
      fun ρ hp hn h => ?_⟩
    refine ⟨_, List.mem_cons_self, _, negs, rfl, fun t mt => ?_, hn⟩
    rcases List.mem_cons.mp mt with rfl | mt
    · simpa using h
    · exact hp t mt
  · intro ok h lit c u d _ _ hc hu hd ic iu id acc pos negs
    obtain ⟨l₁, r₁, a₁, h₁⟩ := iu acc pos negs
    obtain ⟨l₂, r₂, a₂, h₂⟩ := ic l₁ (lit :: pos) negs
    obtain ⟨l₃, r₃, a₃, h₃⟩ := id l₂ pos (lit :: negs)
    refine ⟨l₃, ?_, fun l ml => a₃ l (a₂ l (a₁ l ml)), fun ρ hp hn e => ?_⟩
    · simp only [Term.list] at r₁ r₂ r₃ ⊢
      simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4», r₁, r₂, r₃]
    simp only [eval_node] at e
    cases hu' : eval ρ u
    · cases hl : ρ lit
      · simp [hl, hu'] at e
        obtain ⟨l, ml, sl⟩ := h₃ ρ hp (fun t mt => by
          rcases List.mem_cons.mp mt with rfl | mt
          · exact hl
          · exact hn t mt) e
        exact ⟨l, ml, sl⟩
      · simp [hl, hu'] at e
        obtain ⟨l, ml, sl⟩ := h₂ ρ (fun t mt => by
          rcases List.mem_cons.mp mt with rfl | mt
          · exact hl
          · exact hp t mt) hn e
        exact ⟨l, a₃ l ml, sl⟩
    · obtain ⟨l, ml, sl⟩ := h₁ ρ hp hn hu'
      exact ⟨l, a₃ l (a₂ l ml), sl⟩

section
variable {E : Term → Prop} {K : Nat} {V : Type} {den : Term → V → Prop} {Safe : List (Term × Term) → Prop}

/-- `list_line_negs_empty?/4` answers `true` only when its negations cover the lists of the line. -/
theorem nl_negs_sound (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a : Term} (ha : E a) :
    ∀ negs : List Term, (∀ t ∈ negs, LLit E t) → ∀ t, E t → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«list_line_negs_empty?/4» (D m) (Term.list negs) a t (.map S) = .ok (.atom "true") →
      ∀ xs : List V, (∀ x ∈ xs, den a x) → ∀ y, den t y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩ := by
  intro negs
  induction negs with
  | nil =>
    intro _ t _ m _ run
    rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def] at run
    simp at run
  | cons N rest ih =>
    intro lits t ht m hm run xs hxs y hy
    obtain ⟨k, nt, nl, rfl, hnt, hnl⟩ := lits _ List.mem_cons_self
    have lits' : ∀ t ∈ rest, LLit E t := fun t m => lits t (List.mem_cons_of_mem _ m)
    obtain ⟨sd, hsd, rsd⟩ := dops.diff ha hnt
    have dsd := sem.diff ha hnt hm (rsd m hm)
    obtain ⟨bs, hbs⟩ := ops.empty hsd S
    cases bs
    · have rc : Elixir.Module.Types.Descr.«list_line_negs_empty?/4» (D m) (Term.list rest) a t (.map S) =
          .ok (.atom "true") := by
        rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def] at run
        simp only [] at run ⊢
        simpa [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, Lynx.Except.guard,
          isMember] using run
      obtain ⟨N', mN, hN⟩ := ih lits' t ht m hm rc xs hxs y hy
      exact ⟨N', List.mem_cons_of_mem _ mN, hN⟩
    · have sub : ∀ x, den a x → den nt x := fun x hx => Classical.byContradiction fun nx =>
        (sem.empty hsd hS hm (hbs m hm)).mp rfl x ((dsd x).mpr ⟨hx, nx⟩)
      have cover : den nl y → ∃ N' ∈ Term.tuple #[.integer k, nt, nl] :: rest, LLitSem den N' ⟨xs, y⟩ :=
        fun h => ⟨_, List.mem_cons_self, llitSem_iff.mpr ⟨fun x mx => sub x (hxs x mx), h⟩⟩
      obtain ⟨t', ht', ht'E, dt'⟩ := tsem.unfold hnl
      obtain ⟨dd, hdd, rdd⟩ := dops.diff ht ht'E
      have ddd := sem.diff ht ht'E hm (rdd m hm)
      obtain ⟨be, hbe⟩ := ops.empty hdd S
      obtain ⟨b, hb⟩ := negs_total ops dops tsem.ok S ha rest lits' dd hdd
      have h₁ := hb m hm
      dsimp only at h₁
      have res : (be || b) = Bool.true := by
        rw [Elixir.Module.Types.Descr.«list_line_negs_empty?/4».eq_def] at run
        simp only [] at h₁ run
        simp [Elixir.Module.Types.Descr.«subtype_seen?/3», rsd m hm, hbs m hm, boolAtom, isMember,
          ht' m (by have := ops.pos; omega), rdd m hm, hbe m hm, h₁] at run
        cases be <;> cases b <;> simp_all
      by_cases hn : den nl y
      · exact cover hn
      have hd : den dd y := (ddd y).mpr ⟨hy, fun h => hn ((dt' y).mp h).1⟩
      cases be
      · simp only [Bool.false_or] at res
        subst res
        obtain ⟨N', mN, hN⟩ := ih lits' dd hdd m hm h₁ xs hxs y hd
        exact ⟨N', List.mem_cons_of_mem _ mN, hN⟩
      · exact absurd hd ((sem.empty hdd hS hm (hbe m hm)).mp rfl y)

/-- `list_line_empty?/4` answers `true` only when the negations cover the lists of the line. -/
theorem nl_line_sound (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) (S : List (Term × Term)) (hS : Safe S) {a b : Term} (ha : E a) (hb : E b)
    {negs : List Term} (lits : ∀ t ∈ negs, LLit E t) {m : Nat} (hm : K ≤ m)
    (run : Elixir.Module.Types.Descr.«list_line_empty?/4» (D m) a b (Term.list negs) (.map S) = .ok (.atom "true")) :
    ∀ xs : List V, xs ≠ [] → (∀ x ∈ xs, den a x) → ∀ y, den b y → ¬tl y → ∃ N ∈ negs, LLitSem den N ⟨xs, y⟩ := by
  intro xs ne hxs y hy ny
  obtain ⟨t, ht, htE, dt⟩ := tsem.unfold hb
  obtain ⟨b₁, h₁⟩ := ops.empty ha S
  obtain ⟨b₂, h₂⟩ := ops.empty htE S
  obtain ⟨b₃, h₃⟩ := negs_total ops dops tsem.ok S ha negs lits t htE
  have e₃ := h₃ m hm
  dsimp only at e₃
  have res : (b₁ || b₂ || b₃) = Bool.true := by
    unfold Elixir.Module.Types.Descr.«list_line_empty?/4» at run
    simp only [ht m (by have := ops.pos; omega), Lynx.Except.ok_bind, h₁ m hm, h₂ m hm, e₃, Elixir.STTDescrProofsTest.orElse_bool] at run
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp_all [boolAtom]
  have hyt : den t y := (dt y).mpr ⟨hy, ny⟩
  cases b₁
  · cases b₂
    · simp only [Bool.false_or] at res
      subst res
      exact nl_negs_sound ops dops sem tsem S hS ha negs lits t htE m hm e₃ xs hxs y hyt
    · exact absurd hyt ((sem.empty htE hS hm (h₂ m hm)).mp rfl y)
  · obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil xs ne
    exact absurd (hxs x mx) ((sem.empty ha hS hm (h₁ m hm)).mp rfl x)

/-- `non_empty_list_literals_intersection/2` finds the positive literals of a line empty only when no list is in all
of them. -/
theorem nl_literals_sound (ops : ElemOk E K) (sem : ElemSem E K V den Safe) (S : List (Term × Term)) (hS : Safe S)
    (pos : List Term) (lits : ∀ t ∈ pos, LLit E t) :
    ((∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«non_empty_list_literals_intersection/2» (D m) (Term.list pos)
      (.map S) = .ok (.atom "empty")) ∧ ∀ v : LV V, v.xs ≠ [] → ¬∀ t ∈ pos, LLitSem den t v) ∨
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
  have semf' : ∀ v : LV V, ((∀ x ∈ v.xs, den a x) ∧ den b v.last) ↔ ∀ t ∈ pos, LLitSem den t v := fun v => by
    rw [semf v]
    exact ⟨fun h => h.2, fun h => ⟨⟨fun x _ => sem.term x, sem.term _⟩, h⟩⟩
  by_cases e : (ea || eb) = Bool.true
  · refine Or.inl ⟨fun m hm => by rw [unfold m hm, ite_eq_left e], fun v ne all => ?_⟩
    obtain ⟨hxs, hlast⟩ := (semf' v).mpr all
    cases ea
    · simp only [Bool.false_or] at e
      subst e
      exact (sem.empty hb hS (Nat.le_refl K) (heb K (Nat.le_refl K))).mp rfl _ hlast
    · obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil v.xs ne
      exact (sem.empty ha hS (Nat.le_refl K) (hea K (Nat.le_refl K))).mp rfl x (hxs x mx)
  · exact Or.inr ⟨a, b, ha, hb, fun m hm => by rw [unfold m hm, ite_eq_right e], semf'⟩

/-- `list_empty?/2` answers `true` only for list BDDs that no list of values satisfies, when the BDD is not seen
and the seen set with it keeps the emptiness of elements exact. -/
theorem nl_list_sound (ops : ElemOk E K) (dops : ElemDiff E K) (sem : ElemSem E K V den Safe) {tl : V → Prop}
    (tsem : TailSem E den tl) {m : Nat} (hm : K + 2 ≤ m) {r : Term} (wr : Bdd (LLit E) r) (S : List (Term × Term))
    (fresh : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 = .eq)) = Bool.false)
    (safe : Safe ((.cons (.atom "list") r, .atom "true") :: S))
    (run : Elixir.Module.Types.Descr.«list_empty?/2» (D m) r (.map S) = .ok (.atom "true")) :
    ∀ v : LV V, v.xs ≠ [] → ¬tl v.last → eval (valL E den v) r = Bool.false := by
  by_cases top : r = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  · subst top
    unfold Elixir.Module.Types.Descr.«list_empty?/2» at run
    simp at run
  have put : Erlang.maps.«put/3» (.cons (.atom "list") r) (.atom "true") (.map S) =
      .ok (.map ((.cons (.atom "list") r, .atom "true") :: S)) := rfl
  generalize hS' : (Term.cons (.atom "list") r, Term.atom "true") :: S = S' at safe put
  obtain ⟨lines, dnf, hlines⟩ := dnf_lines wr (LLit E) (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  obtain ⟨lines', dnf', -, hcov⟩ := nl_dnf_cover wr [] [] []
  have same : lines' = lines := list_inj (by rw [dnf] at dnf'; exact (Except.ok.inj dnf').symm)
  subst same
  have each : ∀ x ∈ lines', ∃ bx, (∀ m', K + 1 ≤ m' →
      Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D m') (.map S') x = .ok (boolAtom bx)) ∧
      (bx = Bool.true → ∀ v : LV V, v.xs ≠ [] → ¬tl v.last → ¬LineSat (valL E den v) x) := by
    intro x mx
    obtain ⟨pos, negs, rfl, hp, hn⟩ := hlines x mx
    rcases nl_literals_sound ops sem S' safe pos hp with ⟨empty, none⟩ | ⟨a, b, ha, hb, runl, semab⟩
    · refine ⟨Bool.true, fun m' h => by
        simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», empty m' h, boolAtom], fun _ v ne _ sat => ?_⟩
      obtain ⟨P, N, e, hP, -⟩ := sat
      obtain ⟨rfl, rfl⟩ := line_inj e
      exact none v ne fun t mt => (valL_iff sem (hp t mt)).mp (hP t mt)
    · obtain ⟨bl, hbl⟩ := line_list_total ops dops tsem.ok S' ha hb hn
      refine ⟨bl, fun m' h => by
        have := hbl m' (by omega)
        dsimp only at this
        simp [Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2», runl m' h, this], fun e v ne nl sat => ?_⟩
      subst e
      obtain ⟨P, N, ee, hP, hN⟩ := sat
      obtain ⟨rfl, rfl⟩ := line_inj ee
      obtain ⟨hxs, hlast⟩ := (semab v).mpr fun t mt => (valL_iff sem (hp t mt)).mp (hP t mt)
      have line := hbl K (Nat.le_refl K)
      dsimp only at line
      obtain ⟨N', mN, hN'⟩ := nl_line_sound ops dops sem tsem S' safe ha hb hn (Nat.le_refl K)
        (by simpa [boolAtom] using line) v.xs ne hxs v.last hlast nl
      have := hN N' mN
      rw [(valL_iff sem (hn N' mN)).mpr hN'] at this
      cases this
  classical
  let res : Term → Bool := fun x => if h : x ∈ lines' then Classical.choose (each x h) else Bool.false
  have hres : ∀ x (h : x ∈ lines'), ∀ m', K + 1 ≤ m' →
      Elixir.Module.Types.Descr.«-list_empty?/2-fun-0-/2» (D m') (.map S') x = .ok (boolAtom (res x)) := by
    intro x mx m' h
    simp only [res, dite_eq_left mx]
    exact (Classical.choose_spec (each x mx)).1 m' h
  obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 + 1 ≤ m by omega)
  have all := all_list (D (n + 1)) _ _ _ res lines' fun x mx => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-list_empty?/2-fun-0-/1».pure]
    exact hres x mx n hn
  have allTrue : lines'.all res = Bool.true := by
    unfold Elixir.Module.Types.Descr.«list_empty?/2» at run
    split at run
    · exact absurd rfl top
    · simp only [Term.list] at dnf
      simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
        Term.false, put, Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf] at run
      rw [all] at run
      cases h : lines'.all res
      · rw [h] at run; simp [boolAtom] at run
      · rfl
  intro v ne nl
  cases e : eval (valL E den v) r
  · rfl
  · obtain ⟨l, ml, sat⟩ := hcov _ (by simp) (by simp) e
    have rl : res l = Bool.true := List.all_eq_true.mp allTrue l ml
    have := (Classical.choose_spec (each l ml)).2
    simp only [res, dite_eq_left ml] at rl
    exact absurd sat (this rl v ne nl)

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! List types of element types: their emptiness is exact on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Lists of values: non-empty, whose tail is not a non-empty list. -/
def ListVal (tl : V → Prop) (v : LV V) : Prop := v.xs ≠ [] ∧ ¬tl v.last

/-- Element types of the whole class, with operations at every call depth from `K`. -/
theorem EF.opsE (ef : EF nd E V den tl K) : ElemOk E K :=
  ⟨ef.term, fun ha hb => let ⟨c, hc, run, _⟩ := ef.inter ha hb; ⟨c, hc, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha; ⟨b, run⟩, ef.none, ef.pos⟩

theorem EF.dopsE (ef : EF nd E V den tl K) : ElemDiff E K :=
  ⟨fun ha hb => let ⟨c, hc, run, _⟩ := ef.diff ha hb; ⟨c, hc, run⟩⟩

theorem EF.tailE (ef : EF nd E V den tl K) : TailOk E := fun _ he =>
  let ⟨e', run, he', _⟩ := ef.tail he
  ⟨e', run, he'⟩

theorem EF.shape (ef : EF nd E V den tl K) {a : Term} (ha : E a) :
    a = .atom "term" ∨ (∃ X, a = .map X) ∨ IsNode a := by
  rcases ef.static ha with rfl | ⟨X, rfl, -⟩ | hn₀
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨X, rfl⟩)
  · exact Or.inr (Or.inr hn₀)

theorem nl_lh_leaf {k : Int} {a b : Term} (hb : b = .atom "term" ∨ (∃ X, b = .map X) ∨ IsNode b)
    (nt : ¬(k = 46675407 ∧ a = .atom "term" ∧ b = .atom "term")) :
    lh (.tuple #[.integer k, a, b]) = max (lh a) (lh b) + 1 :=
  lh_leaf _ _ _ (fun h => by rcases hb with rfl | ⟨X, rfl⟩ | ⟨r, st, g, rfl⟩ <;> simp at h)
    (fun ⟨e, ea, eb⟩ => nt ⟨by simpa using e, ea, eb⟩)
    (by rintro ⟨-, r, x, y, rfl⟩; rcases hb with h | ⟨X, h⟩ | ⟨r', st, g, h⟩ <;> simp at h) (by simp)

theorem nl_lh_node {h k : Int} {a b c u d : Term} (ha : a = .atom "term" ∨ (∃ X, a = .map X) ∨ IsNode a) :
    lh (.tuple #[.integer h, .tuple #[.integer k, a, b], c, u, d]) =
      max (max (lh a) (lh b) + 1) (max (lh c) (max (lh u) (lh d))) :=
  lh_node _ _ _ _ _ _ _ (by rcases ha with rfl | ⟨X, rfl⟩ | ⟨r, st, g, rfl⟩ <;> simp [litZ])

theorem nl_lh_node_le {h k : Int} {a b c u d : Term} :
    lh (.tuple #[.integer h, .tuple #[.integer k, a, b], c, u, d]) ≤
      max (max (lh a) (lh b) + 1) (max (lh c) (max (lh u) (lh d))) := by
  cases hz : litZ a b
  · exact Nat.le_of_eq (lh_node _ _ _ _ _ _ _ hz)
  · rw [show (#[.integer h, .tuple #[.integer k, a, b], c, u, d] : Array Term) =
      ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩ from rfl, lh_node_z _ _ _ _ _ _ _ hz]
    unfold litZ at hz
    split at hz
    · rw [lh_nodeLit]; simp only [lh]; omega
    · cases hz

/-- The literals of a list BDD below some height have elements below that height. -/
theorem nl_lits_bound (ef : EF nd E V den tl K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → LLit E t) → ∀ N, 1 ≤ N → lh r ≤ N → Bdd (fun t => ok t ∧ LLit (EB E N) t) r := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → LLit E t) → ∀ N, 1 ≤ N → lh r ≤ N →
    Bdd (fun t => ok t ∧ LLit (EB E N) t) r) ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ _ _ _; exact Bdd.top
  · intro _ _ _ _ _; exact Bdd.bot
  · intro ok k x y okl lits N one le
    obtain ⟨k', a, b, e, ha, hb⟩ := lits _ okl
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    refine Bdd.leaf_iff.mpr ⟨okl, k, x, y, rfl, ⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
    all_goals
      by_cases top : k = 46675407 ∧ x = .atom "term" ∧ y = .atom "term"
      · obtain ⟨-, e₁, e₂⟩ := top; subst e₁ e₂; simp [lh]; omega
      · rw [nl_lh_leaf (ef.shape hb) top] at le; omega
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits N one le
    obtain ⟨k', a, b, rfl, ha, hb⟩ := lits _ okl
    rw [nl_lh_node (ef.shape ha)] at le
    have lift : ∀ x, (fun t => Above ok (.tuple #[.integer k', a, b]) t ∧ LLit (EB E N) t) x →
        Above (fun t => ok t ∧ LLit (EB E N) t) (.tuple #[.integer k', a, b]) x :=
      fun x hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
    have lits' : ∀ t, Above ok (.tuple #[.integer k', a, b]) t → LLit E t := fun t ht => lits t ht.1
    refine Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, k', a, b, rfl, ⟨ha, by omega⟩, ⟨hb, by omega⟩⟩,
      (ic lits' N one (by omega)).mono lift, (iu lits' N one (by omega)).mono lift,
      (id lits' N one (by omega)).mono lift⟩

/-- Seen sets of higher BDDs never hold a BDD. -/
theorem nl_fresh {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {r : Term} (hr : lh r < N) (kind : String) :
    S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom kind) r) e.1) (.cons (.atom kind) r) e.1 = .eq)) = Bool.false := by
  cases h : S.any (fun e => decide (Term.compareExact (Term.fuel (.cons (.atom kind) r) e.1) (.cons (.atom kind) r) e.1 = .eq))
  · rfl
  · exfalso
    obtain ⟨e, me, hit⟩ := List.any_eq_true.mp h
    obtain ⟨k, b, e₁, -, hb⟩ := hS e me
    rw [e₁] at hit
    simp only [decide_eq_true_eq, compareExact_cons, Ordering.then_eq_eq] at hit
    have := lh_exact _ _ _ (Nat.lt_succ_self _) hit.2
    omega

theorem nl_safe_put {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) {r : Term} (hr : lh r < N) (one : 1 ≤ lh r)
    (kind : String) : SafeN (lh r) ((.cons (.atom kind) r, .atom "true") :: S) := by
  intro e me
  rcases List.mem_cons.mp me with rfl | me
  · exact ⟨.atom kind, r, rfl, one, Nat.le_refl _⟩
  · obtain ⟨k, b, e₁, one', hb⟩ := hS e me
    exact ⟨k, b, e₁, one', by omega⟩

/-- Valuations of list literals do not depend on how far below the element types are. -/
theorem nl_valL_eq (ef : EF nd E V den tl K) {N : Nat} (v : LV V) {t : Term} (ht : LLit (EB E N) t) :
    valL (EB E N) den v t = valL E den v t := by
  obtain ⟨k, a, b, rfl, ha, hb⟩ := ht
  apply Bool.eq_iff_iff.mpr
  rw [valL_iff (ef.sem N) ⟨k, a, b, rfl, ha, hb⟩, valL_iff ef.semR ⟨k, a, b, rfl, ha.1, hb.1⟩]

theorem nl_safeF_put {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) (r : Term)
    (nt : compareExact (fuel (.tuple #[.integer 61102469, .atom "open", .nil]) r) (.tuple #[.integer 61102469, .atom "open", .nil]) r ≠ .eq) (kind : String) :
    SafeF ((.cons (.atom kind) r, .atom "true") :: S) := by
  obtain ⟨L, e, all⟩ := safeF_of hS
  simp only [Term.map.injEq] at e
  subst e
  refine ⟨_, rfl, fun e me k hit => ?_⟩
  rcases List.mem_cons.mp me with rfl | me
  · rw [compareExact_cons, Ordering.then_eq_eq] at hit
    exact nt hit.2
  · exact all e me k hit

/-- `list_empty?/2` decides exactly whether list types of element types hold lists of values. -/
theorem nl_list_empty (ef : EF nd E V den tl K) {x : Term} (wx : Bdd (LLit E) x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m → Elixir.Module.Types.Descr.«list_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ v, ListVal tl v → eval (valL E den v) x = Bool.false) := by
  obtain ⟨b, hb⟩ := list_total ef.opsE ef.dopsE ef.tailE S wx
  refine ⟨b, hb, fun N hN hS => ?_⟩
  obtain ⟨x₀⟩ := ef.inhabited
  obtain ⟨y₀, hy₀⟩ := ef.tl_witness
  have v₀ : ListVal tl ⟨[x₀], y₀⟩ := ⟨by simp, hy₀⟩
  have fresh := nl_fresh hS hN "list"
  have run := hb (K + 2) (Nat.le_refl _)
  dsimp only at run
  by_cases top : x = .tuple #[.integer 46675407, .atom "term", .atom "term"]
  · subst top
    have : b = Bool.false := by
      unfold Elixir.Module.Types.Descr.«list_empty?/2» at run
      cases b <;> simp_all [boolAtom]
    subst this
    simp only [Bool.false_eq_true, false_iff]
    intro all
    have := all _ v₀
    rw [eval_leaf, (valL_iff ef.semR ⟨_, _, _, rfl, ef.term, ef.term⟩).mpr
      (llitSem_iff.mpr ⟨fun x _ => ef.den_term x, ef.den_term _⟩)] at this
    cases this
  by_cases one : 1 ≤ lh x
  · have wb := (nl_lits_bound ef wx (fun _ h => h) (lh x) one (Nat.le_refl _)).mono fun _ h => h.2
    have safe := nl_safe_put hS hN one "list"
    have agree : ∀ v, eval (valL (EB E (lh x)) den v) x = eval (valL E den v) x := fun v =>
      eval_ext wb fun t ht => nl_valL_eq ef v ht
    constructor
    · intro e v lv
      subst e
      rw [← agree v]
      exact nl_list_sound (ef.ops _ one) (ef.dops _) (ef.sem _) (ef.tsem _) (Nat.le_refl _) wb S fresh safe
        (by simpa [boolAtom] using run) v lv.1 lv.2
    · intro unsat
      have := list_empty_val (ef.ops _ one) (ef.dops _) (ef.sem _) (ef.tsem _) (Nat.le_refl _) wb S
        (fun S' put => by
          simp only [Erlang.maps.«put/3», Except.ok.injEq, Term.map.injEq] at put
          subst put; exact safe)
        fun v ne nl => by rw [agree v]; exact unsat v ⟨ne, nl⟩
      rw [run] at this
      cases b <;> simp_all [boolAtom]
  · have shape : x = .atom "bdd_top" ∨ x = .atom "bdd_bot" := by
      rcases wx.shape with h | h | ⟨k, a, c, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        obtain ⟨k', a', c', e, -, hc⟩ := Bdd.leaf_iff.mp wx
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
        subst e₂ e₃
        have nt : ¬(k = 46675407 ∧ a = .atom "term" ∧ c = .atom "term") := fun ⟨e, e₁, e₂⟩ => by
          subst e e₁ e₂; exact top rfl
        rw [nl_lh_leaf (ef.shape hc) nt] at one
        omega
      · exfalso
        obtain ⟨-, okl, -⟩ := Bdd.node_iff.mp wx
        obtain ⟨k', a', c', rfl, ha', -⟩ := okl
        rw [nl_lh_node (ef.shape ha')] at one
        omega
    rcases shape with rfl | rfl
    · have : b = Bool.false := by
        cases b
        · rfl
        · exfalso
          have fl := nl_list_sound lelemOk lelemDiff flatSem tailF (m := K + 4) (by omega) (Bdd.top (ok := LLit LElem))
            S fresh (nl_safeF_put hS _ (by simp) "list") (by simpa [boolAtom] using hb (K + 4) (by omega))
            ⟨[.bit 0], .bit 0⟩ (by simp) (by simp [tlF])
          simp at fl
      subst this
      simp only [Bool.false_eq_true, false_iff]
      intro all
      have := all _ v₀
      simp at this
    · have := list_empty_unsat (D (K + 2)) (Bdd.bot (ok := LLit E)) (fun _ _ => by simp) S
      rw [run] at this
      have : b = Bool.true := by cases b <;> simp_all [boolAtom]
      subst this
      simp

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! List fields of element types: plain unions, intersections, and differences on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- List fields: ordered BDDs of list literals of element types, top literals included. -/
abbrev LF (E : Term → Prop) (x : Term) : Prop := Bdd (LLit E) x

/-- The lists of values of a list field. -/
noncomputable def dL (E : Term → Prop) (den : Term → V → Prop) (x : Term) (v : LV V) : Bool := eval (valL E den v) x

theorem nl_top_val (ef : EF nd E V den tl K) (k : Int) (v : LV V) :
    valL E den v (.tuple #[.integer k, .atom "term", .atom "term"]) = Bool.true :=
  (valL_iff ef.semR ⟨k, _, _, rfl, ef.term, ef.term⟩).mpr
    (llitSem_iff.mpr ⟨fun x _ => ef.den_term x, ef.den_term _⟩)

theorem nl_denL (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (v : LV V) :
    denL x (valL E den v) = dL E den x v := by
  unfold denL dL
  cases h : isListTop x
  · rfl
  · obtain ⟨k, rfl⟩ := (listTop_iff x).mp h
    obtain ⟨k, rfl⟩ := leaf_int wx
    rw [eval_leaf, nl_top_val ef]; rfl

/-- List fields that compare equal hold the same lists. -/
theorem nl_dL_resp {x x' : Term} (wx : LF E x) (e : Term.compare (Term.fuel x x') x x' = .eq) (v : LV V) :
    dL E den x v = dL E den x' v :=
  eval_congr_cmp wx (valL_resp v) e

theorem nl_listVal_exists (ef : EF nd E V den tl K) : ∃ v : LV V, ListVal tl v := by
  obtain ⟨x₀⟩ := ef.inhabited
  obtain ⟨y₀, hy₀⟩ := ef.tl_witness
  exact ⟨⟨[x₀], y₀⟩, by simp, hy₀⟩

/-- The literal of a list leaf, as a height. -/
def litH : Term → Nat
  | .tuple ⟨[_, a, b]⟩ => max (lh a) (lh b) + 1
  | _ => 0

theorem litH_eq (k a b : Term) : litH (.tuple #[k, a, b]) = max (lh a) (lh b) + 1 := rfl

theorem lh_le_litH (k x y : Term) : lh (.tuple #[k, x, y]) ≤ litH (.tuple #[k, x, y]) := by
  rw [litH_eq]
  by_cases ho : x = .atom "open" ∧ y = .nil
  · obtain ⟨rfl, rfl⟩ := ho
    rw [show lh (.tuple #[k, .atom "open", .nil]) = 0 from lh_leaf_top k]; omega
  by_cases ht : k = .integer 46675407 ∧ x = .atom "term" ∧ y = .atom "term"
  · obtain ⟨rfl, rfl, rfl⟩ := ht
    rw [show lh (.tuple #[.integer 46675407, .atom "term", .atom "term"]) = 0 from lh_leaf_list]; omega
  by_cases hr : ∃ r a, k = .reference r ∧ x = .map a
  · obtain ⟨r, a, rfl, rfl⟩ := hr
    rw [show (#[.reference r, .map a, y] : Array Term) = ⟨[.reference r, .map a, y]⟩ from rfl, lh_node_term]
    omega
  by_cases hn : NodeLit k x y
  · obtain ⟨rfl, r, a, b, rfl⟩ := hn
    rw [show (#[k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)] : Array Term) =
      ⟨[k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩ from rfl, lh_nodeLit]
    simp only [lh]; omega
  · rw [show lh (.tuple #[k, x, y]) = max (lh x) (lh y) + 1 from lh_leaf k x y ho ht hn hr]; exact Nat.le_refl _

/-- BDDs whose literals are below a height are below it, when that height covers the top and empty BDDs. -/
theorem nl_lh_le {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    ∀ M, (r = .atom "bdd_top" ∨ r = .atom "bdd_bot" → 1 ≤ M) → (∀ t, ok t → litH t ≤ M) → lh r ≤ M := by
  refine Bdd.induction (P := fun ok r => ∀ M, (r = .atom "bdd_top" ∨ r = .atom "bdd_bot" → 1 ≤ M) →
    (∀ t, ok t → litH t ≤ M) → lh r ≤ M) ?_ ?_ ?_ ?_ ok r wr
  · intro _ M top _; simp [lh]; exact top (Or.inl rfl)
  · intro _ M top _; simp [lh]; exact top (Or.inr rfl)
  · intro ok k x y okl M _ h
    exact Nat.le_trans (lh_le_litH _ _ _) (h _ okl)
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id M _ hM
    obtain ⟨k, a, b, rfl⟩ := isLeaf
    have hl := hM _ okl
    rw [litH_eq] at hl
    have below : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → litH t ≤ M := fun t ht => hM t ht.1
    have one : ∀ z : Term, z = .atom "bdd_top" ∨ z = .atom "bdd_bot" → 1 ≤ M := fun _ _ => by omega
    have := ic M (one c) below
    have := iu M (one u) below
    have := id M (one d) below
    refine Nat.le_trans nl_lh_node_le ?_
    omega

/-- The literals of a list field are below its height, and the top list leaf is at height one. -/
theorem nl_lit_le (ef : EF nd E V den tl K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) :
    (∀ t, ok t → LLit E t) → ∀ M, lh r ≤ M →
      (r = .tuple #[.integer 46675407, .atom "term", .atom "term"] → 1 ≤ M) →
      Bdd (fun t => ok t ∧ litH t ≤ M) r := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → LLit E t) → ∀ M, lh r ≤ M →
      (r = .tuple #[.integer 46675407, .atom "term", .atom "term"] → 1 ≤ M) →
      Bdd (fun t => ok t ∧ litH t ≤ M) r) ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ _ _ _; exact Bdd.top
  · intro _ _ _ _ _; exact Bdd.bot
  · intro ok k x y okl lits M le top
    refine Bdd.leaf_iff.mpr ⟨okl, ?_⟩
    obtain ⟨k', a, b, e, ha, hb⟩ := lits _ okl
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    rw [litH_eq]
    by_cases t : k = 46675407 ∧ x = .atom "term" ∧ y = .atom "term"
    · obtain ⟨rfl, rfl, rfl⟩ := t
      have := top rfl
      simp [lh]; omega
    · rw [nl_lh_leaf (ef.shape hb) t] at le; exact le
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits M le _
    obtain ⟨k, a, b, rfl⟩ := isLeaf
    obtain ⟨k₀, a₀, b₀, e₀, ha₀, -⟩ := lits _ okl
    obtain ⟨-, e₂, -⟩ := tuple3_inj e₀
    subst e₂
    rw [nl_lh_node (ef.shape ha₀)] at le
    have lits' : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → LLit E t := fun t ht => lits t ht.1
    have lift : ∀ x, (fun t => Above ok (.tuple #[.integer k, a, b]) t ∧ litH t ≤ M) x →
        Above (fun t => ok t ∧ litH t ≤ M) (.tuple #[.integer k, a, b]) x :=
      fun x hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
    refine Bdd.node_iff.mpr ⟨⟨k, a, b, rfl⟩, ⟨okl, by rw [litH_eq]; omega⟩,
      (ic lits' M (by omega) fun _ => by omega).mono lift, (iu lits' M (by omega) fun _ => by omega).mono lift,
      (id lits' M (by omega) fun _ => by omega).mono lift⟩

/-! Clauses of the plain list operations. -/

abbrev NoTopL (x : Term) : Prop := ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"]

theorem nl_union_eq {x y : Term} (nx : NoTopL x) (ny : NoTopL y) :
    Elixir.Module.Types.Descr.«list_union/2» x y = Elixir.Module.Types.Descr.«bdd_union/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_union/2»
  split
  · exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · rfl

theorem nl_inter_eq {x y : Term} (nx : NoTopL x) (ny : NoTopL y) :
    Elixir.Module.Types.Descr.«list_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_intersection/2»
  split
  · exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · rfl

theorem nl_diff_eq {x y : Term} (nx : NoTopL x) :
    Elixir.Module.Types.Descr.«list_difference/2» x y = Elixir.Module.Types.Descr.«bdd_difference/2» x y := by
  unfold Elixir.Module.Types.Descr.«list_difference/2»
  split
  · exact (nx _ rfl).elim
  · exact (nx _ rfl).elim
  · rfl

theorem nl_diff_top_eq {k y : Term} (ny : NoTopL y) :
    Elixir.Module.Types.Descr.«list_difference/2» (.tuple #[k, .atom "term", .atom "term"]) y =
      Elixir.Module.Types.Descr.«bdd_negation/1» y := by
  unfold Elixir.Module.Types.Descr.«list_difference/2»
  split
  · exact (ny _ rfl).elim
  · rfl
  · rename_i h₁ h₂; exact (h₁ _ rfl).elim

theorem nl_top_dL (ef : EF nd E V den tl K) {k : Term} (w : LF E (.tuple #[k, .atom "term", .atom "term"])) (v : LV V) :
    dL E den (.tuple #[k, .atom "term", .atom "term"]) v = Bool.true := by
  obtain ⟨k, rfl⟩ := leaf_int w
  rw [dL, eval_leaf, nl_top_val ef]

/-- Literals of list fields that are not a top leaf are below their height. -/
theorem nl_lits_le (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (nx : NoTopL x) {M : Nat} (le : lh x ≤ M) :
    Bdd (fun t => LLit E t ∧ litH t ≤ M) x :=
  nl_lit_le ef wx (fun _ h => h) M le fun e => absurd e (nx _)

/-- List fields other than top list leaves have a height. -/
theorem nl_lh_pos (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (nx : NoTopL x) : 1 ≤ lh x := by
  refine Classical.byContradiction fun h0' => ?_
  have h0 : lh x = 0 := by omega
  rcases wx.shape with h | h | ⟨k, a, c, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · subst h; simp [lh] at h0
  · subst h; simp [lh] at h0
  · exfalso
    obtain ⟨k', a', c', e, -, hc⟩ := Bdd.leaf_iff.mp wx
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    subst e₂ e₃
    have nt : ¬(k = 46675407 ∧ a = .atom "term" ∧ c = .atom "term") := fun ⟨_, e₁, e₂⟩ => by
      subst e₁ e₂; exact nx _ rfl
    rw [nl_lh_leaf (ef.shape hc) nt] at h0
    omega
  · exfalso
    obtain ⟨-, okl, -⟩ := Bdd.node_iff.mp wx
    obtain ⟨k', a', c', rfl, ha', -⟩ := okl
    rw [nl_lh_node (ef.shape ha')] at h0
    omega

theorem nl_dL_bot (v : LV V) : dL E den (.atom "bdd_bot") v = Bool.false := by simp [dL]

/-- Plain unions of list fields hold the lists of either. -/
theorem nl_bare_union (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_union/3» d (.atom "list") x y = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v || dL E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    refine ⟨_, fun d => by simp [Elixir.Module.Types.Descr.«bare_union/3», Elixir.Module.Types.Descr.«list_union/2»],
      wx, fun v => by rw [nl_top_dL ef wx]; rfl, Nat.le_max_left _ _⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    have nx : NoTopL x := fun k e => tx ⟨k, e⟩
    refine ⟨_, fun d => ?_, wy, fun v => by rw [nl_top_dL ef wy]; simp, Nat.le_max_right _ _⟩
    simp only [Elixir.Module.Types.Descr.«bare_union/3»]
    unfold Elixir.Module.Types.Descr.«list_union/2»
    split
    · exact (nx _ rfl).elim
    · rename_i heq; obtain ⟨rfl, -, -⟩ := tuple3_inj heq; rfl
    · rename_i h; exact (h _ rfl).elim
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  have ny : NoTopL y := fun k e => ty ⟨k, e⟩
  obtain ⟨r, run, keep, sem⟩ := union_ok wx wy
  refine ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_union/3»]; rw [nl_union_eq nx ny, run],
    keep _ wx wy, fun v => sem _ (valL_resp v), ?_⟩
  have := nl_lh_pos ef wx nx
  exact nl_lh_le (keep _ (nl_lits_le ef wx nx (Nat.le_max_left _ _)) (nl_lits_le ef wy ny (Nat.le_max_right _ _)))
    _ (fun _ => by omega) fun t h => h.2

/-- Plain intersections of list fields hold the lists of both. -/
theorem nl_bare_inter (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom "list") x y = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v && dL E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    refine ⟨y, fun d => by
      simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«list_intersection/2»],
      wy, fun v => by rw [nl_top_dL ef wx]; rfl, Nat.le_max_right _ _⟩
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    refine ⟨x, fun d => ?_, wx, fun v => by rw [nl_top_dL ef wy]; simp, Nat.le_max_left _ _⟩
    simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]
    unfold Elixir.Module.Types.Descr.«list_intersection/2»
    split
    · exact (nx _ rfl).elim
    · rfl
    · rename_i h; exact (h _ rfl).elim
  have ny : NoTopL y := fun k e => ty ⟨k, e⟩
  obtain ⟨r, run, keep, sem⟩ := inter_ok wx wy
  refine ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_intersection/3»]; rw [nl_inter_eq nx ny, run],
    keep _ wx wy, fun v => sem _ (valL_resp v), ?_⟩
  have := nl_lh_pos ef wx nx
  exact nl_lh_le (keep _ (nl_lits_le ef wx nx (Nat.le_max_left _ _)) (nl_lits_le ef wy ny (Nat.le_max_right _ _)))
    _ (fun _ => by omega) fun t h => h.2

/-- Plain differences of list fields hold the lists of the first and not the second. Their non-empty results are
below the inputs' height. -/
theorem nl_bare_diff (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom "list") x y = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v && !dL E den y v)) ∧
      (r ≠ .atom "bdd_bot" → lh r ≤ max (lh x) (lh y)) := by
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
    · obtain ⟨k', rfl⟩ := ty
      exact ⟨.atom "bdd_bot", fun d => by
        simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»],
        Bdd.bot, fun v => by rw [nl_top_dL ef wx, nl_top_dL ef wy]; rfl, fun nb => absurd rfl nb⟩
    have ny : NoTopL y := fun k e => ty ⟨k, e⟩
    obtain ⟨r, run, keep, sem⟩ := neg_ok wy
    have one := nl_lh_pos ef wy ny
    exact ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_difference/3»]; rw [nl_diff_top_eq ny, run],
      keep _ wy, fun v => by rw [nl_top_dL ef wx, dL, sem _ (valL_resp v)]; rfl,
      fun _ => Nat.le_trans (nl_lh_le (keep _ (nl_lits_le ef wy ny (Nat.le_refl _))) _ (fun _ => one)
        fun t h => h.2) (Nat.le_max_right _ _)⟩
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  obtain ⟨r, run, keep, sem⟩ := diff_ok wx wy
  have one := nl_lh_pos ef wx nx
  exact ⟨r, fun d => by simp only [Elixir.Module.Types.Descr.«bare_difference/3»]; rw [nl_diff_eq nx, run],
    keep _ wx wy, fun v => sem _ (valL_resp v), fun _ => nl_lh_le (keep _ (nl_lits_le ef wx nx (Nat.le_max_left (lh x) (lh y)))
      (nl_lit_le ef wy (fun _ h => h) _ (Nat.le_max_right _ _) fun _ => by omega)) _ (fun _ => by omega) fun t h => h.2⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized unions and intersections of list fields on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `empty?/1` decides the emptiness of element types. -/
theorem nl_empty1 (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {t : Term} (ht : E t) :
    ∃ b, Elixir.Module.Types.Descr.«empty?/1» (D m) t = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ v, ¬den t v) := by
  obtain ⟨b, run, exact⟩ := ef.empty [] ht
  have iff := exact (lh t + 1) (Nat.lt_succ_self _) (safeN_nil _)
  refine ⟨b, ?_, iff⟩
  rcases ef.static ht with rfl | ⟨X, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩
  · have : b = Bool.false := by
      cases b
      · rfl
      · exact absurd (ef.den_term (Classical.choice ef.inhabited)) (iff.mp rfl _)
    subst this
    rfl
  · simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm
  · simpa [Elixir.Module.Types.Descr.«empty?/1»] using run m hm

theorem nl_leaf_new (ef : EF nd E V den tl K) {a b : Term} (ha : E a) (hb : E b) :
    ∃ k : Int, Elixir.Module.Types.Descr.«bdd_leaf_new/2» a b = .ok (.tuple #[.integer k, a, b]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons a b)
  rcases ef.static ha with rfl | ⟨A, rfl, -⟩ | ⟨r₀, st₀, g₀, rfl⟩ <;>
    rcases ef.static hb with rfl | ⟨B, rfl, -⟩ | ⟨r₁, st₁, g₁, rfl⟩
  all_goals
    exact ⟨hash, by
      simp [Elixir.Module.Types.Descr.«bdd_leaf_new/2», Elixir.Module.Types.Descr.«bdd_leaf_key/2», hrun,
        Erlang.erlang.«is_list/1»]⟩

theorem nl_llit_val (ef : EF nd E V den tl K) {k : Int} {a b : Term} (ha : E a) (hb : E b) (v : LV V) :
    valL E den v (.tuple #[.integer k, a, b]) = Bool.true ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last :=
  (valL_iff ef.semR ⟨k, a, b, rfl, ha, hb⟩).trans llitSem_iff

/-- Optimized intersections of list literals hold the lists of both. -/
theorem nl_leaf_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {k₁ k₂ : Int} {a₁ b₁ a₂ b₂ : Term}
    (ha₁ : E a₁) (hb₁ : E b₁) (ha₂ : E a₂) (hb₂ : E b₂) (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3» (D m) (.tuple #[.integer k₁, a₁, b₁])
        (.tuple #[.integer k₂, a₂, b₂]) (.map S) = .ok r ∧ LF E r ∧
      ∀ v : LV V, v.xs ≠ [] → dL E den r v =
        (dL E den (.tuple #[.integer k₁, a₁, b₁]) v && dL E den (.tuple #[.integer k₂, a₂, b₂]) v) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  obtain ⟨a, ea, ra, sa⟩ := ef.opt_inter S ha₁ ha₂ hn
  obtain ⟨b, eb, rb, sb⟩ := ef.opt_inter S hb₁ hb₂ hn
  obtain ⟨xa, runa, iffa⟩ := nl_empty1 ef (m := n + 1) (by omega) ea
  obtain ⟨xb, runb, iffb⟩ := nl_empty1 ef (m := n + 1) (by omega) eb
  obtain ⟨k, leaf⟩ := nl_leaf_new ef ea eb
  have both : ∀ v : LV V, (dL E den (.tuple #[.integer k₁, a₁, b₁]) v && dL E den (.tuple #[.integer k₂, a₂, b₂]) v) =
      Bool.true ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last := by
    intro v
    simp only [dL, eval_leaf, Bool.and_eq_true, nl_llit_val ef ha₁ hb₁, nl_llit_val ef ha₂ hb₂, sa, sb]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩; exact ⟨fun x mx => ⟨h₁ x mx, h₃ x mx⟩, h₂, h₄⟩
    · rintro ⟨h₁, h₂, h₄⟩; exact ⟨⟨fun x mx => (h₁ x mx).1, h₂⟩, fun x mx => (h₁ x mx).2, h₄⟩
  have unfold : Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3» (D (n + 1)) (.tuple #[.integer k₁, a₁, b₁])
      (.tuple #[.integer k₂, a₂, b₂]) (.map S) =
      if xa then .ok (.atom "bdd_bot") else if xb then .ok (.atom "bdd_bot")
      else .ok (.tuple #[.integer k, a, b]) := by
    unfold Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3»
    have fa : Lynx.Dispatcher.pure (D (n + 1))
        (.function false "Elixir.Module.Types.Descr" "-opt_list_leaf_intersection/3-fun-0-" 2 #[.map S]) #[a₁, a₂] = .ok a := by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_list_leaf_intersection/3-fun-0-/2».pure]
      simpa [Elixir.Module.Types.Descr.«-opt_list_leaf_intersection/3-fun-0-/3»] using ra
    have fb : Lynx.Dispatcher.pure (D (n + 1))
        (.function false "Elixir.Module.Types.Descr" "-opt_list_leaf_intersection/3-fun-0-" 2 #[.map S]) #[b₁, b₂] = .ok b := by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_list_leaf_intersection/3-fun-0-/2».pure]
      simpa [Elixir.Module.Types.Descr.«-opt_list_leaf_intersection/3-fun-0-/3»] using rb
    cases xa <;> cases xb <;>
      simp [Elixir.Module.Types.Descr.«non_empty_intersection!/3», fa, fb, runa, runb, isMember,
        boolAtom, Lynx.Except.tryWith, Lynx.Exception.classTerm, Lynx.Exception.reason, leaf]
  rw [unfold]
  cases xa
  · cases xb
    · refine ⟨_, rfl, Bdd.leaf_iff.mpr ⟨k, a, b, rfl, ea, eb⟩, fun v _ => ?_⟩
      have e : dL E den (.tuple #[.integer k, a, b]) v = Bool.true ↔ (∀ x ∈ v.xs, den a x) ∧ den b v.last := by
        rw [dL, eval_leaf]; exact nl_llit_val ef ea eb v
      exact Bool.eq_iff_iff.mpr (e.trans (both v).symm)
    · refine ⟨_, rfl, Bdd.bot, fun v _ => ?_⟩
      refine Bool.eq_iff_iff.mpr ⟨fun h => by simp [dL] at h, fun h => ?_⟩
      exact absurd ((both v).mp h).2 ((iffb.mp rfl) v.last)
  · refine ⟨_, rfl, Bdd.bot, fun v ne => ?_⟩
    refine Bool.eq_iff_iff.mpr ⟨fun h => by simp [dL] at h, fun h => ?_⟩
    obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil v.xs ne
    exact absurd (((both v).mp h).1 x mx) ((iffa.mp rfl) x)

theorem nl_oi_top_l {d : Dispatcher} {k y S : Term} :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k, .atom "term", .atom "term"]) y S = .ok y := by
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»; rfl

theorem nl_oi_top_r {d : Dispatcher} {x k S : Term} (nx : NoTopL x) :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d x (.tuple #[k, .atom "term", .atom "term"]) S = .ok x := by
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
  split
  all_goals first
    | rfl
    | exact (nx _ rfl).elim
    | (rename_i h; exact (h _ rfl).elim)
    | (rename_i h _; exact (h _ rfl).elim)
    | (exfalso; simp_all)

theorem nl_oi_plain {d : Dispatcher} {x y S : Term} (nx : NoTopL x) (ny : NoTopL y)
    (nl : ¬((∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b])) :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d x y S = Elixir.Module.Types.Descr.«list_intersection/2» x y := by
  have ne : ∀ a b c, x = .tuple #[a, b, c] → compareExact (fuel y x) y x ≠ .eq := by
    rintro a b c rfl e
    obtain ⟨_, _, _, rfl, -⟩ := exact_tuple3 e
    exact nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
  split
  · exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · simp only [leaf_guard]
    split
    · rw [ite_eq_right (ne _ _ _ rfl)]
      split
      · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
      · rfl
    · split
      · exact (nl ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩).elim
      · rfl

/-- Exactly equal list leaves intersect to the first. -/
theorem nl_oi_same {d : Dispatcher} {S k a b y : Term} (nx : NoTopL (.tuple #[k, a, b])) (ny : NoTopL y)
    (e : compareExact (fuel y (.tuple #[k, a, b])) y (.tuple #[k, a, b]) = .eq) :
    Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k, a, b]) y S = .ok (.tuple #[k, a, b]) := by
  unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
  split
  · rename_i heq; obtain ⟨-, rfl, rfl⟩ := tuple3_eq heq; exact (nx _ rfl).elim
  · exact (ny _ rfl).elim
  · simp only [leaf_guard]
    rw [ite_eq_left (by simpa using e)]
    rfl

theorem nl_oi_leaves {d : Dispatcher} {S k₁ a₁ b₁ k₂ a₂ b₂ : Term}
    (nx : NoTopL (.tuple #[k₁, a₁, b₁])) (ny : NoTopL (.tuple #[k₂, a₂, b₂]))
    (ne : compareExact (fuel (.tuple #[k₂, a₂, b₂]) (.tuple #[k₁, a₁, b₁])) (.tuple #[k₂, a₂, b₂]) (.tuple #[k₁, a₁, b₁]) ≠ .eq) :
    (Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_intersection") (.tuple #[k₁, a₁, b₁])
        (.tuple #[k₂, a₂, b₂]) = .ok (.atom "seen") →
      Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k₁, a₁, b₁]) (.tuple #[k₂, a₂, b₂]) S =
        Elixir.Module.Types.Descr.«list_intersection/2» (.tuple #[k₁, a₁, b₁]) (.tuple #[k₂, a₂, b₂])) ∧
    (∀ S', Elixir.Module.Types.Descr.«opt_bdd_seen/4» S (.atom "list_intersection") (.tuple #[k₁, a₁, b₁])
        (.tuple #[k₂, a₂, b₂]) = .ok (.tuple #[.atom "ok", S']) →
      Elixir.Module.Types.Descr.«opt_list_intersection/3» d (.tuple #[k₁, a₁, b₁]) (.tuple #[k₂, a₂, b₂]) S =
        Elixir.Module.Types.Descr.«opt_list_leaf_intersection/3» d (.tuple #[k₁, a₁, b₁])
          (.tuple #[k₂, a₂, b₂]) S') := by
  constructor <;> intros <;>
  · unfold Elixir.Module.Types.Descr.«opt_list_intersection/3»
    split
    all_goals try (simp only [leaf_guard]; rw [ite_eq_right (by simpa using ne)])
    all_goals first
      | (exfalso; rename_i heq; obtain ⟨-, rfl, rfl⟩ := heq; first | exact nx _ rfl | exact ny _ rfl)
      | (exfalso; rename_i heq h; obtain ⟨-, rfl, rfl⟩ := heq; first | exact nx _ rfl | exact ny _ rfl)
      | (exfalso; rename_i h heq; obtain ⟨-, rfl, rfl⟩ := heq; first | exact nx _ rfl | exact ny _ rfl)
      | (next h => exact (h _ _ _ _ _ _ rfl rfl).elim)
      | simp_all

/-- Optimized intersections of list fields hold the lists of both. -/
theorem nl_opt_inter (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {x y : Term} (wx : LF E x) (wy : LF E y)
    (S : List (Term × Term)) :
    ∃ r, Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom "list") x y (.map S) = .ok r ∧ LF E r ∧
      ∀ v, ListVal tl v → dL E den r v = (dL E den x v && dL E den y v) := by
  simp only [Elixir.Module.Types.Descr.«opt_intersection/4»]
  have plain : Elixir.Module.Types.Descr.«opt_list_intersection/3» (D m) x y (.map S) =
      Elixir.Module.Types.Descr.«list_intersection/2» x y → ∃ r,
      Elixir.Module.Types.Descr.«opt_list_intersection/3» (D m) x y (.map S) = .ok r ∧ LF E r ∧
      ∀ v, ListVal tl v → dL E den r v = (dL E den x v && dL E den y v) := by
    intro e
    obtain ⟨r, run, wr, sem, -⟩ := nl_bare_inter ef wx wy
    exact ⟨r, by rw [e]; simpa [Elixir.Module.Types.Descr.«bare_intersection/3»] using run (D m), wr,
      fun v _ => sem v⟩
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    exact ⟨y, nl_oi_top_l, wy, fun v _ => by rw [nl_top_dL ef wx]; rfl⟩
  have nx : NoTopL x := fun k e => tx ⟨k, e⟩
  by_cases ty : ∃ k, y = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := ty
    exact ⟨x, nl_oi_top_r nx, wx, fun v _ => by rw [nl_top_dL ef wy]; simp⟩
  have ny : NoTopL y := fun k e => ty ⟨k, e⟩
  by_cases leaves : (∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b]
  · obtain ⟨⟨k₁, a₁, b₁, rfl⟩, ⟨k₂, a₂, b₂, rfl⟩⟩ := leaves
    obtain ⟨k₁, rfl⟩ := leaf_int wx
    obtain ⟨k₂, rfl⟩ := leaf_int wy
    obtain ⟨k₁', a₁', b₁', e₁, ha₁, hb₁⟩ := Bdd.leaf_iff.mp wx
    obtain ⟨-, e₁₂, e₁₃⟩ := tuple3_inj e₁
    subst e₁₂ e₁₃
    obtain ⟨k₂', a₂', b₂', e₂, ha₂, hb₂⟩ := Bdd.leaf_iff.mp wy
    obtain ⟨-, e₂₂, e₂₃⟩ := tuple3_inj e₂
    subst e₂₂ e₂₃
    by_cases same : compareExact (fuel (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁])) (.tuple #[.integer k₂, a₂, b₂]) (.tuple #[.integer k₁, a₁, b₁]) = .eq
    · exact ⟨_, nl_oi_same nx ny same, wx, fun v _ => by
        simp only [dL, eval_exact wx (valL_resp v) same, Bool.and_self]⟩
    rcases opt_bdd_seen_map S (.atom "list_intersection") (.tuple #[.integer k₁, a₁, b₁])
      (.tuple #[.integer k₂, a₂, b₂]) with seen | ⟨S', ok⟩
    · exact plain ((nl_oi_leaves nx ny same).1 seen)
    · obtain ⟨r, run, wr, sem⟩ := nl_leaf_inter ef hm ha₁ hb₁ ha₂ hb₂ S'
      exact ⟨r, by rw [(nl_oi_leaves nx ny same).2 _ ok, run], wr, fun v lv => sem v lv.1⟩
  · exact plain (nl_oi_plain nx ny leaves)

/-- Optimized unions of list fields are plain unions. -/
theorem nl_opt_union (ef : EF nd E V den tl K) {x y : Term} (wx : LF E x) (wy : LF E y) :
    ∃ r, (∀ d S, Elixir.Module.Types.Descr.«opt_union/4» d (.atom "list") x y S = .ok r) ∧ LF E r ∧
      (∀ v, dL E den r v = (dL E den x v || dL E den y v)) ∧ lh r ≤ max (lh x) (lh y) := by
  obtain ⟨r, run, wr, sem, le⟩ := nl_bare_union ef wx wy
  refine ⟨r, fun d S => ?_, wr, sem, le⟩
  simpa [Elixir.Module.Types.Descr.«opt_union/4», Elixir.Module.Types.Descr.«bare_union/3»] using run d

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized differences of list fields on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Valuations of list literals induced by lists of values. -/
def ValLG (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (ρ : Term → Bool) : Prop :=
  ∃ v, ListVal tl v ∧ ρ = valL E den v

theorem valLG_resp : ∀ ρ, ValLG E den tl ρ → Resp ρ := fun _ ⟨v, _, e⟩ => e ▸ valL_resp v

/-- `opt_list_leaf_difference/3` compares list literals soundly. -/
theorem nl_list_cmp (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a₁ a₂ type : Term) (h₁ : LLit E a₁)
    (h₂ : LLit E a₂) :
    ∃ res, (D (n + 1)).pure (.function false "Elixir.Module.Types.Descr" "opt_list_leaf_difference" 3 #[])
      #[a₁, a₂, type] = .ok res ∧ CmpOk (ValLG E den tl) (LLit E) a₁ a₂ type res := by
  obtain ⟨k₁, l₁, t₁, rfl, hl₁, ht₁⟩ := h₁
  obtain ⟨k₂, l₂, t₂, rfl, hl₂, ht₂⟩ := h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:opt_list_leaf_difference/3».pure]
  obtain ⟨b₁, hb₁, s₁⟩ := ef.disj hl₁ hl₂
  obtain ⟨b₂, hb₂, s₂⟩ := ef.disj ht₁ ht₂
  have r₁ := hb₁ n hn
  have r₂ := hb₂ n hn
  cases b₁
  · cases b₂
    · refine ⟨.atom "none", ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_list_leaf_difference/3».eq_def]
      simp [r₁, r₂, boolAtom, Lynx.Except.orElse, isMember]
    · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨v, lv, e⟩ => ?_⟩⟩
      · rw [Elixir.Module.Types.Descr.«opt_list_leaf_difference/3».eq_def]
        simp [r₁, r₂, boolAtom, Lynx.Except.orElse, isMember]
      · subst e
        apply Bool.eq_false_iff.mpr
        intro h
        rw [Bool.and_eq_true, nl_llit_val ef hl₁ ht₁, nl_llit_val ef hl₂ ht₂] at h
        exact s₂ rfl _ h.1.2 h.2.2
  · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨v, lv, e⟩ => ?_⟩⟩
    · rw [Elixir.Module.Types.Descr.«opt_list_leaf_difference/3».eq_def]
      simp [r₁, boolAtom, Lynx.Except.orElse, isMember]
    · subst e
      apply Bool.eq_false_iff.mpr
      intro h
      rw [Bool.and_eq_true, nl_llit_val ef hl₁ ht₁, nl_llit_val ef hl₂ ht₂] at h
      obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil v.xs lv.1
      exact s₁ rfl x (h.1.1 x mx) (h.2.1 x mx)

/-- Optimized differences of list fields hold the lists of the first and not the second. -/
theorem nl_opt_diff (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {x y : Term} (wx : LF E x) (wy : LF E y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom "list") x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  simp only [Elixir.Module.Types.Descr.«opt_difference/4»]
  have spec := fun a₁ a₂ type (_ : TypeOk type) (h₁ : LLit E a₁) (h₂ : LLit E a₂) =>
    nl_list_cmp ef hn a₁ a₂ type h₁ h₂
  have viaDiff3 : Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) =
      Elixir.Module.Types.Descr.«bdd_difference/3» (D (n + 1)) x y optListCmp → ∃ w,
      Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
    intro e
    obtain ⟨r, hr, okr, semr⟩ := diff3_ok valLG_resp spec _ y wy (fun _ h => h) x wx
    exact ⟨r, by rw [e, hr], okr, fun v lv => semr _ ⟨v, lv, rfl⟩⟩
  have viaBare : Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) =
      Elixir.Module.Types.Descr.«list_difference/2» x y → ∃ w,
      Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
    intro e
    obtain ⟨w, run, ww, sem, -⟩ := nl_bare_diff ef wx wy
    exact ⟨w, by rw [e]; simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run (D (n + 1)), ww,
      fun v _ => sem v⟩
  have same : ∀ {k a b : Term}, x = .tuple #[k, a, b] → compareExact (fuel y x) y x = .eq → ∃ w,
      Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
    rintro k a b rfl e
    refine ⟨_, opt_list_same e, Bdd.bot, fun v _ => ?_⟩
    simp only [dL, eval_exact wx (valL_resp v) e, eval_bot, Bool.and_not_self]
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    by_cases e : compareExact (fuel y (.tuple #[k, .atom "term", .atom "term"])) y (.tuple #[k, .atom "term", .atom "term"]) = .eq
    · exact same rfl e
    obtain ⟨k', rfl⟩ := leaf_int wx
    obtain ⟨r, hr, okr, semr⟩ := neg_ok wy
    refine ⟨r, by rw [opt_list_top, ite_eq_right e, hr], okr _ wy, fun v _ => ?_⟩
    simp only [dL, semr _ (valL_resp v), eval_leaf, nl_top_val ef, Bool.true_and]
  have nt : ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"] := fun k e => tx ⟨k, e⟩
  by_cases leaves : (∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b]
  rotate_left
  · exact viaDiff3 (opt_list_other nt leaves)
  obtain ⟨⟨k₁, l₁, t₁, rfl⟩, ⟨k₂, l₂, t₂, rfl⟩⟩ := leaves
  obtain ⟨k₁, rfl⟩ := leaf_int wx
  obtain ⟨k₂, rfl⟩ := leaf_int wy
  obtain ⟨k₁', l₁', t₁', e₁, hl₁, ht₁⟩ := Bdd.leaf_iff.mp wx
  obtain ⟨-, e₁₂, e₁₃⟩ := tuple3_inj e₁
  subst e₁₂ e₁₃
  obtain ⟨k₂', l₂', t₂', e₂, hl₂, ht₂⟩ := Bdd.leaf_iff.mp wy
  obtain ⟨-, e₂₂, e₂₃⟩ := tuple3_inj e₂
  subst e₂₂ e₂₃
  have ntop : ¬(l₁ = .atom "term" ∧ t₁ = .atom "term") := fun ⟨a, b⟩ => nt _ (by rw [a, b])
  by_cases e : compareExact (fuel (.tuple #[.integer k₂, l₂, t₂]) (.tuple #[.integer k₁, l₁, t₁])) (.tuple #[.integer k₂, l₂, t₂]) (.tuple #[.integer k₁, l₁, t₁]) = .eq
  · exact same rfl e
  obtain ⟨c₁, hc₁, sc₁⟩ := ef.sub hl₁ hl₂
  obtain ⟨c₂, hc₂, sc₂⟩ := ef.sub ht₁ ht₂
  have r₁ := hc₁ (n + 1) (by omega)
  have r₂ := hc₂ (n + 1) (by omega)
  obtain ⟨L₁, L₂, L₃, L₄⟩ := opt_list_leaves (d := D (n + 1)) (S := .map S) (k₁ := .integer k₁) (k₂ := .integer k₂)
    (t₂ := t₂) ntop e
  cases c₁
  · exact viaDiff3 (L₁ r₁)
  have sl := sc₁ rfl
  cases c₂
  · rcases opt_bdd_seen_map S (.atom "list_difference") (.tuple #[.integer k₁, l₁, t₁])
        (.tuple #[.integer k₂, l₂, t₂]) with seen | ⟨S', ok⟩
    · exact viaBare (L₃ r₁ r₂ seen)
    obtain ⟨c, hc, run, semc⟩ := ef.opt_diff S' ht₁ ht₂ (show K ≤ n + 1 by omega)
    obtain ⟨k, leaf⟩ := nl_leaf_new ef hl₁ hc
    refine ⟨.tuple #[.integer k, l₁, c], by rw [L₄ _ r₁ r₂ ok, run]; exact leaf,
      Bdd.leaf_iff.mpr ⟨k, l₁, c, rfl, hl₁, hc⟩, fun v lv => ?_⟩
    simp only [dL, eval_leaf]
    apply Bool.eq_iff_iff.mpr
    rw [nl_llit_val ef hl₁ hc, Bool.and_eq_true, nl_llit_val ef hl₁ ht₁, Bool.not_eq_true', Bool.eq_false_iff, Ne,
      nl_llit_val ef hl₂ ht₂, semc]
    constructor
    · rintro ⟨all, last, nlast⟩
      exact ⟨⟨all, last⟩, fun ⟨_, h⟩ => nlast h⟩
    · rintro ⟨⟨all, last⟩, h⟩
      exact ⟨all, last, fun hl => h ⟨fun x mx => sl x (all x mx), hl⟩⟩
  · have st := sc₂ rfl
    refine ⟨.atom "bdd_bot", L₂ r₁ r₂, Bdd.bot, fun v lv => ?_⟩
    simp only [dL, eval_leaf, eval_bot]
    cases h : valL E den v (.tuple #[.integer k₁, l₁, t₁])
    · rfl
    · rw [nl_llit_val ef hl₁ ht₁] at h
      have : valL E den v (.tuple #[.integer k₂, l₂, t₂]) = Bool.true :=
        (nl_llit_val ef hl₂ ht₂ v).mpr ⟨fun x mx => sl x (h.1 x mx), st _ h.2⟩
      rw [this]; rfl

/-- `empty_key?/3` decides exactly whether list fields hold lists of values. -/
theorem nl_empty_key (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
        Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "list") x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ v, ListVal tl v → dL E den x v = Bool.false) := by
  obtain ⟨b, run, exact⟩ := nl_list_empty ef wx S
  exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m hm, exact⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Lists are a structural kind. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Valuations of list literals that lists of values induce. -/
def ValLN (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (ρ : Term → Bool) : Prop :=
  ∃ v, ListVal tl v ∧ ρ = valL E den v

theorem dn_listL (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) {p : Point} {v : LV V} (e : p.2.2 = valL E den v) :
    dn "list" (some x) p = dL E den x v := by
  rw [dn_list, e, nl_denL ef wx]

theorem lf_nz {w : Term} (fw : LF E w) : w ≠ .integer 0 := bdd_ne_zero fw

theorem listKind (ef : EF nd E V den tl K) : KindOk (K + 2) "list" (LF E) (ValLN E den tl) where
  resp := fun _ ⟨v, _, e⟩ => e ▸ valL_resp v
  wit := let ⟨v, hv⟩ := nl_listVal_exists ef; ⟨_, v, hv, rfl⟩
  top := fun t ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> try simp at h
    exact ⟨Bdd.leaf_iff.mpr ⟨_, _, _, rfl, ef.term, ef.term⟩, lh_leaf_list,
      fun p _ => by simp [dn_list, denL, isListTop]⟩
  congr := fun fx fx' e p ⟨v, _, hv⟩ => by
    rw [dn_listL ef fx hv, dn_listL ef fx' hv]
    exact nl_dL_resp fx e v
  union := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := nl_bare_union ef fx fy
    exact ⟨w, fun m _ => run _, fw, fun p ⟨v, _, hv⟩ => by
      rw [dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem], le⟩
  inter := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := nl_bare_inter ef fx fy
    refine ⟨w, fun m _ => run _, fun _ => ⟨fw, le⟩, fun p ⟨v, _, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem]
  diff := fun {x y} fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := nl_bare_diff ef fx fy
    refine ⟨w, fun m _ => run _, fun k => ⟨fw, le (kept_ne_bot k)⟩, fun p ⟨v, _, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem]
  opt_union := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem, -⟩ := nl_opt_union ef fx fy
    exact ⟨w, run _ _, fw, fun p ⟨v, _, hv⟩ => by
      rw [dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem]⟩
  opt_inter := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := nl_opt_inter ef (m := m) (by omega) fx fy S
    refine ⟨w, run, fun _ => fw, fun p ⟨v, lv, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem v lv,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem v lv]
  opt_diff := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := nl_opt_diff ef (m := m) (by omega) fx fy S
    refine ⟨w, run, fun _ => fw, fun p ⟨v, lv, hv⟩ => ?_⟩
    cases k : kept (.atom "list", w)
    · rw [keptO_false k, dn_none, dn_listL ef fx hv, dn_listL ef fy hv, ← sem v lv,
        dropped_bdd (by rw [kept_name]; exact k) (lf_nz fw), nl_dL_bot]
    · rw [keptO_true k, dn_listL ef fw hv, dn_listL ef fx hv, dn_listL ef fy hv, sem v lv]
  empty := fun S fx => by
    obtain ⟨b, run, ex⟩ := nl_empty_key ef fx S
    refine ⟨b, run, fun N hx hS => (ex N hx hS).trans ⟨fun h p ⟨v, lv, hv⟩ => by rw [dn_listL ef fx hv]; exact h v lv,
      fun h v lv => by have := h (0, .nil, valL E den v) ⟨v, lv, rfl⟩; rwa [dn_listL ef fx rfl] at this⟩⟩

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fields of types, over the structural kinds. -/

/-- Fields: non-empty bitmaps and atom types, function fields `Fn`, and the fields of the structural kinds. -/
def FieldC (Fn TF LF MF : Term → Prop) (name : String) (x : Term) : Prop :=
  (name = "bitmap" ∧ BitField x) ∨ (name = "atom" ∧ AtomF x) ∨ (name = "fun" ∧ Fn x) ∨
    (name = "list" ∧ LF x) ∨ (name = "tuple" ∧ TF x) ∨ (name = "map" ∧ MF x)

/-- Points of fields: bitmaps hold bit indices, the structural kinds hold valuations from values, and function
types hold an arity and a valuation `FV` allows. -/
def PtOkC (TV LV MV : (Term → Bool) → Prop) (FV : Term → (Term → Bool) → Prop) (name : String) (p : Point) : Prop :=
  Resp p.2.2 ∧ (name = "bitmap" → p.1 < 8) ∧ (name = "list" → LV p.2.2) ∧ (name = "tuple" → TV p.2.2) ∧
    (name = "map" → MV p.2.2) ∧ (name = "fun" → FV p.2.1 p.2.2)

/-- Function points with any arity and valuation. -/
abbrev FVT : Term → (Term → Bool) → Prop := fun _ _ => True

/-- The three structural kinds. -/
structure Kinds (K : Nat) (TF LF MF : Term → Prop) (TV LV MV : (Term → Bool) → Prop) : Prop where
  t : KindOk K "tuple" TF TV
  l : KindOk K "list" LF LV
  m : KindOk K "map" MF MV

/-- Function fields `Fn`, whose points `FV` allows: function types, closed under plain operations, whose emptiness
is complete on the seen sets `FS` below them, at call depths from `K`. When `H` holds, the plain operations keep
literal heights, and emptiness is decided and sound. -/
structure FunC (K : Nat) (Fn : Term → Prop) (FV : Term → (Term → Bool) → Prop) (FS : List (Term × Term) → Prop)
    (H : Prop) : Prop where
  funF : ∀ {x}, Fn x → FunF x
  union : ∀ {x y}, Fn x → Fn y → ∀ m w, K ≤ m →
    Elixir.Module.Types.Descr.«bare_union/3» (D m) (.atom "fun") x y = .ok w → Fn w ∧ (H → lh w ≤ max (lh x) (lh y))
  inter : ∀ {x y}, Fn x → Fn y → ∀ m w, K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom "fun") x y = .ok w →
    kept (.atom "fun", w) = Bool.true → Fn w ∧ (H → lh w ≤ max (lh x) (lh y))
  diff : ∀ {x y}, Fn x → Fn y → ∀ m w, K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom "fun") x y = .ok w →
    kept (.atom "fun", w) = Bool.true → Fn w ∧ (H → lh w ≤ max (lh x) (lh y))
  empty : ∀ {x} (S : List (Term × Term)) {m}, Fn x → FS S → K ≤ m →
    (∀ N, lh x < N → SafeN N S → (∀ p : Point, Resp p.2.2 → FV p.2.1 p.2.2 → dn "fun" (some x) p = Bool.false) →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "fun") x (.map S) = .ok (.atom "true")) ∧
    (H → ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "fun") x (.map S) = .ok (boolAtom b) ∧
      ∀ N, lh x < N → SafeN N S → b = Bool.true →
        ∀ p : Point, Resp p.2.2 → FV p.2.1 p.2.2 → dn "fun" (some x) p = Bool.false)

theorem lh_int (n : Int) : lh (.integer n) = 0 := by simp [lh]

theorem lh_set {S : List (Term × Term)} (set : Erlang.sets.elements? (.map S) = some S) : lh (.map S) = 0 := by
  refine Nat.le_zero.mp (lh_map_le.mpr fun e' me' => ?_)
  simp only [Erlang.sets.elements?] at set
  split at set
  · rename_i all
    have := List.all_eq_true.mp all e' me'
    match e', this with
    | (_, .nil), _ => simp [lh]
  · cases set

theorem lh_atomF {x : Term} (h : AtomF x) : lh x = 0 := by
  obtain ⟨⟨p, S, rfl, set⟩, -⟩ := h
  show lh (.tuple ⟨[_, _]⟩) = 0
  cases p <;> simp [lh, lh_set set]

theorem lh_bitF {x : Term} (h : BitField x) : lh x = 0 := by
  obtain ⟨b, rfl, -⟩ := h
  exact lh_int _

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

theorem fieldC_cases {name : String} {x : Term} (h : FieldC Fn TF LF MF name x) :
    name = "bitmap" ∨ name = "atom" ∨ name = "fun" ∨ name = "list" ∨ name = "tuple" ∨ name = "map" := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem fieldC_bitmap {x : Term} (h : FieldC Fn TF LF MF "bitmap" x) : BitField x := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_atom {x : Term} (h : FieldC Fn TF LF MF "atom" x) : AtomF x := by
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_fun {x : Term} (h : FieldC Fn TF LF MF "fun" x) : Fn x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_list {x : Term} (h : FieldC Fn TF LF MF "list" x) : LF x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_tuple {x : Term} (h : FieldC Fn TF LF MF "tuple" x) : TF x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ <;> first | exact h | simp at h
theorem fieldC_map {x : Term} (h : FieldC Fn TF LF MF "map" x) : MF x := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> first | exact h | simp at h

/-- Plain unions of fields. -/
theorem fieldC_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m) {name : String}
    {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_union/3» (D m) (.atom name) x y = .ok w ∧ FieldC Fn TF LF MF name w ∧
      (∀ p, PtOkC TV LV MV FV name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
      (H → lh w ≤ max (lh x) (lh y)) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, fw, sem⟩ := bit_union (D m) (fieldC_bitmap fx) (fieldC_bitmap fy)
    exact ⟨w, run, Or.inl ⟨rfl, fw⟩, fun p _ => by simp [dn_bitmap, sem], fun _ => by rw [lh_bitF fw]; omega⟩
  · obtain ⟨w, run, fw, sem⟩ := atom_union_spec (D m) (fieldC_atom fx) (fieldC_atom fy)
    exact ⟨w, run, Or.inr (Or.inl ⟨rfl, fw⟩), fun p _ => by simp [dn_atom, sem], fun _ => by rw [lh_atomF fw]; omega⟩
  · obtain ⟨n, rfl, -⟩ := succ_of_le hm
    obtain ⟨w, run, -, sem⟩ := fun_union_spec n (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fy))
    obtain ⟨fw, le⟩ := fc.union (fieldC_fun fx) (fieldC_fun fy) _ w (by omega) run
    exact ⟨w, run, Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), fun p ok => by simp [dn_fun, sem _ _ ok.1], le⟩
  · obtain ⟨w, run, fw, sem, le⟩ := ks.l.union (fieldC_list fx) (fieldC_list fy)
    exact ⟨w, run m (by omega), Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩))), fun p ok => sem p (ok.2.2.1 rfl), fun _ => le⟩
  · obtain ⟨w, run, fw, sem, le⟩ := ks.t.union (fieldC_tuple fx) (fieldC_tuple fy)
    exact ⟨w, run m (by omega), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)))),
      fun p ok => sem p (ok.2.2.2.1 rfl), fun _ => le⟩
  · obtain ⟨w, run, fw, sem, le⟩ := ks.m.union (fieldC_map fx) (fieldC_map fy)
    exact ⟨w, run m (by omega), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw⟩)))),
      fun p ok => sem p (ok.2.2.2.2.1 rfl), fun _ => le⟩

theorem kept_of_ne {name : String} {w : Term} (k : kept (.atom name, w) = Bool.false) :
    w = .integer 0 ∨ w = .atom "bdd_bot" := by
  simp only [kept, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at k
  rcases k with k | k
  · exact Or.inl ((compareExact_eq_integer _ _).mp k)
  · exact Or.inr ((compareExact_eq_atom _ _).mp k)

/-- Plain intersections of fields. -/
theorem fieldC_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m) {name : String}
    {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (H → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, k, d⟩ := bit_inter (D m) (fieldC_bitmap fx) (fieldC_bitmap fy)
    refine ⟨w, run, fun kw => ⟨Or.inl ⟨rfl, (k kw).1⟩, fun _ => by rw [lh_bitF (k kw).1]; omega⟩, fun p _ => ?_⟩
    cases kw : kept (.atom "bitmap", w)
    · simp [keptO_false kw, dn_none, dn_bitmap, d kw]
    · simp [keptO_true kw, dn_bitmap, (k kw).2]
  · obtain ⟨w, run, k, d⟩ := atom_inter_spec (D m) (fieldC_atom fx) (fieldC_atom fy)
    refine ⟨w, run, fun kw => ⟨Or.inr (Or.inl ⟨rfl, (k kw).1⟩), fun _ => by rw [lh_atomF (k kw).1]; omega⟩, fun p _ => ?_⟩
    cases kw : kept (.atom "atom", w)
    · simp [keptO_false kw, dn_none, dn_atom, d kw]
    · simp [keptO_true kw, dn_atom, (k kw).2]
  · obtain ⟨n, rfl, -⟩ := succ_of_le hm
    obtain ⟨w, run, k, d⟩ := fun_inter_spec n (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fy))
    refine ⟨w, run, fun kw => ?_, fun p ok => ?_⟩
    · obtain ⟨fw, le⟩ := fc.inter (fieldC_fun fx) (fieldC_fun fy) _ w (by omega) run kw
      exact ⟨Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), le⟩
    cases kw : kept (.atom "fun", w)
    · simp [keptO_false kw, dn_none, dn_fun, d kw _ _ ok.1]
    · simp [keptO_true kw, dn_fun, (k kw).2 _ _ ok.1]
  · obtain ⟨w, run, k, sem⟩ := ks.l.inter (fieldC_list fx) (fieldC_list fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.t.inter (fieldC_tuple fx) (fieldC_tuple fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.m.inter (fieldC_map fx) (fieldC_map fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Plain differences of fields. -/
theorem fieldC_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m) {name : String}
    {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y) :
    ∃ w, Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (H → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, rfl, a₁, a₂⟩ := fieldC_bitmap fx
    obtain ⟨b, rfl, b₁, b₂⟩ := fieldC_bitmap fy
    obtain ⟨r, run, ok, bm, -⟩ := diff_key "bitmap" _ _ (Or.inl ⟨rfl, a, rfl, a₁, a₂⟩) (Or.inl ⟨rfl, b, rfl, b₁, b₂⟩)
    obtain ⟨a', b', ea, eb, rfl⟩ := bm rfl
    have ea' : a = a' := by simp only [Term.integer.injEq] at ea; exact_mod_cast ea
    have eb' : b = b' := by simp only [Term.integer.injEq] at eb; exact_mod_cast eb
    subst ea' eb'
    refine ⟨_, run _, fun kw => ⟨?_, fun _ => by rw [lh_int]; omega⟩, fun p _ => ?_⟩
    · rcases ok kw with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
      · exact Or.inl ⟨rfl, h⟩
      · simp at h
      · exact absurd rfl h
    · cases kw : kept (.atom "bitmap", Term.integer ↑(a - (a &&& b)))
      · simp [kept] at kw
        have : (a - (a &&& b)).testBit p.1 = Bool.false := by
          have z : a - (a &&& b) = 0 := by omega
          rw [z]; simp
        rw [testBit_sub_and] at this
        simpa [keptO_false (show kept (.atom "bitmap", Term.integer ↑(a - (a &&& b))) = Bool.false by simp [kept]; omega),
          dn_none, dn_bitmap, bitOf_nat] using this.symm
      · simp [keptO_true kw, dn_bitmap, bitOf_nat, testBit_sub_and]
  · obtain ⟨r, run, ok, -, am, -⟩ := diff_key "atom" x y (Or.inr (Or.inl ⟨rfl, fieldC_atom fx⟩))
      (Or.inr (Or.inl ⟨rfl, fieldC_atom fy⟩))
    refine ⟨r, run _, fun kw => ?_, fun p _ => ?_⟩
    · rcases ok kw with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩
      · simp at h
      · exact ⟨Or.inr (Or.inl ⟨rfl, h⟩), fun _ => by rw [lh_atomF h]; omega⟩
      · exact absurd rfl h
    · have := am rfl p.2.1
      cases kw : kept (.atom "atom", r)
      · rw [kw] at this
        simp only [Bool.false_eq_true, ite_false] at this
        have h0 : amemV Option.none p.2.1 = Bool.false := rfl
        rw [h0] at this
        simp [keptO_false kw, dn_none, dn_atom, ← this]
      · rw [kw] at this
        simpa [keptO_true kw, dn_atom] using this
  · obtain ⟨n, rfl, -⟩ := succ_of_le (show 1 + 1 ≤ m by omega)
    obtain ⟨w, run, k, d⟩ := fun_diff_spec n (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fy))
    refine ⟨w, run, fun kw => ?_, fun p ok => ?_⟩
    · obtain ⟨fw, le⟩ := fc.diff (fieldC_fun fx) (fieldC_fun fy) _ w (by omega) run kw
      exact ⟨Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)), le⟩
    cases kw : kept (.atom "fun", w)
    · simp [keptO_false kw, dn_none, dn_fun, d kw _ _ ok.1]
    · simp [keptO_true kw, dn_fun, (k kw).2 _ _ ok.1]
  · obtain ⟨w, run, k, sem⟩ := ks.l.diff (fieldC_list fx) (fieldC_list fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.t.diff (fieldC_tuple fx) (fieldC_tuple fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, k, sem⟩ := ks.m.diff (fieldC_map fx) (fieldC_map fy)
    exact ⟨w, run m (by omega), fun kw => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, (k kw).1⟩)))), fun _ => (k kw).2⟩,
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Optimized unions of fields. -/
theorem fieldC_opt_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {name : String} {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_union/4» (D m) (.atom name) x y (.map S) = .ok w ∧ FieldC Fn TF LF MF name w ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (some w) p = (dn name (some x) p || dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, fw, sem, -⟩ := fieldC_union ks fc hm fx fy
    exact ⟨w, by rw [opt_union4_eq _ (Or.inl rfl)]; exact run, fw, sem⟩
  · obtain ⟨w, run, fw, sem, -⟩ := fieldC_union ks fc hm fx fy
    exact ⟨w, by rw [opt_union4_eq _ (Or.inr (Or.inl rfl))]; exact run, fw, sem⟩
  · obtain ⟨w, run, fw, sem, -⟩ := fieldC_union ks fc hm fx fy
    exact ⟨w, by rw [opt_union4_eq _ (Or.inr (Or.inr (Or.inl rfl)))]; exact run, fw, sem⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.l.opt_union S (fieldC_list fx) (fieldC_list fy) (show K ≤ m by omega)
    exact ⟨w, run, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩))), fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.t.opt_union S (fieldC_tuple fx) (fieldC_tuple fy) (show K ≤ m by omega)
    exact ⟨w, run, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw⟩)))), fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.m.opt_union S (fieldC_map fx) (fieldC_map fy) (show K ≤ m by omega)
    exact ⟨w, run, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw⟩)))), fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Optimized intersections of fields. -/
theorem fieldC_opt_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {name : String} {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom name) x y (.map S) = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy
    exact ⟨w, by rw [opt_inter4_eq _ (Or.inl rfl)]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy
    exact ⟨w, by rw [opt_inter4_eq _ (Or.inr (Or.inl rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy
    exact ⟨w, by rw [opt_inter4_eq _ (Or.inr (Or.inr rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.l.opt_inter S (fieldC_list fx) (fieldC_list fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩))), fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.t.opt_inter S (fieldC_tuple fx) (fieldC_tuple fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.m.opt_inter S (fieldC_map fx) (fieldC_map fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Optimized differences of fields. -/
theorem fieldC_opt_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m)
    {name : String} {x y : Term} (fx : FieldC Fn TF LF MF name x) (fy : FieldC Fn TF LF MF name y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom name) x y (.map S) = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy
    exact ⟨w, by rw [opt_diff4_eq _ (Or.inl rfl)]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy
    exact ⟨w, by rw [opt_diff4_eq _ (Or.inr (Or.inl rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy
    exact ⟨w, by rw [opt_diff4_eq _ (Or.inr (Or.inr rfl))]; exact run, fun kw => (k kw).1, sem⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.l.opt_diff S (fieldC_list fx) (fieldC_list fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩))), fun p ok => sem p (ok.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.t.opt_diff S (fieldC_tuple fx) (fieldC_tuple fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨w, run, fw, sem⟩ := ks.m.opt_diff S (fieldC_map fx) (fieldC_map fy) (show K ≤ m by omega)
    exact ⟨w, run, fun kw => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, fw kw⟩)))),
      fun p ok => sem p (ok.2.2.2.2.1 rfl)⟩

/-- Bitmap and atom fields have points. -/
theorem bit_point {x : Term} (h : BitField x) : ∃ i, i < 8 ∧ bitOf x i = Bool.true := by
  obtain ⟨b, rfl, b₁, b₂⟩ := h
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (show b ≠ 0 by omega)
  exact ⟨i, small_bit b₂ hi, by simpa [bitOf_nat] using hi⟩

theorem ptOk_list (ks : Kinds K TF LF MF TV LV MV) {p : Point} (h : LV p.2.2) : PtOkC TV LV MV FV "list" p :=
  ⟨ks.l.resp _ h, by simp, fun _ => h, by simp, by simp, by simp⟩
theorem ptOk_tuple (ks : Kinds K TF LF MF TV LV MV) {p : Point} (h : TV p.2.2) : PtOkC TV LV MV FV "tuple" p :=
  ⟨ks.t.resp _ h, by simp, by simp, fun _ => h, by simp, by simp⟩
theorem ptOk_map (ks : Kinds K TF LF MF TV LV MV) {p : Point} (h : MV p.2.2) : PtOkC TV LV MV FV "map" p :=
  ⟨ks.m.resp _ h, by simp, by simp, by simp, fun _ => h, by simp⟩
theorem ptOk_fun {p : Point} (r : Resp p.2.2) (h : FV p.2.1 p.2.2) : PtOkC TV LV MV FV "fun" p :=
  ⟨r, by simp, by simp, by simp, by simp, fun _ => h⟩

/-- Field emptiness: exact on the structural kinds, never empty on bitmaps and atoms, and complete on functions. -/
theorem fieldC_empty (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {m : Nat} (hm : K ≤ m)
    {name : String} {x : Term} (fx : FieldC Fn TF LF MF name x) (S : List (Term × Term)) (hS : name = "fun" → FS S) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S) = .ok (boolAtom b) ∧
      ∀ N, lh x < N → SafeN N S →
        ((∀ p, PtOkC TV LV MV FV name p → dn name (some x) p = Bool.false) → b = Bool.true) ∧
        (b = Bool.true → ∀ p, PtOkC TV LV MV FV name p → dn name (some x) p = Bool.false) := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom], fun N _ _ => ⟨fun h => ?_,
      fun h => by cases h⟩⟩
    obtain ⟨i, lt, hi⟩ := bit_point (fieldC_bitmap fx)
    have := h (i, .nil, fun _ => Bool.true) ⟨resp_const _, fun _ => lt, by simp, by simp, by simp, by simp⟩
    simp [dn_bitmap, hi] at this
  · refine ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom], fun N _ _ => ⟨fun h => ?_,
      fun h => by cases h⟩⟩
    obtain ⟨⟨p₀, S₀, e, -⟩, q, hq⟩ := fieldC_atom fx
    have := h (0, q, fun _ => Bool.true) ⟨resp_const _, by simp, by simp, by simp, by simp, by simp⟩
    simp [dn_atom, hq] at this
  · obtain ⟨comp, total⟩ := fc.empty S (fieldC_fun fx) (hS rfl) hm
    obtain ⟨b, run, snd⟩ := total hH
    refine ⟨b, run, fun N hx hS' => ⟨fun h => ?_, fun hb p ok => snd N hx hS' hb p ok.1 (ok.2.2.2.2.2 rfl)⟩⟩
    have := (comp N hx hS' fun p r f => h p (ptOk_fun r f)).symm.trans run
    cases b <;> simp_all [boolAtom]
  · obtain ⟨b, run, ex⟩ := ks.l.empty S (fieldC_list fx)
    exact ⟨b, run m hm, fun N hx hS' => ⟨fun h => (ex N hx hS').mpr fun p v => h p (ptOk_list ks v),
      fun hb p ok => (ex N hx hS').mp hb p (ok.2.2.1 rfl)⟩⟩
  · obtain ⟨b, run, ex⟩ := ks.t.empty S (fieldC_tuple fx)
    exact ⟨b, run m hm, fun N hx hS' => ⟨fun h => (ex N hx hS').mpr fun p v => h p (ptOk_tuple ks v),
      fun hb p ok => (ex N hx hS').mp hb p (ok.2.2.2.1 rfl)⟩⟩
  · obtain ⟨b, run, ex⟩ := ks.m.empty S (fieldC_map fx)
    exact ⟨b, run m hm, fun N hx hS' => ⟨fun h => (ex N hx hS').mpr fun p v => h p (ptOk_map ks v),
      fun hb p ok => (ex N hx hS').mp hb p (ok.2.2.2.2.1 rfl)⟩⟩

/-- Fields with no points are checked empty. -/
theorem fieldC_empty_none (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K ≤ m) {name : String}
    {x : Term} (fx : FieldC Fn TF LF MF name x) (hS : name = "fun" → FS [])
    (h : ∀ p, PtOkC TV LV MV FV name p → dn name (some x) p = Bool.false) :
    Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map []) = .ok (.atom "true") := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨i, lt, hi⟩ := bit_point (fieldC_bitmap fx)
    have := h (i, .nil, fun _ => Bool.true) ⟨resp_const _, fun _ => lt, by simp, by simp, by simp, by simp⟩
    simp [dn_bitmap, hi] at this
  · obtain ⟨⟨p₀, S₀, e, -⟩, q, hq⟩ := fieldC_atom fx
    have := h (0, q, fun _ => Bool.true) ⟨resp_const _, by simp, by simp, by simp, by simp, by simp⟩
    simp [dn_atom, hq] at this
  · exact (fc.empty [] (fieldC_fun fx) (hS rfl) hm).1 (lh x + 1) (by omega) (safeN_nil _)
      fun p r f => h p (ptOk_fun r f)
  · obtain ⟨b, run, ex⟩ := ks.l.empty [] (fieldC_list fx)
    have := (ex (lh x + 1) (by omega) (safeN_nil _)).mpr fun p v => h p (ptOk_list ks v)
    subst this; exact run m hm
  · obtain ⟨b, run, ex⟩ := ks.t.empty [] (fieldC_tuple fx)
    have := (ex (lh x + 1) (by omega) (safeN_nil _)).mpr fun p v => h p (ptOk_tuple ks v)
    subst this; exact run m hm
  · obtain ⟨b, run, ex⟩ := ks.m.empty [] (fieldC_map fx)
    have := (ex (lh x + 1) (by omega) (safeN_nil _)).mpr fun p v => h p (ptOk_map ks v)
    subst this; exact run m hm

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Types over the structural kinds: unions, intersections, and differences. -/

/-- Types whose fields are `FieldC`. -/
structure DescrC (Fn TF LF MF : Term → Prop) (X : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup X q).isSome → ∃ name ∈ names, q = .atom name
  fields : ∀ name x, mapLookup X (.atom name) = some x → FieldC Fn TF LF MF name x

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

theorem DescrC.static {X : List (Term × Term)} (s : DescrC Fn TF LF MF X) :
    mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w =>
    obtain ⟨name, m, e⟩ := s.keys (.atom "dynamic") (by rw [h]; rfl)
    simp only [Term.atom.injEq] at e
    subst e
    simp [names] at m

theorem lh_field_le {X : List (Term × Term)} {q x : Term} (h : mapLookup X q = some x) : lh x ≤ lh (.map X) := by
  obtain ⟨e, me, rfl⟩ := entry_of_lookup h
  exact le_lh_map me

/-- Types are as high as their highest field. -/
theorem lh_descr_le {X : List (Term × Term)} {M : Nat} (keys : ∀ q, (mapLookup X q).isSome → ∃ name ∈ names, q = .atom name)
    (h : ∀ name x, mapLookup X (.atom name) = some x → lh x ≤ M) : lh (.map X) ≤ M := by
  refine lh_map_le.mpr fun e me => ?_
  have hx := mapLookup_of_mem_mapEntries me
  obtain ⟨name, -, he⟩ := keys e.1 (by simp [hx])
  rw [he] at hx
  exact h name e.2 hx

/-- Merging two types field by field, keeping fields of either. -/
theorem union_gen {slh : Prop} {L R U : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R)
    (f : Term → Term → Term → Except Exception Term)
    (look : ∀ name, (mapLookup R (.atom name) = none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
      (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = none → mapLookup U (.atom name) = some y) ∧
      (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok u →
        mapLookup U (.atom name) = some u))
    (keysU : ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome)
    (spec : ∀ name x y, FieldC Fn TF LF MF name x → FieldC Fn TF LF MF name y → ∃ u, f (.atom name) x y = .ok u ∧
      FieldC Fn TF LF MF name u ∧
      (∀ p, PtOkC TV LV MV FV name p → dn name (some u) p = (dn name (some x) p || dn name (some y) p)) ∧
      (slh → lh u ≤ max (lh x) (lh y))) :
    DescrC Fn TF LF MF U ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup U (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p)) ∧
      (slh → lh (.map U) ≤ max (lh (.map L)) (lh (.map R))) := by
  have at_name : ∀ name, (mapLookup R (.atom name) = none ∧ mapLookup U (.atom name) = mapLookup L (.atom name)) ∨
      (∃ y, mapLookup R (.atom name) = some y ∧ mapLookup L (.atom name) = none ∧ mapLookup U (.atom name) = some y) ∨
      ∃ x y u, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup U (.atom name) = some u ∧ FieldC Fn TF LF MF name u ∧
        (∀ p, PtOkC TV LV MV FV name p → dn name (some u) p = (dn name (some x) p || dn name (some y) p)) ∧
        (slh → lh u ≤ max (lh x) (lh y)) := by
    intro name
    obtain ⟨h₁, h₂, h₃⟩ := look name
    cases hR : mapLookup R (.atom name) with
    | none => exact Or.inl ⟨rfl, h₁ hR⟩
    | some y =>
      cases hL : mapLookup L (.atom name) with
      | none => exact Or.inr (Or.inl ⟨y, rfl, rfl, h₂ y hR hL⟩)
      | some x =>
        obtain ⟨u, run, fu, sem, le⟩ := spec name x y (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr (Or.inr ⟨x, y, u, rfl, rfl, h₃ x y u hL hR run, fu, sem, le⟩)
  have keys : ∀ q, (mapLookup U q).isSome → ∃ name ∈ names, q = .atom name := fun q h =>
    (keysU q h).elim (sL.keys q) (sR.keys q)
  refine ⟨⟨keys, fun name u hu => ?_⟩, fun name p ok => ?_, fun hs => lh_descr_le keys fun name u hu => ?_⟩
  · rcases at_name name with ⟨-, hU⟩ | ⟨y, hR, -, hU⟩ | ⟨x, y, u', -, -, hU, fu, -⟩
    · rw [hU] at hu; exact sL.fields name u hu
    · rw [hU] at hu; cases hu; exact sR.fields name _ hR
    · rw [hU] at hu; cases hu; exact fu
  · rcases at_name name with ⟨hR, hU⟩ | ⟨y, hR, hL, hU⟩ | ⟨x, y, u, hL, hR, hU, -, sem, -⟩
    · rw [hU, hR, dn_none]; simp
    · rw [hU, hR, hL, dn_none]; simp
    · rw [hU, hL, hR, sem p ok]
  · rcases at_name name with ⟨-, hU⟩ | ⟨y, hR, -, hU⟩ | ⟨x, y, u', hL, hR, hU, -, -, le⟩
    · rw [hU] at hu; have := lh_field_le hu; omega
    · rw [hU] at hu; cases hu; have := lh_field_le hR; omega
    · rw [hU] at hu; cases hu
      have := le hs; have := lh_field_le hL; have := lh_field_le hR; omega

/-- Plain unions of types. -/
theorem descr_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D (m + 1)) (.map L) (.map R) = .ok (.map U) ∧
      DescrC Fn TF LF MF U ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup U (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p)) ∧
      (H → lh (.map U) ≤ max (lh (.map L)) (lh (.map R))) := by
  obtain ⟨U, run, look⟩ := union_any m L R sL.static sR.static (fun q h => by
      obtain ⟨name, -, e⟩ := sR.keys q h; exact ⟨name, e⟩)
    (fun q x y hx hy => by
      obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
      obtain ⟨u, run, -⟩ := fieldC_union ks fc hm (sL.fields name x hx) (sR.fields name y hy)
      exact ⟨u, run⟩)
  have keysU : ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome := by
    intro q h
    obtain ⟨h₁, h₂, h₃⟩ := look q
    cases hR : mapLookup R q with
    | none => rw [h₁ hR] at h; exact Or.inl h
    | some y => exact Or.inr (by simp)
  obtain ⟨cU, sem, lh⟩ := union_gen (slh := H) sL sR (fun q x y => Elixir.Module.Types.Descr.«bare_union/3» (D m) q x y)
    (fun name => ⟨(look _).1, (look _).2.1, (look _).2.2⟩) keysU
    (fun name x y fx fy => let ⟨u, run, fu, sem, le⟩ := fieldC_union ks fc hm fx fy; ⟨u, run, fu, sem, le⟩)
  exact ⟨U, run, cU, sem, lh⟩

/-- Optimized unions of types. -/
theorem descr_opt_union (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) (S : List (Term × Term)) :
    ∃ U, Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) (.map L) (.map R) (.map S) = .ok (.map U) ∧
      DescrC Fn TF LF MF U ∧
      ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup U (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p || dn name (mapLookup R (.atom name)) p) := by
  obtain ⟨U, run, look, keysU⟩ := opt_union_lookup m L R (.map S) sL.static sR.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨u, run, -⟩ := fieldC_opt_union ks fc hm (sL.fields name x hx) (sR.fields name y hy) S
    exact ⟨u, run⟩
  obtain ⟨cU, sem, -⟩ := union_gen (slh := False) sL sR
    (fun q x y => Elixir.Module.Types.Descr.«opt_union/4» (D m) q x y (.map S)) look keysU
    (fun name x y fx fy => let ⟨u, run, fu, sem⟩ := fieldC_opt_union ks fc hm fx fy S; ⟨u, run, fu, sem, False.elim⟩)
  exact ⟨U, run, cU, sem⟩

/-- Intersecting two types field by field, keeping fields of both. -/
theorem inter_gen {slh : Prop} {L R I : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R)
    (f : Term → Term → Term → Except Exception Term)
    (look : ∀ name, (mapLookup L (.atom name) = none → mapLookup I (.atom name) = none) ∧
      (mapLookup R (.atom name) = none → mapLookup I (.atom name) = none) ∧
      (∀ x y w, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y → f (.atom name) x y = .ok w →
        mapLookup I (.atom name) = keptO name w))
    (keysI : ∀ q, (mapLookup I q).isSome → (mapLookup L q).isSome)
    (spec : ∀ name x y, FieldC Fn TF LF MF name x → FieldC Fn TF LF MF name y → ∃ w, f (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (slh → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)) :
    DescrC Fn TF LF MF I ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup I (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p)) ∧
      (slh → lh (.map I) ≤ max (lh (.map L)) (lh (.map R))) := by
  have at_name : ∀ name, (mapLookup L (.atom name) = none ∧ mapLookup I (.atom name) = none) ∨
      (mapLookup R (.atom name) = none ∧ mapLookup I (.atom name) = none) ∨
      ∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup I (.atom name) = keptO name w ∧
        (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧ (slh → lh w ≤ max (lh x) (lh y))) ∧
        (∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)) := by
    intro name
    obtain ⟨h₁, h₂, h₃⟩ := look name
    cases hL : mapLookup L (.atom name) with
    | none => exact Or.inl ⟨rfl, h₁ hL⟩
    | some x =>
      cases hR : mapLookup R (.atom name) with
      | none => exact Or.inr (Or.inl ⟨rfl, h₂ hR⟩)
      | some y =>
        obtain ⟨w, run, k, sem⟩ := spec name x y (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr (Or.inr ⟨x, y, w, rfl, rfl, h₃ x y w hL hR run, k, sem⟩)
  have keys : ∀ q, (mapLookup I q).isSome → ∃ name ∈ names, q = .atom name := fun q h => sL.keys q (keysI q h)
  refine ⟨⟨keys, fun name w hw => ?_⟩, fun name p ok => ?_, fun hs => lh_descr_le keys fun name w hw => ?_⟩
  · rcases at_name name with ⟨-, hI⟩ | ⟨-, hI⟩ | ⟨x, y, w', -, -, hI, k, -⟩
    · rw [hI] at hw; cases hw
    · rw [hI] at hw; cases hw
    · rw [hI] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw; exact (k kw).1
  · rcases at_name name with ⟨hL, hI⟩ | ⟨hR, hI⟩ | ⟨x, y, w, hL, hR, hI, -, sem⟩
    · rw [hI, hL, dn_none]; simp
    · rw [hI, hR, dn_none]; simp
    · rw [hI, hL, hR, sem p ok]
  · rcases at_name name with ⟨-, hI⟩ | ⟨-, hI⟩ | ⟨x, y, w', hL, hR, hI, k, -⟩
    · rw [hI] at hw; cases hw
    · rw [hI] at hw; cases hw
    · rw [hI] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw
        have := (k kw).2 hs; have := lh_field_le hL; have := lh_field_le hR; omega

/-- Plain intersections of types. -/
theorem descr_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) :
    ∃ I, Elixir.Module.Types.Descr.«bare_intersection/2» (D (m + 1)) (.map L) (.map R) = .ok (.map I) ∧
      DescrC Fn TF LF MF I ∧
      (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup I (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p)) ∧
      (H → lh (.map I) ≤ max (lh (.map L)) (lh (.map R))) := by
  obtain ⟨I, run, look, keysI⟩ := inter_lookup m L R sL.static sR.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := fieldC_inter ks fc hm (sL.fields name x hx) (sR.fields name y hy)
    exact ⟨w, run⟩
  obtain ⟨cI, sem, lh⟩ := inter_gen (slh := H) sL sR
    (fun q x y => Elixir.Module.Types.Descr.«bare_intersection/3» (D m) q x y)
    (fun name => ⟨(look name).1, (look name).2.1, fun x y w hx hy r => by rw [(look name).2.2 x y w hx hy r]; rfl⟩)
    keysI (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_inter ks fc hm fx fy;
      ⟨w, run, fun kw => ⟨(k kw).1, (k kw).2⟩, sem⟩)
  exact ⟨I, run, cI, sem, lh⟩

/-- Optimized intersections of types. -/
theorem descr_opt_inter (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 1 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) (S : List (Term × Term)) :
    ∃ I, Elixir.Module.Types.Descr.«opt_intersection/3» (D (m + 1)) (.map L) (.map R) (.map S) = .ok (.map I) ∧
      DescrC Fn TF LF MF I ∧
      ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup I (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && dn name (mapLookup R (.atom name)) p) := by
  obtain ⟨I, run, look, keysI⟩ := opt_inter_lookup m L R (.map S) sL.static sR.static fun q x y hx hy => by
    obtain ⟨name, -, rfl⟩ := sL.keys q (by simp [hx])
    obtain ⟨w, run, -⟩ := fieldC_opt_inter ks fc hm (sL.fields name x hx) (sR.fields name y hy) S
    exact ⟨w, run⟩
  obtain ⟨cI, sem, -⟩ := inter_gen (slh := False) sL sR
    (fun q x y => Elixir.Module.Types.Descr.«opt_intersection/4» (D m) q x y (.map S))
    (fun name => ⟨(look name).1, (look name).2.1, fun x y w hx hy r => by rw [(look name).2.2 x y w hx hy r]; rfl⟩)
    keysI (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_opt_inter ks fc hm fx fy S;
      ⟨w, run, fun kw => ⟨k kw, False.elim⟩, sem⟩)
  exact ⟨I, run, cI, sem⟩

/-- Folding the differences of fields, which keeps the fields of the first type outside the second. -/
theorem diff_gen {slh : Prop} (depth : Nat) (fn : Term) (f : Term → Term → Term → Except Exception Term)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R)
    (call : ∀ q v₁ v₂, Lynx.Dispatcher.pure (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) fn #[q, v₁, v₂] =
      f q v₁ v₂)
    (spec : ∀ name x y, FieldC Fn TF LF MF name x → FieldC Fn TF LF MF name y → ∃ w, f (.atom name) x y = .ok w ∧
      (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧
        (slh → lh w ≤ max (lh x) (lh y))) ∧
      ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)) :
    ∃ O, (mapEntries R).foldlM (fun acc entry =>
        (Dispatch.dispatch (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
          (.function false "Elixir.Module.Types.Descr" "-dynamic_difference/3-fun-0-" 3 #[fn]) #[entry.1, entry.2, acc] :
          Except Exception Term)) (.map L) = .ok (.map O) ∧
      DescrC Fn TF LF MF O ∧ (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup O (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && !dn name (mapLookup R (.atom name)) p)) ∧
      (slh → lh (.map O) ≤ max (lh (.map L)) (lh (.map R))) := by
  let g : Term → Term → Term → Term := fun q v₁ v₂ =>
    match f q v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y w, f q x y = .ok w → g q x y = w := by intro q x y w run; simp [g, run]
  obtain ⟨O, fold, lookO, -⟩ := difference_fold depth fn g (mapEntries R) L (mapEntries_distinct R) (by
    intro e member v₁ found
    have hy := mapLookup_of_mem_mapEntries member
    obtain ⟨name, -, he⟩ := sR.keys e.1 (by simp [hy])
    rw [he] at hy found ⊢
    obtain ⟨w, run, -⟩ := spec name v₁ e.2 (sL.fields name v₁ found) (sR.fields name e.2 hy)
    rw [call, run, value _ _ _ _ run])
  have look := lookup_fold lookO
  have at_name : ∀ name, (mapLookup R (.atom name) = none ∧ mapLookup O (.atom name) = mapLookup L (.atom name)) ∨
      (mapLookup L (.atom name) = none ∧ mapLookup O (.atom name) = none) ∨
      ∃ x y w, mapLookup L (.atom name) = some x ∧ mapLookup R (.atom name) = some y ∧
        mapLookup O (.atom name) = keptO name w ∧
        (kept (.atom name, w) = Bool.true → FieldC Fn TF LF MF name w ∧
          (slh → lh w ≤ max (lh x) (lh y))) ∧
        ∀ p, PtOkC TV LV MV FV name p → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p) := by
    intro name
    rw [look name]
    cases hR : mapLookup R (.atom name) with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some y =>
      cases hL : mapLookup L (.atom name) with
      | none => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | some x =>
        obtain ⟨w, run, k, d⟩ := spec name x y (sL.fields name x hL) (sR.fields name y hR)
        exact Or.inr (Or.inr ⟨x, y, w, rfl, rfl, by simp [value _ _ _ _ run, keptO], k, d⟩)
  have keysO : ∀ q, (mapLookup O q).isSome → ∃ name ∈ names, q = .atom name := by
    intro q h
    rw [lookO] at h
    cases hit : (mapEntries R).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
    | none => rw [hit] at h; exact sL.keys q h
    | some e =>
      rw [hit] at h
      obtain ⟨qe, -⟩ := find_entry hit
      cases hl : mapLookup L e.1 with
      | none => simp [hl] at h
      | some x =>
        obtain ⟨name, m, he⟩ := sL.keys e.1 (by simp [hl])
        rw [he] at qe
        exact ⟨name, m, (compareExact_eq_atom q name).mp qe⟩
  refine ⟨O, by simpa using fold, ⟨keysO, fun name w hw => ?_⟩, fun name p ok => ?_, fun hs => ?_⟩
  · rcases at_name name with ⟨-, hO⟩ | ⟨-, hO⟩ | ⟨x, y, w', -, -, hO, k, -⟩
    · rw [hO] at hw; exact sL.fields name w hw
    · rw [hO] at hw; cases hw
    · rw [hO] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw; exact (k kw).1
  · rcases at_name name with ⟨hR, hO⟩ | ⟨hL, hO⟩ | ⟨x, y, w, hL, hR, hO, -, d⟩
    · rw [hO, hR, dn_none]; simp
    · rw [hO, hL, dn_none]; simp
    · rw [hO, hL, hR, d p ok]
  · refine lh_descr_le keysO fun name w hw => ?_
    rcases at_name name with ⟨-, hO⟩ | ⟨-, hO⟩ | ⟨x, y, w', hL, hR, hO, k, -⟩
    · rw [hO] at hw; have := lh_field_le hw; omega
    · rw [hO] at hw; cases hw
    · rw [hO] at hw
      cases kw : kept (.atom name, w')
      · rw [keptO_false kw] at hw; cases hw
      · rw [keptO_true kw] at hw; cases hw
        have := (k kw).2 hs; have := lh_field_le hL; have := lh_field_le hR; omega

/-- Plain differences of types. -/
theorem descr_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) :
    ∃ O, Elixir.Module.Types.Descr.«bare_difference/2» (D (m + 2)) (.map L) (.map R) = .ok (.map O) ∧
      DescrC Fn TF LF MF O ∧ (∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup O (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && !dn name (mapLookup R (.atom name)) p)) ∧
      (H → lh (.map O) ≤ max (lh (.map L)) (lh (.map R))) := by
  by_cases nR : R = []
  · subst nR
    refine ⟨L, by unfold Elixir.Module.Types.Descr.«bare_difference/2»; simp [Erlang.erlang.«==/2»], sL,
      fun name p _ => by simp [mapLookup, dn_none], by omega⟩
  obtain ⟨O, fold, sO, dO, lO⟩ := diff_gen (slh := H) m
    (.function false "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    (fun q x y => Elixir.Module.Types.Descr.«bare_difference/3» (D m) q x y) sL sR
    (fun q x y => by rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure])
    (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx fy;
      ⟨w, run, fun kw => ⟨(k kw).1, (k kw).2⟩, sem⟩)
  refine ⟨O, ?_, sO, dO, lO⟩
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sL.static, static_map sR.static, nR]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», nR, Erlang.maps.«fold/3»]
  simpa using fold

/-- Optimized differences of types. -/
theorem descr_opt_diff (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {m : Nat} (hm : K + 2 ≤ m)
    {L R : List (Term × Term)} (sL : DescrC Fn TF LF MF L) (sR : DescrC Fn TF LF MF R) (S : List (Term × Term)) :
    ∃ O, Elixir.Module.Types.Descr.«opt_difference/3» (D (m + 2)) (.map L) (.map R) (.map S) = .ok (.map O) ∧
      DescrC Fn TF LF MF O ∧ ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup O (.atom name)) p =
        (dn name (mapLookup L (.atom name)) p && !dn name (mapLookup R (.atom name)) p) := by
  by_cases nR : R = []
  · subst nR
    refine ⟨L, by unfold Elixir.Module.Types.Descr.«opt_difference/3»; simp [Erlang.erlang.«==/2»], sL,
      fun name p _ => by simp [mapLookup, dn_none]⟩
  obtain ⟨O, fold, sO, dO, -⟩ := diff_gen (slh := False) m
    (.function false "Elixir.Module.Types.Descr" "-opt_difference/3-anonymous-0-" 3 #[.map S])
    (fun q x y => Elixir.Module.Types.Descr.«opt_difference/4» (D m) q x y (.map S)) sL sR
    (fun q x y => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_difference/3-anonymous-0-/3».pure]
      simp only [Elixir.Module.Types.Descr.«-opt_difference/3-anonymous-0-/4»])
    (fun name x y fx fy => let ⟨w, run, k, sem⟩ := fieldC_opt_diff ks fc hm fx fy S;
      ⟨w, run, fun kw => ⟨k kw, False.elim⟩, sem⟩)
  refine ⟨O, ?_, sO, dO⟩
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sL.static, static_map sR.static, nR]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», nR, Erlang.maps.«fold/3»]
  simpa using fold

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Emptiness of types over the structural kinds. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

/-- The emptiness check of a field, as a Boolean, for absent fields `true`. -/
theorem key_bool (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {m : Nat} (hm : K ≤ m)
    {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) (S : List (Term × Term)) (hS : FS S) (name : String) :
    ∃ b : Bool, (∀ x, mapLookup X (.atom name) = some x →
        Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S) = .ok (boolAtom b)) ∧
      (mapLookup X (.atom name) = none → b = Bool.true) ∧
      ∀ N, lh (.map X) < N → SafeN N S →
        ((∀ p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) → b = Bool.true) ∧
        (b = Bool.true → ∀ p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) := by
  cases hx : mapLookup X (.atom name) with
  | none => exact ⟨Bool.true, ⟨fun _ h => by simp at h, fun _ => rfl, fun _ _ _ => ⟨fun _ => rfl, fun _ p _ => dn_none _ _⟩⟩⟩
  | some x =>
    obtain ⟨b, run, ex⟩ := fieldC_empty ks fc hH hm (sX.fields name x hx) S (fun _ => hS)
    exact ⟨b, ⟨fun x' h => by simp only [Option.some.injEq] at h; subst h; exact run, fun h => by simp at h,
      fun N hN hs => ex N (by have := lh_field_le hx; omega) hs⟩⟩

theorem descr_empty_run (d : Dispatcher) {X : List (Term × Term)} (static : mapLookup X (.atom "dynamic") = none)
    (nonempty : X ≠ []) {S : Term} {bt bm bl bf : Bool}
    (ht : ∀ x, mapLookup X (.atom "tuple") = some x → Elixir.Module.Types.Descr.«tuple_empty?/2» d x S = .ok (boolAtom bt))
    (hm : ∀ x, mapLookup X (.atom "map") = some x → Elixir.Module.Types.Descr.«map_empty?/2» d x S = .ok (boolAtom bm))
    (hl : ∀ x, mapLookup X (.atom "list") = some x → Elixir.Module.Types.Descr.«list_empty?/2» d x S = .ok (boolAtom bl))
    (hf : ∀ x, mapLookup X (.atom "fun") = some x → Elixir.Module.Types.Descr.«fun_empty?/2» d x S = .ok (boolAtom bf)) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d (.map X) S = .ok (boolAtom (
      !(mapLookup X (.atom "atom")).isSome && !(mapLookup X (.atom "bitmap")).isSome &&
      ((mapLookup X (.atom "tuple")).isNone || bt) && ((mapLookup X (.atom "map")).isNone || bm) &&
      ((mapLookup X (.atom "list")).isNone || bl) && ((mapLookup X (.atom "fun")).isNone || bf))) := by
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
  cases ha : mapLookup X (.atom "atom") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso, boolAtom]
  | none =>
  cases hb : mapLookup X (.atom "bitmap") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  | none =>
  cases h₁ : mapLookup X (.atom "tuple") <;> cases h₂ : mapLookup X (.atom "map") <;>
    cases h₃ : mapLookup X (.atom "list") <;> cases h₄ : mapLookup X (.atom "fun") <;>
    simp [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», Lynx.Except.andAlso, ha, hb, h₁, h₂, h₃, h₄,
      ht, hm, hl, hf] <;>
    cases bt <;> cases bm <;> cases bl <;> cases bf <;> simp [boolAtom]

theorem names_mem {name : String} (h : name ∈ names) :
    name = "bitmap" ∨ name = "atom" ∨ name = "fun" ∨ name = "list" ∨ name = "tuple" ∨ name = "map" := by
  simp [names] at h; omega

theorem atom_full {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {x : Term}
    (hx : mapLookup X (.atom "atom") = some x) : ∃ p, PtOkC TV LV MV FV "atom" p ∧ dn "atom" (some x) p = Bool.true := by
  obtain ⟨⟨p₀, S₀, e, -⟩, q, hq⟩ := fieldC_atom (sX.fields "atom" x hx)
  exact ⟨(0, q, fun _ => Bool.true), ⟨resp_const _, by simp, by simp, by simp, by simp, by simp⟩, by simp [dn_atom, hq]⟩

theorem bitmap_full {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {x : Term}
    (hx : mapLookup X (.atom "bitmap") = some x) : ∃ p, PtOkC TV LV MV FV "bitmap" p ∧ dn "bitmap" (some x) p = Bool.true := by
  obtain ⟨i, lt, hi⟩ := bit_point (fieldC_bitmap (sX.fields "bitmap" x hx))
  exact ⟨(i, .nil, fun _ => Bool.true), ⟨resp_const _, fun _ => lt, by simp, by simp, by simp, by simp⟩, by simp [dn_bitmap, hi]⟩

/-- Types decide their emptiness: completely, and soundly when their function field is checked non-empty. -/
theorem descr_empty (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {m : Nat} (hm : K ≤ m)
    {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) (S : List (Term × Term)) (hS : FS S) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.map X) (.map S) = .ok (boolAtom b) ∧
      ∀ N, lh (.map X) < N → SafeN N S →
        ((∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) → b = Bool.true) ∧
        (b = Bool.true → ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) := by
  by_cases ne : X = []
  · subst ne
    exact ⟨Bool.true, by simpa [boolAtom] using empty_none_seen (D m) (.map S),
      fun _ _ _ => ⟨fun _ => rfl, fun _ name p _ => by simp [mapLookup, dn_none]⟩⟩
  obtain ⟨bt, rt, nt, et⟩ := key_bool ks fc hH hm sX S hS "tuple"
  obtain ⟨bm, rm, nm, em⟩ := key_bool ks fc hH hm sX S hS "map"
  obtain ⟨bl, rl, nl, el⟩ := key_bool ks fc hH hm sX S hS "list"
  obtain ⟨bf, rf, nf, efu⟩ := key_bool ks fc hH hm sX S hS "fun"
  have run := descr_empty_run (D m) (S := .map S) (bt := bt) (bm := bm) (bl := bl) (bf := bf) sX.static ne
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rt x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rm x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rl x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rf x h)
  refine ⟨_, run, fun N hN hs => ⟨fun none => ?_, fun yes name p ok => ?_⟩⟩
  · have noA : (mapLookup X (.atom "atom")).isSome = Bool.false := by
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
    rw [noA, noB, (et N hN hs).1 (none "tuple"), (em N hN hs).1 (none "map"), (el N hN hs).1 (none "list"),
      (efu N hN hs).1 (none "fun")]
    simp
  · simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      Bool.or_eq_true] at yes
    obtain ⟨⟨⟨⟨⟨hA, hB⟩, yt⟩, ym⟩, yl⟩, yf⟩ := yes
    by_cases mem : name ∈ names
    rotate_left
    · have : mapLookup X (.atom name) = none := by
        cases h : mapLookup X (.atom name) with
        | none => rfl
        | some x =>
          obtain ⟨name', m', e⟩ := sX.keys _ (by rw [h]; rfl)
          simp only [Term.atom.injEq] at e; subst e; exact absurd m' mem
      rw [this, dn_none]
    have kindCase : ∀ {b : Bool}, (mapLookup X (.atom name) = none ∨ b = Bool.true) →
        (b = Bool.true → dn name (mapLookup X (.atom name)) p = Bool.false) →
        dn name (mapLookup X (.atom name)) p = Bool.false := fun h k => by
      rcases h with h | h
      · rw [h, dn_none]
      · exact k h
    rcases names_mem mem with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hB, dn_none]
    · rw [hA, dn_none]
    · exact kindCase yf fun h => (efu N hN hs).2 h p ok
    · exact kindCase yl fun h => (el N hN hs).2 h p ok
    · exact kindCase yt fun h => (et N hN hs).2 h p ok
    · exact kindCase ym fun h => (em N hN hs).2 h p ok
end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fields and types mean the same up to comparison. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

theorem lookup_rel_cmp {M M' : List (Term × Term)} (h : Term.compare (Term.fuel (Term.map M) (Term.map M')) (Term.map M) (Term.map M') = .eq) (q : Term) :
    Option.Rel (fun x y => Term.compare (Term.fuel x y) x y = .eq) (mapLookup M q) (mapLookup M' q) :=
  lookup_of_map_compare_eq M M' h q

theorem isSome_rel {a b : Option Term} (h : Option.Rel (fun x y => Term.compare (Term.fuel x y) x y = .eq) a b) :
    a.isSome = b.isSome := by cases h <;> rfl

theorem tuple2_cmp {a b a' b' : Term} (h : Term.compare (Term.fuel (.tuple #[a, b]) (.tuple #[a', b'])) (.tuple #[a, b]) (.tuple #[a', b']) = .eq) :
    Term.compare (Term.fuel a a') a a' = .eq ∧ Term.compare (Term.fuel b b') b b' = .eq := by
  rw [compare_tuple] at h
  simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
  exact ⟨h.1, h.2.1⟩

theorem map_cmp_shape {X : List (Term × Term)} {b : Term} (h : Term.compare (Term.fuel (.map X) b) (.map X) b = .eq) : ∃ Y, b = .map Y := by
  cases b <;> rw [compare_step] at h <;> simp [Compare.compareStep] at h
  exact ⟨_, rfl⟩

theorem atomF_congr {x x' : Term} (fx : AtomF x) (fx' : AtomF x') (e : Term.compare (Term.fuel x x') x x' = .eq) (q : Term) :
    amemV (some x) q = amemV (some x') q := by
  obtain ⟨⟨p, S, rfl, -⟩, -⟩ := fx
  obtain ⟨⟨p', S', rfl, -⟩, -⟩ := fx'
  obtain ⟨et, es⟩ := tuple2_cmp e
  have tags : p = p' := by cases p <;> cases p' <;> simp_all
  subst tags
  have := isSome_rel (lookup_rel_cmp es q)
  cases p <;> simp [amemV, this]

theorem funF_congr {x x' : Term} (fx : FunF x) (fx' : FunF x') (e : Term.compare (Term.fuel x x') x x' = .eq) (a : Term)
    {ρ : Term → Bool} (resp : Resp ρ) : arityOf x a ρ = arityOf x' a ρ := by
  obtain ⟨p, R, rfl, bR⟩ := fx
  obtain ⟨p', R', rfl, bR'⟩ := fx'
  obtain ⟨et, er⟩ := tuple2_cmp e
  have tags : p = p' := by cases p <;> cases p' <;> simp_all
  subst tags
  rw [arity_tag, arity_tag]
  congr 1
  simp only [evalR]
  have rel := lookup_rel_cmp er a
  cases h : mapLookup R a <;> cases h' : mapLookup R' a <;> rw [h, h'] at rel <;> cases rel
  rename_i v v' cmp
  exact eval_congr_cmp (bR a v h) resp cmp

/-- Fields mean the same up to comparison. -/
theorem fieldC_congr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {name : String} {x x' : Term}
    (fx : FieldC Fn TF LF MF name x) (fx' : FieldC Fn TF LF MF name x') (e : Term.compare (Term.fuel x x') x x' = .eq) (p : Point)
    (ok : PtOkC TV LV MV FV name p) : dn name (some x) p = dn name (some x') p := by
  rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨b, rfl, -⟩ := fieldC_bitmap fx
    obtain ⟨b', rfl, -⟩ := fieldC_bitmap fx'
    have : (b : Int) = b' := by simpa using e
    simp [dn_bitmap, this]
  · rw [dn_atom, dn_atom, atomF_congr (fieldC_atom fx) (fieldC_atom fx') e]
  · rw [dn_fun, dn_fun, funF_congr (fc.funF (fieldC_fun fx)) (fc.funF (fieldC_fun fx')) e _ ok.1]
  · exact ks.l.congr (fieldC_list fx) (fieldC_list fx') e p (ok.2.2.1 rfl)
  · exact ks.t.congr (fieldC_tuple fx) (fieldC_tuple fx') e p (ok.2.2.2.1 rfl)
  · exact ks.m.congr (fieldC_map fx) (fieldC_map fx') e p (ok.2.2.2.2.1 rfl)

/-- Types mean the same up to comparison. -/
theorem descr_congr (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) {A B : List (Term × Term)}
    (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B) (e : Term.compare (Term.fuel (.map A) (.map B)) (.map A) (.map B) = .eq)
    (name : String) (p : Point) (ok : PtOkC TV LV MV FV name p) :
    dn name (mapLookup A (.atom name)) p = dn name (mapLookup B (.atom name)) p := by
  have rel := lookup_rel_cmp e (.atom name)
  cases hA : mapLookup A (.atom name) <;> cases hB : mapLookup B (.atom name) <;> rw [hA, hB] at rel <;> cases rel
  rename_i x y cmp
  exact fieldC_congr ks fc (sA.fields name x hA) (sB.fields name y hB) cmp p ok

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Subtyping and disjointness of types over the structural kinds. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

/-- A checked field is included in the other type's field. -/
theorem keySub_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) (hS : FS []) {m : Nat} (hm : K + 2 ≤ m)
    {B : List (Term × Term)} (sB : DescrC Fn TF LF MF B) {name : String} {x : Term} (fx : FieldC Fn TF LF MF name x)
    (h : KeySub (D m) B (.atom name) x) (p : Point) (ok : PtOkC TV LV MV FV name p) (hx : dn name (some x) p = Bool.true) :
    dn name (mapLookup B (.atom name)) p = Bool.true := by
  rcases h with ⟨y, w, hy, run, e⟩ | ⟨hy, e⟩
  · obtain ⟨w', run', k, sem⟩ := fieldC_diff ks fc hm fx (sB.fields name y hy)
    rw [run] at run'; cases run'
    have hd := sem p ok
    rw [hy]
    have gone : dn name (keptO name w) p = Bool.false := by
      cases kw : kept (.atom name, w)
      · rw [keptO_false kw, dn_none]
      · rw [keptO_true kw]
        rcases e with rfl | rfl | e
        · simp [kept] at kw
        · simp [kept] at kw
        · obtain ⟨fw, -⟩ := k kw
          obtain ⟨b, rb, ex⟩ := fieldC_empty ks fc hH (show K ≤ m by omega) fw [] (fun _ => hS)
          have hb : b = Bool.true := by
            have := rb.symm.trans e; cases b <;> simp_all [boolAtom]
          exact (ex (lh w + 1) (by omega) (safeN_nil _)).2 hb p ok
    rw [gone, hx] at hd
    cases hdy : dn name (some y) p
    · rw [hdy] at hd; simp at hd
    · rfl
  · exfalso
    rcases fieldC_cases fx with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Elixir.Module.Types.Descr.«empty_key?/3»] at e
    all_goals
      obtain ⟨b, rb, ex⟩ := fieldC_empty ks fc hH (show K ≤ m by omega) fx [] (fun _ => hS)
      have hb : b = Bool.true := by
        have := rb.symm.trans e; cases b <;> simp_all [boolAtom]
      have := (ex (lh x + 1) (by omega) (safeN_nil _)).2 hb p ok
      rw [hx] at this; cases this

/-- `subtype?/2` answers `true` only on included types. -/
theorem descr_sub_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) (hS : FS []) {m : Nat}
    (hm : K + 2 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B) = .ok (.atom "true")) :
    ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup A (.atom name)) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true := by
  have stA := sA.static
  have stB := sB.static
  unfold Elixir.Module.Types.Descr.«subtype?/2» at h
  simp [unfold_map, Erlang.erlang.«is_map_key/2», stA, stB, any_key, Lynx.Except.andAlso,
    Erlang.erlang.«/=/2»] at h
  unfold Elixir.Module.Types.Descr.«subtype_static?/2» at h
  by_cases same : compareExact (fuel (.map B) (.map A)) (.map B) (.map A) = .eq
  · intro name p ok hx
    rw [← descr_congr ks fc sA sB (Lynx.Term.compare_eq_symm (compare_eq_of_compareExact_eq _ _ same)) name p ok]
    exact hx
  · simp [Erlang.erlang.«=:=/2», same, Elixir.Module.Types.Descr.«empty_difference_subtype?/2»] at h
    rw [Elixir.Module.Types.Descr.«empty_difference_subtype?/3».eq_def] at h
    simp [getMapKeys_single, stA, Erlang.maps.«iterator/1»] at h
    have walk := iterator_sound (D m) B (mapEntries A) h
    intro name p ok hx
    cases hA : mapLookup A (.atom name) with
    | none => rw [hA, dn_none] at hx; cases hx
    | some x =>
      rw [hA] at hx
      obtain ⟨e, me, qe, ex⟩ := lookup_entry hA
      have e1 : e.1 = .atom name := by
        have := Lynx.Term.compareExact_eq_symm qe
        simpa using this
      have := walk e me
      rw [e1, ex] at this
      exact keySub_sound ks fc hH hS hm sB (sA.fields name x hA) this p ok hx

/-- `subtype?/2` answers `true` on included types. -/
theorem descr_sub_complete (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hS : FS []) {m : Nat}
    (hm : K + 2 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (incl : ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup A (.atom name)) p = Bool.true →
      dn name (mapLookup B (.atom name)) p = Bool.true) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) (.map A) (.map B) = .ok (.atom "true") := by
  refine subtype_keys (D m) A B sA.static sB.static fun e me => ?_
  have hx := mapLookup_of_mem_mapEntries me
  obtain ⟨name, -, key⟩ := sA.keys e.1 (by simp [hx])
  rw [key] at hx ⊢
  have fx := sA.fields name e.2 hx
  have none : ∀ w, FieldC Fn TF LF MF name w →
      (∀ p, PtOkC TV LV MV FV name p → dn name (some w) p = Bool.false) →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) w (.map []) = .ok (.atom "true") := by
    intro w fw empty
    exact fieldC_empty_none ks fc (show K ≤ m by omega) fw (fun _ => hS) empty
  cases hy : mapLookup B (.atom name) with
  | none =>
    refine Or.inr ⟨hy, none _ fx fun p ok => ?_⟩
    cases h : dn name (some e.2) p
    · rfl
    · have := incl name p ok (by rw [hx]; exact h)
      rw [hy, dn_none] at this; cases this
  | some y =>
    obtain ⟨w, run, k, sem⟩ := fieldC_diff ks fc hm fx (sB.fields name y hy)
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
      · have := incl name p ok (by rw [hx]; exact h)
        rw [hy] at this; simp [this]

/-- Walks that find no common field leave only intersections that drop their field or are checked empty. -/
theorem iter_disj_gen (K' : Nat) (B : List (Term × Term)) (Sm : Term) :
    ∀ es : List (Term × Term), (∀ e ∈ es, ∀ y d', K' ≤ d' → mapLookup B e.1 = some y → ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
        ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w Sm = .ok (boolAtom b))) →
    ∀ m, K' + es.length ≤ m →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") →
      ∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∃ d', K' ≤ d' ∧ ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w Sm = .ok (.atom "true")) := by
  intro es
  induction es with
  | nil => intro _ _ _ _ e m; simp at m
  | cons e rest ih =>
    intro calls m hm h
    have calls' := fun e' (me' : e' ∈ rest) => calls e' (List.mem_cons_of_mem _ me')
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    have hm' : K' + rest.length ≤ m := by simp at hm; omega
    have cont : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-iterator_non_disjoint_intersection?/3-fun-0-" 1
        #[Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]), .map B, Sm]) #[x] =
        (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) := by
      intro x
      rw [Erlang.program.«Elixir.Module.Types.Descr:-iterator_non_disjoint_intersection?/3-fun-0-/1».pure]
      simp [Elixir.Module.Types.Descr.«-iterator_non_disjoint_intersection?/3-fun-0-/4»]
    cases hb : mapLookup B e.1 with
    | none =>
      have hrest : (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") := by
        rw [← h]
        simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
        simp [getMapKeys_single, hb, cont]
      intro e' me' y hy
      rcases List.mem_cons.mp me' with rfl | me'
      · rw [hb] at hy; cases hy
      · exact ih calls' m hm' hrest e' me' y hy
    | some y₀ =>
      obtain ⟨w, rw', hb''⟩ := calls e List.mem_cons_self y₀ (m + 1) (by simp at hm; omega) hb
      have k₀ : kept (e.1, w) = Bool.false ∨
          Elixir.Module.Types.Descr.«empty_key?/3» (D (m + 1)) e.1 w Sm = .ok (boolAtom Bool.true) := by
        cases k : kept (e.1, w)
        · exact Or.inl rfl
        · right
          obtain ⟨b, hb'⟩ := hb'' k
          rw [hb']
          cases b
          · exfalso
            have ⟨z, b0⟩ : compareExact (fuel w (.integer 0)) w (.integer 0) ≠ .eq ∧ compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") ≠ .eq := by
              simpa [kept] using k
            revert h
            simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
            rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
            simp [getMapKeys_single, hb, rw', z, b0, hb',
              Erlang.erlang.«=:=/2», isMember, boolAtom]
          · rfl
      have hrest : (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") := by
        rw [← h]
        simp only [List.map, Term.list, next_cons, Lynx.Except.ok_bind]
        rw [Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3».eq_def]
        rcases k₀ with k | hb'
        · rcases dropped k with e₀ | e₀ <;> rw [e₀] at rw' <;>
            simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont,
              isMember]
        · by_cases dz : (compareExact (fuel w (.integer 0)) w (.integer 0) = .eq ∨ compareExact (fuel w (.atom "bdd_bot")) w (.atom "bdd_bot") = .eq)
          · rcases dz with dz | dz <;>
              simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont,
                isMember, dz]
          · simp only [not_or] at dz
            simp [getMapKeys_single, hb, rw', Erlang.erlang.«=:=/2», cont,
              isMember, dz.1, dz.2, hb', boolAtom]
      intro e' me' y hy
      rcases List.mem_cons.mp me' with rfl | me'
      · rw [hb] at hy; cases hy
        refine ⟨m + 1, by simp at hm; omega, w, rw', ?_⟩
        rcases k₀ with k | hb'
        · exact Or.inl k
        · exact Or.inr (by simpa [boolAtom] using hb')
      · exact ih calls' m hm' hrest e' me' y hy

theorem descrC_six {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) : (mapEntries X).length ≤ 6 :=
  entries_le_six fun q h => by
    obtain ⟨name, m, rfl⟩ := sX.keys q h
    rcases names_mem m with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Fields the disjointness walk leaves share no point. -/
theorem walk_disj_sem (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {S : List (Term × Term)}
    (hS : FS S) {N : Nat} (safe : SafeN N S)
    {X Y : List (Term × Term)} (sX : DescrC Fn TF LF MF X) (sY : DescrC Fn TF LF MF Y) (lX : lh (.map X) < N)
    (lY : lh (.map Y) < N)
    (walk : ∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∃ d', K + 1 ≤ d' ∧ ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
      (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map S) = .ok (.atom "true")))
    (name : String) (p : Point) (ok : PtOkC TV LV MV FV name p) :
    (dn name (mapLookup X (.atom name)) p && dn name (mapLookup Y (.atom name)) p) = Bool.false := by
  cases hx : mapLookup X (.atom name) with
  | none => simp [dn_none]
  | some x =>
    cases hy : mapLookup Y (.atom name) with
    | none => simp [dn_none]
    | some y =>
      obtain ⟨e, me, qe, ex⟩ := lookup_entry hx
      have e1 : e.1 = .atom name := by
        have := Lynx.Term.compareExact_eq_symm qe
        simpa using this
      obtain ⟨d', hd', w, run, out⟩ := walk e me y (by rw [e1]; exact hy)
      rw [e1, ex] at run
      rw [e1] at out
      obtain ⟨w', run', k, sem⟩ := fieldC_inter ks fc hd' (sX.fields name x hx) (sY.fields name y hy)
      rw [run] at run'; cases run'
      rw [← sem p ok]
      cases kw : kept (.atom name, w)
      · rw [keptO_false kw, dn_none]
      · rw [keptO_true kw]
        rcases out with out | out
        · rw [kw] at out; cases out
        · have fw := (k kw).1
          obtain ⟨b, rb, ex'⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) fw S (fun _ => hS)
          have hb : b = Bool.true := by
            have := rb.symm.trans (by simpa using out)
            cases b <;> simp_all [boolAtom]
          have lw := (k kw).2 hH
          have lx := lh_field_le hx
          have ly := lh_field_le hy
          exact (ex' N (by omega) safe).2 hb p ok

/-- `disjoint?/2` answers `true` only on types that share no point. -/
theorem descr_disj_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) (hS : FS [])
    {m : Nat} (hm : K + 7 ≤ m) {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B)
    (h : Elixir.Module.Types.Descr.«disjoint?/2» (D m) (.map A) (.map B) = .ok (.atom "true")) :
    ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y → ∀ e ∈ mapEntries X,
      ∀ y d', K + 1 ≤ d' → mapLookup Y e.1 = some y → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
          ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map []) = .ok (boolAtom b)) := by
    intro X Y sX sY e me y d' hd hy
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, -⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, fun kw => ?_⟩
    obtain ⟨b, rb, -⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) (k kw).1 [] (fun _ => hS)
    exact ⟨b, by simpa using rb⟩
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  unfold Elixir.Module.Types.Descr.«disjoint?/2» at h
  simp [getMapKeys_single, stA, stB] at h
  unfold Elixir.Module.Types.Descr.«non_disjoint_intersection?/2» at h
  rw [Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def] at h
  by_cases g : sa > sb
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen (K + 1) A (.map []) (mapEntries B) (calls sB sA) m
      (by have := descrC_six sB; omega) (not_true (by rw [bind_assoc]; exact h))
    intro name p ok
    rw [Bool.and_comm]
    exact walk_disj_sem ks fc hH hS (safeN_nil (max (lh (.map A)) (lh (.map B)) + 1)) sB sA (by omega) (by omega) walk name p ok
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h
    have walk := iter_disj_gen (K + 1) B (.map []) (mapEntries A) (calls sA sB) m
      (by have := descrC_six sA; omega) (not_true (by rw [bind_assoc]; exact h))
    exact walk_disj_sem ks fc hH hS (safeN_nil (max (lh (.map A)) (lh (.map B)) + 1)) sA sB (by omega) (by omega) walk

/-- Walks whose common fields all intersect into dropped or empty fields under the seen set find no common field. -/
theorem iter_disj_false_seen (K' : Nat) (B : List (Term × Term)) (Sm : Term) :
    ∀ es : List (Term × Term), (∀ e ∈ es, ∀ y, mapLookup B e.1 = some y → ∀ d', K' ≤ d' → ∃ w,
      Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
        (kept (e.1, w) = Bool.false ∨ Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w Sm = .ok (.atom "true"))) →
    ∀ m, K' + es.length ≤ m →
      (do
        let it ← Erlang.maps.«next/1» (Term.list (es.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
        Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) = .ok (.atom "false") := by
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
        #[Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]), .map B, Sm]) #[x] =
        (do
          let it ← Erlang.maps.«next/1» (Term.list (rest.map fun (e : Term × Term) => .tuple #[e.1, e.2]))
          Elixir.Module.Types.Descr.«iterator_non_disjoint_intersection?/3» (D m) it (.map B) Sm) := by
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

/-- `disjoint_seen?/3` answers `true` on static maps only when they share no point, when the seen BDDs are higher
than them. -/
theorem descr_sdisj_sound (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {S : List (Term × Term)}
    (hS : FS S) {N : Nat} (safe : SafeN N S) {m : Nat} (hm : K + 7 ≤ m) {A B : List (Term × Term)}
    (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B) (lA : lh (.map A) < N) (lB : lh (.map B) < N)
    (h : Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) (.map A) (.map B) (.map S) = .ok (.atom "true")) :
    ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y → ∀ e ∈ mapEntries X,
      ∀ y d', K + 1 ≤ d' → mapLookup Y e.1 = some y → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧ (kept (e.1, w) = Bool.true →
          ∃ b : Bool, Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map S) = .ok (boolAtom b)) := by
    intro X Y sX sY e me y d' hd hy
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, -⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, fun kw => ?_⟩
    obtain ⟨b, rb, -⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) (k kw).1 S (fun _ => hS)
    exact ⟨b, by simpa using rb⟩
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  rw [disj_seen_maps _ _ _ _ stA stB] at h
  have h' := not_true h
  rw [Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def] at h'
  by_cases g : sa > sb
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h'
    have walk := iter_disj_gen (K + 1) A (.map S) (mapEntries B) (calls sB sA) m
      (by have := descrC_six sB; omega) h'
    intro name p ok
    rw [Bool.and_comm]
    exact walk_disj_sem ks fc hH hS safe sB sA lB lA walk name p ok
  · simp [hsa, hsb, g, Erlang.maps.«iterator/1»] at h'
    have walk := iter_disj_gen (K + 1) B (.map S) (mapEntries A) (calls sA sB) m
      (by have := descrC_six sA; omega) h'
    exact walk_disj_sem ks fc hH hS safe sA sB lA lB walk

/-- `disjoint_seen?/3` answers `true` on static maps that share no point, when the seen BDDs are higher than them. -/
theorem descr_sdisj_complete (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H)
    {S : List (Term × Term)} (hS : FS S) {N : Nat} (safe : SafeN N S) {m : Nat} (hm : K + 7 ≤ m)
    {A B : List (Term × Term)} (sA : DescrC Fn TF LF MF A) (sB : DescrC Fn TF LF MF B) (lA : lh (.map A) < N)
    (lB : lh (.map B) < N)
    (disj : ∀ name p, PtOkC TV LV MV FV name p →
      (dn name (mapLookup A (.atom name)) p && dn name (mapLookup B (.atom name)) p) = Bool.false) :
    Elixir.Module.Types.Descr.«disjoint_seen?/3» (D m) (.map A) (.map B) (.map S) = .ok (.atom "true") := by
  have stA := sA.static
  have stB := sB.static
  have calls : ∀ {X Y : List (Term × Term)}, DescrC Fn TF LF MF X → DescrC Fn TF LF MF Y → lh (.map X) < N →
      lh (.map Y) < N → (∀ name p, PtOkC TV LV MV FV name p →
        (dn name (mapLookup X (.atom name)) p && dn name (mapLookup Y (.atom name)) p) = Bool.false) →
      ∀ e ∈ mapEntries X, ∀ y, mapLookup Y e.1 = some y → ∀ d', K + 1 ≤ d' → ∃ w,
        Elixir.Module.Types.Descr.«bare_intersection/3» (D d') e.1 e.2 y = .ok w ∧
          (kept (e.1, w) = Bool.false ∨
            Elixir.Module.Types.Descr.«empty_key?/3» (D d') e.1 w (.map S) = .ok (.atom "true")) := by
    intro X Y sX sY lX lY dXY e me y hy d' hd
    have hx := mapLookup_of_mem_mapEntries me
    obtain ⟨name, -, key⟩ := sX.keys e.1 (by simp [hx])
    rw [key] at hx hy ⊢
    obtain ⟨w, run, k, sem⟩ := fieldC_inter ks fc hd (sX.fields name e.2 hx) (sY.fields name y hy)
    refine ⟨w, run, ?_⟩
    cases kw : kept (.atom name, w)
    · exact Or.inl rfl
    · refine Or.inr ?_
      obtain ⟨b, rb, ex⟩ := fieldC_empty ks fc hH (show K ≤ d' by omega) (k kw).1 S (fun _ => hS)
      have lw := (k kw).2 hH
      have lx := lh_field_le hx
      have ly := lh_field_le hy
      have hb := (ex N (by omega) safe).1 fun p ok => by
        have := sem p ok
        rw [keptO_true kw] at this
        rw [this, ← hx, ← hy]
        exact dXY name p ok
      subst hb
      simpa using rb
  obtain ⟨sa, hsa⟩ : ∃ sa : Int, Erlang.erlang.«map_size/1» (.map A) = .ok (.integer sa) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ sb : Int, Erlang.erlang.«map_size/1» (.map B) = .ok (.integer sb) :=
    ⟨_, by simp [Erlang.erlang.«map_size/1»]; rfl⟩
  rw [disj_seen_maps _ _ _ _ stA stB, Elixir.Module.Types.Descr.«non_disjoint_intersection?/3».eq_def]
  by_cases g : sa > sb
  · have walk := iter_disj_false_seen (K + 1) A (.map S) (mapEntries B)
      (calls sB sA lB lA fun name p ok => by rw [Bool.and_comm]; exact disj name p ok) m
      (by have := descrC_six sB; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [walk]
    rfl
  · have walk := iter_disj_false_seen (K + 1) B (.map S) (mapEntries A) (calls sA sB lA lB disj) m
      (by have := descrC_six sA; omega)
    simp [hsa, hsb, g, Erlang.maps.«iterator/1»]
    rw [walk]
    rfl

end

end Elixir.STTDescrProofsTest.Nest
