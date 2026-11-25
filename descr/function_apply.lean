/-! Static function application: `fun_apply/2` on static types whose function types are arrows. -/

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

-- The mode of applications, whether the module is static: static types apply alike in both modes.
variable {s : Term}

theorem filter_list (d : Dispatcher) (mo nm : String) (caps : Array Term) (res : Term → Bool) (l : List Term)
    (hf : ∀ x ∈ l, d.pure (.function false mo nm 1 caps) #[x] = .ok (boolAtom (res x))) :
    Erlang.lists.«filter/2» d (.function false mo nm 1 caps) (Term.list l) = .ok (Term.list (l.filter res)) := by
  have loop : ∀ l' : List Term, (∀ x ∈ l', d.pure (.function false mo nm 1 caps) #[x] = .ok (boolAtom (res x))) →
      Erlang.lists.«-filter/2-lc$^0/1-/2» d (Term.list l') (.function false mo nm 1 caps) = .ok (Term.list (l'.filter res)) := by
    intro l'
    induction l' with
    | nil => intro _; simp [Erlang.lists.«-filter/2-lc$^0/1-/2», Term.list]
    | cons x xs ih =>
      intro hf
      rw [Erlang.lists.«-filter/2-lc$^0/1-/2».eq_def]
      have tail := ih fun y m => hf y (List.mem_cons_of_mem _ m)
      cases h : res x <;> simp [Term.list, hf x List.mem_cons_self, h, boolAtom] at tail ⊢ <;>
        simp [tail]
  simp [Erlang.lists.«filter/2», Erlang.erlang.«is_function/2», loop l hf]

/-- The answer of a `filtermap/2` callback: `false`, or `{true, value}`. -/
def fmAns : Option Term → Term
  | none => .atom "false"
  | some y => .tuple #[.atom "true", y]

theorem filtermap_list (d : Dispatcher) (mo nm : String) (caps : Array Term) (o : Term → Option Term)
    (l : List Term) (hf : ∀ x ∈ l, d.pure (.function false mo nm 1 caps) #[x] = .ok (fmAns (o x))) :
    Erlang.lists.«filtermap/2» d (.function false mo nm 1 caps) (Term.list l) = .ok (Term.list (l.filterMap o)) := by
  have loop : ∀ l' : List Term, (∀ x ∈ l', d.pure (.function false mo nm 1 caps) #[x] = .ok (fmAns (o x))) →
      Erlang.lists.«filtermap_1/2» d (.function false mo nm 1 caps) (Term.list l') = .ok (Term.list (l'.filterMap o)) := by
    intro l'
    induction l' with
    | nil => intro _; simp [Erlang.lists.«filtermap_1/2», Term.list]
    | cons x xs ih =>
      intro hf
      rw [Erlang.lists.«filtermap_1/2».eq_def]
      have tail := ih fun y m => hf y (List.mem_cons_of_mem _ m)
      cases h : o x <;> simp [Term.list, hf x List.mem_cons_self, h, fmAns] at tail ⊢ <;>
        simp [tail]
  simp [Erlang.lists.«filtermap/2», Erlang.erlang.«is_function/2», loop l hf]


section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {K : Nat} {seen : Term}

/-- Arrow lists whose arrows allow every row the arrows of the first one allow. -/
def ArrSub (den : Term → V → Prop) (q q' : List (Term × List Term × Term)) : Prop :=
  ∀ r : FunSem.Row V, (∀ p ∈ semP den q, FunSem.Allows p r) → ∀ p ∈ semP den q', FunSem.Allows p r

theorem arrSub_refl (q : List (Term × List Term × Term)) : ArrSub den q q := fun _ h => h

theorem arrSub_trans {a b c : List (Term × List Term × Term)} (h₁ : ArrSub den a b) (h₂ : ArrSub den b c) :
    ArrSub den a c := fun r h => h₂ r (h₁ r h)

/-- Argument types included in others, position by position. -/
def ArgsIn (den : Term → V → Prop) : List Term → List Term → Prop
  | a :: as, b :: bs => (∀ v, den a v → den b v) ∧ ArgsIn den as bs
  | _, _ => True

theorem args_subtype_run (fe : FunElem E den K seen) {m : Nat} (hm : K ≤ m) :
    ∀ (as bs : List Term), (∀ a ∈ as, E a) → (∀ b ∈ bs, E b) →
      Elixir.Module.Types.Descr.«args_subtype?/2» (D m) (Term.list as) (Term.list bs) =
        .ok (boolAtom (bp (ArgsIn den as bs)))
  | a :: as, b :: bs, ha, hb => by
    rw [Elixir.Module.Types.Descr.«args_subtype?/2».eq_def]
    have rest := args_subtype_run fe hm as bs (fun x mx => ha x (List.mem_cons_of_mem _ mx))
      (fun x mx => hb x (List.mem_cons_of_mem _ mx))
    simp only at rest ⊢
    rw [fe.sub (ha a List.mem_cons_self) (hb b List.mem_cons_self) m hm]
    by_cases h : ∀ v, den a v → den b v
    · rw [bp_true.mpr h, rest]
      by_cases h' : ArgsIn den as bs
      · rw [bp_true.mpr h', bp_true.mpr (show ArgsIn den (a :: as) (b :: bs) from ⟨h, h'⟩)]; rfl
      · rw [bp_false.mpr h', bp_false.mpr (show ¬ArgsIn den (a :: as) (b :: bs) from fun h'' => h' h''.2)]; rfl
    · rw [bp_false.mpr h, bp_false.mpr (show ¬ArgsIn den (a :: as) (b :: bs) from fun h'' => h h''.1)]; rfl
  | [], bs, _, _ => by
    rw [Elixir.Module.Types.Descr.«args_subtype?/2».eq_def]
    rw [bp_true.mpr (show ArgsIn den [] bs by cases bs <;> trivial)]
    cases bs <;> rfl
  | a :: as, [], _, _ => by
    rw [Elixir.Module.Types.Descr.«args_subtype?/2».eq_def, bp_true.mpr (show ArgsIn den (a :: as) [] from trivial)]
    rfl

theorem inDom_argsIn : ∀ (as bs : List Term) (x : List (Option V)), as.length = bs.length → ArgsIn den as bs →
    FunSem.InDom (as.map den) x → FunSem.InDom (bs.map den) x
  | a :: as, b :: bs, o :: os, len, ⟨h, hs⟩, ⟨ho, hos⟩ => by
    refine ⟨?_, inDom_argsIn as bs os (by simpa using len) hs hos⟩
    cases o with
    | none => exact ho
    | some v => exact h v ho
  | [], [], _, _, _, h => by cases ‹List (Option V)› <;> simp_all [FunSem.InDom]
  | [], _ :: _, _, len, _, _ => by simp at len
  | _ :: _, [], _, len, _, _ => by simp at len
  | _ :: _, _ :: _, [], _, _, h => by simp [FunSem.InDom] at h

/-- Whether an arrow is in another one: its return is in the other's, whose arguments are in its own. -/
noncomputable def arrowSubB (den : Term → V → Prop) (p p' : Term × List Term × Term) : Bool :=
  bp ((∀ v, den p.2.2 v → den p'.2.2 v) ∧ ArgsIn den p'.2.1 p.2.1)

/-- `arrow_subtype?/4` checks that an arrow is in another one. -/
theorem arrow_subtype_run (fe : FunElem E den K seen) {m : Nat} (hm : K ≤ m) {n : Nat}
    (p p' : Term × List Term × Term) (hp : PosOk E n [p]) (hp' : PosOk E n [p']) :
    Elixir.Module.Types.Descr.«arrow_subtype?/4» (D m) (Term.list p.2.1) p.2.2 (Term.list p'.2.1) p'.2.2 =
      .ok (boolAtom (arrowSubB den p p')) := by
  obtain ⟨ha, hr, hl⟩ := hp p List.mem_cons_self
  obtain ⟨ha', hr', hl'⟩ := hp' p' List.mem_cons_self
  unfold Elixir.Module.Types.Descr.«arrow_subtype?/4»
  rw [fe.sub hr hr' m hm, args_subtype_run fe hm _ _ ha' ha]
  by_cases h₁ : ∀ v, den p.2.2 v → den p'.2.2 v
  · rw [bp_true.mpr h₁]
    by_cases h₂ : ArgsIn den p'.2.1 p.2.1
    · rw [bp_true.mpr h₂, show arrowSubB den p p' = Bool.true from bp_true.mpr ⟨h₁, h₂⟩]; rfl
    · rw [bp_false.mpr h₂, show arrowSubB den p p' = Bool.false from bp_false.mpr fun h => h₂ h.2]; rfl
  · rw [bp_false.mpr h₁, show arrowSubB den p p' = Bool.false from bp_false.mpr fun h => h₁ h.1]; rfl

theorem arrowSubB_sub {n : Nat} {p p' : Term × List Term × Term} (hp : PosOk E n [p]) (hp' : PosOk E n [p'])
    (h : arrowSubB den p p' = Bool.true) : ArrSub den [p] [p'] := by
  obtain ⟨h₁, h₂⟩ := bp_true.mp h
  intro r all q mq
  simp only [semP, List.map_cons, List.map_nil, List.mem_singleton] at mq all
  subst mq
  intro hd
  have len : p'.2.1.length = p.2.1.length := by
    rw [(hp' p' List.mem_cons_self).2.2, (hp p List.mem_cons_self).2.2]
  obtain ⟨y, ey, hy⟩ := all _ rfl (inDom_argsIn _ _ _ len h₂ hd)
  exact ⟨y, ey, h₁ y hy⟩

/-- Whether the arrows `w` are a single arrow that contains the arrow `p`. -/
noncomputable def supB (den : Term → V → Prop) (p : Term × List Term × Term) (x : Term) : Bool :=
  bp (∃ p', x = encP [p'] ∧ arrowSubB den p p' = Bool.true)

theorem supB_run (fe : FunElem E den K seen) {m : Nat} (hm : K ≤ m) {n : Nat} (p : Term × List Term × Term)
    (hp : PosOk E n [p]) (w : List (Term × List Term × Term)) (hw : PosOk E n w) :
    (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-fun_eliminate_unions/2-fun-0-" 1
      #[Term.list p.2.1, p.2.2]) #[encP w] = .ok (boolAtom (supB den p (encP w))) := by
  rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_eliminate_unions/2-fun-0-/1».pure]
  match w, hw with
  | [], _ =>
    rw [show supB den p (encP []) = Bool.false from bp_false.mpr fun ⟨p', e, _⟩ => by
      simp [encP, Term.list] at e]
    simp [encP, Term.list, Elixir.Module.Types.Descr.«-fun_eliminate_unions/2-fun-0-/3», boolAtom]
  | [p'], hw =>
    have run := arrow_subtype_run fe hm p p' hp hw
    rw [show supB den p (encP [p']) = arrowSubB den p p' from by
      unfold supB
      cases h : arrowSubB den p p'
      · exact bp_false.mpr fun ⟨p'', e, h'⟩ => by
          have e' := encP_inj e
          simp only [List.cons.injEq, and_true] at e'
          subst e'; simp_all
      · exact bp_true.mpr ⟨p', rfl, h⟩]
    simpa [encP, Term.list, Elixir.Module.Types.Descr.«-fun_eliminate_unions/2-fun-0-/3»] using run
  | p₁ :: p₂ :: w', _ =>
    rw [show supB den p (encP (p₁ :: p₂ :: w')) = Bool.false from bp_false.mpr fun ⟨p', e, _⟩ => by
      have := encP_inj e; simp at this]
    simp [encP, Term.list, Elixir.Module.Types.Descr.«-fun_eliminate_unions/2-fun-0-/3», boolAtom]

theorem supB_sub {n : Nat} {p : Term × List Term × Term} (hp : PosOk E n [p]) {w : List (Term × List Term × Term)}
    (hw : PosOk E n w) (h : supB den p (encP w) = Bool.true) : ArrSub den [p] w := by
  obtain ⟨p', e, h'⟩ := bp_true.mp h
  obtain rfl := encP_inj e
  exact arrowSubB_sub hp hw h'

/-- `fun_eliminate_unions/2` drops single arrows that another line contains: what it keeps comes from its lines
and its accumulator, and contains each of them. -/
theorem eliminate_run (fe : FunElem E den K seen) {n : Nat} :
    ∀ (ins acc : List (List (Term × List Term × Term))), (∀ q ∈ ins, PosOk E n q) → (∀ q ∈ acc, PosOk E n q) →
      ∃ out : List (List (Term × List Term × Term)), (∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«fun_eliminate_unions/2» (D m) (Term.list (ins.map encP))
          (Term.list (acc.map encP)) = .ok (Term.list (out.map encP))) ∧
        (∀ q ∈ out, q ∈ ins ∨ q ∈ acc) ∧ ∀ q ∈ ins ++ acc, ∃ q' ∈ out, ArrSub den q q'
  | [], acc, _, _ => ⟨acc, fun m _ => by
      rw [Elixir.Module.Types.Descr.«fun_eliminate_unions/2».eq_def]; simp [Term.list],
      fun q mq => Or.inr mq, fun q mq => ⟨q, by simpa using mq, arrSub_refl q⟩⟩
  | P :: ins, acc, hins, hacc => by
    have hP := hins P List.mem_cons_self
    have hins' : ∀ q ∈ ins, PosOk E n q := fun q mq => hins q (List.mem_cons_of_mem _ mq)
    -- Keeping the line.
    have keep : ∃ out : List (List (Term × List Term × Term)), (∀ m, K + 1 ≤ m →
          Elixir.Module.Types.Descr.«fun_eliminate_unions/2» (D m) (Term.list (ins.map encP))
            (Term.list ((P :: acc).map encP)) = .ok (Term.list (out.map encP))) ∧
          (∀ q ∈ out, q ∈ P :: ins ∨ q ∈ acc) ∧ ∀ q ∈ (P :: ins) ++ acc, ∃ q' ∈ out, ArrSub den q q' := by
      obtain ⟨out, run, from', sup⟩ := eliminate_run fe ins (P :: acc) hins' (fun q mq => by
        rcases List.mem_cons.mp mq with rfl | mq
        · exact hP
        · exact hacc q mq)
      refine ⟨out, run, fun q mq => ?_, fun q mq => sup q ?_⟩
      · rcases from' q mq with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl List.mem_cons_self
          · exact Or.inr h
      · simp only [List.cons_append, List.mem_cons, List.mem_append] at mq ⊢
        rcases mq with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    match P, hP with
    | [p], hP =>
      let res := supB den p
      have each : ∀ (l : List (List (Term × List Term × Term))), (∀ q ∈ l, PosOk E n q) → ∀ m, K ≤ m →
          ∀ x ∈ l.map encP, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-fun_eliminate_unions/2-fun-0-" 1
            #[Term.list p.2.1, p.2.2]) #[x] = .ok (boolAtom (res x)) := by
        intro l hl m hm x mx
        obtain ⟨w, mw, rfl⟩ := List.mem_map.mp mx
        exact supB_run fe hm p hP w (hl w mw)
      by_cases found : ((ins.map encP).any res || (acc.map encP).any res) = Bool.true
      · obtain ⟨out, run, from', sup⟩ := eliminate_run fe ins acc hins' hacc
        refine ⟨out, fun m hm => ?_, fun q mq => ?_, fun q mq => ?_⟩
        · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
          rw [Elixir.Module.Types.Descr.«fun_eliminate_unions/2».eq_def]
          have a₁ := any_list (D (m' + 1)) _ _ _ res _ (each ins hins' m' hm')
          have a₂ := any_list (D (m' + 1)) _ _ _ res _ (each acc hacc m' hm')
          simp only [encP, List.map_cons, List.map_nil, Term.list] at a₁ a₂ run ⊢
          rw [Bool.or_eq_true] at found
          rcases found with f | f
          · simp [a₁, f, boolAtom, Lynx.Except.orElse, run (m' + 1) hm]
          · cases f' : (ins.map encP).any res <;> simp_all [boolAtom, Lynx.Except.orElse]
        · rcases from' q mq with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
        · simp only [List.cons_append, List.mem_cons] at mq
          rcases mq with rfl | mq
          · rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true] at found
            obtain ⟨x, mx, hx⟩ : ∃ x ∈ (ins ++ acc).map encP, res x = Bool.true := by
              rcases found with ⟨x, mx, hx⟩ | ⟨x, mx, hx⟩
              · exact ⟨x, by simp only [List.map_append, List.mem_append]; exact Or.inl mx, hx⟩
              · exact ⟨x, by simp only [List.map_append, List.mem_append]; exact Or.inr mx, hx⟩
            obtain ⟨w, mw, rfl⟩ := List.mem_map.mp mx
            have hw : PosOk E n w := by
              rcases List.mem_append.mp mw with h | h
              · exact hins' w h
              · exact hacc w h
            obtain ⟨q', mq', s'⟩ := sup w mw
            exact ⟨q', mq', arrSub_trans (supB_sub hP hw hx) s'⟩
          · exact sup q mq
      · obtain ⟨out, run, from', sup⟩ := keep
        refine ⟨out, fun m hm => ?_, from', sup⟩
        obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Elixir.Module.Types.Descr.«fun_eliminate_unions/2».eq_def]
        have a₁ := any_list (D (m' + 1)) _ _ _ res _ (each ins hins' m' hm')
        have a₂ := any_list (D (m' + 1)) _ _ _ res _ (each acc hacc m' hm')
        have r := run (m' + 1) hm
        simp only [encP, List.map_cons, List.map_nil, Term.list] at a₁ a₂ r ⊢
        rw [Bool.or_eq_true, not_or] at found
        simp only [Bool.not_eq_true] at found
        simp [a₁, a₂, found.1, found.2, boolAtom, Lynx.Except.orElse, r]
    | [], _ =>
      obtain ⟨out, run, from', sup⟩ := keep
      refine ⟨out, fun m hm => ?_, from', sup⟩
      rw [Elixir.Module.Types.Descr.«fun_eliminate_unions/2».eq_def]
      simpa [encP, Term.list] using run m hm
    | p₁ :: p₂ :: P', _ =>
      obtain ⟨out, run, from', sup⟩ := keep
      refine ⟨out, fun m hm => ?_, from', sup⟩
      rw [Elixir.Module.Types.Descr.«fun_eliminate_unions/2».eq_def]
      simpa [encP, Term.list] using run m hm

/-- A line of positive and negative arrows, as `bdd_to_dnf/4` builds it. -/
abbrev encL (l : List (Term × List Term × Term) × List (Term × List Term × Term)) : Term :=
  .tuple #[encP l.1, encP l.2]

theorem posOk_mono {E' : Term → Prop} (h : ∀ a, E a → E' a) {n : Nat} {P : List (Term × List Term × Term)}
    (hP : PosOk E n P) : PosOk E' n P := fun p mp =>
  let ⟨ha, hr, hl⟩ := hP p mp
  ⟨fun u mu => h u (ha u mu), h _ hr, hl⟩

/-- The lines of a BDD of arrows: a function satisfies the BDD exactly when it satisfies one of them. -/
theorem bdd_sat_lines {E₀ : Term → Prop} (cg : DenCongr E₀ den) (hE : ∀ a, E a → E₀ a) {n : Nat}
    {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t) {b : Term} (wb : Bdd L b) :
    ∃ ls : List (List (Term × List Term × Term) × List (Term × List Term × Term)),
      Elixir.Module.Types.Descr.«bdd_to_dnf/1» b = .ok (Term.list (ls.map encL)) ∧
      (∀ l ∈ ls, PosOk E n l.1 ∧ PosOk E n l.2) ∧
      ∀ g : List (FunSem.Row V), eval (valF E₀ den g) b = Bool.true ↔ ∃ l ∈ ls,
        (∀ p ∈ semP den l.1, ∀ r ∈ g, FunSem.Allows p r) ∧ ∀ q ∈ semP den l.2, ¬∀ r ∈ g, FunSem.Allows q r := by
  obtain ⟨lines, run, hlines⟩ := dnf_lines wb L (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  obtain ⟨ls, rfl, hls⟩ := lines_enc (E := E) hL lines hlines
  obtain ⟨lines₁, run₁, sat⟩ := dnf_sat wb [] [] []
  obtain ⟨lines₂, run₂, -, cover⟩ := nl_dnf_cover wb [] [] []
  rw [run] at run₁ run₂
  have e₁ := list_inj (Except.ok.inj run₁)
  have e₂ := list_inj (Except.ok.inj run₂)
  rw [← e₁] at sat
  rw [← e₂] at cover
  refine ⟨ls, by simpa [Elixir.Module.Types.Descr.«bdd_to_dnf/1»] using run, fun l ml => ⟨(hls l ml).1, (hls l ml).2.1⟩,
    fun g => ⟨fun h => ?_, fun ⟨l, ml, hl⟩ => ?_⟩⟩
  · obtain ⟨t, mt, lt⟩ := cover _ (by simp) (by simp) h
    obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mt
    exact ⟨l, ml, (lineSat_valF cg g l.1 l.2 (posOk_mono hE (hls l ml).1) (posOk_mono hE (hls l ml).2.1)).mp lt⟩
  · have lt := (lineSat_valF cg g l.1 l.2 (posOk_mono hE (hls l ml).1) (posOk_mono hE (hls l ml).2.1)).mpr hl
    rcases sat _ (List.mem_map.mpr ⟨l, ml, rfl⟩) with m | sat
    · simp at m
    · exact (sat _ lt).2.2

theorem encL_inj {l l' : List (Term × List Term × Term) × List (Term × List Term × Term)} (h : encL l = encL l') :
    l = l' := by
  simp only [encL, encP] at h
  obtain ⟨e₁, e₂⟩ := line_inj h
  have h₁ := encP_inj (P := l.1) (P' := l'.1) (by simp only [encP]; rw [e₁])
  have h₂ := encP_inj (P := l.2) (P' := l'.2) (by simp only [encP]; rw [e₂])
  exact Prod.ext h₁ h₂

end

section
variable {V : Type} {E Dm : Term → Prop} {den : Term → V → Prop} {dden : Term → List V → Prop} {K : Nat}

/-- Whether a line of arrows is not empty. -/
noncomputable def liveB (den : Term → V → Prop) (n : Nat) (x : Term) : Bool :=
  bp (∃ l : List (Term × List Term × Term) × List (Term × List Term × Term), x = encL l ∧
    ¬FunSem.LineEmpty n (semP den l.1) (semP den l.2))

/-- The top arrow of arity `n`, from `n` arguments of `none()` to `term()`, with key `k`. -/
def topA (k : Int) (n : Nat) : Term × List Term × Term := (.integer k, List.replicate n (.map []), .atom "term")

/-- The positive arrows `fun_bdd_to_pos_dnf/2` applies for a line: the top arrow when it has none. -/
def posOf (k : Int) (n : Nat) : List (Term × List Term × Term) → List (Term × List Term × Term)
  | [] => [topA k n]
  | P => P

theorem posOf_cons (k : Int) (n : Nat) (p : Term × List Term × Term) (P : List (Term × List Term × Term)) :
    posOf k n (p :: P) = p :: P := rfl

theorem semP_top (fe : FunElem E den K (.map [])) (k : Int) (n : Nat) : semP den [topA k n] = [FunSem.top n] := by
  simp only [semP, List.map_cons, List.map_nil, FunSem.top, topA, List.map_replicate]
  have e₁ : den (.map []) = fun _ => False := funext fun v => propext (iff_false_intro (fe.none.2 v))
  have e₂ : den (.atom "term") = fun _ => True := funext fun v => propext (iff_true_intro (fe.term.2 v))
  rw [e₁, e₂]

theorem topA_ok (fe : FunElem E den K (.map [])) (k : Int) (n : Nat) : PosOk E n [topA k n] := by
  intro p mp
  rw [List.mem_singleton.mp mp]
  exact ⟨fun u mu => by rw [List.eq_of_mem_replicate mu]; exact fe.none.1, fe.term.1, by simp [topA]⟩

/-- `fun_bdd_to_pos_dnf/2` on BDDs other than the top one: the positive arrows of the non-empty lines, or the top
arrow for lines without any, without the single arrows other lines contain. Each function of the BDD is in one of
them, and each comes from a non-empty line of the BDD, whose functions the BDD holds. -/
theorem pos_dnf_run (fe : FunElem E den K (.map [])) (fd : FunDom Dm E den dden K (.map [])) {E₀ : Term → Prop}
    (cg : DenCongr E₀ den) (hE : ∀ a, E a → E₀ a) {n : Nat} {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t)
    {b : Term} (wb : Bdd L b) (ntop : b ≠ .atom "bdd_top") :
    ∃ Q : List (List (Term × List Term × Term)),
      (∀ m, K + 5 ≤ m → Elixir.Module.Types.Descr.«fun_bdd_to_pos_dnf/2» (D m) (.integer n) b =
        .ok (Term.list (Q.map encP))) ∧ (∀ q ∈ Q, PosOk E n q) ∧ (∀ q ∈ Q, q ≠ []) ∧
      (∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → eval (valF E₀ den g) b = Bool.true →
        ∃ q ∈ Q, ∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r) ∧
      ∀ q ∈ Q, ∃ N, PosOk E n N ∧ ¬FunSem.LineEmpty n (semP den q) (semP den N) ∧
        ∀ g : List (FunSem.Row V), (∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r) →
          (∀ q' ∈ semP den N, ¬∀ r ∈ g, FunSem.Allows q' r) → eval (valF E₀ den g) b = Bool.true := by
  obtain ⟨ls, dnf, hls, sem⟩ := bdd_sat_lines cg hE hL wb
  obtain ⟨k, leaf⟩ := leaf_fun (List.replicate n (.map []))
  let kept := ls.filter fun l => liveB den n (encL l)
  have hkept : ∀ l ∈ kept, l ∈ ls ∧ ¬FunSem.LineEmpty n (semP den l.1) (semP den l.2) := by
    intro l ml
    obtain ⟨ml, h⟩ := List.mem_filter.mp ml
    obtain ⟨l', e, h'⟩ := bp_true.mp h
    obtain rfl := encL_inj e
    exact ⟨ml, h'⟩
  have live : ∀ l ∈ ls, ¬FunSem.LineEmpty n (semP den l.1) (semP den l.2) → l ∈ kept := fun l ml h =>
    List.mem_filter.mpr ⟨ml, bp_true.mpr ⟨l, rfl, h⟩⟩
  have posOk : ∀ l ∈ ls, PosOk E n (posOf k n l.1) := by
    intro l ml
    cases h : l.1 with
    | nil => exact topA_ok fe k n
    | cons p P => rw [posOf_cons, ← h]; exact (hls l ml).1
  have posSem : ∀ l : List (Term × List Term × Term) × List (Term × List Term × Term),
      ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) →
      (∀ p ∈ semP den l.1, ∀ r ∈ g, FunSem.Allows p r) → ∀ p ∈ semP den (posOf k n l.1), ∀ r ∈ g, FunSem.Allows p r := by
    intro l g vg allP
    cases h : l.1 with
    | nil =>
      simp only [posOf]
      rw [semP_top fe]
      intro p mp r mr
      rw [List.mem_singleton.mp mp]
      exact FunSem.allows_top (vg r mr)
    | cons p P => rw [posOf_cons, ← h]; exact allP
  obtain ⟨out, run, from', sup⟩ := eliminate_run fe (n := n) (kept.map fun l => posOf k n l.1) [] (fun q mq => by
    obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mq
    exact posOk l (hkept l ml).1) (by simp)
  have filt : ∀ m, K + 3 ≤ m → Erlang.lists.«filter/2» (D (m + 1))
      (.function false "Elixir.Module.Types.Descr" "-fun_bdd_to_dnf/1-fun-0-" 1 #[]) (Term.list (ls.map encL)) =
      .ok (Term.list (kept.map encL)) := by
    intro m hm
    rw [filter_list _ _ _ _ (liveB den n) _ fun x mx => ?_, List.filter_map]
    · rfl
    obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mx
    obtain ⟨b', rb, sb⟩ := fun_line_sem fe fd n l.1 l.2 (hls l ml).1 (hls l ml).2
    rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_bdd_to_dnf/1-fun-0-/1».pure]
    have e : liveB den n (encL l) = !b' := by
      unfold liveB
      cases b'
      · exact bp_true.mpr ⟨l, rfl, fun h => by have := sb.mpr h; cases this⟩
      · exact bp_false.mpr fun ⟨l', e, h⟩ => by
          obtain rfl := encL_inj e
          exact h (sb.mp rfl)
    simp only [Elixir.Module.Types.Descr.«-fun_bdd_to_dnf/1-fun-0-/1», Elixir.Module.Types.Descr.«fun_line_empty?/2»]
    rw [rb m hm, e]
    cases b' <;> rfl
  refine ⟨out, fun m hm => ?_, fun q mq => ?_, fun q mq => ?_, fun g vg hg => ?_, fun q mq => ?_⟩
  · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    rw [Elixir.Module.Types.Descr.«fun_bdd_to_pos_dnf/2».eq_def]
    split
    · exact absurd rfl ntop
    have mp : Erlang.lists.«map/2» (D (m' + 1))
        (.function false "Elixir.Module.Types.Descr" "-fun_bdd_to_pos_dnf/2-fun-0-" 1 #[.integer n])
        (Term.list (kept.map encL)) = .ok (Term.list ((kept.map fun l => posOf k n l.1).map encP)) := by
      rw [map_list _ _ _ _ (fun x => match x with
          | .tuple ⟨[.nil, _]⟩ => Term.list [.tuple #[.integer k, Term.list (List.replicate n (.map [])), .atom "term"]]
          | .tuple ⟨[p, _]⟩ => p
          | _ => .nil) _ fun x mx => ?_]
      · simp only [List.map_map]
        refine congrArg (fun l => Except.ok (Term.list l)) (List.map_congr_left fun l _ => ?_)
        simp only [Function.comp]
        cases h : l.1 with
        | nil => simp [encL, h, encP, posOf, topA, Term.list]
        | cons p P => simp [encL, h, encP, posOf, Term.list]
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp mx
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_bdd_to_pos_dnf/2-fun-0-/1».pure]
      cases h : l.1 with
      | nil => simp [Elixir.Module.Types.Descr.«-fun_bdd_to_pos_dnf/2-fun-0-/2», encL, h, encP, Term.list, dup_nat, leaf]
      | cons p P => simp [Elixir.Module.Types.Descr.«-fun_bdd_to_pos_dnf/2-fun-0-/2», encL, h, encP, Term.list]
    have r := run (m' + 1) (by omega)
    simp only [List.map_nil] at r
    simp only [Elixir.Module.Types.Descr.«fun_bdd_to_dnf/1», dnf, Lynx.Except.ok_bind]
    simp [filt m' (by omega), mp]
    simpa using r
  · rcases from' q mq with h | h
    · obtain ⟨l, ml, rfl⟩ := List.mem_map.mp h
      exact posOk l (hkept l ml).1
    · simp at h
  · rcases from' q mq with h | h
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp h
      cases l.1 with
      | nil => simp [posOf]
      | cons p P => simp [posOf_cons]
    · simp at h
  · obtain ⟨l, ml, allP, noN⟩ := (sem g).mp hg
    have lv : ¬FunSem.LineEmpty n (semP den l.1) (semP den l.2) := fun h => by
      obtain ⟨q, mq, hq⟩ := h g vg allP
      exact noN q mq hq
    obtain ⟨q', mq', s'⟩ := sup (posOf k n l.1) (List.mem_append_left _ (List.mem_map.mpr ⟨l, live l ml lv, rfl⟩))
    have all' := posSem l g vg allP
    exact ⟨q', mq', fun p mp r mr => s' r (fun p' mp' => all' p' mp' r mr) p mp⟩
  · rcases from' q mq with h | h
    · obtain ⟨l, ml, rfl⟩ := List.mem_map.mp h
      obtain ⟨ml', lv⟩ := hkept l ml
      refine ⟨l.2, (hls l ml').2, ?_, fun g allP noN => (sem g).mpr ⟨l, ml', ?_, noN⟩⟩
      · cases h : l.1 with
        | nil =>
          rw [h] at lv
          simp only [posOf]
          rw [semP_top fe, ← FunSem.lineEmpty_top]
          simpa [semP] using lv
        | cons p P => rw [posOf_cons, ← h]; exact lv
      · cases h : l.1 with
        | nil => simp [semP]
        | cons p P => rw [h, posOf_cons] at allP; exact allP
    · simp at h

/-- No function of arity `n` satisfies a line exactly when the line is empty. -/
theorem lineEmpty_iff_none (n : Nat) (P N : List (FunSem.Arrow V)) :
    FunSem.LineEmpty n P N ↔ ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) →
      ¬((∀ p ∈ P, ∀ r ∈ g, FunSem.Allows p r) ∧ ∀ q ∈ N, ¬∀ r ∈ g, FunSem.Allows q r) := by
  constructor
  · intro h g vg ⟨allP, noN⟩
    obtain ⟨q, mq, hq⟩ := h g vg allP
    exact noN q mq hq
  · intro h g vg allP
    apply Classical.byContradiction
    intro hn
    exact h g vg ⟨allP, fun q mq hq => hn ⟨q, mq, hq⟩⟩

/-- Whether a BDD of arrows of arity `n` holds no function of arity `n`. -/
noncomputable def deadB (E₀ : Term → Prop) (den : Term → V → Prop) (n : Nat) (b : Term) : Bool :=
  bp (∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → eval (valF E₀ den g) b = Bool.false)

/-- The lines of a BDD of arrows are all empty exactly when it holds no function. -/
theorem bdd_dead_run (fe : FunElem E den K (.map [])) (fd : FunDom Dm E den dden K (.map [])) {E₀ : Term → Prop}
    (cg : DenCongr E₀ den) (hE : ∀ a, E a → E₀ a) {n : Nat} {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t)
    {b : Term} (wb : Bdd L b) {m : Nat} (hm : K + 3 ≤ m) :
    ∃ lines, Elixir.Module.Types.Descr.«bdd_to_dnf/1» b = .ok lines ∧
      Erlang.lists.«all/2» (D (m + 1)) (.function false "Elixir.Module.Types.Descr" "-bdds_non_empty_arities/1-fun-0-" 1 #[])
        lines = .ok (boolAtom (deadB E₀ den n b)) := by
  obtain ⟨ls, dnf, hls, sem⟩ := bdd_sat_lines cg hE hL wb
  let res : Term → Bool := fun x => bp (∃ l : List (Term × List Term × Term) × List (Term × List Term × Term),
    x = encL l ∧ FunSem.LineEmpty n (semP den l.1) (semP den l.2))
  have all := all_list (D (m + 1)) _ _ _ res (ls.map encL) fun x mx => by
    obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mx
    obtain ⟨b', rb, sb⟩ := fun_line_sem fe fd n l.1 l.2 (hls l ml).1 (hls l ml).2
    rw [Erlang.program.«Elixir.Module.Types.Descr:-bdds_non_empty_arities/1-fun-0-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-bdds_non_empty_arities/1-fun-0-/1»,
      Elixir.Module.Types.Descr.«fun_line_empty?/2»]
    rw [rb m hm]
    congr 2
    cases b'
    · exact (bp_false.mpr fun ⟨l', e, h⟩ => by obtain rfl := encL_inj e; exact absurd (sb.mpr h) (by simp)).symm
    · exact (bp_true.mpr ⟨l, rfl, sb.mp rfl⟩).symm
  refine ⟨_, dnf, ?_⟩
  rw [all]
  congr 2
  unfold deadB
  cases h : (ls.map encL).all res
  · symm; refine bp_false.mpr fun dead => ?_
    obtain ⟨x, mx, hx⟩ := List.all_eq_false.mp h
    obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mx
    refine absurd (bp_true.mpr ⟨l, rfl, (lineEmpty_iff_none n _ _).mpr fun g vg sat => ?_⟩) hx
    have := dead g vg
    rw [(sem g).mpr ⟨l, ml, sat⟩] at this
    cases this
  · symm; refine bp_true.mpr fun g vg => ?_
    cases he : eval (valF E₀ den g) b
    · rfl
    · obtain ⟨l, ml, sat⟩ := (sem g).mp he
      obtain ⟨l', e, le⟩ := bp_true.mp (List.all_eq_true.mp h _ (List.mem_map.mpr ⟨l, ml, rfl⟩))
      obtain rfl := encL_inj e
      exact absurd sat ((lineEmpty_iff_none n _ _).mp le g vg)

/-- Maps from arities to BDDs of arrows of that arity. -/
def ArityBdds (E : Term → Prop) (R : List (Term × Term)) : Prop :=
  ∀ q v, mapLookup R q = some v → ∃ n : Nat, q = .integer n ∧ ∃ L : Term → Prop, (∀ t, L t → FunLit E n t) ∧ Bdd L v

/-- `bdds_non_empty_arities/1` finds no arity exactly when no arity holds a function. -/
theorem nonempty_arities_run (fe : FunElem E den K (.map [])) (fd : FunDom Dm E den dden K (.map []))
    {E₀ : Term → Prop} (cg : DenCongr E₀ den) (hE : ∀ a, E a → E₀ a) {R : List (Term × Term)}
    (hR : ArityBdds E R) :
    ∃ l : List Term, (∀ m, K + 5 ≤ m →
      Elixir.Module.Types.Descr.«bdds_non_empty_arities/1» (D m) (.map R) = .ok (Term.list l)) ∧
      (l = [] ↔ ∀ (n : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow n r) →
        evalR R (.integer n) (valF E₀ den g) = Bool.false) := by
  classical
  let dead : Term → Prop := fun x => ∃ e ∈ mapEntries R, x = .tuple #[e.1, e.2] ∧ ∀ (n : Nat), e.1 = .integer n →
    deadB E₀ den n e.2 = Bool.true
  let o : Term → Option Term := fun x => if dead x then none else
    match x with
    | .tuple ⟨[a, _]⟩ => some a
    | _ => none
  have each : ∀ e ∈ mapEntries R, ∀ m, K + 3 ≤ m →
      (D (m + 2)).pure (.function false "Elixir.Module.Types.Descr" "-bdds_non_empty_arities/1-fun-1-" 1 #[])
        #[.tuple #[e.1, e.2]] = .ok (fmAns (o (.tuple #[e.1, e.2]))) := by
    intro e me m hm
    obtain ⟨n, hn, L, hL, wb⟩ := hR e.1 e.2 (mapLookup_of_mem_mapEntries me)
    obtain ⟨lines, dnf, run⟩ := bdd_dead_run fe fd cg hE hL wb hm
    have hd : dead (.tuple #[e.1, e.2]) ↔ deadB E₀ den n e.2 = Bool.true := by
      constructor
      · rintro ⟨e', me', h, d⟩
        have h₀ := congrArg (fun a : Term => match a with | .tuple ⟨[x, _]⟩ => x | _ => .nil) h
        have h₁ := congrArg (fun a : Term => match a with | .tuple ⟨[_, y]⟩ => y | _ => .nil) h
        simp only at h₀ h₁
        rw [h₁]; exact d n (h₀ ▸ hn)
      · intro d
        refine ⟨e, me, rfl, fun n' hn' => ?_⟩
        rw [hn] at hn'
        simp only [Term.integer.injEq] at hn'
        obtain rfl : n' = n := by omega
        exact d
    rw [Erlang.program.«Elixir.Module.Types.Descr:-bdds_non_empty_arities/1-fun-1-/1».pure]
    simp only [Elixir.Module.Types.Descr.«-bdds_non_empty_arities/1-fun-1-/1»]
    simp only [dnf, pure, Except.pure, Lynx.Except.ok_bind]
    erw [run]
    cases h : deadB E₀ den n e.2
    · have : ¬dead (.tuple #[e.1, e.2]) := fun d => by rw [hd.mp d] at h; cases h
      simp [o, this, boolAtom, fmAns, Term.isMember]
    · have : dead (.tuple #[e.1, e.2]) := hd.mpr h
      simp [o, this, boolAtom, fmAns, Term.isMember]
  refine ⟨((mapEntries R).map fun e => Term.tuple #[e.1, e.2]).filterMap o, fun m hm => ?_, ?_⟩
  · obtain ⟨m', rfl, hm'⟩ : ∃ m', m = m' + 2 ∧ K + 3 ≤ m' := ⟨m - 2, by omega, by omega⟩
    unfold Elixir.Module.Types.Descr.«bdds_non_empty_arities/1»
    simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind, pure, Except.pure]
    exact filtermap_list _ _ _ _ o _ fun x mx => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      exact each e me m' hm'
  · rw [List.filterMap_eq_nil_iff]
    constructor
    · intro h n g vg
      cases hl : mapLookup R (.integer n) with
      | none => simp [evalR, hl]
      | some b =>
        obtain ⟨e, me, ek, rfl⟩ := lookup_entry hl
        have ho := h _ (List.mem_map.mpr ⟨e, me, rfl⟩)
        have d : dead (.tuple #[e.1, e.2]) := by
          refine Classical.byContradiction fun nd => ?_
          simp [o, nd] at ho
        obtain ⟨e', me', h', d'⟩ := d
        have h₀ := congrArg (fun a : Term => match a with | .tuple ⟨[x, _]⟩ => x | _ => .nil) h'
        have h₁ := congrArg (fun a : Term => match a with | .tuple ⟨[_, y]⟩ => y | _ => .nil) h'
        simp only at h₀ h₁
        have en : e.1 = .integer n := (integer_compareExact_eq n e.1).mp ek
        simp only [evalR, hl, Option.elim]
        rw [h₁]
        exact bp_true.mp (d' n (h₀ ▸ en)) g vg
    · intro h x mx
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨n, hn, -⟩ := hR e.1 e.2 (mapLookup_of_mem_mapEntries me)
      have d : dead (.tuple #[e.1, e.2]) := ⟨e, me, rfl, fun n' hn' => by
        rw [hn] at hn'
        simp only [Term.integer.injEq] at hn'
        obtain rfl : n' = n := by omega
        refine bp_true.mpr fun g vg => ?_
        have := h n' g vg
        simpa [evalR, ← hn, mapLookup_of_mem_mapEntries me, Option.elim] using this⟩
      simp [o, d]

/-- The domain of positive arrows, as `fun_normalize/2` folds it: `term()` or a domain. -/
def NDom (Dm : Term → Prop) (t : Term) : Prop := t = .atom "term" ∨ Dm t

/-- The argument lists of such a domain. -/
def nden (dden : Term → List V → Prop) (t : Term) (x : List V) : Prop := t = .atom "term" ∨ dden t x

/-- The fold of `fun_normalize/2` intersects the domains of the lines, and gathers the lines in reverse. -/
theorem domain_fold (fd : FunDom Dm E den dden K (.map [])) {n : Nat} :
    ∀ (Q : List (List (Term × List Term × Term))), (∀ q ∈ Q, PosOk E n q) →
      ∀ (dom₀ : Term) (acc : List (List (Term × List Term × Term))), NDom Dm dom₀ →
      ∃ dom, NDom Dm dom ∧ (Q ≠ [] → Dm dom) ∧ (∀ m, K + 2 ≤ m → Erlang.lists.«foldl_1/3» (D m)
          (.function false "Elixir.Module.Types.Descr" "-fun_normalize/2-fun-0-" 2 #[])
          (.tuple #[dom₀, Term.list (acc.map encP)]) (Term.list (Q.map encP)) =
            .ok (.tuple #[dom, Term.list ((Q.reverse ++ acc).map encP)])) ∧
        ∀ x, nden dden dom x ↔ nden dden dom₀ x ∧ ∀ q ∈ Q, ∃ p ∈ semP den q, FunSem.InDomR p.1 x
  | [], _, dom₀, acc, h₀ => ⟨dom₀, h₀, fun h => absurd rfl h, fun m _ => by simp [Erlang.lists.«foldl_1/3», Term.list], fun x => by simp⟩
  | q :: Q, hQ, dom₀, acc, h₀ => by
    obtain ⟨fdom, hfd, rfd, sfd⟩ := fetch_domain_sem fd n q (hQ q List.mem_cons_self)
    obtain ⟨dom₁, h₁, run₁, sem₁⟩ : ∃ dom₁, NDom Dm dom₁ ∧ (∀ m, K ≤ m →
        Elixir.Module.Types.Descr.«bare_intersection/2» (D m) dom₀ fdom = .ok dom₁) ∧
        ∀ x, nden dden dom₁ x ↔ nden dden dom₀ x ∧ dden fdom x := by
      rcases h₀ with rfl | h₀
      · refine ⟨fdom, Or.inr hfd, fun m _ => inter_term_left _ _, fun x => ?_⟩
        simp only [nden, true_or, true_and]
        constructor
        · rintro (h | h)
          · obtain ⟨X, rfl⟩ := fd.isMap hfd; cases h
          · exact h
        · exact Or.inr
      · obtain ⟨c, hc, rc, sc⟩ := fd.inter h₀ hfd
        refine ⟨c, Or.inr hc, rc, fun x => ?_⟩
        have nt : ∀ {t}, Dm t → t ≠ .atom "term" := fun ht e => by
          obtain ⟨X, rfl⟩ := fd.isMap ht; cases e
        simp only [nden, nt hc, nt h₀, false_or]
        exact sc x
    obtain ⟨dom, hd, hne, run, sem⟩ := domain_fold fd Q (fun q' mq => hQ q' (List.mem_cons_of_mem _ mq)) dom₁ (q :: acc) h₁
    have hdm : Dm dom := by
      cases Q with
      | nil =>
        have e : dom = dom₁ := by
          have := run (K + 2) (Nat.le_refl _)
          simp [Erlang.lists.«foldl_1/3», Term.list] at this
          exact this.symm
        subst e
        rcases h₁ with rfl | h
        · rcases h₀ with rfl | h₀
          · exact absurd (run₁ K (Nat.le_refl _)) (by rw [inter_term_left]; intro e; cases e; obtain ⟨X, h⟩ := fd.isMap hfd; cases h)
          · obtain ⟨c, hc, rc, -⟩ := fd.inter h₀ hfd
            have := (run₁ K (Nat.le_refl _)).symm.trans (rc K (Nat.le_refl _))
            cases this; obtain ⟨X, h⟩ := fd.isMap hc; cases h
        · exact h
      | cons _ _ => exact hne (by simp)
    refine ⟨dom, hd, fun _ => hdm, fun m hm => ?_, fun x => ?_⟩
    · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [List.map_cons, Term.list]
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_normalize/2-fun-0-/2».pure]
      simp only [Elixir.Module.Types.Descr.«-fun_normalize/2-fun-0-/2»]
      rw [rfd m' (by omega), Lynx.Except.ok_bind, run₁ m' (by omega), Lynx.Except.ok_bind]
      have r := run (m' + 1) hm
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, Term.list] at r ⊢
      exact r
    · rw [sem, sem₁, sfd]
      simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

open Classical in
/-- Removing a key from a map, for keys only equal to themselves. -/
theorem lookup_drop_key (k : Term) (hk : ∀ x, compareExact (fuel k x) k x = .eq ↔ x = k)
    (hk' : ∀ x, compareExact (fuel x k) x k = .eq ↔ x = k) : ∀ (R : List (Term × Term)) (q : Term),
    mapLookup (R.filter fun e => !decide (Term.compareExact (Term.fuel k e.1) k e.1 = .eq)) q =
      (if q = k then none else mapLookup R q : Option Term)
  | [], q => by simp [mapLookup]
  | e :: R, q => by
    have ih := lookup_drop_key k hk hk' R q
    by_cases he : e.1 = k
    · have : (!decide (Term.compareExact (Term.fuel k e.1) k e.1 = .eq)) = Bool.false := by
        simp [he]
      rw [List.filter_cons, this]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih]
      by_cases hq : q = k
      · simp [hq]
      · have nq : ¬compareExact (fuel q e.1) q e.1 = .eq := by rw [he, hk']; exact hq
        simp [hq, mapLookup, nq]
    · have : (!decide (Term.compareExact (Term.fuel k e.1) k e.1 = .eq)) = Bool.true := by
        simp [hk, he]
      rw [List.filter_cons, this]
      simp only [ite_true]
      by_cases hq : q = k
      · subst hq
        have nq : ¬compareExact (fuel q e.1) q e.1 = .eq := by rw [hk]; exact he
        simp only [mapLookup, List.find?_cons, nq, decide_false] at ih ⊢
        simp
      · simp only [hq, ite_false] at ih ⊢
        simp only [mapLookup, List.find?_cons] at ih ⊢
        split <;> simp_all

open Classical in
/-- Removing an arity from a map of arities. -/
theorem lookup_drop (n : Int) (R : List (Term × Term)) (q : Term) :
    mapLookup (R.filter fun e => !decide (Term.compareExact (Term.fuel (.integer n) e.1) (.integer n) e.1 = .eq)) q =
      (if q = .integer n then none else mapLookup R q : Option Term) :=
  lookup_drop_key (.integer n) (integer_compareExact_eq n) (fun x => compareExact_eq_integer x n) R q

theorem arityBdds_drop {R : List (Term × Term)} (h : ArityBdds E R) (n : Int) :
    ArityBdds E (R.filter fun e => !decide (Term.compareExact (Term.fuel (.integer n) e.1) (.integer n) e.1 = .eq)) := by
  intro q v hv
  classical
  rw [lookup_drop] at hv
  split at hv
  · cases hv
  · exact h q v hv

/-- The lines `fun_normalize/2` applies, for the BDD `b` of arity `n`: each function of the BDD is in one of them,
and each comes from a non-empty line of the BDD, whose functions the BDD holds. -/
structure NormOk (E E₀ : Term → Prop) (den : Term → V → Prop) (n : Nat) (b : Term)
    (Q : List (List (Term × List Term × Term))) : Prop where
  pos : ∀ q ∈ Q, PosOk E n q
  nonempty : ∀ q ∈ Q, q ≠ []
  cover : ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → eval (valF E₀ den g) b = Bool.true →
    ∃ q ∈ Q, ∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r
  live : ∀ q ∈ Q, ∃ N, PosOk E n N ∧ ¬FunSem.LineEmpty n (semP den q) (semP den N) ∧
    ∀ g : List (FunSem.Row V), (∀ p ∈ semP den q, ∀ r ∈ g, FunSem.Allows p r) →
      (∀ q' ∈ semP den N, ¬∀ r ∈ g, FunSem.Allows q' r) → eval (valF E₀ den g) b = Bool.true

/-- `fun_bdd_to_pos_dnf/2` on the lines of a BDD of arrows. -/
theorem pos_dnf_norm (fe : FunElem E den K (.map [])) (fd : FunDom Dm E den dden K (.map [])) {E₀ : Term → Prop}
    (cg : DenCongr E₀ den) (hE : ∀ a, E a → E₀ a) {n : Nat} {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t)
    {b : Term} (wb : Bdd L b) :
    ∃ Q, (∀ m, K + 5 ≤ m → Elixir.Module.Types.Descr.«fun_bdd_to_pos_dnf/2» (D m) (.integer n) b =
      .ok (Term.list (Q.map encP))) ∧ NormOk E E₀ den n b Q := by
  by_cases top : b = .atom "bdd_top"
  · subst top
    obtain ⟨k, leaf⟩ := leaf_fun (List.replicate n (.map []))
    let a : Term × List Term × Term := (.integer k, List.replicate n (.map []), .atom "term")
    have semT : semP den [a] = [FunSem.top n] := semP_top fe k n
    refine ⟨[[a]], fun m _ => ?_, ⟨fun q mq => ?_, fun q mq => by rw [List.mem_singleton.mp mq]; simp, fun g vg _ => ⟨[a], List.mem_singleton_self _, ?_⟩,
      fun q mq => ⟨[], by simp [PosOk], ?_, fun g _ _ => eval_top _⟩⟩⟩
    · rw [Elixir.Module.Types.Descr.«fun_bdd_to_pos_dnf/2».eq_def]
      simp [dup_nat, leaf, encP, Term.list, a]
    · rw [List.mem_singleton.mp mq]
      intro p mp
      rw [List.mem_singleton.mp mp]
      exact ⟨fun u mu => by rw [List.eq_of_mem_replicate mu]; exact fe.none.1, fe.term.1, by simp [a]⟩
    · rw [semT]
      intro p mp r mr
      rw [List.mem_singleton.mp mp]
      exact FunSem.allows_top (vg r mr)
    · rw [List.mem_singleton.mp mq, semT]
      simp only [semP, List.map_nil]
      exact fun h => FunSem.lineEmpty_nil n ((FunSem.lineEmpty_top n []).mpr h)
  · obtain ⟨Q, run, pos, ne, cover, live⟩ := pos_dnf_run fe fd cg hE hL wb top
    exact ⟨Q, run, ⟨pos, ne, cover, live⟩⟩

theorem foldl3_of_1 (d : Dispatcher) (mo nm : String) (caps : Array Term) (acc r : Term) (l : List Term)
    (h : Erlang.lists.«foldl_1/3» d (.function false mo nm 2 caps) acc (Term.list l) = .ok r) :
    Erlang.lists.«foldl/3» d (.function false mo nm 2 caps) acc (Term.list l) = .ok r := by
  cases l with
  | nil =>
    have e : acc = r := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using h
    subst e
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  | cons x xs =>
    rw [Erlang.lists.«foldl_1/3».eq_def] at h
    simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using h

/-- `fun_normalize/2` on a union of arities, at the arity `n`: the domain and lines of the BDD of `n` when it holds
functions, or else `:badfun` exactly when no arity holds functions, and `:badarity` otherwise. -/
theorem normalize_union (fe : FunElem E den K (.map [])) (fd : FunDom Dm E den dden K (.map []))
    {E₀ : Term → Prop} (cg : DenCongr E₀ den) (hE : ∀ a, E a → E₀ a) {X R : List (Term × Term)}
    (hX : mapLookup X (.atom "fun") = some (.tuple #[.atom "union", .map R])) (hR : ArityBdds E R) (n : Nat) :
    ∃ res, (∀ m, K + 8 ≤ m → Elixir.Module.Types.Descr.«fun_normalize/2» (D m) (.map X) (.integer n) = .ok res) ∧
      ((∃ b dom Q, mapLookup R (.integer n) = some b ∧ NormOk E E₀ den n b Q ∧ Q ≠ [] ∧ Dm dom ∧
          (∀ x, dden dom x ↔ ∀ q ∈ Q, ∃ p ∈ semP den q, FunSem.InDomR p.1 x) ∧
          res = .tuple #[.atom "ok", dom, Term.list (Q.reverse.map encP)]) ∨
        ((∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → evalR R (.integer n) (valF E₀ den g) = Bool.false) ∧
          (res = .atom "badfun" ↔ ∀ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) →
            evalR R (.integer a) (valF E₀ den g) = Bool.false) ∧
          (res = .atom "badfun" ∨ ∃ o, res = .tuple #[.atom "badarity", .atom "positive", o]))) := by
  classical
  let rest := R.filter fun e => !decide (Term.compareExact (Term.fuel (.integer n) e.1) (.integer n) e.1 = .eq)
  have evalRest : ∀ (a : Nat) ρ, a ≠ n → evalR rest (.integer a) ρ = evalR R (.integer a) ρ := by
    intro a ρ ha
    simp only [evalR, rest, lookup_drop, Term.integer.injEq]
    rw [ite_eq_right (by omega)]
  have restN : ∀ ρ, evalR rest (.integer n) ρ = Bool.false := by
    intro ρ; simp [evalR, rest, lookup_drop, -integer_compareExact_eq]
  -- What `bdds_non_empty_arities/1` answers on the other arities, once the arity `n` holds no function.
  have others : ∀ (dead : ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) →
      evalR R (.integer n) (valF E₀ den g) = Bool.false) (R' : List (Term × Term)), ArityBdds E R' →
      (∀ (a : Nat) ρ, a ≠ n → evalR R' (.integer a) ρ = evalR R (.integer a) ρ) →
      (∀ ρ, evalR R' (.integer n) ρ = Bool.false ∨ evalR R' (.integer n) ρ = evalR R (.integer n) ρ) →
      ∃ res, (∀ m, K + 5 ≤ m → (do
          let l ← Elixir.Module.Types.Descr.«bdds_non_empty_arities/1» (D m) (.map R')
          match l with
          | .nil => pure (Term.atom "badfun")
          | o => pure (Term.tuple #[.atom "badarity", .atom "positive", o])) = .ok res) ∧
        (res = .atom "badfun" ↔ ∀ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) →
            evalR R (.integer a) (valF E₀ den g) = Bool.false) ∧
        (res = .atom "badfun" ∨ ∃ o, res = .tuple #[.atom "badarity", .atom "positive", o]) := by
    intro dead R' hR' same atN
    obtain ⟨l, run, sem⟩ := nonempty_arities_run fe fd cg hE hR'
    have iff : (∀ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) →
        evalR R' (.integer a) (valF E₀ den g) = Bool.false) ↔
        ∀ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) →
          evalR R (.integer a) (valF E₀ den g) = Bool.false := by
      constructor
      · intro h a g vg
        by_cases ha : a = n
        · subst ha; exact dead g vg
        · rw [← same a _ ha]; exact h a g vg
      · intro h a g vg
        by_cases ha : a = n
        · subst ha
          rcases atN (valF E₀ den g) with e | e
          · exact e
          · rw [e]; exact h a g vg
        · rw [same a _ ha]; exact h a g vg
    cases l with
    | nil =>
      refine ⟨.atom "badfun", fun m hm => by rw [run m hm]; rfl, ⟨fun _ => iff.mp (sem.mp rfl), fun _ => rfl⟩,
        Or.inl rfl⟩
    | cons o os =>
      refine ⟨.tuple #[.atom "badarity", .atom "positive", Term.list (o :: os)], fun m hm => by rw [run m hm]; rfl,
        Iff.intro (fun h => by cases h) (fun h => by have := sem.mpr (iff.mpr h); cases this), Or.inr ⟨_, rfl⟩⟩
  have shape : ∀ d, Elixir.Module.Types.Descr.«fun_normalize/2» d (.map X) (.integer n) =
      (do
        let t ← Erlang.maps.«take/2» (.integer n) (.map R)
        match t with
        | .tuple ⟨[bdd, rest]⟩ => do
          let q ← Elixir.Module.Types.Descr.«fun_bdd_to_pos_dnf/2» d (.integer n) bdd
          let acc ← Erlang.lists.«foldl/3» d (.function false "Elixir.Module.Types.Descr" "-fun_normalize/2-fun-0-" 2 #[])
            (.tuple #[.atom "term", .nil]) q
          match acc with
          | .tuple ⟨[dom, arrows]⟩ => do
            let e ← Erlang.erlang.«==/2» arrows .nil
            match e with
            | .atom "false" => pure (.tuple #[.atom "ok", dom, arrows])
            | .atom "true" => do
              let l ← Elixir.Module.Types.Descr.«bdds_non_empty_arities/1» d rest
              match l with
              | .nil => pure (.atom "badfun")
              | o => pure (.tuple #[.atom "badarity", .atom "positive", o])
            | u => .error (.error (.tuple #[.atom "case_clause", u]))
          | u => .error (.error (.tuple #[.atom "badmatch", u]))
        | .atom "error" => do
          let l ← Elixir.Module.Types.Descr.«bdds_non_empty_arities/1» d (.map R)
          match l with
          | .nil => pure (.atom "badfun")
          | o => pure (.tuple #[.atom "badarity", .atom "positive", o])
        | u => .error (.error (.tuple #[.atom "case_clause", u]))) := by
    intro d
    rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]
    simp [getMapKeys_single, hX]
    rfl
  cases hl : mapLookup R (.integer n) with
  | none =>
    have dead : ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) →
        evalR R (.integer n) (valF E₀ den g) = Bool.false := fun g _ => by simp [evalR, hl]
    obtain ⟨res, run, sem, sh⟩ := others dead R hR (fun _ _ _ => rfl) (fun _ => Or.inr rfl)
    refine ⟨res, fun m hm => ?_, Or.inr ⟨dead, sem, sh⟩⟩
    rw [shape]
    simp only [Erlang.maps.«take/2», hl, Lynx.Except.ok_bind]
    exact run m (by omega)
  | some b =>
    obtain ⟨n', hn', L, hL, wb⟩ := hR _ _ hl
    simp only [Term.integer.injEq] at hn'
    obtain rfl : n = n' := by omega
    obtain ⟨Q, rQ, nQ⟩ := pos_dnf_norm fe fd cg hE hL wb
    obtain ⟨dom, -, hdom, rdom, sdom⟩ := domain_fold fd Q nQ.pos (.atom "term") [] (Or.inl rfl)
    have fold : ∀ m, K + 2 ≤ m → Erlang.lists.«foldl/3» (D m)
        (.function false "Elixir.Module.Types.Descr" "-fun_normalize/2-fun-0-" 2 #[])
        (.tuple #[.atom "term", .nil]) (Term.list (Q.map encP)) =
          .ok (.tuple #[dom, Term.list (Q.reverse.map encP)]) := fun m hm =>
      foldl3_of_1 _ _ _ _ _ _ _ (by simpa using rdom m hm)
    cases Q with
    | nil =>
      have dead : ∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) →
          evalR R (.integer n) (valF E₀ den g) = Bool.false := fun g vg => by
        simp only [evalR, hl, Option.elim]
        cases he : eval (valF E₀ den g) b
        · rfl
        · obtain ⟨q, mq, -⟩ := nQ.cover g vg he; cases mq
      obtain ⟨res, run, sem, sh⟩ := others dead rest (arityBdds_drop hR n) evalRest (fun ρ => Or.inl (restN ρ))
      refine ⟨res, fun m hm => ?_, Or.inr ⟨dead, sem, sh⟩⟩
      rw [shape]
      simp only [Erlang.maps.«take/2», hl, Lynx.Except.ok_bind]
      rw [rQ m (by omega), Lynx.Except.ok_bind, fold m (by omega), Lynx.Except.ok_bind]
      simp [Term.list, Erlang.erlang.«==/2», -integer_compareExact_eq]
      exact run m (by omega)
    | cons q Q' =>
      refine ⟨.tuple #[.atom "ok", dom, Term.list ((q :: Q').reverse.map encP)], fun m hm => ?_,
        Or.inl ⟨b, dom, q :: Q', rfl, nQ, by simp, hdom (by simp), fun x => ?_, rfl⟩⟩
      · rw [shape]
        simp only [Erlang.maps.«take/2», hl, Lynx.Except.ok_bind]
        rw [rQ m (by omega), Lynx.Except.ok_bind, fold m (by omega), Lynx.Except.ok_bind]
        have ne : Term.list ((Q'.map encP).reverse ++ [encP q]) ≠ .nil := by
          cases h : (Q'.map encP).reverse <;> simp [Term.list]
        simp [Erlang.erlang.«==/2», List.reverse_cons, ne]
      · have nt : dom ≠ .atom "term" := fun e => by
          obtain ⟨X, h⟩ := fd.isMap (hdom (by simp)); rw [e] at h; cases h
        have := sdom x
        simp only [nden, nt, false_or, true_or, true_and] at this
        exact this

end

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop} {K : Nat} {seen : Term}

/-- `fun_apply_static/2` applies each line of positive arrows to nonempty arguments, and unites the results. -/
theorem apply_static_lines (fe : FunElem E den K seen) (n : Nat) (args : List Term) (hargs : ∀ a ∈ args, E a)
    (ne : ∀ a ∈ args, ∃ v, den a v) (len : args.length = n) (Q : List (List (Term × List Term × Term)))
    (hQ : ∀ q ∈ Q, PosOk E n q) :
    ∃ r, E r ∧ (∀ m, K + 1 ≤ m →
      Elixir.Module.Types.Descr.«fun_apply_static/2» (D m) (Term.list args) (Term.list (Q.map encP)) = .ok r) ∧
      ∀ v, den r v ↔ ∃ q ∈ Q, FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den q) v := by
  let G : Term → V → Prop := fun t v => ∃ q ∈ Q, t = encP q ∧
    FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den q) v
  have prod : ∀ x, ProdSem den [args] x ↔ FunSem.InDomR (args.map den) x := fun x => by simp [ProdSem]
  obtain ⟨r, hr, run, s⟩ := foldl_or (K + 1) "Elixir.Module.Types.Descr" "-fun_apply_static/2-fun-0-"
    #[Term.list args] E den G (Q.map encP) (by
      intro t mt a ha
      obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
      obtain ⟨r, hr, run, s⟩ := aux_apply_sem fe n q (hQ q mq) a (.atom "term") [args] ha fe.term.1
        (fun p mp => by
          rw [List.mem_singleton.mp mp]
          exact ⟨len, fun e me => ⟨hargs e me, ne e me⟩⟩) (by simp)
      refine ⟨r, hr, fun m hm => ?_, fun v => ?_⟩
      · obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_static/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-fun_apply_static/2-fun-0-/3»] using run m' hm'
      · rw [s, app_congr_I prod, app_congr_r _ (fun v => iff_true_intro (fe.term.2 v))]
        refine or_congr Iff.rfl ⟨fun h => ⟨q, mq, rfl, h⟩, fun ⟨q', mq', e, h⟩ => ?_⟩
        rw [encP_inj e]; exact h) (.map []) fe.none.1
  refine ⟨r, hr, fun m hm => by unfold Elixir.Module.Types.Descr.«fun_apply_static/2»; simpa using run m hm,
    fun v => ?_⟩
  rw [s]
  simp only [fe.none.2, false_or, List.mem_map, G]
  constructor
  · rintro ⟨_, ⟨q, mq, rfl⟩, q', mq', e, h⟩
    exact ⟨q', mq', h⟩
  · rintro ⟨q, mq, h⟩
    exact ⟨_, ⟨q, mq, rfl⟩, q, mq, rfl, h⟩

end

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- Applying positive arrows that cover non-empty arguments: every row of a function in the arrows is allowed by the
arrow from the arguments to any type that holds the results of the application. -/
theorem app_allows {n : Nat} (args : List Term) (len : args.length = n) (ne : ∃ w, FunSem.InDomR (args.map den) w)
    (q : List (Term × List Term × Term)) (hq : PosOk E n q)
    (cover : ∀ x, FunSem.InDomR (args.map den) x → ∃ p ∈ semP den q, FunSem.InDomR p.1 x)
    (s : V → Prop) (hs : ∀ v, FunSem.App (FunSem.InDomR (args.map den)) (fun _ => True) (semP den q) v → s v) :
    ∀ r, FunSem.ValidRow n r → (∀ p ∈ semP den q, FunSem.Allows p r) → FunSem.Allows (args.map den, s) r := by
  obtain ⟨w, hw⟩ := ne
  have qne : semP den q ≠ [] := by
    obtain ⟨p, mp, -⟩ := cover w hw
    exact List.ne_nil_of_mem mp
  have lP : ∀ p ∈ semP den q, p.1.length = n := by
    intro p mp
    obtain ⟨p', mp', rfl⟩ := List.mem_map.mp mp
    simp [(hq p' mp').2.2]
  have noRow := (FunSem.noRow_app (semP den q) (args.map den) s w hw cover).mpr hs
  have phi := (FunSem.phiS_iff _ _ _ (fun p mp => by rw [lP p mp]; simp [len])).mpr noRow
  exact (FunSem.neg_iff_phi n _ qne lP _ _ (by simp [len])).mpr phi

end

theorem leaf_arrow (args : List Term) {ret : Term} (hr : Static ret) : ∃ k : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (Term.list args) ret = .ok (.tuple #[.integer k, Term.list args, ret]) := by
  obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (Term.list args) ret)
  have nl : Erlang.erlang.«is_list/1» ret = .ok (.atom "false") := by
    rcases hr with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩ <;> rfl
  unfold Elixir.Module.Types.Descr.«bdd_leaf_new/2»
  cases args <;> simp [hrun, Elixir.Module.Types.Descr.«bdd_leaf_key/2», nl, Term.list]

/-- The arrow from static arguments to a static return. -/
theorem fun2_run (args : List Term) (hargs : ∀ e ∈ args, Static e) {ret : Term} (hr : Static ret) : ∃ k : Int,
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (Term.list args) ret = .ok (.tuple #[.integer k, Term.list args, ret]) ∧
    ∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«fun/2» (D m) (Term.list args) ret =
      .ok (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer args.length, .tuple #[.integer k, Term.list args, ret])]])]) := by
  obtain ⟨k, leaf⟩ := leaf_arrow args hr
  obtain ⟨r, ⟨s, d, rfl⟩, run⟩ := foldl_uni 1 "Elixir.Module.Types.Descr" "-fun_descr/2-fun-0-" #[]
    (fun a => ∃ s d, a = .tuple #[s, d, .atom "false"]) args (by
      intro x mx a ⟨s, d, ha⟩
      subst ha
      refine ⟨.tuple #[.cons x s, .cons x d, .atom "false"], ⟨_, _, rfl⟩, fun m hm => ?_⟩
      obtain ⟨m', rfl, -⟩ := succ_of_le hm
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_descr/2-fun-0-/2».pure]
      simp [Elixir.Module.Types.Descr.«-fun_descr/2-fun-0-/2», split_static (hargs x mx),
        Lynx.Except.orElse]) (.tuple #[.nil, .nil, .atom "false"]) ⟨_, _, rfl⟩
  refine ⟨k, leaf, fun m hm => ?_⟩
  have hl : Erlang.erlang.«is_list/1» (Term.list args) = .ok (.atom "true") := by
    cases args <;> simp [Erlang.erlang.«is_list/1»]
  unfold Elixir.Module.Types.Descr.«fun/2» Elixir.Module.Types.Descr.«fun_descr/2»
  simp [hl, length_list, run m hm, split_static hr, Lynx.Except.orElse, isMember,
    Elixir.Module.Types.Descr.«fun_new/3», leaf]

theorem descrC_fn {Fn Fn' TF LF MF : Term → Prop} (h : ∀ x, Fn x → Fn' x) {X : List (Term × Term)}
    (sX : DescrC Fn TF LF MF X) : DescrC Fn' TF LF MF X := by
  refine ⟨sX.keys, fun name x hx => ?_⟩
  rcases sX.fields name x hx with h₁ | h₂ | ⟨e, f⟩ | h₄ | h₅ | h₆
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₂)
  · exact Or.inr (Or.inr (Or.inl ⟨e, h x f⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h₄)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₅))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₆))))

section
variable {t : Term} {n : Nat}

theorem domA_de {H : Nat} {a : Term} (ha : DomA (level t n).E H a) : DE (level t n).E a := by
  obtain ⟨-, X, rfl, sX, -⟩ := ha
  exact Or.inr ⟨X, rfl, descrC_fn (fun x h => by rw [h]; exact funA_top) sX⟩

theorem ddenA_tpt {X : List (Term × Term)} (w : List (level t n).V) :
    ddenA (level t n).E (level t n).den (.map X) w ↔ denD (.map X) (tpt (t := t) (n := n) w) := by
  rw [denD_map]
  exact ⟨fun ⟨Y, e, d⟩ => by simp only [Term.map.injEq] at e; subst e; exact d, fun d => ⟨X, rfl, d⟩⟩

/-- Subtyping of domains compares the lists of values they hold. -/
theorem dom_sub {H : Nat} {a b : Term} (ha : DomA (level t n).E H a) (hb : DomA (level t n).E H b) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom (bp (∀ x,
      ddenA (level t n).E (level t n).den a x → ddenA (level t n).E (level t n).den b x))) := by
  have da := domA_de ha
  have db := domA_de hb
  obtain ⟨⟨A, eA, -, onlyA⟩, A', rfl, -, -⟩ := ha
  obtain ⟨⟨B, eB, -, onlyB⟩, B', rfl, -, -⟩ := hb
  simp only [Term.map.injEq] at eA eB
  subst eA eB
  rw [next_sub da db hm]
  refine congrArg (fun x => Except.ok (boolAtom x)) (bp_congr ⟨fun h x hx => (ddenA_tpt x).mpr (h _ ((ddenA_tpt x).mp hx)),
    fun h v hv => ?_⟩)
  by_cases tv : v.1.1 = "tuple"
  · obtain ⟨w, hw⟩ := pt_tuple v tv
    rw [hw] at hv ⊢
    rw [← denD_tpt, ← ddenA_tpt] at hv ⊢
    exact h w hv
  · exfalso
    rw [denD_map] at hv
    cases hl : mapLookup A' (.atom v.1.1) with
    | none => rw [hl] at hv; simp [dn_none] at hv
    | some _ =>
      have := onlyA _ (by rw [hl]; rfl)
      simp only [Term.atom.injEq] at this
      exact tv this

end

section
variable {t : Term} {n : Nat}

/-- Functions of arity `a` in the function field of a map. -/
def FunIn (t : Term) (n : Nat) (X : List (Term × Term)) (a : Nat) (g : List (FunSem.Row (level t n).V)) : Prop :=
  ∃ F, mapLookup X (.atom "fun") = some F ∧ arityOf F (.integer a) (valF (level t n).E (level t n).den g) = Bool.true

/-- The point of the next level of a function of arity `a`. -/
noncomputable def fpt (a : Nat) (g : List (FunSem.Row (level t n).V)) (vg : ∀ r ∈ g, FunSem.ValidRow a r) : PN t n :=
  ⟨("fun", (0, .integer a, valF (level t n).E (level t n).den g)), by simp [names],
    ⟨valF_resp g, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
      fun h => by simp at h, fun _ => ⟨a, g, rfl, vg, rfl⟩⟩⟩

theorem denD_fpt {X : List (Term × Term)} (a : Nat) (g : List (FunSem.Row (level t n).V))
    (vg : ∀ r ∈ g, FunSem.ValidRow a r) : denD (.map X) (fpt (t := t) (n := n) a g vg) ↔ FunIn t n X a g := by
  rw [denD_map]
  simp only [fpt, FunIn]
  cases h : mapLookup X (.atom "fun") with
  | none => simp [dn_none]
  | some F => simp [dn_fun]

theorem pt_fun (v : PN t n) (h : v.1.1 = "fun") : ∃ (a : Nat) (g : List (FunSem.Row (level t n).V)),
    (∀ r ∈ g, FunSem.ValidRow a r) ∧ ∀ X : List (Term × Term), (denD (.map X) v ↔ FunIn t n X a g) := by
  obtain ⟨⟨name, p⟩, mem, ok⟩ := v
  simp only at h
  subst h
  obtain ⟨a, g, ea, vg, eρ⟩ := ok.2.2.2.2.2 rfl
  refine ⟨a, g, vg, fun X => ?_⟩
  rw [denD_map]
  simp only [FunIn]
  cases hl : mapLookup X (.atom "fun") with
  | none => simp [dn_none]
  | some F => simp only at ea eρ; simp [dn_fun, ea, eρ]

/-- Inclusion of maps over their function points and their other points. -/
theorem subN_funs {X Y : List (Term × Term)} :
    SubN t n (.map X) (.map Y) ↔ (∀ v : PN t n, v.1.1 ≠ "fun" → denD (.map X) v → denD (.map Y) v) ∧
      ∀ (a : Nat) g, (∀ r ∈ g, FunSem.ValidRow a r) → FunIn t n X a g → FunIn t n Y a g := by
  constructor
  · intro h
    exact ⟨fun v _ hv => h v hv, fun a g vg hx => (denD_fpt a g vg).mp (h _ ((denD_fpt a g vg).mpr hx))⟩
  · rintro ⟨h₁, h₂⟩ v hv
    by_cases f : v.1.1 = "fun"
    · obtain ⟨a, g, vg, e⟩ := pt_fun v f
      rw [e] at hv ⊢
      exact h₂ a g vg hv
    · exact h₁ v f hv

open Classical in
theorem lookup_drop_fun (X : List (Term × Term)) (q : Term) :
    mapLookup (X.filter fun e => !decide (Term.compareExact (Term.fuel (.atom "fun") e.1) (.atom "fun") e.1 = .eq)) q =
      (if q = .atom "fun" then none else mapLookup X q : Option Term) := by
  classical
  exact lookup_drop_key (.atom "fun") (atom_compareExact_eq "fun") (fun x => compareExact_eq_atom x "fun") X q

/-- `fun_only?/1` checks that a map holds no point of other kinds than functions. -/
theorem fun_only_run {X : List (Term × Term)} (sX : DE (level t n).E (.map X)) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«fun_only?/1» (D m) (.map X) =
      .ok (boolAtom (bp (∀ v : PN t n, v.1.1 ≠ "fun" → ¬denD (.map X) v))) := by
  classical
  obtain ⟨X', e, sX'⟩ : ∃ X', Term.map X = .map X' ∧ DescrC (FunA (level t n).E) (TField (level t n).E)
      (LF (level t n).E) (MField (level t n).E) X' := by
    rcases sX with h | h
    · cases h
    · exact h
  simp only [Term.map.injEq] at e
  subst e
  let Y := X.filter fun e => !decide (Term.compareExact (Term.fuel (.atom "fun") e.1) (.atom "fun") e.1 = .eq)
  have sY : DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E) (MField (level t n).E) Y := by
    refine ⟨fun q h => ?_, fun name x h => ?_⟩
    · rw [lookup_drop_fun] at h
      split at h
      · cases h
      · exact sX'.keys q h
    · rw [lookup_drop_fun] at h
      split at h
      · cases h
      · exact sX'.fields name x h
  have eY : ∀ v : PN t n, denD (.map Y) v ↔ v.1.1 ≠ "fun" ∧ denD (.map X) v := by
    intro v
    rw [denD_map, denD_map, lookup_drop_fun]
    by_cases f : v.1.1 = "fun"
    · rw [ite_eq_left (by rw [f])]; simp [f, dn_none]
    · rw [ite_eq_right (by simp [f])]; simp [f]
  simp only [Elixir.Module.Types.Descr.«fun_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
  rw [next_empty (Or.inr ⟨Y, rfl, sY⟩) hm]
  congr 2
  exact bp_congr ⟨fun h v f d => h v ((eY v).mpr ⟨f, d⟩), fun h v d => h v ((eY v).mp d).1 ((eY v).mp d).2⟩

/-- The arrow from arguments to a return, as a type of the next level. -/
theorem arrow_de (args : List Term) (hargs : ∀ a ∈ args, (level t n).E a) {ret : Term} (hret : (level t n).E ret)
    (k : Int) : DE (level t n).E
      (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer args.length, .tuple #[.integer k, Term.list args, ret])]])]) := by
  refine Or.inr ⟨_, rfl, ⟨fun q h => ?_, fun name x h => ?_⟩⟩
  · by_cases e : compareExact (fuel q (.atom "fun")) q (.atom "fun") = .eq
    · exact ⟨"fun", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [mapLookup, e] at h
  · by_cases e : name = "fun"
    · subst e
      simp [mapLookup] at h
      subst h
      refine Or.inr (Or.inr (Or.inl ⟨rfl, Bool.true, _, rfl, by simp, fun q v hv => ?_, fun q hq => ?_⟩))
      · by_cases eq : compareExact (fuel q (.integer args.length)) q (.integer args.length) = .eq
        · simp [mapLookup, eq] at hv
          subst hv
          rw [compareExact_eq_integer] at eq
          subst eq
          exact Bdd.leaf_iff.mpr ⟨args.length, rfl, k, args, ret, rfl, rfl, hargs, hret⟩
        · simp [mapLookup, eq] at hv
      · by_cases eq : compareExact (fuel q (.integer args.length)) q (.integer args.length) = .eq
        · exact ⟨args.length, (compareExact_eq_integer _ _).mp eq⟩
        · simp [mapLookup, eq] at hq
    · simp [mapLookup, e] at h

theorem funIn_arrow (args : List Term) (hargs : ∀ a ∈ args, (level t n).E a) {ret : Term}
    (hret : (level t n).E ret) (k : Int) (a : Nat) (g : List (FunSem.Row (level t n).V)) :
    FunIn t n [(.atom "fun", .tuple #[.atom "union", .map [(.integer args.length, .tuple #[.integer k, Term.list args, ret])]])] a g ↔
      a = args.length ∧ ∀ r ∈ g, FunSem.Allows (args.map (level t n).den, (level t n).den ret) r := by
  simp only [FunIn, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some,
    Option.some.injEq, exists_eq_left', arityOf]
  by_cases e : a = args.length
  · subst e
    simp [valF_iff (level t n).ef.congrE g hargs hret]
  · have : decide ((a : Int) = (args.length : Int)) = Bool.false := by simp; omega
    simp [this, e]

theorem funIn_top (a b : Nat) (g : List (FunSem.Row (level t n).V)) :
    FunIn t n [(.atom "fun", .tuple #[.atom "union", .map [(.integer b, .atom "bdd_top")]])] a g ↔ a = b := by
  by_cases e : a = b
  · subst e; simp [FunIn, mapLookup, arityOf]
  · have : decide ((a : Int) = (b : Int)) = Bool.false := by simp; omega
    simp [FunIn, mapLookup, arityOf, this, e]

theorem top_de (b : Nat) : DE (level t n).E (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer b, .atom "bdd_top")]])]) := by
  refine Or.inr ⟨_, rfl, ⟨fun q h => ?_, fun name x h => ?_⟩⟩
  · by_cases e : compareExact (fuel q (.atom "fun")) q (.atom "fun") = .eq
    · exact ⟨"fun", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [mapLookup, e] at h
  · by_cases e : name = "fun"
    · subst e
      simp [mapLookup] at h
      subst h
      refine Or.inr (Or.inr (Or.inl ⟨rfl, Bool.true, _, rfl, by simp, fun q v hv => ?_, fun q hq => ?_⟩))
      · by_cases eq : compareExact (fuel q (.integer b)) q (.integer b) = .eq
        · simp [mapLookup, eq] at hv
          subst hv
          simp [Bdd]
        · simp [mapLookup, eq] at hv
      · by_cases eq : compareExact (fuel q (.integer b)) q (.integer b) = .eq
        · exact ⟨b, (compareExact_eq_integer _ _).mp eq⟩
        · simp [mapLookup, eq] at hq
    · simp [mapLookup, e] at h

end

section
variable {V : Type} {E Dm : Term → Prop} {den : Term → V → Prop} {dden : Term → List V → Prop} {K : Nat}

/-- A live line of a BDD holds some function. -/
theorem normOk_live {E₀ : Term → Prop} {n : Nat} {b : Term} {Q : List (List (Term × List Term × Term))}
    (h : NormOk E E₀ den n b Q) (ne : Q ≠ []) :
    ∃ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) ∧ eval (valF E₀ den g) b = Bool.true := by
  obtain ⟨q, mq⟩ := List.exists_mem_of_ne_nil Q ne
  obtain ⟨N, -, lv, sat⟩ := h.live q mq
  rw [lineEmpty_iff_none] at lv
  obtain ⟨g, hg⟩ := Classical.not_forall.mp lv
  obtain ⟨vg, hab⟩ := Classical.not_imp.mp hg
  obtain ⟨allP, noN⟩ := Classical.not_not.mp hab
  exact ⟨g, vg, sat g allP noN⟩

/-- `fun_normalize_both/3` on a static union of arities, at the arity `n`: the domain and lines of the BDD of `n`
when it holds functions and no other arity does, or else neither `{:ok, _}` nor `{:ok, _, _, _}`, and `:badfun`
exactly when no arity holds functions. -/
theorem normalize_both_union (fe : FunElem E den K (.map [])) (fd : FunDom Dm E den dden K (.map []))
    {E₀ : Term → Prop} (cg : DenCongr E₀ den) (hE : ∀ a, E a → E₀ a) {X R : List (Term × Term)}
    (hX : mapLookup X (.atom "fun") = some (.tuple #[.atom "union", .map R])) (hR : ArityBdds E R) (n : Nat) :
    ∃ nb, (∀ m, K + 8 ≤ m →
        Elixir.Module.Types.Descr.«fun_normalize_both/3» (D m) (.map X) (.atom "nil") (.integer n) = .ok nb) ∧
      ((∃ b dom Q, mapLookup R (.integer n) = some b ∧ NormOk E E₀ den n b Q ∧ Q ≠ [] ∧ Dm dom ∧
          (∀ x, dden dom x ↔ ∀ q ∈ Q, ∃ p ∈ semP den q, FunSem.InDomR p.1 x) ∧
          (∀ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) → a ≠ n →
            evalR R (.integer a) (valF E₀ den g) = Bool.false) ∧
          nb = .tuple #[.atom "ok", dom, Term.list (Q.reverse.map encP), Term.list (Q.reverse.map encP)]) ∨
        ((∀ x, nb ≠ .tuple #[.atom "ok", x]) ∧ (∀ a b c, nb ≠ .tuple #[.atom "ok", a, b, c]) ∧
          (nb = .atom "badfun" ↔ ∀ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) →
            evalR R (.integer a) (valF E₀ den g) = Bool.false) ∧
          ((∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) →
              evalR R (.integer n) (valF E₀ den g) = Bool.false) ∨
            ∃ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) ∧ a ≠ n ∧
              evalR R (.integer a) (valF E₀ den g) = Bool.true))) := by
  classical
  obtain ⟨res, run, cs⟩ := normalize_union fe fd cg hE hX hR n
  rcases cs with ⟨b, dom, Q, hb, nQ, ne, hdom, sdom, rfl⟩ | ⟨dead, bf, sh⟩
  · let rest := R.filter fun e => !decide (Term.compareExact (Term.fuel (.integer n) e.1) (.integer n) e.1 = .eq)
    obtain ⟨l, rl, sl⟩ := nonempty_arities_run fe fd cg hE (arityBdds_drop hR n)
    have other : ∀ m, K + 5 ≤ m → Elixir.Module.Types.Descr.«fun_other_non_empty_arities/2» (D m) (.map X)
        (.integer n) = .ok (Term.list l) := by
      intro m hm
      unfold Elixir.Module.Types.Descr.«fun_other_non_empty_arities/2»
      simp [getMapKeys_single, hX, Erlang.maps.«take/2», hb, -integer_compareExact_eq]
      exact rl m hm
    have restEq : ∀ (a : Nat) ρ, a ≠ n → evalR rest (.integer a) ρ = evalR R (.integer a) ρ := by
      intro a ρ ha
      simp only [evalR, rest, lookup_drop, Term.integer.injEq]
      rw [ite_eq_right (by omega)]
    cases l with
    | nil =>
      refine ⟨_, fun m hm => ?_, Or.inl ⟨b, dom, Q, hb, nQ, ne, hdom, sdom, fun a g vg ha => ?_, rfl⟩⟩
      · rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
        simp [getMapKeys_single, hX, run m hm, other m (by omega), Term.list]
      · rw [← restEq a _ ha]; exact sl.mp rfl a g vg
    | cons o os =>
      obtain ⟨g, vg, hg⟩ := normOk_live nQ ne
      have elsewhere : ∃ (a : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow a r) ∧ a ≠ n ∧
          evalR R (.integer a) (valF E₀ den g) = Bool.true := by
        refine Classical.byContradiction fun none => ?_
        have : o :: os = [] := sl.mpr fun a g vg => by
          by_cases ha : a = n
          · subst ha; simp [evalR, lookup_drop, -integer_compareExact_eq]
          · rw [restEq a _ ha]
            cases h : evalR R (.integer a) (valF E₀ den g)
            · rfl
            · exact absurd ⟨a, g, vg, ha, h⟩ none
        cases this
      refine ⟨.tuple #[.atom "badarity", .atom "positive", .cons (.integer n) (Term.list (o :: os))],
        fun m hm => ?_, Or.inr ⟨fun x e => by simp at e, fun a b c e => by simp at e,
          ⟨fun e => by simp at e, fun h => ?_⟩, Or.inr elsewhere⟩⟩
      · rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
        simp [getMapKeys_single, hX, run m hm, other m (by omega), Term.list]
      · have := h n g vg
        simp [evalR, hb, hg] at this
  · refine ⟨res, fun m hm => ?_, Or.inr ⟨?_, ?_, ?_, Or.inl dead⟩⟩
    · rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
      rcases sh with rfl | ⟨o, rfl⟩ <;> simp [getMapKeys_single, hX, run m hm]
    · rcases sh with rfl | ⟨o, rfl⟩ <;> simp
    · rcases sh with rfl | ⟨o, rfl⟩ <;> simp
    · exact bf

end

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- A row with real arguments and a result is allowed by an arrow when the result is in its return whenever the
arguments are in its domain. -/
theorem allows_row (p : FunSem.Arrow V) (x : List V) (v : V) :
    FunSem.Allows p (x.map some, some v) ↔ (FunSem.InDomR p.1 x → p.2 v) := by
  simp only [FunSem.Allows, FunSem.inDom_real]
  exact ⟨fun h hd => by obtain ⟨y, e, hy⟩ := h hd; cases e; exact hy, fun h hd => ⟨v, rfl, h hd⟩⟩

/-- The image of the functions of a BDD of arrows of arity `n` on argument lists `I`: the results of their rows
whose arguments are in `I`. -/
def ImgB (E₀ : Term → Prop) (den : Term → V → Prop) (n : Nat) (b : Term) (I : List V → Prop) (v : V) : Prop :=
  ∃ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) ∧ eval (valF E₀ den g) b = Bool.true ∧
    ∃ x, I x ∧ (x.map some, some v) ∈ g

/-- Applying the lines `fun_normalize/2` keeps for a BDD gives its image: a function of a line can return any result
the arrows of the line allow, by adding a row. -/
theorem app_image {E₀ : Term → Prop} {n : Nat} {b : Term} {Q : List (List (Term × List Term × Term))}
    (nQ : NormOk E E₀ den n b Q) {I : List V → Prop} (len : ∀ x, I x → x.length = n) (ne : ∃ x, I x) (v : V) :
    (∃ q ∈ Q, FunSem.App I (fun _ => True) (semP den q) v) ↔ ImgB E₀ den n b I v := by
  constructor
  · rintro ⟨q, mq, app⟩
    obtain ⟨x, hx, -, hall⟩ := (FunSem.app_iff _ I _ ne v).mp app
    obtain ⟨N, -, lv, sat⟩ := nQ.live q mq
    rw [lineEmpty_iff_none] at lv
    obtain ⟨g, hg⟩ := Classical.not_forall.mp lv
    obtain ⟨vg, hab⟩ := Classical.not_imp.mp hg
    obtain ⟨allP, noN⟩ := Classical.not_not.mp hab
    let row : FunSem.Row V := (x.map some, some v)
    refine ⟨row :: g, fun r mr => ?_, sat _ (fun p mp r mr => ?_) (fun q' mq' h => noN q' mq' fun r mr =>
      h r (List.mem_cons_of_mem _ mr)), x, hx, List.mem_cons_self⟩
    · rcases List.mem_cons.mp mr with rfl | mr
      · exact ⟨by simp [row, len x hx], fun h => by simp [row] at h⟩
      · exact vg r mr
    · rcases List.mem_cons.mp mr with rfl | mr
      · exact (allows_row p x v).mpr (hall p mp)
      · exact allP p mp r mr
  · rintro ⟨g, vg, hg, x, hx, mr⟩
    obtain ⟨q, mq, allP⟩ := nQ.cover g vg hg
    exact ⟨q, mq, (FunSem.app_iff _ I _ ne v).mpr ⟨x, hx, trivial, fun p mp => (allows_row p x v).mp (allP p mp _ mr)⟩⟩

end

theorem normalize_both_ok {X : List (Term × Term)} (F : Term) (hF : mapLookup X (.atom "fun") = some F)
    (hneg : ∀ R, F ≠ .tuple #[.atom "negation", R]) {d : Dispatcher} {len res : Term}
    (h : Elixir.Module.Types.Descr.«fun_normalize_both/3» d (.map X) (.atom "nil") len = .ok res)
    (shape : ∃ dom a₁ a₂, res = .tuple #[.atom "ok", dom, a₁, a₂])
    (norm : ∀ r₀, Elixir.Module.Types.Descr.«fun_normalize/2» d (.map X) len = .ok r₀ →
      ∀ a b c, r₀ ≠ .tuple #[.atom "ok", a, b, c]) :
    ∃ dom a, res = .tuple #[.atom "ok", dom, a, a] ∧
      Elixir.Module.Types.Descr.«fun_normalize/2» d (.map X) len = .ok (.tuple #[.atom "ok", dom, a]) ∧
      Elixir.Module.Types.Descr.«fun_other_non_empty_arities/2» d (.map X) len = .ok .nil := by
  obtain ⟨dom, a₁, a₂, rfl⟩ := shape
  rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def] at h
  have hm : (match getMapKeys [Term.atom "fun"] (Term.map X) with
      | [Term.tuple ⟨[Term.atom "negation", _]⟩] => (0 : Nat)
      | _ => 1) = 1 := by
    rw [getMapKeys_single, hF]
    split
    · rename_i h'; simp at h'; subst h'; exact absurd rfl (hneg _)
    · rfl
  simp [getMapKeys_single, hF] at h
  split at h
  · rename_i R _ e; simp only [List.cons.injEq, and_true] at e; exact absurd e (hneg _)
  cases hn : Elixir.Module.Types.Descr.«fun_normalize/2» d (.map X) len with
  | error err => simp [hn] at h
  | ok r₀ =>
    simp only [hn, Lynx.Except.ok_bind] at h
    split at h
    · rename_i sd sa
      cases ho : Elixir.Module.Types.Descr.«fun_other_non_empty_arities/2» d (.map X) len with
      | error err => simp [ho] at h
      | ok o =>
        simp only [ho, Lynx.Except.ok_bind] at h
        split at h
        · simp only [Except.ok.injEq] at h
          exact ⟨sd, sa, h.symm, rfl, rfl⟩
        · split at h
          · contradiction
          · simp at h
    · split at h
      · simp at h
      · split at h
        · contradiction
        · exact absurd (Except.ok.inj h) (norm r₀ hn _ _ _)

theorem normalize_both_neg {X : List (Term × Term)} {R : Term}
    (hF : mapLookup X (.atom "fun") = some (.tuple #[.atom "negation", R])) {d : Dispatcher} {len res : Term}
    (h : Elixir.Module.Types.Descr.«fun_normalize_both/3» d (.map X) (.atom "nil") len = .ok res) :
    ∀ a b c, res ≠ .tuple #[.atom "ok", a, b, c] := by
  intro a b c e
  subst e
  rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def] at h
  simp [getMapKeys_single, hF] at h
  cases hn : Elixir.Module.Types.Descr.«fun_negation_arities/1» d (.map X) <;> simp [hn] at h

/-- The static branch of `fun_apply_with_strategy/4`, once the arguments are not empty and the function normalizes:
the arguments are in the domain, and the arrows apply to them. -/
theorem strategy_ok {X : List (Term × Term)} {args : List Term} {d : Dispatcher} {dom a r : Term}
    (hany : Erlang.lists.«any/2» d (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) (Term.list args) =
      .ok (.atom "false"))
    (hnb : Elixir.Module.Types.Descr.«fun_normalize_both/3» d (.map X) (.atom "nil") (.integer args.length) =
      .ok (.tuple #[.atom "ok", dom, a, a]))
    {T Y : List (Term × Term)} (hT : Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list args) = .ok (.map T))
    (sT : mapLookup T (.atom "dynamic") = none) (hdom : dom = .map Y) (sY : mapLookup Y (.atom "dynamic") = none)
    (hall : Erlang.lists.«all/2» d (.function false "Elixir.Module.Types.Descr" "-fun_apply_with_strategy/4-fun-0-" 1 #[])
      (Term.list args) = .ok (.atom "true"))
    (run : Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» d (.map X) (.atom "nil") (Term.list args) s =
      .ok (.tuple #[.atom "ok", r])) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.map T) (.map Y) = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«fun_apply_static/2» d (Term.list args) a = .ok r := by
  subst hdom
  unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» at run
  simp [hany, length_list, hnb, hT, hall, getMapKeys_single, sT, sY] at run
  cases hs : Elixir.Module.Types.Descr.«subtype?/2» d (.map T) (.map Y) with
  | error e => simp [hs] at run
  | ok v =>
    simp only [hs, Lynx.Except.ok_bind] at run
    split at run
    · refine ⟨rfl, ?_⟩
      unfold Elixir.Module.Types.Descr.«fun_apply_result/5» at run
      cases hf : Elixir.Module.Types.Descr.«fun_apply_static/2» d (Term.list args) a <;>
        simp_all [Erlang.erlang.«/=/2», Lynx.Except.andAlso]
    · simp [Elixir.Module.Types.Descr.«domain_to_flat_args/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso] at run
    · simp at run

theorem strategy_needs {X : List (Term × Term)} {args : List Term} {d : Dispatcher} {r : Term}
    (hany : Erlang.lists.«any/2» d (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) (Term.list args) =
      .ok (.atom "false"))
    {nb : Term} (hnb : Elixir.Module.Types.Descr.«fun_normalize_both/3» d (.map X) (.atom "nil") (.integer args.length) =
      .ok nb) (n2 : ∀ x, nb ≠ .tuple #[.atom "ok", x])
    (run : Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» d (.map X) (.atom "nil") (Term.list args) s =
      .ok (.tuple #[.atom "ok", r])) :
    ∃ dom a₁ a₂, nb = .tuple #[.atom "ok", dom, a₁, a₂] := by
  unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» at run
  simp [hany, length_list, hnb] at run
  split at run
  · exact ⟨_, _, _, rfl⟩
  · simp only [Except.ok.injEq] at run
    exact absurd run (n2 r)

/-- `fun_apply_with_strategy/4` with non-empty arguments returns what fails to normalize. -/
theorem strategy_fail {X : List (Term × Term)} {args : List Term} {d : Dispatcher}
    (hany : Erlang.lists.«any/2» d (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) (Term.list args) =
      .ok (.atom "false"))
    {nb : Term} (hnb : Elixir.Module.Types.Descr.«fun_normalize_both/3» d (.map X) (.atom "nil") (.integer args.length) =
      .ok nb) (n4 : ∀ a b c, nb ≠ .tuple #[.atom "ok", a, b, c]) :
    Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» d (.map X) (.atom "nil") (Term.list args) s =
      .ok nb := by
  unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4»
  simp [hany, length_list, hnb]
  done

/-- The static branch of `fun_apply_with_strategy/4` succeeds when the arguments are in the domain. -/
theorem strategy_run {X : List (Term × Term)} {args : List Term} {d : Dispatcher} {a r : Term}
    (hany : Erlang.lists.«any/2» d (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) (Term.list args) =
      .ok (.atom "false"))
    {T Y : List (Term × Term)}
    (hnb : Elixir.Module.Types.Descr.«fun_normalize_both/3» d (.map X) (.atom "nil") (.integer args.length) =
      .ok (.tuple #[.atom "ok", .map Y, a, a]))
    (hT : Elixir.Module.Types.Descr.«args_to_domain/1» (Term.list args) = .ok (.map T))
    (sT : mapLookup T (.atom "dynamic") = none) (sY : mapLookup Y (.atom "dynamic") = none)
    (hall : Erlang.lists.«all/2» d (.function false "Elixir.Module.Types.Descr" "-fun_apply_with_strategy/4-fun-0-" 1 #[])
      (Term.list args) = .ok (.atom "true"))
    (sub : Elixir.Module.Types.Descr.«subtype?/2» d (.map T) (.map Y) = .ok (.atom "true"))
    (app : Elixir.Module.Types.Descr.«fun_apply_static/2» d (Term.list args) a = .ok r) :
    Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» d (.map X) (.atom "nil") (Term.list args) s =
      .ok (.tuple #[.atom "ok", r]) := by
  unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4»
  simp [hany, length_list, hnb, hT, hall, getMapKeys_single, sT, sY, sub]
  unfold Elixir.Module.Types.Descr.«fun_apply_result/5»
  simp [app, Erlang.erlang.«/=/2», Lynx.Except.andAlso]

section
variable {t : Term} {n : Nat}

/-- `fun_apply/2` on a static map: `:badfun` unless it only holds functions. -/
theorem apply_head {X : List (Term × Term)} (hd : mapLookup X (.atom "dynamic") = none) (args : Term) {m : Nat}
    {fo : Bool} (run : Elixir.Module.Types.Descr.«fun_only?/1» (D m) (.map X) = .ok (boolAtom fo)) :
    Elixir.Module.Types.Descr.«fun_apply/3» (D m) (.map X) args s =
      if fo then Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» (D m) (.map X) (.atom "nil") args s
      else .ok (.atom "badfun") := by
  rw [Elixir.Module.Types.Descr.«fun_apply/3».eq_def]
  cases fo <;> simp [Erlang.maps.«take/2», hd, run, boolAtom]

/-- Arguments of static applications: element types of the level, below the height `H`, that are the top type or
static maps. -/
def ArgOk (t : Term) (n H : Nat) (a : Term) : Prop :=
  (level t n).E a ∧ lh a < H ∧ (a = .atom "term" ∨ ∃ Y, a = .map Y ∧ mapLookup Y (.atom "dynamic") = none)

theorem argOk_static {H : Nat} {a : Term} (h : ArgOk t n H a) : Static a := by
  rcases h.2.2 with rfl | ⟨Y, rfl, hY⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨Y, rfl, hY⟩)

/-- Function fields of types of the next level are BDDs of arrows below the height of the type. -/
theorem arityBdds_of {H : Nat} {X R : List (Term × Term)} (hlX : lh (.map X) < H)
    (hF : mapLookup X (.atom "fun") = some (.tuple #[.atom "union", .map R])) (bR : AllBddP (FunArityN (level t n).E) R)
    (kR : NatKeys R) : ArityBdds (EB (level t n).E H) R := by
  intro q v hv
  obtain ⟨a, ha⟩ := kR q (by rw [hv]; rfl)
  refine ⟨a, ha, LitB (level t n).E v a, fun x hx => funLit_mono (fun e he => ⟨he.1, ?_⟩) hx, litB_of (bR q v hv) ha⟩
  have h₁ := lookup_lh hv
  have h₂ := lh_field_le hF
  have h₃ := lh_tag Bool.true R
  simp only [ite_true] at h₃
  have := he.2
  omega

/-- What a successful static application of a static map of functions establishes: the map holds no other point,
its functions have the arity of the arguments, and the arrow from the arguments to the result holds them. -/
theorem apply_ok_facts {H : Nat} (one : 1 ≤ H) {X : List (Term × Term)} (hX : DE (level t n).E (.map X))
    (hlX : lh (.map X) < H) {args : List Term} (hargs : ∀ a ∈ args, ArgOk t n H a) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«fun_apply/3» (D m) (.map X) (Term.list args) s = .ok (.tuple #[.atom "ok", r])) :
    (level t n).E r ∧ Static r ∧ (∀ v : PN t n, v.1.1 ≠ "fun" → ¬denD (.map X) v) ∧
      ∀ (a : Nat) g, (∀ row ∈ g, FunSem.ValidRow a row) → FunIn t n X a g →
        a = args.length ∧ ∀ row ∈ g, FunSem.Allows (args.map (level t n).den, (level t n).den r) row := by
  have ef := (level t n).ef
  obtain ⟨X', eX, sX⟩ : ∃ X', Term.map X = .map X' ∧ DescrC (FunA (level t n).E) (TField (level t n).E)
      (LF (level t n).E) (MField (level t n).E) X' := by
    rcases hX with h | h
    · cases h
    · exact h
  simp only [Term.map.injEq] at eX
  subst eX
  have fe : FunElem (EB (level t n).E H) (level t n).den ((level t n).K + 6) (.map []) :=
    (felem (level t n).ef (level t n).ef.subc one (safeN_nil H)).mono (by omega)
  have fd := fdom (level t n).ef one (safeT_nil (H + 1))
  have hE : ∀ a, EB (level t n).E H a → (level t n).E a := fun a h => h.1
  have cg : DenCongr (level t n).E (level t n).den := (level t n).ef.congrE
  have argE : ∀ a ∈ args, EB (level t n).E H a := fun a ma => ⟨(hargs a ma).1, (hargs a ma).2.1⟩
  -- Only functions.
  have fo := fun_only_run hX (m := m) (by omega)
  rw [apply_head sX.static _ fo] at run
  split at run
  case isFalse => cases run
  rename_i only
  have only : ∀ v : PN t n, v.1.1 ≠ "fun" → ¬denD (.map X) v := bp_true.mp only
  -- Non-empty arguments.
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have anyE : Erlang.lists.«any/2» (D (m' + 1)) (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[]) (Term.list args) =
      .ok (boolAtom (args.any (isEmpty (level t n).den))) :=
    any_list _ _ _ _ _ _ fun a ma => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:empty?/1».pure]
      exact fe.empty1 (argE a ma) m' (by omega)
  have strat := run
  cases hA : args.any (isEmpty (level t n).den)
  case true =>
    unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» at run
    simp [anyE, hA, boolAtom] at run
  clear run
  have ne : ∀ a ∈ args, ∃ v, (level t n).den a v := fun a ma => by
    have := List.any_eq_false.mp hA a ma
    simp only [Bool.not_eq_true, isEmpty, decide_eq_false_iff_not, Classical.not_forall, Classical.not_not] at this
    exact this
  have anyF : Erlang.lists.«any/2» (D (m' + 1)) (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[])
      (Term.list args) = .ok (.atom "false") := by rw [anyE, hA]; rfl
  -- Results of `fun_normalize_both/3` that are not `{:ok, _}` or `{:ok, _, _, _}` are returned.
  have fails : ∀ nb, Elixir.Module.Types.Descr.«fun_normalize_both/3» (D (m' + 1)) (.map X) (.atom "nil")
      (.integer args.length) = .ok nb → (∀ x, nb ≠ .tuple #[.atom "ok", x]) → (∀ a b c, nb ≠ .tuple #[.atom "ok", a, b, c]) →
      False := fun nb hnb n2 n4 => by
    rw [strategy_fail anyF hnb n4] at strat
    exact n2 r (Except.ok.inj strat)
  cases hF : mapLookup X (.atom "fun") with
  | none =>
    refine (fails (.atom "badfun") ?_ (fun x e => by cases e) (fun a b c e => by cases e)).elim
    have hn : Elixir.Module.Types.Descr.«fun_normalize/2» (D (m' + 1)) (.map X) (.integer args.length) =
        .ok (.atom "badfun") := by
      rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]
      simp [getMapKeys_single, hF]
    rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
    simp [getMapKeys_single, hF, hn]
  | some F =>
    rcases sX.fields "fun" F hF with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
    obtain ⟨pos, R, rfl, -, bR, kR⟩ := fF
    cases pos
    case false =>
      exfalso
      simp only [Bool.false_eq_true, ite_false] at hF
      cases hnb : Elixir.Module.Types.Descr.«fun_normalize_both/3» (D (m' + 1)) (.map X) (.atom "nil")
          (.integer args.length) with
      | error e =>
        unfold Elixir.Module.Types.Descr.«fun_apply_with_strategy/4» at strat
        simp [anyF, length_list, hnb] at strat
      | ok nb =>
        have n4 := normalize_both_neg hF hnb
        rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def] at hnb
        simp [getMapKeys_single, hF] at hnb
        cases hz : Elixir.Module.Types.Descr.«fun_negation_arities/1» (D (m' + 1)) (.map X) with
        | error e => simp [hz] at hnb
        | ok z =>
          simp only [hz, Lynx.Except.ok_bind, Except.ok.injEq] at hnb
          subst hnb
          refine fails _ ?_ (fun x e => by simp at e) n4
          rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
          simp [getMapKeys_single, hF, hz]
    simp only [ite_true] at hF
    have hR := arityBdds_of hlX hF bR kR
    obtain ⟨nb, rnb, cs⟩ := normalize_both_union fe fd cg hE hF hR args.length
    have hnb := rnb (m' + 1) (by omega)
    rcases cs with ⟨b, dom, Q, hb, nQ, neQ, hdom, sdom, others, rfl⟩ | ⟨n2, n4, -, -⟩
    case inr => exact (fails nb hnb n2 n4).elim
    -- The domain of the arguments.
    obtain ⟨td, htd, rtd, std⟩ := fd.dom args argE
    obtain ⟨T, rfl⟩ := fd.isMap htd
    obtain ⟨Y, rfl⟩ := fd.isMap hdom
    have stat : ∀ {Z : List (Term × Term)}, DomA (level t n).E H (.map Z) → mapLookup Z (.atom "dynamic") = none := by
      intro Z hZ
      obtain ⟨-, Z', e, sZ, -⟩ := hZ
      simp only [Term.map.injEq] at e
      subst e
      exact sZ.static
    have hall : Erlang.lists.«all/2» (D (m' + 1))
        (.function false "Elixir.Module.Types.Descr" "-fun_apply_with_strategy/4-fun-0-" 1 #[]) (Term.list args) =
        .ok (.atom "true") := by
      have := all_list (D (m' + 1)) _ _ _ (fun _ => Bool.true) args fun a ma => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_with_strategy/4-fun-0-/1».pure]
        rcases (hargs a ma).2.2 with rfl | ⟨Z, rfl, sZ⟩
        · rfl
        · simp [Elixir.Module.Types.Descr.«-fun_apply_with_strategy/4-fun-0-/1», unfold_map,
            Erlang.erlang.«is_map_key/2», any_key, sZ, Erlang.erlang.«not/1», boolAtom]
      simpa [boolAtom] using this
    obtain ⟨sub, stat'⟩ := strategy_ok anyF hnb (rtd) (stat htd) rfl (stat hdom) hall strat
    have incl : ∀ x, ddenA (level t n).E (level t n).den (.map T) x → ddenA (level t n).E (level t n).den (.map Y) x := by
      have := (dom_sub htd hdom (m := m' + 1) (by omega)).symm.trans sub
      have := bp_true.mp (by simpa [boolAtom] using this)
      exact this
    obtain ⟨r', hr', rr', sr'⟩ := apply_static_lines fe args.length args argE ne rfl Q.reverse
      (fun q mq => nQ.pos q (List.mem_reverse.mp mq))
    have er : r = r' := by
      have := (stat'.symm.trans (rr' (m' + 1) (by omega)))
      exact Except.ok.inj this
    subst er
    refine ⟨hr'.1, (level t n).ef.static hr'.1, only, fun a g vg hin => ?_⟩
    obtain ⟨F', hF', ar⟩ := hin
    rw [hF] at hF'
    cases hF'
    have ev : evalR R (.integer a) (valF (level t n).E (level t n).den g) = Bool.true := by
      simpa [arityOf, evalR] using ar
    by_cases ha : a = args.length
    · subst ha
      refine ⟨rfl, ?_⟩
      have eb : eval (valF (level t n).E (level t n).den g) b = Bool.true := by
        simpa [evalR, hb] using ev
      obtain ⟨q, mq, allP⟩ := nQ.cover g vg eb
      obtain ⟨w, hw⟩ := inDomR_exists (args.map (level t n).den) fun u mu => by
        obtain ⟨a, ma, rfl⟩ := List.mem_map.mp mu
        exact ne a ma
      refine fun row mrow => app_allows args rfl ⟨w, hw⟩ q (nQ.pos q mq) (fun x hx => ?_) _ (fun v hv => ?_) row
        (vg row mrow) (fun p mp => allP p mp row mrow)
      · exact (sdom x).mp (incl x ((std x).mpr hx)) q mq
      · exact (sr' v).mpr ⟨q, List.mem_reverse.mpr mq, hv⟩
    · have := others a g vg ha
      rw [this] at ev
      cases ev

end

theorem arguments_ok : ∀ {args nested : Term}, «arguments?/2» args nested = .ok (.atom "true") →
    ∃ l, args = Term.list l ∧ ∀ a ∈ l, «arrows_static?/2» a nested = .ok (.atom "true")
  | .cons a rest, nested, h => by
    unfold «arguments?/2» at h
    obtain ⟨h₁, h₂⟩ := (Lynx.Except.andAlso_eq_true _ _ _).mp h
    obtain ⟨l, rfl, hl⟩ := arguments_ok h₂
    refine ⟨a :: l, rfl, fun x mx => ?_⟩
    rcases List.mem_cons.mp mx with rfl | mx
    · exact h₁
    · exact hl x mx
  | .nil, _, _ => ⟨[], rfl, by simp⟩
  | .atom _, _, h | .integer _, _, h | .float _, _, h | .tuple _, _, h | .map _, _, h | .pid _, _, h
  | .reference _, _, h | .function .., _, h | .bitstring .., _, h => by
    unfold «arguments?/2» at h; simp at h

theorem lh_le_max (l : List Term) : ∀ a ∈ l, lh a ≤ (l.map lh).foldr max 0 :=
  fun a ma => foldr_max_le.mp (Nat.le_refl _) (lh a) (List.mem_map.mpr ⟨a, ma, rfl⟩)

section
variable {t : Term}

/-- Arguments of the laws, types of one level below the function, are arguments of static applications. -/
theorem argOk_of {d H : Nat} {a : Term} (h : DE (level t d).E a) (hl : lh a < H) : ArgOk t (d + 1) H a := by
  refine ⟨Or.inl h, hl, ?_⟩
  rcases h with rfl | ⟨X, rfl, sX⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨X, rfl, sX.static⟩

/-- A successful static application: the function is in the arrow from the arguments to the result, and in the top
function of their arity. -/
theorem apply_ok_sub {d : Nat} {fn : Term} {l : List Term} (hf : DE (level t (d + 1)).E fn)
    (hl : ∀ a ∈ l, DE (level t d).E a) {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«fun_apply/3» (D m) fn (Term.list l) s = .ok (.tuple #[.atom "ok", r])) :
    (∃ F, Elixir.Module.Types.Descr.«fun/2» (D m) (Term.list l) r = .ok F ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) fn F = .ok (.atom "true")) ∧
    Elixir.Module.Types.Descr.«subtype?/2» (D m)
      fn (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer l.length, .atom "bdd_top")]])]) = .ok (.atom "true") := by
  rcases hf with rfl | ⟨X, rfl, sX⟩
  · rw [Elixir.Module.Types.Descr.«fun_apply/3».eq_def] at run
    simp at run
  let H := max (lh (.map X)) ((l.map lh).foldr max 0) + 1
  have hX : DE (level t (d + 1)).E (.map X) := Or.inr ⟨X, rfl, sX⟩
  have args : ∀ a ∈ l, ArgOk t (d + 1) H a := fun a ma =>
    argOk_of (hl a ma) (by have := lh_le_max l a ma; omega)
  obtain ⟨er, sr, only, facts⟩ := apply_ok_facts (H := H) (by omega) hX (by omega) args hm run
  obtain ⟨k, -, fr⟩ := fun2_run l (fun a ma => argOk_static (args a ma)) sr
  have hm' : (level t (d + 1)).K + 23 ≤ m := by omega
  refine ⟨⟨_, fr m (by omega), ?_⟩, ?_⟩
  · have ad := arrow_de l (fun a ma => (args a ma).1) er k
    rw [next_sub hX ad hm', bp_true.mpr (subN_funs.mpr ⟨fun v f hv => absurd hv (only v f), fun a g vg hin => ?_⟩)]
    · rfl
    rw [funIn_arrow l (fun a ma => (args a ma).1) er k a g]
    exact facts a g vg hin
  · rw [next_sub hX (top_de l.length) hm', bp_true.mpr (subN_funs.mpr ⟨fun v f hv => absurd hv (only v f),
      fun a g vg hin => (funIn_top a l.length g).mpr (facts a g vg hin).1⟩)]
    rfl

end

section
variable {t : Term}

theorem inhabited_ok {d : Nat} {m : Nat} (hm : (level t d).K + 23 ≤ m) : ∀ (l : List Term),
    (∀ a ∈ l, DE (level t d).E a) → «inhabited?/1» (D m) (Term.list l) = .ok (.atom "true") →
      ∀ a ∈ l, ∃ v : PN t d, denD a v
  | [], _, _ => by simp
  | a :: l, hl, h => by
    unfold «inhabited?/1» at h
    rw [next_empty (hl a List.mem_cons_self) hm] at h
    by_cases e : ∀ v : PN t d, ¬denD a v
    · rw [bp_true.mpr e] at h; simp [boolAtom] at h
    · rw [bp_false.mpr e] at h
      simp only [boolAtom, Bool.false_eq_true, ite_false, Lynx.Except.ok_bind] at h
      have rest := inhabited_ok hm l (fun x mx => hl x (List.mem_cons_of_mem _ mx)) h
      intro x mx
      rcases List.mem_cons.mp mx with rfl | mx
      · exact Classical.byContradiction fun ne => e fun v hv => ne ⟨v, hv⟩
      · exact rest x mx

theorem funTopMap_de {n : Nat} : DE (level t n).E (.map [(.atom "fun", funTopT)]) := by
  refine Or.inr ⟨_, rfl, ⟨fun q h => ?_, fun name x h => ?_⟩⟩
  · by_cases e : compareExact (fuel q (.atom "fun")) q (.atom "fun") = .eq
    · exact ⟨"fun", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [mapLookup, e] at h
  · by_cases e : name = "fun"
    · subst e
      simp [mapLookup] at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨rfl, funA_top⟩))
    · simp [mapLookup, e] at h

theorem denD_funTop {n : Nat} (v : PN t n) : denD (.map [(.atom "fun", funTopT)]) v ↔ v.1.1 = "fun" := by
  rw [denD_map]
  by_cases e : v.1.1 = "fun"
  · simp [mapLookup, e, dn_funTop]
  · simp [mapLookup, e, dn_none]

/-- Static application of empty functions, or of types with other points than functions, to non-empty arguments
is `:badfun`. -/
theorem apply_badfun {n H : Nat} (one : 1 ≤ H) {fn : Term} (hX : DE (level t n).E fn) (hlX : lh fn < H)
    {args : List Term} (hargs : ∀ a ∈ args, ArgOk t n H a) (inh : ∀ a ∈ args, ∃ v, (level t n).den a v)
    (bad : (∀ v : PN t n, ¬denD fn v) ∨ ¬∀ v : PN t n, denD fn v → v.1.1 = "fun") {m : Nat}
    (hm : (level t n).K + 30 ≤ m) :
    Elixir.Module.Types.Descr.«fun_apply/3» (D m) fn (Term.list args) s = .ok (.atom "badfun") := by
  rcases hX with rfl | ⟨X, rfl, sX⟩
  · rw [Elixir.Module.Types.Descr.«fun_apply/3».eq_def]
    rfl
  have hX : DE (level t n).E (.map X) := Or.inr ⟨X, rfl, sX⟩
  have fe : FunElem (EB (level t n).E H) (level t n).den ((level t n).K + 6) (.map []) :=
    (felem (level t n).ef (level t n).ef.subc one (safeN_nil H)).mono (by omega)
  have fd := fdom (level t n).ef one (safeT_nil (H + 1))
  have hE : ∀ a, EB (level t n).E H a → (level t n).E a := fun a h => h.1
  have cg : DenCongr (level t n).E (level t n).den := (level t n).ef.congrE
  rw [apply_head sX.static _ (fun_only_run hX (m := m) (by omega))]
  split
  case isFalse => rfl
  rename_i only
  have only : ∀ v : PN t n, v.1.1 ≠ "fun" → ¬denD (.map X) v := bp_true.mp only
  have empty : ∀ v : PN t n, ¬denD (.map X) v := by
    rcases bad with h | h
    · exact h
    · exact absurd (fun v hv => Classical.byContradiction fun f => only v f hv) h
  have noFun : ∀ (a : Nat) g, (∀ r ∈ g, FunSem.ValidRow a r) → ¬FunIn t n X a g := fun a g vg h =>
    empty _ ((denD_fpt a g vg).mpr h)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have anyF : Erlang.lists.«any/2» (D (m' + 1)) (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[])
      (Term.list args) = .ok (.atom "false") := by
    rw [any_list _ _ _ _ (isEmpty (level t n).den) _ fun a ma => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:empty?/1».pure]
      exact fe.empty1 ⟨(hargs a ma).1, (hargs a ma).2.1⟩ m' (by omega)]
    have : args.any (isEmpty (level t n).den) = Bool.false := List.any_eq_false.mpr fun a ma h => by
      obtain ⟨v, hv⟩ := inh a ma
      exact (isEmpty_iff _ a).mp h v hv
    rw [this]; rfl
  cases hF : mapLookup X (.atom "fun") with
  | none =>
    have hn : Elixir.Module.Types.Descr.«fun_normalize/2» (D (m' + 1)) (.map X) (.integer args.length) =
        .ok (.atom "badfun") := by
      rw [Elixir.Module.Types.Descr.«fun_normalize/2».eq_def]
      simp [getMapKeys_single, hF]
    refine strategy_fail anyF ?_ (fun a b c e => by cases e)
    rw [Elixir.Module.Types.Descr.«fun_normalize_both/3».eq_def]
    simp [getMapKeys_single, hF, hn]
  | some F =>
    rcases sX.fields "fun" F hF with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
    obtain ⟨pos, R, rfl, -, bR, kR⟩ := fF
    cases pos
    case false =>
      exfalso
      obtain ⟨a, ha⟩ := fresh_arities R
      exact noFun a [] (by simp) ⟨_, hF, by simp [arityOf, ha a (Nat.le_refl _)]⟩
    simp only [ite_true] at hF
    have hR := arityBdds_of hlX hF bR kR
    obtain ⟨nb, rnb, cs⟩ := normalize_both_union fe fd cg hE hF hR args.length
    rcases cs with ⟨b, dom, Q, hb, nQ, neQ, -, -, -, -⟩ | ⟨n2, n4, bf, -⟩
    · exfalso
      obtain ⟨g, vg, hg⟩ := normOk_live nQ neQ
      exact noFun _ g vg ⟨_, hF, by simp [arityOf, hb, hg]⟩
    · have : nb = .atom "badfun" := bf.mpr fun a g vg => by
        cases h : evalR R (.integer a) (valF (level t n).E (level t n).den g)
        · rfl
        · exact (noFun a g vg ⟨_, hF, by simpa [arityOf, evalR] using h⟩).elim
      rw [← this]
      exact strategy_fail anyF (rnb (m' + 1) (by omega)) n4

/-- The law on `:badfun`, for functions one level above the arguments. -/
theorem apply_badfun_law {d : Nat} {fn : Term} {l : List Term} (hf : DE (level t (d + 1)).E fn)
    (hl : ∀ a ∈ l, DE (level t d).E a) {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m)
    (inh : «inhabited?/1» (D m) (Term.list l) = .ok (.atom "true"))
    (bad : Lynx.Except.orElse (Elixir.Module.Types.Descr.«empty?/1» (D m) fn)
      (do
        let f ← Elixir.Module.Types.Descr.«fun/0»
        let s ← Elixir.Module.Types.Descr.«subtype?/2» (D m) fn f
        Erlang.erlang.«not/1» s) true = .ok (.atom "true")) :
    Elixir.Module.Types.Descr.«fun_apply/3» (D m) fn (Term.list l) s = .ok (.atom "badfun") := by
  have hm' : (level t (d + 1)).K + 23 ≤ m := by omega
  have hd : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  have ne := inhabited_ok hd l hl inh
  have sub := next_sub hf (funTopMap_de (t := t) (n := d + 1)) hm'
  simp only [Elixir.Module.Types.Descr.«fun/0», next_empty hf hm', funTopT] at bad sub
  simp only [pure, Except.pure, Lynx.Except.ok_bind, sub] at bad
  have bad' : (∀ v : PN t (d + 1), ¬denD fn v) ∨ ¬∀ v : PN t (d + 1), denD fn v → v.1.1 = "fun" := by
    by_cases e : ∀ v : PN t (d + 1), ¬denD fn v
    · exact Or.inl e
    · refine Or.inr fun h => ?_
      have s : SubN t (d + 1) fn (.map [(.atom "fun", .tuple #[.atom "negation", .map []])]) := fun v hv =>
        (denD_funTop v).mpr (h v hv)
      rw [bp_false.mpr e, bp_true.mpr s] at bad
      simp [Lynx.Except.orElse, boolAtom, Erlang.erlang.«not/1»] at bad
  let H := max (lh fn) ((l.map lh).foldr max 0) + 1
  exact apply_badfun (H := H) (by omega) hf (by omega)
    (fun a ma => argOk_of (hl a ma) (by have := lh_le_max l a ma; omega))
    (fun a ma => by obtain ⟨v, hv⟩ := ne a ma; exact ⟨v, (den_succ (hl a ma) v).mpr hv⟩) bad' hm

/-- Static application of a non-empty static map of functions in the arrow from non-empty arguments to `term()`
succeeds. -/
theorem apply_domain {n H : Nat} (one : 1 ≤ H) {X : List (Term × Term)} (hX : DE (level t n).E (.map X))
    (hlX : lh (.map X) < H) {args : List Term} (hargs : ∀ a ∈ args, ArgOk t n H a)
    (inh : ∀ a ∈ args, ∃ v, (level t n).den a v) (ne : ∃ v : PN t n, denD (.map X) v)
    (only : ∀ v : PN t n, v.1.1 ≠ "fun" → ¬denD (.map X) v)
    (arrow : ∀ (a : Nat) g, (∀ r ∈ g, FunSem.ValidRow a r) → FunIn t n X a g →
      a = args.length ∧ ∀ row ∈ g, FunSem.Allows (args.map (level t n).den, (level t n).den (.atom "term")) row)
    {m : Nat} (hm : (level t n).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D m) (.map X) (Term.list args) s = .ok (.tuple #[.atom "ok", r]) := by
  obtain ⟨X', eX, sX⟩ : ∃ X', Term.map X = .map X' ∧ DescrC (FunA (level t n).E) (TField (level t n).E)
      (LF (level t n).E) (MField (level t n).E) X' := by
    rcases hX with h | h
    · cases h
    · exact h
  simp only [Term.map.injEq] at eX
  subst eX
  have fe : FunElem (EB (level t n).E H) (level t n).den ((level t n).K + 6) (.map []) :=
    (felem (level t n).ef (level t n).ef.subc one (safeN_nil H)).mono (by omega)
  have fd := fdom (level t n).ef one (safeT_nil (H + 1))
  have hE : ∀ a, EB (level t n).E H a → (level t n).E a := fun a h => h.1
  have cg : DenCongr (level t n).E (level t n).den := (level t n).ef.congrE
  have argE : ∀ a ∈ args, EB (level t n).E H a := fun a ma => ⟨(hargs a ma).1, (hargs a ma).2.1⟩
  rw [apply_head sX.static _ (fun_only_run hX (m := m) (by omega))]
  simp only [bp_true.mpr only, ite_true]
  -- Some function of the map, of the arity of the arguments.
  obtain ⟨a₀, g₀, vg₀, in₀⟩ : ∃ (a : Nat) (g : List (FunSem.Row (level t n).V)),
      (∀ r ∈ g, FunSem.ValidRow a r) ∧ FunIn t n X a g := by
    obtain ⟨v, hv⟩ := ne
    by_cases f : v.1.1 = "fun"
    · obtain ⟨a, g, vg, e⟩ := pt_fun v f
      exact ⟨a, g, vg, (e X).mp hv⟩
    · exact absurd hv (only v f)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have anyF : Erlang.lists.«any/2» (D (m' + 1)) (.function false "Elixir.Module.Types.Descr" "empty?" 1 #[])
      (Term.list args) = .ok (.atom "false") := by
    rw [any_list _ _ _ _ (isEmpty (level t n).den) _ fun a ma => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:empty?/1».pure]
      exact fe.empty1 (argE a ma) m' (by omega)]
    have : args.any (isEmpty (level t n).den) = Bool.false := List.any_eq_false.mpr fun a ma h => by
      obtain ⟨v, hv⟩ := inh a ma
      exact (isEmpty_iff _ a).mp h v hv
    rw [this]; rfl
  obtain ⟨F, hF, ar₀⟩ := in₀
  rcases sX.fields "fun" F hF with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, fF⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> try (simp at e; done)
  obtain ⟨pos, R, rfl, -, bR, kR⟩ := fF
  cases pos
  case false =>
    exfalso
    obtain ⟨a, ha⟩ := fresh_arities R
    have := (arrow (max a (args.length + 1)) [] (by simp)
      ⟨_, hF, by simp [arityOf, ha (max a (args.length + 1)) (by omega)]⟩).1
    omega
  simp only [ite_true] at hF
  have hR := arityBdds_of hlX hF bR kR
  have arityIn : ∀ (a : Nat) g, (∀ r ∈ g, FunSem.ValidRow a r) →
      evalR R (.integer a) (valF (level t n).E (level t n).den g) = Bool.true →
      a = args.length ∧ ∀ row ∈ g, FunSem.Allows (args.map (level t n).den, (level t n).den (.atom "term")) row :=
    fun a g vg h => arrow a g vg ⟨_, hF, by simpa [arityOf, evalR] using h⟩
  obtain ⟨nb, rnb, cs⟩ := normalize_both_union fe fd cg hE hF hR args.length
  rcases cs with ⟨b, dom, Q, hb, nQ, neQ, hdom, sdom, -, rfl⟩ | ⟨-, -, -, dead | ⟨a, g, vg, ha, h⟩⟩
  rotate_left
  · exfalso
    have ev : evalR R (.integer a₀) (valF (level t n).E (level t n).den g₀) = Bool.true := by
      simpa [arityOf, evalR] using ar₀
    obtain rfl := (arityIn a₀ g₀ vg₀ ev).1
    rw [dead g₀ vg₀] at ev
    cases ev
  · exact absurd (arityIn a g vg h).1 ha
  have hnb := rnb (m' + 1) (by omega)
  obtain ⟨td, htd, rtd, std⟩ := fd.dom args argE
  obtain ⟨T, rfl⟩ := fd.isMap htd
  obtain ⟨Y, rfl⟩ := fd.isMap hdom
  have stat : ∀ {Z : List (Term × Term)}, DomA (level t n).E H (.map Z) → mapLookup Z (.atom "dynamic") = none := by
    intro Z hZ
    obtain ⟨-, Z', e, sZ, -⟩ := hZ
    simp only [Term.map.injEq] at e
    subst e
    exact sZ.static
  have hall : Erlang.lists.«all/2» (D (m' + 1))
      (.function false "Elixir.Module.Types.Descr" "-fun_apply_with_strategy/4-fun-0-" 1 #[]) (Term.list args) =
      .ok (.atom "true") := by
    have := all_list (D (m' + 1)) _ _ _ (fun _ => Bool.true) args fun a ma => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_apply_with_strategy/4-fun-0-/1».pure]
      rcases (hargs a ma).2.2 with rfl | ⟨Z, rfl, sZ⟩
      · rfl
      · simp [Elixir.Module.Types.Descr.«-fun_apply_with_strategy/4-fun-0-/1», unfold_map,
          Erlang.erlang.«is_map_key/2», any_key, sZ, Erlang.erlang.«not/1», boolAtom]
    simpa [boolAtom] using this
  -- Arguments outside the domain of a line: a function of the line that fails on them is in the map, and not in
  -- the arrow to `term()`.
  have cover : ∀ x, FunSem.InDomR (args.map (level t n).den) x → ∀ q ∈ Q, ∃ p ∈ semP (level t n).den q,
      FunSem.InDomR p.1 x := by
    intro x hx q mq
    refine Classical.byContradiction fun none => ?_
    obtain ⟨N, -, lv, sat⟩ := nQ.live q mq
    rw [lineEmpty_iff_none] at lv
    obtain ⟨g, hg⟩ := Classical.not_forall.mp lv
    obtain ⟨vg, hab⟩ := Classical.not_imp.mp hg
    obtain ⟨allP, noN⟩ := Classical.not_not.mp hab
    have lx : x.length = args.length := by have := FunSem.inDomR_length hx; simpa using this
    -- Every arrow of the line covers the empty list of arguments.
    obtain ⟨v, x', rfl⟩ : ∃ v x', x = v :: x' := by
      cases x with
      | cons v x' => exact ⟨v, x', rfl⟩
      | nil =>
        exfalso
        obtain ⟨p, mp⟩ := List.exists_mem_of_ne_nil q (nQ.nonempty q mq)
        have lp : p.2.1.length = 0 := by rw [(nQ.pos q mq p mp).2.2]; simp at lx; omega
        exact none ⟨_, List.mem_map.mpr ⟨p, mp, rfl⟩, by simp [List.length_eq_zero_iff.mp lp, FunSem.InDomR]⟩
    let row : FunSem.Row (level t n).V := ((v :: x').map some, Option.none)
    have vrow : FunSem.ValidRow args.length row := by
      refine ⟨by simp only [row, List.length_map]; exact lx, fun h => ?_⟩
      have e := h.1
      simp only [row] at e
      rw [← lx] at e
      simp [List.replicate_succ] at e
    have allP' : ∀ p ∈ semP (level t n).den q, ∀ r ∈ row :: g, FunSem.Allows p r := by
      intro p mp r mr
      rcases List.mem_cons.mp mr with rfl | mr
      · intro hd; exact absurd ⟨p, mp, (FunSem.inDom_real p.1 _).mp hd⟩ none
      · exact allP p mp r mr
    have noN' : ∀ q' ∈ semP (level t n).den N, ¬∀ r ∈ row :: g, FunSem.Allows q' r := fun q' mq' h =>
      noN q' mq' fun r mr => h r (List.mem_cons_of_mem _ mr)
    have ev := sat (row :: g) allP' noN'
    have vg' : ∀ r ∈ row :: g, FunSem.ValidRow args.length r := fun r mr => by
      rcases List.mem_cons.mp mr with rfl | mr
      · exact vrow
      · exact vg r mr
    obtain ⟨y, e, -⟩ := (arityIn args.length (row :: g) vg' (by simp [evalR, hb, ev])).2 row List.mem_cons_self
      ((FunSem.inDom_real _ _).mpr hx)
    cases e
  have incl : ∀ x, ddenA (level t n).E (level t n).den (.map T) x → ddenA (level t n).E (level t n).den (.map Y) x :=
    fun x hx => (sdom x).mpr (cover x ((std x).mp hx))
  have sub : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) (.map T) (.map Y) = .ok (.atom "true") := by
    rw [dom_sub htd hdom (by omega), bp_true.mpr incl]; rfl
  obtain ⟨r, -, rr, -⟩ := apply_static_lines fe args.length args argE inh rfl Q.reverse
    (fun q mq => nQ.pos q (List.mem_reverse.mp mq))
  exact ⟨r, strategy_run anyF hnb rtd (stat htd) (stat hdom) hall sub (rr _ (by omega))⟩

/-- The law on successful applications, for functions one level above the arguments. -/
theorem apply_domain_law {d : Nat} {fn : Term} {l : List Term} (hf : DE (level t (d + 1)).E fn)
    (hl : ∀ a ∈ l, DE (level t d).E a) {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m)
    (inh : «inhabited?/1» (D m) (Term.list l) = .ok (.atom "true"))
    (ne : (do
      let e ← Elixir.Module.Types.Descr.«empty?/1» (D m) fn
      Erlang.erlang.«not/1» e) = .ok (.atom "true"))
    (sub : (do
      let tm ← Elixir.Module.Types.Descr.«term/0»
      let F ← Elixir.Module.Types.Descr.«fun/2» (D m) (Term.list l) tm
      Elixir.Module.Types.Descr.«subtype?/2» (D m) fn F) = .ok (.atom "true")) :
    ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D m) fn (Term.list l) s = .ok (.tuple #[.atom "ok", r]) := by
  have hm' : (level t (d + 1)).K + 23 ≤ m := by omega
  have hd : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  have inh := inhabited_ok hd l hl inh
  let H := max (lh fn) ((l.map lh).foldr max 0) + 1
  have args : ∀ a ∈ l, ArgOk t (d + 1) H a := fun a ma =>
    argOk_of (hl a ma) (by have := lh_le_max l a ma; omega)
  obtain ⟨k, -, fr⟩ := fun2_run l (fun a ma => argOk_static (args a ma)) (Or.inl rfl)
  have ad := arrow_de (t := t) (n := d + 1) l (fun a ma => (args a ma).1) (level t (d + 1)).ef.term k
  simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, Lynx.Except.ok_bind, fr m (by omega),
    next_sub hf ad hm'] at sub
  have sub : SubN t (d + 1) fn _ := bp_true.mp (by simpa [boolAtom] using sub)
  simp only [next_empty hf hm', Lynx.Except.ok_bind] at ne
  have ne : ∃ v : PN t (d + 1), denD fn v := by
    refine Classical.byContradiction fun none => ?_
    rw [bp_true.mpr fun v hv => none ⟨v, hv⟩] at ne
    simp [boolAtom, Erlang.erlang.«not/1»] at ne
  rcases hf with rfl | ⟨X, rfl, sX⟩
  · -- The top type holds tuples, which no arrow holds.
    have := sub (tpt []) (denD_term _)
    rw [denD_map] at this
    simp [tpt, mapLookup, dn_none] at this
  obtain ⟨only, funs⟩ := subN_funs.mp sub
  exact apply_domain (H := H) (by omega) (Or.inr ⟨X, rfl, sX⟩) (by omega) args
    (fun a ma => by obtain ⟨v, hv⟩ := inh a ma; exact ⟨v, (den_succ (hl a ma) v).mpr hv⟩) ne
    (fun v f hv => by
      have := only v f hv
      rw [denD_map] at this
      simp [mapLookup, f, dn_none] at this)
    (fun a g vg hin => (funIn_arrow l (fun a ma => (args a ma).1) (level t (d + 1)).ef.term k a g).mp (funs a g vg hin))
    hm

end

end Elixir.STTDescrProofsTest.Nest
