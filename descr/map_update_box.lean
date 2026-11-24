namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- Updates with a constant field: a type, whether it is optional, and what to do with absent keys. -/
abbrev cOp (nt : Term) (nopt : Bool) (md : String) : Term :=
  .tuple #[.tuple #[.atom "constant", .tuple #[nt, boolAtom nopt]], .atom md]

/-- The modes of updates. -/
def Mode (md : String) : Prop := md = "force" ∨ md = "keep" ∨ md = "reject"

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The new field of an update of a key whose old field allows `Old`: the new field where the key held a value,
and where it was absent, the new field when forcing or absence when keeping. -/
def NewF (den : Term → V → Prop) (nt : Term) (nopt : Bool) (md : String) (Old : Option V → Prop) (o : Option V) : Prop :=
  ((∃ x, Old (some x)) ∧ ((o = none ∧ nopt = Bool.true) ∨ ∃ x, o = some x ∧ den nt x)) ∨
    (Old none ∧ ((md = "force" ∧ ((o = none ∧ nopt = Bool.true) ∨ ∃ x, o = some x ∧ den nt x)) ∨
      (md = "keep" ∧ o = none)))

theorem update_field_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) {old : Term} (ho : FieldValue E old) :
    ∃ F, Elixir.Module.Types.Descr.«map_update_field/2» (D m) old (cOp nt nopt md) = .ok F ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ NewF den nt nopt md (FieldSem den old) o := by
  obtain ⟨t, opt, rfl, ht⟩ := ho
  obtain ⟨e, re, se⟩ := ef.empty1 (m := m) hm ht
  have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
  -- The present part and the absent part.
  let pt : Term := if e then .map [] else nt
  let po : Bool := if e then Bool.false else nopt
  let at' : Term := if opt ∧ md = "force" then nt else .map []
  let ao : Bool := if opt ∧ md = "force" then nopt else if opt ∧ md = "keep" then Bool.true else Bool.false
  have hpt : E pt := by by_cases h : e = Bool.true <;> simp [pt, h, ef.none, hnt]
  have hat : E at' := by by_cases h : opt = Bool.true ∧ md = "force" <;> simp only [at', h] <;> simp [ef.none, hnt]
  obtain ⟨F, hF, rF, sF⟩ := field_opt_union_val (den := den) ef (m := m) hm (f₁ := .tuple #[pt, boolAtom po])
    (f₂ := .tuple #[at', boolAtom ao]) rfl rfl hpt hat []
  refine ⟨_, ?_, ⟨F, po || ao, rfl, hF⟩, fun o => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_field/2»
    simp only [Elixir.Module.Types.Descr.«map_update_apply_callback/3», re, Lynx.Except.ok_bind]
    rcases hmd with rfl | rfl | rfl <;> cases e <;> cases opt <;> cases nopt <;>
      simp [Lynx.Term.isMember, boolAtom, Erlang.program.«Elixir.Module.Types.Descr:-map_update_field/2-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-map_update_field/2-fun-0-/3», pt, at', po, ao] at rF ⊢ <;> exact rF
  · have ne : (∃ x, FieldSem den (.tuple #[t, boolAtom opt]) (some x)) ↔ e = Bool.false := by
      simp only [fieldSem_mk, reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or]
      constructor
      · rintro ⟨x, hx⟩; cases e; rfl; exact absurd hx (se.mp rfl x)
      · intro h; subst h
        exact Classical.byContradiction fun nx => by
          have := se.mpr fun y hy => nx ⟨y, hy⟩; cases this
    have abs : FieldSem den (.tuple #[t, boolAtom opt]) none ↔ opt = Bool.true := by simp [fieldSem_mk]
    rw [sF, NewF, ne, abs]
    simp only [fieldSem_mk]
    rcases hmd with rfl | rfl | rfl <;> cases e <;> cases opt <;> cases nopt <;>
      simp [pt, po, at', ao, nn]

/-- The values an update puts at the keys of a kind: the new type, when forcing or when some line's tag gives the
kind a value. -/
def NewDom (den : Term → V → Prop) (lines : List Term) (nt : Term) (md : String) (kind : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ ∃ L ∈ lines, ∃ y, LineTag den L kind y)

/-- What the tag of the box allows at the keys of a kind, for any constant update. -/
def BoxTagG (den : Term → V → Prop) (lines : List Term) (nt : Term) (md : String) (Ds : List String) (kind : String)
    (x : V) : Prop :=
  (∃ L ∈ lines, LineTag den L kind x) ∨ (kind ∈ Ds ∧ NewDom den lines nt md kind x)

/-- Kinds whose update field is not empty. -/
def DomNE (den : Term → V → Prop) (lines : List Term) (nt : Term) (nopt : Bool) (md : String) (kind : String) : Prop :=
  md = "keep" ∨ ((md = "force" ∨ ∃ L ∈ lines, ∃ y, LineTag den L kind y) ∧ (nopt = Bool.true ∨ ∃ x, den nt x))

/-- A domain update of `map_update_box/6`: an updated kind whose new field is not empty, the type the lines give it,
and the new type. -/
def DomUpdG (E : Term → Prop) (den : Term → V → Prop) (lines : List Term) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (u : Term) : Prop :=
  ∃ d o t, u = .tuple #[.atom d, o, t] ∧ d ∈ Ds ∧ DomNE den lines nt nopt md d ∧ E o ∧ E t ∧
    (∀ x, den o x ↔ ∃ L ∈ lines, LineTag den L d x) ∧ ∀ x, den t x ↔ NewDom den lines nt md d x

/-- The fold of `map_update_box/6` over the kinds of keys, for any constant update: the tag, and the updated
domains. -/
theorem box_domains_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K + 3 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) {nt : Term} (hnt : E nt) (nopt : Bool) {md : String} (hmd : Mode md)
    (Ds : List String) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ T U, Erlang.lists.«foldl/3» (D (n + 1))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-7-" 2
          #[Term.list lines, Term.list (Ds.map Term.atom), cOp nt nopt md])
        (.tuple #[.atom "closed", .nil]) (Term.list (domainKinds.map Term.atom)) = .ok (.tuple #[T, Term.list U]) ∧
      LowTag E T (.atom "zzz") ∧
      (∀ kind ∈ domainKinds, ∀ x, den (tagType T kind) x ↔ BoxTagG den lines nt md Ds kind x) ∧
      (∀ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ E t) ∧
      ((∃ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ↔ ∃ d ∈ Ds, ∃ x, NewDom den lines nt md d x) ∧
      (U ≠ [] ↔ ∃ d ∈ Ds, DomNE den lines nt nopt md d) ∧ (∀ u ∈ U, DomUpdG E den lines nt nopt md Ds u) ∧
      (∀ d ∈ Ds, DomNE den lines nt nopt md d → ∃ u ∈ U, ∃ o t, u = .tuple #[.atom d, o, t]) := by
  have nn : ∀ x, ¬den (.map []) x := fun x h => ef.den_none x h
  let R : List Term → Term → Prop := fun pre a => ∃ T U, a = .tuple #[T, Term.list U] ∧
    (∀ d', (∀ p ∈ pre, Term.compare (Term.fuel p d') p d' = .lt) → LowTag E T d') ∧
    (∀ kind x, den (tagType T kind) x ↔ .atom kind ∈ pre ∧ BoxTagG den lines nt md Ds kind x) ∧
    (∀ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ E t) ∧
    ((∃ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ↔
      ∃ d ∈ Ds, .atom d ∈ pre ∧ ∃ x, NewDom den lines nt md d x) ∧
    (U ≠ [] ↔ ∃ d ∈ Ds, .atom d ∈ pre ∧ DomNE den lines nt nopt md d) ∧
    (∀ u ∈ U, DomUpdG E den lines nt nopt md Ds u) ∧
    (∀ d ∈ Ds, .atom d ∈ pre → DomNE den lines nt nopt md d → ∃ u ∈ U, ∃ o t, u = .tuple #[.atom d, o, t])
  obtain ⟨r, ⟨T, U, rfl, low, sem, du, pu, ne, dg, cv⟩, run⟩ := foldl_prefix_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-map_update_box/6-fun-7-" #[Term.list lines, Term.list (Ds.map Term.atom), cOp nt nopt md] R
    (domainKinds.map Term.atom)
    (fun pre x rest a e ⟨T, U, ha, low, sem, du, pu, ne, dg, cv⟩ => by
      subst ha
      have mx : x ∈ domainKinds.map Term.atom := by rw [← e]; simp
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mx
      have before : ∀ p ∈ pre, Term.compare (Term.fuel p (.atom d)) p (.atom d) = .lt := by
        have := kinds_sorted; rw [← e, List.pairwise_append] at this
        exact fun p mp => this.2.2 p mp _ List.mem_cons_self
      have notPre : Term.atom d ∉ pre := fun m => by
        have := before _ m
        rw [Lynx.Term.compare_self] at this
        cases this
      obtain ⟨old, rold, hold, sold⟩ := get_domain1 ef (n := n) (by omega) lines hl d
      have pureE : ∀ a, (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-7-" 2
          #[Term.list lines, Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.atom d, a] =
          Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5» (D n) (Term.list lines) (Term.list (Ds.map Term.atom))
            (cOp nt nopt md) (.atom d) a := fun a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-7-/2».pure]
      -- The kind's new type and the updates, then the tag.
      have finish : ∀ type U', E type → (∀ x, den type x ↔ den old x ∨ (d ∈ Ds ∧ NewDom den lines nt md d x)) →
          (∀ u ∈ U', ∃ d o t, u = .tuple #[d, o, t] ∧ E t) →
          ((∃ u ∈ U', ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ↔
            (∃ u ∈ U, ∃ d o t, u = .tuple #[d, o, t] ∧ ∃ x, den t x) ∨ (d ∈ Ds ∧ ∃ x, NewDom den lines nt md d x)) →
          (U' ≠ [] ↔ U ≠ [] ∨ (d ∈ Ds ∧ DomNE den lines nt nopt md d)) →
          (∀ u ∈ U', DomUpdG E den lines nt nopt md Ds u) →
          (∀ d' ∈ Ds, .atom d' ∈ pre ++ [.atom d] → DomNE den lines nt nopt md d' →
            ∃ u ∈ U', ∃ o t, u = .tuple #[.atom d', o, t]) →
          ∃ T', Elixir.Module.Types.Descr.«map_replace_domain/3» (D n) T (.atom d) type = .ok T' ∧
            R (pre ++ [.atom d]) (.tuple #[T', Term.list U']) := fun type U' hty stype du' pu' ne' dg' cv' => by
        obtain ⟨T', rT, low', sT'⟩ := replace_domain ef hd (low _ before) hty n
        refine ⟨T', rT, T', U', rfl, fun d' h => low' d' (h _ (by simp)), fun kind x => ?_, du', ?_, ?_, dg', cv'⟩
        · rw [sT']
          by_cases k : kind = d
          · subst k
            rw [ite_eq_left rfl, stype, sold]
            simp only [BoxTagG, List.mem_append, List.mem_singleton, or_true, true_and]
          · rw [ite_eq_right k, sem]
            simp [k]
        · rw [pu', pu]
          constructor
          · rintro (⟨d', md', hm, hx⟩ | ⟨md', hx⟩)
            · exact ⟨d', md', List.mem_append_left _ hm, hx⟩
            · exact ⟨d, md', by simp, hx⟩
          · rintro ⟨d', md', hm, hx⟩
            rcases List.mem_append.mp hm with hm | hm
            · exact Or.inl ⟨d', md', hm, hx⟩
            · simp at hm; subst hm; exact Or.inr ⟨md', hx⟩
        · rw [ne', ne]
          constructor
          · rintro (⟨d', md', hm, hx⟩ | ⟨md', hx⟩)
            · exact ⟨d', md', List.mem_append_left _ hm, hx⟩
            · exact ⟨d, md', by simp, hx⟩
          · rintro ⟨d', md', hm, hx⟩
            rcases List.mem_append.mp hm with hm | hm
            · exact Or.inl ⟨d', md', hm, hx⟩
            · simp at hm; subst hm; exact Or.inr ⟨md', hx⟩
      have mem := member_atoms d Ds
      by_cases up : d ∈ Ds
      · simp only [up, ↓reduceIte] at mem
        obtain ⟨F, rF, hF, sF⟩ := update_field_gen ef (m := n) (by omega) hnt nopt hmd
          (old := .tuple #[old, .atom "true"]) ⟨old, Bool.true, rfl, hold⟩
        obtain ⟨ft, fo, rfl, hft⟩ := hF
        have hn : FieldSem den (.tuple #[old, .atom "true"]) none := by
          rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
        have sOld : (∃ x, FieldSem den (.tuple #[old, .atom "true"]) (some x)) ↔ ∃ L ∈ lines, ∃ y, LineTag den L d y := by
          rw [show (Term.atom "true") = boolAtom Bool.true from rfl]
          simp only [fieldSem_mk, reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or]
          exact ⟨fun ⟨y, hy⟩ => let ⟨L, mL, h⟩ := (sold y).mp hy; ⟨L, mL, y, h⟩,
            fun ⟨L, mL, y, h⟩ => ⟨y, (sold y).mpr ⟨L, mL, h⟩⟩⟩
        have sft : ∀ x, den ft x ↔ NewDom den lines nt md d x := fun x => by
          have := sF (some x)
          rw [fieldSem_mk] at this
          simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or] at this
          rw [this, NewF, NewDom, sOld]
          simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or]
          constructor
          · rintro (⟨ho, hx⟩ | ⟨-, (⟨rfl, hx⟩ | ⟨-, h⟩)⟩)
            · exact ⟨hx, Or.inr ho⟩
            · exact ⟨hx, Or.inl rfl⟩
            · cases h
          · rintro ⟨hx, rfl | ho⟩
            · exact Or.inr ⟨hn, Or.inl ⟨rfl, hx⟩⟩
            · exact Or.inl ⟨ho, hx⟩
        obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef (m := n) (by omega) ⟨ft, fo, rfl, hft⟩
        have neF : b = Bool.false ↔ DomNE den lines nt nopt md d := by
          rw [← Bool.not_eq_true, sb, DomNE]
          simp only [Classical.not_forall, Classical.not_not]
          constructor
          · rintro ⟨o, ho⟩
            rcases (sF o).mp ho with ⟨hold', hv'⟩ | ⟨-, (⟨rfl, hv'⟩ | ⟨rfl, -⟩)⟩
            · rcases hv' with ⟨-, h⟩ | ⟨x, -, hx⟩
              · exact Or.inr ⟨Or.inr (sOld.mp hold'), Or.inl h⟩
              · exact Or.inr ⟨Or.inr (sOld.mp hold'), Or.inr ⟨x, hx⟩⟩
            · rcases hv' with ⟨-, h⟩ | ⟨x, -, hx⟩
              · exact Or.inr ⟨Or.inl rfl, Or.inl h⟩
              · exact Or.inr ⟨Or.inl rfl, Or.inr ⟨x, hx⟩⟩
            · exact Or.inl rfl
          · rintro (rfl | ⟨hf, hv'⟩)
            · exact ⟨none, (sF none).mpr (Or.inr ⟨hn, Or.inr ⟨rfl, rfl⟩⟩)⟩
            · rcases hv' with h | ⟨x, hx⟩
              · rcases hf with rfl | ho
                · exact ⟨none, (sF none).mpr (Or.inr ⟨hn, Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩⟩)⟩
                · exact ⟨none, (sF none).mpr (Or.inl ⟨sOld.mpr ho, Or.inl ⟨rfl, h⟩⟩)⟩
              · rcases hf with rfl | ho
                · exact ⟨some x, (sF _).mpr (Or.inr ⟨hn, Or.inl ⟨rfl, Or.inr ⟨x, rfl, hx⟩⟩⟩)⟩
                · exact ⟨some x, (sF _).mpr (Or.inl ⟨sOld.mpr ho, Or.inr ⟨x, rfl, hx⟩⟩)⟩
        cases b
        · obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hold hft (m := n) (by omega)
          obtain ⟨T', rT, hR⟩ := finish c (.tuple #[.atom d, old, ft] :: U) hc
            (fun x => by rw [sc, sft]; simp [up]) (fun u mu => by
              rcases List.mem_cons.mp mu with rfl | mu
              · exact ⟨_, _, _, rfl, hft⟩
              · exact du u mu)
            (by
              constructor
              · rintro ⟨u, mu, d', o, t, rfl, x, hx⟩
                rcases List.mem_cons.mp mu with e | mu
                · obtain ⟨-, -, rfl⟩ := tuple3_inj e; exact Or.inr ⟨up, x, (sft x).mp hx⟩
                · exact Or.inl ⟨_, mu, d', o, t, rfl, x, hx⟩
              · rintro (⟨u, mu, h⟩ | ⟨-, x, hx⟩)
                · exact ⟨u, List.mem_cons_of_mem _ mu, h⟩
                · exact ⟨_, List.mem_cons_self, _, _, _, rfl, x, (sft x).mpr hx⟩)
            (by simp [up, neF.mp rfl])
            (fun u mu => by
              rcases List.mem_cons.mp mu with rfl | mu
              · exact ⟨d, old, ft, rfl, up, neF.mp rfl, hold, hft, sold, sft⟩
              · exact dg u mu)
            (fun d' md' hp hne => by
              rcases List.mem_append.mp hp with hp | hp
              · obtain ⟨u, mu, h⟩ := cv d' md' hp hne; exact ⟨u, List.mem_cons_of_mem _ mu, h⟩
              · simp at hp; subst hp; exact ⟨_, List.mem_cons_self, _, _, rfl⟩)
          refine ⟨_, hR, ?_⟩
          rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5», rold, mem, Term.true,
            rF, Elixir.Module.Types.Descr.«opt_union/2», rc]
          rw [rb]
          simp [boolAtom, rT]
        · have nF : ¬DomNE den lines nt nopt md d := fun h => by have := neF.mpr h; cases this
          have nNew : ∀ x, ¬NewDom den lines nt md d x := fun x hx => by
            have := (sb.mp rfl) (some x)
            exact this ((sF _).mpr (by
              rcases hx.2 with rfl | ho
              · exact Or.inr ⟨hn, Or.inl ⟨rfl, Or.inr ⟨x, rfl, hx.1⟩⟩⟩
              · exact Or.inl ⟨sOld.mpr ho, Or.inr ⟨x, rfl, hx.1⟩⟩))
          obtain ⟨T', rT, hR⟩ := finish old U hold
            (fun x => ⟨Or.inl, fun h => h.elim id fun ⟨_, hx⟩ => absurd hx (nNew x)⟩) du
            ⟨Or.inl, fun h => h.elim id fun ⟨_, x, hx⟩ => absurd hx (nNew x)⟩
            ⟨Or.inl, fun h => h.elim id fun ⟨_, hx⟩ => absurd hx nF⟩ dg
            (fun d' md' hp hne => by
              rcases List.mem_append.mp hp with hp | hp
              · exact cv d' md' hp hne
              · simp at hp; subst hp; exact absurd hne nF)
          refine ⟨_, hR, ?_⟩
          rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5», rold, mem, Term.true, rF]
          rw [rb]
          simp [boolAtom, rT, Elixir.Module.Types.Descr.«-map_update_box/6-fun-6-/3»]
      · obtain ⟨T', rT, hR⟩ := finish old U hold
          (fun x => ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩) du
          ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩
          ⟨Or.inl, fun h => h.elim id fun ⟨a, _⟩ => absurd a up⟩ dg
          (fun d' md' hp hne => by
            rcases List.mem_append.mp hp with hp | hp
            · exact cv d' md' hp hne
            · simp at hp; subst hp; exact absurd md' up)
        refine ⟨_, hR, ?_⟩
        rw [pureE]
        have nm : Erlang.lists.«member/2» (.atom d) (Term.list (Ds.map Term.atom)) = .ok (.atom "false") := by
          simpa [up, Term.false] using mem
        simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-7-/5», rold, nm, rT,
          Elixir.Module.Types.Descr.«-map_update_box/6-fun-6-/3»,
          Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-6-/1».pure])
    _ ⟨.atom "closed", [], rfl, fun _ _ => Or.inl rfl, fun kind x => by simp [tagType, nn], fun u mu => by simp at mu,
      by simp, by simp, by simp, by simp⟩
  have allIn : ∀ d ∈ Ds, Term.atom d ∈ domainKinds.map Term.atom := fun d md => List.mem_map_of_mem (hD d md)
  refine ⟨T, U, run, low _ fun p mp => ?_, fun kind mk x => (sem kind x).trans ?_, du, pu.trans ?_, ne.trans ?_, dg,
    fun d md h => cv d md (allIn d md) h⟩
  · simp only [domainKinds, List.map, List.mem_cons, List.not_mem_nil, or_false] at mp
    rcases mp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp [List.mem_map, mk]
  · exact ⟨fun ⟨d, md, _, h⟩ => ⟨d, md, h⟩, fun ⟨d, md, h⟩ => ⟨d, md, allIn d md, h⟩⟩
  · exact ⟨fun ⟨d, md, _, h⟩ => ⟨d, md, h⟩, fun ⟨d, md, h⟩ => ⟨d, md, allIn d md, h⟩⟩

/-- An updated named key, for any constant update: the old field, as the lines hold it, and the new one. -/
def KeyUpdG (E : Term → Prop) (den : Term → V → Prop) (lines : List Term) (nt : Term) (nopt : Bool) (md : String)
    (s : String) (q : Term) : Prop :=
  ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldValue E old ∧ (∀ o, FieldSem den old o ↔ ∃ L ∈ lines, LongM den L s o) ∧
    FieldValue E new ∧ ∀ o, FieldSem den new o ↔ NewF den nt nopt md (FieldSem den old) o

/-- The fold of `map_update_box/6` over the named keys: their fields over the lines, and the updates of those
among the updated keys. -/
theorem box_fields_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {nt : Term} (hnt : E nt) (nopt : Bool) {md : String} (hmd : Mode md) (ks NK : List String)
    (nd : NK.Nodup) :
    ∃ P Q, Erlang.lists.«foldr/3» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-4-" 2
          #[Term.list lines, Term.list (ks.map Term.atom), cOp nt nopt md])
        (.tuple #[.nil, .nil]) (Term.list (NK.map Term.atom)) = .ok (.tuple #[fieldsTerm P, Term.list Q]) ∧
      P.map Prod.fst = NK.map Term.atom ∧
      (∀ e ∈ P, ∃ s, e.1 = .atom s ∧ FieldValue E e.2 ∧ ∀ o, FieldSem den e.2 o ↔ ∃ L ∈ lines, LongM den L s o) ∧
      (∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpdG E den lines nt nopt md s q) ∧
      (∀ s ∈ NK, s ∈ ks → ∃ q ∈ Q, KeyUpdG E den lines nt nopt md s q) ∧ (Q.map updKey).Nodup ∧
      ∀ q ∈ Q, updKey q ∈ NK.map Term.atom := by
  obtain ⟨r, ⟨P, Q, rfl, hP, fP, uQ, cQ, kQ, nQ⟩, run⟩ := foldr_rel_at (m := n + 4) "Elixir.Module.Types.Descr"
    "-map_update_box/6-fun-4-" #[Term.list lines, Term.list (ks.map Term.atom), cOp nt nopt md]
    (fun suf a => ∃ P Q, a = .tuple #[fieldsTerm P, Term.list Q] ∧ P.map Prod.fst = suf ∧
      (∀ e ∈ P, ∃ s, e.1 = .atom s ∧ FieldValue E e.2 ∧ ∀ o, FieldSem den e.2 o ↔ ∃ L ∈ lines, LongM den L s o) ∧
      (∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpdG E den lines nt nopt md s q) ∧
      (∀ s, .atom s ∈ suf → s ∈ ks → ∃ q ∈ Q, KeyUpdG E den lines nt nopt md s q) ∧ (∀ q ∈ Q, updKey q ∈ suf) ∧
      (Q.map updKey).Nodup) (NK.map Term.atom)
    (fun pre x suf a e ⟨P, Q, ha, hP, fP, uQ, cQ, kQ, nQ⟩ => by
      subst ha
      have mx : x ∈ NK.map Term.atom := by rw [← e]; simp
      have xs : x ∉ suf := by
        have : (NK.map Term.atom).Nodup := List.pairwise_map.mpr (nd.imp fun h e => h (Term.atom.inj e))
        rw [← e] at this
        exact (List.nodup_cons.mp (List.nodup_append.mp this).2.1).1
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp mx
      obtain ⟨old, rold, hold, sold⟩ := mdnf_fetch ef hn s lines hl
      have pureE : ∀ a, (D (n + 4)).pure (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-4-" 2
          #[Term.list lines, Term.list (ks.map Term.atom), cOp nt nopt md]) #[.atom s, a] =
          Elixir.Module.Types.Descr.«-map_update_box/6-fun-4-/5» (D (n + 3)) (Term.list lines)
            (Term.list (ks.map Term.atom)) (cOp nt nopt md) (.atom s) a := fun a => by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-4-/2».pure]
      have mem := member_atoms s ks
      by_cases sk : s ∈ ks
      · obtain ⟨F, rF, hF, sF⟩ := update_field_gen ef (m := n + 3) (by omega) hnt nopt hmd hold
        obtain ⟨ft, fo, rfl, hft⟩ := hF
        refine ⟨_, ⟨(.atom s, old) :: P, .tuple #[.atom s, old, .tuple #[ft, boolAtom fo]] :: Q, rfl, by simp [hP],
          fun e me => ?_, fun q mq => ?_, fun s' ms' hs' => ?_, fun q mq => ?_, ?_⟩, ?_⟩
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨s, rfl, hold, sold⟩
          · exact fP e me
        · rcases List.mem_cons.mp mq with rfl | mq
          · exact ⟨s, sk, old, _, rfl, hold, sold, ⟨ft, fo, rfl, hft⟩, sF⟩
          · exact uQ q mq
        · rcases List.mem_cons.mp ms' with e | ms'
          · cases e; exact ⟨_, List.mem_cons_self, old, _, rfl, hold, sold, ⟨ft, fo, rfl, hft⟩, sF⟩
          · obtain ⟨q, mq, hq⟩ := cQ s' ms' hs'
            exact ⟨q, List.mem_cons_of_mem _ mq, hq⟩
        · rcases List.mem_cons.mp mq with rfl | mq
          · simp [updKey]
          · exact List.mem_cons_of_mem _ (kQ q mq)
        · refine List.nodup_cons.mpr ⟨fun m => ?_, nQ⟩
          obtain ⟨q, mq, eq⟩ := List.mem_map.mp m
          obtain ⟨s', -, old', new', rfl, -⟩ := uQ q mq
          have := kQ _ mq
          simp only [updKey] at eq this
          rw [eq] at this
          exact xs this
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-4-/5», rold, mem, sk, rF, Term.true, fieldsTerm_cons]
      · refine ⟨_, ⟨(.atom s, old) :: P, Q, rfl, by simp [hP], fun e me => ?_, uQ, fun s' ms' hs' => ?_,
          fun q mq => List.mem_cons_of_mem _ (kQ q mq), nQ⟩, ?_⟩
        · rcases List.mem_cons.mp me with rfl | me
          · exact ⟨s, rfl, hold, sold⟩
          · exact fP e me
        · rcases List.mem_cons.mp ms' with e | ms'
          · cases e; exact absurd hs' sk
          · exact cQ s' ms' hs'
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-4-/5», rold, mem, sk, Term.false, fieldsTerm_cons])
    (.tuple #[.nil, .nil]) ⟨[], [], by simp [fieldsTerm, Term.list], rfl, by simp, by simp, by simp, by simp, by simp⟩
  exact ⟨P, Q, run, hP, fP, uQ, fun s ms hs => cQ s (List.mem_map_of_mem ms) hs, nQ, kQ⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem req_fields_any {l : List (Term × Term)} (hl : ∀ e ∈ l, FieldValue E e.2) (m : Nat) :
    ∃ b : Bool, Erlang.lists.«any/2» (D m) (.function "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-1-" 1 #[])
      (fieldsTerm l) = .ok (boolAtom b) ∧ (b = Bool.true ↔ ¬OptFields l) := by
  classical
  let res : Term → Bool := fun x => decide (∃ k t, x = .tuple #[k, .tuple #[t, .atom "false"]])
  have := any_list (D m) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-1-" #[] res
    (l.map fun e => .tuple #[e.1, e.2]) (fun x mx => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨t, o, he, -⟩ := hl e me
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-1-/1».pure]
      cases o <;> simp [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-1-/1», he, boolAtom,
        Erlang.erlang.«not/1», res])
  refine ⟨_, this, ?_⟩
  simp only [List.any_eq_true, List.mem_map, OptFields, Classical.not_forall, res, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨e, me, rfl⟩, k, t, he⟩
    simp only [Term.tuple.injEq] at he
    refine ⟨e, me, fun ⟨ty, h⟩ => ?_⟩
    have := congrArg (fun a : Array Term => a[1]?) he
    simp [h] at this
  · rintro ⟨e, me, h⟩
    obtain ⟨t, o, he, -⟩ := hl e me
    cases o
    · exact ⟨_, ⟨e, me, rfl⟩, e.1, t, by rw [he]; rfl⟩
    · exact absurd ⟨t, he⟩ h

/-- The check of `map_update_present?/3` keeping absent keys: whether no line holds the empty map. -/
theorem allNE_gen {m : Nat} (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) :
    ∃ b : Bool, Erlang.lists.«all/2» (D (m + 3)) (.function "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-4-" 1 #[])
      (Term.list lines) = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∀ L ∈ lines, ¬InMLine den L wNone) := by
  · obtain ⟨b, rb, sb⟩ := all_sem (K' := 2) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-4-" #[] lines
      (m := m + 3) (by omega) (fun L => ¬InMLine den L wNone)
      (fun m x => Elixir.Module.Types.Descr.«-map_update_present?/3-fun-4-/1» (D m) x)
      (fun m x => by rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-4-/1».pure])
      (fun L mL => by
        obtain ⟨tag, l, negs, rfl, -, sl, sn⟩ := hl L mL
        -- Literals of optional fields hold the empty map.
        have optAll : ∀ (l' : List (Term × Term)), FieldsV E l' → ∀ m, ∃ c : Bool,
            Erlang.lists.«all/2» (D (m + 1)) (.function "Elixir.Module.Types.Descr"
              "-map_update_present?/3-fun-2-" 1 #[]) (fieldsTerm l') = .ok (boolAtom c) ∧ (c = Bool.true ↔ OptFields l') := by
          intro l' sl' m
          obtain ⟨c, rc, sc⟩ := all_sem (K' := 0) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-2-" #[]
            (l'.map fun e => .tuple #[e.1, e.2]) (m := m + 1) (by omega)
            (fun x => ∃ k ty, x = .tuple #[k, .tuple #[ty, .atom "true"]])
            (fun _ x => Elixir.Module.Types.Descr.«-map_update_present?/3-fun-2-/1» x)
            (fun m x => by rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-2-/1».pure])
            (fun x mx => by
              obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
              obtain ⟨ty, o, he, -⟩ := (sl'.1 e me).2
              refine ⟨o, fun _ _ => by simp [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-2-/1», he], ?_⟩
              cases o <;> simp [he, boolAtom])
          refine ⟨c, rc, ?_⟩
          rw [sc]
          simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, OptFields]
          constructor
          · intro h e me
            obtain ⟨k, ty, he⟩ := h e me
            simp only [Term.tuple.injEq] at he
            have := congrArg (fun a : Array Term => a[1]?) he
            simp at this
            exact ⟨ty, this⟩
          · intro h e me
            obtain ⟨ty, he⟩ := h e me
            exact ⟨e.1, ty, by rw [he]⟩
        classical
        refine ⟨decide (¬InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) wNone), fun m hm1 => ?_,
          by simp⟩
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
        obtain ⟨c, rc, sc⟩ := any_sem (m := m + 2) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-3-" #[]
          (fun N => NSem den N wNone) negs (fun N mN => by
            obtain ⟨k, tag', l', rfl, -, sl'⟩ := sn N mN
            obtain ⟨c, rc, sc⟩ := optAll l' sl' m
            refine ⟨c, ?_, sc.trans ?_⟩
            · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-3-/1».pure]
              simpa [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-3-/1»] using rc
            · rw [← msem_none (den := den) (tag := tag') sl']
              exact ⟨fun h => ⟨k, tag', l', rfl, h⟩, fun ⟨k', t', l'', e, h⟩ => by
                obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
                cases e₂; rw [fieldsTerm_inj e₃]; exact h⟩)
        obtain ⟨r, rr, sr⟩ := req_fields_any (fun e me => (sl.1 e me).2) (m + 2)
        have eq : (r || c) = decide (¬InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) wNone) := by
          rw [inMLine_iff, msem_none (den := den) (tag := tag) sl]
          cases r <;> cases c <;> simp_all
        rw [← eq]
        simp only [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-4-/1», Lynx.Except.orElse, pure_bind]
        erw [rr]
        cases r
        · simp only [boolAtom, Bool.false_eq_true, ↓reduceIte]
          erw [rc]
          cases c <;> rfl
        · rfl)
    exact ⟨b, rb, sb⟩

/-- `map_update_present?/3` for any constant update: when keeping, whether no update removes all values and no line
holds the empty map; otherwise, whether some update gives a value. -/
theorem present_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (nt : Term) (nopt : Bool) {md : String} (hmd : Mode md) (ups : List Term)
    (hu : ∀ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ E o ∧ E n) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«map_update_present?/3» (D (m + 3)) (cOp nt nopt md) (Term.list lines)
        (Term.list ups) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ (md = "keep" → (¬∃ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ (∀ x, ¬den n x) ∧ ∃ x, den o x) ∧
          ∀ L ∈ lines, ¬InMLine den L wNone) ∧ (md ≠ "keep" → ∃ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ ∃ x, den n x)) := by
  by_cases mk : md = "keep"
  · subst mk
    obtain ⟨a, ra, sa⟩ := any_sem (m := m + 3) "Elixir.Module.Types.Descr" "-map_update_present?/3-fun-0-" #[]
      (fun p => ∃ o n, p = .tuple #[o, n] ∧ (∀ x, ¬den n x) ∧ ∃ x, den o x) ups (fun p mp => by
        obtain ⟨o, n, rfl, ho, hn⟩ := hu p mp
        obtain ⟨en, ren, sen⟩ := ef.empty1 (m := m + 2) (by omega) hn
        obtain ⟨eo, reo, seo⟩ := ef.empty1 (m := m + 2) (by omega) ho
        have neo : eo = Bool.false ↔ ∃ x, den o x := by
          constructor
          · intro h; subst h
            exact Classical.byContradiction fun nx => by have := seo.mpr fun y hy => nx ⟨y, hy⟩; cases this
          · rintro ⟨x, hx⟩; cases eo; rfl; exact absurd hx (seo.mp rfl x)
        refine ⟨en && !eo, ?_, ?_⟩
        · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_present?/3-fun-0-/1».pure]
          cases en <;> cases eo <;>
            simp [Elixir.Module.Types.Descr.«-map_update_present?/3-fun-0-/1», ren, reo, Lynx.Except.andAlso,
              Erlang.erlang.«not/1», boolAtom]
        · rw [Bool.and_eq_true, Bool.not_eq_true', neo, sen]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨o, n, rfl, h1, h2⟩
          · rintro ⟨o', n', e', h1, h2⟩
            obtain ⟨rfl, rfl⟩ : o' = o ∧ n' = n := by simp at e'; exact ⟨e'.1.symm, e'.2.symm⟩
            exact ⟨h1, h2⟩)
    obtain ⟨b, rb, sb⟩ := allNE_gen (den := den) (m := m) lines hl
    cases a
    · refine ⟨b, ?_, ?_⟩
      · simp [Elixir.Module.Types.Descr.«map_update_present?/3», ra, boolAtom, rb]
      · rw [sb]
        have : ¬∃ p ∈ ups, ∃ o n, p = .tuple #[o, n] ∧ (∀ x, ¬den n x) ∧ ∃ x, den o x := fun h => by
          have := sa.mpr h; cases this
        simp [this]
    · refine ⟨Bool.false, ?_, ?_⟩
      · simp [Elixir.Module.Types.Descr.«map_update_present?/3», ra, boolAtom]
      · constructor
        · intro h; cases h
        · intro h; exact absurd (sa.mp rfl) (h.1 rfl).1
  · have hmd' : md = "force" ∨ md = "reject" := by
      rcases hmd with h | h | h
      · exact Or.inl h
      · exact absurd h mk
      · exact Or.inr h
    obtain ⟨b, rb, sb⟩ := present_any (den := den) ef (m := m + 2) (by omega)
      (.tuple #[.atom "constant", .tuple #[nt, boolAtom nopt]]) md hmd' (Term.list lines) ups
      (fun p mp => let ⟨o, n, e, _, hn⟩ := hu p mp; ⟨o, n, e, hn⟩)
    refine ⟨b, rb, ?_⟩
    rw [sb]
    simp [mk]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem box_filter_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {lines : List Term} {nt : Term} {nopt : Bool} {md : String} {ks : List String}
    (Q : List Term) (uQ : ∀ q ∈ Q, ∃ s, s ∈ ks ∧ KeyUpdG E den lines nt nopt md s q) :
    ∃ Q', Erlang.lists.«filter/2» (D (m + 1)) (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-5-" 1 #[])
        (Term.list Q) = .ok (Term.list Q') ∧ Q'.Sublist Q ∧
      (∀ q ∈ Q, (∃ o, FieldSem den (updNew q) o) → q ∈ Q') ∧ ∀ q ∈ Q', ∃ o, FieldSem den (updNew q) o := by
  classical
  let res : Term → Bool := fun q => decide (∃ o, FieldSem den (updNew q) o)
  refine ⟨Q.filter res, filter_list _ _ _ _ res Q fun q mq => ?_, List.filter_sublist,
    fun q mq h => List.mem_filter.mpr ⟨mq, by simp [res, h]⟩, fun q mq => by
      have := (List.mem_filter.mp mq).2; simpa [res] using this⟩
  obtain ⟨s, -, old, new, rfl, -, -, hnew, -⟩ := uQ q mq
  obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef hm hnew
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-5-/1».pure]
  simp only [Elixir.Module.Types.Descr.«-map_update_box/6-fun-5-/1», rb, Lynx.Except.ok_bind]
  cases b
  · have : ∃ o, FieldSem den new o := Classical.byContradiction fun h => by
      have := sb.mpr fun o ho => h ⟨o, ho⟩; cases this
    simp [Erlang.erlang.«not/1», boolAtom, res, updNew, this]
  · have : ¬∃ o, FieldSem den new o := fun ⟨o, ho⟩ => sb.mp rfl o ho
    simp [Erlang.erlang.«not/1», boolAtom, res, updNew, this]

/-- The fold of `map_update_box/6` storing a single update, when replacing: the new field. -/
theorem box_store_rep {m : Nat} {P : List (Term × Term)} (sP : FieldsV E P) {s : String} {old new : Term}
    (fnew : FieldValue E new) :
    ∃ P2, Erlang.lists.«foldl/3» (D (m + 1)) (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-11-" 2
        #[.atom "true"]) (fieldsTerm P) (Term.list [.tuple #[.atom s, old, new]]) = .ok (fieldsTerm P2) ∧ FieldsV E P2 ∧
      mapLookup P2 (.atom s) = some new ∧ ∀ s', s' ≠ s → mapLookup P2 (.atom s') = mapLookup P (.atom s') := by
  obtain ⟨P3, rP3, sP3, -, look3⟩ := store_val s fnew sP
  refine ⟨P3, ?_, sP3, by rw [look3]; simp, fun s' ne => by rw [look3]; simp [Ne.symm ne]⟩
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-11-/2».pure,
    Elixir.Module.Types.Descr.«-map_update_box/6-fun-11-/3», Lynx.Term.isMember, rP3]


/-- The maps of the box of an update, for any constant update: at each named key its old values, unless replaced,
or the new field of the updated keys, and at other keys what the tag of the box allows. -/
def BoxSynG (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (R : String → Prop) (nt : Term)
    (nopt : Bool) (md : String) (Ds : List String) (w : MW V) : Prop :=
  (∀ s ∈ NK, (¬R s ∧ ∃ L ∈ lines, LongM den L s (w (.atom s))) ∨
      (s ∈ ks ∧ NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) (w (.atom s)))) ∧
  (∀ s, s ∉ NK → w (.atom s) = none ∨ ∃ x, w (.atom s) = some x ∧ BoxTagG den lines nt md Ds "atom" x) ∧
  ∀ k i, w (.dom k i) = none ∨ ∃ x, w (.dom k i) = some x ∧ BoxTagG den lines nt md Ds (domKind k) x

/-- Named keys whose update gives some field. -/
def KeyNE (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool) (md : String)
    (s : String) : Prop :=
  s ∈ NK ∧ s ∈ ks ∧ ∃ o, NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) o

/-- Whether an update has old values or new values at a named key or a kind, with `A` on whether each is held. -/
def UpdHas (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool) (md : String)
    (Ds : List String) (A : Prop → Prop → Prop) : Prop :=
  (∃ s, KeyNE den lines ks NK nt nopt md s ∧ A (∃ x, ∃ L ∈ lines, LongM den L s (some x))
      (∃ x, NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) (some x))) ∨
    ∃ d ∈ Ds, DomNE den lines nt nopt md d ∧ A (∃ x, ∃ L ∈ lines, LineTag den L d x) (∃ x, NewDom den lines nt md d x)

/-- Whether the box is among the updated maps: when keeping, no update removes the values of a key and no line holds
the empty map; otherwise, some update gives a value. -/
def BoxPresent (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool)
    (md : String) (Ds : List String) : Prop :=
  (md = "keep" → ¬UpdHas den lines ks NK nt nopt md Ds (fun o n => o ∧ ¬n) ∧ ∀ L ∈ lines, ¬InMLine den L wNone) ∧
    (md ≠ "keep" → UpdHas den lines ks NK nt nopt md Ds (fun _ n => n))

/-- Keeping absent keys with no key or kind holding old or new values: the maps are unchanged. -/
def BoxSame (den : Term → V → Prop) (lines : List Term) (ks NK : List String) (nt : Term) (nopt : Bool)
    (md : String) (Ds : List String) : Prop :=
  md = "keep" ∧ ¬UpdHas den lines ks NK nt nopt md Ds (fun o n => o ∨ n)

/-- The maps `map_update_box/6` gives, for any constant update. -/
def BoxRes (den : Term → V → Prop) (lines : List Term) (ks AK NK : List String) (R : String → Prop) (nt : Term)
    (nopt : Bool) (md : String) (Ds : List String) (w : MW V) : Prop :=
  ((∃ s, KeyNE den lines ks NK nt nopt md s) ∨ ∃ d ∈ Ds, DomNE den lines nt nopt md d) ∧
    (BoxSame den lines ks NK nt nopt md Ds → ∃ L ∈ lines, InMLine den L w) ∧
    (¬BoxSame den lines ks NK nt nopt md Ds → BoxSynG den lines ks NK R nt nopt md Ds w ∧
      (BoxPresent den lines ks NK nt nopt md Ds →
        ((nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12) → ¬UnsetSemD den ks AK Ds nt w) ∧
        (¬(nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12) → w ≠ wNone)))

/-- `map_update_box/6` for any constant update. -/
theorem box_runG (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term) (bdd : Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (fbd : MField E bdd)
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {nt : Term} (hnt : E nt)
    (snt : nt = .atom "term" ∨ ∃ Z, nt = .map Z) (nopt : Bool) {md : String} (hmd : Mode md)
    (ks AK Ds : List String) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ (NK : List String) (R : String → Prop) (res : Term), Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 4)) bdd (Term.list lines)
        (Term.list (ks.map Term.atom)) (Term.list (Ds.map Term.atom)) (cOp nt nopt md) (Term.list (AK.map Term.atom)) =
        .ok res ∧ (∀ s ∈ AK, s ∈ NK) ∧
      (∀ L ∈ lines, ∀ s, LineNames L s → s ∈ NK) ∧ (∀ s ∈ NK, s ∈ AK ∨ ∃ L ∈ lines, LineNames L s) ∧
      (∀ s, R s ↔ md = "reject" ∧ (∀ d ∈ Ds, ¬DomNE den lines nt nopt md d) ∧ KeyNE den lines ks NK nt nopt md s ∧
        ∀ s', KeyNE den lines ks NK nt nopt md s' → s' = s) ∧
      ∃ X, res = .map X ∧ MapsD E den X (BoxRes den lines ks AK NK R nt nopt md Ds) := by
  classical
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  obtain ⟨X, NK, rX, rNK, ndNK, saNK, akNK, lnNK, orNK⟩ := box_named (E := E) (n + 1) lines hl' AK
  obtain ⟨P, Q, rPQ, hP, fP, uQ, cQ, nQ, kQ⟩ := box_fields_gen ef hn lines hl hnt nopt hmd ks NK ndNK
  obtain ⟨Q', rQ', subQ', supQ', neQ'⟩ := box_filter_gen ef (m := n + 3) (by omega) Q uQ
  obtain ⟨T, U, rTU, lowT, semT, duU, puU, neU, dgU, cvU⟩ := box_domains_gen ef (n := n + 3) (by omega) lines hl' hnt nopt hmd Ds hD
  have sP : FieldsV E P := by
    refine ⟨fun e me => ?_, ?_⟩
    · obtain ⟨s, e₁, fe, -⟩ := fP e me; exact ⟨⟨s, e₁⟩, fe⟩
    · have := saNK; rw [← hP] at this; exact List.pairwise_map.mp this
  -- The field of a named key over the lines.
  have lookP : ∀ s ∈ NK, ∃ f, mapLookup P (.atom s) = some f ∧ FieldValue E f ∧
      ∀ o, FieldSem den f o ↔ ∃ L ∈ lines, LongM den L s o := fun s ms => by
    have : Term.atom s ∈ P.map Prod.fst := by rw [hP]; exact List.mem_map_of_mem ms
    obtain ⟨e, me, e₁⟩ := List.mem_map.mp this
    obtain ⟨s', e₁', fe, se⟩ := fP e me
    rw [e₁] at e₁'; cases e₁'
    exact ⟨e.2, lookup_of_mem sP me e₁, fe, se⟩
  have noneP : ∀ s, s ∉ NK → mapLookup P (.atom s) = none := fun s ns => by
    cases h : mapLookup P (.atom s) with
    | none => rfl
    | some f =>
      obtain ⟨e, me, e₁, -⟩ := lookup_some_mem h
      have : Term.atom s ∈ NK.map Term.atom := by rw [← hP]; exact List.mem_map.mpr ⟨e, me, e₁⟩
      exact absurd (by simpa using this) ns
  -- The filtered updates are those of the keys whose update gives some field.
  have uQ' : ∀ q ∈ Q', ∃ s, s ∈ ks ∧ s ∈ NK ∧ KeyUpdG E den lines nt nopt md s q := fun q mq => by
    obtain ⟨s, sk, hq⟩ := uQ q (subQ'.subset mq)
    have := kQ q (subQ'.subset mq)
    obtain ⟨old, new, e, rest⟩ := hq
    subst e
    simp only [updKey, List.mem_map, Term.atom.injEq, exists_eq_right] at this
    exact ⟨s, sk, this, old, new, rfl, rest⟩
  have memQ' : ∀ s, (∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new]) ↔ KeyNE den lines ks NK nt nopt md s := by
    intro s
    constructor
    · rintro ⟨q, mq, old, new, rfl⟩
      obtain ⟨s', sk, ms, old', new', e', -, sold, -, snew⟩ := uQ' _ mq
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e'
      cases Term.atom.inj e₁
      subst e₂ e₃
      obtain ⟨o, ho⟩ := neQ' _ mq
      refine ⟨ms, sk, o, ?_⟩
      have := (snew o).mp ho
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold o)
      rwa [eqF] at this
    · rintro ⟨ms, sk, o, ho⟩
      obtain ⟨q, mq, old, new, rfl, -, sold, -, snew⟩ := cQ s ms sk
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold o)
      have hn : FieldSem den new o := (snew o).mpr (by rw [eqF]; exact ho)
      exact ⟨_, supQ' _ mq ⟨o, hn⟩, old, new, rfl⟩
  have ndQ' : (Q'.map updKey).Nodup := (subQ'.map updKey).nodup nQ
  -- Replacing: rejecting with a single key update and no domain update.
  let rep : Prop := md = "reject" ∧ U = [] ∧ ∃ q, Q' = [q]
  let R : String → Prop := fun s => rep ∧ ∃ old new, Q' = [.tuple #[.atom s, old, new]]
  have hR : ∀ s, R s ↔ md = "reject" ∧ (∀ d ∈ Ds, ¬DomNE den lines nt nopt md d) ∧
      KeyNE den lines ks NK nt nopt md s ∧ ∀ s', KeyNE den lines ks NK nt nopt md s' → s' = s := by
    intro s
    have eU : U = [] ↔ ∀ d ∈ Ds, ¬DomNE den lines nt nopt md d := by
      exact ⟨fun h d md hd => (neU.mpr ⟨d, md, hd⟩) h,
        fun h => Classical.byContradiction fun ne => let ⟨d, md, hd⟩ := neU.mp ne; h d md hd⟩
    constructor
    · rintro ⟨⟨hr, hU, -⟩, old, new, hq⟩
      refine ⟨hr, eU.mp hU, (memQ' s).mp ⟨_, by rw [hq]; simp, old, new, rfl⟩, fun s' h' => ?_⟩
      obtain ⟨q, mq, old', new', rfl⟩ := (memQ' s').mpr h'
      rw [hq, List.mem_singleton] at mq
      obtain ⟨e₁, -, -⟩ := tuple3_inj mq
      exact Term.atom.inj e₁
    · rintro ⟨hr, hU, hs, uniq⟩
      obtain ⟨q, mq, old, new, rfl⟩ := (memQ' s).mpr hs
      have single : Q' = [.tuple #[.atom s, old, new]] := by
        have all : ∀ q' ∈ Q', q' = .tuple #[.atom s, old, new] → True := fun _ _ _ => trivial
        clear all
        obtain ⟨pre, suf, rfl⟩ := List.append_of_mem mq
        have keyOf : ∀ q' ∈ pre ++ suf, updKey q' = .atom s := fun q' m' => by
          have m'' : q' ∈ pre ++ Term.tuple #[.atom s, old, new] :: suf := by
            rcases List.mem_append.mp m' with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
          obtain ⟨s', -, -, old', new', rfl, -⟩ := uQ' _ m''
          have := uniq s' ((memQ' s').mp ⟨_, m'', old', new', rfl⟩)
          simp [updKey, this]
        have nd := ndQ'
        simp only [List.map_append, List.map_cons] at nd
        have hpre : pre = [] := by
          cases pre with
          | nil => rfl
          | cons p ps =>
            exfalso
            have := (List.nodup_append.mp nd).2.2 (updKey p) (by simp) (updKey (.tuple #[.atom s, old, new]))
              List.mem_cons_self
            exact this (by rw [keyOf p (by simp)]; simp [updKey])
        have hsuf : suf = [] := by
          cases suf with
          | nil => rfl
          | cons p ps =>
            exfalso
            subst hpre
            have := (List.nodup_cons.mp nd).1
            exact this (by rw [show updKey (.tuple #[.atom s, old, new]) = updKey p by
              rw [keyOf p (by simp)]; simp [updKey]]; simp)
        subst hpre hsuf; rfl
      exact ⟨⟨hr, eU.mpr hU, _, single⟩, old, new, single⟩
  -- The fields of the box, with the updates.
  obtain ⟨P2, rP2, sP2, keysP2, lookP2⟩ : ∃ P2, Erlang.lists.«foldl/3» (D (n + 4))
      (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-11-" 2 #[boolAtom (decide rep)])
      (fieldsTerm P) (Term.list Q') = .ok (fieldsTerm P2) ∧ FieldsV E P2 ∧
      (∀ s, mapLookup P2 (.atom s) = none ↔ mapLookup P (.atom s) = none) ∧
      ∀ s o, (∃ f, mapLookup P2 (.atom s) = some f ∧ FieldSem den f o) ↔
        ((¬R s ∧ ∃ f, mapLookup P (.atom s) = some f ∧ FieldSem den f o) ∨
          ∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o) := by
    by_cases hrep : rep
    · have hrep' := hrep
      obtain ⟨-, -, q, hq⟩ := hrep
      obtain ⟨s₀, -, ms₀, old, new, rfl, -, sold, fnew, -⟩ := uQ' q (by rw [hq]; simp)
      obtain ⟨P2, rP2, sP2, l₀, lo⟩ := box_store_rep (m := n + 3) sP (s := s₀) (old := old) fnew
      refine ⟨P2, by rw [decide_eq_true hrep', hq]; exact rP2, sP2, fun s => ?_, fun s o => ?_⟩
      · by_cases e : s = s₀
        · subst e; obtain ⟨f, lf, -⟩ := lookP s ms₀; simp [l₀, lf]
        · rw [lo s e]
      · have Rs : R s ↔ s = s₀ := ⟨fun ⟨_, old', new', h⟩ => by
            rw [hq] at h; simp at h; exact h.1.symm,
          fun e => ⟨hrep', old, new, by rw [hq, e]⟩⟩
        by_cases e : s = s₀
        · subst e
          rw [l₀]
          simp only [Option.some.injEq, exists_eq_left', hq, List.mem_singleton]
          constructor
          · intro h; exact Or.inr ⟨_, rfl, old, new, rfl, h⟩
          · rintro (⟨nr, -⟩ | ⟨q', rfl, old', new', e', h⟩)
            · exact absurd (Rs.mpr rfl) nr
            · obtain ⟨-, -, rfl⟩ := tuple3_inj e'; exact h
        · rw [lo s e, Rs]
          simp only [e, not_false_eq_true, true_and, hq, List.mem_singleton]
          constructor
          · exact Or.inl
          · rintro (h | ⟨q', rfl, old', new', e', -⟩)
            · exact h
            · obtain ⟨e₁, -, -⟩ := tuple3_inj e'; exact absurd (Term.atom.inj e₁).symm e
    · obtain ⟨P2, rP2, sP2, keysP2, lookP2⟩ := box_store ef (m := n + 3) (by omega) sP Q' (fun q mq => by
          obtain ⟨s, -, ms, old, new, rfl, hold, sold, hnew, -⟩ := uQ' q mq
          obtain ⟨f, lf, -, sf⟩ := lookP s ms
          exact ⟨s, old, new, rfl, hold, hnew, f, lf, fun o => (sold o).trans (sf o).symm⟩) ndQ'
      have nR : ∀ s, ¬R s := fun s h => hrep h.1
      refine ⟨P2, by rw [decide_eq_false hrep]; exact rP2, sP2, keysP2, fun s o => ?_⟩
      rw [lookP2]
      simp [nR s]
  -- The tag, open when every kind holds `term()`.
  have gT := lowTag_tagV lowT
  let T2 := if Term.compare (Term.fuel T allTerm) T allTerm = .eq then Term.atom "open" else T
  have gT2 : TagV E T2 := by
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte]; exact Or.inl rfl
    · simp only [T2, e, ↓reduceIte]; exact gT
  have semT2 : ∀ kind ∈ domainKinds, ∀ x, den (tagType T2 kind) x ↔ BoxTagG den lines nt md Ds kind x := by
    intro kind mk x
    rw [← semT kind mk x]
    by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq
    · simp only [T2, e, ↓reduceIte, tagType]
      exact ⟨fun _ => allTerm_full ef gT e kind mk x, fun _ => ef.den_term x⟩
    · simp only [T2, e, ↓reduceIte]
  obtain ⟨bo, rbo, fbo, sbo⟩ := map_new_leaf (den := den) ef gT2 sP2
  have semNew : ∀ s ∈ NK, ∀ o, (∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new o) ↔
      s ∈ ks ∧ NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) o := fun s ms o => by
    constructor
    · rintro ⟨q, mq, old, new, rfl, hq⟩
      obtain ⟨s', ks', -, old', new', e', -, sold', -, snew'⟩ := uQ' _ mq
      obtain ⟨e₁, e₂, e₃⟩ := tuple3_inj e'
      cases Term.atom.inj e₁
      subst e₂ e₃
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold' o)
      exact ⟨ks', by rw [← eqF]; exact (snew' o).mp hq⟩
    · rintro ⟨sk, ho⟩
      obtain ⟨q, mq, old, new, rfl, -, sold, -, snew⟩ := cQ s ms sk
      have eqF : FieldSem den old = fun o => ∃ L ∈ lines, LongM den L s o := funext fun o => propext (sold o)
      have hn : FieldSem den new o := (snew o).mpr (by rw [eqF]; exact ho)
      exact ⟨_, supQ' _ mq ⟨o, hn⟩, old, new, rfl, hn⟩
  have semBo : ∀ w, MSem den T2 P2 w ↔ BoxSynG den lines ks NK R nt nopt md Ds w := fun w => by
    rw [msem_keys]
    constructor
    · intro h
      refine ⟨fun s ms => ?_, fun s ns => ?_, fun k i => ?_⟩
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        obtain ⟨f, lf, -, sf⟩ := lookP s ms
        cases l2 : mapLookup P2 (.atom s) with
        | none => exact absurd ((keysP2 s).mp l2) (by simp [lf])
        | some f2 =>
          rw [l2] at this
          rcases (lookP2 s _).mp ⟨f2, l2, this⟩ with ⟨nr, f', lf', h'⟩ | h'
          · rw [lf] at lf'; cases lf'; exact Or.inl ⟨nr, (sf _).mp h'⟩
          · exact Or.inr ((semNew s ms _).mp h')
      · have := h (.atom s)
        simp only [KeyAllow, FSem] at this
        rw [(keysP2 s).mpr (noneP s ns)] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mp hx⟩
      · have := h (.dom k i)
        simp only [KeyAllow] at this
        rcases (tagSem_iff ef gT2 _ _).mp this with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mp hx⟩
    · rintro ⟨hn, hu, hd⟩ q
      cases q with
      | atom s =>
        simp only [KeyAllow, FSem]
        by_cases ms : s ∈ NK
        · obtain ⟨f, lf, -, sf⟩ := lookP s ms
          have hf : (¬R s ∧ ∃ f', mapLookup P (.atom s) = some f' ∧ FieldSem den f' (w (.atom s))) ∨
              ∃ q ∈ Q', ∃ old new, q = .tuple #[.atom s, old, new] ∧ FieldSem den new (w (.atom s)) := by
            rcases hn s ms with ⟨nr, h'⟩ | h'
            · exact Or.inl ⟨nr, f, lf, (sf _).mpr h'⟩
            · exact Or.inr ((semNew s ms _).mpr h')
          obtain ⟨f2, l2, h2⟩ := (lookP2 s _).mpr hf
          rw [l2]; exact h2
        · rw [(keysP2 s).mpr (noneP s ms)]
          simp only
          rw [tagSem_iff ef gT2]
          rcases hu s ms with h' | ⟨x, h', hx⟩
          · exact Or.inl h'
          · exact Or.inr ⟨x, h', (semT2 "atom" (by simp [domainKinds]) x).mpr hx⟩
      | dom k i =>
        simp only [KeyAllow]
        rw [tagSem_iff ef gT2]
        rcases hd k i with h' | ⟨x, h', hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, h', (semT2 _ (domKind_mem k) x).mpr hx⟩
  -- The pairs of old and new types of the updates.
  have shQ : ∀ q ∈ Q', ∃ s ot oo t' o', q = .tuple #[.atom s, .tuple #[ot, oo], .tuple #[t', o']] ∧
      KeyNE den lines ks NK nt nopt md s ∧ E ot ∧ E t' ∧ (∀ x, den ot x ↔ ∃ L ∈ lines, LongM den L s (some x)) ∧
      ∀ x, den t' x ↔ NewF den nt nopt md (fun o => ∃ L ∈ lines, LongM den L s o) (some x) := by
    intro q mq
    obtain ⟨s, -, -, old, new, rfl, ⟨ot, oo, rfl, hot⟩, sold, ⟨t', o', rfl, ht'⟩, snew⟩ := uQ' q mq
    have eqF : FieldSem den (.tuple #[ot, boolAtom oo]) = fun o => ∃ L ∈ lines, LongM den L s o :=
      funext fun o => propext (sold o)
    refine ⟨s, ot, boolAtom oo, t', boolAtom o', rfl, (memQ' s).mp ⟨_, mq, _, _, rfl⟩, hot, ht', fun x => ?_,
      fun x => ?_⟩
    · rw [← sold (some x), fieldSem_mk]; simp
    · have := snew (some x)
      rw [eqF] at this
      rw [← this, fieldSem_mk]; simp
  have rKP := keyPair_eval (n + 4) Q' fun q mq => by
    obtain ⟨s, ot, oo, t', o', e, -⟩ := shQ q mq; exact ⟨_, _, _, _, _, e⟩
  have rDP := domPair_eval (n + 4) U fun u mu => by
    obtain ⟨d, o, t, e, -⟩ := dgU u mu; exact ⟨_, _, _, e⟩
  have rAp := append_list (Q'.map keyPair) (U.map domPair)
  have upsE : ∀ p ∈ Q'.map keyPair ++ U.map domPair, ∃ o n', p = .tuple #[o, n'] ∧ E o ∧ E n' := by
    intro p mp
    rcases List.mem_append.mp mp with mp | mp
    · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
      obtain ⟨s, ot, oo, t', o', rfl, -, hot, ht', -⟩ := shQ q mq
      exact ⟨ot, t', by simp [keyPair], hot, ht'⟩
    · obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
      obtain ⟨d, o, t, rfl, -, -, ho, ht, -⟩ := dgU u mu
      exact ⟨o, t, by simp [domPair], ho, ht⟩
  -- The pairs hold what the named keys and kinds updated hold.
  have upsHas : ∀ A : Prop → Prop → Prop, (∃ p ∈ Q'.map keyPair ++ U.map domPair, ∃ o n', p = .tuple #[o, n'] ∧
      A (∃ x, den o x) (∃ x, den n' x)) ↔ UpdHas den lines ks NK nt nopt md Ds A := by
    intro A
    constructor
    · rintro ⟨p, mp, o, n', e, h⟩
      rcases List.mem_append.mp mp with mp | mp
      · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mp
        obtain ⟨s, ot, oo, t', o', rfl, hk, -, -, so, sn⟩ := shQ q mq
        simp only [keyPair, Term.tuple.injEq, List.cons.injEq, and_true, Array.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [propext (exists_congr so), propext (exists_congr sn)] at h
        exact Or.inl ⟨s, hk, h⟩
      · obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
        obtain ⟨d, o', t, rfl, md', hne, -, -, so, sn⟩ := dgU u mu
        simp only [domPair, Term.tuple.injEq, List.cons.injEq, and_true, Array.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [propext (exists_congr so), propext (exists_congr sn)] at h
        exact Or.inr ⟨d, md', hne, h⟩
    · rintro (⟨s, hk, h⟩ | ⟨d, md', hne, h⟩)
      · obtain ⟨q, mq, old, new, rfl⟩ := (memQ' s).mpr hk
        obtain ⟨s', ot, oo, t', o', e, -, -, -, so, sn⟩ := shQ _ mq
        obtain ⟨e1, rfl, rfl⟩ := tuple3_inj e
        cases Term.atom.inj e1
        rw [← propext (exists_congr so), ← propext (exists_congr sn)] at h
        exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem mq), ot, t', by simp [keyPair], h⟩
      · obtain ⟨u, mu, o, t, rfl⟩ := cvU d md' hne
        obtain ⟨d', o', t', e, -, -, -, -, so, sn⟩ := dgU _ mu
        obtain ⟨e1, rfl, rfl⟩ := tuple3_inj e
        cases Term.atom.inj e1
        rw [← propext (exists_congr so), ← propext (exists_congr sn)] at h
        exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem mu), o, t, by simp [domPair], h⟩
  -- Keeping with no old or new values: unchanged.
  obtain ⟨ba, ra, sa⟩ : ∃ ba : Bool, Erlang.lists.«all/2» (D (n + 4))
      (.function "Elixir.Module.Types.Descr" "-map_update_box/6-fun-10-" 1 #[])
      (Term.list (Q'.map keyPair ++ U.map domPair)) = .ok (boolAtom ba) ∧
      (ba = Bool.true ↔ ¬UpdHas den lines ks NK nt nopt md Ds (fun o n => o ∨ n)) := by
    classical
    let res : Term → Bool := fun p => decide (∃ o n', p = .tuple #[o, n'] ∧ ¬((∃ x, den o x) ∨ ∃ x, den n' x))
    refine ⟨_, all_list _ _ _ _ res _ fun p mp => ?_, ?_⟩
    · obtain ⟨o, n', rfl, ho, hn'⟩ := upsE p mp
      obtain ⟨eo, reo, seo⟩ := ef.empty1 (m := n + 3) (by omega) ho
      obtain ⟨en, ren, sen⟩ := ef.empty1 (m := n + 3) (by omega) hn'
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_box/6-fun-10-/1».pure]
      have hP : (∃ o' n'', Term.tuple #[o, n'] = .tuple #[o', n''] ∧ ¬((∃ x, den o' x) ∨ ∃ x, den n'' x)) ↔
          (eo = Bool.true ∧ en = Bool.true) := by
        constructor
        · rintro ⟨o', n'', e, h⟩
          obtain ⟨rfl, rfl⟩ : o = o' ∧ n' = n'' := by simpa using e
          exact ⟨seo.mpr fun x hx => h (Or.inl ⟨x, hx⟩), sen.mpr fun x hx => h (Or.inr ⟨x, hx⟩)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨o, n', rfl, fun h => h.elim (fun ⟨x, hx⟩ => seo.mp h1 x hx) (fun ⟨x, hx⟩ => sen.mp h2 x hx)⟩
      have dec : res (.tuple #[o, n']) = (eo && en) := by
        cases h : (eo && en)
        · exact decide_eq_false fun hh => by
            have := hP.mp hh; rw [this.1, this.2] at h; cases h
        · exact decide_eq_true (hP.mpr (by cases eo <;> cases en <;> simp_all))
      rw [dec]
      cases eo <;> cases en <;>
        simp [Elixir.Module.Types.Descr.«-map_update_box/6-fun-10-/1», reo, ren, Lynx.Except.andAlso, boolAtom]
    · rw [List.all_eq_true, ← upsHas]
      constructor
      · rintro h ⟨p, mp, o, n', e, hh⟩
        obtain ⟨o', n'', e', hn⟩ := of_decide_eq_true (h p mp)
        rw [e] at e'
        obtain ⟨rfl, rfl⟩ : o = o' ∧ n' = n'' := by simpa using e'
        exact hn hh
      · intro h p mp
        apply decide_eq_true
        obtain ⟨o, n', rfl, -, -⟩ := upsE p mp
        exact ⟨o, n', rfl, fun hh => h ⟨_, mp, o, n', rfl, hh⟩⟩
  obtain ⟨bp, rbp, sbp⟩ := present_gen (den := den) ef (m := n + 1) (by omega) lines hl' nt nopt hmd
    (Q'.map keyPair ++ U.map domPair) upsE
  have present : bp = Bool.true ↔ BoxPresent den lines ks NK nt nopt md Ds := by
    rw [sbp]
    unfold BoxPresent
    have k1 := upsHas (fun o n => o ∧ ¬n)
    have k2 := upsHas (fun _ n => n)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun hu => (h1 hk).1 ?_, (h1 hk).2⟩, fun hk => k2.mp (h2 hk)⟩
      obtain ⟨p, mp, o, n', e, ho, hn⟩ := k1.mpr hu
      exact ⟨p, mp, o, n', e, fun x hx => hn ⟨x, hx⟩, ho⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun ⟨p, mp, o, n', e, hn, ho⟩ => (h1 hk).1 (k1.mp ⟨p, mp, o, n', e, ho, fun ⟨x, hx⟩ => hn x hx⟩),
        (h1 hk).2⟩, fun hk => k2.mpr (h2 hk)⟩
  obtain ⟨bu, rbu, fbu, sbu⟩ := box_unsetD ef (m := n + 2) (by omega) ks AK Ds hD hnt snt
  obtain ⟨r, rr, hr⟩ := map_opt_diff1 (den := den) ef (m := n + 2) (by omega) fbo fbu
  have rTU' := rTU
  simp only [domainKinds, List.map] at rTU'
  have rAll : Erlang.lists.«map/2» (D (n + 4))
      (.function "Elixir.Module.Types.Descr" "-map_update_box/6-anonymous-0-" 1 #[])
      (Term.list (domainKinds.map Term.atom)) = .ok allTerm := by
    have := all_term_run _ (Or.inl rfl) (n + 3)
    rwa [usort_sorted _ kinds_sa, Lynx.Except.ok_bind] at this
  have uK := usort_sorted _ kinds_sa
  simp only [domainKinds, List.map] at rAll uK
  have rT2 : Erlang.erlang.«==/2» T allTerm = .ok (boolAtom (Term.compare (Term.fuel T allTerm) T allTerm == .eq)) :=
    eqq_val T allTerm
  have eQ := eqq_val (Term.list Q') .nil
  have eU := eqq_val (Term.list U) .nil
  have Q0 : Q' = [] ↔ ¬∃ s, KeyNE den lines ks NK nt nopt md s := by
    constructor
    · rintro e ⟨s, hs⟩
      obtain ⟨q, mq, -⟩ := (memQ' s).mpr hs
      rw [e] at mq; cases mq
    · intro h
      cases hq : Q' with
      | nil => rfl
      | cons q qs =>
        obtain ⟨s, -, -, old, new, rfl, -⟩ := uQ' q (by rw [hq]; simp)
        exact absurd ⟨s, (memQ' s).mp ⟨_, by rw [hq]; simp, old, new, rfl⟩⟩ h
  have U0 : U = [] ↔ ¬∃ d ∈ Ds, DomNE den lines nt nopt md d := by
    constructor
    · intro e h; exact (neU.mpr h) e
    · intro h; exact Classical.byContradiction fun ne => h (neU.mp ne)
  -- The run, given its result.
  have run : ∀ res, (Q' = [] ∧ U = [] → res = .map []) →
      (¬(Q' = [] ∧ U = []) → BoxSame den lines ks NK nt nopt md Ds → res = .map [(.atom "map", bdd)]) →
      (¬(Q' = [] ∧ U = []) → ¬BoxSame den lines ks NK nt nopt md Ds → ¬BoxPresent den lines ks NK nt nopt md Ds →
        res = .map [(.atom "map", bo)]) →
      (¬(Q' = [] ∧ U = []) → ¬BoxSame den lines ks NK nt nopt md Ds → BoxPresent den lines ks NK nt nopt md Ds →
        nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12 → .ok res = Elixir.Module.Types.Descr.«opt_difference/2» (D (n + 4))
          (.map [(.atom "map", bo)]) (.map [(.atom "map", bu)])) →
      (¬(Q' = [] ∧ U = []) → ¬BoxSame den lines ks NK nt nopt md Ds → BoxPresent den lines ks NK nt nopt md Ds →
        ¬(nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12) → .ok res = (do
          let a ← Elixir.Module.Types.Descr.«map_update_domains_add/3» (D (n + 4)) bo (fieldsTerm P2)
            (.tuple #[.nil, .nil])
          Elixir.Module.Types.Descr.«map_update_domains_result/1» (D (n + 4)) a)) →
      Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 4)) bdd (Term.list lines) (Term.list (ks.map Term.atom))
        (Term.list (Ds.map Term.atom)) (cOp nt nopt md) (Term.list (AK.map Term.atom)) = .ok res := by
    intro res c0 cS c1 c2 c3
    have lenD : Erlang.erlang.«length/1» (Term.list (Ds.map Term.atom)) = .ok (.integer (Ds.length : Int)) := by
      simpa using length_list (Ds.map Term.atom)
    have cmpNil : ∀ l : List Term, (Term.compare ((Term.list l).fuel .nil) (Term.list l) .nil == .eq) =
        decide (l = []) := fun l => by
      cases l with
      | nil => simp [Term.list, Lynx.Term.compare_self]
      | cons x xs => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]
    unfold Elixir.Module.Types.Descr.«map_update_box/6»
    simp [rX, rNK, rPQ, rQ', rTU', rKP, rDP, rAp, Lynx.Except.andAlso, Erlang.erlang.«element/2», uK, rAll, rT2,
      cmpNil, eqq_val]
    have same : BoxSame den lines ks NK nt nopt md Ds ↔ md = "keep" ∧ ba = Bool.true := by
      rw [BoxSame, sa]
    by_cases h0 : Q' = [] ∧ U = []
    · rw [c0 h0]; obtain ⟨rfl, rfl⟩ := h0; simp [boolAtom]
    have hd : (decide (Q' = []) && decide (U = [])) = Bool.false := by
      cases h : (decide (Q' = []) && decide (U = []))
      · rfl
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
        exact absurd h h0
    rw [hd]
    simp only [boolAtom, Bool.false_eq_true, ↓reduceIte]
    by_cases hS : BoxSame den lines ks NK nt nopt md Ds
    · rw [cS h0 hS]
      obtain ⟨rfl, rfl⟩ := same.mp hS
      simp [ra, boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith]
    · have ba_f : md = "keep" → ba = Bool.false := fun hk => by
        cases h : ba
        · rfl
        · exact absurd (same.mpr ⟨hk, h⟩) hS
      rcases hmd with rfl | rfl | rfl
      · simp [Erlang.erlang.«/=/2», Lynx.Except.tryWith]
        have dr : decide rep = Bool.false := decide_eq_false fun ⟨h, _⟩ => by simp at h
        rw [dr] at rP2
        simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rP2
        by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
          simp only [T2, e, ↓reduceIte] at rbo <;>
          simp [e, rP2, rbo, rbp, Lynx.Except.orElse] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
        all_goals first
          | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
          | (have hp := present.mp (by simp)
             by_cases hu : nopt = Bool.false ∧ "force" ≠ "keep" ∧ Ds.length ≠ 12
             · have c2' := c2 h0 hS hp hu
               obtain ⟨rfl, hk, hL⟩ := hu
               first
                 | exact absurd rfl hk
                 | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                    simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
             · have c3' := c3 h0 hS hp hu
               cases nopt <;> simp [cOp, boolAtom, Erlang.erlang.«/=/2», lenD] at hu ⊢ <;>
                 first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                           simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
        all_goals done
      · rw [ba_f rfl] at ra
        simp [ra, boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith]
        have dr : decide rep = Bool.false := decide_eq_false fun ⟨h, _⟩ => by simp at h
        rw [dr] at rP2
        simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rP2
        by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
          simp only [T2, e, ↓reduceIte] at rbo <;>
          simp [e, rP2, rbo, rbp, Lynx.Except.orElse] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
        all_goals first
          | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
          | (have hp := present.mp (by simp)
             by_cases hu : nopt = Bool.false ∧ "keep" ≠ "keep" ∧ Ds.length ≠ 12
             · have c2' := c2 h0 hS hp hu
               obtain ⟨rfl, hk, hL⟩ := hu
               first
                 | exact absurd rfl hk
                 | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                    simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
             · have c3' := c3 h0 hS hp hu
               cases nopt <;> simp [cOp, boolAtom, Erlang.erlang.«/=/2», lenD] at hu ⊢ <;>
                 first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                           simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
        all_goals done
      · simp [Erlang.erlang.«/=/2», Lynx.Except.tryWith]
        split
        · rename_i q₀ e₁ e₂ _
          have eQ1 : Q' = [q₀] := list_inj (e₁.trans rfl)
          have eU1 : U = [] := list_inj (e₂.trans rfl)
          have dr : decide rep = Bool.true := decide_eq_true ⟨rfl, eU1, q₀, eQ1⟩
          rw [dr] at rP2
          simp only [boolAtom, ↓reduceIte] at rP2
          by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
            simp only [T2, e, ↓reduceIte] at rbo <;>
            simp [e, rP2, rbo, rbp, Lynx.Except.orElse] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
          all_goals first
            | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
            | (have hp := present.mp (by simp)
               by_cases hu : nopt = Bool.false ∧ "reject" ≠ "keep" ∧ Ds.length ≠ 12
               · have c2' := c2 h0 hS hp hu
                 obtain ⟨rfl, hk, hL⟩ := hu
                 first
                   | exact absurd rfl hk
                   | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                      simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
               · have c3' := c3 h0 hS hp hu
                 cases nopt <;> simp [cOp, boolAtom, Erlang.erlang.«/=/2», lenD] at hu ⊢ <;>
                   first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                             simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
          all_goals done

        · rename_i hnot
          have dr : decide rep = Bool.false := decide_eq_false fun ⟨_, eU1, q, eQ1⟩ =>
            hnot q (by rw [eQ1]) (by rw [eU1]) rfl
          rw [dr] at rP2
          simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rP2
          by_cases e : Term.compare (Term.fuel T allTerm) T allTerm = .eq <;>
            simp only [T2, e, ↓reduceIte] at rbo <;>
            simp [e, rP2, rbo, rbp, Lynx.Except.orElse] <;> cases bp <;> simp [boolAtom, Erlang.erlang.«=:=/2»]
          all_goals first
            | exact (c1 h0 hS fun hp => by have := present.mpr hp; simp at this).symm
            | (have hp := present.mp (by simp)
               by_cases hu : nopt = Bool.false ∧ "reject" ≠ "keep" ∧ Ds.length ≠ 12
               · have c2' := c2 h0 hS hp hu
                 obtain ⟨rfl, hk, hL⟩ := hu
                 first
                   | exact absurd rfl hk
                   | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                      simpa [cOp, boolAtom, Erlang.erlang.«/=/2», lenD, hL', rbu] using c2'.symm)
               · have c3' := c3 h0 hS hp hu
                 cases nopt <;> simp [cOp, boolAtom, Erlang.erlang.«/=/2», lenD] at hu ⊢ <;>
                   first | exact c3'.symm | (have hL' : ¬((Ds.length : Int) = 12) := by omega
                                             simp [hL'] at hu) | simp [hu] <;> exact c3'.symm)
          all_goals done
  have congr : ∀ {X : List (Term × Term)} {S S' : MW V → Prop}, MapsD E den X S → (∀ w, S w ↔ S' w) →
      MapsD E den X S' := fun h e => ⟨h.1, h.2.1, fun w => (h.2.2 w).trans (e w)⟩
  have upd : ¬(Q' = [] ∧ U = []) → ((∃ s, KeyNE den lines ks NK nt nopt md s) ∨ ∃ d ∈ Ds, DomNE den lines nt nopt md d) :=
    fun h0 => Classical.byContradiction fun h => h0 ⟨Q0.mpr fun e => h (Or.inl e), U0.mpr fun e => h (Or.inr e)⟩
  by_cases h0 : Q' = [] ∧ U = []
  · refine ⟨NK, R, .map [], run _ (fun _ => rfl) (fun h => absurd h0 h) (fun h => absurd h0 h) (fun h => absurd h0 h)
      (fun h => absurd h0 h), akNK, lnNK, orNK, hR, [], rfl, mapsD_nil fun w hw => ?_⟩
    rcases hw.1 with h | h
    · exact (Q0.mp h0.1) h
    · exact (U0.mp h0.2) h
  have up := upd h0
  by_cases hS : BoxSame den lines ks NK nt nopt md Ds
  · refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ _ => rfl) (fun _ h => absurd hS h) (fun _ h => absurd hS h)
      (fun _ h => absurd hS h), akNK, lnNK, orNK, hR, _, rfl, mapsD_field fbd fun w => ?_⟩
    rw [sbd]
    exact ⟨fun h => ⟨up, fun _ => h, fun h' => absurd hS h'⟩, fun h => h.2.1 hS⟩
  by_cases hp : BoxPresent den lines ks NK nt nopt md Ds
  · by_cases hu : nopt = Bool.false ∧ md ≠ "keep" ∧ Ds.length ≠ 12
    · obtain ⟨X', eX, mX⟩ := mapsD_box (E := E) (den := den) (res := r) (S := BoxRes den lines ks AK NK R nt nopt md Ds) (by
        rcases hr with ⟨rfl, emp⟩ | ⟨c, rfl, fc, sc⟩
        · refine Or.inl ⟨rfl, fun w ⟨_, _, hq⟩ => ?_⟩
          have := emp w
          rw [(sbo w).mpr ((semBo w).mpr (hq hS).1)] at this
          cases h : denMF E den bu w
          · rw [h] at this; cases this
          · exact ((hq hS).2 hp).1 hu ((sbu w).mp h)
        · refine Or.inr ⟨c, bo, rfl, fc, fun w => ?_⟩
          rw [sc, Bool.and_eq_true, Bool.not_eq_true', sbo, semBo]
          constructor
          · rintro ⟨hb, hu'⟩
            refine ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun _ => ⟨fun _ h => ?_, fun h => absurd hu h⟩⟩⟩
            rw [(sbu w).mpr h] at hu'
            simp at hu'
          · rintro ⟨-, -, hq⟩
            refine ⟨(hq hS).1, ?_⟩
            cases h : denMF E den bu w
            · rfl
            · exact absurd ((sbu w).mp h) (((hq hS).2 hp).1 hu))
      exact ⟨NK, R, r, run r (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ h => absurd hp h)
        (fun _ _ _ _ => rr.symm) (fun _ _ _ h => absurd hu h), akNK, lnNK, orNK, hR, X', eX, mX⟩
    · rcases domains_add (E := E) (n + 3) bo sP2 [] [] with ⟨rda, req⟩ | ⟨rda, nreq⟩
      · obtain ⟨X', rX', mX⟩ := domains_result (den := den) ef (m := n + 2) (by omega) [] [bo] (by simp)
          (fun b mb => by simp at mb; subst mb; exact fbo)
        refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ h => absurd hp h)
          (fun _ _ _ h => absurd h hu) (fun _ _ _ _ => by rw [rda]; simpa using rX'.symm), akNK, lnNK, orNK, hR, X',
          rfl, congr mX fun w => ?_⟩
        simp only [List.not_mem_nil, false_and, exists_false, false_or, List.mem_singleton, exists_eq_left]
        rw [sbo, semBo]
        exact ⟨fun hb => ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun _ => ⟨fun h => absurd h hu, fun _ =>
          msem_req_ne_none sP2 req ((semBo w).mpr hb)⟩⟩⟩, fun h => (h.2.2 hS).1⟩
      · obtain ⟨X', rX', mX⟩ := domains_result (den := den) ef (m := n + 2) (by omega) [bo] []
          (fun b mb => by simp at mb; subst mb; exact fbo) (by simp)
        refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ h => absurd hp h)
          (fun _ _ _ h => absurd h hu) (fun _ _ _ _ => by rw [rda]; simpa using rX'.symm), akNK, lnNK, orNK, hR, X',
          rfl, congr mX fun w => ?_⟩
        simp only [List.mem_singleton, exists_eq_left, List.not_mem_nil, false_and, exists_false, or_false]
        rw [sbo, semBo]
        exact ⟨fun ⟨hb, hn⟩ => ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun _ => ⟨fun h => absurd h hu, fun _ => hn⟩⟩⟩,
          fun ⟨_, _, hq⟩ => ⟨(hq hS).1, ((hq hS).2 hp).2 hu⟩⟩
  · refine ⟨NK, R, _, run _ (fun h => absurd h h0) (fun _ h => absurd h hS) (fun _ _ _ => rfl) (fun _ _ h => absurd h hp)
      (fun _ _ h => absurd h hp), akNK, lnNK, orNK, hR, _, rfl, mapsD_field fbo fun w => ?_⟩
    rw [sbo, semBo]
    exact ⟨fun hb => ⟨up, fun h => absurd h hS, fun _ => ⟨hb, fun h => absurd h hp⟩⟩, fun h => (h.2.2 hS).1⟩

end

end Elixir.STTDescrProofsTest.Nest
