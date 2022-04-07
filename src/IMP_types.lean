import tactic.induction
import data.real.basic

abbreviation vname := string

inductive val : Type
| Iv : ℕ → val
| Rv : ℝ → val

open val

abbreviation pstate := vname → val

def state_update (s : pstate) (x : vname) (v : val) : pstate :=
  λ y, if (y = x) then v else s y

notation s `[` x ` ↦ ` v `]`:100 := state_update s x v
notation   `[` x ` ↦ ` v `]`     := (λ _, (Iv 0)) [x ↦ v]

@[simp] def apply_state_update_pos {x y : vname} {s : pstate} {v : val} :
  (y = x) → s[x ↦ v] y = v := 
begin
  intro,
  dsimp[state_update],
  apply if_pos,
  assumption
end

@[simp] def apply_state_update_neg {x y : vname} {s : pstate} {v : val} :
  ¬(y = x) → s[x ↦ v] y = (s y) :=
begin
  intro,
  dsimp[state_update],
  apply if_neg,
  assumption
end

inductive aexp : Type
| Ic   : ℕ → aexp
| Rc   : ℝ → aexp
| V    : vname → aexp
| Plus : aexp → aexp → aexp

open aexp

inductive taval : aexp → pstate → val → Prop
| tavalI {i : ℕ} {s : pstate} : 
  taval (Ic i) s (Iv i)

| tavalR {r : ℝ} {s : pstate} : 
  taval (Rc r) s (Rv r)

| tavalV {x : vname} {s : pstate} :
  taval (V x) s (s x)

| tavalPI {a₁ a₂ : aexp} {s : pstate} {i₁ i₂ : ℕ} :
  taval a₁ s (Iv i₁) →
  taval a₂ s (Iv i₂) →
  taval (Plus a₁ a₂) s (Iv (i₁ + i₂))

| tavalPR {a₁ a₂ : aexp} {s : pstate} {r₁ r₂ : ℝ} :
  taval a₁ s (Rv r₁) →
  taval a₂ s (Rv r₂) →
  taval (Plus a₁ a₂) s (Rv (r₁ + r₂))

open taval

inductive bexp : Type
| Bc   : bool → bexp
| Not  : bexp → bexp
| And  : bexp → bexp → bexp
| Less : aexp → aexp → bexp

open bexp

inductive tbval : bexp → pstate → bool → Prop
| tbvalC {bv : bool} {s : pstate} :
  tbval (Bc bv) s bv

| tbvalN {b : bexp} {s : pstate} {bv : bool} :
  tbval b s bv →
  tbval (Not b) s (¬bv)

| tbvalA {b₁ b₂ : bexp} {s : pstate} {bv₁ bv₂ : bool} :
  tbval b₁ s bv₁ →
  tbval b₂ s bv₂ →
  tbval (And b₁ b₂) s (bv₁ ∧ bv₂)

| tbvalLI {a₁ a₂ : aexp} {s : pstate} {i₁ i₂ : ℕ} :
  taval a₁ s (Iv i₁) →
  taval a₂ s (Iv i₂) →
  tbval (Less a₁ a₂) s (i₁ < i₂)

| tbvalLR {a₁ a₂ : aexp} {s : pstate} {r₁ r₂ : ℝ} :
  taval a₁ s (Rv r₁) →
  taval a₂ s (Rv r₂) →
  tbval (Less a₁ a₂) s (r₁ < r₂)

open tbval

-- TODO: definizione condivisa
inductive com : Type
| SKIP   : com
| Assign : vname → aexp → com
| Seq    : com → com → com
| If     : bexp → com → com → com
| While  : bexp → com → com

infix ` ::= `:68                                    := com.Assign
infix ` ;; `:67                                     := com.Seq
notation `IF `:0 b ` THEN `:0 c₁ ` ELSE `:68 c₂:68  := com.If b c₁ c₂
notation `WHILE `:0 b ` DO `:68 c:68                := com.While b c

abbreviation conf := com × pstate

open com

inductive small_step : conf → conf → Prop
| Assign  {s : pstate} {x : vname} {a : aexp} {v : val}:
  taval a s v →
  small_step (x ::= a, s) (SKIP, s[x ↦ v])

| Seq1 {c₂ : com} {s : pstate} :
  small_step (SKIP;;c₂, s) (c₂, s)

| Seq2 {c₁ c₁' c₂ : com} {s s' : pstate} :
  small_step (c₁, s) (c₁', s') →
  small_step (c₁ ;; c₂, s) (c₁' ;; c₂, s')

| IfTrue {b : bexp} {s : pstate} {c₁ c₂ : com}:
  tbval b s tt →
  small_step (IF b THEN c₁ ELSE c₂, s) (c₁, s)

| IfFalse {b : bexp} {s : pstate} {c₁ c₂ : com}:
  tbval b s ff →
  small_step (IF b THEN c₁ ELSE c₂, s) (c₂, s)

| While {b : bexp} {c : com} {s : pstate} :
  small_step (WHILE b DO c, s) (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s)

infix `↝`:70 := small_step

open small_step

namespace small_step

inductive small_step_star : conf → conf → Prop
| refl {c : com} {s : pstate} : small_step_star (c, s) (c, s)

| step {c c₁ c₂ : com} {s s₁ s₂ : pstate}:
  small_step (c, s) (c₁, s₁) →
  small_step_star (c₁, s₁) (c₂, s₂) →
  small_step_star (c, s) (c₂, s₂)

infix `↝*`:70 := small_step_star

end small_step

inductive ty : Type
| Ity
| Rty

open ty

abbreviation tyenv := vname → ty

inductive atyping : tyenv → aexp → ty → Prop
| atypeI {Γ : tyenv} {i : ℕ} :
  atyping Γ (Ic i) Ity

| atypeR {Γ : tyenv} {r : ℝ} :
  atyping Γ (Rc r) Rty

| atypeV {Γ : tyenv} {x : vname} :
  atyping Γ (V x) (Γ x)

| atypeP {Γ : tyenv} {a₁ a₂ : aexp} {τ : ty} :
  atyping Γ a₁ τ →
  atyping Γ a₂ τ →
  atyping Γ (Plus a₁ a₂) τ

notation Γ ` ⊢ₐ ` a ` : ` τ := atyping Γ a τ

open atyping

inductive btyping : tyenv → bexp → Prop
| btypeC {Γ : tyenv} {bv : bool} :
  btyping Γ (Bc bv)

| btypeN {Γ : tyenv} {b : bexp} :
  btyping Γ b →
  btyping Γ (Not b)

| btypeA {Γ : tyenv} {b₁ b₂ : bexp} :
  btyping Γ b₁ →
  btyping Γ b₂ →
  btyping Γ (And b₁ b₂)

| btypeL {Γ : tyenv} {a₁ a₂ : aexp} {τ : ty} :
  atyping Γ a₁ τ →
  atyping Γ a₂ τ →
  btyping Γ (Less a₁ a₂)

notation Γ ` ⊢₆ ` b := btyping Γ b

open btyping

inductive ctyping : tyenv → com → Prop
| ctypeSKIP {Γ : tyenv} :
  ctyping Γ SKIP

| ctypeAssign {Γ : tyenv} {a : aexp} {x : vname} :
  (Γ ⊢ₐ a : (Γ x)) →
  ctyping Γ (x ::= a)

| ctypeSeq {Γ : tyenv} {c₁ c₂ : com} :
  ctyping Γ c₁ →
  ctyping Γ c₂ →
  ctyping Γ (c₁ ;; c₂)

| ctypeIf {Γ : tyenv} {b : bexp} {c₁ c₂ : com} :
  (Γ ⊢₆ b) →
  ctyping Γ c₁ →
  ctyping Γ c₂ →
  ctyping Γ (IF b THEN c₁ ELSE c₂)

| ctypeWhile {Γ : tyenv} {b : bexp} {c : com} :
  (Γ ⊢₆ b) →
  ctyping Γ c →
  ctyping Γ (WHILE b DO c)

notation Γ ` ⊢. ` c := ctyping Γ c

open ctyping

def type : val → ty
| (Iv i) := Ity
| (Rv r) := Rty

-- TODO: definizione più strutturata?
notation Γ ` ⊢ₛ ` s := ∀ (y : vname), type (s y) = Γ y

lemma preservation_aexp {Γ : tyenv} {a : aexp} {τ : ty} {s : pstate} {v : val} : 
  (Γ ⊢ₐ a : τ) → taval a s v → (Γ ⊢ₛ s) → type v = τ :=
begin
  intros,
  induction' ‹(Γ ⊢ₐ a : τ)›,
    case atypeI : {
      cases ‹taval (Ic i) s v›,
      trivial
    },
    case atypeR : {
      cases ‹taval (Rc r) s v›,
      trivial
    },
    case atypeV : {
      cases ‹taval (V x) s v›,
      apply ‹(Γ ⊢ₛ s)›
    },
    case atypeP : _ a₁ a₂ τ _ _ ih₁ ih₂ {
      cases ‹taval (Plus a₁ a₂) s v›,
        case tavalPI : _ _ _ i₁ i₂ _ _ { 
          have : τ = Ity, {
            have : type (Iv i₁) = τ, from ih₁ ‹taval a₁ s (Iv i₁)› ‹(Γ ⊢ₛ s)›,
            rw[type] at this,
            symmetry,
            assumption
          },
          rw[‹τ = Ity›],
          trivial
        },
        case tavalPR : _ _ _ r₁ r₂ _ _ {
          have : τ = Rty, {
            have : type (Rv r₁) = τ, from ih₁ ‹taval a₁ s (Rv r₁)› ‹(Γ ⊢ₛ s)›,
            rw[type] at this,
            symmetry,
            assumption
          },
          rw[‹τ = Rty›],
          trivial
        }
    }
end

lemma extract_Ity {v : val} :
  (type v = Ity) → ∃ i, v = (Iv i) :=
begin
  intro,
  cases v,
    case Iv : i { exact ⟨i, rfl⟩ },
    case Rv : { contradiction }
end

lemma extract_Rty {v : val} :
  (type v = Rty) → ∃ r, v = (Rv r) :=
begin
  intro,
  cases v,
    case Iv : { contradiction },
    case Rv : r { exact ⟨r, rfl⟩ }
end

lemma progress_aexp {Γ : tyenv} {a : aexp} {τ : ty} {s : pstate} :
  (Γ ⊢ₐ a : τ) → (Γ ⊢ₛ s) → ∃ (v : val), taval a s v :=
begin
  intros,
  induction' ‹(Γ ⊢ₐ a : τ)›,
    case atypeI : { 
      show ∃ v, taval (Ic i) s v, from ⟨ (Iv i), tavalI ⟩ 
    },
    case atypeR : { 
      show ∃ v, taval (Rc r) s v, from ⟨ (Rv r), tavalR ⟩ 
    },
    case atypeV : { 
      show ∃ v, taval (V x) s v, from ⟨ (s x), tavalV ⟩ 
    },
    case atypeP : _ a₁ a₂ τ _ _ ih₁ ih₂ {
      have : ∃ v, taval a₁ s v, from ih₁ ‹(Γ ⊢ₛ s)›,
      cases ‹∃ v, taval a₁ s v› with v₁,

      have : ∃ v, taval a₂ s v, from ih₂ ‹(Γ ⊢ₛ s)›,
      cases ‹∃ v, taval a₂ s v› with v₂,

      have : type v₁ = τ, from 
        preservation_aexp ‹(Γ ⊢ₐ a₁ : τ)› ‹taval a₁ s v₁› ‹(Γ ⊢ₛ s)›,

      have : type v₂ = τ, from
        preservation_aexp ‹(Γ ⊢ₐ a₂ : τ)› ‹taval a₂ s v₂› ‹(Γ ⊢ₛ s)›,

      cases τ,
        case Ity : {
          have : ∃ i₁, v₁ = (Iv i₁), from extract_Ity ‹type v₁ = Ity›,
          cases ‹∃ i₁, v₁ = (Iv i₁)› with i₁,
          rw[‹v₁ = Iv i₁›] at *,

          have : ∃ i₂, v₂ = (Iv i₂), from extract_Ity ‹type v₂ = Ity›,
          cases ‹∃ i₂, v₂ = (Iv i₂)› with i₂,
          rw[‹v₂ = Iv i₂›] at *,

          show ∃ v, taval (Plus a₁ a₂) s v, from 
            ⟨ (Iv (i₁ + i₂)), tavalPI ‹taval a₁ s (Iv i₁)› ‹taval a₂ s (Iv i₂)› ⟩
        },
        case Rty : {
          have : ∃ r₁, v₁ = (Rv r₁), from extract_Rty ‹type v₁ = Rty›,
          cases ‹∃ r₁, v₁ = (Rv r₁)› with r₁,
          rw[‹v₁ = Rv r₁›] at *,

          have : ∃ r₂, v₂ = (Rv r₂), from extract_Rty ‹type v₂ = Rty›,
          cases ‹∃ r₂, v₂ = (Rv r₂)› with r₂,
          rw[‹v₂ = Rv r₂›] at *,

          show ∃ v, taval (Plus a₁ a₂) s v, from 
            ⟨ (Rv (r₁ + r₂)), tavalPR ‹taval a₁ s (Rv r₁)› ‹taval a₂ s (Rv r₂)› ⟩
        }
    },
end

lemma progress_bexp {Γ : tyenv} {b : bexp} {s : pstate} :
  (Γ ⊢₆ b) → (Γ ⊢ₛ s) → ∃ (v : bool), tbval b s v :=
begin
  intros,
  induction' ‹(Γ ⊢₆ b)›,
    case btypeC : {
      show ∃ v, tbval (Bc bv) s v, from
        ⟨ bv, tbvalC ⟩
    },
    case btypeN : {
      have : ∃ v, tbval b s v, from ih ‹(Γ ⊢ₛ s)›,
      cases ‹∃ v, tbval b s v› with bv,

      show ∃ v, tbval (Not b) s v, from
        ⟨ ¬bv, tbvalN ‹tbval b s bv› ⟩
    },
    case btypeA : _ b₁ b₂ _ _ ih₁ ih₂ { 
      have : ∃ v, tbval b₁ s v, from ih₁ ‹(Γ ⊢ₛ s)›,
      cases ‹∃ v, tbval b₁ s v› with bv₁,

      have : ∃ v, tbval b₂ s v, from ih₂ ‹(Γ ⊢ₛ s)›,
      cases ‹∃ v, tbval b₂ s v› with bv₂,

      show ∃ v, tbval (And b₁ b₂) s v, from
        ⟨ (bv₁ ∧ bv₂), tbvalA ‹tbval b₁ s bv₁› ‹tbval b₂ s bv₂› ⟩
    },
    case btypeL : _ _ _ τ _ _ { 
      have : ∃ v, taval a₁ s v, from 
        progress_aexp ‹(Γ ⊢ₐ a₁ : τ)› ‹(Γ ⊢ₛ s)›,
      cases ‹∃ v, taval a₁ s v› with v₁,

      have : ∃ v, taval a₂ s v, from 
        progress_aexp ‹(Γ ⊢ₐ a₂ : τ)› ‹(Γ ⊢ₛ s)›,
      cases ‹∃ v, taval a₂ s v› with v₂,

      have : type v₁ = τ, from 
        preservation_aexp ‹(Γ ⊢ₐ a₁ : τ)› ‹taval a₁ s v₁› ‹(Γ ⊢ₛ s)›,

      have : type v₂ = τ, from
        preservation_aexp ‹(Γ ⊢ₐ a₂ : τ)› ‹taval a₂ s v₂› ‹(Γ ⊢ₛ s)›,

      cases τ,
        case Ity : {
          have : ∃ i, v₁ = (Iv i), from extract_Ity ‹type v₁ = Ity›,
          cases ‹∃ i, v₁ = (Iv i)› with i₁,
          rw[‹v₁ = Iv i₁›] at *,

          have : ∃ i, v₂ = (Iv i), from extract_Ity ‹type v₂ = Ity›,
          cases ‹∃ i, v₂ = (Iv i)› with i₂,
          rw[‹v₂ = Iv i₂›] at *,

          show ∃ v, tbval (Less a₁ a₂) s v, from
            ⟨ (i₁ < i₂), tbvalLI ‹taval a₁ s (Iv i₁)› ‹taval a₂ s (Iv i₂)› ⟩
        },
        case Rty : {
          have : ∃ r, v₁ = (Rv r), from extract_Rty ‹type v₁ = Rty›,
          cases ‹∃ r, v₁ = (Rv r)› with r₁,
          rw[‹v₁ = Rv r₁›] at *,

          have : ∃ r, v₂ = (Rv r), from extract_Rty ‹type v₂ = Rty›,
          cases ‹∃ r, v₂ = (Rv r)› with r₂,
          rw[‹v₂ = Rv r₂›] at *,

          show ∃ v, tbval (Less a₁ a₂) s v, from
            ⟨ (r₁ < r₂), tbvalLR ‹taval a₁ s (Rv r₁)› ‹taval a₂ s (Rv r₂)› ⟩
        }
    }
end

theorem preservation_com {Γ : tyenv} {c c' : com} {s s' : pstate } :
  (Γ ⊢. c) → (c, s)↝(c', s') → (Γ ⊢. c') :=
begin
  intros,
  induction' ‹(Γ ⊢. c)›,
    case ctypeSKIP : {
      cases ‹(SKIP, s)↝(c', s')› -- impossibile
    },
    case ctypeAssign : {
      cases' ‹(x ::= a, s)↝(c', s')›,

      show (Γ ⊢. SKIP), from ctypeSKIP
    },
    case ctypeSeq : _ c₁ c₂ _ _ ih₁ ih₂ {
      cases' ‹(c₁ ;; c₂, s)↝(c', s')›,
        case Seq1 : { assumption },
        case Seq2 : {
          have : (Γ ⊢. c₁'), from ih₁ ‹(c₁, s)↝(c₁', s')›,

          show (Γ ⊢. c₁' ;; c₂), from ctypeSeq ‹(Γ ⊢. c₁')› ‹(Γ ⊢. c₂)›
        }
    },
    case ctypeIf : _ _ c₁ c₂ _ _ _ ih₁ ih₂ { 
      cases' ‹(IF b THEN c₁ ELSE c₂, s)↝(c', s')›,
        case IfTrue : { assumption },
        case IfFalse : { assumption } 
    },
    case ctypeWhile : {
      cases' ‹(WHILE b DO c, s)↝(c', s')›,

      have : (Γ ⊢. WHILE b DO c), from ctypeWhile ‹(Γ ⊢₆ b)› ‹(Γ ⊢. c)›,
      have : (Γ ⊢. c ;; WHILE b DO c), from ctypeSeq ‹(Γ ⊢. c)› ‹(Γ ⊢. WHILE b DO c)›,

      show (Γ ⊢. IF b THEN (c ;; WHILE b DO c) ELSE SKIP), from
        ctypeIf ‹(Γ ⊢₆ b)› ‹(Γ ⊢. c ;; WHILE b DO c)› ctypeSKIP
    }
end

theorem preservation_state {Γ : tyenv} {c c' : com} {s s' : pstate } :
  (Γ ⊢. c) → (Γ ⊢ₛ s) → (c, s)↝(c', s') → (Γ ⊢ₛ s') :=
begin
  intro, intro, intro,
  induction' ‹(Γ ⊢. c)›,
    case ctypeSKIP : {
      cases' ‹(SKIP, s)↝(c', s')› -- impossibile
    },
    case ctypeAssign : _ _ x _ {
      cases' ‹(x ::= a, s)↝(c', s')› with _ x _ _ _,

      have : type v = Γ x, from
        preservation_aexp ‹(Γ ⊢ₐ a : Γ x)› ‹taval a s v› ‹(Γ ⊢ₛ s)›,

      assume y : vname,
      have : (y = x) ∨ ¬(y = x), from em (y = x),

      cases' ‹(y = x) ∨ ¬(y = x)›,
        case or.inl : { -- y = x
          have : (s[x ↦ v] y) = v, by simp[‹y = x›],
          rw[‹(s[x ↦ v] y) = v›, ‹y = x›],
          
          show type v = Γ x , by assumption
        },
        case or.inr : { -- ¬(y = x)
          have : (s[x ↦ v] y) = s y, by simp[‹¬y = x›],
          rw[‹s[x ↦ v] y = s y›],

          show type (s y) = Γ y, from ‹(Γ ⊢ₛ s)› y
        }

    },
    case ctypeSeq : _ c₁ c₂ _ _ ih₁ ih₂ {
      cases' ‹(c₁ ;; c₂, s)↝(c', s')›,
        case Seq1 : {
          show (Γ ⊢ₛ s), by assumption
        },
        case Seq2 : {
          show (Γ ⊢ₛ s'), from ih₁ ‹(Γ ⊢ₛ s)› ‹(c₁, s)↝(c₁', s')›,
        }
    },
    case ctypeIf : _ _ c₁ c₂ _ _ _ ih₁ ih₂ { 
      cases' ‹(IF b THEN c₁ ELSE c₂, s)↝(c', s')›,
        case IfTrue : {
          show (Γ ⊢ₛ s), by assumption
        },
        case IfFalse : {
          show (Γ ⊢ₛ s), by assumption
        }
    },
    case ctypeWhile : {
      cases' ‹(WHILE b DO c, s)↝(c', s')›,

      show (Γ ⊢ₛ s), by assumption 
    }
end

theorem progress_com {Γ : tyenv} {c : com} { s: pstate} :
  (Γ ⊢. c) → (Γ ⊢ₛ s) → ¬(c = SKIP) → ∃ (cs' : conf), (c, s)↝cs' :=
begin
  intros,
  induction' ‹(Γ ⊢. c)›,
    case ctypeSKIP : { 
      contradiction 
    },
    case ctypeAssign : {
      have : ∃ v, taval a s v, from progress_aexp ‹(Γ ⊢ₐ a : Γ x)› ‹(Γ ⊢ₛ s)›,
      cases' ‹∃ v, taval a s v› with v,

      show ∃ cs', (x ::= a, s)↝cs', from
        ⟨ (SKIP,  s[x ↦ v]), Assign ‹taval a s v› ⟩
    },
    case ctypeSeq : _ c₁ c₂ _ _ ih₁ ih₂ {
      have : (c₁ = SKIP) ∨ ¬(c₁ = SKIP), from em (c₁ = SKIP),

      cases' ‹(c₁ = SKIP) ∨ ¬(c₁ = SKIP)›,
        case or.inl : { -- c₁ = SKIP
          rw[‹c₁ = SKIP›] at *,
          
          show ∃ cs', (SKIP ;; c₂, s)↝cs', from ⟨ (c₂, s), Seq1 ⟩
        },
        case or.inr : { -- ¬(c₁ = SKIP) 
          have : ∃ cs', (c₁, s)↝cs', from ih₁ ‹(Γ ⊢ₛ s)› ‹¬(c₁ = SKIP)›,
          cases' ‹∃ cs', (c₁, s)↝cs'› with cs',
          cases' cs' with c₁' s',
          
          show ∃ cs', (c₁ ;; c₂, s)↝cs', from
            ⟨ (c₁';; c₂, s'), Seq2 ‹(c₁, s)↝(c₁', s')› ⟩
        }
    },
    case ctypeIf : _ _ c₁ c₂ _ _ _ ih₁ ih₂ {
      have : ∃ v, tbval b s v, from progress_bexp ‹(Γ ⊢₆ b)› ‹(Γ ⊢ₛ s)›,
      cases' ‹∃ v, tbval b s v› with bv,

      cases' bv,
        case tt : {
          show ∃ cs', (IF b THEN c₁ ELSE c₂, s)↝cs', from
            ⟨ (c₁, s), IfTrue ‹tbval b s tt› ⟩
        },
        case ff : {
          show ∃ cs', (IF b THEN c₁ ELSE c₂, s)↝cs', from
            ⟨ (c₂, s), IfFalse ‹tbval b s ff› ⟩
        }
    },
    case ctypeWhile : {
       show ∃ cs', (WHILE b DO c, s)↝cs', from
        ⟨ (IF b THEN c ;; WHILE b DO c ELSE SKIP, s), While ⟩
    }
end

theorem type_soundness {Γ : tyenv} {c c' : com} {s s' : pstate} {cs'' : conf} :
  (c, s)↝*(c', s') → (Γ ⊢. c) → (Γ ⊢ₛ s) → ¬(c' = SKIP) → ∃ (cs'' : conf), (c', s')↝cs'':=
begin
  intros,
  induction' ‹(c, s)↝*(c', s')›,
    case refl : {
      show ∃ cs'', (c, s)↝cs'', from
        progress_com ‹(Γ ⊢. c)› ‹(Γ ⊢ₛ s)› ‹¬(c = SKIP)›
    },
    case step : _ c₃ c' _ s₃ s' _ _ _ {
      have : (Γ ⊢. c₃), from 
        preservation_com ‹(Γ ⊢. c)› ‹(c, s)↝(c₃, s₃)›,

      have : (Γ ⊢ₛ s₃), from 
        preservation_state ‹(Γ ⊢. c)› ‹(Γ ⊢ₛ s)› ‹(c, s)↝(c₃, s₃)›,

      show ∃ cs'', (c', s')↝cs'', from
        ih ‹(Γ ⊢. c₃)› ‹(Γ ⊢ₛ s₃)› ‹¬(c' = SKIP)› 
    }
end