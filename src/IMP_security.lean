import tactic.induction
import order.min_max

abbreviation vname  := string
abbreviation val    := ℕ
abbreviation pstate := vname → val

inductive aexp : Type
| N    : ℕ → aexp
| V    : vname → aexp
| Plus : aexp → aexp → aexp

open aexp

def aval : aexp → pstate → val
| (N n)        _ := n
| (V x)        s := s x
| (Plus a₁ a₂) s := (aval a₁ s) + (aval a₂ s)

def state_update (s : pstate) (x : vname) (v : val) : pstate :=
  λ y, if (y = x) then v else s y

notation s `[` x ` ↦ ` v `]`:100 := state_update s x v
notation   `[` x ` ↦ ` v `]` := (λ _, 0 ) [x ↦ v]

inductive bexp : Type
| Bc   : bool → bexp
| Not  : bexp → bexp
| And  : bexp → bexp → bexp
| Less : aexp → aexp → bexp

open bexp

def bval : bexp → pstate → bool
| (Bc v)       _ := v
| (Not b)      s := ¬(bval b s)
| (And b₁ b₂)  s := (bval b₁ s) ∧ (bval b₂ s)
| (Less a₁ a₂) s := (aval a₁ s) < (aval a₂ s)

abbreviation lv := ℕ

def sec : vname → lv :=
  λ (x : vname), x.length

def secₐ : aexp → lv
| (N n)        := 0
| (V x)        := sec x
| (Plus a₁ a₂) := max (secₐ a₁) (secₐ a₂)

def sec₆ : bexp → lv
| (Bc v)       := 0
| (Not b)      := sec₆ b
| (And b₁ b₂)  := max (sec₆ b₁) (sec₆ b₂)
| (Less a₁ a₂) := max (secₐ a₁) (secₐ a₂)

notation s ` = ` t ` ⦅<= ` l `⦆` := ∀ (x : vname), (sec x <= l) → s x = t x
notation s ` = ` t ` ⦅< ` l `⦆` := ∀ (x : vname), (sec x < l) → s x = t x

lemma noninterference_aexp {s t : pstate} {l : lv} {a : aexp} :
  s = t ⦅<= l⦆ → (secₐ a <= l) → (aval a s = aval a t) :=
begin
  intros,
  induction' a,
    case N : {
      trivial
    },
    case V : x {
      dsimp[secₐ] at *,

      show aval (V x) s = aval (V x) t, by
        simp_rw[aval, ‹s = t ⦅<= l⦆› x ‹sec x ≤ l›]
    },
    case Plus : a₁ a₂ ih₁ ih₂ {
      dsimp[secₐ] at *,

      have : (secₐ a₁ <= l) ∧ (secₐ a₂ <= l), by 
        simpa using ‹max (secₐ a₁) (secₐ a₂) ≤ l›,
      cases' ‹(secₐ a₁ <= l) ∧ (secₐ a₂ <= l)›,

      have : aval a₁ s = aval a₁ t, from ih₁ ‹s = t ⦅<= l⦆› ‹(secₐ a₁ <= l)›,
      have : aval a₂ s = aval a₂ t, from ih₂ ‹s = t ⦅<= l⦆› ‹(secₐ a₂ <= l)›,

      show aval (Plus a₁ a₂) s = aval (Plus a₁ a₂) t, by
        simp_rw[aval, ‹aval a₁ s = aval a₁ t›, ‹aval a₂ s = aval a₂ t›]
    }
end

lemma noninterference_bexp {s t : pstate} {l : lv} {b : bexp} :
  s = t ⦅<= l⦆ → (sec₆ b <= l) → (bval b s = bval b t) :=
begin
  intros,
  induction' b,
    case Bc : {
      trivial
    },
    case Not : {
      dsimp[sec₆] at *,

      have : bval b s = bval b t, from ih ‹s = t ⦅<= l⦆› ‹sec₆ b ≤ l›,

      show bval (Not b) s = bval (Not b) t, by 
        simp_rw[bval, ‹bval b s = bval b t›]
    },
    case And : b₁ b₂ ih₁ ih₂ {
      dsimp[sec₆] at *,

      have : (sec₆ b₁ <= l) ∧ (sec₆ b₂ <= l), by
        simpa using ‹max (sec₆ b₁) (sec₆ b₂) <= l›,
      cases' ‹(sec₆ b₁ <= l) ∧ (sec₆ b₂ <= l)›,

      have : bval b₁ s = bval b₁ t, from ih₁ ‹s = t ⦅<= l⦆› ‹sec₆ b₁ ≤ l›,
      have : bval b₂ s = bval b₂ t, from ih₂ ‹s = t ⦅<= l⦆› ‹sec₆ b₂ ≤ l›,

      show bval (And b₁ b₂) s = bval (And b₁ b₂) t, by
        simp_rw[bval, ‹bval b₁ s = bval b₁ t›, ‹bval b₂ s = bval b₂ t›]
    },
    case Less : a₁ a₂ {
      dsimp[sec₆] at *,

      have : (secₐ a₁ <= l) ∧ (secₐ a₂ <= l), by
        simpa using ‹max (secₐ a₁) (secₐ a₂) <= l›,
      cases' ‹(secₐ a₁ <= l) ∧ (secₐ a₂ <= l)›,

      have : aval a₁ s = aval a₁ t, from 
        noninterference_aexp ‹s = t ⦅<= l⦆› ‹(secₐ a₁ <= l)›,
      have : aval a₂ s = aval a₂ t, from 
        noninterference_aexp ‹s = t ⦅<= l⦆› ‹(secₐ a₂ <= l)›,

      show bval (Less a₁ a₂) s = bval (Less a₁ a₂) t, by
        simp_rw[bval, ‹aval a₁ s = aval a₁ t›, ‹aval a₂ s = aval a₂ t›]
    }
end
