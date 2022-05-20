/-
Authore: Andrea Delmastro
-/
import tactic.induction
import data.real.basic

/-!
# Tipi semplici per IMP

Questo file estende il linguaggio di programmazione IMP ad ammettere sia valori interi sia valori
reali. Assunto che le due categorie di valori siano tra di loro incompatibili, la semantica viene
modificata per supportare questa assunzione. Programmi sintatticamente corretti possono allora
comporatare condizioni di errore. Il sistema di tipi garantisce l'assenza di errori a tempo di 
esecuzione tramite una valutazione statica a tempo di compilazione.

## Note di implementazione

Questo file utilizza i tattici `cases'` e `induction'` definiti in `tactic.induction`. 
Nonostante le medesime dimostrazioni siano ottenibili tramite i tattici `cases` e `induction` 
classici, le due versioni qui utilizzate meglio si prestano all'utilizzo con predicati induttivi e 
sono più 'naturali' rispetto alla medesima dimostrazione svolta su carta.

## Notazione

* `vname` : nome di variabile, `string`
* `val` : valore di un'espressione, `ℕ`
* `pstate` : stato di programma, funzione da `vname` a `val`
* `s[x ↦ v]` : aggiornamento dello stato `s`, con assegnazione di `v` a `x`
* `::=` : comando di assegnamento
* `;;` : comando di concatenazione sequenziale tra comandi
* `IF THEN ELSE` : comando ramificazione condizionale
* `WHILE DO` : comando di ciclo
* `conf` : configurazione, coppia `com × pstate`
* `⟹` : relazione big-step
* `∼` : equivalenza di comandi
* `↝` : riduzione small-step
* `↝*` : chiusura riflessiva e transitiva di `↝`
* `⊢ₐ` : giudizio di tipo per espressioni aritmetiche
* `⊢₆` : giudizio di tipo per espressioni booleane
* `⊢.` : giudizio di tipo per comandi
* `⊢₅` : compatibilità tra contesto e stato

## Risultati principali

* `progress_aexp {Γ : tyenv} {a : aexp} {τ : ty} {s : pstate} : (Γ ⊢ₐ a : τ) → (Γ ⊢₅ s) → ∃ (v : val), taval a s v`
* `progress_bexp {Γ : tyenv} {b : bexp} {s : pstate} : (Γ ⊢₆ b) → (Γ ⊢₅ s) → ∃ (v : bool), tbval b s v`
* `progress_com {Γ : tyenv} {c : com} { s: pstate} : (Γ ⊢. c) → (Γ ⊢₅ s) → ¬(c = SKIP) → ∃ (cs' : conf), (c, s)↝cs'`
* `type_soundness {Γ : tyenv} {c c' : com} {s s' : pstate} {cs'' : conf} : (c, s)↝*(c', s') → (Γ ⊢. c) → (Γ ⊢₅ s) → ¬(c' = SKIP) → ∃ (cs'' : conf), (c', s')↝cs''`

## Riferimenti

* [Nipkow, Klein, Concrete Semantics with Isabelle/HOL][Nipkow] cap. 9 par. 9.1
-/

abbreviation vname := string

inductive val : Type
| Iv : ℕ → val
| Rv : ℝ → val

open val

/--
Uno stato è una rappresentazione astratta della memora che  associa ad ogni variabile un valore.
-/
abbreviation pstate := vname → val

/--
Aggiornamento dello stato: associa ad una variabile un nuovo valore entro uno stato.
-/
def state_update (s : pstate) (x : vname) (v : val) : pstate :=
  λ y, if (y = x) then v else s y

/--
Stato vuoto, associa ad ogni variabile il valore intero 0.
-/
def emp : pstate := (λ _, (Iv 0))

notation s `[` x ` ↦ ` v `]`:100 := state_update s x v
notation   `[` x ` ↦ ` v `]`     := emp [x ↦ v]

/--
Lemma tecnico utile all'utilizzo del tattico `simp` per l'applicazione degli stati.
-/
@[simp] lemma apply_state_update_pos {x y : vname} {s : pstate} {v : val} :
  (y = x) → s[x ↦ v] y = v := 
begin
  intro,
  dsimp[state_update],
  apply if_pos,
  assumption
end

/--
Lemma tecnico utile all'utilizzo del tattico `simp` per l'applicazione degli stati.
-/
@[simp] lemma apply_state_update_neg {x y : vname} {s : pstate} {v : val} :
  ¬(y = x) → s[x ↦ v] y = (s y) :=
begin
  intro,
  dsimp[state_update],
  apply if_neg,
  assumption
end

/-!
### Espressioni aritmetiche

Le espressioni aritmentiche prevedono due tipi di costanti: intere e reali.
-/

inductive aexp : Type
| Ic   : ℕ → aexp
| Rc   : ℝ → aexp
| V    : vname → aexp
| Plus : aexp → aexp → aexp

open aexp

/-!
### Valutazione di espressioni aritmetiche

La valutazione delle espressioni aritmetiche è ora una funzione parziale: solo per le espressioni 
ben formate (quelle che coinvolgono solo valori interi o solo valori reali) la valutazione termina
producendo un valore.
A questa formulazione viene preferita una definizione tramite un predicato induttivo, dove 
un'espressione viene messa in relazione al suo valore entro lo stato di valutazione. I casi non ben 
formati non vengono definiti: in questo modo non esiterà una valutazione entro il sistema di tali 
espressioni.
-/

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

/-!
### Espressioni booleane
-/

inductive bexp : Type
| Bc   : bool → bexp
| Not  : bexp → bexp
| And  : bexp → bexp → bexp
| Less : aexp → aexp → bexp

open bexp

/-!
### Valutazione di espressioni booleane

Analogo alla valutazione per espressioni aritmetiche.
-/

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

/-!
### Sintassi per il linguaggio di programmazione IMP
-/

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

/-!
### Semantica operazionale small-step di IMP

La semantica dei comandi viene definita tramite una formulazione small-step, che meglio si presta 
alla rappresentazione di computazioni che possono produrre errori. La semantica per questa versione 
di IMP è molto simile a quella già definita, con la differenza che ogniqualvolta sia richiesta la 
valutazione di un’espressione, questa deve essere derivabile entro i sistemi definiti 
precedentemente.
-/

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

/-!
### Sistema di tipo per IMP

L'obiettivo del sistema di tipo é di predirre staticamente quali valori verranno generati dalle 
espressioni ed evitare che espressioni malformate possano comparire durante la computazione.
Il sistema di tipo qui presentato è molto rudimentale: presenta solamente due tipi (`Ity` e `Rty`) 
che corrispondono alle due categorie di valori introdotte per le espressioni aritmetiche.
Lo scopo del sistema di tipo é di tenere traccia dei tipi associati alle variabili e di permettere 
esclusivamente combinazioni compatibili internamente alle espressioni.
Definiamo un contesto `tyenv` come una funzione che associa ad ogni variabile il proprio tipo.
-/

inductive ty : Type
| Ity
| Rty

open ty

/--
Un contesto tiene traccia dei tipi associati a ciascuna variabile.
-/
abbreviation tyenv := vname → ty

/-!
### Giudizi per espressioni aritmetiche

Una espressione aritmetica `a` è ben tipata nel contesto `Γ` con tipo `τ`, simbolicamente 
`Γ ⊢ₐ a : τ` se é una costante, una variabile o la somma di due espressioni ben tipate a cui è
associato lo stesso tipo.
-/

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

/-!
### Giudizi per espressioni booleane

Una espressione booleana `b` è ben tipata nel contesto `Γ`, simbolicamente `Γ ⊢₆ b` se é una 
costante, la negazione di una espressione ben tipata o il confronto tra due espressioni aritmetiche 
ben tipate a cui è associato lo stesso tipo.
-/

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

/-!
### Giudizi per comandi

Un comando `c` è ben tipato nel contesto `Γ`, simbolicamente `Γ ⊢. c` se le sue componenti sono ben 
tipate e se ogni assegnamento avviene tra variabili ed espressioni dello stesso tipo.
-/

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

/-
La funzione `type` associa ad ogni valore il tipo cui è compatibile.
-/
def type : val → ty
| (Iv i) := Ity
| (Rv r) := Rty

/-
Uno stato `s` é ben tipato in un contesto `Γ`, simbolicamente `Γ ⊢₅ s` se associa ad ogni variabile 
un valore compatibile.
-/
notation Γ ` ⊢₅ ` s := ∀ (y : vname), type (s y) = Γ y

/--
Lemma di preservazione per espressioni aritmetiche: se una espressione aritmetica é ben tipata, la 
sua valutazione in uno stato ben tipato produce un valore compatibile con il tipo associato
all'espressione.
-/
lemma preservation_aexp {Γ : tyenv} {a : aexp} {τ : ty} {s : pstate} {v : val} : 
  (Γ ⊢ₐ a : τ) → taval a s v → (Γ ⊢₅ s) → type v = τ :=
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
      apply ‹(Γ ⊢₅ s)›
    },
    case atypeP : _ a₁ a₂ τ _ _ ih₁ ih₂ {
      cases ‹taval (Plus a₁ a₂) s v›,
        case tavalPI : _ _ _ i₁ i₂ _ _ { 
          have : τ = Ity, {
            have : type (Iv i₁) = τ, from ih₁ ‹taval a₁ s (Iv i₁)› ‹(Γ ⊢₅ s)›,
            rw[type] at this,
            symmetry,
            assumption
          },
          rw[‹τ = Ity›],
          trivial
        },
        case tavalPR : _ _ _ r₁ r₂ _ _ {
          have : τ = Rty, {
            have : type (Rv r₁) = τ, from ih₁ ‹taval a₁ s (Rv r₁)› ‹(Γ ⊢₅ s)›,
            rw[type] at this,
            symmetry,
            assumption
          },
          rw[‹τ = Rty›],
          trivial
        }
    }
end

namespace extract

/-!
Regole di inversione per `type`.
-/

lemma Ity {v : val} :
  (type v = Ity) → ∃ i, v = (Iv i) :=
begin
  intro,
  cases v,
    case Iv : i { exact ⟨i, rfl⟩ },
    case Rv : { contradiction }
end

lemma Rty {v : val} :
  (type v = Rty) → ∃ r, v = (Rv r) :=
begin
  intro,
  cases v,
    case Iv : { contradiction },
    case Rv : r { exact ⟨r, rfl⟩ }
end

end extract

/--
Lemma di progresso per espressioni aritmetiche: se una espressione é ben tipata, allora la sua 
valutazione termina senza errori.
-/
lemma progress_aexp {Γ : tyenv} {a : aexp} {τ : ty} {s : pstate} :
  (Γ ⊢ₐ a : τ) → (Γ ⊢₅ s) → ∃ (v : val), taval a s v :=
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
      have : ∃ v, taval a₁ s v, from ih₁ ‹(Γ ⊢₅ s)›,
      cases ‹∃ v, taval a₁ s v› with v₁,

      have : ∃ v, taval a₂ s v, from ih₂ ‹(Γ ⊢₅ s)›,
      cases ‹∃ v, taval a₂ s v› with v₂,

      have : type v₁ = τ, from 
        preservation_aexp ‹(Γ ⊢ₐ a₁ : τ)› ‹taval a₁ s v₁› ‹(Γ ⊢₅ s)›,

      have : type v₂ = τ, from
        preservation_aexp ‹(Γ ⊢ₐ a₂ : τ)› ‹taval a₂ s v₂› ‹(Γ ⊢₅ s)›,

      cases τ,
        case Ity : {
          have : ∃ i₁, v₁ = (Iv i₁), from extract.Ity ‹type v₁ = Ity›,
          cases ‹∃ i₁, v₁ = (Iv i₁)› with i₁,
          rw[‹v₁ = Iv i₁›] at *,

          have : ∃ i₂, v₂ = (Iv i₂), from extract.Ity ‹type v₂ = Ity›,
          cases ‹∃ i₂, v₂ = (Iv i₂)› with i₂,
          rw[‹v₂ = Iv i₂›] at *,

          show ∃ v, taval (Plus a₁ a₂) s v, from 
            ⟨ (Iv (i₁ + i₂)), tavalPI ‹taval a₁ s (Iv i₁)› ‹taval a₂ s (Iv i₂)› ⟩
        },
        case Rty : {
          have : ∃ r₁, v₁ = (Rv r₁), from extract.Rty ‹type v₁ = Rty›,
          cases ‹∃ r₁, v₁ = (Rv r₁)› with r₁,
          rw[‹v₁ = Rv r₁›] at *,

          have : ∃ r₂, v₂ = (Rv r₂), from extract.Rty ‹type v₂ = Rty›,
          cases ‹∃ r₂, v₂ = (Rv r₂)› with r₂,
          rw[‹v₂ = Rv r₂›] at *,

          show ∃ v, taval (Plus a₁ a₂) s v, from 
            ⟨ (Rv (r₁ + r₂)), tavalPR ‹taval a₁ s (Rv r₁)› ‹taval a₂ s (Rv r₂)› ⟩
        }
    },
end

/--
Lemma di progresso per espressioni booleane: se una espressione booleana é ben tipata, la sua 
valutazione termina senza errori.
-/
lemma progress_bexp {Γ : tyenv} {b : bexp} {s : pstate} :
  (Γ ⊢₆ b) → (Γ ⊢₅ s) → ∃ (v : bool), tbval b s v :=
begin
  intros,
  induction' ‹(Γ ⊢₆ b)›,
    case btypeC : {
      show ∃ v, tbval (Bc bv) s v, from
        ⟨ bv, tbvalC ⟩
    },
    case btypeN : {
      have : ∃ v, tbval b s v, from ih ‹(Γ ⊢₅ s)›,
      cases ‹∃ v, tbval b s v› with bv,

      show ∃ v, tbval (Not b) s v, from
        ⟨ ¬bv, tbvalN ‹tbval b s bv› ⟩
    },
    case btypeA : _ b₁ b₂ _ _ ih₁ ih₂ { 
      have : ∃ v, tbval b₁ s v, from ih₁ ‹(Γ ⊢₅ s)›,
      cases ‹∃ v, tbval b₁ s v› with bv₁,

      have : ∃ v, tbval b₂ s v, from ih₂ ‹(Γ ⊢₅ s)›,
      cases ‹∃ v, tbval b₂ s v› with bv₂,

      show ∃ v, tbval (And b₁ b₂) s v, from
        ⟨ (bv₁ ∧ bv₂), tbvalA ‹tbval b₁ s bv₁› ‹tbval b₂ s bv₂› ⟩
    },
    case btypeL : _ _ _ τ _ _ { 
      have : ∃ v, taval a₁ s v, from 
        progress_aexp ‹(Γ ⊢ₐ a₁ : τ)› ‹(Γ ⊢₅ s)›,
      cases ‹∃ v, taval a₁ s v› with v₁,

      have : ∃ v, taval a₂ s v, from 
        progress_aexp ‹(Γ ⊢ₐ a₂ : τ)› ‹(Γ ⊢₅ s)›,
      cases ‹∃ v, taval a₂ s v› with v₂,

      have : type v₁ = τ, from 
        preservation_aexp ‹(Γ ⊢ₐ a₁ : τ)› ‹taval a₁ s v₁› ‹(Γ ⊢₅ s)›,

      have : type v₂ = τ, from
        preservation_aexp ‹(Γ ⊢ₐ a₂ : τ)› ‹taval a₂ s v₂› ‹(Γ ⊢₅ s)›,

      cases τ,
        case Ity : {
          have : ∃ i, v₁ = (Iv i), from extract.Ity ‹type v₁ = Ity›,
          cases ‹∃ i, v₁ = (Iv i)› with i₁,
          rw[‹v₁ = Iv i₁›] at *,

          have : ∃ i, v₂ = (Iv i), from extract.Ity ‹type v₂ = Ity›,
          cases ‹∃ i, v₂ = (Iv i)› with i₂,
          rw[‹v₂ = Iv i₂›] at *,

          show ∃ v, tbval (Less a₁ a₂) s v, from
            ⟨ (i₁ < i₂), tbvalLI ‹taval a₁ s (Iv i₁)› ‹taval a₂ s (Iv i₂)› ⟩
        },
        case Rty : {
          have : ∃ r, v₁ = (Rv r), from extract.Rty ‹type v₁ = Rty›,
          cases ‹∃ r, v₁ = (Rv r)› with r₁,
          rw[‹v₁ = Rv r₁›] at *,

          have : ∃ r, v₂ = (Rv r), from extract.Rty ‹type v₂ = Rty›,
          cases ‹∃ r, v₂ = (Rv r)› with r₂,
          rw[‹v₂ = Rv r₂›] at *,

          show ∃ v, tbval (Less a₁ a₂) s v, from
            ⟨ (r₁ < r₂), tbvalLR ‹taval a₁ s (Rv r₁)› ‹taval a₂ s (Rv r₂)› ⟩
        }
    }
end

/--
Teorema di preservazione per comandi: se un comando `c` é ben tipato e si riduce in un passo ad un 
comando `c'`, allora anche `c'` é ben tipato. 
-/
lemma preservation_com {Γ : tyenv} {c c' : com} {s s' : pstate } :
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

/--
Teorema di preservazione per gli stati: uno stato `s` ben tipato si mantiene tale anche dopo 
l'esecuzione di un comando `c`.
-/
lemma preservation_state {Γ : tyenv} {c c' : com} {s s' : pstate } :
  (Γ ⊢. c) → (Γ ⊢₅ s) → (c, s)↝(c', s') → (Γ ⊢₅ s') :=
begin
  intro, intro, intro,
  induction' ‹(Γ ⊢. c)›,
    case ctypeSKIP : {
      cases' ‹(SKIP, s)↝(c', s')› -- impossibile
    },
    case ctypeAssign : _ _ x _ {
      cases' ‹(x ::= a, s)↝(c', s')› with _ x _ _ _,

      have : type v = Γ x, from
        preservation_aexp ‹(Γ ⊢ₐ a : Γ x)› ‹taval a s v› ‹(Γ ⊢₅ s)›,

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

          show type (s y) = Γ y, from ‹(Γ ⊢₅ s)› y
        }

    },
    case ctypeSeq : _ c₁ c₂ _ _ ih₁ ih₂ {
      cases' ‹(c₁ ;; c₂, s)↝(c', s')›,
        case Seq1 : {
          show (Γ ⊢₅ s), by assumption
        },
        case Seq2 : {
          show (Γ ⊢₅ s'), from ih₁ ‹(Γ ⊢₅ s)› ‹(c₁, s)↝(c₁', s')›,
        }
    },
    case ctypeIf : _ _ c₁ c₂ _ _ _ ih₁ ih₂ { 
      cases' ‹(IF b THEN c₁ ELSE c₂, s)↝(c', s')›,
        case IfTrue : {
          show (Γ ⊢₅ s), by assumption
        },
        case IfFalse : {
          show (Γ ⊢₅ s), by assumption
        }
    },
    case ctypeWhile : {
      cases' ‹(WHILE b DO c, s)↝(c', s')›,

      show (Γ ⊢₅ s), by assumption 
    }
end

/--
Teorema di progresso per comandi: se un comando `c` diverso da `SKIP` ben tipato viene eseguito in 
un contesto `s` ben tipato, allora il programma esegue per almeno un passo di calcolo.
-/
lemma progress_com {Γ : tyenv} {c : com} { s: pstate} :
  (Γ ⊢. c) → (Γ ⊢₅ s) → ¬(c = SKIP) → ∃ (cs' : conf), (c, s)↝cs' :=
begin
  intros,
  induction' ‹(Γ ⊢. c)›,
    case ctypeSKIP : { 
      contradiction 
    },
    case ctypeAssign : {
      have : ∃ v, taval a s v, from progress_aexp ‹(Γ ⊢ₐ a : Γ x)› ‹(Γ ⊢₅ s)›,
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
          have : ∃ cs', (c₁, s)↝cs', from ih₁ ‹(Γ ⊢₅ s)› ‹¬(c₁ = SKIP)›,
          cases' ‹∃ cs', (c₁, s)↝cs'› with cs',
          cases' cs' with c₁' s',
          
          show ∃ cs', (c₁ ;; c₂, s)↝cs', from
            ⟨ (c₁';; c₂, s'), Seq2 ‹(c₁, s)↝(c₁', s')› ⟩
        }
    },
    case ctypeIf : _ _ c₁ c₂ _ _ _ ih₁ ih₂ {
      have : ∃ v, tbval b s v, from progress_bexp ‹(Γ ⊢₆ b)› ‹(Γ ⊢₅ s)›,
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

/--
Teorema di correttezza del sistema di tipo: data l'esecuzione di un comando `c` ben tipato in uno 
stato `s` ben tipato, o l'esecuzione é terminata, o é possibile compiere un ulteriore passo di 
calcolo (la computazione non si blocca).
                        'Well typed programs cannot go wrong'.
-/
theorem type_soundness {Γ : tyenv} {c c' : com} {s s' : pstate} {cs'' : conf} :
  (c, s)↝*(c', s') → (Γ ⊢. c) → (Γ ⊢₅ s) → ¬(c' = SKIP) → ∃ (cs'' : conf), (c', s')↝cs'':=
begin
  intros,
  induction' ‹(c, s)↝*(c', s')›,
    case refl : {
      show ∃ cs'', (c, s)↝cs'', from
        progress_com ‹(Γ ⊢. c)› ‹(Γ ⊢₅ s)› ‹¬(c = SKIP)›
    },
    case step : _ c₃ c' _ s₃ s' _ _ _ {
      have : (Γ ⊢. c₃), from 
        preservation_com ‹(Γ ⊢. c)› ‹(c, s)↝(c₃, s₃)›,

      have : (Γ ⊢₅ s₃), from 
        preservation_state ‹(Γ ⊢. c)› ‹(Γ ⊢₅ s)› ‹(c, s)↝(c₃, s₃)›,

      show ∃ cs'', (c', s')↝cs'', from
        ih ‹(Γ ⊢. c₃)› ‹(Γ ⊢₅ s₃)› ‹¬(c' = SKIP)› 
    }
end