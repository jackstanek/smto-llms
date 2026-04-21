(set-logic ALL)

(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(set-option :incremental true)

; =============================================================================
; WORKPLACE THEORY — parametric schema
; Instantiate by replacing Employee, Company, Department with concrete ADTs.
; =============================================================================

; --- Sorts (replace per instance with enumerated datatypes) ---------------

; Instance: 4 employees, 2 departments, 1 company.
(declare-datatype Employee  ((alice) (bob) (carol) (dave)))
(declare-datatype Department ((engineering) (sales)))
(declare-datatype Company   ((acme)))

; --- Option type ----------------------------------------------------------

(declare-datatypes ((Maybe 1))
  ((par (T) ((none) (some (val T))))))

; --- Structural functions -------------------------------------------------

; Every employee has exactly one company and one department.
; Document: this is a simplification; matrix orgs are out of scope.
(declare-fun works_at      (Employee)   Company)
(declare-fun works_in      (Employee)   Department)

; Every department belongs to exactly one company.
(declare-fun department_of (Department) Company)

; Partial: a department may have no head; the top of an org reports to no one.
(declare-fun head_of       (Department) (Maybe Employee))
(declare-fun reports_to    (Employee)   (Maybe Employee))

; --- Act relations --------------------------------------------------------

; Kept as relations: many-to-many semantics.
(declare-fun fired            (Employee Employee) Bool)
(declare-fun approved_expense (Employee Employee) Bool)

; =============================================================================
; STRUCTURAL AXIOMS
; =============================================================================

; S1. Department membership implies company membership.
;     name: dept_company_coherence
;     category: structural, implicit_by_default: FALSE (often stated)
(assert (forall ((p Employee))
  (! (= (works_at p) (department_of (works_in p)))
     :pattern ((works_at p)) :pattern ((works_in p)))))

; S2. A department head works in that department.
;     implicit_by_default: TRUE (very inferable)
(assert (forall ((d Department))
  (! (=> ((_ is some) (head_of d))
         (= (works_in (val (head_of d))) d))
     :pattern ((head_of d)))))

; S3. Reporting propagates company membership.
;     implicit_by_default: TRUE (core puzzle rule)
(assert (forall ((p Employee))
  (! (=> ((_ is some) (reports_to p))
         (= (works_at p) (works_at (val (reports_to p)))))
     :pattern ((reports_to p)))))

; S4. Reporting propagates department membership.
;     implicit_by_default: TRUE (one of your original rules)
;     Modeling note: this forces single-department; drop for matrix orgs.
(assert (forall ((p Employee))
  (! (=> ((_ is some) (reports_to p))
         (= (works_in p) (works_in (val (reports_to p)))))
     :pattern ((reports_to p)))))

; S5. A head of a department implicitly "reports to" no one within the
;     department (heads don't report to themselves or to subordinates).
;     implicit_by_default: TRUE (structural integrity)
(assert (forall ((d Department) (p Employee))
  (=> (= (head_of d) (some p))
      (not (and ((_ is some) (reports_to p))
                (= (works_in (val (reports_to p))) d))))))

; S6. No self-reporting.
;     implicit_by_default: TRUE (axiomatic)
(assert (forall ((p Employee))
  (=> ((_ is some) (reports_to p))
      (not (= (val (reports_to p)) p)))))

; S7. Anti-symmetry of direct reporting. Acyclicity beyond this is enforced
;     at generation time (produce tree-shaped orgs).
(assert (forall ((p Employee) (q Employee))
  (=> (and (= (reports_to p) (some q))
           ((_ is some) (reports_to q)))
      (not (= (val (reports_to q)) p)))))

; =============================================================================
; DERIVED RELATIONS
; =============================================================================

; D1. manages is the inverse of reports_to (sugar, but handy in NL).
(define-fun manages ((p Employee) (q Employee)) Bool
  (= (reports_to q) (some p)))

; D2. chain_of_command = transitive closure of manages.
;     Z3's define-fun-rec handles this; termination relies on the finite
;     Employee domain plus acyclicity from the generator.
(define-fun-rec manages_plus ((p Employee) (q Employee)) Bool
  (or (manages p q)
      (exists ((r Employee))
        (and (manages p r) (manages_plus r q)))))

; D3. Same-company / same-department (convenience).
(define-fun same_company ((p Employee) (q Employee)) Bool
  (= (works_at p) (works_at q)))

(define-fun same_department ((p Employee) (q Employee)) Bool
  (= (works_in p) (works_in q)))

; =============================================================================
; AUTHORITY AXIOMS (structural -> authority)
; =============================================================================

(declare-fun can_fire            (Employee Employee) Bool)
(declare-fun can_approve_expense (Employee Employee) Bool)

; A1. Direct managers can fire.
;     implicit_by_default: FALSE (often stated in the puzzle)
(assert (forall ((p Employee) (q Employee))
  (=> (manages p q) (can_fire p q))))

; A2. Anyone up the chain of command can fire.
;     implicit_by_default: TRUE (this is the big transitive inference
;     the oracle must recover)
(assert (forall ((p Employee) (q Employee))
  (=> (manages_plus p q) (can_fire p q))))

; A3. Department heads can fire department members.
;     implicit_by_default: TRUE
(assert (forall ((p Employee) (q Employee) (d Department))
  (=> (and (= (head_of d) (some p))
           (= (works_in q) d)
           (not (= p q)))
      (can_fire p q))))

; A4. Analogous for expense approval.
(assert (forall ((p Employee) (q Employee))
  (=> (manages p q) (can_approve_expense p q))))

(assert (forall ((p Employee) (q Employee))
  (=> (manages_plus p q) (can_approve_expense p q))))

(assert (forall ((p Employee) (q Employee) (d Department))
  (=> (and (= (head_of d) (some p))
           (= (works_in q) d)
           (not (= p q)))
      (can_approve_expense p q))))

; =============================================================================
; INTEGRITY CONSTRAINTS (disequality-based)
; =============================================================================

; I1. No one can fire themselves.
;     implicit_by_default: TRUE
(assert (forall ((p Employee)) (not (can_fire p p))))

; I2. No one can approve their own expenses. THE classic integrity rule,
;     and a nice trap for the LLM to get wrong.
;     implicit_by_default: TRUE
(assert (forall ((p Employee)) (not (can_approve_expense p p))))

; =============================================================================
; ACT COHERENCE (acts -> authority)
; =============================================================================

; C1. If an act happened, the actor had authority.
(assert (forall ((p Employee) (q Employee))
  (=> (fired p q) (can_fire p q))))

(assert (forall ((p Employee) (q Employee))
  (=> (approved_expense p q) (can_approve_expense p q))))



; Ground facts
(assert (= (works_at alice) acme))
(assert (= (works_in alice) engineering))
(assert (= (works_at bob) acme))
(assert (= (works_in bob) engineering))
(assert (= (works_at carol) acme))
(assert (= (works_in carol) sales))
(assert (= (department_of engineering) acme))
(assert (= (department_of sales) acme))
(assert (= (reports_to alice) (some bob)))
(assert (= (reports_to bob) (some dave)))
(assert (= (head_of engineering) (some dave)))

; Query: can Dave fire Alice? (Should be SAT with can_fire dave alice = true.)
(push)
(assert (not (can_fire dave alice)))
(check-sat)
(pop)
