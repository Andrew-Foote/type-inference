#lang racket
(require rackunit)

(define log (make-parameter #f))

(define (app-till-false f x)
  (let loop ([x x])
    (when (log) (displayln x))
    (let ([y (f x)])
      (if y
          (loop y)
          x))))

(module+ test (check-equal? (app-till-false (λ (x) (and (not (zero? x)) (sub1 x))) 10) 0))
    
(define type-var? symbol?)

(define type?
  (flat-rec-contract
   type?
   type-var?
   (list/c '→ type? type?)))

(define/contract (→ . As) (->* () () #:rest (non-empty-listof type?) type?)
  (match-let ([(list As ... B) As])
    (foldl (curry list '→) B (reverse As))))

(module+ test (check-equal? (→ 'a 'b 'c) '(→ a (→ b c))))

(define/contract (type-free-vars A) (-> type? (set/c type-var?))
  (match A
    [(? type-var? a) (set a)]
    [`(→ ,A ,B)      (set-union (type-free-vars A) (type-free-vars B))]))

(module+ test (check-equal? (type-free-vars (→ (→ 'a 'b) 'a 'c)) (set 'a 'b 'c)))

(define/contract type-var-letters string? "abcdefghijklmnopqrstuvwxyz")
(define/contract type-var-letter-count natural? (string-length type-var-letters))

(define/contract (type-var-ref i) (-> natural? type-var?)
  (string->symbol
   (let-values ([(q r) (quotient/remainder i type-var-letter-count)])
     (string-append
      (string (string-ref type-var-letters r))
      (if (zero? q) "" (number->string q))))))

(module+ test
  (check-equal? (type-var-ref 0) 'a)
  (check-equal? (type-var-ref 1) 'b)
  (check-equal? (type-var-ref 25) 'z)
  (check-equal? (type-var-ref 26) 'a1))

(define/contract (in-type-vars) (-> (stream/c type-var?))
  (stream-map type-var-ref (in-naturals)))

(module+ test
  (check-equal? (stream->list (stream-take (in-type-vars) 4)) '(a b c d)))

(define/contract (fresh-type-vars stale-vars n) (-> (set/c type-var?) natural? (listof type-var?))
  (stream->list
   (stream-take (stream-filter (compose not (curry set-member? stale-vars)) (in-type-vars)) n)))

(define/contract (fresh-type-var stale-vars) (-> (set/c type-var?) type-var?)
  (car (fresh-type-vars stale-vars 1)))

(module+ test
  (check-equal? (fresh-type-var (set 'a 'b 'c)) 'd)
  (check-equal? (fresh-type-var (set 'b 'c)) 'a)
  (check-equal? (fresh-type-vars (set 'a 'd 'e) 3) '(b c f)))

(define/contract (subst? obj) (-> any/c boolean?)
  (match obj
    [(list (cons as As) ...) (and (andmap type-var? as)
                                  (andmap type? As)
                                  (not (check-duplicates as))
                                  (andmap (compose not equal?) as As))]
    [_                       #f]))

(module+ test
  (check-true (subst? '((a . b) (b . (→ c a)))))
  (check-false (subst? '((a . b) (b . 2))))
  (check-false (subst? '((a . b) (a . (→ c a)))))
  (check-false (subst? '((a . b) (b . b)))))

(define/contract (make-subst lst) (-> (listof (cons/c type-var? type?)) subst?)
  (append-map (λ (a) (let ([A (dict-ref lst a)]) (if (eq? a A) '() `((,a . ,A)))))
              (remove-duplicates (dict-keys lst))))

(module+ test
  (check-equal? (make-subst '((a . b) (b . (→ c a)))) '((a . b) (b . (→ c a))))
  (check-equal? (make-subst '((a . b) (a . (→ c a)))) '((a . b)))
  (check-equal? (make-subst '((a . b) (b . b))) '((a . b))))

(define/contract (subst-set s a A) (-> subst? type-var? type? subst?)
  (if (eq? a A) (dict-remove s a) (dict-set s a A)))

(define/contract (subst-remove s a) (-> subst? type-var? subst?)
  (dict-remove s a))

(define/contract (subst-app s A) (-> subst? type? type?)
  (match A
    [(? symbol? a) (dict-ref s a a)]
    [`(→ ,A ,B)    `(→ ,(subst-app s A) ,(subst-app s B))]))

(module+ test
  (check-equal? (subst-app '((a . (→ a b)) (b . c)) (→ 'a 'b 'a)) (→ '(→ a b) 'c '(→ a b))))

(define term-var? symbol?)

(define term?
  (flat-rec-contract
   term?
   term-var?
   (list/c 'λ term-var? term?)
   (list/c term? term?)))

(define/contract (λ* . xs-and-t) (->* () () #:rest (*list/c term-var? term?) term?)
  (match-let ([(list xs ... t) xs-and-t])
    (foldl (curry list 'λ) t (reverse xs))))

(module+ test
  (check-equal? (λ* 'x 'y 'z '((x z) (y z))) '(λ x (λ y (λ z ((x z) (y z)))))))

(define S (λ* 'x 'y 'z '((x z) (y z))))
(define K (λ* 'x 'y 'x))

(define env? (listof (cons/c term-var? type?)))

(define judg? (list/c '⊢ env? term? type?))

(define/contract (typed-term? obj) (-> any/c boolean?)
  (match obj
    [`(⊢ ,(? env? Γ) ,(? term-var? x))        (dict-has-key? Γ x)]
    [`(λ ,(? symbol? x) ,(? typed-term? t))   (match-let ([`(⊢ ,Γ ,_ ,_) (typed-term->judg t)])
                                                (dict-has-key? Γ x))]
    [`(,(? typed-term? t) ,(? typed-term? u)) (match* ((typed-term->judg t) (typed-term->judg u))
                                                [(`(⊢ ,Γ ,_ (→ ,A ,_)) `(⊢ ,Γ ,_ ,A)) #t]
                                                [(_ _)                                #f])]))

(define/contract (typed-term->judg t) (-> typed-term? judg?)
  (match t
    [`(⊢ ,Γ ,x) `(⊢ ,Γ ,x ,(dict-ref Γ x))]
    [`(λ ,x ,t) (match-let ([`(⊢ ,Γ ,t ,B) (typed-term->judg t)])
                  (let ([A (dict-ref Γ x)])
                    `(⊢ ,(dict-remove Γ x) (λ ,x ,t) (→ ,A ,B))))]
    [`(,t ,u)   (match-let ([`(⊢ ,Γ ,t (→ ,_ ,A)) (typed-term->judg t)])
                  `(⊢ ,Γ (,t ,u) ,A))]))

(define equation? (list/c '= type? type?))
(define substitution? (list/c ':= type-var? type?))
(define assignment? (list/c ': term-var? type?))

(define constraint?
  (flat-rec-contract
   constraint?
   equation? substitution? assignment?
   (list/c '∧ constraint? constraint?)
   (list/c '∃ type-var? constraint?)
   (list/c 'def term-var? type? constraint?)))

(define/contract (∧ . cs) (->* () () #:rest (non-empty-listof constraint?) constraint?)
  (match-let ([(list cs ... d) cs])
    (foldl (curry list '∧) d (reverse cs))))

(define/contract (∃ . as-and-c) (->* () () #:rest (*list/c type-var? constraint?) constraint?)
  (match-let ([(list as ... c) as-and-c])
    (foldl (curry list '∃) c (reverse as))))

(module+ test
  (check-equal? (λ* 'x 'y 'z '((x z) (y z))) '(λ x (λ y (λ z ((x z) (y z)))))))

(define/contract (constraint-free-vars c) (-> constraint? (set/c type-var?))
  (match c
    [`(= ,A ,B)      (set-union (type-free-vars A) (type-free-vars B))]
    [`(:= ,a ,A)     (set-add (type-free-vars A) a)]
    [`(: ,x ,A)      (type-free-vars A)]
    [`(∧ ,c0 ,c1)    (set-union (constraint-free-vars c0) (constraint-free-vars c1))]
    [`(∃ ,a ,c)      (set-remove (constraint-free-vars c) a)]
    [`(def ,x ,A ,c) (set-union (type-free-vars A) (constraint-free-vars c))]))

(module+ test
  (check-equal? (constraint-free-vars '(= (→ a b) a)) (set 'a 'b))
  (check-equal? (constraint-free-vars '(∃ a (∧ (: x a) (: y b)))) (set 'b))
  (check-equal? (constraint-free-vars `(def x (→ b d) ,(∃ 'b 'c `(: x ,(→ 'a 'b 'c 'd)))))
                (set 'a 'b 'd)))

(define/contract (subst-app-constraint s c) (-> subst? constraint? constraint?)
  (match c
    [`(= ,A ,B)      `(= ,(subst-app s A) ,(subst-app s B))]
    [`(:= ,a ,A)     `(= ,(subst-app s a) ,(subst-app s A))]
    [`(: ,x ,A)      `(: ,x ,(subst-app s A))]
    [`(∧ ,c0 ,c1)    `(∧ ,(subst-app-constraint s c0) ,(subst-app-constraint s c1))]
    [`(∃ ,a ,c)      (let* ([b (fresh-type-var
                                 (apply set-union (set)
                                        (set-map (set-remove (constraint-free-vars c) a)
                                                 (compose type-free-vars (curry subst-app s)))))])
                       `(∃ ,b ,(subst-app-constraint (subst-set s a b) c)))]
    [`(def ,x ,A ,c) `(def ,x ,(subst-app s A) ,(subst-app-constraint s c))]))

(module+ test
  (check-equal? (subst-app-constraint '((a . (→ a a))) '(= (→ a b) a)) '(= (→ (→ a a) b) (→ a a)))
  (check-equal? (subst-app-constraint '((b . (→ a b))) '(∃ a (∧ (: x a) (: y (→ a b)))))
                '(∃ c (∧ (: x c) (: y (→ c (→ a b)))))))

(define/contract (constraint-propagate-rule rule c)
  (-> (-> constraint? (or/c constraint? #f)) constraint? (or/c constraint? #f))
  (match c
    [`(∧ ,c0 ,c1)    (let ([d (rule c0)])
                       (if d
                           (∧ d c1)
                           (let ([d (rule c1)])
                             (and d (∧ c0 d)))))]
    [`(∃ ,a ,c)      (let ([d (rule c)])
                       (and d (∃ a d)))]
    [`(def ,x ,A ,c) (let ([d (rule c)])
                       (and d `(def ,x ,A ,d)))]
    [_               #f]))

(define qf-constraint?
  (flat-rec-contract
   qf-constraint?
   equation? substitution? assignment?
   (list/c '∧ qf-constraint? qf-constraint?)
   (list/c 'def term-var? type? qf-constraint?)))

(define prenex-constraint?
  (flat-rec-contract
   prenex-constraint?
   qf-constraint?
   (list/c '∃ type-var? prenex-constraint?)))

; (∧ c0 (∃ a c1)) is equivalent to (∃ a (∧ c0 c1)) as long as a is not free in c0
; if a is free in c0, then we need to rewrite (∃ a c1) to use a new variable b in place of a, which
; is not free in c0, and also not already free in c1
; p(x) ∧ ∃x q(x) := ∃y p(x) ∧ q(y)
(define/contract (∧∃->∃∧ a c0 c1)
  (-> type-var? constraint? constraint? (values type-var? constraint? constraint?))
  (let* ([b (fresh-type-var
             (set-union (constraint-free-vars c0) (set-remove (constraint-free-vars c1) a)))]
         [s (make-subst `((,a . ,b)))])
    (values b c0 (subst-app-constraint s c1))))

(define/contract (def∃->∃def x A a c)
  (-> term-var? type? type-var? constraint? constraint?)
  (let* ([b (fresh-type-var (set-union (type-free-vars A) (set-remove (constraint-free-vars c) a)))]
         [s (make-subst `((,a . ,b)))])
    `(∃ ,b (def ,x ,A ,(subst-app-constraint s c)))))

(define/contract (prenex-1-step c) (-> constraint? (or/c constraint? #f))
  (match c
    [`(∧ (∃ ,a ,c0) ,c1)    (let-values ([(a c1 c0) (∧∃->∃∧ a c1 c0)])
                              `(∃ ,a (∧ ,c1 ,c0)))]
    [`(∧ ,c0 (∃ ,a ,c1))    (let-values ([(a c0 c1) (∧∃->∃∧ a c0 c1)])
                              `(∃ ,a (∧ ,c0 ,c1)))]
    [`(def ,x ,A (∃ ,a ,c)) (def∃->∃def x A a c)]
    [_                      (constraint-propagate-rule prenex-1-step c)]))

(define/contract prenex (-> constraint? prenex-constraint?) (curry app-till-false prenex-1-step))

(define defless-constraint?
  (flat-rec-contract
   defless-constraint?
   (or/c equation? substitution?)
   (list/c '∧ defless-constraint? defless-constraint?)
   (list/c '∃ type-var? defless-constraint?)))

(define/contract (expand-defs-1-step c) (-> constraint? (or/c constraint? #f))
  (match c
    [`(def ,x ,A (= ,B ,C))   `(= ,B ,C)]
    [`(def ,x ,A (:= ,a ,B))  `(:= ,a ,B)]
    [`(def ,x ,A (: ,x ,B))   `(= ,A ,B)]
    [`(def ,x ,A (: ,y ,B))   `(: ,y ,B)]
    [`(def ,x ,A (∧ ,c0 ,c1)) `(∧ (def ,x ,A ,c0) (def ,x ,A ,c1))]
    [`(def ,x ,A (∃ ,a ,c))   (def∃->∃def x A a c)]
    [_                        (constraint-propagate-rule expand-defs-1-step c)]))

(define/contract expand-defs (-> constraint? defless-constraint?)
  (curry app-till-false expand-defs-1-step))

(define equation-conjunction?
  (flat-rec-contract
   equation-conjunction?
   equation?
   substitution?
   (list/c '∧ (or/c equation? substitution?) equation-conjunction?)))

(define solvable-constraint?
  (flat-rec-contract
   solvable-constraint?
   equation-conjunction?
   (list/c '∃ type-var? solvable-constraint?)))

(define/contract (solvable-form-1-step c)
  (-> (and/c prenex-constraint? defless-constraint?)
      (or/c (and/c prenex-constraint? defless-constraint?) #f))
  (match c
    [`(∧ (∧ ,c0 ,c1) ,c2) `(∧ ,c0 (∧ ,c1 ,c2))]
    [_                    (constraint-propagate-rule solvable-form-1-step c)]))

(define/contract solvable-form (-> constraint? solvable-constraint?)
  (compose (curry app-till-false solvable-form-1-step) expand-defs prenex))

(struct/contract exn:unif-fail exn:fail:user ())

(define/contract (raise-unif-fail msg A B) (-> string? type? type? void?)
  (raise (exn:unif-fail
          (string-join (list "unification failure;"
                             (string-append "  " msg)
                             (format "    LHS: ~a" A)
                             (format "    RHS: ~a" B))
                       "\n")
          (current-continuation-marks))))

(define substitution-conjunction?
  (flat-rec-contract
   substitution-conjunction?
   substitution?
   (list/c '∧ substitution? substitution-conjunction?)))

(define solved-constraint?
  (flat-rec-contract
   solved-constraint?
   substitution-conjunction?
   (list/c '∃ type-var? solved-constraint?)))

(define call-count 0)

; very slow, but elegant
(define/contract (solved-form-1-step c)
  (-> solvable-constraint? (or/c solvable-constraint? #f))
  (set! call-count (add1 call-count))
  (match c
    [`(= ,(? type-var? a) ,A)
     `(:= ,a ,A)]
    [`(= ,(? (not/c type-var?) A) ,a)
     `(= ,a ,A)]
    [`(∧ (= (→ ,A ,B) (→ ,C ,D)) ,c)
     (∧ `(= ,A ,C) `(= ,B ,D) c)]
    [`(∧ (= ,(? type-var? a) ,a) ,c)
     c]
    [`(∧ (= ,(? type-var? a) ,A) ,c)
     #:when (set-member? (type-free-vars A) a)
     (raise-unif-fail "LHS occurs in but is not equal to RHS" a A)]
    [`(∧ (:= ,a ,A) ,c)
     #:when (set-member? (constraint-free-vars c) a)
     (∧ `(:= ,a ,A) (subst-app-constraint (make-subst `((,a . ,A))) c))]
    [`(∧ (:= ,a ,A) (= ,(? type-var? b) ,C))
     (∧ `(= ,b ,C) `(:= ,a ,A))]
    [`(∧ (:= ,a ,A) (∧ (= ,(? type-var? b) ,C) ,c))
     (∧ `(= ,b ,C) `(:= ,a ,A) c)]
    [_
     (constraint-propagate-rule solved-form-1-step c)]))

(define/contract solved-form (-> constraint? solved-constraint?)
  (compose (curry app-till-false solved-form-1-step) solvable-form))

(define/contract (solved-constraint->subst c) (-> solved-constraint? subst?)
  (match c
    [`(:= ,a ,A)        (make-subst `((,a . ,A)))]
    [`(∧ (:= ,a ,A) ,c) (subst-set (solved-constraint->subst c) a A)]
    [`(∃ ,a ,c)         (solved-constraint->subst c)]))

(define/contract (solve-constraint c) (-> constraint? subst?)
  (solved-constraint->subst (solved-form c)))

(define/contract (: t A) (-> term? type? constraint?)
  (match t
    [(? symbol? x) `(: ,x ,A)]
    [`(λ ,x ,t)    (match-let ([`(,a ,b) (fresh-type-vars (type-free-vars A) 2)])
                     (∃ a b (∧ `(def ,x ,a ,(: t b)) `(= ,(→ a b) ,A))))]
    [`(,t ,u)      (let ([a (fresh-type-var (type-free-vars A))])
                     (∃ a (∧ (: t (→ a A)) (: u a))))]))

(define/contract (refine-type t A) (-> term? type? type?)
  (let ([s (solve-constraint (: t A))])
    (subst-app s A)))
