#lang racket
(module+ test (require rackunit))

; An even better way of dealing with the limitations of combinatory logic is to introduce
; λ-abstraction terms, turning the system into a λ-calculus. This is a kind of means of defining
; primitive combinators into the formal system itself.
;
; So let's forget about primitive combinators for now. That means our contexts don't need to assign
; types to arbitrary continuations any more. On the other hand, the addition of λ-abstractions adds
; its own complications to the notion of a context. Term variables now exist within a particular
; scope, so they no longer have to be assigned the same type wherever they occur in a term. Two
; occurrences of the same variable need only be assigned the same type if they are feee, or if they
; are bound by the same λ-binder.
;
; Fortunately there's a fairly simple way to deal with this: just have a context assign a type to
; to each occurrence of a variable within a λ-binder, as well as each free variable.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type?
  (flat-rec-contract
   type?
   symbol? ; type variable
   (list/c '→ type? type?))) ; function type

(define/contract (occurs-in? a A)
  (-> symbol? type? boolean?)
  (match A
    [(? symbol? b) (eq? a b)]
    [`(→ ,A ,B)    (or (occurs-in? a A) (occurs-in? a B))]))

(define/contract (type-vars-in A)
  (-> type? (listof symbol?))
  (match A
    [(? symbol? a) (list a)]
    [`(→ ,A ,B)    (remove-duplicates (append (type-vars-in A) (type-vars-in B)))]))

(define subst? (hash/c symbol? type? #:immutable #t))

(define/contract (subst-app subst term)
  (-> subst? type? type?)
  (match term
    [(? symbol? a) (hash-ref subst a a)]
    [`(→ ,A ,B)    `(→ ,(subst-app subst A) ,(subst-app subst B))]))

(define/contract (subst-compose s2 s1)
  (-> subst? subst? subst?)
  (let loop ([s1 (hash->list s1)]
             [result s2])
    (match s1
      ['()                      result]
      [(list (cons x A) s1 ...) (loop s1
                                      (hash-set result x (subst-app s2 A)))])))

(module+ test
  (check-equal? (subst-compose (hasheq 'c 'd) (hasheq 'a 'd 'b 'e))
                (hasheq 'a 'd 'b 'e 'c 'd)))

(define equation? (list/c '= type? type?))

(define log (make-parameter #f))

(define/contract (unify equations [subst (hasheq)])
  (->* ((listof equation?)) (subst?) subst?)
  (when (log) (displayln (format "~a  |  ~a" equations subst)))
  (match equations
    ['()                             subst]
    [(list `(= ,A ,B) equations ...)
     (match* (A B)
       [(A A)                   (unify equations subst)]
       [(`(→ ,A ,B) `(→ ,C ,D)) (unify (list* `(= ,A ,C) `(= ,B ,D) equations) subst)]
       [((? symbol? a) A)       (if (occurs-in? a A)
                                    (raise-arguments-error
                                     'unify "type variable not unifiable with type it occurs in"
                                     "type variable" a "type" A)
                                    (let ([s (hasheq a A)])
                                      (unify
                                       (map (match-lambda [`(= ,A ,B)
                                                           `(= ,(subst-app s A) ,(subst-app s B))])
                                            equations)
                                       (subst-compose s subst))))]
       [(A a)                   (unify (cons `(= ,a ,A) equations) subst)])]))

(module+ test
  (check-equal? (unify '((= (→ a b) (→ b a)))) (hasheq 'a 'b))
  (check-equal? (unify '((= (→ (→ a b) (→ b a)) (→ c c)))) (hasheq 'c '(→ a a) 'b 'a))
  (check-equal? (unify '((= (→ (→ a (→ b c)) (→ (→ a b) (→ a c)))
                            (→ (→ d (→ e d)) f))))
                (hasheq 'a 'd
                        'b 'e
                        'c 'd
                        'f '(→ (→ d e) (→ d d))))
  (check-equal? (unify '((= (→ (→ (→ a (→ b c)) (→ a b)) (→ (→ a (→ b c)) (→ a c)))
                           (→ (→ (→ d e) (→ d d)) f))))
                (hasheq 'a 'd
                        'e '(→ d c)
                        'b 'd
                        'f '(→ (→ d (→ d c)) (→ d c)))))

(define alphabet "abcdefghijklmnopqrstuvwxyz")

; 0 -> a, 1 -> b, ..., 25 -> z, 26 -> a1, 27 -> b1, ...
(define/contract (type-var-ref i)
  (-> natural? symbol?)
  (string->symbol
   (let-values ([(q r) (quotient/remainder i (string-length alphabet))])
     (string-append
      (string (string-ref alphabet r))
      (if (zero? q)
          ""
          (number->string q))))))

(define/contract (normalizer vars)
  (-> (listof symbol?) subst?)
  (make-immutable-hasheq
   (map cons vars (map type-var-ref (range (length vars))))))

(define/contract (normalize type)
  (-> type? type?)
  (subst-app (normalizer (type-vars-in type)) type))

(define/contract (freshener vars)
  (-> (listof symbol?) subst?)
  (make-immutable-hasheq
   (map cons vars (map (λ (_) (gensym)) vars))))

(define/contract (freshen type)
  (-> type? type?)
  (subst-app (freshener (type-vars-in type)) type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define term?
  (flat-rec-contract
   term?
   symbol? ; term variable
   (list/c term? term?) ; application
   (list/c 'λ symbol? term?))) ; abstraction

(define cont?
  (flat-rec-contract
   cont?
   '() ; the hole
   (list/c cont? term?)
   (list/c term? cont?)
   (list/c 'λ symbol? cont?)))

(define scope? ; like a continuation, but the hole has to be in a λ-binder
  (flat-rec-contract
   scope?
   (list/c 'λ '() term?)
   (list/c 'λ symbol? scope?)
   (list/c scope? term?)
   (list/c term? scope?)))

(define (-cont-app k t) ; replace the hole in k with t
  (match k
    ['()                  t]
    [(? symbol? x)        x]
    [`(,(? cont? k) ,u)   `(,(-cont-app k t) ,u)]
    [`(,u ,(? cont? k))   `(,u ,(-cont-app k t))]
    [`(λ ,x ,(? cont? k)) `(λ ,x ,(-cont-app k t))]))

; -cont-app is the common implementation of three functions with different contracts
; (we now have scopes as a third possible second argument/result type)

(define/contract (cont-app k t)
  (-> cont? term? term?)
  (-cont-app k t))

(define/contract (cont-app-cont k2 k1)
  (-> cont? cont? cont?)
  (-cont-app k2 k1))

(define/contract (cont-app-scope k s)
  (-> cont? scope? scope?)
  (-cont-app k s))

(define context? (listof (cons/c (or/c symbol? scope?) type?)))

(define/contract (type-of term context [cont '()]) ; non-inferred
  (->* (term? context?) (cont?) type?)
  (match term
    [(? symbol? x) (dict-ref context x
                             (thunk (raise-arguments-error
                              'type-of "free variable type unassigned"
                              "free variable" x)))]
    [`(,t ,u)      (match* ((type-of t context (cont-app-cont cont `(() ,u)))
                            (type-of u context (cont-app-cont cont `(,t ()))))
                     [(`(→ ,A ,B) A) B]
                     [(A B)          (raise-arguments-error
                                      'type-of "ill-typed application"
                                      "function type" A "argument type" B)])]
    [`(λ ,x ,t)    (let* ([A (dict-ref context (cont-app-scope cont `(λ () ,t))
                                       (thunk (raise-arguments-error
                                               'type-of "bound variable type unassigned"
                                               "bound variable" x "scope" t)))]
                          [B (type-of t (dict-set context x A) (cont-app-cont cont `(λ ,x ())))])
                     `(→ ,A ,B))]))

(define/contract (subst-app-context subst context)
  (-> subst? context? context?)
  (dict-map context (λ (x A)
                      (cons x (subst-app subst A)))))

(define/contract (cont-app-context cont context)
  (-> cont? context? context?)
  (dict-map context (λ (k A)
                      (cons (if (scope? k)
                                (cont-app-scope cont k)
                                k)
                            A))))

(define/contract (unify-contexts Γ Δ)
  (-> context? context? context?)
  (let loop ([Γ Γ]
             [result Δ]
             [equations '()])
    (match Γ
      ['()                     (subst-app-context (unify equations) result)]
      [(list (cons x A) Γ ...) (loop Γ (dict-set result x A)
                                     (let ([B (dict-ref Δ x #f)])
                                       (if B
                                           (cons `(= ,A ,B) equations)
                                           equations)))])))

(define/contract (infer-context-for t [cont '()])
  (->* (term?) (cont?) context?)
  (match t
    [(? symbol? x)
     `((,x . ,(gensym)))]
    [`(,t ,u)
     (let ([t-cont (cont-app-cont cont `(() ,u))]
           [u-cont (cont-app-cont cont `(,t ()))])
       (let ([Γ (infer-context-for t t-cont)]
             [Δ (infer-context-for u u-cont)])
         (let ([Θ (unify-contexts Γ Δ)])
           (let ([A (type-of t Θ t-cont)]
                 [B (type-of u Θ u-cont)])
             (subst-app-context (unify `((= ,A (→ ,B ,(gensym))))) Θ)))))]
    [`(λ ,x ,t)
     (let ([x-scope (cont-app-scope cont `(λ () ,t))]
           [t-cont (cont-app-cont cont `(λ ,x ()))])
       (let ([Γ (infer-context-for t t-cont)])
         (let ([A (dict-ref Γ x #f)])
           (dict-set (dict-remove Γ x) x-scope (or A (gensym))))))]))

(define/contract (infer-type-of t)
  (-> term? type?)
  (type-of t (infer-context-for t)))

(define/contract (type-vars-in-context context)
  (-> context? (listof symbol?))
  (remove-duplicates
   (append-map (match-lambda [(cons _ A)
                              (type-vars-in A)])
               context)))

(define/contract (normalize-context context)
  (-> context? context?)
  (subst-app-context (normalizer (type-vars-in-context context)) context))

(module+ test
  (check-equal? (normalize-context (infer-context-for '(f (g x))))
                '((x . a) (g . (→ a b)) (f . (→ b c))))
  (check-equal? (normalize-context (infer-context-for '((f x) (g x))))
                '((x . a) (g . (→ a b)) (f . (→ a (→ b c)))))
  (check-exn exn:fail? (thunk (infer-context-for '(f f))))
  (check-equal? (normalize-context (infer-context-for '(λ x x)))
                '(((λ () x) . a)))
  (check-equal? (normalize-context (infer-context-for '(λ x (λ y x))))
                '(((λ x (λ () x)) . a) ((λ () (λ y x)) . b)))
  (check-equal? (normalize-context (infer-context-for '(λ x (λ y (λ z ((x z) (y z)))))))
                '(((λ x (λ y (λ () ((x z) (y z))))) . a)
                  ((λ x (λ () (λ z ((x z) (y z))))) . (→ a b))
                  ((λ () (λ y (λ z ((x z) (y z))))) . (→ a (→ b c)))))
  (check-exn exn:fail? (thunk (infer-context-for '(λ f (f f))))))

; one way to define abbreviations, which works fine:

(define I '(λ x x))

(module+ test
  (check-equal? (normalize (infer-type-of I)) '(→ a a))
  (check-equal? (normalize (infer-type-of `(,I ,I))) '(→ a a)))

; but what about this?

(define (-let x t u) `((λ ,x ,u) ,t))

(module+ test
  (check-equal? (normalize (infer-type-of (-let 'I '(λ x x) 'I))) '(→ a a))
  (check-exn exn:fail? (thunk (infer-type-of (-let 'I '(λ x x) '(I I))))))

; since each variable has to have a single type within its scope, I as a variable cannot have both
; the types '(→ (→ a a) (→ a a)) and '(→ a a), even though it can as a simple abbreviation