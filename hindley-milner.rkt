#lang racket
(module+ test (require rackunit))

; blah blah blah

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

(define scope?
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

(define/contract (cont-app k t)
  (-> cont? term? term?)
  (-cont-app k t))

(define/contract (cont-app-cont k2 k1)
  (-> cont? cont? cont?)
  (-cont-app k2 k1))

(define/contract (cont-app-scope k s)
  (-> cont? scope? scope?)
  (-cont-app k s))

(define context? (listof (cons/c (or/c symbol? cont? scope?) type?)))

(define/contract (type-of term context [cont '()] [env (set)]) ; non-inferred
  (->* (term? context?) (cont? (set/c symbol?)) type?)
  (match term
    [(? symbol? x)   (if (set-member? env x)
                         (dict-ref context cont
                                   (thunk (raise-arguments-error
                                           'type-of "bound variable occurrence has no assigned type"
                                           "bound variable" x "occurrence" cont)))
                         (dict-ref context x
                             (thunk (raise-arguments-error
                              'type-of "free variable type unassigned"
                              "free variable" x))))]
    [`((λ ,x ,t) ,u) (type-of t context
                              (cont-app-cont cont `((λ ,x ()) ,u))
                              (set-add env x))]
    [`(,t ,u)      (match* ((type-of t context (cont-app-cont cont `(() ,u)) env)
                            (type-of u context (cont-app-cont cont `(,t ())) env))
                     [(`(→ ,A ,B) A) B]
                     [(A B)          (raise-arguments-error
                                      'type-of "ill-typed application"
                                      "function type" A "argument type" B)])]
    [`(λ ,x ,t)    (let* ([A (dict-ref context (cont-app-scope cont `(λ () ,t))
                                       (thunk (raise-arguments-error
                                               'type-of "bound variable type unassigned"
                                               "bound variable" x "scope" t)))]
                          [B (type-of t
                                      (dict-set context x A)
                                      (cont-app-cont cont `(λ ,x ()))
                                      env)])
                     `(→ ,A ,B))]))

(define/contract (subst-app-context subst context)
  (-> subst? context? context?)
  (dict-map context (λ (x A)
                      (cons x (subst-app subst A)))))

(define/contract (cont-app-context cont context)
  (-> cont? context? context?)
  (dict-map context (λ (k A)
                      (cons (cond [(symbol? k) k]
                                  [(scope? k) (cont-app-scope cont k)]
                                  [(cont? k) (cont-app-cont cont k)])
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

(define/contract (infer-context-for t [cont '()] [env (hash)])
  (->* (term?) (cont? (hash/c symbol? type?)) context?)
  (match t
    [(? symbol? x)
     (list
      (let ([A (hash-ref env x #f)])
        (if A
            (cons cont (freshen A)) ; but we don't want to fresh the variables that are free in the context!
                                    ; sot hat's probabyly why we need explict type schemes, so the scheme
                                    ; can include both free and bound vars. we need to find a concrete example
                                    ; this fails on though
            (cons x (gensym)))))]
    [`((λ ,x ,t) ,u)
     (let ([t-cont (cont-app-cont cont `((λ ,x ()) ,u))]
           [u-cont (cont-app-cont cont `((λ ,x ,t) ()))])
       (let ([Γ (infer-context-for u u-cont env)])
         (let ([A (type-of u Γ u-cont (list->set (hash-keys env)))])
           (let ([env (hash-set env x A)])
             (infer-context-for t t-cont env)))))]
    [`(,t ,u)
     (let ([t-cont (cont-app-cont cont `(() ,u))]
           [u-cont (cont-app-cont cont `(,t ()))])
       (let ([Γ (infer-context-for t t-cont env)]
             [Δ (infer-context-for u u-cont env)])
         (let ([Θ (unify-contexts Γ Δ)])
           (let ([A (type-of t Θ t-cont (list->set (hash-keys env)))]
                 [B (type-of u Θ u-cont (list->set (hash-keys env)))])
             (subst-app-context (unify `((= ,A (→ ,B ,(gensym))))) Θ)))))]
    [`(λ ,x ,t)
     (let ([x-cont (cont-app-scope cont `(λ () ,t))]
           [t-cont (cont-app-cont cont `(λ ,x ()))])
       (let ([Γ (infer-context-for t t-cont env)])
         (let ([A (dict-ref Γ x #f)])
           (dict-set (dict-remove Γ x) x-cont (or A (gensym))))))]))

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
  (check-equal? (normalize (infer-type-of (-let 'I '(λ x x) '(I I)))) '(→ a a)))

(module+ test
  (check-equal? (normalize (infer-type-of `(λ x ,(-let 'Kx '(λ y x) '((Kx x) x))))) '(→ a b)))
                
; here, the x has a type a
; Kx is assigned λy.x, which has polymorphic type b -> a --- only the b is polymorphic.
; so Kx should be able to accept any type as an arg, but it shouldn't be able to return any type
; so in (Kx x) x, the inner argument is of type a (fine, b insted as a), the inner return value is
; a (fine), but then we're trying to apply something of type a to something of type a, which we
; can't do
; however, if both of the types in the signature of Kx are polymorphic, we could just instantiate
; Kx with a -> (a -> b)
; (this then leaves the term above with a type of a -> b)



