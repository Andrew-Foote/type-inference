#lang racket

; The type inference system we introduced in combinatory-logic.rkt is nice and simple, but it only
; works if the underlying calculus is combinatory logic without any primitive combinators---which is
; a completely useless calculus! (It's Curry-Howard equivalent to a Hilbert system without any
; axioms, only the modus ponens rule of inference.)
;
; A more practical combinatory logic system will have some primitive combinators with pre-defined
; type schemes---for example, S with type scheme '(→ (→ a (→ b c)) (→ (→ a b) (→ a c))) and K with
; type schemes '(→ a (→ b a)). Note that these are type *schemes*, which means different occurrences
; of the primitive combinators can have types that instantiate the scheme in different ways---for
; example '(K K) should have the principal type '(→ c (→ a (→ b a))), from instanting the first K as
; '(→ (→ a (→ b a)) (→ c (→ a (→ b a)))) and the second K as '(→ a (→ b a)).
;
; The way we deal with this is straightforward in principle---when inferring the type of a primitive
; combinator, we simply instantiate its type scheme with fresh type variables. However, the way our
; algorithm works at the moment is that we infer a context, rather than inferring a type directly.
; A context assigns types to each term variable, but with a primitive combinator, there's no
; variable to assign the inferred type to. We can't simply treat the primitive combinator as a
; variable because it will have different types in different places, unlike a variable.
;
; There are different ways to deal with this. The one I prefer is to simply have the context assign
; a type to each occurrence of a primitive combinator, as well as each variable. We can encode
; "occurrences" elegantly as continuations, i.e. "terms with holes"---the hole is where the
; primitive combinator occurs.
;
; Another approach would be to give up on having the context have an independent meaning, and just
; make it a sort of tracking variable we use during the type inference algorithm. This is what we'll
; eventually have to do when we get to λ-calculus, but I'll put it off for now.

(require syntax/parse/define)
(module+ test (require rackunit))

; let's separate out all the type-related stuff, which is mostly unchanged from
; combinatory-logic.rkt, from the term-related stuff

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

; we need these new helper functions to replace all the type variables in a type with fresh ones
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
   symbol? ; term variable or primitive combinator
   (list/c term? term?))) ; application

; hash to distinguish primitive combinators from term variables and assign their type schemes
(define/contract prim-combs (hash/c symbol? type? #:immutable #f) (make-hasheq))

(define cont?
  (flat-rec-contract
   cont?
   '() ; the hole
   (list/c cont? term?)
   (list/c term? cont?)))

(define (-cont-app k t) ; replace the hole in k with t
  (match k
    ['()                t]
    [(? symbol? x)      x]
    [`(,(? cont? k) ,u) `(,(-cont-app k t) ,u)]
    [`(,u ,(? cont? k)) `(,u ,(-cont-app k t))]))

; -cont-app is the common implementation of two functions with different contracts

(define/contract (cont-app k t)
  (-> cont? term? term?)
  (-cont-app k t))

(define/contract (cont-app-cont k2 k1)
  (-> cont? cont? cont?)
  (-cont-app k2 k1))

(define context? (listof (cons/c (or/c symbol? cont?) type?)))

; we have a new cont argument, which contains the continuation of the term
(define/contract (type-of term context [cont '()])
  (->* (term? context?) (cont?) type?)
  (match term
    [(? symbol? x) ( let ([is-prim-comb (hash-ref prim-combs x #f)])
                     (if is-prim-comb
                         (dict-ref context cont
                                   (thunk (raise-arguments-error
                                           'type-of
                                           "primitive combinator occurrence has no assigned type"
                                           "primitive combinator" x
                                           "occurrence" cont)))
                         (dict-ref context x
                                   (thunk (raise-arguments-error
                                           'type-of "variable type unassigned"
                                           "variable" x)))))]
    [`(,t ,u)      (match* ((type-of t context (cont-app-cont cont `(() ,u)))
                            (type-of u context (cont-app-cont cont `(,t ()))))
                     [(`(→ ,A ,B) A) B]
                     [(A B)          (raise-arguments-error
                                      'type-of "ill-typed application"
                                      "function type" A "argument type" B)])]))

(define/contract (subst-app-context subst context)
  (-> subst? context? context?)
  (dict-map context (λ (x A)
                      (cons x (subst-app subst A)))))

(define/contract (cont-app-context cont context)
  (-> cont? context? context?)
  (dict-map context (λ (k A)
                      (cons (if (cont? k)
                                (cont-app-cont cont k)
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
     (list
      (let ([A (hash-ref prim-combs x #f)])
        (if A
            (cons cont (freshen A))
            (cons x (gensym)))))]
    [`(,t ,u)
     (let ([t-cont (cont-app-cont cont `(() ,u))]
           [u-cont (cont-app-cont cont `(,t ()))])
       (let ([Γ (infer-context-for t t-cont)]
             [Δ (infer-context-for u u-cont)])
         (let ([Θ (unify-contexts Γ Δ)])
           (let ([A (type-of t Θ t-cont)]
                 [B (type-of u Θ u-cont)])
             (subst-app-context (unify `((= ,A (→ ,B ,(gensym))))) Θ)))))]))

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
  (check-exn exn:fail? (thunk (infer-context-for '(f f)))))

; the classic S and K combinators
(hash-set! prim-combs 'S '(→ (→ a (→ b c)) (→ (→ a b) (→ a c))))
(hash-set! prim-combs 'K '(→ a (→ b a)))

(module+ test
  (check-equal? (normalize-context (infer-context-for 'K))
                '((() . (→ a (→ b a)))))
  (check-equal? (normalize-context (infer-context-for '(K K)))
                '(((K ()) . (→ a (→ b a)))
                  ((() K) . (→ (→ a (→ b a)) (→ c (→ a (→ b a))))))))

(define I '((S K) K))

(module+ test
  (check-equal? (normalize-context (infer-context-for I))
                '((((S K) ()) . (→ a (→ b a)))
                  (((S ()) K) . (→ a (→ (→ b a) a)))
                  (((() K) K) . (→ (→ a (→ (→ b a) a)) (→ (→ a (→ b a)) (→ a a)))))))

(define B '((S (K S)) K))

(module+ test
  (check-equal? (normalize-context (infer-context-for B))
                '((((S (K S)) ()) . (→ (→ a b) (→ c (→ a b))))
                  (((S (K ())) K) . (→ (→ c (→ a b)) (→ (→ c a) (→ c b))))
                  (((S (() S)) K) . (→ (→ (→ c (→ a b)) (→ (→ c a) (→ c b)))
                                       (→ (→ a b) (→ (→ c (→ a b)) (→ (→ c a) (→ c b))))))
                  (((() (K S)) K) . (→ (→ (→ a b) (→ (→ c (→ a b)) (→ (→ c a) (→ c b))))
                                       (→ (→ (→ a b) (→ c (→ a b)))
                                          (→ (→ a b) (→ (→ c a) (→ c b)))))))))

(define W '((S S) (S K)))

(module+ test
  (check-equal? (normalize (infer-type-of W))
                '(→ (→ a (→ a b)) (→ a b)))
  (check-equal? (normalize (infer-type-of `(,W K)))
                '(→ a a)))

(define C `((S ((S (K ,B)) S)) (K K)))

(module+ test
  (check-equal? (normalize (infer-type-of C))
                '(→ (→ a (→ b c)) (→ b (→ a c)))))

(hash-set! prim-combs 'P '(→ (→ (→ a b) a) a)) ; Peirce's law