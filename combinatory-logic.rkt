#lang racket
(require syntax/parse/define)
(module+ test (require rackunit))

(define type?
  (flat-rec-contract
   type?
   symbol? ; type variable
   (list/c '→ type? type?))) ; function type

(define term?
  (flat-rec-contract
   term?
   symbol? ; term variable
   (list/c term? term?))) ; application

; map from term variables to types---terms only have types within a given context!
; (we use an alist rather than a hash just because our type inference algorithm will generate fresh
; tpe variables with gensym, and we want to normalize these variables in a predictable manner when
; presenting the result)
(define context? (listof (cons/c symbol? type?)))

(define/contract (type-of term context) ; non-inferred
  (-> term? context? type?)
  (match term
    [(? symbol? x) (dict-ref context x
                             (thunk (raise-arguments-error
                              'type-of "variable type unassigned"
                              "variable" x)))]
    [`(,t ,u)      (match* ((type-of t context) (type-of u context))
                     [(`(→ ,A ,B) A) B]
                     [(A B)          (raise-arguments-error
                                      'type-of "ill-typed application"
                                      "function type" A "argument type" B)])]))

; the problem of inferring the type of a term can also be understood as that of inferring a suitable
; context assigning a type to each of the term variables in it; the type will then be given by the
; `type-of` function above.

; what makes the context "suitable"? well, we want the types assigned to be as general as possible.
; the precise meaning of "as general as possible" would be: the context is not a substitution
; instance of any other context that would make the term well-typed. so, let's define substitution.

(define subst? (hash/c symbol? type? #:immutable #t))

(define/contract (subst-app subst term)
  (-> subst? type? type?)
  (match term
    [(? symbol? a) (hash-ref subst a a)]
    [`(→ ,A ,B)    `(→ ,(subst-app subst A) ,(subst-app subst B))]))

(define/contract (subst-app-context subst context)
  (-> subst? context? context?)
  (dict-map context (λ (x A)
                      (cons x (subst-app subst A)))))

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

; now let's think about how type inference is going to work.
;
; a term variable on its own can obviously have any type, so the context we should infer should just
; assign a fresh type variable to that term variable
;
; what about an application `(,t ,u)? Well, we can recursively infer a context Γ from t, and a
; context Δ from u. There are then two things we need to do:
;
; - we need to ensure Γ and Δ agree if a term variable is assigned a type by both contexts. if they
;   don't already agree, we can *make* them agree, i.e. "unify" them, by finding a suitable
;   substitution to apply to both contexts. obviously we'll want the substitution to be as general
;   as possible, i.e. if we call the substitution s1, there shouldn't be any other unifying
;   substitution s2 such that s1 = (subst-compose s3 s2) for some third substitution s3. we can then
;   combine the two contexts into one, knowing that wherever there might be a conflict, the types
;   assigned are the same.
;
; - then, we need to ensure that the type assigned to t by the new unified context Θ is of the form
;   `(→ ,A ,B), where A is the type assigned to u by Θ. This is just another unification problem:
;   we can introduce a fresh type variable a, and find the most general substitution that unifies
;   `(→ ,A ,a) and B, where A is the type assigned to t by Θ and B is the type assigned to u by Θ.
;   once we've got this substitution, the inferred type of the application is simply whatever the
;   substitution replaces a with.

; so to develop this type inference algorithm, we first need a unification algorithm. this will take
; a list of type equations, and return the most general substitution that, if applied to the types
; in these equations, will result in each of them being satisfied.

(define equation? (list/c '= type? type?))

; implementation of unification is a substantial topic in its own right, but there's a reasonably
; obvious and straightforward way to do it that will work fine for us. basically you recurse on the
; structure of the type and do the obvious thing

; first, a little helper function---this is used to identify when we can't unify two types, since if
; a type variable occurs in another type but is not equal to it, there is no substitution which can
; make the two types equal (whatever you replace the type variable with, it also gets replaced with
; the same thing in the other type, so the other type is always "bigger")

(define/contract (occurs-in? a A)
  (-> symbol? type? boolean?)
  (match A
    [(? symbol? b) (eq? a b)]
    [`(→ ,A ,B)    (or (occurs-in? a A) (occurs-in? a B))]))

(define log (make-parameter #f))

(define/contract (unify equations [subst (hasheq)])
  (->* ((listof equation?)) (subst?) subst?)
  (when (log) (displayln (format "~a  |  ~a" equations subst))) ; for debugging
  (match equations
    ['()                             (unify equations subst)]
    [(list `(= ,A ,B) equations ...)
     (match* (A B)
       ; if two terms are equal, nothing needs to be done to unify them
       [(A A)                   subst]
       ; to unify two function types, unify the argument types and unify the return types
       [(`(→ ,A ,B) `(→ ,C ,D)) (unify (list* `(= ,A ,C) `(= ,B ,D) equations) subst)]
       ; to unify a type variable with another type:
       ; - first check if it occurs in the other type; given that we already know the types aren't
       ;   equal at this point, if this "occurs check" fails, the unification fails
       ; - otherwise, we know that we need to replace the type variable with the other type as part
       ;   of the substitution to be returned. we should also do this replacement in all the
       ;   remaining equations and in the substitution we have so far, in order to eliminate a from
       ;   the system for good 
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
       ; if the type variable is the second type rather than the first, just flip them around
       [(A a)                   (unify (cons `(= ,a ,A) equations) subst)])]))

(module+ test
  (check-equal? (unify '((= (→ a b) (→ b a)))) (hasheq 'a 'b))
  (check-equal? (unify '((= (→ (→ a b) (→ b a)) (→ c c)))) (hasheq 'c '(→ a a) 'b 'a))
  ; regression tests below! these failed with my original code
  ; this one failed because i forgot to call the loop again in the inductive case of subst-compose
  (check-equal? (unify '((= (→ (→ a (→ b c)) (→ (→ a b) (→ a c)))
                            (→ (→ d (→ e d)) f))) (hasheq))
                (hasheq 'a 'd
                        'b 'e
                        'c 'd
                        'f '(→ (→ d e) (→ d d))))
  ; and similarly this one failed because i forgot to continue the tail recursion in the case where
  ; the two sides of the equation are equal, and instead just returned the current substitution
  (check-equal? (unify '((= (→ (→ (→ a (→ b c)) (→ a b)) (→ (→ a (→ b c)) (→ a c)))
                           (→ (→ (→ d e) (→ d d)) f))))
                (hasheq 'a 'd
                        'e '(→ d c)
                        'b 'd
                        'f '(→ (→ d (→ d c)) (→ d c)))))

(define/contract (unify-contexts Γ Δ) ; helper function to unify contexts
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

(define/contract (infer-context-for t)
  (-> term? context?)
  (match t
    [(? symbol? x)
     `((,x . ,(gensym)))]
    [`(,t ,u)
     (let ([Γ (infer-context-for t)]
           [Δ (infer-context-for u)])
       (let ([Θ (unify-contexts Γ Δ)])
         (let ([A (type-of t Θ)]
               [B (type-of u Θ)])
           (subst-app-context (unify `((= ,A (→ ,B ,(gensym))))) Θ))))]))

(define/contract (infer-type-of t)
  (-> term? type?)
  (type-of t (infer-context-for t)))

; the fact that we introduce fresh type variables using gensym during the type inference process
; means the results don't look very nice, and also, makes testing for expected results harder than
; it needs to be. we solve this by introducing a way to normalize the type variables in a
; type/context

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

(define/contract (type-vars-in A)
  (-> type? (listof symbol?))
  (match A
    [(? symbol? a) (list a)]
    [`(→ ,A ,B)    (remove-duplicates (append (type-vars-in A) (type-vars-in B)))]))

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
