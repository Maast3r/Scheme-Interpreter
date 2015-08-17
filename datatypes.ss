
;; Parsed expression datatypes
(define-datatype assignment-expression assignment-expression?
  [assignment-exp
    (var symbol?)
    (val expression?)])

(define-datatype expression expression?
  [var-exp
    (id symbol?)]
    [lit-exp
      (literal (lambda (x) #t))]
  [lambda-exp
    (ids (list-of symbol?))
    (bodies (list-of expression?))]
  [improper-lambda-exp
    (ids (list-of symbol?))
    (id symbol?)
    (bodies (list-of expression?))]
  [lambda-ref-exp
    (ids (list-of 
      (lambda (x)
          (or (symbol? x)
              (and (list? x)
                   (= (length x) 2)
                   (eq? (car x) 'ref)
                   (symbol? (cadr x)))))))
   (bodies (list-of expression?))]
  [or-exp
   (bodies (list-of expression?))]
  [and-exp
   (bodies (list-of expression?))]
  [cond-exp
    (cond-exps (list-of (list-of expression?)))]
  [case-exp
    (key-exp expression?)
    (cond-exps (list-of (list-of expression?)))]
  [case-lambda-exp
    (keys (list-of (list-of symbol?)))
    (bodies (list-of (list-of expression?)))]
  [define-exp
    (id symbol?)
    (body expression?)]
  [for-exp-two
    (last integer?)
    (proc expression?)]
  [for-exp-three
   (first integer?)
   (last integer?)
   (proc expression?)]
  [begin-exp
    (bodies (list-of expression?))]
  [while-exp
    (test-exp expression?)
    (bodies (list-of expression?))]
  [if-exp
    (if-exp expression?)
    (then-exp expression?)
    (else-exp expression?)]
  [no-else-if-exp
    (if-exp expression?)
    (then-exp expression?)]
  [when-exp
    (if-exp expression?)
    (bodies (list-of expression?))]
  [set!-exp
    (id symbol?)
    (val expression?)]
  [set!-car-exp
    (id symbol?)
    (val expression?)]
  [let-exp
    (ids (list-of symbol?))
    (vals (list-of expression?))
    (bodies (list-of expression?))]
  [named-let-exp
    (name symbol?)
    (ids (list-of symbol?))
    (vals (list-of expression?))
    (bodies (list-of expression?))]
  [let*-exp
    (ids (list-of symbol?))
    (vals (list-of expression?))
    (bodies (list-of expression?))]
  [letrec-exp
    (proc-names (list-of symbol?))
    (ids (list-of (list-of symbol?)))
    (bodies (list-of expression?))
    (letrec-bodies (list-of expression?))]
  [app-exp
    (rator expression?)
    (rand (list-of expression?))])
	
; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.
(define-datatype environment environment?
  (empty-env-record)
  [extended-env-record
    (syms (list-of symbol?))
    (vals (list-of scheme-value?))
    (env environment?)]
  [improper-extended-env-record
    (syms (list-of symbol?))
    (sym symbol?)
    (vals (list-of scheme-value?))
    (env environment?)]
  [recursively-extended-env-record
    (proc-names (list-of symbol?))
    (ids (list-of (list-of symbol?)))
    (bodies (list-of expression?))
    (env environment?)])

(define-datatype proc-val proc-val?
  [prim-proc
    (name symbol?)]
  [closure
    (ids (list-of symbol?))
    (bodies (list-of expression?))
    (env environment?)]
  [improper-closure
    (ids (list-of symbol?))
    (id symbol?)
    (bodies (list-of expression?))
    (env environment?)]
  [closure-ref
   (ids (list-of (lambda (x)
                   (or (symbol? x)
                       (and (list? x)
                            (= (length x) 2)
                            (eq? (car x) 'ref)
                            (symbol? (cadr x)))))))
   (bodies (list-of expression?))
   (env environment?)]
  [continuation-proc (k continuation?)])
	 
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype continuation continuation?
  (initial-k)
  (map-k1 (proc-cps scheme-value?)
          (ls scheme-value?)
          (k continuation?))
  (map-k2 (v1 scheme-value?)
          (k continuation?))
  (eval-while-rands-k1 (test-exp expression?)
                       (bodies (list-of expression?))
                       (env environment?)
                       (k continuation?))
  (eval-while-rands-k2 (test-exp expression?)
                       (bodies (list-of expression?))
                       (env environment?)
                       (k continuation?))
  (if-k (then-exp expression?)
        (else-exp expression?)
        (env environment?)
        (k continuation?))
  (no-else-if-k (then-exp expression?)
                (env environment?)
                (k continuation?))
  (when-k (then-exp (list-of expression?))
          (env environment?)
          (k continuation?))
  (define-k (id symbol?)
            (env environment?)
            (k continuation?))
  (set!-k (id symbol?)
          (env environment?)
          (k continuation?))
  (rator-k (rands (list-of expression?))
           (env environment?)
           (k continuation?))
  (rands-k (proc-value scheme-value?)
           (k continuation?))
  (eval-rator-k (rands (list-of expression?))
                (env environment?)
                (k continuation?))
  (eval-rands-k (proc-value scheme-value?)
                (k continuation?))
  (eval-begin-rator-k (rands (list-of expression?))
                      (env environment?)
                      (k continuation?))
  (eval-begin-rands-k (proc-value scheme-value?)
                      (k continuation?))
  (call/cc-cont
      (cont continuation?)))