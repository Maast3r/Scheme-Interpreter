;cps
(define apply-k
  (lambda (k val)
    (cases continuation k
      [initial-k ()
                val]
      [map-k1 (proc-cps ls k)
              (map-cps proc-cps
                       (cdr ls)
                       (map-k2 val k))]
      [map-k2 (v1 k)
              (apply-k k (cons v1 val))]
      [eval-while-rands-k1 (test-exp bodies env k)
                           (if val
                               (eval-begin-rands bodies env (eval-while-rands-k2 test-exp bodies env k))
                               (apply-k k val))]
      [eval-while-rands-k2 (test-exp bodies env k)
                           (eval-while-rands test-exp bodies env k)]
      [if-k (then-exp else-exp env k)
            (if val
                (eval-exp then-exp env k)
                (eval-exp else-exp env k))]
      [no-else-if-k (then-exp env k)
                    (if val
                        (eval-exp then-exp env k)
                        (apply-k k val))]
      [when-k (then-exp env k)
                    (if val
                        (eval-begin-rands then-exp env k)
                        (apply-k k val))]
      [define-k (id env k)
        (begin (set! init-env (extend-env (list id) (list val) init-env)) (apply-k k val))]
      [set!-k (id env k)
              (begin (set-ref! (apply-env-ref env
                                       id
                                       (lambda (x) x)
                                       (lambda ()
                                         (apply-env-ref init-env
                                                        id
                                                        (lambda (x) x)
                                                        (lambda () (eopl:error 'env "Variable not found in environment: " id)))))
                        val) (apply-k k val))]
      [rator-k (rands env k)
               (eval-rands rands
                           env
                           (rands-k val k))]
      [rands-k (proc-value k)
               (apply-proc proc-value val k)]
      [eval-rator-k (rands env k)
                    (eval-rands (cdr rands)
                                env
                                (eval-rands-k val k))]
      [eval-rands-k (proc-value k)
                    (apply-k k (cons proc-value val))]
      [eval-begin-rator-k (rands env k)
                          (eval-begin-rands (cdr rands)
                                            env
                                            (eval-begin-rands-k val k))]
      [eval-begin-rands-k (proc-value k)
                    (apply-k k val)]
      [call/cc-cont (k)
        (cases proc val
          [closure (ids bodies env)
            (eval-expression (begin-exp bodies) k
                             (extend-env (list (acontinuation k)) env))]
          [else (eopl:error 'call/cc "Invalid receiver: ~s" val)])])))

; syntatic expansion
(define syntax-expand
  (lambda (parsed-exp)
    (cases expression parsed-exp
      [lambda-exp (ids bodies)
        (lambda-exp ids (map syntax-expand bodies))]
      [lambda-ref-exp (ids bodies)
        (lambda-ref-exp ids (map syntax-expand bodies))]
      [let-exp (ids vals bodies)
        (app-exp (lambda-exp ids (map syntax-expand bodies)) (map syntax-expand vals))]
      [let*-exp (ids vals bodies)
        (syntax-expand 
          (let loop ([ids ids] [vals (map syntax-expand vals)])
            (if (null? (cdr ids))
              (let-exp ids vals (map syntax-expand bodies))
              (let-exp (list (car ids)) (list (car vals)) (list (loop (cdr ids) (cdr vals)))))))]
      [letrec-exp (proc-names ids bodies letrec-bodies)
        (letrec-exp proc-names ids (map syntax-expand bodies) (map syntax-expand letrec-bodies))]
      [named-let-exp (name ids vals bodies)
        (syntax-expand (app-exp (letrec-exp (list name) (list ids) (list (begin-exp bodies)) (list (var-exp name))) vals))]
      [cond-exp (cond-exps)
        (let loop ([expanded-conds (map (lambda (x) (map syntax-expand x)) cond-exps)])
          (if (null? (cdr expanded-conds))
            (cadar expanded-conds)
            (if-exp (caar expanded-conds) (cadar expanded-conds) (loop (cdr expanded-conds)))))]
      [and-exp (bodies)
        (syntax-expand  
          (let loop ([bodies bodies])
            (if (null? bodies)
              (lit-exp #t)
              (if (null? (cdr bodies))
                (car bodies)
                (if-exp (car bodies) 
                  (loop (cdr bodies))
                  (lit-exp #f))))))]
      [or-exp (bodies)
        (syntax-expand  
          (let loop ([bodies bodies])
            (if (null? bodies)
              (lit-exp #f)
              (if (null? (cdr bodies))
                (car bodies)
                (syntax-expand 
                  (let-exp (list 'temp) (list (car bodies)) (list (if-exp (var-exp 'temp) (var-exp 'temp) (loop (cdr bodies))))))))))]
      [case-exp (key-exp cond-exps)
        (let ([key (syntax-expand key-exp)])
          (let loop ([cond-exps cond-exps])
            (if (null? (cdr cond-exps))
              (syntax-expand (cadar cond-exps))
              (if-exp (app-exp (var-exp 'member) (list key (caar cond-exps)))
                (syntax-expand (cadar cond-exps))
                (loop (cdr cond-exps))))))]
      [case-lambda-exp (key-exp cond-exps)
        (let ([key (syntax-expand key-exp)])
          (let loop ([cond-exps cond-exps])
            (if (null? (cdr cond-exps))
              (syntax-expand (cadar cond-exps))
              (if-exp (app-exp (var-exp 'equal?) (var-exp 'length) key (var-exp 'length) (caar cond-exps))
                (syntax-expand (cadar cond-exps))
                (loop (cdr cond-exps))))))]
      [set!-exp (id body)
        (set!-exp id (syntax-expand body))]
      [define-exp (id body)
        (define-exp id (syntax-expand body))]
      [begin-exp (bodies)
        (begin-exp (map syntax-expand bodies))]
      [if-exp (condition then otherwise)
        (if-exp (syntax-expand condition) (syntax-expand then) (syntax-expand otherwise))]
      [no-else-if-exp (condition then)
        (no-else-if-exp (syntax-expand condition) (syntax-expand then))]
      [while-exp (test-exp bodies)
        (while-exp (syntax-expand test-exp) (map syntax-expand bodies))]
      [app-exp (rator rands)
        (app-exp (syntax-expand rator) (map syntax-expand rands))]
      [else parsed-exp])))

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env (initial-k))))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env k)
    (cases expression exp
      [lit-exp (datum) (apply-k k datum)]
      [var-exp (id) (apply-k k (apply-env env id 
        (lambda (x) x) 
        (lambda ()
          (apply-env init-env
                     id
                     (lambda (x) x)
                     (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
                                            "variable not found in environment: ~s"
                                            id))))))]
      [if-exp (if-exp then-exp else-exp)
        (eval-exp if-exp env (if-k then-exp else-exp env k))]
      [no-else-if-exp (if-exp then-exp)
        (eval-exp if-exp env (no-else-if-k then-exp env k))]
      [when-exp (if-exp bodies)
        (eval-exp if-exp env (when-k bodies env k))]
      [lambda-exp (ids bodies)
        (apply-k k (closure ids bodies env))]
      [lambda-ref-exp (ids bodies)
        (apply-k k (closure-ref ids bodies env))]
      [improper-lambda-exp (ids id bodies)
        (apply-k k (improper-closure ids id bodies env))]
      [begin-exp (bodies)
        (eval-begin-rands bodies env k)]
      [while-exp (test-exp bodies)
        (eval-while-rands test-exp bodies env k)]
      [letrec-exp (proc-names idss bodies letrec-bodies)
        (eval-begin-rands letrec-bodies (extend-env-recursively proc-names idss bodies env) k)]
      [define-exp (id body)
        (eval-exp body env (define-k id env k))]
      [set!-exp (id body)
        (eval-exp body env (set!-k id env k))]
            [app-exp (rator rands)
       (eval-exp rator
                 env
                 (rator-k rands env k))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands 
  (lambda (rands env k)
    (if (null? rands) 
        (apply-k k '())
        (eval-exp (car rands)
                  env
                  (eval-rator-k rands env k)))))

(define eval-begin-rands
  (lambda (rands env k)
    (cond
      [(null? rands) (apply-k k '())]
      [(null? (cdr rands)) (eval-exp (car rands) env k)]
      [else (eval-exp (car rands) env (eval-begin-rator-k rands env k))])))

(define eval-for-rands
  (lambda (first last body env)
    (if (< first last)
      (begin
        (eval-exp body env)
        (eval-for-rands (+ 1 first) last body env)))))

(define eval-while-rands
  (lambda (test-exp bodies env k)
    (eval-exp test-exp env (eval-while-rands-k1 test-exp bodies env k))))

(define eval-bodies 
  (lambda (bodies env)
    (if (null? (cdr bodies))
      (eval-exp (car bodies) env)
      (begin
        (eval-exp (car bodies) env)
        (eval-bodies (cdr bodies) env)))))

(define eval-closure-ref-rands
  (lambda (ids rands closure-env env)
    (if (null? ids)
        closure-env
        (if (symbol? (car ids))
            (eval-closure-ref-rands (cdr ids)
              (cdr rands)
              (extend-env (list (car ids)) (list (eval-exp (car rands) env)) closure-env) env)
            (eval-closure-ref-rands (cdr ids)
              (cdr rands)
              (extend-env-ref (list (cadr (car ids)))
                (list (apply-env-ref env
                       (cadr (car rands))
                       (lambda (x) x)
                       (lambda ()
                         (apply-env-ref init-env
                                        (cadr (car rands))
                                        (lambda (x) x)
                                        (lambda ()
                                          (eopl:error 'apply-env-ref
                                                      "variable not found in environment: ~s"
                                                      (cadr (car rands))))))))
                              closure-env)
              env)))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args k)
    (cases proc-val proc-value
      [prim-proc (op)
        (apply-prim-proc op args k)]
			; You will add other cases
      [closure (ids bodies env)
        (let ([new-env (extend-env ids args env)])
          (eval-begin-rands bodies new-env k))]
      [improper-closure (ids id bodies env)
        (let ([new-env (improper-extend-env ids id args env)])
          (eval-begin-rands bodies new-env k))]
      [continuation-proc (k)
        (apply-k k (car args))]
      [else 
        (error 'apply-proc "Attempt to apply bad procedure: ~s" proc-value)])))

(define *prim-proc-names* '(+ - * / < = <= >= > add1 append apply assq atom? caaar caadr caar cadar caddr cadr car cdaar cdadr cdar cddar cdddr cddr cdr call/cc cons display eq? eqv? equal? even? exit-list length list list->vector list? list-tail length make-vector map member newline not null? number? pair? procedure? quotient set-cdr! set-car! sub1 symbol? vector vector->list vector-ref vector-set! vector? zero?))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

(define reset-global-env
  (lambda ()
    (set! 
      init-env 
      (extend-env
        *prim-proc-names*
        (map prim-proc
             *prim-proc-names*)
        (empty-env)))))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define map-cps
  (lambda (proc-cps ls k)
    (if (null? ls)
        (apply-k k ls)
        (proc-cps (car ls) (map-k1 proc-cps ls k)))))

(define apply-prim-proc
  (lambda (prim-proc args k)
    (case prim-proc
      [(+) (apply-k k (apply + args))]
      [(-) (apply-k k (apply - args))]
      [(*) (apply-k k (apply * args))]
      [(/) (apply-k k (apply / args))]
      [(<) (apply-k k (apply < args))]
      [(=) (apply-k k (apply = args))]
      [(<=) (apply-k k (apply <= args))]
      [(>=) (apply-k k (apply >= args))]
      [(>) (apply-k k (apply > args))]
      [(add1) (apply-k k (apply add1 args))]
      [(assq) (apply-k k (apply assq args))]
      [(append) (apply-k k (apply append args))]
      [(apply) (apply-proc (car args) (cadr args) k)]
      [(atom?) (apply-k k (apply atom? args))]
      [(caaar) (apply-k k (apply caaar args))]
      [(caadr) (apply-k k (apply caadr args))]
      [(caar) (apply-k k (apply caar args))]
      [(cadar) (apply-k k (apply cadar args))]
      [(caddr) (apply-k k (apply caddr args))]
      [(cadr) (apply-k k (apply cadr args))]
      [(car) (apply-k k (apply car args))]
      [(cdaar) (apply-k k (apply cdaar args))]
      [(cdadr) (apply-k k (apply cdadr args))]
      [(cdar) (apply-k k (apply cdar args))]
      [(cddar) (apply-k k (apply cddar args))]
      [(cdddr) (apply-k k (apply cdddr args))]
      [(cddr) (apply-k k (apply cddr args))]
      [(cdr) (apply-k k (apply cdr args))]
      [(call/cc) (apply-proc (car args) (list (continuation-proc k)) k)]
      [(cons) (apply-k k (apply cons args))]
      [(display) (apply-k k (apply display args))]
      [(eq?) (apply-k k (apply eq? args))]
      [(eqv?) (apply-k k (apply eqv? args))]
      [(equal?) (apply-k k (apply equal? args))]
      [(even?) (apply-k k (apply even? args))]
      [(exit-list) args]
      [(length) (apply-k k (apply length args))]
      [(list) (apply-k k (apply list args))]
      [(list->vector) (apply-k k (apply list->vector args))]
      [(list?) (apply-k k (apply list? args))]
      [(list-tail) (apply-k k (apply list-tail args))]
      [(length) (apply-k k (apply length args))]
      [(make-vector) (apply-k k (apply make-vector args))]
      [(map) (map-cps (lambda (x k) (apply-proc (car args) (list x) k)) (cadr args) k)]
      [(member) (apply-k k (member (1st args) (2nd args)))]
      [(newline) (apply-k k (apply newline args))]
      [(not) (apply-k k (apply not args))]
      [(null?) (apply-k k (apply null? args))]
      [(number?) (apply-k k (apply number? args))]
      [(pair?) (apply-k k (apply pair? args))]
      [(procedure?) (apply-k k (proc-val? (car args)))]
      [(quotient) (apply-k k (apply quotient args))]
      [(set-cdr!) (apply-k k (apply set-cdr! args))]
      [(set-car!) (apply-k k (apply set-car! args))]
      [(sub1) (apply-k k (apply sub1 args))]
      [(symbol?) (apply-k k (apply symbol? args))]
      [(vector) (apply-k k (apply vector args))]
      [(vector->list) (apply-k k (apply vector->list args))]
      [(vector-ref) (apply-k k (apply vector-ref args))]
      [(vector-set!) (apply-k k (apply vector-set! args))]
      [(vector?) (apply-k k (apply vector? args))]
      [(zero?) (apply-k k (apply zero? args))]
      [else (eopl:error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))


(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))