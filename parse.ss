; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
;(define 1st car)
;(define 2nd cadr)
;(define 3rd caddr)
;
;(define parse-exp
;  (lambda (datum)
;    (cond
;     [(symbol? datum) (var-exp datum)]
;     [(number? datum) (lit-exp datum)]
;     [(pair? datum)
;      (cond
;       
;       [else (app-exp (parse-exp (1st datum))
;		      (map parse-exp (cdr datum)))])]
;     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))
(define throw-error
  (lambda (datum)
    (eopl:error 'parse-exp
                "Invalid concrete syntax ~s" datum)))

(define proper-list?
  (lambda (l)
    (cond [(null? l) #t]
          [(pair? l) (proper-list? (cdr l))]
          [else #f])))

(define andmap
  (lambda (pred? l)
    (cond [(null? l) #t]
          [else (and (pred? (car l))
                     (andmap pred? (cdr l)))])))

(define set?
  (lambda (l)
    (cond [(null? l) #t]
          [(member (car l) (cdr l)) #f]
          [else (set? (cdr l))])))

(define parse-exp-helper
  (lambda (l x y datum)
    (if (and (>= l x)
             (<= l y))
        #t
        (throw-error datum))))

(define improper->proper
  (lambda (improper)
    (cond [(null? improper) '()]
          [(pair? improper)  (cons  (car improper)
                                    (improper->proper (cdr improper)))]
          [else (list improper)])))

(define not-last
  (lambda (l)
    (if (null? (cdr l))
        '()
        (cons (car l)
              (not-last (cdr l))))))

(define last
  (lambda (l)
    (if (null? (cdr l))
        (car l)
        (last (cdr l)))))

(define parse-exp
  (lambda (datum)
    (cond [(null? datum) (lit-exp datum)]
          [(symbol? datum) (var-exp datum)]
          [(string? datum) (lit-exp datum)]
          [(number? datum) (lit-exp datum)]
          [(vector? datum) (lit-exp datum)]
          [(boolean? datum) (lit-exp datum)]
          [(not (proper-list? datum)) (throw-error datum)]
          [(pair? datum)
           (let ([first (car datum)]
                 [l (length datum)])
             (cond  [(equal? first 'begin) 
                     (begin-exp (map (lambda (x) (parse-exp x)) (cdr datum)))]
                    [(eqv? first 'when)
                      (cond
                        [(null? (cdr datum))
                          (eopl:error 'parse-exp "Invalid if syntax ~s\n~s" datum "No condition or results")]
                        [(null? (cddr datum))
                          (eopl:error 'parse-exp "Invalid if syntax ~s\n~s" datum "No  result")]
                        [(and (not (null? (cdddr datum))) (not (null? (cddddr datum))))
                          (eopl:error 'parse-exp "Invalid if syntax ~s\n~s" datum "Too many arguments")]
                        [else
                          ;(display (map parse-exp (cddr datum)))
                                          (when-exp (parse-exp (cadr datum))
                                                (map parse-exp (cddr datum)))])]
                    [(equal? first 'or) 
                     (or-exp (map parse-exp (cdr datum)))]
                    [(equal? first 'and)
                     (and-exp (map parse-exp (cdr datum)))]
                    [(equal? first 'cond)
                     (cond-exp (map (lambda (x) (list (parse-exp (car x)) (parse-exp (cadr x)))) (cdr datum)))]
                    [(equal? first 'while)
                     (while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))]
                    [(equal? first 'case)
                     (case-exp (parse-exp (cadr datum)) (map (lambda (x) (list (lit-exp (car x)) (parse-exp (cadr x)))) (cddr datum)))]
                    [(equal? first 'lambda)
                     (cond [(and (> l 2)
                                 (symbol? (cadr datum))) (improper-lambda-exp '()
                                                                              (cadr datum)
                                                                              (map parse-exp (cddr datum)))]
                           [(and (> l 2)
                                 (proper-list? (cadr datum))
                                 (andmap symbol? (cadr datum))
                                 (set? (cadr datum))) (lambda-exp (cadr datum)
                                                                  (map parse-exp (cddr datum)))]
                           [(let ([args (improper->proper (cadr datum))])
                              (and (> l 2)
                                   (andmap symbol? args)
                                   (set? args))) (let ([args (improper->proper (cadr datum))])
                                                   (improper-lambda-exp (not-last args)
                                                                        (last args)
                                                                        (map parse-exp (cddr datum))))]
                           [(and (> l 2)
                                 (proper-list? (cadr datum))
                                 (andmap (lambda (x)
                                           (or (symbol? x)
                                               (and (list? x)
                                                    (= (length x) 2)
                                                    (eq? (car x) 'ref)
                                                    (symbol? (cadr x)))))
                                         (cadr datum))
                                 (set? (cadr datum))) (lambda-ref-exp (cadr datum)
                                                                      (map parse-exp (cddr datum)))]
                           [else (throw-error datum)])]
                    [(equal? first 'if)
                     (begin (parse-exp-helper l 3 4 datum)
                            (if (null? (cdddr datum))
                                (no-else-if-exp (parse-exp (cadr datum))
                                                (parse-exp (caddr datum)))
                                (if-exp (parse-exp (cadr datum))
                                        (parse-exp (caddr datum))
                                        (parse-exp (cadddr datum)))))]
                    [(equal? first 'let)
                    (cond [(and (> l 2)
                                (proper-list? (cadr datum))
                                (andmap proper-list? (cadr datum))
                                (andmap (lambda (x) (= (length x) 2))
                                        (cadr datum))
                                (andmap (lambda (x) (symbol? (car x)))
                                        (cadr datum))
                                (set? (map car (cadr datum))))
                           (let-exp (map car (cadr datum))
                                    (map parse-exp (map cadr (cadr datum)))
                                    (map parse-exp (cddr datum)))]
                          [(and (> l 2)
                                (symbol? (cadr datum))
                                (proper-list? (caddr datum))
                                (andmap proper-list? (caddr datum))
                                (andmap (lambda (x) (= (length x) 2))
                                        (caddr datum))
                                (andmap (lambda (x) (symbol? (car x)))
                                        (caddr datum))
                                (set? (map car (caddr datum))))
                           (named-let-exp (cadr datum)
                                          (map car (caddr datum))
                                          (map parse-exp (map cadr (caddr datum)))
                                          (map parse-exp (cdddr datum)))]
                          [else (throw-error datum)])]
                   [(equal? first 'let*)
                    (cond [(and (> l 2)
                                (proper-list? (cadr datum))
                                (andmap proper-list? (cadr datum))
                                (andmap (lambda (x) (= (length x) 2))
                                        (cadr datum))
                                (andmap (lambda (x) (symbol? (car x)))
                                        (cadr datum))
                                (set? (map car (cadr datum))))
                           (let*-exp (map car (cadr datum))
                                     (map parse-exp (map cadr (cadr datum)))
                                     (map parse-exp (cddr datum)))]
                          [else (throw-error datum)])]
                   [(equal? first 'letrec)
                    (cond [(and (> l 2)
                                (proper-list? (cadr datum))
                                (andmap proper-list? (cadr datum))
                                (andmap (lambda (x) (= (length x) 2))
                                        (cadr datum))
                                (andmap (lambda (x) (symbol? (car x)))
                                        (cadr datum))
                                (set? (map car (cadr datum))))
                           (letrec-exp (map car (cadr datum))
                                       (map cadadr (cadr datum))
                                       (map parse-exp (map car (map cddadr (cadr datum))))
                                       (map parse-exp (cddr datum)))]
                          [else (throw-error datum)])]
                   [(equal? first 'set!)
                    (begin (parse-exp-helper l 3 3 datum)
                           (set!-exp (cadr datum)
                                     (parse-exp (caddr datum))))]
                   [(equal? first 'define)
                    (begin (parse-exp-helper l 3 3 datum)
                           (define-exp (cadr datum)
                             (parse-exp (caddr datum))))]
                   [(equal? first 'quote)
                    (begin (parse-exp-helper l 2 2 datum)
                           (lit-exp (cadr datum)))]
                   [else (app-exp
                          (parse-exp first)
                          (map parse-exp (cdr datum)))]))]
          [else (throw-error datum)])))