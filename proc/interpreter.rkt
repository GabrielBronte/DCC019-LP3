#lang racket

(require dcc019/util/env
         dcc019/proc/ast)

(provide value-of)

; Representação de procedimentos para escopo estático

#|   
var =>  Variável
body => Expr
env => Environment de execução (escopo estático)
val => ExpVal

(apply-proc (procedure var body env) val
  (value-of body (extend-env var val env))
|#

; proc-val :: Var x Expr x Env -> Proc
(define (proc-val var exp Δ)
  (lambda (val)
    (value-of exp (extend-env var val Δ))))

; apply-proc :: Proc x ExpVal -> ExpVal  
(define (apply-proc proc val)
  (proc val))

; value-of :: Exp -> ExpVal
(define (value-of exp Δ)
  (match exp
    [(ast:int n) n]
    [(ast:dif e1 e2) (- (value-of e1 Δ) (value-of e2 Δ))]
    [(ast:zero? e) (zero? (value-of e Δ))]
    [(ast:if e1 e2 e3) (if (value-of e1 Δ) (value-of e2 Δ) (value-of e3 Δ))]
    [(ast:var v) (apply-env Δ v)]
    [(ast:let (ast:var v) e1 e2) (value-of e2 (extend-env v (value-of e1 Δ) Δ))]
    [(ast:proc (ast:var v) e) (proc-val v e Δ)]
    [(ast:call e1 e2) (apply-proc (value-of e1 Δ) (value-of e2 Δ))]
    [e (raise-user-error "unimplemented-construction: " e)]
    )
  )
