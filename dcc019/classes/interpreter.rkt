; Daniel Machado Barbosa Delgado 201835013
; Gabriel Bronte Cardoso         201835002
#lang racket

(require dcc019/util/env
         dcc019/util/memory
         dcc019/classes/ast)

(provide value-of-program)

; Representação de procedimentos para escopo estático

; proc-val :: Var x Expr x Env -> Proc
(define (proc-val var exp Δ) ; call by value
  (lambda (val)
    (value-of exp (extend-env var (newref val) Δ))))

; apply-proc :: Proc x ExpVal -> ExpVal  
(define (apply-proc proc val)
  (proc val))

; Criação de ambiente estendido com procedimento recursivo
(define (extend-env-rec name var body env)
  (lambda (svar)
    (if (equal? svar name)
        (newref (proc-val var body (extend-env-rec name var body env)))
        (apply-env env svar))))

; value-of :: Exp -> ExpVal
(define (value-of exp Δ)
  (match exp
    [(ast:int n) n]
    [(ast:dif e1 e2) (- (value-of e1 Δ) (value-of e2 Δ))]
    [(ast:zero? e) (zero? (value-of e Δ))]
    [(ast:if e1 e2 e3) (if (value-of e1 Δ) (value-of e2 Δ) (value-of e3 Δ))]
    [(ast:var v) (deref (apply-env Δ v))]
    [(ast:let (ast:var x) e1 e2) (value-of e2 (extend-env x (newref (value-of e1 Δ)) Δ))]
    [(ast:proc (ast:var v) e) (proc-val v e Δ)]
    [(ast:call e1 e2) (apply-proc (value-of e1 Δ) (value-of e2 Δ))] ; call by value
    [(ast:letrec (ast:var f) (ast:var v) e1 e2) (value-of e2 (extend-env-rec f v e1 Δ))]
    [(ast:begin es) (foldl (lambda (e v) (value-of e Δ)) (value-of (first es) Δ) (rest es))]
    [(ast:assign (ast:var x) e) (begin
                                  (setref! (apply-env Δ x) (value-of e Δ)) ;set the value in the store
                                  42)] ; return the 42 value
    [(ast:self) (apply-env Δ '%self)]
              
    [(ast:send obj-exp method-name rands) 
                          (let ([args (values-of-exps (cadddr exp) Δ)]
                                [obj (value-of (cadr exp) Δ)])
                            (apply-method
                            (find-method (object-class-name obj) (caddr exp))
                            obj
                            args))]
    [(ast:super name args) 
                            (let ([args (values-of-exps (caddr exp) Δ)]
                                [obj (apply-env Δ '%self)])
                            (apply-method
                              (find-method (apply-env Δ '%super) (cadr exp))
                              obj
                              args))]
    [(ast:new class-name args)
                            (let ([args (values-of-exps args Δ)])
                              (let ([this-meth (find-method (object-class-name object) 'initialize)])
                                (apply-method
                                  this-meth
                                  object
                                  args))
                              object)]
    [e (raise-user-error "unimplemented-construction: " e)]
    ))


; Comportamento de uma lista de expressões, podendo ser vazia.
(define values-of-exps
  (lambda (exps env)
    (map
     (lambda (exp) (value-of exp env))
     exps)))

(define (apply-env env var)
  (env var))

; value-of-program :: Program -> ExpVal
(define value-of-program
  (lambda (prog)
    (match-define  
      (ast:prog decls exp) prog)
    (empty-store)
    (initialize-class-env)
    (printf "Classe criada com sucesso \n")
    ;(value-of exp the-class-env)
  ))

; Tipo de dados object, que representa um objeto, que é uma instância de uma classe. Possui nome da classe e campos.
(struct object (class-name fields)) 

; new-object :: ClassName -> Obj
 (define new-object
   (lambda (class-name)
     (object
       class-name
       (map
        (lambda (field-name)
          (newref field-name))
        (ast:decl-fields (lookup-class class-name))))))

; initialize-class-env! :: () -> Unspecified
(define initialize-class-env
  (lambda ()
    (set! the-class-env
      (list
        (list "object" (ast:decl  #f #f  '() '()))))))

; my initialize-class-decl! :: ClassDecl -> Unspecified
(define initialize-class-decl!
  (lambda (class-name super-name field-names m-decls)
    (let ([field-names 
            (append-field-names
              (ast:decl-fields (lookup-class super-name))
              field-names)])
          (add-to-class-env!
            class-name
            (ast:decl class-name super-name field-names 
              (merge-method-envs
                (ast:decl-methods (lookup-class super-name))
                (method-decls->method-env
                m-decls super-name)
              )
            )
          )
    )
  ))
; apply-method :: Method x Obj x ListOf(ExpVal) -> ExpVal
(define (apply-method class-method self args)
  (if (ast:method? class-method)
        (let ([vars (ast:method-params class-method)]
              [body (ast:method-body class-method)]
              [super-name (ast:method-name class-method)])
          (value-of body 
            (extend-env vars (map newref args)
              (extend-env-with-self-and-super
                self super-name
                (extend-env (object-fields self)
                            empty-env)))))(display "Metodo não encontrado\n")))


; lookup-class :: ClassName -> Class
(define lookup-class
  (lambda (name)
    (let ((maybe-pair (assf (lambda (x) (string=? name x)) the-class-env)))
      (if maybe-pair (cadr maybe-pair)
        (display "\nClasse nao encontrada\n"))
  )))

; fresh-identifier           
(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)  
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string identifier)
        "%"
        (number->string sn))))))

; append-field-names :: Listof(FieldName) x Listof(FieldName) -> Listof(FieldName)
(define append-field-names
  (lambda (super-fields new-fields)
    (cond
      ((null? super-fields) new-fields)
      (else
       (cons
        (if (memq (car super-fields) new-fields)
            (fresh-identifier (car super-fields))
            (car super-fields))
        (append-field-names
         (cdr super-fields) new-fields))))))

;the-class :: ClassEnv
(define the-class-env '())

; add-to-class-env! :: ClassName x Class -> Unspecified
(define add-to-class-env!
  (lambda (class-name class)
    (set! the-class-env
          (cons
           (list class-name class)
           the-class-env))))

; find-method :: Sym x Sym -> Method
(define find-method
  (lambda (class-name method_name)
    (let ([this-class (lookup-class class-name)])
      (if (void? this-class) (display "Classe não encontrada\n")
          (let ([m-env (ast:decl-methods this-class)])
             (let ([maybe-pair (assq method_name m-env)])
               (if (pair? maybe-pair) (cadr maybe-pair)
                   (display "Método não encontrado\n"))))))))

; method-decls->method-env :: Listof(MethodDecl) x ClassName -> MethodEnv
(define method-decls->method-env
  (lambda (m-decls super-name)
    (map
      (lambda (m-decl)
        (match-define 
          (ast:method method-name params body) m-decl)
            (list method-name 
              (ast:method super-name params body))) 
     m-decls)))

; merge-method-envs :: MethodEnv x MethodEnv -> MethodEnv
(define merge-method-envs
  (lambda (super-m-env new-m-env)
    (append new-m-env super-m-env)))
; extend-env-with-self-and-super
(define (extend-env-with-self-and-super self super-name saved-env)
  (lambda (svar)
    (case svar
            ((%self) self)
            ((%super) super-name)
            (else (apply-env saved-env svar)))))