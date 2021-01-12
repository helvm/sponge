#lang racket

(define (fmt &rest xs)
 (apply #'format nil xs))

(define (out-repeat port n s)
  (dotimes (i n)
    (format port s)))

;;

(defmacro rec (name args . body)
 `(labels ((,name ,args ,@body))
    (,name ,@args)))

(defmacro => (x . forms)
 (rec aux (x forms)
    (if (null forms)
      x
      (aux (append (car forms) (list x))
           (cdr forms)))))

;;; numbers in befunge
;;; (in decimal fashion)

(define (bf-num n)
 (cond
  ((< n 0) (fmt "0~A-" (bf-num (- n))))
  ((<= n 9) (fmt "~A" n))
  (t (fmt "~Aa*~A+" (bf-num (floor n 10))
                    (mod n 10)))))

;;; implemented Lisp:
;;;
;;; - integers (limited by the befunge implementation)
;;; - booleans: true, false (not #t and #f)
;;; - lambda, if, set!, begin
;;; - functions with variadic arguments are not supported
;;;
;;; error numbers:
;;;
;;; - 7: type error (primitive function applied to
;;;                  wrong object)
;;;
;;; format of the befunge output:
;;;
;;;   main program       (row 0)
;;;   memory ("heap")    (row 1)
;;;   error handling     (row 2)
;;;   routine handlers   (from row 3 on)
;;;
;;; - use "absolute delta" ("x") to simulate goto
;;; - the main program jumps to the appropiate routine handler,
;;;   then the routine handler jumps back to the corresponding
;;;   code in the main program
;;; - do so to avoid backpatching
;;; - keep the first 32 cells of the memory as registers
;;;     0 - pointer to next free space in the heap
;;;     1 - auxiliary register
;;;     2 - pointer to current environment
;;;     3 - yet another auxiliary register
;;; - allocate objects in our "heap"
;;; - no garbage collection -- should use Cheney on the MTA?
;;; - only compile calls and convert to CPS (no need to
;;;   take care of returns)
;;;

(defvar *heap-offset*             1)
(defvar *routine-offset*          2)
(defvar *error-handler-position*  '(2 . 0))

(defstruct compiler-state
  ;; program keeps the befunge code in a list of pairs (position . string)
  (program
   `( ((,*heap-offset* . 0) .
       ,(string (code-char 33))) ; next free space in the heap
      (,*error-handler-position* . "<@,a.,k9a\"Error #\"a0")
    ))
  ;; pos tracks the last occupied cell in the main program
  (pos '(0 . 0)))

(define (produce str cs)
  (make-compiler-state
    :program (acons (compiler-state-pos cs) str
                    (compiler-state-program cs))
    :pos (cons
           (car (compiler-state-pos cs))
           (+ (length str) (cdr (compiler-state-pos cs))))))

(define (bf-jump-driver y0 x0 y1 x1)
  (fmt "<x~A~A"
       (reverse (bf-num (- y1 y0)))
       (reverse (bf-num (- x1 x0 1)))))

(define (pos-for-id num)
 (cons (+ num *routine-offset*) 0))

(define (define-function num cs)
 (let ((p (pos-for-id num))
       (cp (compiler-state-pos cs)))
  (make-compiler-state
    :program (acons p
               (bf-jump-driver
                 (car p) (cdr p) (car cp) (cdr cp))
               (compiler-state-program cs))
    :pos cp)))

;;; =~ malloc
;;; leaves the address of the allocated vector in the stack
(define (bf-allocate size cs)
 ; increase register 0 by size
 (produce
   (fmt "0~Ag:~A+0~Ap"
        (bf-num *heap-offset*)
        (bf-num size)
        (bf-num *heap-offset*))
   cs))

;;; allocates an n-cell vector in the heap
;;; and fills it with the n top elements in
;;; the stack. (the top of the stack goes last).
;;; leaves the address in the stack
(define (bf-create-vector n cs)
 (=> cs
  ; allocate memory
  (bf-allocate n)
  ; save address in register 1
  (produce (fmt "1~Ap" *heap-offset*))
  ; set all values
  (each=>
    #'(lambda (i cs)
        (produce
          (fmt "1~Ag~A+~Ap"
                 (bf-num *heap-offset*)
                 (bf-num i)
                 (bf-num *heap-offset*))
          cs))
    (loop for i from (- n 1) downto 0
       collecting i))
  ; restore address from register 1
  (produce (fmt "1~Ag" *heap-offset*))))

;;; pushes i-th element of the vector at the top of the stack
(define (bf-vector-ref i cs)
  ; dereference memory
  (produce (fmt "~A+~Ag" (bf-num i) (bf-num *heap-offset*))
           cs))

;;; sets the i-th element of the vector to the value
;;; at the top of the stack
(define (bf-vector-set i cs)
  (produce (fmt "\\~A+~Ap" (bf-num i) (bf-num *heap-offset*))
           cs))

(define (bf-jump y0 x0)
  (fmt ">#x;# \\-~A0-~A+~A;# <"
       (reverse (bf-num (+ x0 2)))
       (reverse (bf-num y0))
       (reverse (bf-num *routine-offset*))))

;;; compiles the function and arguments, and the
;;; necessary code for the invocation
(define (call-function func args n-args cs)
  (=> cs
      (comp2-args args)            ; compile the arguments
      (comp2-expr func)            ; compile the function
      (invoke-function n-args)))

(define (invoke-function n-args cs)
  (let ((cs
    (=> cs
       (produce ":")
       (produce (fmt "3~Ap" *heap-offset*)) ; save the function
       (bf-vector-ref 2)                    ; take the function env.
       (bf-create-vector (1+ n-args))       ; arguments + pointer to parent env
       (produce (fmt "2~Ap" *heap-offset*)) ; set it as the current env
       (produce (fmt "3~Ag" *heap-offset*)) ; restore the function
       (bf-vector-ref 1)                    ; take the function-code
      )))
    (let ((cp (compiler-state-pos cs)))
      ; call it
      (produce (bf-jump (car cp) (cdr cp)) cs))))

;;; constructors for Scheme objects

(define (create-function num cs)
 (=> cs
   (produce (bf-num *function-tag*))    ; TAG
   (produce (bf-num num))               ; function-code
   (produce (fmt "2~Ag" *heap-offset*)) ; current env
   (bf-create-vector 3)))

(define (push-number n cs)
 (=> cs
   (produce (bf-num *integer-tag*))     ; TAG
   (produce (bf-num n))                 ; value
   (bf-create-vector 2)))

(define (make-number cs)
 (=> cs
   (produce (bf-num *integer-tag*))     ; TAG
   (produce "\\")                       ; take value
   (bf-create-vector 2)))

(define (push-unspecified cs)
 (=> cs
   (produce (bf-num *unspecified-tag*)) ; TAG
   (bf-create-vector 1)))

(define (push-boolean v cs)
 (=> cs
   (produce (bf-num *boolean-tag*))     ; TAG
   (produce (bf-num (if v 1 0)))
   (bf-create-vector 2)))

;;; produce code to reference / set the variable
;;; bound by `name' in the given environment.
;;; the current environment is at register 2

(define (local-ref-base-offset env name cs)
  (if (null env)
    (assert (not "unbound variable"))
    (let ((p (position name (car env))))
     (if p
       (bf-vector-ref p cs)
       (let ((l (length (car env))))
         (=> cs
           (bf-vector-ref l) ; pointer to next
           (local-ref-base-offset (cdr env) name)))))))

(define (local-ref env name cs)
 (=> cs
   (produce (fmt "2~Ag" *heap-offset*)) ; current env
   (local-ref-base-offset env name)))

(define (local-set-base-offset env name value cs)
  (if (null env)
    (assert (not "unbound variable"))
    (let ((p (position name (car env))))
     (if p
       (=> cs
         (comp2-expr value)
         (bf-vector-set p))
       (let ((l (length (car env))))
         (=> cs
           (bf-vector-ref l) ; pointer to next
           (local-set-base-offset (cdr env) name value)))))))

(define (local-set env name value cs)
 (=> cs
   (produce (fmt "2~Ag" *heap-offset*)) ; current env
   (local-set-base-offset env name value)
   (push-unspecified)))

;; Output
;; - emit befunge code to a file, from a list representation

(define (pos-< x y)
  (or (< (car x) (car y))
      (and (= (car x) (car y))
           (< (cdr x) (cdr y)))))

(define (print-program cs &optional (port t))
 (let ((instructions
         (sort
            (compiler-state-program cs)
            #'(lambda (x y) (pos-< (car x) (car y)))))
       (last-row 0)
       (last-col 0)
       (last-size 0))

  (dolist (i instructions)
   (let ((row (caar i))
         (col (cdar i))
         (instr (cdr i)))
    (out-repeat port (- row last-row) "~%")
    (out-repeat port (- col last-col last-size) " ")
    (format port "~A" instr)
    (setf last-size (if (= last-row row)
                      (length instr)
                      0))
    (setf last-row row)
    (setf last-col col)))))

;;;; Compiler

(defvar *toplevel-forms* '())

(let ((c 0))
 (define make-id ()
  (incf c)))

(defvar *builtins* '())

(defvar *function-tag*     0)
(defvar *cons-tag*         1)
(defvar *integer-tag*      2)
(defvar *unspecified-tag*  3)
(defvar *boolean-tag*      4)

(defmacro defbuiltin (name arity &rest rest)
  `(push (list ',name ,arity #'(lambda ,@rest))
         *builtins*))

(defbuiltin _write-int 1 (expr cs)
  (=> cs
    (comp2-expr (second expr))
    (check-tag *integer-tag*)
    (bf-vector-ref 1)
    (produce ".")))

(define (check-tag tag cs)
  (let ((cs
          (=> cs
              (produce ":")
              (bf-vector-ref 0)
              (produce (bf-num tag)))))
    (let* ((y (car (compiler-state-pos cs)))
           (x (cdr (compiler-state-pos cs)))
           (dy (- y (car *error-handler-position*)))
           (dx (- (+ x 2) (cdr *error-handler-position*))))
      (produce (fmt "-;x~A~A7;# _"
                    (reverse (bf-num dy))
                    (reverse (bf-num dx)))
               cs))))

(define (bf-tagged tag cs)
  (=> cs
      (bf-vector-ref 0)
      (produce (bf-num tag))
      (produce "-!")
      (produce (bf-num *boolean-tag*))     ; TAG
      (produce "\\")
      (bf-create-vector 2)))

(define (operator operation elems result-tag cs)
 (let ((cs (if (eq result-tag t)
             cs
             (produce (bf-num result-tag) cs))))
  (let ((cs
          (=> cs
              (each=>
                #'(lambda (x cs)
                    (let ((cs (comp2-expr (second x) cs)))
                      (let ((cs (if (eq (first x) t)
                                  cs
                                  (check-tag (first x) cs))))
                        (bf-vector-ref 1 cs))))
                elems)
              (produce operation))))
   (if (eq result-tag t)
     cs
     (bf-create-vector 2 cs)))))

(defmacro defoperator (name operation args result)
 (let ((gexpr (gensym))
       (gcs (gensym))
       (n 0))
  `(defbuiltin ,name ,(length args) (,gexpr ,gcs)
    (operator ,operation
      ,(cons 'list
         (mapcar #'(lambda (x)
                     (list 'list x (list 'nth (incf n) gexpr)))
                 args))
      ,result
      ,gcs))))

(defoperator _+ "+" (*integer-tag* *integer-tag*) *integer-tag*)
(defoperator _- "-" (*integer-tag* *integer-tag*) *integer-tag*)
(defoperator _* "*" (*integer-tag* *integer-tag*) *integer-tag*)
(defoperator _/ "/" (*integer-tag* *integer-tag*) *integer-tag*)
(defoperator _% "%" (*integer-tag* *integer-tag*) *integer-tag*)

(defoperator _not "!" (*boolean-tag*) *boolean-tag*)
(defoperator _= "-!" (*integer-tag* *integer-tag*) *boolean-tag*)

(defmacro defpredicate (name tag)
 (with-gensyms ("" ge gc)
  `(defbuiltin ,name 1 (,ge ,gc)
     (=> ,gc
        (comp2-expr (second ,ge))
        (bf-tagged ,tag)))))

(defpredicate _pair?        *cons-tag*)
(defpredicate _integer?     *integer-tag*)
(defpredicate _procedure?   *function-tag*)
(defpredicate _boolean?     *boolean-tag*)
(defpredicate _unspecified? *unspecified-tag*)

(defbuiltin _cons 2 (expr cs)
  (=> cs
    (produce (bf-num *cons-tag*))  ; TAG
    (comp2-expr (second expr))     ; car
    (comp2-expr (third expr))      ; cdr
    (bf-create-vector 3)))

(defbuiltin _car 1 (expr cs)
  (=> cs
    (comp2-expr (second expr))
    (check-tag *cons-tag*)
    (bf-vector-ref 1)))

(defbuiltin _cdr 1 (expr cs)
  (=> cs
    (comp2-expr (second expr))
    (check-tag *cons-tag*)
    (bf-vector-ref 2)))

;;; desugar:
;;; - convert (let ...) and (letrec ...) to lambdas

(define (desugar expr)
  (cond
    ((consp expr)
     (case (car expr)
       ((let)
        (unless (>= (length expr) 3)
          (assert (not "malformed let")))
        (unless (every #'(lambda (x) (and (consp x) (= (length x) 2)))
                       (second expr))
          (assert (not "malformed bindings")))
        `((lambda ,(mapcar #'first (second expr))
            ,@(mapcar #'desugar (cddr expr)))
          ,@(mapcar #'desugar (mapcar #'second (second expr)))))
       (t (mapcar #'desugar expr))))
    (t expr)))


;;; convert an expression to CPS

(let ((k (gensym))
      (r1 (gensym)))

  (define cpsify-application (expr)
    (let* ((gen-exprs (mapcar (lambda (x) (gensym)) expr))
           (e expr)
           (g gen-exprs))
     (list 'lambda (list k)
        (rec aux (e g)
           (if (null e)
             (list* (car gen-exprs) k (cdr gen-exprs))
             `(,(cpsify (car e))
                (lambda (,(car g))
                  ,(aux (cdr e) (cdr g)))))))))

  (define cpsify-builtin-application (builtin args)
    (let* ((gen-args (mapcar (lambda (x) (gensym)) args))
           (a args)
           (g gen-args))
      (list 'lambda (list k)
            (rec aux (a g)
                 (if (null a)
                   `(,k (,builtin ,@gen-args))
                   `(,(cpsify (car a))
                      (lambda (,(car g))
                        ,(aux (cdr a) (cdr g)))))))))

  (define cpsify-progn (expr)
    (if (consp expr)
      (if (consp (cdr expr))
       `(lambda (,k)
          (,(cpsify (car expr))
           (lambda (,r1)
            (,(cpsify-progn (cdr expr)) ,k))))
       (cpsify (car expr)))
      (assert (not "empty progn"))))
      
  (define cpsify (expr)
    (cond
      ((consp expr)
       (if (assoc (car expr) *builtins*)
         (cpsify-builtin-application (car expr) (cdr expr))
         ; else (not a builtin)
         (case (car expr)
           ; special forms
           ((lambda)
            (unless (>= (length expr) 3)
              (assert (not "malformed lambda")))
            `(lambda (,k)
               (,k (lambda (,k ,@(second expr))
                     (,(cpsify-progn (cddr expr)) ,k)))))

           ((begin)
            (unless (>= (length expr) 2)
              (assert (not "malformed begin")))
            (cpsify-progn (cdr expr)))

           ((set!)
            (unless (= (length expr) 3)
              (assert (not "malformed set!")))
            (princ
            `(lambda (,k)
               (,(cpsify (third expr))
                 (lambda (,r1)
                   (,k (set! ,(second expr) ,r1)))))))

           ((if)
            (unless (member (length expr) '(3 4))
              (assert (not "malformed if")))
            `(lambda (,k)
               (,(cpsify (second expr))
                 (lambda (,r1)
                   (if ,r1
                     (,(cpsify (third expr)) ,k)
                     (,(if (= (length expr) 4)
                         (cpsify (fourth expr))
                         (cpsify 0)) ,k))))))

           (t (cpsify-application expr)))))
      (t `(lambda (,k) (,k ,expr)))))
  
  (define cps (expr)
   `(,(cpsify expr) (lambda (x) x))))

;;; comp1:
;;;
;;; - flatten lambdas
;;;   each (lambda ...) form
;;;   gets into (%use-lambda ID)
;;;   plus a toplevel function definition (%def-lambda ID ...)
;;;
;;; - check arities of special forms and builtins

(define (valid-constant-p x)
  (numberp x))

(define (comp1 expr env)
 (cond
  ((consp expr)
   (if (assoc (car expr) *builtins*)
     ; builtins
     (progn
       (unless (= (length (cdr expr))
                  (second (assoc (car expr) *builtins*)))
         (assert (not "builtin: wrong arity")))
       (cons (car expr) (comp1-seq (cdr expr) env)))

     ; else (not a builtin)
     (case (car expr)
       ; special forms
       ((lambda)
        (unless (>= (length expr) 3)
          (assert (not "malformed lambda")))
        (let ((cbody
                (comp1
                  `(begin ,@(cddr expr))
                  (env-extend env (cadr expr))))
              (lambda-id (make-id)))
          (push
            `(%def-lambda ,lambda-id ,(cadr expr) ,cbody)
            *toplevel-forms*)
          `(%use-lambda ,lambda-id)))

       ((begin)
        (unless (>= (length expr) 2)
          (assert (not "malformed begin")))
        (cons (car expr) (comp1-seq (cdr expr) env)))

       ((set!)
        (unless (= (length expr) 3)
          (assert (not "malformed set!")))
        `(%local-set ,env ,(second expr) ,(comp1 (third expr) env)))

       ((if)
        (unless (= (length expr) 4)
          (assert (not "malformed if")))
        `(%if ,(comp1 (second expr) env)
              ,(comp1 (list 'lambda '() (third expr)) env)
              ,(comp1 (list 'lambda '() (fourth expr)) env)))

       ; else (application)
       (t (comp1-seq expr env)))))

  ; variables
  ((symbolp expr)
     (if (member expr '(true false))
       `(%boolean-constant ,(eq expr 'true))
       `(%local-ref ,env ,expr)))

  ; constants
  ((valid-constant-p expr) expr)

  ; else
  (t (assert (not "unimplemented type of constant")))))

(define comp1-seq (exprs env)
 (mapcar #'(lambda (e) (comp1 e env)) exprs))

(define (each=> f list x)
 (if (null list)
   x
   (=> x
     (funcall f (car list))
     (each=> f (cdr list)))))

(define (env-empty )
 '())

(define (env-extend env names)
 (cons names env))

;;; comp2:
;;; - produce befunge code in list representation
(define (comp2 exprs cs)
 (comp2-progn exprs cs))

(define (comp2-progn exprs cs)
 (=> cs
   (comp2-expr (car exprs))
   (each=>
     #'(lambda (e cs1)
         (=> cs1
             (produce "$")
             (comp2-expr e)))
     (cdr exprs))))

(define (comp2-args exprs cs)
  (each=> #'comp2-expr exprs cs))

(define (comp2-expr expr cs)
  ;(princ expr) (terpri)
  (cond
    ((consp expr)
     (if (assoc (car expr) *builtins*)
       (let ((func (third (assoc (car expr) *builtins*))))
         (funcall func expr cs))
       ; else (not a builtin)
       (case (car expr)
         ; special forms
         ((begin)
          (comp2-progn (cdr expr) cs))
         ((%def-lambda)
          (=> cs
              (define-function (second expr))
              (produce ">")
              (comp2-expr (fourth expr))
              (produce "q")
              ))
         ((%use-lambda)
          (=> cs
              (create-function (second expr))))
         ((%main)
          (=> cs
              (produce ">")
              (comp2-expr (second expr))
              (produce "q")))
         ((%if)
          (=> cs
              ;; the "then" and "else" parts get protected
              ;; by (lambda () ...) in comp1.
              ;; here we select the thunk and then invoke it.
              (comp2-expr (third expr))  ; then
              (comp2-expr (fourth expr)) ; else

              (comp2-expr (second expr)) ; condition

              ; transform scheme boolean -> befunge boolean
              ; for it to be false...:

              (produce ":")
              (bf-vector-ref 1)
              (produce "!\\")     ; 1. value must be 0
              (bf-vector-ref 0)
              (produce (bf-num *boolean-tag*))
              (produce "-!*!")    ; 2. tag must be boolean

              ; if true then drop "else" else drop "then"
              (produce ";x0a$;# _\\$>") 
              (invoke-function 0)))
         ((%local-set)
          (let ((env (second expr))
                (name (third expr))
                (value (fourth expr)))
            (local-set env name value cs)))
         ((%local-ref)
          (let ((env (cadr expr))
                (name (caddr expr)))
            (local-ref env name cs)))
         ((%boolean-constant)
          (push-boolean (second expr) cs))
         ; else (application)
         (t
           (=> cs
               (call-function (car expr) (cdr expr) (length (cdr expr)))))
         )))
    ((numberp expr)
     (push-number expr cs))
    ; else (constant)
    (t (format t "~A~%" expr)
       (assert (not "unimplemented type of constant")))))

(define (comp expr)
 (let ((expr (cps (desugar expr))))
  (pprint expr)
  (let ((main-expr (comp1 expr (env-empty))))
    (comp2
      (cons `(%main ,main-expr) *toplevel-forms*)
        (make-compiler-state)))))

(define (sponge-compile* output-file code)
  (with-open-file (f output-file :direction :output)
    (print-program (comp code) f)))

(defmacro (sponge-compile output-file code)
  `(sponge-compile* ,output-file ',code))
      

;;;; Tests

(sponge-compile "out.bf"
  (let ((fact false))
     (set! fact
       (lambda (n)
         (if (_= n 0)
           1
           (_* n (fact (_- n 1))))))
     (_write-int (fact 5))))

#|
(sponge-compile "out.bf"
  (_write-int 
    (((lambda (x)
        (lambda (y) (_+ x y)))
      11) 31)))

(sponge-compile "out.bf"
 ((lambda (x y w) (x y w))
            (lambda (x z)
              (set! z (_+ x z))
              (_write-int z))
            10
            3))
(sponge-compile "out.bf"
   (_write-int
        ((lambda (x) (set! x 1) x) 4)))

(sponge-compile "out.bf"
    (if
        (if
          (if false
             (begin (_write-int 4) false)
             (begin (_write-int 9) true))
          (begin (_write-int 9) false)
          (begin (_write-int 4) 0))
        (begin (_write-int 4) false)
        (begin (_write-int 9) false)))

(sponge-compile "out.bf"
    (if false
       (begin (_write-int 4) false)
       (begin (_write-int 9) 
         (if true
           (begin (_write-int 9) 
               (if false
                  (begin (_write-int 4)) 
                  (begin (_write-int 9))))
           (begin (_write-int 4) false)))))

(sponge-compile "out.bf"
    (if true
       (_write-int (_+ 10 5))
       (_write-int 20)))

(sponge-compile "out.bf"
    (_write-int
       (let ((x (let ((y 5)) (_+ y 2))))
         (let ((y 10))
           (_+ x y)))))

(sponge-compile "out.bf"
    (let ((sum false))
      (set! sum
        (lambda (x)
          (if (_pair? x)
            (_+ (_car x) (sum (_cdr x)))
            0)))
      (_write-int (length (_cons 10 (_cons 20 (_cons 30 false)))))))
|#
