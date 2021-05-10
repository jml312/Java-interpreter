; Josh Levy, William Park, Arthur Erlandson

; We were able to get 8 out of the 13 cases working (cases 7, 8, 11, 12, 13 did not work). Our idea was to have eval-dot-operator handle the left side
; of a dot, whether it is "this", "super", or the class instance, and remove the eval-super method. However, we were not able to get that working in time. 

#lang racket
;(require "functionParser.rkt")
(require "classParser.rkt")

(define interpret
  (lambda (file className)
    (scheme->language
     (interpret-statement-list (parser file) (newenvironment) (lambda (v) v)
                              (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                              (lambda (v env) (myerror "Uncaught exception thrown")) (lambda (env) (interpret-main-method (string->symbol className) env (lambda (v) v)
                                                                                                                      (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                                                                                                                      (lambda (v env) (myerror "Uncaught exception thrown")) (lambda (v) v)))))))
; interprets main method of a class
(define interpret-main-method
  (lambda (classname environment return break continue throw next)
    (interpret-funcall '(funcall main) (prep-env-for-class environment classname) return break continue throw next)))

; interprets a list of statements. The state/environment from each statement is used for the next ones.
(define interpret-statement-list
  (lambda (statement-list environment return break continue throw next)
    (cond
      ((null? statement-list) (next environment))
      (else (interpret-statement (car statement-list) environment return break continue throw
                                 (lambda (env) (interpret-statement-list (cdr statement-list) env return break continue throw next)))))))

; interpret a statement in the environment with continuations for return, break, continue, throw, and "next statement"
(define interpret-statement
  (lambda (statement environment return break continue throw next)
    (cond
      ((eq? 'return (statement-type statement)) (interpret-return statement environment throw return))
      ((eq? 'var (statement-type statement)) (interpret-declare statement environment throw next))
      ((eq? '= (statement-type statement)) (interpret-assign statement environment throw next))
      ((eq? 'if (statement-type statement)) (interpret-if statement environment return break continue throw next))
      ((eq? 'while (statement-type statement)) (interpret-while statement environment return throw next))
      ((eq? 'continue (statement-type statement)) (continue environment))
      ((eq? 'break (statement-type statement)) (break environment))
      ((eq? 'begin (statement-type statement)) (interpret-block statement environment return break continue throw next))
      ((eq? 'throw (statement-type statement)) (interpret-throw statement environment throw))
      ((eq? 'try (statement-type statement)) (interpret-try statement environment return break continue throw next))
      ((eq? 'function (statement-type statement)) (interpret-function statement environment next))
      ((eq? 'funcall (statement-type statement)) (interpret-funcall statement environment (lambda (v) (next environment)) break continue throw next))
      ((eq? 'class (statement-type statement)) (interpret-class (cadr statement)
                                                                (caddr statement) (cdddr statement) environment return break continue throw next))
      (else (myerror "Unknown statement:" (statement-type statement))))))  

; Calls the return continuation with the given expression value
(define interpret-return
  (lambda (statement environment throw return)
    (eval-expression (get-expr statement) environment throw return)))

; Adds a new variable binding to the environment.  There may be an assignment with the variable
(define interpret-declare
  (lambda (statement environment throw next)
    (if (exists-declare-value? statement)
        (eval-expression (get-declare-value statement) environment throw (lambda (val) (next (insert (get-declare-var statement) val environment))))
        (next (insert (get-declare-var statement) 'novalue environment)))))

; Updates the environment to add a new binding for a variable
(define interpret-assign
  (lambda (statement environment throw next)
    (eval-expression (get-assign-rhs statement) environment throw (lambda (val) (next (update (get-assign-lhs statement) val environment))))))

; We need to check if there is an else condition.  Otherwise, we evaluate the expression and do the right thing.
(define interpret-if
  (lambda (statement environment return break continue throw next)
    (eval-expression (get-condition statement) environment throw (lambda (val) (cond
                                                                           (val (interpret-statement (get-then statement) environment return break continue throw next))
                                                                           ((exists-else? statement) (interpret-statement (get-else statement) environment return break continue throw next))
                                                                           (else (next environment)))))))

; Interprets a while loop.  We must create break and continue continuations for this loop
(define interpret-while
  (lambda (statement environment return throw next)
    (letrec ((loop (lambda (condition body environment)
                     (eval-expression condition environment throw (lambda (val) (if val
                         (interpret-statement body environment return (lambda (env) (next env)) (lambda (env) (loop condition body env)) throw (lambda (env) (loop condition body env)))
                         (next environment)))))))
      (loop (get-condition statement) (get-body statement) environment))))


; Interprets a block.  The break, continue, throw and "next statement" continuations must be adjusted to pop the environment
(define interpret-block
  (lambda (statement environment return break continue throw next)
    (interpret-statement-list (cdr statement)
                                         (push-frame environment)
                                         return
                                         (lambda (env) (break (pop-frame env)))
                                         (lambda (env) (continue (pop-frame env)))
                                         (lambda (v env) (throw v (pop-frame env)))
                                         (lambda (env) (next (pop-frame env))))))

; We use a continuation to throw the proper value.  Because we are not using boxes, the environment/state must be thrown as well so any environment changes will be kept
(define interpret-throw
  (lambda (statement environment throw)
    (eval-expression (get-expr statement) environment throw (lambda (e) (throw e environment)))))

; Interpret a try-catch-finally block

; Create a continuation for the throw.  If there is no catch, it has to interpret the finally block, and once that completes throw the exception.
;   Otherwise, it interprets the catch block with the exception bound to the thrown value and interprets the finally block when the catch is done
(define create-throw-catch-continuation
  (lambda (catch-statement environment return break continue throw next finally-block)
    (cond
      ((null? catch-statement) (lambda (ex env) (interpret-block finally-block env return break continue throw (lambda (env2) (throw ex env2)))))
      ((not (eq? 'catch (statement-type catch-statement))) (myerror "Incorrect catch statement"))
      (else (lambda (ex env)
                  (interpret-statement-list
                       (get-body catch-statement)
                       (insert (catch-var catch-statement) ex (push-frame env))
                       return
                       (lambda (env2) (break (pop-frame env2)))
                       (lambda (env2) (continue (pop-frame env2)))
                       (lambda (v env2) (throw v (pop-frame env2)))
                       (lambda (env2) (interpret-block finally-block (pop-frame env2) return break continue throw next))))))))

; To interpret a try block, we must adjust  the return, break, continue continuations to interpret the finally block if any of them are used.
;  We must create a new throw continuation and then interpret the try block with the new continuations followed by the finally block with the old continuations
(define interpret-try
  (lambda (statement environment return break continue throw next)
    (let* ((finally-block (make-finally-block (get-finally statement)))
           (try-block (make-try-block (get-try statement)))
           (new-return (lambda (v) (interpret-block finally-block environment return break continue throw (lambda (env2) (return v)))))
           (new-break (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (break env2)))))
           (new-continue (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (continue env2)))))
           (new-throw (create-throw-catch-continuation (get-catch statement) environment return break continue throw next finally-block)))
      (interpret-block try-block environment new-return new-break new-continue new-throw (lambda (env) (interpret-block finally-block env return break continue throw next))))))

; helper methods so that I can reuse the interpret-block method on the try and finally blocks
(define make-try-block
  (lambda (try-statement)
    (cons 'begin try-statement)))

(define make-finally-block
  (lambda (finally-statement)
    (cond
      ((null? finally-statement) '(begin))
      ((not (eq? (statement-type finally-statement) 'finally)) (myerror "Incorrectly formatted finally block"))
      (else (cons 'begin (cadr finally-statement))))))

(define catch-var
  (lambda (catch-statement)
    (car (operand1 catch-statement))))

; Add a new function to a state
(define interpret-function
  (lambda (statement environment next)
    (next (insert (get-function-var statement) (get-function-value statement) environment))))

; Call a function
(define interpret-funcall
  (lambda (statement environment return break continue throw next)
    (cond
      ((list? (operand1 statement)) (eval-expression (cadr statement) environment throw (lambda (f)
                                                              (addBinding (append (car f) (list 'this)) (append (cddr statement) (list (operand1 (operand1 statement)))) environment (setupEnv (cadr statement) environment) throw (lambda (e)
                                                                                                                                                               (interpret-statement-list (cadr f) e return break continue (lambda (v e2) (throw v environment)) (lambda (e2)
                                                                                                                                                                                                                                                                  (next environment))))))))
      (else (eval-expression (cadr statement) environment throw (lambda (f)
                                                              (addBinding (car f) (cddr statement) environment (setupEnv (cadr statement) environment) throw (lambda (e)
                                                                                                                                                               (interpret-statement-list (cadr f) e return break continue (lambda (v e2) (throw v environment)) (lambda (e2) (next environment)))))))))))

; Adds a binging to the state. Evaluates the parameters in a function
(define addBinding
  (lambda (paramList inputParamList environment activeEnv throw next)
    (cond
      ((and (null? paramList) (null? inputParamList)) (next activeEnv))
      ((or (and (null? inputParamList) (not (null? paramList))) (and (not (null? inputParamList)) (null? paramList))) (myerror "mismatched parameters and arguments"))
      (else (eval-expression (car inputParamList) environment throw (lambda (p)
                                                                      (addBinding (cdr paramList) (cdr inputParamList) environment (insert (car paramList) p activeEnv) throw next)))))))

; Setup the environment
(define setupEnv
  (lambda (name environment)
    (cond
      ((list? name) (push-frame (prep-env-for-instance environment (operand1 name))))
      (push-frame (getactiveenvironment name environment)))))

; interprets a class call. If there is no super class, a new class frame is created. Otherwise, a super class closure is created with a new class frame.
(define interpret-class
  (lambda (classname superclass body environment return break continue throw next)
    (cond
      ((null? superclass) (interpret-class-closure (car body) new-class-frame return break continue throw (lambda (cc) (next (insert classname cc environment)))))
      (else (interpret-class-closure (car body) (add-superclass (cdr superclass) new-class-frame) return break continue throw (lambda (cc) (next (insert classname cc environment))))))))

; interprets a classes' closure by checking the statement type and either interpreting a declaration or function call from it.
(define interpret-class-closure
  (lambda (statements environment return break continue throw next)
    (cond
      ((null? statements) (next environment))
      ((eq? 'var (statement-type (car statements))) (interpret-declare (car statements) (list (get-dynamic-variables environment))
                                                                       throw (lambda (e) (interpret-class-closure (cdr statements) (add-new-dynamic-variables environment (car e)) return break continue throw next))))
      ((eq? 'static-var (statement-type (car statements))) (interpret-declare (car statements) (list (get-static-variables environment))
                                                                              throw (lambda (e) (interpret-class-closure (cdr statements) (add-new-static-variables environment (car e)) return break continue throw next))))
      ((eq? 'function (statement-type (car statements))) (interpret-function (car statements) (list (get-dynamic-methods environment))
                                                                             (lambda (e) (interpret-class-closure (cdr statements) (add-new-dynamic-methods environment (car e)) return break continue throw next))))
      ((eq? 'static-function (statement-type (car statements))) (interpret-function (car statements) (list (get-static-methods environment))
                                                                                    (lambda (e) (interpret-class-closure (cdr statements) (add-new-static-methods environment (car e)) return break continue throw next))))
      ((eq? 'abstract-function (statement-type (car statements))) (interpret-function (car statements) (list (get-dynamic-methods environment))
                                                                                      (lambda (e) (interpret-class-closure (cdr statements) (add-new-dynamic-methods environment (car e)) return break continue throw next))))
      (else (myerror "Unknown statement:" (statement-type (car statements)))))))

; Evaluates all possible boolean and arithmetic expressions, including constants and variables. Also checks for super call.
(define eval-expression
  (lambda (expr environment throw next)
    (cond
      ((number? expr) (next expr))
      ((eq? expr 'true) (next #t))
      ((eq? expr 'false) (next #f))
      ((eq? expr #t) expr)
      ((eq? expr #f) expr)
      ((eq? expr 'super) (eval-super environment throw next))
      ((not (list? expr)) (next (lookup expr environment)))
      (else (eval-operator expr environment throw next)))))

; evaluates a super call by creating a closure of the super class, the variable values, and the current type
(define eval-super
  (lambda (env throw next)
    (next (cons (get-super-name (lookup (getclass (lookup 'this env)) env)) (cdr (lookup 'this env))))))

; Evaluate a binary (or unary) operator.  Although this is not dealing with side effects, I have the routine evaluate the left operand first and then
; pass the result to eval-binary-op2 to evaluate the right operand.  This forces the operands to be evaluated in the proper order in case you choose
; to add side effects to the interpreter
(define eval-operator
  (lambda (expr environment throw next)
    (cond
      ((eq? 'new (operator expr)) (next (create-instance-closure (cadr expr) environment)))
      ((eq? '! (operator expr)) (eval-expression (operand1 expr) environment throw (lambda (val) (next (not val)))))
      ((eq? 'funcall (operator expr)) (interpret-funcall expr environment (lambda (v) (next v)) (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop")) throw next))
      ((and (eq? '- (operator expr)) (= 2 (length expr))) (eval-expression (operand1 expr) environment throw (lambda (val) (next (- val)))))
      ((eq? '= (operator expr)) (interpret-assign expr environment throw (lambda (env) (next (lookup expr env)))))
      (else (eval-expression (operand1 expr) environment throw (lambda (op1value) (eval-binary-op2 expr op1value environment throw next)))))))

; Complete the evaluation of the binary operator by evaluating the second operand and performing the operation. Also evaluates a dot operator if a dot is
; in the expression.
(define eval-binary-op2
  (lambda (expr op1value environment throw next)
    (cond
      ((eq? '+ (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (+ op1value op2value)))))
      ((eq? '- (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (- op1value op2value)))))
      ((eq? '* (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (* op1value op2value)))))
      ((eq? '/ (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (/ op1value op2value)))))
      ((eq? '% (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (remainder op1value op2value)))))
      ((eq? '== (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (isequal op1value op2value)))))
      ((eq? '!= (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (not (isequal op1value op2value))))))
      ((eq? '< (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (< op1value op2value)))))
      ((eq? '> (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (> op1value op2value)))))
      ((eq? '<= (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (<= op1value op2value)))))
      ((eq? '>= (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (>= op1value op2value)))))
      ((eq? '|| (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (or op1value op2value)))))
      ((eq? '&& (operator expr)) (eval-expression (operand2 expr) environment throw (lambda (op2value) (next (and op1value op2value)))))
      ((eq? 'dot (operator expr)) (eval-dot-operator op1value (operand2 expr) environment next))
      (else (next (myerror "Unknown operator:" (operator expr)))))))

; evalutes a dot by creating a closure with the function call. For example, if the closure looks like "((w) ((= width w)))", then the left side is the parameter
; list and the right is the body of the function. Function bodies can also contain both this and super calls in them, and parameter lists can be empty.
(define eval-dot-operator
  (lambda (instance value env next)
    (next (lookup value (list (merge-state-frames (get-all-methods-from-class
                                                   (lookup (get-true-type instance) env) env) (list (append (get-static-variable-names
                                                                                                             (lookup (getclass instance) env)) (get-dynamic-variable-names
                                                                                                                                                (lookup (getclass instance) env))) (get-variable-values instance))))))))

; Determines if two values are equal.  We need a special test because there are both boolean and integer types.
(define isequal
  (lambda (val1 val2)
    (if (and (number? val1) (number? val2))
        (= val1 val2)
        (eq? val1 val2))))

;-----------------
; HELPER FUNCTIONS
;-----------------

; These helper functions define the operator and operands of a value expression
(define operator car)
(define operand1 cadr)
(define operand2 caddr)
(define operand3 cadddr)

(define exists-operand2?
  (lambda (statement)
    (not (null? (cddr statement)))))

(define exists-operand3?
  (lambda (statement)
    (not (null? (cdddr statement)))))

; these helper functions define the parts of the various statement types
(define statement-type operator)
(define get-expr operand1)
(define get-function-var operand1)
(define get-function-value cddr)
(define get-declare-var operand1)
(define get-declare-value operand2)
(define exists-declare-value? exists-operand2?)
(define get-assign-lhs operand1)
(define get-assign-rhs operand2)
(define get-condition operand1)
(define get-then operand2)
(define get-else operand3)
(define get-body operand2)
(define exists-else? exists-operand3?)
(define get-try operand1)
(define get-catch operand2)
(define get-finally operand3)

; class getter/helper abstractions
(define getclass car)
(define get-dynamic-methods car)
(define get-static-methods cadr)
(define get-variable-values cadr)
(define get-var-vals cadr)
(define get-dynamic-variables caddr)
(define get-static-variables cadddr)
(define get-dynamic-variable-names caaddr)
(define get-true-type caddr)
(define get-super (lambda (class) (car (cddddr class))))
(define get-super-name (lambda (class) (caar (cddddr class))))
(define get-static-variable-names (lambda (class) (caar (cdddr class))))

(define new-instance-frame '(()))

; returns a new class frame with: classname, methods, variables (from instances and methods), and super class
(define new-class-frame '((()()) (()()) (()()) (()()) ()))

;------------------------
; Environment/State Functions
;------------------------

; get active environment
(define getactiveenvironment
  (lambda (var environment)
    (if (exists-in-list? var (variables (topframe environment)))
        environment
        (getactiveenvironment var (remainingframes environment)))))

; create a new empty environment
(define newenvironment
  (lambda ()
    (list (newframe))))

; create an empty frame: a frame is two lists, the first are the variables and the second is the "store" of values
(define newframe
  (lambda ()
    '(() ())))

; add a frame onto the top of the environment
(define push-frame
  (lambda (environment)
    (cons (newframe) environment)))

; remove a frame from the environment
(define pop-frame
  (lambda (environment)
    (cdr environment)))

; some abstractions
(define topframe car)
(define remainingframes cdr)

; does a variable exist in the environment?
(define exists?
  (lambda (var environment)
    (cond
      ((null? environment) #f)
      ((exists-in-list? var (variables (topframe environment))) #t)
      (else (exists? var (remainingframes environment))))))

; does a variable exist in a list?
(define exists-in-list?
  (lambda (var l)
    (cond
      ((null? l) #f)
      ((eq? var (car l)) #t)
      (else (exists-in-list? var (cdr l))))))

; Looks up a value in the environment.  If the value is a boolean, it converts our languages boolean type to a Scheme boolean type
(define lookup
  (lambda (var environment)
    (unbox (lookup-variable var environment))))

; A helper function that does the lookup.  Returns an error if the variable does not have a legal value
(define lookup-variable
  (lambda (var environment)
    (let ((value (lookup-in-env var environment)))
      (if (eq? 'novalue value)
          (myerror "error: variable without an assigned value:" var)
          value))))

; Return the value bound to a variable in the environment
(define lookup-in-env
  (lambda (var environment)
    (cond
      ((null? environment) (myerror "error: undefined variable" var))
      ((exists-in-list? var (variables (topframe environment))) (lookup-in-frame var (topframe environment)))
      (else (lookup-in-env var (cdr environment))))))

; Return the value bound to a variable in the frame
(define lookup-in-frame
  (lambda (var frame)
    (cond
      ((not (exists-in-list? var (variables frame))) (myerror "error: undefined variable" var))
      (else (language->scheme (get-value (indexof var (variables frame)) (store frame)))))))

; Get the location of a name in a list of names
(define indexof
  (lambda (var l)
    (cond
      ((null? l) 0)  ; should not happen
      ((eq? var (car l)) 0)
      (else (+ 1 (indexof var (cdr l)))))))

; Get the value stored at a given index in the list
(define get-value
  (lambda (n l)
    (cond
      ((zero? (- (length l) (+ n 1))) (car l))
      (else (get-value n (cdr l))))))

; Adds a new variable/value binding pair into the environment.  Gives an error if the variable already exists in this frame.
(define insert
  (lambda (var val environment)
    (cond
      ((exists-in-list? var (variables (car environment))) (myerror "error: variable is being re-declared:" var))
      ((box? var) (cons (add-to-frame var (box (unbox val)) (car environment)) (cdr environment)))
      (else (cons (add-to-frame var (box val) (car environment)) (cdr environment))))))

; Changes the binding of a variable to a new value in the environment.  Gives an error if the variable does not exist.
(define update
  (lambda (var val environment)
    (cond
      ((list? var) (set-boxed-value (operand1 var) (operand2 var) val environment))
      ((exists? var environment) (update-existing var val environment))
      (else (myerror "error: variable used but not defined:" var)))))

; Add a new variable/value pair to the frame.
(define add-to-frame
  (lambda (var val frame)
    (list (cons var (variables frame)) (append (store frame) (list (scheme->language val))))))

; Changes the binding of a variable in the environment to a new value
(define update-existing
  (lambda (var val environment)
    (if (exists-in-list? var (variables (car environment)))
        (begin (update-in-frame var val (topframe environment)) environment) 
        (cons (topframe environment) (update-existing var val (remainingframes environment))))))

; Changes the binding of a variable in the frame to a new value.
(define update-in-frame
  (lambda (var val frame)
    (list (variables frame) (update-in-frame-store var val (variables frame) (store frame)))))

; Changes a variable binding by placing the new value in the appropriate place in the store
(define update-in-frame-store
  (lambda (var val varlist vallist)
    (cond
      ((eq? var (car varlist)) (reverse (cons (scheme->language (begin (set-box! (car (reverse vallist)) val) (car (reverse vallist)))) (reverse (cdr vallist)))))
      (else (cons (car vallist) (update-in-frame-store var val (cdr varlist) (reverse (cdr (reverse vallist)))))))))

; Returns the list of variables from a frame
(define variables
  (lambda (frame)
    (car frame)))

; Returns the store from a frame
(define store
  (lambda (frame)
    (cadr frame)))

;------------------------
; Box functions
;------------------------

(define reboxlist
 (lambda (lis)
   (cond
     ((null? lis) lis)
     (else (cons (unbox-rebox (car lis)) (reboxlist (cdr lis)))))))

(define unbox-rebox
  (lambda (var)
    (box (unbox var))))

; sets a boxed value to a new value
(define set-boxed-value
  (lambda (instance value newvalue env)
    (begin (update-existing value newvalue (list (list (append (get-static-variable-names
                                                                (lookup (getclass (lookup instance env)) env)) (get-dynamic-variable-names
                                                                                                                (lookup (getclass (lookup instance env)) env))) (get-variable-values (lookup instance env))))) env)))

;------------------------
; Class Functions
;------------------------

; adds an instance frame to an environment
(define push-instance-frame
  (lambda (env next)
    (display (cons (new-instance-frame) env)) (newline)
    (next (cons (new-instance-frame) env))))

; creates a closure with class name, variables, then super class
(define create-instance-closure 
  (lambda (classname env)
        (cons classname (append (list (get-super-instance-closure classname env)) (list classname)))))

; adds new static variables onto a class closure
(define add-new-static-variables
  (lambda (cc vars)
    (append (list (get-dynamic-methods cc) (get-static-methods cc) (get-dynamic-variables cc) vars) (list (get-super cc)))))

; adds ew dynamic variables onto a class closure
(define add-new-dynamic-variables
  (lambda (cc vars)
    (append (list (get-dynamic-methods cc) (get-static-methods cc) vars) (cdddr cc))))

; adds new static methods onto a class closure
(define add-new-static-methods
  (lambda (cc methods)
    (append (list (get-dynamic-methods cc) methods) (cddr cc))))

; adds new dynamic variables onto a class closure
(define add-new-dynamic-methods
  (lambda (cc methods)
    (cons methods (cdr cc))))

; adds a super class inside of a list onto the end of a closure
(define add-superclass
  (lambda (superclass env)
    (append (list (get-dynamic-methods env) (get-static-methods env) (get-dynamic-variables env) (get-static-variables env)) (list superclass))))

; checks if a given class contains a super class
(define has-super?
  (lambda (class)
    (cond
      ((null? (get-super class)) #f)
      (else #t))))

; evaluates an expression with the given instance
(define prep-env-for-instance 
  (lambda (env instance)
    (eval-expression instance env (lambda (v) (myerror "error: could not prepare env for instance")) (lambda (v)
                                                                          (append  (list (get-all-methods-from-class (lookup (getclass v) env) env)
                                                                                   (get-instance-names-and-values env v)) env)))))

; prepares the environment for a new classname to be inserted
(define prep-env-for-class
  (lambda (env classname)
    (append (list (get-static-methods (lookup classname env)) (get-static-variables (lookup classname env))) env)))

; coombines two state frames together into one
(define merge-state-frames 
  (lambda (frame-a frame-b)
    (list (append (car frame-a) (car frame-b)) (append (cadr frame-b) (cadr frame-a)))))


; getter functions for classes

; returns the names and values of instance variables from a class
(define get-instance-names-and-values
  (lambda (env instance)
    (list (get-all-variable-names-from-class (lookup (getclass instance) env) env) (get-variable-values instance))))

; returns the variable names of a class
(define get-all-variable-names-from-class
  (lambda (cc env)
    (cond
      ((has-super? cc) (append (get-all-variable-names-from-class (lookup (get-super-name cc) env) env)
                               (get-dynamic-variable-names cc)(get-static-variable-names cc)))
      (else (append (get-dynamic-variable-names cc) (get-static-variable-names cc))))))

; returns all methods from a given class closure
(define get-all-methods-from-class 
  (lambda (cc env)
    (cond
      ((has-super? cc) (merge-state-frames (merge-state-frames (get-dynamic-methods cc)
                                                               (get-static-methods cc)) (get-all-methods-from-class (lookup (get-super-name cc) env) env)))
      (else (merge-state-frames (get-dynamic-methods cc) (get-static-methods cc))))))

; returns the closure of a super instance. If the classname does not have a super class, the closure value of the class is returned
(define get-super-instance-closure
  (lambda (classname env)
    (cond
      ((has-super? (lookup classname env)) (append (get-closure-value classname env) (get-super-instance-closure (get-super-name (lookup classname env)) env)))
      (else (get-closure-value classname env)))))

; returns a closure with the values (or non values) from a class
(define get-closure-value
  (lambda (classname env)
    (append (get-var-vals (get-static-variables (lookup classname env))) (reboxlist (get-var-vals (get-dynamic-variables (lookup classname env)))))))

; Functions to convert the Scheme #t and #f to our languages true and false, and back.
(define language->scheme
  (lambda (v)
    (cond
      ((eq? v 'false) #f)
      ((eq? v 'true) #t)
      (else v))))

(define scheme->language
  (lambda (v)
    (cond
      ((eq? v #f) 'false)
      ((eq? v #t) 'true)
      (else v))))

; Because the error function is not defined in R5RS scheme, I create my own:
(define error-break (lambda (v) v))
(call-with-current-continuation (lambda (k) (set! error-break k)))

(define myerror
  (lambda (str . vals)
    (letrec ((makestr (lambda (str vals)
                        (if (null? vals)
                            str
                            (makestr (string-append str (string-append " " (symbol->string (scheme->language (car vals))))) (cdr vals))))))
      (error-break (display (string-append str (makestr "" vals)))))))