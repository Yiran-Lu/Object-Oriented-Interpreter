#lang racket
;(require "functionParser.rkt")
(require "classParser.rkt")
;group 25
;Yiran lu  Zhongyan Tang





;ABSTRACTION
(define operator (lambda (expression) (car expression)))
(define leftoperand cadr)
(define rightoperand caddr)
(define get-field-lists caddr)
(define variablename cadr)
(define fieldname caddr)


;Loop Condition
(define condition (lambda (expression) (cadr expression)))
(define truecase caddr)
(define falsecase cadddr)
(define condition1 cadr)
(define body1 caddr)

;try catch condition
(define catch-variable caadar)
(define catch-body caddar)

(define class-extension cadr)
(define state-name cadr)
(define extension caddr)
(define class-body cadddr)

(define variable cadr)
(define value caddr)
(define assignment cddr)
(define current-state car)
(define the-rest-part cdr)

(define functionname cadr)
(define parameter-and-body cddr)
(define formalparameter caddr)
(define functionbody cadddr)

(define parameters cddr)
(define parameter-values cddr)
(define closure-body cdadr)
(define parameter-names caadr)
(define varname cadadr)

;interpret
(define interpret
  (lambda (filename classname)
    (interpret-helper (parser filename) classname)))

;interpret helper
(define interpret-helper
  (lambda (expression classname)
    (interpret-command (main-body classname (get-class-closure expression '())) '(()) (get-class-closure expression '()) '() error error error)))

;interpret the commend
(define interpret-command
  (lambda(expression state closures this break continue throw)
    (call/cc (lambda(return)
               (ibreak expression state closures this break continue return throw)))))


;reformat the raw parser into class closures
(define get-class-closure
  (lambda (expression closure)
    (if (null? expression)
        closure
        (get-class-closure (cdr expression) (M-class (car expression) '() closure error error error error)))))





;pop state
(define remove-state
  (lambda (state)
    (cdr state)))

;add layer
(define add-state
  (lambda (state)
    (cons '() state)))

;interpreter break
(define ibreak
  (lambda (expression state closures this break continue return throw)
    (if(null? expression)
       (remove-state state)
       (if (eq? (caar expression) 'funcall)
           (begin (pass (car expression) state closures this break continue return throw  '()) (ibreak (cdr expression) state closures this break continue return throw ))
           (ibreak (cdr expression) (pass (car expression) state closures this break continue return throw '()) closures this break continue return throw )))))



;initializing an object
(define M-new
  (lambda (expression state closures this break continue return throw)
    (M-new-helper (cadr expression) closures)))

;count how many index are behind the current variable
(define counter-index
  (lambda (variablename classname classclosure)
    (counter-index-helper variablename (reverse (find-class-and-parent-field classname classclosure)) 0)))


;get the value of the compile filed by count index
(define compile-value
  (lambda (instance-closure index)
    (compile-value-helper (get-field-lists instance-closure) index)))


;find body
(define main-body
  (lambda(classname state)
    (cadadr (main-closure (find-class-closure classname state)))))

;closure of main func
(define main-closure
  (lambda (state)
    (cond
      ((null? state) (error 'main-closure-not-found))
      ((eq? 'main (caar state)) (car state))
      (else (main-closure (cdr state))))))

;gets the class closure
(define find-class-closure
  (lambda (classname state)
    (cond
      ((null? state) (error 'class-name-not-found))
      ((eq? classname (caar state)) (caddar state))
      (else (find-class-closure classname (cdr state))))))




;pass the code to its correct state
(define pass
  (lambda (expression state closures this break continue return throw class-name)
    (cond
      ((null? expression) state)
      ((eq? 'true expression) #t)
      ((eq? 'false expression) #f)
      ((number? expression) expression)
      ((boolean? expression) expression)
      ((contain? expression state) (M-value expression state))
      ((and (not (null? this)) (contain-helper expression (caddr this))) (compile-value this (counter-index expression class-name closures)))
      ((list? (car expression)) (ibreak expression state closures this break continue return throw))
      ((eq? (car expression) 'new) (M-new expression state closures this break continue return throw))
      ((eq? (car expression) 'class) (M-class expression state closures this break continue return throw))
      ((eq? (car expression) 'function) (M-function expression state closures this break continue return throw class-name))
      ((eq? (car expression) 'dot) (M-dot-field (variablename expression) (fieldname expression) state closures this))
      ((eq? (car expression) 'static-function) (M-function expression state closures this break continue return throw class-name ))
      ((eq? (car expression) 'funcall) (M-funcall expression state closures this break continue return throw class-name))
      ((eq? (car expression) 'begin) (M-block expression (add-state state) closures this break continue return throw))
      ((eq? (car expression) 'try) (M-try (cdr expression) state closures this break continue return throw))
      ((eq? (car expression) 'throw) (throw (cons (cons (cons 'throw-value (box (pass (cadr expression) state closures this break continue return throw class-name))) (car state)) (cdr state))))
      ((eq? (car expression) 'break)(break (remove-state state)))
      ((eq? (car expression) 'continue)(continue (remove-state state)))
      ((eq? (car expression) 'return) (return (pass (cadr expression) state closures this break continue return throw class-name)))
      ((eq? (car expression) 'if) (M-if expression state closures this break continue return throw))
      ((eq? (car expression) 'while) (M-while (condition1 expression) (body1 expression) state closures this continue return throw))
      ((eq? (car expression) 'var) (M-declare expression state closures this break continue return throw))
      ((eq? (car expression) '=) (M-assign expression state closures this break continue return throw))
      ((checkArith (car expression)) (M-integer expression state closures this break continue return throw))
      ((checkboolean expression) (M-boolean expression state closures this break continue return throw))
      (else (error 'invalid-statement)))))

;. field helper
(define M-dot-field-helper
  (lambda (body-closure field)
    (cond
      ((null? body-closure) error 'field-not-found)
      ((eq? field (caar body-closure)) (unbox (cdar body-closure)))
      (else (M-dot-field-helper (cdr body-closure) field)))))

;gets the . field
(define M-dot-field
  (lambda (name field state closures this)
    (cond
      ((eq? name 'this) (M-dot-field-helper (caddr this) field))
      ((list? name) (M-dot-field-helper (caddr (pass name state closures this error error error error '())) field))
      (else (M-dot-field-helper (caddr (check-field-in-closure name state this)) field)))))
;. function
(define M-dot-function
 (lambda (name state class-closure function-name this)
   (cond
     ((eq? name 'this) (M-dot-function1 (car this) class-closure function-name))
     ((eq? name 'super) (M-dot-function1 (cadr this) class-closure function-name))
     (else (M-dot-function1 (get-runtime-type name state this) class-closure function-name)))))

(define M-class
  (lambda (class-define-statement local-state class-state break continue return throw)
    (cons (append (cons (state-name class-define-statement) (cons (extension class-define-statement) '())) (M-class-helper (class-body class-define-statement) '(()) '() '() '() '() (state-name class-define-statement) ) ) class-state)))


;helper function
(define M-class-helper
  (lambda (class-body state break continue return throw class-name)
    (if(null? class-body)
       state
       (M-class-helper (cdr class-body) (pass (car class-body) state '() '() break continue return throw class-name) break continue return throw class-name))))

; code block
(define M-block
  (lambda (expression state closures this break continue return throw)
     (ibreak (cdr expression) state closures this break continue return throw)))


;'(expression1 (catch (e) expression2) (finally expression3))
(define M-try
  (lambda (expression state closures this break continue return throw)
    (M-catch (cdr expression) (call/cc (lambda(throw-w) (ibreak-try (car expression) state closures this break continue return throw-w))) closures this break continue return throw)))

;catch
(define M-catch
  (lambda (expression state closures this break continue return throw)
    (cond
      ((null? (car expression)) (ibreak-try (final-exp expression) state closures this break continue return throw))
      ((if (contain? 'throw-value state)
         (ibreak-try (final-exp expression) (ibreak-try (catch-body expression) (add-exception (catch-variable expression) (box (get-throw-value state)) state) closures break continue return throw) closures break continue return throw)
         (ibreak-try (final-exp expression) state closures this break continue return throw))))))

;while loop
(define M-while
  (lambda (condition body state closures this continue return throw)
    (call/cc (lambda(break)
               (M-loop-break condition body state break closures this continue return throw)))))


;M-while maps if expressions to expression
(define M-loop-break
   (lambda (condition body state closures this break continue return throw)
     (if (M-boolean condition state closures this break continue return throw)
         (M-loop-break condition body (call/cc (lambda(continue-w) (pass body state closures this break continue-w return throw '()))) closures this break continue return throw)
         state)))


;call function
(define M-funcall
  (lambda(expression state closures this break continue return throw class-name)
    (if (eq? (parameters expression) '())
        (if(list? (varname expression))
           (interpret-command-funcall (closure-body (M-dot-function1 (cadr (varname expression)) closures (funname expression)))
                                      state
                                      closures
                                      (pass (varname expression) state closures this break continue return throw '())
                                      error
                                      error
                                      throw
                                      (caddr (M-dot-function1 (cadr (varname expression)) closures (funname expression)))
                                      )
           (interpret-command-funcall (closure-body (M-dot-function (varname expression) state closures (funname expression) this))
                                      state
                                      closures
                                      (check-field-in-closure (varname expression) state this)
                                      error
                                      error
                                      throw
                                      (caddr (M-dot-function (varname expression) state closures (funname expression) this))
                                      ))
         (if(list? (varname expression))
           (interpret-command-funcall (closure-body (M-dot-function1 (cadr (varname expression)) closures (funname expression)))
                                      (pbind
                                       (parameter-names (M-dot-function1 (cadr (varname expression)) closures (funname expression)))
                                       (parameter-values expression)
                                       state
                                       closures
                                       this
                                       )
                                      closures
                                      (pass (varname expression) state closures this break continue return throw '())
                                      error
                                      error
                                      throw
                                      (caddr (M-dot-function1 (cadr (varname expression)) closures (funname expression))))

           (interpret-command-funcall (closure-body (M-dot-function (varname expression) state closures (funname expression) this))
                                      (pbind
                                       (parameter-names (M-dot-function (varname expression) state closures (funname expression) this))
                                       (parameter-values expression)
                                       state
                                       closures
                                       this
                                       )
                                      closures
                                      (check-field-in-closure (varname expression) state this)
                                      error
                                      error
                                      throw
                                      (caddr (M-dot-function (varname expression) state closures (funname expression) this)))))))

;declaration
(define M-declare
  (lambda (expression state closures this break continue return throw)
    (cond
      ((contain? (variable expression) (list (current-state state))) (error 'redefiningerror))
      ((null? (assignment expression)) (cons (cons (cons (variable expression) (box 'notassigned)) (current-state state)) (the-rest-part state)))
      (else (cons (cons (cons (variable expression) (box (pass (value expression) state closures this break continue return throw '()))) (current-state state)) (the-rest-part state))))))


; M-integer maps expressions(including variables) to integer values
(define M-integer
  (lambda (expression state closures this break continue return throw)
    (cond
      ((number? expression) expression)
      ((contain? expression state) (M-value expression state))
      ((eq? (operator expression) '+) (+ (pass (leftoperand expression) state closures this break continue return throw '()) (pass (rightoperand expression) state closures this break continue return throw '())))
      ((and (eq? (operator expression) '-) (unary? expression))(- 0 (pass (leftoperand expression) state closures this break continue return throw  '())))      
      ((and (eq? (operator expression) '-)  (not (unary? expression))) (- (pass (leftoperand expression) state closures this break continue return throw '()) (pass (rightoperand expression) state closures this break continue return throw  '())))
      ((eq? (operator expression) '*) (* (pass (leftoperand expression) state closures this break continue return throw  '()) (pass (rightoperand expression) state closures this break continue return throw  '())))
      ((eq? (operator expression) '/) (quotient (pass (leftoperand expression) state closures this break continue return throw  '()) (pass (rightoperand expression) state closures this break continue return throw  '())))
      ((eq? (operator expression) '%) (remainder (pass (leftoperand expression) state closures this break continue return throw  '()) (pass (rightoperand expression) state closures this break continue return throw  '())))
      (else (error 'bad-operator)))))

(define M-value
  (lambda (var state)
      (if (contain? var (cons (car state) '()))
          (M-value-helper var (car state))
          (M-value var (cdr state)))))


;(try expression1 (catch(e) expression2) (finally expression3))
;(expression1 (catch(e) expression2) (finally expression3)))
(define ibreak-try
  (lambda (expression state closures this break continue return throw)
    (if(null? expression)
       state
       (ibreak-try (cdr expression) (pass (car expression) state closures this break continue return throw '()) closures this break continue return throw))))



;'((catch (e) expression2) (finally expression3))
(define final-exp
  (lambda(expression)
    (if(null? (cadr expression))
      null
      (cadr (cadr expression)))))


(define compile-value-helper
  (lambda ( field-list index)
    (cond
      ((zero? index) (unbox (cdar field-list)))
      (else (compile-value-helper (cdr field-list) (- index 1))))))

;lookup value
(define lookup-value
  (lambda (variable-name state this)
    (if (contain-helper variable-name (car state))
        (lookup-value-helper variable-name (car state))
        (lookup-value-helper variable-name (caddr this)))))

;helper of lookup value
(define lookup-value-helper
  (lambda (variable-name list)
    (cond
      ((null? list) error 'value-not-found)
      ((eq? (caar list) variable-name) (unbox (cdar list)))
      (else lookup-value-helper variable-name (cdr list)))))

;add the exception and its value to state
(define add-exception
  (lambda (exception exception-value state)
    (cons  (cons (cons exception exception-value) (car state))  (cdr state))))
 

;get the value for variable 'throw-value
(define get-throw-value
  (lambda (state)
    (cond
      ((null? state) '())
      ((contain? 'throw-value (list (car state))) (get-throw-value-helper (car state)))
      (else (get-throw-value (cdr state))))))

;helper method to get the value for variable 'throw-value
(define get-throw-value-helper
  (lambda (state)
    (cond
      ((null? state) '())
      ((eq? (car (car state)) 'throw-value) (unbox (cdr (car state))))
      (else (get-throw-value-helper (cdr state))))))



;check whether the value is valid
(define checkvalidvalue?
  (lambda (expression state)
    (cond
      ((number? expression) #f)
      ((list? expression) (and (checkvalidvalue? (car expression) state) (checkvalidvalue? (cdr expression) state)))
      ((boolean? expression) #f)
      ((contain? expression state) #f)
      (else #t))))

;assign
(define M-assign
  (lambda (expression state closures this break continue return throw)
    (if (list? (variable expression))
        (M-assign-this expression (list (get-this-field this)) closures this break continue return throw (pass (value expression) state closures this break continue return throw '()) state)
        (M-assign-in-state expression state closures this break continue return throw))))

;this's assign
(define M-assign-this
  (lambda (expression state closures this break continue return throw value original-state)
    (if (contain? (caddr (variable expression)) (list (get-this-field this)))
        (begin (set-this (get-this-field this) (caddr (variable expression)) value) original-state) 
        (error 'variable-not-in-this))))

;set this
(define set-this
  (lambda (this-field variable value)
    (if (eq? (caar this-field) variable)
        (set-box! (cdr (car this-field)) value)
        (set-this (cdr this-field) variable value))))
 

(define get-this-field
  (lambda (this)
    (caddr this)))

(define M-assign-in-state
  (lambda (expression state closures this break continue return throw)
    (cond
       ((not (contain? (variable expression) state)) (error 'variable-out-of-scope))
       ((checkvalidvalue? (value expression) state) (error 'assigned-value-not-valid))
       (else (update state (variable expression) (pass (value expression) state closures this break continue return throw '()) break continue return throw)))))


          
;remove the original value of the variable and add new value
(define update
  (lambda (state variable value break continue return throw)
    (cond
      ((null? state) state)
      ((contain? variable (cons (car state) '())) (cons (update-helper variable value (car state)) (cdr state)))
      (else (cons (car state) (update (cdr state) variable value break continue return throw))))))


(define update-helper
  (lambda (variable value state)
    (cond
      ((null? state) state)
      ((eq? variable (caar state)) (begin (set-box! (cdr (car state)) value) state))
      (else (cons (car state) (update-helper variable value (cdr state)))))))


(define not-contain?
  (lambda (state a)
    (cond
      ((null? state)       #t)
      ((eq? a (caar state)) #f)
      (else  (not-contain? (cdr state) a)))))



(define contain?
  (lambda (a state)
    (cond
      ((null? state) #f)
      ((contain-helper a (car state)) #t)
      (else (contain? a (cdr state))))))


(define contain-helper
  (lambda (a lis)
    (cond
      ((null? lis) #f)
      ((eq? a (car (car lis))) #t)
      (else (contain-helper a (cdr lis))))))


;M-if maps if expressions to expression
(define M-if
  (lambda (expression state closures this break continue return throw)
    (if (M-boolean (condition1 expression) state  closures this break continue return throw)
         (pass (truecase expression) state closures this break continue return throw '())
         (if (null? (cdddr expression))
             state
             (pass (falsecase expression) state closures this break continue return throw '())))))


;M-boolean
(define M-boolean
  (lambda (expression state closures this break continue return throw)
    (cond
      ((number? expression) expression)
      ((boolean? expression) expression)
      ((eq? expression 'true) #t)
      ((eq? expression 'false) #f)
      ((contain? expression state) (M-value expression state))
      ((eq? (operator expression) '!) (not ( pass (leftoperand expression) state closures this break continue return throw '())))
      ((eq? (operator expression) '==) (eq? ( pass (leftoperand expression) state closures this break continue return throw '()) (pass (rightoperand expression) state closures this break continue return throw '()) ))
      ((eq? (operator expression) '!=) (not (eq? (pass (leftoperand expression) state closures this break continue return throw '()) ( pass (rightoperand expression) state closures this break continue return throw '()))))
      ((eq? (operator expression) '<) (< (  pass (leftoperand expression) state closures this break continue return throw '()) ( pass (rightoperand expression) state closures this break continue return throw'()) ))
      ((eq? (operator expression) '>) (> ( pass (leftoperand expression) state closures this break continue return throw '()) ( pass (rightoperand expression) state closures this break continue return throw '())))
      ((eq? (operator expression) '<=) (<= ( pass (leftoperand expression) state closures this break continue return throw '() ) ( pass (rightoperand expression) state closures this  break continue return throw '())))
      ((eq? (operator expression) '>=) (>= ( pass (leftoperand expression) state closures this break continue return throw '()) ( pass (rightoperand expression) state closures this break continue return throw '())))
      ((eq? (operator expression) '||) (or ( pass (leftoperand expression) state closures this break continue return throw '()) ( pass (rightoperand expression) state closures this break continue return throw '())))
      ((eq? (operator expression) '&&) (and ( pass (leftoperand expression) state closures this break continue return throw '()) ( pass (rightoperand expression) state closures this break continue return throw'())))
      ((checkArith (operator expression)) (M-integer expression state closures this))
      (else error 'bad-operator))))



(define M-function
  (lambda (expression state closures this break continue return throw class-name)
    (cons (cons (cons (functionname expression) (append (list (parameter-and-body expression)) (cons class-name '()))) (current-state state)) (the-rest-part state))))

(define funname
  (lambda (expression)
    (caddr (cadr expression))))


(define interpret-command-funcall
  (lambda(expression state closures this break continue throw class-name)
    (call/cc (lambda(return)
               (ibreak-funcall expression state closures this break continue return throw class-name)))))


(define ibreak-funcall
  (lambda (expression state closures this break continue return throw class-name)
    (if(null? expression)
       state
       (ibreak-funcall (cdr expression) (pass (car expression) state closures this break continue return throw class-name)  closures this break continue return throw class-name))))


(define pbind
  (lambda (paramname paramvalue state closures this)
    (cons (pbind-helper paramname paramvalue state closures this) state)))
 

(define pbind-helper
  (lambda (paramname paramvalue state closures this)
    (cond
      ((and (null? paramname) (null? paramvalue)) '())
      ((or ( null? paramname) (null? paramvalue)) (error 'parameter-names-are-not-consistent-with-parameter-value))
      (else (cons (cons (car paramname) (box (pass (car paramvalue) state closures this error error error error '()))) (pbind-helper (cdr paramname) (cdr paramvalue) state closures this))))))



                                                   
(define get-closure
  (lambda (functionname lis)
    (cond
      ((null? lis) (error 'closure-not-found))
      ((eq? functionname (car (car lis))) (cdr (car lis)))
      (else (get-closure functionname (cdr lis))))))



(define get-layer
  (lambda(x state break)
    (cond
      ((null? state) '())
      ((eq? x (car (car state))) (break state))
      (else (get-layer x (cdr state) break)))))

(define state-function
  (lambda(x state this)
    (caddr (unbox (cdr (check-field-in-closure x state this))))))




(define checkArith
  (lambda (operatorexpression)
    (cond
      ((eq? operatorexpression '+) #t)
      ((eq? operatorexpression '-) #t)
      ((eq? operatorexpression '*) #t)
      ((eq? operatorexpression '/) #t)
      ((eq? operatorexpression '%) #t)
      (else #f))))

(define checkboolean
  (lambda (lis)
    (cond
      ((eq? (car lis) '!=) #t)
      ((eq? (car lis) '==) #t)
      ((eq? (car lis) '>) #t)
      ((eq? (car lis) '>=) #t)
      ((eq? (car lis) '<) #t)
      ((eq? (car lis) '<=) #t)
      ((eq? (car lis) '||) #t)
      ((eq? (car lis) '&&) #t)
      ((eq? (car lis) '!) #t)
      (else #f))))

(define unary?
  (lambda (expression)
     (null? (cddr expression))))

(define add-main-funcall
  (lambda (statement-list)
    (append statement-list (cons '(funcall (find main state)) '()))))

(define M-value-helper
  (lambda (var state)
    (cond
      ((null? state) (error 'variable-is-not-declared))
      ((eq? (caar state) var) (if (eq? (unbox (cdr (car state))) 'notassigned )
                                       (error 'using-before-assigning)
                                       (unbox (cdr (car state)))))
      (else (M-value-helper var (cdr state))))))

(define check-field-in-closure
  (lambda (name state this)
    (cond
      ((eq? name 'this) this)
      ((eq? name 'super) this)
      ((null? (check-field-in-closure-helper name (car state))) (check-field-in-closure name (cdr state) this))
      (else (check-field-in-closure-helper name (car state))))))

(define check-field-in-closure-helper
  (lambda (name state-list)
    (cond
      ((null? state-list) '())
      ((eq? name (caar state-list)) (unbox (cdar state-list)))
      (else (check-field-in-closure-helper name (cdr state-list))))))


(define lookup-function
  (lambda (name state-list)
    (cond
      ((null? state-list) '())
      ((eq? name (caar state-list)) (car state-list))
      (else (lookup-function name (cdr state-list))))))


(define get-runtime-type
  (lambda (name state this)
    (car (check-field-in-closure name state this))))

(define M-dot-function1
  (lambda (type class-closure function-name)
    (M-dot-function-helper type class-closure function-name)))

(define M-dot-function-helper
  (lambda (type class-closure function-name)
    (if (null? (lookup-function function-name (caddr (check-class type class-closure)) ))
        (M-dot-function1  ( cadr ( class-extension (check-class type class-closure))) class-closure function-name)
        (lookup-function function-name (caddr (check-class type class-closure))))))
    

(define M-new-helper
  (lambda (class closures)
    (cond
      ((null? closures) (error 'class-does-not-exist))
      ((eq? (caar closures) class) (inst (car closures) closures))
      (else (M-new-helper class (cdr closures))))))



(define inst
  (lambda (one-class closures)
    (append (cons (car one-class) (list (get-parent (cadr one-class)))) (list (get-all-fields (get-parent (cadr one-class)) one-class closures)))))



(define get-all-fields
  (lambda (parent one-class closures)
    (if (null? parent)
        (get-this-class-fields (caddr one-class) '())
        (append (get-all-fields (get-parent (cadr (find-class-closure-1 parent closures)))
                                 (find-class-closure-1 parent closures) closures) (get-this-class-fields (caddr one-class) '())))))

(define find-class-closure-1
  (lambda (class closures)
    (cond
      ((null? closures) (error 'class-does-not-exist))
      ((eq? (caar closures) class) (car closures))
      (else (find-class-closure-1 class (cdr closures))))))



(define get-this-class-fields
  (lambda (expression state)
    (if (null? expression)
        state
        (if (box? (cdr (car expression)))
            (get-this-class-fields (cdr expression) (cons (cons (caar expression) (box (unbox (cdar expression)))) state))
            (get-this-class-fields (cdr expression) state)))))

(define get-parent
  (lambda (expression)
    (if (null? expression)
        null
        (cadr expression))))

(define check-class
  (lambda (name state)
    (cond
      ((null? state) (error 'class-not-found))
      ((eq? name (caar state)) (car state))
      (else (check-class name (cdr state))))))



(define counter-index-helper
  (lambda (varaiblename fieldlist acc)
    (cond
    ((null? fieldlist) (error 'variable-not-found))
    ((and (eq? (caar fieldlist) varaiblename) (not (fcontain? varaiblename (cdr fieldlist)))) acc)
    (else (counter-index-helper varaiblename (cdr fieldlist) (+ acc 1))))))

(define fcontain?
  (lambda(variablename fieldlist)
    (cond
      ((null? fieldlist) #f)
      ((eq? variablename (caar fieldlist)) #t)
      (else (fcontain? variablename (cdr fieldlist))))))
    

(define find-class-and-parent-field
  (lambda(classname classclosure)
    (findfield (find-class-and-parent classname classclosure))))

(define find-class-and-parent
  (lambda(classname classclosure)
    (cond
      ((null? classclosure) '())
      ((eq? (caar classclosure) classname) (cons (car classclosure) (find-class-and-parent (get-parent (cadr (car classclosure))) (cdr classclosure))))
      (else (find-class-and-parent classname (cdr classclosure))))))

(define findfield
  (lambda(classandparentclosure)
    (cond
      ((null? classandparentclosure) '())
      (else (append (findfieldhelper (caddr (car classandparentclosure))) (findfield (cdr classandparentclosure)))))))

(define findfieldhelper
  (lambda(classclosurebody)
    (cond
      ((null? classclosurebody) '())
      ((box? (cdr (car classclosurebody))) (cons (car classclosurebody) (findfieldhelper (cdr classclosurebody))))
      (else (findfieldhelper (cdr classclosurebody))))))
