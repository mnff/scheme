

(define true #t)

(define false #f)


(define apply-in-underlying-scheme apply)


(define (tagged-list? exp tag)
  (if (pair? exp)
  	(eq? (car exp) tag)
  	false))


(define (make-stack)
  (let ((s '())
  			(max-depth 0)
  			(current-depth 0)
  			(number-pushes 0))
		(define (push x)
		  (set! s (cons x s))
			(set! number-pushes (+ 1 number-pushes))
			(set! current-depth (+ 1 current-depth))
			(set! max-depth (max max-depth current-depth)))
		(define (pop)
		  (if (null? s)
		  		(error "Empty stack -- POP" "")
		  		(let ((top (car s)))
		  			(set! s (cdr s))
		  			(set! current-depth (- current-depth 1))
		  			top)))
		(define (initialize)
			(set! s '())
		  (set! max-depth 0)
			(set! current-depth 0)
			(set! number-pushes 0)
			'done)
		(define (print-statistics)
		  (newline)
			(display (list 'total-pushes '= number-pushes 'max-depth '= max-depth))
			(newline))
		(define (dispatch message)
		  (cond ((eq? message 'push) push)
		  			((eq? message 'pop) (pop))
		  			((eq? message 'initialize) (initialize))
		  			((eq? message 'print-statistics) (print-statistics))
		  			(else
		  				(error "Unknow request -- STACK" message))))
		dispatch))

(define (pop stack)
  (stack 'pop))

(define (push stack value)
  ((stack 'push) value))


(define (make-register name)
	(let ((contents '*unassigned*))
		(define (set value)
		  (set! contents value))
		(define (dispatch message)
			(cond ((eq? message 'get) contents)
						((eq? message 'set) set)
						(else
							(error "Unknow request -- REGISTER" message))))
		dispatch))

(define (get-contents register)
  (register 'get))

(define (set-contents! register value)
  ((register 'set) value))

(define (get-register machine register-name)
  ((machine 'get-register) register-name))

(define (set-register-contents! machine register-name value)
  (set-contents! (get-register machine register-name) value)
	'done)

(define (get-register-contents machine register-name)
  (get-contents (get-register machine register-name)))


(define (make-instruction text)
  (cons text '()))

(define (instruction-text inst)
  (car inst))

(define (set-instruction-execution-proc! inst proc)
  (set-cdr! inst proc))

(define (instruction-execution-proc inst)
  (cdr inst))


(define (make-new-machine)
  (let ((pc (make-register 'pc))
  			(flag (make-register 'flag))
  			(stack (make-stack))
  			(the-instruction-sequence '()))

  	(let ((the-ops (list (list 'initialize-stack
  															(lambda () (stack 'initialize)))
  												(list 'print-stack-statistics
  															(lambda () (stack 'print-statistics)))))
  				(register-table (list (list 'pc pc) (list 'flag flag))))

  		(define (allocate-register name)
  		  (if (assoc name register-table)
  		  		(error "Mutiple register" name)
  		  		(set! register-table (cons (list name (make-register name)) register-table)))
  					'register-allocated)

  		(define (lookup-register name)
  			(let ((val (assoc name register-table)))
  				(if val
  				    (cadr val)
  				    (error "Unknow register" name))))

  		(define (execute)
  		  (let ((insts (get-contents pc)))
  		  	(if (null? insts)
  		  			'done
  		  			(begin
  		  				((instruction-execution-proc (car insts)))
  		  				(execute)))))

  		(define (dispatch message)
  		  (cond ((eq? message 'start)
  		  				(set-contents! pc the-instruction-sequence)
  		  				(execute))
  						((eq? message 'install-instruction-sequence)
  							(lambda (seq) (set! the-instruction-sequence seq)))
  						((eq? message 'allocate-register) allocate-register)
  						((eq? message 'get-register) lookup-register)
  						((eq? message 'install-operations)
  							(lambda (ops) (set! the-ops (append the-ops ops))))
  						((eq? message 'stack) stack)
  						((eq? message 'operations) the-ops)
  						(else (error "Unknow request -- MACHINE" message))))

  		dispatch)))

(define (start machine)
  (machine 'start))


(define (assemble controller-text machine)
  (extract-labels controller-text
    (lambda (insts labels)
      (update-insts! insts labels machine)
      insts)))

(define (make-label-entry label-name insts)
  (cons label-name insts))

;建立指令中的标签到指令序列的映射，方便后续根据标签跳转到对应的指令序列
(define (extract-labels text receive)
  (if (null? text)
      (receive '() '())
      (extract-labels (cdr text)
       (lambda (insts labels)
         (let ((next-inst (car text)))
           (if (symbol? next-inst)
               (receive insts
                        (cons (make-label-entry next-inst
                                                insts)
                              labels))
               (receive (cons (make-instruction next-inst)
                              insts)
                        labels)))))))

;把指令替换为过程
(define (update-insts! insts labels machine)
  (let ((pc (get-register machine 'pc))
        (flag (get-register machine 'flag))
        (stack (machine 'stack))
        (ops (machine 'operations)))
    (for-each
     (lambda (inst)
       (set-instruction-execution-proc!
        inst
        (make-execution-procedure
         (instruction-text inst) labels machine
         pc flag stack ops)))
     insts)))

(define (assign-reg-name inst)
  (cadr inst))

(define (assign-value-exp inst)
  (cddr inst))

(define (constant-exp? exp)
  (tagged-list? exp 'const))

(define (constant-exp-value exp)
  (cadr exp))

(define (label-exp? exp)
  (tagged-list? exp 'label))

(define (label-exp-label exp)
  (cadr exp))

(define (register-exp? exp)
  (tagged-list? exp 'reg))

(define (register-exp-reg exp)
  (cadr exp))

(define (lookup-prim symbol operations)
  (let ((val (assoc symbol operations)))
    (if val
        (cadr val)
        (error "Unknow operation -- ASSEMBLE" symbol))))

(define (lookup-label labels label-name)
  (let ((val (assoc label-name labels)))
    (if val
        (cdr val)
        (error "Unknow label -- ASSEMBLE" label-name))))

(define (operation-exp? exp)
  (and (pair? exp) (tagged-list? (car exp) 'op)))

(define (operation-exp-op exp)
  (cadr (car exp)))

(define (operation-exp-operands exp)
  (cdr exp))

(define (stack-exp-reg exp)
  (cadr exp))

(define (branch-dest exp)
  (cadr exp))

(define (goto-dest exp)
  (cadr exp))

(define (advance-pc pc)
  (set-contents! pc (cdr (get-contents pc))))

(define (test-condition inst)
  (cdr inst))

(define (perform-action inst)
  (cdr inst))

(define (make-primitive-exp exp machine labels)
  (cond ((constant-exp? exp)
          (let ((c (constant-exp-value exp)))
            (lambda () c)))
        ((label-exp? exp)
          (let ((insts (lookup-label labels (label-exp-label exp))))
            (lambda () insts)))
        ((register-exp? exp)
          (let ((r (get-register machine (register-exp-reg exp))))
            (lambda () (get-contents r))))
        (else (error "Unknow expression type -- ASSEMBLE" exp))))

(define (make-operation-exp exp machine labels operations)
  (let ((op (lookup-prim (operation-exp-op exp) operations))
        (args (map (lambda (e) (make-primitive-exp e machine labels))
                   (operation-exp-operands exp))))
    (lambda () (apply op (map (lambda (arg) (arg)) args)))))

(define (make-execution-procedure inst labels machine pc flag stack ops)
  (cond ((tagged-list? inst 'assign)
         (make-assign inst machine labels ops pc))
        ((tagged-list? inst 'test)
         (make-test inst machine labels ops flag pc))
        ((tagged-list? inst 'branch)
         (make-branch inst machine labels flag pc))
        ((tagged-list? inst 'goto)
         (make-goto inst machine labels pc))
        ((tagged-list? inst 'save)
         (make-save inst machine stack pc))
        ((tagged-list? inst 'restore)
         (make-restore inst machine stack pc))
        ((tagged-list? inst 'perform)
         (make-perform inst machine labels ops pc))
        (else (error "Unknow instruction type -- ASSEMBLE" inst))))

(define (make-assign inst machine labels ops pc)
  (let ((target (get-register machine (assign-reg-name inst)))
        (value-exp (assign-value-exp inst)))
    (let ((value-proc (if (operation-exp? value-exp)
                          (make-operation-exp value-exp machine labels ops)
                          (make-primitive-exp (car value-exp) machine labels))))
      (lambda ()
        (set-contents! target (value-proc))
        (advance-pc pc)))))

(define (make-test inst machine labels ops flag pc)
  (let ((condition-exp (test-condition inst)))
    (if (operation-exp? condition-exp)
        (let ((proc (make-operation-exp condition-exp machine labels ops)))
          (lambda ()
            (set-contents! flag (proc))
            (advance-pc pc)))
        (error "Bad Test instuction -- ASSEMBLE" inst))))

(define (make-branch inst machine labels flag pc)
  (let ((dest (branch-dest inst)))
    (if (label-exp? dest)
        (let ((insts (lookup-label labels (label-exp-label dest))))
          (lambda ()
            (if (get-contents flag)
                (set-contents! pc insts)
                (advance-pc pc))))
        (error "Bad Branch instuction -- ASSEMBLE" inst))))

(define (make-goto inst machine labels pc)
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts
                  (lookup-label labels
                                (label-exp-label dest))))
            (lambda () (set-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg
                  (get-register machine
                                (register-exp-reg dest))))
            (lambda () (set-contents! pc (get-contents reg)))))
          (else (error "Bad Goto instuction -- ASSEMBLE" inst)))))

(define (make-save inst machine stack pc)
  (lambda ()
    (push stack (get-register-contents machine (stack-exp-reg inst)))
    (advance-pc pc)))

(define (make-restore inst machine stack pc)
  (lambda ()
    (set-register-contents! machine (stack-exp-reg inst) (pop stack))
    (advance-pc pc)))

(define (make-perform inst machine labels ops pc)
  (let ((action (perform-action inst)))
    (if (operation-exp? action)
        (let ((action-proc (make-operation-exp action machine labels ops)))
          (lambda ()
            (action-proc)
            (advance-pc pc)))
        (error "Bad Perform instuction -- ASSEMBLE" inst))))

(define (make-machine register-names ops controller-text)
  (let ((machine (make-new-machine)))
    (for-each (lambda (register-name)
                      ((machine 'allocate-register) register-name))
              register-names)
    ((machine 'install-operations) ops)
    ((machine 'install-instruction-sequence) (assemble controller-text machine))
    machine))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;计算gcd的机器;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (remainder n d) (if (< n d) n (remainder (- n d) d)))

(define gcd-machine
  (make-machine
   '(a b t)
   (list (list 'rem remainder) (list '= =))
   '(test-b
       (test (op =) (reg b) (const 0))
       (branch (label gcd-done))
       (assign t (op rem) (reg a) (reg b))
       (assign a (reg b))
       (assign b (reg t))
       (goto (label test-b))
     gcd-done)))

;(set-register-contents! gcd-machine 'a 100)
;(set-register-contents! gcd-machine 'b 200)
;(gcd-machine 'start)
;(get-register-contents gcd-machine 'a)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;scheme脚本解释器;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;基本操作
(define (true? x)
  (not (eq? x false)))

(define (false? x)
  (eq? x false))


(define (prompt-for-input string)
  (newline)
  (newline)
  (newline)
  (display string)
  (newline))

(define (prompt-for-output string)
  (newline)
  (display string)
  (newline))

(define (print-object object)
  (cond ((compound-procedure? object)
         (display (list 'compound-procedure
                        (procedure-parameters object)
                        (procedure-body object))))
        ((compiled-procedure? object)
         (display '<compiled-procedure>))
        (else (display object))))


(define (self-evaluating? exp)
  (cond ((number? exp) true)
        ((string? exp) true)
        (else false)))


(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp)
  (cadr exp))


(define (variable? exp)
  (symbol? exp))


(define (assignment? exp)
  (tagged-list? exp 'set!))

(define (assignment-variable exp)
  (cadr exp))

(define (assignment-value exp)
  (caddr exp))


(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (lambda? exp)
  (tagged-list? exp 'lambda))

(define (lambda-parameters exp)
  (cadr exp))

(define (lambda-body exp)
  (cddr exp))


(define (if? exp)
  (tagged-list? exp 'if))

(define (if-predicate exp)
  (cadr exp))

(define (if-then exp)
  (caddr exp))

(define (if-else exp)
  (cadddr exp))


(define (begin? exp)
  (tagged-list? exp 'begin))

(define (begin-actions exp)
  (cdr exp))


(define (last-exp? exps)
  (null? (cdr exps)))

(define (first-exp exps)
  (car exps))

(define (rest-exps exps)
  (cdr exps))


(define (application? exp)
  (pair? exp))

(define (operator exp)
  (car exp))

(define (operands exp)
  (cdr exp))

(define (no-operands? exp)
  (null? exp))

(define (first-operand exp)
  (car exp))

(define (rest-operands exp)
  (cdr exp))

(define (last-operand? exp)
  (null? (cdr exp)))


;基本变量
(define primitive-variables
  (list (list 'true true)
        (list 'false false)))

;基本运算符
(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list '+ +)
        (list 'list list)
        (list '= =)
        (list '- -)
        (list '* *)
        (list '< <)
        (list '> >)
        ))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-object)
  (map (lambda (proc) (list 'primitive (cadr proc))) primitive-procedures))

(define (primitive-implementation proc)
  (cadr proc))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme (primitive-implementation proc) args))


(define the-empty-environment '())

(define (enclosing-environment env)
  (cdr env))

(define (make-frame vars vals)
  (cons vars vals))

(define (first-frame env)
  (car env))

(define (frame-variables frame)
  (car frame))

(define (frame-values frame)
  (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))


(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp) (cddr exp))))

(define (do-define var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (if (null? vars)
          (add-binding-to-frame! var val frame)
          (if (eq? var (car vars))
              (set-car! vals val)
              (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame) (frame-values frame))))


(define (extend-environment vars vals env)
  (if (= (length vars) (length vals))
    (cons (make-frame vars vals) env)
    (if (< (length vars) (length vals))
        (error "Too many arguments supplied" vars vals)
        (error "Too few arguments supplied" vars vals))))

(define (init-global-environment)
  (let ((env (extend-environment (primitive-procedure-names)
                                 (primitive-procedure-object)
                                 the-empty-environment)))
    (for-each (lambda (x)
                      (do-define (car x) (cadr x) env))
              primitive-variables)
    env))

(define the-global-environment (init-global-environment))

(define (get-global-environment)
  the-global-environment)


(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame) (frame-values frame)))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame) (frame-values frame)))))
  (env-loop env))


(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (compound-procedure? proc)
  (tagged-list? proc 'procedure))

(define (procedure-parameters proc)
  (cadr proc))

(define (procedure-body proc)
  (caddr proc))

(define (procedure-env proc)
  (cadddr proc))


(define (make-compiled-procedure entry env)
  (list 'compiled-procedure entry env))

(define (compiled-procedure? proc)
  (tagged-list? proc 'compiled-procedure))

(define (compiled-procedure-entry proc)
  (cadr proc))

(define (compiled-procedure-env proc)
  (caddr proc))


(define (empty-arglist)
  '())

(define (adjoin-arg arg arglist)
  (append arglist (list arg)))


(define interpreter-operations
  (list (list 'list list)
        (list 'cons cons)
        (list 'false? false?)
        (list 'true? true?)
        (list 'read read)
        (list 'apply-in-underlying-scheme apply-in-underlying-scheme)

        (list 'prompt-for-input prompt-for-input)
        (list 'prompt-for-output prompt-for-output)
        (list 'print-object print-object)

        (list 'tagged-list? tagged-list?)

        (list 'self-evaluating? self-evaluating?)

        (list 'quoted? quoted?)
        (list 'text-of-quotation text-of-quotation)
        
        (list 'variable? variable?)

        (list 'assignment? assignment?)
        (list 'assignment-variable assignment-variable)
        (list 'assignment-value assignment-value)

        (list 'definition? definition?)
        (list 'definition-variable definition-variable)
        (list 'definition-value definition-value)
        (list 'do-define do-define)

        (list 'lambda? lambda?)
        (list 'lambda-parameters lambda-parameters)
        (list 'lambda-body  lambda-body)

        (list 'if? if?)
        (list 'if-predicate if-predicate)
        (list 'if-then if-then)
        (list 'if-else if-else)

        (list 'begin? begin?)
        (list 'begin-actions begin-actions)

        (list 'last-exp? last-exp?)
        (list 'first-exp first-exp)
        (list 'rest-exps rest-exps)

        (list 'application? application?)
        (list 'operator operator)
        (list 'operands operands)
        (list 'no-operands? no-operands?)
        (list 'first-operand first-operand)
        (list 'rest-operands rest-operands)
        (list 'last-operand? last-operand?)

        (list 'lookup-variable-value lookup-variable-value)
        (list 'set-variable-value! set-variable-value!)

        (list 'get-global-environment get-global-environment)
        (list 'extend-environment extend-environment)

        (list 'primitive-procedure? primitive-procedure?)
        (list 'apply-primitive-procedure apply-primitive-procedure)

        (list 'compound-procedure? compound-procedure?)
        (list 'make-procedure make-procedure)
        (list 'procedure-parameters procedure-parameters)
        (list 'procedure-body procedure-body)
        (list 'procedure-env procedure-env)

        (list 'compiled-procedure? compiled-procedure?)
        (list 'make-compiled-procedure make-compiled-procedure)
        (list 'compiled-procedure-entry compiled-procedure-entry)
        (list 'compiled-procedure-env compiled-procedure-env)

        (list 'empty-arglist empty-arglist)
        (list 'adjoin-arg adjoin-arg)
  )
)

(define interpreter-reg-names '(exp env val proc argl continue unev))

(define interpreter-text
  '(
    read-eval-print-loop
      (perform (op initialize-stack))
      (perform (op prompt-for-input) (const "输入要求值的表达式:"))
      (assign exp (op read))
      (assign env (op get-global-environment))
      (assign continue (label print-result))
      (goto (label eval-dispatch))

    print-result
      (perform (op prompt-for-output) (const "表达式求值结果:"))
      (perform (op print-object) (reg val))
      (goto (label read-eval-print-loop))

    unkown-expression-type
      (perform (op prompt-for-output) (const "不支持这种表达式:"))
      (goto (label read-eval-print-loop))

    eval-dispatch
      (test (op self-evaluating?) (reg exp))
      (branch (label eval-self-evaluating))

      (test (op variable?) (reg exp))
      (branch (label eval-variable))

      (test (op quoted?) (reg exp))
      (branch (label eval-quote))

      (test (op assignment?) (reg exp))
      (branch (label eval-assignment))

      (test (op definition?) (reg exp))
      (branch (label eval-definition))

      (test (op if?) (reg exp))
      (branch (label eval-if))

      (test (op lambda?) (reg exp))
      (branch (label eval-lambda))

      (test (op begin?) (reg exp))
      (branch (label eval-begin))

      (test (op application?) (reg exp))
      (branch (label eval-application))

      (goto (label unkown-expression-type))

    eval-self-evaluating
      (assign val (reg exp))
      (goto (reg continue))

    eval-variable
      (assign val (op lookup-variable-value) (reg exp) (reg env))
      (goto (reg continue))

    eval-quote
      (assign val (op text-of-quotation) (reg exp))
      (goto (reg continue))

    eval-assignment
      (assign unev (op assignment-variable) (reg exp))
      (save unev)
      (save env)
      (save continue)

      (assign continue (label eval-assignment-1))
      (assign exp (op assignment-value) (reg exp))
      (goto (label eval-dispatch))

    eval-assignment-1
      (restore continue)
      (restore env)
      (restore unev)

      (perform (op set-variable-value!) (reg unev) (reg val) (reg env))
      (assign val (const ok))
      (goto (reg continue))

    eval-definition
      (assign unev (op definition-variable) (reg exp))
      (save unev)
      (save env)
      (save continue)

      (assign continue (label eval-definition-1))
      (assign exp (op definition-value) (reg exp))
      (goto (label eval-dispatch))

    eval-definition-1
      (restore continue)
      (restore env)
      (restore unev)

      (perform (op do-define) (reg unev) (reg val) (reg env))
      (assign val (const ok))
      (goto (reg continue))

    eval-if
      (save exp)
      (save env)
      (save continue)

      (assign continue (label eval-if-decide))
      (assign exp (op if-predicate) (reg exp))
      (goto (label eval-dispatch))

    eval-if-decide
      (restore continue)
      (restore env)
      (restore exp)

      (test (op false?) (reg val))
      (branch (label eval-if-else))

    eval-if-then
      (assign exp (op if-then) (reg exp))
      (goto (label eval-dispatch))

    eval-if-else
      (assign exp (op if-else) (reg exp))
      (goto (label eval-dispatch))

    eval-lambda
      (assign unev (op lambda-parameters) (reg exp))
      (assign val (op lambda-body) (reg exp))
      (assign val (op make-procedure) (reg unev) (reg val) (reg env))
      (goto (reg continue))

    eval-begin
      (assign unev (op begin-actions) (reg exp))
      (save continue)
      (goto (label eval-sequence))

    eval-sequence
      (assign exp (op first-exp) (reg unev))

      (test (op last-exp?) (reg unev))
      (branch (label eval-sequence-last-exp))

      (save unev)
      (save env)
      (assign continue (label eval-sequence-continue))
      (goto (label eval-dispatch))

    eval-sequence-continue
      (restore env)
      (restore unev)
      (assign unev (op rest-exps) (reg unev))
      (goto (label eval-sequence))

    eval-sequence-last-exp
      (restore continue)
      (goto (label eval-dispatch))

    eval-application
      (save continue)
      (save env)
      (assign unev (op operands) (reg exp))
      (save unev)
      (assign exp (op operator) (reg exp))
      (assign continue (label eval-application-operator))
      (goto (label eval-dispatch))

    eval-application-operator
      (restore unev)
      (restore env)
      (assign argl (op empty-arglist))
      (assign proc (reg val))
      (test (op no-operands?) (reg unev))
      (branch (label eval-do-application))
      (save proc)

    eval-application-operands
      (assign exp (op first-operand) (reg unev))
      (assign unev (op rest-operands) (reg unev))
      (assign continue (label eval-application-operands-continue))

      (save env)
      (save unev)
      (save argl)

      (goto (label eval-dispatch))

    eval-application-operands-continue
      (restore argl)
      (restore unev)
      (restore env)
      (assign argl (op adjoin-arg) (reg val) (reg argl))

      (test (op no-operands?) (reg unev))
      (branch (label eval-application-last-operand))
      (goto (label eval-application-operands))

    eval-application-last-operand
      (restore proc)
      (goto (label eval-do-application))

    eval-do-application
      (test (op primitive-procedure?) (reg proc))
      (branch (label eval-primitive-procedure))

      (test (op compound-procedure?) (reg proc))
      (branch (label eval-compound-procedure))

    eval-primitive-procedure
      (assign val (op apply-primitive-procedure) (reg proc) (reg argl))
      (restore continue)
      (goto (reg continue))

    eval-compound-procedure
      (assign unev (op procedure-parameters) (reg proc))
      (assign env (op procedure-env) (reg proc))
      (assign env (op extend-environment) (reg unev) (reg argl) (reg env))
      (assign unev (op procedure-body) (reg proc))
      (goto (label eval-sequence))
    ))

(define interpreter
  (make-machine
    interpreter-reg-names
    interpreter-operations
    interpreter-text))

;可以在控制台试试解释器是否能工作了
;(start interpreter)
;(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) ;计算斐波拉切数列
;(define (factorial n) (if (= n 1) 1 (* (factorial (- n 1)) n))) ;计算阶乘