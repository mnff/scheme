

(define (log msg) (newline) (display msg) (newline))

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
  ((stack 'stack) value))

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

(define (make-label-entry label-name insts)
  (cons label-name insts))

(define (make-instruction text)
  (cons text '()))

(define (set-instruction-execution-proc! inst proc)
  (set-cdr! inst proc))

(define (instruction-text inst)
  (car inst))

(define (assemble controller-text machine)
  (extract-labels controller-text
    (lambda (insts labels)
      (update-insts! insts labels machine)
      insts)))

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

(define (label-exp? exp)
  (tagged-list? exp 'label))

(define (register-exp? exp)
  (tagged-list? exp 'reg))

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

(define (constant-exp-value exp)
  (cadr exp))

(define (label-exp-label exp)
  (cadr exp))

(define (register-exp-reg exp)
  (cadr exp))

(define (stack-exp-reg exp)
  (cadr exp))

(define (operation-exp? exp)
  (and (pair? exp) (tagged-list? (car exp) 'op)))

(define (operation-exp-op exp)
  (cadr (car exp)))

(define (operation-exp-operands exp)
  (cdr exp))

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