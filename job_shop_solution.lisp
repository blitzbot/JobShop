;(in-package :user)

(load (compile-file "procura.lisp"))
(load (compile-file "job-shop-problemas-modelos.lisp"))

(defun sondagem-iterativa (problema)
	"Algoritmo de sondagem iterativa
	retorna primeira solucao encontrada"
	(let ((objectivo? (problema-objectivo? problema))
		  (*nos-gerados* 0)
		  (*nos-expandidos* 0)
		  (solucao nil))
		;procura sonda
		(labels ((procura-sonda (estado)
			; se chegamos a funcao objectivo devolvemos o estado
			; caso contrario chamamos a funcao recursivamento se nao for no folha
			(if (funcall objectivo? estado)
				estado
				(let ((sucessores (problema-gera-sucessores problema estado)))
					; se estivermos num no' folha, nao tiver sucessores, devolve nil
					; caso contrario procura num no' filho num ramo aleatorio
					(if (null sucessores)
						nil
						(procura-sonda (nth (random (length sucessores)) sucessores)))))))
		(loop
			(setf solucao (procura-sonda (problema-estado-inicial problema)))
			(when (not (null solucao))
				(return solucao))))))

;Paper: http://aaaipress.org/Papers/AAAI/1996/AAAI96-043.pdf
(defun improved-lds(problema depth)
	"Algoritmo ILDS"
	(let ((objectivo? (problema-objectivo? problema))
		  (k 0)
		  ;(depth (total-tasks (problema-estado-inicial problema)))
		  (*nos-gerados* 0)
		  (*nos-expandidos* 0)
		  (solucao nil))

	(labels ((ilds (estado k depth)
		(if (or (null estado) (funcall objectivo? estado))
			estado
			(let ((sucessores (problema-gera-sucessores problema estado)))
				;(format t "~S~%" sucessores)
				(setf sucessores (ordena-sucessores sucessores (problema-heuristica problema)))
				
				(when (> depth k)
					(progn
						(setf solucao (ilds (car sucessores) k (- depth 1)))
						(when (not (null solucao))
							(return-from ilds solucao)))
				(when (> k 0)
					(dolist (sucessor (cdr sucessores))
						(progn
							(setf solucao (ilds sucessor (- k 1) (- depth 1)))
							(when (not (null solucao))
								(return-from ilds solucao))))))))))
	(loop
		(setf solucao (ilds (problema-estado-inicial problema) k depth))
		(if (not (null solucao))
			(return solucao)
			(incf k))))))

(defun ordena-sucessores (sucessores heuristica)
	(sort sucessores #'(lambda (x y) (< (funcall heuristica x) (funcall heuristica y)))))


(defun total-tasks (state)
	(let ((totalTasks 0))
		(dolist (job (job-shop-state-jobs state))
			(setf totalTasks (+ totalTasks (length (job-shop-job-tasks job)))))
		totalTasks))

;JobShop Operators
(defun operador (state)
	(let ((sucessores '()))
		(dotimes (i (length (job-shop-state-jobs state)))
			(let ((job (nth i (job-shop-state-jobs state))))
				(when (not (null (job-shop-job-tasks job)))
					(let* (
						; copia do estado que ira passar para o proximo no
						(newState (copia-job_shop_state state))
						; lista de tarefas actuais
						(newStateJob (nth i (job-shop-state-jobs state)))
						; tarefa a colocar na sequencia de tarefas
						(newTask (car (job-shop-job-tasks newStateJob)))
						(m.start.time (job-shop-state-machines.start.time newState))
						(jobs.start.time (job-shop-state-jobs.start.time newState))
						; qual e' o tempo de inicio?
						(start.time (max
							(aref m.start.time (job-shop-task-machine.nr newTask))
							(aref jobs.start.time (job-shop-task-job.nr newTask))))
						(new.time (+ start.time (job-shop-task-duration newTask))))
						; remover primeira tarefa do job
						(setf newState (pop-task newState i))
						(setf (job-shop-task-start.time newTask) start.time)
						(setf (aref m.start.time (job-shop-task-machine.nr newTask)) new.time)
						(setf (aref jobs.start.time (job-shop-task-job.nr newTask)) new.time)
						; TODO: append em vez de cons?
						(setf (aref (job-shop-state-taskSequence newState) (job-shop-task-job.nr newTask))
							(nconc (aref (job-shop-state-taskSequence newState) (job-shop-task-job.nr newTask)) (list newTask)))
						(setf sucessores (cons newState sucessores))))))
		sucessores))

(defun estado-objectivo (state)
	(dolist (job (job-shop-state-jobs state))
		(when (not (null (job-shop-job-tasks job)))
			(return-from estado-objectivo NIL)))
	t)

(defun heuristica (state)
	(let ((max 0))
		(dotimes (i (array-dimension (job-shop-state-machines.start.time state) 0))
			(let ((value (aref (job-shop-state-machines.start.time state) i)))
				(when (> value max)
					(setf max value))))
		max))

(defstruct job-shop-state
   taskSequence
   machines.start.time
   jobs.start.time
   jobs)

(setf a (make-job-shop-problem
    :name "mt06"
    :n.jobs 2
    :n.machines 2
    :jobs (list (MAKE-JOB-SHOP-JOB :JOB.NR 0
				   :TASKS (list (MAKE-JOB-SHOP-TASK :JOB.NR 0 :TASK.NR 0 :MACHINE.NR 1 :DURATION 12 :START.TIME NIL)
						(MAKE-JOB-SHOP-TASK :JOB.NR 0 :TASK.NR 1 :MACHINE.NR 0 :DURATION 68 :START.TIME NIL)))
		(MAKE-JOB-SHOP-JOB :JOB.NR 1
				   :TASKS (list (MAKE-JOB-SHOP-TASK :JOB.NR 1 :TASK.NR 0 :MACHINE.NR 0 :DURATION 5 :START.TIME NIL)
						(MAKE-JOB-SHOP-TASK :JOB.NR 1 :TASK.NR 1 :MACHINE.NR 1 :DURATION 5 :START.TIME NIL))))))

(setf b (make-job-shop-problem
    :name "mt06"
    :n.jobs 3
    :n.machines 6
    :jobs (list (MAKE-JOB-SHOP-JOB :JOB.NR 0
				   :TASKS '())
				(MAKE-JOB-SHOP-JOB :JOB.NR 1
				   :TASKS '())
				(MAKE-JOB-SHOP-JOB :JOB.NR 2
				   :TASKS '()))))

(defun cria-estado (problema)
	(make-job-shop-state
		:taskSequence (make-array (job-shop-problem-n.jobs problema) :initial-element '())
		:machines.start.time (make-array (job-shop-problem-n.machines problema) :initial-element 0)
		:jobs.start.time (make-array (job-shop-problem-n.jobs problema) :initial-element 0)
		:jobs (job-shop-problem-jobs problema)))

(defun pop-task (state job.index)
	(setf (job-shop-job-tasks (nth job.index (job-shop-state-jobs state))) 
		(cdr (job-shop-job-tasks (nth job.index (job-shop-state-jobs state)))))
	state)

(defun copia-job_shop_state (state)
	(let ((jobs (copy-list (job-shop-state-jobs state))))
		(make-job-shop-state
			:taskSequence (copia-job_task_sequence (job-shop-state-taskSequence state))
			:machines.start.time (copy-array (job-shop-state-machines.start.time state))
			:jobs (mapcar #'copia-job_shop_job jobs)
			:jobs.start.time (copy-array (job-shop-state-jobs.start.time state)))))

(defun copia-job_shop_job (job)
	(let ((tasks (copy-list (job-shop-job-tasks job))))
		(make-job-shop-job
			:job.nr (job-shop-job-job.nr job)
			:tasks (mapcar #'copia-job_shop_task tasks))))

(defun copia-job_task_sequence (taskSequence)
	(let ((taskSequenceCopy (copy-array taskSequence)))
		(dotimes (i (array-dimension taskSequenceCopy 0))
			(setf (aref taskSequenceCopy i) (mapcar #'copia-job_shop_task (aref taskSequenceCopy i))))
		taskSequenceCopy))

(defun copia-job_shop_task (task)
	(make-job-shop-task
		:job.nr (job-shop-task-job.nr task)
		:task.nr (job-shop-task-task.nr task)
		:machine.nr (job-shop-task-machine.nr task)
		:duration (job-shop-task-duration task)
		:start.time (job-shop-task-start.time task)))

;(resolve-problema (make-array '(20 20)) 'profundidade)

;(improved-lds (cria-problema (make-array '(4 4)) (list #'coloca-rainha) :objectivo? #'estado-objectivo? :heuristica #'heuristica))
;(sondagem-iterativa (cria-problema (cria-estado a) (list #'operador) :objectivo? #'estado-objectivo))
;(improved-lds (cria-problema (cria-estado a) (list #'operador) :objectivo? #'estado-objectivo :heuristica #'heuristica) 4)