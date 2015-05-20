(in-package :user)

(load "procura.lisp")
(load "job-shop-problemas-modelos.lisp")

(defun iterative-sampling (problema)
	(let ((objectivo? (problema-objectivo? problema)))
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
(defun improved-lds(problema)
	(let ((objectivo? (problema-objectivo? problema))
		  (k 0)
		  (depth (total-tasks (problema-estado-inicial problema)))
		  ;TO REMOVE
		  (nos-gerados nil)
		  (nos-expandidos nil))

	(labels ((ilds (node k depth)
		(if (funcall objectivo? node)
			node
			(let ((sucessores (problema-gera-sucessores problema estado)))
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
		(if (not (null solucao)
			(return solucao)
			(incf k)))))))


(defun total-tasks (state)
	(let ((totalTasks 0))
		(dolist (job (job-shop-state-jobs state))
			(setf totalTasks (+ totalTasks (length (job-shop-job tasks)))))
		totalTasks))

(defun cria-estado-inicial (estado)
	(make-job-shop-state
		:taskSequence '()
		:machines.start.time (make-array (job-shop-problem-n.machines estado) :initial-element 0)
		:jobs (job-shop-problem-jobs estado)
		:jobs.start.time (make-array (job-shop-problem-n.jobs estado) :initial-element 0)))

;JobShop Operators
(defun dotask (state)
	(let ((sucessores '()))
		(dotimes (i (length (job-shop-state-jobs state)))
			(let ((job (nth i (job-shop-state-jobs state))))
				(when (not (null (job-shop-job-tasks job)))
					(let* (
						; copia do estado que ira passar para o proximo no
						(newState (copy-job-shop-state state))
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
						(setf (job-shop-state-taskSequence newState)
							(cons newTask (job-shop-state-taskSequence newState)))
						(setf sucessores (cons newState sucessores))))))
		sucessores))

(defun estado-objectivo (state)
	(dolist (job (job-shop-state-jobs state))
		(when (not (job-shop-job-tasks))
			(return-from estado-objectivo NIL)))
	t)

(defstruct job-shop-state
   taskSequence
   machines.start.time
   jobs
   jobs.start.time)

(setf a (make-job-shop-state
		:taskSequence '()
		:machines.start.time (make-array 2 :initial-element 0)
		:jobs (list (make-job-shop-job
			:job.nr 0
			:tasks (list 
				(make-job-shop-task :job.nr 0
 					:task.nr 0 :machine.nr 1 :duration 12 :start.time NIL)
				(make-job-shop-task :job.nr 0
 					:task.nr 1 :machine.nr 0 :duration 68 :start.time NIL)))
			(make-job-shop-job
				:job.nr 1
				:tasks (list
					(make-job-shop-task :job.nr 1
 					:task.nr 0 :machine.nr 1 :duration 5 :start.time NIL)
				(make-job-shop-task :job.nr 1
 					:task.nr 1 :machine.nr 0 :duration 5 :start.time NIL))))
		:jobs.start.time (make-array 2 :initial-element 0)))

(defun pop-task (state job.index)
	(setf (job-shop-job-tasks (nth job.index (job-shop-state-jobs state))) 
		(cdr (job-shop-job-tasks (nth job.index (job-shop-state-jobs state)))))
	state)

(defun copy-job-shop-state (state)
	(let ((taskSequence (copy-list (job-shop-state-taskSequence state)))
		  (jobs (copy-list (job-shop-state-jobs state))))
	(make-job-shop-state
		:taskSequence (mapcar #'copy-job-shop-task taskSequence)
		:machines.start.time (copy-array (job-shop-state-machines.start.time state))
		:jobs (mapcar #'copy-job-shop-job jobs)
		:jobs.start.time (copy-array (job-shop-state-jobs.start.time state)))))

(defun copy-job-shop-job (job)
	(let ((tasks (copy-list (job-shop-job-tasks job))))
		(make-job-shop-job
			:job.nr (job-shop-job-job.nr job)
			:tasks (mapcar #'copy-job-shop-task tasks))))
	

(defun copy-job-shop-task (task)
	(make-job-shop-task
		:job.nr (job-shop-task-job.nr task)
		:task.nr (job-shop-task-task.nr task)
		:machine.nr (job-shop-task-machine.nr task)
		:duration (job-shop-task-duration task)
		:start.time (job-shop-task-start.time task)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;RAINHAS


(defstruct posicao
	x
	y)

(defun estado-objectivo? (tabuleiro)
	(let ((nQueens 0)
		(foundQueen nil))
	(progn
		(dotimes (i (array-dimension tabuleiro 0))
			(progn
				(setf foundQueen nil)
				(dotimes (j (array-dimension tabuleiro 1))
					(when (equal (aref tabuleiro i j) "T")
						(progn
							(setf foundQueen 1)
							(incf nQueens)
							(return))))
				(when (not foundQueen)
					(return-from estado-objectivo? nil))))
		(= nQueens (array-dimension tabuleiro 0)))))

(defun ameaca? (rainha1-pos rainha2-pos)
	(or (= (posicao-x rainha1-pos) (posicao-x rainha2-pos))
		(= (posicao-y rainha1-pos) (posicao-y rainha2-pos))
		(= (- (posicao-x rainha1-pos) (posicao-y rainha1-pos)) (- (posicao-x rainha2-pos) (posicao-y rainha2-pos)))
		(= (+ (posicao-x rainha1-pos) (posicao-y rainha1-pos)) (+ (posicao-x rainha2-pos) (posicao-y rainha2-pos)))))

(defun imprime-tabuleiro (tabuleiro)
	(dotimes (i (array-dimension tabuleiro 0))
		(progn
			(format t "~%")
			(dotimes (j (array-dimension tabuleiro 1))
				(format t "~a "(aref tabuleiro i j))))))

;Heuristica - numero de casas livres para jogar a proxima rainha
(defun heuristica (tabuleiro)
	(let ((casas-atacadas 0)
		(rainhas '())
		(foundQueen nil)
		(startLine 0)
		(nlinhas (array-dimension tabuleiro 0)))

	(progn
		(when (estado-objectivo? tabuleiro)
			(return-from heuristica 0))

		;Procurar a linha a inserir
		(dotimes (i (array-dimension tabuleiro 0))
			(progn
				(setf foundQueen nil)
				(dotimes (j (array-dimension tabuleiro 1))
					(if (equal (aref tabuleiro i j) "T")
						(progn 
							(incf startLine)
							(setf rainhas (cons (make-posicao :x i :y j) rainhas))
							(setf foundQueen 1)
							(return))))
				(when (not foundQueen)
					(return))))
		
		;Contar o numero de casas livres a partir da linha
		(loop for i from startLine to (- nlinhas 1) do
			(dotimes (j (array-dimension tabuleiro 1))
				(dolist (rainha rainhas)
					(when (ameaca? (make-posicao :x i :y j) rainha)
						(progn
							(incf casas-atacadas)
							(return))))))
		(let ((casas-totais (* (- nlinhas startLine) (array-dimension tabuleiro 1))))
			(return-from heuristica (- casas-totais casas-atacadas))))))


;Operador
(defun coloca-rainha (tabuleiro)
	(let* ((rainhas '())
		(sucessores '())
		(linha-a-inserir 0)
		(foundQueen nil))

	(progn
		;Procurar a linha a inserir
		(dotimes (i (array-dimension tabuleiro 0))
			(progn
				(setf foundQueen nil)
				(dotimes (j (array-dimension tabuleiro 1))
					(if (equal (aref tabuleiro i j) "T")
						(progn 
							(incf linha-a-inserir)
							(setf rainhas (cons (make-posicao :x i :y j) rainhas))
							(setf foundQueen 1)
							(return))))
				(when (not foundQueen)
					(return))))
		;Procurar a coluna a inserir
		(if rainhas
			(dotimes (j (array-dimension tabuleiro 1))
				(progn
					(let ((ameaca nil))
						(dolist (rainha rainhas)
							(when (ameaca? (make-posicao :x linha-a-inserir :y j) rainha)
								(progn
									(setf ameaca 1)
									(return))))
						(when (not ameaca)
							(let ((tabuleiro-copia (copy-array tabuleiro)))
								(progn
									(setf (aref tabuleiro-copia linha-a-inserir j) "T")
									(setf sucessores (cons tabuleiro-copia sucessores))))))))
			(dotimes (j (array-dimension tabuleiro 1))
				(let ((tabuleiro-copia (copy-array tabuleiro)))
					(progn
						(setf (aref tabuleiro-copia linha-a-inserir j) "T")
						(setf sucessores (cons tabuleiro-copia sucessores))))))
		sucessores)))

(defun resolve-problema (estado-inicial procura-str)
	(let* ((operadores (list #'coloca-rainha))
		(problema (cria-problema estado-inicial operadores :objectivo? #'estado-objectivo? :heuristica #'heuristica)))
	(procura problema procura-str)))


;(resolve-problema (make-array '(20 20)) 'profundidade)

;(improved-lds (cria-problema (make-array '(4 4)) (list #'coloca-rainha) :objectivo? #'estado-objectivo? :heuristica #'heuristica))
;(iterative-sampling (cria-problema (make-array '(4 4)) (list #'coloca-rainha) :objectivo? #'estado-objectivo? :heuristica #'heuristica))