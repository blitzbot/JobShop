(in-package :user)

(load (compile-file "procura.lisp"))
(load (compile-file "job-shop-problemas-modelos.lisp"))

(defstruct job-shop-state
   taskSequence
   machines.start.time
   jobs.start.time
   jobs)

(defun sondagem-iterativa (problema)
	"Algoritmo de sondagem iterativa
	retorna primeira solucao encontrada"
	(let ((objectivo? (problema-objectivo? problema))
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
		  (solucao nil))

	(labels ((ilds (estado k depth)
		(if (or (null estado) (funcall objectivo? estado))
			estado
			(let ((sucessores (problema-gera-sucessores problema estado)))
				;(format t "~S~%" sucessores)
				(setf sucessores (ordena-sucessores sucessores (problema-heuristica problema)))
				
				(when (> depth k)
					(progn
						; TODO: devia retornar o que quer que encontrasse
						; ver melhor
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

; TODO: Pouco generico
(defun sonda-heuristica (problema)
	"Lanca sonda que vai percorrer um unico caminho segundo a melhor heuristica
	Nunca vai chegar a um estado impossivel neste problema"
	(let ((objectivo? (problema-objectivo? problema)))
		(labels ((sonda (estado)
			(if (or (null estado) (funcall objectivo? estado))
				estado
				(let ((sucessores (problema-gera-sucessores problema estado)))
					(setf sucessores (ordena-sucessores sucessores (problema-heuristica problema)))
					(sonda (car sucessores))))))
		(sonda (problema-estado-inicial problema)))))

; Baseado na funcao beam-search de: norvig.com/paip/search.lisp
(defun beam-search (problema beam-width tempo-inicio)
	"Search highest scoring states first until goal is reached,
  	but never consider more than beam-width states at a time."
  	(let ((objectivo? (problema-objectivo? problema))
  		  (melhor-solucao nil))
  	(labels (
  		(tree-search (estados)
  			; 300 sao os 5minutos em que e' permitido correr o algoritmo
  			(cond ((or (< (- 300 (tempo-passado tempo-inicio)) 0.5) (null estados)) melhor-solucao)
  				   ((funcall objectivo? (car estados))
  				   	; quando chega a um estado objectivo guarda-o caso seja o melhor encontrado e continua a procurar
  				   	(setf melhor-solucao (escolhe-melhor (car estados) melhor-solucao (problema-heuristica problema)))
  				   	(tree-search (cdr estados)))
  				   (t 
  				   	(let ((sucessores (problema-gera-sucessores problema (car estados))))
  				   		; TODO: sera' possivel inserir de forma ordenada?
  				   		(setf estados (append sucessores (cdr estados)))
  				   		(setf estados (ordena-sucessores estados (problema-heuristica problema)))
  				   		(if (> beam-width (length estados))
  				   			(setf estados estados)
  				   			(setf estados (subseq estados 0 beam-width)))
  				   		(tree-search estados))))))
  	(tree-search (list (problema-estado-inicial problema))))))

(defun procura-com-corte (problema tempo-inicio)
	(let* ((objectivo? (problema-objectivo? problema))
		  (heuristica (problema-heuristica problema))
		  (melhor-solucao (sonda-heuristica problema))
		  (melhor-valor (funcall heuristica melhor-solucao)))
	(format t "melhor valor: ~d~%" melhor-valor)
	(labels (
		(tree-search (estados)
			(cond ((or (< (- 300 (tempo-passado tempo-inicio)) 0.5) (null estados)) (format t "Acabou~%") melhor-solucao)
				   ((funcall objectivo? (car estados))
				   	(format t "Objectivo~%")
				   	(let ((valor (funcall heuristica (car estados))))
				   		(when (< valor melhor-valor)
				   			(setf melhor-valor valor)
				   			(setf melhor-solucao (car estados))))
				   	(tree-search (cdr estados)))
				   (t
				   	(let ((sucessores (problema-gera-sucessores problema (car estados))))
				   		(setf estados (filtra-estados (append sucessores (cdr estados)) melhor-valor heuristica))
				   		(setf estados (ordena-sucessores estados heuristica))
				   		(tree-search estados))))))
	(tree-search (list (problema-estado-inicial problema))))))

(defun escolhe-melhor (estado1 estado2 heuristica)
	(cond ((null estado1) estado2)
		   ((null estado2) estado1)
		   ((< (funcall heuristica estado1) (funcall heuristica estado2)) estado1)
		   (t estado2)))

; Baseado na funcao profundidade-primeira disponibilizada em procura.lisp
; BF-BT (+/-)
(defun procura-teste (problema profundidade-maxima)
	"Faz procura sistematica (profundidade-primeiro) ate' 'a profundidade-maxima
	e guarda todos os estados desta profundidade. De seguida corre o ILDS no estado com melhor
	valor de f.
	Correr ILDS e' equivalente a fazer o melhor caminho segundo a heuristica"
  (let ((objectivo? (problema-objectivo? problema))
  		(estados nil))

    (labels (
    	(procura-prof (estado caminho prof-actual)
	       (block procura-prof
		 
			 ;; base da recursao:
			 ;; 1. quando comecamos a repetir estados pelos quais ja
			 ;;    passamos no caminho que esta a ser percorrido
			 ;;    (para evitar caminhos infinitos)
			 ;; 2. quando atingimos o objectivo
			 ;; 3. quando ultrapassamos a profundidade limite ate
			 ;;    onde se deve efectuar a procura
			 (cond ((funcall objectivo? estado) estado)
			       ((= prof-actual profundidade-maxima) (setf estados (cons estado estados)) nil)
			       (t 
				(dolist (suc (problema-gera-sucessores problema
								       estado))
				  ;; avancamos recursivamente, em profundidade,
				  ;; para cada sucessor
				  (let ((solucao (procura-prof suc 
							       (cons estado caminho)
							       (1+ prof-actual))))
				    (when solucao
				      (return-from procura-prof solucao)))))))))
      
      (procura-prof (problema-estado-inicial problema) nil 0)
      (setf estados (ordena-sucessores estados (problema-heuristica problema)))
      ;(format t "~S~%" estados)
      (sonda-heuristica (cria-problema
      					(car estados) (problema-operadores problema)
      					:objectivo? (problema-objectivo? problema)
      					:heuristica (problema-heuristica problema)
      					:custo (always 0))))))

(defun ordena-sucessores (sucessores heuristica)
	"Ordena sucessores segundo a heuristica passada"
	(sort sucessores #'(lambda (x y) (< (funcall heuristica x) (funcall heuristica y)))))


(defun total-tasks (state)
	"Conta numero total de tarefas ainda por atribuir tempo de inicio"
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
						(newStateJob (nth i (job-shop-state-jobs newState)))
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
						;(setf (aref (job-shop-state-taskSequence newState) (job-shop-task-job.nr newTask))
						;	(nconc (aref (job-shop-state-taskSequence newState) (job-shop-task-job.nr newTask)) (list newTask)))
						(nconc (aref (job-shop-state-taskSequence newState) (job-shop-task-job.nr newTask)) (list newTask))
						(setf sucessores (cons newState sucessores))))))
		sucessores))

(defun estado-objectivo (state)
	"Recebe o estado e diz se este e' objectivo ou nao"
	(dolist (job (job-shop-state-jobs state))
		(when (not (null (job-shop-job-tasks job)))
			(return-from estado-objectivo NIL)))
	t)

(defun custo (estado)
	"Funcao custo: Devolve o tempo ma'ximo ocupado pelas tarefas atribuidas"
	(let ((max 0))
		(dotimes (i (array-dimension (job-shop-state-machines.start.time estado) 0))
			(let ((valor (aref (job-shop-state-machines.start.time estado) i)))
				(when (> valor max)
					(setf max valor))))
		max))

(defun heuristica (estado)
	"heuristica optimista:

	consideramos que as tarefas que ainda nao tem atribuido um valor de inicio
	seriam idealmente, divididas igualmente entre todas as maquinas
	formula: tempo.ja.atribuido + (tempo.por.atribuir / n.maquinas)"
	(let ((n.maquinas (length (job-shop-state-machines.start.time estado)))
		  (duracao.restante 0)
		  (tempo.atribuido (custo estado)))
		; percorre todos os trabalhos
		(dolist (job (job-shop-state-jobs estado))
			; percorre todas as tarefas do trabalho
			(dolist (task (job-shop-job-tasks job))
				; incrementa a duracao restante com a duracao de cada tarefa
				(setf duracao.restante (+ duracao.restante (job-shop-task-duration task)))))
		(+ tempo.atribuido (/ duracao.restante n.maquinas))))

(defun heuristica-alternativa (estado)
	"Considera como unica restricao um trabalho por maquina de cada vez"
	(let ((maquinas (make-array (length (job-shop-state-machines.start.time estado)) :initial-element 0))
		  (tempo.atribuido (custo estado))
		  (restante 0))
		(dolist (job (job-shop-state-jobs estado))
			(dolist (task (job-shop-job-tasks job))
				(incf (aref maquinas (job-shop-task-machine.nr task)) (job-shop-task-duration task))))
		(dotimes (i (length maquinas))
			(when (< restante (aref maquinas i))
				(setf restante (aref maquinas i))))
		(+ tempo.atribuido restante)))

(defun heuristica-alternativa2 (estado)
	"Considera como unica restricao a precedencia de tarefas"
	(let ((jobs (make-array (length (job-shop-state-jobs estado)) :initial-element 0))
		  (tempo.atribuido (custo estado))
		  (restante 0))
		(dolist (job (job-shop-state-jobs estado))
			(dolist (task (job-shop-job-tasks job))
				(incf (aref jobs (job-shop-task-job.nr task)) (job-shop-task-duration task))))
		(dotimes (i (length jobs))
			(when (< restante (aref jobs i))
				(setf restante (aref jobs i))))
		(+ tempo.atribuido restante)))

(defun heuristica-alternativa3 (estado)
	(let ((maquinas (make-array (length (job-shop-state-machines.start.time estado)) :initial-element 0))
		  (jobs (make-array (length (job-shop-state-jobs estado)) :initial-element 0))
		  (tempo.atribuido (custo estado))
		  (restante 0))
	(dolist (job (job-shop-state-jobs estado))
		(dolist (task (job-shop-job-tasks job))
			(incf (aref maquinas (job-shop-task-machine.nr task)) (job-shop-task-duration task))
			(incf (aref jobs (job-shop-task-job.nr task)) (job-shop-task-duration task))))
	(dotimes (i (length maquinas))
			(when (< restante (aref maquinas i))
				(setf restante (aref maquinas i))))
	(dotimes (i (length jobs))
			(when (< restante (aref jobs i))
				(setf restante (aref jobs i))))
	(+ tempo.atribuido restante)))

(defun calendarizacao (problema-job-shop estrategia)
	(let ((problema (cria-problema (cria-estado problema-job-shop) (list #'operador)
						:objectivo? #'estado-objectivo
						:heuristica #'heuristica-alternativa2
						:hash #'funcao-hash
						; custo esta' inserido na heuristica
						:custo (always 0)))
		  (*nos-expandidos* 0)
		  (*nos-gerados* 0)
		  (tempo-inicio-run (get-internal-run-time))
		  (tempo-inicio (get-internal-real-time)))
		(let ((solucao 
			(cond ((string-equal estrategia "melhor.abordagem")
				; ainda nao esta' decidido
				(beam-search problema 6 tempo-inicio))
			((string-equal estrategia "a*.melhor.heuristica")
				(car (last (car (procura problema "a*")))))
			((string-equal estrategia "a*.melhor.heuristica.alternativa")
				(setf (problema-heuristica problema) #'heuristica-alternativa2)
				(car (last (car (procura problema "a*")))))
			((string-equal estrategia "sondagem.iterativa")
				(sondagem-iterativa problema))
			((string-equal estrategia "ILDS")
				(improved-lds problema (total-tasks (problema-estado-inicial problema))))
			((string-equal estrategia "abordagem.alternativa")
				; ainda nao esta decidido
				(procura-com-corte problema tempo-inicio)))))
			;(output solucao))))
			(if (null solucao)
				solucao
				(list (output solucao) (- (get-internal-run-time) tempo-inicio-run) *nos-expandidos* *nos-gerados* (funcall (problema-custo problema) solucao))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Funcoes auxiliares
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cria-estado (problema)
	"Recebe um job-shop-problem e devolve o estado correspondente usado nas procuras"
	(make-job-shop-state
		:taskSequence (make-array (job-shop-problem-n.jobs problema) :initial-element '())
		:machines.start.time (make-array (job-shop-problem-n.machines problema) :initial-element 0)
		:jobs.start.time (make-array (job-shop-problem-n.jobs problema) :initial-element 0)
		:jobs (job-shop-problem-jobs problema)))

(defun pop-task (state job.index)
	"Retira a primeira tarefa do trabalho na posicao job.index
	Assume que as tarefas estao ordenadas por numero de tarefa"
	(setf (job-shop-job-tasks (nth job.index (job-shop-state-jobs state))) 
		(cdr (job-shop-job-tasks (nth job.index (job-shop-state-jobs state)))))
	state)

(defun output (estado)
	"Recebe o estado e cria o output apropriado"
	(let ((taskSequence (job-shop-state-taskSequence estado))
		  (tamanho (array-dimension (job-shop-state-taskSequence estado) 0))
		  (resultado nil))
		(dotimes (i tamanho)
			(setf resultado (append (aref taskSequence (- (- tamanho 1) i)) resultado)))
		resultado))

(defun tempo-passado (tempo-inicio)
	"Devolve a quantidade de tempo real que passou desde tempo-inicio"
	(/ (- (get-internal-real-time) tempo-inicio) internal-time-units-per-second))

(defun filtra-estados (estados valor heuristica)
	(let ((resultado nil))
		(dolist (estado estados)
			(when (< (funcall heuristica estado) valor)
				(setf resultado (cons estado resultado))))
		resultado))

;(defun filtra-estados (estados valor heuristica)
;	(let ((resultado nil)
;		  (cortes 0))
;		(dolist (estado estados)
;			(if (< (funcall heuristica estado) valor)
;				(setf resultado (cons estado resultado))
;				(incf cortes)))
;		(format t "~d~%" cortes)
;		resultado))

(defun funcao-hash (estado)
	(let ((resultado nil))
		(dolist (job (job-shop-state-jobs estado))
			(setf resultado (cons (length (job-shop-job-tasks job)) resultado)))
		(sxhash (cons (custo estado) resultado))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Funcoes para a copia do estado
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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