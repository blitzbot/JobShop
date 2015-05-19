;(in-package :user)

(defun iterative-probing (problema)
	(let ((objectivo? (problema-objectivo? problema)))
		;procura sonda
		(labels ((procura-sonda (estado)
			(block procura-sonda
				(if ((funcall objectivo? estado) estado)
					(let ((sucessores (problema-gera-sucessores problema estado)))
						(if (null sucessores)
							nil
							(return-from procura-sonda (nth (random (length sucessores)) sucessores))))))))
		(procura-sonda (problema-estado-inicial problema)))))

(defun improved-lds())