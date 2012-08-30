;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

;;; The runtime of PTTPP.
;;; ====================

(in-package #:pttpp)
;; (declaim (optimize (debug 3)))
(declaim (optimize (speed 2) (compilation-speed 0)))

#+5am
(5am:in-suite pttpp-runtime-suite)

(defconstant +float-internal-time-units-per-second+
  (float internal-time-units-per-second))

(defconstant +and-connective+ '|,/2|
  "The canonical operator for and.")
(defconstant +or-connective+  '\;/2
  "The canonical operator for or.")

#+5am
(5am:test test-connective-names
  (5am:is (string-equal ",/2" (symbol-name +and-connective+)))
  (5am:is (string-equal ";/2" (symbol-name +or-connective+))))


;; dynamic variables used during compilation

;;; arity of procedure being compiled
(defvar *arity*)
;:; association list of clauses and their numbers
(defvar *clause-numbers*)
;;: the type of the first argument to the procedure
(defvar *first-argument-type*)
;;; compile-procedure option to not compile code for depth-bounded
;;; search
(defvar *unbounded-search*)
;;; compile-procedure option to not use the occurs check during
;;; unification
(defvar *unsafe-unification*)
;;; compile-procedure option to compile ME reduction operations
(defvar *incomplete-inference*)
;;; compile-procedure option to compile ME pruning operations
(defvar *allow-repeated-goals*)
;;; if nil, tracing will not be compiled regardless of :traceable
;;; option
(defvar *trace-calls* t)
;;; recompile procedure even if clauses and parameters are the same
(defvar *recompile* nil)
;;; print input clauses
(defvar *print-clauses* t)
;;; print names of functions as they are compiled
(defvar *print-compile-names* t)
;;; print compilation time 
(defvar *print-compile-times* t)
;;; Print execution time
(defvar *print-execution-time* t)


(defmacro dereference (x &key (if-constant t)
                              (if-variable nil)
                              (if-compound nil))
  "Dereferences the place X.  If X references a bound variable, recursively
stores the binding in X until it is no longer a variable or an unbound
variable.  Returns IF-CONSTANT, if (after this update) X is a constant value;
IF-VARIABLE if X is an unbound variable, and IF-COMPOUND if X is a compound
term."
  (with-gensyms ((variable-value #:variable-value-))
    `(iter 
       (cond ((variable-p ,x)
              (let ((,variable-value (variable-value ,x)))
                (if ,variable-value
                    (setf ,x ,variable-value)
                    (leave ,if-variable))))
             ((atom ,x)
              (leave ,if-constant))
             (t (leave ,if-compound))))))

(declaim (type runtime-data *runtime-data*))
(defglobal *runtime-data* (make-runtime-data)
    "The data needed by the pttpp runtime.")

(defmacro trail-variable-p (var)
  `(< (variable-level ,var) !level!))

(defmacro bind-variable-to-term (var term trail?)
  ;; returns non-nil value (term is never nil)
  (assert (symbolp var))
  (assert (member trail? '(:trail :dont-trail :maybe-trail)))
  (cond ((eq trail? :dont-trail)
	 `(progn (setf (variable-value ,var) ,term)
		 t))
	((eq trail? :trail)
	 `(progn (setf (svref (rt-trail-array *runtime-data*)
                              (incf (rt-trail-index *runtime-data*)))
                       ,var)
		 (setf (variable-value ,var) ,term)
		 t))
	(t `(progn (if (trail-variable-p ,var)
		       (setf (svref (rt-trail-array *runtime-data*)
                                    (incf (rt-trail-index *runtime-data*)))
                             ,var))
		   (setf (variable-value ,var) ,term)
		   t))))

(defmacro undo-bindings ()
  ;; MUST RETURN NIL
  `(let ((trail (rt-trail-index *runtime-data*)))
     (when (> trail !old-trail!)
       (do ((trail-array (rt-trail-array *runtime-data*)))
	   (nil)
	 (setf (variable-value (svref trail-array trail)) nil)
	 (when (= (decf trail) !old-trail!)
	   (setf (rt-trail-index *runtime-data*) !old-trail!)
	   (return nil))))))

(defmacro safe-bind-variable-to-compound (var term trail? undo?)
  ;; returns non-nil value if binding is successful,
  ;; undoes bindings on trail and returns nil if not successful
  (assert (symbolp term))
  `(if (variable-occurs-in-terms-p ,var (cdr ,term))
       ,(if undo? `(undo-bindings) nil)
       (bind-variable-to-term ,var ,term ,trail?)))

(defmacro pcall (term (vars unbound) level continuation)
  (stack-list-new-variables
   unbound
   (let* ((formals (head-locs (cdr term) 'a))
          (actuals (mapcar #'(lambda (x)
                               (term-constructor x vars))
                           (cdr term)))
          (decls (mapcan #'(lambda (x y)
                             (if (or (atom y) (eq (car y) 'quote))
                                 nil
                                 (list (list x y))))
                         formals actuals))
          (args (mapcar #'(lambda (x y)
                            (if (or (atom y) (eq (car y) 'quote))
                                y
                                x))
                        formals actuals)))
     (if decls
         `(let ,decls
            (,(car term) ,@args ,level ,continuation))
         `(,(car term) ,@args ,level ,continuation)))))


;; UNIFICATION

(defun ground-term-p (term)
  (dereference term
    :if-constant  t
    :if-variable  nil
    :if-compound  (ground-terms-p (cdr term))))

(defun ground-terms-p (terms)
  (do ((l terms (cdr l)) (term))
      ((null l) t)
    (setq term (car l))
    (dereference term
      :if-constant  nil
      :if-variable  (return-from ground-terms-p nil)
      :if-compound  (cond ((null (cdr l)) (setq l term))
                          ((not (ground-terms-p (cdr term)))
                           (return-from ground-terms-p nil))))))

(defun variable-occurs-in-term-p (var term)
  ;; works for both external (e.g., X) and internal (i.e., 
  ;; (level pointer-or-nil . name)) variable representations i.e., we check
  ;; (eq var term) in the constant as well as variable case it would be
  ;; slightly more efficient to handle only the internal representation when
  ;; running Prolog programs
  (dereference term
    :if-constant  (eq var term)
    :if-variable  (eq var term)
    :if-compound  (variable-occurs-in-terms-p var (cdr term))))

(defun variable-occurs-in-terms-p (var terms)
  ;; works for both external (e.g., X) and internal (i.e., 
  ;; (level pointer-or-nil . name)) variable representations i.e., we check
  ;; (eq var term) in the constant as well as variable case it would be
  ;; slightly more efficient to handle only the internal representation when
  ;; running Prolog programs
  (do ((l terms (cdr l)) (term))
      ((null l) nil)
    (setq term (car l))
    (dereference term
      :if-constant  (if (eq var term)
                        (return-from variable-occurs-in-terms-p t))
      :if-variable  (if (eq var term)
                        (return-from variable-occurs-in-terms-p t))
      :if-compound  (cond ((null (cdr l)) (setq l term))
                          ((variable-occurs-in-terms-p var (cdr term))
                           (return-from variable-occurs-in-terms-p t))))))

(defmacro unify-macro (unify-list-fun trail? safely?)
  ;; undoes bindings on trail and returns nil if not successful
  `(dereference t1
     :if-constant
     (dereference t2
       :if-constant  (or (eql t1 t2) (undo-bindings))
       :if-variable  (bind-variable-to-term t2 t1 ,trail?)
       :if-compound  (undo-bindings))
     :if-variable
     (dereference t2
       :if-constant  (bind-variable-to-term t1 t2 ,trail?)
       :if-variable  (or (eq t1 t2)
                         (if (<= (variable-level t1) (variable-level t2))
                             (bind-variable-to-term t2 t1 ,trail?)
                             (bind-variable-to-term t1 t2 ,trail?)))
       :if-compound  ,(if safely?
                          `(safe-bind-variable-to-compound t1 t2 ,trail? t)
                          `(bind-variable-to-term t1 t2 ,trail?)))
     :if-compound
     (dereference t2
       :if-constant  (undo-bindings)
       :if-variable  ,(if safely?
                          `(safe-bind-variable-to-compound t2 t1 ,trail? t)
                          `(bind-variable-to-term t2 t1 ,trail?))
       :if-compound  (or (eq t1 t2)
                         (if (eq (car t1) (car t2))
                             (let ((l1 (cdr t1)) (l2 (cdr t2)))
                               (unify-list-macro
                                ,unify-list-fun ,trail? ,safely?))
                             (undo-bindings))))))

(defmacro unify-list-macro (unify-list-fun trail? safely?)
  ;; undoes bindings on trail and returns nil if not successful
  `(block unify-list
     (do ((t1) (t2))
	 ((null l1) (return t))
       (setq t1 (car l1)) (setq l1 (cdr l1))
       (setq t2 (car l2)) (setq l2 (cdr l2))
       (dereference t1
         :if-constant
         (dereference t2
           :if-constant  (unless (eql t1 t2)
                           (return-from unify-list (undo-bindings)))
           :if-variable  (bind-variable-to-term t2 t1 ,trail?)
           :if-compound  (return-from unify-list (undo-bindings)))
         :if-variable
         (dereference t2
           :if-constant  (bind-variable-to-term t1 t2 ,trail?)
           :if-variable  (or (eq t1 t2)
                             (if (<= (variable-level t1) (variable-level t2))
                                 (bind-variable-to-term t2 t1 ,trail?)
                                 (bind-variable-to-term t1 t2 ,trail?)))
           :if-compound  ,(if safely?
                              `(unless (safe-bind-variable-to-compound
                                        t1 t2 ,trail? t)
                                 (return-from unify-list nil))
                              `(bind-variable-to-term t1 t2 ,trail?)))
         :if-compound
         (dereference t2
           :if-constant  (return-from unify-list (undo-bindings))
           :if-variable  ,(if safely?
                              `(unless (safe-bind-variable-to-compound
                                        t2 t1 ,trail? t)
                                 (return-from unify-list nil))
                              `(bind-variable-to-term t2 t1 ,trail?))
           :if-compound  (cond ((eq t1 t2))
                               ((not (eq (car t1) (car t2)))
                                (return-from unify-list (undo-bindings)))
                               ((null l1)
                                (setq l1 (cdr t1)) (setq l2 (cdr t2)))
                               ((not ,(if (eq trail? :maybe-trail)
                                          `(,unify-list-fun
                                            (cdr t1) (cdr t2) !old-trail! !level!)
                                          `(,unify-list-fun
                                            (cdr t1) (cdr t2) !old-trail!)))
                                (return-from unify-list nil))))))))

(defun always-trails-unify (t1 t2 !old-trail!)
  (unify-macro always-trails-unify-list :trail t))

(defun always-trails-unify-list (l1 l2 !old-trail!)
  (unify-list-macro always-trails-unify-list :trail t))

(defun maybe-trails-unify (t1 t2 !old-trail! !level!)
  (unify-macro maybe-trails-unify-list :maybe-trail t))

(defun maybe-trails-unify-list (l1 l2 !old-trail! !level!)
  (unify-list-macro maybe-trails-unify-list :maybe-trail t))

(defun unsafe-always-trails-unify (t1 t2 !old-trail!)
  (unify-macro unsafe-always-trails-unify-list :trail nil))

(defun unsafe-always-trails-unify-list (l1 l2 !old-trail!)
  (unify-list-macro unsafe-always-trails-unify-list :trail nil))

(defun unsafe-maybe-trails-unify (t1 t2 !old-trail! !level!)
  (unify-macro unsafe-maybe-trails-unify-list :maybe-trail nil))

(defun unsafe-maybe-trails-unify-list (l1 l2 !old-trail! !level!)
  (unify-list-macro unsafe-maybe-trails-unify-list :maybe-trail nil))

(defmacro unify-argument-with-constant (actual formal &key trail-is-nil)
  (assert (or (atom formal)
              (eq (car formal) 'quote)
              (eq (car formal) 'nth)))
  `(let ((!temp! ,actual))
     (dereference !temp!
       :if-constant  ,(if trail-is-nil
                          `(eql !temp! ,formal)
                          `(or (eql !temp! ,formal) (undo-bindings)))
       :if-variable  (bind-variable-to-term !temp! ,formal :trail)
       :if-compound  ,(if trail-is-nil nil `(undo-bindings)))))

(defmacro unify-argument-with-compound
    (actual formal &key trail-is-nil unsafe)
  (assert (symbolp formal))
  `(let ((!temp! ,actual))
     (dereference !temp!
       :if-constant  ,(if trail-is-nil nil `(undo-bindings))
       :if-variable  ,(if unsafe
                          `(bind-variable-to-term !temp! ,formal :trail)
                          `(safe-bind-variable-to-compound
                            !temp! ,formal :trail ,(not trail-is-nil)))
       :if-compound  (or (eq !temp! ,formal)
                         (if (eq (car !temp!) (car ,formal))
                             ,(if unsafe
                                  `(unsafe-maybe-trails-unify-list
                                    (cdr !temp!) (cdr ,formal) !old-trail! !level!)
                                  `(maybe-trails-unify-list
                                    (cdr !temp!) (cdr ,formal) !old-trail! !level!))
                             ,(if trail-is-nil nil `(undo-bindings)))))))

(defmacro identical-to-constant (term constant)
  (assert (symbolp constant))
  (if (symbolp term)
      `(dereference ,term
         :if-constant  (eql ,term ,constant)
         :if-variable  nil
         :if-compound  nil)
      (let ((temp (gensym)))
	`(let ((,temp ,term))
	   (identical-to-constant ,temp ,constant)))))

(defmacro identical-to-variable (term variable)
  (assert (symbolp variable))
  (if (symbolp term)
      `(dereference ,term
         :if-constant  nil
         :if-variable  (eq ,term ,variable)
         :if-compound  nil)
      (let ((temp (gensym)))
	`(let ((,temp ,term))
	   (identical-to-variable ,temp ,variable)))))

(defmacro identical-to-compound (term compound)
  (assert (symbolp compound))
  (if (symbolp term)
      `(dereference ,term
         :if-constant  nil
         :if-variable  nil
         :if-compound  (or (eq ,term ,compound)
                           (and (eq (car ,term) (car ,compound))
                                (identical-list (cdr ,term) (cdr ,compound)))))
      (let ((temp (gensym)))
	`(let ((,temp ,term))
	   (identical-to-compound ,temp ,compound)))))

(defmacro identical (t1 t2)
  (if (symbolp t2)
      `(dereference ,t2
         :if-constant  (identical-to-constant ,t1 ,t2)
         :if-variable  (identical-to-variable ,t1 ,t2)
         :if-compound  (identical-to-compound ,t1 ,t2))
      (let ((temp (gensym)))
	`(let ((,temp ,t2))
	   (identical ,t1 ,temp)))))

(defmacro identical-list (l1 l2)
  `(block identical-list
     (do ((l1 ,l1) (l2 ,l2) (t1) (t2))
	 ((null l1) (return t))
       (setq t1 (car l1)) (setq l1 (cdr l1))
       (setq t2 (car l2)) (setq l2 (cdr l2))
       (dereference t2
         :if-constant  (unless (identical-to-constant t1 t2)
                         (return-from identical-list nil))
         :if-variable  (unless (identical-to-variable t1 t2)
                         (return-from identical-list nil))
         :if-compound  (dereference t1
                         :if-constant
                         (return-from identical-list nil)
                         :if-variable
                         (return-from identical-list nil)
                         :if-compound
                         (cond ((eq t1 t2))
                               ((not (eq (car t1) (car t2)))
                                (return-from identical-list nil))
                               ((null l1)
                                (setq l1 (cdr t1)) (setq l2 (cdr t2)))
                               ((not (identical-list-fun (cdr t1) (cdr t2)))
                                (return-from identical-list nil))))))))

(defun identical-list-fun (l1 l2)
  (identical-list l1 l2))

;; SUPPORT FOR OUTPUT AND TRACING

;;; use prefix, postfix, infix operators during printing
(defvar *writing* t)

(defun function-case (x)
  (string-downcase x))

(defun constant-case (x)
  (string-downcase x))

(defun variable-case (x)
  (string-capitalize x))

(defun display-term (term)
  (let ((*writing* nil))
    (write-term term)))

(defun write-term (term)
  (dereference term)
  (cond	((variable-p term)
         (princ (variable-case (variable-name term)))
         (princ "_")
         (princ (variable-level term)))
        ((atom term)
         (princ (if (symbolp term) (constant-case term) term)))
	(t (write-functor-and-arguments (car term) (cdr term))))
  term)

(defun parenthesize-argument (arg prec rel)
  (dereference arg
    :if-constant  nil
    :if-variable  nil
    :if-compound  (let ((argprec (precedence (car arg))))
                    (and argprec (funcall rel prec argprec)))))

(defun write-functor-and-arguments (fn args &aux spec prec)
  (cond ((eq fn 'cons/2)
	 (princ "[")
	 (write-term (car args))
	 (do ((x (cadr args) (caddr x)))
	     (nil)
	   (dereference x)
	   (cond ((eq x '|[]|)
                  (princ "]") (return))
		 ((and (not (atom x)) (eq (car x) 'cons/2))
                  (princ ",") (write-term (cadr x)))
		 (t (princ "|") (write-term x) (princ "]")
                    (return)))))
	((and *writing* (setq spec (specifier fn)))
	 (setq prec (precedence fn))
	 (case spec
	   ((fx fy)
	    (princ (function-case (functor-name fn)))
	    (princ " ")
	    (cond ((parenthesize-argument
                    (car args) prec (if (eq spec 'fx) #'<= #'<))
		   (princ "(") (write-term (car args)) (princ ")"))
		  (t (write-term (car args)))))
	   ((xf yf)
	    (cond ((parenthesize-argument
                    (car args) prec (if (eq spec 'fx) #'<= #'<))
		   (princ "(") (write-term (car args)) (princ ")"))
		  (t (write-term (car args))))
	    (princ " ")
	    (princ (function-case (functor-name fn))))
	   ((xfx xfy yfx yfy)
	    (cond ((parenthesize-argument
                    (car args) prec (if (member spec '(xfx xfy)) #'<= #'<))
		   (princ "(") (write-term (car args)) (princ ")"))
		  (t (write-term (car args))))
	    (princ " ")
	    (princ (function-case (functor-name fn)))
	    (princ " ")
	    (cond ((parenthesize-argument
                    (cadr args) prec (if (member spec '(xfx yfx)) #'<= #'<))
		   (princ "(") (write-term (cadr args)) (princ ")"))
		  (t (write-term (cadr args)))))))
	(t (princ (function-case (functor-name fn)))
	   (when args
	     (princ "(")
	     (cond ((parenthesize-argument (car args) 0 #'<)
		    (princ "(") (write-term (car args)) (princ ")"))
		   (t (write-term (car args))))
	     (dolist (term (cdr args))
	       (princ ",")
	       (cond ((parenthesize-argument term 0 #'<)
		      (princ "(") (write-term term) (princ ")"))
		     (t (write-term term))))
	     (princ ")"))))
  nil)

(defun write-functor-and-arguments* (fn &rest args)
  (write-functor-and-arguments fn args))

(defun write-clause (clause &optional number variables)
  (let ((goalp (and (eq (car clause) '<-/2)
                    (equal (cadr clause) '(query/0)))))
    (fresh-line)
    (when goalp (princ " ----------------") (terpri))
    (when number
      (if (consp number)
          (format t "~3D~A. " (car number) (cdr number))
          (format t "~3D.  " number)))
    (if goalp
        (let (quantified)
          (write-term (cadr clause))
          (princ " <- ")
          (dolist (v variables)
            (when (variable-occurs-in-term-p v (caddr clause))
              (princ "(") (write-term v) (princ ")") (setq quantified t)))
          (when quantified (princ " "))
          (write-term (caddr clause)))
        (let (quantified)
          (dolist (v variables)
            (when (variable-occurs-in-term-p v clause)
              (princ "(") (write-term v) (princ ")") (setq quantified t)))
          (when quantified (princ " "))
          (write-term clause)))
    (princ ".")))


(defvar *tracing* nil)
(defvar *spy-points* nil)

(defmacro trace-call-fail (nm form)
  (let ((args (head-locs (get nm 'arity))))
    `(progn
       (when (or *tracing* (member ',nm *spy-points*))
	 (format t "~&~VT~4D CALL " (+ !level! !level! -1) !level!)
         (write-functor-and-arguments* ',nm . ,args))
       ,form
       (when (or *tracing* (member ',nm *spy-points*))
	 (format t "~&~VT~4D FAIL " (+ !level! !level! -1) !level!)
         (write-functor-and-arguments* ',nm . ,args)))))

(defmacro trace-exit-redo (nm form)
  (let ((args (head-locs (get nm 'arity))))
    `(progn (when (or *tracing* (member ',nm *spy-points*))
	      (format t "~&~VT~4D EXIT " (+ !level! !level! -1) !level!)
              (write-functor-and-arguments* ',nm . ,args))
	    ,form
	    (when (or *tracing* (member ',nm *spy-points*))
	      (format t "~&~VT~4D REDO " (+ !level! !level! -1) !level!)
              (write-functor-and-arguments* ',nm . ,args)))))

(defun wrap-call-fail-trace (form)
  (if *traceable*
      `(trace-call-fail ,*name* ,form)
      form))

;; CONSECUTIVELY BOUNDED DEPTH-FIRST SEARCH

;;; effectively infinite values so that depth-bounded code
(defvar *remaining-depth* 1000000)
;;; will run outside of search calls
(defvar *prev-depth-increment* 1000001)
(defvar *minus-next-depth-increment* -1000)

(defvar *old-remaining-depths* nil)
(defvar *old-prev-depth-increments* nil)
(defvar *old-minus-next-depth-increments* nil)

;; search is a Prolog predicate which takes goal argument so that the user
;; does not have to insert end-search calls between the goals and additional
;; code to do something with, e.g., print, each solution

;;; print a message when starting search on each level, etc.
(defvar *trace-search* t)
;;; include number of inferences in the message
(defvar *trace-search-calls* t)
;;; time spent printing search messages to be excluded from execution time
(defvar *trace-search-time*)

(defmacro trace-search (&rest args)
  `(when *trace-search*
     (let ((start-time (get-internal-run-time)))
       (fresh-line)
       (when *trace-search-calls*
	 (format t "~11:D inferences so far.   " *ncalls*))
       (format t ,@args)
       (incf *trace-search-time* (- (get-internal-run-time) start-time)))))

(defun begin-search
    (maximum-depth minimum-depth default-depth-increment !level! !continuation!)
  (let ((*old-remaining-depths*
          (cons *remaining-depth* *old-remaining-depths*))
        (*old-prev-depth-increments*
          (cons *prev-depth-increment* *old-prev-depth-increments*))
        (*old-minus-next-depth-increments*
          (cons *minus-next-depth-increment* *old-minus-next-depth-increments*)))
    (let (*remaining-depth*
          *prev-depth-increment*
          *minus-next-depth-increment*
          cut)
      (dereference maximum-depth)
      (if (null maximum-depth) (setq maximum-depth 1000000))
      (dereference minimum-depth)
      (if (null minimum-depth) (setq minimum-depth 0))
      (dereference default-depth-increment)
      (if (null default-depth-increment) (setq default-depth-increment 1))
      (setq *remaining-depth* minimum-depth)
      (setq *prev-depth-increment* (1+ minimum-depth))
      (do nil (nil)
	(when (> *remaining-depth* maximum-depth)
          (trace-search "Search ended, maximum depth reached. ")
          (return nil))
	(trace-search 
         "Start searching with ~:[no subgoals~;at most ~2D subgoal~:P~]. "
         (> *remaining-depth* 0) *remaining-depth*)
	(setq *minus-next-depth-increment* -1000)
	(setq cut t)
	(unwind-protect
             (progn (funcall !continuation! !level!) (setq cut nil))
	  (when cut (trace-search "Search ended by cut. ")))
	(let ((next-depth-increment (- *minus-next-depth-increment*)))
	  (when (= next-depth-increment 1000)
            (trace-search "Search ended, no more inferences possible. ")
            (return nil))
	  (setq next-depth-increment (max next-depth-increment default-depth-increment))
	  (incf *remaining-depth* next-depth-increment)
	  (setq *prev-depth-increment* next-depth-increment))))))

(defmacro end-search (form)
  ;; executes form only for solutions that were not discovered in a previous
  ;; search with lower depth bound
  `(if (< *remaining-depth* *prev-depth-increment*)
       (let* ((*remaining-depth* (car *old-remaining-depths*))
	      (*prev-depth-increment* (car *old-prev-depth-increments*))
	      (*minus-next-depth-increment* (car *old-minus-next-depth-increments*))
	      (*old-remaining-depths* (cdr *old-remaining-depths*))
	      (*old-prev-depth-increments* (cdr *old-prev-depth-increments*))
	      (*old-minus-next-depth-increments* (cdr *old-minus-next-depth-increments*)))
	 ,form)))

(defmacro with-n-subgoals (n form)
  `(let ((*remaining-depth* (- *remaining-depth* ,n)))
     (cond ((minusp *remaining-depth*)
	    (if (> *remaining-depth* *minus-next-depth-increment*)
                (setq *minus-next-depth-increment* *remaining-depth*))
	    nil)
	   (t ,form))))

(defun wrap-depth-test (form clause-body)
  (if *unbounded-search*
      form
      (let ((n (clause-body-length clause-body T)))
	(if (> n 0)
	    `(with-n-subgoals ,n ,form)
	    form))))

(defun not-solvable (!arg1! !arg2! !level! !continuation!
                     &aux (!old-trail! (rt-trail-index *runtime-data*)))
  ;; !arg2! specifies depth of search
  (incf !level!)
  (trace-call-fail
   not/2
   (dereference !arg1!
     :if-variable
     (error "NOT was given non-compound argument ~A" !arg1!)
     :if-constant
     (error "NOT was given non-compound argument ~A" !arg1!)
     :if-compound
     (if (ground-term-p !arg1!)
         (let ((*trace-search* (and *tracing* *trace-search*)))
           (begin-search
            !arg2! !arg2! nil !level!
            #'(lambda (lev)
                (apply (car !arg1!)
                       (append (cdr !arg1!)	; inefficient
                               (list lev
                                     #'(lambda (lev)
                                         (declare (ignore lev))
                                         (undo-bindings)
                                         (return-from not-solvable nil)))))))
           (trace-exit-redo not/2 (funcall !continuation! !level!)))
         (error "NOT was given non-ground argument ~A" !arg1!)))))

;; MODEL-ELIMINATION REDUCTION RULE

(defun ancestors-name (nm)
  (or (get nm 'ancestors)
      (let ((w (intern (concatenate 'string "*" (symbol-name nm) "-ANCESTORS*")
                       'pttpp)))
	(setf (get nm 'ancestors) w)
	w)))

(defun wrap-push-ancestor (form)
  (if (or (not *allow-repeated-goals*) (not *incomplete-inference*))
      (let ((nname (ancestors-name *name*)))
	(if (= *arity* 0)
	    `(let ((,nname t))
	       ,form)
	    `(let ((,nname (cons ,(cond ((= *arity* 0) t)
                                        ((= *arity* 1) '!arg1!)
                                        (t '!args!))
                                 ,nname)))
               ,form)))
      form))

(defun wrap-pop-ancestor (form)
  (if (or (not *allow-repeated-goals*) (not *incomplete-inference*))
      (let ((nname (ancestors-name *name*)))
	(if (= *arity* 0)
	    `(let ((,nname nil))
	       ,form)
	    `(let ((,nname (cdr ,nname)))
	       ,form)))
      form))

(defmacro reduce-by-ancestor (arity type)
  ;; must recompile this and its calls to change counting and tracing
  (let ((*count-calls* t) (*traceable* nil))
    `(dolist (!ancestor! !ancestors!)
       (when ,(cond ((eq type :constant-first-argument)
		     (if (= arity 1)
			 `(unify-argument-with-constant
                           !ancestor! !arg1! :trail-is-nil t)
			 `(and (unify-argument-with-constant
                                (car !ancestor!) !arg1! :trail-is-nil t)
			       ,(if (= arity 2)
				    `(always-trails-unify-list
                                      (cdr !ancestor!) (cdr !args!) !old-trail!)
				    `(always-trails-unify-list
                                      (cdr !ancestor!) (cdr !args!) !old-trail!)))))
		    ((eq type :variable-first-argument)
		     (if (= arity 1)
			 `(always-trails-unify !ancestor! !arg1! !old-trail!)
			 `(always-trails-unify-list !ancestor! !args! !old-trail!)))
		    ((eq type :compound-first-argument)
		     (if (= arity 1)
			 `(unify-argument-with-compound
                           !ancestor! !arg1! :trail-is-nil t)
			 `(and (unify-argument-with-compound
                                (car !ancestor!) !arg1! :trail-is-nil t)
			       ,(if (= arity 2)
				    `(always-trails-unify-list
                                      (cdr !ancestor!) (cdr !args!) !old-trail!)
				    `(always-trails-unify-list
                                      (cdr !ancestor!) (cdr !args!) !old-trail!)))))
		    (t (error "Unrecognized first argument type ~A" type)))
	 ,(wrap-count-calls
           (wrap-exit-redo-trace `(funcall !continuation! !level!)))
	 (if (= (rt-trail-index *runtime-data*) !old-trail!)
	     (return t)
	     (undo-bindings))))))

(defun reduce-by-ancestor-for-constant-first-argument/1
    (!ancestors! !arg1! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 1 :constant-first-argument))

(defun reduce-by-ancestor-for-variable-first-argument/1
    (!ancestors! !arg1! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 1 :variable-first-argument))

(defun reduce-by-ancestor-for-compound-first-argument/1
    (!ancestors! !arg1! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 1 :compound-first-argument))

(defun reduce-by-ancestor-for-constant-first-argument/2
    (!ancestors! !arg1! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 2 :constant-first-argument))

(defun reduce-by-ancestor-for-variable-first-argument/2
    (!ancestors! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 2 :variable-first-argument))

(defun reduce-by-ancestor-for-compound-first-argument/2
    (!ancestors! !arg1! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 2 :compound-first-argument))

(defun reduce-by-ancestor-for-constant-first-argument/3
    (!ancestors! !arg1! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 3 :constant-first-argument))

(defun reduce-by-ancestor-for-variable-first-argument/3
    (!ancestors! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 3 :variable-first-argument))

(defun reduce-by-ancestor-for-compound-first-argument/3
    (!ancestors! !arg1! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 3 :compound-first-argument))

(defun reduce-by-ancestor-for-constant-first-argument/4+
    (!ancestors! !arg1! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 4 :constant-first-argument))

(defun reduce-by-ancestor-for-variable-first-argument/4+
    (!ancestors! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 4 :variable-first-argument))

(defun reduce-by-ancestor-for-compound-first-argument/4+
    (!ancestors! !arg1! !args! !old-trail! !level! !continuation!)
  (reduce-by-ancestor 4 :compound-first-argument))

(defun reduce-by-ancestor-call-fun (arity type)
  (case arity
    (1 (case type
	 (:constant-first-argument
          'reduce-by-ancestor-for-constant-first-argument/1)
	 (:variable-first-argument
          'reduce-by-ancestor-for-variable-first-argument/1)
	 (:compound-first-argument
          'reduce-by-ancestor-for-compound-first-argument/1)))
    (2 (case type
	 (:constant-first-argument
          'reduce-by-ancestor-for-constant-first-argument/2)
	 (:variable-first-argument
          'reduce-by-ancestor-for-variable-first-argument/2)
	 (:compound-first-argument
          'reduce-by-ancestor-for-compound-first-argument/2)))
    (3 (case type
	 (:constant-first-argument
          'reduce-by-ancestor-for-constant-first-argument/3)
	 (:variable-first-argument
          'reduce-by-ancestor-for-variable-first-argument/3)
	 (:compound-first-argument
          'reduce-by-ancestor-for-compound-first-argument/3)))
    (t (case type
	 (:constant-first-argument
          'reduce-by-ancestor-for-constant-first-argument/4+)
	 (:variable-first-argument
          'reduce-by-ancestor-for-variable-first-argument/4+)
	 (:compound-first-argument
          'reduce-by-ancestor-for-compound-first-argument/4+)))))

(defun reduce-by-ancestor-call (name arity type)
  (let ((ancestors (ancestors-name (negated-functor name))))
    (if (= arity 0)
	`(when ,ancestors
	   ,(wrap-count-calls
             (wrap-exit-redo-trace
              `(progn
                 (funcall !continuation! !level!)
                 (return-from ,name nil)))))
	`(when ,ancestors
	   (,(reduce-by-ancestor-call-fun arity type)
	    ,ancestors
	    ,@(cond ((= arity 0) nil)
		    ((= arity 1) `(!arg1!))
		    (t (if (eq type :variable-first-argument)
                           `(!args!)
                           `(!arg1! !args!))))
	    !old-trail!
	    !level!
	    !continuation!)))))


;; MODEL ELIMINATION PRUNING

(defmacro identical-to-ancestor (arity type)
  (let ((temp (cond ((= arity 2)
                     `(identical (cadr !ancestor!) !arg2!))
		    ((= arity 3)
                     `(and (identical (cadr !ancestor!) !arg2!)
                           (identical (caddr !ancestor!) !arg3!)))
		    ((>= arity 4)
                     `(identical-list (cdr !ancestor!) (cdr !args!))))))
    `(dolist (!ancestor! !ancestors!)
       (when ,(cond ((eq type :constant-first-argument)
		     (if (= arity 1)
			 `(identical-to-constant !ancestor! !arg1!)
			 `(and (identical-to-constant (car !ancestor!) !arg1!)
                               ,temp)))
		    ((eq type :variable-first-argument)
		     (if (= arity 1)
			 `(identical-to-variable !ancestor! !arg1!)
			 `(and (identical-to-variable (car !ancestor!) !arg1!)
                               ,temp)))
		    ((eq type :compound-first-argument)
		     (if (= arity 1)
			 `(identical-to-compound !ancestor! !arg1!)
			 `(and (identical-to-compound (car !ancestor!) !arg1!)
                               ,temp)))
		    (t (error "Unrecognized first argument type ~A" type)))
	 (return t)))))

(defun identical-to-ancestor-for-constant-first-argument/1
    (!ancestors! !arg1!)
  (identical-to-ancestor 1 :constant-first-argument))

(defun identical-to-ancestor-for-variable-first-argument/1
    (!ancestors! !arg1!)
  (identical-to-ancestor 1 :variable-first-argument))

(defun identical-to-ancestor-for-compound-first-argument/1
    (!ancestors! !arg1!)
  (identical-to-ancestor 1 :compound-first-argument))

(defun identical-to-ancestor-for-constant-first-argument/2
    (!ancestors! !arg1! !arg2!)
  (identical-to-ancestor 2 :constant-first-argument))

(defun identical-to-ancestor-for-variable-first-argument/2
    (!ancestors! !arg1! !arg2!)
  (identical-to-ancestor 2 :variable-first-argument))

(defun identical-to-ancestor-for-compound-first-argument/2
    (!ancestors! !arg1! !arg2!)
  (identical-to-ancestor 2 :compound-first-argument))

(defun identical-to-ancestor-for-constant-first-argument/3
    (!ancestors! !arg1! !arg2! !arg3!)
  (identical-to-ancestor 3 :constant-first-argument))

(defun identical-to-ancestor-for-variable-first-argument/3
    (!ancestors! !arg1! !arg2! !arg3!)
  (identical-to-ancestor 3 :variable-first-argument))

(defun identical-to-ancestor-for-compound-first-argument/3
    (!ancestors! !arg1! !arg2! !arg3!)
  (identical-to-ancestor 3 :compound-first-argument))

(defun identical-to-ancestor-for-constant-first-argument/4+
    (!ancestors! !arg1! !args!)
  (identical-to-ancestor 4 :constant-first-argument))

(defun identical-to-ancestor-for-variable-first-argument/4+
    (!ancestors! !arg1! !args!)
  (identical-to-ancestor 4 :variable-first-argument))

(defun identical-to-ancestor-for-compound-first-argument/4+
    (!ancestors! !arg1! !args!)
  (identical-to-ancestor 4 :compound-first-argument))

(defun identical-to-ancestor-call-fun (arity type)
  (case arity
    (1 (case type
	 (:constant-first-argument
          'identical-to-ancestor-for-constant-first-argument/1)
	 (:variable-first-argument
          'identical-to-ancestor-for-variable-first-argument/1)
	 (:compound-first-argument
          'identical-to-ancestor-for-compound-first-argument/1)))
    (2 (case type
	 (:constant-first-argument
          'identical-to-ancestor-for-constant-first-argument/2)
	 (:variable-first-argument
          'identical-to-ancestor-for-variable-first-argument/2)
	 (:compound-first-argument
          'identical-to-ancestor-for-compound-first-argument/2)))
    (3 (case type
	 (:constant-first-argument
          'identical-to-ancestor-for-constant-first-argument/3)
	 (:variable-first-argument
          'identical-to-ancestor-for-variable-first-argument/3)
	 (:compound-first-argument
          'identical-to-ancestor-for-compound-first-argument/3)))
    (t (case type
	 (:constant-first-argument
          'identical-to-ancestor-for-constant-first-argument/4+)
	 (:variable-first-argument
          'identical-to-ancestor-for-variable-first-argument/4+)
	 (:compound-first-argument
          'identical-to-ancestor-for-compound-first-argument/4+)))))

(defun identical-to-ancestor-call (name arity type)
  (let ((ancestors (ancestors-name name)))
    (if (= arity 0)
	ancestors
	`(when ,ancestors
	   (,(identical-to-ancestor-call-fun arity type)
	    ,ancestors
	    ,@(cond ((= arity 0) nil)
		    ((= arity 1) `(!arg1!))
		    ((= arity 2) `(!arg1! !arg2!))
		    ((= arity 3) `(!arg1! !arg2! !arg3!))
		    (t `(!arg1! !args!))))))))


