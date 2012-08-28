;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

;;; The compiler of PTTPP.
;;; =====================

(in-package #:pttpp)
;; (declaim (optimize (debug 3)))
;; (declaim (optimize (speed 2) (compilation-speed 0)))

#+5am
(5am:in-suite pttpp-compiler-suite)

(defun clause-head (clause)
  (cond
    ((or (eq (car clause) '<-/2) (eq (car clause) '<-))
     (cadr clause))
    ((or (eq (car clause) '->/2) (eq (car clause) '->))
     (caddr clause))
    (t
     clause)))

(defun clause-pred (clause)
  (car (clause-head clause)))

(defun clause-args (clause)
  (cdr (clause-head clause)))

(defun clause-body (clause)
  (cond
    ((or (eq (car clause) '<-/2) (eq (car clause) '<-))
     (caddr clause))
    ((or (eq (car clause) '->/2) (eq (car clause) '->))
     (cadr clause))
    (t
     '(true/0))))

(defun replace-variable-in-term (var value term)
  (cond ((eq var term) value)
	((atom term) term)
	(t (let ((z (replace-variable-in-terms var value (cdr term))))
	     (if (eq z (cdr term))
                 term
                 (cons (car term) z))))))

(defun replace-variable-in-terms (var value terms)
  (cond ((null terms) nil)
	(t (let ((x (replace-variable-in-term var value (car terms)))
		 (y (replace-variable-in-terms var value (cdr terms))))
	     (if (and (eq x (car terms)) (eq y (cdr terms)))
                 terms
                 (cons x y))))))			      

(defun term-constructor (term vars)
  (cond ((atom term)
	 (cond ((eq term '_)
                `(new-variable '_ !level!))
	       ((member term vars) term)
	       (t (list 'quote term))))
	(t (let ((args (mapcar #'(lambda (x)
                                   (term-constructor x vars))
                               (cdr term))))
	     (cond ((every #'(lambda (x)
                               (and (not (atom x)) (eq (car x) 'quote)))
                           args)
                    (list 'quote term))
		   (t (list* 'list (list 'quote (car term)) args)))))))

(defun term-constructors (terms vars)
  (let ((newterms nil))
    (setf newterms (mapcar #'(lambda (term)
                               (term-constructor term vars))
                           terms))
    (cond ((every #'(lambda (x)
                      (and (not (atom x)) (eq (car x) 'quote)))
                  newterms)
           (list 'quote terms))
          (t (cons 'list newterms)))))

(defun wrap-progn (forms)
  (cond ((null forms) nil)
	((null (cdr forms)) (car forms))
	(t (cons 'progn forms))))

(defun wrap-bind-args (form)
  (if (and (or (not *allow-repeated-goals*) (not *incomplete-inference*))
           (> *arity* 1))
      `(let ((!args! (list . ,(head-locs *arity*))))
	 ,form)
      form))

(defvar trail-is-nil)

(defun wrap-undo-bindings (form)
  (if trail-is-nil
      form
      `(progn ,form (undo-bindings))))

(defun stack-list-new-variables (variables form)
  (cond ((null variables) form)
	(t (list 'let
		 (mapcar
                  #'(lambda (v)
                      (list v `(new-variable ',v !level!) ))
                  variables)
		 form))))

#+5am
(5am:test test-stack-list-new-variables
  (5am:is (equal '(foo bar)
                 (stack-list-new-variables '() '(foo bar))))
  (5am:is (equal '(let ((a (new-variable 'a !level!)))
                   (foo bar))
                 (stack-list-new-variables '(a) '(foo bar)))))

(defun clause-body-length (body &optional fl)
  (cond ((atom body) 0)
	((eq (car body) 'true/0) 0)
	((eq (car body) 'fail/0) 0)
	((eq (car body) 'false/0) 0)
	((eq (car body) 'nsubgoals/1)
         (if fl (cadr body) 0))
	((eq (car body) +and-connective+)
         (+ (clause-body-length (cadr body) fl)
            (clause-body-length (caddr body) fl)))
	((eq (car body) +or-connective+)
	 (let ((l1 (clause-body-length (cadr body) fl))
               (l2 (clause-body-length (caddr body) fl)))
	   (if (= l1 l2)
	       l1
	       (error
                "OR branches ~A and ~A not of same length.~%Proof printing won't work."
                (cadr body) (caddr body)))))
	((member (car body) '(search/1 search/2 search/3 search/4))
         (clause-body-length (cadr body) fl))
	((invisible-functor-p (car body)) 0)
	(t 1)))

(defun compile-body-cut (continuation)
  `(progn 
     ,continuation
     (undo-bindings)
     (return-from ,*name* nil)))

(defun compile-body-question-bang (continuation)
  (if (member *first-argument-type*
              '(:variable-bound-to-constant-first-argument
                :variable-bound-to-compound-first-argument))
      continuation
      `(progn
         ,continuation
         (when (= (rt-trail-index *runtime-data*) !old-trail!)
           (return-from ,*name* nil)))))

(defun compile-body-search (body vars unbound continuation)
  (compile-clause-body1
   `(,+and-connective+ (begin-search
                        ,(caddr body) ,(car (cdddr body)) ,(cadr (cdddr body)))
                       (,+and-connective+ ,(cadr body) end-search))
   vars unbound continuation))

(defun compile-body-and (body vars unbound continuation)
  (cond ((and (not (atom (cadr body)))
              (eq (car (cadr body)) +and-connective+))
         (compile-clause-body1
          `(,+and-connective+
            ,(cadr (cadr body))
            (,+and-connective+ ,(caddr (cadr body)) ,(caddr body)))
          vars unbound continuation))
        ((and (not (atom (cadr body)))
              (eq (car (cadr body)) +or-connective+))
         (compile-clause-body1
          `(,+or-connective+ (,+and-connective+ ,(cadr (cadr body)) ,(caddr body))
                             (,+and-connective+ ,(caddr (cadr body)) ,(caddr body)))
          vars unbound continuation))
        (t (compile-clause-body1 (cadr body) vars unbound
                                 (compile-clause-body1
                                  (caddr body)
                                  vars
                                  (remove-if #'(lambda (v)
                                                 (variable-occurs-in-term-p v (cadr body)))
                                             unbound)
                                  continuation)))))

(defun compile-body-or (body vars unbound continuation)
  (let ((x (compile-clause-body1 (cadr body) vars unbound continuation))
        (y (compile-clause-body1 (caddr body) vars unbound continuation)))
    (cond ((and (not (atom x)) (eq (car x) 'progn))
           (cond ((and (not (atom y)) (eq (car y) 'progn))
                  `(progn ,@(cdr x) ,@(cdr y)))
                 (t `(progn ,@(cdr x) ,y))))
          ((and (not (atom y)) (eq (car y) 'progn))
           `(progn ,x ,@(cdr y)))
          (t `(progn ,x ,y)))))

(defun compile-body-default (body vars unbound continuation)
  `(pcall ,body
       (,(remove-if-not #'(lambda (v)
                            (variable-occurs-in-term-p v body))
                        vars)
        ,(remove-if-not #'(lambda (v)
                            (variable-occurs-in-term-p v body))
                        unbound))
       !level!
       ,(if (and (not (atom continuation))
                 (eq (car continuation) 'funcall)
                 (eq (caddr continuation) '!level!))
            (cadr continuation)
            `(function (lambda (!new-level!)
               ;; WARNING: PUT !LEVEL! INSIDE MACRO IF NO SUBST DESIRED
               ,(subst '!new-level! '!level! continuation))))))

(defun compile-clause-body1 (body vars unbound continuation)
  (cond ((eq body '!)
         (compile-body-cut continuation))
	((eq body '?!)
         (compile-body-question-bang continuation))
	((eq body 'end-search) 
         `(end-search ,continuation))
	((member (car body) '(search/1 search/2 search/3 search/4))
         (compile-body-search body vars unbound continuation))
	((equal body '(true/0)) continuation)
	((equal body '(fail/0)) nil)
	((equal body '(false/0)) nil)
	((eq (car body) 'nsubgoals/1) continuation)
	((eq (car body) +and-connective+)
         (compile-body-and body vars unbound continuation))
	((eq (car body) +or-connective+)
         (compile-body-or body vars unbound continuation))
	(t (compile-body-default body vars unbound continuation))))

(defun compile-clause-body (body vars unbound)
  (if (equal body '(true/0))
      ;;  automatically cut if unit clause subsumes goal
      (setf body '?!))
  (let* ((length (clause-body-length body))
	 (nonunit (> length 0))
	 (*incomplete-inference* (or *incomplete-inference* (not nonunit)))
	 (*allow-repeated-goals* (or *allow-repeated-goals* (not nonunit)))
	 (x (compile-clause-body1 body vars unbound
                                  (wrap-pop-ancestor
                                   (wrap-exit-redo-trace
                                    `(funcall !continuation! !level!))))))
    `(progn 
       ,(wrap-count-calls
         (wrap-push-ancestor
          (wrap-undo-bindings x))))))

(defun compile-clause-with-unbound-head
    (headpats headlocs body vars unbound trail-is-nil)
  (if (and (not (variable-occurs-in-terms-p (car headpats) (cdr headpats)))
           (not (variable-occurs-in-term-p (car headpats) body)))
      (compile-clause1 (cdr headpats) (cdr headlocs)
                       body vars unbound trail-is-nil)
      (if (atom (car headlocs))
          (compile-clause1
           (replace-variable-in-terms
            (car headpats) (car headlocs) (cdr headpats))
           (cdr headlocs)
           (replace-variable-in-term
            (car headpats) (car headlocs) body)
           (cons (car headlocs) vars)
           (remove (car headpats) unbound) trail-is-nil)
          `(let ((,(car headpats) ,(car headlocs)))
             ,(compile-clause1 (cdr headpats) (cdr headlocs) body
                               vars (remove (car headpats) unbound)
                               trail-is-nil)))))

(defun compile-clause-with-variable-head
    (headpats headlocs body vars unbound trail-is-nil)
  (cond ((and (eq (car headpats) '!arg1!)
              (member *first-argument-type* 
                      '(:constant-first-argument
                        :variable-bound-to-constant-first-argument)))
         `(when (unify-argument-with-constant
                 ,(car headlocs) !arg1! :trail-is-nil ,trail-is-nil)
            ,(compile-clause1
              (cdr headpats) (cdr headlocs) body vars unbound nil)))
        ((and (eq (car headpats) '!arg1!)
              (member *first-argument-type*
                      '(:compound-first-argument
                        :variable-bound-to-compound-first-argument)))
         `(when (unify-argument-with-compound
                 ,(car headlocs) !arg1! :unsafe ,*unsafe-unification*)
            ,(compile-clause1 (cdr headpats) (cdr headlocs)
                              body vars unbound nil)))
        (t `(when (,(if *unsafe-unification*
                        'unsafe-maybe-trails-unify
                        'maybe-trails-unify)
                   ,(car headlocs) ,(car headpats) !old-trail! !level!)
              ,(compile-clause1 (cdr headpats) (cdr headlocs)
                                body vars unbound nil)))))

(defun compile-clause-with-atomic-head
    (headpats headlocs body vars unbound trail-is-nil)
  `(when (unify-argument-with-constant ,(car headlocs)
                                       ,(if (and (not (atom (car headpats)))
                                                 (eq (caar headpats) 'nth))
                                            (car headpats)
                                            `',(car headpats))
                                       :trail-is-nil ,trail-is-nil)
     ,(compile-clause1 (cdr headpats) (cdr headlocs) body vars unbound nil)))

(defun compile-clause-default
    (headpats headlocs body vars unbound trail-is-nil)
  (let ((newunbound (remove-if #'(lambda (v)
                                   (variable-occurs-in-term-p v (car headpats)))
                               unbound)))
    (stack-list-new-variables
     (remove-if-not #'(lambda (v)
                        (variable-occurs-in-term-p v (car headpats)))
                    unbound)
     `(let ((!compound! ,(term-constructor (car headpats) vars)))
        (when (unify-argument-with-compound
               ,(car headlocs) !compound! :trail-is-nil
               ,trail-is-nil :unsafe ,*unsafe-unification*)
          ,(compile-clause1
            (cdr headpats) (cdr headlocs) body vars newunbound nil))))))

(defun compile-clause1 (headpats headlocs body vars unbound trail-is-nil)
  (cond ((null headpats)
         (compile-clause-body body vars unbound))
	((eq (car headpats) '_)
         (compile-clause1 (cdr headpats) (cdr headlocs)
                          body vars unbound trail-is-nil))
	((member (car headpats) unbound)
         (compile-clause-with-unbound-head
          headpats headlocs body vars unbound trail-is-nil))
	((member (car headpats) vars)
         (compile-clause-with-variable-head
          headpats headlocs body vars unbound trail-is-nil))
	((or (atom (car headpats)) (eq (caar headpats) 'nth))
         (compile-clause-with-atomic-head
          headpats headlocs body vars unbound trail-is-nil))
	(t
         (compile-clause-default
          headpats headlocs body vars unbound trail-is-nil))))

(defun compile-clause
    (headpats headlocs body vars unbound)
  (let ((trail-is-nil t))
    (compile-clause1 headpats headlocs body vars unbound trail-is-nil)))

(defun all-distinct-variable-arguments (clause variables)
  (let (seen)
    (dolist (arg (clause-args clause) t)
      (if (or (eq arg '_) (and (member arg variables) (not (member arg seen))))
	  (push arg seen)
	  (return nil)))))

(defun all-constant-arguments (clause variables)
  (dolist (arg (clause-args clause) t)
    (if (or (not (atom arg)) (eq arg '_) (member arg variables))
        (return nil))))

(defun compile-procedure-for-constant-first-argument (clauses variables)
  (do ((*first-argument-type* :constant-first-argument)
       (clauses clauses (cdr clauses))
       (compiled-clauses nil)
       (unbound variables)
       (clause)
       (*clausenum*))
      ((null clauses)
       (wrap-progn
        (nconc
	   (if (not *allow-repeated-goals*)
               (list
                `(when ,(identical-to-ancestor-call *name* *arity* *first-argument-type*)
                   (return-from ,*name* nil))))
	   (if (not *incomplete-inference*)
               (list
                `(when ,(reduce-by-ancestor-call *name* *arity* *first-argument-type*)
                   (return-from ,*name* nil))))
	   (nreverse compiled-clauses))))
    (declare (special *clausenum*))
    (setf clause (car clauses))
    (setf *clausenum* (cdr (assoc clause *clause-numbers*)))
    (unless (not (atom (first (clause-args clause))))
      (push (cond ((eq (first (clause-args clause)) '_)
		   (wrap-depth-test
		     (compile-clause (rest (clause-args clause))
                                     (rest (head-locs (clause-args clause)))
				     (clause-body clause) variables unbound)
		     (clause-body clause)))
		  ((member (first (clause-args clause)) variables)
		   (wrap-depth-test
		     (compile-clause (replace-variable-in-terms
                                      (first (clause-args clause))
                                      '!arg1! (rest (clause-args clause)))
				     (rest (head-locs (clause-args clause)))
				     (replace-variable-in-term
                                      (first (clause-args clause))
                                      '!arg1! (clause-body clause))
				     (cons '!arg1! variables)
				     (remove (first (clause-args clause)) unbound))
		     (clause-body clause)))
		  ((and (not (null (cdr clauses)))
			(all-constant-arguments clause variables)
			(equal (clause-body clause) (clause-body (cadr clauses)))
			(all-constant-arguments (cadr clauses) variables))
		   (setf *clausenum* nil)
		   (setf clauses (cdr clauses))
		   (do ((values (list (if (= *arity* 1)
                                          (first (clause-args (car clauses)))
                                          (clause-args (car clauses)))
				      (if (= *arity* 1)
                                          (first (clause-args clause))
                                          (clause-args clause)))
				(cons (if (= *arity* 1)
                                          (first (clause-args (car clauses)))
                                          (clause-args (car clauses)))
                                      values)))
		       ((not (and (not (null (cdr clauses)))
				  (equal (clause-body clause)
                                         (clause-body (cadr clauses)))
				  (all-constant-arguments (cadr clauses) variables)))
			`(dolist (!vector! ',(nreverse values))
			   (when (eql !arg1!
                                      ,(if (= *arity* 1) `!vector! `(car !vector!)))
			     ,(wrap-depth-test
				(if (= *arity* 1)
				    (compile-clause
                                     nil nil (clause-body clause) variables unbound)
				    (compile-clause
                                     (head-locs (rest (clause-args clause)) '!vector! t)
                                     (cdr (head-locs (clause-args clause)))
                                     (clause-body clause) variables unbound))
				(clause-body clause)))))
		     (setf clauses (cdr clauses))))
		  (t `(when (eql !arg1! ',(first (clause-args clause)))
			,(wrap-depth-test
			   (compile-clause
                            (rest (clause-args clause))
                            (rest (head-locs (clause-args clause)))
                            (clause-body clause) variables unbound)
			   (clause-body clause)))))
	    compiled-clauses))))

(defun compile-procedure-for-compound-first-argument (clauses variables)
  (do ((*first-argument-type* :compound-first-argument)
       (clauses clauses (cdr clauses))
       (compiled-clauses nil)
       (unbound variables)
       (clause)
       (*clausenum*))
      ((null clauses)
       (wrap-progn
	 (nconc
	   (if (not *allow-repeated-goals*)
               (list
                `(when ,(identical-to-ancestor-call *name* *arity* *first-argument-type*)
                   (return-from ,*name* nil))))
	   (if (not *incomplete-inference*)
               (list
                `(when ,(reduce-by-ancestor-call *name* *arity* *first-argument-type*)
                   (return-from ,*name* nil))))
	   (nreverse compiled-clauses))))
    (declare (special *clausenum*))
    (setf clause (car clauses))
    (setf *clausenum* (cdr (assoc clause *clause-numbers*)))
    (unless (and (atom (first (clause-args clause)))
		 (not (eq (first (clause-args clause)) '_))
		 (not (member (first (clause-args clause)) variables)))
      (push (cond ((eq (first (clause-args clause)) '_)
		   (wrap-depth-test
		     (compile-clause
                      (rest (clause-args clause))
                      (rest (head-locs (clause-args clause)))
                      (clause-body clause) variables unbound)
		     (clause-body clause)))
		  ((member (first (clause-args clause)) variables)
		   (wrap-depth-test
                    (compile-clause
                     (replace-variable-in-terms
                      (first (clause-args clause))
                      '!arg1! (rest (clause-args clause)))
                     (rest (head-locs (clause-args clause)))
                     (replace-variable-in-term
                      (first (clause-args clause))
                      '!arg1! (clause-body clause))
                     (cons '!arg1! variables)
                     (remove (first (clause-args clause)) unbound))
                    (clause-body clause)))
		  (t `(when (eq (car !arg1!) ',(car (first (clause-args clause))))
			,(wrap-depth-test
                          (compile-clause
                           (append (rest (first (clause-args clause)))
                                   (rest (clause-args clause)))
                           (append (head-locs
                                    (rest (first (clause-args clause))) '!arg1! t)
                                   (rest (head-locs (clause-args clause))))
                           (clause-body clause) variables unbound)
                          (clause-body clause)))))
	    compiled-clauses))))

(defun compile-procedure-for-variable-first-argument (clauses  variables)
  (do ((*first-argument-type* :variable-first-argument)
       (clauses clauses (cdr clauses))
       (compiled-clauses nil)
       (unbound variables)
       (clause)
       (*clausenum*))
      ((null clauses)
       (wrap-progn
        (nconc
         (if (not *allow-repeated-goals*)
             (list
              `(when ,(identical-to-ancestor-call *name* *arity* *first-argument-type*)
                 (return-from ,*name* nil))))
	   (if (not *incomplete-inference*)
               (list
                `(when ,(reduce-by-ancestor-call *name* *arity* *first-argument-type*)
                   (return-from ,*name* nil))))
	   (nreverse compiled-clauses))))
    (declare (special *clausenum*))
    (setf clause (car clauses))
    (setf *clausenum* (cdr (assoc clause *clause-numbers*)))
    (push (cond ((eq (first (clause-args clause)) '_)
		 (wrap-depth-test
		   (compile-clause
                    (rest (clause-args clause))
                    (rest (head-locs (clause-args clause)))
                    (clause-body clause) variables unbound)
		   (clause-body clause)))
		((member (first (clause-args clause)) variables)
		 (wrap-depth-test
		   (compile-clause
                    (replace-variable-in-terms
                     (first (clause-args clause)) '!arg1! (rest (clause-args clause)))
                    (rest (head-locs (clause-args clause)))
                    (replace-variable-in-term
                     (first (clause-args clause)) '!arg1! (clause-body clause))
				   (cons '!arg1! variables)
				   (remove (first (clause-args clause)) unbound))
		   (clause-body clause)))
		((and (not (null (cdr clauses)))
		      (all-constant-arguments clause variables)
		      (equal (clause-body clause) (clause-body (cadr clauses)))
		      (all-constant-arguments (cadr clauses) variables))
		 (setf *clausenum* nil)
		 (setf clauses (cdr clauses))
		 (do ((*first-argument-type* :variable-bound-to-constant-first-argument)
		      (values (list (if (= *arity* 1)
                                        (first (clause-args (car clauses)))
                                        (clause-args (car clauses)))
				    (if (= *arity* 1)
                                        (first (clause-args clause))
                                        (clause-args clause)))
			      (cons (if (= *arity* 1)
                                        (first (clause-args (car clauses)))
                                        (clause-args (car clauses)))
                                    values)))
		     ((not (and (not (null (cdr clauses)))
				(equal (clause-body clause)
                                       (clause-body (cadr clauses)))
				(all-constant-arguments (cadr clauses) variables)))
		      `(dolist (!vector! ',(nreverse values))
			 ,(wrap-depth-test
                           (if (= *arity* 1)
                               `(progn
                                  (bind-variable-to-term !arg1! !vector! :trail)
                                  ,(compile-clause
                                    nil nil (clause-body clause) variables unbound)
                                  (undo-bindings))
                               `(progn
                                  (bind-variable-to-term !arg1! (car !vector!) :trail)
                                  ,(compile-clause
                                    (head-locs (rest (clause-args clause)) '!vector! t)
                                    (cdr (head-locs (clause-args clause)))
                                    (clause-body clause) variables unbound)
                                  (undo-bindings)))
                           (clause-body clause))))
		   (setf clauses (cdr clauses))))
		((atom (first (clause-args clause)))
		 (let ((*first-argument-type* :variable-bound-to-constant-first-argument))
		   (wrap-depth-test
                    `(progn
                       (bind-variable-to-term
                        !arg1! ',(first (clause-args clause)) :trail)
                       ,(compile-clause (rest (clause-args clause))
                                        (rest (head-locs (clause-args clause)))
                                        (clause-body clause) variables unbound)
                       (undo-bindings))
                    (clause-body clause))))
		(t (wrap-depth-test
		     (let ((*first-argument-type*
                             :variable-bound-to-compound-first-argument)
			   (unbound
                             (remove-if #'(lambda (v)
                                            (variable-occurs-in-term-p
                                             v
                                             (first (clause-args clause))))
                                        unbound)))
		       (stack-list-new-variables
			 (remove-if-not #'(lambda (v)
                                            (variable-occurs-in-term-p
                                             v (first (clause-args clause))))
                                        variables)
			 `(let
                              ((!compound! ,(term-constructor
                                             (first (clause-args clause))
                                             variables)))
			    (progn (bind-variable-to-term !arg1! !compound! :trail)
				   ,(compile-clause
                                     (rest (clause-args clause))
                                     (rest (head-locs (clause-args clause)))
                                     (clause-body clause) variables unbound)
				   (undo-bindings)))))
		     (clause-body clause))))
	  compiled-clauses)))

(defun compile-procedure (*name* variables clauses
                          &key ((:traceable *traceable*) nil)
                               ((:unbounded-search *unbounded-search*) nil)
                               ((:unsafe-unification *unsafe-unification*) nil)
                               ((:incomplete-inference *incomplete-inference*) nil)
                               ((:allow-repeated-goals *allow-repeated-goals*) nil)
                               (split-procedure nil)
                               (collapse-clauses nil))
  (declare (ignore collapse-clauses))
  (let ((*arity* (get *name* 'arity)) 
        parameters
        (unbound variables)
        (lisp-compile-time 0))
    (when (eq *name* 'query/0)
      (setf *traceable* nil)
      (setf *unbounded-search* t)
      (setf *incomplete-inference* t)
      (setf *allow-repeated-goals* t))
    (if (= *arity* 0) (setf split-procedure nil))
    (if (not *trace-calls*) (setf *traceable* nil))
    (setf parameters
          (list :count-calls *count-calls*
                :clause-numbers
                (mapcar #'(lambda (clause)
                            (cdr (assoc clause *clause-numbers* :test #'equal)))
                        clauses)
                :variables variables
                :traceable *traceable*
                :unbounded-search *unbounded-search*
                :unsafe-unification *unsafe-unification*
                :incomplete-inference *incomplete-inference*
                :allow-repeated-goals *allow-repeated-goals*
                :split-procedure split-procedure))
    (when (or *recompile*
              (not (equal clauses (get *name* 'compiled-clauses)))
              (not (equal parameters (get *name* 'compiled-parameters))))
      (let (arglist auxlist namec names namev defn defnc defns defnv)
        (when (not *allow-repeated-goals*)
          (dolist (clause clauses (setf *allow-repeated-goals* t))
            (when (> (clause-body-length (clause-body clause)) 0)
              (return))))
        (setf arglist
              (append (head-locs *arity*) '(!level! !continuation!)))
        (setf auxlist
              (append arglist '(&aux (!old-trail! (rt-trail-index *runtime-data*)))))
        (when (or (not *allow-repeated-goals*) (not *incomplete-inference*))
          (eval `(defvar ,(ancestors-name *name*) nil))
          (eval `(defvar ,(ancestors-name (negated-functor *name*)) nil)))
        (setf defn
              (list 
               'lambda
               (if (and split-procedure (not (= *arity* 0))) arglist auxlist)
               '(declare (ignorable !old-trail!))
               `(incf !level!)
               (list 'block *name*
                     (wrap-call-fail-trace
                      (cond ((= *arity* 0)
                             (do ((*first-argument-type* nil)
                                  (clauses clauses (cdr clauses))
                                  (compiled-clauses nil)
                                  (clause)
                                  (*clausenum*))
                                 ((null clauses)
                                  (wrap-progn
                                   (nconc
                                    (if (not *allow-repeated-goals*)
                                        (list
                                         `(when ,(identical-to-ancestor-call
                                                  *name* 0 nil)
                                            (return-from ,*name* nil))))
                                    (if (not *incomplete-inference*)
                                        (list
                                         `(when ,(reduce-by-ancestor-call
                                                  *name* 0 nil)
                                            (return-from ,*name* nil))))
                                    (nreverse compiled-clauses))))
                               (declare (special *clausenum*))
                               (setf clause (car clauses))
                               (setf *clausenum*
                                     (cdr (assoc clause *clause-numbers*)))
                               (push (wrap-depth-test
                                      (compile-clause
                                       nil nil (clause-body clause)
                                       variables unbound)
                                      (clause-body clause))
                                     compiled-clauses)))
                            (split-procedure
                             (setf namec
                                   (intern 
                                    (concatenate 'string (symbol-name *name*) "C")
                                    'pttpp))
                             (setf names
                                   (intern
                                    (concatenate 'string (symbol-name *name*) "S")
                                    'pttpp))
                             (setf namev
                                   (intern
                                    (concatenate 'string (symbol-name *name*) "V")
                                    'pttpp))
                             (let ((nm (functor-name *name*)))
                               (setf (get namec 'name) nm)
                               (setf (get names 'name) nm)
                               (setf (get namev 'name) nm)
                               (setf (get namec 'arity) *arity*)
                               (setf (get names 'arity) *arity*)
                               (setf (get namev 'arity) *arity*))
                             (setf defnc
                                   (list
                                    'lambda
                                    auxlist
                                    (list 'block *name*
                                          (wrap-bind-args
                                           (compile-procedure-for-constant-first-argument
                                            clauses variables)))))
                             (setf defns
                                   (list
                                    'lambda
                                    auxlist
                                    (list 'block *name*
                                          (wrap-bind-args
                                           (compile-procedure-for-compound-first-argument
                                            clauses variables)))))
                             (setf defnv
                                   (list
                                    'lambda
                                    auxlist
                                    (list 'block *name*
                                          (wrap-bind-args
                                           (compile-procedure-for-variable-first-argument
                                            clauses variables)))))
                             `(dereference
                                  !arg1!
                                :if-constant  (,namec . ,arglist)
                                :if-compound  (,names . ,arglist)
                                :if-variable  (,namev . ,arglist)))
                            (t (wrap-bind-args
                                `(dereference
                                     !arg1!
                                   :if-constant
                                   ,(compile-procedure-for-constant-first-argument
                                     clauses variables)
                                   :if-compound
                                   ,(compile-procedure-for-compound-first-argument
                                     clauses variables)
                                   :if-variable
                                   ,(compile-procedure-for-variable-first-argument
                                     clauses variables)))))))))
        (when *print-compile-names*
          (format t "~&~A compiled from PTTPP to LISP" *name*))
        (setf lisp-compile-time (get-internal-run-time))
        (when (and split-procedure (> *arity* 0))
          (compile namec defnc)
          (compile names defns)
          (compile namev defnv))
        (compile *name* defn)
        (when *print-compile-names*
          (format t "~&~A compiled from LISP to machine code" *name*))
        (setf lisp-compile-time (- (get-internal-run-time) lisp-compile-time)))
      (setf (get *name* 'compiled-clauses) clauses)
      (setf (get *name* 'compiled-parameters) parameters))
    lisp-compile-time))

(defun *print-clauses* (clauses variables)
    (when variables
    (fresh-line)
    (terpri)
    (cond ((null (cdr variables))
	   (princ " The symbol ")
	   (write-term (car variables))
	   (princ " denotes a variable."))
	  (t (princ " The symbols ")
	     (write-term (car variables))
	     (do ((v (cdr variables) (cdr v)))
		 ((null (cdr v)) (princ " and ") (write-term (car v)))
	       (princ ", ") (write-term (car v)))
	     (princ " denote variables."))))
  (dolist (clause clauses)
    (write-clause clause (cdr (assoc clause *clause-numbers*)))))

(defun predicate-clauses (predicate clauses)
  (remove-if-not #'(lambda (clause) (eq (clause-pred clause) predicate))
		 clauses))

(defun program (variables wffs &rest options)
  (let (clauses predicates wff-number start-time stop-time (lisp-compile-time 0))
    (setf start-time (get-internal-run-time))
    (setf wffs (canonicalize-functors-in-terms wffs))
    (setf stop-time (get-internal-run-time))
    
    (when *print-clauses*
      (setf wff-number 0)
      (setf *clause-numbers* nil)
      (dolist (wff wffs)
	(incf wff-number)
	(push (cons wff wff-number) *clause-numbers*))
      (*print-clauses* wffs variables))
    
    (setf start-time (- (get-internal-run-time) (- stop-time start-time)))
    (setf wff-number 0)
    (setf *clause-numbers* nil)
    (dolist (wff wffs)
      (incf wff-number)
      (let ((cls (clauses-from-wff wff)))
	(cond ((null cls))			;if wff is tautology 2005-07-21
              ((null (cdr cls))
	       (push (car cls) clauses)
	       (push (cons (car clauses) wff-number) *clause-numbers*)
	       (pushnew (clause-pred (car clauses)) predicates))
	      (t (let ((literal-number 0))
		   (dolist (cl cls)
		     (incf literal-number)
		     (push cl clauses)
		     (push (cons (car clauses)
                                 (cons wff-number
                                       (numbered-letter literal-number)))
                           *clause-numbers*)
		     (pushnew (clause-pred (car clauses))
                              predicates)
		     (pushnew (negated-functor (clause-pred (car clauses)))
                              predicates)))))))
    (setf clauses (nreverse clauses))
    (setf predicates (nreverse predicates))
    
    (dolist (pred predicates)
      (incf lisp-compile-time
            (apply #'compile-procedure
                   (list* pred variables (predicate-clauses pred clauses)
                          options))))
    (setf stop-time (get-internal-run-time))
    
    (when *print-compile-times*
      (format t "~2&Compilation time: ~,3F seconds (PTTPP) + ~,3F seconds (LISP)~%"
	      (/ (- stop-time start-time lisp-compile-time)
                 +float-internal-time-units-per-second+)
	      (/ lisp-compile-time
                 +float-internal-time-units-per-second+)))
    
    nil))

(defvar *print-proof* t)
(defvar *print-trail* t)
(defvar *print-success-notification* t)
(defvar *single-solution* nil)
(defvar *number-of-solutions-found* 0)

(defvar *print-proof-time* 0)

(defun query-success (!level!)
  (declare (ignore !level!))
  (let ((*print-readably* t)
	(*print-circle* t))
    (when *print-success-notification*
      (if *print-trail*
	  (format t "~&Success:  trail = ~A,~%~4Ttrail-array = ~W.~%"
		  (rt-trail-index *runtime-data*)
                  (make-array `(,(1+ (rt-trail-index *runtime-data*)))
                              :displaced-to (rt-trail-array *runtime-data*)))
	  (format t "~&Success."))))
    (incf *number-of-solutions-found*)
  (if *single-solution*
      (throw 'query t)
      nil))

(defun query (&optional variables goal &rest options)
  (when goal
    (apply #'program variables (list* `((<- (query) ,goal)) options)))
  (let (start-time stop-time value time)
    (setf *ncalls* 0)
    (setf (rt-trail-index *runtime-data*) -1)
    (setf *trace-search-time* 0)
    (setf *print-proof-time* 0)
    (setf start-time (get-internal-run-time))
    (setf value (catch 'query 
		  (query/0 0 #'query-success)))
    (setf stop-time (get-internal-run-time))
    (when (> *ncalls* 0)
      (setf time
            (/ (max 1 (- stop-time start-time *trace-search-time* *print-proof-time*))
               (float internal-time-units-per-second)))
      (when *print-execution-time*
        (format t "~2&Execution time: ~:D inferences in ~,3F seconds (~,2F K lips)~%"
                *ncalls* time (/ *ncalls* time 1000))))
    value))


;; INPUT EXPRESSION CANONICALIZATION

(defun make-functor (name arity)
  (let ((l (get name 'functors)))
    (or (cdr (assoc arity l))
	(let ((w (intern (concatenate 'string (symbol-name name)
                                      "/" (princ-to-string arity))
                         'pttpp)))
	  (setf (get name 'functors) (cons (cons arity w) l))
	  (setf (get w 'arity) arity)
	  (setf (get w 'name) name)
	  w))))

(defun negated-functor (name)
  (or (get name 'negation)
      (let* ((s (symbol-name name))
	     (w (intern (if (and (>= (length s) 2) (char= (char s 0) '#\~))
			    (subseq s 1)
			    (concatenate 'string "~" s))
			'pttpp)))
	(setf (get name 'negation) w)
	(setf (get w 'negation) name)
	(let ((arity (get name 'arity)))
          (when arity (setf (get w 'arity) arity)))
	w)))

(defun functor-name (x)
  (or (get x 'name)
      (let* ((s (symbol-name x)) (n (length s)))
	(if (digit-char-p (char s (1- n)))
	    (do ((n (- n 2) (1- n)) (ch))
		((= n 0) x)
	      (setf ch (char s n))
	      (cond ((digit-char-p ch))
		    ((char= ch '#\/) (return (setf (get x 'name) (subseq s 0 n))))
		    (t (return (setf (get x 'name) x)))))
	    x))))

(defun functor-arity (x)
  (or (get x 'arity)
      (let* ((s (symbol-name x))
             (n (length s))
             (arity (digit-char-p (char s (1- n)))))
	(if arity
	    (do ((n (- n 2) (1- n)) (tens 10 (* 10 tens)) (ch) (num))
		((= n 0) '?)
	      (setf ch (char s n))
	      (setf num (digit-char-p ch))
	      (cond (num (incf arity (* tens num)))
		    ((char= ch '#\/) (setf (get x 'arity) arity) (return arity))
		    (t (return '?))))
	    '?))))

(defun negate (x)
  (cond ((equal x '(true/0)) '(false/0))
	((equal x '(false/0)) '(true/0))
	((and (not (atom x))
              (eq (car x) +and-connective+))
         (list +or-connective+ (negate (cadr x)) (negate (caddr x))))
	((and (not (atom x)) 
              (eq (car x) +or-connective+))
         (list +and-connective+ (negate (cadr x)) (negate (caddr x))))
	(t (cons (negated-functor (car x)) (cdr x)))))

(defun conjoin (x y)
  (cond ((equal x '(true/0)) y)
	((equal y '(true/0)) x)
	((equal x '(false/0)) x)
	((equal y '(false/0)) y)
	((and (not (atom x))
              (not (atom y))
              (eq (car x) (negated-functor (car y)))
              (equal (cdr x) (cdr y)))
         '(false/0))
	((and (not (atom x))
              (eq (car x) +and-connective+))
         (list +and-connective+ (cadr x) (list +and-connective+ (caddr x) y)))
	(t (list +and-connective+ x y))))

(defun disjoin (x y)
  (cond ((equal x '(false/0)) y)
	((equal y '(false/0)) x)
	((equal x '(true/0)) x)
	((equal y '(true/0)) y)
	((and (not (atom x))
              (not (atom y))
              (eq (car x) (negated-functor (car y)))
              (equal (cdr x) (cdr y)))
         '(true/0))
	((and (not (atom x))
              (eq (car x) +or-connective+))
         (list +or-connective+ (cadr x) (list +or-connective+ (caddr x) y)))
	(t (list +or-connective+ x y))))

(defun convert-string-to-list (s)
  (do ((i (1- (length s)) (1- i)) (w '|[]|))
      ((< i 0) w)
    (setf w `(cons/2 ,(char-code (char s i)) ,w))))

(defun canonicalize-functors-in-term (term)
  (cond ((atom term)
         (cond ((null term) '|[]|)
               ((stringp term) (convert-string-to-list term))
               (t term)))
	((not (symbolp (car term)))
         (error "Nonsymbol functor ~A" (car term)))
	((member (car term) '(and \ \& \,))
	 (if (null (cddr term))
	     (canonicalize-functors-in-term (cadr term))
	     (conjoin
              (canonicalize-functors-in-term (cadr term))
              (if (cdddr term)
                  (canonicalize-functors-in-term (cons (car term) (cddr term)))
                  (canonicalize-functors-in-term (caddr term))))))
	((member (car term) '(or \ \| \;))
	 (if (null (cddr term))
	     (canonicalize-functors-in-term (cadr term))
	     (disjoin
              (canonicalize-functors-in-term (cadr term))
              (if (cdddr term)
                  (canonicalize-functors-in-term (cons (car term) (cddr term)))
                  (canonicalize-functors-in-term (caddr term))))))
	((member (car term) '(\ imply imp implies))
	 (disjoin
          (negate (canonicalize-functors-in-term (cadr term)))
          (canonicalize-functors-in-term (caddr term))))
	((member (car term) '(\ equiv equ iff))
	 (let ((x (canonicalize-functors-in-term (cadr term)))
               (y (canonicalize-functors-in-term (caddr term))))
	   (conjoin (disjoin (negate x) y) (disjoin x (negate y)))))
	(t (cons (make-functor (car term) (length (cdr term)))
                 (canonicalize-functors-in-terms (cdr term))))))

(defun canonicalize-functors-in-terms (terms)
  (cond ((null terms) nil)
	(t (let ((x (canonicalize-functors-in-term (car terms)))
                 (y (canonicalize-functors-in-terms (cdr terms))))
	     (if (and (eq x (car terms)) (eq y (cdr terms))) terms (cons x y))))))


;; CONVERSION OF NONCLAUSAL INPUTS TO CLAUSE FORM

(defun clause-body-for-literal (lit wff)
  (let ((~f nil))
    (cond ((atom wff) wff)
          ((eq (car wff) +and-connective+)
           (disjoin (clause-body-for-literal lit (cadr wff))
                    (clause-body-for-literal lit (caddr wff))))
          ((eq (car wff) +or-connective+)
           (conjoin (clause-body-for-literal lit (cadr wff))
                    (clause-body-for-literal lit (caddr wff))))
          ((equal lit wff) '(true/0))
          ((and (eq (car lit) (setf ~f (negated-functor (car wff))))
                (equal (cdr lit) (cdr wff)))
           '(false/0))
          (t (cons ~f (cdr wff))))))

(defun literals-in-wff (wff &optional literals)
  (cond ((and (not (atom wff))
              (or (eq (car wff) +and-connective+) (eq (car wff) +or-connective+)))
	 (literals-in-wff (caddr wff) (literals-in-wff (cadr wff) literals)))
	(t (pushnew wff literals :test #'equal))))

(defun clauses-from-wff (wff)
  (cond ((eq (car wff) +and-connective+)
	 (nconc (clauses-from-wff (cadr wff)) (clauses-from-wff (caddr wff))))
	((eq (car wff) +or-connective+)
	 (let (result)
	   (dolist (lit (literals-in-wff wff))
	     (when (not (atom lit))		;don't promote ! to head
	       (push (list '<-/2 lit (clause-body-for-literal lit wff)) result)))
	   result))
        ((eq (car wff) 'true/0) nil)		;if wff is tautology 2005-07-21
	(t (list wff))))

