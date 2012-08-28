;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;;
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

;;; The built-in Prolog predicates of PTTPP.
;;; =======================================

(in-package #:pttpp)
;; (declaim (optimize (debug 3)))
;; (declaim (optimize (speed 2) (compilation-speed 0)))

#+5am
(5am:in-suite pttpp-builtins-suite)

;; Prolog built-in predicates

;; Auxiliary variable !NSUBGOALS! with value '(0 NIL) necessary for proof
;; printing due to bug in DBG:FRAME-LOCAL-VALUE that causes an error if named
;; variable isn't found

(defun call/1 (x !level! !continuation!)
  (incf !level!)
  (dereference x
    :if-variable (error "CALL was given non-compound argument ~A" x)
    :if-constant (error "CALL was given non-compound argument ~A" x)
    :if-compound (apply (car x)
                        ;; inefficient
                        (append (cdr x) (list !level! !continuation!)))))

(defun not/1 (x !level! !continuation!)
  (not-solvable x 1000000 !level! !continuation!))

(defun not/2 (x y !level! !continuation!)
  (not-solvable x y !level! !continuation!))

(defun y-or-n-p/0 (!level! !continuation!)
  (incf !level!)
  (if (y-or-n-p)
      (funcall !continuation! !level!)
      nil))

(defun y-or-n-p/1 (x !level! !continuation!)
  (incf !level!)
  (fresh-line) (write-term x) (princ "? ")
  (if (y-or-n-p)
      (funcall !continuation! !level!)
      nil))

(defun atomic/1 (x !level! !continuation!)
  (incf !level!)
  (and (dereference x) (funcall !continuation! !level!)))

(defun atom/1 (x !level! !continuation!)
  (incf !level!)
  (and (dereference x) (symbolp x) (funcall !continuation! !level!)))

(defun integer/1 (x !level! !continuation!)
  (incf !level!)
  (and (dereference x) (integerp x) (funcall !continuation! !level!)))

(defun var/1 (x !level! !continuation!)
  (incf !level!)
  (dereference x
    :if-constant  nil
    :if-variable  (funcall !continuation! !level!)
    :if-compound  nil))

(defun nonvar/1 (x !level! !continuation!)
  (incf !level!)
  (dereference x
    :if-constant  (funcall !continuation! !level!)
    :if-variable  nil
    :if-compound  (funcall !continuation! !level!)))

(defun functor/3 (term functor arity !level! !continuation!
                  &aux (!old-trail! (rt-trail-index *runtime-data*)))
  (incf !level!)
  (dereference
      term
    :if-variable
    (when (and (dereference functor) (dereference arity))
      (case arity
	(0 (progn (bind-variable-to-term term functor :trail)
		  (funcall !continuation! !level!)
		  (undo-bindings)))
        ;; (new-variable '_)
	(1 (let ((struct (list functor
                               (new-variable 'z1 !level!))))	
	     (progn (bind-variable-to-term term struct :trail)
		    (funcall !continuation! !level!)
		    (undo-bindings))))
	(2 (let ((struct (list functor
                               (new-variable 'z1 !level!)
                               (new-variable 'z2 !level!))))
	     (progn (bind-variable-to-term term struct :trail)
		    (funcall !continuation! !level!)
		    (undo-bindings))))
	(3 (let ((struct (list functor
                               (new-variable 'z1 !level!)
                               (new-variable 'z2 !level!)
                               (new-variable 'z3 !level!))))
	     (progn (bind-variable-to-term term struct :trail)
		    (funcall !continuation! !level!)
		    (undo-bindings))))
	(4 (let ((struct (list functor
                               (new-variable 'z1 !level!)
                               (new-variable 'z2 !level!)
                               (new-variable 'z3 !level!)
                               (new-variable 'z4 !level!))))
	     (progn (bind-variable-to-term term struct :trail)
		    (funcall !continuation! !level!)
		    (undo-bindings))))
	(5 (let ((struct (list functor
                               (new-variable 'z1 !level!)
                               (new-variable 'z2 !level!)
                               (new-variable 'z3 !level!)
                               (new-variable 'z4 !level!)
                               (new-variable 'z5 !level!))))
	     (progn (bind-variable-to-term term struct :trail)
		    (funcall !continuation! !level!)
		    (undo-bindings))))
	(otherwise
         (error "Functor argument of FUNCTOR has arity ~A.  Unimplemented"
                arity))))
    :if-constant
    (when (and (always-trails-unify functor term !old-trail!)
               (always-trails-unify arity 0 !old-trail!))
      (funcall !continuation! !level!) (undo-bindings))
    :if-compound 
    (when (and (always-trails-unify functor (car term) !old-trail!)
               (always-trails-unify arity (length (cdr term)) !old-trail!))
      (funcall !continuation! !level!) (undo-bindings))))

(defun arg/3 (index term arg !level! !continuation!
              &aux (!old-trail! (rt-trail-index *runtime-data*)))
  (incf !level!)
  (dereference term
    :if-variable  (error "ARG was given non-compound second argument ~A" term)
    :if-constant  (error "ARG was given non-compound second argument ~A" term)
    :if-compound  (progn
                    (dereference index)
                    (cond ((not (integerp index))
                           (error "ARG was given non-integer first argument ~A"
                                  index))
                          ((or (< index 1) (> index (length (cdr term))))
                           (error
                            "ARG was given out-of-range first argument ~A for term ~A"
                            index term))
                          (t (when (always-trails-unify
                                    arg (nth (1- index) (cdr term)) !old-trail!)
                               (funcall !continuation! !level!)
                               (undo-bindings)))))))

(defun is/2 (x y !level! !continuation!
             &aux (!old-trail! (rt-trail-index *runtime-data*)))
  (incf !level!)
  (labels ((evaluate (term)
             (if (dereference term)
                 term
                 (case (length (cdr term))
                   (0 (funcall (car term)))
                   (1 (funcall (car term) (evaluate (cadr term))))
                   (2 (funcall (car term) (evaluate (cadr term))
                               (evaluate (caddr term))))
                   (3 (funcall (car term) (evaluate (cadr term))
                               (evaluate (cadddr term))))
                   (otherwise
                    (error "Function argument of IS has ~A arguments.  Unimplemented"
                           (length (cdr term))))))))
    (let ((y (evaluate y)))
      (when (unify-argument-with-constant x y :trail-is-nil t)
	(funcall !continuation! !level!)
        (undo-bindings)))))

(defun =/2 (x y !level! !continuation!
            &aux (!old-trail! (rt-trail-index *runtime-data*)))
  (incf !level!)
  (when (always-trails-unify x y !old-trail!)
    (funcall !continuation! !level!)
    (undo-bindings)))

(defun \\=/2 (x y !level! !continuation! &aux (!old-trail! (rt-trail-index *runtime-data*)))
  (incf !level!)
  (if (always-trails-unify x y !old-trail!)
      (undo-bindings)
      (funcall !continuation! !level!)))

(defun unsafe-=/2 (x y !level! !continuation! &aux (!old-trail! (rt-trail-index *runtime-data*)))
  (incf !level!)
  (when (unsafe-always-trails-unify x y !old-trail!)
    (funcall !continuation! !level!)
    (undo-bindings)))

(defun unsafe-\\=/2 (x y !level! !continuation! &aux (!old-trail! (rt-trail-index *runtime-data*)))
  (incf !level!)
  (if (unsafe-always-trails-unify x y !old-trail!)
      (undo-bindings)
      (funcall !continuation! !level!)))

(defun ==/2 (x y !level! !continuation!)
  (incf !level!)
  (and (identical x y)
       (funcall !continuation! !level!)))

(defun \\==/2 (x y !level! !continuation!)
  (incf !level!)
  (and (not (identical x y))
       (funcall !continuation! !level!)))

(defun >/2 (x y !level! !continuation!)
  (incf !level!)
  (and (dereference x)
       (dereference y)
       (> x y)
       (funcall !continuation! !level!)))

(defun </2 (x y !level! !continuation!)
  (incf !level!)
  (and (dereference x)
       (dereference y)
       (< x y)
       (funcall !continuation! !level!)))

(defun >=/2 (x y !level! !continuation!)
  (incf !level!)
  (and (dereference x)
       (dereference y)
       (>= x y)
       (funcall !continuation! !level!)))

(defun =</2 (x y !level! !continuation!)
  (incf !level!)
  (and (dereference x)
       (dereference y)
       (<= x y)
       (funcall !continuation! !level!)))

(setf (invisible-functor-p 'nl/0) t)
(defun nl/0 (!level! !continuation!)
  (incf !level!)
  (terpri)
  (funcall !continuation! !level!))

(setf (invisible-functor-p 'dislay/1) t)
(defun display/1 (x !level! !continuation!)
  (incf !level!)
  (display-term x)
  (funcall !continuation! !level!))

(setf (invisible-functor-p 'write/1) t)
(defun write/1 (x !level! !continuation!)
  (incf !level!)
  (write-term x)
  (funcall !continuation! !level!))

(setf (invisible-functor-p 'trace/0) t)
(defun trace/0 (&optional (!level! 0) !continuation!)
  (incf !level!)
  (setq *tracing* t)
  (if !continuation!
      (funcall !continuation! !level!)))

;; and !continuation! arguments of trace/0, notrace/0, spy/1, nospy/1,
;; nodebug/0, debugging/0, op/3 are optional to make them easier to use as
;; user callable functions

(setf (invisible-functor-p 'notrace/0) t)
(defun notrace/0 (&optional (!level! 0) !continuation!)
  (incf !level!)
  (setq *tracing* nil)
  (if !continuation!
      (funcall !continuation! !level!)))

(setf (invisible-functor-p 'spy/1) t)
(defun spy/1 (x &optional (!level! 0) !continuation!)
  ;; takes single predicate argument, e.g., (spy reverse/2) (spy reverse),
  ;; (spy (reverse 2)), (spy [reverse,concatenate]), etc. not allowed
  (incf !level!)
  (pushnew x *spy-points*)
  (if !continuation!
      (funcall !continuation! !level!)))

(setf (invisible-functor-p 'nospy/1) t)
(defun nospy/1 (x &optional (!level! 0) !continuation!)
  ;; takes single predicate argument, e.g., (nospy reverse/2) (nospy reverse),
  ;; (nospy (reverse 2)), (nospy [reverse,concatenate]), etc. not allowed
  (incf !level!)
  (setq *spy-points* (delete x *spy-points*))
  (if !continuation!
      (funcall !continuation! !level!)))

(setf (invisible-functor-p 'nodebug/0) t)
(defun nodebug/0 (&optional (!level! 0) !continuation!)
  (incf !level!)
  (setq *spy-points* nil)
  (if !continuation!
      (funcall !continuation! !level!)))

(setf (invisible-functor-p 'debugging/0) t)
(defun debugging/0 (&optional (!level! 0) !continuation!)
  (incf !level!)
  (cond ((null *spy-points*) (princ "[]"))
	(t (princ "[") (princ (car *spy-points*))
           (dolist (x (cdr *spy-points*))
             (princ ",") (princ x)) (princ "]")))
  (if !continuation!
      (funcall !continuation! !level!)))


(defun op/3 (prec spec name &optional (!level! 0) !continuation!)
  (incf !level!)
  (when (not (numberp prec)) (error "Non-numeric precedence ~A" prec))
  (case spec
    ((fx fy xf yf)
     (let ((arity (functor-arity name)))
       (case arity
	 (? 
          (setq name (make-functor name 1))
          (setf (precedence name) prec)
          (setf (specifier name) spec))
	 (1
          (setf (precedence name) prec)
          (setf (specifier name) spec))
	 (otherwise
          (error "Functor ~A is ~D-ary, but specifier ~A is 1-ary"
                 name arity spec)))))
    ((xfx xfy yfx yfy)
     (let ((arity (functor-arity name)))
       (case arity
	 (?
          (setq name (make-functor name 2))
          (setf (precedence name) prec)
          (setf (specifier name) spec))
	 (2
          (setf (precedence name) prec)
          (setf (specifier name) spec))
	 (otherwise
          (error "Functor ~A is ~D-ary, but specifier ~A is 2-ary"
                 name arity spec)))))
    (otherwise
     (error "Unknown position/associativity specifier ~A" spec)))
  (if !continuation!
      (funcall !continuation! !level!)))

(op/3 1200 'xfx '<-)				; unimplemented
(op/3 1200 'xfx '-->)				; unimplemented
(op/3 1200 'fx  '|:-|)				; unimplemented
(op/3 1200 'fx  '?-)				; unimplemented
(op/3 1100 'xfy +or-connective+)
(op/3 1100 'xf  '\;)				; unimplemented
(op/3 1050 'xfy '->)				; unimplemented
(op/3 1000 'xfy +and-connective+)
(op/3  800 'fx  'not)				; unimplemented
(op/3  700 'xfx '=)
(op/3  700 'xfx '\\=)
(op/3  700 'xfx '==)
(op/3  700 'xfx '\\==)
(op/3  700 'xfx 'is)
(op/3  700 'xfx '|=..|)				; unimplemented
(op/3  700 'xfx '<)
(op/3  700 'xfx '>)
(op/3  700 'xfx '=<)
(op/3  700 'xfx '>=)
(op/3  500 'yfx '+)
(op/3  500 'yfx '-)
(op/3  500 'fx  '+)
(op/3  500 'fx  '-)
(op/3  400 'yfx '*)
(op/3  400 'yfx '/)
(op/3  300 'xfx 'mod)


;;; Prolog built-in functions (for IS/2 predicate interpretation)

(defun |+/1| (m)
  m)

(defun |-/1| (m)
  (- m))

(defun |+/2| (m n)
  (+ m n))

(defun |-/2| (m n)
  (- m n))

(defun */2 (m n)
  (* m n))

(defun //2 (m n)
  (truncate m n))

(defun mod/2 (m n)
  (rem m n))

(defun cputime/0 ()
  (get-internal-run-time))


;;; Proof Printing Facility
;;;
;;; This was a Symbolics-only feature and will have to be re-implemented in a
;;; portable manner.
