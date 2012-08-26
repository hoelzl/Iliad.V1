;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;; 
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp)
(declaim (optimize (debug 3)))

(eval-when (:compile-toplevel :load-toplevel :execute)
(defvar *integration-test-generators* '())

(defmacro generate-integration-test (name &body body)
  (let ((generator-name (let ((*print-case* :upcase))
                          (intern (format nil "~A-GENERATOR" name)))))
    (pushnew generator-name *integration-test-generators*)
    `(defun ,generator-name ()
       (let ((print-compile-names nil)
             (print-compile-times nil)
             (*print-execution-time* nil)
             (print-clauses nil)
             (*trace-search* nil)
             (*print-proof* nil)
             (*print-trail* nil)
             (*print-success-notification* nil)
             (*single-solution* t))
         ,@body
         (let ((bindings '())
               (tests `((5am:is (= ,*trail* *trail*))))
               (counter 0))
           (labels ((name (prefix)
                      (intern (format nil "~A-~A" prefix (incf counter))))
                    (walk (obj form)
                      (cond ((variable-p obj)
                             (let* ((name (name "VAR"))
                                    (value (variable-value obj)))
                               (push `(,name ,form) bindings)
                               (push `(5am:is (= ',(variable-level obj)
                                                 (variable-level ,name)))
                                     tests)
                               (push `(5am:is (equal ',(variable-name obj)
                                                     (variable-name ,name)))
                                     tests)
                               (if (atom value)
                                   (push `(5am:is (equal ',value
                                                         (variable-value ,name)))
                                         tests)
                                   (walk value `(variable-value ,name)))))
                            ((consp obj)
                             (let ((name (name "PRED")))
                               (push `(,name ,form) bindings)
                               (dotimes (i (length obj))
                                 (if (zerop i)
                                     (push `(5am:is (eql ',(nth i obj)
                                                         (first ,name))) tests)
                                     (let ((value (nth i obj)))
                                       (if (atom value)
                                           (push `(5am:is (equal ',value
                                                                 (nth ,i ,name)))
                                                 tests)
                                           (walk value `(nth ,i ,name))))))))
                            (t
                             (warn "Don't know how to handle ~A, ~A." obj form)))))
             (dotimes (i *trail*)
               (walk (aref *trail-array* i) `(aref *trail-array* ,i)))
             `(define-integration-test ,',name
                ,@',body
                (let* (,@(nreverse bindings))
                  ,@(nreverse tests)))))))))

(defun run-all-generators (&optional (output-stream nil))
  (let ((*print-case* :downcase)
        (*print-circle* nil)
        (*print-readably* t))
    (format output-stream "~&~{#+5AM~%~W~2%~}"
            (mapcar (lambda (g)
                      (funcall g))
                    (reverse *integration-test-generators*)))))

(defun generate-file (file-name)
  (with-open-file (stream file-name :direction :output :if-exists :supersede)
    (format stream
            "~
;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: PTTPP; Base: 10; common-lisp-style: poem -*-

;;; Copyright (c) 1986 Mark E. Stickel, SRI International, Menlo Park, CA 94025 USA
;;; Copyright (c) 2012 Matthias Hölzl
;;; 
;;; This file is licensed under the MIT license; see the file LICENSE
;;; in the root directory for further information.

(in-package #:pttpp)
(declaim (optimize (debug 3)))~3%")
    (run-all-generators stream)))
) ;; eval-when

#+5am
(generate-integration-test chang&lee-test-1
  (program '(u v w x y z)
	   '((p (g x y) x y)
	     (p x (h x y) y)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p (k x) x (k x))) !)))
	   :incomplete-inference t)
  (query))

#+5am
(generate-integration-test chang&lee-test-2
  (program '(u v w x y z)
	   '((p e x x)
	     (p x e x)
	     (p x x e)
	     (p a b c)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p b a c)) !)))
	   :incomplete-inference t)
  (query))

#+5am
(generate-integration-test chang&lee-test-3
  (program '(u v w x y z)
	   '((p e x x)
	     (p (i x) x e)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p a e a)) !)))
	   :incomplete-inference t)
  (query))

#+5am
(generate-integration-test chang&lee-test-4
  (program '(u v w x y z)
	   '((p e x x)
	     (p (i x) x e)
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (p a x e)) !)))
	   :incomplete-inference t)
  (query))

#+5am
(generate-integration-test chang&lee-test-5
  (program '(u v w x y z)
	   '((p e x x)
	     (p x e x)
	     (p x (i x) e)
	     (p (i x) x e)
	     (s a)
	     (-> (and (s x) (s y) (p x (i y) z)) (s z))
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (s e)) !)))
	   :incomplete-inference t)
  (query))

#+5am
(generate-integration-test chang&lee-test-6
  (program '(u v w x y z)
	   '((p e x x)
	     (p x e x)
	     (p x (i x) e)
	     (p (i x) x e)
	     (s a)
	     (-> (and (s x) (s y) (p x (i y) z)) (s z))
	     (-> (and (p x y u) (p y z v) (p x v w)) (p u z w))
	     (-> (and (p x y u) (p y z v) (p u z w)) (p x v w))
	     (<- (query) (and (search (s (i a))) !)))
	   :incomplete-inference t)
  (query))

#+5am
(generate-integration-test chang&lee-test-7
  (program '(u x y z)
	   '((p a)
	     (m a (s c) (s b))
	     (m x x (s x))
	     (or (~m x y z) (m y x z))
	     (or (~m x y z) (d x z))
	     (or (~p x) (~m y z u) (~d x u) (d x y) (d x z))
	     (<- (query) (and (search (d a b)) !))))
  (query))

#+5am
(generate-integration-test chang&lee-test-8
  (program '(x y z)
	   '((l 1 a)
	     (d x x)
	     (or (p x) (d (g x) x))
	     (or (p x) (l 1 (g x)))
	     (or (p x) (l (g x) x))
	     (or (~p x) (~d x a))		; negation of theorem
	     (or (~d x y) (~d y z) (d x z))
	     (or (~l 1 x) (~l x a) (p (f x)))
	     (or (~l 1 x) (~l x a) (d (f x) x))
	     (<- (query) (and (search (and (p x) (d x a))) !))))
  (query))

#+5am
(generate-integration-test chang&lee-test-9
  (program '(x y)
	   '((l x (f x))
	     (~l x x)
	     (or (~l x y) (~l y x))
	     (or (~d x (f y)) (l y x))
	     (or (p x) (d (h x) x))
	     (or (p x) (p (h x)))
	     (or (p x) (l (h x) x))
	     (or (~p x) (~l a x) (l (f a) x))	; negation of theorem
	     (<- (query) (and (search (and (p x) (l a x) (~l (f a) x))) !))))
  (query))
