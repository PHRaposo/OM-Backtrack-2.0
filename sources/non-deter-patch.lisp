;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; REVISED VERSION (RESTORATION OF OM-BACKTRACK)
;;; Copyright 2024 PAULO HENRIQUE RAPOSO AND KARIM HADDAD
;;;
;;; OM-BACKTRACK 2.0
;;; Copyright 2024 PAULO HENRIQUE RAPOSO
;;;

(in-package :om)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; NON-DETER-PATCH?
;;;
(defmethod non-deter-patch? ((self OMPatch)) 
 (let ((record (s::get-function-record (intern (string (car (list! (code self)))) :om))))
  (not (s::function-record-deterministic? record))))

(defmethod non-deter-patch? ((self OMLispPatch))
  (let ((exp (get-lisp-exp (lisp-exp self))))
    (handler-case
        (not (s::function-record-deterministic?
              (s::get-function-record
               (eval `(screamer::defun ,(intern (string (code self)) :om)
                                       ,.(cdr exp))))))
      (error () nil))))

;;; ----------------------------------------------------------------
;;; Visual indicator on the patch icon.

(defmethod om-draw-contents :after ((self patch-icon-box))
  (when (non-deter-patch? (reference (object (om-view-container self))))
    (om-with-fg-color self *om-pink-color*
      (om-with-font (om-make-font "Courier"
                                  (* *icon-size-factor*
                                     (if (>= cl-user::*version* 8) 30 34)))
        (om-draw-char (- (round (w self) 2) (* *icon-size-factor* 10))
                      (+ (round (h self) 2) (* *icon-size-factor* 10))
                      #\?)))))

(defmethod om-draw-contents :after ((self patch-finder-icon))
  (let* ((obj (object (om-view-container self)))
         (obj-type (type-of obj)))
   (when (and (member obj-type '(ompatch omlisppatch) :test #'eq)
              (non-deter-patch? obj))
   (cond ((big-icon-p (editor (om-view-container self)))
          (om-with-fg-color self *om-pink-color*
           (om-with-font (om-make-font "Courier"
                                       (* *icon-size-factor*
                                         (if (>= cl-user::*version* 8) 30 34)))
            (om-draw-char (- (round (w self) 2) (* *icon-size-factor* 10))
                          (+ (round (h self) 2) (* *icon-size-factor* 10))
                          #\?))))
         (t 
          (om-with-fg-color self *om-pink-color*
           (om-with-font (om-make-font "Courier"
                                       (* *icon-size-factor*
                                         (if (>= cl-user::*version* 8) 14 18)))
            (om-draw-char (- (round (w self) 2) (* *icon-size-factor* 5))
                          (+ (round (h self) 2) (* *icon-size-factor* 5))
                          #\?))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; omNG-box-value - OMBoxPatch

(defmethod omNG-box-value ((self OMBoxPatch) &optional (num-out 0))
  (handler-bind ((error #'(lambda (c)
                            (when *msg-error-label-on*
                              (om-message-dialog
                               (string+ "Error while evaluating the box "
                                        (string (name self)) " : "
                                        (om-report-condition c))
                               :size (om-make-point 300 200))
                              (clear-after-error self)
                              (om-abort)))))
    (cond
      ((and (equal (allow-lock self) "x") (value self))
       (nth num-out (value self)))
      ((and (equal (allow-lock self) "o")
            (setf (value self) (list (reference self)))
            (car (value self))))
      ((equal (allow-lock self) "l")
       (unless (compiled? (reference self))
         (if (and (lisp-exp-p (reference self)) (editorframe self))
             (compile-without-close (editorframe self))
             (compile-patch (reference self))))
       (setf (value self)
             (list (special-lambda-value
                    self
                    (intern (string (code (reference self))) :om))))
       (car (value self)))
      ((and (equal (allow-lock self) "&") (ev-once-p self))
       (nth num-out (value self)))
      (t (if (and (lisp-exp-p (reference self)) (editorframe (reference self)))
             (compile-without-close (editorframe (reference self)))
             (compile-patch (reference self)))
         (let* ((args (mapcar #'(lambda (input)
                                  (omNG-box-value input))
                              (inputs self)))
                (rep nil))
           (if (non-deter-patch? (reference self))
               (setf rep
                     (multiple-value-list
                      (eval `(,(intern (string (code (reference self))) :om)
                               ,.(loop for item in args collect `',item)))))
               (setf rep
                     (multiple-value-list
                      (apply (intern (string (code (reference self))) :om)
                             args))))
           (when (equal (allow-lock self) "&")
             (setf (ev-once-p self) t)
             (setf (value self) rep))
           (when (equal (allow-lock self) "x")
             (setf (value self) rep))
           (when (equal (allow-lock self) nil)
             (setf (value self) rep))
           (nth num-out rep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; COMPILE-PATCH and GEN-PATCH-CODE 
;;;

(defmethod compile-patch ((self OMPatch))
 (unless (compiled? self)
  (if (lisp-exp-p self)
      (let* ((exp (get-lisp-exp (lisp-exp self)))
             (screamer? (handler-case
                         (not (s::function-record-deterministic?
                               (s::get-function-record
                                (eval `(screamer::defun ,(intern (string (code self)) :om)
                                     ,.(cdr exp))))))
                         (error () nil))))
        (or screamer?
           (progn (screamer::purge (intern (string (code self)) :om))
                  (compile (eval `(defun ,(intern (string (code self)) :om)
                                ,.(cdr (get-lisp-exp (lisp-exp-p self)))))))))
        (let* ((boxes (boxes self))
               (temp-out-box (find-class-boxes boxes 'OMtempOut))
               (self-boxes (patch-has-temp-in-p self))
               (out-box (find-class-boxes boxes 'OMout))
               (in-boxes (find-class-boxes boxes 'OMin))
               (out-symb (code self))
               (oldletlist *let-list*)
               (oldlambdacontext *lambda-context*)
               symbols body screamer?)
        (setf out-box (list+ temp-out-box (sort out-box '< :key 'indice)))
        (setf in-boxes (list+ self-boxes (sort in-boxes '< :key 'indice)))
        (setf symbols (mapcar #'(lambda (thein) (setf (in-symbol thein) (gensym))) in-boxes))
        (setf *let-list* nil)
        (setf body `(values ,.(mapcar #'(lambda (theout)
                                          (gen-code theout 0)) out-box)))
        (setf screamer? (handler-case
                         (not (s::function-record-deterministic?
                               (s::get-function-record
                         (eval `(screamer::defun ,(intern (string out-symb) :om)  (,.symbols)
                                 (let* ,(reverse *let-list*) ,body))))))
                        (error () nil)))
        (or screamer?
           (progn (screamer::purge (intern (string (code self)) :om))
                  (eval `(defun ,(intern (string out-symb) :om)  (,.symbols)
                          (let* ,(reverse *let-list*) ,body)))))
        (setf *let-list* oldletlist)
        (setf *lambda-context* oldlambdacontext)
        ))
    (setf (compiled? self) t)))

(defmethod gen-patch-code ((self OMPatch))
 (let ((clone (clone self)))
  (if (lisp-exp-p clone)
      (let* ((exp (get-lisp-exp (lisp-exp clone)))
             (screamer? (handler-case
                         (not (s::function-record-deterministic?
                               (s::get-function-record
                                (eval `(screamer::defun ,(intern (string (code clone)) :om)
                                     ,.(cdr exp))))))
                         (error () nil))))
               
        (if screamer?
           `(screamer::defun ,(intern (string (code clone)) :om)
                                     ,.(cdr exp))
           (progn (screamer::purge (intern (string (code clone)) :om))
                 `(defun ,(intern (string (code clone)) :om)
                ,.(cdr (get-lisp-exp (lisp-exp-p clone)))))))
        (let* ((boxes (boxes clone))
               (temp-out-box (find-class-boxes boxes 'OMtempOut))
               (self-boxes (patch-has-temp-in-p clone))
               (out-box (find-class-boxes boxes 'OMout))
               (in-boxes (find-class-boxes boxes 'OMin))
               (out-symb (code clone))
               (oldletlist *let-list*)
               (oldlambdacontext *lambda-context*)
               symbols body screamer? code)
        (setf out-box (list+ temp-out-box (sort out-box '< :key 'indice)))
        (setf in-boxes (list+ self-boxes (sort in-boxes '< :key 'indice)))
        (setf symbols (mapcar #'(lambda (thein) (setf (in-symbol thein) (gensym))) in-boxes))
        (setf *let-list* nil)
        (setf body `(values ,.(mapcar #'(lambda (theout)
                                          (gen-code theout 0)) out-box)))
        (setf screamer? (handler-case
                         (not (s::function-record-deterministic?
                               (s::get-function-record
                         (eval `(screamer::defun ,(intern (string out-symb) :om)  (,.symbols)
                                 (let* ,(reverse *let-list*) ,body))))))
                        (error () nil)))
        (setf code 
         (if screamer?
            `(screamer::defun ,(intern (string out-symb) :om)  (,.symbols)
                                 (let* ,(reverse *let-list*) ,body))
             (progn (screamer::purge (intern (string (code clone)) :om))
                   `(defun ,(intern (string out-symb) :om)  (,.symbols)
                     (let* ,(reverse *let-list*) ,body)))))
        (setf *let-list* oldletlist)
        (setf *lambda-context* oldlambdacontext)
        code))))
#|
(defmethod gen-code-for-ev-once ((self OMBoxPatch) numout)
   (let ((varname (read-from-string (gen-box-string self)))
         (patchfun `,(intern (string (code (reference self))) :om)))
      (when (not (member varname *screamer-let-list* :test 'equal :key 'car))
        (push `(,varname (multiple-value-list (,patchfun ,.(decode self))))  *screamer-let-list*))
      `(nth ,numout ,varname)))
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;OMLispPatch
;;;

(defun compile-lisp-patch-fun (patch)
  (if (get-lisp-exp (lisp-exp patch))
      (cond ((non-deter-patch? patch)
             (eval `(screamer::defun
                     ,(intern (string (code patch)) :om)
                      ,.(cdr (get-lisp-exp (lisp-exp patch))))))
            (t
             (screamer::purge (intern (string (code patch)) :om))
             (eval `(defun
                     ,(intern (string (code patch)) :om)
                      ,.(cdr (get-lisp-exp (lisp-exp patch)))))))
      (eval `(defun ,(intern (string (code patch)) :om) () nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Evaluation -- lambda mode
;;;
;;; OM core defines SPECIAL-LAMBDA-VALUE on OMBoxcall (OMBoxPatch's
;;; parent) emitting (LAMBDA ... (APPLY ',SYMBOL (LIST ,.ARGS))).
;;; OM-Backtrack's only divergence is for non-deter patches, where
;;; the body must be a direct (,SYMBOL ,.ARGS) so the calling
;;; continuation flows through CPS.  Implemented as :AROUND so case
;;; (1) delegates to OM core via CALL-NEXT-METHOD.

(defmethod special-lambda-value :around ((self OMBoxPatch) symbol)
  (if (non-deter-patch? (reference self))
      (multiple-value-bind (nesymbs args) (get-args-eval-currry self)
        (eval `#'(lambda ,(reverse nesymbs)
                   (,symbol ,.args))))
      (call-next-method)))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;code generation -- lambda-mode source emission
;;;
;;; Same delegation pattern as SPECIAL-LAMBDA-VALUE: OMBoxcall's
;;; primary already emits the deterministic apply-form; we only
;;; intervene on the non-deter branch.

(defmethod curry-lambda-code :around ((self OMBoxPatch) symbol)
  (if (non-deter-patch? (reference self))
      (let ((nesymbs nil)
            (oldlambdacontext *lambda-context*))
        (setf *lambda-context* t)
        (unwind-protect
            (let ((args (mapcan #'(lambda (input)
                                    (let ((a (if (connected? input)
                                                 (gen-code input 0)
                                                 (let ((newsymbol (gensym)))
                                                   (push newsymbol nesymbs)
                                                   newsymbol))))
                                      (if (keyword-input-p input)
                                          (list (value input) a)
                                          (list a))))
                                (inputs self))))
              `#'(lambda ,(reverse nesymbs)
                   (,symbol ,.args)))
          (setf *lambda-context* oldlambdacontext)))
      (call-next-method)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;TODO (IF NEEDED)
;;;
;;; => OMLOOP (???)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
