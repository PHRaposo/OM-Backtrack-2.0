;; Copyright (c) 2025 Paulo Henrique Raposo

;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in all
;; copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

(in-package :om)

;;;; =========================================================================
;;;; NONDETERMINISTIC-PATCH CLASSES
;;;; =========================================================================

(defclass NonDeterministicPatch (OMPatch) ()
  (:metaclass omstandardclass))

(defclass NonDeterministicPatchAbs (NonDeterministicPatch OMPatchAbs) ()
  (:metaclass omstandardclass))

(defclass NonDeterministicLispPatch (OMLispPatch) ()
  (:metaclass omstandardclass))

(defclass NonDeterministicLispPatchAbs (NonDeterministicLispPatch OMLispPatchAbs) ()
  (:metaclass omstandardclass))

(defmethod get-object-insp-name ((self NonDeterministicPatch)) "nondeterministic patch")
(defmethod get-object-insp-name ((self NonDeterministicLispPatch)) "nondeterministic lisp")

(defmethod non-deter-patch? ((self NonDeterministicPatch)) nil)

(defmethod non-deter-patch? ((self NonDeterministicLispPatch)) nil)

;;;; =========================================================================
;;;; COMPILE-PATCH -- body wrapped with PUSH-ASSERT!-INTO
;;;; =========================================================================

(defmethod compile-patch ((self NonDeterministicPatch))
  (unless (compiled? self)
    (handler-bind
        ((error #'(lambda (c)
                    (when *msg-error-label-on*
                      (om-message-dialog
                       (string+ "Error while compiling nondeterministic patch '"
                                (string (name self)) "' : "
                                (om-report-condition c))
                       :size (om-make-point 300 200))
                      (om-abort)))))
      (if (lisp-exp-p self)
          (compile-nondeterministic-lisp-patch-fun self)
          (let* ((boxes (boxes self))
                 (temp-out-box (find-class-boxes boxes 'OMtempOut))
                 (self-boxes (patch-has-temp-in-p self))
                 (out-box (find-class-boxes boxes 'OMout))
                 (in-boxes (find-class-boxes boxes 'OMin))
                 (out-symb (code self))
                 (oldletlist *let-list*)
                 (oldlambdacontext *lambda-context*)
                  symbols body)
           (setf out-box (list+ temp-out-box (sort out-box '< :key 'indice)))
           (setf in-boxes (list+ self-boxes (sort in-boxes '< :key 'indice)))
           (setf symbols (mapcar #'(lambda (thein) (setf (in-symbol thein) (gensym))) in-boxes))
           (setf *let-list* nil)
           (setf body `(values ,.(mapcar #'(lambda (theout)
                                          (gen-code theout 0)) out-box)))
           (eval `(screamer::defun ,(intern (string out-symb) :om)  (,.symbols)
                   (let* ,(reverse *let-list*) ,body)))
           (setf *let-list* oldletlist)
           (setf *lambda-context* oldlambdacontext)
           ))
    (setf (compiled? self) t))))

(defmethod compile-patch ((self NonDeterministicLispPatch))
  (unless (compiled? self)
    (handler-bind
        ((error #'(lambda (c)
                    (when *msg-error-label-on*
                      (om-message-dialog
                       (string+ "Error while compiling nondeterministic lisp patch '"
                                (string (name self)) "' : "
                                (om-report-condition c))
                       :size (om-make-point 300 200))
                      (om-abort)))))
      (compile-nondeterministic-lisp-patch-fun self)
      (setf (compiled? self) t))))

(defun compile-nondeterministic-lisp-patch-fun (patch)
 (let ((exp (get-lisp-exp (lisp-exp patch))))
  (eval `(screamer::defun ,(intern (string (code patch)) :om)
          ,.(cdr exp)))))

;;;; =========================================================================
;;;; BOX CLASS + SPECIAL-LAMBDA-VALUE --
;;;; =========================================================================

(defclass OMBoxNonDeterministicPatch (OMBoxAbsPatch) ()
  (:metaclass omstandardclass))

(defmethod box-class ((self NonDeterministicPatchAbs))     'OMBoxNonDeterministicPatch)
(defmethod box-class ((self NonDeterministicLispPatchAbs)) 'OMBoxNonDeterministicPatch)

(defmethod special-lambda-value ((self OMBoxNonDeterministicPatch) symbol)
  (multiple-value-bind (nesymbs args) (get-args-eval-currry self)
    (eval `(screamer::lambda-nondeterministic ,(reverse nesymbs)
               (,symbol (list ,.args))))))

(defmethod curry-lambda-code ((self OMBoxNonDeterministicPatch) symbol)
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
          `(screamer::lambda-nondeterministic ,(reverse nesymbs)
               (,symbol ,.args)))
      (setf *lambda-context* oldlambdacontext))))
      
;;;; =========================================================================
;;;; OM-SAVE / LOADERS -- preserve subclass across .omp / .oml roundtrip
;;;; =========================================================================

(defmethod om-save ((self NonDeterministicPatch) &optional (values? nil))
  (if (lisp-exp-p self)
      `(setf *om-current-persistent*
             (om-load-ndlisp-patch ,(name self) ,*om-version*
                                  ,(str-without-nl (lisp-exp-p self))))
      (let ((boxes        (mapcar #'(lambda (b) (omNG-save b values?)) (boxes self)))
            (connectiones (mk-connection-list (boxes self)))
            (pictlist     (omng-save (pictu-list self))))
        `(setf *om-current-persistent*
               (om-load-ndpatch1 ,(name self) ',boxes ',connectiones ,pictlist ,*om-version*)))))

(defmethod om-save ((self NonDeterministicPatchAbs) &optional (values? nil))
  (if (lisp-exp-p self)
      `(om-load-ndlisp-abspatch ,(name self) ,*om-version* ,(str-without-nl (lisp-exp-p self)))
      (let ((boxes        (mapcar #'(lambda (b) (omNG-save b values?)) (boxes self)))
            (connectiones (mk-connection-list (boxes self)))
            (doc          (str-without-nl (doc self)))
            (pictlist     (omng-save (pictu-list self))))
        (when (editorframe self)
          (set-win-size self (om-interior-size (window (editorframe self))))
          (set-win-position self (om-view-position (window (editorframe self)))))
        `(om-load-ndpatch-abs1 ,(name self) ',boxes ',connectiones ,*om-version* ,pictlist ,doc
                              ,(om-save-point (w-pos self)) ,(om-save-point (w-size self))))))

(defmethod om-save ((self NonDeterministicLispPatch) &optional (values? nil))
  (declare (ignore values?))
  `(setf *om-current-persistent*
         (om-load-ndlisp-patch ,(name self) ,*om-version*
                              ,(str-without-nl (lisp-exp self)))))

(defmethod om-save ((self NonDeterministicLispPatchAbs) &optional (values? nil))
  (declare (ignore values?))
  `(om-load-ndlisp-abspatch ,(name self) ,*om-version* ,(str-without-nl (lisp-exp self))))

(defun om-load-ndpatch1 (name boxes connections &optional (fond-ec nil) (version nil) (pictueditors nil))
  (declare (ignore pictueditors))
  (let ((newpatch (omNG-make-new-ndpatch name)))
    (setf (boxes newpatch) nil)
    (mapc #'(lambda (b) (omNG-add-element newpatch (eval b))) boxes)
    (setf (boxes newpatch) (reverse (boxes newpatch)))
    (setf (connec newpatch) (loop for i in connections collect (load-connection i)))
    (setf (pictu-list newpatch) fond-ec)
    (when version (setf (omversion newpatch) version))
    newpatch))

(defun om-load-ndpatch-abs1 (name boxes connections
                            &optional (version nil) (pictlist nil) (doc "") wpos wsize
                            &rest args)
  (declare (ignore args))
  (let ((newpatch (make-instance 'NonDeterministicPatchAbs :name name :icon 486210)))
    (setf (boxes newpatch) nil)
    (mapc #'(lambda (b) (omNG-add-element newpatch (eval b))) boxes)
    (setf (boxes newpatch) (reverse (boxes newpatch)))
    (setf (saved? newpatch) connections)
    (remk-connections (boxes newpatch) (loop for i in connections collect (load-connection i)))
    (setf (pictu-list newpatch) pictlist)
    (setf (doc newpatch) (str-with-nl doc))
    (when wpos  (setf (w-pos newpatch) wpos))
    (when wsize (setf (w-size newpatch) wsize))
    (compile-patch newpatch)
    (when version (setf (omversion newpatch) version))
    newpatch))

(defun om-load-ndlisp-patch (name version expression)
  (let ((newpatch (omNG-make-new-ndlisp-patch name)))
    (setf (omversion newpatch) version)
    (setf (lisp-exp newpatch) (get-lisp-str expression))
    newpatch))

(defun om-load-ndlisp-abspatch (name version expression)
  (let ((newpatch (make-instance 'NonDeterministicLispPatchAbs :name name :icon 486123)))
    (setf (omversion newpatch) version)
    (setf (lisp-exp newpatch) (get-lisp-str expression))
    (compile-nondeterministic-lisp-patch-fun newpatch)
    newpatch))

;;;; =========================================================================
;;;; CONSTRUCTORS
;;;; =========================================================================

(defun omNG-make-new-ndpatch (name &optional (posi (om-make-point 0 0)))
  (let ((newpatch (make-instance 'NonDeterministicPatch :name name :icon 486183)))
    (set-icon-pos newpatch posi)
    newpatch))

(defun omNG-make-new-ndlisp-patch (name &optional (posi (om-make-point 0 0)))
  (let ((newpatch (make-instance 'NonDeterministicLispPatch :name name :icon 486124)))
    (set-icon-pos newpatch posi)
    newpatch))

;;;; =========================================================================
;;;; PATCH2ABS / ABS2PATCH -- preserve subclass across conversion
;;;; TODO
;;;; =========================================================================

(defmethod patch2abs ((self NonDeterministicPatch))
 (om-message-dialog "Currently you cannot convert an NonDeterministicPatch into a NonDeterministicPatchAbs.")
 (om-abort))
 
(defmethod abs2patch ((self NonDeterministicPatchAbs) name pos)
 (om-message-dialog "Currently you cannot convert an NonDeterministicPatchAbs into a NonDeterministicPatch.")
 (om-abort))
 
(defmethod patch2abs ((self NonDeterministicLispPatch))
 (om-message-dialog "Currently you cannot convert an NonDeterministicLispPatch into a NonDeterministicLispPatchAbs.")
 (om-abort))
 
(defmethod abs2patch ((self NonDeterministicLispPatchAbs) name pos)
 (om-message-dialog "Currently you cannot convert an NonDeterministicLispPatchAbs into a NonDeterministicLispPatch.")
 (om-abort))
 
#|(defmethod patch2abs ((self NonDeterministicPatch))
  (let ((newabs (make-instance 'NonDeterministicPatchAbs :name (name self) :icon 486210)))
    (if (lisp-exp-p self)
        (setf (lisp-exp-p newabs) (lisp-exp-p self))
        (let ((boxes (boxes self)))
          (loop for item in (reverse (mapcar #'omNG-copy boxes)) do
                (omng-add-element newabs (eval item)))
          (copy-connections boxes (boxes newabs))
          (setf (pictu-list newabs) (mapcar 'copy-picture (pictu-list self)))))
    (set-icon-pos newabs (get-icon-pos self))
    (set-win-size newabs (get-win-size self))
    (setf (doc newabs) (doc self))
    newabs))

(defmethod abs2patch ((self NonDeterministicPatchAbs) name pos)
  (let ((newabs (omNG-make-new-ndpatch name pos)))
    (if (lisp-exp-p self)
        (setf (lisp-exp-p newabs) (lisp-exp-p self))
        (let ((boxes (boxes self)))
          (loop for item in (reverse (mapcar #'omNG-copy boxes)) do
                (omng-add-element newabs (eval item)))
          (copy-connections boxes (boxes newabs))
          (setf (pictu-list newabs) (mapcar 'copy-picture (pictu-list self)))))
    (set-icon-pos newabs (get-icon-pos self))
    (set-win-size newabs (get-win-size self))
    (setf (doc newabs) (doc self))
    newabs))

(defmethod patch2abs ((self NonDeterministicLispPatch))
  (let ((newabs (make-instance 'NonDeterministicLispPatchAbs :name (name self) :icon 486123)))
    (setf (lisp-exp newabs) (lisp-exp self))
    (set-icon-pos newabs (get-icon-pos self))
    (setf (doc newabs) (doc self))
    newabs))

(defmethod abs2patch ((self NonDeterministicLispPatchAbs) name pos)
  (let ((newabs (omNG-make-new-ndlisp-patch name pos)))
    (setf (lisp-exp newabs) (lisp-exp self))
    (set-icon-pos newabs (get-icon-pos self))
    (setf (doc newabs) (doc self))
    newabs))|#

;;;; =========================================================================
;;;; ADVICE ON COMPILE-LISP-PATCH-FUN -- dispatch to nondeterministic compiler
;;;; =========================================================================
;;; OM calls COMPILE-LISP-PATCH-FUN directly from COMPILE-WITHOUT-CLOSE
;;; (editor), LOAD-ABSTRACTION-ATTRIBUTES, GET-PATCH-INPUTS, OMNG-COPY --
;;; bypassing COMPILE-PATCH entirely. This advice intercepts those paths for
;;; NonDeterministicLispPatch instances so the screamer::defun is used.

(lw:defadvice (compile-lisp-patch-fun intercept-nondeterministic-lisp-patch :around)
              (patch)
  (cond
    ((typep patch 'NonDeterministicLispPatch)
     ;(format *om-stream* "~%[compile-lisp-patch-fun advice -> NonDeterministicLispPatch '~A']~%"
     ;        (or (name patch) "unnamed"))
     (compile-nondeterministic-lisp-patch-fun patch))
    (t (lw:call-next-advice patch))))

;;;; =========================================================================
;;;; ADVICE -- register "ndpatch" / "ndlisp" as creation keywords
;;;; =========================================================================

(lw:defadvice (update-pack-symbols add-ndpatch-ndlisp-symbols :after) ()
  (setf *all-om-pack-symbols*
        (sort (append *all-om-pack-symbols* (list "ndpatch" "ndlisp"))
              'string<)))

(update-pack-symbols)

;;;; =========================================================================
;;;; ADVICE -- redirect kernel icon lookup to library's icon folder
;;;; =========================================================================
;;; Instead of copying PNGs into the OM install folder (requires admin
;;; on Win/Mac/Linux), we intercept om-load-icon for these specific IDs and
;;; redirect to OM-Backtrack's own resources/icon folder.

(lw:defadvice (om-load-icon intercept-nondeterministic-patch-icons :around)
              (id &optional folder)
  (if (and (not folder)
           (integerp id)
           (member id '(170 486183 486210 486123 486124) :test #'=)
           *om-backtrack-icon-folder*)
      (or (lw:call-next-advice id *om-backtrack-icon-folder*)
          (lw:call-next-advice id folder))
      (lw:call-next-advice id folder)))

(lw:defadvice (add-box-in-patch-panel intercept-ndpatch-ndlisp :around)
              (str scroller pos)
  (let* ((*package* (find-package :om))
         (funname   (ignore-errors (read-from-string str))))
    (cond
      ((equal funname 'ndpatch)
       (let ((newbox (omNG-make-new-boxcall
                      (make-instance 'NonDeterministicPatchAbs
                                     :name (mk-unique-name scroller "myndpatch")
                                     :icon 486210)
                      pos
                      (mk-unique-name scroller "myndpatch"))))
         (when (and newbox (box-allowed-p newbox scroller))
           (omG-add-element scroller (make-frame-from-callobj newbox)))
         newbox))
      ((equal funname 'ndlisp)
       (let ((newbox (omNG-make-new-boxcall
                      (make-instance 'NonDeterministicLispPatchAbs
                                     :name (mk-unique-name scroller "myndlisp")
                                     :icon 486123)
                      pos
                      (mk-unique-name scroller "myndlisp"))))
         (when (and newbox (box-allowed-p newbox scroller))
           (omG-add-element scroller (make-frame-from-callobj newbox)))
         newbox))
      (t (lw:call-next-advice str scroller pos)))))
