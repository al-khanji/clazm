(eval-when (:compile-toplevel)
  (ql:quickload :alexandria)
  (ql:quickload :cl-ppcre))

(cl:defpackage :clazm
  (:use :cl :alexandria))

(cl:in-package :clazm)

(defvar *nasm/x86* "~/github/netwide-assembler/nasm/x86")
(defvar *nasm/x86/regs.dat* (format nil "~A/~A" *nasm/x86* "regs.dat"))
(defvar *nasm/x86/insns.dat* (format nil "~A/~A" *nasm/x86* "insns.dat"))

(defvar *regs.dat-line-scanner*
  (cl-ppcre:create-scanner "\\s*(\\S+)\\s*(\\S+)\\s*(\\S+)\\s*([0-9]+)\\s*(\\S*)"
                           :case-insensitive-mode t))
(defvar *insns.dat-line-scanner*
  (cl-ppcre:create-scanner "^\\s*(\\S+)\\s+(\\S+)\\s+(\\S+|\\[.*\\])\\s+(\\S+)\\s*$"))

(defvar *condd* (list   "o"  0 "no"  1 "c"    2 "nc"  3
                        "z"  4 "nz"  5 "na"   6 "a"   7
                        "s"  8 "ns"  9 "pe"  10 "po" 11
                        "l" 12 "nl" 13 "ng"  14 "g"  15))
(defvar *conds* (list* "ae"  3 "b"   2 "be"   6 "e" 4
                       "ge" 13 "le" 14 "nae"  2 "nb" 3
                       "nbe" 7 "ne"  5 "nge" 12 "nle" 15
                       "np" 11 "p"  10
                       *condd*))

(defclass line ()
  ((filename :initarg :filename :reader line-filename)
   (number :initarg :number :reader line-number)
   (string :initarg :string :reader line-string)))

(define-condition bad-line (error)
  ((line :initarg :line
         :initform nil
         :reader line))
  (:documentation "Encountered a malformed line in a file")
  (:report (lambda (condition stream)
             (with-slots (filename number string) (line condition)
               (format stream "~a:~a malformed line: \"~a\"~&" filename 
                                                               number
                                                               string)))))

(defmethod print-object ((line line) stream)
  (print-unreadable-object (line stream :type 'line)
    (with-slots (filename number string) line
      (format stream "~A \"~A\"" number string))))

(defclass instruction ()
  ((line :initarg :line :accessor instruction-line)
   (name :initarg :name :accessor instruction-name)
   (operands :initarg :operands :accessor instruction-operands)
   (opcodes :initarg :opcodes :accessor instruction-opcodes)
   (flags :initarg :flags :accessor instruction-flags)))

(defmethod print-object ((ins instruction) stream)
  (print-unreadable-object (ins stream :type 'instruction)
    (with-slots (name operands opcodes flags) ins
      (format stream "~A ~A ~A ~A" name operands opcodes flags))))

(defclass instruction-function ()
  ((instruction :initarg :instruction :accessor instruction-function-instruction)
   (lambda :initarg :lambda :accessor instruction-function-lambda)))

(defmethod print-object ((ins-f instruction-function) stream)
  (print-unreadable-object (ins-f stream :type 'instruction-function)
    (with-slots (instruction lambda) ins
      (with-slots (name operands flags)
       (format stream "~A ~A ~A")))))

(defun read-lines (filename &optional (filter (constantly t)))
  (loop for line in (uiop:read-file-lines filename)
        for number from 1
        when (funcall filter line)
          collect (make-instance 'line :filename filename
                                       :number number
                                       :string line)))

(defun make-comment-char-filter (char &optional (whitespace " "))
  (lambda (line)
    (when-let* ((predicate (lambda (c) (find c whitespace)))
                (relevant-char (find-if-not predicate line)))
      (not (equal char relevant-char)))))

(defun regs-read-lines (&optional (filename *nasm/x86/regs.dat*))
  (read-lines filename (make-comment-char-filter #\#)))

(defun insns-read-lines (&optional (filename *nasm/x86/insns.dat*))
  (read-lines filename (make-comment-char-filter #\;)))

(defun instruction-parse-fields (instruction)
  (with-slots (name operands opcodes flags) instruction
    (setf operands (cl-ppcre:split "," operands)
          flags (cl-ppcre:split "," flags))
    instruction))

(defun instruction-name-expand-cc (name)
  (when-let* ((cc-pos (search "cc" name))
              (prefix (subseq name 0 cc-pos))
              (suffix (subseq name (+ 2 cc-pos))))
    (loop for (c-name c-value) on *conds* by #'cddr
          collect (cons (format nil "~A~:@(~A~)~A" prefix c-name suffix)
                        c-value))))

(defun instruction-opcodes-patch-cc (opcodes value)
  (if (not value)
      opcodes
      (let* ((+c-pos (search "+c" opcodes))
             (prefix-end-pos (- +c-pos 2))
             (suffix-start-pos (+ +c-pos 2))
             (prefix (subseq opcodes 0 prefix-end-pos))
             (suffix (subseq opcodes suffix-start-pos))
             (base-value (parse-integer opcodes
                                        :start prefix-end-pos
                                        :end +c-pos
                                        :radix 16)))
        (format nil "~A~(~X~)~A" prefix (+ base-value value) suffix))))

(defun insns-parse-line (line &optional (scanner *insns.dat-line-scanner*))
  (multiple-value-bind (match strings)
      (cl-ppcre:scan-to-strings scanner (line-string line))
    (when (not match)
      (error 'bad-line :line line))
    (let* ((base-name (aref strings 0))
           (operands (aref strings 1))
           (opcodes (aref strings 2))
           (flags (aref strings 3))
           (cc-names (instruction-name-expand-cc base-name)))
      (flet ((make-instruction (name &optional cc-value)
               (instruction-parse-fields
                (make-instance 'instruction
                               :name name
                               :operands operands
                               :opcodes (instruction-opcodes-patch-cc opcodes cc-value)
                               :flags flags))))
        (cond (cc-names (loop for (cc-name . cc-value) in cc-names
                              collect (make-instruction cc-name cc-value)))
              (t (make-instruction base-name)))))))

(defparameter *instruction-db* (make-hash-table :test 'equalp))

(defun insns-process ()
  (loop for line in (insns-read-lines)
        for instruction = (insns-parse-line line)
        if (listp instruction)
          append instruction
        else
          collect instruction))

(defun insns-db-push-1 (ins &optional (db *instruction-db*))
  (with-slots (name operands opcodes flags) ins
    (push ins (gethash name db))))

(defun insns-db-populate (&optional (db *instruction-db*))
  (mapcar (lambda (ins) (insns-db-push-1 ins db)) (insns-process))
  db)

(defun insns-db-print (&optional (db *instruction-db*))
  (maphash (lambda (k v)
             (format t "~A ~A~%"
                     k
                     (loop for ins in v
                           collect (with-slots (operands opcodes flags) ins
                                     (list operands opcodes flags)))))
           db))
