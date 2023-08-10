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

(defstruct line
  filename number string)

(defstruct instruction
  line name operands opcodes flags function)

(define-condition bad-line (error)
  ((line :initarg :line
         :initform nil
         :reader line))
  (:documentation "Encountered a malformed line in a file")
  (:report (lambda (condition stream)
             (let* ((line (line condition))
                    (filename (line-filename line))
                    (number (line-number line))
                    (string (line-string line)))
               (format-symbol stream "~A:~A malformed line: \"~A\"~&" filename 
                                                                      number
                                                                      string)))))

(defun read-lines (filename &optional (filter (constantly t)))
  (loop for line in (uiop:read-file-lines filename)
        for number from 1
        when (funcall filter line)
          collect (make-line :filename filename
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
  (let ((operands (instruction-operands instruction))
        (flags (instruction-flags instruction)))
    (setf (instruction-operands instruction) (cl-ppcre:split "," operands)
          (instruction-flags instruction) (cl-ppcre:split "," flags))
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
                (make-instruction :line line
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

(defun instruction-relaxed-p (ins n)
  "Is nth operand relaxed?"
  (find #\* (nth n (instruction-operands ins))))

(defvar *instruction-tuple-codes*
  '((""    . 000)
    ("fv"  . 001)
    ("hv" . 002)
    ("fvm" . 003)
    ("t1s8" . 004)
    ("t1s16" . 005)
    ("t1s" . 006)
    ("t1f32" . 007)
    ("t1f64" . 010)
    ("t2" . 011)
    ("t4" . 012)
    ("t8" . 013)
    ("hvm" . 014)
    ("qvm" . 015)
    ("ovm" . 016)
    ("m128" . 017)
    ("dup" . 020)))

(defun instruction-compile (ins)
  (let* ((opcodes (instruction-opcodes ins))
         (codestring (multiple-value-bind (match strings)
                         (cl-ppcre:scan-to-strings "^\\s*\\[([^\\]]*)\\]\\s*$" opcodes)
                       (when match (aref strings 0))))
         (parts (multiple-value-bind (match strings)
                    (cl-ppcre:scan-to-strings "^(([^\\s:]*)\\:*([^\\s:]*)\\:|)\\s*(.*\\S)\\s*$" codestring)
                  (when match strings))))
    (when parts
      (let* ((opr (aref parts 1))
             (tuple (aref parts 2))
             (opc (aref parts 3))
             oppos
             (op (loop with op = 0
                       for c across (or opr #())
                       for i from 0
                       do (cond ((char= #\+ c) (decf op))
                                (t
                                 (progn
                                   (when (instruction-relaxed-p ins i)
                                     (decf op))
                                   (push (cons c op) oppos)
                                   (incf op))))
                          
                       finally (return op)))
             (tup (cdr (assoc tuple *instruction-tuple-codes* :test #'string=))))
        (list `(opr . ,opr)
              `(tuple . ,tuple)
              `(opc . ,opc)
              `(op . ,op)
              `(oppos . ,oppos)
              `(tup . ,tup))))))

(defun insns-db-populate (&optional (db *instruction-db*))
  (mapcar (lambda (ins) (insns-db-push-1 ins db)) (insns-process))
  db)

(defun insns-db-compile (&optional (db *instruction-db*))
  (maphash (lambda (k v)
             (declare (ignore k))
             (mapcar (lambda (ins)
                       (setf (instruction-function ins) (instruction-compile ins)))
                     v))
           db))

(defun insns-db-print (&optional (db *instruction-db*))
  (maphash (lambda (k v)
             (format t "(~S ~S)~%" k v))
           db))

(defun insns-developer-crank (&optional (db *instruction-db*))
  (clrhash db)
  (insns-db-populate db)
  (insns-db-compile db)
  (insns-db-print db))
