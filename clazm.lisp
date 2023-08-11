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
(defvar *regs.dat-name-scanner*
  (cl-ppcre:create-scanner "^(.*[^0-9])([0-9]+)\\-([0-9]+)(|[^0-9].*)$"))

(defvar *insns.dat-line-scanner*
  (cl-ppcre:create-scanner "^\\s*(\\S+)\\s+(\\S+)\\s+(\\S+|\\[.*\\])\\s+(\\S+)\\s*$"))

(defvar *condd* (list   "o"  0 "no"  1 "c"    2 "nc"   3
                        "z"  4 "nz"  5 "na"   6 "a"    7
                        "s"  8 "ns"  9 "pe"  10 "po"  11
                        "l" 12 "nl" 13 "ng"  14 "g"   15))
(defvar *conds* (list* "ae"  3 "b"   2 "be"   6 "e"    4
                       "ge" 13 "le" 14 "nae"  2 "nb"   3
                       "nbe" 7 "ne"  5 "nge" 12 "nle" 15
                       "np" 11 "p"  10
                       *condd*))

(defstruct line
  filename number string)

(defstruct instruction
  line name operands opcodes flags function)

(defstruct register
  line name assembler-class disassembler-classes number token-flag)

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

(defun regs-parse-line (line &optional (line-scanner *regs.dat-line-scanner*)
                                       (name-scanner *regs.dat-name-scanner*))
  (multiple-value-bind (match strings)
      (cl-ppcre:scan-to-strings line-scanner (line-string line))
    (when (not match)
      (error 'bad-line :line line))
    (let ((register-name (aref strings 0))
          (assembler-class (aref strings 1))
          (disassembler-classes (cl-ppcre:split "," (aref strings 2)))
          (x86-register-number (parse-integer (aref strings 3)))
          (token-flag (aref strings 4)))
      (flet ((make-register (name &optional (num 0))
               (make-register :line line
                              :name name
                              :assembler-class assembler-class
                              :disassembler-classes disassembler-classes
                              :number (+ x86-register-number num)
                              :token-flag token-flag)))
       (multiple-value-bind (match strings)
           (cl-ppcre:scan-to-strings name-scanner register-name)
         (cond (match (loop with bottom = (parse-integer (aref strings 1))
                            with top = (parse-integer (aref strings 2))
                            with prefix = (aref strings 0)
                            with suffix = (aref strings 3)
                            for i from bottom upto top
                            for j from 0
                            collect (make-register (format nil "~A~A~A" prefix i suffix) j)))
               (t (make-register register-name))))))))

(defun regs-process ()
  (loop for line in (regs-read-lines)
        for register = (regs-parse-line line)
        if (listp register)
          append register
        else
          collect register))

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

(defvar *plain-codes*
  '("o16"                ; indicates fixed 16-bit operand size, i.e. optional 0x66
    "o32"                ; indicates fixed 32-bit operand size, i.e. optional 0x66
    "odf"                ; indicates that this instruction is only valid when the
                         ; operand size is the default (instruction to disassembler,
                         ; generates no code in the assembler)
    "o64"                ; 64-bit operand size requiring REX.W
    "o64nw"              ; Implied 64-bit operand size (no REX.W); REX on extensions only
    "a16"                ; 16-bit address size, i.e. optional 0x67 
    "a32"                ; 32-bit address size, i.e. optional 0x67
    "adf"                ; (disassembler only) Address size is default
    "a64"                ; fixed 64-bit address size, 0x67 invalid
    "!osp"               ; operand-size prefix (0x66) not permitted
    "!asp"               ; address-size prefix (0x67) not permitted
    "f2i"                ; F2 prefix used as opcode extension, but 66 for operand size is OK
    "f3i"                ; F3 prefix used as opcode extension, but 66 for operand size is OK
    "mustrep"            ; force a REP(E) prefix (0xF3) even if not specified
    "mustrepne"          ; force a REPNE prefix (0xF2) even if not specified
    "rex.l"              ; LOCK prefix used as REX.R (used in non-64-bit mode)
    "norexb"             ; (disassembler only) invalid with REX.B
    "norexx"             ; (disassembler only) invalid with REX.X
    "norexr"             ; (disassembler only) invalid with REX.R
    "norexw"             ; (disassembler only) invalid with REX.W
    "repe"               ; disassemble a rep (0xF3 byte) prefix as repe not rep
    "nohi"               ; Use spl/bpl/sil/dil even without REX
    "nof3"               ; No REP 0xF3 prefix permitted
    "norep"              ; No REP prefix permitted
    "wait"               ; Needs a wait prefix
    "resb"               ; reserve <operand 0> bytes of uninitialized storage
    "np"                 ; No prefix
    "jcc8"               ; Match only if Jcc possible with single byte
    "jmp8"               ; Match only if JMP possible with single byte
    "jlen"               ; Length of jump; assemble 0x03 if bits==16, 0x05 if bits==32; used for conditional jump over longer jump
    "hlexr"              ; instruction takes XRELEASE (F3) with or without lock
    "hlenl"              ; instruction takes XACQUIRE/XRELEASE with or without lock
    "hle"                ; instruction takes XACQUIRE/XRELEASE with lock only
    "vsibx"              ; This instruction takes an XMM VSIB memory EA
    "vm32x"              ; This instruction takes an XMM VSIB memory EA
    "vm64x"              ; This instruction takes an XMM VSIB memory EA
    "vsiby"              ; This instruction takes an YMM VSIB memory EA
    "vm32y"              ; This instruction takes an YMM VSIB memory EA
    "vm64y"              ; This instruction takes an YMM VSIB memory EA
    "vsibz"              ; This instruction takes an ZMM VSIB memory EA
    "vm32z"              ; This instruction takes an ZMM VSIB memory EA
    "vm64z"              ; This instruction takes an ZMM VSIB memory EA
    ))

(defvar *imm-codes*
  '("ib"        ; imm8
    "ib,u"      ; Unsigned imm8
    "iw"        ; imm16
    "ib,s"      ; imm8 sign-extended to opsize or bits
    "iwd"       ; imm16 or imm32, depending on opsize
    "id"        ; imm32
    "id,s"      ; imm32 sign-extended to 64 bits
    "iwdq"      ; imm16/32/64, depending on addrsize
    "rel8"      ; a byte relative operand, from operand 0..3
    "iq"        ; a qword immediate operand, from operand 0..3
    "rel16"     ; a word relative operand, from operand 0..3
    "rel"       ; 16 or 32 bit relative operand; select between \6[0-3] and \7[0-3] depending on 16/32 bit
                ; assembly mode or the operand-size override on the operand
    "rel32"     ; a long relative operand, from operand 0..3
    "seg"       ;  a word constant, from the _segment_ part of operand 0..3
    ))

(defun instruction-opcode-compile (opcode)
  (cond
    ((find opcode *plain-codes* :test #'string=) opcode)
    ((find opcode *imm-codes* :test #'string=) opcode)
    ((string= "/r" opcode) `(make-modrm ,opcode))
    ((cl-ppcre:scan "/\\d" opcode) `(make-modrm ,opcode))
    ((cl-ppcre:scan "^[0-9a-f]{2}$" opcode) `(emit-raw-byte ,opcode))
    (t `(unknown ,opcode))))

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
              `(tup . ,tup)
              `(ops . ,(loop for op in (cl-ppcre:split " " opc)
                             collect (instruction-opcode-compile op))))))))

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
