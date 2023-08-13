(cl:eval-when (:compile-toplevel)
  (ql:quickload :alexandria)
  (ql:quickload :cl-ppcre)
  (ql:quickload :named-readtables))

(cl:defpackage :clazm
  (:use :cl :alexandria :named-readtables))

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

(defvar *instruction-db* (make-hash-table :test 'equalp))

(defvar *register-db* (make-hash-table :test 'equalp))

(defstruct line
  filename number string)

(defstruct instruction
  line name operands opcodes flags function compiled)

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

(defun regs-process (&optional (filename *nasm/x86/regs.dat*))
  (loop for line in (regs-read-lines filename)
        for register = (regs-parse-line line)
        if (listp register)
          append register
        else
          collect register))

(defun regs-db-push-1 (reg &optional (db *register-db*))
  (assert (not (gethash (register-name reg) db)))
  (setf (gethash (register-name reg) db) reg))

(defun regs-populate-db (&optional (db *register-db*))
  (loop for reg in (regs-process *nasm/x86/regs.dat*)
        do (regs-db-push-1 reg db)))

(defun regs-developer-crank (&optional (db *register-db*))
  (clrhash db)
  (regs-populate-db db))

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

(defun insns-process ()
  (loop for line in (insns-read-lines)
        for instruction = (insns-parse-line line)
        if (listp instruction)
          append instruction
        else
          collect instruction))

(defun insns-db-push-1 (ins &optional (db *instruction-db*))
  (push ins (gethash (instruction-name ins) db)))

(defun instruction-relaxed-p (ins n)
  "Is nth operand relaxed?"
  (find #\* (nth n (instruction-operands ins))))

(defvar *instruction-tuple-codes*
  '(""
    "fv"
    "hv"
    "fvm"
    "t1s8"
    "t1s16"
    "t1s"
    "t1f32"
    "t1f64"
    "t2"
    "t4"
    "t8"
    "hvm"
    "qvm"
    "ovm"
    "m128"
    "dup"))

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

(defvar *prefixes*
  '(("LOCK" . #xF0)
    (("REPNE" "REPNZ") . #xF2)
    (("REP" "REPE" "REPZ" . #xF3))
    ("BND" . #xF2)))

(defparameter *feature-flags*
  '(("PRIV"              "Privileged instruction")
    ("SMM"               "Only valid in SMM")
    ("PROT"              "Protected mode only")
    ("LOCK"              "Lockable if operand 0 is memory")
    ("NOLONG"            "Not available in long mode")
    ("LONG"              "Long mode")
    ("NOHLE"             "HLE prefixes forbidden")
    ("MIB"               "split base/index EA")
    ("SIB"               "SIB encoding required")
    ("BND"               "BND (0xF2) prefix available")
    ("UNDOC"             "Undocumented")
    ("HLE"               "HLE prefixed")
    ("FPU"               "FPU")
    ("MMX"               "MMX")
    ("3DNOW"             "3DNow!")
    ("SSE"               "SSE (KNI MMX2)")
    ("SSE2"              "SSE2")
    ("SSE3"              "SSE3 (PNI)")
    ("VMX"               "VMX")
    ("SSSE3"             "SSSE3")
    ("SSE4A"             "AMD SSE4a")
    ("SSE41"             "SSE4.1")
    ("SSE42"             "SSE4.2")
    ("SSE5"              "SSE5")
    ("AVX"               "AVX  (256-bit floating point)")
    ("AVX2"              "AVX2 (256-bit integer)")
    ("FMA"               "")
    ("BMI1"              "")
    ("BMI2"              "")
    ("TBM"               "")
    ("RTM"               "")
    ("INVPCID"           "")
    ("AVX512"            "AVX-512F (512-bit base architecture)")
    ("AVX512CD"          "AVX-512 Conflict Detection")
    ("AVX512ER"          "AVX-512 Exponential and Reciprocal")
    ("AVX512PF"          "AVX-512 Prefetch")
    ("MPX"               "MPX")
    ("SHA"               "SHA")
    ("PREFETCHWT1"       "PREFETCHWT1")
    ("AVX512VL"          "AVX-512 Vector Length Orthogonality")
    ("AVX512DQ"          "AVX-512 Dword and Qword")
    ("AVX512BW"          "AVX-512 Byte and Word")
    ("AVX512IFMA"        "AVX-512 IFMA instructions")
    ("AVX512VBMI"        "AVX-512 VBMI instructions")
    ("AES"               "AES instructions")
    ("VAES"              "AES AVX instructions")
    ("VPCLMULQDQ"        "AVX Carryless Multiplication")
    ("GFNI"              "Galois Field instructions")
    ("AVX512VBMI2"       "AVX-512 VBMI2 instructions")
    ("AVX512VNNI"        "AVX-512 VNNI instructions")
    ("AVX512BITALG"      "AVX-512 Bit Algorithm instructions")
    ("AVX512VPOPCNTDQ"   "AVX-512 VPOPCNTD/VPOPCNTQ")
    ("AVX5124FMAPS"      "AVX-512 4-iteration multiply-add")
    ("AVX5124VNNIW"      "AVX-512 4-iteration dot product")
    ("AVX512FP16"        "AVX-512 FP16 instructions")
    ("AVX512FC16"        "AVX-512 FC16 instructions")
    ("SGX"               "Intel Software Guard Extensions (SGX)")
    ("CET"               "Intel Control-Flow Enforcement Technology (CET)")
    ("ENQCMD"            "Enqueue command instructions")
    ("PCONFIG"           "Platform configuration instruction")
    ("WBNOINVD"          "Writeback and do not invalidate instruction")
    ("TSXLDTRK"          "TSX suspend load address tracking")
    ("SERIALIZE"         "SERIALIZE instruction")
    ("AVX512BF16"        "AVX-512 bfloat16")
    ("AVX512VP2INTERSECT" "AVX-512 VP2INTERSECT instructions")
    ("AMXTILE"           "AMX tile configuration instructions")
    ("AMXBF16"           "AMX bfloat16 multiplication")
    ("AMXINT8"           "AMX 8-bit integer multiplication")
    ("FRED"              "Flexible Return and Exception Delivery (FRED)")
    ("RAOINT"		 "Remote atomic operations (RAO-INT)")
    ("UINTR"		 "User interrupts")
    ("CMPCCXADD"         "CMPccXADD instructions")
    ("PREFETCHI"         "PREFETCHI0 and PREFETCHI1")
    ("WRMSRNS"		 "WRMSRNS")
    ("MSRLIST"           "RDMSRLIST and WRMSRLIST")
    ("AVXNECONVERT"	 "AVX exceptionless floating-point conversions")
    ("AVXVNNIINT8"       "AVX Vector Neural Network 8-bit integer instructions")
    ("AVXIFMA"           "AVX integer multiply and add")
    ("HRESET"            "History reset")
    ("OBSOLETE"          "Instruction removed from architecture")
    ("NEVER"             "Instruction never implemented")
    ("NOP"               "Instruction is always a (nonintentional) NOP")
    ("VEX"               "VEX or XOP encoded instruction ")
    ("EVEX"              "EVEX encoded instruction")))

(defvar *cpu-flags*
  '(("8086"              "8086")
    ("186"               "186+")
    ("286"               "286+")
    ("386"               "386+")
    ("486"               "486+")
    ("PENT"              "Pentium")
    ("P6"                "P6")
    ("KATMAI"            "Katmai")
    ("WILLAMETTE"        "Willamette")
    ("PRESCOTT"          "Prescott")
    ("X86_64"            "x86-64 (long or legacy mode)")
    ("NEHALEM"           "Nehalem")
    ("WESTMERE"          "Westmere")
    ("SANDYBRIDGE"       "Sandy Bridge")
    ("FUTURE"            "Ivy Bridge or newer")
    ("IA64"              "IA64 (in x86 mode)")
    ("DEFAULT"           "Default CPU level")
    ("ANY"               "Allow any known instruction")
    ("CYRIX"             "Cyrix-specific")
    ("AMD"               "AMD-specific")))

(defun instruction-opcode-compile (opcode)
  (flet ((opcode-to-integer (&key junk-allowed)
           (parse-integer opcode
                          :radix 16
                          :junk-allowed junk-allowed))
         (opcode-to-symbol ()
           (read-from-string opcode)))
   (cond
     ((find opcode *plain-codes* :test #'string=) `(:plain ,(opcode-to-symbol)))
     ((find opcode *imm-codes* :test #'string=)   `(:immediate ,(opcode-to-symbol)))
     ((string= "/is4" opcode)                     `(:is4))
     ((string= "/r" opcode)                       `(:modrm /r))
     ((cl-ppcre:scan "/\\d" opcode)               `(:modrm ,(opcode-to-symbol)))
     ((cl-ppcre:scan "^[0-9a-fA-F]{2}$" opcode)   `(:raw-byte ,(opcode-to-integer)))
     ((cl-ppcre:scan "^evex\\." opcode)           `(:evex ,(subseq opcode 5)))
     ((cl-ppcre:scan "^vex\\." opcode)            `(:vex ,(subseq opcode 4)))
     ((cl-ppcre:scan "^xop\\." opcode)            `(:xop ,(subseq opcode 4)))
     ((cl-ppcre:scan "^[0-9a-f]{2}\\+r$" opcode)  `(:+r ,(opcode-to-integer :junk-allowed t)))
     (t                                           `(:unknown ,opcode)))))

(defvar *args* 'args)
(defvar *all-binding-symbols* nil)

(defvar x)
(defvar s)
(defvar v)
(defvar j)
(defvar r)
(defvar m)
(defvar i)

(defun operand-type-check (args index spec)
  (declare (ignore args index spec)))

(defun emit-code-for-plain (arg)
  (case arg
    ))

(defun instruction-compile (ins)
  (when-let* ((opcodes (instruction-opcodes ins))
              (codestring (multiple-value-bind (match strings)
                              (cl-ppcre:scan-to-strings "^\\s*\\[([^\\]]*)\\]\\s*$" opcodes)
                            (when match (aref strings 0))))
              (parts (multiple-value-bind (match strings)
                         (cl-ppcre:scan-to-strings "^(([^\\s:]*)\\:*([^\\s:]*)\\:|)\\s*(.*\\S)\\s*$" codestring)
                       (when match strings)))
              (opr (aref parts 1))
              (opc (aref parts 3))
              (oppos (loop with oppos
                           with op = 0
                           for c across opr
                           for i from 0
                           do (cond ((char= #\+ c) (decf op))
                                    (t
                                     (progn
                                       (when (instruction-relaxed-p ins i)
                                         (decf op))
                                       (appendf oppos (list (cons c op)))
                                       (incf op))))
                           finally (return oppos)))
              (type-checks (loop for o in (instruction-operands ins)
                                 for (v . pos) in oppos
                                 collect `(operand-type-check ,*args* ,pos ,o)))
              (binding-symbols (mapcar (lambda (oppos)
                                         (let ((op (car oppos)))
                                           (read-from-string (format nil "~C" op))))
                                       oppos))
              (binding-values (loop for (op . pos) in oppos
                                    collect `(nth ,pos ,*args*)))
              (bindings (loop for s in binding-symbols
                              for v in binding-values
                              unless (eq s '-)
                                collect `(,s ,v)
                                and do (pushnew s *all-binding-symbols*)))
              (code (loop for o in (cl-ppcre:split " " opc)
                          collect (instruction-opcode-compile o)))
              (doc (format nil "~A~@[ ~{~A~^,~}~]~@[ [~{~A~^ ~}]~]" (instruction-name ins)
                                                                    (instruction-operands ins)
                                                                    (instruction-flags ins))))
    `(lambda (&rest ,*args*)
       ,doc
       ,@type-checks
       (let ,bindings
         '(asm-build ,code)))))

(defun insns-db-populate (&optional (db *instruction-db*))
  (mapcar (lambda (ins) (insns-db-push-1 ins db)) (insns-process))
  db)

(defun insns-db-compile (&optional (db *instruction-db*))
  (maphash (lambda (k v)
             (declare (ignore k))
             (mapcar (lambda (ins)
                       (let ((f (instruction-compile ins)))
                         (setf (instruction-function ins) f)
                         (when f
                           (setf (instruction-compiled ins) (compile nil f)))))
                     v))
           db))

(defun db-print (&optional (db *instruction-db*))
  (maphash (lambda (k v)
             (format t "(~S ~S)~%" k v))
           db))

(defun insns-developer-crank (&optional (db *instruction-db*))
  (clrhash db)
  (insns-db-populate db)
  (insns-db-compile db))

(defun developer-crank ()
  (regs-developer-crank)
  (insns-developer-crank))

;; (defmacro with-asm-syntax (syntax &body body)
;;   (with-gensyms (readtable)
;;     `(let ((*readtable* (copy-readtable)))
;;        ,@body)))

;; (defmacro with-saved-registers ((&rest regs) &body body)
;;   (declare (ignore regs))
;;   `(progn
;;      ,@body))

;; (defun asm-test ()
;;   (with-asm-syntax 'x86-intel
;;     (with-saved-registers (rax)
;;       (add [bx+si] al)   ; opcode=0x00 (add byte, mem dst)  mod=00 r=000 r/m=000
;;       (add ax ax)        ; add r/m, r   mod=11 (register) r=000 (AX) r/m=0 (AX)
;;       (add [bx+si] cx)   ; add r/m, r
;;       (add cx [bx+si])   ; mod=0, r=001 (CX) r/m=000 ([bx+si])
;;       (add cx [bx])      ; mod=00 r=001 (CX) r/m=111 ([BX])
;;       (add cx [bx + 4])  ; mod=01 r=001 (CX) r/m=111  disp8=4
;;       (add dx si)        ; mod=11 r=110 (SI) r/m=010 (DX)
;;       )))


(defun statement-parameter-type (p)
  (etypecase p
    (register (register-assembler-class p))
    (t p)))

(defun compatible-p (operand parameter)

  (cond ((register-p parameter) (setf parameter (register-assembler-class parameter))))
  (let ((result (equalp operand parameter)))

    result))

(defun instruction-compatible-p (instruction parameters)
  (when-let* ((n-instruction-operands (length (instruction-operands instruction)))
              (n-parameters (length parameters))
              (parameter-count-compatible (= n-instruction-operands n-parameters)))
    (loop for o in (instruction-operands instruction)
          for p in parameters
          if (not (compatible-p o p))
            return nil
          finally (return t))))

(defun find-instruction-for-parameters (candidates parameters)
  (list candidates parameters))

(defun regs-find-by-name (name &optional (db *register-db*))
  (gethash (format nil "~A" name) db))

(defun insns-find-by-name (name &optional (db *instruction-db*))
  (gethash (format nil "~A" name) db))

(defun statement-assemble (statement)
  (flet ((make-parameter (p)
           (or (regs-find-by-name p) p)))
    (let ((instructions (insns-find-by-name (car statement)))
          (parameters (mapcar #'make-parameter (cdr statement))))
      (find-instruction-for-parameters instructions parameters))))

(defparameter *parameter-size-default* 4)
(defparameter *parameter-is-ptr-default* nil)

(defparameter *parameter-size* *parameter-size-default*)
(defparameter *parameter-is-ptr* *parameter-is-ptr-default*)

(defstruct rex-prefix
  (w 0 :type fixnum)
  (r 0 :type fixnum)
  (x 0 :type fixnum)
  (b 0 :type fixnum))

(defstruct modr/m
  (mod 0 :type fixnum)
  (reg 0 :type fixnum)
  (r/m 0 :type fixnum))

(defstruct sib
  (scale 0 :type fixnum)
  (index 0 :type fixnum)
  (base 0 :type fixnum))

;; (defun bit-p (x)
;;   (cond ((not x) 0)
;;         ((zerop x) 0)
;;         (t 1)))

;; (defun rex-prefix-to-byte (rex-prefix)
;;   (with-slots (w r x b) rex-prefix
;;     (build-byte (#b0100 :size 4)
;;       (w :size 1)
;;       (r :size 1)
;;       (x :size 1)
;;       (b :size 1))))

;; (defun mod/rm-to-byte (modr/m)
;;   (with-slots (mod reg r/m) modr/m
;;     (build-byte (mod :size 2)
;;                 (reg :size 3)
;;                 (r/m :size 3))))

(defun parameter-size-string-to-size (string)
  (cond ((equalp string "byte") 1)
        ((equalp string "word") 2)
        ((equalp string "dword") 4)
        ((equalp string "qword") 8)))

(defstruct immediate
  string
  size
  val)

(defstruct memory-reference
  string
  size
  ptr)

(defun parse-memory-reference (mem-string)

  (let ((ref (make-memory-reference :string mem-string
               :size *parameter-size*
               :ptr *parameter-is-ptr*)))
    (setf *parameter-size* *parameter-size-default*
      *parameter-is-ptr* *parameter-is-ptr-default*)
    ref))

(defconstant +left-bracket+ #\[)
(defconstant +right-bracket+ #\])

(defun read-separator (stream char)
  (declare (ignore stream))
  (error "Separator ~S shouldn't be read alone" char))

(defun read-until (stream end-char &optional (drop-end-char t))
  (flet ((peek-next () (peek-char t stream t nil t))
         (read-next () (read-char stream t nil t)))
    (coerce (loop for c = (peek-next)
                  until (char= c end-char)
                  collect (read-next)
                  finally (when drop-end-char
                            (read-next)))
            'string)))

(defun read-left-bracket (stream char)
  (assert (char= char +left-bracket+))
  (parse-memory-reference (read-until stream +right-bracket+)))

(defreadtable asm-syntax-table
  (:merge :standard)
  (:macro-char +left-bracket+ 'read-left-bracket)
  (:macro-char +right-bracket+ 'read-separator))
