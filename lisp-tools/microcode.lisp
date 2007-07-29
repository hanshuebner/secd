(in-package :secd-tools)

(defconstant +default-microcode-length+ 1024)

(defvar *labels*)
(defvar *slebal*)
(defvar *microcode*)

(defun find-label (key)
  (etypecase key
    (number (gethash key *slebal*))
    (symbol (gethash key *labels*))))

(defun reset ()
  (setf *slebal* (make-hash-table :test #'equal))
  (setf *labels* (make-hash-table))
  (setf *microcode* (make-array +default-microcode-length+ :adjustable t :fill-pointer 0)))

(defun define-label (label address)
  (when (gethash label *labels*)
    (error "can't redefine label ~A to ~A, already defined to ~A" label address (gethash label *labels*)))
  (setf (gethash label *labels*) address)
  (setf (gethash address *slebal*) label))

(defstruct (microinstruction (:conc-name mi-) (:constructor make-microinstruction/unchecked))
  line-number addr label status read write alu test a)

(defun make-microinstruction (&rest args &key read write alu &allow-other-keys)
  (when read
    (unless (position read *read-regs*)
      (error "invalid read register ~S specified in microinstruction" read)))
  (when write
    (unless (position write *write-regs*)
      (error "invalid write register ~S specified in microinstruction" write)))
  (when alu
    (unless (position alu *alu-ops*)
      (error "invalid ALU operation ~S specified in microinstruction" alu)))
  (apply #'make-microinstruction/unchecked args))

(defparameter +microinstruction-format+ "~(~3A ~15A ~3A ~10A ~10A ~11A ~@[~*~9A ~A~]~)~%")

(defun print-microinstruction-picture (&optional (stream *standard-output*))
  (format stream +microinstruction-format+
          "###"
          "LLLLLLLLLLLLLLL"
          "SSS"
          "RRRRRRRRR"
          "WWWWWWWWW"
          "AAAAAAAAAAA"
          t
          "TTTTTTTTT"
          "JJJJJJJJJJ"))

(defun print-microinstruction (mi &optional (stream *standard-output*))
  (format stream +microinstruction-format+
          (mi-addr mi)
          (or (mi-label mi) "")
          (or (mi-status mi) "")
          (or (mi-read mi) "")
          (or (mi-write mi) "")
          (or (mi-alu mi) "")
          (mi-test mi)
          (mi-test mi)
          (if (or (not (mi-a mi))
                  (zerop (mi-a mi)))
              ""
              (find-label (mi-a mi)))))

(defun make-microinstruction-from-string (line-number string)
  (let ((field-descriptions '((:addr 0 3)
                              (:label 4 15)
                              (:status 20 1)
                              (:read 24 10)
                              (:write 35 10)
                              (:alu 46 11)
                              (:test 58 9)
                              (:a 68)))
        args)
    (loop for field-description in field-descriptions
          with last-end = 0
          do (destructuring-bind (field-name offset &optional length) field-description
               (unless (zerop offset)
                   (loop for last-end from last-end below (min offset (length string))
                         do (unless (eq #\Space (aref string last-end))
                              (error "Illegal non-space character ~A at position ~A"
                                     (aref string last-end) last-end))))
               (when length
                 (setf last-end (+ offset length)))
               (when (> (length string) offset)
                 (let ((contents (string-right-trim '(#\Space) (subseq string offset
                                                                       (when length (min (length string)
                                                                                         (+ offset length)))))))
                   (unless (equal "" contents)
                     (push (or (parse-integer contents :junk-allowed t)
                               (intern (string-upcase contents))) args)
                     (push field-name args))))))
    (apply #'make-microinstruction :line-number line-number args)))

(defun parse-intermediate-line (line)
  (destructuring-bind (addr status read write alu test a) (read-from-string (format nil "(~A))" line))
    (make-microinstruction :addr addr
                           :status status
                           :read (and read (nth read *read-regs*))
                           :write (and write (nth write *write-regs*))
                           :alu (and alu (nth alu *alu-ops*))
                           :test (and test (nth test *next-mi-code*))
                           :label (find-label addr)
                           :a a)))

(defun read-intermediate ()
  (reset)
  (let ((original-labels '(22 "boot" 24 "error" 26 "_3" 28
                           "start-program" 43 "top-of-cycle" 47 "ld" 56 "_7" 61 "_8" 72 "_9" 77
                           "_10" 86 "ldc" 97 "ldf" 110 "ap" 137 "rtn" 156 "dum" 161 "rap" 192
                           "sel" 213 "_18" 218 "_19" 220 "join" 226 "car" 236 "cdr" 245 "atom"
                           250 "_24" 251 "_25" 256 "cons" 272 "eq" 275 "_28" 276 "_29" 278 "add"
                           282 "sub" 286 "mul" 290 "div" 294 "rem" 298 "leq" 301 "_36" 302 "_37"
                           304 "stop" 309 "setup-alu-args" 318 "push-alu-result" 325 "consx1x2"
                           326 "_42" 329 "cons-gc" 331 "alu-gc" 332 "_45" 335 "_46" 337 "gc" 348
                           "_48" 352 "_49" 353 "_50" 355 "_51" 357 "mark" 358 "_53" 372 "_54" 383
                           "_55" 398 "_56")))
    (loop for (address label) on original-labels by #'cddr
          do (define-label (intern (string-upcase label)) address))
    (with-open-file (f #p"../SECD-Proof/intermediate")
      (assert (eql 399 (read f)))
      (loop for i from 0 below 399
            for line = (read-line f)
            do (vector-push-extend (parse-intermediate-line line) *microcode*)))))

(defun find-jump-targets ()
  (read-intermediate)
  (let (targets)
    (loop for mi across *microcode*
          do (unless (zerop (mi-a mi))
               (pushnew (mi-a mi) targets :test #'eql)))
    (reverse targets)))

(defun list-microcode (&optional (stream *standard-output*))
  (let ((*standard-output* stream))
    (print-microinstruction-picture stream)
    (loop for mi across *microcode*
          for addr = (mi-addr mi)
          do (let ((label (find-label addr)))
               (when (and (not (nth addr *secd-inst*))
                          label
                          (not (eq #\_ (aref (symbol-name label) 0))))
                 (princ "-------------------------------------------------------------------------------------")
                 (terpri))
               (print-microinstruction mi)))))

(defun assemble-microcode (filename)
  (with-open-file (input filename)
    (with-open-file (listing (merge-pathnames (make-pathname :type "lis") filename) :direction :output)
      (with-open-file (vhdl-output (merge-pathnames (make-pathname :type "vhd") filename) :direction :output)
        (with-open-stream (*standard-output* (make-broadcast-stream *standard-output* listing))
          (with-open-stream (*error-output* (make-synonym-stream '*standard-output*))
            (parse-microcode input :listing listing :filename filename)
            (write-vhdl-rom vhdl-output)))))))

(defun parse-microcode (input &key listing filename)
  (let ((errors 0))
    (reset)
    ;; pass1 - parse microcode, remember all labels
    (loop for line = (read-line input nil)
          for line-number from 1
          with addr = 0
          while line
          do (if (or (equal 0 (length line)) (find (aref line 0) '(#\# #\-)))
                 (format listing "     ~A~%" line)
                 (progn
                   (format listing "~4A ~A~%" addr line)
                   (handler-case
                       (let ((mi (make-microinstruction-from-string line-number line)))
                         (setf (mi-addr mi) addr)
                         (when (mi-label mi)
                           (define-label (mi-label mi) addr))
                         (vector-push-extend mi *microcode*)
                         (incf addr))
                     (error (e)
                       (incf errors)
                       (format *error-output* "~A line ~A: ~A~%" filename line-number e))))))
    ;; pass2 - resolve labels
    (loop for mi across *microcode*
          when (mi-a mi)
          do (handler-case
                 (etypecase (mi-a mi)
                   (symbol (setf (mi-a mi) (or (find-label (mi-a mi))
                                               (error "undefined jump target ~A" (mi-a mi)))))
                   (number (warn "literal jump target ~A in line ~A" mi (mi-line-number mi))))
               (error (e)
                 (incf errors)
                 (format *error-output* "~A line ~A: ~A~%" filename (mi-line-number mi) e))))
    (unless (zerop errors)
      (error "~A: ~A error~:P~%" filename errors))))

(defun write-intermediate ()
  (format t "~A~%" (length *microcode*))
  (loop for mi across *microcode*
        do (progn
             (princ (mi-addr mi))
             (princ #\tab)
             (princ (mi-status mi))
             (princ #\tab)
             (princ (or (position (mi-read mi) *read-regs*) 0))
             (princ #\tab)
             (princ (or (position (mi-write mi) *write-regs*) 0))
             (princ #\tab)
             (princ (or (position (mi-alu mi) *alu-ops*) 0))
             (princ #\tab)
             (princ (or (position (mi-test mi) *next-mi-code*) 0))
             (princ #\tab)
             (princ (or (mi-a mi) 0))
             (princ #\tab)
             (princ #\newline))))

(defun resolve-field (field field-list)
  (if field
      (or (position field field-list)
          (error "invalid symbolic value ~A for field ~A" field field-list))
      0))

(defun write-vhdl-rom (&optional (stream *standard-output*))
  (let ((rom-size (expt 2 (ceiling (log (length *microcode*) 2)))))
    (format stream "

-- Automatically generated SECD microcode

library ieee;

use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity microcode_rom is
  port (clk  : in std_logic;
        en   : in std_logic;
        addr : in std_logic_vector(8 downto 0);
        data : out std_logic_vector(27 downto 0));
end microcode_rom;

architecture rtl of microcode_rom is

constant MICROCODE_ROM_SIZE : integer := ~A;
type rom_type is array (0 to MICROCODE_ROM_SIZE - 1) of std_logic_vector (27 downto 0);
constant MICROCODE_ROM : rom_type := (~%" rom-size)
  (with-standard-io-syntax 
    (loop for mi across *microcode*
          do (format stream "\"~2,9,'0R~2,4,'0R~2,5,'0R~2,5,'0R~2,5,'0R\", -- "
                     (or (mi-a mi) 0)
                     (resolve-field (mi-test mi) *next-mi-code*)
                     (resolve-field (mi-alu mi) *alu-ops*)
                     (resolve-field (mi-write mi) *write-regs*)
                     (resolve-field (mi-read mi) *read-regs*))
          do (print-microinstruction mi stream)))
    (format stream "others => (others => '0'));

begin

  process (clk)
  begin
    if falling_edge(clk) then
      if en = '1' then
        data <= MICROCODE_ROM(conv_integer(addr));
      end if;
    end if;
  end process;


end;
~%")))

