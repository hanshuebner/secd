(in-package :secd-tools)

(defconstant +memory-size+ 16384)
(defconstant +memory-address-bits+ 14)

(defvar *symbol-number* 0)
(defvar *symbol-table* (make-hash-table))

(defvar *p* 0)
(defvar *memory* nil)

(defstruct (memory-word (:conc-name mw-))
  type car cdr mark field note)

(defun lookup-symbol-reverse (number)
  (loop for key being the hash-keys of *symbol-table*
        when (equal (gethash key *symbol-table*) number)
        return key))

(defmethod print-object ((mw memory-word) stream)
  (ecase (mw-type mw)
    (cons (format stream "~&#<CONS ~A ~A" (mw-car mw) (mw-cdr mw)))
    (symbol (format stream "~&#<SYMBOL ~A" (lookup-symbol-reverse (mw-car mw))))
    (number (format stream "~&#<NUMBER ~A" (mw-car mw))))
  (when (mw-mark mw)
    (format stream " (marked)"))
  (format stream ">"))

;; XXX type 1 not used?

(defun make-binary (mw)
  (ecase (mw-type mw)
    (cons (dpb (mw-car mw) (byte 14 14) (mw-cdr mw)))
    (symbol (dpb 2 (byte 4 28) (mw-car mw)))
    (number (dpb 3 (byte 4 28) (mw-car mw)))))

(defun add-to-memory (&rest args)
  (setf (aref *memory* *p*) (apply #'make-memory-word args))
  (prog1
      *p*
    (incf *p*)))

(defun %cons (car cdr &optional note)
  (add-to-memory :type 'cons :car car :cdr cdr :note note))

(defun init-symbol-table ()
  (prog1
      (setf *symbol-table* (make-hash-table))
    (setf *symbol-number* 0)
    (lookup-symbol 'nil)
    (lookup-symbol 't)
    (lookup-symbol 'f)))
  
(defun lookup-symbol (symbol)
  (or (gethash symbol *symbol-table*)
      (prog1
          (setf (gethash symbol *symbol-table*) *symbol-number*)
        (incf *symbol-number*))))

(defun process (object &optional note)
  (cond
    ((symbolp object)
     (add-to-memory :type 'symbol :car (lookup-symbol object) :note note))
    ((listp object)
     (%cons (process (car object) note)
            (if (cdr object)
                (process (cdr object) note)
                0)
            note))
    ((numberp object)
     (add-to-memory :type 'number :car object :note note))
    (t (error "unknown object ~A" object))))

(defun init-memory (&key (init-symbol-table t))
  (setf *memory* (make-array +memory-size+))
  (setf *p* 0)
  (when init-symbol-table
    (add-to-memory :car 0 :type 'symbol :note 'nil)
    (add-to-memory :car 1 :type 'symbol :note 'true)
    (add-to-memory :car 2 :type 'symbol :note 'false)))

(defun create-memory (input argument)
  (init-memory)
  (init-symbol-table)
  (let* ((secd-program (typecase input
                         (string (with-open-file (input input)
                                   (read input)))
                         (t input)))
         (program-addr (process secd-program 'prog))
         (arg-addr (process (list (list (typecase argument
                                          (string (with-open-file (input argument)
                                                    (read input)))
                                          (t argument))))
                            'arg))
         (problem-addr (%cons program-addr arg-addr 'problem))
         (free-list-addr *p*))
    ;; set up free list
    (loop for addr from *p* below (1- +memory-size+)
          do (%cons 0 (1+ addr) 'free))
    (%cons problem-addr free-list-addr 'initialize)
    (assert (eql 16384 *p*))))

(defun write-c-ram ()
  (let ((free-list-start (mw-cdr (aref *memory* 16383)))
        (*print-base* 16))
    (loop for addr from 0 below free-list-start
          for word = (make-binary (aref *memory* addr))
          do (format t "~{0x~A, ~}~%" (list (ldb (byte 8  0) word)
                                            (ldb (byte 8  8) word)
                                            (ldb (byte 8 16) word)
                                            (ldb (byte 8 24) word))))))

(defun write-c-problem ()
  (let ((problem (dpb 16383 (byte 14 0) (make-binary (aref *memory* 16383)))))
    (format t "~16,8,'0R" problem)))

(defun write-vhdl-ram (input argument output-pathname)
  (create-memory input argument)
  
  (with-open-file (output output-pathname :direction :output :if-does-not-exist :create)
    (format output "
-- Automatically generated RAM initialization definitions for SECD program ~A and argument ~A~%" input argument)
    (format output "

library ieee;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package secd_ram_defs is

constant RAM_SIZE : integer := ~A;
constant RAM_ADDRESS_BITS : integer := ~A;
type RAM_TYPE is array (0 to (RAM_SIZE - 1)) of std_logic_vector (31 downto 0);
constant RAM_INIT : RAM_TYPE := (~%"
            +memory-size+ +memory-address-bits+)

    (loop for addr from 0 below +memory-size+
          for mw = (aref *memory* addr)
          do (format output " \"~2,28,'0R\"~@[~*,~] -- ~A ~A ~A~%"
                     (make-binary mw) (> (1- +memory-size+) addr) addr (mw-note mw) mw))
    (format output ");

end package;

")))

(defun read-dump (filename)
  (init-memory :init-symbol-table nil)
  (with-open-file (input filename)
    (let (roots)
      (handler-case
          (loop for line = (read-line input nil)
                for addr = (parse-integer (subseq line 0 5) :junk-allowed t)
                while line
                do (if addr
                       (assert (eql addr
                                    (let ((type (ecase (aref line 9)
                                                  (#\C 'cons)
                                                  (#\I 'number)
                                                  (#\S 'symbol))))
                                      (add-to-memory
                                       :mark (equal #\M (aref line 7))
                                       :type type
                                       :car (parse-integer (subseq line 11 (+ 11 (if (eq 'cons type) 5 11))))
                                       :cdr (if (eq 'cons type) (parse-integer (subseq line 17 22)) nil)))))
                       (let ((reg (intern (string-upcase (subseq line 0 (position #\: line)))))
                             (addr (parse-integer (subseq line (1+ (position #\: line))))))
                         (push (cons reg addr) roots))))
        (error (e)
          (warn "error ignored: ~A~%" e)))
      (format t "done reading~%")
      roots)))

(defun mark (address)
  (unless (mw-mark (aref *memory* address))
    (setf (mw-mark (aref *memory* address)) t)
    (when (eq 'cons (mw-type (aref *memory* address)))
      (mark (mw-car (aref *memory* address)))
      (mark (mw-cdr (aref *memory* address))))))

(defun do-mark (roots)
  (mark 0)
  (mark 1)
  (mark 2)
  (dolist (root roots)
    (destructuring-bind (register . address) root
      (declare (ignore register))
      (mark address))))

(defun marked ()
  (loop for i from 0 below 16384
        when (mw-mark (aref *memory* i))
        collect i))

(defun sweep ()
  (loop with free = 16383
        for p from 16383 downto 0
        do (if (mw-mark (aref *memory* p))
               (setf (mw-mark (aref *memory* p)) nil)
               (progn
                 (setf (mw-type (aref *memory* p)) 'cons)
                 (setf (mw-car (aref *memory* p)) 0)
                 (setf (mw-cdr (aref *memory* p)) free)
                 (setf free p)))
        finally (return free)))