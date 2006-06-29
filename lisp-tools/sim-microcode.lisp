(in-package :secd-tools)

(defvar *regs* (make-hash-table))
(defvar *mpc* 0)
(defvar *microcode* (read-intermediate))

(defun reset ()
  (setf *mpc* 0)
  (setf *regs* (make-hash-table)))

(defun read-reg (name)
  (or (gethash name *regs*) 0))

(defun write-reg (name value)
  (setf (gethash name *regs*) value))

(defun read-mem (addr)
  (aref *memory* addr))

(defun write-mem (addr value)
  (setf (aref *memory* addr) value))

(defun execute-next ()
  (let ((mi (nth *mpc* *microcode*))
        databus)
    (format t "~A~%" mi)
    (when (mi-read mi)
      (case (mi-read mi)
        (num (setf databus 4095))
        (mem (setf databus (read-mem (gethash 'mar *regs*))))
        (t (setf databus (gethash (mi-read mi) *regs*)))))
    (when (mi-alu mi)
      (execute-alu mi))
    (when (mi-write mi)
      (setf (gethash (mi-write mi) *regs*) databus))
    (setf *mpc*
          (ecase (mi-test mi)
            (jump (mi-a mi))
            (button? (mi-a mi))
            (next (1+ *mpc*))))))
