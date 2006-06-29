;; -*- Lisp -*-

(in-package :cl-user)

(defpackage :secd-tools.system
  (:use :cl :asdf))

(in-package :secd-tools.system)

(defsystem :secd-tools
    :name "SECD tools"
    :description "Microcode assembler and disassembler tools for the SECD microprocessor"
    :author "Hans Hübner <hans.huebner@gmail.com>"
    :licence "BSD"

    :components ((:file "packages")
                 (:file "secd-defs" :depends-on ("packages"))
                 (:file "tools" :depends-on ("packages"))
                 (:file "microcode" :depends-on ("tools" "secd-defs"))
                 (:file "secd-ram" :depends-on ("tools" "secd-defs"))))