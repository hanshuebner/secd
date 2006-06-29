(in-package :secd-tools)

(defmacro with-output-to ((filename) &body body)
  `(with-open-file (*standard-output* ,filename :direction :output)
    ,@body))

(defmacro with-input-from ((filename) &body body)
  `(with-open-file (*standard-input* ,filename)
    ,@body))