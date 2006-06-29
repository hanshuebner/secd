(in-package :secd-tools)

(loop for code in *read-regs* for i from 0 do (format t "  constant ~(~7A~) : std_logic_vector := \"~2,5,'0R\";~%" code i))

(loop for code in *write-regs* for i from 0 do (format t "  constant ~(~7A~) : std_logic_vector := \"~2,5,'0R\";~%" code i))

(loop for code in *alu-ops* for i from 0 do (format t "  constant ~(~10A~) : std_logic_vector := \"~2,4,'0R\";~%" code i))

(loop for code in *next-mi-code* for i from 0 do (format t "  constant ~(~8A~) : std_logic_vector := \"~2,4,'0R\";~%" code i))