;; to load the microcode workbench
(asdf:oos 'asdf:load-op :secd-tools)

(in-package :secd-tools)

;; assuming that you are chdir'd to the secd-tools directory:

;; to assemble the microcode file:
(assemble-microcode "../secd-microcode.txt")

;; to set up a ram image for the simulator:
(write-vhdl-ram "../lispkit/LKIT-2/NQUEEN.LKC" 6 "../vhdl/secd_ram_defs.vhd")