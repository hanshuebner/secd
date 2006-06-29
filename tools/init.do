asim -xtrace -advdataflow  testbench_for_secd_system
run @10ms
onbreak {
        runscript -perl {H:\fpga\secd\tools\secd-state.do}
}
runscript -perl {H:\fpga\secd\tools\secd-state.do}
