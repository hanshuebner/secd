

-- Automatically generated SECD microcode

library ieee;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package microcode_rom_defs is

constant MICROCODE_ROM_SIZE : integer := 512;
type rom_type is array (0 to MICROCODE_ROM_SIZE - 1) of std_logic_vector (27 downto 0);
constant MICROCODE_ROM : rom_type := (
"0000101100001000000000000000", -- 0                                                         jump      boot
"0001011110001000000000000000", -- 1   ld-ins                                                jump      ld
"0010101100001000000000000000", -- 2   ldc-ins                                               jump      ldc
"0011000010001000000000000000", -- 3   ldf-ins                                               jump      ldf
"0011011100001000000000000000", -- 4   ap-ins                                                jump      ap
"0100010100001000000000000000", -- 5   rtn-ins                                               jump      rtn
"0100111010001000000000000000", -- 6   dum-ins                                               jump      dum
"0101000100001000000000000000", -- 7   rap-ins                                               jump      rap
"0110000010001000000000000000", -- 8   sel-ins                                               jump      sel
"0110111010001000000000000000", -- 9   join-ins                                              jump      join
"0111000110001000000000000000", -- 10  car-ins                                               jump      car
"0111011010001000000000000000", -- 11  cdr-ins                                               jump      cdr
"0111101100001000000000000000", -- 12  atom-ins                                              jump      atom
"1000000010001000000000000000", -- 13  cons-ins                                              jump      cons
"1000100010001000000000000000", -- 14  eq-ins                                                jump      eq
"1000101110001000000000000000", -- 15  add-ins                                               jump      add
"1000110110001000000000000000", -- 16  sub-ins                                               jump      sub
"1000111110001000000000000000", -- 17  mul-ins                                               jump      mul
"1001000110001000000000000000", -- 18  div-ins                                               jump      div
"1001001110001000000000000000", -- 19  rem-ins                                               jump      rem
"1001010110001000000000000000", -- 20  leq-ins                                               jump      leq
"1001100010001000000000000000", -- 21  stop-ins                                              jump      stop
"0000111001010100010000000000", -- 22  boot            1                         halted      button?   start-program
"0000101100001000000000000000", -- 23                                                        jump      boot
"0000110101010000000000000000", -- 24  error           2                                     button?   _3
"0000110000001000000000000000", -- 25                                                        jump      error
"0000110101010000000000000000", -- 26  _3                                                    button?   _3
"0000101100001000000000000000", -- 27                                                        jump      boot
"0000000000000100000101010011", -- 28  start-program       num        mar        running     
"0000000000000000000010100010", -- 29                      mem        car                    
"0000000000000000000101000110", -- 30                      car        mar                    
"0000000000000000000011000010", -- 31                      mem        s                      
"0000000000000000000011110100", -- 32                      nilx       e                      
"0000000000000000000101010011", -- 33                      num        mar                    
"0000000000000000000010100010", -- 34                      mem        car                    
"0000000000000000000101000110", -- 35                      car        mar                    
"0000000000000000000010100010", -- 36                      mem        car                    
"0000000000000000000100000110", -- 37                      car        c                      
"0000000000000000000100110100", -- 38                      nilx       d                      
"0000000000000000000101110100", -- 39                      nilx       x1                     
"0000000000000000000110010100", -- 40                      nilx       x2                     
"0000000000000000000101010011", -- 41                      num        mar                    
"0000000000000000000110100010", -- 42                      mem        free                   
"0000000000000000000101001001", -- 43  top-of-cycle        c          mar                    
"0000000000000000000010100010", -- 44                      mem        car                    
"0000000000000000000101000110", -- 45                      car        mar                    
"0000000000010000000001000010", -- 46                      mem        arg                    dispatch  
"0000000000000000000101101000", -- 47  ld                  e          x1                     
"0000000000000000000101001001", -- 48                      c          mar                    
"0000000000000000000110000010", -- 49                      mem        x2                     
"0000000000000000000101001101", -- 50                      x2         mar                    
"0000000000000000000010100010", -- 51                      mem        car                    
"0000000000000000000101000110", -- 52                      car        mar                    
"0000000000000000000010100010", -- 53                      mem        car                    
"0000000000000000000101000110", -- 54                      car        mar                    
"0000000000000000000001000010", -- 55                      mem        arg                    
"0001111011001000000000000011", -- 56  _7                  arg                               nil?      _8
"0000000000000000000101001100", -- 57                      x1         mar                    
"0000000000000000000101100010", -- 58                      mem        x1                     
"0000000000000000010001100000", -- 59                                 buf1       dec         
"0001110000001000000001000100", -- 60                      buf1       arg                    jump      _7
"0000000000000000000101001100", -- 61  _8                  x1         mar                    
"0000000000000000000010100010", -- 62                      mem        car                    
"0000000000000000000101100110", -- 63                      car        x1                     
"0000000000000000000101001001", -- 64                      c          mar                    
"0000000000000000000110000010", -- 65                      mem        x2                     
"0000000000000000000101001101", -- 66                      x2         mar                    
"0000000000000000000010100010", -- 67                      mem        car                    
"0000000000000000000101000110", -- 68                      car        mar                    
"0000000000000000000110000010", -- 69                      mem        x2                     
"0000000000000000000101001101", -- 70                      x2         mar                    
"0000000000000000000001000010", -- 71                      mem        arg                    
"0010011011001000000000000011", -- 72  _9                  arg                               nil?      _10
"0000000000000000000101001100", -- 73                      x1         mar                    
"0000000000000000000101100010", -- 74                      mem        x1                     
"0000000000000000010001100000", -- 75                                 buf1       dec         
"0010010000001000000001000100", -- 76                      buf1       arg                    jump      _9
"0000000000000000000101001100", -- 77  _10                 x1         mar                    
"0000000000000000000010100010", -- 78                      mem        car                    
"0000000000000000000101100110", -- 79                      car        x1                     
"1010001101011000000110000111", -- 80                      s          x2                     call      consx1x2
"0000000000000000000011001011", -- 81                      mar        s                      
"0000000000000000000101001001", -- 82                      c          mar                    
"0000000000000000000100000010", -- 83                      mem        c                      
"0000000000000000000101001001", -- 84                      c          mar                    
"0001010110001000000100000010", -- 85                      mem        c                      jump      top-of-cycle
"0000000000000000000110000111", -- 86  ldc                 s          x2                     
"0000000000000000000101001001", -- 87                      c          mar                    
"0000000000000000000101100010", -- 88                      mem        x1                     
"0000000000000000000101001100", -- 89                      x1         mar                    
"0000000000000000000010100010", -- 90                      mem        car                    
"1010001101011000000101100110", -- 91                      car        x1                     call      consx1x2
"0000000000000000000011001011", -- 92                      mar        s                      
"0000000000000000000101001001", -- 93                      c          mar                    
"0000000000000000000100000010", -- 94                      mem        c                      
"0000000000000000000101001001", -- 95                      c          mar                    
"0001010110001000000100000010", -- 96                      mem        c                      jump      top-of-cycle
"0000000000000000000110001000", -- 97  ldf                 e          x2                     
"0000000000000000000101001001", -- 98                      c          mar                    
"0000000000000000000101100010", -- 99                      mem        x1                     
"0000000000000000000101001100", -- 100                     x1         mar                    
"0000000000000000000010100010", -- 101                     mem        car                    
"1010001101011000000101100110", -- 102                     car        x1                     call      consx1x2
"0000000000000000000101101011", -- 103                     mar        x1                     
"1010001101011000000110000111", -- 104                     s          x2                     call      consx1x2
"0000000000000000000011001011", -- 105                     mar        s                      
"0000000000000000000101001001", -- 106                     c          mar                    
"0000000000000000000100000010", -- 107                     mem        c                      
"0000000000000000000101001001", -- 108                     c          mar                    
"0001010110001000000100000010", -- 109                     mem        c                      jump      top-of-cycle
"0000000000000000000110001010", -- 110 ap                  d          x2                     
"0000000000000000000101001001", -- 111                     c          mar                    
"1010001101011000000101100010", -- 112                     mem        x1                     call      consx1x2
"0000000000000000000110001011", -- 113                     mar        x2                     
"1010001101011000000101101000", -- 114                     e          x1                     call      consx1x2
"0000000000000000000110001011", -- 115                     mar        x2                     
"0000000000000000000101000111", -- 116                     s          mar                    
"0000000000000000000101100010", -- 117                     mem        x1                     
"0000000000000000000101001100", -- 118                     x1         mar                    
"1010001101011000000101100010", -- 119                     mem        x1                     call      consx1x2
"0000000000000000000100101011", -- 120                     mar        d                      
"0000000000000000000101000111", -- 121                     s          mar                    
"0000000000000000000010100010", -- 122                     mem        car                    
"0000000000000000000101000110", -- 123                     car        mar                    
"0000000000000000000110000010", -- 124                     mem        x2                     
"0000000000000000000101000111", -- 125                     s          mar                    
"0000000000000000000101100010", -- 126                     mem        x1                     
"0000000000000000000101001100", -- 127                     x1         mar                    
"0000000000000000000010100010", -- 128                     mem        car                    
"1010001101011000000101100110", -- 129                     car        x1                     call      consx1x2
"0000000000000000000011101011", -- 130                     mar        e                      
"0000000000000000000000000000", -- 131                                                       
"0000000000000000000101000111", -- 132                     s          mar                    
"0000000000000000000010100010", -- 133                     mem        car                    
"0000000000000000000101000110", -- 134                     car        mar                    
"0000000000000000000010100010", -- 135                     mem        car                    
"0000000000000000000100000110", -- 136                     car        c                      
"0001010110001000000011010100", -- 137                     nilx       s                      jump      top-of-cycle
"0000000000000000000101001010", -- 138 rtn                 d          mar                    
"0000000000000000000010100010", -- 139                     mem        car                    
"0000000000000000000110000110", -- 140                     car        x2                     
"0000000000000000000101000111", -- 141                     s          mar                    
"0000000000000000000010100010", -- 142                     mem        car                    
"1010001101011000000101100110", -- 143                     car        x1                     call      consx1x2
"0000000000000000000011001011", -- 144                     mar        s                      
"0000000000000000000101001010", -- 145                     d          mar                    
"0000000000000000000100100010", -- 146                     mem        d                      
"0000000000000000000101001010", -- 147                     d          mar                    
"0000000000000000000010100010", -- 148                     mem        car                    
"0000000000000000000011100110", -- 149                     car        e                      
"0000000000000000000101001010", -- 150                     d          mar                    
"0000000000000000000100100010", -- 151                     mem        d                      
"0000000000000000000101001010", -- 152                     d          mar                    
"0000000000000000000010100010", -- 153                     mem        car                    
"0000000000000000000100000110", -- 154                     car        c                      
"0000000000000000000101001010", -- 155                     d          mar                    
"0001010110001000000100100010", -- 156                     mem        d                      jump      top-of-cycle
"0000000000000000000110001000", -- 157 dum                 e          x2                     
"1010001101011000000101110100", -- 158                     nilx       x1                     call      consx1x2
"0000000000000000000011101011", -- 159                     mar        e                      
"0000000000000000000101001001", -- 160                     c          mar                    
"0001010110001000000100000010", -- 161                     mem        c                      jump      top-of-cycle
"0000000000000000000110001010", -- 162 rap                 d          x2                     
"0000000000000000000101001001", -- 163                     c          mar                    
"1010001101011000000101100010", -- 164                     mem        x1                     call      consx1x2
"0000000000000000000110001011", -- 165                     mar        x2                     
"0000000000000000000101001000", -- 166                     e          mar                    
"1010001101011000000101100010", -- 167                     mem        x1                     call      consx1x2
"0000000000000000000110001011", -- 168                     mar        x2                     
"0000000000000000000101000111", -- 169                     s          mar                    
"0000000000000000000101100010", -- 170                     mem        x1                     
"0000000000000000000101001100", -- 171                     x1         mar                    
"1010001101011000000101100010", -- 172                     mem        x1                     call      consx1x2
"0000000000000000000100101011", -- 173                     mar        d                      
"0000000000000000000101000111", -- 174                     s          mar                    
"0000000000000000000010100010", -- 175                     mem        car                    
"0000000000000000000101000110", -- 176                     car        mar                    
"0000000000000000000011100010", -- 177                     mem        e                      
"0000000000000000000101000111", -- 178                     s          mar                    
"0000000000000000001000100010", -- 179                     mem        y2                     
"0000000000000000000101010010", -- 180                     y2         mar                    
"0000000000000000000010100010", -- 181                     mem        car                    
"0000000000000000001000100110", -- 182                     car        y2                     
"0000000000000000000101001000", -- 183                     e          mar                    
"0000000000000000000001000010", -- 184                     mem        arg                    
"0000000000000010100001100000", -- 185                                buf1       replcar     
"0000000000000000000000100100", -- 186                     buf1       bidir                  
"0000000000000000000101000111", -- 187                     s          mar                    
"0000000000000000000010100010", -- 188                     mem        car                    
"0000000000000000000101000110", -- 189                     car        mar                    
"0000000000000000000010100010", -- 190                     mem        car                    
"0000000000000000000100000110", -- 191                     car        c                      
"0001010110001000000011010100", -- 192                     nilx       s                      jump      top-of-cycle
"0000000000000000000110001010", -- 193 sel                 d          x2                     
"0000000000000000000101001001", -- 194                     c          mar                    
"0000000000000000000101100010", -- 195                     mem        x1                     
"0000000000000000000101001100", -- 196                     x1         mar                    
"0000000000000000000101100010", -- 197                     mem        x1                     
"0000000000000000000101001100", -- 198                     x1         mar                    
"1010001101011000000101100010", -- 199                     mem        x1                     call      consx1x2
"0000000000000000000100101011", -- 200                     mar        d                      
"0000000000000000000101000111", -- 201                     s          mar                    
"0000000000000000000010100010", -- 202                     mem        car                    
"0000000000000000000101000110", -- 203                     car        mar                    
"0000000000000000000001000010", -- 204                     mem        arg                    
"0000000000000000000101010101", -- 205                     true       mar                    
"0110101100101000000000000010", -- 206                     mem                               eq?       _18
"0000000000000000000101001001", -- 207                     c          mar                    
"0000000000000000000100000010", -- 208                     mem        c                      
"0000000000000000000101001001", -- 209                     c          mar                    
"0000000000000000000100000010", -- 210                     mem        c                      
"0000000000000000000101001001", -- 211                     c          mar                    
"0000000000000000000010100010", -- 212                     mem        car                    
"0110110110001000000100000110", -- 213                     car        c                      jump      _19
"0000000000000000000101001001", -- 214 _18                 c          mar                    
"0000000000000000000100000010", -- 215                     mem        c                      
"0000000000000000000101001001", -- 216                     c          mar                    
"0000000000000000000010100010", -- 217                     mem        car                    
"0000000000000000000100000110", -- 218                     car        c                      
"0000000000000000000101000111", -- 219 _19                 s          mar                    
"0001010110001000000011000010", -- 220                     mem        s                      jump      top-of-cycle
"0000000000000000000100001010", -- 221 join                d          c                      
"0000000000000000000101001001", -- 222                     c          mar                    
"0000000000000000000010100010", -- 223                     mem        car                    
"0000000000000000000100000110", -- 224                     car        c                      
"0000000000000000000101001010", -- 225                     d          mar                    
"0001010110001000000100100010", -- 226                     mem        d                      jump      top-of-cycle
"0000000000000000000101000111", -- 227 car                 s          mar                    
"0000000000000000000110000010", -- 228                     mem        x2                     
"0000000000000000000101000111", -- 229                     s          mar                    
"0000000000000000000010100010", -- 230                     mem        car                    
"0000000000000000000101000110", -- 231                     car        mar                    
"0000000000000000000010100010", -- 232                     mem        car                    
"1010001101011000000101100110", -- 233                     car        x1                     call      consx1x2
"0000000000000000000011001011", -- 234                     mar        s                      
"0000000000000000000101001001", -- 235                     c          mar                    
"0001010110001000000100000010", -- 236                     mem        c                      jump      top-of-cycle
"0000000000000000000101000111", -- 237 cdr                 s          mar                    
"0000000000000000000110000010", -- 238                     mem        x2                     
"0000000000000000000101000111", -- 239                     s          mar                    
"0000000000000000000010100010", -- 240                     mem        car                    
"0000000000000000000101000110", -- 241                     car        mar                    
"1010001101011000000101100010", -- 242                     mem        x1                     call      consx1x2
"0000000000000000000011001011", -- 243                     mar        s                      
"0000000000000000000101001001", -- 244                     c          mar                    
"0001010110001000000100000010", -- 245                     mem        c                      jump      top-of-cycle
"0000000000000000000101000111", -- 246 atom                s          mar                    
"0000000000000000000010100010", -- 247                     mem        car                    
"0000000000000000000101000110", -- 248                     car        mar                    
"0111110111000000000000000010", -- 249                     mem                               atom?     _24
"0111111000001000000101110110", -- 250                     false      x1                     jump      _25
"0000000000000000000101110101", -- 251 _24                 true       x1                     
"0000000000000000000101000111", -- 252 _25                 s          mar                    
"1010001101011000000110000010", -- 253                     mem        x2                     call      consx1x2
"0000000000000000000011001011", -- 254                     mar        s                      
"0000000000000000000101001001", -- 255                     c          mar                    
"0001010110001000000100000010", -- 256                     mem        c                      jump      top-of-cycle
"0000000000000000000101000111", -- 257 cons                s          mar                    
"0000000000000000000110000010", -- 258                     mem        x2                     
"0000000000000000000101001101", -- 259                     x2         mar                    
"0000000000000000000010100010", -- 260                     mem        car                    
"0000000000000000000110000110", -- 261                     car        x2                     
"0000000000000000000101000111", -- 262                     s          mar                    
"0000000000000000000010100010", -- 263                     mem        car                    
"1010001101011000000101100110", -- 264                     car        x1                     call      consx1x2
"0000000000000000000101101011", -- 265                     mar        x1                     
"0000000000000000000101000111", -- 266                     s          mar                    
"0000000000000000000110000010", -- 267                     mem        x2                     
"0000000000000000000101001101", -- 268                     x2         mar                    
"1010001101011000000110000010", -- 269                     mem        x2                     call      consx1x2
"0000000000000000000011001011", -- 270                     mar        s                      
"0000000000000000000101001001", -- 271                     c          mar                    
"0001010110001000000100000010", -- 272                     mem        c                      jump      top-of-cycle
"1001101101011000000000000000", -- 273 eq                                                    call      setup-alu-args
"1000101000101000000000000010", -- 274                     mem                               eq?       _28
"1000101010001000000101110110", -- 275                     false      x1                     jump      _29
"0000000000000000000101110101", -- 276 _28                 true       x1                     
"1001111111011000000000000000", -- 277 _29                                                   call      push-alu-result
"0001010110001000000000000000", -- 278                                                       jump      top-of-cycle
"1001101101011000000000000000", -- 279 add                                                   call      setup-alu-args
"1010011001011000100001100010", -- 280                     mem        buf1       add         call      alu-gc
"1001111111011000000101101011", -- 281                     mar        x1                     call      push-alu-result
"0001010110001000000000000000", -- 282                                                       jump      top-of-cycle
"1001101101011000000000000000", -- 283 sub                                                   call      setup-alu-args
"1010011001011000110001100010", -- 284                     mem        buf1       sub         call      alu-gc
"1001111111011000000101101011", -- 285                     mar        x1                     call      push-alu-result
"0001010110001000000000000000", -- 286                                                       jump      top-of-cycle
"1001101101011000000000000000", -- 287 mul                                                   call      setup-alu-args
"1010011001011001000001100010", -- 288                     mem        buf1       mul         call      alu-gc
"1001111111011000000101101011", -- 289                     mar        x1                     call      push-alu-result
"0001010110001000000000000000", -- 290                                                       jump      top-of-cycle
"1001101101011000000000000000", -- 291 div                                                   call      setup-alu-args
"1010011001011001010001100010", -- 292                     mem        buf1       div         call      alu-gc
"1001111111011000000101101011", -- 293                     mar        x1                     call      push-alu-result
"0001010110001000000000000000", -- 294                                                       jump      top-of-cycle
"1001101101011000000000000000", -- 295 rem                                                   call      setup-alu-args
"1010011001011001100001100010", -- 296                     mem        buf1       rem         call      alu-gc
"1001111111011000000101101011", -- 297                     mar        x1                     call      push-alu-result
"0001010110001000000000000000", -- 298                                                       jump      top-of-cycle
"1001101101011000000000000000", -- 299 leq                                                   call      setup-alu-args
"1001011100110000000000000010", -- 300                     mem                               leq?      _36
"1001011110001000000101110110", -- 301                     false      x1                     jump      _37
"0000000000000000000101110101", -- 302 _36                 true       x1                     
"1001111111011000000000000000", -- 303 _37                                                   call      push-alu-result
"0001010110001000000000000000", -- 304                                                       jump      top-of-cycle
"0000000000000000000101000111", -- 305 stop                s          mar                    
"0000000000000000000010100010", -- 306                     mem        car                    
"0000000000000000000011000110", -- 307                     car        s                      
"0000000000000000000101010011", -- 308                     num        mar                    
"0000101100001000000000100111", -- 309                     s          bidir                  jump      boot
"0000000000000000000101000111", -- 310 setup-alu-args      s          mar                    
"0000000000000000000101100010", -- 311                     mem        x1                     
"0000000000000000000101001100", -- 312                     x1         mar                    
"0000000000000000000010100010", -- 313                     mem        car                    
"0000000000000000000101000110", -- 314                     car        mar                    
"0000000000000000000001000010", -- 315                     mem        arg                    
"0000000000000000000101000111", -- 316                     s          mar                    
"0000000000000000000010100010", -- 317                     mem        car                    
"0000000001100000000101000110", -- 318                     car        mar                    return    
"0000000000000000000101000111", -- 319 push-alu-result     s          mar                    
"0000000000000000000110000010", -- 320                     mem        x2                     
"0000000000000000000101001101", -- 321                     x2         mar                    
"1010001101011000000110000010", -- 322                     mem        x2                     call      consx1x2
"0000000000000000000011001011", -- 323                     mar        s                      
"0000000000000000000101001001", -- 324                     c          mar                    
"0000000001100000000100000010", -- 325                     mem        c                      return    
"1010010100111000000000001110", -- 326 consx1x2            free                              num?      cons-gc
"0000000000000000000101001110", -- 327 _42                 free       mar                    
"0000000000000000000110100010", -- 328                     mem        free                   
"0000000001100000000000110111", -- 329                     cons       bidir                  return    
"1010100101011000000000000000", -- 330 cons-gc                                               call      gc
"1010001110001000000000000000", -- 331                                                       jump      _42
"1010100000111000000000001110", -- 332 alu-gc              free                              num?      _46
"0000000000000000000101001110", -- 333 _45                 free       mar                    
"0000000000000000000110100010", -- 334                     mem        free                   
"0000000001100000000000100100", -- 335                     buf1       bidir                  return    
"1010100101011000000000000000", -- 336 _46                                                   call      gc
"1010011010001000000000000000", -- 337                                                       jump      _45
"1011010101011100100111100111", -- 338 gc                  s          root       gc          call      mark-start
"1011010101011000000111101000", -- 339                     e          root                   call      mark-start
"1011010101011000000111101001", -- 340                     c          root                   call      mark-start
"1011010101011000000111101010", -- 341                     d          root                   call      mark-start
"1011010101011000000111101100", -- 342                     x1         root                   call      mark-start
"1011010101011000000111101101", -- 343                     x2         root                   call      mark-start
"1011010101011000000111110100", -- 344                     nilx       root                   call      mark-start
"1011010101011000000111110101", -- 345                     true       root                   call      mark-start
"1011010101011000000111110110", -- 346                     false      root                   call      mark-start
"0000000000000000000110110011", -- 347                     num        free                   
"0000000000000000000001010011", -- 348                     num        arg                    
"0000000000000000010010000000", -- 349                                buf2       dec         
"0000000000000000000101000101", -- 350                     buf2       mar                    
"1011010001001000000000000011", -- 351 _48                 arg                               nil?      _51
"1011000110011000000001000010", -- 352                     mem        arg                    mark?     _49
"0000000000000000000000101110", -- 353                     free       bidir                  
"1011001010001000000110101011", -- 354                     mar        free                   jump      _50
"0000000000000010010010000000", -- 355 _49                            buf2       clear-mark  
"0000000000000000000000100101", -- 356                     buf2       bidir                  
"0000000000000000000001001011", -- 357 _50                 mar        arg                    
"0000000000000000010010000000", -- 358                                buf2       dec         
"1010111110001000000101000101", -- 359                     buf2       mar                    jump      _48
"0000110000111000000000001110", -- 360 _51                 free                              num?      error
"0000000001100100000000000000", -- 361                                           running     return    
"0000000000000000000111010100", -- 362 mark-start          nilx       parent                 
"0000000000000000000101010000", -- 363 mark                root       mar                    
"1011100110011000000001000010", -- 364                     mem        arg                    mark?     backup
"0000000000000001110010000000", -- 365                                buf2       set-mark    
"1011100111000000000000100101", -- 366                     buf2       bidir                  atom?     backup
"0000000000000000001000001111", -- 367                     parent     y1                     
"0000000000000000001000110000", -- 368                     root       y2                     
"0000000000000011110000000000", -- 369                                           gcmark      
"1011010110001000000000100101", -- 370                     buf2       bidir                  jump      mark
"1011111001001000000101001111", -- 371 backup              parent     mar                    nil?      _56
"1011110010100000000001000010", -- 372                     mem        arg                    field?    _55
"0000000000000000001000010000", -- 373                     root       y1                     
"0000000000000000001000101111", -- 374                     parent     y2                     
"0000000000000011100000000000", -- 375                                           gcreset     
"1011100110001000000000100101", -- 376                     buf2       bidir                  jump      backup
"0000000000000000001000110000", -- 377 _55                 root       y2                     
"0000000000000011010000000000", -- 378                                           gcreverse   
"1011010110001000000000100101", -- 379                     buf2       bidir                  jump      mark
"0000000001100000000000000000", -- 380 _56                                                   return    
others => (others => '0'));

end package;
