% ================================================================= %
% This file contains a number of theorems to extend the theory      %
% of buses.  Particularly important are theorems permitting the     %
% equivalence of Width of buses to break down buses on which we     %
% do not induct, to subcomponents.                                  %
% ================================================================= %

new_theory `bus_theorems`;;

loadt `wordn`;;
load_all `bus`;;

% ================================================================= %
% Some useful higher order functions for buses.                     %
% ================================================================= %
let bus_map = new_recursive_definition
  false
  (theorem `bus` `bus_axiom`)
  `bus_map`
  "(bus_map (f:*->**) (Wire (b:*)) = Wire (f b)) /\
   (bus_map (f:*->**) (Bus b bus) = Bus (f b) (bus_map f bus))
  ";;
					 
let bus_map2 = new_recursive_definition
  false
  (theorem `bus` `bus_axiom`)
  `bus_map2`
  "(bus_map2 (f:*->**->***) (Wire (b:*)) (c:(**)bus) =
             Wire (f b (Hd_bus c))) /\
   (bus_map2 (f:*->**->***) (Bus b bus) c =
             Bus (f b (Hd_bus c)) (bus_map2 f bus (Tl_bus c)))
  ";;
					 
let bus_map_sum = new_recursive_definition
  false
  (theorem `bus` `bus_axiom`)
  `bus_map_sum`
  "(bus_map_sum (p:*->**) (c:**->**->**) (Wire (b:*)) = p b) /\
   (bus_map_sum p c (Bus (b:*) bus) = c (p b) (bus_map_sum p c bus))";;

% interleaving of 2 separate buses (used for in, inverse of in)     %
let shuffle = new_recursive_definition
  false
  (theorem `bus` `bus_axiom`)
  `shuffle`
  "(shuffle (Wire (b:*)) c  = Bus b (Wire (Hd_bus c))) /\
   (shuffle (Bus b bus) c =
         Bus b (Bus (Hd_bus c) (shuffle bus (Tl_bus c))))
  ";;

close_theory();;

let Wire_same_Width = prove_thm
(`Wire_same_Width`,
 "(Width bus = Width (Wire (b':*))) = (?b:**. bus = Wire b)",
 port[Width]
 THEN rt[Width_Wire]);;

let Bus_same_Width = prove_thm
(`Bus_same_Width`,
 "(Width (bus:(**)bus) = Width (Bus (b':*) bus'')) =
     (?b bus'. (Width bus' = Width bus'') /\ (bus = Bus b bus'))",
 port[Width]
 THEN STRIP_THM_THEN
          (\th.rt[th])
	  (SPEC "bus'':(*)bus" Width_non_zero)
 THEN rt[Width_Bus]);;

print_theory `-`;;
