-------------------------------------------- MODULE SCS ----------------------------------------------
(*********************************************************************************)
(* This specification expresses the actions/states that happens arround cruise   *)
(* control system. Speed increase/decrease, car braking, etc are some behaviours *)
(* that are somehow realated with a car with cruise control system.              *)
(*********************************************************************************)
                          
                          
                          (*##########################*)

EXTENDS Integers


                          (*##########################*)                             


VARIABLES acousticWarn, brakePedal, cc, desiredLimit, desiredSpeed, engine, frontCarGap, gasPedal, lever, sl, slWarn, speed, visualWarn


                          (*##########################*)

(*********************************************************************************)
(* Macro variables are established below.                                        *)
(*********************************************************************************)
critical       == 4
maxSpeed       == 4
minSpeed       == 2
none           == 1
safe           == 2
speedVariation == 1
stopped        == 1 
unsafe         == 3


                          (*##########################*)


(*********************************************************************************)
(* Anyone who wants to see if something is working/happening must enter below    *)
(* a predicate (which will be an invariant) where model will certainly fail, in  *) 
(* order to see the steps until the desired state.                               *) 
(*********************************************************************************)

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before speed       *) 
(* equals desiredLimit when the speed limit function is available.               *)
(*********************************************************************************)
\*End == ~(speed = desiredLimit /\ sl = "on")

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before engine      *) 
(* turns off. Note that engine's init state needs to be modified to "on" or TLC  *)
(* will always find this invariant to be false at the init state.                *)
(*********************************************************************************)
\*End == engine /= "off"

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before engine      *) 
(* turns off with speed limit function activated. Note that engine's init state  *)
(* needs to be modified to "on" or TLC will always find this invariant to be     *)
(* false at the init state.                                                      *)
(*********************************************************************************)
\*End == ~(engine = "off" /\ sl = "off")

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before speed       *) 
(* equals desired speed in order to check if, before that and after cruise       *)
(* control is activated, the lever turns, for example, position 3.               *)
(*********************************************************************************)
\*End == ~(cc = "on" /\ speed /= desiredSpeed /\ lever = 3)

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states where desiredLimit *)
(* is either 2, 3 or 4.                                                          *)
(*********************************************************************************)
\*End == ~(desiredLimit = 2) /\ ~(desiredLimit = 3) /\ ~(desiredLimit = 4)

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states where lever turns  *)
(* to 5, which turns the speed limit function off (it also turns it on but       *)
(* that's not what we want to check here.                                        *)
(*********************************************************************************)
\*End == ~(lever = 5 /\ sl = "off")

End == 1 = 1

                          (*##########################*)
                          
(*********************************************************************************)                          
(*SCS1 (NAO ESTA COMPLETAMENTE DIREITO                                           *)
(*********************************************************************************)
SCS1 == (engine = "off") => (desiredSpeed = none)  

(*********************************************************************************)
(*SCS2 (NAO ESTA COMPLETAMENTE DIREITO)                                          *)
(*********************************************************************************)
SCS2 == (lever = 1) => \/ desiredSpeed = none
                       \/ speed < desiredSpeed
                       \/ speed > desiredSpeed
                       \/ speed = desiredSpeed       
                    
(*********************************************************************************)
(* SCS3 - Assuming that below 20km/h is equal to stopped)                        *)
(*********************************************************************************)
SCS3 == (speed = stopped /\ desiredSpeed = none) => cc = "off" 

(*********************************************************************************)
(* SCSA - SCSA gathers SCSs 4, 5, 7 and 8, assuming that the lever doesn't have  *)
(* resistance levels and that pushing the lever to 2 only increases the desired  *)
(* speed, under normal conditions (with speed limit function off).               *) 
(*********************************************************************************)
\*NOT WORKING
\*SCSA == (lever = 2 /\ sl = "off") => (desiredSpeed = desiredSpeed + speedVariation)  

(*********************************************************************************)
(* SCSB - SCSB gathers SCSs 6, 9 and 10, assuming that the lever doesn't have    *)
(* resistance levels and that pushing the lever to 3 only decreases the desired  *)
(* speed, under normal conditions (with speed limit function off).               *) 
(*********************************************************************************)
\*NOT WORKING
\*SCSB == (lever = 3 /\ sl = "off") => (desiredSpeed = desiredSpeed - speedVariation)
 
(*********************************************************************************)
(* SCS11 (DEVIAMOS USAR O SPEED ANTERIOR E NAO O DO MESMO ESTADO DO desired speed)*)
(*MAS FUNCIONA BEM                                                               *)
(*********************************************************************************)
SCS11 == /\ lever = 2 \/ lever = 3 
         /\ cc = "off" 
         /\ sl = "off" 
         => (desiredSpeed = speed)
         
\* isto é igual ao que está em cima certo ???
\*SCS11 == ((lever = 2 \/ lever = 3) /\ cc = "off" /\ sl = "off") => (desiredSpeed = speed)
         
(*********************************************************************************)
(* SCS12                                                                          *)
(*********************************************************************************)
SCS12 == lever = 4 => cc = "off"

(*********************************************************************************)
(* SCS13                                                                             *)
(*********************************************************************************)
SCS13 == lever = 1 => cc = "on"

(*********************************************************************************)
(* SCS14   está a acontecer, mas como provar?? tinhamos que pegar em todos os estados seguintes até speed = desiredspeed *)
(*********************************************************************************)


(*********************************************************************************)
(* SCS15                                                                         *)
(*********************************************************************************)
SCS15 == (cc = "on" /\ gasPedal = "pressed") => speed > desiredSpeed 

(*********************************************************************************)
(* SCS16                                                                         *)
(*********************************************************************************)
SCS16 == brakePedal = "pressed" => cc = "off"

(*********************************************************************************)
(* SCS17                                                                         *)
(*********************************************************************************)
SCS17 == lever = 4 => cc = "off"

(*********************************************************************************)
(* SCS18 - Assuming cruise control only gets activated when lever is pulled to 1 *) 
(* SCS18 É O MESMO PROB QUE A SCS14                                              *)
(*********************************************************************************)

(*********************************************************************************)
(* SCS19 WE HAVE TO ASSURE SPECS SCS1 E SCS12, THERE IS NO REQUIREMENT HERE      *)
(*********************************************************************************)

(*********************************************************************************)
(* SCS25 - Assuming that visual warning is activated if the actual distance is   *)
(* either unsafe or critical.                                                    *)
(*********************************************************************************)
SCS25 == (frontCarGap = unsafe \/ frontCarGap = critical) => visualWarn = "on"

(*********************************************************************************)
(* SCS26 - Assuming that acoustic warning is activated if the actual distance is *)
(* critical.                                                                     *)
(*********************************************************************************)
SCS26 == frontCarGap = critical => acousticWarn = "on"

(*********************************************************************************)
(* SCS29 - (NAO ESTA COMPLETAMENTO DIREITO)                                                                      *)
(*********************************************************************************)
SCS29 == (lever = 5 /\ sl = "on") => sl = "on" 

(*********************************************************************************)
(* SCS30                                                                         *)
(*********************************************************************************)
\*SCS30 == /\ sl = "on" => slWarn = "on"
\*         /\ sl = "off" => slWarn = "off"
(*********************************************************************************)
(* SCS31 (NAO ESTA COMPLETAMENTO DIREITO)                                        *)
(*********************************************************************************)
SCS31 == /\ ((lever = 2) /\ (sl = "on")) => speed < desiredLimit
         /\ ((lever = 3) /\ (sl = "on")) => speed <= desiredLimit  

(*********************************************************************************)
(* SCS32                                                                         *)
(*********************************************************************************)
SCS32 == sl = "on" => speed <= desiredLimit

(*********************************************************************************)
(* SCS35 (NAO ESTA COMPLETAMENTO DIREITO)                                        *)
(*********************************************************************************)
SCS35 == /\ lever = 4 => sl = "off"
         /\ (lever = 5 /\ sl = "off") => sl = "off"
         
(*********************************************************************************)
(*                                                                               *)
(*********************************************************************************)

(*********************************************************************************)
(*                                                                               *)
(*********************************************************************************)


SCSsOK == /\ SCS1
          /\ SCS2
          /\ SCS3
          \*/\ SCSA
          \*/\ SCSB
          /\ SCS11
          /\ SCS12
          /\ SCS13
          \*/\ scs14
          /\ SCS15
          /\ SCS16
          /\ SCS17
          /\ SCS25
          /\ SCS26
          /\ SCS29
          \*/\ SCS30
          /\ SCS31
          /\ SCS32
          \*/\ SCS33
          \*/\ SCS34
          /\ SCS35
          
          
                          (*##########################*)


(*********************************************************************************)
(* This predicate is an invariant and remains true across all of the states.     *)
(*********************************************************************************)
TypeOK == /\ acousticWarn \in {"off", "on"}
          /\ brakePedal   \in {"pressed", "unpressed"}
          /\ cc           \in {"off", "on"}
          /\ desiredLimit \in none..maxSpeed \*2-slow 3-medium 4-fast
          /\ desiredSpeed \in none..maxSpeed \*1-none 2-slow 3-medium 4-fast
          /\ engine       \in {"off", "on"}
          /\ frontCarGap  \in none..critical \*1-none 2-safe 3-unsafe 4-critical
          /\ gasPedal     \in {"pressed", "unpressed"}
          /\ lever        \in 0..5
          /\ sl           \in {"off", "on"}
          /\ slWarn       \in {"off", "on"}
          /\ speed        \in stopped..maxSpeed \*1-stopped 2-slow 3-medium 4-fast
          /\ visualWarn   \in {"off", "on"}


                          (*##########################*)


(*********************************************************************************)
(* The speed limit is either - on and respected - or - off.                      *)
(*********************************************************************************)
SpeedUnderDesiredLimit == \/ speed <= desiredLimit /\ sl = "on"
                          \/ sl = "off"
                          
\*SpeedEqualsDesiredSpeed == (cc = "on" /\ speed < desiredSpeed) ~> (cc = "on" /\ speed = desiredSpeed)
\* e se ele trava ou desativa cruise control ?? o Q deixa de fazer sentido ! 

(*********************************************************************************)
(* This predicate is another invariant and remains true across all of the        *)
(* states. It's different than the other above because it assures properties not *)
(* related with variables types.     \se calhar nao vai ser usado pq é a SCSS    *)
(*********************************************************************************)
PropertiesOK == /\ SpeedUnderDesiredLimit 
                \*/\ SpeedEqualsDesiredSpeed\* quando cc = on e desiredspeed /= speed, a speed terá que igualar a desiredspeed  
                
           
                          (*##########################*)                   

           
(*********************************************************************************)
(* Defines initial state.                                                        *)
(*********************************************************************************)
Init == /\ acousticWarn = "off"
        /\ brakePedal   = "unpressed"
        /\ cc           = "off"
        /\ desiredLimit = none
        /\ desiredSpeed = none
        /\ engine       = "off"
        /\ frontCarGap  = none
        /\ gasPedal     = "unpressed"
        /\ lever        = 0
        /\ sl           = "off"
        /\ slWarn       = "off"
        /\ speed        = stopped
        /\ visualWarn   = "off"
    
    
                          (*##########################*)    
    
      
(*********************************************************************************)
(* Puts speed with desiredSpeed value instantly (but we want to make it gradual).*)
(*********************************************************************************)
ApproachesDesiredSpeed == IF speed < desiredSpeed
                            THEN speed' = speed + 1
                            ELSE speed' = speed - 1

(*********************************************************************************)
(* Predicate that is continuously called since when the lever is turned to 1     *)
(* untill speed equals desired speed.                                            *)  
(*********************************************************************************)
EqualsDesiredSpeed == /\ brakePedal    = "unpressed"
                      /\ cc            = "on"
                      /\ desiredSpeed  /= none
                      /\ engine        = "on"
                      /\ gasPedal      = "unpressed"
                      /\ lever         = 0
                      /\ speed         /= desiredSpeed
                      /\ acousticWarn' = acousticWarn
                      /\ brakePedal'   = brakePedal
                      /\ cc'           = cc 
                      /\ desiredLimit' = desiredLimit
                      /\ desiredSpeed' = desiredSpeed
                      /\ engine'       = engine
                      /\ frontCarGap'  = frontCarGap
                      /\ gasPedal'     = gasPedal
                      /\ lever'        = lever
                      /\ sl'           = sl
                      /\ slWarn'       = slWarn
                      /\ visualWarn'   = visualWarn
                      /\ ApproachesDesiredSpeed
                    
(*********************************************************************************)
(* The car brakes and reduces current speed (in one unit).                       *)
(*********************************************************************************)             
Brake == /\ engine        = "on"
         /\ gasPedal      = "unpressed"
         /\ lever         = 0
         /\ speed         > stopped
         /\ acousticWarn' = acousticWarn
         /\ brakePedal'   = "pressed"
         /\ cc'           = "off"
         /\ desiredLimit' = desiredLimit
         /\ desiredSpeed' = desiredSpeed
         /\ engine'       = engine
         /\ frontCarGap'  = frontCarGap
         /\ gasPedal'     = gasPedal
         /\ lever'        = lever   
         /\ sl'           = sl
         /\ slWarn'       = slWarn
         /\ speed'        = speed - speedVariation
         /\ visualWarn'   = visualWarn   

(*********************************************************************************)
(* Increases front car gap from critical to unsafe or from unsafe to safe,       *)
(* deactivating the corresponding warnings.                                      *)
(*********************************************************************************)
IncreaseFrontCarGap == /\ cc            = "on"
                       /\ engine        = "on"
                       /\ frontCarGap   > safe
                       /\ gasPedal      = "unpressed"
                       /\ lever         = 0 
                       /\ IF frontCarGap = 3
                            THEN /\ acousticWarn' = "off"
                                 /\ visualWarn'   = "off" 
                            ELSE /\ acousticWarn' = "off"
                                 /\ visualWarn'   = "on"  
                       /\ brakePedal'   = brakePedal
                       /\ cc'           = cc
                       /\ desiredLimit' = desiredLimit
                       /\ desiredSpeed' = desiredSpeed
                       /\ engine'       = engine
                       /\ frontCarGap'  = frontCarGap - 1
                       /\ gasPedal'     = gasPedal
                       /\ lever'        = lever
                       /\ sl'           = sl
                       /\ slWarn'       = slWarn
                       /\ speed'        = speed 

(*********************************************************************************)
(* Decreases front car gap from safe to unsafe or from unsafe to critical,       *)
(* activating the corresponding warnings.                                        *)
(*********************************************************************************)
DecreaseFrontCarGap == /\ cc            = "on"
                       /\ engine        = "on"
                       /\ frontCarGap   < critical
                       /\ lever         = 0 
                       /\ IF frontCarGap = 3
                            THEN /\ acousticWarn' = "on"
                                 /\ visualWarn'   = "on" 
                            ELSE IF frontCarGap = 2
                                   THEN /\ acousticWarn' = "off"
                                        /\ visualWarn'   = "on"
                                   ELSE /\ acousticWarn' = "off"
                                        /\ visualWarn'   = "off"  
                       /\ brakePedal'   = brakePedal
                       /\ cc'           = cc
                       /\ desiredLimit' = desiredLimit
                       /\ desiredSpeed' = desiredSpeed
                       /\ engine'       = engine
                       /\ frontCarGap'  = frontCarGap + 1
                       /\ gasPedal'     = gasPedal
                       /\ lever'        = lever
                       /\ sl'           = sl
                       /\ slWarn'       = slWarn
                       /\ speed'        = speed

(*********************************************************************************)
(* Increases current speed (in one unit) until the maximum speed is achieved or  *)
(* until speed limit is reached as long as speed limit function is activated.    *)
(*********************************************************************************)
IncreaseSpeed == \/ /\ brakePedal    = "unpressed"
                    /\ cc            = "off"
                    /\ engine        = "on"
                    /\ lever         = 0
                    /\ speed         < maxSpeed
                    /\ sl            = "off"
                    /\ acousticWarn' = acousticWarn
                    /\ brakePedal'   = brakePedal
                    /\ cc'           = cc
                    /\ desiredSpeed' = desiredSpeed
                    /\ desiredLimit' = desiredLimit 
                    /\ engine'       = engine
                    /\ frontCarGap'  = frontCarGap
                    /\ gasPedal'     = "pressed"
                    /\ lever'        = lever  
                    /\ sl'           = sl
                    /\ slWarn'       = slWarn
                    /\ speed'        = speed + speedVariation
                    /\ visualWarn'   = visualWarn  
                 \/ /\ brakePedal    = "unpressed"
                    /\ cc            = "off"
                    /\ engine        = "on"
                    /\ lever         = 0
                    /\ sl            = "on"
                    /\ speed         < desiredLimit
                    /\ acousticWarn' = acousticWarn
                    /\ brakePedal'   = brakePedal
                    /\ cc'           = cc
                    /\ desiredLimit' = desiredLimit
                    /\ desiredSpeed' = desiredSpeed 
                    /\ engine'       = engine
                    /\ frontCarGap'  = frontCarGap
                    /\ gasPedal'     = "pressed"
                    /\ lever'        = lever   
                    /\ sl'           = sl
                    /\ slWarn'       = slWarn
                    /\ speed'        = speed + speedVariation
                    /\ visualWarn'   = visualWarn
                 \/ /\ brakePedal    = "unpressed"
                    /\ cc            = "on"
                    /\ engine        = "on"
                    /\ lever         = 0
                    /\ speed         < maxSpeed
                    /\ speed         >= desiredSpeed
                    /\ sl            = "off"
                    /\ acousticWarn' = acousticWarn
                    /\ brakePedal'   = brakePedal
                    /\ cc'           = cc
                    /\ desiredSpeed' = desiredSpeed
                    /\ desiredLimit' = desiredLimit 
                    /\ engine'       = engine
                    /\ frontCarGap'  = frontCarGap
                    /\ gasPedal'     = "pressed"
                    /\ lever'        = lever  
                    /\ sl'           = sl
                    /\ slWarn'       = slWarn
                    /\ speed'        = speed + speedVariation
                    /\ visualWarn'   = visualWarn
                                    
(*********************************************************************************)
(* Decreases current speed (in one unit).                                        *)
(*********************************************************************************)                 
DecreaseSpeed == /\ brakePedal    = "unpressed"
                 /\ cc            = "off"
                 /\ engine        = "on"
                 /\ gasPedal      = "unpressed"
                 /\ lever         = 0
                 /\ speed         > stopped
                 /\ acousticWarn' = acousticWarn
                 /\ brakePedal'   = brakePedal
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit
                 /\ desiredSpeed' = desiredSpeed
                 /\ engine'       = engine
                 /\ frontCarGap'  = frontCarGap
                 /\ gasPedal'     = gasPedal
                 /\ lever'        = lever   
                 /\ sl'           = sl
                 /\ slWarn'       = slWarn
                 /\ speed'        = speed - speedVariation
                 /\ visualWarn'   = visualWarn 

(*********************************************************************************)
(* Releases gas pedal right after speed increasement unless it keeps increasing  *)
(* speed.                                                                        *)
(*********************************************************************************)
ReleaseGasPedal == /\ brakePedal    = "unpressed"
                   /\ engine        = "on"
                   /\ gasPedal      = "pressed"
                   /\ lever         = 0
                   /\ acousticWarn' = acousticWarn
                   /\ brakePedal'   = brakePedal
                   /\ cc'           = cc
                   /\ desiredLimit' = desiredLimit
                   /\ desiredSpeed' = desiredSpeed
                   /\ engine'       = engine
                   /\ frontCarGap'  = frontCarGap
                   /\ gasPedal'     = "unpressed"
                   /\ lever'        = lever   
                   /\ sl'           = sl
                   /\ slWarn'       = slWarn
                   /\ speed'        = speed
                   /\ visualWarn'   = visualWarn 

(*********************************************************************************)
(* Releases brake pedal right after being pressed unless it keeps breaking.      *)
(*********************************************************************************)
ReleaseBrakePedal == /\ brakePedal    = "pressed"
                     /\ engine        = "on"
                     /\ gasPedal      = "unpressed"
                     /\ lever         = 0
                     /\ acousticWarn' = acousticWarn
                     /\ brakePedal'   = "unpressed"
                     /\ cc'           = cc
                     /\ desiredLimit' = desiredLimit
                     /\ desiredSpeed' = desiredSpeed
                     /\ engine'       = engine
                     /\ frontCarGap'  = frontCarGap
                     /\ gasPedal'     = gasPedal
                     /\ lever'        = lever   
                     /\ sl'           = sl
                     /\ slWarn'       = slWarn
                     /\ speed'        = speed
                     /\ visualWarn'   = visualWarn

(*********************************************************************************)
(* Nothing changes.                                                              *)
(*********************************************************************************)                        
NothingChanges == /\ brakePedal    = "unpressed"
                  /\ gasPedal      = "unpressed"
                  /\ lever         = 0
                  /\ acousticWarn' = acousticWarn
                  /\ brakePedal'   = brakePedal
                  /\ cc'           = cc
                  /\ desiredLimit' = desiredLimit
                  /\ desiredSpeed' = desiredSpeed
                  /\ engine'       = engine
                  /\ frontCarGap'  = frontCarGap
                  /\ gasPedal'     = gasPedal
                  /\ lever'        = lever   
                  /\ sl'           = sl
                  /\ slWarn'       = slWarn
                  /\ speed'        = speed
                  /\ visualWarn'   = visualWarn
                  
(*********************************************************************************)
(* Lever goes to it's neutral state after being manipulated.                     *)
(*********************************************************************************)         
TurnLever0 == /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         /= 0
              /\ acousticWarn' = acousticWarn
              /\ brakePedal'   = brakePedal 
              /\ cc'           = cc
              /\ desiredLimit' = desiredLimit
              /\ desiredSpeed' = desiredSpeed
              /\ engine'       = engine
              /\ frontCarGap'  = frontCarGap
              /\ gasPedal'     = gasPedal
              /\ lever'        = 0   
              /\ sl'           = sl
              /\ slWarn'       = slWarn
              /\ speed'        = speed
              /\ visualWarn'   = visualWarn
          
(*********************************************************************************)
(* Activates cruise control.                                                     *)
(*********************************************************************************)            
TurnLever1 == /\ cc              = "off"
              /\ brakePedal      = "unpressed"
              /\ engine          = "on"
              /\ gasPedal        = "unpressed"
              /\ lever           = 0
              /\ sl              = "off"
              /\ \/ desiredSpeed > none
                 \/ speed        > stopped
              /\ acousticWarn'   = "off"
              /\ brakePedal'     = brakePedal
              /\ cc'             = "on"
              /\ desiredLimit'   = desiredLimit
              /\ engine'         = engine
              /\ frontCarGap'    = safe
              /\ gasPedal'       = gasPedal
              /\ lever'          = 1   
              /\ sl'             = sl
              /\ slWarn'         = slWarn
              /\ speed'          = speed
              /\ visualWarn'     = "off"
              /\ IF desiredSpeed = none 
                   THEN desiredSpeed' = speed
                   ELSE /\ desiredSpeed' = desiredSpeed 
                        /\ ApproachesDesiredSpeed
              
(*********************************************************************************)
(* Increases desired speed, desired limit or equals desired speed to current     *)
(* speed depending on the cc, sl, or cc and sl states.                           *)
(*********************************************************************************)
TurnLever2 == /\ brakePedal    = "unpressed"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ acousticWarn' = acousticWarn
              /\ brakePedal'   = brakePedal 
              /\ cc'           = cc
              /\ engine'       = engine
              /\ frontCarGap'  = frontCarGap
              /\ gasPedal'     = gasPedal
              /\ lever'        = 2   
              /\ sl'           = sl
              /\ slWarn'       = slWarn
              /\ speed'        = speed
              /\ visualWarn'   = visualWarn
              /\ \/ /\ cc            = "on"
                    /\ desiredSpeed  < maxSpeed
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = desiredSpeed + speedVariation
                 \/ /\ cc            = "off"
                    /\ desiredLimit  < maxSpeed
                    /\ sl            = "on"
                    /\ desiredLimit' = desiredLimit + speedVariation
                    /\ desiredSpeed' = desiredSpeed
                 \/ /\ cc            = "off"
                    /\ speed         > stopped 
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = speed
                    

(*********************************************************************************)
(* Decreases desired speed, desired limit or equals desired speed to current     *)
(* speed depending on the cc, sl, or cc and sl states.                           *)
(*********************************************************************************)
TurnLever3 == /\ brakePedal    = "unpressed"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ acousticWarn' = acousticWarn
              /\ brakePedal'   = brakePedal 
              /\ cc'           = cc
              /\ engine'       = engine
              /\ frontCarGap'  = frontCarGap
              /\ gasPedal'     = gasPedal
              /\ lever'        = 3   
              /\ sl'           = sl
              /\ slWarn'       = slWarn
              /\ speed'        = speed
              /\ visualWarn'   = visualWarn
              /\ \/ /\ cc            = "on"
                    /\ desiredSpeed  > minSpeed
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = desiredSpeed - speedVariation
                 \/ /\ cc            = "off"
                    /\ desiredLimit  > minSpeed
                    /\ sl            = "on"
                    /\ desiredLimit - speedVariation >= speed
                    /\ desiredLimit' = desiredLimit - speedVariation
                    /\ desiredSpeed' = desiredSpeed
                 \/ /\ cc            = "off"
                    /\ speed         > stopped 
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = speed

\* MAIS SIMPLES EM CIMA, NAO ?? CONFIRMAR
(*TurnLever3 == \//\ brakePedal    = "unpressed"  
                 /\ desiredSpeed  > minSpeed
                 /\ engine        = "on"
                 /\ gasPedal      = "unpressed"
                 /\ lever         = 0
                 /\ sl            = "off"
                 /\ brakePedal'   = brakePedal
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit 
                 /\ desiredSpeed' = desiredSpeed - speedVariation
                 /\ engine'       = engine
                 /\ gasPedal'     = gasPedal
                 /\ lever'        = 3   
                 /\ sl'           = sl
                 /\ speed'        = speed
              \/ /\ brakePedal    = "unpressed" 
                 /\ desiredLimit  > minSpeed
                 /\ engine        = "on"
                 /\ speed         < desiredLimit
                 /\ lever         = 0
                 /\ sl            = "on"
                 /\ brakePedal'   = brakePedal 
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit - speedVariation
                 /\ desiredSpeed' = desiredSpeed
                 /\ engine'       = engine
                 /\ gasPedal'     = gasPedal
                 /\ lever'        = 3   
                 /\ sl'           = sl
                 /\ speed'        = speed*)
                               
(*********************************************************************************)
(* Deactivates cruise control or speed limit function.                           *)
(*********************************************************************************)
TurnLever4 == /\ brakePedal    = "unpressed"
              /\ \/ cc            = "on"
                 \/ sl            = "on"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ brakePedal'   = brakePedal
              /\ acousticWarn' = "off"
              /\ cc'           = "off"
              /\ desiredLimit' = desiredLimit
              /\ desiredSpeed' = desiredSpeed
              /\ engine'       = engine
              /\ frontCarGap'  = none
              /\ gasPedal'     = gasPedal
              /\ lever'        = 4   
              /\ sl'           = "off"
              /\ slWarn'       = "off"
              /\ speed'        = speed
              /\ visualWarn'   = "off"

(*********************************************************************************)
(* Activates or deactivates speed limit depending on the actual state.           *)
(*********************************************************************************)
TurnLever5 == /\ brakePedal    = "unpressed"
              /\ cc            = "off"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ speed         <= desiredLimit
              /\ acousticWarn' = acousticWarn
              /\ brakePedal'   = brakePedal
              /\ cc'           = cc
              /\ desiredLimit' = desiredLimit
              /\ desiredSpeed' = desiredSpeed
              /\ engine'       = engine
              /\ frontCarGap'  = frontCarGap
              /\ gasPedal'     = gasPedal
              /\ lever'        = 5
              /\ \/ /\ sl      = "on"
                    /\ sl'     = "off"
                    /\ slWarn' = "off"
                 \/ /\ sl      = "off"
                    /\ sl'     = "on"
                    /\ slWarn' = "on" 
              /\ speed'        = speed
              /\ visualWarn'   = visualWarn

(*********************************************************************************)
(* Turn engine off.                                                              *)
(*********************************************************************************)
TurnEngineOff == /\ brakePedal    = "unpressed"
                 /\ engine        = "on"
                 /\ gasPedal      = "unpressed"
                 /\ speed         = stopped
                 /\ acousticWarn' = "off"
                 /\ brakePedal'   = brakePedal
                 /\ cc'           = "off"
                 /\ desiredLimit' = none
                 /\ desiredSpeed' = none
                 /\ engine'       = "off"
                 /\ frontCarGap'  = none
                 /\ gasPedal'     = gasPedal
                 /\ lever'        = 0
                 /\ sl'           = "off"
                 /\ slWarn'       = "off"
                 /\ speed'        = stopped
                 /\ visualWarn'   = visualWarn

(*********************************************************************************)
(* Turn engine on.                                                               *)
(*********************************************************************************)
TurnEngineOn == /\ brakePedal    = "unpressed"
                /\ cc            = "off"
                /\ engine        = "off"
                /\ gasPedal      = "unpressed"
                /\ lever         = 0
                /\ sl            = "off"
                /\ acousticWarn' = acousticWarn
                /\ brakePedal'   = brakePedal
                /\ cc'           = cc
                /\ desiredLimit' = none
                /\ desiredSpeed' = desiredSpeed
                /\ engine'       = "on"
                /\ frontCarGap'  = frontCarGap
                /\ gasPedal'     = gasPedal
                /\ lever'        = 0
                /\ sl'           = sl
                /\ slWarn'       = slWarn
                /\ speed'        = 1
                /\ visualWarn'   = visualWarn 


                          (*##########################*)


(*********************************************************************************)
(* Defines the next state.                                                       *)
(*********************************************************************************)                        
Next == \/ Brake
        \/ DecreaseSpeed
        \/ DecreaseFrontCarGap
        \/ EqualsDesiredSpeed
        \/ IncreaseSpeed
        \/ IncreaseFrontCarGap
        \/ NothingChanges
        \/ ReleaseGasPedal
        \/ ReleaseBrakePedal
        \/ TurnLever0
        \/ TurnLever1
        \/ TurnLever2
        \/ TurnLever3 
        \/ TurnLever4
        \/ TurnLever5
        \/ TurnEngineOff
        \/ TurnEngineOn


                          (*##########################*)
                          
                          
(*********************************************************************************)
(* SCS-1 -> not hap                                                              *)
(* SCS-2 -> a desired speed vai ter que ter um valor stopped, por exemplo        *)
(* SCS-3 -> not hap                                                              *) 
(* SCS-4 -> not hap pq muito especificado, manter?                               *)
(* SCS-5 -> not hap pq muito especificado, manter?                               *)
(* SCS-6 -> not hap pq muito especificado, manter?                               *)
(* SCS-7 -> not hap pq muito especificado, manter?                               *)
(* SCS-8 -> not hap pq muito especificado, manter?                               *)
(* SCS-9 -> not hap pq muito especificado, manter?                               *)
(* SCS-10 -> not hap pq muito especificado, manter?                              *)
(* SCS-11 -> está a mudar a desired speed para cima ou para baixo, nao está a    *)
(* igualar a current speed                                                       *)
(* SCS-12 -> check!                                                              *)
(* SCS-13 -> check!                                                              *) 
(* SCS-14 -> verificar e check! COM PROBLEMA                                     *)
(* SCS-15 -> not hap                                                             *)
(* SCS-16 -> check!                                                              *)
(* SCS-17 -> check!                                                              *)
(* SCS-18 -> (CC ACTIVATES WHEN LEVER GOES UP OR DOWN??!!)                       *)
(* SCS-19 -> not hap porque scs1 not hap                                         *)
(* SCS-20 -> not hap, think its easy to do                                       *)
(* SCS-21 -> not hap, think its easy to do if despecified                        *)
(* SCS-22 -> not hap, think its easy to do if despecified                        *)
(* SCS-23 -> not hap                                                             *)
(* SCS-24 -> not hap                                                             *)
(* SCS-25 -> check!                                                              *)
(* SCS-26 -> check!                                                              *)
(* SCS-27 -> not hap, think its easy to do if despecified                        *)
(* SCS-28 -> not hap                                                             *)
(* SCS-29 -> verificar e check!                                                  *)
(* SCS-30 -> not hap, think its easy to do   MUITO FÁCIL MUITO!!                 *)
(* SCS-31 -> verificar e check!                                                  *)
(* SCS-32 -> verificar e check!                                                  *)
(* SCS-33 -> won't be specified.                                                 *)
(* SCS-34 -> won't be specified.                                                 *)
(* SCS-35 -> NOT HAP IMPORTANT                                                   *)
(* SCS-36 -> won't be specified.                                                 *)
(* SCS-37 -> won't be specified.                                                 *)
(* SCS-38 -> won't be specified.                                                 *)
(* SCS-39 -> won't be specified.                                                 *)
(* SCS-40 -> won't be specified.                                                 *)
(* SCS-41 -> won't be specified.                                                 *)
(* SCS-42 -> won't be specified.                                                 *)
(* SCS-43 -> won't be specified.                                                 *)
(*********************************************************************************)


                          (*##########################*)

\* cc can be turned on when current speed is 1 (stopped)

\* acho que seria decente colocar a speed a tender para a desiredSpeed (enquanto
\*   não ficassem igualadas, fazia-se o predicado EqualsDesiredSpeed) nao tenho 
\*   a certeza se isto já está a acontecer visto que ativando o cruise control 
\*   apenas deveria ser possivel os proximos passos serem TurnLever0 (alavanca ir
\*   para o estado neutro) e EqualsDiseredSpeed até speed = desiredSpeed; enquanto
\*   desiredspeed /= speed, turnlever1,2,3,4, nothingchanges, break, etc, e esses
\*   passos todos nao deveriam acontecer -> até agora nao detetei nada que estivesse mal

\* 

===========================================================================================================
\* Modification History
\* Last modified Fri Jan 03 18:42:42 WET 2020 by ricardo