;The agents are required to understand what it the "true-class" of the world. It may either be "X_1" or "X_2". Notably, X_1 = \neg X_2.
; They are making an experiment in order to find which one is it. The experiment has two possible outcomes: D_1 and D_2. Notably, P(D_1|X_i) + P(D_2|X_i) = 1 for all X_i.
; All the agents know which is the correlation between X_2 and D_1, D_2. In particular, P(D_1 | X_2) is expressed by d_1_given_x_2.
; However, the agents do not agree and may be mistaken about the correlation of X_1 and D_1 and D_2. In particular, there exists a true value for P(D_1 | X_1) which is selected as
; a parameter, i.e. d_1_given_x_1. And, then every agent may assign a different value to this link, i.e. biased-d_1_given_x_1.

extensions[nw]
turtles-own [player-belief biased-d_1_given_x_1 new-biased-d_1_given_x_1 number-of-influencers personal-evidence-piece agent-epsilon
  personal-successes-drawn ]

globals[evidence final-result d_1_given_x_2 percentage-of-correct-scientists]

;Globals and and individual variables will be explained when met inside the model.

to setup
  ca
  reset-ticks
  set d_1_given_x_2 1 - d_1_given_x_1
  set evidence [] ; the vector of all the pieces of evidence that have been drawn from the beginning. It does not have any use in the model, it serves as a monitor.
  nw:generate-random turtles links number-of-agents connection-probability [
    set player-belief 0.5 ; probability that each agent assigns to the possibility of X_1 being the true class of the world. Notably, X_1 is the true class of the world.
    if initial-distance-diag-value + d_1_given_x_1 > 1 [set initial-distance-diag-value 1 - d_1_given_x_1]
    if d_1_given_x_1 - initial-distance-diag-value < 0 [set initial-distance-diag-value  d_1_given_x_1]
    set biased-d_1_given_x_1 ifelse-value random-float 1 > 0.5 [d_1_given_x_1 + random-float initial-distance-diag-value ][ d_1_given_x_1 - random-float initial-distance-diag-value]
    ; The value that agent i assigns to D_1 | X_1. If we have wisdom of the crowd we want to make sure that the mean of the agents is around the real value.
    ; For this reason we need also to make sure that the superior and the inferior limit go below or above 1 and 0.
    set agent-epsilon epsilon ;Each agent has the same epsilon.
  ]
end

to go
  ;The Go procedure is composed of three parts. 1) Agents draw evidence and update their factual Beliefs. 2) Agents interact and update their Diagnostic Values.
  ;3) The program checks if the run is stable. If it is it generates results and then stops.
  draw-evidence-and-update-belief
  influence-each-other
  tick
  if stable [
    generate-result
    stop
  ]
end

to draw-evidence-and-update-belief

  ; There are two ways to generate evidence. If the parameter total-data-points is higher than 0, we assume  that there is a certain amount of data (i.e. total-data-points)
  ; that each agent sees every turn, and we also assume that it is the same for every agent. This implies that the amount of evidence observed by each agent does not depend on
  ; the amount of people they are connected to. Consequently, the parameter "samples" plays no role. If the parameter total-data-points is 0, then each agent collects a data point equal to
  ; the value of samples. Hence, each agents sees the samples of everybody else she is connected to.

  ifelse total-data-points > 0 [
    let total-successes-drawn random-binomial total-data-points (d_1_given_x_1)
    set evidence lput total-successes-drawn evidence
    ask turtles [
      update-belief-multiple-draws total-successes-drawn total-data-points
    ]
  ][
    ask turtles [
      set personal-successes-drawn random-binomial samples (d_1_given_x_1)
    ]
    update-belief-in-network
  ]
end

to update-belief-in-network

  ; Each agent updates her belief on her evidence and on other people-she-is-connected-to's evidence.

  ask turtles [
    update-belief-multiple-draws personal-successes-drawn samples
    foreach [self] of link-neighbors [ i ->
      ;update-belief [personal-evidence-piece] of i
      update-belief-multiple-draws [personal-successes-drawn] of i samples
    ]
  ]
end

to update-belief-multiple-draws [successes-drawn data-points]

  ; The Update is Bayesian. First, we compute P(data| X_1) and P(data| X_2). Thus, we compute P (X_1| data) by decomposing it into P(data|X_1)*P(X_1) / P(data)
  ; Notably, to compute P(data| X_1) and P(data| X_2) we use the formula for binomial distribution. P(data|X_1) = (p^k) * ((1-p)^(n-k)), where k successes and n data points.

  let p_D_1 ((biased-d_1_given_x_1 ) ^ successes-drawn) * ((1 - biased-d_1_given_x_1 ) ^ (data-points - successes-drawn))
  let p_D_2 ((d_1_given_x_2 ) ^ successes-drawn) * (1 - d_1_given_x_2) ^ (data-points - successes-drawn)
  let p_D P_D_1 * player-belief + p_D_2 * (1 - player-belief) ; Calculate P(data). Law of total probability.
  ;if p_D < 0.0000000000000000000000001 [set P_D 0.000000000000000000000000000001]
  set player-belief (P_D_1 * player-belief / P_D)

end


to influence-each-other

  ; This procedure updates the diagnostic value of each agent. This procedure is also composed of two parts.
  ; First, we sum the all the values an agent is influenced from and the number of influencers...

  ask turtles [
    set new-biased-d_1_given_x_1 biased-d_1_given_x_1
    set number-of-influencers 1
    foreach [self] of link-neighbors with [condition-verified myself] [i ->
      set new-biased-d_1_given_x_1 new-biased-d_1_given_x_1 + [biased-d_1_given_x_1] of i
      set number-of-influencers number-of-influencers + 1
    ]
  ]

  ;... then we compute the perceived value of reality (real value + (reality noise)) and we update biased-d_1_given_x_1 following the formula:
  ; (1 - alpha)(value-from-others) + (alpha)(value-from-reality).

  ask turtles [
    ;Here, we are assigning the new-value to P(D_1|X_1) after the numbers have been divided by the sum of all the influencers.
    set biased-d_1_given_x_1 ( new-biased-d_1_given_x_1 / number-of-influencers)
  ]
end

to-report condition-verified [turtle1]

  ; the condition is verified if the interval between the two player-beliefs is not too big

  let reporter False
  if abs(player-belief - [player-belief] of turtle1) < [agent-epsilon] of turtle1 [set reporter True]
  report reporter
end


to-report stable
  let reporter True
  ask turtles[
    if (not is-right) and (not is-wrong)
    [set reporter False]
  ]
  report reporter
end

to-report is-right
  report ifelse-value player-belief > .99 [True][False]
end

to-report is-wrong
  report ifelse-value player-belief < .01 [True][False]
end

to generate-result
  ifelse consensus 1 [
    set final-result "True-Consensus"
  ][
    ifelse consensus 2 [
      set final-result "Wrong-Consensus"
    ][
      set final-result "Polarization"
    ]
  ]
  set percentage-of-correct-scientists ( count turtles with [player-belief > 0.9] / number-of-agents)
end

to-report consensus  [x]
  let reporter True
  ask turtles [
    if x = 1 and player-belief < 0.99 [set reporter False]
    if x = 2 and player-belief > 0.01 [set reporter False]
  ]
  report reporter
end



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;PRODUCE DATA POINTS;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to-report random-binomial [n p]
  report reduce + (n-values n [ifelse-value (p > random-float 1) [1] [0]])
end
@#$#@#$#@
GRAPHICS-WINDOW
880
53
1248
422
-1
-1
10.91
1
10
1
1
1
0
1
1
1
-16
16
-16
16
0
0
1
ticks
30.0

BUTTON
83
132
146
165
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
14
130
77
163
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
11
212
183
245
d_1_given_x_1
d_1_given_x_1
0
1
0.41
0.01
1
NIL
HORIZONTAL

SLIDER
12
92
184
125
number-of-agents
number-of-agents
0
100
25.0
1
1
NIL
HORIZONTAL

SLIDER
10
285
182
318
epsilon
epsilon
0
1
0.66
0.01
1
NIL
HORIZONTAL

PLOT
277
54
599
422
 Diagnostic Values of the First 25 Agents
NIL
NIL
0.0
1.0
0.3
0.7
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 0"
"pen-1" 1.0 0 -7500403 true "" "plot [biased-d_1_given_x_1] of turtle 1"
"pen-2" 1.0 0 -2674135 true "" "plot [biased-d_1_given_x_1] of turtle 2"
"pen-3" 1.0 0 -955883 true "" "plot [biased-d_1_given_x_1] of turtle 3"
"pen-4" 1.0 0 -6459832 true "" "plot [biased-d_1_given_x_1] of turtle 4"
"pen-5" 1.0 0 -1184463 true "" "plot [biased-d_1_given_x_1] of turtle 5"
"pen-6" 1.0 0 -10899396 true "" "plot [biased-d_1_given_x_1] of turtle 6"
"pen-7" 1.0 0 -13840069 true "" "plot [biased-d_1_given_x_1] of turtle 7"
"pen-8" 1.0 0 -14835848 true "" "plot [biased-d_1_given_x_1] of turtle 8"
"pen-9" 1.0 0 -11221820 true "" "plot [biased-d_1_given_x_1] of turtle 9"
"pen-10" 1.0 0 -13791810 true "" "plot [biased-d_1_given_x_1] of turtle 10"
"pen-11" 1.0 0 -13345367 true "" "plot [biased-d_1_given_x_1] of turtle 11"
"pen-12" 1.0 0 -8630108 true "" "plot [biased-d_1_given_x_1] of turtle 12"
"pen-13" 1.0 0 -5825686 true "" "plot [biased-d_1_given_x_1] of turtle 13"
"pen-14" 1.0 0 -2064490 true "" "plot [biased-d_1_given_x_1] of turtle 14"
"pen-15" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 15"
"pen-16" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 16"
"pen-17" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 17"
"pen-18" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 18"
"pen-19" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 19"
"pen-20" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 20"
"pen-21" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 21"
"pen-22" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 22"
"pen-23" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 23"
"pen-24" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 24"
"pen-25" 1.0 0 -16777216 true "" "plot [biased-d_1_given_x_1] of turtle 25"
"pen-26" 1.0 0 -16777216 true "" ""
"pen-27" 1.0 0 -16777216 true "" ""
"pen-28" 1.0 0 -16777216 true "" ""
"pen-29" 1.0 0 -16777216 true "" ""
"pen-30" 1.0 0 -16777216 true "" ""
"pen-31" 1.0 0 -16777216 true "" ""

MONITOR
1142
426
1249
471
NIL
final-result
17
1
11

BUTTON
155
132
232
165
go-once
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
0

PLOT
609
55
878
422
Factual Beliefs of the First 25 Agents
NIL
NIL
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 0"
"pen-1" 1.0 0 -7500403 true "" "plot [player-belief] of turtle 1"
"pen-2" 1.0 0 -2674135 true "" "plot [player-belief] of turtle 2"
"pen-3" 1.0 0 -955883 true "" "plot [player-belief] of turtle 3"
"pen-4" 1.0 0 -6459832 true "" "plot [player-belief] of turtle 4"
"pen-5" 1.0 0 -1184463 true "" "plot [player-belief] of turtle 5"
"pen-6" 1.0 0 -10899396 true "" "plot [player-belief] of turtle 6"
"pen-7" 1.0 0 -13840069 true "" "plot [player-belief] of turtle 7"
"pen-8" 1.0 0 -14835848 true "" "plot [player-belief] of turtle 8"
"pen-9" 1.0 0 -11221820 true "" "plot [player-belief] of turtle 9"
"pen-10" 1.0 0 -13791810 true "" "plot [player-belief] of turtle 10"
"pen-11" 1.0 0 -13345367 true "" "plot [player-belief] of turtle 11"
"pen-12" 1.0 0 -8630108 true "" "plot [player-belief] of turtle 12"
"pen-13" 1.0 0 -5825686 true "" "plot [player-belief] of turtle 13"
"pen-14" 1.0 0 -2064490 true "" "plot [player-belief] of turtle 14"
"pen-15" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 15"
"pen-16" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 16"
"pen-17" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 17"
"pen-18" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 18"
"pen-19" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 19"
"pen-20" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 20"
"pen-21" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 21"
"pen-22" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 22"
"pen-23" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 23"
"pen-24" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 24"
"pen-25" 1.0 0 -16777216 true "" "plot [player-belief] of turtle 25"

SLIDER
11
406
183
439
samples
samples
1
100
2.0
1
1
NIL
HORIZONTAL

PLOT
880
54
1249
422
Number of "Correct" Agents
NIL
NIL
0.0
10.0
0.0
30.0
true
false
"" ""
PENS
"default" 1.0 0 -8275240 true "" "plot count turtles with [player-belief > .99]"

SLIDER
12
477
207
510
initial-distance-diag-value
initial-distance-diag-value
0
1
0.38
0.01
1
NIL
HORIZONTAL

SLIDER
11
442
183
475
total-data-points
total-data-points
0
300
180.0
1
1
NIL
HORIZONTAL

MONITOR
277
428
1137
473
NIL
evidence
17
1
11

SLIDER
10
250
182
283
connection-probability
connection-probability
0
1
0.2
0.1
1
NIL
HORIZONTAL

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.2.0
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="ExperimentCharitableOConn1FourRepeatedLimitedInitialCondsFalse4951" repetitions="300" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <metric>final-result</metric>
    <metric>count turtles with[player-belief &gt; .99]</metric>
    <metric>ticks</metric>
    <enumeratedValueSet variable="reality-noise">
      <value value="0.01"/>
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number-of-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="which-condition">
      <value value="&quot;closeness-factual-belief&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="influence-from-reality">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="network">
      <value value="&quot;Cycle&quot;"/>
      <value value="&quot;Complete&quot;"/>
      <value value="&quot;Wheel&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="reality-sensitivity-is-a-thing">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="d_1_given_x_1">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="epsilon">
      <value value="0.01"/>
      <value value="0.1"/>
      <value value="0.2"/>
      <value value="0.3"/>
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="d_1_given_x_2">
      <value value="0.51"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="samples">
      <value value="1"/>
      <value value="5"/>
      <value value="10"/>
      <value value="20"/>
      <value value="50"/>
      <value value="100"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="ExperimentCharitableOConn1Comparison" repetitions="100" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <metric>final-result</metric>
    <metric>count turtles with[player-belief &gt; .99]</metric>
    <metric>ticks</metric>
    <enumeratedValueSet variable="reality-noise">
      <value value="0.01"/>
      <value value="0.1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number-of-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="which-condition">
      <value value="&quot;closeness-factual-belief&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="influence-from-reality">
      <value value="0.01"/>
      <value value="0.2"/>
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="network">
      <value value="&quot;Cycle&quot;"/>
      <value value="&quot;Complete&quot;"/>
      <value value="&quot;Wheel&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="d_1_given_x_1">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="epsilon">
      <value value="0.01"/>
      <value value="0.1"/>
      <value value="0.2"/>
      <value value="0.3"/>
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="d_1_given_x_2">
      <value value="0.55"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="samples">
      <value value="1"/>
      <value value="5"/>
      <value value="10"/>
      <value value="20"/>
      <value value="50"/>
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="reality-sensitivity-is-a-thing">
      <value value="true"/>
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
