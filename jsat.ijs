Note 'what is SAT?'

- Boolean Satisfiability Problem

- Problem is stated as an AND-product of OR-clauses.
  Each clause is the OR-sum of a set of signed literals.

  For example:

  (~x1 + x2 + x7) * (~x8 + x3 + ~x2) ...

- Can be generated at random, or derived from pretty much any
  problem that you can express as a function of input bits.

- Most common case (3SAT) has clauses of exactly 3 literals each
)

NB. Knuth, pg 4: R (6) (unsatisfiable)
Ru=:   > 1  2 _3;  2  3 _4;  3  4  1;  4 _1  2
Ru=:Ru,>_1 _2  3; _2 _3  4; _3 _4 _1; _4  1 _2
NB. Knuth R` (7) (satisfiable)
R =: }:Ru

NB. rcnf: random cnf with x clauses of y variables
rcnf =: {{(<:+:?x#,:2 2 2) * 1+3? x$y}}


NB. make some bit vectors for repl demos
NB. they go into a locale (namespace) called 'bits'
NB. that we insert into the lookup path
mkbits=: {{
  oldcc =. coname''
  cocurrent 'bits'
  clear'bits'
  names =. ;(' b',":)&.> 1+i.y
  (names) =: ,:"1 |. |:#:i.2^y
  cocurrent oldcc
  coinsert 'bits' }}

mkbits 4

NB. convert number to variable literal
n2lit =: {{< ('(-.', ')' ,~ ])^:(y<0:) 'b',":|y}}"0
NB. convert a clause (OR-sum) to string
c2str =: {{ '+./ ', ; (,', ';])/  n2lit y}}"1

NB. truth tables for super naive brute force "solver"
tt =: {{ *./ ". c2str y [ mkbits >./,| y }}

NB. completely naive brute force "solver" for sat problem
sat0 =: +./@tt


NB. load a SAT in the format used by this web solver:
NB. https://simewu.com/SAT-solver/
loadSAT =: {{ > ".each LF cut '-_' charsub freads y }}

NB. turn rectangular array with zeros into list of boxed lists
boxed =: {{-.&0 L:0 ;/y}}
ZEBRA =: boxed loadSAT 'zebra.sat'

NB. clauses in x containing the variable y (regardless of sign)
NB. (this assumes inversion is provided by negative number)
NB. cwv =: {{x#~+./"1] y=|x}}  TODO: FIX

NB. group y by key x (where x is group number 0..n)
groups =: {{ (/:~.x) { x </.y }}


NB. sat solver that follows a simple recursive algorithm
NB. returns either a (possibly empty) list of inputs
NB. (ex: 4 _2 means b4 and -.b2) if the formula is satisfiable,
NB. otherwise returns _. for UNSAT

UNS =: s:' unsat'
sat1 =: {{
  NB. y is the the cnf formula as list of boxed lists
  if. 0=#y do. '' return. end. NB. satisfiable without inputs
  if. a: e. y do. UNS return. end. NB. UNSAT by empty clause (0=+./'')
  NB. still here, so choose a bit and try setting it.
  b =. choose_bit y
  r =. sat1 y when b
  if. UNS -: r do. r =. sat1 y when -b else. r,b return. end.
  if. UNS -: r do. return. UNS else. r,-b return. end. }}

choose_bit =: {{|0{;y}} NB. just take first variable we see

when =: {{ NB. assign bit y in boxed cnf x
  x =. x #~ -. y e.&> x  NB. remove clauses with given literal
  x =. -.&(-y)L:0 x      NB. remove the negated literal from clauses
  x }}


Note ''

  timespacex 'sat1 ZEBRA'
572.651 7.48989e6

  timespacex 'zc =: sat1 ZEBRA'
530.96 7.49027e6

  $zc
155

  q:$zc
5 31

  (|.q:155)$zc
_155 _153 _152 _150 _147
_146  151  149  154  148
_145 _144 _143 _141 _140
_138 _136 _135 _134 _133
_132 _131 _130 _129 _127
_126  142  139  137  128
 100  _99  _98  _97  _96
 _95   94  _93  _92  _91
 _90  _89   88  _87  _86
 _85  _84  _83   82  _81
 _80  _79  _78  _77   76
_125 _124 _123  122 _121
_120 _119  118 _117 _116
_115  114 _113 _112 _111
_110 _109 _108 _107  106
 105 _104 _103 _102 _101
 _50  _49   48  _47  _46
 _45  _44  _43   42  _41
 _40   39  _38  _37  _36
 _35  _34  _33  _32   31
  30  _29  _28  _27  _26
  75  _74  _73  _72  _71
 _70  _69   68  _67  _66
 _65   64  _63  _62  _61
 _60  _59  _58   57  _56
 _55  _54  _53  _52   51
 _25  _24  _23   22  _21
 _20   19  _18  _17  _16
 _15  _14  _13  _12   11
  10   _9   _8   _7   _6
  _5   _4    3   _2   _1
)
