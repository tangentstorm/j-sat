NB. Algorithm A in Satisfiability (TAOCP by Knuth)
dbr 1

NB. helper functions for inspecting the
NB. problem as boxed literals
NB. ----------------------------------------

NB. Knuth, pg 4: R (6) (unsatisfiable)
Ru=:   > 1  2 _3;  2  3 _4;  3  4  1;  4 _1  2
Ru=:Ru,>_1 _2  3; _2 _3  4; _3 _4 _1; _4  1 _2
Ru=:;/Ru
NB. Knuth R` (7) (satisfiable)
R =: }:Ru

NB. rcnf: random cnf with x clauses of y variables
rcnf =: {{(<:+:?x#,:2 2 2) * 1+3? x$y}}

NB. indices in x where x contains the literal y
iwl =: {{ I. y&e. S:0 x }}

NB. clauses in x where x contains the literal y
cwl =: [ {~ iwl

NB. number of clauses in x where x contains the literal y
nwl =: #@cwl"_ 0

NB. number of variables of boxed CNF list y
NB. (max absolute value of the raze)
nvars =: {{>./|;y}}

NB. notational helpers
NB. ----------------------------------------

not =: XOR 1:
sgn =: AND 1:

NB. -- vars --
NB. M = movement codes per variable
M =: {{ if. y -: _ do. mm else. mm{~y end. }} :: {{ mm =: x y } mm }}

NB. --clauses--
NB. ST = start of each clause
ST=: {{ if. y -: _ do. st else. st{~y end. }}
NB. SZ = size of each clause
SZ=: {{ if. y -: _ do. sz else. sz{~y end. }} :: {{ sz =: x y } sz }}
NB. deleted flag (per clause)
D =: {{ if. y -: _ do. dd else. dd{~y end. }} :: {{ dd =: x y } dd }}

NB. -- cells --
NB. L =: literal in each cell (clauses are composed of cells)
L =: {{ if. y -: _ do. ll else. ll{~y end. }}
NB. Fwd link to next cell that contains same literal (in circular linked list)
F =: {{ if. y -: _ do. ff else. ff{~y end. }} :: {{ ff =: x y } ff }}
NB. backward link
B =: {{ if. y -: _ do. bb else. bb{~y end. }} :: {{ bb =: x y } bb }}
NB. the clause number for each cell
C =: {{ if. y -: _ do. cc else. cc{~y end. }} :: {{ cc =: x y } cc }}

NB.   C 5 -> 4{cc
NB. 3 C 5 -> cc =: 3 (4)}cc


NB. helpers to build knuth-style table
NB. ----------------------------------------

NB. key value array of length n with fill _
NB. x is list of indices, y is list of values
kva =: {{ y x } n$m}}/

linked=:{{ NB. builds a circular linked list
  NB. !! refactor this to be more general purpose.
  NB. it could be a general purpose linked list maker
  NB. but it has this weird prefix with start of the list...
  ii =. <@I. x =/ y   NB. indices of x in y
  '`start link chop'=.m     NB. verbs to construct the list
  (_ kva(#y))/ ;"1 (x,:y start x);"1 ii,:(;/x) link L:0 chop L:0 ii }}


knuth =: {{ NB. convert boxed cnf y to knuth form
  NB. --- input variables ----------------
  nv =: nvars y
  mm =: (nv+1) $ _  NB. list of move codes for each var, plus a blank.

  NB. --- clauses ------------------------
  NB. first convert _1 2 _3 .. to knuth numbers: 3 4 7
  NB. then sort each clause from highest to lowest
  NB. and then reverse the list of clauses
  yy =. |. ([: \:~ <&0++:@|)L:0 y
  sl =: +: nv + 1               NB. start of literals (2*nv+1 (0 1 empty))
  sz =: #&> yy                  NB. SIZE of each clause
  st =: sl+0,}:+/\sz            NB. START of each clause
  dd =: 0"0 yy                  NB. deleted flag per clause

  NB. --- cells --------------------------
  NB. (one cell per literal in a clause)
  ll =: (sl$_),;yy              NB. literal for cell
  ul =. 2+i.sl-2                NB. unique literals (also index of "head" cell)
  lc =. +/ll=/ul                NB. counts of these literals
  id =. sz#i.-#y                NB. id of clause to which a cell belongs
  cc =: _ _, lc, id             NB. cc=count of or id of clauses
  ff =: ul i:`(, )`}: linked ll NB. fwd: next cell with this literal
  bb =: ul i.`(,~)`}. linked ll NB. bak: prev cell with this literal
}}

lstate =: {{(,.'pLFBC');(i.#ll),ll,ff,bb,:cc }}  NB. state of cells/lits
cstate =: {{(,.'C^#D');((i.# ST _),ST,SZ,:D)_}}  NB. state of clauses


NB. TODO: make these local variables??

NB. show currently active clauses
clauses =: ST ({.@C;L)@(+i.@])"0 SZ

satA =: {{NB. solve boxed cnf y using Knuth Algorithm A
  knuth y                         NB. init variables in locale
label_A1. NB. [Initialize]
  a =: +/0<sz                     NB. no. of active clauses (#y at start)
  am=: 1"0 sz
  d =: 1                          NB. search depth+1
label_A2. NB. [Choose]
  b =: 2 * d                      NB. bit (literal) to set
  if. </C b+0 1 do. b=:b+1 end.   NB. choose whichever value for bit has more clauses.
  d M~ (sgn b) + 4 * 0=C not b     NB. set move code
  if. (C b) = a do. goto_AZ. end.  NB. all terms satisfied! (all clauses contained b)
label_A3. NB. [Remove (not b)]
  c =: C I. (not b) = L _          NB. clauses containing 'not b'
  if. 1 e. SZ c do. goto_A5.       NB. removing last item = unsat
  else. (SZ~ <:@SZ) c end.
label_A4. NB. [Deactivate clauses for b]
  c =: C I. b = L _                NB. clauses containing b
  d D c =: (#~ 0 = D) c            NB. delete those that are not yet deleted. (by storing depth)
  NB. decrement the "number of clauses with this literal set" counters
  ci =.  I.c e.~cc                 NB. indices for cells of the deleted clauses
  (C~ <:@C)"0 L (#~ sl<]) ci       NB. decrease count for literals in those cells
  a =: a - #c [ d =: d+1           NB. update total clause count
  goto_A2.
label_A5. NB. [Try again]
  echo 'got to step A5' throw.
label_A6. NB. [Backtrack]
label_A7. NB. [Reactivate clauses for b]
label_A8. NB. [Unremove (not b)]

label_AZ.
  echo'!!!!!! satisified !!!!'
  echo'assignments:', ": }. -. mm
}}


NB. begin main program
knuth R NB. just to show initial state
echo 'literals:'
echo lstate''
echo 'clause state:'
echo cstate''
echo 'clauses:'
echo clauses _
satA R
