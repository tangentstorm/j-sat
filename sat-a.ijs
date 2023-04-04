NB. Algorithm A in Satisfiability (TAOCP by Knuth)


NB. helper functions for inspecting the
NB. problem as boxed literals
NB. ----------------------------------------

NB. Knuth, pg 4: R (6) (unsatisfiable)
Ru=:   > 1  2 _3;  2  3 _4;  3  4  1;  4 _1  2
Ru=:Ru,>_1 _2  3; _2 _3  4; _3 _4 _1; _4  1 _2
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
nv =: {{>./|;y}}

NB. notational helpers
NB. ----------------------------------------

not =: XOR 1:
sgn =: AND 1:

M =: {{ mm{~<:y }} :: {{ mm =: x (<:y) } mm }}
ST=: {{ st{~<:y }}
SZ=: {{ sz{~<:y }} :: {{ sz =: x (<:y) } sz }}
L =: {{ ll{~<:y }}
F =: {{ ff{~<:y }} :: {{ ff =: x (<:y) } ff }}
B =: {{ bb{~<:y }} :: {{ bb =: x (<:y) } bb }}
C =: {{ cc{~<:y }} :: {{ cc =: x (<:y) } cc }}

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
  nv =. nvars y
  mm =: nv $ _  NB. list of move codes for each variable

  NB. --- clauses ------------------------
  NB. first convert _1 2 _3 .. to knuth numbers: 3 4 7
  NB. then sort each clause from highest to lowest
  NB. and then reverse the list of clauses
  yy =. |. ([: \:~ <&0++:@|)L:0 y
  sl =. +: nv + 1               NB. start of literals (2*nv+1 (0 1 empty))
  sz =: #&> yy                  NB. SIZE of each clause
  st =: sv+0,}:+/\sz            NB. START of each clause

  NB. --- cells --------------------------
  NB. (one cell per literal in a clause)
  ll =: (sl$_),;yy              NB. literal for cell
  ul =. 2+i.sl-2                NB. unique literals (also index of "head" cell)
  lc =. +/ll=/ul                NB. counts of these literals
  id =. sz#1+i.-#y              NB. id of clause to which a cell belongs
  cc =: _ _, lc, id             NB. cc=count of or id of clauses
  ff =: ul i:`(, )`}: linked ll NB. fwd: next cell with this literal
  bb =: ul i.`(,~)`}. linked ll NB. bak: prev cell with this literal

  NB. -- return his state table, just for debugging
  (i.#ll),ll,ff,bb,:cc }}


satA =: {{
  knuth y                       NB. init variables in locale
label_A1. NB. [Initialize]
  a =: #cc                      NB. number of active clauses
  d =: 0                        NB. search depth
label_A2. NB. [Choose]
  b =: 2 * d+1                  NB. bit (literal) to set
  if. </C b+0 1 do. b=:b+1 end.
  d M (sgn b) + 4 * 0=C not b
  if. (C b) = a do. goto_AZ end.
label_A3. NB. [Remove (not b)]
label_A4. NB. [Deactivate clauses for b]
label_A5. NB. [Try again]
label_A6. NB. [Backtrack]
label_A7. NB. [Reactivate clauses for b]
label_A8. NB. [Unremove (not b)]

label_AZ }}
